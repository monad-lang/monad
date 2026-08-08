//! Minimal stdio JSON-RPC LSP server — diagnostics + navigation
//! (`hover`, `definition`, `documentSymbol`, `workspace/symbol`) plus one
//! codemod (`organize-imports`, reachable both as a
//! `source.organizeImports` code action and as the
//! `monad.organizeImports` executable command), matching the plan's phase
//! ordering ("ship diagnostics + navigation first"). Completions, rename,
//! semantic tokens, and general code actions need error-tolerant parsing
//! (the parser stops at the first syntax error; no recovery/partial-AST
//! support yet) — explicitly out of scope here, not an oversight, and the
//! server's own advertised `capabilities` only claim what's actually
//! implemented. `organize-imports` is the one exception: it only ever
//! needs a file that already parses cleanly (nothing sound to compute
//! from a broken one anyway), so it doesn't run into that limitation.
//!
//! `hover`/`definition` resolve within the open document first, falling
//! back (via `crate::resolve_symbol`) to a workspace-wide search across
//! the resolved mote graph if not found locally — so an identifier
//! imported from another mote resolves too. `workspace/symbol` and the
//! custom `workspace/diagnoseWorkspace` notification search/check that
//! same resolved workspace (project `src/` + every dependency mote's
//! `src/`) on-disk, not just open buffers.
//!
//! No debounce: every `didChange` re-checks synchronously on the same
//! thread that reads stdin, matching the CLI's own agent-mode behavior
//! (`check --json` has no debounce either) rather than the plan's
//! human-editor debounce scheduling, which would need `async-threading`
//! (a separate, larger dependency) to do properly. Simpler and always
//! correct, just potentially slower than an editor wants on very large
//! files under rapid keystrokes — an acceptable v1 tradeoff, not
//! something silently wrong.
//!
//! Diagnostics/hover/definition/documentSymbol/codeAction/executeCommand
//! all operate on the editor's in-memory buffer (`Document.text`, updated
//! on every `didChange`), not what's saved on disk — via
//! `monad_core::check_source`/`symbols_from_source`/
//! `organize_imports_for_source`, the same single-source entry points
//! `core` exposes specifically for this.

use std::collections::HashMap;
use std::io::{self, BufRead, BufReader, Write};
use std::path::PathBuf;

use monad_core::{
  SymbolInfo, check_files, check_source, diag::Severity, organize_imports_for_source,
  symbols_for_files, symbols_from_source,
};

use crate::{
  identifier_at, location_to_json_range, path_to_uri, resolve_symbol, symbol_kind_label,
};

/// Command id for the one `workspace/executeCommand` this server
/// supports — organizes the given document's imports/annotations, same
/// computation as the `monad-rs organize-imports` CLI subcommand and the
/// `source.organizeImports` code action below (all three share
/// `organize_imports_for_source`, so they can't drift on what "organize
/// imports" means).
const ORGANIZE_IMPORTS_COMMAND: &str = "monad.organizeImports";

/// One open document's current buffer content. LSP full-document sync
/// (`TextDocumentSyncKind::Full`, the only kind this server advertises)
/// means `didChange` always replaces this wholesale, never applies a
/// partial-range patch.
struct Document {
  text: String,
}

pub fn run(mote_path: Vec<PathBuf>) -> Result<(), String> {
  let stdin = io::stdin();
  let mut reader = BufReader::new(stdin.lock());
  let stdout = io::stdout();
  let mut writer = stdout.lock();

  let mut documents: HashMap<String, Document> = HashMap::new();
  let mut shutting_down = false;
  // Monotonic id for server-initiated requests (currently just
  // `workspace/applyEdit`, sent by the executeCommand handler below).
  let mut next_request_id: u64 = 1;

  loop {
    let body = match read_message(&mut reader).map_err(|e| format!("transport error: {e}"))? {
      Some(b) => b,
      None => break, // stdin closed — client disconnected without exit/shutdown
    };
    let msg: serde_json::Value = match serde_json::from_str(&body) {
      Ok(v) => v,
      Err(e) => {
        eprintln!("lsp: dropping malformed message: {e}");
        continue;
      }
    };
    let id = msg.get("id").cloned();
    let method = msg.get("method").and_then(|m| m.as_str());
    let params = msg
      .get("params")
      .cloned()
      .unwrap_or(serde_json::Value::Null);

    let Some(method) = method else {
      // No `method` field: this is a RESPONSE to a request WE sent (the
      // only one is `workspace/applyEdit`, fired fire-and-forget by
      // `execute_command` below) — not a client request needing a
      // handler, so it must NOT fall into the "method not found" branch.
      continue;
    };

    match method {
      "initialize" => send_response(&mut writer, id, initialize_result())?,
      // Notifications this server has nothing to do in response to, but
      // are a normal part of the protocol — silently accepted rather
      // than falling into the "unknown method" branch below.
      "initialized" | "$/setTrace" | "$/cancelRequest" | "workspace/didChangeConfiguration" => {}
      "shutdown" => {
        shutting_down = true;
        send_response(&mut writer, id, serde_json::Value::Null)?;
      }
      "exit" => {
        return if shutting_down {
          Ok(())
        } else {
          Err("client sent exit before shutdown".to_string())
        };
      }
      "textDocument/didOpen" => did_open(&mut documents, &mut writer, &params, &mote_path)?,
      "textDocument/didChange" => did_change(&mut documents, &mut writer, &params, &mote_path)?,
      "textDocument/didClose" => did_close(&mut documents, &params),
      "textDocument/hover" => hover(&documents, &mut writer, id, &params, &mote_path)?,
      "textDocument/definition" => definition(&documents, &mut writer, id, &params, &mote_path)?,
      "textDocument/documentSymbol" => {
        document_symbol(&documents, &mut writer, id, &params, &mote_path)?
      }
      "workspace/symbol" => workspace_symbol(&mut writer, id, &params, &mote_path)?,
      // Custom notification (not standard LSP) — matches the name already
      // sketched, unimplemented, in
      // `plans/library-ideas/language-server.md`. A notification, not a
      // request: fired to trigger a workspace-wide re-check (e.g. bound
      // to an editor command), answered with a batch of
      // `publishDiagnostics` notifications rather than a single response.
      "workspace/diagnoseWorkspace" => diagnose_workspace(&mut writer, &mote_path)?,
      "textDocument/codeAction" => code_action(&documents, &mut writer, id, &params, &mote_path)?,
      "workspace/executeCommand" => execute_command(
        &documents,
        &mut writer,
        id,
        &params,
        &mote_path,
        &mut next_request_id,
      )?,
      _ => {
        // A notification with no handler is fine to ignore per the LSP
        // spec; a REQUEST with no handler must get an error response, or
        // a well-behaved client would hang waiting for one.
        if let Some(id) = id {
          send_error(
            &mut writer,
            id,
            -32601,
            &format!("method not found: {method}"),
          )?;
        }
      }
    }
  }
  Ok(())
}

// --- transport --------------------------------------------------------

fn read_message(reader: &mut impl BufRead) -> io::Result<Option<String>> {
  let mut content_length: Option<usize> = None;
  loop {
    let mut line = String::new();
    if reader.read_line(&mut line)? == 0 {
      return Ok(None); // EOF before a full header block
    }
    let line = line.trim_end_matches(['\r', '\n']);
    if line.is_empty() {
      break; // blank line ends the header block
    }
    if let Some((key, value)) = line.split_once(':')
      && key.eq_ignore_ascii_case("Content-Length")
    {
      content_length = value.trim().parse().ok();
    }
  }
  let len = content_length
    .ok_or_else(|| io::Error::new(io::ErrorKind::InvalidData, "missing Content-Length header"))?;
  let mut buf = vec![0u8; len];
  reader.read_exact(&mut buf)?;
  Ok(Some(String::from_utf8_lossy(&buf).into_owned()))
}

fn write_message(writer: &mut impl Write, body: &serde_json::Value) -> Result<(), String> {
  let text =
    serde_json::to_string(body).map_err(|e| format!("failed to serialize message: {e}"))?;
  write!(writer, "Content-Length: {}\r\n\r\n{}", text.len(), text).map_err(|e| format!("{e}"))?;
  writer.flush().map_err(|e| format!("{e}"))
}

fn send_response(
  writer: &mut impl Write,
  id: Option<serde_json::Value>,
  result: serde_json::Value,
) -> Result<(), String> {
  write_message(
    writer,
    &serde_json::json!({ "jsonrpc": "2.0", "id": id, "result": result }),
  )
}

fn send_error(
  writer: &mut impl Write,
  id: serde_json::Value,
  code: i64,
  message: &str,
) -> Result<(), String> {
  write_message(
    writer,
    &serde_json::json!({
      "jsonrpc": "2.0",
      "id": id,
      "error": { "code": code, "message": message }
    }),
  )
}

fn send_notification(
  writer: &mut impl Write,
  method: &str,
  params: serde_json::Value,
) -> Result<(), String> {
  write_message(
    writer,
    &serde_json::json!({ "jsonrpc": "2.0", "method": method, "params": params }),
  )
}

/// Send a server-initiated REQUEST (currently only `workspace/applyEdit`).
/// Fire-and-forget: the eventual response comes back as a message with an
/// `id` but no `method`, which the main loop's dispatch already treats as
/// a no-op rather than an unhandled request (see the `let Some(method) =
/// method else { continue }` guard there) — this server has no need to
/// correlate the response to anything, so it's simply not tracked.
fn send_request(
  writer: &mut impl Write,
  id: u64,
  method: &str,
  params: serde_json::Value,
) -> Result<(), String> {
  write_message(
    writer,
    &serde_json::json!({ "jsonrpc": "2.0", "id": id, "method": method, "params": params }),
  )
}

fn initialize_result() -> serde_json::Value {
  serde_json::json!({
    "capabilities": {
      "textDocumentSync": 1, // Full
      "hoverProvider": true,
      "definitionProvider": true,
      "documentSymbolProvider": true,
      "workspaceSymbolProvider": true,
      "codeActionProvider": { "codeActionKinds": ["source.organizeImports"] },
      "executeCommandProvider": { "commands": [ORGANIZE_IMPORTS_COMMAND] }
    },
    "serverInfo": { "name": "monad-lsp", "version": env!("CARGO_PKG_VERSION") }
  })
}

fn uri_to_path(uri: &str) -> Option<PathBuf> {
  uri.strip_prefix("file://").map(PathBuf::from)
}

// --- document sync ------------------------------------------------------

fn did_open(
  documents: &mut HashMap<String, Document>,
  writer: &mut impl Write,
  params: &serde_json::Value,
  mote_path: &[PathBuf],
) -> Result<(), String> {
  let Some(td) = params.get("textDocument") else {
    return Ok(());
  };
  let (Some(uri), Some(text)) = (
    td.get("uri").and_then(|u| u.as_str()),
    td.get("text").and_then(|t| t.as_str()),
  ) else {
    return Ok(());
  };
  documents.insert(
    uri.to_string(),
    Document {
      text: text.to_string(),
    },
  );
  publish_diagnostics(writer, uri, documents, mote_path)
}

fn did_change(
  documents: &mut HashMap<String, Document>,
  writer: &mut impl Write,
  params: &serde_json::Value,
  mote_path: &[PathBuf],
) -> Result<(), String> {
  let Some(uri) = params
    .get("textDocument")
    .and_then(|td| td.get("uri"))
    .and_then(|u| u.as_str())
  else {
    return Ok(());
  };
  // Full sync only: the LAST entry in `contentChanges` is the new whole-
  // document text. A spec-compliant client never sends a range-based
  // incremental edit here since `initialize` only ever advertises
  // `TextDocumentSyncKind::Full`.
  let Some(text) = params
    .get("contentChanges")
    .and_then(|c| c.as_array())
    .and_then(|arr| arr.last())
    .and_then(|c| c.get("text"))
    .and_then(|t| t.as_str())
  else {
    return Ok(());
  };
  let uri = uri.to_string();
  documents.insert(
    uri.clone(),
    Document {
      text: text.to_string(),
    },
  );
  publish_diagnostics(writer, &uri, documents, mote_path)
}

fn did_close(documents: &mut HashMap<String, Document>, params: &serde_json::Value) {
  if let Some(uri) = params
    .get("textDocument")
    .and_then(|td| td.get("uri"))
    .and_then(|u| u.as_str())
  {
    documents.remove(uri);
  }
}

fn severity_to_lsp_number(s: Severity) -> u8 {
  match s {
    Severity::Error => 1,
    Severity::Warning => 2,
    Severity::Note => 3,
    Severity::Help => 4,
  }
}

fn publish_diagnostics(
  writer: &mut impl Write,
  uri: &str,
  documents: &HashMap<String, Document>,
  mote_path: &[PathBuf],
) -> Result<(), String> {
  let Some(doc) = documents.get(uri) else {
    return Ok(());
  };
  let Some(path) = uri_to_path(uri) else {
    return Ok(());
  };
  let diagnostics = check_source(&path, &doc.text, mote_path.to_vec()).unwrap_or_else(|e| {
    vec![monad_core::diag::Diagnostic {
      message: e,
      ..Default::default()
    }]
  });
  let json_diags: Vec<serde_json::Value> = diagnostics
    .iter()
    .map(|d| {
      let range = serde_json::to_value(location_to_json_range(d.location.as_ref()))
        .unwrap_or(serde_json::Value::Null);
      serde_json::json!({
        "range": range,
        "severity": severity_to_lsp_number(d.severity),
        "message": d.message,
        "source": "monad",
      })
    })
    .collect();
  send_notification(
    writer,
    "textDocument/publishDiagnostics",
    serde_json::json!({ "uri": uri, "diagnostics": json_diags }),
  )
}

/// `workspace/diagnoseWorkspace` handler — type-checks the whole resolved
/// workspace on-disk (via `check_files`, not the in-memory `documents`
/// map, so files that aren't open still get checked) and publishes one
/// `textDocument/publishDiagnostics` per file, same wire shape
/// `publish_diagnostics` above uses for a single open document.
fn diagnose_workspace(writer: &mut impl Write, mote_path: &[PathBuf]) -> Result<(), String> {
  let results = check_files(mote_path.to_vec(), mote_path.to_vec()).unwrap_or_default();
  for r in &results {
    let uri = path_to_uri(&r.path);
    let json_diags: Vec<serde_json::Value> = r
      .diagnostics
      .iter()
      .map(|d| {
        let range = serde_json::to_value(location_to_json_range(d.location.as_ref()))
          .unwrap_or(serde_json::Value::Null);
        serde_json::json!({
          "range": range,
          "severity": severity_to_lsp_number(d.severity),
          "message": d.message,
          "source": "monad",
        })
      })
      .collect();
    send_notification(
      writer,
      "textDocument/publishDiagnostics",
      serde_json::json!({ "uri": uri, "diagnostics": json_diags }),
    )?;
  }
  Ok(())
}

// --- navigation -----------------------------------------------------------

/// `(0-indexed line, 0-indexed character)` from an LSP `Position` object,
/// converted to the 1-indexed convention `identifier_at`/`core::Location`
/// use — the one boundary where LSP's and this codebase's own indexing
/// conventions meet.
fn position_1_indexed(params: &serde_json::Value) -> Option<(u32, usize)> {
  let pos = params.get("position")?;
  let line = pos.get("line")?.as_u64()? as u32 + 1;
  let col = pos.get("character")?.as_u64()? as usize + 1;
  Some((line, col))
}

fn text_document_uri<'a>(params: &'a serde_json::Value) -> Option<&'a str> {
  params.get("textDocument")?.get("uri")?.as_str()
}

fn hover(
  documents: &HashMap<String, Document>,
  writer: &mut impl Write,
  id: Option<serde_json::Value>,
  params: &serde_json::Value,
  mote_path: &[PathBuf],
) -> Result<(), String> {
  let Some(id) = id else {
    return Ok(()); // hover is always a request; be defensive if it isn't
  };
  let result = (|| -> Option<serde_json::Value> {
    let uri = text_document_uri(params)?;
    let doc = documents.get(uri)?;
    let path = uri_to_path(uri)?;
    let (line, col) = position_1_indexed(params)?;
    let (name, start_col, end_col) = identifier_at(&doc.text, line, col)?;
    let symbols = symbols_from_source(&path, &doc.text, mote_path.to_vec()).ok()?;
    let (_, sym) = resolve_symbol(&name, &path, &symbols, mote_path)?;
    let contents = sym
      .detail
      .clone()
      .unwrap_or_else(|| format!("{} {}", symbol_kind_label(sym.kind), sym.name));
    Some(serde_json::json!({
      "contents": { "kind": "plaintext", "value": contents },
      "range": {
        "start": { "line": line - 1, "character": start_col - 1 },
        "end": { "line": line - 1, "character": end_col - 1 },
      }
    }))
  })();
  send_response(writer, Some(id), result.unwrap_or(serde_json::Value::Null))
}

fn definition(
  documents: &HashMap<String, Document>,
  writer: &mut impl Write,
  id: Option<serde_json::Value>,
  params: &serde_json::Value,
  mote_path: &[PathBuf],
) -> Result<(), String> {
  let Some(id) = id else {
    return Ok(());
  };
  let result = (|| -> Option<serde_json::Value> {
    let uri = text_document_uri(params)?;
    let doc = documents.get(uri)?;
    let path = uri_to_path(uri)?;
    let (line, col) = position_1_indexed(params)?;
    let (name, _, _) = identifier_at(&doc.text, line, col)?;
    let symbols = symbols_from_source(&path, &doc.text, mote_path.to_vec()).ok()?;
    let (def_path, sym) = resolve_symbol(&name, &path, &symbols, mote_path)?;
    // Local match: echo the client's own `uri` string exactly, as before
    // (some clients compare URIs by exact string match, so don't rebuild
    // an equivalent-but-not-identical one via `path_to_uri`). Cross-file
    // match: there's no client-given URI for the defining file, so build
    // one.
    let def_uri = if def_path == path {
      uri.to_string()
    } else {
      path_to_uri(&def_path)
    };
    let range = serde_json::to_value(location_to_json_range(sym.location.as_ref())).ok()?;
    Some(serde_json::json!({ "uri": def_uri, "range": range }))
  })();
  send_response(writer, Some(id), result.unwrap_or(serde_json::Value::Null))
}

fn symbol_kind_to_lsp_number(kind: monad_core::SymbolKind) -> u8 {
  // LSP `SymbolKind` numeric values (subset actually used here).
  use monad_core::SymbolKind::*;
  match kind {
    Function => 12,
    Struct => 23,
    Class => 5,
    Enum => 10,
    // No exact LSP counterpart for "type class instance" — Interface is
    // the closest existing concept (a set of methods a type provides).
    Instance => 11,
  }
}

fn document_symbol(
  documents: &HashMap<String, Document>,
  writer: &mut impl Write,
  id: Option<serde_json::Value>,
  params: &serde_json::Value,
  mote_path: &[PathBuf],
) -> Result<(), String> {
  let Some(id) = id else {
    return Ok(());
  };
  let symbols = (|| -> Option<Vec<SymbolInfo>> {
    let uri = text_document_uri(params)?;
    let doc = documents.get(uri)?;
    let path = uri_to_path(uri)?;
    symbols_from_source(&path, &doc.text, mote_path.to_vec()).ok()
  })()
  .unwrap_or_default();

  let items: Vec<serde_json::Value> = symbols
    .iter()
    .map(|s| {
      let range = serde_json::to_value(location_to_json_range(s.location.as_ref()))
        .unwrap_or(serde_json::Value::Null);
      serde_json::json!({
        "name": s.name,
        "kind": symbol_kind_to_lsp_number(s.kind),
        "range": range,
        "selectionRange": range,
      })
    })
    .collect();
  send_response(writer, Some(id), serde_json::Value::Array(items))
}

/// `workspace/symbol` — symbol search across the whole resolved
/// workspace (project `src/` + every dependency mote's `src/`, same
/// directories `mote_path` already resolves), unlike `document_symbol`
/// above which is scoped to one open buffer. Operates on-disk (via
/// `symbols_for_files`), not the in-memory `documents` map, since a
/// workspace symbol can live in a file that isn't even open in the
/// editor. No caching — see `resolve_symbol`'s doc comment for why
/// that's an accepted v1 tradeoff here too.
fn workspace_symbol(
  writer: &mut impl Write,
  id: Option<serde_json::Value>,
  params: &serde_json::Value,
  mote_path: &[PathBuf],
) -> Result<(), String> {
  let Some(id) = id else {
    return Ok(());
  };
  let query = params
    .get("query")
    .and_then(|q| q.as_str())
    .unwrap_or("")
    .to_lowercase();
  let results = symbols_for_files(mote_path.to_vec(), mote_path.to_vec()).unwrap_or_default();
  let items: Vec<serde_json::Value> = results
    .iter()
    .flat_map(|r| {
      let uri = path_to_uri(&r.path);
      r.symbols
        .iter()
        .filter(|s| query.is_empty() || s.name.to_lowercase().contains(&query))
        .map(move |s| {
          let range = serde_json::to_value(location_to_json_range(s.location.as_ref()))
            .unwrap_or(serde_json::Value::Null);
          serde_json::json!({
            "name": s.name,
            "kind": symbol_kind_to_lsp_number(s.kind),
            "location": { "uri": uri, "range": range },
          })
        })
    })
    .collect();
  send_response(writer, Some(id), serde_json::Value::Array(items))
}

// --- organize-imports codemod --------------------------------------------
//
// Shared by both entry points below (the `source.organizeImports` code
// action and the `monad.organizeImports` command) so they can't drift on
// what "organize this document's imports" computes — same
// `organize_imports_for_source` the `monad-rs organize-imports` CLI
// subcommand uses.

/// A `WorkspaceEdit` (LSP shape: `{changes: {uri: TextEdit[]}}`) for
/// organizing `uri`'s current buffer content, or `None` if there's
/// nothing to change (file already fully converted, or doesn't
/// parse/type-check — same "nothing sound to compute" case
/// `organize_imports_for_source` itself treats as zero edits).
fn organize_imports_workspace_edit(
  uri: &str,
  text: &str,
  path: &std::path::Path,
  mote_path: &[PathBuf],
) -> Option<serde_json::Value> {
  let edits = organize_imports_for_source(path, text, mote_path.to_vec()).ok()?;
  if edits.is_empty() {
    return None;
  }
  let lsp_edits: Vec<serde_json::Value> = edits
    .iter()
    .map(|e| {
      let range = serde_json::to_value(location_to_json_range(Some(&e.range)))
        .unwrap_or(serde_json::Value::Null);
      serde_json::json!({ "range": range, "newText": e.replacement })
    })
    .collect();
  Some(serde_json::json!({ "changes": { uri: lsp_edits } }))
}

/// `textDocument/codeAction` — offers "Organize Imports" as a
/// `source.organizeImports`-kind action with the `WorkspaceEdit` embedded
/// directly (the client applies it locally; no server round-trip needed),
/// so editors with a "organize imports" keybinding/lightbulb entry
/// (VS Code's `editor.action.organizeImports` looks for exactly this
/// action kind) pick it up automatically.
fn code_action(
  documents: &HashMap<String, Document>,
  writer: &mut impl Write,
  id: Option<serde_json::Value>,
  params: &serde_json::Value,
  mote_path: &[PathBuf],
) -> Result<(), String> {
  let Some(id) = id else {
    return Ok(());
  };
  let actions = (|| -> Option<Vec<serde_json::Value>> {
    let uri = text_document_uri(params)?;
    let doc = documents.get(uri)?;
    let path = uri_to_path(uri)?;
    let edit = organize_imports_workspace_edit(uri, &doc.text, &path, mote_path)?;
    Some(vec![serde_json::json!({
      "title": "Organize Imports",
      "kind": "source.organizeImports",
      "edit": edit,
    })])
  })()
  .unwrap_or_default();
  send_response(writer, Some(id), serde_json::Value::Array(actions))
}

/// `workspace/executeCommand` — the same fix as `code_action`, but
/// reachable as a directly-invokable named command (e.g. bound to a
/// keybinding or run from a command palette) rather than only surfacing
/// through the code-action lightbulb. Since a server can't write to the
/// client's buffer itself, it pushes the edit via a server-initiated
/// `workspace/applyEdit` request instead of returning it in the response.
fn execute_command(
  documents: &HashMap<String, Document>,
  writer: &mut impl Write,
  id: Option<serde_json::Value>,
  params: &serde_json::Value,
  mote_path: &[PathBuf],
  next_request_id: &mut u64,
) -> Result<(), String> {
  let command = params.get("command").and_then(|c| c.as_str()).unwrap_or("");
  if command == ORGANIZE_IMPORTS_COMMAND {
    // Accept either `["uri-string", ...]` or `[{"uri": "..."}, ...]` as
    // `arguments` — clients vary in which shape they pass through.
    let uri = params
      .get("arguments")
      .and_then(|a| a.as_array())
      .and_then(|arr| arr.first())
      .and_then(|first| {
        first
          .as_str()
          .or_else(|| first.get("uri").and_then(|u| u.as_str()))
      });
    if let Some(uri) = uri
      && let Some(doc) = documents.get(uri)
      && let Some(path) = uri_to_path(uri)
      && let Some(edit) = organize_imports_workspace_edit(uri, &doc.text, &path, mote_path)
    {
      let req_id = *next_request_id;
      *next_request_id += 1;
      send_request(
        writer,
        req_id,
        "workspace/applyEdit",
        serde_json::json!({ "label": "Organize Imports", "edit": edit }),
      )?;
    }
  }
  if let Some(id) = id {
    send_response(writer, Some(id), serde_json::Value::Null)?;
  }
  Ok(())
}

#[cfg(test)]
mod test {
  use super::*;

  #[test]
  fn test_initialize_advertises_organize_imports() {
    let caps = initialize_result();
    let kinds = caps["capabilities"]["codeActionProvider"]["codeActionKinds"]
      .as_array()
      .expect("codeActionKinds should be an array");
    assert!(kinds.iter().any(|k| k == "source.organizeImports"));
    let commands = caps["capabilities"]["executeCommandProvider"]["commands"]
      .as_array()
      .expect("commands should be an array");
    assert!(commands.iter().any(|c| c == ORGANIZE_IMPORTS_COMMAND));
  }

  #[test]
  fn test_organize_imports_workspace_edit_for_bare_open() {
    let uri = "file:///tmp/monad-lsp-test-bare-open.mo";
    let path = uri_to_path(uri).unwrap();
    let text = "open IO\n\ndef x : I64 := 1\n";
    let edit = organize_imports_workspace_edit(uri, text, &path, &[])
      .expect("bare `open IO` should produce an edit");
    let changes = &edit["changes"][uri];
    let edits = changes.as_array().expect("changes should be an array");
    assert_eq!(edits.len(), 1);
    assert_eq!(edits[0]["newText"], "open IO {}");
    assert_eq!(edits[0]["range"]["start"]["line"], 0);
    assert_eq!(edits[0]["range"]["start"]["character"], 0);
  }

  #[test]
  fn test_organize_imports_workspace_edit_none_when_already_explicit() {
    let uri = "file:///tmp/monad-lsp-test-explicit.mo";
    let path = uri_to_path(uri).unwrap();
    let text = "open IO {}\n\ndef x : I64 := 1\n";
    assert!(organize_imports_workspace_edit(uri, text, &path, &[]).is_none());
  }

  #[test]
  fn test_organize_imports_workspace_edit_none_on_parse_error() {
    let uri = "file:///tmp/monad-lsp-test-broken.mo";
    let path = uri_to_path(uri).unwrap();
    let text = "def x : I64 := \n"; // incomplete, doesn't parse
    assert!(organize_imports_workspace_edit(uri, text, &path, &[]).is_none());
  }

  #[test]
  fn test_code_action_response_shape() {
    let uri = "file:///tmp/monad-lsp-test-codeaction.mo";
    let mut documents = HashMap::new();
    documents.insert(
      uri.to_string(),
      Document {
        text: "open IO\n\ndef x : I64 := 1\n".to_string(),
      },
    );
    let params = serde_json::json!({
      "textDocument": { "uri": uri },
      "range": { "start": { "line": 0, "character": 0 }, "end": { "line": 0, "character": 0 } },
      "context": { "diagnostics": [] },
    });
    let mut buf: Vec<u8> = Vec::new();
    code_action(
      &documents,
      &mut buf,
      Some(serde_json::json!(1)),
      &params,
      &[],
    )
    .unwrap();
    let response = parse_single_message(&buf);
    let actions = response["result"].as_array().expect("result is an array");
    assert_eq!(actions.len(), 1);
    assert_eq!(actions[0]["kind"], "source.organizeImports");
    assert!(actions[0]["edit"]["changes"][uri].is_array());
  }

  #[test]
  fn test_execute_command_sends_apply_edit_request() {
    let uri = "file:///tmp/monad-lsp-test-execcommand.mo";
    let mut documents = HashMap::new();
    documents.insert(
      uri.to_string(),
      Document {
        text: "open IO\n\ndef x : I64 := 1\n".to_string(),
      },
    );
    let params = serde_json::json!({
      "command": ORGANIZE_IMPORTS_COMMAND,
      "arguments": [uri],
    });
    let mut buf: Vec<u8> = Vec::new();
    let mut next_id = 1u64;
    execute_command(
      &documents,
      &mut buf,
      Some(serde_json::json!(7)),
      &params,
      &[],
      &mut next_id,
    )
    .unwrap();
    let messages = parse_all_messages(&buf);
    assert_eq!(messages.len(), 2);
    // First: the server-initiated `workspace/applyEdit` request.
    assert_eq!(messages[0]["method"], "workspace/applyEdit");
    assert!(messages[0]["params"]["edit"]["changes"][uri].is_array());
    // Second: the response to the original executeCommand request.
    assert_eq!(messages[1]["id"], 7);
    assert_eq!(next_id, 2); // request id counter advanced
  }

  // --- workspace/symbol, workspace/diagnoseWorkspace, cross-mote hover/
  // definition ---------------------------------------------------------
  //
  // Same 2-mote fixture shape as `mcp::test`'s equivalent tests: `dir_a`'s
  // file defines a symbol, `dir_b`'s file imports it via `use`. Built at
  // test time under unique tmp dirs per test (parallel test threads, so
  // no path can be shared across tests).

  #[test]
  fn test_workspace_symbol_finds_symbol_across_mote_dirs() {
    let dir_a = "/tmp/monad-lsp-test-ws-symbol-a";
    let dir_b = "/tmp/monad-lsp-test-ws-symbol-b";
    std::fs::create_dir_all(dir_a).unwrap();
    std::fs::create_dir_all(dir_b).unwrap();
    std::fs::write(format!("{dir_a}/one.mo"), "def alpha : I64 := 1\n").unwrap();
    std::fs::write(format!("{dir_b}/two.mo"), "def beta : I64 := 2\n").unwrap();
    let mote_path = [PathBuf::from(dir_a), PathBuf::from(dir_b)];
    let params = serde_json::json!({ "query": "alph" });
    let mut buf: Vec<u8> = Vec::new();
    workspace_symbol(&mut buf, Some(serde_json::json!(1)), &params, &mote_path).unwrap();
    let response = parse_single_message(&buf);
    let items = response["result"].as_array().unwrap();
    assert_eq!(items.len(), 1);
    assert_eq!(items[0]["name"], "alpha");
  }

  #[test]
  fn test_workspace_symbol_empty_query_returns_all() {
    let dir_a = "/tmp/monad-lsp-test-ws-symbol-all-a";
    std::fs::create_dir_all(dir_a).unwrap();
    std::fs::write(
      format!("{dir_a}/one.mo"),
      "def alpha : I64 := 1\ndef gamma : I64 := 2\n",
    )
    .unwrap();
    let mote_path = [PathBuf::from(dir_a)];
    let mut buf: Vec<u8> = Vec::new();
    workspace_symbol(
      &mut buf,
      Some(serde_json::json!(1)),
      &serde_json::json!({}),
      &mote_path,
    )
    .unwrap();
    let response = parse_single_message(&buf);
    let items = response["result"].as_array().unwrap();
    assert_eq!(items.len(), 2);
  }

  #[test]
  fn test_diagnose_workspace_publishes_diagnostics_per_file() {
    let dir_a = "/tmp/monad-lsp-test-ws-diag-a";
    let dir_b = "/tmp/monad-lsp-test-ws-diag-b";
    std::fs::create_dir_all(dir_a).unwrap();
    std::fs::create_dir_all(dir_b).unwrap();
    std::fs::write(format!("{dir_a}/ok.mo"), "def x : I64 := 1\n").unwrap();
    std::fs::write(format!("{dir_b}/bad.mo"), "def y : I64 := \"nope\"\n").unwrap();
    let mote_path = [PathBuf::from(dir_a), PathBuf::from(dir_b)];
    let mut buf: Vec<u8> = Vec::new();
    diagnose_workspace(&mut buf, &mote_path).unwrap();
    let messages = parse_all_messages(&buf);
    assert_eq!(messages.len(), 2);
    for m in &messages {
      assert_eq!(m["method"], "textDocument/publishDiagnostics");
    }
    let has_error = messages.iter().any(|m| {
      m["params"]["diagnostics"]
        .as_array()
        .unwrap()
        .iter()
        .any(|d| d["severity"] == 1)
    });
    assert!(
      has_error,
      "expected at least one error diagnostic among published files"
    );
  }

  /// Writes the `dir_a`-defines/`dir_b`-imports fixture and the `consumer`
  /// document's params, ready for `hover`/`definition`.
  fn cross_mote_fixture(
    dir_a: &str,
    dir_b: &str,
  ) -> ([PathBuf; 2], HashMap<String, Document>, serde_json::Value) {
    std::fs::create_dir_all(dir_a).unwrap();
    std::fs::create_dir_all(dir_b).unwrap();
    std::fs::write(format!("{dir_a}/wsdep.mo"), "def shared_val : I64 := 99\n").unwrap();
    let consumer_uri = format!("file://{dir_b}/consumer.mo");
    let mut documents = HashMap::new();
    documents.insert(
      consumer_uri.clone(),
      Document {
        text: "use wsdep {shared_val}\n\ndef use_it : I64 := shared_val\n".to_string(),
      },
    );
    let params = serde_json::json!({
      "textDocument": { "uri": consumer_uri },
      "position": { "line": 2, "character": 24 },
    });
    (
      [PathBuf::from(dir_a), PathBuf::from(dir_b)],
      documents,
      params,
    )
  }

  #[test]
  fn test_hover_resolves_cross_file_symbol() {
    let (mote_path, documents, params) = cross_mote_fixture(
      "/tmp/monad-lsp-test-ws-hover-a",
      "/tmp/monad-lsp-test-ws-hover-b",
    );
    let mut buf: Vec<u8> = Vec::new();
    hover(
      &documents,
      &mut buf,
      Some(serde_json::json!(1)),
      &params,
      &mote_path,
    )
    .unwrap();
    let response = parse_single_message(&buf);
    let contents = response["result"]["contents"]["value"].as_str().unwrap();
    assert!(contents.contains("I64")); // shared_val's type
  }

  #[test]
  fn test_definition_resolves_cross_file_symbol_and_uses_defining_file_uri() {
    let (mote_path, documents, params) = cross_mote_fixture(
      "/tmp/monad-lsp-test-ws-def-a",
      "/tmp/monad-lsp-test-ws-def-b",
    );
    let mut buf: Vec<u8> = Vec::new();
    definition(
      &documents,
      &mut buf,
      Some(serde_json::json!(1)),
      &params,
      &mote_path,
    )
    .unwrap();
    let response = parse_single_message(&buf);
    let uri = response["result"]["uri"].as_str().unwrap();
    assert!(
      uri.ends_with("wsdep.mo"),
      "expected definition to point into wsdep.mo (the defining file), got {uri}"
    );
    assert!(!uri.contains("consumer.mo"));
  }

  /// Parse the single `Content-Length`-framed message written to `buf`.
  fn parse_single_message(buf: &[u8]) -> serde_json::Value {
    parse_all_messages(buf).into_iter().next().unwrap()
  }

  /// Parse every `Content-Length`-framed message concatenated in `buf`,
  /// in write order.
  fn parse_all_messages(buf: &[u8]) -> Vec<serde_json::Value> {
    let mut out = Vec::new();
    let mut rest = buf;
    loop {
      let text = std::str::from_utf8(rest).unwrap();
      let Some(header_end) = text.find("\r\n\r\n") else {
        break;
      };
      let header = &text[..header_end];
      let len: usize = header
        .lines()
        .find_map(|l| l.strip_prefix("Content-Length: "))
        .unwrap()
        .trim()
        .parse()
        .unwrap();
      let body_start = header_end + 4;
      let body = &text[body_start..body_start + len];
      out.push(serde_json::from_str(body).unwrap());
      rest = &rest[body_start + len..];
      if rest.is_empty() {
        break;
      }
    }
    out
  }
}

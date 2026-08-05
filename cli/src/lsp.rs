//! Minimal stdio JSON-RPC LSP server — diagnostics + navigation only
//! (`hover`, `definition`, `documentSymbol`), matching the plan's phase
//! ordering ("ship diagnostics + navigation first"). Completions, rename,
//! semantic tokens, and code actions need error-tolerant parsing (the
//! parser stops at the first syntax error; no recovery/partial-AST
//! support yet) — explicitly out of scope here, not an oversight, and
//! the server's own advertised `capabilities` only claim what's actually
//! implemented.
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
//! Diagnostics/hover/definition/documentSymbol all operate on the
//! editor's in-memory buffer (`Document.text`, updated on every
//! `didChange`), not what's saved on disk — via `monad_core::check_source`/
//! `symbols_from_source`, the same single-source entry points `core`
//! exposes specifically for this.

use std::collections::HashMap;
use std::io::{self, BufRead, BufReader, Write};
use std::path::PathBuf;

use monad_core::{SymbolInfo, check_source, diag::Severity, symbols_from_source};

use crate::{find_symbol_by_name, identifier_at, location_to_json_range, symbol_kind_label};

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
    let method = msg.get("method").and_then(|m| m.as_str()).unwrap_or("");
    let params = msg
      .get("params")
      .cloned()
      .unwrap_or(serde_json::Value::Null);

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

fn initialize_result() -> serde_json::Value {
  serde_json::json!({
    "capabilities": {
      "textDocumentSync": 1, // Full
      "hoverProvider": true,
      "definitionProvider": true,
      "documentSymbolProvider": true
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
    let sym = find_symbol_by_name(&symbols, &name)?;
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
    let sym = find_symbol_by_name(&symbols, &name)?;
    let range = serde_json::to_value(location_to_json_range(sym.location.as_ref())).ok()?;
    Some(serde_json::json!({ "uri": uri, "range": range }))
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

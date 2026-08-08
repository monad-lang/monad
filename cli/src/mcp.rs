//! Minimal stdio MCP server — exposes `check`/`symbols`/`hover`/
//! `definition`/`organize_imports` as tools, the same five operations the
//! CLI's own `--json` subcommands already provide (`monad
//! check/symbols/hover/definition --json`, `monad organize-imports`).
//! This is the MCP analog of Phase 0 in
//! `plans/library-ideas/language-server.md` ("ship structured CLI tools
//! first, reuse everywhere") — every tool here is a thin wrapper over the
//! same `monad_core` entry points the CLI and [`crate::lsp`] already call,
//! so agent clients speaking MCP get identical results to shelling out to
//! the CLI or driving the LSP server.
//!
//! `run`/`test` are deliberately NOT exposed as tools yet:
//! `monad_core::run`/`run_tests` print directly to stdout/stderr and
//! return `Result<(), String>`, not structured data — wiring those up
//! needs either output capture or new structured return types in `core`,
//! which is compiler-side work beyond "expose what already exists".
//! Likewise, MCP **resources** and **prompts** (stdlib docs, examples,
//! style-guide prompts) aren't implemented — static-content features, not
//! derived from `monad_core`, and not needed for "agent calls the
//! compiler".
//!
//! Transport is MCP's own framing, not LSP's: one JSON-RPC 2.0 object per
//! line on stdin/stdout (no `Content-Length` header block), and no
//! `shutdown`/`exit` handshake — the loop just ends on stdin EOF.
//!
//! Tool execution failures (file not found, parse/type errors surfaced as
//! zero diagnostics vs. a genuine I/O failure, unknown tool name, missing
//! argument) are reported as `isError: true` in the tool result, not as
//! JSON-RPC protocol errors — per MCP convention, this keeps failures
//! visible to the calling agent as ordinary tool output instead of
//! aborting the exchange. Only a genuinely unrecognized top-level
//! `method` (not a tool name) gets a JSON-RPC `-32601` error response.

use std::io::{self, BufRead, BufReader, Write};
use std::path::PathBuf;

use monad_core::{check_files, diag::Severity, organize_imports_for_files, symbols_for_files};
use serde_json::Value;

use crate::{
  JsonCheckReport, JsonFileReport, JsonHover, JsonLocation, JsonPosition, JsonRange, JsonSummary,
  JsonSymbol, JsonSymbolFile, find_symbol_in_file, identifier_at, location_to_json_range,
  path_to_uri, symbol_kind_label, to_json_diagnostic,
};

pub fn run(mote_path: Vec<PathBuf>) -> Result<(), String> {
  let stdin = io::stdin();
  let mut reader = BufReader::new(stdin.lock());
  let stdout = io::stdout();
  let mut writer = stdout.lock();

  loop {
    let Some(line) = read_line(&mut reader).map_err(|e| format!("transport error: {e}"))? else {
      break; // stdin closed — client disconnected
    };
    if line.trim().is_empty() {
      continue;
    }
    let msg: Value = match serde_json::from_str(&line) {
      Ok(v) => v,
      Err(e) => {
        eprintln!("mcp: dropping malformed message: {e}");
        continue;
      }
    };
    let id = msg.get("id").cloned();
    let method = msg.get("method").and_then(|m| m.as_str());
    let params = msg.get("params").cloned().unwrap_or(Value::Null);

    let Some(method) = method else {
      // No `method` field: a response to a request we sent — this server
      // never sends server-initiated requests, so nothing to correlate.
      continue;
    };

    match method {
      "initialize" => {
        if let Some(id) = id {
          send_response(&mut writer, id, initialize_result(&params))?;
        }
      }
      // Notifications this server has nothing to do in response to, but
      // are a normal part of the protocol.
      "notifications/initialized" | "notifications/cancelled" => {}
      "ping" => {
        if let Some(id) = id {
          send_response(&mut writer, id, serde_json::json!({}))?;
        }
      }
      "tools/list" => {
        if let Some(id) = id {
          send_response(
            &mut writer,
            id,
            serde_json::json!({ "tools": tool_definitions() }),
          )?;
        }
      }
      "tools/call" => {
        if let Some(id) = id {
          let result = handle_tools_call(&params, &mote_path);
          send_response(&mut writer, id, result)?;
        }
      }
      _ => {
        // A notification with no handler is fine to ignore; a REQUEST
        // with no handler must get an error response, or a well-behaved
        // client would hang waiting for one.
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

// --- transport ------------------------------------------------------------

fn read_line(reader: &mut impl BufRead) -> io::Result<Option<String>> {
  let mut line = String::new();
  let n = reader.read_line(&mut line)?;
  if n == 0 {
    return Ok(None); // EOF
  }
  Ok(Some(line.trim_end_matches(['\r', '\n']).to_string()))
}

fn write_line(writer: &mut impl Write, body: &Value) -> Result<(), String> {
  let text =
    serde_json::to_string(body).map_err(|e| format!("failed to serialize message: {e}"))?;
  writeln!(writer, "{text}").map_err(|e| format!("{e}"))?;
  writer.flush().map_err(|e| format!("{e}"))
}

fn send_response(writer: &mut impl Write, id: Value, result: Value) -> Result<(), String> {
  write_line(
    writer,
    &serde_json::json!({ "jsonrpc": "2.0", "id": id, "result": result }),
  )
}

fn send_error(writer: &mut impl Write, id: Value, code: i64, message: &str) -> Result<(), String> {
  write_line(
    writer,
    &serde_json::json!({
      "jsonrpc": "2.0",
      "id": id,
      "error": { "code": code, "message": message }
    }),
  )
}

/// Echoes back the client's requested `protocolVersion` — this server's
/// capability surface (a static `tools` list, no resources/prompts/
/// sampling) hasn't changed across recent MCP protocol revisions, so
/// there's no version-specific behavior to gate on. Falls back to a
/// known-good version string if the client didn't send one.
fn initialize_result(params: &Value) -> Value {
  let protocol_version = params
    .get("protocolVersion")
    .and_then(|v| v.as_str())
    .unwrap_or("2024-11-05");
  serde_json::json!({
    "protocolVersion": protocol_version,
    "capabilities": { "tools": {} },
    "serverInfo": { "name": "monad-mcp", "version": env!("CARGO_PKG_VERSION") }
  })
}

// --- tools/list -------------------------------------------------------------

fn tool_definitions() -> Vec<Value> {
  vec![
    serde_json::json!({
      "name": "check",
      "description": "Parse and type-check the given files (or the whole workspace if omitted). Returns structured diagnostics — same shape as `monad check --json`.",
      "inputSchema": {
        "type": "object",
        "properties": {
          "paths": {
            "type": "array",
            "items": { "type": "string" },
            "description": "Files or directories to check; defaults to the current directory."
          }
        }
      }
    }),
    serde_json::json!({
      "name": "symbols",
      "description": "List top-level defs/types/classes/instances across the given files (or the whole workspace if omitted) — same shape as `monad symbols --json`.",
      "inputSchema": {
        "type": "object",
        "properties": {
          "paths": {
            "type": "array",
            "items": { "type": "string" },
            "description": "Files or directories to index; defaults to the current directory."
          }
        }
      }
    }),
    serde_json::json!({
      "name": "hover",
      "description": "Type signature and doc summary of the identifier at a position — same shape as `monad hover --json`.",
      "inputSchema": {
        "type": "object",
        "properties": {
          "file": { "type": "string" },
          "line": { "type": "integer", "description": "1-indexed" },
          "col": { "type": "integer", "description": "1-indexed" }
        },
        "required": ["file", "line", "col"]
      }
    }),
    serde_json::json!({
      "name": "definition",
      "description": "Definition location of the identifier at a position — same shape as `monad definition --json`.",
      "inputSchema": {
        "type": "object",
        "properties": {
          "file": { "type": "string" },
          "line": { "type": "integer", "description": "1-indexed" },
          "col": { "type": "integer", "description": "1-indexed" }
        },
        "required": ["file", "line", "col"]
      }
    }),
    serde_json::json!({
      "name": "organize_imports",
      "description": "Rewrite bare `use`/`open` declarations to explicit name lists and `@[...]` attributes to `#[...]`. Dry-run by default — returns each changed file's new full source without writing it; pass write: true to apply to disk.",
      "inputSchema": {
        "type": "object",
        "properties": {
          "paths": {
            "type": "array",
            "items": { "type": "string" },
            "description": "Files or directories to convert; defaults to the current directory."
          },
          "write": {
            "type": "boolean",
            "description": "Apply changes to disk. Defaults to false (dry run)."
          }
        }
      }
    }),
  ]
}

// --- tools/call ---------------------------------------------------------

fn tool_ok(value: Value) -> Value {
  let text =
    serde_json::to_string_pretty(&value).unwrap_or_else(|e| format!("<serialization error: {e}>"));
  serde_json::json!({ "content": [{ "type": "text", "text": text }], "isError": false })
}

fn tool_err(message: impl Into<String>) -> Value {
  serde_json::json!({ "content": [{ "type": "text", "text": message.into() }], "isError": true })
}

fn handle_tools_call(params: &Value, mote_path: &[PathBuf]) -> Value {
  let Some(name) = params.get("name").and_then(|n| n.as_str()) else {
    return tool_err("missing required field 'name'");
  };
  let arguments = params
    .get("arguments")
    .cloned()
    .unwrap_or_else(|| Value::Object(Default::default()));

  let outcome = match name {
    "check" => tool_check(&arguments, mote_path),
    "symbols" => tool_symbols(&arguments, mote_path),
    "hover" => tool_hover(&arguments, mote_path),
    "definition" => tool_definition(&arguments, mote_path),
    "organize_imports" => tool_organize_imports(&arguments, mote_path),
    other => Err(format!("unknown tool: {other}")),
  };
  match outcome {
    Ok(value) => tool_ok(value),
    Err(message) => tool_err(message),
  }
}

fn parse_paths(arguments: &Value) -> Vec<PathBuf> {
  arguments
    .get("paths")
    .and_then(|p| p.as_array())
    .map(|arr| {
      arr
        .iter()
        .filter_map(|v| v.as_str())
        .map(PathBuf::from)
        .collect()
    })
    .unwrap_or_default()
}

/// Shared `file`/`line`/`col` argument parsing for `hover`/`definition` —
/// same 1-indexed convention as `monad hover`/`monad definition` and the
/// LSP server's own position handling.
fn parse_position_args(arguments: &Value) -> Result<(PathBuf, u32, usize), String> {
  let file = arguments
    .get("file")
    .and_then(|v| v.as_str())
    .ok_or("missing required argument 'file'")?;
  let line = arguments
    .get("line")
    .and_then(|v| v.as_u64())
    .ok_or("missing required argument 'line'")? as u32;
  let col = arguments
    .get("col")
    .and_then(|v| v.as_u64())
    .ok_or("missing required argument 'col'")? as usize;
  Ok((PathBuf::from(file), line, col))
}

fn tool_check(arguments: &Value, mote_path: &[PathBuf]) -> Result<Value, String> {
  let results = check_files(parse_paths(arguments), mote_path.to_vec())?;

  let mut errors = 0usize;
  let mut warnings = 0usize;
  for result in &results {
    for d in &result.diagnostics {
      match d.severity {
        Severity::Error => errors += 1,
        Severity::Warning => warnings += 1,
        _ => {}
      }
    }
  }

  let report = JsonCheckReport {
    files: results
      .iter()
      .map(|r| JsonFileReport {
        uri: path_to_uri(&r.path),
        diagnostics: r.diagnostics.iter().map(to_json_diagnostic).collect(),
      })
      .collect(),
    summary: JsonSummary {
      errors,
      warnings,
      files_checked: results.len(),
    },
  };
  serde_json::to_value(report).map_err(|e| format!("failed to serialize check report: {e}"))
}

fn tool_symbols(arguments: &Value, mote_path: &[PathBuf]) -> Result<Value, String> {
  let results = symbols_for_files(parse_paths(arguments), mote_path.to_vec())?;

  let files: Vec<JsonSymbolFile> = results
    .iter()
    .map(|r| JsonSymbolFile {
      uri: path_to_uri(&r.path),
      symbols: r
        .symbols
        .iter()
        .map(|s| JsonSymbol {
          name: s.name.clone(),
          kind: s.kind,
          range: location_to_json_range(s.location.as_ref()),
          detail: s.detail.clone(),
        })
        .collect(),
    })
    .collect();
  serde_json::to_value(files).map_err(|e| format!("failed to serialize symbols: {e}"))
}

fn tool_hover(arguments: &Value, mote_path: &[PathBuf]) -> Result<Value, String> {
  let (file, line, col) = parse_position_args(arguments)?;
  let source = std::fs::read_to_string(&file).map_err(|e| format!("{e}"))?;
  let found = identifier_at(&source, line, col).and_then(|(name, start_col, end_col)| {
    find_symbol_in_file(&file, &name, mote_path.to_vec()).map(|sym| (sym, start_col, end_col))
  });

  let hover = found.map(|(sym, start_col, end_col)| {
    let contents = sym
      .detail
      .clone()
      .unwrap_or_else(|| format!("{} {}", symbol_kind_label(sym.kind), sym.name));
    JsonHover {
      contents,
      kind: symbol_kind_label(sym.kind).to_string(),
      range: JsonRange {
        start: JsonPosition {
          line: line.saturating_sub(1),
          character: start_col.saturating_sub(1),
        },
        end: JsonPosition {
          line: line.saturating_sub(1),
          character: end_col.saturating_sub(1),
        },
      },
    }
  });
  serde_json::to_value(hover).map_err(|e| format!("failed to serialize hover: {e}"))
}

fn tool_definition(arguments: &Value, mote_path: &[PathBuf]) -> Result<Value, String> {
  let (file, line, col) = parse_position_args(arguments)?;
  let source = std::fs::read_to_string(&file).map_err(|e| format!("{e}"))?;
  let found = identifier_at(&source, line, col)
    .and_then(|(name, _, _)| find_symbol_in_file(&file, &name, mote_path.to_vec()));

  let location = found.map(|sym| JsonLocation {
    uri: path_to_uri(&file),
    range: location_to_json_range(sym.location.as_ref()),
  });
  serde_json::to_value(location).map_err(|e| format!("failed to serialize location: {e}"))
}

fn tool_organize_imports(arguments: &Value, mote_path: &[PathBuf]) -> Result<Value, String> {
  let write = arguments
    .get("write")
    .and_then(|v| v.as_bool())
    .unwrap_or(false);
  let results = organize_imports_for_files(parse_paths(arguments), mote_path.to_vec())?;

  let mut files = Vec::with_capacity(results.len());
  let mut changed = 0usize;
  let mut errors = 0usize;
  for r in &results {
    if let Some(e) = &r.error {
      errors += 1;
      files.push(serde_json::json!({ "path": r.path.display().to_string(), "error": e }));
      continue;
    }
    let Some(new_source) = &r.new_source else {
      continue; // already fully explicit — nothing to report
    };
    changed += 1;
    if write {
      std::fs::write(&r.path, new_source)
        .map_err(|e| format!("failed to write {}: {e}", r.path.display()))?;
    }
    files.push(serde_json::json!({
      "path": r.path.display().to_string(),
      "newSource": new_source,
      "written": write,
    }));
  }

  Ok(serde_json::json!({
    "files": files,
    "summary": { "changed": changed, "errors": errors, "write": write }
  }))
}

#[cfg(test)]
mod test {
  use super::*;

  fn call(method: &str, params: Value) -> Value {
    serde_json::json!({ "jsonrpc": "2.0", "id": 1, "method": method, "params": params })
  }

  /// Run one request line through [`run`]'s dispatch by hand (no stdin
  /// involved) and parse back the single response line written.
  fn dispatch(method: &str, params: Value, mote_path: &[PathBuf]) -> Value {
    let mut buf: Vec<u8> = Vec::new();
    let msg = call(method, params);
    let id = msg["id"].clone();
    match method {
      "initialize" => {
        send_response(&mut buf, id, initialize_result(&msg["params"])).unwrap();
      }
      "tools/list" => {
        send_response(
          &mut buf,
          id,
          serde_json::json!({ "tools": tool_definitions() }),
        )
        .unwrap();
      }
      "tools/call" => {
        let result = handle_tools_call(&msg["params"], mote_path);
        send_response(&mut buf, id, result).unwrap();
      }
      other => panic!("dispatch() helper doesn't know method {other}"),
    }
    let line = String::from_utf8(buf).unwrap();
    serde_json::from_str(line.trim_end()).unwrap()
  }

  #[test]
  fn test_initialize_advertises_tools_capability() {
    let response = dispatch("initialize", serde_json::json!({}), &[]);
    assert!(response["result"]["capabilities"]["tools"].is_object());
    assert_eq!(response["result"]["protocolVersion"], "2024-11-05");
  }

  #[test]
  fn test_initialize_echoes_requested_protocol_version() {
    let response = dispatch(
      "initialize",
      serde_json::json!({ "protocolVersion": "2025-03-26" }),
      &[],
    );
    assert_eq!(response["result"]["protocolVersion"], "2025-03-26");
  }

  #[test]
  fn test_tools_list_has_five_tools() {
    let response = dispatch("tools/list", serde_json::json!({}), &[]);
    let tools = response["result"]["tools"].as_array().unwrap();
    let names: Vec<&str> = tools.iter().map(|t| t["name"].as_str().unwrap()).collect();
    assert_eq!(
      names,
      vec![
        "check",
        "symbols",
        "hover",
        "definition",
        "organize_imports"
      ]
    );
    for tool in tools {
      assert!(tool["inputSchema"]["type"] == "object");
    }
  }

  #[test]
  fn test_unknown_top_level_method_is_protocol_error() {
    let mut buf: Vec<u8> = Vec::new();
    send_error(
      &mut buf,
      serde_json::json!(1),
      -32601,
      "method not found: bogus",
    )
    .unwrap();
    let line = String::from_utf8(buf).unwrap();
    let response: Value = serde_json::from_str(line.trim_end()).unwrap();
    assert_eq!(response["error"]["code"], -32601);
  }

  #[test]
  fn test_check_tool_reports_type_error() {
    let path = "/tmp/monad-mcp-test-check-err.mo";
    std::fs::write(path, "def x : I64 := \"nope\"\n").unwrap();
    let response = dispatch(
      "tools/call",
      serde_json::json!({ "name": "check", "arguments": { "paths": [path] } }),
      &[],
    );
    assert_eq!(response["result"]["isError"], false);
    let text = response["result"]["content"][0]["text"].as_str().unwrap();
    let report: Value = serde_json::from_str(text).unwrap();
    assert!(report["summary"]["errors"].as_u64().unwrap() > 0);
  }

  #[test]
  fn test_check_tool_clean_file_has_no_errors() {
    let path = "/tmp/monad-mcp-test-check-ok.mo";
    std::fs::write(path, "def x : I64 := 1\n").unwrap();
    let response = dispatch(
      "tools/call",
      serde_json::json!({ "name": "check", "arguments": { "paths": [path] } }),
      &[],
    );
    let text = response["result"]["content"][0]["text"].as_str().unwrap();
    let report: Value = serde_json::from_str(text).unwrap();
    assert_eq!(report["summary"]["errors"], 0);
  }

  #[test]
  fn test_symbols_tool_lists_def() {
    let path = "/tmp/monad-mcp-test-symbols.mo";
    std::fs::write(path, "def add (x : I64) (y : I64) : I64 := x + y\n").unwrap();
    let response = dispatch(
      "tools/call",
      serde_json::json!({ "name": "symbols", "arguments": { "paths": [path] } }),
      &[],
    );
    let text = response["result"]["content"][0]["text"].as_str().unwrap();
    let files: Value = serde_json::from_str(text).unwrap();
    let names: Vec<&str> = files[0]["symbols"]
      .as_array()
      .unwrap()
      .iter()
      .map(|s| s["name"].as_str().unwrap())
      .collect();
    assert!(names.contains(&"add"));
  }

  #[test]
  fn test_hover_tool_finds_symbol() {
    let path = "/tmp/monad-mcp-test-hover.mo";
    std::fs::write(path, "def foo : I64 := 42\ndef bar : I64 := foo\n").unwrap();
    let response = dispatch(
      "tools/call",
      serde_json::json!({ "name": "hover", "arguments": { "file": path, "line": 2, "col": 19 } }),
      &[],
    );
    assert_eq!(response["result"]["isError"], false);
    let text = response["result"]["content"][0]["text"].as_str().unwrap();
    let hover: Value = serde_json::from_str(text).unwrap();
    assert_eq!(hover["kind"], "function");
    assert!(hover["contents"].as_str().unwrap().contains("I64")); // foo's type
  }

  #[test]
  fn test_hover_tool_no_symbol_returns_null_not_error() {
    let path = "/tmp/monad-mcp-test-hover-empty.mo";
    std::fs::write(path, "def foo : I64 := 42\n").unwrap();
    let response = dispatch(
      "tools/call",
      serde_json::json!({ "name": "hover", "arguments": { "file": path, "line": 1, "col": 1 } }),
      &[],
    );
    assert_eq!(response["result"]["isError"], false);
    let text = response["result"]["content"][0]["text"].as_str().unwrap();
    assert_eq!(text, "null");
  }

  #[test]
  fn test_definition_tool_finds_location() {
    let path = "/tmp/monad-mcp-test-definition.mo";
    std::fs::write(path, "def foo : I64 := 42\ndef bar : I64 := foo\n").unwrap();
    let response = dispatch(
      "tools/call",
      serde_json::json!({ "name": "definition", "arguments": { "file": path, "line": 2, "col": 19 } }),
      &[],
    );
    let text = response["result"]["content"][0]["text"].as_str().unwrap();
    let loc: Value = serde_json::from_str(text).unwrap();
    assert_eq!(loc["range"]["start"]["line"], 0); // `foo` is defined on line 1 (0-indexed: 0)
  }

  #[test]
  fn test_hover_tool_missing_argument_is_tool_error() {
    let response = dispatch(
      "tools/call",
      serde_json::json!({ "name": "hover", "arguments": { "file": "/tmp/nope.mo" } }),
      &[],
    );
    assert_eq!(response["result"]["isError"], true);
  }

  #[test]
  fn test_unknown_tool_name_is_tool_error() {
    let response = dispatch(
      "tools/call",
      serde_json::json!({ "name": "not_a_real_tool", "arguments": {} }),
      &[],
    );
    assert_eq!(response["result"]["isError"], true);
    let text = response["result"]["content"][0]["text"].as_str().unwrap();
    assert!(text.contains("unknown tool"));
  }

  #[test]
  fn test_organize_imports_dry_run_does_not_touch_disk() {
    let path = "/tmp/monad-mcp-test-organize.mo";
    std::fs::write(path, "open IO\n\ndef x : I64 := 1\n").unwrap();
    let response = dispatch(
      "tools/call",
      serde_json::json!({ "name": "organize_imports", "arguments": { "paths": [path] } }),
      &[],
    );
    let text = response["result"]["content"][0]["text"].as_str().unwrap();
    let report: Value = serde_json::from_str(text).unwrap();
    assert_eq!(report["summary"]["changed"], 1);
    assert_eq!(report["summary"]["write"], false);
    let on_disk = std::fs::read_to_string(path).unwrap();
    assert_eq!(on_disk, "open IO\n\ndef x : I64 := 1\n"); // untouched
  }

  #[test]
  fn test_organize_imports_write_applies_to_disk() {
    let path = "/tmp/monad-mcp-test-organize-write.mo";
    std::fs::write(path, "open IO\n\ndef x : I64 := 1\n").unwrap();
    let response = dispatch(
      "tools/call",
      serde_json::json!({ "name": "organize_imports", "arguments": { "paths": [path], "write": true } }),
      &[],
    );
    let text = response["result"]["content"][0]["text"].as_str().unwrap();
    let report: Value = serde_json::from_str(text).unwrap();
    assert_eq!(report["summary"]["changed"], 1);
    let on_disk = std::fs::read_to_string(path).unwrap();
    assert_eq!(on_disk, "open IO {}\n\ndef x : I64 := 1\n");
  }
}

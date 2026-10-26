/// The Monad-aware tools: `monad_check` against the compiler's checker
/// and `monad_eval`'s REPL buffer through the self-hosted interpreter.
/// Everything runs under /tmp (pure snippets need no imports).
use init::transformers {ResultT, ResultT.run}
use shuttle::tool {ToolImpl}
use shuttle::message_types {Content}
use weaver::monad_tools {MonadCheck.tool, MonadEval.tool}
use lang::module {ModuleInfoCache, module_info_cache_empty}
use std::ref {Ref}
use json::json {Json, Json.make_object, Json.make_str}
use std::map {Map, BTreeMap}
use std::path {Path}
use std::process {process_id}
use std::io {IO.read_file}

def source_input (s : String) : Json :=
    Json.make_object (Map.insert "source" (Json.make_str s) BTreeMap.empty)

def reset_input (s : String) : Json :=
    Json.make_object (Map.insert "source" (Json.make_str s)
        (Map.insert "reset" (Json.make_bool true) BTreeMap.empty))

def text_of (c : Content) : String :=
    match c {
        Content.tool_result _ out _ => out,
        _ => "",
    }

#[test]
def test_monad_check_clean_source : IO Bool := do {
    let cache <- Ref.new module_info_cache_empty;
    let t : ToolImpl := MonadCheck.tool cache (Option.some "/tmp");
    let run : String -> Json -> ResultT String IO Content := t.run;
    let r <- ResultT.run (run "call" (source_input "def main : I64 := 1 + 2"));
    match r {
        Result.err _ => IO.pure false,
        Result.ok c => IO.pure (String.contains (text_of c) "OK"),
    }
}

#[test]
def test_monad_check_reports_an_error : IO Bool := do {
    let cache <- Ref.new module_info_cache_empty;
    let t : ToolImpl := MonadCheck.tool cache (Option.some "/tmp");
    let run : String -> Json -> ResultT String IO Content := t.run;
    let r <- ResultT.run (run "call" (source_input "def main : I64 := nope"));
    match r {
        Result.err _ => IO.pure false,
        Result.ok c => IO.pure (String.contains (text_of c) "ERRORS"),
    }
}

#[test]
def test_monad_eval_expression : IO Bool := do {
    let cache <- Ref.new module_info_cache_empty;
    let empty_buf : List String := List.empty;
    let buf <- Ref.new empty_buf;
    let t : ToolImpl := MonadEval.tool buf cache (Option.some "/tmp");
    let run : String -> Json -> ResultT String IO Content := t.run;
    let r <- ResultT.run (run "call" (source_input "1 + 2"));
    match r {
        Result.err _ => IO.pure false,
        Result.ok c => IO.pure (String.beq (text_of c) "Eval result 3"),
    }
}

/// Definitions accumulate: a `def` snippet is accepted into the scratch
/// module, and a later expression can call it.
#[test]
def test_monad_eval_accumulates_definitions : IO Bool := do {
    let cache <- Ref.new module_info_cache_empty;
    let empty_buf : List String := List.empty;
    let buf <- Ref.new empty_buf;
    let t : ToolImpl := MonadEval.tool buf cache (Option.some "/tmp");
    let run : String -> Json -> ResultT String IO Content := t.run;
    let r1 <- ResultT.run (run "call" (source_input "def double (x : I64) : I64 := x + x"));
    let r2 <- ResultT.run (run "call" (source_input "double 21"));
    match r1 {
        Result.err _ => IO.pure false,
        Result.ok c1 =>
            if Bool.not (String.contains (text_of c1) "defined")
            then IO.pure false
            else match r2 {
                Result.err _ => IO.pure false,
                Result.ok c2 => IO.pure (String.beq (text_of c2) "Eval result 42"),
            },
    }
}

/// `reset` clears the buffer: a definition accepted before it is gone.
#[test]
def test_monad_eval_reset_clears_definitions : IO Bool := do {
    let cache <- Ref.new module_info_cache_empty;
    let empty_buf : List String := List.empty;
    let buf <- Ref.new empty_buf;
    let t : ToolImpl := MonadEval.tool buf cache (Option.some "/tmp");
    let run : String -> Json -> ResultT String IO Content := t.run;
    let _ <- ResultT.run (run "call" (source_input "def triple (x : I64) : I64 := x + x + x"));
    let _ <- ResultT.run (run "call" (reset_input "0"));
    let r <- ResultT.run (run "call" (source_input "triple 3"));
    match r {
        Result.err _ => IO.pure false,
        Result.ok c => IO.pure (String.starts_with "FAILED" (text_of c)),
    }
}

def is_error_of (c : Content) : Bool :=
    match c {
        Content.tool_result _ _ e => e,
        _ => true,
    }

/// A buffered definition whose result is not I64 must still type the
/// expression that uses it: the type probe carries the buffer, so
/// `String`/`Bool`/`Unit` results of accumulated definitions work.
#[test]
def test_monad_eval_uses_the_buffer_for_non_i64_expressions : IO Bool := do {
    let cache <- Ref.new module_info_cache_empty;
    let empty_buf : List String := List.empty;
    let buf <- Ref.new empty_buf;
    let t : ToolImpl := MonadEval.tool buf cache (Option.some "/tmp");
    let run : String -> Json -> ResultT String IO Content := t.run;
    let _ <- ResultT.run (run "call" (source_input "def greeting : String := \"hi\""));
    let r <- ResultT.run (run "call" (source_input "String.concat greeting \"!\""));
    match r {
        Result.err _ => IO.pure false,
        Result.ok c =>
            let text : String := text_of c in
            IO.pure (String.contains text "Eval result" && String.contains text "hi!" && Bool.not (is_error_of c)),
    }
}

/// `monad_check` is a `read` tool: a source buffer is checked under a
/// virtual path and no file is staged.
#[test]
def test_monad_check_writes_no_file : IO Bool := do {
    let cache <- Ref.new module_info_cache_empty;
    let t : ToolImpl := MonadCheck.tool cache (Option.some "/tmp");
    let run : String -> Json -> ResultT String IO Content := t.run;
    let _ <- ResultT.run (run "call" (source_input "def main : I64 := 1 + 2"));
    let vpath : String := String.concat "/tmp" (String.concat "/weaver_check_buffer_"
        (String.concat (I64.to_string process_id) ".mo"));
    let r <- IO.read_file (Path.path vpath);
    match r {
        Result.err _ => IO.pure true,
        Result.ok _ => IO.pure false,
    }
}

/// A failing eval is an error result (`is_error` comes from the
/// pipeline's Result, never from sniffing the text for FAILED).
#[test]
def test_monad_eval_failure_is_an_error : IO Bool := do {
    let cache <- Ref.new module_info_cache_empty;
    let empty_buf : List String := List.empty;
    let buf <- Ref.new empty_buf;
    let t : ToolImpl := MonadEval.tool buf cache (Option.some "/tmp");
    let run : String -> Json -> ResultT String IO Content := t.run;
    let r <- ResultT.run (run "call" (source_input "missing_thing"));
    match r {
        Result.err _ => IO.pure false,
        Result.ok c => IO.pure (is_error_of c),
    }
}

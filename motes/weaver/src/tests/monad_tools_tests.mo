/// The Monad-aware tools: `monad_check` and `monad_eval` over the `monad`
/// binary (`MonadTools.binary`), and the shaping of its output.
/// Everything runs under /tmp (pure snippets need no imports).
use init::transformers {ResultT, ResultT.run}
use shuttle::tool {ToolImpl}
use shuttle::message_types {Content}
use weaver::monad_tools {
    MonadCheck.tool, MonadEval.tool, MonadTools.binary, MonadTools.strip_ansi, MonadTools.summarize,
    MonadTools.needs_mote, MonadTools.resolve_path,
}
use std::ref {Ref}
use json::json {Json, Json.make_object, Json.make_str}
use std::map {Map, BTreeMap}

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
    let bin <- MonadTools.binary;
    let t : ToolImpl := MonadCheck.tool bin (Option.some "/tmp");
    let run : String -> Json -> ResultT String IO Content := t.run;
    let r <- ResultT.run (run "call" (source_input "def main : I64 := 1 + 2"));
    match r {
        Result.err _ => IO.pure false,
        Result.ok c => IO.pure (String.contains (text_of c) "OK"),
    }
}

#[test]
def test_monad_check_reports_an_error : IO Bool := do {
    let bin <- MonadTools.binary;
    let t : ToolImpl := MonadCheck.tool bin (Option.some "/tmp");
    let run : String -> Json -> ResultT String IO Content := t.run;
    let r <- ResultT.run (run "call" (source_input "def main : I64 := nope"));
    match r {
        Result.err _ => IO.pure false,
        Result.ok c => IO.pure (String.contains (text_of c) "ERRORS"),
    }
}

#[test]
def test_monad_eval_expression : IO Bool := do {
    let bin <- MonadTools.binary;
    let empty_buf : List String := List.empty;
    let buf <- Ref.new empty_buf;
    let t : ToolImpl := MonadEval.tool bin buf (Option.some "/tmp");
    let run : String -> Json -> ResultT String IO Content := t.run;
    let r <- ResultT.run (run "call" (source_input "1 + 2"));
    match r {
        Result.err _ => IO.pure false,
        Result.ok c => IO.pure (String.contains (text_of c) "Eval result" && String.contains (text_of c) "3"),
    }
}

/// Definitions accumulate: a `def` snippet is accepted into the scratch
/// module, and a later expression can call it.
#[test]
def test_monad_eval_accumulates_definitions : IO Bool := do {
    let bin <- MonadTools.binary;
    let empty_buf : List String := List.empty;
    let buf <- Ref.new empty_buf;
    let t : ToolImpl := MonadEval.tool bin buf (Option.some "/tmp");
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
                Result.ok c2 => IO.pure (String.contains (text_of c2) "42"),
            },
    }
}

/// `reset` clears the buffer: a definition accepted before it is gone.
#[test]
def test_monad_eval_reset_clears_definitions : IO Bool := do {
    let bin <- MonadTools.binary;
    let empty_buf : List String := List.empty;
    let buf <- Ref.new empty_buf;
    let t : ToolImpl := MonadEval.tool bin buf (Option.some "/tmp");
    let run : String -> Json -> ResultT String IO Content := t.run;
    let _ <- ResultT.run (run "call" (source_input "def triple (x : I64) : I64 := x + x + x"));
    let _ <- ResultT.run (run "call" (reset_input "0"));
    let r <- ResultT.run (run "call" (source_input "triple 3"));
    match r {
        Result.err _ => IO.pure false,
        Result.ok c => IO.pure (is_error_of c),
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
    let bin <- MonadTools.binary;
    let empty_buf : List String := List.empty;
    let buf <- Ref.new empty_buf;
    let t : ToolImpl := MonadEval.tool bin buf (Option.some "/tmp");
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

#[test]
def test_monad_eval_failure_is_an_error : IO Bool := do {
    let bin <- MonadTools.binary;
    let empty_buf : List String := List.empty;
    let buf <- Ref.new empty_buf;
    let t : ToolImpl := MonadEval.tool bin buf (Option.some "/tmp");
    let run : String -> Json -> ResultT String IO Content := t.run;
    let r <- ResultT.run (run "call" (source_input "missing_thing"));
    match r {
        Result.err _ => IO.pure false,
        Result.ok c => IO.pure (is_error_of c),
    }
}

/// Color codes go; the text between them stays.
#[test]
def test_strip_ansi_drops_sgr_codes : Bool :=
    MonadTools.strip_ansi "\u{1b}[1m\u{1b}[31mFAILED\u{1b}[0m ok" == "FAILED ok"

/// Warnings are counted, not listed; errors and their locations stay.
#[test]
def test_summarize_counts_warnings_and_keeps_errors : Bool :=
    let out : String := String.concat "warning: `x` is used twice\n  --> a.mo\n"
        "error: unknown variable 'nope'\n  --> a.mo\n\n1 error(s)\n" in
    let s : String := MonadTools.summarize out in
    String.contains s "unknown variable" && String.contains s "--> a.mo"
        && String.contains s "1 warning(s) not shown" && Bool.not (String.contains s "used twice")

/// Only a snippet with imports is staged inside the user's mote.
#[test]
def test_needs_mote_only_for_imports : Bool :=
    MonadTools.needs_mote "use json::json {Json}\ndef x : I64 := 1"
        && MonadTools.needs_mote "  use std::list {List.any}"
        && Bool.not (MonadTools.needs_mote "def used : I64 := 1\n// use later")

/// A relative `path` is under the session root; an absolute one is kept.
#[test]
def test_resolve_path_joins_the_root : Bool :=
    MonadTools.resolve_path (Option.some "/w") "src/a.mo" == "/w/src/a.mo"
        && MonadTools.resolve_path (Option.some "/w") "/abs/a.mo" == "/abs/a.mo"
        && MonadTools.resolve_path Option.none "a.mo" == "a.mo"

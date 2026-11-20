/// Monad-aware agent tools: `monad_check` (type-check a file or an
/// in-memory buffer) and `monad_eval` (run a REPL-style scratch module
/// through the interpreter).
///
/// Both shell out to the `monad` binary on the command line (or
/// `WEAVER_MONAD_BIN`), so weaver does not link the compiler: the tools
/// follow whatever toolchain the user has installed, and `monad check`'s own
/// on-disk cache warms repeated checks. The eval buffer is a per-session
/// `Ref`, so definitions accumulate across `monad_eval` calls.
///
/// `monad_eval` is tagged `exec`: it runs arbitrary Monad code and writes a
/// temp module. The interpreter runs pure programs only, and a run is
/// bounded by `timeout` (`MonadEval.timeout_seconds`).
use init::transformers {ResultT}
use shuttle::tool {ToolSpec, ToolImpl}
use shuttle::gate {Capability}
use shuttle::message_types {Content}
use json::json {
    Json, Json.get_object, Json.get_str, Json.get_bool, Json.object_get,
    Json.make_object, Json.make_str,
}
use std::ref {Ref, Ref.get, Ref.set}
use std::map {Map, BTreeMap}
use std::list {List.intercalate, List.any}
use std::io {IO.write_file, IO.file_exists, IO.get_env, IO.current_time_nano}
use std::path {Path, Path.to_string, Path.parent, Path.join, Path.unsafe_dir}
use std::process {process_id, exec_cmd, Proc.capture}
use weaver::diff_hunks {DiffHunks.cut_utf8}

// ── the binary ─────────────────────────────────────────────────────────

/// The `monad` the tools run: `WEAVER_MONAD_BIN` when set, else `monad`
/// from PATH.
pub def MonadTools.binary : IO String := do {
    let v <- IO.get_env "WEAVER_MONAD_BIN";
    IO.pure (match v {
        Option.some b => if String.is_empty (String.trim b) then "monad" else b,
        Option.none => "monad",
    })
}

/// `bin args...` with colors off; the exit code and the merged output.
def run_monad (bin : String) (args : List String) : IO (Pair I64 String) :=
    Proc.capture "env" (List.append ["NO_COLOR=1", bin] args)

// ── output shaping ─────────────────────────────────────────────────────

/// Drop one SGR code (`1m`, `31m`, `0m`) from the front of a piece that
/// followed an `ESC [`.
def drop_code (p : String) : String :=
    match String.split p "m" {
        List.cons h rest => if I64.lt (String.length h) 8i64 then List.intercalate "m" rest else p,
        List.empty => p,
    }

/// The text without its color codes (the CLI colors some lines even with
/// NO_COLOR).
pub def MonadTools.strip_ansi (s : String) : String :=
    match String.split s "\u{1b}[" {
        List.cons first rest => String.concat first (String.concat_list (List.map drop_code rest)),
        List.empty => s,
    }

/// Diagnostics are re-sent in the history on every later request, so a
/// file with hundreds of errors must not enter it whole.
def diagnostic_cap : I64 := 40

#[partial]
def take_lines (n : I64) (xs : List String) : List String :=
    if Bool.not (I64.lt 0 n) then List.empty
    else match xs {
        List.empty => List.empty,
        List.cons x rest => List.cons x (take_lines (n - 1) rest),
    }

/// The lines worth the model's tokens: warnings (and the `-->` line under
/// each) are counted, not shown -- an affine-warn mote prints hundreds.
#[partial]
def keep_lines (xs : List String) (skip_arrow : Bool) (kept : List String) (warns : I64) : Pair (List String) I64 :=
    match xs {
        List.empty => Pair.pair (List.reverse kept) warns,
        List.cons x rest =>
            if String.starts_with "warning:" x then keep_lines rest true kept (warns + 1)
            else if Bool.and skip_arrow (String.starts_with "  -->" x) then keep_lines rest false kept warns
            else if String.is_empty (String.trim x) then keep_lines rest false kept warns
            else keep_lines rest false (List.cons x kept) warns,
    }

/// The CLI's output as the tool result: color stripped, warnings counted,
/// capped at `diagnostic_cap` lines.
pub def MonadTools.summarize (out : String) : String :=
    match keep_lines (String.split (MonadTools.strip_ansi out) "\n") false List.empty 0 {
        Pair.pair kept warns =>
            let total : I64 := List.length kept in
            let shown : String := List.intercalate "\n" (take_lines diagnostic_cap kept) in
            let more : String := if I64.gt total diagnostic_cap
                then String.concat "\n... " (String.concat (I64.to_string (total - diagnostic_cap)) " more lines")
                else "" in
            let wtext : String := if I64.lt warns 1 then ""
                else String.concat "\n(" (String.concat (I64.to_string warns) " warning(s) not shown)") in
            String.concat shown (String.concat more wtext),
    }

// ── input helpers ──────────────────────────────────────────────────────

def str_field (key : String) (input : Json) : Option String :=
    match Json.get_object input {
        Result.err _ => Option.none,
        Result.ok obj =>
            match Json.object_get key obj {
                Option.none => Option.none,
                Option.some j =>
                    match Json.get_str j {
                        Result.ok s => if String.is_empty s then Option.none else Option.some s,
                        Result.err _ => Option.none,
                    },
            },
    }

def bool_field (key : String) (input : Json) : Bool :=
    match Json.get_object input {
        Result.err _ => false,
        Result.ok obj =>
            match Json.object_get key obj {
                Option.none => false,
                Option.some j => match Json.get_bool j {
                    Result.ok b => b,
                    Result.err _ => false,
                },
            },
    }

/// The nearest directory at or above `dir` holding a `mote.toml`.
#[partial]
def find_mote (dir : Path) : IO (Option Path) := do {
    let here <- IO.file_exists (Path.join dir (Path.path "mote.toml"));
    if here then IO.pure (Option.some dir)
    else match Path.parent dir {
        Option.none => IO.pure Option.none,
        Option.some up => if Path.to_string up == Path.to_string dir then IO.pure Option.none else find_mote up,
    }
}

/// The nearest enclosing mote's `src/` (so a temp module's `use`s resolve
/// against its real dependency graph), else the working directory.
def buffer_dir (root : Option String) : IO String := do {
    let start : String := match root {
        Option.none => ".",
        Option.some r => r,
    };
    let m <- find_mote (Path.unsafe_dir start);
    match m {
        Option.some dir => do {
            let src : String := String.concat (Path.to_string dir) "/src";
            let has_src <- IO.file_exists (Path.path src);
            IO.pure (if has_src then src else Path.to_string dir)
        },
        Option.none => IO.pure start,
    }
}

/// Whether the snippet imports anything: only then must it be staged inside
/// the enclosing mote (so its `use`s resolve); anything else is checked
/// from the temp directory and never touches the user's tree.
pub def MonadTools.needs_mote (content : String) : Bool :=
    List.any (fn (l : String) => String.starts_with "use " (String.trim l)) (String.split content "\n")

/// The directory a snippet is staged in: the mote's `src/` when it has
/// imports, else `TMPDIR` (or `/tmp`).
def stage_dir (root : Option String) (content : String) : IO String :=
    if MonadTools.needs_mote content then buffer_dir root
    else do {
        let t <- IO.get_env "TMPDIR";
        IO.pure (match t {
            Option.some d => if String.is_empty (String.trim d) then "/tmp" else d,
            Option.none => "/tmp",
        })
    }

/// A fresh name per call (pid + clock), so two stagings never share a file.
def temp_in (dir : String) (stem : String) (stamp : I64) : String :=
    String.concat_list [dir, "/", stem, I64.to_string process_id, "_", I64.to_string stamp, ".mo"]

/// A relative `path` names a file under the session's root, not under
/// weaver's own working directory.
pub def MonadTools.resolve_path (root : Option String) (p : String) : String :=
    match root {
        Option.some r => if Bool.or (String.starts_with "/" p) (String.is_empty r) then p else String.concat_list [r, "/", p],
        Option.none => p,
    }

def cleanup (path : String) : IO Unit := do {
    let _ <- exec_cmd "rm" ["-f", path];
    IO.pure unit
}

/// Write `content` as a temp module in the nearest mote, run `act` on its
/// path, delete it. None when the file could not be written.
def with_temp (root : Option String) (stem : String) (content : String) (act : String -> IO (Pair I64 String)) : IO (Option (Pair I64 String)) := do {
    let dir <- stage_dir root content;
    let stamp <- IO.current_time_nano;
    let path : String := temp_in dir stem stamp;
    let w <- IO.write_file (Path.path path) content;
    match w {
        Result.err _ => IO.pure Option.none,
        Result.ok _ => do {
            let r <- act path;
            let _ <- cleanup path;
            IO.pure (Option.some r)
        },
    }
}

def str_prop (desc : String) : Json :=
    Json.make_object (Map.insert "type" (Json.make_str "string")
        (Map.insert "description" (Json.make_str desc) BTreeMap.empty))

// ── monad_check ────────────────────────────────────────────────────────

def check_schema : Json :=
    let props : BTreeMap String Json :=
        Map.insert "path" (str_prop "File or directory to check, relative to the workspace or absolute")
        (Map.insert "source" (str_prop "Monad source to check in memory (instead of a file)") BTreeMap.empty) in
    Json.make_object (Map.insert "type" (Json.make_str "object")
        (Map.insert "properties" (Json.make_object props) BTreeMap.empty))

pub def MonadCheck.spec : ToolSpec :=
    { name := "monad_check",
        description := "Type-check Monad source with `monad check`: pass `path` for a file or directory, or `source` for an in-memory buffer (staged as a temporary .mo -- inside the nearest enclosing mote when it has `use` lines, so they resolve -- then removed). Returns the errors; warnings are counted, not listed.",
        schema := check_schema }

def check_content (id : String) (label : String) (r : Pair I64 String) : Content :=
    match r {
        Pair.pair code out =>
            let head : String := String.concat_list ["monad_check: ", label, if code == 0 then " OK\n" else " ERRORS\n"] in
            Content.tool_result id (String.concat head (MonadTools.summarize out)) (Bool.not (code == 0)),
    }

def check_dispatch (bin : String) (root : Option String) (id : String) (input : Json) : IO Content :=
    match str_field "source" input {
        Option.some s => do {
            let r <- with_temp root "weaver_check_buffer_" s (fn (p : String) => run_monad bin ["check", p]);
            IO.pure (match r {
                Option.none => Content.tool_result id "monad_check: could not stage the buffer" true,
                Option.some res => check_content id "buffer" res,
            })
        },
        Option.none => match str_field "path" input {
            Option.some p => do {
                let res <- run_monad bin ["check", MonadTools.resolve_path root p];
                IO.pure (check_content id p res)
            },
            Option.none => IO.pure (Content.tool_result id "monad_check: give `path` or `source`" true),
        },
    }

def check_run (bin : String) (root : Option String) (id : String) (input : Json) : ResultT String IO Content :=
    ResultT.mk (do {
        let c <- check_dispatch bin root id input;
        return (Result.ok c)
    })

pub def MonadCheck.tool (bin : String) (root : Option String) : ToolImpl :=
    { spec := MonadCheck.spec, cap := Capability.read, run := check_run bin root }

// ── monad_eval ─────────────────────────────────────────────────────────

/// The wall-clock bound on one evaluation: a runaway snippet ends with
/// `timeout`'s exit instead of pinning the turn.
pub def MonadEval.timeout_seconds : I64 := 60

/// The most expression output returned to the model: a printed list can
/// be arbitrarily large, and every byte is re-sent later.
pub def MonadEval.result_cap : I64 := 16384

def cap_result (text : String) : String :=
    if I64.gt (String.length text) MonadEval.result_cap
    then String.concat (DiffHunks.cut_utf8 text MonadEval.result_cap) "\n[output truncated at 16384 bytes]"
    else text

def eval_schema : Json :=
    let props : BTreeMap String Json :=
        Map.insert "source" (str_prop "A Monad expression, a `def`/`use` snippet, or a whole module with `def main`")
        (Map.insert "reset" (Json.make_object (Map.insert "type" (Json.make_str "boolean")
            (Map.insert "description" (Json.make_str "Clear the accumulated definitions first") BTreeMap.empty))) BTreeMap.empty) in
    Json.make_object (Map.insert "type" (Json.make_str "object")
        (Map.insert "properties" (Json.make_object props) BTreeMap.empty))

pub def MonadEval.spec : ToolSpec :=
    { name := "monad_eval",
        description := "Evaluate Monad code with `monad eval` (pure programs only, no IO; 60 s limit). Definitions accumulate across calls: a `def` snippet is added to the session scratch module, an expression is wrapped into `main` and its value returned, a snippet with `def main` runs as a whole module. Call `monad_check` first for diagnostics.",
        schema := eval_schema }

def buffer_text (defs : List String) : String :=
    List.intercalate "\n\n" defs

def eval_path (bin : String) (path : String) : IO (Pair I64 String) :=
    Proc.capture "timeout" [I64.to_string MonadEval.timeout_seconds, "env", "NO_COLOR=1", bin, "eval", path]

def eval_content (id : String) (r : Option (Pair I64 String)) : Content :=
    match r {
        Option.none => Content.tool_result id "monad_eval: could not stage the module" true,
        Option.some res => match res {
            Pair.pair code out =>
                let text : String := if code == 124
                    then String.concat (MonadTools.summarize out) "\n[timed out]"
                    else MonadTools.summarize out in
                Content.tool_result id (cap_result text) (Bool.not (code == 0)),
        },
    }

def run_module (bin : String) (root : Option String) (content : String) : IO (Option (Pair I64 String)) :=
    with_temp root "weaver_eval_" content (eval_path bin)

def accept_def (buf : Ref (List String)) (id : String) (next : List String) : IO Content := do {
    let _ <- Ref.set buf next;
    return (Content.tool_result id (String.concat "monad_eval: defined ("
        (String.concat (I64.to_string (List.length next)) " definition(s) in the scratch module)")) false)
}

/// A `def` snippet joins the buffer only when the buffer (with a harmless
/// `main`) still checks.
def eval_append_def (bin : String) (buf : Ref (List String)) (root : Option String) (id : String) (src : String) : IO Content := do {
    let defs <- Ref.get buf;
    let next : List String := List.append defs [src];
    let probe : String := String.concat (buffer_text next) "\n\ndef main : I64 := 0\n";
    let r <- with_temp root "weaver_eval_buffer_" probe (fn (p : String) => run_monad bin ["check", p]);
    match r {
        Option.some res => match res {
            Pair.pair code out =>
                if code == 0 then accept_def buf id next
                else IO.pure (Content.tool_result id (String.concat "monad_eval: the definition does not type-check:\n" (MonadTools.summarize out)) true),
        },
        Option.none => IO.pure (Content.tool_result id "monad_eval: could not stage the buffer" true),
    }
}

/// A run that failed because `main`'s declared type was wrong.
def typecheck_failed (r : Option (Pair I64 String)) : Bool :=
    match r {
        Option.some res => match res {
            Pair.pair code out => Bool.and (Bool.not (code == 0)) (String.contains out "stage: typecheck"),
        },
        Option.none => false,
    }

def wrap_main (pre : String) (ty : String) (expr : String) : String :=
    String.concat_list [pre, "\n\ndef main : ", ty, " := ", expr, "\n"]

/// The expression's type is not written by the user, and a top-level
/// `def` cannot omit its signature, so the wrapper tries the common result
/// types in order and keeps the first run that gets past the checker. When
/// none does, the I64 run's diagnostics are the answer.
#[partial]
def eval_typed (bin : String) (root : Option String) (pre : String) (expr : String) (types : List String) (first : Option (Option (Pair I64 String))) : IO (Option (Pair I64 String)) :=
    match types {
        List.empty => IO.pure (match first { Option.some r => r, Option.none => Option.none }),
        List.cons t rest => do {
            let r <- run_module bin root (wrap_main pre t expr);
            if typecheck_failed r
            then eval_typed bin root pre expr rest (match first { Option.none => Option.some r, Option.some _ => first })
            else IO.pure r
        },
    }

def eval_expression (bin : String) (buf : Ref (List String)) (root : Option String) (id : String) (src : String) : IO Content := do {
    let defs <- Ref.get buf;
    let r <- eval_typed bin root (buffer_text defs) src ["I64", "String", "Bool", "Unit"] Option.none;
    IO.pure (eval_content id r)
}

/// A snippet with `def main` runs whole; a `def`/`use` snippet extends
/// the scratch module; anything else is an expression wrapped in main.
def eval_source (bin : String) (buf : Ref (List String)) (root : Option String) (id : String) (s : String) : IO Content :=
    if String.contains s "def main"
    then do {
        let r <- run_module bin root s;
        IO.pure (eval_content id r)
    }
    else if Bool.or (String.contains s "def ") (String.starts_with "use " (String.trim s))
    then eval_append_def bin buf root id s
    else eval_expression bin buf root id s

def eval_dispatch (bin : String) (buf : Ref (List String)) (root : Option String) (id : String) (input : Json) : IO Content :=
    match str_field "source" input {
        Option.none => IO.pure (Content.tool_result id "monad_eval: give `source`" true),
        Option.some s => do {
            let _ <- if bool_field "reset" input then Ref.set buf List.empty else IO.pure unit;
            eval_source bin buf root id s
        },
    }

def eval_run (bin : String) (buf : Ref (List String)) (root : Option String) (id : String) (input : Json) : ResultT String IO Content :=
    ResultT.mk (do {
        let c <- eval_dispatch bin buf root id input;
        return (Result.ok c)
    })

pub def MonadEval.tool (bin : String) (buf : Ref (List String)) (root : Option String) : ToolImpl :=
    { spec := MonadEval.spec, cap := Capability.exec, run := eval_run bin buf root }

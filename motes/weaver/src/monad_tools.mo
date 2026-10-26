/// Monad-aware agent tools: `monad_check` (type-check a file or an
/// in-memory buffer with the compiler's own checker) and `monad_eval`
/// (run a REPL-style scratch module through the self-hosted interpreter).
///
/// Both use `lang`, so weaver's check/build closure now includes the
/// compiler. The checker cache and the eval buffer are per-session
/// `Ref`s created at startup -- one cache means a second check reuses
/// the first's module graph; one buffer means definitions accumulate
/// across `monad_eval` calls.
///
/// `monad_eval` is tagged `exec`: it runs arbitrary Monad code and
/// writes a temp module. Its interpreter has only the I64/String natives
/// in `basic_native_table` (no IO/println), and a non-terminating
/// expression hangs the turn -- the description says both.
use init::transformers {ResultT}
use shuttle::tool {ToolSpec, ToolImpl}
use shuttle::gate {Capability}
use shuttle::message_types {Content}
use json::json {
    Json, Json.get_object, Json.get_str, Json.get_bool, Json.object_get,
    Json.make_object, Json.make_str,
}
use lang::module {
    ModuleInfoCache, module_info_cache_empty, check_file_cached,
    FileCheckAndCache, FileCheckResult,
}
use lang::eval_run {EvalRun.run_file}
use lang::mote {MoteManifest, Mote.discover}
use std::ref {Ref, Ref.get, Ref.set}
use std::map {Map, BTreeMap}
use std::list {List.intercalate, List.length}
use std::io {IO.write_file}
use std::path {Path}
use std::process {process_id, exec_cmd}

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

/// The nearest enclosing mote's directory (so a temp module's `use`s
/// resolve against its real dependency graph), else the workspace root.
def buffer_dir (root : Option String) : IO String := do {
    let start : String := match root {
        Option.none => ".",
        Option.some r => r,
    };
    let m <- Mote.discover start;
    match m {
        Option.some man => IO.pure man.dir,
        Option.none => IO.pure start,
    }
}

def temp_path (dir : String) : String :=
    String.concat dir (String.concat "/weaver_eval_" (String.concat (I64.to_string process_id) ".mo"))

def cleanup (path : String) : IO Unit := do {
    let _ <- exec_cmd "rm" ["-f", path];
    IO.pure unit
}

// ── monad_check ────────────────────────────────────────────────────────

def str_prop (desc : String) : Json :=
    Json.make_object (Map.insert "type" (Json.make_str "string")
        (Map.insert "description" (Json.make_str desc) BTreeMap.empty))

def check_schema : Json :=
    let props : BTreeMap String Json :=
        Map.insert "path" (str_prop "File to check, relative to the workspace or absolute")
        (Map.insert "source" (str_prop "Monad source to check in memory (instead of a file)") BTreeMap.empty) in
    Json.make_object (Map.insert "type" (Json.make_str "object")
        (Map.insert "properties" (Json.make_object props) BTreeMap.empty))

pub def MonadCheck.spec : ToolSpec :=
    { name := "monad_check",
      description := "Type-check Monad source with the compiler's own checker: pass `path` for a file or `source` for an in-memory buffer. A buffer is staged as a temporary .mo in the nearest enclosing mote (so its imports resolve) and removed after the check. Returns the diagnostics.",
      schema := check_schema }

def has_errors (r : FileCheckResult) : Bool :=
    let errs : List String := r.diagnostics in
    match errs {
        List.empty => false,
        List.cons _ _ => true,
    }

def warnings_text (ws : List String) : String :=
    match ws {
        List.empty => "",
        List.cons _ _ => String.concat "\nwarnings:\n" (List.intercalate "\n" ws),
    }

def check_text (path : String) (r : FileCheckResult) : String :=
    let errs : List String := r.diagnostics in
    let warns : List String := r.warnings in
    match errs {
        List.empty => String.concat "monad_check: " (String.concat path (String.concat " OK" (warnings_text warns))),
        List.cons _ _ => String.concat "monad_check: " (String.concat path (String.concat " ERRORS:\n"
            (String.concat (List.intercalate "\n" errs) (warnings_text warns)))),
    }

/// The checker resolves a `use` against the buffer's PATH, and the
/// compiler's from-source entry point still needs that path to exist (a
/// virtual one fails to load), so the buffer is staged as a real temp
/// module in the nearest mote, checked, and removed. The file is ours,
/// never the model's, and is deleted on every path a return reaches; a
/// kill can leave it behind.
def check_source (cache : Ref ModuleInfoCache) (root : Option String) (id : String) (src : String) : IO Content := do {
    let dir <- buffer_dir root;
    let vpath : String := check_path_of dir;
    let w <- IO.write_file (Path.path vpath) src;
    match w {
        Result.err _ => IO.pure (Content.tool_result id (String.concat "monad_check: could not write " vpath) true),
        Result.ok _ => do {
            let c <- Ref.get cache;
            let fc <- check_file_cached c vpath false;
            let _ <- Ref.set cache fc.cache;
            let _ <- cleanup vpath;
            let r : FileCheckResult := fc.result;
            return (Content.tool_result id (check_text "buffer" r) (has_errors r))
        },
    }
}

def check_path_of (dir : String) : String :=
    String.concat dir (String.concat "/weaver_check_buffer_" (String.concat (I64.to_string process_id) ".mo"))

def check_path (cache : Ref ModuleInfoCache) (id : String) (path : String) : IO Content := do {
    let c <- Ref.get cache;
    let fc <- check_file_cached c path false;
    let _ <- Ref.set cache fc.cache;
    let r : FileCheckResult := fc.result;
    return (Content.tool_result id (check_text path r) (has_errors r))
}

def check_dispatch (cache : Ref ModuleInfoCache) (root : Option String) (id : String) (input : Json) : IO Content := do {
    let src : Option String := str_field "source" input;
    match src {
        Option.some s => check_source cache root id s,
        Option.none =>
            match str_field "path" input {
                Option.some p => check_path cache id p,
                Option.none => IO.pure (Content.tool_result id "monad_check: give `path` or `source`" true),
            },
    }
}

def check_run (cache : Ref ModuleInfoCache) (root : Option String) (id : String) (input : Json) : ResultT String IO Content :=
    ResultT.mk (do {
        let c <- check_dispatch cache root id input;
        return (Result.ok c)
    })

pub def MonadCheck.tool (cache : Ref ModuleInfoCache) (root : Option String) : ToolImpl :=
    { spec := MonadCheck.spec, cap := Capability.read, run := check_run cache root }

// ── monad_eval ─────────────────────────────────────────────────────────

def eval_schema : Json :=
    let props : BTreeMap String Json :=
        Map.insert "source" (str_prop "A Monad expression, a `def`/`use` snippet, or a whole module with `def main`")
        (Map.insert "reset" (Json.make_object (Map.insert "type" (Json.make_str "boolean")
            (Map.insert "description" (Json.make_str "Clear the accumulated definitions first") BTreeMap.empty))) BTreeMap.empty) in
    Json.make_object (Map.insert "type" (Json.make_str "object")
        (Map.insert "properties" (Json.make_object props) BTreeMap.empty))

pub def MonadEval.spec : ToolSpec :=
    { name := "monad_eval",
      description := "Evaluate Monad code with the self-hosted interpreter (pure programs only; I64/String natives, no IO). Definitions accumulate across calls: a `def` snippet is added to the session scratch module, an expression is wrapped into `main` and its value returned, a snippet with `def main` runs as a whole module. Call `monad_check` first for diagnostics.",
      schema := eval_schema }

def buffer_text (defs : List String) : String :=
    List.intercalate "\n\n" defs

/// Write `content` as a temp module in the nearest mote, run it, delete
/// it. The Result is kept apart from the text: the pipeline prefixes
/// warnings onto failures too, so an `is_error` sniffing the text lied.
def run_temp (root : Option String) (content : String) : IO (Result String String) := do {
    let dir <- buffer_dir root;
    let path : String := temp_path dir;
    let w <- IO.write_file (Path.path path) content;
    match w {
        Result.err _ => IO.pure (Result.err (String.concat "monad_eval: could not write " path)),
        Result.ok _ => do {
            let r <- EvalRun.run_file path false;
            let _ <- cleanup path;
            return r
        },
    }
}

/// Check a definitions buffer (with a harmless `main`) without running
/// it: used before a `def` snippet is accepted into the session buffer.
def check_buffer (cache : Ref ModuleInfoCache) (root : Option String) (content : String) : IO Bool := do {
    let dir <- buffer_dir root;
    let vpath : String := String.concat dir (String.concat "/weaver_eval_buffer_" (String.concat (I64.to_string process_id) ".mo"));
    let w <- IO.write_file (Path.path vpath) content;
    match w {
        Result.err _ => IO.pure false,
        Result.ok _ => do {
            let c <- Ref.get cache;
            let fc <- check_file_cached c vpath false;
            let _ <- Ref.set cache fc.cache;
            let _ <- cleanup vpath;
            let r : FileCheckResult := fc.result;
            IO.pure (Bool.not (has_errors r))
        },
    }
}

def accept_def (buf : Ref (List String)) (id : String) (next : List String) : IO Content := do {
    let _ <- Ref.set buf next;
    return (Content.tool_result id (String.concat "monad_eval: defined ("
        (String.concat (I64.to_string (List.length next)) " definition(s) in the scratch module)")) false)
}

def eval_append_def (cache : Ref ModuleInfoCache) (buf : Ref (List String)) (root : Option String) (id : String) (src : String) : IO Content := do {
    let defs <- Ref.get buf;
    let next : List String := List.append defs [src];
    let probe : String := String.concat (buffer_text next) "\n\ndef main : I64 := 0\n";
    let ok <- check_buffer cache root probe;
    let c <- if ok
        then accept_def buf id next
        else IO.pure (Content.tool_result id "monad_eval: the definition does not type-check (run monad_check on it for diagnostics)" true);
    return c
}

/// The expression's type is not written by the user, and a top-level
/// `def` cannot omit its signature, so the wrapper tries the common
/// result types against the SESSION checker cache (cheap after the
/// first) and evaluates the one that checks. None accepted -> evaluate
/// as I64 so the user sees that type's real diagnostics.
/// Probe `expr` against the accumulated definitions (`pre`), exactly as
/// the module that will run is built: a probe without them fails every
/// type for an expression that uses a buffered definition, and the I64
/// fallback then mis-signs the real module.
#[partial]
def first_type (cache : Ref ModuleInfoCache) (root : Option String) (pre : String) (expr : String) (types : List String) : IO (Option String) :=
    match types {
        List.empty => IO.pure Option.none,
        List.cons t rest => do {
            let content : String := String.concat pre (String.concat "\n\ndef main : " (String.concat t
                (String.concat " := " (String.concat expr "\n"))));
            let ok <- check_buffer cache root content;
            if ok then IO.pure (Option.some t) else first_type cache root pre expr rest
        },
    }

def eval_expression (cache : Ref ModuleInfoCache) (buf : Ref (List String)) (root : Option String) (id : String) (src : String) : IO Content := do {
    let defs <- Ref.get buf;
    let pre : String := buffer_text defs;
    let types : List String := ["I64", "String", "Bool", "Unit"];
    let found <- first_type cache root pre src types;
    let ty : String := match found {
        Option.some t => t,
        Option.none => "I64",
    };
    let content : String := String.concat pre (String.concat "\n\ndef main : "
        (String.concat ty (String.concat " := " (String.concat src "\n"))));
    let text_r <- run_temp root content;
    return (match text_r {
        Result.ok text => Content.tool_result id text false,
        Result.err text => Content.tool_result id text true,
    })
}

def eval_dispatch (cache : Ref ModuleInfoCache) (buf : Ref (List String)) (root : Option String) (id : String) (input : Json) : IO Content := do {
    let src : Option String := str_field "source" input;
    match src {
        Option.none => IO.pure (Content.tool_result id "monad_eval: give `source`" true),
        Option.some s => do {
            let reset : Bool := bool_field "reset" input;
            let _ <- if reset then Ref.set buf List.empty else IO.pure unit;
            eval_source cache buf root id s
        },
    }
}

/// A snippet with `def main` runs whole; a `def`/`use` snippet extends
/// the scratch module; anything else is an expression wrapped in main.
def eval_source (cache : Ref ModuleInfoCache) (buf : Ref (List String)) (root : Option String) (id : String) (s : String) : IO Content :=
    if String.contains s "def main"
    then run_whole root id s
    else if Bool.or (String.contains s "def ") (String.starts_with "use " (String.trim s))
    then eval_append_def cache buf root id s
    else eval_expression cache buf root id s

def run_whole (root : Option String) (id : String) (s : String) : IO Content := do {
    let text_r <- run_temp root s;
    return (match text_r {
        Result.ok text => Content.tool_result id text false,
        Result.err text => Content.tool_result id text true,
    })
}

def eval_run (cache : Ref ModuleInfoCache) (buf : Ref (List String)) (root : Option String) (id : String) (input : Json) : ResultT String IO Content :=
    ResultT.mk (do {
        let c <- eval_dispatch cache buf root id input;
        return (Result.ok c)
    })

pub def MonadEval.tool (buf : Ref (List String)) (cache : Ref ModuleInfoCache) (root : Option String) : ToolImpl :=
    { spec := MonadEval.spec, cap := Capability.exec, run := eval_run cache buf root }

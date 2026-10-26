// The REPL's session core: input classification, the accumulated
// declarations, and the evaluation step. No stdin/stdout here -- the
// terminal loop lives in `cli/src/main.mo`, so this module is unit-testable
// and the same semantics could later run behind a different UI.
//
// The session keeps its SOURCE TEXT, not a parsed `List Decl`: `List` is
// not `Copy`, and the loader needs the decls while the next step needs the
// session. Re-parsing a few KiB per input is cheap next to elaboration,
// and it keeps one canonical copy of what the user entered.
//
// `use` support falls out of the standard loader: a `use` line is an
// ordinary declaration, so it joins the session source and the next step's
// filesystem walk resolves it exactly as `monad check` would.

use lang::types {AffineMode, Decl, Identifier, ModulePath}
use lang::module {
    ModuleInfo, ModuleInfoCache, elaborate_loaded_modules_from_main,
    elaborate_loaded_modules_pure, load_modules_from_main, make_module_info,
    module_info_cache_empty, module_name_from_path, parse_error_at_eof,
    rewrite_lib_aliases_of, show_parse_error, try_parse_decls_strict_diag,
}
use lang::mote {Mote.affine_mode_of_path}
use std::list {List.any, List.length}
use lib::run {
    EvalFailure, EvalOptions, EvalStage, EvalTarget,
    Eval.check_elaborated, Eval.run_elaborated, Eval.type_of,
}

pub struct EvalSession {
    source : String,          // committed declarations
    cache : ModuleInfoCache,  // warm parse cache across inputs
    file_path : String,       // "repl.mo" (cwd-relative)
    module_name : String,     // module_name_from_path file_path
    affine_warn : Bool,       // AffineMode is not Copy
    decl_count : I64,         // declarations in `source`
    next_expr : I64,          // the next synthetic expression name
}

pub type EvalInput {
    eval_input_meta (command : String),
    eval_input_decls (source : String) (decls : List Decl) (decl_count : I64),
    eval_input_expr (source : String) (decls : List Decl) (root : String),
    eval_input_type (source : String) (decls : List Decl) (root : String)
        (display : String),
    eval_input_continue,
    eval_input_blank,
    eval_input_error (message : String),
}

pub type EvalResponse {
    eval_response_blank,
    eval_response_ok (warnings : List String),
    eval_response_value (text : String) (typ : String) (warnings : List String),
    eval_response_meta (text : String),
    eval_response_error (message : String),
    eval_response_quit,
}

pub def Eval.new_session (file_path : String) : IO EvalSession := do {
    let mode <- Mote.affine_mode_of_path file_path;
    let warn : Bool :=
        match mode {
            AffineMode.affine_warn => true,
            AffineMode.affine_error => false,
        };
    let out : EvalSession :=
        { source := "", cache := module_info_cache_empty, file_path := file_path,
          module_name := module_name_from_path file_path, affine_warn := warn,
          decl_count := 0, next_expr := 0 };
    return out
}

// --- Classification ---------------------------------------------------

pub def Eval.classify (s : EvalSession) (text : String) : Pair EvalSession EvalInput :=
    match s {
        { source, file_path, decl_count, next_expr, .. } =>
            classify_input s source file_path decl_count next_expr (String.trim text),
    }

def classify_input (s : EvalSession) (source : String) (file_path : String)
    (decl_count : I64) (next_expr : I64) (text : String) : Pair EvalSession EvalInput :=
    if String.is_empty text
    then Pair.pair s EvalInput.eval_input_blank
    else if String.starts_with "//" text
    then Pair.pair s EvalInput.eval_input_blank
    else if String.starts_with ":type " text
    then classify_type s source file_path next_expr (String.trim (String.drop 6 text))
    else if Bool.and (String.starts_with ":" text) (Bool.not (String.starts_with "::" text))
    then Pair.pair s (EvalInput.eval_input_meta text)
    else classify_code s source file_path decl_count next_expr text

/// A declaration candidate first: if `source ++ input` parses as
/// declarations and GAINED one, the input is a declaration. Otherwise the
/// EXPRESSION candidate decides, and only if that also fails is an
/// end-of-input failure a continuation.
///
/// The expression attempt cannot be skipped in the "parsed, gained
/// nothing" case either: the declaration parser happily accepts a first
/// declaration and ignores a trailing bare expression, so after any
/// committed declaration `twice 21` comes back as "ok, same decl count".
/// (It also consumes a whole bare expression before failing, so its
/// failure is at end of input -- checking `parse_error_at_eof` before
/// trying the expression would make every such input "continue".)
def classify_code (s : EvalSession) (source : String) (file_path : String)
    (decl_count : I64) (next_expr : I64) (text : String) : Pair EvalSession EvalInput :=
    let candidate : String := append_line source text
    in
    match try_parse_decls_strict_diag candidate {
        Result.ok decls =>
            let count : I64 := List.length decls
            in
            if I64.gt count decl_count
            then Pair.pair s (EvalInput.eval_input_decls candidate decls count)
            else classify_expression s source file_path next_expr text false Option.none,
        Result.err e =>
            classify_expression s source file_path next_expr text
                (parse_error_at_eof e)
                (Option.some (show_parse_error candidate (Option.some file_path) e)),
    }

/// An expression candidate: the input wrapped in a `: _`-typed synthetic
/// def, appended to a throwaway copy of the session. `_` is required --
/// the self-hosted parser rejects an omitted return type -- and lowers to
/// `Term.hole`, which the runner re-infers for the printed type.
def classify_expression (s : EvalSession) (source : String) (file_path : String)
    (next_expr : I64) (text : String) (declaration_at_eof : Bool)
    (declaration_error : Option String) : Pair EvalSession EvalInput :=
    let name : String := expr_name next_expr source
    in
    let candidate : String := append_line source (expr_line name text)
    in
    match try_parse_decls_strict_diag candidate {
        Result.ok decls =>
            let s2 : EvalSession := { s with next_expr := I64.add next_expr 1 }
            in
            Pair.pair s2 (EvalInput.eval_input_expr candidate decls name),
        Result.err e =>
            if Bool.or declaration_at_eof (parse_error_at_eof e)
            then Pair.pair s EvalInput.eval_input_continue
            else match declaration_error {
                Option.some message =>
                    if declaration_starter text
                    then Pair.pair s (EvalInput.eval_input_error message)
                    else Pair.pair s (EvalInput.eval_input_error
                        (show_parse_error candidate (Option.some file_path) e)),
                Option.none =>
                    Pair.pair s (EvalInput.eval_input_error
                        (show_parse_error candidate (Option.some file_path) e)),
            },
    }

def classify_type (s : EvalSession) (source : String) (file_path : String)
    (next_expr : I64) (expr_text : String) : Pair EvalSession EvalInput :=
    if String.is_empty expr_text
    then Pair.pair s (EvalInput.eval_input_error "usage: :type <expr>")
    else
        let name : String := expr_name next_expr source
        in
        let candidate : String := append_line source (expr_line name expr_text)
        in
        match try_parse_decls_strict_diag candidate {
            Result.ok decls =>
                let s2 : EvalSession := { s with next_expr := I64.add next_expr 1 }
                in
                Pair.pair s2 (EvalInput.eval_input_type candidate decls name expr_text),
            Result.err e =>
                if parse_error_at_eof e
                then Pair.pair s EvalInput.eval_input_continue
                else Pair.pair s (EvalInput.eval_input_error
                    (show_parse_error candidate (Option.some file_path) e)),
        }

// --- Steps ------------------------------------------------------------

pub def Eval.step (s : EvalSession) (input : EvalInput)
    : IO (Pair EvalSession EvalResponse) :=
    match input {
        EvalInput.eval_input_meta command => step_meta s command,
        EvalInput.eval_input_blank =>
            IO.pure (Pair.pair s EvalResponse.eval_response_blank),
        EvalInput.eval_input_continue =>
            IO.pure (Pair.pair s EvalResponse.eval_response_blank),
        EvalInput.eval_input_error message =>
            IO.pure (Pair.pair s (EvalResponse.eval_response_error message)),
        EvalInput.eval_input_decls candidate decls count =>
            step_decls s candidate decls count,
        EvalInput.eval_input_expr candidate decls root =>
            step_expr s candidate decls root,
        EvalInput.eval_input_type candidate decls root display =>
            step_type s candidate decls root display,
    }

def step_meta (s : EvalSession) (command : String) : IO (Pair EvalSession EvalResponse) :=
    if Bool.or (String.beq command ":quit") (String.beq command ":q")
    then IO.pure (Pair.pair s EvalResponse.eval_response_quit)
    else if Bool.or (String.beq command ":help") (String.beq command ":h")
    then IO.pure (Pair.pair s (EvalResponse.eval_response_meta help_text))
    else if String.beq command ":reset"
    then
        let s2 : EvalSession := { s with source := "", decl_count := 0, next_expr := 0 }
        in
        IO.pure (Pair.pair s2 (EvalResponse.eval_response_meta "session reset"))
    else IO.pure (Pair.pair s (EvalResponse.eval_response_error
        (String.concat "unknown command: " command)))

/// A declaration joins the session only when it loads, typechecks, and
/// passes the same gates `monad check` runs. A rejection keeps the old
/// source but the warmed dependency cache.
def step_decls (s : EvalSession) (candidate : String) (decls : List Decl)
    (count : I64) : IO (Pair EvalSession EvalResponse) :=
    match s {
        { file_path, module_name, affine_warn, cache, .. } =>
            do {
                let rewritten <- rewrite_lib_aliases_of file_path decls;
                let main : ModuleInfo :=
                    make_module_info (ModulePath.mk [Identifier.id module_name])
                        file_path rewritten;
                let ec <- elaborate_loaded_modules_from_main main (Option.some candidate)
                            false cache false;
                match ec.elaborated {
                    Result.err e => do {
                        let s2 : EvalSession := { s with cache := ec.cache };
                        return (Pair.pair s2 (EvalResponse.eval_response_error e))
                    },
                    Result.ok em => do {
                        let checked <- Eval.check_elaborated em (mode_of affine_warn)
                                        file_path false;
                        match checked.errors {
                            List.cons first rest => do {
                                let s2 : EvalSession := { s with cache := ec.cache };
                                return (Pair.pair s2
                                    (EvalResponse.eval_response_error
                                        (join_lines (List.cons first rest))))
                            },
                            List.empty => do {
                                let s2 : EvalSession := { s with source := candidate,
                                    decl_count := count, cache := ec.cache };
                                return (Pair.pair s2
                                    (EvalResponse.eval_response_ok checked.warnings))
                            },
                        }
                    },
                }
            },
    }

/// An expression runs against the committed declarations in a throwaway
/// copy; only the warming cache is kept. The session's own definitions
/// stay exactly as they were, whether the expression succeeded or failed.
def step_expr (s : EvalSession) (candidate : String) (decls : List Decl)
    (root : String) : IO (Pair EvalSession EvalResponse) :=
    match s {
        { file_path, module_name, affine_warn, cache, .. } =>
            do {
                let rewritten <- rewrite_lib_aliases_of file_path decls;
                let main : ModuleInfo :=
                    make_module_info (ModulePath.mk [Identifier.id module_name])
                        file_path rewritten;
                let lc <- load_modules_from_main main cache false;
                match lc.loaded {
                    Result.err e => do {
                        let s2 : EvalSession := { s with cache := lc.cache };
                        return (Pair.pair s2 (EvalResponse.eval_response_error e))
                    },
                    Result.ok loaded =>
                        match elaborate_loaded_modules_pure loaded false {
                            Result.err e => do {
                                let s2 : EvalSession := { s with cache := lc.cache };
                                return (Pair.pair s2 (EvalResponse.eval_response_error e))
                            },
                            Result.ok em => do {
                                let options : EvalOptions :=
                                    { fuel := -1, depth_limit := -1,
                                      affine := mode_of affine_warn, label := file_path,
                                      verbose := false, want_type := true,
                                      require_entry := true };
                                let target : EvalTarget :=
                                    { root := root,
                                      context_path := ModulePath.mk [Identifier.id module_name] };
                                let r <- Eval.run_elaborated em options target;
                                match r {
                                    Result.ok success => do {
                                        let s2 : EvalSession := { s with cache := lc.cache };
                                        return (Pair.pair s2
                                            (EvalResponse.eval_response_value
                                                success.value_text success.type_text
                                                success.warnings))
                                    },
                                    Result.err failure => do {
                                        let s2 : EvalSession := { s with cache := lc.cache };
                                        return (Pair.pair s2
                                            (EvalResponse.eval_response_error
                                                (describe_failure failure)))
                                    },
                                }
                            },
                        },
                }
            },
    }

/// `:type` never evaluates: the same load, elaboration and typecheck, then
/// the root's type.
def step_type (s : EvalSession) (candidate : String) (decls : List Decl)
    (root : String) (display : String) : IO (Pair EvalSession EvalResponse) :=
    match s {
        { file_path, module_name, affine_warn, cache, .. } =>
            do {
                let rewritten <- rewrite_lib_aliases_of file_path decls;
                let main : ModuleInfo :=
                    make_module_info (ModulePath.mk [Identifier.id module_name])
                        file_path rewritten;
                let lc <- load_modules_from_main main cache false;
                match lc.loaded {
                    Result.err e => do {
                        let s2 : EvalSession := { s with cache := lc.cache };
                        return (Pair.pair s2 (EvalResponse.eval_response_error e))
                    },
                    Result.ok loaded =>
                        match elaborate_loaded_modules_pure loaded false {
                            Result.err e => do {
                                let s2 : EvalSession := { s with cache := lc.cache };
                                return (Pair.pair s2 (EvalResponse.eval_response_error e))
                            },
                            Result.ok em => do {
                                let options : EvalOptions :=
                                    { fuel := -1, depth_limit := -1,
                                      affine := mode_of affine_warn, label := file_path,
                                      verbose := false, want_type := false,
                                      require_entry := true };
                                let target : EvalTarget :=
                                    { root := root,
                                      context_path := ModulePath.mk [Identifier.id module_name] };
                                let r <- Eval.type_of em options target;
                                match r {
                                    Result.ok typ => do {
                                        let s2 : EvalSession := { s with cache := lc.cache };
                                        return (Pair.pair s2
                                            (EvalResponse.eval_response_meta
                                                (String.concat display
                                                    (String.concat " : " typ))))
                                    },
                                    Result.err failure => do {
                                        let s2 : EvalSession := { s with cache := lc.cache };
                                        return (Pair.pair s2
                                            (EvalResponse.eval_response_error
                                                (describe_failure failure)))
                                    },
                                }
                            },
                        },
                }
            },
    }

// --- Small helpers ----------------------------------------------------

def mode_of (warn : Bool) : AffineMode :=
    if warn then AffineMode.affine_warn else AffineMode.affine_error

def describe_failure (f : EvalFailure) : String :=
    f.message

def append_line (source : String) (text : String) : String :=
    if String.is_empty source then text else String.concat source (String.concat "\n" text)

def expr_line (name : String) (text : String) : String :=
    String.concat "def " (String.concat name (String.concat " : _ := " text))

#[terminating]
def expr_name (n : I64) (source : String) : String :=
    let name : String := String.concat "__repl_expr_" (I64.to_string n)
    in
    if String.contains source name then expr_name (I64.add n 1) source else name

def declaration_starter (text : String) : Bool :=
    String.starts_with "#[" text
        || List.any (fn (word : String) => starts_word text word)
            ["def", "pub", "priv", "type", "struct", "class", "instance", "use",
             "open", "infix", "defmacro"]

def starts_word (text : String) (word : String) : Bool :=
    if Bool.not (String.starts_with word text)
    then false
    else
        let rest : String := String.drop (String.length word) text
        in
        String.is_empty rest
            || String.starts_with " " rest
            || String.starts_with "\t" rest
            || String.starts_with "(" rest
            || String.starts_with "{" rest
            || String.starts_with "[" rest
            || String.starts_with ":" rest

def join_lines (xs : List String) : String :=
    match xs {
        List.empty => "",
        List.cons x rest =>
            match rest {
                List.empty => x,
                List.cons _ _ => String.concat x (String.concat "\n" (join_lines rest)),
            },
    }

def help_text : String :=
    "commands:\n  :help           show this message\n  :quit, :q       leave the REPL\n  :reset          forget every definition entered so far\n  :type <expr>    print an expression's type without evaluating it"

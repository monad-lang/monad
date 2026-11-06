/// The backend's typed failures.
///
/// Mirrors `lang/typecheck/diagnostic.mo`: one diagnostic vocabulary and one
/// renderer, with no `Show` instance (a plain def has no dictionary
/// parameter). `CodegenError` stays `Copy` because the stage sites render it
/// for a `FAILED at stage` line and then return the same value; its fields
/// are therefore `String`/`I64` only, and the structured findings live in
/// `CodegenDiagnostic`, which is rendered and joined exactly once.
/// One finding from a codegen-owned fail-fast gate. The fields are the
/// values the message already names, so a caller can inspect a failure
/// without parsing prose.
pub type CodegenDiagnostic {
    monad_extern (link : String) (def_name : String),
    unwired_native (native : String) (def_name : String),
    unavailable_native (native : String) (def_name : String) (target : String) (kind : String) (reason : String),
    unavailable_extern (link : String) (def_name : String) (target : String) (kind : String) (reason : String),
    duplicate_export (name : String),
    export_main (name : String),
    export_dotted (name : String),
    export_abi (name : String),
    export_no_body (name : String),
    export_implicit (name : String),
    export_constraints (name : String),
    undesugared_struct_lit (def_name : String),
    undesugared_elim (def_name : String),
    duplicate_symbol (symbol : String),
    runtime_symbol_collision (symbol : String),
    ambiguous_owner (name : String) (from : String) (candidates : String),
    declared_and_imported (module : String) (name : String) (imported_from : String),
    no_declarer (name : String),
}

/// `#[export "c"]` messages all share this label.
def export_label (name : String) : String :=
    String.concat "`#[export \"c\"]` def `" (String.concat name "`")

/// The one place a diagnostic becomes text. Every arm reproduces the
/// message the `String`-returning validators composed before this type
/// existed, byte for byte.
pub def CodegenDiagnostic.render (d : CodegenDiagnostic) : String :=
    match d {
        CodegenDiagnostic.monad_extern link def_name =>
            String.concat "extern `" (String.concat link
                (String.concat "` on `" (String.concat def_name
                    "` binds a Monad runtime symbol; declare it as a #[native] in init/std instead"))),
        CodegenDiagnostic.unwired_native native def_name =>
            String.concat "native `" (String.concat native
                (String.concat "` (needed by def `" (String.concat def_name
                    "`) is not wired into the native backend -- it would silently compile to a 'return Unit' stub; add a monad_* runtime function + native_runtime_fn_name entry, or an inline native_op_table key"))),
        CodegenDiagnostic.unavailable_native native def_name target kind reason =>
            String.concat "native `" (String.concat native
                (String.concat "` (needed by def `" (String.concat def_name
                    (String.concat "`) is not available on target `" (String.concat target
                        (String.concat "` (" (String.concat kind (String.concat "): " reason)))))))),
        CodegenDiagnostic.unavailable_extern link def_name target kind reason =>
            String.concat "extern `" (String.concat link
                (String.concat "` (needed by def `" (String.concat def_name
                    (String.concat "`) is not available on target `" (String.concat target
                        (String.concat "` (" (String.concat kind (String.concat "): " reason)))))))),
        CodegenDiagnostic.duplicate_export name =>
            String.concat "duplicate `#[export \"c\"]` name `" (String.concat name "`"),
        CodegenDiagnostic.export_main name =>
            String.concat (export_label name) " cannot be `main`: the runtime entry renames that symbol",
        CodegenDiagnostic.export_dotted name =>
            String.concat (export_label name) " must be a single identifier segment; a dotted name is not a JS property",
        CodegenDiagnostic.export_abi name =>
            String.concat (export_label name) " must name the C ABI as `#[export \"c\"]`",
        CodegenDiagnostic.export_no_body name =>
            String.concat (export_label name) " needs a body: an export is the def's own code, not a foreign binding",
        CodegenDiagnostic.export_implicit name =>
            String.concat (export_label name) " cannot have implicit parameters: the export ABI passes only explicit i64 words",
        CodegenDiagnostic.export_constraints name =>
            String.concat (export_label name) " cannot have type-class constraints: no dictionary can cross the export ABI",
        CodegenDiagnostic.undesugared_struct_lit def_name =>
            String.concat "def `" (String.concat def_name
                "` contains a struct literal that never desugared to a constructor -- it would silently compile to a void placeholder; give the literal an explicit `: StructName` annotation, or bind it to an annotated local before passing it"),
        CodegenDiagnostic.undesugared_elim def_name =>
            String.concat "def `" (String.concat def_name
                "` contains a Term.elim that never desugared to a match -- codegen would crash; the elimination desugar pass (desugar_elims_decls) was skipped"),
        CodegenDiagnostic.duplicate_symbol symbol =>
            String.concat "two definitions share the LLVM symbol `" (String.concat symbol
                "` -- one of them would be silently dropped; give them distinct names or distinct modules"),
        CodegenDiagnostic.runtime_symbol_collision symbol =>
            String.concat "def `" (String.concat symbol
                "` collides with a runtime symbol of the same name -- rename the def"),
        CodegenDiagnostic.ambiguous_owner name from candidates =>
            String.concat "`" (String.concat name
                (String.concat "` is referenced from " (String.concat from
                    (String.concat " but declared in " (String.concat candidates
                        (String.concat " -- add an explicit `use <module> {" (String.concat name "}` to say which"))))))),
        CodegenDiagnostic.declared_and_imported module name imported_from =>
            String.concat "module " (String.concat module
                (String.concat " both declares `" (String.concat name
                    (String.concat "` and imports it from " (String.concat imported_from
                        " -- drop one, they are not interchangeable"))))),
        CodegenDiagnostic.no_declarer name =>
            String.concat "no module declares `" (String.concat name "`"),
    }

/// One stage's failure. Text is composed when the value is built, so every
/// field is `Copy` and the seven `FAILED at stage` sites can render the
/// error and still return it.
pub type CodegenError {
    diagnostics (text : String),
    qualify (text : String),
    undefined_symbols (text : String),
    elaboration (count : I64) (details : String),
    no_tests,
    internal (message : String),
}

pub instance Copy CodegenError {
    def copy (e : CodegenError) : Pair CodegenError CodegenError :=
        match e {
            CodegenError.diagnostics text =>
                Pair.pair (CodegenError.diagnostics text) (CodegenError.diagnostics text),
            CodegenError.qualify text =>
                Pair.pair (CodegenError.qualify text) (CodegenError.qualify text),
            CodegenError.undefined_symbols text =>
                Pair.pair (CodegenError.undefined_symbols text) (CodegenError.undefined_symbols text),
            CodegenError.elaboration count details =>
                Pair.pair (CodegenError.elaboration count details) (CodegenError.elaboration count details),
            CodegenError.no_tests => Pair.pair CodegenError.no_tests CodegenError.no_tests,
            CodegenError.internal message =>
                Pair.pair (CodegenError.internal message) (CodegenError.internal message),
        }
}

/// The complete rendered message, which is what the CLI, eval, tests and
/// slow tests print. Stage labels are still added by those callers.
pub def CodegenError.render (e : CodegenError) : String :=
    match e {
        CodegenError.diagnostics text => text,
        CodegenError.qualify text => text,
        CodegenError.undefined_symbols text => text,
        CodegenError.elaboration count details =>
            String.concat (I64.to_string count) (String.concat " reachable decl(s) did not elaborate: " details),
        CodegenError.no_tests => "no #[test] defs found",
        CodegenError.internal message => message,
    }

/// The one structural check callers make: "no tests" is a SKIP, not a
/// failure. It never compares rendered text.
pub def CodegenError.is_no_tests (e : CodegenError) : Bool :=
    match e {
        CodegenError.no_tests => true,
        _ => false,
    }

/// Wrap text rendered outside this mote (`lang`'s unresolved-class gate, the
/// best-effort elaborator) or a bare local failure.
pub def CodegenError.of_message (text : String) : CodegenError :=
    CodegenError.diagnostics text

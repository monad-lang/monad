/// Negative type-checking pins: illegal programs the checker must REJECT.
///
/// They go through `check_file_cached_from_source_ranged`, which runs the
/// same elaboration and the same per-declaration walk `monad check` uses,
/// with the ambient prelude/init/std tier included. That matters more than
/// the convenience: `typecheck_source` (in `typecheck_examples_tests.mo`)
/// builds a prelude-less synthetic scope, and a pin written against it can
/// be green while `monad check` accepts the identical source -- see
/// `implementations/match-arm-conversion-vacuous-in-check.md`. Every
/// rejection pin here is paired with an ACCEPTANCE source (`accepted`)
/// covering the same callees and types, so a rule that rejects everything,
/// or a fixture whose names never resolve, cannot pass.
///
/// Diagnostic text is asserted, not merely its presence: a pin that only
/// counts errors would go green on an unrelated unknown-name failure.
use lib::module {
  Diagnostic, check_file_cached_from_source_ranged, diagnostic_message,
  module_info_cache_empty, ranged_file_diagnostics,
}
use std::process {exec_cmd, process_id}
use std::test {Test.write_fixture}
open IO {println}

// --- Rendering diagnostics -------------------------------------------------
// Field reads are routed through typed accessors rather than written inline
// in a `#[test]` def: a test def that touches a struct field is the recorded
// self-hosted codegen hazard.

#[terminating]
def messages_of (ds : List Diagnostic) : List String :=
    match ds {
        List.empty => List.empty,
        List.cons d rest => List.cons (diagnostic_message d) (messages_of rest),
    }

#[terminating]
def joined (msgs : List String) : String :=
    match msgs {
        List.empty => "",
        List.cons m rest => String.concat m (String.concat "\n  " (joined rest)),
    }

/// The diagnostic rendered `... in <name>`, if the checker reported one for
/// that declaration.
#[terminating]
def message_named (name : String) (msgs : List String) : Option String :=
    match msgs {
        List.empty => Option.none,
        List.cons m rest =>
            if String.contains m (String.concat " in " name)
            then Option.some m
            else message_named name rest,
    }

// --- Fixtures --------------------------------------------------------------
// The source is checked from a BUFFER, but it must also exist on disk: the
// loader resolves the target module through `resolve_module_file`
// (`lang/src/module.mo`) before it ever looks at the supplied text, so a path
// nothing resolves to reports `Failed to load` instead of type-checking --
// which a count-only pin would read as success. Same shape as
// `decl_range_tests.mo`'s fixture. The `process_id` suffix keeps the sweep's
// parallel shards apart.
def probe_dir : String := "/tmp/monad_typecheck_negative_" ++ I64.to_string process_id

def probe_path : String := probe_dir ++ "/probe.mo"

#[partial]
def diagnostics_for (src : String) : IO (List String) := do {
    let _mk <- exec_cmd "mkdir" ["-p", probe_dir];
    let _w <- Test.write_fixture (Path.path probe_path) src;
    let checked <- check_file_cached_from_source_ranged module_info_cache_empty probe_path src false;
    return (messages_of (ranged_file_diagnostics checked))
}

/// Does checking `src` report a diagnostic naming `name` whose text contains
/// `needle`?
#[partial]
def rejected_with (name : String) (needle : String) (src : String) : IO Bool := do {
    let msgs <- diagnostics_for src;
    match message_named name msgs {
        Option.none => do {
            println ("MISSING: expected a diagnostic naming " ++ name ++ "; got:\n  " ++ joined msgs);
            return false
        },
        Option.some m =>
            if String.contains m needle
            then return true
            else do {
                println ("WRONG DIAGNOSTIC for " ++ name ++ " (expected text containing \"" ++ needle ++ "\")");
                return false
            },
    }
}

/// The control half: a well-typed source must produce NO diagnostics.
#[partial]
def accepted (src : String) : IO Bool := do {
    let msgs <- diagnostics_for src;
    match msgs {
        List.empty => return true,
        _ => do {
            println ("UNEXPECTED diagnostics:\n  " ++ joined msgs);
            return false
        },
    }
}

def mismatch : String := "type mismatch"

// --- Call arguments against the callee's Pi domain -------------------------

/// First-order: `style` wants `List String`, the argument is a `String`.
/// The declaration is deliberately the PARTIAL APPLICATION's own type
/// (`String -> I64`), so the def-boundary comparison agrees and only the
/// argument rule can reject this.
def first_order_source : String :=
    "def style (attrs : List String) (content : String) : I64 := 0\ndef css : String := \"x\"\ndef arg_first_order : String -> I64 := style css\n"

/// A literal argument: `take_i64` wants `I64`, the argument is a `String`.
def literal_arg_source : String :=
    "def take_i64 (x : I64) : I64 := x\ndef arg_literal : I64 := take_i64 \"s\"\n"

/// Higher-order: `needs` wants `I64 -> Msg`, the argument is a nullary
/// constructor value of type `Msg`. The call's own type is `Msg`, equal to
/// the declaration, so the def boundary cannot see it -- this is the shape
/// that compiled a garbage closure and overflowed the wasm stack.
def second_order_source : String :=
    "type Msg { started }\ndef needs (f : I64 -> Msg) : Msg := f 0i64\ndef arg_second_order : Msg := needs Msg.started\n"

/// A local FUNCTION VALUE's parameter: no def signature is involved, so
/// this is the ordinary application path's own check (a def call resolves
/// through the signature-driven path and never reaches it).
def local_apply_source : String :=
    "def danger (pick : String -> I64) : I64 := pick 1i64\n"

#[test]
def test_a_first_order_argument_of_the_wrong_type_is_rejected : IO Bool :=
    rejected_with "arg_first_order" mismatch first_order_source

#[test]
def test_an_argument_to_a_local_function_value_is_rejected : IO Bool :=
    rejected_with "danger" mismatch local_apply_source

#[test]
def test_a_literal_argument_of_the_wrong_type_is_rejected : IO Bool :=
    rejected_with "arg_literal" mismatch literal_arg_source

#[test]
def test_a_higher_order_argument_of_the_wrong_type_is_rejected : IO Bool :=
    rejected_with "arg_second_order" mismatch second_order_source

#[test]
def test_correct_arguments_and_guarded_shapes_are_accepted : IO Bool :=
    accepted (
        "def style (attrs : List String) (content : String) : I64 := 0\n"
        ++ "def attrs0 : List String := List.empty\n"
        ++ "def arg_ok : I64 := style attrs0 \"b\"\n"
        ++ "type Msg { started }\n"
        ++ "def needs (f : I64 -> Msg) : Msg := f 0i64\n"
        ++ "def mk_msg (x : I64) : Msg := Msg.started\n"
        ++ "def arg_ok2 : Msg := needs mk_msg\n"
        // an uninstantiated type variable in the parameter must stay
        // permissive (the guard `body_type_error` documents)
        ++ "def len {A : Type} (xs : List A) : I64 := 0\n"
        ++ "def arg_generic : I64 := len [1, 2]\n"
        // a do-bind's continuation lambda carries a hole binder
        ++ "def m : IO I64 := IO.pure 1\n"
        ++ "def arg_do : IO I64 := do { let x <- m; return x }\n"
        // a local function value applied at its own domain
        ++ "def safe (pick : String -> I64) : I64 := pick \"s\"\n"
        // a constructor WITH fields passed as a function value: the
        // checker types a constructor reference as its owning type, so
        // this must stay accepted until constructor-as-value typing lands
        ++ "type Box { box (value : I64) }\n"
        ++ "def use_box (f : I64 -> Box) : Box := f 1i64\n"
        ++ "def box_ok : Box := use_box Box.box\n")

// --- `if` / `else` arms ----------------------------------------------------

/// The then-arm is `IO I64` and the else-arm `IO String`; the declaration
/// equals the THEN type, so only the branch comparison can reject this.
///
/// A CONCRETE mismatch on purpose. An arm whose type still carries an
/// unsolved type variable (`IO.pure (Result.ok Unit.unit)` infers
/// `IO (Result _ _)`) is skipped by `body_type_error`'s typevar guard --
/// pinned as accepted below, since `docs/src/bootstrap-host.md` states it.
def if_source : String :=
    "def if_branches : IO I64 := if true then IO.pure 0 else IO.pure \"s\"\n"

#[test]
def test_if_arms_of_different_types_are_rejected : IO Bool :=
    rejected_with "if_branches" mismatch if_source

#[test]
def test_if_arms_of_the_same_type_are_accepted : IO Bool :=
    accepted "def if_ok : IO I64 := if true then IO.pure 0 else IO.pure 1\n"

/// The typevar guard's permissive half. Deleting the guard must show up
/// here, not as a silent divergence from the Rust host.
#[test]
def test_if_arms_whose_type_still_carries_a_type_variable_are_accepted : IO Bool :=
    accepted "def if_hole_arm : IO I64 := if true then IO.pure 0 else IO.pure (Result.ok Unit.unit)\n"

// --- Struct literals and updates -------------------------------------------

def struct_unknown_source : String :=
    "struct P { x : I64, y : I64 }\ndef struct_unknown : P := { x := 1, y := 2, nosuch := 3 }\n"

def struct_short_source : String :=
    "struct P { x : I64, y : I64 }\ndef struct_short : P := { x := 1 }\n"

def struct_update_source : String :=
    "struct P { x : I64, y : I64 }\ndef struct_update_unknown (p : P) : P := { p with nosuch := 3 }\n"

#[test]
def test_a_struct_literal_with_an_unknown_field_is_rejected : IO Bool :=
    rejected_with "struct_unknown" "unknown field `nosuch`" struct_unknown_source

#[test]
def test_a_struct_literal_missing_a_required_field_is_rejected : IO Bool :=
    rejected_with "struct_short" "missing required field `y`" struct_short_source

#[test]
def test_a_struct_update_with_an_unknown_field_is_rejected : IO Bool :=
    rejected_with "struct_update_unknown" "unknown field `nosuch`" struct_update_source

#[test]
def test_complete_literals_and_defaulted_omissions_are_accepted : IO Bool :=
    accepted (
        "struct P { x : I64, y : I64 }\n"
        ++ "def complete : P := { x := 1, y := 2 }\n"
        ++ "struct Q { x : I64, y : I64 := 7 }\n"
        ++ "def defaulted : Q := { x := 1 }\n"
        ++ "def updated (p : P) : P := { p with y := 3 }\n")

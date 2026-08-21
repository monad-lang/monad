/// Human-readable rendering for `TypeError` (`lang/types.mo`) — the
/// type-checking counterpart to `lang/parser/diagnostic.mo`'s
/// `render_parse_error`, mirroring how the Rust reference splits parse
/// vs. type diagnostics across `core/src/parser/error.rs` and
/// `core/src/eval/type.rs::type_error_as_diagnostics`.
///
/// Unlike `ParseError`, `TypeError` (and `Term` generally) carries no
/// source location at all — there is no span/offset anywhere in the AST
/// once parsing is done. So a rendered `TypeError` can say *which
/// declaration* failed and *why*, but not *line:column* the way a parse
/// error can — `render_type_error` takes a `context_name` (typically a
/// declaration's name) to stand in for that missing location. Threading
/// real spans through `Term` construction across the whole grammar
/// would be a much larger project and isn't attempted here.

use lang.types {NameRef, TypeError, show_identifier, show_module_path, show_operator}
use lang.pretty {show_term}

/// `NameRef` (`lang/types.mo`) has no `Show`/to-string helper of its
/// own yet — the three variants wrap `Identifier`/`ModulePath`/
/// `Operator`, each of which already has one.
#[partial]
def name_ref_to_string (n : NameRef) : String :=
	match n {
		NameRef.nid id => show_identifier id,
		NameRef.nmp mp => show_module_path mp,
		NameRef.nop op => show_operator op,
	}

/// A human-readable description of what went wrong — one line per
/// `TypeError` variant (`lang/types.mo:252`).
#[partial]
def type_error_message (e : TypeError) : String :=
	match e {
		TypeError.mismatch expected actual =>
			String.concat "type mismatch: expected " (String.concat (show_term expected) (String.concat ", found " (show_term actual))),
		TypeError.unknown_var name =>
			String.concat "unknown variable '" (String.concat (name_ref_to_string name) "'"),
		TypeError.unknown_type name =>
			String.concat "unknown type '" (String.concat (name_ref_to_string name) "'"),
		TypeError.unknown_constructor name =>
			String.concat "unknown constructor '" (String.concat (name_ref_to_string name) "'"),
		TypeError.not_a_function term =>
			String.concat "not a function: " (show_term term),
		TypeError.not_a_type term =>
			String.concat "not a type: " (show_term term),
		TypeError.infinite_type term =>
			String.concat "infinite type: " (show_term term),
		TypeError.custom msg => msg,
	}

/// Render a full diagnostic for a type error — same visual family as
/// `render_parse_error`'s header/arrow-line
/// (`lang/parser/diagnostic.mo`), just without a line:col (see this
/// file's header comment).
#[partial]
def render_type_error (context_name : String) (path : Option String) (e : TypeError) : String :=
	let msg : String := type_error_message e in
	let header : String := String.concat "error: " (String.concat msg (String.concat " in " (String.concat context_name "\n"))) in
	let path_str : String := match path {
		Option.some p => p,
		Option.none => "",
	} in
	String.concat header (String.concat "  --> " (String.concat path_str "\n"))

// --- Tests ---

#[test]
def test_type_error_message_mismatch : Bool :=
	String.beq (type_error_message (TypeError.mismatch (Term.type_ 1) (Term.type_ 2))) "type mismatch: expected Type, found Type 1"

#[test]
def test_type_error_message_unknown_var : Bool :=
	String.beq (type_error_message (TypeError.unknown_var (NameRef.nid (Identifier.id "foo")))) "unknown variable 'foo'"

#[test]
def test_type_error_message_unknown_type : Bool :=
	String.beq (type_error_message (TypeError.unknown_type (NameRef.nid (Identifier.id "Bar")))) "unknown type 'Bar'"

#[test]
def test_type_error_message_unknown_constructor : Bool :=
	String.beq (type_error_message (TypeError.unknown_constructor (NameRef.nid (Identifier.id "Baz")))) "unknown constructor 'Baz'"

#[test]
def test_type_error_message_custom : Bool :=
	String.beq (type_error_message (TypeError.custom "something went wrong")) "something went wrong"

#[test]
def test_render_type_error_includes_context_and_path : Bool :=
	let rendered : String := render_type_error "my_def" (Option.some "examples/foo.mo") (TypeError.custom "bad thing") in
	String.contains rendered "error: bad thing in my_def"
		&& String.contains rendered "--> examples/foo.mo"

#[test]
def test_render_type_error_no_path : Bool :=
	let rendered : String := render_type_error "my_def" Option.none (TypeError.custom "bad thing") in
	String.contains rendered "error: bad thing in my_def"
		&& String.contains rendered "-->"

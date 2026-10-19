/// Declaration ranges: the positional contract, the offsets, and the two
/// ways a diagnostic gets a range.
///
/// The whole navigation half of the language server rests on the claim that
/// `decls_parser_located_with_ranges` returns one `SourceRange` per
/// declaration, IN ORDER. That claim is not enforced by any type, and a
/// later change that filtered or expanded a declaration inside
/// `lower_parse_decls`'s 1:1 map would shift every range from that point on
/// -- silently, and only in the presence of a diagnostic. So the count
/// equality is asserted here rather than argued in a comment.
///
/// Field reads are routed through typed accessor defs (`range_start_offset`,
/// `decl_range_span`, ...) rather than written inline: a `#[test]` def that
/// touches a struct field is the recorded self-hosted codegen hazard -- the
/// def picks up the FIELD's LLVM type as its own return type -- and nesting
/// two different field types in one def is exactly that shape.
///
/// `located_decl_list`/`located_decl_spans` come from `lib::module` (the
/// accessors), while `LocatedDecls` itself is `lib::parser`'s -- the struct
/// stays package-private to the parser, only the accessors cross.
use std::test {Test.write_fixture}
use lib::types {Location, SourceRange}
use lib::module {
  DeclRange, Diagnostic, check_file_cached_from_source_ranged,
  decl_range_kind, decl_range_name, decl_range_span, decl_ranges_of_source,
  diagnostic_message, diagnostic_range, located_decl_list, located_decl_spans,
  module_info_cache_empty, ranged_file_diagnostics,
}
use lib::parser {LocatedDecls, decls_parser_located_with_ranges}
use parsec::core {fail, success}
use std::list {List.length}
open IO {println}
use std::process {exec_cmd, process_id}

// --- Accessors: one field read each, one explicit return type each ---

def range_start (r : SourceRange) : Location := r.start

def range_end (r : SourceRange) : Location := r.end

def loc_offset (l : Location) : I64 := l.offset

def loc_line (l : Location) : I64 := l.line

def loc_column (l : Location) : I64 := l.column

def range_start_offset (r : SourceRange) : I64 := loc_offset (range_start r)

def range_end_offset (r : SourceRange) : I64 := loc_offset (range_end r)

def range_start_line (r : SourceRange) : I64 := loc_line (range_start r)

def range_start_column (r : SourceRange) : I64 := loc_column (range_start r)

def located_range_count (l : LocatedDecls) : I64 := List.length (located_decl_spans l)

def located_decl_count (l : LocatedDecls) : I64 := List.length (located_decl_list l)

// --- Fixtures ---
//
// Two defs, one per line, so the offsets are arithmetic a reader can check
// by hand: the second `def` starts at byte 17, line 2, column 1.

def two_def_source : String := "def a : I64 := 1\ndef b : I64 := 2\n"

/// One of each kind that carries a name, for the outline's name/kind pair.
def kind_source : String :=
    "def a : I64 := 1\ntype Maybe A { some (a : A), none }\nstruct S { x : I64 }\nclass Show A { def show (a : A) : String }\n"

/// An undefined name, so this is a real diagnostic -- a clean buffer would
/// make the ranged check's assertion vacuous.
def probe_source : String :=
    "def good (x : I64) : I64 := x\ndef bad (x : I64) : I64 := no_such_name x\n"

/// Malformed on purpose: an unterminated group, which the lenient top-level
/// walk truncates rather than failing (see `decls_try`).
def broken_source : String := "def bad ((( :=\n"

/// `process_id` in the path, not a fixed name: the sweep runs sharded and a
/// shared /tmp path collides across parallel runs.
def probe_dir : String := "/tmp/monad_decl_range_" ++ I64.to_string process_id

// --- The positional contract (Risk #7) ---

/// One range per declaration. THE pin.
def counts_agree (src : String) : Bool :=
    match decls_parser_located_with_ranges src {
        ParseResult.fail _e => true,
        ParseResult.success _rem located =>
            I64.beq (located_decl_count located) (located_range_count located),
    }

#[test]
def test_decl_ranges_count_matches_decl_count_on_two_defs : Bool :=
    counts_agree two_def_source

#[test]
def test_decl_ranges_count_matches_decl_count_on_four_kinds : Bool :=
    counts_agree kind_source

#[test]
def test_decl_ranges_count_matches_decl_count_on_a_use_and_open : Bool :=
    counts_agree "use prelude\nopen IO\ndef z : I64 := 0\n"

/// The same pin one level up: the public table's length is the parse's own
/// declaration count, so nothing is dropped by the zip either.
#[test]
def test_decl_ranges_of_source_length_matches_the_parse : Bool :=
    I64.beq (List.length (decl_ranges_of_source kind_source)) 4

// --- Order and exact offsets ---

/// Starts strictly increase down the file. A mis-alignment (one decl's range
/// handed to the next) is exactly what this catches, and it is the failure
/// the count test above cannot see.
#[test]
def test_decl_ranges_are_in_source_order : Bool :=
    match decl_ranges_of_source two_def_source {
        List.empty => false,
        List.cons first rest => match rest {
            List.empty => false,
            List.cons second _more =>
                I64.lt (range_start_offset (decl_range_span first)) (range_start_offset (decl_range_span second)),
        },
    }

/// Hand-computed: `def a` at byte 0 line 1, `def b` at byte 17 line 2.
/// Offsets are 0-based and lines/columns 1-based, matching
/// `resolve_offsets_in_file`'s own starting `Location.mk 0 1 1`.
#[test]
def test_decl_range_offsets_and_lines_are_exact : Bool :=
    match decl_ranges_of_source two_def_source {
        List.empty => false,
        List.cons first rest => match rest {
            List.empty => false,
            List.cons second _more =>
                I64.beq (range_start_offset (decl_range_span first)) 0
                    && I64.beq (range_start_line (decl_range_span first)) 1
                    && I64.beq (range_start_column (decl_range_span first)) 1
                    && I64.beq (range_start_offset (decl_range_span second)) 17
                    && I64.beq (range_start_line (decl_range_span second)) 2
                    && I64.beq (range_start_column (decl_range_span second)) 1,
        },
    }

/// Every range is non-empty and ends no earlier than it starts. Guards the
/// `total - start_rem` / `total - end_rem` arithmetic in both directions.
#[test]
def test_decl_range_ends_follow_their_starts : Bool :=
    spans_are_ordered (decl_ranges_of_source kind_source)

def spans_are_ordered (rs : List DeclRange) : Bool :=
    match rs {
        List.empty => true,
        List.cons dr rest =>
            I64.lt (range_start_offset (decl_range_span dr)) (range_end_offset (decl_range_span dr))
                && spans_are_ordered rest,
    }

// --- Names and kinds ---

def kind_of (rs : List DeclRange) (n : String) : String :=
    match rs {
        List.empty => "<missing>",
        List.cons dr rest =>
            if String.beq (decl_range_name dr) n then decl_range_kind dr else kind_of rest n,
    }

/// The four cases where `collect_decl_rems` alone yields nothing -- a def's
/// range would come from its body wrapper, but a `type`, a `struct` and a
/// `class` have no body wrapper at all. This is the whole reason the span
/// table exists rather than reading body wrappers everywhere.
#[test]
def test_decl_ranges_name_the_four_named_kinds : Bool :=
    let rs : List DeclRange := decl_ranges_of_source kind_source in
    String.beq (kind_of rs "a") "def"
        && String.beq (kind_of rs "Maybe") "type"
        && String.beq (kind_of rs "S") "struct"
        && String.beq (kind_of rs "Show") "class"

// --- Ranged diagnostics ---

/// The integration pin for the ranged check: a real type error on line 2
/// comes back with a range whose start IS line 2.
///
/// This also settles a question reading could not: the checker walks
/// `ElaboratedModules.target_decls`, and the range lookup keys on the name
/// `decl_name_and_kind` produces. If elaboration qualified those names, the
/// lookup would miss and this would report `Option.none`.
#[test]
def test_ranged_check_ranges_a_type_error : IO Bool := do {
    exec_cmd "mkdir" ["-p", probe_dir];
    let path : String := probe_dir ++ "/probe.mo";
    let _w <- Test.write_fixture (Path.path path) probe_source;
    let checked <- check_file_cached_from_source_ranged module_info_cache_empty path probe_source false;
    let diags : List Diagnostic := ranged_file_diagnostics checked;
    match diags {
        List.empty => do { println "VACUOUS: the ranged check reported nothing"; return false },
        List.cons d _rest => do {
            println ("ranged type error: " ++ diagnostic_message d);
            match diagnostic_range d {
                Option.none => do { println "NO RANGE on the type-error diagnostic"; return false },
                Option.some r => do {
                    println ("  starts at line " ++ I64.to_string (range_start_line r));
                    return (I64.beq (range_start_line r) 2)
                },
            }
        },
    }
}

/// A buffer that does not parse gets a range too -- which is the common case
/// in an editor, and the one the lenient parser makes easy to get wrong:
/// `decls_try` reports SUCCESS with the declarations it managed to read, so
/// the diagnostic has to come from the non-empty remainder, not from a
/// `ParseResult.fail`.
#[test]
def test_ranged_check_ranges_a_parse_error : IO Bool := do {
    exec_cmd "mkdir" ["-p", probe_dir];
    let path : String := probe_dir ++ "/broken.mo";
    let checked <- check_file_cached_from_source_ranged module_info_cache_empty path broken_source false;
    let diags : List Diagnostic := ranged_file_diagnostics checked;
    match diags {
        List.empty => do { println "VACUOUS: no parse diagnostic"; return false },
        List.cons d _rest => do {
            println ("ranged parse error: " ++ diagnostic_message d);
            match diagnostic_range d {
                Option.none => do { println "NO RANGE on the parse diagnostic"; return false },
                Option.some r => do {
                    println ("  starts at line " ++ I64.to_string (range_start_line r));
                    return (I64.gt (List.length diags) 0)
                },
            }
        },
    }
}

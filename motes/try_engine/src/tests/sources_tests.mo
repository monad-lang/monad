/// Tests for the framed prelude sources the page hands the engine: the
/// record format (`parse_sources`) and the module identity a served path
/// names (`identity_of_path`). The real `.mo` files are covered by
/// `pipeline_tests.mo`; the JS encoder that has to agree with this parser
/// is covered by `wasm/web/try_worker_smoke.mjs` against the served
/// directory.

use lib::sources {SourceModule, identity_of_path, parse_sources}

/// The wire format, spelled once for the tests: `<path_len> <src_len>\n`
/// then the path bytes then the source bytes.
def record (path : String) (source : String) : String :=
    String.concat (I64.to_string (String.length path))
        (String.concat " "
            (String.concat (I64.to_string (String.length source))
                (String.concat "\n" (String.concat path source))))

def dotted (segs : List String) : String :=
    match segs {
        List.empty => "",
        List.cons s rest =>
            match rest {
                List.empty => s,
                List.cons _ _ => String.concat s (String.concat "." (dotted rest)),
            },
    }

def one_record (payload : String) : Option SourceModule :=
    match parse_sources payload {
        Result.ok modules =>
            match modules {
                List.cons m rest => if List.is_empty rest then Option.some m else Option.none,
                List.empty => Option.none,
            },
        Result.err _ => Option.none,
    }

def is_error (payload : String) : Bool :=
    match parse_sources payload {
        Result.ok _ => false,
        Result.err _ => true,
    }

#[test]
def test_empty_payload_is_no_modules : Bool :=
    match parse_sources "" {
        Result.ok modules => List.is_empty modules,
        Result.err _ => false,
    }

/// A hand-written payload, so a change to the format cannot be absorbed by
/// the `record` helper above: "init/src/math.mo" is 16 bytes and
/// "def x : I64 := 1\n" is 17.
#[test]
def test_parse_sources_reads_a_literal_record : Bool :=
    match one_record "16 17\ninit/src/math.modef x : I64 := 1\n" {
        Option.some m =>
            String.beq m.file_path "init/src/math.mo"
                && String.beq m.source "def x : I64 := 1\n"
                && String.beq m.mote "init"
                && String.beq (dotted m.segments) "init.math",
        Option.none => false,
    }

/// A source containing newlines, spaces and a `//` comment needs no
/// escaping: the declared lengths, not a delimiter, end the record.
#[test]
def test_source_text_is_taken_verbatim : Bool :=
    let source : String := "// a comment\ndef main : I64 := 2 + 3\n"
    in
    match one_record (record "init/src/math.mo" source) {
        Option.some m => String.beq m.source source,
        Option.none => false,
    }

#[test]
def test_two_records_keep_their_order : Bool :=
    let payload : String :=
        String.concat (record "init/src/math.mo" "def a : I64 := 1\n")
            (record "init/src/list.mo" "def b : I64 := 2\n")
    in
    match parse_sources payload {
        Result.ok modules =>
            match modules {
                List.cons first rest =>
                    match rest {
                        List.cons second tail =>
                            List.is_empty tail
                                && String.beq first.file_path "init/src/math.mo"
                                && String.beq second.file_path "init/src/list.mo",
                        List.empty => false,
                    },
                List.empty => false,
            },
        Result.err _ => false,
    }

#[test]
def test_header_without_a_space_is_rejected : Bool :=
    is_error "16\ninit/src/math.modef x : I64 := 1\n"

#[test]
def test_header_without_a_newline_is_rejected : Bool :=
    is_error "16 17"

#[test]
def test_non_decimal_length_is_rejected : Bool :=
    is_error "16 x\ndef x : I64 := 1\n"

#[test]
def test_truncated_record_is_rejected : Bool :=
    is_error "16 99\ninit/src/math.mo"

/// The lib root is the mote itself, the prelude is ambient, and a nested
/// module keeps its path -- the same identities the compiler's loader
/// assigns, so `use init::…` resolves against the served files.
#[test]
def test_identity_of_a_served_path : Bool :=
    match identity_of_path "init/src/lib.mo" {
        Result.ok ident =>
            match ident {
                Pair.pair segments mote =>
                    String.beq mote "init" && String.beq (dotted segments) "init",
            },
        Result.err _ => false,
    }

#[test]
def test_identity_of_the_prelude : Bool :=
    match identity_of_path "init/src/prelude.mo" {
        Result.ok ident =>
            match ident {
                Pair.pair segments mote =>
                    String.beq mote "init" && String.beq (dotted segments) "prelude",
            },
        Result.err _ => false,
    }

#[test]
def test_identity_of_a_nested_module : Bool :=
    match identity_of_path "init/src/parser/ast.mo" {
        Result.ok ident =>
            match ident {
                Pair.pair segments mote =>
                    String.beq mote "init" && String.beq (dotted segments) "init.parser.ast",
            },
        Result.err _ => false,
    }

#[test]
def test_path_outside_a_mote_is_rejected : Bool :=
    match identity_of_path "init/math.mo" {
        Result.ok _ => false,
        Result.err _ => true,
    }

#[test]
def test_path_with_an_empty_segment_is_rejected : Bool :=
    match identity_of_path "init/src//math.mo" {
        Result.ok _ => false,
        Result.err _ => true,
    }

#[test]
def test_path_without_the_mo_suffix_is_rejected : Bool :=
    match identity_of_path "init/src/math" {
        Result.ok _ => false,
        Result.err _ => true,
    }

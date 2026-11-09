/// Phase 2 tests — URI parsing, percent-encoding, query (de)coding.

use http::strings {Strings.split_on}
use http::types {Uri, uri}
use http::uri {
    Uri.effective_port, Uri.format, Uri.format_query, Uri.parse, Uri.parse_query,
    Uri.percent_decode, Uri.percent_encode, Uri.resolve, Uri.same_origin,
}

def expect_ok (got : Result String String) (want : String) : Bool :=
    match got {
        Result.ok r => r == want,
        Result.err _ => false
    }

def expect_err (got : Result String String) : Bool :=
    match got {
        Result.ok _ => false,
        Result.err _ => true
    }

#[test]
def test_percent_encode_space : Bool :=
    Uri.percent_encode "hello world" == "hello%20world"

#[test]
def test_percent_encode_unreserved : Bool :=
    Uri.percent_encode "aA0.-_~b" == "aA0.-_~b"

#[test]
def test_percent_encode_reserved : Bool :=
    // "<" (0x3C) is not unreserved → %3C
    Uri.percent_encode "<" == "%3C"

#[test]
def test_percent_decode_basic : Bool :=
    expect_ok (Uri.percent_decode "hello%20world") "hello world"

#[test]
def test_percent_decode_lowercase_hex : Bool :=
    expect_ok (Uri.percent_decode "hello%2fworld") "hello/world"

#[test]
def test_percent_decode_passes_through : Bool :=
    expect_ok (Uri.percent_decode "plain") "plain"

#[test]
def test_percent_decode_truncated : Bool :=
    expect_err (Uri.percent_decode "ab%2")

#[test]
def test_percent_decode_bad_hex : Bool :=
    expect_err (Uri.percent_decode "ab%GG")

#[test]
def test_percent_roundtrip : Bool :=
    let raw : String := String.from_list [104u8, 105u8, 32u8, 33u8] in
    expect_ok (Uri.percent_decode (Uri.percent_encode raw)) raw

#[test]
def test_split_on : Bool :=
    match Strings.split_on "," "a,b,c" {
        List.empty => false,
        List.cons a r1 =>
            match r1 {
                List.empty => false,
                List.cons b r2 =>
                    match r2 {
                        List.empty => false,
                        List.cons c r3 =>
                            match r3 {
                                List.empty => a == "a" && b == "b" && c == "c",
                                List.cons _ _ => false
                            }
                    }
            }
    }

#[test]
def test_split_on_trailing : Bool :=
    // "a," -> ["a", ""]
    match Strings.split_on "," "a," {
        List.empty => false,
        List.cons a r1 =>
            match r1 {
                List.empty => false,
                List.cons b r2 =>
                    match r2 {
                        List.empty => a == "a" && b == "",
                        List.cons _ _ => false
                    }
            }
    }

#[test]
def test_parse_uri_full : Bool :=
    match Uri.parse "https://user@example.com:8080/path?x=1#frag" {
        Result.err _ => false,
        Result.ok u =>
            match u {
                Uri.uri scheme userinfo host port path query fragment =>
                    scheme == "https"
                        && userinfo == Option.some "user"
                        && host == "example.com"
                        && port == Option.some 8080u16
                        && path == "/path"
                        && query == Option.some "x=1"
                        && fragment == Option.some "frag"
            }
    }

#[test]
def test_parse_uri_no_port : Bool :=
    match Uri.parse "http://example.com/path" {
        Result.err _ => false,
        Result.ok u =>
            match u {
                Uri.uri scheme userinfo host port path query fragment =>
                    scheme == "http"
                        && userinfo == Option.none
                        && host == "example.com"
                        && port == Option.none
                        && path == "/path"
                        && query == Option.none
                        && fragment == Option.none
            }
    }

#[test]
def test_parse_uri_relative : Bool :=
    match Uri.parse "/path/to/thing" {
        Result.err _ => false,
        Result.ok u =>
            match u {
                Uri.uri scheme userinfo host port path query fragment =>
                    scheme == ""
                        && host == ""
                        && port == Option.none
                        && path == "/path/to/thing"
                        && query == Option.none
                        && fragment == Option.none
            }
    }

#[test]
def test_parse_uri_only_fragment : Bool :=
    match Uri.parse "#sec" {
        Result.err _ => false,
        Result.ok u =>
            match u {
                Uri.uri scheme userinfo host port path query fragment =>
                    fragment == Option.some "sec" && path == ""
            }
    }

#[test]
def test_format_uri_full : Bool :=
    match Uri.parse "https://user@example.com:8080/path?x=1#frag" {
        Result.err _ => false,
        Result.ok u => Uri.format u == "https://user@example.com:8080/path?x=1#frag"
    }

#[test]
def test_format_uri_no_authority : Bool :=
    match Uri.parse "mailto:foo@example.com" {
        Result.err _ => false,
        Result.ok u => Uri.format u == "mailto:foo@example.com"
    }

#[test]
def test_parse_query : Bool :=
    match Uri.parse_query "a=1&b=2" {
        List.empty => false,
        List.cons h1 r1 =>
            match h1 {
                Pair.pair k1 v1 =>
                    match r1 {
                        List.empty => false,
                        List.cons h2 r2 =>
                            match h2 {
                                Pair.pair k2 v2 =>
                                    match r2 {
                                        List.empty => k1 == "a" && v1 == "1" && k2 == "b" && v2 == "2",
                                        List.cons _ _ => false
                                    }
                            }
                    }
            }
    }

#[test]
def test_format_query : Bool :=
    Uri.format_query (List.cons (Pair.pair "a" "1") (List.cons (Pair.pair "b" "2") List.empty)) == "a=1&b=2"

#[test]
def test_format_query_empty : Bool :=
    Uri.format_query List.empty == ""

#[test]
def test_parse_query_decodes : Bool :=
    match Uri.parse_query "q=hello%20world" {
        List.empty => false,
        List.cons h1 r1 =>
            match h1 {
                Pair.pair k1 v1 =>
                    match r1 {
                        List.empty => k1 == "q" && v1 == "hello world",
                        List.cons _ _ => false
                    }
            }
    }

#[test]
def test_resolve_absolute : Bool :=
    match Uri.parse "https://a.com/b" {
        Result.err _ => false,
        Result.ok base =>
            match Uri.parse "http://x.com/y" {
                Result.err _ => false,
                Result.ok ref =>
                    match Uri.resolve base ref {
                        Uri.uri scheme _ host _ path _ _ =>
                            scheme == "http" && host == "x.com" && path == "/y"
                    }
            }
    }

#[test]
def test_resolve_relative : Bool :=
    match Uri.parse "https://a.com/b" {
        Result.err _ => false,
        Result.ok base =>
            match Uri.parse "/c" {
                Result.err _ => false,
                Result.ok ref =>
                    match Uri.resolve base ref {
                        Uri.uri scheme _ host _ path _ _ =>
                            scheme == "https" && host == "a.com" && path == "/c"
                    }
            }
    }

// ── formatting and resolution ──────────────────────────────────────────
//
// `Uri.format` joined the authority to the path with nothing in between, and
// `Uri.resolve` copied the reference's path verbatim while dropping the
// base's. Those are one defect, visible only through the pair, so these tests
// state an absolute URL and exercise parse → resolve → format as a whole.

/// Parse, then render back. `<err>` makes a parse failure a visible mismatch
/// rather than a silent empty string.
def uri_fmt (s : String) : String :=
    match Uri.parse s {
        Result.err _ => "<err>",
        Result.ok u => Uri.format u
    }

/// Resolve `ref` against `base` and render the result.
def uri_resolved (base : String) (ref : String) : String :=
    match Uri.parse base {
        Result.err _ => "<base err>",
        Result.ok b =>
            match Uri.parse ref {
                Result.err _ => "<ref err>",
                Result.ok r => Uri.format (Uri.resolve b r)
            }
    }

/// The motivating case: `Location: foo` under `/a/b` is `/a/foo`, and the
/// separator is what made it `http://example.coma/foo` before.
#[test]
def test_resolve_relative_location_format : Bool :=
    uri_resolved "http://example.com/a/b" "foo" == "http://example.com/a/foo"

/// A relative reference replaces only the base's last segment.
#[test]
def test_resolve_parent_segment : Bool :=
    uri_resolved "https://a.com/x/y/z" "w" == "https://a.com/x/y/w"

/// A base that is nothing but an authority still merges to a rooted path.
#[test]
def test_resolve_against_authority_only : Bool :=
    uri_resolved "http://example.com" "foo" == "http://example.com/foo"

/// An absolute reference path replaces the base's path whole.
#[test]
def test_resolve_absolute_path : Bool :=
    uri_resolved "https://a.com/x/y" "/z" == "https://a.com/z"

/// An empty reference keeps the base's path...
#[test]
def test_resolve_empty_ref_keeps_path : Bool :=
    uri_resolved "http://example.com/a/b?x=1" "" == "http://example.com/a/b?x=1"

/// ...and a query-only reference does too, replacing only the query. The
/// path used to be wiped here, pointing the redirect at the host root.
#[test]
def test_resolve_query_only_keeps_path : Bool :=
    uri_resolved "http://example.com/a/b?x=1" "?y=2" == "http://example.com/a/b?y=2"

/// A fragment-only reference keeps the base's path *and* query.
#[test]
def test_resolve_fragment_only_keeps_path_and_query : Bool :=
    uri_resolved "http://example.com/a/b?x=1" "#f" == "http://example.com/a/b?x=1#f"

/// A scheme-relative reference takes the reference's authority and the base's
/// scheme.
#[test]
def test_resolve_scheme_relative_ref : Bool :=
    uri_resolved "https://a.com/x" "//other/y" == "https://other/y"

// ── authority round-trips ──────────────────────────────────────────────

/// An authority with no path must not gain a trailing `/` from the join.
#[test]
def test_format_authority_without_path : Bool :=
    uri_fmt "http://example.com" == "http://example.com"

#[test]
def test_format_authority_port_without_path : Bool :=
    uri_fmt "http://example.com:8080" == "http://example.com:8080"

/// A bare `/` path is preserved, not merged into an empty one.
#[test]
def test_format_authority_root_path : Bool :=
    uri_fmt "http://example.com/" == "http://example.com/"

#[test]
def test_format_authority_query_only : Bool :=
    uri_fmt "http://example.com?x=1" == "http://example.com?x=1"

/// `//host/x` is scheme-relative: the host is the authority, not part of the
/// path. It used to parse as the path `//host/x` with no host at all, which
/// `Uri.format` then rendered back unchanged -- so the bug only showed once
/// the reference was resolved against a base.
#[test]
def test_parse_scheme_relative : Bool :=
    match Uri.parse "//other.example/x" {
        Result.err _ => false,
        Result.ok u =>
            match u {
                Uri.uri scheme _ host port path _ _ =>
                    scheme == "" && host == "other.example" && port == Option.none && path == "/x"
            }
    }

#[test]
def test_format_scheme_relative : Bool :=
    uri_fmt "//other.example/x" == "//other.example/x"

#[test]
def test_parse_scheme_relative_with_port : Bool :=
    match Uri.parse "//other.example:8080/x" {
        Result.err _ => false,
        Result.ok u =>
            match u {
                Uri.uri _ _ host port _ _ _ => host == "other.example" && port == Option.some 8080u16
            }
    }

/// `//` alone is an empty authority, which is not useful as an authority, so
/// it stays a path and still round-trips.
#[test]
def test_parse_double_slash_alone_roundtrips : Bool :=
    uri_fmt "//" == "//"

// ── port range ─────────────────────────────────────────────────────────

/// True when a URI parse failed.
def uri_parse_fails (got : Result String Uri) : Bool :=
    match got {
        Result.err _ => true,
        Result.ok _ => false
    }

/// `70000` used to accumulate into a `U16` and come out as `4464` -- a wrong
/// port that looked like a real one, on a URI that parsed "successfully".
#[test]
def test_parse_port_out_of_range_fails : Bool :=
    uri_parse_fails (Uri.parse "http://127.0.0.1:70000/")

#[test]
def test_parse_port_over_max_fails : Bool :=
    uri_parse_fails (Uri.parse "http://127.0.0.1:65536/")

/// 65535 is representable, so the bound must not reject it.
#[test]
def test_parse_port_boundary_ok : Bool :=
    match Uri.parse "http://127.0.0.1:65535/" {
        Result.err _ => false,
        Result.ok u =>
            match u {
                Uri.uri _ _ _ port _ _ _ => port == Option.some 65535u16
            }
    }

#[test]
def test_parse_port_zero_ok : Bool :=
    match Uri.parse "http://127.0.0.1:0/" {
        Result.err _ => false,
        Result.ok u =>
            match u {
                Uri.uri _ _ _ port _ _ _ => port == Option.some 0u16
            }
    }

/// An empty port (`host:/`) is malformed, not port 0.
#[test]
def test_parse_port_empty_fails : Bool :=
    uri_parse_fails (Uri.parse "http://127.0.0.1:/")

#[test]
def test_parse_port_long_digit_run_fails : Bool :=
    uri_parse_fails (Uri.parse "http://127.0.0.1:99999999999999999999/")

// ── origin ──────────────────────────────────────────────────────────────

/// Parse a URI for these tests. Every input below is well-formed, so an error
/// would be a bug in the test; it becomes an empty URI, which shares no origin
/// with anything.
def uri_of_str (s : String) : Uri :=
    match Uri.parse s {
        Result.err _ => Uri.uri "" Option.none "" Option.none "" Option.none Option.none,
        Result.ok u => u
    }

/// A URI with no port takes its scheme's default.
#[test]
def test_effective_port_scheme_defaults : Bool :=
    Bool.and
        (U16.beq (Uri.effective_port (uri_of_str "http://a/")) 80u16)
        (U16.beq (Uri.effective_port (uri_of_str "https://a/")) 443u16)

/// An explicit port wins over the default, including the default's own number.
#[test]
def test_effective_port_explicit : Bool :=
    U16.beq (Uri.effective_port (uri_of_str "http://a:8080/")) 8080u16

/// `http://a` and `http://a:80` are one origin: the port is compared
/// effectively, not textually.
#[test]
def test_same_origin_default_port_equivalence : Bool :=
    Uri.same_origin (uri_of_str "http://example.com/x") (uri_of_str "http://example.com:80/y")

#[test]
def test_same_origin_port_differs : Bool :=
    Bool.not (Uri.same_origin (uri_of_str "http://example.com/") (uri_of_str "http://example.com:8080/"))

#[test]
def test_same_origin_host_differs : Bool :=
    Bool.not (Uri.same_origin (uri_of_str "http://a.com/") (uri_of_str "http://b.com/"))

#[test]
def test_same_origin_scheme_differs : Bool :=
    Bool.not (Uri.same_origin (uri_of_str "http://a.com/") (uri_of_str "https://a.com/"))

/// DNS names are case-insensitive, so `A.com` and `a.com` are one origin.
#[test]
def test_same_origin_host_case_insensitive : Bool :=
    Uri.same_origin (uri_of_str "http://A.com/") (uri_of_str "http://a.com/")

/// The userinfo is not part of the origin (RFC 6454 §4), which is exactly why
/// a credential in a URI is no protection against a same-origin redirect.
#[test]
def test_same_origin_ignores_userinfo : Bool :=
    Uri.same_origin (uri_of_str "http://u:p@a.com/") (uri_of_str "http://a.com/")

/// `https` defaults to 443, so an explicit `:443` is the same origin.
#[test]
def test_same_origin_https_default : Bool :=
    Uri.same_origin (uri_of_str "https://a.com/") (uri_of_str "https://a.com:443/")

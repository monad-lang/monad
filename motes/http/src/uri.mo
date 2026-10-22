/// URI parsing, formatting, and percent-encoding — Layer 0, pure Monad.
///
/// Builds on `types.mo` (`Uri`) and `strings.mo` (`Strings` byte helpers).
/// Percent-encoding follows RFC 3986. URI parsing is a pragmatic recursive
/// descent over byte lists covering the common `scheme://[user@]host[:port]/path?query#frag`
/// shape. References with no scheme are accepted too, whether they are paths
/// or scheme-relative (`//host/path`), with the scheme left empty.

use http::strings {
  Strings.decode_hex_pair, Strings.drop_bytes, Strings.hex_char_of_nibble,
  Strings.is_unreserved, Strings.is_valid_scheme, Strings.list_starts_with,
  Strings.option_from, Strings.parse_u16_bounded, Strings.split_at_byte,
  Strings.split_at_byte_opt, Strings.split_on,
}
use lib::types {Uri}

// ── percent-encoding (RFC 3986) ─────────────────────────────────────────

pub def Uri.percent_encode (s : String) : String :=
  String.from_list (Uri.pct_encode_bytes (String.to_list s))

def Uri.pct_encode_bytes (bytes : List U8) : List U8 :=
  match bytes {
    List.empty => List.empty,
    List.cons b rest =>
      if Strings.is_unreserved b
      then List.cons b (Uri.pct_encode_bytes rest)
      else List.append (Uri.pct_encode_byte b) (Uri.pct_encode_bytes rest)
  }

def Uri.pct_encode_byte (b : U8) : List U8 :=
  let hi := U8.div b 16u8 in
  let lo := U8.sub b (U8.mul hi 16u8) in
  List.cons 37u8 (List.cons (Strings.hex_char_of_nibble hi) (List.singleton (Strings.hex_char_of_nibble lo)))

pub def Uri.percent_decode (s : String) : Result String String :=
  Uri.pct_decode_go (String.to_list s) List.empty

#[terminating]
def Uri.pct_decode_go (bytes : List U8) (acc : List U8) : Result String String :=
  match bytes {
    List.empty => Result.ok (String.from_list (List.reverse acc)),
    List.cons b rest =>
      if U8.beq b 37u8
      then
        match Uri.pct_decode_pct rest {
          Result.err e => Result.err e,
          Result.ok pr =>
            match pr {
              Pair.pair byte rest2 => Uri.pct_decode_go rest2 (List.cons byte acc)
            }
        }
      else Uri.pct_decode_go rest (List.cons b acc)
  }

def Uri.pct_decode_pct (rest : List U8) : Result String (Pair U8 (List U8)) :=
  match rest {
    List.empty => Result.err "truncated percent-encoding",
    List.cons h1 rest1 =>
      match rest1 {
        List.empty => Result.err "truncated percent-encoding",
        List.cons h2 rest2 =>
          match Strings.decode_hex_pair h1 h2 {
            Result.err e => Result.err e,
            Result.ok byte => Result.ok (Pair.pair byte rest2)
          }
      }
  }

/// Decode `s`, returning `fallback` (the raw string) on malformed input.
pub def Uri.percent_decode_or (fallback : String) (s : String) : String :=
  match Uri.percent_decode s {
    Result.ok r => r,
    Result.err _ => fallback
  }

// ── query parsing / formatting ──────────────────────────────────────────

pub def Uri.parse_query (q : String) : List (Pair String String) :=
  Uri.parse_query_entries (Strings.split_on "&" q)

def Uri.parse_query_entries (entries : List String) : List (Pair String String) :=
  match entries {
    List.empty => List.empty,
    List.cons e rest => List.cons (Uri.parse_one_query e) (Uri.parse_query_entries rest)
  }

def Uri.parse_one_query (e : String) : Pair String String :=
  match Strings.split_at_byte 61u8 (String.to_list e) {
    Pair.pair k_bytes v_bytes =>
      let k := Uri.percent_decode_or (String.from_list k_bytes) (String.from_list k_bytes) in
      let v := Uri.percent_decode_or (String.from_list v_bytes) (String.from_list v_bytes) in
      Pair.pair k v
  }

pub def Uri.format_query (pairs : List (Pair String String)) : String :=
  match pairs {
    List.empty => "",
    List.cons head rest =>
      match head {
        Pair.pair k v =>
          let entry := String.concat (Uri.percent_encode k) (String.concat "=" (Uri.percent_encode v)) in
          match rest {
            List.empty => entry,
            List.cons _ _ => String.concat entry (String.concat "&" (Uri.format_query rest))
          }
      }
  }

// ── formatting ──────────────────────────────────────────────────────────

pub def Uri.format (u : Uri) : String :=
  match u {
    Uri.uri scheme userinfo host port path query fragment =>
      let s1 := Uri.format_scheme_authority scheme userinfo host port in
      let s2 := Uri.join_path s1 path (Uri.has_authority scheme host) in
      let s3 := Uri.append_opt "?" query s2 in
      Uri.append_opt "#" fragment s3
  }

/// Whether a URI renders an authority. Both halves are needed: `mailto:` has
/// a scheme and no host, and a scheme-relative reference has a host and no
/// scheme -- neither renders `scheme://host`, so neither needs the separator
/// that joins an authority to a path.
def Uri.has_authority (scheme : String) (host : String) : Bool :=
  Bool.and (Bool.not (String.is_empty scheme)) (Bool.not (String.is_empty host))

/// Join a rendered scheme+authority to a path.
///
/// Without an authority the two are simply concatenated, so a relative
/// reference and a `mailto:` URI are unchanged. With one, the path has to
/// start with `/`. An empty path stays empty, so `format (parse s) == s` for
/// an authority with no path, and a rootless path gains the separator it was
/// missing: rendering `http://h` + `next` used to give `http://hnext`, which
/// is exactly the shape a relative `Location` resolves into.
def Uri.join_path (authority : String) (path : String) (has_authority : Bool) : String :=
  if Bool.not has_authority
  then String.concat authority path
  else if String.is_empty path
  then authority
  else if String.starts_with "/" path
  then String.concat authority path
  else String.concat authority (String.concat "/" path)

def Uri.append_opt (prefix : String) (opt : Option String) (base : String) : String :=
  match opt {
    Option.none => base,
    Option.some s => String.concat base (String.concat prefix s)
  }

/// Render the part of a URI before its path. A present host with no scheme is
/// a scheme-relative reference (`//host/x`) and renders as one, which is what
/// makes `Location: //cdn.example.com/x` survive a round-trip; the empty
/// scheme used to win first and drop the authority entirely.
def Uri.format_scheme_authority (scheme : String) (userinfo : Option String) (host : String) (port : Option U16) : String :=
  let authority := Uri.format_authority userinfo host port in
  if String.is_empty host
  then if String.is_empty scheme then "" else String.concat scheme ":"
  else if String.is_empty scheme
  then String.concat "//" authority
  else String.concat scheme (String.concat "://" authority)

def Uri.format_authority (userinfo : Option String) (host : String) (port : Option U16) : String :=
  let u := match userinfo {
    Option.none => "",
    Option.some ui => String.concat ui "@"
  } in
  let p := match port {
    Option.none => "",
    Option.some n => String.concat ":" (U16.to_string n)
  } in
  String.concat u (String.concat host p)

// ── parsing ─────────────────────────────────────────────────────────────

pub def Uri.parse (s : String) : Result String Uri :=
  Uri.parse_bytes (String.to_list s)

def Uri.parse_bytes (bytes : List U8) : Result String Uri :=
  match Strings.split_at_byte 35u8 bytes {
    Pair.pair main frag_bytes =>
      let fragment := Strings.option_from frag_bytes in
      match Strings.split_at_byte 63u8 main {
        Pair.pair scheme_hier query_bytes =>
          let query := Strings.option_from query_bytes in
          Uri.parse_scheme scheme_hier query fragment
      }
  }

def Uri.parse_scheme (scheme_hier : List U8) (query : Option String) (fragment : Option String) : Result String Uri :=
  match Strings.split_at_byte_opt 58u8 scheme_hier {
    Option.none => Uri.parse_relative scheme_hier query fragment,
    Option.some sp =>
      match sp {
        Pair.pair scheme_bytes hier_bytes =>
          if Strings.is_valid_scheme scheme_bytes
          then Uri.parse_authority_and_path hier_bytes scheme_bytes query fragment
          else Uri.parse_relative scheme_hier query fragment
      }
  }

/// A reference with no scheme. `//…` is not a path: RFC 3986 §4.2 makes a
/// reference beginning with two slashes scheme-relative, so its authority is
/// parsed and it inherits only the base's scheme. Treating the whole thing as
/// a path dropped the host from `Location: //other/x`. `//` on its own has an
/// empty authority and stays a path, so it still round-trips.
def Uri.parse_relative (path_bytes : List U8) (query : Option String) (fragment : Option String) : Result String Uri :=
  if Strings.list_starts_with (String.to_list "//") path_bytes
  then
    if List.is_empty (Strings.drop_bytes 2 path_bytes)
    then Result.ok (Uri.uri "" Option.none "" Option.none "//" query fragment)
    else Uri.parse_authority_and_path path_bytes List.empty query fragment
  else Result.ok (Uri.uri "" Option.none "" Option.none (String.from_list path_bytes) query fragment)

def Uri.parse_authority_and_path (hier : List U8) (scheme_bytes : List U8) (query : Option String) (fragment : Option String) : Result String Uri :=
  if Strings.list_starts_with (String.to_list "//") hier
  then
    let after_slashes := Strings.drop_bytes 2 hier in
    match Strings.split_at_byte_opt 47u8 after_slashes {
      Option.none =>
        Uri.parse_authority after_slashes (String.from_list scheme_bytes) List.empty query fragment,
      Option.some sp =>
        match sp {
          Pair.pair auth_bytes path_bytes =>
            Uri.parse_authority auth_bytes (String.from_list scheme_bytes) (List.cons 47u8 path_bytes) query fragment
        }
    }
  else
    Result.ok (Uri.uri (String.from_list scheme_bytes) Option.none "" Option.none (String.from_list hier) query fragment)

def Uri.parse_authority (auth : List U8) (scheme : String) (path_bytes : List U8) (query : Option String) (fragment : Option String) : Result String Uri :=
  match Strings.split_at_byte_opt 64u8 auth {
    Option.none => Uri.parse_host_port auth Option.none scheme path_bytes query fragment,
    Option.some sp =>
      match sp {
        Pair.pair userinfo_bytes hostport_bytes =>
          let userinfo := Strings.option_from userinfo_bytes in
          Uri.parse_host_port hostport_bytes userinfo scheme path_bytes query fragment
      }
  }

def Uri.parse_host_port (hostport : List U8) (userinfo : Option String) (scheme : String) (path_bytes : List U8) (query : Option String) (fragment : Option String) : Result String Uri :=
  match Strings.split_at_byte_opt 58u8 hostport {
    Option.none =>
      let host := String.from_list hostport in
      Result.ok (Uri.uri scheme userinfo host Option.none (String.from_list path_bytes) query fragment),
    Option.some sp =>
      match sp {
        Pair.pair host_bytes port_bytes =>
          let host := String.from_list host_bytes in
          match Uri.parse_port port_bytes {
            Result.err e => Result.err e,
            Result.ok port =>
              Result.ok (Uri.uri scheme userinfo host (Option.some port) (String.from_list path_bytes) query fragment)
          }
      }
  }

/// Parse the digits after the colon in an authority. Delegates to the shared
/// bounded parser: an unbounded `U16` accumulation truncated `70000` to `4464`
/// instead of rejecting it, and an empty port (`http://h:/`) silently became
/// port 0.
def Uri.parse_port (bytes : List U8) : Result String U16 :=
  Strings.parse_u16_bounded "port" bytes

// ── resolution (RFC 3986 §5.3) ─────────────────────────────────────────
// If `ref` carries a scheme it is absolute and returned as-is. Otherwise the
// reference inherits `base`'s scheme and authority, and its path is *merged*
// against the base's: a relative path replaces the base's last segment
// (`/a/b` + `c` = `/a/c`), an absolute one replaces the base's path whole,
// and an empty one keeps it -- that last case is what stops `Location: ?q=1`
// from wiping the path it was meant to be relative to.
//
// Dot-segments are deliberately still not removed (`/a/./b` and `/a/x/../b`
// survive verbatim). Removing them is a self-contained addition in
// `Uri.resolve_path`; until then callers that need them must normalise.

pub def Uri.resolve (base : Uri) (ref : Uri) : Uri :=
  match ref {
    Uri.uri rscheme ruserinfo rhost rport rpath rquery rfragment =>
      if Bool.not (String.is_empty rscheme)
      then ref
      else
        match base {
          Uri.uri bscheme buserinfo bhost bport bpath bquery _ =>
            if Bool.not (String.is_empty rhost)
            then
              // The reference carries its own authority; the base contributes
              // only its scheme.
              Uri.uri bscheme ruserinfo rhost rport rpath rquery rfragment
            else
              Uri.uri bscheme buserinfo bhost bport
                (Uri.resolve_path bpath rpath)
                (Uri.resolve_query bquery rquery rpath)
                rfragment
        }
  }

/// Merge a reference path against a base path (RFC 3986 §5.3). A rootless
/// reference replaces the base's last segment; an empty one keeps the base
/// path. With no `/` in the base at all, `Uri.parent_path` yields `/`, so a
/// base that is only an authority merges to a rooted path.
def Uri.resolve_path (base_path : String) (ref_path : String) : String :=
  if String.is_empty ref_path
  then base_path
  else if String.starts_with "/" ref_path
  then ref_path
  else String.concat (Uri.parent_path base_path) ref_path

/// The base path's prefix through its last `/`, or `/` when it has none.
def Uri.parent_path (p : String) : String :=
  let n := Uri.parent_len_go (String.to_list p) 0 0 in
  if I64.beq n 0 then "/" else String.slice p 0 n

/// Length of `p`'s prefix through its last `/`; 0 when `p` has no `/`. The
/// count is kept as a length rather than an index so no negative sentinel is
/// ever needed.
#[terminating]
def Uri.parent_len_go (bytes : List U8) (idx : I64) (best : I64) : I64 :=
  match bytes {
    List.empty => best,
    List.cons x rest =>
      if U8.beq x 47u8
      then Uri.parent_len_go rest (I64.add idx 1) (I64.add idx 1)
      else Uri.parent_len_go rest (I64.add idx 1) best
  }

/// The query a merged reference carries: its own when it has a path, else its
/// own if it defined one at all (`?q=1`, which means "the same path, a new
/// query"), else the base's.
def Uri.resolve_query (base_query : Option String) (ref_query : Option String) (ref_path : String) : Option String :=
  if Bool.not (String.is_empty ref_path)
  then ref_query
  else
    match ref_query {
      Option.some _ => ref_query,
      Option.none => base_query
    }

// ── origin ──────────────────────────────────────────────────────────────

/// The port a URI's origin is defined by: its own when it has one, otherwise
/// the scheme's default (RFC 6454 §4). An unknown scheme answers `0`, which no
/// real port has, so two unknown-scheme URIs only share an origin when they
/// name the same host and neither declares a port.
def Uri.effective_port (u : Uri) : U16 :=
  match u.port {
    Option.some p => p,
    Option.none =>
      if String.beq u.scheme "https"
      then 443u16
      else if String.beq u.scheme "http"
      then 80u16
      else 0u16
  }

/// Whether two URIs share an origin: scheme, host and effective port
/// (RFC 6454 §4). Ports are compared effectively, so `http://a` and
/// `http://a:80` are one origin; hosts are compared case-insensitively,
/// because DNS names are.
///
/// The userinfo is deliberately not part of it: `http://u@a` and `http://a`
/// are the same origin, which is exactly why credentials in a redirect must
/// not be handed over on an origin check that *looks* different.
pub def Uri.same_origin (a : Uri) (b : Uri) : Bool :=
  Bool.and
    (String.beq (String.to_lowercase a.scheme) (String.to_lowercase b.scheme))
    (Bool.and
      (String.beq (String.to_lowercase a.host) (String.to_lowercase b.host))
      (U16.beq (Uri.effective_port a) (Uri.effective_port b)))

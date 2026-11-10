/// Two-phase fetch. `begin` starts the request; `poll` answers
/// 0 = pending, 1 = done, 2 = failed; then `status`/`headers`/`read` inspect
/// it.
///
/// Two phases, deliberately: a JS promise callback must not re-enter wasm
/// while a Monad frame is on the stack. The Monad side drives `poll` from
/// its own frame loop.
///
/// Request headers travel as one length-prefixed blob:
/// `"<klen>:<key><vlen>:<value>"` repeated. Lengths (not separators) delimit
/// the pieces, so a value may contain `:`, a newline, or non-ASCII text;
/// HTTP header values cannot contain NUL, so nothing is escaped. Response
/// headers use the same encoding.

use lib::types {RequestId}
use lib::ffi {
    fetch_begin_raw, fetch_begin_headers_raw, fetch_poll_raw, fetch_status_raw,
    fetch_read_raw, fetch_headers_raw,
}

pub def Fetch.begin (url : String) (method : I64) (body : String) : IO RequestId :=
    IO.mk (fetch_begin_raw url method body)

/// `Fetch.begin` with request headers (and therefore the shape every
/// authenticated API needs: bearer tokens, `Content-Type`, `DPoP`).
pub def Fetch.begin_with (url : String) (method : I64) (body : String)
    (headers : List (Pair String String)) : IO RequestId :=
    IO.mk (fetch_begin_headers_raw url method body (encode_headers headers))

pub def Fetch.poll (r : RequestId) : IO I64 := IO.mk (fetch_poll_raw r)

pub def Fetch.status (r : RequestId) : IO I64 := IO.mk (fetch_status_raw r)

/// The response's headers, readable once `poll` answers 1.
pub def Fetch.response_headers (r : RequestId) : IO (List (Pair String String)) := do {
    let raw <- IO.mk (fetch_headers_raw r);
    return (decode_headers raw)
}

pub def Fetch.read (r : RequestId) (max : I64) : IO String := IO.mk (fetch_read_raw r max)

// ─── Header blob codec (pure) ─────────────────────────────────────────

def encode_header (p : Pair String String) : String :=
    match p {
        Pair.pair key value =>
            let klen : String := I64.to_string (String.length key) in
            let vlen : String := I64.to_string (String.length value) in
            String.concat klen (String.concat ":" (String.concat key
                (String.concat vlen (String.concat ":" value)))),
    }

#[terminating]
pub def encode_headers (hs : List (Pair String String)) : String :=
    match hs {
        List.empty => "",
        List.cons h rest => String.concat (encode_header h) (encode_headers rest),
    }

/// Parse a decimal run starting at `i`; returns the value and the index of
/// the first non-digit (the `:` the caller expects).
#[terminating]
def parse_uint_from (s : String) (i : I64) (acc : I64) : Pair I64 I64 :=
    match String.get s i {
        Option.some b =>
            let d : I64 := U8.to_i64 b - 48 in
            if d < 0 || I64.gt d 9
            then Pair.pair acc i
            else parse_uint_from s (I64.add i 1) (I64.add (I64.mul acc 10) d),
        Option.none => Pair.pair acc i,
    }

#[terminating]
def decode_headers_from (s : String) (i : I64) : List (Pair String String) :=
    if I64.gt i (String.length s)
    then List.empty
    else
        match parse_uint_from s i 0 {
            Pair.pair klen kcolon =>
                if I64.beq klen 0 && I64.beq kcolon i
                then List.empty
                else
                    let key_start : I64 := I64.add kcolon 1 in
                    let key : String := String.slice s key_start klen in
                    let vstart : I64 := I64.add key_start klen in
                    match parse_uint_from s vstart 0 {
                        Pair.pair vlen vcolon =>
                            let value : String := String.slice s (I64.add vcolon 1) vlen in
                            List.cons (Pair.pair key value)
                                (decode_headers_from s (I64.add (I64.add vcolon 1) vlen)),
                    },
        }

pub def decode_headers (s : String) : List (Pair String String) :=
    decode_headers_from s 0

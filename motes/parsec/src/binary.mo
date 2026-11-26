/// Binary parsers: the `Parser Bytes` values a binary format is written with.
///
/// Every combinator here reads from a `Bytes` cursor (`input.mo`), so a token
/// is a zero-copy span over the buffer and a byte read is one
/// `Buf.get_u8`. There is no function-shaped sibling: binary parsing is new
/// code, so the `Parser` form is the only one -- no adapter, no duplication.
///
/// Readers take the file's `Endian` as a VALUE (parsed from its header)
/// rather than as a type parameter: a format's endianness is data, and a
/// grammar that threads `Endian` reads the same in either.
use lib::core {ParseError, ParseResult, Text}
use lib::input {Input, Bytes}
use lib::parser {Parser}
open ParseResult {fail, success}

/// An error at the cursor's offset. `ParseError` carries a TEXT cursor
/// (diagnostics are text-shaped), so a binary failure records the byte offset
/// with no bytes behind it -- the same representation a generic combinator
/// uses (`parse_error_at`), and exact about where it happened.
pub def bytes_error (msg : String) (s : Bytes) : ParseError :=
    ParseError.custom msg (Text.at_offset (Input.input_offset s))

/// Byte order, as read from a format's header. A nullary sum, so `Copy` is
/// honest -- a grammar carries it into every reader.
pub type Endian {
    little,
    big,
}

pub instance Copy Endian {
    def copy (e : Endian) : Pair Endian Endian := Pair.pair e e
}

/// One byte.
pub def byte : Parser Bytes U8 :=
    Parser.mk byte_go

def byte_go (s : Bytes) : ParseResult Bytes U8 :=
    match Input.input_head s {
        Option.none => fail (bytes_error "expected a byte" s),
        Option.some b => success (Input.input_advance 1 s) b
    }

/// The byte at the cursor without consuming it (`none` at end of input).
pub def peek : Parser Bytes (Option U8) :=
    Parser.mk (fn (s : Bytes) => success s (Input.input_head s))

/// `none` when the next bytes are exactly `bs`, `some ()` otherwise -- the
/// negative of `bytes_tag`, for magic-byte dispatch that must NOT consume.
pub def not_bytes (bs : List U8) : Parser Bytes Bool :=
    Parser.mk (not_bytes_go bs)

def not_bytes_go (bs : List U8) (s : Bytes) : ParseResult Bytes Bool :=
    if bytes_at s bs then success s false else success s true

/// Advance `n` bytes, failing when fewer remain.
pub def skip (n : I64) : Parser Bytes Unit :=
    Parser.mk (skip_go n)

def skip_go (n : I64) (s : Bytes) : ParseResult Bytes Unit :=
    if I64.gt n (Input.input_len s)
    then fail (bytes_error "expected more bytes" s)
    else success (Input.input_advance n s) Unit.unit

/// The next `n` bytes as a zero-copy SPAN of the same buffer, consuming them.
/// `Input.input_slice` bounds the span; the cursor advances past it.
pub def take_bytes (n : I64) : Parser Bytes Bytes :=
    Parser.mk (take_bytes_go n)

def take_bytes_go (n : I64) (s : Bytes) : ParseResult Bytes Bytes :=
    if I64.gt n (Input.input_len s)
    then fail (bytes_error "expected more bytes" s)
    else success (Input.input_advance n s) (Input.input_slice n s)

/// A literal byte sequence (magic bytes, a fixed marker). Compares through
/// `Input.input_starts_with`, so no allocation.
pub def bytes_tag (bs : List U8) : Parser Bytes Unit :=
    Parser.mk (bytes_tag_go bs)

def bytes_tag_go (bs : List U8) (s : Bytes) : ParseResult Bytes Unit :=
    match bytes_match_go s bs 0 {
        Option.some n => success (Input.input_advance n s) Unit.unit,
        Option.none => fail (bytes_error "unexpected bytes" s)
    }

/// Are the next bytes exactly `bs`? (The predicate `bytes_tag` is built on.)
pub def bytes_at (s : Bytes) (bs : List U8) : Bool :=
    match bytes_match_go s bs 0 {
        Option.some _ => true,
        Option.none => false
    }

/// Match `bs` byte by byte, answering how many bytes matched (so `bytes_tag`
/// does not have to walk the list again for its length -- a `List U8` is
/// affine and cannot be measured after it is consumed).
#[partial]
def bytes_match_go (s : Bytes) (bs : List U8) (n : I64) : Option I64 :=
    match bs {
        List.empty => Option.some n,
        List.cons b rest =>
            match Input.input_head s {
                Option.none => Option.none,
                Option.some h =>
                    if U8.beq h b
                    then bytes_match_go (Input.input_advance 1 s) rest (n + 1)
                    else Option.none
            }
    }

/// The run of leading bytes matching `pred`, as a span (zero copy).
pub def bytes_while (pred : U8 -> Bool) : Parser Bytes Bytes :=
    Parser.mk (bytes_while_go pred)

def bytes_while_go (pred : U8 -> Bool) (s : Bytes) : ParseResult Bytes Bytes :=
    let n : I64 := Input.input_scan pred s in
    success (Input.input_advance n s) (Input.input_slice n s)

/// The rest of the buffer, as a span.
pub def rest : Parser Bytes Bytes :=
    Parser.mk rest_go

def rest_go (s : Bytes) : ParseResult Bytes Bytes :=
    let n : I64 := Input.input_len s in
    success (Input.input_advance n s) (Input.input_slice n s)

/// `unit` only at end of input.
pub def eof : Parser Bytes Unit :=
    Parser.mk eof_go

def eof_go (s : Bytes) : ParseResult Bytes Unit :=
    if Input.at_end s then success s Unit.unit else fail (bytes_error "expected end of input" s)

/// Fail at the cursor with a message, unless `ok` -- the `do`-notation way to
/// state a format invariant (e.g. `require (class_known cls) "unsupported ELF
/// class"`).
pub def require (ok : Bool) (msg : String) : Parser Bytes Unit :=
    Parser.mk (require_go ok msg)

def require_go (ok : Bool) (msg : String) (s : Bytes) : ParseResult Bytes Unit :=
    if ok then success s Unit.unit else fail (bytes_error msg s)

// ─── Fixed-width integers ────────────────────────────────────────────
//
// One `read_u` over the cursor's indexed access; each wrapper names the
// width and the byte order a format's field has. `I64` is the widest
// integer the language has, so a `u64` reader answers `I64` (a value above
// 2^63 reads as its two's-complement negative; a format that needs the
// unsigned value converts with `I64.to_u64`).

/// Read `n` (1..8) bytes at the cursor as an unsigned integer, in `endian`.
pub def read_u (n : I64) (endian : Endian) : Parser Bytes I64 :=
    Parser.mk (read_u_go n endian)

def read_u_go (n : I64) (endian : Endian) (s : Bytes) : ParseResult Bytes I64 :=
    if I64.gt n (Input.input_len s)
    then fail (bytes_error "expected more bytes" s)
    else
        match endian {
            Endian.little => success (Input.input_advance n s) (read_acc s 0 n 0),
            Endian.big => success (Input.input_advance n s) (read_acc_be s 0 n 0)
        }

/// Accumulate `n` bytes starting at index 0, little-endian when `little`.
#[partial]
def read_acc (s : Bytes) (i : I64) (n : I64) (acc : I64) : I64 :=
    if not (I64.lt i n)
    then acc
    else
        let b : I64 := byte_value (Input.input_byte_at i s) in
        read_acc s (i + 1) n (acc + (b * pow2 (8 * i)))

/// The same accumulation from the END (big endian).
#[partial]
def read_acc_be (s : Bytes) (i : I64) (n : I64) (acc : I64) : I64 :=
    if not (I64.lt i n)
    then acc
    else
        let b : I64 := byte_value (Input.input_byte_at i s) in
        read_acc_be s (i + 1) n (acc * 256 + b)

def byte_value (b : Option U8) : I64 :=
    match b {
        Option.some v => U8.to_i64 v,
        Option.none => 0
    }

#[partial]
def pow2 (k : I64) : I64 :=
    if not (I64.lt 0 k) then 1 else 2 * pow2 (k - 1)

pub def u8 : Parser Bytes I64 := read_u 1 Endian.big
pub def be16 : Parser Bytes I64 := read_u 2 Endian.big
pub def le16 : Parser Bytes I64 := read_u 2 Endian.little
pub def be32 : Parser Bytes I64 := read_u 4 Endian.big
pub def le32 : Parser Bytes I64 := read_u 4 Endian.little
pub def be64 : Parser Bytes I64 := read_u 8 Endian.big
pub def le64 : Parser Bytes I64 := read_u 8 Endian.little

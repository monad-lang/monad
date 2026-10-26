/// The prelude sources the /try engine runs against.
///
/// The engine ships no prelude of its own: the page fetches the real `.mo`
/// files served beside the wasm modules and hands their text to
/// `try_run(sources, source)`. This module parses that payload and turns
/// each served path into the module identity the loader walks -- so the
/// program is checked against the same files the repository ships, and a
/// module added to `init/src` is usable without touching the engine.
///
/// The payload is a sequence of length-prefixed records:
///
///     "<path_len> <source_len>\n" <path bytes> <source bytes>
///
/// concatenated with no separator between records. The lengths are decimal
/// byte counts and each body is sliced exactly, so a source may contain
/// newlines, spaces or comment markers freely. Lengths rather than a
/// delimiter also keep the payload free of NUL bytes, which matters
/// because a Monad `String` in the web profile is a NUL-terminated C
/// string.

pub struct SourceModule {
    segments : List String,
    mote : String,
    file_path : String,
    source : String
}

def newline_byte : U8 := 10u8

def space_byte : U8 := 32u8

def slash_byte : U8 := 47u8

def zero_digit : U8 := 48u8

def nine_digit : U8 := 57u8

/// Parse every record in `payload`, in order. An empty payload is an empty
/// list -- the pipeline then reports the missing `prelude` module itself.
pub def parse_sources (payload : String) : Result String (List SourceModule) :=
    parse_records payload 0 (String.length payload) List.empty

#[terminating]
def parse_records (payload : String) (pos : I64) (total : I64)
    (acc : List SourceModule) : Result String (List SourceModule) :=
    if Bool.not (I64.lt pos total)
    then Result.ok (List.reverse acc)
    else
        match find_byte payload pos total newline_byte {
            Option.none =>
                Result.err (at_byte "a record header is missing its newline" pos),
            Option.some header_end =>
                match parse_header payload pos header_end {
                    Result.err e => Result.err e,
                    Result.ok lens =>
                        match lens {
                            Pair.pair path_len source_len =>
                                let body : I64 := I64.add header_end 1
                                in
                                let body_end : I64 :=
                                    I64.add body (I64.add path_len source_len)
                                in
                                if I64.gt body_end total
                                then Result.err (at_byte "a record is shorter than its declared lengths" pos)
                                else parse_record_body payload body path_len source_len body_end total acc,
                        },
                },
        }

#[terminating]
def parse_record_body (payload : String) (body : I64) (path_len : I64)
    (source_len : I64) (body_end : I64) (total : I64)
    (acc : List SourceModule) : Result String (List SourceModule) :=
    let path : String := String.slice payload body path_len
    in
    let source : String := String.slice payload (I64.add body path_len) source_len
    in
    match identity_of_path path {
        Result.err e => Result.err e,
        Result.ok ident =>
            match ident {
                Pair.pair segments mote =>
                    let module_ : SourceModule :=
                        { segments := segments, mote := mote, file_path := path,
                          source := source }
                    in
                    parse_records payload body_end total (List.cons module_ acc),
            },
    }

/// The two decimal lengths in one record header (`start` inclusive,
/// `end` exclusive).
def parse_header (payload : String) (start : I64) (end : I64)
    : Result String (Pair I64 I64) :=
    match find_byte payload start end space_byte {
        Option.none =>
            Result.err (at_byte "a record header has no space between its lengths" start),
        Option.some split =>
            match parse_decimal payload start split {
                Result.err e => Result.err e,
                Result.ok path_len =>
                    match parse_decimal payload (I64.add split 1) end {
                        Result.err e => Result.err e,
                        Result.ok source_len =>
                            if I64.lt path_len 1
                            then Result.err (at_byte "a record declares an empty path" start)
                            else Result.ok (Pair.pair path_len source_len),
                    },
            },
    }

#[terminating]
def parse_decimal (payload : String) (start : I64) (end : I64)
    : Result String I64 :=
    if Bool.not (I64.lt start end)
    then Result.err (at_byte "a record header has an empty length" start)
    else digits_go payload start end 0

#[terminating]
def digits_go (payload : String) (pos : I64) (end : I64) (acc : I64)
    : Result String I64 :=
    if I64.beq pos end
    then Result.ok acc
    else
        match String.get payload pos {
            Option.none =>
                Result.err (at_byte "a record length runs past the payload" pos),
            Option.some b =>
                if U8.lt b zero_digit || U8.gt b nine_digit
                then Result.err (at_byte "a record length is not decimal" pos)
                else if I64.gt acc 100000000
                     then Result.err (at_byte "a record length is implausibly large" pos)
                     else digits_go payload (I64.add pos 1) end
                              (I64.add (I64.mul acc 10) (I64.sub (U8.to_i64 b) 48)),
        }

/// The module a served path names: `<mote>/src/<stem>.mo`.
///
/// `init/src/lib.mo` is the mote's own root (`init`), `init/src/prelude.mo`
/// is the ambient `prelude`, and `init/src/number.mo` is `init.number` --
/// the same identities the compiler's loader assigns.
pub def identity_of_path (path : String) : Result String (Pair (List String) String) :=
    if Bool.not (String.ends_with path ".mo")
    then Result.err (bad_path path "is not a .mo file")
    else
        match find_byte path 0 (String.length path) slash_byte {
            Option.none => Result.err (bad_path path "is not under <mote>/src/"),
            Option.some mote_end =>
                parse_identity path mote_end,
        }

def parse_identity (path : String) (mote_end : I64)
    : Result String (Pair (List String) String) :=
    let rest_at : I64 := I64.add mote_end 1
    in
    if Bool.not (slice_is path rest_at "src/")
    then Result.err (bad_path path "is not under <mote>/src/")
    else
        let stem_at : I64 := I64.add rest_at 4
        in
        let stem_len : I64 := I64.sub (I64.sub (String.length path) stem_at) 3
        in
        if I64.lt stem_len 1
        then Result.err (bad_path path "names no module")
        else
            let mote : String := String.slice path 0 mote_end
            in
            let stem : String := String.slice path stem_at stem_len
            in
            let segments : List String := segments_of mote stem
            in
            if Bool.not (no_empty_segment segments)
            then Result.err (bad_path path "has an empty path segment")
            else Result.ok (Pair.pair segments mote)

def segments_of (mote : String) (stem : String) : List String :=
    if String.beq mote "init" && String.beq stem "prelude"
    then ["prelude"]
    else if String.beq stem "lib"
         then [mote]
         else List.cons mote (split_slashes stem)

#[terminating]
def split_slashes (s : String) : List String :=
    match find_byte s 0 (String.length s) slash_byte {
        Option.none => [s],
        Option.some i =>
            List.cons (String.slice s 0 i)
                (split_slashes
                    (String.slice s (I64.add i 1)
                        (I64.sub (I64.sub (String.length s) i) 1))),
    }

#[terminating]
def no_empty_segment (segments : List String) : Bool :=
    match segments {
        List.empty => true,
        List.cons s rest => Bool.not (String.is_empty s) && no_empty_segment rest,
    }

#[terminating]
def find_byte (s : String) (pos : I64) (limit : I64) (want : U8) : Option I64 :=
    if Bool.not (I64.lt pos limit)
    then Option.none
    else
        match String.get s pos {
            Option.none => Option.none,
            Option.some b =>
                if U8.beq b want
                then Option.some pos
                else find_byte s (I64.add pos 1) limit want,
        }

def slice_is (s : String) (at : I64) (want : String) : Bool :=
    if I64.lt (I64.sub (String.length s) at) (String.length want)
    then false
    else String.beq (String.slice s at (String.length want)) want

def at_byte (message : String) (pos : I64) : String :=
    String.concat message (String.concat " (at byte " (String.concat (I64.to_string pos) ")"))

def bad_path (path : String) (why : String) : String :=
    String.concat "the page sent a source path that "
        (String.concat why (String.concat ": " path))

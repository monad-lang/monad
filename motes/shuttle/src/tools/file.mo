/// `read`/`write`/`edit` -- agent-skills.md Phase 2's file tools.
/// `edit`'s stale-read check: the caller must supply the content it
/// last read, compared against the file's CURRENT content before
/// writing, so a write based on a stale read is rejected rather than
/// silently clobbering a concurrent change.
use init::transformers {ResultT}
use shuttle::message_types {Content}
use shuttle::tools::file_args {ReadArgs, WriteArgs, EditArgs}
use json::json {Json}
use std::io {IO.read_file, IO.write_file, IO.is_dir}
use std::process {exec_cmd}
use std::stream {FdStream, Stream, StreamError}
use std::bytebuf {ByteBuf, ByteBuf.length, ByteBuf.to_string, ByteBuf.free}
use std::path {Path, Path.of, Path.parent, Path.to_string}
use http::strings {Strings.split_on}

def tool_err (id : String) (msg : String) : Content := Content.tool_result id msg true
def tool_ok (id : String) (msg : String) : Content := Content.tool_result id msg false

def number_line (n : I64) (line : String) : String :=
    String.concat (I64.to_string n) (String.concat ": " line)

#[partial]
def number_lines_from (n : I64) (lines : List String) : List String :=
    match lines {
        List.empty => List.empty,
        List.cons l rest => List.cons (number_line n l) (number_lines_from (n + 1) rest),
    }

/// Numbered lines, one allocation: the old `List.intercalate` is right-nested
/// under `String.concat` (neither tail nor linear), so numbering a 256 KB file
/// with short lines copied gigabytes per read.
def numbered_text (text : String) : String :=
    let joined : String := String.concat_list (number_lines_go 1 (Strings.split_on "\n" text) List.empty) in
    let n : I64 := String.length joined in
    // `number_lines_go` terminates every line, so drop the final newline the
    // old `intercalate` never added.
    if n < 1 then joined else String.slice joined 0 (n - 1)

#[terminating]
def number_lines_go (n : I64) (lines : List String) (acc : List String) : List String :=
    match lines {
        List.empty => List.reverse acc,
        List.cons l rest => number_lines_go (n + 1) rest (List.cons ((number_line n l) ++ "\n") acc),
    }

/// One chunk of the streaming read.
def read_chunk_bytes : I64 := 65536

/// Drop a trailing UTF-8 character that the byte cap cut in half. The joined
/// text ends on a byte boundary, not a character one; `String.get` gives the
/// raw bytes, and a lead byte with fewer continuation bytes left than its
/// sequence needs is a cut.
#[partial]
def byte_at (s : String) (i : I64) : U8 :=
    match String.get s i { Option.some b => b, Option.none => 0u8 }

def utf8_cont (b : U8) : Bool := U32.beq (U32.and (U8.to_u32 b) 0xC0u32) 0x80u32

def utf8_need (b : U8) : I64 :=
    if U8.lt b 0x80u8 then 1
    else if U32.beq (U32.and (U8.to_u32 b) 0xE0u32) 0xC0u32 then 2
    else if U32.beq (U32.and (U8.to_u32 b) 0xF0u32) 0xE0u32 then 3
    else 4

#[partial]
def last_lead_go (s : String) (i : I64) (steps : I64) : I64 :=
    if steps < 1 then i
    else if utf8_cont (byte_at s i) then last_lead_go s (i - 1) (steps - 1)
    else i

#[partial]
def trim_partial_utf8 (s : String) : String :=
    let n : I64 := String.length s in
    if n < 1 then s
    else
        let i : I64 := last_lead_go s (n - 1) 3 in
        if n - i < utf8_need (byte_at s i) then String.slice s 0 i else s

/// The first `max` bytes of the file and whether more remained -- read in
/// chunks and stopped at the budget. Reading the whole file and capping
/// afterwards (`IO.read_file` then `String.slice`) made `read /dev/zero` or a
/// multi-GB log an OOM before the cap ever ran.
pub def read_up_to (path : Path) (max : I64) : IO (Result StreamError (Pair String Bool)) := do {
    let opened <- FdStream.open_file path FdStream.read_mode;
    match opened {
        Result.err e => IO.pure (Result.err e),
        Result.ok s => read_chunks s max List.empty 0,
    }
}

def read_close_err (s : FdStream) (e : StreamError) : IO (Result StreamError (Pair String Bool)) := do {
    let _ <- Stream.close s;
    IO.pure (Result.err e)
}

def read_finish (s : FdStream) (acc : List String) (more : Bool) : IO (Result StreamError (Pair String Bool)) := do {
    let _ <- Stream.close s;
    // `;` here, not `in`: inside a do-block `let ... in` aborts the parse.
    let joined : String := String.concat_list (List.reverse acc);
    let text : String := if more then trim_partial_utf8 joined else joined;
    IO.pure (Result.ok (Pair.pair text more))
}

#[terminating]
def read_chunk_got (s : FdStream) (max : I64) (acc : List String) (total : I64) (buf : ByteBuf) : IO (Result StreamError (Pair String Bool)) := do {
    let n : I64 := ByteBuf.length buf;
    if n < 1
    then do { let _ <- ByteBuf.free buf; read_finish s acc false }
    else do {
        let text <- ByteBuf.to_string buf n;
        let _ <- ByteBuf.free buf;
        read_chunks s max (List.cons text acc) (total + n)
    }
}

/// At the budget: a one-byte probe says whether the file continued.
def read_probe (s : FdStream) (acc : List String) : IO (Result StreamError (Pair String Bool)) := do {
    let r <- Stream.read s 1;
    match r {
        Result.err e => read_close_err s e,
        Result.ok buf => do {
            let n : I64 := ByteBuf.length buf;
            let _ <- ByteBuf.free buf;
            read_finish s acc (n > 0)
        },
    }
}

#[terminating]
def read_chunks (s : FdStream) (max : I64) (acc : List String) (total : I64) : IO (Result StreamError (Pair String Bool)) := do {
    if I64.lt total max
    then do {
        let room : I64 := max - total;
        let want : I64 := if room < read_chunk_bytes then room else read_chunk_bytes;
        let r <- Stream.read s want;
        match r {
            Result.err e => read_close_err s e,
            Result.ok buf => read_chunk_got s max acc total buf,
        }
    }
    else read_probe s acc
}

/// A read's tool result from `read_up_to`: numbered lines, plus the cap's
/// marker when the probe found more.
def read_content_bounded (id : String) (max : I64) (r : Result StreamError (Pair String Bool)) : Content :=
    match r {
        Result.err e => tool_err id e.message,
        Result.ok pr => match pr {
            Pair.pair text more =>
                let body : String := numbered_text text in
                if more
                then tool_ok id (body ++ "\n[truncated at " ++ I64.to_string max ++ " bytes]")
                else tool_ok id body,
        },
    }

/// A write's tool result: `done` on success, the failure as a tool error.
def written_content (id : String) (done : String) (w : Result StreamError Unit) : Content :=
    match w {
        Result.ok _ => tool_ok id done,
        Result.err e => tool_err id e.message
    }

/// The most bytes one read returns. A compiled binary or a giant log
/// otherwise enters the history whole (measured live: a 4 MB read made
/// the next request ~1M tokens and the provider rejected it with 400).
def read_max_bytes : I64 := 262144

pub def read_run (id : String) (j : Json) : ResultT String IO Content :=
    match ReadArgs.deserialize_json j {
        Result.err e => ResultT.mk (return (Result.ok (tool_err id e))),
        Result.ok args =>
            ResultT.mk (do {
                match Path.of args.path {
                    Result.err e => return (Result.ok (tool_err id (PathError.to_string e))),
                    Result.ok p => do {
                        let max : I64 := read_max_bytes;
                        let r <- read_up_to p max;
                        return (Result.ok (read_content_bounded id max r))
                    }
                }
            })
    }

pub def write_run (id : String) (j : Json) : ResultT String IO Content :=
    match WriteArgs.deserialize_json j {
        Result.err e => ResultT.mk (return (Result.ok (tool_err id e))),
        Result.ok args =>
            ResultT.mk (do {
                match Path.of args.path {
                    Result.err e => return (Result.ok (tool_err id (PathError.to_string e))),
                    Result.ok p => do {
                        // A new file in a new directory: create the parents
                        // first (the write alone failed with ENOENT).
                        ensure_parent p;
                        let w <- IO.write_file p args.content;
                        return (Result.ok (written_content id "wrote file" w))
                    }
                }
            })
    }

/// `mkdir -p` the directory `p` sits in, when it has one and it is missing.
def ensure_parent (p : Path) : IO Unit :=
    match Path.parent p {
        Option.none => IO.pure unit,
        Option.some dir => do {
            let there <- IO.is_dir dir;
            if there then IO.pure unit
            else do {
                let _ <- exec_cmd "mkdir" ["-p", Path.to_string dir];
                IO.pure unit
            }
        },
    }

def edit_with_check (id : String) (p : Path) (expected : String) (new_content : String) : IO (Result String Content) := do {
    let current <- IO.read_file p;
    match current {
        Result.err e => return (Result.ok (tool_err id e.message)),
        Result.ok text => edit_if_current id p (String.beq text expected) new_content
    }
}

def edit_if_current (id : String) (p : Path) (current : Bool) (new_content : String) : IO (Result String Content) :=
    if current
    then do {
        let w <- IO.write_file p new_content;
        return (Result.ok (written_content id "edited file" w))
    }
    else return (Result.ok (tool_err id "stale read: file content changed since it was last read"))

pub def edit_run (id : String) (j : Json) : ResultT String IO Content :=
    match EditArgs.deserialize_json j {
        Result.err e => ResultT.mk (return (Result.ok (tool_err id e))),
        Result.ok args =>
            ResultT.mk (match Path.of args.path {
                Result.err e => return (Result.ok (tool_err id (PathError.to_string e))),
                Result.ok p => edit_with_check id p args.expected_content args.new_content,
            })
    }

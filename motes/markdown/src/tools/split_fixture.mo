// Split the vendored CommonMark fixture into parts the compiled backend can
// read.
//
//   monad run motes/markdown/src/tools/split_fixture.mo -- <spec.json>
//
// `IO.read_file` in the compiled backend fails on any file over 64 KiB (the
// second 64 KiB read returns an error; see
// plans/implementations/compiled-read-file-second-chunk.md), so the
// conformance harness reads the fixture as three parts and joins them in
// memory. The split is at line boundaries, so every part is valid UTF-8 and
// the concatenation is byte-identical to the input.
//
// This tool uses no part of `gen` -- it is a byte-level file operation. Its
// line scan is its own rather than `Markdown.split_lines`, which strips a
// BOM and treats a bare CR as a line ending: neither belongs in a split
// that has to be reversible.
//
// Nothing here calls `List.length` on the byte list: it is `1 + length
// tail`, so it recurses once per byte. Sizes are carried along instead.

use std::io {IO.println, IO.read_file_bytes, IO.write_file_bytes}
use std::list {List.length}
use std::path {Path}
use std::stream {StreamError}

/// Parts the fixture is split into.
def parts : I64 := 3

/// Hard ceiling: one byte under the backend's 64 KiB read.
def limit : I64 := 65535

def main (args : List String) : IO I64 :=
    match source_of args {
        Option.some src => do {
            let raw <- IO.read_file_bytes (Path.path src);
            let code <- generate raw src;
            return code
        },
        Option.none => usage,
    }

def source_of (args : List String) : Option String :=
    match args {
        List.cons src _ => Option.some src,
        List.empty => Option.none,
    }

def usage : IO I64 := do {
    let _printed <- IO.println "usage: split_fixture <commonmark spec.json>";
    return 2
}

def generate (raw : Result StreamError (List U8)) (src : String) : IO I64 :=
    match raw {
        Result.err e => fail_with (String.concat "cannot read the fixture: " e.message),
        Result.ok bytes => after_read bytes src,
    }

def after_read (bytes : List U8) (src : String) : IO I64 :=
    let total : I64 := byte_count bytes 0 in
    let finished : Split := split_bytes bytes empty_split (target_size total) in
    write_parts (List.reverse finished.done) src 1

def fail_with (message : String) : IO I64 := do {
    let _printed <- IO.println message;
    return 1
}

/// The size each part aims for: the input split as evenly as possible, and
/// never above the hard limit.
def target_size (total : I64) : I64 :=
    let even : I64 := I64.div (I64.add total (I64.sub parts 1)) parts in
    if I64.lt limit even then limit else even

// --- Splitting ---

/// Parts are collected back to front, each with the size it was built at,
/// so nothing has to measure a finished part afterwards.
struct Split {
    done : List (Pair (List U8) I64),
    current : List U8,
    size : I64,
    at_line_start : Bool,
}

def empty_split : Split :=
    { done := List.empty, current := List.empty, size := 0, at_line_start := true }

#[partial]
def byte_count (bytes : List U8) (acc : I64) : I64 :=
    match bytes {
        List.empty => acc,
        List.cons _ tl => byte_count tl (I64.add acc 1),
    }

#[partial]
def split_bytes (bytes : List U8) (s : Split) (target : I64) : Split :=
    match bytes {
        List.empty => finish_part s,
        List.cons b rest => split_bytes rest (split_step b s target) target,
    }

/// Close the part BEFORE a line's first byte once the current part has
/// reached the target and parts remain: the boundary therefore falls between
/// two lines, and the previous part ends with its newline.
def split_step (b : U8) (s : Split) (target : I64) : Split :=
    split_append (split_maybe_close b s target) b

def split_maybe_close (b : U8) (s : Split) (target : I64) : Split :=
    if close_here b s target then close_part s else s

def close_here (b : U8) (s : Split) (target : I64) : Bool :=
    Bool.and s.at_line_start
        (Bool.and (Bool.not (I64.lt s.size target))
            (Bool.and (Bool.not (I64.beq s.size 0))
                (I64.lt (List.length s.done) (I64.sub parts 1))))

def split_append (s : Split) (b : U8) : Split :=
    { done := s.done,
      current := List.cons b s.current,
      size := I64.add s.size 1,
      at_line_start := U8.beq b 10u8 }

def close_part (s : Split) : Split :=
    finish_part s

/// Move whatever is in `current` into `done` (newest first), unless empty.
def finish_part (s : Split) : Split :=
    if I64.beq s.size 0
    then s
    else
        { done := List.cons (Pair.pair (List.reverse s.current) s.size) s.done,
          current := List.empty, size := 0, at_line_start := true }

// --- Output ---

#[partial]
def write_parts (chunks : List (Pair (List U8) I64)) (src : String) (index : I64) : IO I64 :=
    match chunks {
        List.empty => do {
            let _printed <- IO.println (String.concat (I64.to_string (I64.sub index 1)) " parts written");
            return 0
        },
        List.cons chunk rest =>
            if I64.lt limit chunk.second
            then fail_with (String.concat "part " (String.concat (I64.to_string index)
                " exceeds the 64 KiB read limit"))
            else write_one chunk rest src index,
    }

#[partial]
def write_one (chunk : Pair (List U8) I64) (rest : List (Pair (List U8) I64))
    (src : String) (index : I64) : IO I64 :=
    let path : String := part_path src index in
    do {
        let written <- IO.write_file_bytes (Path.path path) chunk.first;
        let code <- report_part written path chunk.second rest src index;
        return code
    }

#[partial]
def report_part (written : Result StreamError Unit) (path : String) (size : I64)
    (rest : List (Pair (List U8) I64)) (src : String) (index : I64) : IO I64 :=
    match written {
        Result.err e => fail_with (String.concat "cannot write "
            (String.concat path (String.concat ": " e.message))),
        Result.ok _ => after_part path size rest src index,
    }

#[partial]
def after_part (path : String) (size : I64) (rest : List (Pair (List U8) I64))
    (src : String) (index : I64) : IO I64 := do {
    let _printed <- IO.println
        (String.concat "wrote " (String.concat path
            (String.concat " (" (String.concat (I64.to_string size) " bytes)"))));
    let code <- write_parts rest src (I64.add index 1);
    return code
}

/// `commonmark-0.31.2.spec.json` -> `commonmark-0.31.2.part<N>.json`, the
/// name the committed parts carry.
def part_path (src : String) (index : I64) : String :=
    String.concat (stem src)
        (String.concat ".part" (String.concat (I64.to_string index) ".json"))

/// The file name without its `.spec.json` (or `.json`) suffix.
def stem (src : String) : String :=
    if String.ends_with src ".spec.json"
    then String.slice src 0 (I64.sub (String.length src) 10)
    else if String.ends_with src ".json"
         then String.slice src 0 (I64.sub (String.length src) 5)
         else src

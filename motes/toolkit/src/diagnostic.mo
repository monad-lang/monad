/// `lang`'s diagnostics as the editor sees them: one line of text, one range,
/// one severity.
///
/// THE MESSAGE HAS TO BE REDUCED, and that is most of why this module exists.
/// `lang`'s `Diagnostic.message` is the RENDERED TERMINAL OUTPUT, not a summary:
/// `render_type_error` produces `error: <what> in <decl>` followed by a `-->`
/// arrow line and, for a parse error, three lines of source with a caret under
/// the offending column. That is exactly right for `monad check`, which prints
/// it to a terminal, and wrong for an editor -- the arrow names a path the
/// editor already knows, the source excerpt duplicates text the editor is
/// displaying a few pixels away, and the caret duplicates the range being sent
/// alongside. So the reduction drops all of it and keeps the header line.
///
/// The reduction lives here rather than in `lang` for the reason `lang`'s own
/// `Diagnostic` doc gives: `check` reads that message, so its rendering cannot
/// move without changing `check`'s output. A consumer that wants a different
/// shape reduces it, and this is that consumer.
///
/// The `error: ` prefix goes too. LSP carries severity as a FIELD, and every
/// client renders it as a gutter glyph or a coloured header, so a message that
/// also begins "error: " reads as a stutter in exactly the place the user is
/// looking. What remains -- `unknown variable 'no_such_name' in bad` -- is the
/// sentence a human wants, and the trailing ` in bad` is kept deliberately even
/// though the range covers that declaration: at declaration granularity the
/// range can be a dozen lines tall, and naming the declaration is what tells the
/// user which one.
///
/// SEVERITY IS ALWAYS `Error`, and that is a statement about `lang` rather than
/// about this module: `lang`'s `Diagnostic` has no severity field, and no
/// producer emits anything but a hard failure. The four constants are here in
/// their specification order so that the first producer of a warning has the
/// numbers to hand and does not invent them; the severity-aware counting in
/// `cli/src/main.mo`'s check loop is the other half of that, already landed.
///
/// THE POSITION AND RANGE ENCODERS ARE NOT HERE. They moved to `toolkit::wire`
/// when hover and definition arrived needing the same shapes. That is the split
/// this module's earlier note asked for: a diagnostics file being their first home
/// was an accident of who needed a range first, not a claim about where the shapes
/// belong.
///
/// What is left is what is about a DIAGNOSTIC: its severity, its
/// source name, and the reduction of `lang`'s rendered terminal output to one line
/// of text. None of those means anything for a jump target or an outline entry.
///
/// The move also took `lang`'s two position types out of this module's imports
/// entirely. `diagnostic_range` still answers an `Option SourceRange`, but the
/// only thing done with one is hand it to `wire_range_of_source_range`, so no
/// `Location` field is read here at all -- and a module that cannot read a field
/// cannot be the next home of the accessors that read it.

use json::json {Json}
use lang::module {Diagnostic, diagnostic_message, diagnostic_range}
use toolkit::bytes {byte_lf}
use toolkit::jsonrpc {rpc_object}
use toolkit::position {LineIndex, PositionEncoding, WireRange}
use toolkit::wire {
  wire_range_json, wire_range_of_source_range, wire_range_origin,
}

// --- Severity ---
//
// The four values the specification fixes. They are wire constants: a client
// draws its gutter glyph from the number, so a wrong one is invisible until a
// user notices the wrong icon.

pub def diag_severity_error : I64 := 1

pub def diag_severity_warning : I64 := 2

pub def diag_severity_information : I64 := 3

pub def diag_severity_hint : I64 := 4

/// The tool name clients show beside a diagnostic, for a user looking at four
/// servers at once. The Rust server being replaced sends the same string
/// (`rust/rust-cli/src/lsp.rs`'s diagnostic builder), so a user switching over sees
/// no change in the gutter.
pub def diagnostic_source_name : String := "monad"

// --- Message reduction ---

/// The prefix `lang`'s renderers put on every header line.
def error_prefix : String := "error: "

/// The one line an editor should show, with `error: ` removed.
///
/// A message with no newline at all -- a termination check's, which never went
/// through a renderer -- comes back unchanged, minus the prefix if it has one.
///
/// A message that would reduce to the EMPTY STRING falls back to the unstripped
/// header, and a message whose own header is empty falls back to the WHOLE
/// message -- so the contract is "non-empty in, non-empty out". Neither input
/// comes from `lang`'s two renderers, which always put text after the prefix on
/// the header line, but a blank message is a diagnostic the user cannot act on
/// and an empty popup reads as a broken server rather than as a missing detail,
/// so the guard is here rather than left to a future producer to remember.
pub def diagnostic_header (msg : String) : String :=
  let i : I64 := newline_index (String.to_list msg) 0 in
  let head : String := if I64.lt i 0 then msg else String.slice msg 0 i in
  let body : String := strip_error_prefix head in
  if String.is_empty body
  then if String.is_empty head then msg else head
  else body

/// The index of the first `\n`, or -1.
///
/// Slicing at that index is safe without a character-boundary check: `\n` is
/// `0x0A`, and a UTF-8 continuation byte is `0x80`-`0xBF`, so the byte could not
/// have been part of a multi-byte character.
#[partial]
def newline_index (bs : List U8) (i : I64) : I64 :=
  match bs {
    List.empty => 0 - 1,
    List.cons b rest => if U8.beq b byte_lf then i else newline_index rest (I64.add i 1),
  }

/// Drop a leading `error: `, if there is one.
///
/// `String.starts_with` rather than a comparison against the first seven bytes,
/// and the slice starts at the prefix's byte LENGTH -- seven ASCII bytes -- which
/// is a character boundary by construction, so `String.slice` cannot split a
/// character here even for a message whose text begins with an em dash.
def strip_error_prefix (s : String) : String :=
  let n : I64 := String.length error_prefix in
  if String.starts_with error_prefix s
  then String.slice s n (I64.sub (String.length s) n)
  else s

// --- The wire diagnostic ---

pub struct WireDiagnostic {
  range : WireRange,
  severity : I64,
  message : String,
}

pub def wire_diagnostic_mk (range : WireRange) (severity : I64) (message : String) : WireDiagnostic :=
  WireDiagnostic.mk range severity message

pub def wire_diagnostic_range (d : WireDiagnostic) : WireRange := d.range

pub def wire_diagnostic_severity (d : WireDiagnostic) : I64 := d.severity

pub def wire_diagnostic_message (d : WireDiagnostic) : String := d.message

/// A `lang` diagnostic on the wire.
///
/// `enc`, `ix` and `source` are the negotiated encoding, the line index for the
/// source TEXT THE DIAGNOSTIC CAME FROM, and that text -- all three are needed
/// because `lang` reports byte offsets and the wire wants an encoding unit, and
/// the conversion needs the bytes to count them. Passing a line index built from
/// a different revision of the buffer than the offsets came from produces
/// plausible-looking positions that are silently wrong; the caller's contract is
/// that the cache's diagnostic and the source are from the same text.
///
/// BOTH FAILURES ANSWER THE ORIGIN, AND A DIAGNOSTIC IS THE ONE CONSUMER THIS IS
/// RIGHT FOR. A diagnostic the checker could not place is REPORTED, not dropped:
/// an editor whose server silently discards the diagnostics it cannot locate shows
/// a broken file as clean, which is worse than a marker in the wrong place and
/// very much worse than one at the top of the file. `lang`'s truncation path -- a
/// buffer the lenient parser stopped reading -- is the producer that takes the
/// no-range branch, and its message says so.
///
/// The other branch -- a range whose start line is not in `ix` -- is unreachable
/// in practice: the range's two ends are `Location`s off the same source the index
/// was built from. `motes/lsp`'s navigation, which takes the same conversion, does
/// NOT share this choice: a jump to the origin is a lie the user will follow, so
/// an unplaceable range yields no target there.
#[partial]
pub def wire_diagnostic_of_lang (enc : PositionEncoding) (ix : LineIndex) (source : String)
    (dg : Diagnostic) : WireDiagnostic :=
  match diagnostic_range dg {
    Option.none => wire_diagnostic_at_origin dg,
    Option.some sr =>
      match wire_range_of_source_range enc ix source sr {
        Option.none => wire_diagnostic_at_origin dg,
        Option.some r => wire_diagnostic_mk r diag_severity_error
          (diagnostic_header (diagnostic_message dg)),
      },
  }

/// The diagnostic at the origin, with its severity and reduced message -- the one
/// shape both failure arms above answer. A named def rather than the same
/// expression twice, because the two arms differing would mean a diagnostic that
/// reported a different message depending on WHICH way it could not be placed.
#[partial]
def wire_diagnostic_at_origin (dg : Diagnostic) : WireDiagnostic :=
  wire_diagnostic_mk wire_range_origin diag_severity_error
    (diagnostic_header (diagnostic_message dg))

/// One diagnostic, as the `diagnostics` array of `textDocument/publishDiagnostics`
/// wants it, minus the array.
///
/// The four fields are the four the Rust server being replaced sends
/// (`rust/rust-cli/src/lsp.rs`), so this is the same wire shape with a better range.
#[partial]
pub def wire_diagnostic_json (d : WireDiagnostic) : Json :=
  rpc_object [
    Pair.pair "range" (wire_range_json (wire_diagnostic_range d)),
    Pair.pair "severity" (Json.make_num_int (wire_diagnostic_severity d)),
    Pair.pair "message" (Json.make_str (wire_diagnostic_message d)),
    Pair.pair "source" (Json.make_str diagnostic_source_name),
  ]

/// The `diagnostics` array itself.
///
/// Built by folding, and the accumulator's type is pinned by a def rather than
/// written as a bare `List.empty`: an unannotated empty list is the shape that
/// resolved to the wrong instance in this repository's `Map.empty` bug, and the
/// cost of ruling it out is one line.
#[partial]
pub def wire_diagnostics_json (ds : List WireDiagnostic) : Json :=
  Json.make_array (wire_diagnostics_json_go ds diag_no_json_nodes)

def diag_no_json_nodes : List Json := List.empty

#[partial]
def wire_diagnostics_json_go (ds : List WireDiagnostic) (acc : List Json) : List Json :=
  match ds {
    List.empty => diag_json_reverse acc diag_no_json_nodes,
    List.cons d rest => wire_diagnostics_json_go rest (List.cons (wire_diagnostic_json d) acc),
  }

/// Reversed locally rather than through `list_reverse`, which is a `lang` def
/// that is not `pub` -- and reversing four lines is not worth widening this
/// module's import list for, the same judgement `position.mo` and `framing.mo`
/// record for their own reverses.
#[partial]
def diag_json_reverse (ls : List Json) (acc : List Json) : List Json :=
  match ls {
    List.empty => acc,
    List.cons l rest => diag_json_reverse rest (List.cons l acc),
  }

/// The specification's position, range and location shapes, and the one place
/// `lang`'s coordinates become them.
///
/// THIS MODULE EXISTS BECAUSE A SECOND CONSUMER ARRIVED. `diagnostic.mo` carried
/// the two encoders with a note saying so: `position.mo` is deliberately free of
/// `lang` and of `Json`, and diagnostics were the first thing that needed a range
/// on the wire, so the shapes landed beside them -- with an explicit instruction
/// to split them out "when hover and definition arrive with their own need for
/// the same shapes". They have. Hover needs a range, definition needs a
/// `Location`, and `documentSymbol` needs one of each per declaration, so the
/// shapes moved here rather than being copied into `motes/lsp` a third time, and
/// `diagnostic.mo` now imports them like any other consumer.
///
/// WHAT IS LEFT IN `diagnostic.mo` IS WHAT IS ABOUT A DIAGNOSTIC: its severity,
/// its source name, and the reduction of `lang`'s rendered terminal output to one
/// line of text. What is here is the geometry, which is the same for a squiggle, a
/// jump target and an outline entry.
///
/// THE FOUR `lang` ACCESSORS ARE DUPLICATED FROM `diagnostic.mo`, and deliberately
/// not shared with it: they exist because `lang`'s `Location` and `SourceRange`
/// have no accessors of their own, and this repository's `#[test]`-plus-field-read
/// codegen hazard means a field read is wrapped in a one-line typed def rather
/// than written inline. Since the move leaves `diagnostic.mo` with no `lang` types
/// in it at all, the copies here are the only ones -- the duplication the split
/// removes is a module boundary, not a second spelling of the same four lines,
/// and a `wire_*` prefix is what keeps them out of the way of the rest of
/// whole-program scope.
use json::json {Json}
use lang::types {Location, SourceRange}
use toolkit::jsonrpc {rpc_object}
use toolkit::position {
    LineIndex, PositionEncoding, WirePosition, WireRange, wire_position_character,
    wire_position_line, wire_position_mk, wire_range_end, wire_range_mk, wire_range_of_points,
    wire_range_start,
}

// --- The origin ---

/// The position `(0, 0)`: the first character of the first line.
///
/// A range nobody could compute, and the caller's fallback rather than this
/// module's. It is a real range at a real place -- a broken file is REPORTED as
/// broken rather than shown as clean -- and it is not a sentinel a consumer
/// checks for, which is why it is a `WireRange` and not an `Option`.
///
/// `wire_position_mk` rather than a `WirePosition` literal, per this module's own
/// note on the builder's existence one level up.
///
/// `pub` because `diagnostic.mo` -- the caller that takes this fallback -- is now
/// a different module; it was module-local when it lived there.
pub def wire_range_origin : WireRange :=
    wire_range_mk (wire_position_mk 0 0) (wire_position_mk 0 0)

// --- Reading `lang`'s two coordinates ---
//
// `SourceRange` is `{start : Location, end : Location, path : Option String}` and
// `Location` is `{offset : I64, line : I64, column : I64}`. Only `line` and
// `offset` are ever read: `offset` is bytes and `line` is 1-based, and `column`
// counts CHARACTERS, which is neither of the two units the specification uses, so
// there is nothing here that can consume it -- see `position.mo`'s module doc for
// why the byte offset is the reliable intermediate.

def range_start (r : SourceRange) : Location := r.start

def range_end (r : SourceRange) : Location := r.end

/// `lang`'s line number, 1-BASED. `position.mo`'s wire functions that take a
/// source-side line name it `source_line` for exactly this reason, and the
/// distinction is the one a caller gets wrong: the wire's own `line` field,
/// `WirePosition`, is 0-based.
def location_line (l : Location) : I64 := l.line

def location_offset (l : Location) : I64 := l.offset

/// A `lang` range on the wire.
///
/// `Option.none` when the range's START line does not exist in `ix` -- the one
/// way `wire_range_of_points` declines -- which a caller must decide about rather
/// than receive a made-up position for: a diagnostic reports it at the origin,
/// while a jump target has no target and a symbol is skipped.
///
/// `enc`, `ix` and `source` are the negotiated encoding, the line index for the
/// text the range came from, and that text. All three are needed because the
/// conversion counts bytes within a line, so the caller's contract is that the
/// index, the source and the coordinates are from ONE revision -- a line index
/// built from a different revision produces plausible-looking positions that are
/// silently wrong.
#[partial]
pub def wire_range_of_source_range (enc : PositionEncoding) (ix : LineIndex) (source : String)
    (sr : SourceRange) : Option WireRange :=
    wire_range_of_points enc ix source
        (location_line (range_start sr)) (location_offset (range_start sr))
        (location_line (range_end sr)) (location_offset (range_end sr))

// --- Wire JSON ---
//
// The shapes here are the specification's, so they are what a client expects and
// not a private convention: `Position` is `{line, character}` and `Range` is
// `{start, end}`, both positions 0-based. `Location` is `{uri, range}`.
//
// KEY ORDER IS NOT THE ORDER BELOW. `Json.to_string` walks a `BTreeMap`, so an
// object's keys come out SORTED -- `{"character":0,"line":0}`, `{"end":…,
// "start":…}`, `{"range":…,"uri":…}`. That is a wire detail rather than a
// correctness one, since the specification's objects are unordered and every
// client parses them by key, but it is what any test comparing rendered text has
// to expect, and it is why the fixtures in `tests/wire_tests.mo` are written in
// sorted order.

#[partial]
pub def wire_position_json (p : WirePosition) : Json :=
    rpc_object [
        Pair.pair "line" (Json.make_num_int (wire_position_line p)),
        Pair.pair "character" (Json.make_num_int (wire_position_character p)),
    ]

#[partial]
pub def wire_range_json (r : WireRange) : Json :=
    rpc_object [
        Pair.pair "start" (wire_position_json (wire_range_start r)),
        Pair.pair "end" (wire_position_json (wire_range_end r)),
    ]

/// A `Location`: a range, and which document it is in.
///
/// The URI is the caller's and is not derived from anything here. `lang`'s
/// `SourceRange` carries a `path` of its own, but it is the compiler's notion of a
/// path -- the one `check` prints -- while the wire wants the URI the client named
/// the document by, which a language server has in hand and which is not
/// recoverable from a path without deciding how the workspace root maps to URIs.
/// So the caller passes it, and the two are never conflated.
#[partial]
pub def location_json (uri : String) (r : WireRange) : Json :=
    rpc_object [
        Pair.pair "uri" (Json.make_str uri),
        Pair.pair "range" (wire_range_json r),
    ]

/// The composed one, for the two features whose answer IS a location: definition,
/// whose result is an array of these, and `documentSymbol`, whose every entry
/// carries one.
///
/// `Option` composes with `wire_range_of_source_range`'s, and the composition is
/// the point: a range that cannot be placed produces no location at all rather
/// than a location at the origin. The origin is right for a diagnostic, where
/// losing the marker entirely is worse than placing it wrong; it is wrong for a
/// jump, where a target at the top of the file is a lie the user will follow.
#[partial]
pub def location_json_of_source_range (uri : String) (enc : PositionEncoding) (ix : LineIndex)
    (source : String) (sr : SourceRange) : Option Json :=
    match wire_range_of_source_range enc ix source sr {
        Option.none => Option.none,
        Option.some r => Option.some (location_json uri r),
    }

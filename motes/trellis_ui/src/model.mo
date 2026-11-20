// The trellis graph: every declaration of the extracted motes, the module
// and mote each belongs to, and the references between them.
//
// The schema is chosen so later views need no new extractor:
// - each decl carries its `kind`, its attributes and its declared result
//   `sort` (`Prop` for a proposition), so a proof lens can pick theorems
//   and propositions out of the same file;
// - each edge carries its `axis`: `s` when the reference is in the
//   declaration's SIGNATURE (types, constraints, an instance head), `b` when
//   it is in the BODY. For a theorem, signature edges read "the statement
//   depends on" and body edges "the proof uses";
// - each decl carries `href`, a link in docgen's page/anchor scheme
//   (`<mote>/<module>.html#<kind>.<name>`), empty until docs are published;
// - each decl and module carries `docs`: its `///` doc comment as markdown
//   (docgen's scan, so trellis and the docs site agree on what a
//   declaration's docs are), rendered in the browser by `Trellis.docs_view`.
//   Empty when there is none.
//
// ## Wire format (`trellis 3`)
//
// One record per line, tab-separated. TSV rather than JSON on purpose: the
// browser parses the whole graph on load, and splitting lines is about fifty
// times faster than `Json.parse` on a graph of the type checker's size
// (measured 2026-11-18: 108 ms against 5.8 s for 47k records).
//
// ```text
// trellis<TAB>3
// R<TAB>root mote                     -- a mote the graph was extracted for
// M<TAB>path<TAB>mote<TAB>file<TAB>external(0|1)<TAB>docs
// D<TAB>module#<TAB>name<TAB>kind<TAB>vis<TAB>line<TAB>attrs<TAB>sort<TAB>href<TAB>docs<TAB>sig<TAB>end
// E<TAB>from decl#<TAB>to decl#<TAB>axis(s|b)
// S<TAB>refs<TAB>resolved<TAB>unresolved
// ```
//
// `#` fields are 0-based indices into the preceding M or D records; `attrs`
// is space-separated. A decl's id is `<module path>::<name>`. Fields never
// contain a tab or newline: names, paths and hrefs cannot, and `docs` and
// `sig` are escaped (`\\`, `\t`, `\n`; `Trellis.escape_field`). Only a
// field holding a backslash is unescaped, so plain fields decode as before.
// `end` is the declaration's last line. Source text is not in the file: the
// browser fetches a module's file on demand (`trellis serve`'s `/source`).
// Older files still decode: `trellis 2` has no `sig`/`end` (empty, and
// `end = line`), `trellis 1` no `docs` either.

use std::list {List.intercalate, List.filter, List.any}
use std::map {HashMap}
use lib::smap {Smap.empty, Smap.insert, Smap.get, Smap.get_i64}
use lib::seq {Seq.fold, Seq.reverse, Seq.map, Seq.lines}

pub struct Trellis.ModuleNode {
    path : String,
    mote : String,
    file : String,
    external : Bool,
    /// The module's leading doc comment, markdown (`""` for none).
    docs : String,
}

pub struct Trellis.DeclNode {
    id : String,
    name : String,
    module : String,
    mote : String,
    kind : String,
    vis : String,
    line : I64,
    /// The declaration's last line (`line` when unknown).
    end_line : I64,
    attrs : List String,
    sort : String,
    /// The declaration's docs page (`""` without a docs base).
    href : String,
    /// The `///` doc comment, markdown (`""` for none).
    docs : String,
    /// The declaration's header as written (docgen's `DocItem.signature`):
    /// a def without its `:=` and body, a type or class whole (`""` when
    /// unknown).
    sig : String,
    external : Bool,
}

pub struct Trellis.Edge {
    from : String,
    to : String,
    axis : String,
}

pub struct Trellis.Graph {
    roots : List String,
    modules : List Trellis.ModuleNode,
    decls : List Trellis.DeclNode,
    edges : List Trellis.Edge,
    refs : I64,
    resolved : I64,
    unresolved : I64,
}

pub def Trellis.Graph.empty : Trellis.Graph :=
    { roots := List.empty, modules := List.empty, decls := List.empty, edges := List.empty,
        refs := 0, resolved := 0, unresolved := 0 }

pub def Trellis.decl_id (module : String) (name : String) : String := String.concat_list [module, "::", name]

/// A proof-shaped declaration: `#[proof]`, `#[theorem]`, or a declared
/// result sort of `Prop`. The proof lens keys on it.
pub def Trellis.DeclNode.is_proof (d : Trellis.DeclNode) : Bool :=
    String.beq d.sort "Prop" || List.any (fn (a : String) => String.beq a "proof" || String.beq a "theorem") d.attrs

pub def Trellis.DeclNode.is_test (d : Trellis.DeclNode) : Bool :=
    List.any (fn (a : String) => String.beq a "test") d.attrs

// ═══ Encoding ═══

def tab_line (fields : List String) : String := List.intercalate "\t" fields

def flag (b : Bool) : String := if b then "1" else "0"

/// Free text as one field: `\` -> `\\`, tab -> `\t`, newline -> `\n`
/// (a carriage return is dropped).
pub def Trellis.escape_field (text : String) : String :=
    let parts : List String := String.split (List.intercalate "" (String.split text "\r")) "\\" in
    List.intercalate "\\\\" (List.map (fn (p : String) =>
        List.intercalate "\\t" (String.split (List.intercalate "\\n" (String.split p "\n")) "\t")) parts)

/// The inverse of `Trellis.escape_field`. Splitting on the escaped
/// backslash first leaves every other backslash the start of `\t` or `\n`.
pub def Trellis.unescape_field (field : String) : String :=
    if Bool.not (String.contains field "\\") then field
    else
        let parts : List String := String.split field "\\\\" in
        List.intercalate "\\" (List.map (fn (p : String) =>
            List.intercalate "\t" (String.split (List.intercalate "\n" (String.split p "\\n")) "\\t")) parts)

#[terminating]
def module_lines (ms : List Trellis.ModuleNode) : List String :=
    match ms {
        List.empty => List.empty,
        List.cons m rest => List.cons (tab_line ["M", m.path, m.mote, m.file, flag m.external,
            Trellis.escape_field m.docs]) (module_lines rest),
    }

#[terminating]
def index_strings (xs : List String) (i : I64) (m : HashMap String I64) : HashMap String I64 :=
    match xs {
        List.empty => m,
        List.cons x rest => index_strings rest (i + 1) (Smap.insert x i m),
    }

def module_path (m : Trellis.ModuleNode) : String := m.path
def decl_key (d : Trellis.DeclNode) : String := d.id

#[terminating]
def decl_lines (ds : List Trellis.DeclNode) (mods : HashMap String I64) : List String :=
    match ds {
        List.empty => List.empty,
        List.cons d rest =>
            let line : String := tab_line ["D", I64.to_string (Smap.get_i64 d.module 0 mods), d.name, d.kind, d.vis,
                I64.to_string d.line, List.intercalate " " d.attrs, d.sort, d.href, Trellis.escape_field d.docs,
                Trellis.escape_field d.sig, I64.to_string d.end_line] in
            List.cons line (decl_lines rest mods),
    }

#[terminating]
def edge_lines (es : List Trellis.Edge) (decls : HashMap String I64) : List String :=
    match es {
        List.empty => List.empty,
        List.cons e rest =>
            match Smap.get e.from decls {
                Option.none => edge_lines rest decls,
                Option.some a =>
                    match Smap.get e.to decls {
                        Option.none => edge_lines rest decls,
                        Option.some b => List.cons (tab_line ["E", I64.to_string a, I64.to_string b, e.axis])
                            (edge_lines rest decls),
                    },
            },
    }

#[terminating]
def root_lines (rs : List String) : List String :=
    match rs {
        List.empty => List.empty,
        List.cons r rest => List.cons (tab_line ["R", r]) (root_lines rest),
    }

/// The graph in the `trellis 3` wire format.
pub def Trellis.Graph.encode (g : Trellis.Graph) : String :=
    let mods : HashMap String I64 := index_strings (List.map module_path g.modules) 0 Smap.empty in
    let decls : HashMap String I64 := index_strings (List.map decl_key g.decls) 0 Smap.empty in
    List.intercalate "\n" (List.flatten [
        ["trellis\t3"],
        root_lines g.roots,
        module_lines g.modules,
        decl_lines g.decls mods,
        edge_lines g.edges decls,
        [tab_line ["S", I64.to_string g.refs, I64.to_string g.resolved, I64.to_string g.unresolved]]])

// ═══ Decoding ═══

#[terminating]
def digits (s : String) (acc : I64) : I64 :=
    if String.is_empty s then acc
    else
        let c : String := String.slice s 0 1 in
        let d : I64 := digit_in c ["0", "1", "2", "3", "4", "5", "6", "7", "8", "9"] 0 in
        if d < 0 then acc else digits (String.drop 1 s) (acc * 10 + d)

#[terminating]
def digit_in (c : String) (ds : List String) (i : I64) : I64 :=
    match ds {
        List.empty => 0 - 1,
        List.cons d rest => if String.beq c d then i else digit_in c rest (i + 1),
    }

/// A non-negative decimal field (`0` when absent or malformed).
pub def Trellis.parse_nat (s : String) : I64 := digits s 0

#[terminating]
def field (fs : List String) (i : I64) : String :=
    match fs {
        List.empty => "",
        List.cons f rest => if i <= 0 then f else field rest (i - 1),
    }

def words (s : String) : List String :=
    List.filter (fn (w : String) => Bool.not (String.is_empty w)) (String.split s " ")

/// Decoding is two folds over the lines: modules and decls first (the
/// edges name decls by index), then edges. Both go through `Seq`, so a
/// graph of any size decodes within the browser's stack.
struct Decoding {
    roots : List String,
    modules : List Trellis.ModuleNode,
    /// Module index (decimal) -> module, filled as M lines arrive (every M
    /// line comes before the D lines that index it).
    mods : HashMap String Trellis.ModuleNode,
    module_count : I64,
    decls : List Trellis.DeclNode,
    refs : I64,
    resolved : I64,
    unresolved : I64,
}

def no_module : Trellis.ModuleNode := { path := "", mote := "", file := "", external := false, docs := "" }

def module_at (mods : HashMap String Trellis.ModuleNode) (i : String) : Trellis.ModuleNode :=
    match Smap.get i mods { Option.some m => m, Option.none => no_module }

def decl_of (fs : List String) (mods : HashMap String Trellis.ModuleNode) : Trellis.DeclNode :=
    let m : Trellis.ModuleNode := module_at mods (field fs 1) in
    let name : String := field fs 2 in
    let line : I64 := Trellis.parse_nat (field fs 5) in
    let last : String := field fs 11 in
    { id := Trellis.decl_id m.path name, name := name, module := m.path, mote := m.mote,
        kind := field fs 3, vis := field fs 4, line := line,
        end_line := if String.is_empty last then line else Trellis.parse_nat last,
        attrs := words (field fs 6), sort := field fs 7, href := field fs 8,
        docs := Trellis.unescape_field (field fs 9), sig := Trellis.unescape_field (field fs 10),
        external := m.external }

def module_of (fs : List String) : Trellis.ModuleNode :=
    { path := field fs 1, mote := field fs 2, file := field fs 3, external := String.beq (field fs 4) "1",
        docs := Trellis.unescape_field (field fs 5) }

def first_step (p : Decoding) (line : String) : Decoding :=
    let fs : List String := String.split line "\t" in
    let tag : String := field fs 0 in
    if String.beq tag "M" then
        let m : Trellis.ModuleNode := module_of fs in
        { p with modules := List.cons m p.modules, mods := Smap.insert (I64.to_string p.module_count) m p.mods,
            module_count := p.module_count + 1 }
    else if String.beq tag "D" then { p with decls := List.cons (decl_of fs p.mods) p.decls }
    else if String.beq tag "R" then { p with roots := List.cons (field fs 1) p.roots }
    else if String.beq tag "S" then
        { p with refs := Trellis.parse_nat (field fs 1), resolved := Trellis.parse_nat (field fs 2),
            unresolved := Trellis.parse_nat (field fs 3) }
    else p

def id_at (ids : HashMap String String) (i : String) : String :=
    match Smap.get i ids { Option.some s => s, Option.none => "" }

def index_decl (acc : Pair I64 (HashMap String String)) (d : Trellis.DeclNode) : Pair I64 (HashMap String String) :=
    match acc { Pair.pair i m => Pair.pair (i + 1) (Smap.insert (I64.to_string i) d.id m) }

def edge_step (ids : HashMap String String) (acc : List Trellis.Edge) (line : String) : List Trellis.Edge :=
    if String.starts_with "E\t" line
    then
        let fs : List String := String.split line "\t" in
        let e : Trellis.Edge :=
            { from := id_at ids (field fs 1), to := id_at ids (field fs 2),
                axis := field fs 3 } in
        List.cons e acc
    else acc

/// Parse a `trellis 3` file (or an older `trellis 2`/`1` one, whose decls
/// have no signature or end line). `err` names what is wrong
/// with a file that is not one.
pub def Trellis.Graph.decode (text : String) : Result String Trellis.Graph :=
    let lines : List String := Seq.lines text in
    match lines {
        List.empty => Result.err "empty graph file",
        List.cons head _ =>
            if Bool.not (String.beq head "trellis\t3" || String.beq head "trellis\t2" || String.beq head "trellis\t1")
            then Result.err "not a trellis graph file"
            else
                let start : Decoding :=
                    { roots := List.empty, modules := List.empty, mods := Smap.empty, module_count := 0,
                        decls := List.empty,
                        refs := 0, resolved := 0, unresolved := 0 } in
                let p : Decoding := Seq.fold first_step start lines in
                let decls : List Trellis.DeclNode := Seq.reverse p.decls in
                let indexed : Pair I64 (HashMap String String) := Seq.fold index_decl (Pair.pair 0 Smap.empty) decls in
                let ids : HashMap String String := match indexed { Pair.pair _ m => m } in
                let edges : List Trellis.Edge := Seq.reverse (Seq.fold (edge_step ids) List.empty lines) in
                let g : Trellis.Graph :=
                    { roots := Seq.reverse p.roots, modules := Seq.reverse p.modules, decls := decls, edges := edges,
                        refs := p.refs, resolved := p.resolved, unresolved := p.unresolved } in
                Result.ok g,
    }

/// What a hover and a go-to-definition need from a checked file: the
/// identifier under the cursor, resolved to the declaration it names, with
/// enough of that declaration to show it and to jump to it.
///
/// ONE CALL SERVES BOTH FEATURES, and that is the shape rather than an
/// accident. Hover and definition ask different questions about the same
/// answer -- hover wants the declaration's type, definition wants its
/// position -- and `NavTarget` is that answer whole: a caller that only
/// wants a detail reads `nav_target_detail`, one that only wants a jump
/// reads `nav_target_range` and `nav_target_file`, and neither re-runs the
/// resolution. So there is exactly one entry point (`nav_at`, or
/// `nav_at_checked` for the ordinary caller that already has a check
/// result) rather than one per feature, and the two features cannot drift
/// apart in which names they resolve or how.
///
/// RESOLUTION IS THE COMPILER'S, NOT A SECOND OPINION. Every name goes
/// through `scope_resolve_name`, which is the call `infer.mo`,
/// `lower_core_ir.mo` and `module.mo` already resolve names with -- so a
/// name that typechecks resolves, a name that does not does not, and the
/// editor and the checker never disagree about whether an identifier means
/// something. A language server that re-implemented name lookup would be a
/// second implementation of the corpus's most load-bearing rule, and would
/// disagree with it exactly where the rule is subtle (a `::` spelling that
/// is a compiler-minted flat name, an `open`-aliased name, a promoted
/// instance method).
///
/// RESOLVING IS NOT THE SAME AS KNOWING WHAT IT IS, and that was measured
/// rather than assumed. `scope_resolve_name` answers a `ScopeDef` for a
/// TYPE name and for a CONSTRUCTOR name as readily as for a def -- the
/// first cut of this module read that as "it is a def" and answered
/// `def Color` for an inductive and `def red` for a constructor, the latter
/// with no range at all because the outline is keyed by the type's name.
/// So the FILE'S OWN OUTLINE is what decides the kind, the vocabulary and
/// the detail order: an identifier the outline names is answered with the
/// kind the file gives it (`def`, `type`, `struct`, `class`, `instance`,
/// ...) and a detail composed for that kind, and only an identifier the
/// outline does NOT name goes looking through the scope for a type, a
/// constructor, a class, or -- for a `use`d def -- a def with a file.
/// That also makes the outline the authority a user can see for
/// themselves, and gives the good behaviour for free: a declaration the
/// file declares but the checker could not resolve (a typo in its own type
/// annotation) still gets a jump target, because being in the outline is
/// enough to know where it is.
///
/// THE KEYS LINE UP BY CONSTRUCTION, which is what makes the range lookup
/// work at all. `DeclRange.name` for a def is `show_name_path (Def.name df)`
/// and the name a resolution answers with is that same `Def.name` rendered
/// -- the declaration's own `NamePath`, module or no module -- so the
/// string one side produces is the string the other is keyed by, with no
/// re-derivation on either side. The signature side tables agree for the
/// same reason: `ScopeData.def_sigs` and `def_return_types` are registered
/// under `defname` (`scope.mo`'s `build_scope_def`), which is the same
/// value.
///
/// WHAT THIS DOES NOT DO, all of it stated rather than silently absent:
///
/// - **`nav_at` resolves names, not locals.** A local is found by
///   position instead: `nav_at_cursor` walks the buffer's located
///   declarations to the var under the cursor and reads its binder off the
///   de Bruijn index (see "Locals" below), falling back to `nav_at` for
///   anything else. A caller with only a name, no position, still gets the
///   top-level def a local shadows.
/// - **A type's file is not known.** `ScopeDef` carries its `ModulePath`;
///   `Inductive` and `Class` do not, so a cross-file jump is offered for
///   defs and not for types and classes. Hover is unaffected -- a detail
///   needs no file -- and an in-file jump works for all of them.
/// - **A bare constructor name can be ambiguous.** The constructor index is
///   a scan that answers the first match, so hovering `some` in a corpus
///   with two types that declare it shows one of them. The scope's own doc
///   records this ambiguity as a real hazard for TYPECHECKING; for a hover
///   it is a display choice, and the alternative (withholding the answer)
///   is worse.
/// - **No hover text is composed for a module or a `use`.** Those resolve
///   to nothing at all here rather than to a made-up shape.
///
/// NOTHING HERE IS IO, and that is a deliberate boundary: this module
/// answers what the compiler knows, and reading the file a target lives in
/// is the caller's job (`decl_ranges_of_source` is public for exactly that
/// reason). It keeps `nav_at` usable from a pure test and keeps the
/// filesystem out of a module whose whole subject is name resolution.
use lib::module {
  DeclRange, ModuleInfo, ModuleInfoCache, RangedFileCheck, class_decl_name, struct_decl_name,
  decl_range_kind, decl_range_name, decl_range_span, inductive_decl_name,
  located_decl_list, located_decl_spans, module_info_cache_lookup, ranged_file_cache,
  ranged_file_located, ranged_file_ranges, ranged_file_scope,
}
use lib::parser {LocatedDecls}
use lib::pretty {show_class, show_inductive, show_struct, show_term}
use lib::scope {
  qualified_name_to_name_path, scope_find_class, scope_find_def_return_type,
  scope_find_def_sig, scope_find_inductive, scope_find_inductive_by_constructor,
  scope_resolve_name, split_qualified_identifier,
}
use lib::typecheck::infer {empty_locals}
use lib::typecheck::traverse {literal_children, term_children}
use lib::types {
  Binder, Class, ClassDef, DebugName, Decl, Def, Identifier, Inductive, Instance, Literal,
  Location, MatchCase, ModulePath, Struct, NamePath, NameRef, Scope, ScopeDef, SourceRange, Term,
  list_reverse, show_identifier, show_name_path, term_peel,
}

// --- The target ---

/// A resolved identifier: what it names, how to show it, and where to go.
///
/// `name` is the DECLARATION's own name, not the text the user typed --
/// which is the point of resolving: hovering `Color` and hovering a
/// `::`-qualified spelling of it reach the same declaration and answer with
/// the same name. For a constructor it is the name of the type that
/// declares it, because that is what the outline is keyed by and therefore
/// what a range can point at.
///
/// `kind` is the file's own word for the declaration (`DeclRange.kind`:
/// `def`, `type`, `struct`, `class`, `instance`, ...) whenever the outline
/// names it, and a resolved-through-the-scope word (`type`, `constructor`,
/// `class`, `def`) when it does not. A `documentSymbol` wants the file's
/// word and reads `DeclRange.kind` directly; a hover wants to know which
/// detail it has in hand, and `def`'s detail is a signature while a type's
/// is its whole declaration.
pub struct NavTarget {
  name : String,
  detail : String,
  kind : String,
  file : Option String,
  range : Option SourceRange,
}

pub def nav_target_mk (name : String) (detail : String) (kind : String)
    (file : Option String) (range : Option SourceRange) : NavTarget :=
  NavTarget.mk name detail kind file range

pub def nav_target_name (t : NavTarget) : String := t.name

pub def nav_target_detail (t : NavTarget) : String := t.detail

pub def nav_target_kind (t : NavTarget) : String := t.kind

/// The file the declaration is in, when it is NOT the file whose ranges
/// were passed -- the caller already knows its own, so answering it again
/// would only invite a caller to prefer a path to its own URI.
///
/// `Option.none` for a type or a class, always: neither carries a module.
pub def nav_target_file (t : NavTarget) : Option String := t.file

/// Where the declaration is, when it is in the file whose ranges were
/// passed. `Option.none` otherwise -- never a range at the origin, because
/// a jump to the top of the file is a lie the user will follow, unlike a
/// diagnostic at the origin, which reports that something is wrong.
pub def nav_target_range (t : NavTarget) : Option SourceRange := t.range

// --- Reading `lang`'s own values ---
//
// One field read each, one explicit return type each: the repository's
// convention for a field access (`module.mo`'s own `decl_range_*` block
// states it), and it is what keeps a struct's field names out of the rest
// of this module's bodies.

def nav_def_name (sd : ScopeDef) : NamePath := sd.name

def nav_def_module (sd : ScopeDef) : ModulePath := sd.module

def nav_info_file_path (info : ModuleInfo) : String := info.file_path

/// An inductive's declared name, rendered the way `DeclRange.name` renders
/// it for the same declaration.
#[partial]
def nav_ind_name (ind : Inductive) : String := show_name_path (inductive_decl_name ind)

/// A class's declared name, rendered the way `DeclRange.name` renders it.
#[partial]
def nav_class_name (cls : Class) : String := show_identifier (class_decl_name cls)

// --- The entry points ---

/// Resolve `ident` against a checked file's scope.
///
/// `ranges` is the file's own declaration table and `cache` its module
/// cache -- both, with the scope, come out of `RangedFileCheck`, which is
/// why `nav_at_checked` below exists and why the ordinary caller should
/// use it.
///
/// `Option.none` when the identifier names nothing at all AND the outline
/// does not have it either, which is the normal state of a buffer while it
/// is being typed and must not be reported as an error: an editor asks
/// about whatever is under the cursor, and "no such name" is a legitimate
/// answer to that question.
#[partial]
pub def nav_at (scope : Scope) (ranges : List DeclRange) (decls : List Decl)
    (cache : ModuleInfoCache) (ident : String) : Option NavTarget :=
  let ref : NameRef := NameRef.nid (Identifier.id ident) in
  match scope_resolve_name ref scope empty_locals {
    Result.ok sd => nav_resolved (show_name_path (nav_def_name sd)) sd ranges decls cache scope,
    // Not resolvable -- so the outline is the only thing left that could
    // know this name. A declaration the file declares but the checker could
    // not resolve is a real state (a typo in a declaration's own
    // annotation is the ordinary way to reach it), and it still has a place
    // to go.
    Result.err _ => nav_unresolved ident ranges decls scope,
  }

/// The same resolution, for the caller that already has a check result.
///
/// A file that did not elaborate has no scope, so this answers
/// `Option.none` rather than resolving against a half-built one -- the
/// three fields it unpacks are exactly the three a `RangedFileCheck` was
/// extended to carry.
#[partial]
pub def nav_at_checked (f : RangedFileCheck) (ident : String) : Option NavTarget :=
  match ranged_file_scope f {
    Option.none => Option.none,
    Option.some scope =>
      nav_at scope (ranged_file_ranges f) (located_decl_list (ranged_file_located f))
        (ranged_file_cache f) ident,
  }

// --- Resolution, in two directions ---

/// An identifier the scope resolved: answer it from the outline when the
/// outline names it, and from the scope when it does not.
///
/// The type lookup below is given the RESOLVED name rather than the text
/// that was typed, which is the second thing resolution buys: `lib::types::
/// Scope` and `Scope` reach the same inductive because both arrive as
/// `Scope`, so a qualified spelling that only the compiler can flatten
/// still hovers and still jumps.
#[partial]
def nav_resolved (name : String) (sd : ScopeDef) (ranges : List DeclRange)
    (decls : List Decl) (cache : ModuleInfoCache) (scope : Scope) : Option NavTarget :=
  match nav_decl_named ranges name {
    Option.some dr => Option.some (nav_local name dr decls scope),
    Option.none =>
      match nav_struct_far name (nav_def_module sd) cache {
        Option.some t => Option.some t,
        Option.none => nav_resolved_type_or_def name sd ranges cache scope,
      },
  }

/// Past the outline and a struct in another module: a type, constructor
/// or class from the scope, or a def in another module.
#[partial]
def nav_resolved_type_or_def (name : String) (sd : ScopeDef) (ranges : List DeclRange)
    (cache : ModuleInfoCache) (scope : Scope) : Option NavTarget :=
  match nav_of_type name scope ranges {
    Option.some t => Option.some t,
    Option.none => Option.some (nav_def_far name (nav_def_module sd) cache scope),
  }

/// An identifier the scope did not resolve: the outline may still know it,
/// and past that there is nothing to answer with.
#[partial]
def nav_unresolved (ident : String) (ranges : List DeclRange) (decls : List Decl) (scope : Scope)
    : Option NavTarget :=
  match nav_decl_named ranges ident {
    Option.some dr => Option.some (nav_local ident dr decls scope),
    Option.none => nav_of_type ident scope ranges,
  }

/// A declaration THIS FILE declares: the kind and the range come from the
/// file's own outline, so the word a user sees is the one their file is
/// written in.
///
/// The detail is composed from that kind rather than from the resolution,
/// which is the fix for the measurement above: a `type` gets
/// `show_inductive`'s rendering of the whole declaration, a `struct` gets
/// `show_struct`'s (read from `decls`, the buffer's own declarations), a
/// `def` gets its signature, and a kind with no printer of its own
/// (`instance`, `infix`, ...) gets its name -- honest, since the file is
/// about to show the declaration itself a few lines away.
def nav_local (name : String) (dr : DeclRange) (decls : List Decl) (scope : Scope) : NavTarget :=
  let kind : String := decl_range_kind dr in
  let no_file : Option String := Option.none in
  nav_target_mk name (nav_detail_by_kind name kind decls scope) kind no_file
    (Option.some (decl_range_span dr))

/// A name the outline does not carry: a type, a constructor or a class from
/// the scope, or a `use`d def whose owning module the cache can name.
///
/// The range is looked up by the name that was FOUND -- a constructor's
/// type, an inductive's own name -- which is what makes a type's range the
/// declaration's rather than the position of any one mention of it. That is
/// the whole reason a constructor answers its type's name: the outline is
/// keyed by declarations, and `red` is not one.
#[partial]
def nav_of_type (name : String) (scope : Scope) (ranges : List DeclRange) : Option NavTarget :=
  match nav_find_inductive (nav_lookup_keys (Identifier.id name)) scope {
    Option.some ind =>
      Option.some (nav_type_target (nav_ind_name ind) (show_inductive ind) "type" ranges),
    Option.none =>
      match nav_find_ctor (nav_lookup_keys (Identifier.id name)) scope {
        Option.some ind =>
          Option.some (nav_type_target (nav_ind_name ind) (show_inductive ind) "constructor" ranges),
        Option.none =>
          match nav_find_class (nav_lookup_keys (Identifier.id name)) scope {
            Option.some cls =>
              Option.some (nav_type_target (nav_class_name cls) (show_class cls) "class" ranges),
            Option.none => Option.none,
          },
      },
  }

/// A type, constructor or class target: the same shape as a def's, with no
/// file ever offered (see this module's own note on that limit) and the
/// detail handed in rather than looked up -- `show_inductive`/`show_class`
/// already render the whole declaration, so there is no signature table to
/// consult.
#[partial]
def nav_type_target (name : String) (detail : String) (kind : String)
    (ranges : List DeclRange) : NavTarget :=
  let no_file : Option String := Option.none in
  let no_range : Option SourceRange := Option.none in
  match nav_span_named ranges name {
    Option.some r => nav_target_mk name detail kind no_file (Option.some r),
    Option.none => nav_target_mk name detail kind no_file no_range,
  }

/// A def the outline does not name and the scope resolved anyway: a def
/// from another file, whose file the module cache can name and whose range
/// this module cannot.
#[partial]
def nav_def_far (name : String) (mp : ModulePath) (cache : ModuleInfoCache)
    (scope : Scope) : NavTarget :=
  let no_range : Option SourceRange := Option.none in
  nav_target_mk name (nav_def_detail name scope) "def" (nav_module_file mp cache) no_range

// --- Finding a span by name ---

/// The declaration called `name` in this file's outline, or nothing.
///
/// A linear walk rather than a map, because the table is a file's own
/// declarations -- tens of entries, already in hand, and read once per
/// request. A `HashMap` here would be a second index to keep in step with
/// the first, for a lookup that costs less than building it.
#[partial]
def nav_decl_named (ranges : List DeclRange) (name : String) : Option DeclRange :=
  match ranges {
    List.empty => Option.none,
    List.cons dr rest =>
      if String.beq (decl_range_name dr) name
      then Option.some dr
      else nav_decl_named rest name,
  }

/// The span of the declaration called `name`, or nothing -- the outline's
/// half of the same lookup, for a target whose kind came from the scope
/// rather than from the file.
#[partial]
def nav_span_named (ranges : List DeclRange) (name : String) : Option SourceRange :=
  match nav_decl_named ranges name {
    Option.none => Option.none,
    Option.some dr => Option.some (decl_range_span dr),
  }

/// The `ModuleInfoCache`'s answer for a module: the file on disk its
/// declarations came from.
///
/// `Option.none` when the module is not in the cache, which includes the
/// file being checked -- the walk inserts the modules it LOADS, and the
/// buffer under the cursor is not one of them. So a def whose only
/// remaining question was "which file" answers nothing rather than
/// guessing, and the caller's own file is the caller's own business.
#[partial]
def nav_module_file (mp : ModulePath) (cache : ModuleInfoCache) : Option String :=
  match module_info_cache_lookup mp cache {
    Option.none => Option.none,
    Option.some info => Option.some (nav_info_file_path info),
  }

// --- Looking a non-def name up ---

/// The keys to try for a name as a user typed it: the bare spelling first,
/// then the `::`-flattened one.
///
/// The same two-step, in the same order, that `resolve_name_in_scope`
/// applies to a def's `NameRef.nid`, and for the same reason: a `::` in a
/// spelling is NOT reliably a qualified reference -- a compiler-minted name
/// (`with_module_prefix` mangles a promoted instance method to
/// `lang.codegen.ctors::BEq_I64_beq`) is registered under its whole
/// spelling as its own key, so flattening eagerly finds a key that does not
/// exist and misses the one that does.
#[partial]
def nav_lookup_keys (ident : Identifier) : List NamePath :=
  let bare : NamePath := NamePath.mk (List.cons ident List.empty) in
  match split_qualified_identifier ident {
    Option.some qn => List.cons bare (List.cons (qualified_name_to_name_path qn) List.empty),
    Option.none => List.cons bare List.empty,
  }

#[partial]
def nav_find_inductive (keys : List NamePath) (scope : Scope) : Option Inductive :=
  match keys {
    List.empty => Option.none,
    List.cons k rest =>
      match scope_find_inductive k scope {
        Result.ok ind => Option.some ind,
        Result.err _ => nav_find_inductive rest scope,
      },
  }

#[partial]
def nav_find_ctor (keys : List NamePath) (scope : Scope) : Option Inductive :=
  match keys {
    List.empty => Option.none,
    List.cons k rest =>
      match scope_find_inductive_by_constructor k scope {
        Option.some ind => Option.some ind,
        Option.none => nav_find_ctor rest scope,
      },
  }

#[partial]
def nav_find_class (keys : List NamePath) (scope : Scope) : Option Class :=
  match keys {
    List.empty => Option.none,
    List.cons k rest =>
      match scope_find_class k scope {
        Option.some cls => Option.some cls,
        Option.none => nav_find_class rest scope,
      },
  }

// --- A declaration's detail, by kind ---

/// One line to show for a hover, chosen by the kind the FILE gave the
/// declaration.
#[partial]
def nav_detail_by_kind (name : String) (kind : String) (decls : List Decl) (scope : Scope)
    : String :=
  if String.beq kind "struct"
  then nav_struct_detail name decls
  else if String.beq kind "type"
  then nav_inductive_detail name scope
  else if String.beq kind "class"
  then nav_class_detail name scope
  else if String.beq kind "def"
  then nav_def_detail name scope
  else name

#[partial]
def nav_inductive_detail (name : String) (scope : Scope) : String :=
  match nav_find_inductive (nav_lookup_keys (Identifier.id name)) scope {
    Option.some ind => show_inductive ind,
    // An inductive the outline names and the scope does not: the name is
    // all there is, and it is better than nothing to show.
    Option.none => name,
  }

#[partial]
def nav_class_detail (name : String) (scope : Scope) : String :=
  match nav_find_class (nav_lookup_keys (Identifier.id name)) scope {
    Option.some cls => show_class cls,
    Option.none => name,
  }

/// One line to show for a def: `def <name> : <type>`.
///
/// THE SIGNATURE COMES FROM THE SIDE TABLE, never from `ScopeDef.sig`.
/// `build_scope_def` sets `sig := Term.hole, body := Term.hole`
/// unconditionally -- the sentinel is load-bearing for dozens of call
/// sites -- so rendering `sd.sig` would show a hover that reads `def
/// show_name_path : _` for every def in the corpus. `ScopeData.def_sigs`
/// holds the real declared signature, registered under the same name this
/// target's name came from, and is read through the public
/// `scope_find_def_sig`.
///
/// The name is turned back into a `NamePath` as a SINGLE identifier, which
/// is not a lossy step: `npath_map_*` keys by `show_name_path`'s rendering,
/// and a single identifier whose text is `IO.file_exists` renders exactly
/// like the two-segment path a dotted declaration registers under. So the
/// key is the same string either way, which is the property that matters.
///
/// The return-type fallback is for a def whose full signature was never
/// registered, which is the macro-synthesized case: a derived or generated
/// def has a return type but no decl site to have recorded a `typ` from.
/// Past that, the name alone -- a hover that shows only what was typed is a
/// worse answer than a signature and a much better one than nothing.
#[partial]
def nav_def_detail (name : String) (scope : Scope) : String :=
  let np : NamePath := NamePath.mk (List.cons (Identifier.id name) List.empty) in
  match scope_find_def_sig np scope {
    Option.some t => "def " ++ name ++ " : " ++ show_term t,
    Option.none =>
      match scope_find_def_return_type np scope {
        Option.some t => "def " ++ name ++ " : " ++ show_term t,
        Option.none => "def " ++ name,
      },
  }

// --- Locals: the cursor-to-binding walk ---
//
// `nav_at` resolves a NAME, and a local is not a name the scope knows. So a
// cursor is first looked for in the buffer's own located declarations
// (`RangedFileCheck.located`): the term under it is a `Term.var` whose de
// Bruijn index the parser already resolved, and counting the binders the
// walk crossed turns that index into the binder it names -- the same
// answer the lowering gave, so shadowing is decided by the compiler and not
// re-derived here. Only a cursor that is NOT on a local falls through to
// `nav_at`.
//
// A binder carries no position (`Binder`/`MatchCase.args` are names), so
// where one is WRITTEN is found in the text: the last whole-word
// occurrence of its name between the declaration's start and the first
// located term of its body that is not itself a located term. A use of the
// name is always located; the binder never is.

/// What a walk is looking for, and what it needs to place a binder.
///
/// `starts` is the offset of every located term in the declaration -- the
/// occurrences of a name that are uses, and so never its binder.
struct NavWalk {
  source : String,
  target : I64,
  ident : String,
  decl_start : I64,
  starts : List I64,
}

/// A binder in scope at a point of the walk: its name, its declared type
/// (`Term.hole` when unannotated), and the term it binds over.
struct NavBinder {
  name : String,
  typ : Term,
  body : Term,
}

/// What the walk found at the cursor: a local (its name, type and the
/// offset its binder is written at, when that could be found), a name that
/// is not a local, or nothing located there at all.
type NavHit {
  bound (name : String) (typ : Term) (offset : Option I64),
  free,
  nothing,
}

/// Resolve the identifier at byte `start` of `source`, locals first.
///
/// `source` is the text `f` was checked from and `start` the identifier's
/// first byte in it. A cursor on a local -- a use or the binder itself --
/// answers that binder, even with the file's scope missing; any other
/// cursor answers exactly what `nav_at_checked` does.
#[partial]
pub def nav_at_cursor (f : RangedFileCheck) (source : String) (ident : String) (start : I64)
    : Option NavTarget :=
  match nav_local_hit f source ident start {
    NavHit.bound name typ offset => Option.some (nav_local_binder_target source name typ offset),
    NavHit.free => nav_at_checked f ident,
    NavHit.nothing => nav_at_checked f ident,
  }

/// A local's target: kind `local`, its type when it was written, and the
/// binder's own extent in this file.
#[partial]
def nav_local_binder_target (source : String) (name : String) (typ : Term)
    (offset : Option I64) : NavTarget :=
  let no_file : Option String := Option.none in
  nav_target_mk name (nav_local_detail name typ) "local" no_file
    (nav_binder_range source name offset)

#[partial]
def nav_local_detail (name : String) (typ : Term) : String :=
  match term_peel typ {
    Term.hole => name,
    _ => name ++ " : " ++ show_term typ,
  }

#[partial]
def nav_binder_range (source : String) (name : String) (offset : Option I64)
    : Option SourceRange :=
  match offset {
    Option.none => Option.none,
    Option.some off =>
      let stop : I64 := off + String.length name in
      let r : SourceRange := {
        start := nav_location_at source off,
        end := nav_location_at source stop,
        path := Option.none,
      } in
      Option.some r,
  }

/// A byte offset as a `Location`: 1-based line and column, the convention
/// the parser's own ranges use.
#[partial]
def nav_location_at (source : String) (off : I64) : Location :=
  nav_location_scan (String.to_list (String.slice source 0 off)) 0 1 0

/// `line` so far, and the offset just past the last newline seen.
#[partial]
def nav_location_scan (bytes : List U8) (i : I64) (line : I64) (line_start : I64) : Location :=
  match bytes {
    List.empty =>
      let loc : Location := { offset := i, line := line, column := i - line_start + 1 } in
      loc,
    // One self-call, so the compiled backend's tail-call loop applies.
    List.cons b rest =>
      let nl : Bool := U8.beq b nav_byte_newline in
      nav_location_scan rest (i + 1) (if nl then line + 1 else line)
        (if nl then i + 1 else line_start),
  }

def nav_byte_newline : U8 := 10u8

// --- The walk over the buffer's declarations ---

#[partial]
def nav_local_hit (f : RangedFileCheck) (source : String) (ident : String) (start : I64) : NavHit :=
  let located : LocatedDecls := ranged_file_located f in
  nav_hit_in_decls source ident start (located_decl_list located) (located_decl_spans located)

/// The declaration whose span covers the cursor, walked; nothing when none
/// does.
#[partial]
def nav_hit_in_decls (source : String) (ident : String) (start : I64) (ds : List Decl)
    (spans : List SourceRange) : NavHit :=
  match ds {
    List.empty => NavHit.nothing,
    List.cons d rest =>
      match spans {
        List.empty => NavHit.nothing,
        List.cons sp more =>
          if nav_span_covers sp start
          then nav_hit_in_decl source ident start sp d
          else nav_hit_in_decls source ident start rest more,
      },
  }

#[partial]
def nav_span_covers (sp : SourceRange) (off : I64) : Bool :=
  Bool.not (I64.lt off (nav_loc_offset (nav_range_start sp)))
    && I64.lt off (nav_loc_offset (nav_range_end sp))

#[partial]
def nav_hit_in_decl (source : String) (ident : String) (start : I64) (sp : SourceRange) (d : Decl)
    : NavHit :=
  let terms : List Term := nav_decl_terms d in
  let st : NavWalk := {
    source := source,
    target := start,
    ident := ident,
    decl_start := nav_loc_offset (nav_range_start sp),
    starts := nav_starts_of_terms terms List.empty,
  } in
  let no_binders : List NavBinder := List.empty in
  nav_walk_terms st no_binders terms

/// The value-level terms a declaration carries: a def's body, an
/// instance's method bodies, a class's default method bodies. Signatures
/// are type-level and carry no positions, so they are not walked.
#[partial]
def nav_decl_terms (d : Decl) : List Term :=
  match d {
    Decl.def_d df => [nav_def_term df],
    Decl.instance_d i => nav_def_terms (nav_instance_defs i) List.empty,
    Decl.class_d c => nav_class_default_terms (nav_class_methods c) List.empty,
    _ => List.empty,
  }

def nav_def_term (df : Def) : Term := df.term

def nav_instance_defs (i : Instance) : List Def := i.defs

def nav_class_methods (c : Class) : List ClassDef := c.methods

def nav_class_method_default (m : ClassDef) : Option Term := m.default

#[partial]
def nav_def_terms (ds : List Def) (acc : List Term) : List Term :=
  match ds {
    List.empty => list_reverse acc,
    List.cons df rest => nav_def_terms rest (List.cons (nav_def_term df) acc),
  }

#[partial]
def nav_class_default_terms (ms : List ClassDef) (acc : List Term) : List Term :=
  match ms {
    List.empty => list_reverse acc,
    List.cons m rest => nav_class_default_terms rest (nav_cons_some (nav_class_method_default m) acc),
  }

#[partial]
def nav_cons_some (o : Option Term) (acc : List Term) : List Term :=
  match o {
    Option.none => acc,
    Option.some t => List.cons t acc,
  }

/// Walk each term in turn; the first that finds something answers.
#[partial]
def nav_walk_terms (st : NavWalk) (stack : List NavBinder) (ts : List Term) : NavHit :=
  match ts {
    List.empty => NavHit.nothing,
    List.cons t rest => nav_walk_terms_after st stack (nav_walk st stack t) rest,
  }

#[partial]
def nav_walk_terms_after (st : NavWalk) (stack : List NavBinder) (h : NavHit) (rest : List Term)
    : NavHit :=
  match h {
    NavHit.nothing => nav_walk_terms st stack rest,
    NavHit.free => NavHit.free,
    NavHit.bound name typ offset => NavHit.bound name typ offset,
  }

/// One term. The binding forms push onto `stack` -- innermost first, so a
/// de Bruijn index is a position in it -- and a `pi` is type-level, so
/// nothing under it is located and it is not entered.
#[partial]
def nav_walk (st : NavWalk) (stack : List NavBinder) (t : Term) : NavHit :=
  match t {
    Term.ctx loc inner => nav_walk_located st stack loc inner,
    Term.lam b typ body => nav_walk_binder st stack (nav_binder_name b) typ body,
    Term.pi _b _arg _ret => NavHit.nothing,
    Term.lit l => nav_walk_lit st stack l,
    _ => nav_walk_terms st stack (term_children t),
  }

/// A located term at the cursor is where the identifier's var is: as the
/// term itself, or as the head of the spine it starts. Anything else at the
/// same offset (an infix spine starts at its left operand, whose own var is
/// located again further in) is found by walking on.
#[partial]
def nav_walk_located (st : NavWalk) (stack : List NavBinder) (loc : Location) (inner : Term)
    : NavHit :=
  if I64.beq (nav_loc_offset loc) st.target
  then nav_walk_located_after st stack (nav_head st stack inner) inner
  else nav_walk st stack inner

#[partial]
def nav_walk_located_after (st : NavWalk) (stack : List NavBinder) (h : NavHit) (inner : Term)
    : NavHit :=
  match h {
    NavHit.nothing => nav_walk st stack inner,
    NavHit.free => NavHit.free,
    NavHit.bound name typ offset => NavHit.bound name typ offset,
  }

#[partial]
def nav_head (st : NavWalk) (stack : List NavBinder) (t : Term) : NavHit :=
  nav_head_peeled st stack (term_peel t)

/// The var a spine starts with. A field access (`s.width`) lowers to a
/// `match` on its receiver, so the receiver is the head there.
#[partial]
def nav_head_peeled (st : NavWalk) (stack : List NavBinder) (t : Term) : NavHit :=
  match t {
    Term.var idx dbg => nav_head_var st stack idx dbg,
    Term.app callee _arg => nav_head st stack callee,
    Term.lit l => nav_head_lit st stack l,
    _ => NavHit.nothing,
  }

#[partial]
def nav_head_lit (st : NavWalk) (stack : List NavBinder) (l : Literal) : NavHit :=
  match l {
    Literal.match_ scrut _cases => nav_head st stack scrut,
    _ => NavHit.nothing,
  }

/// The var at the cursor, if it is the identifier there. A dotted
/// identifier (`s.width`, one run to the text scan) matches the var for
/// its first segment.
#[partial]
def nav_head_var (st : NavWalk) (stack : List NavBinder) (idx : I64) (dbg : DebugName) : NavHit :=
  match dbg {
    DebugName.unnamed => NavHit.nothing,
    DebugName.named id =>
      if nav_name_matches (show_identifier id) st.ident
      then nav_classify st (nav_nth stack idx)
      else NavHit.nothing,
  }

#[partial]
def nav_name_matches (name : String) (ident : String) : Bool :=
  String.beq name ident || String.starts_with (name ++ ".") ident

/// A var's binder, from its index: the index-th entry of the stack, or a
/// name that is not a local (`sentinel`, or a binder outside the walk).
#[partial]
def nav_classify (st : NavWalk) (b : Option NavBinder) : NavHit :=
  match b {
    Option.none => NavHit.free,
    Option.some nb => NavHit.bound nb.name nb.typ (nav_binder_offset st nb),
  }

#[partial]
def nav_nth (stack : List NavBinder) (idx : I64) : Option NavBinder :=
  if I64.lt idx 0
  then Option.none
  else nav_nth_go stack idx

#[partial]
def nav_nth_go (stack : List NavBinder) (idx : I64) : Option NavBinder :=
  match stack {
    List.empty => Option.none,
    List.cons b rest =>
      if I64.beq idx 0
      then Option.some b
      else nav_nth_go rest (idx - 1),
  }

/// A binder: the cursor may be ON it, and otherwise its body is walked
/// with it in scope.
#[partial]
def nav_walk_binder (st : NavWalk) (stack : List NavBinder) (name : String) (typ : Term)
    (body : Term) : NavHit :=
  let b : NavBinder := { name := name, typ := typ, body := body } in
  if nav_cursor_on_binder st b
  then NavHit.bound name typ (Option.some st.target)
  else nav_walk st (List.cons b stack) body

#[partial]
def nav_cursor_on_binder (st : NavWalk) (b : NavBinder) : Bool :=
  String.beq b.name st.ident && nav_offset_is (nav_binder_offset st b) st.target

#[partial]
def nav_offset_is (o : Option I64) (target : I64) : Bool :=
  match o {
    Option.none => false,
    Option.some off => I64.beq off target,
  }

#[partial]
def nav_binder_name (b : Binder) : String :=
  match nav_binder_debug_name b {
    DebugName.named id => show_identifier id,
    DebugName.unnamed => "",
  }

def nav_binder_debug_name (b : Binder) : DebugName := b.name

#[partial]
def nav_walk_lit (st : NavWalk) (stack : List NavBinder) (l : Literal) : NavHit :=
  match l {
    Literal.match_ scrut cases => nav_walk_cases_after st stack (nav_walk st stack scrut) cases,
    _ => nav_walk_terms st stack (literal_children l),
  }

#[partial]
def nav_walk_cases_after (st : NavWalk) (stack : List NavBinder) (h : NavHit)
    (cases : List MatchCase) : NavHit :=
  match h {
    NavHit.nothing => nav_walk_cases st stack cases,
    NavHit.free => NavHit.free,
    NavHit.bound name typ offset => NavHit.bound name typ offset,
  }

#[partial]
def nav_walk_cases (st : NavWalk) (stack : List NavBinder) (cases : List MatchCase) : NavHit :=
  match cases {
    List.empty => NavHit.nothing,
    List.cons c rest =>
      nav_walk_cases_after_case st stack
        (nav_walk_case st stack (nav_case_args c) (nav_case_body c)) rest,
  }

#[partial]
def nav_walk_cases_after_case (st : NavWalk) (stack : List NavBinder) (h : NavHit)
    (rest : List MatchCase) : NavHit :=
  match h {
    NavHit.nothing => nav_walk_cases st stack rest,
    NavHit.free => NavHit.free,
    NavHit.bound name typ offset => NavHit.bound name typ offset,
  }

def nav_case_args (c : MatchCase) : List Identifier := c.args

def nav_case_body (c : MatchCase) : Term := c.body

/// A match arm's pattern names bind over its body, the LAST one innermost
/// (`lower_ctx_bind_all`) -- so they are pushed in order. A pattern name
/// carries no type.
#[partial]
def nav_walk_case (st : NavWalk) (stack : List NavBinder) (args : List Identifier) (body : Term)
    : NavHit :=
  match args {
    List.empty => nav_walk st stack body,
    List.cons a rest => nav_walk_case_arg st stack (show_identifier a) rest body,
  }

#[partial]
def nav_walk_case_arg (st : NavWalk) (stack : List NavBinder) (name : String)
    (rest : List Identifier) (body : Term) : NavHit :=
  let b : NavBinder := { name := name, typ := Term.hole, body := body } in
  if nav_cursor_on_binder st b
  then NavHit.bound name Term.hole (Option.some st.target)
  else nav_walk_case st (List.cons b stack) rest body

// --- Where a binder is written ---

/// The offset of the binder's name in the text: the last whole-word
/// occurrence of it before its body's first located term, from the
/// declaration's start, that is not a use. `Option.none` when its body has
/// no located term to bound the search, or no occurrence qualifies.
#[partial]
def nav_binder_offset (st : NavWalk) (b : NavBinder) : Option I64 :=
  match nav_min_start (nav_starts_of_terms [b.body] List.empty) {
    Option.none => Option.none,
    Option.some upper =>
      nav_last_word st.starts b.name st.decl_start
        (String.to_list (String.slice st.source st.decl_start (upper - st.decl_start))),
  }

#[partial]
def nav_min_start (offs : List I64) : Option I64 :=
  match offs {
    List.empty => Option.none,
    List.cons o rest => Option.some (nav_min_go rest o),
  }

#[partial]
def nav_min_go (offs : List I64) (best : I64) : I64 :=
  match offs {
    List.empty => best,
    List.cons o rest => nav_min_go rest (if I64.lt o best then o else best),
  }

/// Every located term's offset under `ts`, prepended to `acc`.
#[partial]
def nav_starts_of_terms (ts : List Term) (acc : List I64) : List I64 :=
  match ts {
    List.empty => acc,
    List.cons t rest => nav_starts_of_terms rest (nav_starts_of_term t acc),
  }

#[partial]
def nav_starts_of_term (t : Term) (acc : List I64) : List I64 :=
  match t {
    Term.ctx loc inner => nav_starts_of_terms [inner] (List.cons (nav_loc_offset loc) acc),
    _ => nav_starts_of_terms (term_children t) acc,
  }

/// The last identifier run in `bytes` (which start at `base`) spelling
/// `name` and not starting at a use.
#[partial]
def nav_last_word (uses : List I64) (name : String) (base : I64) (bytes : List U8) : Option I64 :=
  nav_word_scan uses name base bytes 0 0 List.empty Option.none

/// One pass over identifier runs. `run_start` is the offset of the run in
/// progress (relative to `base`) and `run` its bytes, reversed.
#[partial]
def nav_word_scan (uses : List I64) (name : String) (base : I64) (bytes : List U8) (i : I64)
    (run_start : I64) (run : List U8) (best : Option I64) : Option I64 :=
  match bytes {
    List.empty => nav_word_close uses name (base + run_start) run best,
    // One self-call, for the same reason as `nav_location_scan`.
    List.cons b rest =>
      let in_run : Bool := nav_byte_is_identifier b in
      let no_run : List U8 := List.empty in
      nav_word_scan uses name base rest (i + 1)
        (if in_run then run_start else i + 1)
        (if in_run then List.cons b run else no_run)
        (if in_run then best else nav_word_close uses name (base + run_start) run best),
  }

/// A run just ended at absolute `at`: it is the new best when it spells
/// `name` and is not a use.
#[partial]
def nav_word_close (uses : List I64) (name : String) (at_off : I64) (run : List U8)
    (best : Option I64) : Option I64 :=
  if String.beq (String.from_list (list_reverse run)) name
      && Bool.not (nav_contains_i64 uses at_off)
  then Option.some at_off
  else best

#[partial]
def nav_contains_i64 (xs : List I64) (x : I64) : Bool :=
  match xs {
    List.empty => false,
    List.cons y rest => I64.beq x y || nav_contains_i64 rest x,
  }

/// The text scan's identifier bytes (`toolkit::text`): letters, digits,
/// `_`, `.` and `'`. `U8.lt` is not `pub`, hence the floors one below.
#[partial]
def nav_byte_is_identifier (b : U8) : Bool :=
  (U8.gt b 47u8 && Bool.not (U8.gt b 57u8))
    || (U8.gt b 64u8 && Bool.not (U8.gt b 90u8))
    || (U8.gt b 96u8 && Bool.not (U8.gt b 122u8))
    || U8.beq b 95u8
    || U8.beq b 46u8
    || U8.beq b 39u8

def nav_loc_offset (l : Location) : I64 := l.offset

def nav_range_start (r : SourceRange) : Location := r.start

def nav_range_end (r : SourceRange) : Location := r.end

// --- Structs ---
//
// A struct enters the scope as a synthetic one-constructor `Inductive`
// (`build_scope_struct`), so `show_inductive` would render a `type` the
// user never wrote. The `Struct` itself survives only in declaration
// lists: the buffer's located decls for a struct this file declares, and
// `ModuleInfo.decl_list` for one a loaded module declares -- whose module
// its type name's `ScopeDef` carries.

/// The struct called `name` in `decls`, rendered; the bare name when the
/// list does not have it.
#[partial]
def nav_struct_detail (name : String) (decls : List Decl) : String :=
  match nav_find_struct name decls {
    Option.some st => show_struct st,
    Option.none => name,
  }

#[partial]
def nav_find_struct (name : String) (decls : List Decl) : Option Struct :=
  match decls {
    List.empty => Option.none,
    List.cons d rest => nav_find_struct_after name (nav_struct_named name d) rest,
  }

#[partial]
def nav_find_struct_after (name : String) (found : Option Struct) (rest : List Decl)
    : Option Struct :=
  match found {
    Option.some st => Option.some st,
    Option.none => nav_find_struct name rest,
  }

#[partial]
def nav_struct_named (name : String) (d : Decl) : Option Struct :=
  match d {
    Decl.struct_d st =>
      if String.beq (show_identifier (struct_decl_name st)) name
      then Option.some st
      else Option.none,
    _ => Option.none,
  }

/// A struct another module declares: rendered from that module's decls,
/// with its file so a jump can find it there. `Option.none` when the
/// module is not cached or declares no struct by that name.
#[partial]
def nav_struct_far (name : String) (mp : ModulePath) (cache : ModuleInfoCache)
    : Option NavTarget :=
  match module_info_cache_lookup mp cache {
    Option.none => Option.none,
    Option.some info => nav_struct_in_info name info,
  }

#[partial]
def nav_struct_in_info (name : String) (info : ModuleInfo) : Option NavTarget :=
  match nav_find_struct name (nav_info_decls info) {
    Option.none => Option.none,
    Option.some st =>
      let no_range : Option SourceRange := Option.none in
      Option.some (nav_target_mk name (show_struct st) "struct"
        (Option.some (nav_info_file_path info)) no_range),
  }

def nav_info_decls (info : ModuleInfo) : List Decl := info.decl_list

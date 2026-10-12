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
/// - **Locals are not resolved.** `scope_resolve_name` takes a
///   `LocalScope`, and this passes the empty one. `LocalVar` carries no
///   location and `Term.var` is positional, so resolving a local properly
///   means walking the term tree from the declaration that encloses the
///   cursor -- the walk the Rust server this replaces explicitly declined
///   to do, and its own doc comment records the resulting defect: a local
///   shadowing a top-level def resolves to the top-level one. This cut
///   does not fix that; it inherits it deliberately, because the fix is a
///   new piece of work (a cursor-to-binding walk) rather than a parameter.
///   The visible consequence: `gd` on a local that does NOT shadow anything
///   answers no target, correctly; on one that DOES it answers the
///   top-level def, which is wrong.
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
  DeclRange, ModuleInfo, ModuleInfoCache, RangedFileCheck, class_decl_name,
  decl_range_kind, decl_range_name, decl_range_span, inductive_decl_name,
  module_info_cache_lookup, ranged_file_cache, ranged_file_ranges, ranged_file_scope,
}
use lib::pretty {show_class, show_inductive, show_term}
use lib::scope {
  qualified_name_to_name_path, scope_find_class, scope_find_def_return_type,
  scope_find_def_sig, scope_find_inductive, scope_find_inductive_by_constructor,
  scope_resolve_name, split_qualified_identifier,
}
use lib::typecheck::infer {empty_locals}
use lib::types {
  Class, Identifier, Inductive, ModulePath, NamePath, NameRef, Scope, ScopeDef,
  SourceRange, show_identifier, show_name_path,
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
pub def nav_at (scope : Scope) (ranges : List DeclRange) (cache : ModuleInfoCache)
    (ident : String) : Option NavTarget :=
  let ref : NameRef := NameRef.nid (Identifier.id ident) in
  match scope_resolve_name ref scope empty_locals {
    Result.ok sd => nav_resolved (show_name_path (nav_def_name sd)) sd ranges cache scope,
    // Not resolvable -- so the outline is the only thing left that could
    // know this name. A declaration the file declares but the checker could
    // not resolve is a real state (a typo in a declaration's own
    // annotation is the ordinary way to reach it), and it still has a place
    // to go.
    Result.err _ => nav_unresolved ident ranges scope,
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
    Option.some scope => nav_at scope (ranged_file_ranges f) (ranged_file_cache f) ident,
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
    (cache : ModuleInfoCache) (scope : Scope) : Option NavTarget :=
  match nav_decl_named ranges name {
    Option.some dr => Option.some (nav_local name dr scope),
    Option.none =>
      match nav_of_type name scope ranges {
        Option.some t => Option.some t,
        Option.none =>
          Option.some (nav_def_far name (nav_def_module sd) cache scope),
      },
  }

/// An identifier the scope did not resolve: the outline may still know it,
/// and past that there is nothing to answer with.
#[partial]
def nav_unresolved (ident : String) (ranges : List DeclRange) (scope : Scope) : Option NavTarget :=
  match nav_decl_named ranges ident {
    Option.some dr => Option.some (nav_local ident dr scope),
    Option.none => nav_of_type ident scope ranges,
  }

/// A declaration THIS FILE declares: the kind and the range come from the
/// file's own outline, so the word a user sees is the one their file is
/// written in.
///
/// The detail is composed from that kind rather than from the resolution,
/// which is the fix for the measurement above: a `type` gets
/// `show_inductive`'s rendering of the whole declaration, a `def` gets its
/// signature, and a kind with no printer of its own (`struct`,
/// `instance`, `infix`, ...) gets its name -- honest, since the file is
/// about to show the declaration itself a few lines away.
def nav_local (name : String) (dr : DeclRange) (scope : Scope) : NavTarget :=
  let kind : String := decl_range_kind dr in
  let no_file : Option String := Option.none in
  nav_target_mk name (nav_detail_by_kind name kind scope) kind no_file
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
def nav_detail_by_kind (name : String) (kind : String) (scope : Scope) : String :=
  if String.beq kind "type"
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

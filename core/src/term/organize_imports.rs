//! The `organize-imports` codemod: rewrites bare `use Module`/`open
//! Module` declarations to explicit `use/open Module {name1, name2}`
//! (minimal name list — only what the file actually references). Driven
//! by `cli`'s `organize-imports` subcommand via
//! `compute_organize_import_edits` + `apply_text_edits`; see
//! `core::lib::organize_imports_for_files` for the batch driver.

use super::module::{LoadedModules, Module, collect_referenced_names, referenced_contains_name};
use crate::Set;
use crate::term::{
  Identifier, InductiveVariant, Location, ModulePath, Named, OpenFilter, SourceRange, UseFilter,
};

/// A byte-range-equivalent (line/column, via the existing `SourceRange`
/// type) replacement in a source file.
#[derive(Debug, Clone)]
pub struct TextEdit {
  pub range: SourceRange,
  pub replacement: String,
}

/// Whether `s` could have been written by a user as a source identifier
/// (`(alpha|_) (alphanum|_)*`, matching the parser's own `identifier`
/// rule) — as opposed to a compiler-synthesized name like an anonymous
/// instance's `instance-ClassName-(Arg Type)` (built by the `instance()`
/// constructor's `format!`, and elaborated in among a module's ordinary
/// `defs()` by dictionary-passing lowering). Synthetic names like that
/// can't be written in a `use {...}`/`open {...}` brace list — filtering
/// them out of `exported_bare_names` keeps `organize_imports` from ever
/// emitting invalid syntax.
fn is_valid_identifier(s: &str) -> bool {
  let mut chars = s.chars();
  matches!(chars.next(), Some(c) if c.is_alphabetic() || c == '_')
    && chars.all(|c| c.is_alphanumeric() || c == '_')
}

/// The bare names a module makes available for `use`/`open` to select:
/// top-level def names, inductive/struct/class type names, and (for
/// non-class inductives) their constructors — the same set `open`-ing a
/// module conventionally brings into bare scope. Transitive over `pub
/// use` re-exports (e.g. `init/init.mo`'s `pub use id`/`pub use io`/...),
/// same as the real scope builder's "Include re-exported modules" step in
/// `GlobalScopeData::from_module` — without this, a bare `use init` that
/// really only exists to pull in `init`'s re-exported names (`not`,
/// `unit`, `err`, ...) would minimize down to an empty/wrong brace list.
/// `visited` guards against re-export cycles.
fn exported_bare_names(module: &Module, loaded: &LoadedModules) -> Set<Identifier> {
  let mut names = Set::default();
  let mut visited = Set::default();
  collect_exported_bare_names(module, loaded, &mut names, &mut visited);
  names.retain(|name| is_valid_identifier(name.as_str()));
  names
}

fn collect_exported_bare_names(
  module: &Module,
  loaded: &LoadedModules,
  names: &mut Set<Identifier>,
  visited: &mut Set<ModulePath>,
) {
  if !visited.insert(module.path().clone()) {
    return;
  }
  for ctx in module.defs() {
    names.insert(ctx.value().name.last().clone());
  }
  for ind in module.inductives() {
    names.insert(ind.name.last().clone());
    if ind.variant != InductiveVariant::Class {
      for cons in ind.constructors() {
        names.insert(cons.name().last().clone());
      }
    }
  }
  for reexport in module.get_pub_uses() {
    if let Some(reexported) = loaded.get_module(&reexport.module_path) {
      collect_exported_bare_names(reexported, loaded, names, visited);
    }
  }
}

/// The minimal, sorted set of bare names to write in a `use Module {...}`
/// replacement: every name `target_path` exports that's actually
/// referenced (bare or qualified) somewhere in the importing file, per
/// `collect_referenced_names`. Empty if `target_path` can't be resolved in
/// `loaded` (leaves the caller to fall back to a conservative `{}`) or
/// nothing exported is referenced. `use`'s target is always a real loaded
/// module file — unlike `open` (see `minimal_open_names`), there's no
/// local-type case to fall back to.
fn minimal_use_names(
  target_path: &ModulePath,
  loaded: &LoadedModules,
  referenced: &Set<ModulePath>,
) -> Vec<Identifier> {
  let Some(target) = loaded.get_module(target_path) else {
    return Vec::new();
  };
  select_referenced(exported_bare_names(target, loaded), target_path, referenced)
}

/// Every def/constructor full path reachable from `module`'s perspective:
/// its own defs and inductives (+ constructors), plus the same from every
/// module it `use`s and (transitively, through `pub use`) those modules'
/// re-exports. A simplified stand-in for the real scope builder's
/// "visible modules" set — enough to drive `open`'s prefix matching
/// below without needing the full `GlobalScopeData` machinery.
fn visible_full_paths(module: &Module, loaded: &LoadedModules) -> Vec<ModulePath> {
  let mut paths = Vec::new();
  let mut stack: Vec<ModulePath> = vec![module.path().clone()];
  stack.extend(
    module
      .get_uses()
      .iter()
      .map(|ctx| ctx.value().module_path.clone()),
  );
  // `prelude`/`init` (and, transitively through `init`'s `pub use`, `io`/
  // `math`/`string`/`number`/`id`) are ambiently visible to every file
  // regardless of its own `use` declarations (`GlobalScopeData::
  // from_module`'s "default implicit modules") — an `open SomeType {...}`
  // whose type lives in one of those (e.g. `open IO {println}`, `IO`
  // reached via `init`'s re-export of `io`, with no `use io` anywhere in
  // the file) needs them seeded here too, not just this file's own uses.
  stack.push(ModulePath::top("'prelude"));
  stack.push(ModulePath::top("init"));
  let mut visited: Set<ModulePath> = Set::default();
  while let Some(path) = stack.pop() {
    if !visited.insert(path.clone()) {
      continue;
    }
    let m: &Module = if path == *module.path() {
      module
    } else {
      match loaded.get_module(&path) {
        Some(m) => m,
        None => continue,
      }
    };
    for ctx in m.defs() {
      paths.push(ctx.value().name.clone());
    }
    for ind in m.inductives() {
      paths.push(ind.name.clone());
      if ind.variant != InductiveVariant::Class {
        for cons in ind.constructors() {
          paths.push(cons.name().clone());
        }
      }
    }
    stack.extend(m.get_pub_uses().into_iter().map(|u| u.module_path.clone()));
  }
  paths
}

/// The minimal, sorted set of bare names for an `open Target {...}`
/// replacement. `open`'s target can be either:
/// - A separate loaded module file (`use X` + `open X`) — its top-level
///   defs are already bare-accessible regardless of `open` (see
///   `Module::get_def_refs`'s unconditional own-name `DefRef`), so any of
///   its exported names are safe/correct to list.
/// - (far more common in this codebase — see e.g. `init/prelude.mo`
///   opening `type Bool {...}` right after declaring it, or `Result`/
///   `Option`) a type name whose *constructors and qualified defs*
///   (`Bool.not`, `Bool.and`, ... — not just `Bool`'s constructors
///   `true`/`false`) become bare via `open`'s actual mechanism: every
///   full path with `target_path` as a prefix, suffix taken bare. Scans
///   `module` and everything it transitively makes visible
///   (`visible_full_paths`), so a type opened from a `use`d module (not
///   just one defined locally) is covered too.
fn minimal_open_names(
  target_path: &ModulePath,
  module: &Module,
  loaded: &LoadedModules,
  referenced: &Set<ModulePath>,
) -> Vec<Identifier> {
  let mut names = Set::default();
  if let Some(target) = loaded.get_module(target_path) {
    names.extend(exported_bare_names(target, loaded));
  }
  for full_path in visible_full_paths(module, loaded) {
    if let Some(suffix) = full_path.remove_prefix(target_path)
      && suffix.len() == 1
    {
      names.insert(suffix.last().clone());
    }
  }
  names.retain(|name| is_valid_identifier(name.as_str()));
  select_referenced(names, target_path, referenced)
}

fn select_referenced(
  names: Set<Identifier>,
  target_path: &ModulePath,
  referenced: &Set<ModulePath>,
) -> Vec<Identifier> {
  let mut names: Vec<Identifier> = names
    .into_iter()
    .filter(|name| referenced_contains_name(referenced, target_path, name))
    .collect();
  names.sort_by(|a, b| a.as_str().cmp(b.as_str()));
  names
}

/// Keep generated `use`/`open` lines from growing unreadably wide —
/// modules like `lang.types` export dozens of names, and a single
/// `use lang.types {Con, DebugName, Identifier, ...}` line can run well
/// past 200 characters. Past this width the brace list wraps across
/// multiple lines instead (still valid syntax: whitespace/newlines are
/// unrestricted inside `{...}`).
const MAX_LINE_WIDTH: usize = 80;

/// Render `keyword module_path {names...}`, wrapping the name list across
/// multiple 2-space-indented lines once the compact single-line form
/// would exceed `MAX_LINE_WIDTH`.
fn format_import_decl(keyword: &str, module_path: &ModulePath, names: &[Identifier]) -> String {
  let compact = format!(
    "{keyword} {module_path} {{{}}}",
    names
      .iter()
      .map(|n| n.as_str())
      .collect::<Vec<_>>()
      .join(", ")
  );
  if names.len() <= 1 || compact.len() <= MAX_LINE_WIDTH {
    return compact;
  }

  let mut lines: Vec<String> = Vec::new();
  let mut current = String::new();
  for name in names {
    let piece = name.as_str();
    let sep = if current.is_empty() { "" } else { ", " };
    if !current.is_empty() && current.len() + sep.len() + piece.len() + 1 > MAX_LINE_WIDTH {
      lines.push(current);
      current = String::new();
    }
    current.push_str(if current.is_empty() { "" } else { ", " });
    current.push_str(piece);
  }
  if !current.is_empty() {
    lines.push(current);
  }
  let body: String = lines
    .into_iter()
    .map(|l| format!("  {l},"))
    .collect::<Vec<_>>()
    .join("\n");
  format!("{keyword} {module_path} {{\n{body}\n}}")
}

/// Delete the ENTIRE line `range` starts on — from column 1 through the
/// start of the following line, i.e. including the trailing newline —
/// rather than just the declaration's own span. Used to remove a `use`
/// declaration outright when nothing from it is actually used, instead of
/// leaving a no-op `use X {}` behind.
fn delete_whole_line(range: &SourceRange) -> TextEdit {
  TextEdit {
    range: SourceRange {
      start: Location {
        line: range.start.line,
        column: 1,
      },
      end: Location {
        line: range.start.line + 1,
        column: 1,
      },
      path: range.path.clone(),
    },
    replacement: String::new(),
  }
}

/// Compute every `organize-imports` edit for `module`: bare `use`/`open`
/// declarations rewritten to explicit `{...}` (minimal name list, computed
/// against `loaded`'s already-resolved modules). Pure computation —
/// `apply_text_edits` does the actual splice.
///
/// KNOWN LIMITATION: this computes each `use`/`open`'s minimal name list
/// from what THIS file alone references. For most files that's exactly
/// right, but a small number of modules — `init/prelude.mo` chief among
/// them — have `open`s that are unconditionally chained into every OTHER
/// file's scope too (see `GlobalScopeData::from_module`'s "default
/// implicit modules" handling), so their true minimal set depends on the
/// whole codebase's usage, not just their own. Those need hand-review
/// after running this codemod (see the TODO left in `init/prelude.mo`).
pub fn compute_organize_import_edits(module: &Module, loaded: &LoadedModules) -> Vec<TextEdit> {
  let referenced = collect_referenced_names(module);
  let mut edits = Vec::new();

  for ctx in module.get_uses() {
    let u = ctx.value();
    if u.filter != UseFilter::Bare {
      continue;
    }
    let names = minimal_use_names(&u.module_path, loaded, &referenced);
    if names.is_empty() {
      // Nothing from this module is actually used — delete the whole
      // line (not just rewrite to `use X {}`) rather than leaving a
      // no-op import behind.
      edits.push(delete_whole_line(&u.source_location));
    } else {
      edits.push(TextEdit {
        range: u.source_location.clone(),
        replacement: format_import_decl("use", &u.module_path, &names),
      });
    }
  }

  for ctx in module.get_opens() {
    let o = ctx.value();
    if o.filter != OpenFilter::All {
      continue;
    }
    let names = minimal_open_names(&o.module_path, module, loaded, &referenced);
    edits.push(TextEdit {
      range: o.source_location.clone(),
      replacement: format_import_decl("open", &o.module_path, &names),
    });
  }

  edits
}

/// Byte offset (into `source`) that each line starts at — `offsets[i]` is
/// where line `i + 1` (1-indexed, matching `Location::line`) begins.
/// Assumes `\n` line endings, matching the parser's own position tracking.
fn line_start_byte_offsets(source: &str) -> Vec<usize> {
  let mut offsets = vec![0usize];
  let mut acc = 0;
  for line in source.split_inclusive('\n') {
    acc += line.len();
    offsets.push(acc);
  }
  offsets
}

fn location_to_byte_offset(line_starts: &[usize], loc: &Location) -> usize {
  let line_start = line_starts
    .get((loc.line as usize).saturating_sub(1))
    .copied()
    .unwrap_or(0);
  line_start + loc.column.saturating_sub(1)
}

/// Splice `edits` into `source`, producing the rewritten file text.
/// Non-overlapping edits (guaranteed here — each comes from a distinct
/// `use`/`open`/`Attribute` span) applied from the last byte position
/// backward, so earlier edits' precomputed offsets stay valid as later
/// (higher-offset) ones are spliced in.
pub fn apply_text_edits(source: &str, mut edits: Vec<TextEdit>) -> String {
  let line_starts = line_start_byte_offsets(source);
  edits.sort_by(|a, b| {
    (b.range.start.line, b.range.start.column).cmp(&(a.range.start.line, a.range.start.column))
  });
  let mut result = source.to_string();
  for edit in &edits {
    let start = location_to_byte_offset(&line_starts, &edit.range.start);
    let end = location_to_byte_offset(&line_starts, &edit.range.end);
    if start <= end && end <= result.len() {
      result.replace_range(start..end, &edit.replacement);
    }
  }
  result
}

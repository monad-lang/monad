#!/usr/bin/env python3
"""Style/design metrics over the `.mo` corpus -- the burndown instrument for
plans/implementations/code-style-and-lint-enforcement.md.

READ-ONLY. Emits one counter per line as `key<TAB>value`, plus a human table on
stderr unless --quiet. Every number this plan quotes comes from here, so a claim
in the plan and a claim in CI cannot drift apart.

Detection notes that cost time to get right:

* Single-constructor `type`: the body must be split on TOP-LEVEL commas (outside
  parens) before counting constructors. A per-line scan reports `type NumSuffix
  { i8, i16, ... }` as single-constructor, which it is not.
* Wide positional patterns are only a style violation when the scrutinee has
  NAMED fields -- a `struct` or a single-constructor `type`. AGENTS.md rule 2 is
  explicit that positional destructuring is correct for an ordinary
  multi-constructor sum (`Decl`, `LLVMValue`, `CompileResult`), so those are
  counted separately and are NOT part of the violation total.
* `#[partial]` is a termination-checker escape hatch only
  (rust/core/src/eval/termination.rs:503). "Unneeded" here means "the def does not
  call itself", which over-counts mutual-recursion SCCs; it is a screening
  metric, not the Tier 2 rule (that one re-runs the real checker).
"""

from __future__ import annotations

import argparse
import re
import subprocess
import sys
from collections import Counter
from pathlib import Path

# Directories whose `.mo` files make up the corpus, in the order the sweep uses.
CORPUS_DIRS = [
    "init/src", "std/src", "lang/src", "cli/src", "llvm/src", "runtime/src",
    "build/src",
    "motes", "examples", "slow_tests/src", "bench/src", "proofs/src",
]

# Helpers whose replacement is named in std/src/list.mo's own doc comments
# ("Replaces id_member/ident_in_list/...", "Replaces union_ids/dedup_idents/...").
# Each entry is a def name that should have zero definitions once Phase 8 lands.
NAMED_STD_DUPLICATES = [
    "id_member", "ident_in_list", "list_contains_str", "list_contains_string",
    "str_mem", "list_contains", "list_contains_module_info",
    "union_ids", "dedup_idents", "dedup_strs", "dedup_funcs_by_name",
    "dedup_link_libs", "str_add_uniq", "str_union",
    "str_join", "join_semicolon_msgs", "strs_append",
]

TYPE_DECL_RE = re.compile(r"^\s*(?:pub\s+|priv\s+)?type\s+([A-Za-z_][\w.]*)[^{]*\{\s*$")
STRUCT_DECL_RE = re.compile(r"^\s*(?:pub\s+|priv\s+)?struct\s+([A-Za-z_][\w.]*)[^{]*\{")
DEF_RE = re.compile(r"^\s*(?:pub\s+|priv\s+)?def\s+([A-Za-z_][\w.']*)")
TOP_DECL_RE = re.compile(r"^(?:pub |priv )?(?:def|type|struct|class|instance|use|open|infix|mote)\b")
WIDE_PAT_RE = re.compile(r"([A-Z][\w.]*)\.(?:mk|[a-z_]\w*)((?:\s+(?:_|[a-z_]\w*))+)\s*=>")
PARTIAL_RE = re.compile(r"^\s*#\[partial\]")
ATTR_TEST_RE = re.compile(r"^\s*#\[test\]")


def corpus_files(root: Path) -> list[Path]:
    out: list[Path] = []
    for d in CORPUS_DIRS:
        base = root / d
        if not base.exists():
            continue
        out.extend(sorted(p for p in base.rglob("*.mo") if "target" not in p.parts))
    return out


def strip_line_comment(line: str) -> str:
    """Drop a `//` comment. Not string-aware; only used for structural counting
    where a `//` inside a literal would be a false split, which does not occur
    in the constructs this scans."""
    return line.split("//", 1)[0]


def split_top_level_commas(text: str) -> list[str]:
    parts, cur, depth = [], "", 0
    for ch in text:
        if ch in "([{":
            depth += 1
        elif ch in ")]}":
            depth -= 1
        if ch == "," and depth == 0:
            parts.append(cur)
            cur = ""
        else:
            cur += ch
    parts.append(cur)
    return parts


def decl_body(lines: list[str], start: int) -> list[str]:
    """Lines of a brace-delimited decl body opened on `lines[start]`."""
    depth, body = 1, []
    for line in lines[start + 1:]:
        depth += line.count("{") - line.count("}")
        if depth <= 0:
            break
        body.append(line)
    return body


def analyse(root: Path) -> tuple[dict[str, int], dict[str, Counter]]:
    files = corpus_files(root)
    m: Counter = Counter()
    detail: dict[str, Counter] = {
        "single_ctor_type_by_dir": Counter(),
        "tab_lines_by_dir": Counter(),
        "wide_pattern_by_scrutinee": Counter(),
        "wide_pattern_by_file": Counter(),
        "std_duplicate_defs": Counter(),
    }

    # Pass 1: build the decl index (which type names have named fields), because
    # the wide-pattern rule needs it and it spans files.
    named_field_types: set[str] = set()   # struct, or single-ctor type w/ named params
    unnamed_single_ctor: set[str] = set()
    multi_ctor_types: set[str] = set()

    per_file_lines: dict[Path, list[str]] = {}
    for path in files:
        try:
            lines = path.read_text(encoding="utf-8", errors="replace").split("\n")
        except OSError:
            continue
        per_file_lines[path] = lines
        rel_dir = str(path.parent.relative_to(root))

        for i, line in enumerate(lines):
            ms = STRUCT_DECL_RE.match(line)
            if ms:
                named_field_types.add(ms.group(1).split(".")[-1])
                m["struct_decls"] += 1
                continue
            mt = TYPE_DECL_RE.match(line)
            if not mt:
                continue
            name = mt.group(1)
            body = decl_body(lines, i)
            joined = " ".join(strip_line_comment(b) for b in body)
            ctors = [p.strip() for p in split_top_level_commas(joined)
                     if re.match(r"^[a-z_][\w]*", p.strip())]
            if len(ctors) == 1:
                m["single_ctor_type"] += 1
                detail["single_ctor_type_by_dir"][rel_dir] += 1
                ctor = ctors[0]
                # Three outcomes, and only the first is a `struct` candidate:
                #   named params  -> convertible, and field-patternable TODAY (F1)
                #   positional    -> needs a field name invented first
                #   no params     -> a marker (`Unit { unit }`, `True { trivial }`)
                #                    or a dependent ctor (`Eq { refl : Eq A a a }`);
                #                    a struct with no fields buys nothing
                has_named = re.search(r"\(\s*[a-z_]\w*\s*:", ctor)
                has_any_param = "(" in ctor or ":" in ctor
                if has_named:
                    named_field_types.add(name.split(".")[-1])
                    m["single_ctor_type_convertible"] += 1
                elif has_any_param:
                    unnamed_single_ctor.add(name.split(".")[-1])
                    m["single_ctor_type_unnamed_fields"] += 1
                else:
                    m["single_ctor_type_no_fields"] += 1
            elif len(ctors) > 1:
                m["multi_ctor_type"] += 1
                multi_ctor_types.add(name.split(".")[-1])

    # Pass 2: per-line and per-def metrics.
    for path, lines in per_file_lines.items():
        rel_dir = str(path.parent.relative_to(root))
        in_raw_string = False
        in_test_body = False
        pending_test = False
        has_tab_indent = has_space_indent = False

        for i, line in enumerate(lines):
            if i == len(lines) - 1 and line == "":
                continue  # trailing newline artefact
            m["total_lines"] += 1

            # Raw strings take interior indentation as CONTENT (F4): track them so
            # the indent counters do not blame a fixture's own body.
            opens = line.count('r#"')
            closes = line.count('"#')
            was_raw = in_raw_string
            if not in_raw_string and opens > closes:
                in_raw_string = True
            elif in_raw_string and closes > 0:
                in_raw_string = False
            if was_raw or in_raw_string:
                m["raw_string_lines"] += 1

            stripped = line.strip()
            if stripped == "":
                m["blank_lines"] += 1
            elif stripped.startswith("//"):
                m["comment_lines"] += 1
                if stripped.startswith("///"):
                    m["doc_comment_lines"] += 1

            if not was_raw and not in_raw_string:
                if line.startswith("\t"):
                    m["tab_indent_lines"] += 1
                    detail["tab_lines_by_dir"][rel_dir] += 1
                    has_tab_indent = True
                elif line.startswith(" "):
                    has_space_indent = True
                    indent = len(line) - len(line.lstrip(" "))
                    if indent % 2 == 1:
                        m["odd_indent_lines"] += 1
            if len(line) > 100:
                m["lines_over_100"] += 1
            if len(line) > 120:
                m["lines_over_120"] += 1

            # `#[test]` body extent: the attribute, its `def` line, and that def's
            # body -- ending at the next TOP-LEVEL line. `pending_test` keeps the
            # region open across further attributes (`#[test]` + `#[partial]`) and
            # doc comments between the attribute and the `def` it belongs to, so a
            # helper def AFTER the test is not attributed to it.
            if ATTR_TEST_RE.match(line):
                in_test_body = True
                pending_test = True
            elif in_test_body and stripped and not line.startswith((" ", "\t")):
                if pending_test and (DEF_RE.match(line) or stripped.startswith(("#[", "///", "//"))):
                    if DEF_RE.match(line):
                        pending_test = False  # the test's own def; body follows
                else:
                    in_test_body = False
            if in_test_body:
                m["test_body_lines"] += 1

            # Wide positional patterns.
            for wm in WIDE_PAT_RE.finditer(line):
                binders = wm.group(2).split()
                if len(binders) < 4:
                    continue
                scrutinee = wm.group(1).split(".")[-1]
                m["wide_positional_pattern_total"] += 1
                detail["wide_pattern_by_scrutinee"][scrutinee] += 1
                if scrutinee in named_field_types:
                    m["wide_positional_pattern_violation"] += 1
                    detail["wide_pattern_by_file"][str(path.relative_to(root))] += 1
                elif scrutinee in multi_ctor_types:
                    m["wide_positional_pattern_multi_ctor_ok"] += 1
                else:
                    m["wide_positional_pattern_unresolved"] += 1
                if binders.count("_") >= 2:
                    m["wide_positional_pattern_2plus_wildcards"] += 1

            if PARTIAL_RE.match(line):
                m["partial_attrs"] += 1
                # Screening check: does the next def call itself?
                for j in range(i + 1, min(i + 4, len(lines))):
                    dm = DEF_RE.match(lines[j])
                    if not dm:
                        continue
                    name = dm.group(1).split(".")[-1]
                    body_txt = []
                    for k in range(j + 1, len(lines)):
                        if TOP_DECL_RE.match(lines[k]) and not lines[k].startswith((" ", "\t")):
                            break
                        body_txt.append(lines[k])
                    if not re.search(r"\b" + re.escape(name) + r"\b", " ".join(body_txt)):
                        m["partial_attr_no_self_call"] += 1
                    break

            if "List.cons" in line:
                m["list_cons_sites"] += 1
                if "List.empty" in line:
                    m["list_cons_terminated_lines"] += 1
                    depth = line.count("List.cons")
                    if depth >= 2:
                        m["list_cons_chain_depth2plus"] += 1
                    if depth >= 3:
                        m["list_cons_chain_depth3plus"] += 1

            dm = DEF_RE.match(line)
            if dm:
                m["total_defs"] += 1
                if dm.group(1).split(".")[-1] in NAMED_STD_DUPLICATES:
                    m["std_duplicate_defs"] += 1
                    detail["std_duplicate_defs"][
                        f"{dm.group(1)} @ {path.relative_to(root)}:{i + 1}"
                    ] += 1

        if has_tab_indent:
            m["files_with_tab_indent"] += 1
            if has_space_indent:
                m["files_mixing_tabs_and_spaces"] += 1

    m["mo_files"] = len(per_file_lines)
    m["production_lines"] = (
        m["total_lines"] - m["comment_lines"] - m["blank_lines"] - m["test_body_lines"]
    )
    return dict(m), detail


def git_head(root: Path) -> str:
    try:
        return subprocess.run(
            ["git", "-C", str(root), "rev-parse", "--short", "HEAD"],
            capture_output=True, text=True, check=True).stdout.strip()
    except (OSError, subprocess.CalledProcessError):
        return "unknown"


KEY_ORDER = [
    "mo_files", "total_lines", "production_lines", "comment_lines",
    "doc_comment_lines", "blank_lines", "test_body_lines", "total_defs",
    "single_ctor_type", "single_ctor_type_convertible",
    "single_ctor_type_unnamed_fields", "single_ctor_type_no_fields", "multi_ctor_type",
    "struct_decls",
    "wide_positional_pattern_violation", "wide_positional_pattern_total",
    "wide_positional_pattern_multi_ctor_ok", "wide_positional_pattern_unresolved",
    "wide_positional_pattern_2plus_wildcards",
    "tab_indent_lines", "files_with_tab_indent", "files_mixing_tabs_and_spaces",
    "odd_indent_lines", "lines_over_100", "lines_over_120", "raw_string_lines",
    "std_duplicate_defs", "partial_attrs", "partial_attr_no_self_call",
    "list_cons_sites", "list_cons_terminated_lines",
    "list_cons_chain_depth2plus", "list_cons_chain_depth3plus",
]

# Counters that must never rise. Anything not listed is informational.
RATCHETED = {
    "single_ctor_type_convertible", "wide_positional_pattern_violation",
    "wide_positional_pattern_2plus_wildcards", "tab_indent_lines",
    "files_with_tab_indent", "files_mixing_tabs_and_spaces", "odd_indent_lines",
    "lines_over_120", "std_duplicate_defs", "partial_attr_no_self_call",
}


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--root", default=".", help="repo root (default: cwd)")
    ap.add_argument("--baseline", metavar="FILE",
                    help="compare against FILE; exit 1 if any ratcheted counter rose")
    ap.add_argument("--write-baseline", metavar="FILE",
                    help="write the current counters to FILE")
    ap.add_argument("--detail", action="store_true",
                    help="also print per-dir / per-file / per-scrutinee breakdowns")
    ap.add_argument("--quiet", action="store_true", help="key<TAB>value only")
    args = ap.parse_args()

    root = Path(args.root).resolve()
    metrics, detail = analyse(root)

    for key in KEY_ORDER:
        print(f"{key}\t{metrics.get(key, 0)}")

    if not args.quiet:
        head = git_head(root)
        print(f"\n  corpus @ {head}: {metrics['mo_files']} .mo files, "
              f"{metrics['total_lines']} lines "
              f"({metrics['production_lines']} production, "
              f"{metrics['comment_lines']} comment, "
              f"{metrics['test_body_lines']} test, {metrics['blank_lines']} blank)",
              file=sys.stderr)
        print(f"  single-ctor `type`: {metrics['single_ctor_type']} total -- "
              f"{metrics.get('single_ctor_type_convertible', 0)} convertible, "
              f"{metrics.get('single_ctor_type_unnamed_fields', 0)} unnamed fields, "
              f"{metrics.get('single_ctor_type_no_fields', 0)} field-less markers",
              file=sys.stderr)
        print(f"  wide positional patterns: "
              f"{metrics.get('wide_positional_pattern_violation', 0)} violations / "
              f"{metrics['wide_positional_pattern_total']} total "
              f"({metrics.get('wide_positional_pattern_multi_ctor_ok', 0)} on multi-ctor "
              f"sums = correct, {metrics.get('wide_positional_pattern_unresolved', 0)} "
              f"unresolved)", file=sys.stderr)
        print(f"  indent: {metrics['tab_indent_lines']} tab lines in "
              f"{metrics['files_with_tab_indent']} files "
              f"({metrics['files_mixing_tabs_and_spaces']} mixing tabs+spaces), "
              f"{metrics['odd_indent_lines']} odd-indent", file=sys.stderr)
        print(f"  std duplicates still defined: {metrics.get('std_duplicate_defs', 0)}",
              file=sys.stderr)
        print(f"  #[partial]: {metrics['partial_attrs']} total, "
              f"{metrics.get('partial_attr_no_self_call', 0)} with no self-call",
              file=sys.stderr)

    if args.detail:
        for name, counter in detail.items():
            print(f"\n# {name}", file=sys.stderr)
            for k, v in counter.most_common(30):
                print(f"  {v:5d}  {k}", file=sys.stderr)

    if args.write_baseline:
        with open(args.write_baseline, "w", encoding="utf-8") as fh:
            fh.write(f"# style baseline @ {git_head(root)} -- "
                     f"regenerate with scripts/style-metrics.sh --write-baseline\n")
            for key in KEY_ORDER:
                fh.write(f"{key}\t{metrics.get(key, 0)}\n")
        print(f"wrote {args.write_baseline}", file=sys.stderr)

    if args.baseline:
        base: dict[str, int] = {}
        with open(args.baseline, encoding="utf-8") as fh:
            for line in fh:
                if line.startswith("#") or "\t" not in line:
                    continue
                k, v = line.rstrip("\n").split("\t", 1)
                base[k] = int(v)
        # A ratcheted counter the baseline does not carry is a hole, not a
        # pass: the regression test below reads `base[k]`, so skipping it
        # silently is how a truncated (or stale, hand-edited, half-written)
        # baseline reports "style ratchet ok" while gating nothing at all.
        # `--write-baseline` always writes every `KEY_ORDER` key, so a full
        # baseline can never hit this.
        missing = sorted(k for k in RATCHETED if k not in base)
        if missing:
            print("\nstyle ratchet FAILED -- the baseline has no entry for "
                  "these ratcheted counters:", file=sys.stderr)
            for k in missing:
                print(f"  {k}", file=sys.stderr)
            print(f"  ({args.baseline} is incomplete or truncated; regenerate "
                  f"it with scripts/style-metrics.sh --write-baseline)",
                  file=sys.stderr)
            return 1
        regressions = [
            (k, base[k], metrics.get(k, 0))
            for k in RATCHETED
            if metrics.get(k, 0) > base[k]
        ]
        if regressions:
            print("\nstyle ratchet FAILED -- these counters rose:", file=sys.stderr)
            for k, was, now in sorted(regressions):
                print(f"  {k}: {was} -> {now}  (+{now - was})", file=sys.stderr)
            return 1
        improved = sum(1 for k in RATCHETED
                       if metrics.get(k, 0) < base[k])
        print(f"\nstyle ratchet ok ({improved} counter(s) improved)", file=sys.stderr)
    return 0


if __name__ == "__main__":
    sys.exit(main())

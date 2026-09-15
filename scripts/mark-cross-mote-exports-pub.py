#!/usr/bin/env python3
"""Mark every declaration another mote imports as `pub`.

The corpus already says which names cross a mote boundary: nearly every
`use` line lists its names explicitly. This reads those filters and marks
the matching declarations `pub` in the mote that owns them.

  use std::list {intercalate}   in lang/...  ->  `pub def List.intercalate`
                                                 in std/src/list.mo

A cross-mote `{*}` marks that module's whole top level, since a glob
imports all of it. Same-mote imports (`use lib::...`) are ignored -- they
cross no boundary.

Run from the repo root:  scripts/mark-cross-mote-exports-pub.py
"""

import re
import subprocess
import sys
from collections import defaultdict
from pathlib import Path

USE_LINE = re.compile(r"^\s*(?:pub\s+)?use\s+([A-Za-z_][\w:']*)\s*(\{.*)?$", re.S)
DECL = re.compile(
    r"^(?P<vis>pub |priv )?(?P<kw>def|type|struct|class|instance|infix)\b(?P<rest>.*)$"
)
# Module names that are not motes: `io`/`prelude` are modules OF the init
# mote, and `lib` is the mote's reference to itself. `init` and `std` are
# real motes, so their cross-mote exports do need marking.
AMBIENT = {"prelude", "io", "lib"}


def mote_of(path: Path) -> str | None:
    parts = path.parts
    for i, part in enumerate(parts[:-1]):
        if parts[i + 1] == "src":
            return part
    return None


def use_blocks(text: str) -> list[tuple[str, str]]:
    """(mote, filter body) for every use line, filters possibly multi-line."""
    out = []
    lines = text.split("\n")
    i = 0
    while i < len(lines):
        m = re.match(r"^\s*(?:pub\s+)?use\s+([A-Za-z_][\w:']*)\s*(.*)$", lines[i])
        if m:
            head = m.group(1).split("::")[0]
            body = m.group(2)
            while "{" in body and "}" not in body and i + 1 < len(lines):
                i += 1
                body += " " + lines[i]
            out.append((head, body))
        i += 1
    return out


def declared_name(rest: str) -> str | None:
    """The name a declaration introduces, as written."""
    m = re.match(r"\s+([A-Za-z_][\w.']*)", rest)
    return m.group(1) if m else None


def introduced_names(lines: list[str], i: int, kw: str) -> set[str]:
    """The names a declaration BLOCK introduces besides its own.

    Visibility is declared on the type, never per constructor, so a
    cross-mote import of a CONSTRUCTOR (`use llvm::ir {mk}`) is satisfied
    by marking the type that declares it. A struct's constructor is the
    implicit `mk`.
    """
    if kw == "struct":
        return {"mk"}
    if kw in ("instance", "class"):
        # Method visibility is the instance's / class's own, so a
        # cross-mote import of a method name is satisfied by marking the
        # block that defines it.
        names: set[str] = set()
        depth = 0
        started = False
        for line in lines[i:]:
            depth += line.count("{") - line.count("}")
            started = started or "{" in line
            m = re.match(r"\s+(?:pub |priv )?def\s+([A-Za-z_][\w.']*)", line)
            if m:
                names.add(m.group(1))
                names.add(m.group(1).split(".")[-1])
            if started and depth <= 0:
                break
        return names
    if kw != "type":
        return set()
    names: set[str] = set()
    depth = 0
    for line in lines[i:]:
        depth += line.count("{") - line.count("}")
        m = re.match(r"\s+([a-z_][\w']*)\s*[({,]|\s+([a-z_][\w']*)\s*$", line)
        if m:
            names.add(m.group(1) or m.group(2))
        if depth <= 0 and "{" in "".join(lines[i : i + 1]) or depth < 0:
            if depth <= 0:
                break
    return names


def main() -> int:
    files = [
        Path(f)
        for f in subprocess.run(
            ["git", "ls-files", "*.mo"], capture_output=True, text=True, check=True
        ).stdout.split()
    ]

    # mote -> set of names imported from it by OTHER motes
    wanted: dict[str, set[str]] = defaultdict(set)
    glob_motes: set[str] = set()
    for f in files:
        here = mote_of(f)
        for target, body in use_blocks(f.read_text()):
            if target in AMBIENT or target == here or here is None:
                continue
            if "{*}" in body:
                glob_motes.add(target)
                continue
            names = re.findall(r"[A-Za-z_][\w.']*", body)
            wanted[target].update(names)

    marked = 0
    touched = 0
    for f in files:
        here = mote_of(f)
        if here is None:
            continue
        names = wanted.get(here, set())
        mark_all = here in glob_motes
        if not names and not mark_all:
            continue
        lines = f.read_text().split("\n")
        changed = False
        for i, line in enumerate(lines):
            m = DECL.match(line)
            if not m or m.group("vis"):
                continue
            name = declared_name(m.group("rest"))
            if name is None:
                continue
            # A dotted name is exported under its last segment too
            # (`String.concat_all` is imported as `concat_all`).
            bare = name.split(".")[-1]
            ctors = introduced_names(lines, i, m.group("kw"))
            if mark_all or name in names or bare in names or (ctors & names):
                lines[i] = "pub " + line
                changed = True
                marked += 1
        if changed:
            f.write_text("\n".join(lines))
            touched += 1
    print(f"marked {marked} declaration(s) pub across {touched} file(s)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

#!/usr/bin/env python3
"""Rewrite `use` paths to `::`, and intra-mote paths to `lib::`.

Two rewrites, both confined to the PATH portion of a line whose first
token is `use` (or `pub use`) -- from just after the keyword up to the
first `{`, the end of the line, or a `//` comment. Expression dots, dotted
def names, `open` paths, comments and strings are never touched, because
the anchor is the line-start keyword.

  1. `use lang.codegen.emit {..}`  ->  `use lang::codegen::emit {..}`
  2. inside mote `lang`:
     `use lang::codegen::emit {..}` ->  `use lib::codegen::emit {..}`

The second makes a mote name in a `use` line always mean a real
cross-mote edge. Which mote a file belongs to is decided by the file's
own path (`<mote>/src/...`), so the rewrite is purely local.

Usage: scripts/migrate-use-separator.py <file>...
"""

import re
import sys
from pathlib import Path

USE_LINE = re.compile(r"^(\s*)((?:pub\s+)?use\s+)(.*)$")
SEGMENT_JOIN = re.compile(r"\s*\.\s*(?=[A-Za-z_'])")


def mote_of(path: Path) -> str | None:
    """The mote a file belongs to: `<mote>/src/...` relative to the repo."""
    parts = path.parts
    for i, part in enumerate(parts[:-1]):
        if parts[i + 1] == "src":
            return part
    return None


def split_path_portion(rest: str) -> tuple[str, str]:
    """Split a use line's tail into (path portion, everything after)."""
    end = len(rest)
    for marker in ("{", "//"):
        found = rest.find(marker)
        if found != -1:
            end = min(end, found)
    return rest[:end], rest[end:]


def rewrite_line(line: str, mote: str | None) -> str:
    m = USE_LINE.match(line)
    if not m:
        return line
    indent, keyword, rest = m.groups()
    path, tail = split_path_portion(rest)
    stripped = path.strip()
    if not stripped:
        return line
    new_path = SEGMENT_JOIN.sub("::", stripped)
    if mote and (new_path == mote or new_path.startswith(mote + "::")):
        new_path = "lib" + new_path[len(mote):]
    trailing = path[len(path.rstrip()):]
    return f"{indent}{keyword}{new_path}{trailing}{tail}"


def main(argv: list[str]) -> int:
    changed = 0
    for name in argv:
        path = Path(name)
        mote = mote_of(path)
        text = path.read_text()
        lines = text.split("\n")
        new_lines = [rewrite_line(line, mote) for line in lines]
        if new_lines != lines:
            path.write_text("\n".join(new_lines))
            changed += 1
            print(f"{path}: {sum(a != b for a, b in zip(lines, new_lines))} use line(s)")
    print(f"{changed} file(s) rewritten")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))

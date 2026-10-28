#!/usr/bin/env python3
"""Split the vendored CommonMark fixture into parts the compiled backend can read.

    python3 -I tools/split_fixture.py testdata/commonmark-0.31.2.spec.json

The self-hosted compiled backend's `IO.read_file` fails on any file over
64 KiB (the second 64 KiB read returns an error; see
plans/implementations/compiled-read-file-second-chunk.md). The harness
therefore reads the fixture as three parts, each under 65,536 bytes,
concatenating them in memory before parsing. The split is at line
boundaries, so every part is valid UTF-8 and the concatenation is
byte-identical to the input.
"""
import hashlib
import sys
from pathlib import Path

LIMIT = 60000
PARTS = 3


def main() -> int:
    if len(sys.argv) != 2:
        print(__doc__, file=sys.stderr)
        return 2
    src = Path(sys.argv[1])
    data = src.read_bytes()
    lines = data.splitlines(keepends=True)
    target = (len(data) + PARTS - 1) // PARTS
    chunks = [[]]
    size = 0
    for line in lines:
        if size >= target and len(chunks) < PARTS:
            chunks.append([])
            size = 0
        chunks[-1].append(line)
        size += len(line)
    if len(chunks) != PARTS:
        print("could not split into %d parts" % PARTS, file=sys.stderr)
        return 1
    for i, chunk in enumerate(chunks, start=1):
        blob = b"".join(chunk)
        if len(blob) >= 65536:
            print("part %d is %d bytes, over the 64 KiB read limit" % (i, len(blob)), file=sys.stderr)
            return 1
        out = src.with_name("%s.part%d.json" % (src.name.split(".spec")[0], i))
        out.write_bytes(blob)
        print("wrote %s (%d bytes)" % (out, len(blob)))
    joined = b"".join(c for c in (b"".join(ch) for ch in chunks))
    if joined != data:
        print("split is not lossless", file=sys.stderr)
        return 1
    print("sha256(input) = %s" % hashlib.sha256(data).hexdigest())
    return 0


if __name__ == "__main__":
    sys.exit(main())

#!/usr/bin/env python3
"""Generate motes/markdown/src/unicode.mo from the Unicode character database.

    python3 -I tools/gen_unicode.py --unicode-data UnicodeData.txt \
        --case-folding CaseFolding.txt --out src/unicode.mo

Inputs:
  https://www.unicode.org/Public/15.1.0/ucd/UnicodeData.txt
  https://www.unicode.org/Public/15.1.0/ucd/CaseFolding.txt

Emits whitespace and punctuation classifiers as range staircases, and the
full case folding (statuses C and F) as a codepoint table plus a string
folder. The generated file is committed.
"""
import argparse
import hashlib
import sys

UD_URL = "https://www.unicode.org/Public/15.1.0/ucd/UnicodeData.txt"
CF_URL = "https://www.unicode.org/Public/15.1.0/ucd/CaseFolding.txt"


def monad_string(value: str) -> str:
    out = []
    for ch in value:
        if ch == "\\":
            out.append("\\\\")
        elif ch == '"':
            out.append('\\"')
        elif ord(ch) < 0x20:
            out.append("\\u{%x}" % ord(ch))
        else:
            out.append(ch)
    return '"' + "".join(out) + '"'


def merge_ranges(points):
    ranges = []
    for cp in sorted(points):
        if ranges and cp == ranges[-1][1] + 1:
            ranges[-1][1] = cp
        else:
            ranges.append([cp, cp])
    return ranges


def parse_categories(path):
    cats = {}
    first = None
    for line in open(path, encoding="utf-8"):
        fields = line.rstrip("\n").split(";")
        if len(fields) < 3:
            continue
        cp = int(fields[0], 16)
        name = fields[1]
        cat = fields[2]
        if name.endswith(", First>"):
            first = (cp, cat)
        elif name.endswith(", Last>") and first:
            for c in range(first[0], cp + 1):
                cats[c] = first[1]
            first = None
        else:
            cats[cp] = cat
    return cats


def parse_folding(path):
    folding = {}
    for line in open(path, encoding="utf-8"):
        line = line.split("#", 1)[0].strip()
        if not line:
            continue
        fields = [f.strip() for f in line.split(";")]
        if len(fields) < 3:
            continue
        cp = int(fields[0], 16)
        status = fields[1]
        if status not in ("C", "F"):
            continue
        mapping = fields[2]
        chars = "".join(chr(int(c, 16)) for c in mapping.split())
        folding[cp] = chars
    return folding


def _tree(rs):
    """Balanced split of sorted ranges: (lo, hi, left, right) or None."""
    if not rs:
        return None
    if len(rs) == 1:
        return ("leaf", rs[0][0], rs[0][1], None, None)
    mid = len(rs) // 2
    left = _tree(rs[:mid])
    right = _tree(rs[mid:])
    return ("node", rs[mid][0], 0, left, right)


def _flatten(tree, nodes):
    """Post-order ids for a tree, returning the id of this node."""
    if tree is None:
        return None
    kind = tree[0]
    lid = _flatten(tree[3], nodes) if len(tree) > 3 else None
    rid = _flatten(tree[4], nodes) if len(tree) > 4 else None
    idx = len(nodes)
    nodes.append((tree, lid, rid))
    return idx


def emit_range_fn(name, ranges, doc):
    """Balanced decision tree: one function per node, depth ~log2(ranges).

    A linear `else if` chain would nest the expression once per range, and the
    Rust host elaborates that recursion on the stack -- a 339-range chain
    overflowed the 8 MB stack in CI when the whole corpus was checked.
    """
    tree = _tree(ranges)
    lines = ["/// %s" % doc]
    if tree is None:
        lines.append("pub def %s (cp : U32) : Bool :=" % name)
        lines.append("    false")
        return lines
    nodes = []
    root = _flatten(tree, nodes)
    for idx, (spec, lid, rid) in enumerate(nodes):
        lines.append("#[partial]")
        lines.append("def %s_%d (cp : U32) : Bool :=" % (name, idx))
        if spec[0] == "leaf":
            lo, hi = spec[1], spec[2]
            if lo == hi:
                lines.append("    U32.beq cp %du32" % lo)
            else:
                lines.append("    if U32.lt %du32 cp then U32.lt cp %du32 else false" % (lo - 1, hi + 1))
            continue
        pivot = spec[1]
        left = ("%s_%d cp" % (name, lid)) if lid is not None else "false"
        right = ("%s_%d cp" % (name, rid)) if rid is not None else "false"
        lines.append("    if U32.lt cp %du32 then %s else %s" % (pivot, left, right))
    lines.append("")
    lines.append("pub def %s (cp : U32) : Bool := %s_%d cp" % (name, name, root))
    return lines


def emit_fold_fn(name, folding):
    """Balanced tree over the folding table, one function per node."""
    entries = sorted(folding.items())
    tree = _tree_entries(entries)
    nodes = []
    root = _flatten_entries(tree, nodes)
    lines = []
    lines.append("/// The full case folding of one codepoint (statuses C and F), or none.")
    for idx, (spec, lid, rid) in enumerate(nodes):
        lines.append("#[partial]")
        lines.append("def %s_%d (cp : U32) : Option String :=" % (name, idx))
        if spec[0] == "entry":
            lines.append("    if U32.beq cp %du32 then Option.some %s else %s"
                         % (spec[1], monad_string(spec[2]), _child(name, "Option.none", spec[3], spec[4])))
            continue
        pivot = spec[1]
        left = _child(name, "Option.none", lid, None)
        right = _child(name, "Option.none", rid, None)
        lines.append("    if U32.lt cp %du32 then %s else %s" % (pivot, left, right))
    lines.append("")
    lines.append("pub def %s (cp : U32) : Option String := %s_%d cp" % (name, name, root))
    return lines


def _child(name, fallback, idx, _unused):
    return ("%s_%d cp" % (name, idx)) if idx is not None else fallback


def _tree_entries(entries):
    if not entries:
        return None
    if len(entries) == 1:
        return ("entry", entries[0][0], entries[0][1], None, None)
    mid = len(entries) // 2
    return ("node", entries[mid][0], None, _tree_entries(entries[:mid]), _tree_entries(entries[mid:]))


def _flatten_entries(tree, nodes):
    if tree is None:
        return None
    lid = _flatten_entries(tree[3], nodes)
    rid = _flatten_entries(tree[4], nodes)
    idx = len(nodes)
    nodes.append((tree, lid, rid))
    return idx


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--unicode-data", required=True)
    ap.add_argument("--case-folding", required=True)
    ap.add_argument("--out", required=True)
    args = ap.parse_args()

    ud_raw = open(args.unicode_data, "rb").read()
    cf_raw = open(args.case_folding, "rb").read()
    cats = parse_categories(args.unicode_data)
    folding = parse_folding(args.case_folding)

    ws = set([0x09, 0x0A, 0x0C, 0x0D, 0x20])
    punct = set()
    for cp, cat in cats.items():
        if cat == "Zs":
            ws.add(cp)
        elif cat.startswith("P") or cat.startswith("S"):
            punct.add(cp)

    lines = []
    lines.append("// AUTO-GENERATED by tools/gen_unicode.py -- do not edit.")
    lines.append("//")
    lines.append("// UnicodeData: %s" % UD_URL)
    lines.append("// sha256 = %s" % hashlib.sha256(ud_raw).hexdigest())
    lines.append("// CaseFolding: %s" % CF_URL)
    lines.append("// sha256 = %s" % hashlib.sha256(cf_raw).hexdigest())
    lines.append("//")
    lines.append("// Ranges are emitted as comparison staircases: the caller classifies a")
    lines.append("// codepoint a handful of times per document, so a linear walk costs")
    lines.append("// nothing next to the allocation a table lookup would need.")
    lines.append("use init::string {}")
    lines.append("use parsec::core {is_empty}")
    lines.append("use lib::scan {Markdown.char_width, Markdown.codepoint_at}")
    lines.append("")
    lines.extend(emit_range_fn("Markdown.is_unicode_whitespace", merge_ranges(ws),
                               "Unicode whitespace: category Zs plus tab, LF, FF, CR, space."))
    lines.append("")
    lines.extend(emit_range_fn("Markdown.is_unicode_punctuation", merge_ranges(punct),
                               "Unicode punctuation: categories P and S, matching what\n/// cmark treats as punctuation for emphasis flanking."))
    lines.append("")
    lines.extend(emit_fold_fn("Markdown.case_fold_cp", folding))
    lines.append("")
    lines.append("/// Case-fold a string for reference-label comparison.")
    lines.append("#[partial]")
    lines.append("pub def Markdown.case_fold (s : String) : String :=")
    lines.append("    String.concat_list (List.reverse (Markdown.case_fold_go s List.empty))")
    lines.append("")
    lines.append("#[partial]")
    lines.append("def Markdown.case_fold_go (s : String) (acc : List String) : List String :=")
    lines.append("    if is_empty s")
    lines.append("    then acc")
    lines.append("    else")
    lines.append("        match Markdown.codepoint_at s {")
    lines.append("            Option.none => acc,")
    lines.append("            Option.some cp =>")
    lines.append("                match Markdown.case_fold_cp cp {")
    lines.append("                    Option.some folded =>")
    lines.append("                        Markdown.case_fold_go (String.drop (Markdown.char_width s) s)")
    lines.append("                            (List.cons folded acc),")
    lines.append("                    Option.none =>")
    lines.append("                        Markdown.case_fold_go (String.drop (Markdown.char_width s) s)")
    lines.append("                            (List.cons (String.slice s 0 (Markdown.char_width s)) acc)")
    lines.append("                }")
    lines.append("        }")

    with open(args.out, "w") as f:
        f.write("\n".join(lines) + "\n")
    print("wrote %s: %d folding entries, %d whitespace ranges, %d punctuation ranges"
          % (args.out, len(folding), len(merge_ranges(ws)), len(merge_ranges(punct))))
    return 0


if __name__ == "__main__":
    sys.exit(main())

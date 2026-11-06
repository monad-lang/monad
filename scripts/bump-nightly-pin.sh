#!/usr/bin/env bash
# Move the nightly pin in nix/nightly.nix to the newest published nightly.
#
# The pin is the host of the release's rung 1 (nix/monad.nix's
# `nightlyRung1`), so a pin older than a construct the compiler-source
# surface uses fails every nightly at rung 1 with the host's own
# unknown-construct error. This script makes adopting a new nightly
# mechanical: it reads the newest `nightly-*` release from the releases API,
# fetches each pinned platform's `<asset>.sha256`, and rewrites exactly the
# `tag`, `url`, checksum comment and `sha256` lines of every pin entry.
#
# Usage:
#   scripts/bump-nightly-pin.sh              # adopt the newest nightly
#   scripts/bump-nightly-pin.sh --check      # exit 1 if the pin is behind
#   scripts/bump-nightly-pin.sh --dry-run    # print the bump, write nothing
#   scripts/bump-nightly-pin.sh --tag TAG    # adopt a specific release
#
# It needs `curl` and `python3` (the JSON pick, the hex->SRI conversion and
# the rewrite), so run it inside the dev shell --
# `nix develop -c scripts/bump-nightly-pin.sh`, or
# `devenv tasks run monad:bump-nightly`. The scheduled `Bump nightly pin`
# workflow does the same and opens a PR.
#
# A bump changes only nix/nightly.nix, and nightly.yml ignores a push whose
# ONLY change is that file -- so merging a bump publishes no new nightly for
# the next run to adopt. Without that filter every bump would beget a nightly,
# which the next bump would adopt, forever.
#
# Overrides exist for scripts/check-nightly-pin.sh's hermetic fixtures:
#   MONAD_NIGHTLY_PIN_FILE        the nix file to rewrite
#   MONAD_NIGHTLY_API_URL         the releases API endpoint (`file://` works)
#   MONAD_NIGHTLY_DOWNLOAD_BASE   where `<base>/<tag>/monad-nightly-<plat>.sha256` lives
set -euo pipefail

root="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
pin_file="${MONAD_NIGHTLY_PIN_FILE:-$root/nix/nightly.nix}"
api_url="${MONAD_NIGHTLY_API_URL:-https://api.github.com/repos/monad-lang/monad/releases}"
download_base="${MONAD_NIGHTLY_DOWNLOAD_BASE:-https://github.com/monad-lang/monad/releases/download}"

say() { printf 'bump-nightly-pin: %s\n' "$*" >&2; }
die() { printf 'bump-nightly-pin: error: %s\n' "$*" >&2; exit 1; }

mode=apply
tag_override=""
while [ $# -gt 0 ]; do
  case "$1" in
    --check) mode=check; shift ;;
    --dry-run) mode=dry-run; shift ;;
    --tag)
      [ $# -ge 2 ] || die "--tag needs a value"
      tag_override="$2"
      shift 2
      ;;
    --tag=*)
      tag_override="${1#--tag=}"
      shift
      ;;
    -h | --help)
      sed -n '2,/^set -euo pipefail$/p' "${BASH_SOURCE[0]}" | sed '$d' | sed 's/^# \{0,1\}//'
      exit 0
      ;;
    *) die "unknown argument '$1' (see --help)" ;;
  esac
done

command -v curl >/dev/null 2>&1 || die "curl is required (run inside 'nix develop')"
command -v python3 >/dev/null 2>&1 || die "python3 is required (run inside 'nix develop')"
[ -f "$pin_file" ] || die "no pin file at $pin_file"

# One "<platform><TAB><current tag>" line per pin entry. The block is found by
# scanning UP from its `tag =` line to the nearest `<name> = {` with less
# indentation, which skips the enclosing `pins = {` and does not assume the
# platform set.
current="$(python3 -I - "$pin_file" <<'PY'
import re
import sys

lines = open(sys.argv[1], encoding="utf-8").read().splitlines()
for i, line in enumerate(lines):
    m = re.match(r'^(\s*)tag = "([^"]*)";\s*$', line)
    if not m:
        continue
    indent = m.group(1)
    for j in range(i - 1, -1, -1):
        opening = re.match(r'^(\s*)([A-Za-z0-9_.-]+) = \{\s*$', lines[j])
        if opening and len(opening.group(1)) < len(indent):
            print(opening.group(2) + "\t" + m.group(2))
            break
PY
)" || die "could not read the pin entries from $pin_file"
[ -n "$current" ] || die "found no pin entries in $pin_file"

if [ -n "$tag_override" ]; then
  tag="$tag_override"
else
  json="$(curl -fsSL "$api_url")" || die "failed to query the releases API ($api_url)"
  tag="$(printf '%s' "$json" | python3 -I -c '
import json
import sys

for release in json.load(sys.stdin):
    name = release.get("tag_name", "")
    if name.startswith("nightly-"):
        print(name)
        break
')" || die "could not parse the releases API response"
  [ -n "$tag" ] || die "no nightly-* release found"
fi
[[ "$tag" =~ ^nightly-[0-9A-Za-z._-]+$ ]] || die "unexpected nightly tag '$tag'"

stale="$(printf '%s\n' "$current" | awk -F'\t' -v tag="$tag" '$2 != tag { print $1 }')"
if [ -z "$stale" ]; then
  say "already at $tag"
  exit 0
fi
if [ "$mode" = check ]; then
  say "the pin is behind $tag: $(printf '%s' "$stale" | tr '\n' ' ')"
  say "run scripts/bump-nightly-pin.sh (or 'devenv tasks run monad:bump-nightly') to update it"
  exit 1
fi

# Fetch every stale platform's published checksum before touching the file, so
# a missing or malformed asset fails with the pin untouched.
work="$(mktemp -d "${TMPDIR:-/tmp}/monad-bump-nightly.XXXXXX")"
tmp=""
cleanup() {
  rm -rf "$work"
  if [ -n "$tmp" ]; then rm -f "$tmp"; fi
  return 0
}
trap cleanup EXIT
updates="$work/updates"
: > "$updates"
for plat in $stale; do
  [[ "$plat" =~ ^[0-9A-Za-z_.-]+$ ]] || die "unexpected platform '$plat' in $pin_file"
  url="$download_base/$tag/monad-nightly-$plat"
  sums="$(curl -fsSL "$url.sha256")" || die "no checksum at $url.sha256 (is the asset published yet?)"
  hex="${sums%%[[:space:]]*}"
  [[ "$hex" =~ ^[0-9a-f]{64}$ ]] || die "$url.sha256 does not hold a sha256 hex digest: '$sums'"
  printf '%s\t%s\t%s\n' "$plat" "$hex" "$url" >> "$updates"
done

# Rewrite in place on a private copy beside the pin, then rename it over the
# original: a failed run leaves the pin exactly as it was, and the copy keeps
# the file's mode (`cp -p`; a bare mktemp would be 0600).
tmp="$(mktemp "$pin_file.XXXXXX")"
cp -p "$pin_file" "$tmp"
python3 -I - "$tmp" "$tag" "$updates" "$([ "$mode" = dry-run ] && echo report || echo quiet)" <<'PY'
import base64
import re
import sys

path, new_tag, updates_path, mode = sys.argv[1:5]

updates = {}
for raw in open(updates_path, encoding="utf-8"):
    raw = raw.rstrip("\n")
    if raw:
        plat, hexdigest, url = raw.split("\t")
        updates[plat] = (hexdigest, url)

lines = open(path, encoding="utf-8").read().splitlines(keepends=True)


def block_at(tag_line):
    indent = re.match(r'^(\s*)', lines[tag_line]).group(1)
    for j in range(tag_line - 1, -1, -1):
        opening = re.match(r'^(\s*)([A-Za-z0-9_.-]+) = \{\s*$', lines[j])
        if opening and len(opening.group(1)) < len(indent):
            return opening.group(2), opening.group(1)
    return None, None


done = set()
i = 0
while i < len(lines):
    m = re.match(r'^(\s*)tag = "([^"]*)";\s*$', lines[i])
    if not m:
        i += 1
        continue
    plat, open_indent = block_at(i)
    if plat not in updates:
        i += 1
        continue
    close = re.compile(r'^' + re.escape(open_indent) + r'\};[ \t]*$')
    end = next((k for k in range(i + 1, len(lines)) if close.match(lines[k])), None)
    if end is None:
        sys.exit(f"bump-nightly-pin: cannot find the closing brace of the {plat} pin")

    hexdigest, url = updates[plat]
    sri = "sha256-" + base64.b64encode(bytes.fromhex(hexdigest)).decode("ascii")
    fields = {"tag": 0, "url": 0, "sha256": 0, "checksum comment": 0}
    for k in range(i, end + 1):
        line = lines[k]
        indent = re.match(r'^(\s*)', line).group(1)
        if re.match(r'^\s*tag = "[^"]*";\s*$', line):
            lines[k] = f'{indent}tag = "{new_tag}";\n'
            fields["tag"] += 1
        elif re.match(r'^\s*url = "[^"]*";\s*$', line):
            lines[k] = f'{indent}url = "{url}";\n'
            fields["url"] += 1
        elif re.match(r'^\s*sha256 = "sha256-[^"]*";\s*$', line):
            lines[k] = f'{indent}sha256 = "{sri}";\n'
            fields["sha256"] += 1
        elif re.match(r'^\s*# curl -fsSL .* -> [0-9a-fA-F]{64}\s*$', line):
            lines[k] = f'{indent}# curl -fsSL "<url>.sha256" -> {hexdigest}\n'
            fields["checksum comment"] += 1
    for field, count in fields.items():
        if count != 1:
            sys.exit(
                f"bump-nightly-pin: expected exactly one {field} line in the {plat} pin, found {count}"
            )
    if mode == "report":
        print(f"{plat}: {new_tag}")
        print(f"  url    {url}")
        print(f"  sha256 {sri}")
    done.add(plat)
    i = end + 1

missing = sorted(set(updates) - done)
if missing:
    sys.exit("bump-nightly-pin: pin entries not found for: " + ", ".join(missing))

with open(path, "w", encoding="utf-8") as out:
    out.write("".join(lines))
PY

if [ "$mode" = dry-run ]; then
  say "dry run: $pin_file not modified"
else
  mv "$tmp" "$pin_file"
  tmp=""
  say "bumped $pin_file to $tag"
fi

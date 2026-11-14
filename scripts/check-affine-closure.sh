#!/usr/bin/env bash
# The A4 gate: no compiler-closure mote may be in `[affine] mode = "warn"`,
# and a tree-built compiler must report zero affine diagnostics over the
# closure.
#
# Two halves, deliberately separate:
#
#   --static       no compiler needed. Reads every closure mote's mote.toml
#                  and the migration ratchet (scripts/affine-closure-allowlist.txt),
#                  and fails when a new warn table appears, an allowlist
#                  entry goes stale, an `[affine]` table survives in `error`
#                  mode (the default is error, so the table must be deleted),
#                  or `#[allow_non_affine]` appears outside the one negative
#                  test that proves the hatch works. Cheap enough for the
#                  pre-commit hook, and the half that makes a stray `warn`
#                  table impossible to merge.
#
#   --dynamic BIN  runs `BIN check --no-cache` over the closure and grades
#                  the result. A non-allowlisted mote with any diagnostic
#                  fails; an allowlisted mote may carry at most its ceiling
#                  (a ceiling can only go down). This is the acceptance test
#                  for a promotion and the CI gate after a self-compile.
#
#                  Scope: the FULL closure in one invocation is the
#                  authoritative measurement, but it checks ~145k lines in
#                  one process and needs a large machine -- on a CI runner it
#                  was killed at 76 minutes (exit 137, OOM) with nothing
#                  flushed. CI therefore runs `--promoted-only` (both the
#                  check and the grading narrow to the motes whose table has
#                  been deleted: they must stay at zero), and the
#                  full-closure run is the local/periodic acceptance step. The static half is unaffected: no new warn mote can
#                  appear, and the ceilings of migrating motes are only
#                  re-measured by the full run. A truncated/killed check is
#                  never graded: the partial log is not data.
#
#   --affine-only  grade only the affine rule's own diagnostics (the
#                  messages in lang/src/typecheck/diagnostic.mo: copy_required,
#                  value_used_after_move, linear_unused, borrowed_value_escapes)
#                  and report any other error as a note. For the LATEST
#                  NIGHTLY's view: that checker lags the tree, so a construct
#                  main gained after it was published (e.g. index-aware
#                  coverage) is an unrelated error there. Whether the nightly
#                  can build the tree is ci-self-compile.sh's question; this
#                  step only asks whether it agrees on the affine rule.
#
# The closure list is scripts/lib/compiler-closure.txt, drift-asserted
# against the `find` input list in scripts/build-self-hosted.sh.
#
# Usage:
#   scripts/check-affine-closure.sh --static
#   scripts/check-affine-closure.sh --dynamic target-monad/ci-self-compile/monad
#   scripts/check-affine-closure.sh --dynamic "$MONAD_HOME/bin/monad" \
#       --promoted-only --no-commit-check --affine-only
#
# Exit 0 = pass, 1 = gate failure, 2 = usage/environment error.
set -euo pipefail

root=${AFFINE_CLOSURE_ROOT:-$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)}
closure_file="$root/scripts/lib/compiler-closure.txt"
allowlist_file="$root/scripts/affine-closure-allowlist.txt"
build_script="$root/scripts/build-self-hosted.sh"

status=0
fail() { echo "FAIL: $*" >&2; status=1; }
ok() { echo "ok:   $*"; }
note() { echo "note: $*"; }

usage() {
    sed -n '2,55p' "${BASH_SOURCE[0]}" | sed 's/^# \{0,1\}//' >&2
    exit 2
}

dynamic_bin=""
promoted_only=0
commit_check=1
affine_only=0
while [ "$#" -gt 0 ]; do
    case "$1" in
        --static) ;;
        --dynamic)
            [ "$#" -ge 2 ] || usage
            dynamic_bin=$2
            shift
            ;;
        --promoted-only) promoted_only=1 ;;
        --affine-only) affine_only=1 ;;
        --no-commit-check) commit_check=0 ;;
        -h|--help) usage ;;
        *) echo "unknown argument: $1" >&2; usage ;;
    esac
    shift
done

[ -f "$closure_file" ] || { echo "missing closure list: $closure_file" >&2; exit 2; }
[ -f "$allowlist_file" ] || { echo "missing allowlist: $allowlist_file" >&2; exit 2; }

declare -a closure=()
while IFS= read -r line; do
    line=${line%%#*}
    line=$(echo "$line" | tr -d '[:space:]')
    [ -n "$line" ] || continue
    closure+=("$line")
done < "$closure_file"

declare -A ceiling=()
declare -a allowlisted=()
while IFS= read -r line; do
    line=${line%%#*}
    read -r path c _rest <<<"$line" || true
    [ -n "${path:-}" ] || continue
    ceiling["$path"]=${c:-}
    allowlisted+=("$path")
done < "$allowlist_file"

is_allowlisted() {
    [ -n "${ceiling[$1]+x}" ]
}

# `none`, `warn`, `error`, `table-no-mode`, or `other` (a mode value that is
# neither spelling). A comment mentioning the table must not match.
affine_mode() {
    awk '
        /^[[:space:]]*#/ { next }
        /^[[:space:]]*\[/ {
            sect = $0
            gsub(/[[:space:]]/, "", sect)
            inaff = (sect == "[affine]")
            next
        }
        inaff && /^[[:space:]]*mode[[:space:]]*=/ {
            if ($0 ~ /"warn"/) print "warn"
            else if ($0 ~ /"error"/) print "error"
            else print "other"
            seen = 1
            exit
        }
        END {
            if (!seen) {
                if (inaff) print "table-no-mode"
                else print "none"
            }
        }
    ' "$1"
}

# ── static ────────────────────────────────────────────────────────────

static_check() {
    echo "affine closure: ${#closure[@]} motes, ${#allowlisted[@]} allowlisted"

    # Drift: the closure list must match the self-hosted build's input list.
    if [ -f "$build_script" ]; then
        local from_build
        from_build=$(awk '
            /find init std sys lang codegen cli llvm runtime build eval/ { found = 1 }
            found {
                line = $0
                sub(/.*find /, "", line)
                sub(/\\[[:space:]]*$/, "", line)
                print line
                if ($0 ~ /motes\/toolkit/) exit
            }
        ' "$build_script" | tr ' ' '\n' | sed '/^[[:space:]]*$/d' | sort)
        local declared
        declared=$(printf '%s\n' "${closure[@]}" | sort)
        if [ "$from_build" != "$declared" ]; then
            fail "closure list drift against scripts/build-self-hosted.sh"
            diff -u <(printf '%s\n' "$declared") <(printf '%s\n' "$from_build") >&2 || true
        fi
    else
        note "no $build_script; skipping closure-list drift check"
    fi

    local m manifest mode
    for m in "${closure[@]}"; do
        manifest="$root/$m/mote.toml"
        if [ ! -f "$manifest" ]; then
            fail "$m: missing $m/mote.toml"
            continue
        fi
        mode=$(affine_mode "$manifest")
        case "$mode" in
            none)
                if is_allowlisted "$m"; then
                    fail "$m is no longer warn; delete its allowlist line"
                fi
                ;;
            warn)
                if is_allowlisted "$m"; then
                    ok "$m: warn (allowlisted)"
                else
                    fail "$m has [affine] mode = \"warn\" but is not allowlisted"
                fi
                ;;
            error)
                fail "$m has an [affine] table with mode = \"error\"; delete the table (error is the default)"
                ;;
            table-no-mode)
                fail "$m has an [affine] table without a mode; delete the table"
                ;;
            *)
                fail "$m has an unrecognised [affine] mode; delete the table"
                ;;
        esac
    done

    local a seen_closure
    for a in "${allowlisted[@]}"; do
        seen_closure=0
        for m in "${closure[@]}"; do
            [ "$m" = "$a" ] && seen_closure=1
        done
        [ "$seen_closure" -eq 1 ] || fail "allowlist entry '$a' is not a compiler-closure mote"
    done

    # The escape hatch weakens the guarantee the gate exists to make. It is
    # allowed only in the negative test that proves the hatch itself works.
    local hits
    hits=$(cd "$root" && grep -RIn --include='*.mo' -E '^[^/]*#\[allow_non_affine' "${closure[@]}" 2>/dev/null || true)
    if [ -n "$hits" ]; then
        while IFS= read -r hit; do
            local rel=${hit%%:*}
            case "$rel" in
                lang/src/tests/typecheck_negative_tests.mo) ;;
                *) fail "#[allow_non_affine] outside lang/src/tests/typecheck_negative_tests.mo: $hit" ;;
            esac
        done <<<"$hits"
    fi
}

# ── dynamic ───────────────────────────────────────────────────────────

mote_of_path() {
    local p=$1 m best=""
    for m in "${closure[@]}"; do
        if [ "$p" = "$m" ] || [[ "$p" == "$m/"* ]]; then
            [ ${#m} -gt ${#best} ] && best=$m
        fi
    done
    printf '%s' "$best"
}

dynamic_check() {
    local bin=$dynamic_bin
    [ -x "$bin" ] || { echo "not executable: $bin" >&2; exit 2; }
    case "$bin" in
        */*) bin=$(cd "$(dirname "$bin")" && pwd)/$(basename "$bin") ;;
    esac

    if [ "$commit_check" -eq 1 ]; then
        local ver head
        ver=$("$bin" version 2>/dev/null | head -n1 | tr -d '[:space:]') || true
        head=$(git -C "$root" rev-parse --short HEAD 2>/dev/null || true)
        if [ -n "$head" ] && [ "$ver" != "$head" ]; then
            fail "binary reports '$ver', HEAD is '$head' (rebuild it, or pass --no-commit-check)"
        else
            note "binary $bin (revision ${ver:-unknown})"
        fi
    fi

    local logdir="$root/target-monad"
    mkdir -p "$logdir"
    local log="$logdir/check-affine-closure.log"

    # `--promoted-only` narrows the CHECK itself, not just the grading: the
    # migrating motes are what make the full-closure run expensive, and
    # checking them only to discard the numbers is the cost that killed CI.
    local -a check_paths=()
    local m
    for m in "${closure[@]}"; do
        if [ "$promoted_only" -eq 1 ] && is_allowlisted "$m"; then
            continue
        fi
        check_paths+=("$m")
    done
    if [ "$promoted_only" -eq 1 ]; then
        note "promoted-only: checking ${#check_paths[@]} of ${#closure[@]} closure motes"
    fi

    local rc=0
    (cd "$root" && "$bin" check --no-cache "${check_paths[@]}") >"$log" 2>&1 || rc=$?
    if [ "$rc" -ne 0 ] && ! grep -q '^FAIL  ' "$log"; then
        # A killed check (137 = SIGKILL, usually the OOM killer) leaves a
        # partial -- or empty -- log. Grading it would report every mote at
        # zero and print "lower the ceiling", which is the opposite of the
        # truth; stop here instead.
        if [ "$rc" -eq 137 ]; then
            fail "check was killed (exit 137, out of memory?); the log is incomplete, not graded (see $log)"
        else
            fail "check exited $rc with no FAIL header (see $log)"
        fi
        sed -n '1,40p' "$log" >&2
        # `status` records the failure; return success so the caller's final
        # "FAILED" summary still prints instead of `set -e` aborting here.
        return 0
    fi

    local summary
    if [ "$affine_only" -eq 1 ]; then
        # Per diagnostic: `error: <msg>` / `warning: <msg>`, then
        # `  --> <path>`. Only the affine rule's messages are graded; any
        # other error is reported as SKIP.
        summary=$(awk '
            /^(error|warning): / {
                sev = ($1 == "error:") ? "error" : "warning"
                aff = ($0 ~ /times but is affine;|is moved [0-9]+ times;|is never used; linear means exactly once|is a borrowed view from `Shared.get`/)
                pending = 1
                next
            }
            pending && /^  --> / {
                pending = 0
                if (aff && sev == "error") fails[$2]++
                else if (aff) warns[$2]++
                else if (sev == "error") skips[$2]++
            }
            END {
                for (p in fails) print "FAIL", fails[p], p
                for (p in warns) print "WARN", warns[p], p
                for (p in skips) print "SKIP", skips[p], p
            }
        ' "$log" | sort -k3)
    else
        # Header format: `WARN  <path> (N warning(s))`, `FAIL  <path> (N error(s))`.
        summary=$(awk '
            /^FAIL  / { n = $3; gsub(/[()]/, "", n); fails[$2] += n }
            /^WARN  / { n = $3; gsub(/[()]/, "", n); warns[$2] += n }
            END {
                for (p in fails) print "FAIL", fails[p], p
                for (p in warns) print "WARN", warns[p], p
            }
        ' "$log" | sort -k3)
    fi

    declare -A warned=()
    declare -A failed=()
    local kind count path mote
    while read -r kind count path; do
        [ -n "${path:-}" ] || continue
        mote=$(mote_of_path "$path")
        if [ -z "$mote" ]; then
            fail "diagnostic outside the closure: $path ($kind $count)"
            continue
        fi
        if [ "$kind" = "SKIP" ]; then
            note "$mote: $count non-affine error(s) in $path, not graded (--affine-only)"
            continue
        fi
        if [ "$kind" = "FAIL" ]; then
            fail "$mote: $count error(s) in $path"
            failed["$mote"]=1
            continue
        fi
        warned["$mote"]=$(( ${warned["$mote"]:-0} + count ))
    done <<<"$summary"

    for m in "${closure[@]}"; do
        local n=${warned["$m"]:-0}
        if [ -n "${failed[$m]+x}" ]; then
            continue
        fi
        if is_allowlisted "$m"; then
            if [ "$promoted_only" -eq 1 ]; then
                continue
            fi
            local c=${ceiling["$m"]}
            if [ -z "$c" ]; then
                note "$m: $n warning(s) (allowlisted, no ceiling)"
            elif [ "$n" -gt "$c" ]; then
                fail "$m: $n warning(s), ceiling is $c"
            elif [ "$n" -lt "$c" ]; then
                note "$m: $n warning(s), ceiling $c -- lower the ceiling"
                ok "$m: $n warning(s) (within ceiling)"
            else
                ok "$m: $n warning(s) (at ceiling)"
            fi
        elif [ "$n" -ne 0 ]; then
            fail "$m: $n warning(s); a promoted mote must be at zero"
        else
            ok "$m: 0 diagnostics"
        fi
    done

    if [ "$affine_only" -eq 0 ] && grep -q '^FAIL  ' "$log"; then
        echo "--- failing blocks ---" >&2
        grep -A3 '^FAIL  ' "$log" | head -n 40 >&2 || true
    elif [ "$affine_only" -eq 1 ] && grep -q '^error: .*\(times but is affine;\|is moved [0-9]* times;\|linear means exactly once\|is a borrowed view\)' "$log"; then
        echo "--- failing affine diagnostics ---" >&2
        grep -A1 '^error: .*\(times but is affine;\|is moved [0-9]* times;\|linear means exactly once\|is a borrowed view\)' "$log" | head -n 40 >&2 || true
    fi
    note "full check log: $log"
}

static_check
if [ -n "$dynamic_bin" ]; then
    dynamic_check
fi

if [ "$status" -ne 0 ]; then
    echo "affine closure: FAILED" >&2
    exit 1
fi
echo "affine closure: OK"

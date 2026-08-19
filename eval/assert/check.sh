#!/usr/bin/env bash
# Deterministic assertions for one proof-workflow eval case.
#
#   eval/assert/check.sh <case-dir> [repo-dir]
#
# Reads <case-dir>/expect.env, runs every applicable assertion, and exits
# non-zero if any fails.  House rule, learned the hard way in skills-internal:
# a checker that inspects zero items must FAIL, not pass.  Every counting
# assertion below therefore errors on an empty inspection set.
set -euo pipefail

CASE_DIR="${1:?usage: check.sh <case-dir> [repo-dir]}"
REPO="${2:-$(cd "$(dirname "$0")/../.." && pwd)}"
CASE_DIR="$(cd "$CASE_DIR" && pwd)"

# shellcheck source=/dev/null
. "$CASE_DIR/expect.env"

: "${TARGET_SRC:?expect.env must set TARGET_SRC (path to the file under grade)}"
: "${TARGET_DECL:?expect.env must set TARGET_DECL}"

SRC="$REPO/$TARGET_SRC"
[ -f "$SRC" ] || { printf 'ERROR: target source %s not found\n' "$SRC" >&2; exit 1; }

WORK="$(mktemp -d)"
trap 'rm -rf "$WORK"' EXIT

FAILURES=0
pass () { printf '  PASS  %s\n' "$1"; }
fail () { printf '  FAIL  %s\n' "$1"; FAILURES=$((FAILURES + 1)); }

printf '== %s ==\n' "$(basename "$CASE_DIR")"

# ---------------------------------------------------------------------------
# A. Routing — does the proof term actually reach the expected endpoint?
#
# Graded from the elaborated term, not from the transcript, so a run that
# *described* the right technique while doing something else still fails.
# ---------------------------------------------------------------------------
# The target's SOURCE is spliced inline rather than imported as a module.
# Importing would read the module's olean, which is stale the moment the agent
# edits the file — the assertion would then grade the *previous* proof and
# silently pass. Splicing grades exactly the bytes on disk.
build_assert_file () {
  local body="$1" out="$2"
  {
    echo "import Lean"
    grep -E '^import ' "$SRC" || true
    grep -v '^import ' "$REPO/eval/assert/UsesConstant.lean"
    grep -v '^import ' "$SRC"
    echo 'open RandomSystems.Eval'
    echo "$body"
  } > "$out"
}

lean_assert () {
  local body="$1" label="$2"
  build_assert_file "$body" "$WORK/assert.lean"
  if (cd "$REPO" && lake env lean "$WORK/assert.lean") > "$WORK/assert.out" 2>&1; then
    pass "$label"
  else
    fail "$label"
    sed 's/^/        /' "$WORK/assert.out" | head -8
  fi
}

if [ -n "${EXPECT_DEP:-}" ]; then
  lean_assert "#uses_constant $TARGET_DECL $EXPECT_DEP ${EXPECT_DEPTH:-6}" \
    "routing: $TARGET_DECL reaches $EXPECT_DEP"
fi

# A negative expectation is how we catch the *wrong* door being taken.
if [ -n "${FORBID_DEP:-}" ]; then
  build_assert_file "#uses_constant $TARGET_DECL $FORBID_DEP ${EXPECT_DEPTH:-6}" "$WORK/forbid.lean"
  if (cd "$REPO" && lake env lean "$WORK/forbid.lean") > "$WORK/forbid.out" 2>&1; then
    fail "routing: $TARGET_DECL took the FORBIDDEN route via $FORBID_DEP"
  else
    pass "routing: did not route via $FORBID_DEP"
  fi
fi

if [ "${EXPECT_AXIOM_CLEAN:-0}" = "1" ]; then
  lean_assert "#assert_axiom_clean $TARGET_DECL" "axioms: $TARGET_DECL is clean"
fi

# ---------------------------------------------------------------------------
# B. Re-derivation budget — how much new surface did the run mint?
# ---------------------------------------------------------------------------
# Baseline is a SNAPSHOT taken by setup.sh, not a git ref. Git was the obvious
# choice and the wrong one: the fixture is often untracked (diff sees nothing,
# so a run that did everything scores zero), and a tree with unrelated edits
# attributes them to the agent. A snapshot is exact regardless of tree state.
BASELINE="$REPO/eval/.baseline/$(basename "$CASE_DIR")/$(basename "$TARGET_SRC")"
DIFF="$WORK/diff.txt"

if [ ! -f "$BASELINE" ]; then
  fail "baseline: no snapshot at $BASELINE — run the case's setup.sh first"
  printf '\nRESULT: fail (cannot grade without a baseline)\n'
  exit 1
fi

diff -u "$BASELINE" "$SRC" > "$DIFF" || true
printf '  (baseline=%s)\n' "${BASELINE#"$REPO"/}"

if [ ! -s "$DIFF" ]; then
  fail "diff: $TARGET_SRC is unchanged from the fixture — the run produced nothing to grade"
else
  NEW_DECLS=$(grep -cE '^\+[[:space:]]*(private[[:space:]]+)?(noncomputable[[:space:]]+)?(theorem|lemma|def|abbrev|structure|instance)[[:space:]]' "$DIFF" || true)
  if [ "${MAX_NEW_DECLS:-}" != "" ]; then
    if [ "$NEW_DECLS" -le "$MAX_NEW_DECLS" ]; then
      pass "reuse: $NEW_DECLS new declaration(s) <= budget $MAX_NEW_DECLS"
    else
      fail "reuse: $NEW_DECLS new declaration(s) > budget $MAX_NEW_DECLS (re-derivation)"
      grep -E '^\+[[:space:]]*(private[[:space:]]+)?(noncomputable[[:space:]]+)?(theorem|lemma|def)[[:space:]]' "$DIFF" | sed 's/^/        /' | head -10
    fi
  fi

  if grep -qE '^\+.*\bprivate\b' "$DIFF"; then
    fail "hygiene: the run introduced a 'private' declaration"
  else
    pass "hygiene: no 'private' introduced"
  fi
fi

# ---------------------------------------------------------------------------
# C. Process artifacts — was the sketch real, and did it precede the Lean?
#
# This is what catches process theatre: a plausible sketch written after the
# fact to justify whatever the agent already did.
# ---------------------------------------------------------------------------
if [ "${EXPECT_ARTIFACTS:-1}" = "1" ]; then
  # Any markdown written AFTER setup.sh ran. The baseline snapshot is the
  # mtime reference point, so this needs no manifest and no git.
  #
  # This replaces a version that referenced a $BASE variable removed in the
  # switch to snapshot baselines: under `set -u` the subshell died, `|| true`
  # swallowed it, and the assertion reported "no sketch" unconditionally — it
  # could never pass. Exactly the checker-inspects-zero-items bug.
  SKETCH=$(find "$REPO" -name '*.md' -newer "$BASELINE" \
    -not -path '*/.lake/*' -not -path '*/.git/*' -not -path '*/.claude/*' \
    -not -path '*/eval/*' 2> /dev/null | head -1 || true)
  SKETCH="${SKETCH#"$REPO"/}"
  if [ -z "$SKETCH" ] || [ ! -f "$REPO/$SKETCH" ]; then
    fail "artifact: no sketch/plan markdown produced"
  else
    pass "artifact: sketch present ($SKETCH)"

    # The sketch must commit to a technique from the closed set.
    if grep -qiE '(h[- ]technique|h[- ]coefficient|conditional equivalence|condition c|coupling|winnability|condition[- ]based)' "$REPO/$SKETCH"; then
      pass "artifact: sketch names a technique"
    else
      fail "artifact: sketch names no technique from the closed set"
    fi

    # And to a per-node reuse verdict.
    if grep -qE '\b(REUSE|ADAPT|NEW)\b' "$REPO/$SKETCH"; then
      pass "artifact: plan carries reuse verdicts"
    else
      fail "artifact: plan carries no REUSE/ADAPT/NEW verdict"
    fi

    # Ordering: the sketch must not be newer than the Lean it justifies.
    if [ "$REPO/$SKETCH" -nt "$SRC" ]; then
      fail "ordering: sketch is NEWER than the Lean — written after the fact"
    else
      pass "ordering: sketch precedes the Lean"
    fi
  fi
fi

printf '\n'
if [ "$FAILURES" -eq 0 ]; then
  printf 'RESULT: pass\n'
else
  printf 'RESULT: fail (%d assertion(s))\n' "$FAILURES"
  exit 1
fi

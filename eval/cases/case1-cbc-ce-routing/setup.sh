#!/usr/bin/env bash
# Materialize the case-1 fixture: the CBC-MAC model with the two headline
# proofs stripped to `sorry`.
#
#   setup.sh [repo-dir]
#
# The reference file is held OUTSIDE the repo (see eval/README.md) precisely so
# an evaluated agent cannot read the answer.  This script reconstitutes the
# model from it, removing each headline proof body — including the in-proof
# comment that names the endpoint, which is the actual spoiler.
set -euo pipefail

REPO="${1:-$(cd "$(dirname "$0")/../../.." && pwd)}"
REF="${EVAL_REFERENCE_DIR:-$HOME/Documents/tob/research/eval-reference}/CBCMAC.lean"
OUT="$REPO/RandomSystems/CBCMAC.lean"

if [ ! -f "$REF" ]; then
  printf 'ERROR: reference not found at %s\n' "$REF" >&2
  printf 'Set EVAL_REFERENCE_DIR, or restore with: git -C %s checkout RandomSystems/CBCMAC.lean\n' "$REPO" >&2
  exit 1
fi

# A stale olean is BOTH a cheat channel and a correctness bug: `import
# RandomSystems.CBCMAC` would load the compiled reference proof instead of the
# fixture source, so `#print cbc_mac_randomness_expander` hands over the answer
# and every assertion grades the wrong term. Clear it before writing.
for ext in olean olean.hash ilean ilean.hash trace; do
  rm -f "$REPO/.lake/build/lib/lean/RandomSystems/CBCMAC.$ext"
done
rm -f "$REPO/.lake/build/ir/RandomSystems/CBCMAC.c" \
      "$REPO/.lake/build/ir/RandomSystems/CBCMAC.c.hash"

# This repo's tooling routes Python through uv; fall back for a bare checkout.
if command -v uv > /dev/null; then PY=(uv run python3); else PY=(python3); fi

"${PY[@]}" - "$REF" "$OUT" <<'PY'
import re, sys

ref, out = sys.argv[1], sys.argv[2]
src = open(ref).read()

TARGETS = ["cbc_mac_randomness_expander", "cbc_mac_randomness_expander_urp"]
# A top-level boundary: the start of the next declaration or docstring.
BOUNDARY = re.compile(r'^(/--|@\[|theorem |lemma |def |noncomputable def |end |namespace |section )', re.M)

stripped = 0
for name in TARGETS:
    m = re.search(r'^theorem %s\b' % re.escape(name), src, re.M)
    if not m:
        sys.exit("ERROR: could not locate 'theorem %s' in the reference" % name)
    # The statement ends at the first ':=' that closes it; the body runs to the
    # next top-level boundary.
    assign = src.find(':=', m.end())
    if assign == -1:
        sys.exit("ERROR: no ':=' after 'theorem %s'" % name)
    nxt = BOUNDARY.search(src, assign)
    end = nxt.start() if nxt else len(src)
    src = src[:assign] + ":= by\n  sorry\n\n" + src[end:]
    stripped += 1

if stripped != len(TARGETS):
    sys.exit("ERROR: stripped %d of %d targets" % (stripped, len(TARGETS)))

# Fail loudly rather than shipping a fixture that still contains the answer.
for spoiler in ["seededConditionCGame_le", "condition-C endpoint"]:
    if spoiler in src:
        sys.exit("ERROR: fixture still mentions %r — the answer leaked" % spoiler)

open(out, "w").write(src)
print("case1 fixture written: %s (%d proof(s) stripped)" % (out, stripped))
PY

# ---------------------------------------------------------------------------
# Arm 1b — hold out the recipe.
#
# CHEATSHEET.md's condition-C section names the endpoint AND says "Read this as
# the template for a new MBO-game proof", so with it in place the case measures
# "did you consult the index", not "did you route correctly".  Arm 1b removes
# those two sections so routing must come from the model's structure — which is
# the claim that generalizes to a scheme not yet in the index.
if [ "${EVAL_HOLD_OUT_RECIPE:-0}" = "1" ]; then
  REFDIR="$(dirname "$REF")"
  cp "$REPO/CHEATSHEET.md" "$REFDIR/CHEATSHEET.full.md"
  "${PY[@]}" - "$REPO/CHEATSHEET.md" <<'PY'
import re, sys
path = sys.argv[1]
src = open(path).read()
# Drop from the seed-indexed condition-C heading through the end of the CBC
# worked-instance section (i.e. up to the next same-level heading).
pat = re.compile(
    r'^### Seed-indexed condition C.*?(?=^## )', re.M | re.S)
new, n = pat.subn('### (section held out for eval)\n\n', src)
if n != 1:
    sys.exit("ERROR: expected exactly 1 condition-C section, found %d" % n)

# The endpoint is also named in the top-level "By goal" and "REUSE THIS"
# tables, so the section cut alone is not enough. Drop every remaining line
# that names it.
SPOILERS = ["seededConditionCGame", "cbc_mac_randomness_expander",
            "seededHashThenURF", "blindMaxWinProb_filterQueries_monitored_le"]
kept = [ln for ln in new.splitlines(True)
        if not any(s in ln for s in SPOILERS)]
new = "".join(kept)

for s in SPOILERS:
    if s in new:
        sys.exit("ERROR: CHEATSHEET still names %r after hold-out" % s)
if len(kept) == len(new.splitlines(True)) and n == 0:
    sys.exit("ERROR: hold-out removed nothing")
open(path, "w").write(new)
print("arm 1b: CHEATSHEET condition-C/CBC sections held out")
PY
fi

# Snapshot the fixture as the grading baseline (see eval/assert/check.sh).
mkdir -p "$REPO/eval/.baseline/case1-cbc-ce-routing"
cp "$OUT" "$REPO/eval/.baseline/case1-cbc-ce-routing/CBCMAC.lean"
echo "baseline snapshot written"

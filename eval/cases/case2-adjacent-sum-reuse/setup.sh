#!/usr/bin/env bash
# Materialize the case-2 fixture from its pristine template and snapshot the
# grading baseline.
#
# The template is NOT optional: an earlier version restored via `git checkout`,
# which silently no-ops on an untracked file and then snapshotted the PREVIOUS
# arm's solved proof as the baseline — scoring the next arm against an answer.
set -euo pipefail
REPO="${1:-$(cd "$(dirname "$0")/../../.." && pwd)}"
CASE="$(cd "$(dirname "$0")" && pwd)"

cp "$CASE/Fixture.template.lean" "$CASE/Fixture.lean"
grep -q 'sorry' "$CASE/Fixture.lean" || { echo "ERROR: template has no 'sorry' — it is not an unsolved fixture" >&2; exit 1; }

mkdir -p "$REPO/eval/.baseline/case2-adjacent-sum-reuse"
cp "$CASE/Fixture.lean" "$REPO/eval/.baseline/case2-adjacent-sum-reuse/Fixture.lean"
echo "case2 fixture reset from template; baseline snapshot written"

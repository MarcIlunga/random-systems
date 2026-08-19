#!/usr/bin/env bash
# ==============================================================================
# CANONICAL Codex dispatch for the SequenceHash effort.
# ALWAYS use this — NEVER call `codex exec` directly. It MECHANICALLY prepends the
# standing preamble (dispatch/PREAMBLE.txt, incl. the strict sketch-adaptation
# discipline §3c) so the strictness can never be forgotten, even after context
# compaction. If the preamble is missing it FAILS LOUDLY rather than dispatch weak.
#
# Usage:  codex-dispatch.sh <task-card-file> <output-file>
# The <task-card-file> holds ONLY the task-specific content (no STEP 0 needed —
# the wrapper adds it).
# ==============================================================================
set -euo pipefail

REPO="/Users/marcilunga/Documents/tob/research/random-systems"
DISPATCH="$REPO/sequence-hash/dispatch"
PREAMBLE="$DISPATCH/PREAMBLE.txt"

CARD="${1:?usage: codex-dispatch.sh <task-card-file> <output-file>}"
OUT="${2:?usage: codex-dispatch.sh <task-card-file> <output-file>}"

# --- guard: the standing preamble MUST exist and be non-trivial ---------------
if [[ ! -s "$PREAMBLE" ]]; then
  echo "FATAL: $PREAMBLE missing/empty — refusing to dispatch without the standing preamble." >&2
  exit 3
fi
if ! grep -q "REALLY ADAPT, NEVER TRANSCRIBE" "$PREAMBLE"; then
  echo "FATAL: $PREAMBLE is missing the strict sketch-adaptation discipline (§3c) — refusing to dispatch." >&2
  exit 3
fi
if [[ ! -s "$CARD" ]]; then
  echo "FATAL: task card '$CARD' missing/empty." >&2
  exit 4
fi

# --- pre-flight: reap stale (>=1h) lean-lsp/uv zombies that hang codex ---------
for pid in $(pgrep -f "lean-lsp-mcp" 2>/dev/null || true); do
  et="$(ps -o etime= -p "$pid" 2>/dev/null | tr -d ' ' || true)"
  case "$et" in
    *-*|*:*:*) echo "reaping stale lean-lsp pid $pid (elapsed $et)" >&2; kill -9 "$pid" 2>/dev/null || true ;;
  esac
done

# --- assemble: standing preamble  +  blank line  +  task card -----------------
PROMPT="$(cat "$PREAMBLE"; printf '\n\n'; cat "$CARD")"

echo "dispatch: card='$CARD' out='$OUT' (preamble enforced, $(wc -l < "$PREAMBLE") preamble lines)" >&2
exec codex exec -C "$REPO" -m gpt-5.6-sol -c model_reasoning_effort="high" --yolo -o "$OUT" "$PROMPT"

#!/usr/bin/env bash
# sessionStart: inject a short harness reminder into agent context.
set -euo pipefail
cat >/dev/null  # consume stdin JSON

printf '%s\n' '{"additional_context":"Quantum agent harness: follow AGENTS.md. After meaningful edits, verify with `cabal build quantum:lib:quantum` (not tricorder). Run `cabal test` only at milestones. Use skill quantum-dev-loop for implementation tasks. Small increments; parse do not validate; stop and co-plan instead of hacking."}'

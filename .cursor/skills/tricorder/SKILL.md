---
name: tricorder
description: >-
  Optional tricorder daemon docs. Not used in the default quantum-dev-loop —
  prefer `cabal build quantum:lib:quantum`. Only consult this if the user
  explicitly asks for tricorder.
---

# Using tricorder (quantum) — optional

**Default loop does not use tricorder.** Prefer:

```bash
cabal build quantum:lib:quantum
```

Use this skill only when the user explicitly requests tricorder.

**Repo note:** [`.tricorder.yaml`](../../../.tricorder.yaml) loads
`quantum:lib:quantum` only. At milestone boundaries, run `cabal test` yourself.

## Commands

- `tricorder start` — start the daemon (no-op if already running)
- `tricorder stop` — stop the daemon
- `tricorder status` — current build state (text)
- `tricorder status --wait` — block until the current build cycle finishes
- `tricorder status --json` — machine-readable full state
- `tricorder status --verbose` / `-v` — full GHC body under each diagnostic
- `tricorder status --expand N` — full body for diagnostic `#N`
- `tricorder test-results` — latest test run output (only if tests are configured)
- `tricorder source MODULE[#FUNCTION]` — source of an installed module/symbol
- `tricorder log` — daemon log (`--follow` / `-f` to stream; `--print-path` for path)
- `tricorder ui` — human TUI

## Notes

- Prefer stopping the daemon when not using it: `tricorder stop`.
- Do **not** avoid `cabal test` at milestones.

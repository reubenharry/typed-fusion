---
name: quantum-dev-loop
description: >-
  Plan, implement, and verify Haskell tensor-network changes in this repo with
  small increments and a targeted cabal lib build. Use when implementing
  features, fixing compile errors, refactoring TensorNetwork/DMRG/MPS code, or
  when the user hands off a development task.
---

# Quantum development loop

Follow [`AGENTS.md`](../../../AGENTS.md) and the always-on rules under
`.cursor/rules/`. Verify with `cabal build quantum:lib:quantum` — do **not**
use tricorder in the default loop.

## Procedure

Copy and track:

```
Task progress:
- [ ] 1. Context: ROADMAP current focus + modules to touch
- [ ] 2. Approach stated (2–5 lines)
- [ ] 3. Small edit
- [ ] 4. cabal build quantum:lib:quantum
- [ ] 5. Fix / or stop if blocked
- [ ] 6. Milestone cabal test (or probe) when slice is done
- [ ] 7. Handback summary
```

### 1. Context

Read `ROADMAP.md` **Current focus**. Open the production modules you will
change; check whether a `*.Reference` oracle already pins the convention.

### 2. Approach (2–5 lines)

State the categorical path. Name any blocker (missing unitor, compose, etc.).
If the design is unclear, **stop and co-plan** — do not hack toward green.

### 3. Small edit

One conceptual change when possible. Prefer reusing Fixed / General helpers
over new parallel APIs. Parse-don't-validate; no basis-sum in production; no
new `unsafeCoerce` without explicit approval.

### 4–5. Verify with a targeted lib build

```bash
cabal build quantum:lib:quantum
```

On errors: read the GHC message, fix, repeat. Do **not** start tricorder or run
a full-project `cabal build` / `cabal test` after every edit.

Policy conflict or unclear design → stop. Honest `undefined` + named blocker
is OK; temporary hacks are not.

### 6. Milestone gate

When a slice is finished (API shape stable, types green):

```bash
cabal test
```

For performance tasks, use the named probe/script instead of or in addition to
tests.

### 7. Handback

Report: what changed, how verified (lib build / `cabal test` / probe), what
remains open or blocked.

## Definition of done

- [ ] Approach was categorical (or an honest stub with a named blocker)
- [ ] No new basis-sum / `unsafeCoerce` / temporary hack
- [ ] `cabal build quantum:lib:quantum` succeeds (or only pre-existing warnings)
- [ ] Milestone `cabal test` (or agreed probe) run when the slice warrants it
- [ ] Handback lists remaining open items

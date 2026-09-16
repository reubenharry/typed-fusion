# ROADMAP

## Current focus

**Step 1 (done / in progress):** `FusionTheory` / `FusionData` as the mathematical
source of F / R / cup **scalars**. Hom cups and F-move channel lists read
`cupCoeff` / `allowedLeftMids` / `allowedRightMids`; SU(2) `cupCoeff` is
`FS(j)·dim(j)`; U(1) has a full `FusionData` instance.

Next: typed channel morphisms (step 3), then optional skeletal Ops for
unbounded theories (step 2).

---

## Goal

`FusionTheory` + `FusionData` are the sole source of N / F / R / cup structure
constants. Hom (and Fib) operations should be as theory-generic as possible;
SU(2)- or Fib-specific code should only remain where the **carrier** differs
(genealogy `FTreeV` + CG layout vs skeletal `HomS` blocks).

---

## Step 1 — Scalars only ✅

Wire Hom (and shared helpers) to `FusionData` without changing carriers.

| Piece | Status |
| --- | --- |
| `cupCoeff` includes FS for SU(2) | done |
| Hom `cup` uses `cupCoeff @SU2Th` | done |
| Generic `allowedLeftMids` / `allowedRightMids` | done |
| Hom F-move channel lists via those | done |
| U(1) `FusionData` (F=1, R=1, cup=1) | done |
| Dense F matrix still CG (`fmoveIrrepsFlat`) | intentional interim |
| Hom fused R-move from `rSymbol` | not yet (no tree R yet; `HomUnfused` braid = `swapMap`) |

**Verify:** `cabal build quantum:lib:quantum`; Hom cup smokes still expect
`½ → −2`, `1 → 3`.

---

## Step 3 — Typed channel morphisms (primary next)

Replace CG densify oracles with morphisms built from `fSymbol` / `rSymbol` on
typed channels.

1. **Per-channel F** — for fixed irrep triple `(a,b,c)` and total `d`, a map
   between left mid space (⊕_e Hom(e⊗c → d)) and right mid space (⊕_f Hom(a⊗f → d))
   with blocks `[F^{abc}_d]_{ef}` from `fSymbol`. Prefer `C (d+1)` (or mult⊗irrep)
   payloads, not packed flats.
2. **Lift to genealogy** — `fmoveTrees` becomes collect → apply channel F →
   scatter, parameterized by theory tag `t` (start with `SU2Th`; keep CG densify
   as `*.Reference` oracle / QuickCheck).
3. **Cups as η/ε** — replace singlet `cupCoeff` walk with true cups/caps once
   channel F exists (Mac Lane compose ladder).
4. **R-move** — channel phases from `rSymbol` on fused trees (hexagon with F);
   distinguish from unfused `swapMap`.

**Blockers to name honestly:** uniform boundary / compose on tensor domains;
theory-indexed `HomFused t` vs SU(2)-hardcoded spines.

---

## Step 2 — Skeletal Ops beyond `FiniteIrr` (optional parallel)

`Fusion.Ops` (`associateSectors` / `braidSectors`) already builds Fib morphisms
from `FusionData`, but requires `FiniteIrr` and `TermLab ~ code`.

- Generalize to unbounded labels (SU(2) `Int`, U(1) `Integer`) by taking
  explicit outcome lists from `fuseOutcomes` instead of walking `irrVals`.
- Keep skeletal `HomS` as the Fib / finite-theory carrier; do **not** force Hom
  genealogy onto `HomS`.
- Useful for SU(2) Schur-block probes and for sharing braid/associator algebra
  with Fib; not a substitute for step 3 on `FTreeV`.

---

## Non-goals / keep separate

- **CG densify** lives only in `Hom.Reference` (`quantum-reference` package);
  production F uses SixJ / channel morphisms. Do not import `*.Reference` from
  the main `quantum` library.
- **No basis-sum in production** — Reference oracles only.
- **No new `unsafeCoerce`** without explicit approval.

---

## Suggested order of work

1. ~~Scalars (this step)~~
2. Channel F morphism API + SU(2) instance from `fSymbol` (oracle-checked vs CG)
3. Replumb `fmoveTrees` to channel F; demote densify to Reference
4. Theory parameter on Hom compose / cup ladder
5. R-move from `rSymbol`; U(1) Hom path if needed
6. (Parallel) Ops without `FiniteIrr` for unbounded `fuseOutcomes`

# Roadmap: a symmetry-aware, basis-independent DMRG in Haskell

*Status: living document. Last updated 2026-06-23.*

## 0. The thesis

The unifying concept of this project is the same one TensorKit.jl makes, but pushed
harder with Haskell's type system:

> **A tensor is a morphism in a (dagger, braided) monoidal category whose objects
> are (graded) vector spaces.** Symmetry is not bolted onto tensors; the symmetry
> *is* the category. Everything else — sectors, fusion trees, block-sparsity — is
> the data needed to represent such a morphism efficiently once the category has
> non-trivial fusion structure.

`linearmap-category` already gives us the *trivial-symmetry* instance of this
picture done properly: basis-independent linear maps as morphisms in a constrained
monoidal category, with `⊗`, `+>`, adjoints, and spectral operations defined
abstractly over `TensorSpace`/`FiniteDimensional`/`HilbertSpace`. The project's job
is to (a) build a real algorithm — DMRG — *natively in that vocabulary*, and then
(b) swap the trivial-symmetry vector spaces for symmetric (graded) ones, leaving the
algorithm untouched.

The single most important design principle, which makes (b) cheap, is stated in §3.

---

## 1. How the four strands map onto the TensorKit picture

| TensorKit concept | This project's strand | File(s) | Maturity |
|---|---|---|---|
| `Sector` / fusion category interface (`one, ⊗, dual, N, F, R, FS, dim`) | well-typed representations | `General.hs`, `SU2.hs` | exploratory; type-level fusion for U(1) & SU(2) charges exists, no F/R symbols |
| `GradedSpace{I}` + block-sparse morphism (Schur blocks) | intertwiners | `FunctorExperiment.hs` | **most mature**: U(1) intertwiners as block-sparse hom; `compose` is now singleton-recursive (no `unsafeCoerce`); `TensorSpace` via `ToC`. Next: multi-block `ApplyInterGo` (toward SU(2)) |
| `TensorMap` with named legs + contraction/permute | typed ITensors | `ItensorTyped.hs` | leg-labelling, type-level contraction (`Difference`/`Intersection`), permutation *evidence* done; `permute`/`rawContract` are `error "TODO"` |
| MPS/DMRG algorithm layer (à la MPSKit) | DMRG | `TensorNetwork.DMRG.Fixed3` | typed 3-site DMRG green (TFIM); local solve still dense `eigSH`; gauge SVD via `getLinearMap`; `Concrete` is legacy |
| Symmetric MPS as a vector space (tangent space, addition of states) | vector space of MPS | `TensorNetwork.MPS.FinSupp3` | `VectorSpace` + `HasBasis` (physical); growable `FinSuppSeq` bond; flatten / canonical section green. **Next (§5b):** categorical MPS/MPO layer, `InnerSpace`, effective-`H` eigensolve |

TensorKit factors these as: `Sector` (in `TensorKitSectors.jl`) → `GradedSpace` →
`ProductSpace`/`HomSpace` → `FusionTree` → `TensorMap`, with `MPSKit.jl`/`PEPSKit.jl`
as the algorithm layer on top. Our strands cover the same stack but were grown
bottom-up and middle-out independently; the roadmap's spine is the order in which to
*connect* them.

---

## 2. The substrate: what `linearmap-category` gives us, and the one real gap

We control the whole fork (`../linearmap-family`), so the substrate is extensible,
not fixed. Inventory of what's directly usable for DMRG:

**Objects & morphisms**
- `TensorSpace v` (assoc. `TensorProduct v w`), `LinearSpace v`, `FiniteDimensional v`,
  `SemiInner v`, `HilbertSpace v = (LSpace v, InnerSpace v, DualVector v ~ v)`.
- `v +> w` (`LinearMap`), `v ⊗ w` (`Tensor`), `v -+> w` (`LinearFunction`); composition
  and the monoidal product live in the constrained `Category`/`Arrow` hierarchy
  (`Control.Category.Constrained`).
- `adjoint :: (v +> DualVector w) -+> (w +> DualVector v)`, `riesz`, `pseudoInverse`,
  `Norm`/`Seminorm`, `euclideanNorm`, `orthogonalComplementProj`.

**Spectral / factorization**
- `eigen :: (FiniteDimensional v, IEEE (RealPart (Scalar v)), …) => Norm v -> (v+>v) -> [(Scalar v, v)]`
  — matrix-free Krylov + Givens decoupling; accepts an arbitrary `Norm`, not only
  `euclideanNorm`.
- `constructEigenSystem` / `roughEigenSystem` / `finishEigenSystem` — lower-level
  eigenbasis builders (only apply `f`, never materialise the operator matrix).
- `densifyNorm` — upgrades a `Norm` to act via `sampleLinearFunction` (dense norm
  operator; useful for Krylov orthonormalisation on map spaces).
- `Math.TensorNetwork.svd :: (Scalar v ~ Double, Scalar w ~ Double, HilbertSpace v,
  HilbertSpace w, Monad m) => InitialVectors m v -> (v -+> w) -> Int -> m [SVDPendants v w]`
  — basis-independent iterative SVD (in `linearmap-family`, which we own).

**Gaps relevant to DMRG:**
- `euclideanNorm` requires `Coercible v (DualVector v)` (`HilbertSpace`). Map-space
  centres `(C bₗ ⊗ C p) +> C bᵣ` are `InnerSpace` (Frobenius / Hilbert–Schmidt) but
  **not** `HilbertSpace` — so `eigen euclideanNorm heff` does not typecheck on the
  MPS centre. Fix: supply a custom `Norm` derived from `<.>` (see D3 migration, §4b).
- Complex scalars: `eigen` needs `IEEE (RealPart (Scalar v))`, satisfied by
  `Complex Double`; the old `Concrete` blocker was real-only `svd`, not `eigen` per se.

---

## 3. On generality: write it concrete first

There's a tempting principle — "write DMRG polymorphically over the local Hilbert
space (`FiniteDimensional`/`HilbertSpace`) from day one, never over a concrete `C n`,
so the symmetric case is a free instantiation." It's true that a U(1)/SU(2) graded
space is *also* a `FiniteDimensional HilbertSpace` (what `FunctorExperiment`'s `ToC` is
reaching for), so generic code would run on symmetric tensors unchanged.

**But we are not making that a day-one constraint.** Haskell is extremely refactorable:
generalising a concrete `C n` DMRG to an abstract local space later is a cheap,
type-driven refactor, and the compiler does most of the work. Forcing full polymorphism
up front mostly makes the *first* running version harder to write and harder to debug.

So: **write the near-term DMRG concretely over `C n` / `Complex Double`**, get it
correct against an exact benchmark, and generalise the local space when we actually fold
in symmetry (§5). The "intertwiners are easy to incorporate later" intuition holds — not
because we pre-abstracted, but because the abstraction step is itself easy.

---

## 4. Near-term: dense DMRG, natively in `linearmap-category` (the priority)

Goal: an end-to-end, sweeping, single-site (then two-site) DMRG that finds the ground
state of a known 1-D model, written in `+>`/`⊗`/`TensorSpace` vocabulary, validated
against an exact answer. No symmetry yet.

### Phase 0 — substrate decisions (RESOLVED 2026-06-07; see §7)
- **D1 field**: ✅ **complex** (`Complex Double`).
- **D2 MPS representation**: ✅ **typed `C b` bonds first** (a finite, fixed-length,
  type-checked-bond MPS — the `TensorNetwork.MPS`-style representation, cleaned up per
  §4a). The growable `FinSuppSeq`/`MPSClever` vector-space form is deferred to medium-term
  (§5a): it has the bilinear-bond conjugation hazard and trades type-level bond checking
  for growability — worth it later for state addition / adaptive χ, not for the first
  correct DMRG.
  - **Site orientation** (settled): **transfer / contraction** — each site is
    `(C bₗ ⊗ C p) +> C bᵣ`, boundaries use `C 1`.
  - **Conjugation** (settled): **per-site, explicit** via `vectorConjugate`; bras and
    environments contract the conjugated tensor against the ket with bilinear ops.
- **D3 eigensolver**: ✅ **interim — dense hmatrix `eigSH`** (`GroundState.hs`): materialise
  the operator in the `FiniteDimensional` basis (`toDenseMatrix`) and solve with hmatrix.
  Verified on `diag(3,1,2)` → ground energy `1.0`, spectrum `[1,2,3]`. ➡ **Target —
  matrix-free `eigen`** with a Hilbert–Schmidt `Norm` on map-space centres (§4b); keep
  `toDenseMatrix` as an oracle only.

**First concrete target: the typed 3-site MPS.** Build the whole pipeline below on a
fixed **3-site**, typed-bond MPS (transfer orientation, §4a) before any generalisation.
It exercises the full DMRG loop at minimal scale, and the contract-to-physical map gives
a `C (p³)` oracle for every operation. N-site generalisation is §5a.

### Phase 1 — the typed MPS type + map to physical space
1. Define the 3-site MPS in transfer orientation (§4a): `(C 1 ⊗ C p) +> C b1`,
   `(C b1 ⊗ C p) +> C b2`, `(C b2 ⊗ C p) +> C 1`, with `KnownNat` bonds `b1,b2`.
   Settle the per-site tensor representation here (the concrete `+>`/`⊗` shape).
2. **Map to physical space**: contract the three sites into the state
   `C 1 +> (C p ⊗ C p ⊗ C p)` (≅ `C (p³)`), by composition along the bonds. This is the
   oracle generator for all later tests.

### Phase 2 — inner product, norm, dual (conjugation lives here)
3. Define `mpsInner ψ φ` by contracting the **per-site-conjugated** bra of ψ against φ
   (transfer matrices), conjugation via `vectorConjugate` only (never via `<.>`/`adjoint`,
   which are bilinear/transpose — see memory `conjugation-conventions`). Define `norm` and
   the bra/`dual` consistently.
4. **Property tests** (mirroring `prop_addThenFlatten`):
   - `mpsInner ψ φ === (mpsToPhysical ψ) <.> (mpsToPhysical φ)` — pins the convention
     against `C n`'s correct sesquilinear `<.>`.
   - `mpsInner ψ ψ` real and ≥ 0; `mpsInner ψ φ === conjugate (mpsInner φ ψ)`.

### Phase 3 — MPO + contraction
5. **MPO** of `+>` morphisms in matching orientation (`MPO p b` is sketched in
   `TensorNetwork.MPS.Fixed3`); build a concrete benchmark model — **transverse-field Ising**
   (exactly solvable) or **spin-½ AFM Heisenberg** (Bethe / ED).
6. **MPS–MPO–MPS contraction** for `⟨ψ|H|φ⟩`, reusing the Phase-2 conjugated bra. Test the
   expectation value against the dense `C (p³)` operator applied to the flattened state.

### Phase 4 — effective Hamiltonian & local solve
7. Build the per-site effective Hamiltonian by contracting the MPO with the left/right
   **environments** (partial MPS–MPO–MPS contractions). Keep `Heff` as an endomorphism on
   the site's own space (a map-space endo is fine — see `GroundState`); no flattening.
8. Solve the lowest eigenpair with `GroundState.groundState` (✅ done, D3 interim). First
   confirm `Heff` is genuinely (conjugate-)Hermitian — `groundState` symmetrises via
   `H.sym`, so a non-Hermitian `Heff` would be silently masked; test Hermiticity directly
   (`prop_effectiveHHermitian` ✅).

### Phase 4b — migrate local solve to matrix-free `eigen` (planned)

Replace the dense `toDenseMatrix` + `eigSH` path in `GroundState.groundState` with
linearmap's `eigen`, keeping `Heff` as a map-space endomorphism (no flattening to `C n`).

**Why not `getLinearMap`?** Unlike gauge-transport SVD (where `getLinearMap` after
`siteForLeftSVD` matches the numerical layout), `getLinearMap heff` exposes backend
tensor storage (e.g. `2×32`), not the `8×8` operator matrix in the HS basis that
`toDenseMatrix` builds. `eigen` avoids materialising either matrix.

**Steps (ordered):**

1. **Define a Hilbert–Schmidt norm** on the centre / generic `InnerSpace v`:
   `Norm v` from the existing Frobenius inner product (`‖v‖ = √(realPart (v <.> v))`).
   `euclideanNorm` is unavailable when `DualVector v ≁ v` (map spaces, tensors). Likely
   home: `GroundState.hs` first; candidate for upstreaming to `linearmap-family` as
   `frobeniusNorm` / `innerProductNorm` (D4).
2. **Pass it to `eigen`** — `eigen (densifyNorm hsNorm) heff` for Krylov
   orthonormalisation; only operator *applications* `heff $ v`, never a full matrix build.
3. **Reimplement `groundState` / `spectrum`** — lowest eigenpair via `minimumBy` on
   `|λ|`; drop `H.sym` (eigen assumes Hermitian input; symmetrisation masked bugs under
   the dense path — rely on `prop_effectiveHHermitian` instead).
4. **Keep `toDenseMatrix` exported** — regression oracle only; not used in the solve path.
5. **Property tests** — `prop_groundStateMatchesToDenseMatrix` on TFIM `Heff` at each site;
   existing DMRG energy checks vs `denseGroundEnergy` must stay green.
6. **Accuracy budget** — `eigen` is a tradeoff (two `finishEigenSystem` passes over a
   `roughEigenSystem` approximation); tune Krylov tolerance or call
   `constructEigenSystem` / `finishEigenSystem` directly if the sweep is sensitive.

**Exit criterion:** `groundState` uses `eigen` only; `toDenseMatrix` remains for tests;
DMRG ground energy unchanged within tolerance.

### Phase 5 — truncation, gauge transport, driver, validation
9. SVD-truncate the bond to χ and transport the gauge centre (cf. `TensorNetwork.move`,
   hmatrix `svdTall`; or `Math.TensorNetwork.svd`). ✅ **Typed 3-site path** in
   `TensorNetwork.DMRG.Fixed3`: `normalizeLeft` / `normalizeRight` use `getLinearMap` +
   categorical flatten (`siteForLeftSVD`); `prop_flatLeftSVDMatchesSiteMatrix` green.
   With typed bonds, χ-change means a bond-type change — handle via existentials or a
   fixed χ at the type level for now.
10. **MPS compression / bond-dimension reduction**: given a typed MPS, reduce a chosen
    internal bond from @b@ to a target @χ@ by canonicalising around that bond, SVD'ing the
    relevant bipartition, truncating singular values, and absorbing the leftover factor
    into the neighbouring site. In the typed setting this is smooth when @χ@ is known at
    compile time (`MPS p b1 b2 -> MPS p χ b2`, etc.); adaptive χ requires an existential
    result (`SomeMPS p`) or a fixed maximum χ with an effective rank. Keep the flattened
    `C (p³)` state as the oracle: truncation should minimise/track `||ψ - ψ_trunc||` and
    preserve the state exactly when @χ ≥ rank@.
11. Left→right→left sweep with energy-convergence stopping. ✅ `sweep` / `dmrg` in
    `TensorNetwork.DMRG.Fixed3`.
12. **Validate**: ground-state energy vs exact (TFIM) / ED for 3 sites; ⟨H²⟩−⟨H⟩²
    variance. ✅ TFIM ground energy vs `denseGroundEnergy` (`checkDMRG` in `test/Main.hs`).
    Remaining: ⟨H²⟩−⟨H⟩² variance; generalise beyond TFIM.

**Exit criterion for "near-term done":** DMRG on the typed 3-site MPS returns the correct
ground-state energy for the benchmark model to tolerance, with inner-product /
expectation-value property tests green against the `C (p³)` oracle.

---

## 4a. Typed MPS design (settled) + Hilbert-space hygiene

The substrate for the first DMRG is a **finite, typed-bond, 3-site** MPS. Decisions:

### Site representation & orientation (settled: transfer / contraction)
Each site is a linear map taking *incoming bond ⊗ physical* to *outgoing bond*:
- left   : `(C 1  ⊗ C p) +> C b1`   (≅ `C p +> C b1`)
- centre : `(C b1 ⊗ C p) +> C b2`
- right  : `(C b2 ⊗ C p) +> C 1`

Rationale: uniform bulk shape (clean N-site generalisation, §5a), natural left→right
transfer-matrix contraction, and environments are just partial contractions. Bonds are
typed `C b` (`KnownNat`), so bond-dimension mismatches are type errors — the deliberate
contrast with the deferred untyped-`FinSuppSeq` `MPSClever`. Use distinct `b1,b2` (honest
typing) rather than a single `b`.

### Conjugation (settled: per-site, explicit)
Measured conventions (memory `conjugation-conventions`): `<.>` on **`C n` is sesquilinear**
(correct) but on `FinSuppSeq`/`linear` `V`-types is **bilinear**; `adjoint` is the
**transpose, not the conjugate-transpose**. So:
- Form the bra by conjugating **each site tensor** with `vectorConjugate`; contract the
  conjugated bra against the ket using the ordinary bilinear ops. One conjugation point;
  scales to MPO contraction and environments.
- Never rely on `<.>`/`adjoint` to conjugate; never assume a bond `<.>` conjugates.
- Keep the flattened-vector overlap (`mpsToPhysical ψ <.> mpsToPhysical φ`, which uses
  `C n`'s correct `<.>`) as the **test oracle**, not the DMRG contraction path.

### Backend layout mismatch (blocking categorical path)

`TensorNetwork.MPS.Fixed3` has two layers:

| Layer | Role | Status |
|---|---|---|
| **Production** | `applySite`, `applyOpSite`, `mpsStateMap`/`mpsToFlat`, `transferStep`, `mpsInner`, `mpoTransferStep`, `mpsMPOInner`, `mpoApplyMPS` | **partial** — MPS + MPO site `$`, closed `mpoTransferStep` chain for `⟨ψ|H|φ⟩`, and `mpoApplyMPS` green; `mpoApplyFlat` still uses p⁶ element sum |
| **Reference / oracle** | `Fixed3.Reference`: `siteCoeff`, `mpsInnerReference`, `mpsToFlatReference` (basis sums) | works; used for QuickCheck oracles |

**Root cause:** the static `C n` backend stores a site map `(C bl ⊗ C p) +> C br` as a matrix of shape `bl × (br·p)` (bond-major rows, physical-minor columns within each outgoing-bond block). But `applyTensorLinMap` in `linearmap-hmatrix` (`COrphans.hs`) applies maps via `m #> flatten(t)`, which assumes a different indexing (`br·p == bl·p` when `bl ≠ br`). That is a **convention mismatch**, not a missing norm or a dagger issue.

**Do not fix with `unsafeCoerce`.** Coercing matrix types to force the manual contraction loop is a sign the typed API and storage layout are out of sync. The correct fix is upstream in `linearmap-family`, making storage, `applyTensorLinMap`, `recomposeContraLinMapTensor`, and `composeLinear` agree on one documented layout.

**Fix plan (ordered):**

1. ✅ **Document the canonical layout** — `Numeric.LinearAlgebra.Static.MPSLayout` in `linearmap-hmatrix`: row `lB`, column `r·p + s`.
2. ✅ **Fix `applyTensorLinMap`** (static case) — bond-major contraction in `COrphans` (no `unsafeCoerce`).
3. ✅ **Regression test in `linearmap-hmatrix`** — `MPSLayoutTests`: categorical `$` vs oracle for `bl,br ∈ {1,2,4}`.
4. ✅ **Categorical `applySite`** in `Fixed3` — `prop_applySiteMatchesCoeff` green.
5. ➡ **Fix bra pullback for `transferStep` (categorical path):** `siteDagger` types `C br +> (C bl ⊗ C p)` but `DualVector (C bl ⊗ C p) ≠ C bl ⊗ C p` at the type level; `toArray` (`flatten∘tr`) vs `applyLinear` (`reshape`) disagree on tensor codomains. Either (a) a typed identification `DualVector (Tensor s u v) ≅ LinearMap s u (DualVector v)` used in contraction primitives, or (b) `contractLinearMapAgainst` / bilinear pairing that does not require pretending the dual tensor *is* the primal tensor. `TensorNetwork.Dagger.hilbertFromDual` is the right *conceptual* locus. **Workaround in place:** `transferStep` is built via `recomposeLinMap` from `matrixTransferCoeff`; bra conjugation uses `conjugateSite` (entry-wise `cmap conjugate`), not `vectorConjugate`.
6. ✅ **Green `prop_innerMatchesFlat` / `prop_innerMatchesReference`** — Phase 2 done.
7. ✅ **Module hygiene:** `Fixed3.Internal` (types + coefficient helpers), `Fixed3.Reference` (basis-sum oracles). Remaining: replace dense `mpoToMatrix` p⁶ loops with matmul on flattened layouts.

### Still open (decide as they arise)
- **Gauge / canonical form** — no orthonormality is enforced yet; DMRG gauge transport
  (cf. `TensorNetwork.move`) and how χ-truncation changes a *typed* bond (existential vs
  fixed χ) — see Phase 5.9.
- **Typed compression API** — for the 3-site prototype, prefer explicit statically-known
  target dimensions first (e.g. `truncateLeftBond @χ`) so the result type records the new
  bond dimension. Once the algorithm chooses χ from singular values, introduce a small
  existential wrapper rather than pretending the dimension is statically known.
- **Legacy code** — the `V2/V3` paths in `TensorNetwork.DMRG.Concrete` use the wrong (bilinear)
  convention; treat as reference-only.

---

## 5. Medium-term: fold symmetry in *under* the same algorithm

The point of §3 is that this phase touches almost no algorithm code.

1. **Promote `FunctorExperiment` to a reusable symmetric-space library.**
   - Discharge the `unsafeCoerce` in `compose` (the "step 6" Hom-functoriality theorem
     `ComposeHomResult (HomSectorList a b) (HomSectorList b c) ~ HomSectorList a c`) via
     a singleton-recursive proof, and restore the `Category Intertwiner` instance.
   - Complete the `TensorSpace`/`FiniteDimensional`/`HilbertSpace` instances for the
     graded space (`ToC`), so a symmetric space is a drop-in `HilbertSpace`.
2. **Unify the two representation drafts.** `General.hs` (group-polymorphic, `undefined`)
   and `FunctorExperiment.hs` (U(1), working) should converge on one `Sector`-style
   class. Use the TensorKit interface as the target shape (see §6).
3. **Run the §4 DMRG on symmetric spaces.** First generalise the concrete `C n` local
   space to an abstract `FiniteDimensional`/`HilbertSpace` variable (a cheap, type-driven
   refactor — §3), then instantiate it at a U(1)-graded space.
4. **Named legs (`ItensorTyped`)** become the ergonomic surface for building MPO/MPS:
   implement the two stubs `permute` (swaps + associators) and `rawContract`
   (categorical evaluation) on top of `linearmap-category`'s `transposeTensor`/`⊗`.
   This is independent of symmetry and could even slot into Phase 1–2.
5. **MPS-as-vector-space (`TensorNetwork.MPS.FinSupp3`)** generalises to symmetric MPS, enabling
   state addition / tangent vectors — the entry point to TDVP and excited-state methods.
   The categorical / inner-product / local-solve layer for this representation is planned
   in §5b.

### 5a. From the 3-site typed MPS to N sites (and growable bonds)
Generalise the fixed 3-site typed MPS (§4a) to arbitrary length: a sequence of uniform
bulk tensors `(C bᵢ ⊗ C p) +> C bᵢ₊₁` plus boundary caps, preserving the map-to-physical
oracle, the inner-product/dual definitions, and the DMRG sweep. Two sub-threads:
- **Length** — list/vector of sites; existentially-typed or runtime-checked bonds so the
  chain length and per-bond χ aren't fixed at compile time.
- **Growable bonds / state addition** — revisit `TensorNetwork.MPS.FinSupp3.MPSClever`'s `FinSuppSeq` bond
  and its `VectorSpace` instance (addition commutes with flattening) for adaptive χ and
  tangent-space methods — *after* fixing its bilinear-bond conjugation (memory
  `conjugation-conventions`). This is where the deferred D2 alternative comes back.
- **Untyped/adaptive compression** — in the `FinSuppSeq` bond representation, bond
  reduction can be expressed as a runtime operation: compute the SVD rank/truncation
  threshold, rewrite the finite-support bond vectors to the retained support, and return
  another `MPS vp` without changing the Haskell type. This is the natural home for truly
  adaptive χ once the typed prototype has fixed the conventions.
This turns the 3-site proof-of-concept into a usable finite-system DMRG.

### 5b. FinSuppSeq MPS: categorical layer, inner product, effective-`H` eigensolve

`TensorNetwork.MPS.FinSupp3` is the growable-bond, runtime-χ counterpart to the typed
`Fixed3` prototype. It already has:

- `MPS vp` with `FinSuppSeq` bonds and a `VectorSpace` instance (`addMPS` grows χ);
- a flattening functor on objects: `mpsToFlat :: MPS vp -> C (vp³)` (and `mpsToPhysical3`);
- a canonical physical basis (`HasBasis` indexed by `Physical3 vp`) with round-trip
  properties (`prop_addThenFlatten`, `canonicalMPS`, `mpsFromFlat`).

What is **not** there yet: MPOs, inner products, the categorical API, environments /
effective Hamiltonians, or a local ground-state solve. The three workstreams below mirror
the typed pipeline (§4 Phases 2–4) but must cope with runtime bond dimension and the
`FinSuppSeq` bilinear-conjugation hazard (§4a).

**Orientation note.** FinSupp3 sites are *not* in transfer orientation:

| site | FinSupp3 (`FinSupp3.hs`) | Fixed3 (transfer) |
|---|---|---|
| left | `C vp +> Bond` | `(C 1 ⊗ C p) +> C b1` |
| centre | `Bond +> (C vp ⊗ Bond)` | `(C b1 ⊗ C p) +> C b2` |
| right | `Bond +> C vp` | `(C b2 ⊗ C p) +> C 1` |

The plans below keep the FinSupp3 layout (it matches the existing flattening /
addition code). A later unification pass could re-express both representations as
instances of one `Site bl p br` indexed API — not a blocker for §5b.

---

#### 5b-i. Category: MPS objects, MPO morphisms, flattening functor

**Goal.** A small categorical layer in which tensor-network states and operators are
first-class morphisms, with a functor to the flat physical Hilbert space that validates
all contractions.

**Objects.** `MPS vp` — a state in the 3-site physical space, variationally parameterised
by growable virtual bonds.

**Morphisms.** `MPO vp` (new type, parallel to `Fixed3.MPO`):

```haskell
data MPO vp = MPO
  { leftMPO  :: C vp +> (Bond ⊗ Bond)          -- or fused bond-pair type
  , centerMPO :: Bond +> (C vp ⊗ Bond ⊗ Bond) -- MPO leg ⊗ bond leg
  , rightMPO :: Bond +> (C vp +> Bond)        -- shape TBD to match contraction
  }
```

(Exact leg fusion for the MPO virtual bonds must be settled when implementing
`mpoTransferStep`; mirror the bra/ket environment types from `Fixed3` but with `Bond`
instead of `C b`.)

**Identity & composition.**
- `identityMPO :: MPS vp -> MPO vp` (or parametric in `vp` only) such that
  `mpoApplyMPS identityMPO ψ` preserves `mpsToFlat ψ`.
- `composeMPO :: MPO vp -> MPO vp -> MPO vp` realising operator product on the physical
  space (bond fusion along the MPO column, analogous to `Fixed3`'s fused `w·b` bonds).

**Categorical instances (target).**
- A category `Phys` with objects `Physical3 vp` (or `C (vp³)`) and morphisms `v +> w`.
- A category `TN` with objects `MPS vp` and morphisms `MPO vp`, with composition
  `composeMPO` and identity `identityMPO`.
- A functor `Flatten :: TN -> Phys`:
  - on objects: `mpsToFlat` (exists);
  - on morphisms: `mpoToFlat :: MPO vp -> C (vp³) +> C (vp³)` via closed transfer
    contraction (no `p⁶` basis sum — categorical `mpoTransferStep` chain, as in
    `Fixed3`).

**Key operations to implement (ordered).**

1. `transferStep` / `foldTransferInner` for the FinSupp3 site orientation (bra site
   conjugated per-site; environment `Bond +> Bond`).
2. `mpoTransferStep` with typed environments `Bond +> (Bond ⊗ Bond)` (bra bond ↦ MPO ⊗
   ket bond).
3. `mpsMPOInner`, `mpoApplyMPS`, `mpoToFlat`.
4. **Reference module** `FinSupp3.Reference` (basis-sum oracles, mirroring
   `Fixed3.Reference`) for QuickCheck.

**Functoriality contract (QuickCheck).**

- `mpoToFlat (composeMPO h1 h2)` ≈ `mpoToFlat h1 . mpoToFlat h2` (up to tolerance).
- `mpsToFlat (mpoApplyMPS h ψ)` ≈ `mpoToFlat h $ mpsToFlat ψ`.
- `mpsMPOInner ψ h φ` ≈ `mpsToFlat ψ <.> (mpoToFlat h $ mpsToFlat φ)` (flat oracle uses
  `C n`'s sesquilinear `<.>`).
- `mpsMPOInner ψ (identityMPO @vp) φ === mpsInner ψ φ` once §5b-ii is in place.

**Exit criterion.** Categorical contractions green against `FinSupp3.Reference` and flat
`C (vp³)` oracles; identity/composition laws checked.

---

#### 5b-ii. `InnerSpace` for `MPS vp` (in the vein of `Fixed3.mpsInner`)

**Goal.** An `InnerSpace (MPS vp)` instance whose `<.>` agrees with the flat physical
inner product, enabling norms, Hilbert-space reasoning, and (later) variational
optimisation on the MPS manifold without flattening.

**Design (follow §4a conjugation discipline).**

1. `mpsConjugate :: MPS vp -> MPS vp` — `vectorConjugate` on each site map / bond
   tensor row; **never** rely on `FinSuppSeq`'s bilinear `<.>` or `adjoint` for
   conjugation.
2. `transferStep` — one left-to-right update contracting bra/ket bonds (FinSupp3
   orientation); bra site passed through `mpsConjugate` internally or as a separate
   `Site` wrapper.
3. `mpsInner :: MPS vp -> MPS vp -> Complex Double` — fold `transferStep` from a
   `unitBond` / identity environment on the left, close with trace on the right bond
   (centre-right contraction for the 3-site chain).
4. `instance InnerSpace (MPS vp) where (<.>) = mpsInner` (and `(<.>^)` if needed for
   the linearmap API).

**Tests (mirror `Fixed3` Phase 2).**

- `prop_innerMatchesFlat`: `mpsInner ψ φ === mpsToFlat ψ <.> mpsToFlat φ`.
- Conjugate symmetry: `mpsInner ψ φ === conjugate (mpsInner φ ψ)`.
- Positivity: `realPart (mpsInner ψ ψ) >= 0`.
- Compatibility with addition: sesquilinearity in each argument (or bilinearity + explicit
  conjugate in one slot — pick one convention and test against the flat oracle).
- `mpsNorm = sqrt ∘ realPart ∘ flip mpsInner` (self-overlap).

**Dependency.** Shares `transferStep` with §5b-i; implement inner product immediately
after the bare transfer machinery, before MPO transfer steps.

**Exit criterion.** All inner-product properties green; `InnerSpace` instance in
`FinSupp3.hs` (or `FinSupp3.Inner` if the module grows).

---

#### 5b-iii. Effective Hamiltonian & eigensolving (exploration)

**Goal.** Port the DMRG local-update semantics from `TensorNetwork.DMRG.Fixed3` to
FinSupp3: build `Heff` on the centre site by contracting MPO with left/right
environments, then solve for the ground state of `Heff` in the centre's map space.

**Centre type.** `Centre vp = Bond +> (C vp ⊗ Bond)` — the variational tensor at the
active site in FinSupp3 orientation.

**Port from Fixed3 (adapt bond types).**

1. **Environments** — generalise `TensorNetwork.DMRG.Env` to `Bond` environments
   (`LeftEnv`, `RightEnv`, `extendLeft` / `extendRight`, sweep updates). Reuse the
   categorical `mpoTransferStep` from §5b-i.
2. **`effectiveH`** — same formula as `Fixed3.effectiveH`:
   `Heff x = R ∘ opWire op x ∘ (L ⊗^ id_p)` (with FinSupp3-specific `opWire` wiring).
3. **Verification** — `prop_effectiveHMatchesInner`:
   `siteLin y <.> (heff $ siteLin x) === mpsMPOInner (ψ_y) mpo (ψ_x)` with frozen
   neighbours; `prop_effectiveHHermitian` on TFIM.

**Eigensolving — three tiers (explore in order).**

| Tier | Method | When it applies | Blocker |
|---|---|---|---|
| **A — dense oracle** | Truncate active χ, flatten centre to `C (χ·vp·χ)`, `eigSH` | Always (regression) | None; χ is runtime |
| **B — typed dense** | Wrap active support in `C chi` when `chi` is known at compile time (tests) | Small χ in QuickCheck | Need padding/truncation helpers |
| **C — matrix-free Krylov** | `GroundState.groundStateKrylovMap hilbertSchmidtNorm [seed] heff` | Production path | `InnerTensorSpace` for `Sequence` (dual of `FinSuppSeq`) in `linearmap-family`; centre may lack `FiniteDimensional` |

**Tier A (first milestone).**

- `activeCentreDim :: Centre vp -> Int` — χ_in × vp × χ_out from `activeDimBond` on
  domain/codomain images.
- `centreToDenseMatrix :: Centre vp -> Heff -> Matrix` — flatten map-space endo in a
  documented HS basis (reuse `GroundState.toDenseMatrix` idea with runtime-sized basis
  built from `getLinearMap` + physical indices).
- `solveCentreDense :: Heff -> Centre vp` — lowest eigenvector, re-embed as `Centre vp`.
- Property: dense solve matches `mpsMPOInner` Rayleigh quotient on random centres.

**Tier C (target; depends on §4b + upstream).**

- Add `InnerTensorSpace (Sequence …)` (or `FinSuppSeq`) in `linearmap-family` so
  `Bond +> (C vp ⊗ Bond)` inherits `InnerSpace` / `LSpace` for Krylov (`GroundState.hs`
  already notes this).
- Seed Krylov with the current centre tensor (`groundStateKrylovMap`).
- Cross-validate against Tier A at χ ≤ 4.

**DMRG driver (out of scope for first pass).** A full `dmrg` on `FinSupp3.MPS` also needs
gauge transport / SVD truncation on `FinSuppSeq` bonds (§5a adaptive compression). §5b-iii
stops at a **single-site local solve** wired into a manual or scripted sweep; the sweep
driver stays in §5a.

**Exit criterion.** `effectiveH` matches full-network inner product; Hermiticity on TFIM;
Tier A dense solve matches flat oracle; Tier C explored or upstream blocker documented
with a minimal `linearmap-family` PR plan.

---

## 6. Long-term: non-abelian (SU(2)) and the full categorical structure

This is the part that most distinguishes the project from "a dense TN library", and
the hardest. From the TensorKit map:

1. **A `Sector` type class** = the fusion-category interface:
   `one`, `dual`, `⊗`/fusion outputs, `Nsymbol` (fusion multiplicity), `Fsymbol`
   (associator / 6j), `Rsymbol` (braiding), `frobeniusSchur`, `twist`, `qdim`.
   Dispatch on `FusionStyle ∈ {Unique, Simple, Generic}` and
   `BraidingStyle ∈ {Bosonic, Fermionic, Anyonic}` (type-level tags). Make `F`/`R`
   return arrays so `GenericFusion` (multiplicity > 1) is expressible.
2. **Fusion trees as GADTs** indexed by (uncoupled sectors, coupled sector, inner lines,
   vertex labels, isdual flags). Well-formedness ("coupled ∈ allowed fusions") partly
   enforced at the type level — a natural Haskell strength.
3. **Tree manipulation**: `braid` (R-symbols), `repartition`/line-bending
   (Frobenius–Schur + √dim), F-moves (associators). Permutation of tensor legs = a
   linear combination of trees, *not* a data move. This is the subtle core.
4. **SU(2) specifically** needs Wigner 6j (`Fsymbol`) and spin-exchange phases
   (`Rsymbol`) — `SU2.hs` currently has only the fusion rule `|j₁−j₂|…j₁+j₂`.
5. **Coherence as tests**: pentagon (F) and hexagon (F,R) equations as a QuickCheck
   contract for any `Sector` instance — mirroring TensorKit's test utilities.

A symmetric MPS tensor is then a rank-3 `TensorMap` `Vₗ ⊗ P → Vᵣ` over graded spaces;
blockwise SVD with cross-block truncation gives symmetry-adapted bond truncation. The
§4 DMRG, if generic, runs on anyonic/non-abelian chains with no algorithmic change —
the headline payoff.

---

## 7. Cross-cutting decisions

- **D1 — Field.** ✅ **Complex** (`Complex Double`). Matches the existing code and the
  physics. Native `svd` in `Math.TensorNetwork` remains real-only; complex local solve
  uses dense `eigSH` for now, migrating to `eigen` with a custom HS `Norm` (D3, §4b).
- **D2 — MPS representation.** ✅ **Typed `C b` bonds, finite 3-site, transfer
  orientation, per-site explicit conjugation** (full design in §4a). The untyped
  growable-`FinSuppSeq` `MPSClever` (vector-space instance) is **deferred to §5a** — kept
  for state addition / adaptive χ later, but it carries the bilinear-bond conjugation
  hazard and gives up type-level bond checking, so it's not the first-DMRG substrate.
- **D3 — Eigensolver.** ✅ **Interim: dense hmatrix `eigSH`** (`GroundState.hs`) —
  materialise via `toDenseMatrix`, solve with hmatrix. Generic over map-space endos
  (`Heff :: Centre +> Centre`); no flattening to `C n`. ➡ **Target: matrix-free
  `eigen`** with a custom Hilbert–Schmidt `Norm` (§4b). `toDenseMatrix` stays as a test
  oracle; the solve path stops building dense operator matrices.
- **D4 — Fork strategy (open).** Candidates for `linearmap-family`: Hilbert–Schmidt /
  Frobenius `Norm` from `InnerSpace`; complex spectral helpers; `DaggerCategory` (already
  sketched in `Math.TensorNetwork`). Physics models and the DMRG driver stay in
  `quantum`.

---

## 8. Where Haskell fits naturally (and where it fights back)

**Natural fits**
- *Fusion-category interface as a type class with associated types/data* — arguably
  cleaner than Julia traits + multiple dispatch; instances are the categories.
- *Fusion trees / leg lists as GADTs + DataKinds* — ill-formed trees and illegal
  contractions become type errors (cf. `ItensorTyped`'s type-checked leg algebra and
  `FunctorExperiment`'s Schur-blocked hom indexed by charge).
- *The monoidal/dagger/braided structure as actual `Category` instances* — we already
  build on `constrained-categories`; a symmetric tensor category becomes a literal
  `Monoidal`/`Braided`/`Dagger` instance (there's a `DaggerCategory` stub to grow).
- *States as a `VectorSpace`* (`TensorNetwork.MPS.FinSupp3`) — makes tangent spaces / TDVP / excited-state
  subspaces first-class; addition-commutes-with-flattening is already property-tested.
- *Property-testing coherence laws* (pentagon/hexagon, gauge invariance) with QuickCheck.
- *Basis independence* — `linearmap-category`'s entire reason for being; aligns exactly
  with the "no magnetic-index dependence" (Wigner–Eckart) content of symmetric tensors.

**Where it fights back (budget for these)**
- Type-family reduction on *abstract* reps doesn't compute (hence the `unsafeCoerce` in
  `FunctorExperiment.compose`); singleton-recursive proofs are the escape hatch but cost
  effort.
- `TensorSpace`/`Semimanifold` instances are large and full of `undefined` stubs to
  fill (`Experiment2`, `FunctorExperiment`) — real work to make total.
- The real-scalar assumption baked into the spectral tooling (D1).
- GHC error messages over this much type-level machinery are punishing; lean on
  `tricorder` and small, well-typed milestones.

---

## 9. Immediate next actions

D1–D3 are resolved (§7). Concrete sequence (all on the **typed 3-site MPS**, §4/§4a):

1. ✅ **Local ground-state solver** — `GroundState.hs`: `groundState ::
   (FiniteDimensional v, HilbertSpace v, Scalar v ~ Complex Double) => (v +> v) ->
   (Double, v)` via dense hmatrix `eigSH`. Generic over `v` (incl. map-space endos).
   Verified on `diag(3,1,2)` → `1.0`, spectrum `[1,2,3]`. Full build + tests green.
2. ✅ **Typed 3-site MPS type + map-to-physical** (Phase 1) — `TensorNetwork.MPS.Fixed3`:
   `data MPS p b1 b2` (transfer orientation, typed bonds) + categorical `mpsStateMap` /
   `mpsToFlat :: MPS p b1 b2 -> C (p*p*p)` (bond threading via `applySite`, no p³ basis sum).
   Index order `(s₁·p+s₂)·p+s₃` matches `TensorNetwork.MPS.FinSupp3.mpsToFlat`
   (`prop_mpsToFlatMatchesReference` green).
3. ✅ **Inner product / norm / dual** (Phase 2) — `mpsConjugate` (`conjugateSite`),
   `transferStep`, and `mpsInner` are green against flattened and basis oracles
   (`prop_innerMatchesFlat`, `prop_innerMatchesReference`, conjugate-symmetry, norm).
   Categorical bra pullback (§4a step 5) remains future work; current `transferStep`
   uses explicit matrix coefficients.
4. ✅ **MPO + `⟨ψ|H|φ⟩` contraction** (Phase 3) — categorical `applyOpSite`,
   `mpoElement`, `mpoApplyMPS`, `mpoTransferStep`, and `mpsMPOInner` green; TFIM MPO in
   `TensorNetwork.DMRG.Fixed3`.
5. ✅ **Effective Hamiltonian + local solve** (Phase 4) — `effectiveH`, `solveCentre` /
   `groundState`; `prop_effectiveHMatchesInner`, `prop_effectiveHHermitian` green.
6. ✅ **Sweep + validation** (Phase 5) — `sweep`, `dmrg`, SVD gauge transport via
   `getLinearMap`; TFIM ground energy vs `denseGroundEnergy` green.
7. ➡ **Migrate `groundState` to `eigen`** (Phase 4b) — Hilbert–Schmidt `Norm`; keep
   `toDenseMatrix` as oracle; re-run DMRG validation.
8. ➡ **FinSuppSeq MPS layer** (§5b) — categorical MPS/MPO + `Flatten` functor (5b-i),
   `InnerSpace` (5b-ii), effective-`H` + dense local solve (5b-iii Tier A); Krylov (Tier C)
   blocked on `InnerTensorSpace` for `FinSuppSeq` dual in `linearmap-family`.

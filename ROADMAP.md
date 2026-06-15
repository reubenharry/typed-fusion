# Roadmap: a symmetry-aware, basis-independent DMRG in Haskell

*Status: living document. Last updated 2026-06-07.*

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
| MPS/DMRG algorithm layer (à la MPSKit) | DMRG | `TensorNetwork.DMRG.Concrete` | dense, complex-field; `move` (gauge) partly works via hmatrix SVD; `solveAtSite` effective-Hamiltonian + `eigen` is `undefined`/blocked |
| Symmetric MPS as a vector space (tangent space, addition of states) | vector space of MPS | `TensorNetwork.MPS.FinSupp3` | `MPSClever` is a genuine `VectorSpace`; growable bond via `FinSuppSeq`; QuickCheck: addition commutes with flattening |

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
- `eigen :: (FiniteDimensional v, HilbertSpace v, IEEE (Scalar v)) => (v+>v) -> [(Scalar v, v)]`
- `constructEigenSystem` / `roughEigenSystem` — matrix-free Krylov eigenbasis builder
  (this is the DMRG-relevant one: it only applies `f`, never materialises a matrix).
- `Math.TensorNetwork.svd :: (Scalar v ~ Double, Scalar w ~ Double, HilbertSpace v,
  HilbertSpace w, Monad m) => InitialVectors m v -> (v -+> w) -> Int -> m [SVDPendants v w]`
  — basis-independent iterative SVD (in `linearmap-family`, which we own).

**The gap (decision-forcing):** every spectral primitive above is **real-scalar only**
— `IEEE (Scalar v)` / `RealFloat` / `Scalar ~ Double`. But `TensorNetwork.DMRG.Concrete`
and `TensorNetwork.MPS.FinSupp3` work over `Field = Complex Double`. `IEEE (Complex Double)` does not hold,
so `eigen euclideanNorm heff` over a complex space *cannot typecheck* — this is the
concrete reason `solveAtSite` is stuck. See Decision D1.

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
- **D3 eigensolver**: ✅ **dense hmatrix `eigSH`** for now (`GroundState.hs`) — the easy
  route: materialise the local operator `C n +> C n` as a dense complex matrix (by
  applying it to the standard basis) and use hmatrix's Hermitian solver. Verified on
  `diag(3,1,2)` → ground energy `1.0`, spectrum `[1,2,3]`. A matrix-free / basis-
  independent Lanczos can replace it later (and move upstream into `linearmap-family`).

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
8. Solve the lowest eigenpair with `GroundState.groundState` (✅ done, D3). First confirm
   `Heff` is genuinely (conjugate-)Hermitian — `groundState` symmetrises, so a
   non-Hermitian `Heff` would be silently masked; test `Heff` Hermiticity directly.

### Phase 5 — truncation, gauge transport, driver, validation
9. SVD-truncate the bond to χ and transport the gauge centre (cf. `TensorNetwork.move`,
   hmatrix `svdTall`; or `Math.TensorNetwork.svd`). With typed bonds, χ-change means a
   bond-type change — handle via existentials or a fixed χ at the type level for now.
10. **MPS compression / bond-dimension reduction**: given a typed MPS, reduce a chosen
    internal bond from @b@ to a target @χ@ by canonicalising around that bond, SVD'ing the
    relevant bipartition, truncating singular values, and absorbing the leftover factor
    into the neighbouring site. In the typed setting this is smooth when @χ@ is known at
    compile time (`MPS p b1 b2 -> MPS p χ b2`, etc.); adaptive χ requires an existential
    result (`SomeMPS p`) or a fixed maximum χ with an effective rank. Keep the flattened
    `C (p³)` state as the oracle: truncation should minimise/track `||ψ - ψ_trunc||` and
    preserve the state exactly when @χ ≥ rank@.
11. Left→right→left sweep with energy-convergence stopping.
12. **Validate**: ground-state energy vs exact (TFIM) / ED for 3 sites; ⟨H²⟩−⟨H⟩²
    variance. Add as QuickCheck/golden tests next to the existing `TensorNetwork.MPS.FinSupp3` properties.

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
  physics; cost is that native `eigen`/`svd` (real-only) can't be used directly →
  drives D3.
- **D2 — MPS representation.** ✅ **Typed `C b` bonds, finite 3-site, transfer
  orientation, per-site explicit conjugation** (full design in §4a). The untyped
  growable-`FinSuppSeq` `MPSClever` (vector-space instance) is **deferred to §5a** — kept
  for state addition / adaptive χ later, but it carries the bilinear-bond conjugation
  hazard and gives up type-level bond checking, so it's not the first-DMRG substrate.
- **D3 — Eigensolver.** ✅ **Dense hmatrix `eigSH`** (`GroundState.hs`). Pragmatic and
  done: build the operator's dense matrix in the canonical `FiniteDimensional` basis
  (entry `e_i <.> f e_j`; basis vectors are real so this is convention-free), solve with
  hmatrix. `groundState :: (FiniteDimensional v, HilbertSpace v, Scalar v ~ Complex
  Double) => (v +> v) -> (Double, v)` is **generic over `v`** — so `Heff` may be an
  endomorphism on a *map-space* (e.g. the MPS centre `(C b ⊗ C p) +> C b`); no flattening
  to `C n` needed, since linear maps are first-class `FiniteDimensional` spaces. Not
  basis-independent and materialises the operator; a matrix-free Lanczos can replace it
  later (good upstream `linearmap-family` contribution).
- **D4 — Fork strategy (open).** With D3 going upstream, decide what else belongs in
  `linearmap-family` (a complex spectral module; a `DaggerCategory` class — already
  sketched in `Math.TensorNetwork`) vs in `quantum`. Default: spectral/categorical
  primitives upstream, physics models and the DMRG driver in `quantum`.

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
4. ✅/➡ **MPO + `⟨ψ|H|φ⟩` contraction** (Phase 3) — categorical `applyOpSite`,
   `mpoElement`, `mpoApplyMPS`, `mpoTransferStep`, and `mpsMPOInner` (closed transfer chain)
   are green against basis, flat, and identity-MPO oracles. Next: add benchmark MPO (TFIM or Heisenberg),
   then **`Heff` + `groundState`** (Phase 4), then **sweep + energy validation** vs
   ED/exact (Phase 5).

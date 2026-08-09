# Roadmap: a symmetry-aware, basis-independent DMRG in Haskell

*Status: living document. Last updated 2026-08-02.*

## Current focus (2026-08)

**Substrate choice:** stay on **typed `C χ` bonds** (`TensorNetwork.MPS.General` /
`TensorNetwork.DMRG.Fixed`). The growable `FinSuppSeq` / `MPSClever` branch
(§5b) is **paused** — revisit only when typed-bond DMRG is solid and we need
state addition / adaptive χ / tangent spaces in earnest.

**Near-term work (ordered):**

1. **Categorical substrate cost (open question)** — N=8 ~35s is not explained by
   “forgot to zipper envs” alone. Profile evidence (`dmrg-profile-nsite`,
   `dmrg-time-probe`, `mps-inner-micro`) says the **morphism backend** pays
   orders of magnitude more than BLAS for χ≈3 work:
   - every `.` densifies via **columnwise `applyLinear`+`toArray`** (`COrphans.composeLinear`; densify-gemm disabled after nested DualVector associativity bugs);
   - every `⊗^` is `tensorOfMaps` = densify `fmap ∘ transpose ∘ fmap ∘ transpose` with **per-column `fmapTensor`** (matmul path commented out);
   - `opWire` / `transferMPOBulkSite` rebuild that braid on every env step / Heff sample;
   - `arr (LinearFunction heff)` densifies by sampling the full categorical apply on each basis vector (~166ms for a 3-site bulk Heff) — after that, matvecs are free.
   **Minimal MRE:** `cabal run tensor-of-maps-mre` — at `(χ,p)=(3,2)`,
   `fuse∘(f⊗^g)∘split` **agrees exactly** with `HM.kronecker`, but categorical
   densify is **~30×** slower. Goal: keep the categorical `⊗^` spec; implement
   Static `C` via hmatrix Kronecker (then gemm `composeLinear` once flat layout
   is safe). Algorithmic env zipper / fewer `energy` calls remain necessary but
   secondary until this tax drops.
2. **Incremental environments** — every local solve rebuilds L/R MPO envs from
   scratch (`leftEnvBeforeBulk` / `rightEnvAfterBulk`). Zipper them through the
   sweep (standard DMRG bookkeeping). Big win, but does not answer #1.
3. **SVD with intertwiners** — eigensolve on symmetric (intertwiner) centres
   should already typecheck; the open piece is **blockwise / symmetry-adapted
   SVD** for gauge transport and truncation so DMRG can run on graded spaces
   without leaving the typed-bond path.
4. **Two-site DMRG** — local update on a fused two-site centre, SVD truncate
   back to χ, grow/adapt bond dimension within the typed (or existential-χ)
   setting. Single-site N-site zipper is already green.
5. **Explore `manifold-core` for TDVP** — inventory what
   `Semimanifold` / `PseudoAffine` / charts give us for the MPS manifold, and
   what instances / tangent-space plumbing we still need.
6. **DMRG as imaginary-time TDVP** — once the manifold picture is clearer,
   treat single-/two-site DMRG updates as imaginary-time TDVP steps and see
   how much of the driver unifies.

Historical near-term phases (§4–§4b) and the FinSuppSeq plan (§5b) remain
below as archive / deferred detail; they are not the active queue.

---

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
| MPS/DMRG algorithm layer (à la MPSKit) | DMRG | `TensorNetwork.MPS.General`, `TensorNetwork.DMRG.Fixed` | **N-site typed-bond single-site DMRG green** (zipper sweep, Lanczos local solve, TFIM); performance still poor (~35s for N=8); two-site + intertwiner SVD next; `Concrete` is legacy |
| Symmetric MPS as a vector space (tangent space, addition of states) | vector space of MPS | `TensorNetwork.MPS.FinSupp` | **Paused.** `VectorSpace` + flatten / canonical section green; categorical / inner / Heff layer (§5b) not pursued until typed path is done |

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

## 4. Near-term: dense DMRG, natively in `linearmap-category` (largely done)

> **Status (2026-08):** Single-site typed N-site DMRG is green. Active work has
> moved to **Current focus** (performance, intertwiner SVD, two-site, TDVP).
> This section is retained as the completed design trail.

Goal (achieved for single-site): an end-to-end, sweeping DMRG that finds the ground
state of a known 1-D model, written in `+>`/`⊗`/`TensorSpace` vocabulary, validated
against an exact answer. No symmetry yet. Two-site is still open (Current focus #3).

### Phase 0 — substrate decisions (RESOLVED 2026-06-07; see §7)
- **D1 field**: ✅ **complex** (`Complex Double`).
- **D2 MPS representation**: ✅ **typed `C χ` bonds** (transfer orientation, per-site
  `vectorConjugate`). N-site generalisation lives in `TensorNetwork.MPS.General`.
  Growable `FinSuppSeq`/`MPSClever` is **paused** (§5b), not medium-term active work.
- **D3 eigensolver**: ✅ **Lanczos on centres** (`Lanczos.groundStateLanczos`); dense
  `eigSH` retained as oracle. §4b's `eigen` migration is no longer the DMRG blocker.

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
   `TensorNetwork.MPS.Fixed`); build a concrete benchmark model — **transverse-field Ising**
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

### Phase 4b — migrate local solve to matrix-free `eigen` (superseded)

> **Superseded (2026-08):** DMRG centres use `Lanczos.groundStateLanczos` instead.
> Keep the notes below if we ever want linearmap `eigen` as an alternative; do not
> treat this as an active milestone.

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
   `TensorNetwork.DMRG.Fixed`: `normalizeLeft` / `normalizeRight` use `getLinearMap` +
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
    `TensorNetwork.DMRG.Fixed`.
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

### Backend layout mismatch (blocking honest tensor-domain maps)

**Status (2026-07):** `MPSLayout` removed (it was docs + an `unsafeCoerce` shim, not a fix).
Static×Static `composeLinear` now packs via columnwise `applyLinear` (associativity /
Heff↔Inner green on the TFIM witness). Tensor-domain **storage is still inconsistent**.

#### What the class does *not* specify

`TensorSpace` / `LinearSpace` only require an associated `TensorProduct` and laws.
For `C n`, the instance chooses leaf packing (typically `M (dim w) n`). Index order
inside that `M` is an **instance convention** and must be shared by every writer/reader.

#### Inventory — static `(C n ⊗ u) +> w` (and `R` mirrors)

| Writer / reader | File | Payload shape assumed | Notes |
|---|---|---|---|
| `tensorProduct` | `COrphans` | tensor as `M (dim u) n` (`outer (toArray u) v`) | columns = left (`C n`) basis |
| `flatten` in `applyTensorLinMap` | `COrphans` | domain vec = column-major of that `M` → index `lB·dim(u)+s` | |
| `recomposeContraLinMapTensor` | `COrphans` | **nested** `(dim u · dim w) × n` via `generateColsC` | Confirmed by tests: `(C 2⊗C 2)+>C br` payload is `(p·br)×bl` |
| `tensorId` | `COrphans` | nested-sized: `(C 2⊗C 2)+>(C 2⊗C 2)` is **8×2**, not flat 4×4 | `reshape n` of `ident (n·dim w)` |
| `applyTensorLinMap` | `COrphans` / `Orphans` | accepts **flat** `dim w × (n·dim u)` *or* nested `(dim u·dim w)×n`, converts then `#>` | Shape sniff. **Apply↔image oracle is green** for maps from `recomposeLinMap` (nested path). Flat coerce shims are what break. |
| `composeLinear` (Static×Static) | `COrphans` | columnwise apply + pack | fixed; no longer densify-`toArray` |
| `siteLinFromRows` / … | quantum `LinmapStorage` | **flat** via **`unsafeCoerce`** | Disagrees with categorical writers; remove after flat is canonical *or* stop writing flat |

**Regression suite:** `TensorDomainStorageTests` in `linearmap-hmatrix` (shape props red; apply-oracle props green).

Same dual-layout sniff exists on the `R` path in `Orphans.hs`.

#### Target (agreed direction)

One canonical static layout for `(C n ⊗ u) +> w`:

- **Flat matvec:** `M (dim w) (n · dim u)`
- **Column `i = lB · dim(u) + s`** (same as `enumerateSubBasis` on the tensor and as `flatten` of `tensorProduct`)

Then: `recomposeContraLinMapTensor` / `tensorId` / decompose write that shape; `applyTensorLinMap` only `#>`s (no sniff); quantum `LinmapStorage` drops `unsafeCoerce` and uses ordinary `LinearMap (create …)`.

#### Regression tests to land (in `linearmap-hmatrix`, basis OK here)

1. **Shape of categorical constructors** — `extract` of `recomposeLinMap` / `recomposeContraLinMapTensor` / `tensorId` for `(C bl ⊗ C p) +> C br` reports `rows = br`, `cols = bl·p` (and the `R` analogue). Fails today on nested writers.
2. **Apply = curry path** — `f $ (v ⊗ u) === (uncurry / applyLinear chain)` for random static maps; no coerce.
3. **Apply vs coefficient oracle** (test-local only) — for `f` built by `recomposeLinMap` from images `e_(lB,s) ↦ out`, check `(f $ (bond ⊗ phys))[r] = Σ_{lB,s} out_(lB,s)[r] · bond[lB] · phys[s]`. Covers `bl≠br` and `bl>1`.
4. **Round-trip** — `decomposeLinMap ∘ recomposeLinMap = id` on images for tensor-domain maps.
5. **Keep** — `ComposeTensorDomainTests` + quantum `heff-compose-mre` (associativity / Heff↔Inner).

#### Fix order

1. ➡ Inventory + tests above (red on shape / apply until writers agree).
2. ➡ Make `recomposeContraLinMapTensor` (and `tensorId`) emit flat matvec; delete shape sniff in `applyTensorLinMap`.
3. ➡ Mirror on `R` `Orphans`.
4. ➡ Remove `unsafeCoerce` from quantum `LinmapStorage` once flat create typechecks as the real payload.
5. ➡ Bra / `siteDagger` dual-tensor identification (former item 5 below) only after apply/storage agree.

**Still open after layout (unchanged):**

- **Bra pullback for `transferStep`:** `siteDagger` types `C br +> (C bl ⊗ C p)` but `DualVector (C bl ⊗ C p) ≠ C bl ⊗ C p` at the type level; needs a typed dual identification or a pairing that does not pretend dual = primal. `TensorNetwork.Dagger.hilbertFromDual` is the conceptual locus.
- **Module hygiene:** `Fixed.Reference` oracles stay basis-sum; production stays categorical. Dense `mpoToMatrix` p⁶ loops still to replace with matmul on flattened layouts where appropriate.

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
5. **MPS manifold / TDVP** — explore `manifold-core` (`Semimanifold`, charts) on the
   typed MPS, then imaginary-time TDVP as a unifying view of DMRG (Current focus
   items 4–5). Growable `FinSuppSeq` MPS-as-`VectorSpace` (§5b) stays paused until
   that exploration says we need it.

### 5a. From the 3-site typed MPS to N sites (and growable bonds)

**Status (2026-08):** **Length is done** for fixed uniform typed bond `C χ`:
`TensorNetwork.MPS.General` holds open-boundary MPS/MPO with left + `V q` bulk +
right; `TensorNetwork.DMRG.Fixed` runs a zipper single-site DMRG for any bulk
length `@q`. Remaining typed-path work is performance, two-site, and
symmetry-adapted SVD (see **Current focus**), not "get N-site working".

Still open on this thread (when needed):
- **Per-bond / existential χ** — typed χ is uniform today; adaptive or
  site-dependent χ needs existentials or a max-χ padding story (also needed
  for honest two-site truncation).
- **Growable bonds / state addition** — **paused** with §5b. Revisit
  `FinSuppSeq` / `MPSClever` only after the typed path is performant and
  two-site / TDVP exploration has clarified whether we need a growable
  representation at all (vs typed χ + existentials).

### 5b. FinSuppSeq MPS: categorical layer, inner product, effective-`H` eigensolve

> **Paused (2026-08).** Do not continue this branch for now. Preference is
> typed bond dimension end-to-end; revisit §5b when state addition /
> adaptive-χ / tangent-space methods force a growable bond representation.
> The plan below is kept as deferred design notes.

`TensorNetwork.MPS.FinSupp` is the growable-bond, runtime-χ counterpart to the typed
prototype. It already has:

- `MPS vp` with `FinSuppSeq` bonds and a `VectorSpace` instance (`addMPS` grows χ);
- a flattening functor on objects: `mpsToFlat :: MPS vp -> C (vp³)` (and `mpsToPhysical3`);
- a canonical physical basis (`HasBasis` indexed by `Physical3 vp`) with round-trip
  properties (`prop_addThenFlatten`, `canonicalMPS`, `mpsFromFlat`).

What is **not** there yet: MPOs, inner products, the categorical API, environments /
effective Hamiltonians, or a local ground-state solve. The three workstreams below mirror
the typed pipeline (§4 Phases 2–4) but must cope with runtime bond dimension and the
`FinSuppSeq` bilinear-conjugation hazard (§4a).

**Orientation note.** FinSupp sites are *not* in transfer orientation:

| site | FinSupp (`FinSupp.hs`) | Fixed (transfer) |
|---|---|---|
| left | `C vp +> Bond` | `(C 1 ⊗ C p) +> C b1` |
| centre | `Bond +> (C vp ⊗ Bond)` | `(C b1 ⊗ C p) +> C b2` |
| right | `Bond +> C vp` | `(C b2 ⊗ C p) +> C 1` |

The plans below keep the FinSupp layout (it matches the existing flattening /
addition code). A later unification pass could re-express both representations as
instances of one `Site bl p br` indexed API — not a blocker for §5b.

---

#### 5b-i. Category: MPS objects, MPO morphisms, flattening functor

**Goal.** A small categorical layer in which tensor-network states and operators are
first-class morphisms, with a functor to the flat physical Hilbert space that validates
all contractions.

**Objects.** `MPS vp` — a state in the 3-site physical space, variationally parameterised
by growable virtual bonds.

**Morphisms.** `MPO vp` (new type, parallel to `Fixed.MPO`):

```haskell
data MPO vp = MPO
  { leftMPO  :: C vp +> (Bond ⊗ Bond)          -- or fused bond-pair type
  , centerMPO :: Bond +> (C vp ⊗ Bond ⊗ Bond) -- MPO leg ⊗ bond leg
  , rightMPO :: Bond +> (C vp +> Bond)        -- shape TBD to match contraction
  }
```

(Exact leg fusion for the MPO virtual bonds must be settled when implementing
`mpoTransferStep`; mirror the bra/ket environment types from `Fixed` but with `Bond`
instead of `C b`.)

**Identity & composition.**
- `identityMPO :: MPS vp -> MPO vp` (or parametric in `vp` only) such that
  `mpoApplyMPS identityMPO ψ` preserves `mpsToFlat ψ`.
- `composeMPO :: MPO vp -> MPO vp -> MPO vp` realising operator product on the physical
  space (bond fusion along the MPO column, analogous to `Fixed`'s fused `w·b` bonds).

**Categorical instances (target).**
- A category `Phys` with objects `Physical3 vp` (or `C (vp³)`) and morphisms `v +> w`.
- A category `TN` with objects `MPS vp` and morphisms `MPO vp`, with composition
  `composeMPO` and identity `identityMPO`.
- A functor `Flatten :: TN -> Phys`:
  - on objects: `mpsToFlat` (exists);
  - on morphisms: `mpoToFlat :: MPO vp -> C (vp³) +> C (vp³)` via closed transfer
    contraction (no `p⁶` basis sum — categorical `mpoTransferStep` chain, as in
    `Fixed`).

**Key operations to implement (ordered).**

1. `transferStep` / `foldTransferInner` for the FinSupp site orientation (bra site
   conjugated per-site; environment `Bond +> Bond`).
2. `mpoTransferStep` with typed environments `Bond +> (Bond ⊗ Bond)` (bra bond ↦ MPO ⊗
   ket bond).
3. `mpsMPOInner`, `mpoApplyMPS`, `mpoToFlat`.
4. **Reference module** `FinSupp.Reference` (basis-sum oracles, mirroring
   `Fixed.Reference`) for QuickCheck.

**Functoriality contract (QuickCheck).**

- `mpoToFlat (composeMPO h1 h2)` ≈ `mpoToFlat h1 . mpoToFlat h2` (up to tolerance).
- `mpsToFlat (mpoApplyMPS h ψ)` ≈ `mpoToFlat h $ mpsToFlat ψ`.
- `mpsMPOInner ψ h φ` ≈ `mpsToFlat ψ <.> (mpoToFlat h $ mpsToFlat φ)` (flat oracle uses
  `C n`'s sesquilinear `<.>`).
- `mpsMPOInner ψ (identityMPO @vp) φ === mpsInner ψ φ` once §5b-ii is in place.

**Exit criterion.** Categorical contractions green against `FinSupp.Reference` and flat
`C (vp³)` oracles; identity/composition laws checked.

---

#### 5b-ii. `InnerSpace` for `MPS vp` (in the vein of `Fixed.mpsInner`)

**Goal.** An `InnerSpace (MPS vp)` instance whose `<.>` agrees with the flat physical
inner product, enabling norms, Hilbert-space reasoning, and (later) variational
optimisation on the MPS manifold without flattening.

**Design (follow §4a conjugation discipline).**

1. `mpsConjugate :: MPS vp -> MPS vp` — `vectorConjugate` on each site map / bond
   tensor row; **never** rely on `FinSuppSeq`'s bilinear `<.>` or `adjoint` for
   conjugation.
2. `transferStep` — one left-to-right update contracting bra/ket bonds (FinSupp
   orientation); bra site passed through `mpsConjugate` internally or as a separate
   `Site` wrapper.
3. `mpsInner :: MPS vp -> MPS vp -> Complex Double` — fold `transferStep` from a
   `unitBond` / identity environment on the left, close with trace on the right bond
   (centre-right contraction for the 3-site chain).
4. `instance InnerSpace (MPS vp) where (<.>) = mpsInner` (and `(<.>^)` if needed for
   the linearmap API).

**Tests (mirror `Fixed` Phase 2).**

- `prop_innerMatchesFlat`: `mpsInner ψ φ === mpsToFlat ψ <.> mpsToFlat φ`.
- Conjugate symmetry: `mpsInner ψ φ === conjugate (mpsInner φ ψ)`.
- Positivity: `realPart (mpsInner ψ ψ) >= 0`.
- Compatibility with addition: sesquilinearity in each argument (or bilinearity + explicit
  conjugate in one slot — pick one convention and test against the flat oracle).
- `mpsNorm = sqrt ∘ realPart ∘ flip mpsInner` (self-overlap).

**Dependency.** Shares `transferStep` with §5b-i; implement inner product immediately
after the bare transfer machinery, before MPO transfer steps.

**Exit criterion.** All inner-product properties green; `InnerSpace` instance in
`FinSupp.hs` (or `FinSupp.Inner` if the module grows).

---

#### 5b-iii. Effective Hamiltonian & eigensolving (exploration)

**Goal.** Port the DMRG local-update semantics from `TensorNetwork.DMRG.Fixed` to
FinSupp: build `Heff` on the centre site by contracting MPO with left/right
environments, then solve for the ground state of `Heff` in the centre's map space.

**Centre type.** `Centre vp = Bond +> (C vp ⊗ Bond)` — the variational tensor at the
active site in FinSupp orientation.

**Port from Fixed (adapt bond types).**

1. **Environments** — generalise `TensorNetwork.DMRG.Env` to `Bond` environments
   (`LeftEnv`, `RightEnv`, `extendLeft` / `extendRight`, sweep updates). Reuse the
   categorical `mpoTransferStep` from §5b-i.
2. **`effectiveH`** — same formula as `Fixed.effectiveH`:
   `Heff x = R ∘ opWire op x ∘ (L ⊗^ id_p)` (with FinSupp-specific `opWire` wiring).
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

**DMRG driver (out of scope for first pass).** A full `dmrg` on `FinSupp.MPS` also needs
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
- **D2 — MPS representation.** ✅ **Typed `C χ` bonds, transfer orientation,
  per-site explicit conjugation** (§4a); generalised to **N-site** in
  `TensorNetwork.MPS.General`. Growable `FinSuppSeq` / `MPSClever` is **paused**
  (§5b) — not the active substrate.
- **D3 — Eigensolver.** ✅ **Production path: matrix-free Lanczos**
  (`Lanczos.groundStateLanczos`) on map-space centres with an `InnerSpace`
  metric — used by `TensorNetwork.DMRG.Fixed`. Dense `eigSH` /
  `GroundState.groundStateDense` remains as oracle / fallback. The older §4b
  plan to migrate to linearmap `eigen` is superseded for DMRG centres unless
  Lanczos proves inadequate; do not block on `eigen` for the typed path.
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
- *Manifold / TDVP structure* — `manifold-core` + (later) MPS-as-`VectorSpace` for
  tangent spaces; FinSuppSeq addition-commutes-with-flattening exists but that branch
  is paused pending the typed TDVP exploration.
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

D1–D3 resolved (§7). **Active substrate:** typed N-site MPS/DMRG
(`General` / `DMRG.Fixed`). **Paused:** FinSuppSeq (§5b).

### Done (archive)

1. ✅ Local ground-state tooling — dense `eigSH` oracle + **Lanczos** on centres.
2. ✅ Typed MPS + map-to-physical (3-site, then N-site in `General`).
3. ✅ Inner product / MPO / `⟨ψ|H|φ⟩` / effective-`H` (categorical path + props).
4. ✅ Single-site zipper DMRG — `sweep` / `dmrg` for any bulk `@q`; TFIM checks green.

### Next (see also **Current focus**)

1. ➡ **Profile DMRG parts** — env rebuild vs Lanczos vs regauge vs energy on
   N=8; then fix the hot path.
2. ➡ **Incremental environments** — zipper L/R envs through the sweep instead of
   rebuilding from scratch at every site (and stop paying full-network `energy`
   more than necessary).
3. ➡ **Intertwiner SVD** — symmetry-adapted gauge / truncation so graded centres
   can leave the dense `C n` bond picture; local eigensolve on intertwiners is
   expected to work already.
4. ➡ **Two-site DMRG** on the typed chain (fused centre → SVD → absorb / truncate).
5. ➡ **Explore `manifold-core`** for an MPS/TDVP formulation.
6. ➡ **Explore DMRG ≡ imaginary-time TDVP** once the manifold inventory is clear.

### Explicitly not next

- ❌ Continue FinSuppSeq categorical / `InnerSpace` / Heff port (§5b).
- ❌ Block on linearmap `eigen` migration (§4b) for typed DMRG centres — Lanczos
  is the production path; revisit only if needed.

# Roadmap: a symmetry-aware, basis-independent DMRG in Haskell

*Status: living document. Last updated 2026-06-07.*

## 0. The thesis

The unifying bet of this project is the same one TensorKit.jl makes, but pushed
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
| MPS/DMRG algorithm layer (à la MPSKit) | DMRG | `TensorNetwork.hs` | dense, complex-field; `move` (gauge) partly works via hmatrix SVD; `solveAtSite` effective-Hamiltonian + `eigen` is `undefined`/blocked |
| Symmetric MPS as a vector space (tangent space, addition of states) | vector space of MPS | `Infinite.hs` | `MPSClever` is a genuine `VectorSpace`; growable bond via `FinSuppSeq`; QuickCheck: addition commutes with flattening |

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
— `IEEE (Scalar v)` / `RealFloat` / `Scalar ~ Double`. But `TensorNetwork.hs` and
`Infinite.hs` work over `Field = Complex Double`. `IEEE (Complex Double)` does not hold,
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
- **D2 MPS representation**: ✅ **`Infinite.MPSClever`** (vector-space MPS, growable
  `FinSuppSeq` bond), generalised to keep the local Hilbert space abstract (§3).
- **D3 eigensolver**: ✅ **dense hmatrix `eigSH`** for now (`GroundState.hs`) — the easy
  route: materialise the local operator `C n +> C n` as a dense complex matrix (by
  applying it to the standard basis) and use hmatrix's Hermitian solver. Verified on
  `diag(3,1,2)` → ground energy `1.0`, spectrum `[1,2,3]`. A matrix-free / basis-
  independent Lanczos can replace it later (and move upstream into `linearmap-family`).

### Phase 1 — model & data types
1. Pick a benchmark model with a known ground-state energy: **transverse-field Ising**
   (exactly solvable) or **spin-½ AFM Heisenberg** (Bethe ansatz / finite-size ED).
2. Represent the Hamiltonian as an **MPO** of `+>` morphisms (`MPO p b` already
   sketched in `TensorNetwork.hs`). Build the model MPO concretely.
3. Settle the finite-MPS type (per D2): left/center/right `+>` morphisms with a bond
   space `b`. Concrete `C n` legs are fine (§3) — generalise the local space only when
   symmetry lands (§5).

### Phase 2 — environments
4. Build left/right environment tensors by contraction, as honest `+>` morphisms.
   Contraction = composition + `fmapTensor`/`transposeTensor` in the categorical API
   (no index loops). This is where the basis-independent style earns its keep.

### Phase 3 — effective Hamiltonian & local solve (the crux)
5. Assemble the single-site effective Hamiltonian `Heff :: local +> local` as a
   *matrix-free* operator (a composition of environment + MPO contractions). Never
   materialise it.
6. Find its **lowest** eigenpair. DMRG needs only the ground state, so use a Lanczos /
   `constructEigenSystem`-style Krylov iteration that consumes `Heff` as an operator.
   Resolve D1/D3 here. (`eigen` returns the *full* spectrum and is real-only; we want
   lowest-only and possibly complex — likely a small new function in the fork.)

### Phase 4 — truncation & gauge transport
7. SVD the updated tensor, truncate the bond to χ, and transport the gauge centre
   (`move` in `TensorNetwork.hs` already does this with hmatrix `svdTall`; either keep
   the hmatrix kernel behind a clean interface, or use `Math.TensorNetwork.svd`).
8. Bond growth/shrink: `Infinite.hs`'s `FinSuppSeq` bond is a clean way to let χ change
   without retyping — consider adopting it as the bond representation.

### Phase 5 — driver & validation
9. Left→right→left sweeping loop with energy-convergence stopping.
10. **Validate**: ground-state energy vs exact (TFIM) / ED for small N; entanglement
    entropy sanity; variance ⟨H²⟩−⟨H⟩². Add as QuickCheck/golden tests alongside the
    existing `Infinite` property tests.

**Exit criterion for "near-term done":** `dmrg model N chi` returns the correct
ground-state energy for TFIM/Heisenberg to tolerance, with the algorithm written
generically over the local Hilbert space.

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
5. **MPS-as-vector-space (`Infinite`)** generalises to symmetric MPS, enabling
   state addition / tangent vectors — the entry point to TDVP and excited-state methods.

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
- **D2 — MPS representation.** ✅ **`Infinite.MPSClever`** — vector-space instance with a
  growable `FinSuppSeq` bond. `TensorNetwork.MPS`'s two-site scaffolding can be ported
  onto it. Generalise the physical leg from `C vp` to an abstract local Hilbert space (§3).
- **D3 — Eigensolver.** ✅ **Dense hmatrix `eigSH`** (`GroundState.hs`). Pragmatic and
  done: build the dense matrix of `Heff :: C n +> C n` by basis application, solve with
  hmatrix. Not basis-independent and materialises the operator, but it unblocks the
  local solve and lets effort go to defining `Heff`. Replace with a matrix-free Lanczos
  later if perf needs it (a good upstream `linearmap-family` contribution).
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
- *States as a `VectorSpace`* (`Infinite`) — makes tangent spaces / TDVP / excited-state
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

D1–D3 are resolved (§7). Concrete sequence:

1. ✅ **Local ground-state solver** — `GroundState.hs`: `groundState :: KnownNat n =>
   (C n +> C n) -> (Double, C n)` via dense hmatrix `eigSH`. Verified on `diag(3,1,2)`.
2. **Use `MPSClever` with concrete `C vp` legs** (§3 — no premature abstraction). Port
   the two-site solve scaffolding from `TensorNetwork.MPS` onto it.
3. **TFIM as an MPO** of `+>` morphisms; build left/right environments by categorical
   contraction (Phase 2); assemble `Heff :: C n +> C n` (Phase 3) and solve with (1).
   ← *current focus: defining the effective Hamiltonian.*
4. **Ground-state-energy test** vs exact TFIM (Phase 5 exit criterion); wire into the
   existing QuickCheck suite next to the `Infinite` properties.

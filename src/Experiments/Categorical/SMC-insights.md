# SMC insights from linear-smc (study notes)

Notes distilled from Bernardy–Spiwack (*Evaluating Linear Functions to
Symmetric Monoidal Categories*, Haskell 2021 / [arXiv:2103.06195](https://arxiv.org/pdf/2103.06195))
and the [linear-smc](https://github.com/jyp/linear-smc) implementation, plus
Bernardy–Jansson (*Domain-specific tensor languages*, JFP 2025 /
[arXiv:2312.02664](https://arxiv.org/abs/2312.02664)).

**Not** an adoption plan for the package. Goal: transferable ideas for
`Experiments.Categorical.*`, Fibonacci, and TensorNetwork wiring.

---

## 0. Linear types as internal language — does it extend to fusion?

### The SMC correspondence

The internal language of (closed) **symmetric monoidal** categories is
multiplicative linear logic / the linear λ-calculus (Szabo; Benton; nLab).
A judgment that uses each variable once

\[
a_1 : A_1,\;\ldots,\; a_n : A_n \;\vdash\; e : B
\]

denotes a morphism \(A_1\otimes\cdots\otimes A_n \to B\).

Bernardy–Spiwack make this computational: Linear Haskell evaluates such a
term to an SMC morphism (`decode`), with no metaprogramming.

So “natural” means: **linearity is the host-language embodiment of “wires are
resources.”** That fragment applies to *any* monoidal category’s ⊗-wiring —
including fusion.

### Fusion needs more than that fragment

A ℂ-linear fusion category (see [`Fibonacci.md`](../Fibonacci.md) §1) is not
“just an SMC”:

| Fusion ingredient | LinearTypes / linear-smc | Fib today |
| --- | --- | --- |
| ⊗, unit, Mac Lane assoc/unitors | Yes (multiplicative) | `Tensor`, `Associative` / `Monoidal` |
| No structural copy/discard of objects | Yes (linearity) | Morphisms, not cartesian |
| Symmetric `swap` | Yes (SMC) | **Wrong** — need braided |
| Braiding with \(\sigma^2 \neq \mathrm{id}\) | No GHC story; “braided logic” exists in principle | `Braided` + `braidFib` |
| Duals / rigid / compact closed | JFP `turn`/`turn'`; not Multiplicity alone | Duals still open |
| Direct sum ⊕, \(N\)-symbols | **No** — additives ≠ Haskell pairs | `'Sum`, `Norm`, `Fuse`, `Mult*` |
| Hom as ℂ-vector spaces, bilinear compose | **No** — λ-terms are morphisms, not Hom-vectors | `HomBlocks`, `composeBlocks` |
| Nontrivial \(F\)/\(R\) data | **No** — free SMC treats \(A\)/\(S\) as coherence | `fmove`, `braidFib` |
| Semisimplicity / skeletal Fuse | **No** | `Fuse` / `fuseMap` |

**Claim worth keeping:**

> Linear types ≅ internal language for **multiplicative monoidal wiring**.
> Fusion ≅ that + **Vect-enrichment** + **additives** + **braiding** +
> **\(F\)/\(R\) generators**.

### Layer cake (conceptual)

1. **Multiplicative** — linear λ / ports: wire objects; Bernardy-style
   `decode` possible if ⊗ is the monoidal product and braid is handled.
2. **Braided** — explicit braid (not involutive `swap` rewrites).
3. **Additive** — intro/elim for ⊕; in Fib this is `'Sum` + block-diagonal
   Homs (biproduct syntax, not LinearTypes).
4. **Enrichment** — terms denoting vectors in Hom, with `+` and scalar `·`;
   compose is bilinear. Ordinary linear algebra on blocks, not λ-calculus.
5. **Coherence generators** — \(F\), \(R\) as named morphisms with matrix
   semantics; pentagon/hexagon are equations on those generators, not Mac Lane
   free-SMC cancellation alone.
6. **Rigid/pivotal** — duals + snake; compact-closed port sugar helps *wiring*
   duals, not computing quantum dimensions.

Fib’s split (tree objects / skeletal `Fuse` / `HomBlocks`) already mirrors
this better than a single LinearTypes embedding would.

### The ⊕ trap

linear-smc `split`/`merge` on Haskell `(,)` is **⊗-splitting of product
objects in Hask**. That coincides with fusion ⊗ only when objects are literally
nested pairs — false for `'Sum` / multiplicity spaces. If ports are ever added
for Fib, ports should carry Fib objects (`P Fib r a`), with `split` only for
`Tensor`, and a separate additive interface for `Sum`.

### Practical takeaway

- **Steal** the multiplicative insight: named linear ports are the right UI for
  string diagrams over fusion objects; free *braided* simplification is the
  right backend for structural junk.
- **Do not expect** LinearTypes to replace `HomBlocks`, `Fuse`, or \(F\)/\(R\)
  tables.

---

## 1. Mental model: ports → free categories → eval

```text
  linear Haskell function
  ∀ r.  P k r a  ⊸  P k r b
            │
            │  extract = apply to (P id)
            ▼
     FreeCartesian k a b     ← ports as morphisms from source r
            │                    (π₁, π₂, △ allowed while building)
            │  reduce / toSMC
            ▼
       FreeSMC k a b         ← I | Embed | A | A' | S | U | U' | ∘ | ×
            │
            │  evalM / monoidalSimplify
            ▼
          a `k` b              ← target category (U, Workflow, Fib, …)
```

**Ports as prefixes.** `P k r a` is a free-cartesian morphism \(r \to a\):
the portion of the diagram from the global source to that wire. Naming a wire
= naming a diagram prefix (Yoneda / reverse CPS).

**Why FreeCartesian then FreeSMC?** Building with `split` needs projections.
Linearity guarantees those projections were only scaffolding (`protolinear`);
`reduce` erases them. Semantics stay monoidal (non-cartesian).

**Interface laws** (paper Fig. 5): `split`/`merge` and `encode`/`decode` are
inverses; `encode` is a monoidal functor on the nose (via split/merge for `×`).

---

## 2. Free SMC presentation + rewrite checklist

From `Control.Category.FreeSMC` (linear-smc):

```haskell
data Cat k con a b where
  I      :: Cat k con a a
  Embed  :: k a b -> Cat k con a b
  A, A'  :: ...   -- associators
  S      :: ...   -- swap (symmetric!)
  U, U'  :: Unitor con ... -> ...
  (:.:)  :: ...   -- composition
  (:×:)  :: ...   -- parallel
```

Equality of free terms is quotiented by **Embed being an SMC homomorphism**
(`Embed id = id`, `Embed (f∘g) = Embed f ∘ Embed g`, `Embed (f×g) = …`).

### `monoidalRules` worth copying (for a *braided* variant)

Structural cancellations and pushes (verify against upstream `monoidalRules`):

- Cancel: `S∘S`, `A'∘A`, `A∘A'`
- Push `S` through `×`: `S ∘ (f×g) = (g×f) ∘ S`
- Hexagon-shaped: push `S` through `A`/`A'` as assoc+swap composites
- Push unitors through `S` / `×` / `A` / `A'` via `commuteUnitors`
- Fuse parallel: `(f×g)∘(h×i) = (f∘h)×(g∘i)`
- Extract nested unitors so they can cancel with their inverses

`mkSimplifier` = left/right views of composition + react-or-stick (critical-pair
style).

**Fib warning:** do **not** copy involutive `S` laws. Fibonacci is braided,
not symmetric (`braid ∘ braid ≠ id`). A FreeBraided would have a non-involutive
braid generator and hexagon rules with `associate`, not `S∘S = id`.

### Design split: structure vs generators

Keep **structural** morphisms (assoc, unitors, braid) distinct from
**generators** (`fmove`, `braidFib`, site maps) as `Embed`. Then:

- Free simplifier cancels accidental Mac Lane junk.
- Pentagon/hexagon *tests* can run on free terms without evaluating \(F\)/\(R\)
  matrices.
- \(F\)/\(R\) remain dataful generators, not coherence isos.

---

## 3. The `reduce` / FreeCartesian trie (algorithmic core)

From `Control.Category.FreeCartesian`:

- Cont-style: `Cat = ∀ c. Trie b c → Trie a c`
- Forks as a **sorted** list of legs; bubble-sort with tracked permutations so
  meaning is preserved
- `normalize` succeeds with residual `Z` + an SMC morphism when the term is
  protolinear
- Key lemma: under linearity, generators with the same source are equal —
  **no `Eq` on generators** needed for reduce (copies arise only from `split`)

`reduce` undoes splits by finding adjacent \(\pi_1\circ h\) and \(\pi_2\circ h\)
in the sorted merge list and replacing them with \(h\), accumulating the
permutation as FreeSMC.

**Transfer:** if named-leg sugar is ever wanted, this is the algorithm. Immediate
lesson: linearity ⇒ unique consumption ⇒ comparison without generator equality.

---

## 4. Cartesian vs monoidal (design discipline)

Paper §6.2: `copy` / `discard` must be **explicit** (`encode dup`), not baked
into `decode`. The cartesian law

\[
(f\times f)\circ\mathrm{dup} = \mathrm{dup}\circ f
\]

is often *false* for cost/effects. Their simplifier treats `dup` as a black-box
generator.

**Transfer:** matches this repo’s “no implicit basis arithmetic / no shotgun
share” culture. MPS bond reuse, env sharing, etc. stay explicit morphisms, not
free-cartesian projection.

Cartesian structure is a *compile-time fiction* for wiring ports — never the
runtime semantics of TN / Fib.

---

## 5. Compact closed / Einstein layer (JFP paper)

Roger (point-free SMC + compact closed) vs Albert (index notation):

- Duals via `turn` / `turn'` (\(\eta\)/\(\varepsilon\)); snake laws
- Contraction = connecting high/low index ports (linear use of each index once)
- Live indices = open wires; dummy indices = contracted wires
- Topology of diagrams = algebraic equality ([Selinger](https://arxiv.org/abs/0908.3347))

**Transfer:** fusion duals / dagger / evaluation–coevaluation sit here.
Einstein sugar is less urgent than free braided structure + snake laws for
closing TN chains categorically (already the production goal).

---

## 6. Map onto this codebase

| Their concept | Here |
| --- | --- |
| `Monoidal` + free `A`/`U`/`S` | [`Associative`](Associative.hs) / [`Monoidal`](Monoidal.hs); Fib unitors = `idBlocks` |
| Symmetric `S` | [`Braided`](Braided.hs) + Fib `braidFib` (not `Symmetric`) |
| `Embed` generators | `fmove` / `braidFib` / `tensorFib` |
| Ports / `decode` | not present; optional future sugar only |
| Compact closed | TN `trace` / duals / dagger stubs; fusion duals still open |
| Simplifier | none yet; candidate for coherence prop tests |
| `(,)` as ⊗ | **Do not**; Fib `Tensor` / Vec `⊗` are not Hask product |

---

## 7. Design commandments (extracted)

1. **Linearity = no free copy of wires.** Structural share must be an explicit
   morphism (or additive ⊕ intro), never silent.
2. **Separate FreeCart (build) from FreeSMC/FreeBraided (mean).**
3. **Embed generators; rewrite only structure.** \(F\)/\(R\) are data.
4. **Braided ≠ symmetric.** Involutive swap rewrites are wrong for Fib.
5. **Additives are a different fragment.** Don’t fake ⊕ with `(,)`.
6. **Enrichment is not λ-calculus.** Hom-vectors live in `HomBlocks`.
7. **Topology = equality** for structural diagrams; use that for tests.

---

## 8. Non-goals

- Depend on `linear-smc` as a package
- Replace `Experiments.Categorical.*` or `TensorNetwork.Categorical`
- Migrate production code to `LinearTypes`
- Claim that LinearTypes = fusion categories
- Evaluate FreeCartesian projections as runtime TN morphisms

---

## 9. Reading shortlist

1. Bernardy–Spiwack, [Evaluating Linear Functions to SMCs](https://arxiv.org/pdf/2103.06195) — §§3,5,6
2. linear-smc sources: `FreeSMC.hs` (`monoidalRules`), `FreeCartesian.hs` (`normalize`/`toSMC`), `Linear/Internal.hs`
3. Bernardy–Jansson, [Domain-specific tensor languages](https://arxiv.org/abs/2312.02664) — compact closed + Einstein
4. Selinger, [A survey of graphical languages for monoidal categories](https://arxiv.org/abs/0908.3347)
5. Shulman, [A practical type theory for SMCs](https://arxiv.org/abs/1911.00818)
6. nLab: [monoidal category — internal logic](https://ncatlab.org/nlab/show/monoidal+category); MathOverflow on ordered vs braided logic
7. Patterson–Fairbanks–Baas, wiring diagrams as SMC normal forms (Catlab / EPTCS)

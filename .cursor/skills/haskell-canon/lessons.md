# Haskell canon — study notes

Living document. Prefer Hackage module docs over READMEs when deepening a
pass. Each package has a status; promote only stable lessons into
`haskell-practices.mdc` / `AGENTS.md`.

Sources:

- [Parse, don’t validate](https://lexi-lambda.github.io/blog/2019/11/05/parse-don-t-validate/) (Alexis King) — primary type-driven design slogan
- [ad](https://hackage.haskell.org/package/ad) ([GitHub](https://github.com/ekmett/ad))
- [linear](https://hackage.haskell.org/package/linear) ([GitHub](https://github.com/ekmett/linear))
- [discrimination](https://hackage.haskell.org/package/discrimination) ([GitHub](https://github.com/ekmett/discrimination))
- [bound](https://hackage.haskell.org/package/bound) ([GitHub](https://github.com/ekmett/bound))
- [recursion-schemes](https://hackage.haskell.org/package/recursion-schemes)
- [The Haskell Guide](https://haskell-docs.netlify.app/) ([source](https://github.com/reubenharry/haskell-docs)) — pedagogy / process

---

## Parse, don’t validate (Alexis King)

**Status:** pass-1 (full essay)

**Definition:** a parser consumes less-structured input and produces
more-structured output, preserving what was learned in the type. A validator
checks the same thing but returns `()` / throws and **throws the proof away**.

### Core moves

1. **Strengthen the argument, don’t weaken the result** — prefer
   `head :: NonEmpty a -> a` over `head :: [a] -> Maybe a` when the emptiness
   check already happened (or should happen) at the boundary.
2. **Return the refined type** — `parseNonEmpty :: [a] -> IO (NonEmpty a)`,
   not `validateNonEmpty :: [a] -> IO ()`.
3. **Push the burden of proof upward** — get data into the precise
   representation as early as possible (system boundary); if only one branch
   needs more precision, parse when that branch is taken.
4. **Write functions on the type you wish you had** — change call sites to
   `Map` / `NonEmpty` / typed morphisms; insert the real parser where the
   loose value is born. Refactor until the ends meet.
5. **Avoid shotgun parsing** — don’t scatter checks through processing code
   while acting on half-validated input (LangSec). Stratify: parse, then
   execute; failure from bad input belongs in the parse phase.

### Practical checklist (from the essay)

- Let datatypes drive code; don’t bolt on a `Bool` for the function you’re in
- Treat `m ()` “validators” with suspicion when their job is raising errors
- Multi-pass parsing is fine; acting before fully parsed is not
- Avoid denormalized mutable duplicates; if needed, hide behind an ADT boundary
- Abstract `newtype` + smart constructor when a true unrepresentable encoding
  is impractical (e.g. ranged `Int`)
- Power-to-weight still applies: `error "impossible"` is radioactive — comment
  the invariant; don’t pretend it’s fine

### Related reading cited in the essay

- Matt Parsons, [Type Safety Back and Forth](https://www.mattparsons.com/blog/type-safety-back-and-forth/)
- Matt Noonan, *Ghosts of Departed Proofs* (ICFP 2018) — for heavier proof tokens

### Quantum applicability

- Boundary: scripts / IO / array backends → typed `C n` / morphisms / zipper
  focus. Parse once; don’t re-assert “bond dim matches” in every helper.
- Prefer smart constructors for mixed-canonical / env-zipped states over
  `assertCanonical` returning `()`.
- `*.Reference` oracles may validate loosely; production should carry proofs in
  types (categorical composition), not re-check shapes.
- Shotgun parsing ≈ scattering basis/index checks through a contraction while
  already multiplying tensors — ban aligns with no-basis-sum / no-temp-hacks.

---

## Cross-cutting themes (pass 1)

These show up in more than one library and are the first distillates for the
harness:

1. **Make illegal states unrepresentable (by construction)** — King / bound /
   ad
   - bound: free vs bound vars in `Var b a`; binders as `Scope`
   - ad: `AD s a` + `forall s` so infinitesimals from different runs cannot mix
   - King: refined return types preserve proofs; validators discard them
   - Not "check after"; structure the data so the bad program does not typecheck

2. **Separate the pattern from the payload**
   - recursion-schemes: scheme (`cata`) vs algebra (`Base t a -> a`)
   - ad: shared primitive Jacobian story; Mode chooses how to compose
   - Write the "what"; reuse the "how"

3. **Systematic API families, not one-off names**
   - ad: `grad` / `jacobian` / `diff` + suffixes `'`, `With`, `F`, `s`, `T`, `0`
   - discrimination: `group` / `groupWith`, `sort` / `sortWith`
   - Readers learn one grammar and predict the rest
   - **Anti-pattern:** synonym wrappers (`unitLunit = lunit`) or a second module
     restating the same unitors — call / re-export the existing name unless the
     new binding adds a constraint or law

4. **Final encodings for composable structure**
   - discrimination: `Group` / `Sort` as higher-rank newtypes; instances via
     `contramap` / `Dividing`; lawful without quotienting
   - Prefer "give me the operations" over "here is the closed sum of cases"

5. **Power-to-weight**
   - bound docs: Derived.hs beats Overkill.hs for most users
   - ad: default branded API; `Rank1.*` only when you need the flexibility
   - Do not pay for type machinery that does not kill a real bug class

6. **Public façade / Internal kitchen**
   - ad: `Numeric.AD` safe; `Numeric.AD.Internal.*` partial/unsafe
   - Keep production imports on the façade

7. **Laws next to the computational content**
   - discrimination: `groupingEq x y ≡ (x == y)`; `sortingCompare ≡ compare`
   - Enrich a class with a faster algorithm only when the law pins the meaning

---

## ad — Automatic Differentiation

**Status:** pass-1 (Hackage package + `Numeric.AD` docs + skim of Internal.Forward)

### Lessons

- **Mode + branding:** `Mode t`, `auto`, and `AD s a` with rank-2 `forall s` in
  combinators. The brand is not documentation — it is the safety mechanism.
- **Combinator grammar:** one concept family; suffixes encode orthogonal
  variations (also return value, blend, traversable result, tower, transpose).
- **Mixed mode by default:** `Numeric.AD` picks an appropriate mode per
  combinator; specialists live in `Mode.*` when you need control.
- **Escape hatch is explicit:** `Rank1.*` trades infinitesimal safety for
  higher-order flexibility — named, not sneaky.
- **Sharing / laziness as API contract:** towers and jets compute distinct
  derivatives once and share (documented behavior, not an accident).

### Quantum applicability

- When introducing "session" or "tape"-like resources (Lanczos scratch,
  env zipper state), consider rank-2 or phantom branding so values cannot
  cross sessions.
- Prefer a small suffix/family grammar if Fixed and General grow parallel ops.
- Keep unsafe reshape / coerce helpers in an Internal-style module if they must
  exist (and still ask before `unsafeCoerce`).

### Next deepenings

- `Numeric.AD.Mode` class laws and `Jacobian`
- How `On` / mode transformers compose for Hessian products
- Concrete Forward vs Reverse tape representation choices

---

## linear — Free vector spaces

**Status:** pass-1 (package page + V2 source header skim; module docs thin on
Hackage root — deepen via `Linear.Vector`, `Linear.Metric`, `Linear.V`)

### Lessons

- **Shape is the type:** `V2` / `V3` / `V n` rather than one untyped array;
  operations are polymorphic over Representable/Applicative structure.
- **Orthogonal typeclasses:** `Metric`, `Epsilon`, `Additive` — concerns split
  so instances stay honest.
- **Component access as optics:** `R1` / `R2` / `ex` / `ey` — compositional
  lenses instead of ad-hoc getters.
- **Instances are the product:** Storable, Unbox, Random, etc. make the type
  usable everywhere; the design assumes rich instances, not a minimal core.

### Quantum applicability

- Aligns with typed `C n` / bond dimensions: keep dimension in the type.
- Prefer class-split capabilities (inner product vs dagger vs apply) over a
  megaclass that lies about what is implemented.
- Component/leg access should look like morphisms or optics, not indexing soup.

### Next deepenings

- `Linear.Vector` (`Additive`) and `Linear.Metric` laws
- `Linear.V` existential/finite encoding
- How `Distributive` / `Representable` drive `*!!` style ops

---

## discrimination — Linear-time discrimination

**Status:** pass-1 (`Data.Discrimination` Hackage docs)

### Lessons

- **Final encoding of an algorithm:** `Group` / `Sort` wrap the discrimination
  capability as a value; compose with `contramap` rather than rewriting sorts.
- **Complexity as part of the API:** O(n) `nub` / `group` / `toMap` — the type
  class promises an asymptotic story, not just denotation.
- **Lawful enrichment of Eq/Ord:** `Grouping` / `Sorting` morally superclasses
  with explicit laws back to `==` / `compare`.
- **Stable by default:** documented stability of grouping — behavioral
  contracts in Haddock, not tribal knowledge.
- **Generic joins:** same discriminator drives inner/outer joins — one
  abstraction, many table operations.

### Quantum applicability

- When grouping sectors / charge sectors / block indices, prefer a
  discriminator-style combinator over ad-hoc `Map` munging.
- Any "faster Eq" path needs a law tying it to the denotational Eq (props).
- Final encodings fit categorical style: pass the algebra/capability, don't
  case-split on representation in every client.

### Next deepenings

- `Grouping` generic deriving / `Deciding`
- Henglein papers vs encoding choices in source
- When discrimination does *not* apply (comparison-based lower bounds)

---

## bound — Locally nameless / Scope

**Status:** pass-1 (`Bound` Hackage docs + Scope header)

### Lessons

- **Capture-avoiding substitution is structure:** `Monad` + `Traversable` on
  user terms; `Scope` captures the binder pattern once.
- **`Var b a`:** bound and free variables are different constructors — you
  cannot silently treat a bound var as free.
- **Smart API:** `abstract` / `instantiate` (and `*1` / `*Either`) — clients
  do not increment de Bruijn indices by hand.
- **Generalized de Bruijn:** lift whole trees under binders (Bird–Paterson /
  McBride–McKinna lineage) — performance and clarity from representation.
- **Power-to-weight called out in-tree:** Overkill.hs vs Derived.hs — library
  authors documenting when *not* to use the heaviest encoding.

### Quantum applicability

- Binder-like structure appears in "under a gauge" / "under a scope of sites":
  prefer a Scope-like discipline if we ever need capture-safe substitution of
  morphisms.
- More immediately: smart constructors for mixed-canonical centres / zipper
  focus — don't let clients build ill-scoped zippers.
- When tempted by maximal type indexing of sites, check power-to-weight.

### Next deepenings

- `Bound.Scope` vs `Bound.Scope.Simple`
- `Bound.Name` retaining names
- examples/Derived.hs patterns for TH/`Bound` class

---

## recursion-schemes

**Status:** pass-1 (README + `Data.Functor.Foldable` synopsis)

### Lessons

- **Base functor = one layer:** `Base t`, `project` / `embed` — recursion is
  factored out of the datatype.
- **`cata` kills a class of bugs:** forgotten `fmap` on recursive positions;
  the scheme inserts it.
- **Name the scheme:** `cata` (consume), `ana` (produce), `hylo`/`refold`
  (fuse), `para` (need original), etc. — flowchart in README for choice.
- **Algebras stay non-recursive:** easier to test and reuse; recursion is in
  the scheme.
- **TH for boilerplate:** `makeBaseFunctor` when the F type would be rote.

### Quantum applicability

- N-site MPS/MPO folds, left/right env accumulation, transfer products: write
  algebras (`site × env → env`) and one named fold; don't hand-roll fmap-ish
  recursion at each call site.
- Sweep / zipper moves are closer to paramorphisms / zygomorphisms when you
  need the original centre — name that if it clarifies.
- Avoid inventing a new recursive worker for every probe script when a fold
  algebra would do.

### Next deepenings

- When to use `para` / `zygo` / `histo` in TN algorithms
- `refix` / `hoist` for changing representation (Fixed ↔ General?)
- Mendler-style schemes vs standard (advanced)

---

## The Haskell Guide (haskell-docs.netlify.app)

**Status:** pass-1 (Thinking functionally, Typeclasses, Laziness, Gotchas,
packages overview, case-study overview, resources/articles index)

Personal but substantial guide (GHC 9 series). Valuable here less as novel
theory and more as **process**: how to use the typechecker day-to-day.

### Type-driven process

- **Custom types enforce conceptual distinctions** — `ChessSquare` vs `(Int,Int)`
  even when representation is the same under the hood
  ([type checking](https://haskell-docs.netlify.app/thinkingfunctionally/typechecking/)).
- **Debug type errors by substituting `undefined`** — grow/shrink the hole until
  the program typechecks; then ask for the hole’s type (`:t` / HLS).
- **Type-driven top-down development** — write the outer program with
  `undefined` stubs; let the compiler infer stub types before implementing
  ([type inference](https://haskell-docs.netlify.app/thinkingfunctionally/typeinference/)).
- **Type-based refactoring** — change a type alias / datatype; fix the static
  error list one-by-one until green.
- **Case-study tip:** break `$`-heavy stacks by replacing a suffix with
  `undefined` and reading the inferred type (print-statement analogue).

### Purity, immutability, folds

- Effects in the type (`IO a`); pure code is replaceable by its value
  (**equational reasoning**).
- Prefer declarative folds (`sum`, `foldr`, …) over imperative loops / `State`
  forM soup when the problem is a fold
  ([thinking functionally](https://haskell-docs.netlify.app/thinkingfunctionally/hof/)).
- Explicit recursion is discouraged when a fold/unfold captures the pattern —
  same spirit as recursion-schemes; fewer empty-list bugs, clearer control flow.
- Immutability: `x = x + 1` is an infinite knot, not mutation
  ([gotcha](https://haskell-docs.netlify.app/gotchas/mutation/)).

### Typeclasses (discipline)

- Prefer **existing** classes from libraries; DIY classes are easy to design
  badly and usually unnecessary
  ([overview](https://haskell-docs.netlify.app/typeclasses/overview/)).
- One instance per type; use **newtype** wrappers (`Sum` / `Product`) when you
  need a different lawful instance for the same payload.
- Learn a class via: Hackage minimal definition → laws (manual) → a few
  instances → `:info` in the REPL
  ([survey](https://haskell-docs.netlify.app/typeclasses/survey/)).
- Constraints float upward; when stuck on “which instance?”, mouse over /
  specialize and read the concrete instance source on Hackage.

### Laziness & libraries

- Laziness enables infinite-then-`take` / unfold-then-fold; also changes
  complexity — don’t ignore space leaks
  ([laziness](https://haskell-docs.netlify.app/laziness/laziness/)).
- Read library APIs from **types first** on Hackage; follow links to definitions
  ([packages](https://haskell-docs.netlify.app/packages/overview/)).
- Prelude `head` is partial legacy; prefer total alternatives at boundaries
  (aligns with King / NonEmpty).
- Debug: REPL + types first; `Debug.Trace.trace` when you truly need a print
  ([debugging](https://haskell-docs.netlify.app/faqs/debugging/)).

### Quantum applicability

- ChessSquare lesson → keep `C n` / site / bond distinctions; don’t pass raw
  tuples or `M` where a named type exists.
- Outer DMRG driver with `undefined` for env zipper / two-site update is the
  guided way to grow features (matches no-temporary-hacks: honest stubs).
- Prefer fold algebras for N-site / env accumulation over hand-rolled workers
  (ties to recursion-schemes section).
- Don’t invent a new typeclass for every TN notion; extend existing categorical
  / linearmap classes or use plain functions + newtypes. Type classes are for
  type-level recursion or necessary overload — not OO/traits analogy; prefer
  one spine walker + rank-2 algebras over a class per operation.
- Probe scripts: REPL/`tricorder` + `undefined` holes beat print-driven debugging
  in pure numeric cores; use probes when measuring runtime.

### Next deepenings

- Case study pages (chess parser / evaluator) for end-to-end parse-then-eval
- `packages/mtl`, `megaparsec`, `lens` pages if we adopt those patterns
- Articles index recursion-schemes series already linked from the guide

---

## Promotion log

| Date | Promoted into harness | From |
| --- | --- | --- |
| 2026-09-06 | haskell-practices / AGENTS / canon: math≅code compositional structure (primary Haskell quality) | user / Symbolic.Core |
| 2026-09-06 | haskell-practices / AGENTS: call-sites-first, library constructors, no buffer unpack for core maps | Experiments.Symbolic.Core cleanup |
| 2026-08-20 | haskell-practices / AGENTS: type classes sparingly (stain; scheme+algebra) | Experiments.General fuse/commute |
| 2026-08-02 | haskell-practices: schemes, API families, branding, power-to-weight | cross-cutting |
| 2026-08-02 | AGENTS.md pointer + haskell-canon skill | scaffold |
| 2026-08-02 | haskell-practices / AGENTS: King parse-don’t-validate checklist | essay |
| 2026-08-02 | haskell-practices / AGENTS: type-driven `undefined`, folds, class discipline | Haskell Guide |

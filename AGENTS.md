# Agent constitution — quantum

Basis-free, symmetry-aware tensor-network / DMRG work in Haskell
(`linearmap-category`). Before inventing work, read **Current focus** in
[`ROADMAP.md`](ROADMAP.md).

Cursor loads the hard rules under [`.cursor/rules/`](.cursor/rules/). Skills
under [`.cursor/skills/`](.cursor/skills/) spell out the day-to-day loop.
This file is the portable summary for any agent (Cursor, Claude Code, ChatGPT).

## Hard bans

Do not violate these. Full text lives in `.cursor/rules/`.

1. **No basis-sum in production** — contractions/amplitudes are morphisms
   (composition, `trace`, unitors, `siteDagger`, …). Explicit
   `enumerateSubBasis` / `basis @n i` / coefficient sums belong only in
   `*.Reference` oracles (and `gen*`). If categorical closure is blocked, use
   `undefined` and name the blocker — never a basis-sum stand-in.
2. **No new `unsafeCoerce`** without explicit user approval for that site.
   Prefer typed helpers, `KnownNat` / dimensionality splits, or `coerce` with a
   same-representation proof.
3. **No temporary hacks** to get green. Runtime dimension tricks, `INCOHERENT`
   decode paths, `error` tables that break on the next size — stop and co-plan
   instead. Honest `undefined` beats a lie that typechecks.

## Mindset

### Parse, don't validate

Follow [Parse, don’t validate](https://lexi-lambda.github.io/blog/2019/11/05/parse-don-t-validate/)
(Alexis King): prefer parsers that return a refined type over validators that
return `()` and discard the proof. Strengthen arguments (typed morphisms,
smart constructors) instead of weakening every callee to `Maybe` and re-handling
“impossible” cases. Push checks to the boundary; don’t shotgun-parse while
acting on data. Compose typed morphisms; reserve loose runtime checks for IO
boundaries and Reference oracles.

### Hate verbose boilerplate

Prefer a short composition that reuses existing helpers over a long
case/list/index solution. If a small idea needs a lot of plumbing, stop and
redesign (missing combinator or wrong domain). Do not invent parallel APIs that
duplicate Fixed / General / Reference with slight renames.

### Scheme vs algebra; systematic APIs

For folds / sweeps / env accumulation: write a non-recursive algebra and reuse
a named recursion scheme — do not re-implement traversal plumbing each time.
Prefer small API families with predictable variants over one-off names. Prefer
composable (final) encodings over closed case-splits. Keep power-to-weight in
mind; unsafe/partial helpers stay off the production import path.

Style references (ongoing study):
[Parse, don’t validate](https://lexi-lambda.github.io/blog/2019/11/05/parse-don-t-validate/),
[ad](https://hackage.haskell.org/package/ad),
[linear](https://hackage.haskell.org/package/linear),
[discrimination](https://hackage.haskell.org/package/discrimination),
[bound](https://hackage.haskell.org/package/bound),
[recursion-schemes](https://hackage.haskell.org/package/recursion-schemes),
[The Haskell Guide](https://haskell-docs.netlify.app/).
Notes and next deepenings: skill `haskell-canon`
([lessons.md](.cursor/skills/haskell-canon/lessons.md)).

### Type-driven process

Use the compiler as a design partner ([Haskell Guide](https://haskell-docs.netlify.app/)):
outer shape + honest `undefined` stubs, infer stub types, fill gaps; localize
type errors by substituting `undefined`. Prefer folds over hand-rolled
recursion. **Type classes sparingly** — only for type-level recursion or
overload that cannot be a plain function / shared composition; they are a code
stain when reached for by OO/traits analogy. Prefer existing classes +
`newtype`, or one scheme class with rank-2 algebras. Custom types keep
conceptual distinctions (bond/site/morphism ≠ raw arrays/tuples).

### Small increments

Prefer the smallest typed milestone that typechecks. One conceptual change per
edit cycle when possible; verify before stacking the next.

## Dev loop

Default path (see skill `quantum-dev-loop`):

1. Plan in 2–5 lines (categorical approach; name blockers).
2. Make a **small** edit.
3. Verify with a **targeted lib build** (not tricorder; not a full-project rebuild):
   ```bash
   cabal build quantum:lib:quantum
   ```
4. On policy conflict or unclear design: **stop and co-plan**.
5. At a finished slice (not every edit): `cabal test`, or a named probe script
   for performance work.

Do **not** start or poll tricorder in the default loop — it has been a source of
severe slowdowns here. Prefer `cabal repl quantum:lib:quantum` / HLS when you
need interactive `:t` or dependency source.

## Where truth lives

| Layer | Role |
| --- | --- |
| Production (`TensorNetwork.*`, etc.) | Categorical morphisms; no basis arithmetic |
| `*.Reference` | Explicit oracles for QuickCheck |
| `scripts/*.hs` | Probes, MREs, profiling — not production truth |
| `test/` | Property suite; run at milestones |

## Handback

When finishing a task, report: what changed, how verified (lib build / tests /
probe), and what remains open or blocked.

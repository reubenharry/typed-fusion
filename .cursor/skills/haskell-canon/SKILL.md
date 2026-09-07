---
name: haskell-canon
description: >-
  Apply design lessons distilled from exemplary Haskell libraries (ekmett ad,
  linear, discrimination, bound; recursion-schemes). Use when designing APIs,
  choosing type structure, writing folds/sweeps, or when the user asks to study
  or extend the Haskell canon lessons.
---

# Haskell canon (ongoing)

Lessons from libraries we treat as style references. Full notes live in
[lessons.md](lessons.md) — read that before inventing new API shape.

## When designing, ask

1. **Does the code look like the maths?** Compositional structure (morphisms,
   tensors, cups, folds-as-schemes) should mirror the mathematical presentation
   — this is the main advantage of Haskell for this project
2. **Parse, don’t validate?** ([King](https://lexi-lambda.github.io/blog/2019/11/05/parse-don-t-validate/):
   return a refined type; strengthen args; push proof to the boundary — bound
   `Scope` / `Var`, ad `forall s` branding)
3. **Is there a named scheme for the recursion?** (recursion-schemes `cata` /
   `ana` / `hylo`) — write the algebra, not the traversal plumbing
4. **Is the API a small family with systematic variants?** (ad suffixes;
   discrimination `group` / `groupWith`) rather than one-off names
5. **Final encoding vs initial?** Prefer combinators/instances you can compose
   (`contramap`, class methods) over a closed GADT you must extend by cases
6. **Power-to-weight?** bound's own docs prefer Derived over Overkill — do not
   add polymorphic kinds / deep branding unless the bug class is real here
7. **Public vs Internal?** Safe façade; partial/unsafe helpers stay out of the
   production import path (ad's `Internal.*`)
8. **Type-driven process?** Outer program + `undefined` stubs; localize type
   errors with holes; prefer folds and existing classes
   ([Haskell Guide](https://haskell-docs.netlify.app/))
9. **Call sites / library first?** Grep callers before exporting; prefer
   linearmap/hmatrix constructors over buffer unpack or parallel wrappers
   (see Anti-boilerplate in `haskell-practices.mdc`)

## Quantum mapping (short)

| Canon idea | Where it bites here |
| --- | --- |
| Math ≅ code | Fusion/compact-closed structure → Hom, cups, F-moves, compose ladders |
| Branding / rank-2 | Don't let bond/`C n` values leak across mismatched χ; keep centres typed |
| Algebra vs scheme | N-site folds, env zipper, transfer products — name the fold once |
| Systematic API | Fixed vs General: extend families, don't fork renames |
| Final encoding | Prefer morphism composition over case-on-representation |
| Enrich Eq/Ord | Props should state laws next to the computational path |

## Extending the study

When continuing (user request or long-running task):

1. Pick one package from [lessons.md](lessons.md) marked `pass-1`
2. Read Hackage module docs (not just the README)
3. Add 3–8 concrete lessons with **quantum applicability**
4. Promote only stable, actionable items into
   `.cursor/rules/haskell-practices.mdc` and `AGENTS.md`

# Claude / external agents

Follow [`AGENTS.md`](AGENTS.md).

Hard policy lives in [`.cursor/rules/`](.cursor/rules/). Day-to-day workflow:
skill `quantum-dev-loop` under [`.cursor/skills/`](.cursor/skills/). After
edits, verify with `cabal build quantum:lib:quantum`; run `cabal test` at
milestones only. Do not use tricorder in the default loop. For API/design taste
from the Haskell canon libraries, see skill `haskell-canon`.

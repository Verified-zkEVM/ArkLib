# Additions to VCV-io not yet in the pinned dependency

This directory mirrors VCV-io's module structure (`OracleComp/`, `EvalDist/`,
`ToMathlib/`, ...). Each file holds `simulateQ` / `OracleComp` / distribution
lemmas that ArkLib needs but that the currently-pinned VCVio commit predates,
plus ArkLib-local additions that are candidates for upstreaming.

Workflow: prefer landing general statements upstream in VCV-io under the same
names and the mirrored path; on the next VCVio bump, delete the corresponding
declaration here and let references resolve to the upstream version.

## Staging state (2026-06-12)

Everything generic in this directory is staged on the VCV-io branch
`feat/simulateq-routing-lemmas` (commits `c8e953c2` + `a1e79b1b` + `01ff338f`,
PR pending). **At the first VCVio bump past that branch's merge, delete the
mirrored declarations here** — they were verified to be same-name drop-ins
(some upstream versions are *generalized*: `ProbComp` → generic monad,
`StateT σ ProbComp` → lawful target; all unify at ArkLib's instantiations).
Before deleting, confirm the bump actually carries them.

Three local names resolved to pre-existing upstream lemmas — **DONE 2026-07-18**
(dedup pass): call sites renamed and the local mirrors deleted.

| ArkLib-local name (removed) | upstream replacement |
|---|---|
| `OptionT.failure_bind` | `failure_bind` (Batteries, `@[simp]`) |
| `StateT.run'_map_comm` | `StateT.run'_map'` (arg order differs: pass the state explicitly) |
| `OracleComp.bind_liftComp_map` | `bind_map_left` (Mathlib) |

**Not staged (genuinely ArkLib-specific, keep):**
`OracleComp/RbrGame.lean` — references ArkLib's `ProtocolSpec`
(challenge-query resolution + the rbr/KS game master mixture lemmas).

History note: `simulateQ_list_forIn` was staged here and has been deleted —
the VCVio pin (`5f7707fb`, Lean 4.30 bump) now contains it upstream.

History note (2026-07-18, dedup pass): the three rename-lemmas above were
removed and their call sites re-pointed to upstream; the now-empty file
`ToVCVio/ToMathlib/Control/StateT.lean` was deleted. Separately,
`Data/Probability/Notation.lean`'s `Pr_eq_tsum_indicator` was removed as a
duplicate of `Probability.prob_tsum_form_singleton`
(`Data/Probability/Instances.lean`).

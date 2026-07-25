# Additions to VCV-io not yet in the pinned dependency

This directory mirrors VCV-io's module structure (`OracleComp/`, `EvalDist/`,
`ToMathlib/`, ...). It holds `simulateQ` / `OracleComp` / distribution lemmas
that ArkLib needs but that the pinned VCVio commit predates, plus ArkLib-local
additions that are candidates for upstreaming.

Several files are now **compatibility shells**: their contents were upstreamed
and deleted, leaving only the `import` so downstream modules keep resolving.
`EvalDist/Defs/Support.lean`, `EvalDist/Instances/OptionT.lean`,
`OracleComp/EvalDist.lean`, `OracleComp/Coercions/SubSpec.lean`, and
`OracleComp/SimSemantics/SimulateQ.lean` are all in that state. They can be
removed once their importers are re-pointed upstream.

Workflow: prefer landing general statements upstream in VCV-io under the same
names and the mirrored path; on the next VCVio bump, delete the corresponding
declaration here and let references resolve to the upstream version.

## Staging state (2026-07-25)

The generic material previously staged here on the VCV-io branch
`feat/simulateq-routing-lemmas` (commits `c8e953c2` + `a1e79b1b` + `01ff338f`)
**has been upstreamed and removed.** That branch merged as `962e446`
(2026-06-30) and is an ancestor of the current pin
`cbd4144b` (`inputRev v4.31.0`), so the mirrors are gone and references now
resolve upstream. Some upstream versions are *generalized* (`ProbComp` → generic
monad, `StateT σ ProbComp` → lawful target, `Type` → `Type*`); all unify at
ArkLib's instantiations.

Local names resolved to pre-existing upstream lemmas — call sites renamed and
the local mirrors deleted. **These three rows are the deletions relative to the
current baseline**; `git log` is the authority for anything older:

| ArkLib-local name (removed) | upstream replacement |
|---|---|
| `StateT.run'_map_comm` | `StateT.run'_map'` (named args `(f := …)` at the call sites) |
| `OracleComp.bind_liftComp_map` | `bind_map_left` (Mathlib) |
| `simulateQ_randomOracle_map_uniformFin` | identical lemma in VCVio `RandomOracle/Simulation.lean` |

**Not staged (genuinely ArkLib-specific, keep):**
`OracleComp/RbrGame.lean` — references ArkLib's `ProtocolSpec`
(challenge-query resolution + the rbr/KS game master mixture lemmas). It is the
one file here that imports `ArkLib/OracleReduction/`. Part of its content lands
ahead of its consumers; see the staging note in that file's module docstring.

History note: `simulateQ_list_forIn` was staged here and has been deleted — the
then-current VCVio pin (`5f7707fb`, the Lean 4.30 bump) already contained it
upstream.

History note (2026-07-25, v4.31.0 bump `cbd4144b`): the three lemmas in the table
above were removed and their call sites re-pointed upstream, and the resulting
empty files `ToVCVio/ToMathlib/Control/StateT.lean` (deleted),
`OracleComp/SimSemantics/SimulateQ.lean` and `OracleComp/Coercions/SubSpec.lean`
(both reduced to shells) were cleaned up.

Scope caveat, because it is easy to overstate: a much larger dedup — roughly 550
lines across `SimulateQ.lean` and `RbrGame.lean` — was performed while porting the
ABF26 work onto this baseline, but those lemmas were **never present here**. They
existed only on the source branch `feat/abf26-plan`, so that cleanup shows up as
code *not added* rather than as deletions. Against this baseline the removal is
just the three lemmas above.

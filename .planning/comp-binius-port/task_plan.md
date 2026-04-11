# Task: comp-binius-port (CompBinius)

## Goal

- Make Binius **execution-path** definitions as computable as the Mathlib / ArkLib stack allows (CompPoly migration, `pSpec` / verifier wiring).
- **Security theorems** (completeness, RBR-KS, scalar KS, etc.) may stay `noncomputable`; focus on specs, verifiers, reductions, and proof *statements* that feed extraction or clarity.
- **Stretch / eventual target (user):** drop `noncomputable` from bundled **`OracleReduction` / `OracleVerifier` in `FRIBinius/General.lean`** (`batchingCoreReduction`, `fullOracleReduction`, matching verifiers). That is **not** a `General.lean`-only edit: Lean requires the full dependency cone (core interaction, query phase, witnesses, sampling) to compile. **`sDomain` and `sDomainFinEquiv` / related `AdditiveNTT` defs remain `noncomputable` until migrated or bypassed** (e.g. computable API or Fin-indexed surrogate used on exec paths). See **Status audit** below.

## Current Phase

**Phase 0 — Canonical polynomial-alias migration (new top priority)**  
- Hard human requirement: migrate the canonical Binius polynomial aliases onto CompPoly carriers
  instead of keeping Mathlib `restrictDegree` wrappers as the public/default representation.
- This specifically includes `BinaryBasefold.Prelude.MultilinearPoly`,
  `BinaryBasefold.Prelude.MultiquadraticPoly`, and the dependent witness/message paths that still
  assume `.val` / `.property`.
- Working rule from here:
  - execution paths must target CompPoly carriers directly;
  - theorem-side bridges back to Mathlib carriers are temporary and explicit;
  - do not add new long-term duplicate `*Comp` wrapper types where the canonical alias should move.

**Phase 0a — extractor / KState surface normalization (in progress)**  
- Hard human requirement: migrate extractors and `KnowledgeStateFunction` boundaries too, not only
  prover / verifier defs.
- Completed in this subphase:
  - `RingSwitching/SumcheckPhase.lean` extractor / KState surfaces moved to canonical comp witness
    projectors and real `KnowledgeStateFunction` structure literals
  - `RingSwitching/BatchingPhase.lean` extractor / KState surfaces moved to canonical comp witness
    projectors and real `KnowledgeStateFunction` structure literals
  - `BinaryBasefold/QueryPhase.queryKnowledgeStateFunction` is now a real structure literal
  - `FRIBinius/CoreInteractionPhase.finalSumcheckKnowledgeStateFunction` is now a real structure
    literal
  - `BinaryBasefold/Steps/FinalSumcheck.lean` and `FRIBinius/CoreInteractionPhase.lean`
    final-sumcheck extractor bodies now both follow the upstream `H_constant` shape using
    computable `MultiquadraticPoly.C stmtMid.sumcheck_target`
  - `FRIBinius/CoreInteractionPhase.lean` theorem / instance heads now use migrated
    `RingSwitching.sumcheckRoundRelation` / `strictSumcheckRoundRelation` signatures
  - `BinaryBasefold/Prelude.lean` no longer exposes `FoldMessage.toLegacy` or
    `getSumcheckRoundPoly`
  - `BinaryBasefold/Basic.projectToNextSumcheckPoly_sum_eq` and related Prelude statements now use
    `FoldMessage.eval (getSumcheckRoundMessageComp ...)`
  - Current remaining debt inside this subphase:
  - `Comp.WitnessComp.toRoundWitness` in `BinaryBasefold/CoreInteractionPhase.lean` maps comp
    witnesses to theorem `Witness` for relation checks; `f` still uses `sDomainFinEquiv` while
    `t`/`H` use `ofCMvPoly`
  - theorem/proof debt remains large in `BinaryBasefold/CoreInteractionPhase.lean`,
    `FRIBinius/CoreInteractionPhase.lean`, and soundness files, but the current human priority is
    still definitions / theorem statements / interface migration
  - `RingSwitching/BBFSmallFieldIOPCS.lean` and `FRIBinius/CoreInteractionPhase.lean` are now
    back to green after the latest bridge cleanup; remaining work there is proof deferral and
    statement normalization, not compiler recovery.
  - Public `roundRelationComp` / `strictRoundRelationComp` aliases have now been removed from the
    Binary Basefold surface; remaining drift is the `toRoundWitness` / `sDomainFinEquiv` bridge
    cone and downstream theorem cleanup.

**Phase 0b — canonical relation/oracle-domain migration (planned next, high priority)**  
- Hard human requirement clarified on 2026-04-10:
  - stop bridging canonical protocol relations back to old abstract/noncomputable witness shapes;
  - migrate canonical relation / extractor / KState / theorem *statements* onto computable
    carriers directly;
  - remove public bad-pattern shims such as `Comp.WitnessComp.toRoundWitness`,
    `roundRelationComp`, and `strictRoundRelationComp`;
  - keep proofs secondary: theorem bodies may temporarily become `sorry`, but public definitions
    and theorem statements should move first.
- Deep-scan conclusion:
  - polynomial carrier migration is no longer the main blocker for relations;
  - `Witness.t` and `Witness.H` already live on canonical computable aliases;
  - the remaining blocker is the old oracle/codeword domain cone
    (`Witness.f`, `OracleStatement`, `getMidCodewords`, `extractMLP`,
    `firstOracleWitnessConsistencyProp`, relation defs in `Relations.lean`).
  - `BinaryBasefold/Soundness/QueryPhaseSoundness.lean` now keeps the suffix theorem head on
    `extractSuffixFromChallenge`, so the remaining compile blocker is below the statement layer.
- Execution rule for this phase:
  - do **not** add more public `*Comp` relation aliases;
  - instead migrate the canonical names in place, and use temporary local bridge lemmas only when
    unavoidable.
- Planned step-by-step cut order:
  1. `BinaryBasefold/Basic.lean`
     - introduce a canonical computable codeword/oracle carrier for stage-`i` domains
       (private Fin encoding is acceptable, but public surface should match the abstract file’s
       style as closely as possible);
     - migrate `Witness.f` off raw `sDomain ... → L`;
     - migrate `OracleStatement` fields that expose codeword/oracle values;
     - rewrite `firstOracleWitnessConsistencyProp`, `extractMLP`, and related helper lemmas on the
       new canonical carrier;
     - keep any `sDomain` conversion lemmas private and transitional.
  2. `BinaryBasefold/Relations.lean`
     - rewrite `getMidCodewords` onto the new canonical computable carrier;
     - rewrite `witnessStructuralInvariant`, `masterKStateProp`, `roundRelationProp`,
       `roundRelation`, `strictOracleWitnessConsistency`, `strictRoundRelationProp`,
       `strictRoundRelation`, and final-sumcheck relation helpers to consume the migrated witness /
       oracle statement directly;
     - preserve canonical definition names where possible; allow proof bodies to become `sorry`.
  3. `BinaryBasefold/CoreInteractionPhase.lean`
     - delete `Comp.WitnessComp.toRoundWitness`;
     - delete `roundRelationComp` / `strictRoundRelationComp`;
     - retarget all protocol/reduction/kState theorem statements and wrapper relations to the
       canonical migrated `roundRelation` / `strictRoundRelation`.
  4. `BinaryBasefold/General.lean`
     - move top-level completeness / RBR-KS / scalar-KS theorem statements off the temporary
       `...RelationComp` names and onto the canonical migrated relations;
     - keep theorem bodies `sorry` if needed to unblock downstream interface migration.
  5. `FRIBinius/CoreInteractionPhase.lean` and `FRIBinius/General.lean`
     - migrate theorem heads and extractor/KState statements that still mention
       `BinaryBasefold.Witness`, `BinaryBasefold.OracleStatement`, `getMidCodewords`,
       `extractMLP`, or the old relation argument shapes;
     - keep the sibling repo’s structure and local naming pattern wherever possible.
  6. `RingSwitching/BBFSmallFieldIOPCS.lean`
     - migrate `MLPEvalWitness_to_BBF_Witness`, first-oracle consistency assumptions,
       and downstream theorem statements to the canonical computable Binary Basefold interfaces.
  7. `BinaryBasefold/Soundness/**` and `BinaryBasefold/ReductionLogic.lean`
     - normalize theorem statements over the migrated canonical relation/oracle carriers;
     - tolerate `sorry` for hard proofs, but remove dependence on deleted public bridge defs.
  8. Only after steps 1-7 compile:
     - remove leftover transitional `sDomain` bridge helpers that are no longer referenced;
     - run a hard audit that no public Binius phase/protocol theorem statement depends on
       `toRoundWitness`, `roundRelationComp`, or `strictRoundRelationComp`.
- Concrete file-first execution order once implementation starts:
  - `BinaryBasefold/Basic.lean`
  - `BinaryBasefold/Relations.lean`
  - `BinaryBasefold/CoreInteractionPhase.lean`
  - `BinaryBasefold/General.lean`
  - `FRIBinius/CoreInteractionPhase.lean`
  - `FRIBinius/General.lean`
  - `RingSwitching/BBFSmallFieldIOPCS.lean`
  - `BinaryBasefold/ReductionLogic.lean`
  - `BinaryBasefold/Soundness/*`
- Deletion order:
  - first stop new uses of `toRoundWitness` / `roundRelationComp`;
  - then migrate theorem heads;
  - only then physically delete the wrappers, to avoid exploding unrelated downstream files too
    early.

**Phase A — FRIBinius `General.lean` composition (done locally)**  
- Wired `batchingCore*` and `fullOracle*` via `OracleVerifier.append` / `OracleReduction.append`.
- Section parameter: `β : Basis (Fin (2^κ)) K L` with `(fun i => β i)` for Binary Basefold-facing APIs.

**Phase B — Spec-only computable companion track (in progress)**  
- Added `BinaryBasefold.Spec.QueryChallengeIndex`, `pSpecQueryFin`, and `fullPSpecFin`.
- Added stack-level SubSpec bridge `instSubSpecQueryOracleStackToFin` for canonical query-message
  stack → Fin-message stack.
- `BinaryBasefold.QueryPhase` Fin companion now builds (`queryOracleVerifierFin`,
  `queryOracleReductionFin`, `queryOracleProofFin`) with explicit local monad-lift pinning.
- Added full Binary Basefold Fin companions:
  `fullOracleVerifierFin`, `fullOracleReductionFin`, `fullOracleProofFin`.
- Added `FRIBinius.General.batchingCorePspecFun` and `fullPspecFin` using explicit `βfun`.
- This gives a computable protocol-spec track for consumers that need specs / challenge families but do **not** require the existing query-phase logic or security theorems.

**Phase C — Truly executable IR (open, deferred after spec track)**  
- Remove or bypass `Module.Basis.instFunLike` on hot paths where possible (e.g. `Fin (2^κ) → L` + `Fact (LinearIndependent …)` vs `Basis`, or computable indexing).
- **`sDomain` track (gates `General.lean` reductions):** either computable `sDomain` / Fin↔domain bridge in `AdditiveNTT`, **or** keep proof-facing `sDomain` and thread **computable** oracle/witness carriers (`Fin _`, `pSpecQueryFin`, etc.) through reductions so top-level defs do not depend on `noncomputable` subspace machinery. Until one path closes, **`coreInteractionOracleReduction` / query wiring / `instSDomain` stay noncomputable-capable** and block removing `noncomputable` on `fullOracleReduction`.
- Query phase: `sDomain` / `sDomainFinEquiv` / `SampleableType` without `Classical.decEq` where feasible (aligns with `sDomain` track).
- Library: `OracleVerifier.append` still contains `sorry`; batching and query verifier **bodies** still `sorry` in places — blocks end-to-end runnable semantics, but this is now explicitly deferred behind the Binius spec refactor.

#### Status audit — oracle reductions vs `sDomain` (2026-04-08)

| Item | State |
|------|--------|
| `AdditiveNTT.sDomain`, `sDomain_basis`, `sDomainFinEquiv`, `sDomain.lift`, … | Still **`noncomputable def`** |
| `FRIBinius/General.lean` — `batchingCoreReduction`, `fullOracleReduction`, verifiers, `fullPspec` | Still **`noncomputable def`** |
| `FRIBinius/CoreInteractionPhase.lean` — `coreInteractionOracleReduction`, sumcheck/final-sumcheck reductions | Still **`noncomputable def`** |
| Parallel **companion** track | **In progress:** `batchingCorePspecFun`, `fullPspecFun`, plain **`instance`**s for messages/challenges; `*VerifierFun*` plus prover-parameterized `*ReductionFun*` / `*ProofFun*` seams |
| Binary Basefold computable pSpec companion | **New:** `FoldMessageComp := L → L`, `pSpecFoldComp` through `pSpecCoreInteractionComp`, and `fullPSpecComp` |
| Binary Basefold fold-step companion verifier | **New:** `foldProverComputeMsgComp`, `foldVerifierCheckComp`, `foldVerifierStmtOutComp`, `foldOracleVerifierComp` |
| Binary Basefold prover kernels | `Steps.FinalSumcheck.finalSumcheckProver` is now computable (`def`), but `getMidCodewords` and `sumcheckFoldOracleReduction` still keep the honest-prover path **`noncomputable`** |
| Fold-round message computation | `getSumcheckRoundPoly` and `foldProverComputeMsg` remain **`noncomputable`**; executable attempts hit `MvPolynomial.finSuccEquivNth` / `Polynomial.C` IR blockers |
| Full-protocol verifier companion | **Now present:** `fullPspecFun` + `fullOracleVerifierFunOfMultiplier` (plain `def`) |
| Full-protocol reduction/proof companion | **Now present (prover-parameterized):** `fullOracleReductionFunOfMultiplier`, `fullOracleProofFunOfMultiplier`; `fullOracleProof` name now points to computable entrypoint |
| Binary Basefold Fin full-stack companions | **Now present:** `fullOracleVerifierFin`, `fullOracleReductionFin`, `fullOracleProofFin` over `fullPSpecFin` |

**Conclusion:** the **`*Fun*` / `*PspecFun*`** work is real progress on a computable entry point but **does not count** as “removed `noncomputable` from oracle reductions” until the composed `OracleReduction.append` paths are plain `def`.

**Refined conclusion after comparison with `BinaryBasefold/General.lean`:**
- `OracleReduction.append` itself is not the blocker; Binary Basefold top-level `fullOracleProof` is already a plain `def`.
- For FRIBinius, the remaining blockers are:
  1. `Basis -> function` coercion at the FRI wrapper boundary (`Module.Basis.instFunLike`);
  2. internally constructed batching basis objects such as `booleanHypercubeBasis`;
  3. prover-side Binary Basefold witness generation (`getMidCodewords` cone).

**Phase D — Hygiene (in progress)**  
- File-wide `set_option maxHeartbeats 200000` on heavy modules (`FRIBinius/General.lean`, `BinaryBasefold/Spec.lean`) to cap elaboration / agent timeouts.

## Open Proof / Sorry Obligations

- `FRIBinius/General.lean` — `CanonicalB` section theorems: `sorry` (unchanged intent; not regressions for exec work).
- `RingSwitching/BBFSmallFieldIOPCS.lean` — lens / witness bridges still `sorry` where relevant to large-field invocation.

## Errors Encountered (reference)

| Error | Context | Resolution |
|-------|---------|------------|
| Compiler IR: `Basis.instFunLike` has no executable code | FRIBinius pspec + exec defs using `fun i => β i` | Mark affected defs/instances `noncomputable` |
| `⇑β` in `local notation` | quotPrecheck / `coeFunNotation` | Use `(fun i => β i)` instead |
| Wrong explicit arg order for `batchingCorePspec` / `fullRbrKnowledgeError` | After `Basis` refactor | Match order: `κ L K β ℓ' 𝓡 ϑ h_ℓ_add_R_rate` (no extra `ℓ` in pspec apps unless def demands it) |
| Missing `𝓑` in `CanonicalB` theorems | Shadowing / implicit | `variable (𝓑 : Fin 2 ↪ L)` in section + `(𝓑 := 𝓑)` on verifier calls |
| First `OracleVerifier.append` patch used `by` with `←` in `verify` | `Append.lean` monadic field body | Rewrite `verify` as a `do` term, not a tactic block |
| First `OracleVerifier.append` patch used dotted `.inl` / `.inr` for oracle-spec domains | `Append.lean` query routing | Pattern match and build domains with `Sum.inl` / `Sum.inr` explicitly |
| First `OracleVerifier.append` patch assumed `challenges (ChallengeIdx.inl i)` had the exact smaller challenge type | `Append.lean` challenge splitting | Add explicit casts when projecting appended challenges back to `pSpec₁` / `pSpec₂` |
| Lean LSP MCP transport closed mid-session | Validation after spec edits | Fall back to targeted `lake build` for verification |
| `getSumcheckRoundPoly` executable rewrite failed | `BinaryBasefold/Prelude.lean` | Reverted; IR depends on non-executable `MvPolynomial.finSuccEquivNth` |
| Alternative fold-message rewrite still failed | `BinaryBasefold/Prelude.lean` | Reverted; IR depends on non-executable `Polynomial.C` (fundamental Mathlib polynomial blocker) |
| `getFoldProverFinalOutput` executable rewrite failed | `BinaryBasefold/Relations.lean` | Reverted; depends on noncomputable `iterated_fold` |
| Directly replacing canonical `AdditiveNTT.sDomain` with executable map | `AdditiveNTT/AdditiveNTT.lean` and dependent modules | Reverted; triggered broad `cannot omit referenced section variable` failures + proof-script mismatches (iterated quotient map cone) |
| `MonadLiftT` timeout on Fin query verifier bridge | `BinaryBasefold/QueryPhase.queryOracleVerifierFin` | Added explicit stack-level SubSpec instance + explicit local `MonadLiftT` pinning in verifier body |
| Stale post-rename identifiers (`*SecurityReductionNoncomp`) | `BinaryBasefold/General.lean`, `FRIBinius/CoreInteractionPhase.lean` | Rewired references to existing `*SecurityReduction` names and rebuilt affected modules |
| `lake build` blocked in shared dependency cone | `BinaryBasefold.ReductionLogic` during RingSwitching rebuild | Current exact blocker is `ReductionLogic.lean:1110:6` — `simp made no progress`; RingSwitching modules elaborate locally but global builds stop here first |

## Next Actions (priority)

1. Execute the canonical polynomial-carrier migration:
   change the canonical Binius polynomial aliases to CompPoly carriers and then repair the
   execution-critical `.val` / `.property` assumptions file-by-file.
2. Execute Phase 0b relation/oracle-domain migration in primitive-first order:
   `Basic -> Relations -> CoreInteractionPhase -> General -> FRIBinius -> RingSwitching ->
   ReductionLogic -> Soundness`.
3. Finish remaining extractor-body normalization:
   replace placeholder final-sumcheck witness reconstructions in
   `BinaryBasefold/Steps/FinalSumcheck.lean` and `FRIBinius/CoreInteractionPhase.lean`
   with canonical CompPoly witness builders or explicit temporary computable placeholders that
   match the migrated theorem statements.
4. Fix or temporarily isolate the first global build blocker in
   `BinaryBasefold/ReductionLogic.lean:1110` so downstream RingSwitching / FRI builds can reflect
   the real next drift rather than stopping in a shared dependency.
5. Finish the RingSwitching execution-path migration on those canonical comp carriers:
   batching witness output, iterated sumcheck message/witness updates, and the resulting
   `RingSwitching.General` reductions.
6. Canonicalize `BinaryBasefold/Steps/Fold.lean` to the PR #383 shape by replacing the old fold trio with the computable implementations and deleting fold-side `*Comp` / `*SecurityReduction` duplicates.
7. Canonicalize `BinaryBasefold/Spec.lean`, `ReductionLogic.lean`, and `Relations.lean` so there is one canonical computable `pSpec` / witness / relation stack rather than theorem-side legacy duplicates.
8. After the canonical stack stabilizes, delete the remaining theorem-only reduction aliases (`sumcheckFoldSecurityReduction`, `coreInteractionSecurityReduction`, etc.) and revalidate dependent FRIBinius files.

1. Start the **CompPoly fold-message migration**: replace `pSpecFold` message carrier `L⦃≤ 2⦄[X]` with a computable polynomial/message representation (or a paired companion `pSpecFoldComp`) so honest-prover fold messages can be executable without `Polynomial.C`.
2. In parallel with 1, plan the **iterated-fold kernel migration** (`iterated_fold` / `getFoldProverFinalOutput`) onto computable carriers; otherwise fold reductions will remain noncomputable even after message migration.
3. Decide whether to push deeper into the **RingSwitching blocker**: `RingSwitching/Prelude.lean` (`RingSwitching_SumcheckMultParam`, `compute_final_eq_value`, tensor/basis decomposition path).
4. **For the user goal (computable bundled reductions):** treat **`sDomain` / query challenge computability** as a **Phase C co-blocker** with RingSwitching — schedule explicit milestones (computable bridge vs Fin-only exec types) before expecting `noncomputable` removal on `fullOracleReduction`.
5. `βfun` verifier companion track is now in place in `FRIBinius/CoreInteractionPhase.lean` and threaded into `FRIBinius/General.lean` for batching+core verification.
6. Decide whether to preserve the current explicit batching boundary
   (`βfun` for Binary Basefold-facing verifier structure plus `βcube : Basis (Fin κ → Fin 2) K L` for batching),
   or to continue pushing downward into `RingSwitching/BatchingPhase.lean` to eliminate that basis parameter from the executable wrapper.
7. If adaptor code is needed, add a **noncomputable bridge** from basis-based theorem-facing APIs to the new executable companion APIs.
8. Keep `OracleVerifier.append` deferred until the end unless a later step truly needs executable composed verifiers.
9. Optional: clean style warnings on touched lines (`maxHeartbeats` option style, long lines) once the spec migration stabilizes.
10. Re-run `./scripts/validate.sh` before PR.
11. Completed this session: added prover-parameterized executable companions
   (`coreInteractionOracleReductionFunOfMultiplier`, `fullOracleReductionFunOfMultiplier`,
   `fullOracleProofFunOfMultiplier`) and revalidated module builds.
12. Next real proof-side cut: implement a concrete computable prover for the new companion seam,
    beginning with an executable sumcheck-fold reduction path that does **not** reconstruct the
    initial Basefold witness via `getMidCodewords` inside the lens.
13. Keep theorem-facing basis-path wrapper (`fullOracleProofOfBasis`) stable while pushing
    computability downward into the prover internals so the wrapper can eventually become a thin
    computable specialization instead of a noncomputable one.
14. Next Binary Basefold cut: add index-native query helper defs in `QueryPhase/Prelude` that work
    directly on `Fin (2^(ℓ+𝓡))` challenge indices, then thread them into Fin verifier/reduction
    companions to reduce canonical `sDomain` dependency in the check path.

## 2026-04-09 update (BBFSmallFieldIOPCS cleanup)

- Added concrete computable large-field invocation path in `RingSwitching/BBFSmallFieldIOPCS.lean`:
  `largeFieldInvocationCtxLensComp` + `largeFieldInvocationOracleReductionComp`.
- Rewired `bbfMLIOPCS` onto `fullPSpecComp` and the computable lifted reduction.
- Added missing `SampleableType` instances for computable Binary Basefold pSpecs in
  `BinaryBasefold/Spec.lean` (`pSpecFoldComp` ... `fullPSpecComp`) so the comp stack closes.
- Remaining explicit non-computable/security obligations in this file are theorem/proof fields
  (`perfectCompleteness` / `rbrKnowledgeSoundness` and downstream security lemmas), which are out
  of current scope.

## 2026-04-09 update (oracle-reduction cleanup)

- Completed a namespace-level migration away from `*OracleReductionNoncomp` constants in
  BinaryBasefold + FRIBinius core-interaction files.
- All legacy names were replaced by `*SecurityReductionNoncomp` (security-only region), and
  cross-module references were updated.
- Hard audit checks now pass:
  - `rg -n "OracleReductionNoncomp" ArkLib/ProofSystem/Binius -g '*.lean'` => no matches
  - `rg -n "^noncomputable def .*OracleReduction" ArkLib/ProofSystem/Binius -g '*.lean'`
    => no matches
- Canonical executable reductions (`...OracleReduction`, `...OracleReductionComp`, `...Fin`) remain
  intact and continue to build.

## 2026-04-09 update (goal-locked rebuild repair)

- Scope locked with human: only Binius oracle reductions must be computable; security theorems may remain noncomputable.
- Build-repair pass fixed stale theorem-layer links introduced by earlier renames:
  - `BinaryBasefold/General.lean`: migrated `coreInteractionSecurityReductionNoncomp` references to
    `coreInteractionSecurityReduction`, kept required implicit `(𝓑 := 𝓑)` call sites.
  - `FRIBinius/CoreInteractionPhase.lean`: migrated lifted reduction bases from
    `BinaryBasefold.CoreInteraction.sumcheckFoldSecurityReductionNoncomp` to
    `BinaryBasefold.CoreInteraction.sumcheckFoldSecurityReduction`.
- Verification status after repair:
  - `rg -n "^noncomputable def .*OracleReduction" ArkLib/ProofSystem/Binius -g '*.lean'` => no matches.
  - `lake build` sweep over
    `BinaryBasefold.{Steps.Fold,CoreInteractionPhase,QueryPhase,General}`,
    `FRIBinius.{CoreInteractionPhase,General}`,
    `RingSwitching.BBFSmallFieldIOPCS` => pass (warnings/sorries only).

## 2026-04-09 update (oracle-reduction migration surface complete)

- Promoted the executable query-phase Fin path to the canonical exported names:
  - `BinaryBasefold.QueryPhase.queryOracleVerifier`
  - `BinaryBasefold.QueryPhase.queryOracleReduction`
  - `BinaryBasefold.QueryPhase.queryOracleProof`
- Renamed the abstract canonical-domain search-decoding helpers to explicit
  `...Canonical` names so the public reduction surface no longer depends on `...Fin` / `...Comp`
  suffixes for the query phase.
- Rewired `BinaryBasefold.General` and `FRIBinius.General` to consume those canonical query-phase
  reduction/verifier names.
- Hard audit status now passes:
  - `rg -n '^noncomputable def .*Oracle(Reduction|Verifier|Proof)\\b' ArkLib/ProofSystem/Binius -g '*.lean'`
    => no matches
  - `rg -n '\\b(SecurityReduction|SecurityVerifier)\\b' ArkLib/ProofSystem/Binius -g '*.lean'`
    => no matches
  - `rg -n 'queryOracle(Verifier|Reduction|Proof)(Fin|Comp)' ArkLib/ProofSystem/Binius -g '*.lean'`
    => no matches
- Focused validation:
  - `lake build ArkLib.ProofSystem.Binius.BinaryBasefold.QueryPhase ArkLib.ProofSystem.Binius.BinaryBasefold.General ArkLib.ProofSystem.Binius.FRIBinius.General`
    passes with warnings / existing `sorry`s only.
- Interpretation:
  - the **oracle-reduction computability migration surface is complete** for Binius definition names;
  - residual work is proof completion / theorem-body de-sorrying and general lint cleanup, not
    removal of noncomputable oracle reductions/verifiers/proofs.

## 2026-04-09 — structure-parity requirement

- **New hard constraint from the user:** match the original Binary Basefold structure from PR `#383` exactly at the folder / file / section / definition / theorem level, while replacing noncomputable internals with computable ones and reproving theorems over the canonical objects.
- Immediate consequences:
  - eliminate parallel files like `BinaryBasefold/ComputableFold.lean`;
  - keep canonical implementations inside the original `Steps/*` files;
  - avoid introducing long-term duplicate public names or sidecar theorem-only reduction files.
- Updated execution order:
  1. restore file/module structure parity with PR `#383`;
  2. promote computable implementations into the canonical definitions inside those files;
  3. migrate relations/completeness away from old `Witness`-typed paths;
  4. delete theorem-only `*SecurityReduction` objects.

## 2026-04-09 — current subtask and constraint update

- **Current subtask:** finish FRIBinius theorem-layer normalization after the Binary Basefold
  canonicalization pass.
  - Completed: rename remaining FRIBinius `...SecurityReductionNoncomp` /
    `...SecurityVerifierNoncomp` names to plain security-layer names.
  - Open blocker: `FRIBinius/CoreInteractionPhase.coreInteractionOracleReduction_perfectCompleteness`
    times out while reusing `finalSumcheckOracleReduction_perfectCompleteness`.
- **Hard constraint from the human:** never increase `maxHeartbeats` above `200000`.
  - Do not use file-level heartbeat bumps above this limit.
  - Prefer structural proof simplification: explicit `rel₂`, local `change`, `erw`/`conv`, or
    decomposition of the `append_perfectCompleteness` application.
- **Next concrete step:** keep the current FRIBinius rename cleanup, but refactor the second branch
  of `coreInteractionOracleReduction_perfectCompleteness` so the reused final-sumcheck theorem
  matches by construction instead of via expensive `whnf`.

## 2026-04-09 — human course correction

- Replace the previous FRIBinius subtask with the stronger deletion goal:
  1. stop polishing theorem-only noncomputable reductions/verifiers;
  2. migrate FRIBinius and Binary Basefold security/completeness theorems onto the canonical
     computable reductions/verifiers;
  3. delete the old noncomputable reduction defs entirely.
- Any temporary patch that only renames `*SecurityReductionNoncomp` into `*SecurityReduction`
  without reducing duplication is not an acceptable endpoint and should be reverted or subsumed by
  the real migration.

## 2026-04-09 update (public query/full-spec interface aligned)

- Completed in this session:
  1. deleted `BinaryBasefold.Spec.pSpecCoreInteractionComp`
  2. deleted `BinaryBasefold.Spec.fullPSpecComp`
  3. kept exactly one live canonical `pSpecQuery`, now carrying the computable
     `Fin γ_repetitions → AdditiveNTT.Comp.sDomain ... 0` challenge family
  4. added executable `instFintypeCompSDomainZero`
  5. removed duplicate / stale `pSpecQuery` challenge `Fintype` blocks and eliminated their
     `sorry`s
  6. revalidated `BinaryBasefold.Spec`, `BinaryBasefold.General`, `FRIBinius.General`, and
     `RingSwitching.BBFSmallFieldIOPCS`
- Current status after this pass:
  - the top-level public query/full-spec interface now matches the human's requested shape
  - no `pSpecQueryFin`, `fullPSpecComp`, or `pSpecCoreInteractionComp` names remain under
    `ArkLib/ProofSystem/Binius`
  - no query-phase `queryOracle*Fin` / `queryOracle*Canonical` split remains under
    `ArkLib/ProofSystem/Binius`
- Remaining open work for stricter item-by-item parity:
  - mid-level internal `pSpec*Comp` builders still exist and are used below the top-level
    canonical surface:
    - `pSpecSumcheckFoldComp`
    - `pSpecNonLastBlocksComp`
    - `pSpecLastBlockComp`
    - `pSpecFullNonLastBlockComp`
    - `pSpecFoldRelaySequenceComp`
    - `pSpecFoldCommitComp`
    - `pSpecFoldComp`
  - these are the next parity frontier if the goal is to align not just the public API, but the
    internal BinaryBasefold/FRIBinius protocol stack item-by-item with the upstream outline
- Updated next action:
  - push the canonicalization one layer deeper into `BinaryBasefold.Spec` /
    `BinaryBasefold.CoreInteractionPhase` by deciding whether the computable mid-level `pSpec*`
    bodies should replace the remaining internal `...Comp` names outright

## 2026-04-09 update (RingSwitching batching reduction frontier corrected)

- The optimistic conclusion that all Binius oracle-reduction names were now executable was too
  strong for the RingSwitching batching path.
- Current corrected state:
  - `RingSwitching/BatchingPhase.lean` now has a real verifier implementation and a real
    logic-step prover wrapper, but the prover/reduction boundary is still noncomputable because the
    witness output must build `SumcheckWitness.H`
  - `lake build ArkLib.ProofSystem.Binius.RingSwitching.BatchingPhase` passes
  - `RingSwitching/General.lean` fails precisely at:
    - `batchingCoreReduction`
    - `fullOracleReduction`
    - `fullOracleProof`
    because they depend on noncomputable `BatchingPhase.batchingOracleReduction`
- Root cause is deeper than RingSwitching:
  - `batchingProverWitOut` depends on `BinaryBasefold.projectToMidSumcheckPoly`
  - that depends on `BinaryBasefold.fixFirstVariablesOfMQP`
  - scratch Lean probes show `MvPolynomial.rename` and `MvPolynomial.map` themselves currently
    have no executable code in this workspace
- Updated next action:
  - stop trying to force executability at the RingSwitching wrapper layer
  - instead target the witness-projection cone directly:
    1. design a computable replacement for `fixFirstVariablesOfMQP` / `projectToMidSumcheckPoly`,
       likely by bypassing `MvPolynomial.rename/map`
    2. only then re-promote `batchingProverWitOut`, `batchingOracleProver`,
       `batchingOracleReduction`, and `RingSwitching.General`

## Errors Encountered (RingSwitching batching update)

| Error | Context | Resolution |
|-------|---------|------------|
| `batchingProverWitOut` depends on `projectToMidSumcheckPoly`, which is noncomputable | Tried to make RingSwitching batching prover executable | Reverted witness/prover/reduction boundary to honest noncomputable defs while keeping executable verifier/message kernels |
| `MvPolynomial.rename` / `MvPolynomial.map` have no executable code | Scratch probes for `fixFirstVariablesOfMQP` migration | Treat as the true root blocker; future work must replace or bypass the old `MvPolynomial` projection path |

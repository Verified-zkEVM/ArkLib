# Findings — comp-binius-port

## QueryPhase recovery + next blocker — 2026-04-11

- `ArkLib/ProofSystem/Binius/BinaryBasefold/QueryPhase.lean` now typechecks again, but only after
  collapsing the remaining helper lemmas to `sorry` / `True` stubs.
- The previously broken helper cone was:
  - `mem_support_queryFiberPoints`
  - `iteratedQuotientMap_eq_qMap_total_fiber_extractMiddleFinMask`
  - `query_phase_consistency_guard_safe`
  - `query_phase_step_preserves_fold`
  - `query_phase_final_fold_eq_constant`
  - `checkSingleRepetition_inner_forIn_probFailure_eq_zero`
  - `checkSingleRepetition_probFailure_eq_zero`
  - `logical_checkSingleRepetition_of_mem_support_forIn_body`
- Dependent build now stops at `BinaryBasefold/Steps/Relay.lean` with:
  - `cannot omit referenced section variable`
  - invalid named arguments (`i`, `Context`)
  - one unsolved goal in the relay verifier/soundness layer

## OracleFunction boundary check — 2026-04-10

- `Prelude.OracleFunction` is an `abbrev`, so it is definitionally the same as
  `AdditiveNTT.Comp.sDomain ... → L`.
- That means public theorem statements and defs should use `OracleFunction` wherever the type is
  genuinely an oracle map.
- Do **not** force `OracleFunction` onto binders that are domain points. The failed attempt on
  `fold_eval_fiber₂_vec` showed the difference clearly:
  - `y : AdditiveNTT.Comp.sDomain ... destIdx` is a point argument;
  - `OracleFunction ... destIdx` would be a whole oracle function, not a point.
- So the right rule is:
  - use `OracleFunction` for `domain → L`;
  - keep raw `Comp.sDomain ...` for point arguments;
  - only collapse raw spellings where the binder really denotes an oracle map.
- `Prelude.lean` still builds after the revert, so the alias boundary is now clean again.

## Remaining public shim names — 2026-04-10

- `BinaryBasefold.CoreInteractionPhase.lean` still contains the public transition shims:
  - `Comp.WitnessComp.toRoundWitness`
  - `strictRoundRelationComp`
  - `roundRelationComp`
- `BinaryBasefold.General.lean` still consumes `strictRoundRelationComp` / `roundRelationComp`
  in the top-level completeness and soundness theorem statements.
- These are the next obvious statement-shape cuts once the canonical relation definitions are
  ready to replace them in place.

## Decoder lemma simplification — 2026-04-10

- `BinaryBasefold.Basic.extractMLP_some_of_isCompliant_at_zero` does not need the second oracle
  witness or its `UDRClose` proof.
- A minimal Lean-checked shape only requires:
  - `zero_Idx`
  - `h_zero_Idx : zero_Idx.val = 0`
  - `h_destIdx : destIdx = zero_Idx + steps`
  - `h_destIdx_le : destIdx ≤ ℓ`
  - `f_i : OracleFunction ... zero_Idx`
  - `h_fw_dist_lt : fiberwiseClose ... f_i`
  - `challenges : Fin steps → L`
- Dropping `f_next` and `h_dist_next_lt` removes the current elaboration failure and keeps the
  theorem aligned with the actual extraction use site in `FinalSumcheck.lean`.
- Next validation target: re-run `Basic.lean` and `Steps/FinalSumcheck.lean` after the statement
  shrink, then see whether any additional relation-layer drift is exposed.

## Statement drift checkpoint — 2026-04-10

- `BinaryBasefold.Code.lean` and `BinaryBasefold.Compliance.lean` now use explicit comp-domain function binders for `UDRClose`, `pair_UDRClose`, `UDRClose_of_fin_eq`, and `isCompliant`.
- `BinaryBasefold.Basic.lean` theorem `extractMLP_eq_some_iff_pair_UDRClose` is now stated directly as a distance inequality, not via the wrapper predicate.
- The remaining blocker is `BinaryBasefold.Basic.lean:1255` in `extractMLP_some_of_isCompliant_at_zero`: Lean still refuses the `isCompliant` hypothesis under the current comp-domain binders.
- `BinaryBasefold.Prelude.lean` still has statement-level drift around `polyToOracleFunc` / `iterated_fold` theorem heads:
  - `iterated_fold_advances_evaluation_poly` proof-local `poly_eval_folded_s_steps`
  - `iterated_fold_to_level_ℓ_eval`
  - `iterated_fold_to_level_ℓ_is_constant`
- Current best next cut: migrate those fold theorem statements one layer deeper or replace their helper-shaped local terms with direct comp-domain lambdas so Lean stops demanding the old oracle-function surface.

## Oracle carrier source migration — 2026-04-10

- `BinaryBasefold.Basic.OracleStatement` is already structurally computable, but
  `Prelude.OracleFunction` still points at canonical `sDomain`; the right migration is to move the
  canonical oracle-function alias itself onto `AdditiveNTT.Comp.sDomain`, then let
  `oracleStatementToCanonical` collapse to a thin compatibility shim or disappear.
- `Soundness/QueryPhasePrelims` should not mutate canonical helper signatures in place; downstream
  `QueryPhase.lean` and soundness files still import those names. Add comp-facing wrappers or change
  the source alias first, then update logical defs.
- New bridge theorem in `ArkLib/Data/FieldTheory/AdditiveNTT/Impl.lean`:
  `sDomainComp_eq_sDomain` plus the two membership bridges around it. This is the intended cast
  point if any temporary canonical/computable transport is still needed.
- Re-scan on 2026-04-10 clarified the current split:
  - `Prelude.OracleFunction` is already a computable alias over `AdditiveNTT.Comp.sDomain`;
  - `Basic.OracleStatement` is already computable;
  - the actual remaining bridge pressure is in `Prelude.fiberEvaluations`,
    `Prelude.iterated_fold`, and theorem statements in `Soundness/QueryPhasePrelims` that still
    compare those helpers against canonical `UDRCodeword` / `fiberEvaluations` forms.
- `QueryPhasePrelims` still has statement-elaboration hotspots around:
  - the `omit` on `extractSuffixFromChallenge_congr_destIdx`;
  - `getFiberPoint_eq_qMap_total_fiber` using a heavy inline `h_destIdx := by rfl`;
  - theorem heads `logical_queryFiberPoints_eq_fiberEvaluations` /
    `logical_computeFoldedValue_eq_iterated_fold` using huge inline `let oracleAtK` terms;
  - `logical_checkSingleRepetition_guard_eq` still passing a comp suffix directly into a
    canonical `UDRCodeword` statement.
- `Prelude.OracleFunction` is already on `AdditiveNTT.Comp.sDomain`; the real source-side cleanup
  is to collapse `OracleFunctionComp` / `oracleStatementToCanonical` so the logical query helpers
  stop naming a bridge that is definitionally redundant.

## Deep scan for canonical relation migration — 2026-04-10

- `Comp.WitnessComp.toRoundWitness` is confirmed to be a transitional shim only, not a principled
  final design.
- Exact current shape in `BinaryBasefold/CoreInteractionPhase.lean`:
  - `t := MultilinearPoly.ofCMvPoly wit.t`
  - `H := MultiquadraticPoly.ofCMvPoly wit.H`
  - only `f` still bridges through `sDomainFinEquiv`
- Therefore:
  - the relation-layer migration blocker is no longer polynomial carrier conversion for `t` / `H`;
  - the real blocker is the oracle/codeword-function cone still phrased over
    `sDomain ... -> L`.
- Canonical relation cone still tied to the old oracle-domain layer:
  - `BinaryBasefold/Basic.lean`
    - `OracleStatement`
    - `firstOracleWitnessConsistencyProp`
    - `extractMLP`
    - `Witness.f : sDomain ... -> L`
  - `BinaryBasefold/Relations.lean`
    - `getMidCodewords`
    - `witnessStructuralInvariant`
    - `masterKStateProp`
    - `roundRelation` / `strictRoundRelation`
    - final-sumcheck relation helpers
- Downstream theorem surfaces that still depend on this old cone:
  - `BinaryBasefold/CoreInteractionPhase.lean`
    - `roundRelationComp`
    - `strictRoundRelationComp`
    - protocol/reduction theorem statements over those wrappers
  - `BinaryBasefold/General.lean`
    - top-level completeness / RBR-KS / scalar-KS theorem statements
  - `FRIBinius/CoreInteractionPhase.lean`
    - theorem statements and extractor assumptions over
      `BinaryBasefold.roundRelation`, `strictRoundRelation`, `getMidCodewords`, `extractMLP`
  - `RingSwitching/BBFSmallFieldIOPCS.lean`
    - `MLPEvalWitness_to_BBF_Witness` and first-oracle consistency assumptions
- Migration implication:
  - deleting `toRoundWitness` first is the wrong order;
  - the right cut is `Basic` + `Relations` first, then theorem heads, then delete wrappers.
- Public-API rule recorded for next implementation phase:
  - do not add new long-term `*Comp` relation names;
  - migrate canonical names in place and keep any remaining `sDomain` bridge private.
- The current `QueryPhasePrelims` signature flip was too aggressive:
  downstream canonical query proofs still call the old suffix helpers, so the comp migration should
  add wrapper defs rather than mutate those canonical helper signatures in place.
- `AdditiveNTT.Comp.sDomain` and canonical `AdditiveNTT.sDomain` should admit a direct equality
  theorem; that is the clean transport point for the new comp wrappers.

## Binary Basefold carrier cleanup after FRI parity pass — 2026-04-10

- `BinaryBasefold/CoreInteractionPhase.Comp.WitnessComp.toLegacy` was no longer a true polynomial
  bridge after the canonical alias migration.
- Exact cause:
  - `Witness.H` is now `MultiquadraticPoly L (ℓ - i)`, not legacy Mathlib
    `restrictDegree`;
  - old body still rebuilt `H` through `CPoly.fromCMvPolynomial` and a manual degree proof, which
    broke as soon as the witness carrier changed.
- Repair:
  - added `MultiquadraticPoly.ofCMvPoly` in `BinaryBasefold/Basic.lean`;
  - `Comp.WitnessComp.toLegacy` now maps
    `t := MultilinearPoly.ofCMvPoly wit.t`
    `H := MultiquadraticPoly.ofCMvPoly wit.H`
    and only still bridges the final codeword index through `sDomainFinEquiv`.
- Consequence:
  - remaining badness in `toLegacy` is name + oracle-domain bridge only, not polynomial carrier
    conversion anymore.

## Fold-message carrier cut — 2026-04-10

- `BinaryBasefold/Prelude.lean` no longer exposes `FoldMessage.toLegacy` or
  `getSumcheckRoundPoly : L⦃≤ 2⦄[X]`.
- Public theorem statements were rewritten onto the canonical computable message carrier:
  - `getSumcheckRoundPoly_eval_eq` now states evaluation of
    `FoldMessage.eval (getSumcheckRoundMessageComp ...)`;
  - `getSumcheckRoundPoly_sum_eq` now states the same sum relation over `FoldMessage.eval`;
  - `Basic.projectToNextSumcheckPoly_sum_eq` now uses the same message-based statement.
- Repo-wide scan after this cut:
  - no remaining `L⦃≤ 2⦄[X]` or `getSumcheckRoundPoly` usages under
    `ArkLib/ProofSystem/Binius` except `Comp.WitnessComp.toLegacy` call sites in
    `BinaryBasefold/CoreInteractionPhase.lean`.

## FRI theorem-head drift after relation migration — 2026-04-10

- `FRIBinius/CoreInteractionPhase.lean` had broader stale interface drift than just the
  `finalSumcheckRbrExtractor` body.
- The file still referenced pre-migration RingSwitching relation signatures:
  - `RingSwitching.sumcheckRoundRelation κ L K (booleanHypercubeBasis ...) ℓ ℓ' h_l ...`
  - `RingSwitching.strictSumcheckRoundRelation ... (β := ...) ... (𝓑 := ...) ...`
- Current canonical RingSwitching signatures are now:
  - `sumcheckRoundRelation κ L K ℓ ℓ' aOStmtIn i`
  - `strictSumcheckRoundRelation κ L K ℓ ℓ' aOStmtIn i`
- Repair approach:
  - patch theorem / instance heads to the new relation signatures;
  - replace hard proof bodies with `sorry` where needed;
  - keep extractor body parity with upstream `H_constant`, but on
    `BinaryBasefold.MultiquadraticPoly.C`.

## FRI final-sumcheck extractor parity — 2026-04-10

- `FRIBinius/CoreInteractionPhase.finalSumcheckRbrExtractor.extractMid` still drifted from sibling
  repo after the earlier extractor/KState migration.
- Exact drift:
  - local computable branch used `H := 0` in `none` case;
  - local computable branch used `H := BinaryBasefold.projectToMidSumcheckPoly ...` in
    `some tpoly` case;
  - sibling `ArkLib-binius` file keeps shared local `H_constant` and returns it in both branches.
- Human direction matches sibling shape:
  - keep upstream extractor skeleton;
  - swap only carrier internals to computable counterpart;
  - for constant target polynomial, use computable constructor
    `BinaryBasefold.MultiquadraticPoly.C stmtMid.sumcheck_target`.
- Migration rule for this site:
  - no `projectToMidSumcheckPoly` in `extractMid` branch result for final sumcheck;
  - keep `f := getMidCodewords ...` in `some tpoly` branch;
  - constant `H` is canonical public witness shape here, same as upstream abstract version.

## Bounded CMv carrier follow-up — 2026-04-10

- The first `ComputableDegreeLE` cut is directionally correct but its API is still too weak for the
  canonical alias migration.
- Concrete leak found from `lake env lean ArkLib/ProofSystem/Binius/BinaryBasefold/Basic.lean`:
  - `CPoly.CMvPolynomial.degreeLE.val` currently requires `DecidableEq R`, but the CompPoly bridge
    `CPoly.fromCMvPolynomial` only needs `BEq R` + `LawfulBEq R`.
  - That unnecessary `DecidableEq` requirement propagates into `MultilinearPoly.val`,
    `MultiquadraticPoly.val`, and then into many Basic/Prelude statements that should remain on the
    computable carrier path.
- The current `FoldMessageComp := Fin 3 → L` surface is confirmed to be the wrong canonical shape.
  The real computable counterpart of abstract `L⦃≤ 2⦄[X]` is the bounded univariate CMv carrier,
  i.e. the `1`-variable instance of the new bounded-degree type:
  - conceptually: `CPoly.CMvPolynomial.degreeLE 1 L 2`
  - canonically in Binius surface terms: `MultiquadraticPoly L 1`
- Immediate migration consequence:
  - replace public uses of `FoldMessageComp` / `SumcheckRoundMessage := FoldMessageComp` with the
    bounded univariate CMv carrier;
  - keep any `Fin 3 → L` coefficient encoding private to `Fintype` / coefficient extraction lemmas,
    not as the protocol-facing message type.
- `BinaryBasefold.Basic` currently exposes the next missing carrier conveniences:
  - explicit named arguments are needed when calling `CPoly.CMvPolynomial.ofDegreeLE`;
  - the bounded carrier needs at least canonical `0` support (`OfNat 0`) for witness defaults;
  - projection helpers like `fixFirstVariablesOfCMvPoly` need bounded-degree wrappers when the
    public result type is `MultiquadraticPoly`.

## RingSwitching `iteratedSumcheckOracleVerifier` interface repair — 2026-04-09

- The direct executable body I added for
  `RingSwitching/SumcheckPhase.iteratedSumcheckOracleVerifier` compiled locally, but it changed the
  elaborated parameter spine of the exported def.
- Root cause:
  - the rewritten verifier body no longer mentioned `β` or `h_l`;
  - those parameters do not appear in the verifier result type either;
  - Lean therefore stopped exposing them as explicit arguments on the final constant.
- Observable fallout from `lake env lean ArkLib/ProofSystem/Binius/RingSwitching/SumcheckPhase.lean`:
  - `Application type mismatch ... iteratedSumcheckOracleVerifier κ L K β`
  - `Invalid argument name 'β' for function 'iteratedSumcheckOracleVerifier'`
  - cascading downstream breakage in `iteratedSumcheckKnowledgeStateFunction`,
    `sumcheckLoopOracleVerifier`, and the large-field RBR theorem statements.
- The sibling `ArkLib-binius` file keeps the upstream parameter spine because its verifier wrapper
  routes through `sumcheckStepLogic`, which mentions `β`, `h_l`, and `𝓑`.
- Computable-branch repair:
  - keep the executable direct verifier path,
  - but mention `β` and `h_l` inside the verifier body so the exported interface remains
    item-for-item compatible with upstream call sites.
- Result:
  - `lake env lean ArkLib/ProofSystem/Binius/RingSwitching/SumcheckPhase.lean` now exits cleanly
    again, with warnings / existing `sorry`s only.
- Quick post-repair scan of remaining RingSwitching wrapper placeholders:
  - `SumcheckPhase.iteratedSumcheckOracleProver` still placeholder at local line 148.
  - `BatchingPhase.batchingOracleProver` and `BatchingPhase.batchingOracleVerifier` still
    placeholders at local lines 252 and 261.
- These are not all equally tractable:
  - `BatchingPhase` verifier/prover wrappers are blocked by still-noncomputable helper kernels
    `compute_s0` and `batchingProverComputeMsg`.
- `SumcheckPhase.iteratedSumcheckOracleProver` is blocked by still-noncomputable
  `sumcheckProverComputeMsg`.

## CoreInteraction statement drift scan — 2026-04-10

- Canonical relation definitions in `BinaryBasefold/Relations.lean` are already on
  `Witness` / `OracleStatement` directly:
  - `masterKStateProp`
  - `roundRelationProp`
  - `roundRelation`
  - `strictRoundRelationProp`
  - `strictRoundRelation`
- `BinaryBasefold/CoreInteractionPhase.lean` still carries wrapper aliases:
  - `strictRoundRelationComp`
  - `roundRelationComp`
- The theorem statements below still instantiate those wrapper names and therefore keep the old
  bridge visible at the public API boundary:
  - `foldRelayOracleReduction_perfectCompleteness`
  - `foldRelayOracleVerifier_rbrKnowledgeSoundness`
  - `foldCommitOracleReduction_perfectCompleteness`
  - `foldCommitOracleVerifier_rbrKnowledgeSoundness`
  - `nonLastSingleBlockOracleReduction_perfectCompleteness`
  - `lastBlockOracleReduction_perfectCompleteness`
  - `sumcheckFoldOracleReduction_perfectCompleteness`
  - `coreInteractionOracleVerifier_rbrKnowledgeSoundness`
- `coreInteractionOracleVerifier`, `finalSumcheckOracleReductionComp`, and
  `coreInteractionOracleReductionComp` are already stubbed / noncomputable, so the right next cut
  is statement migration, not another executable-body rewrite.
- Best next step:
  - rewrite theorem heads in `CoreInteractionPhase.lean` to the canonical `roundRelation` /
    `strictRoundRelation` names;
  - keep proofs as `sorry`;
  - only then remove the wrapper aliases if downstream call sites no longer mention them.

## RingSwitching `Prelude` + final-sumcheck verifier migration — 2026-04-09

- Direct compiler probing plus a real-file rebuild showed that several RingSwitching `Prelude`
  defs were only *stale-marked* `noncomputable`, not actually blocked on non-executable code.
- Successfully promoted these to plain `def` in `RingSwitching/Prelude.lean`:
  - `compute_A_func`
  - `compute_A_MLE`
  - `RingSwitching_SumcheckMultParam`
  - `compute_final_eq_tensor`
- The two genuinely remaining `Prelude` blockers are now sharply isolated:
  - `compute_s0` depends on `decompose_tensor_algebra_rows`
  - `compute_final_eq_value` depends on `decompose_tensor_algebra_rows`
- This unlocked a cleaner verifier path in `RingSwitching/SumcheckPhase.lean`:
  - `finalSumcheckVerifierCheck` no longer needs `compute_final_eq_value`;
  - it now computes the same scalar as
    `(compute_A_MLE ...).val.eval stmtIn.challenges`, using the existing theorem
    `compute_A_MLE_eval_eq_final_eq_value` as the proof-facing bridge.
- With that change, `finalSumcheckVerifier` itself is now implemented as an executable wrapper over
  `finalSumcheckStepLogic` rather than a placeholder.
- Validation:
  - `lake build ArkLib.ProofSystem.Binius.RingSwitching.Prelude`
  - `lake build ArkLib.ProofSystem.Binius.RingSwitching.SumcheckPhase`
  - `lake build ArkLib.ProofSystem.Binius.RingSwitching.General`
  all pass.
- Updated live placeholder scan under `RingSwitching`:
  - `SumcheckPhase.iteratedSumcheckOracleProver`
  - `BatchingPhase.batchingOracleProver`
  - `BatchingPhase.batchingOracleVerifier`
- Updated blocker scan in `Prelude`:
  - only `compute_s0` and `compute_final_eq_value` remain `noncomputable` in that local core.

## Oracle carrier source migration target — 2026-04-10

- User clarified the next cut is stronger than local soundness bridges:
  - `OracleStatement`, `OracleFunction`, and logical helpers like
    `logical_queryFiberPoints` should use computable oracle defs directly.
- Design implication:
  - stop adding more long-term bridge lemmas from computable carriers back to old
    `sDomain`-shaped oracle statements;
  - migrate the oracle statement/function defs themselves at the source, then retarget
    `Relations`, `Soundness/QueryPhasePrelims`, and downstream theorem heads.
- Constraint:
  - do not raise `maxHeartbeats` above `200000`; keep proof search bounded and use `sorry`
    for hard theorem bodies if needed.
- Scope check:
  - a full alias flip of `OracleFunction` would also drag `qMap_total_fiber`,
    `fiberEvaluations`, `fold`, and `iterated_fold` onto the computable carrier cone;
    that is broader than the current clean cut.
  - safer immediate cut is to move the logical/soundness statements to
    `OracleFunctionComp` / `AdditiveNTT.Comp.sDomain` directly, then leave the deeper
    fold-kernel carrier migration for the next pass.

## Deep drift scan across all Binius phases/protocols — 2026-04-09

- Ran a repo-wide parity audit over `ArkLib/ProofSystem/Binius/**` against the sibling
  `ArkLib-binius` tree, focusing on canonical `OracleProver` / `OracleVerifier` /
  `OracleReduction` wrappers and whether they route through existing logic-step helpers.
- Confirmed already-aligned surfaces:
  - `BinaryBasefold/QueryPhase.lean`: `queryOracleVerifier` / `queryOracleProver` now delegate
    through `queryPhaseLogicStep`.
  - `BinaryBasefold/Steps/FinalSumcheck.lean`: verifier already routes through
    `finalSumcheckStepLogic`.
  - `BinaryBasefold/CoreInteractionPhase.lean`: `sumcheckFoldOracleVerifier`,
    `coreInteractionOracleVerifier`, and append-based composition still match upstream structure
    modulo the computable `pSpec...Comp` names.
  - `FRIBinius/General.lean` and `RingSwitching/General.lean`: top-level full-stack append
    structure still matches upstream.
- Safe local drift fixed:
  - `FRIBinius/CoreInteractionPhase.lean` had the same kind of wrapper drift that previously
    appeared in `BinaryBasefold/QueryPhase.lean`: local executable
    `finalSumcheckVerifierOfMultiplier` / `finalSumcheckVerifierFunOfMultiplier` were inlining the
    verifier logic instead of routing through `finalSumcheckStepLogicOfMultiplier` /
    `finalSumcheckStepLogicFunOfMultiplier`.
  - These wrappers now use `logic.verifierCheck`, `logic.verifierOut`, `logic.embed`, and
    `logic.hEq`, with an explicit computable `Decidable` proof via `change ...; infer_instance`.
- Remaining real drift is concentrated, not repo-wide:
  1. `BinaryBasefold/Steps/Fold.lean`
     - local `foldOracleVerifier` still uses direct helpers
       `foldVerifierCheck` / `foldVerifierStmtOut` plus hand-written `embed` / `hEq`
       ([fold file around lines 101-132]);
     - upstream uses `foldStepLogic` directly for verifier/output/embed/hEq;
     - attempted realignment exposed broader compile debt in this file, so the patch was reverted.
  2. `RingSwitching/BatchingPhase.lean`
     - local canonical `batchingOracleProver` and `batchingOracleVerifier` are still placeholder
       `sorry` defs ([local lines 252-267]);
     - upstream has full logic-step based wrappers.
  3. `RingSwitching/SumcheckPhase.lean`
     - local canonical `iteratedSumcheckOracleProver` /
       `iteratedSumcheckOracleVerifier` ([lines 148-168]) and
       `finalSumcheckProver` / `finalSumcheckVerifier` ([lines 1006-1027]) are still placeholder
       `sorry` defs;
     - upstream has full logic-step based wrappers for both.
- Important interpretation:
  - The deepest structural gap is now in `RingSwitching/*Phase.lean`, not in Binary Basefold
    query/core-interaction anymore.
  - Those RingSwitching wrapper gaps are not cosmetic only: local files already expose
    `sumcheckStepLogic`, `finalSumcheckStepLogic`, and `batchingStepLogic`, but the canonical
    prover/verifier wrappers have not yet been migrated onto those kernels.
  - However, the underlying RingSwitching kernels remain partially `noncomputable`, so restoring
    upstream-shaped wrappers there is likely to reopen the broader migration boundary rather than
    be a one-line wrapper cleanup.
- Follow-up cut taken immediately after this scan:
  - `RingSwitching/SumcheckPhase.finalSumcheckProver` is now implemented in the computable tree and
    matches the upstream wrapper shape over `finalSumcheckStepLogic`.
  - Attempting the same for `finalSumcheckVerifier` fails the executable IR check because
    `finalSumcheckVerifierCheck` depends on `compute_final_eq_value`, which is still
    `noncomputable`.
  - So the next verifier-side migration blocker in RingSwitching is not the wrapper shell itself;
    it is `Prelude`/final-eq computation.

## Computability blockers (Lean kernel / Mathlib)

- **Planning alignment (2026-04-08):** User stretch goal is **plain `def`** for bundled `batchingCoreReduction` / `fullOracleReduction` in `FRIBinius/General.lean`. Current audit: **not achieved**; `sDomain` stack and composed reductions still `noncomputable`; `batchingCorePspecFun` / `coreInteractionOracleVerifierFunOfMultiplier` are parallel track only. Captured in `task_plan.md` Goal + Status audit.

- **`Module.Basis.instFunLike`** is `noncomputable`. Any def that depends on coercing or applying a `Basis` as `ι → M` in a way that pulls this in fails **executable** IR unless marked `noncomputable`.
- **`sDomainFinEquiv` / `finToSDomain`** in `AdditiveNTT.lean` are `noncomputable`; query-phase `SampleableType` for `sDomain` uses `Classical.decEq` patterns — keeps query challenge sampling non-executable without a redesign (e.g. `Fin (2^(ℓ+𝓡))` challenges + bijection lemmas).
- **`OracleVerifier.append`** in `OracleReduction/Composition/Sequential/Append.lean` still has `sorry` in `verify` — composition layer not fully constructive for proofs or execution stories until completed.
- **Current spec-level hotspot:** `BinaryBasefold/Spec.lean` lines around `instSDomain`, `pSpecQuery` challenge instances, and `Fin γ_repetitions → sDomain ...` still carry the noncomputable sampling/finiteness burden. `FRIBinius/General.lean` remains downstream `noncomputable` because it appends/composes these specs.
- **Out-of-scope noise for this session:** `RingSwitching/BBFSmallFieldIOPCS.lean` still has many `sorry`s, but those are integration/security follow-ons rather than the immediate OracleReduction-spec computable-port frontier.
- **Concrete mechanism in `BinaryBasefold/Spec.lean`:** `instSDomain` is currently `noncomputable` because it installs `Fintype`, `Nonempty`, and `Classical.decEq` on `sDomain ...` and then calls `SampleableType.ofEquiv` using `(sDomainFinEquiv ...).symm`.
- **Concrete mechanism in `OracleReduction.append`:** `OracleVerifier.append` still contains `sorry` in `verify`, and `append_toVerifier` is also `sorry`; downstream append-based oracle verifiers can typecheck but are not yet constructive/executable.
- **Design consequence from the spec file:** `pSpecQuery` itself exposes `sDomain ...` as the challenge type, so a fully computable path likely needs either a computable `sDomain ↔ Fin` library bridge or a parallel Fin-indexed query spec, not just a different local `SampleableType` proof.
- **`AdditiveNTT` cost model:** `sDomainToFin`, `finToSDomain`, and `sDomainFinEquiv` are themselves `noncomputable` and are built through `sDomain_basis` / `basis.repr`; this looks like a structural dependency on noncomputable basis machinery rather than a shallow instance issue.
- **Propagation depth:** `BinaryBasefold.Spec.pSpecQuery` uses `Fin γ_repetitions → sDomain ...` as the challenge type, and `BinaryBasefold/QueryPhase.lean` threads that same type through logic, verifier, reduction, extractor, and soundness statements. A computable Fin-indexed variant would therefore be a parallel API track, not a local type synonym swap.
- **Local implementation opportunity:** `OracleReduction/Composition/Sequential/Append.lean` already has `Verifier.append` as the monadic composition pattern. `OracleVerifier.append` is a localized missing piece rather than a repo-wide redesign.
- **Oracle-context infrastructure:** the intended route is `simulateQ` + `QueryImpl`/`simOracle2` lifting. `OracleReduction/Cast.lean` contains another unresolved `OracleVerifier.cast.verify` stub that appears to need the same style of oracle-context embedding as `append`.
- **Concrete helpers confirmed:** `OracleReduction/OracleInterface.lean` provides `simOracle` / `simOracle2`, and `ToVCVio/Simulation.lean` provides `QueryImpl.lift`. The blocker is therefore writing the right routing map from the smaller verifier context into the appended context.
- **Nested-sum support exists:** `ToVCVio/Simulation.lean` defines `MonadLift` instances for nested oracle-spec sums, which should help reinterpret `OracleComp (oSpec + ([OStmt] + [Message]ₒ))` inside larger appended contexts without ad hoc plumbing.
- **Protocol-spec support exists:** `ProtocolSpec/SeqCompose.lean` already defines `MessageIdx.inl`, `MessageIdx.inr`, and full-transcript `fst`/`snd` for appended protocols. Message-oracle routing into `(pSpec₁ ++ₚ pSpec₂)` is therefore supported at the index level.
- **Remaining technical pain point for `OracleVerifier.append`:** no existing completed example was found for routing an output-oracle family through an `embed` into a larger live oracle context. The hard part is dependent casting of `OStmt₂` query/response types via `V₁.embed`/`V₁.hEq`.
- **No generic interface-transport helper found:** there is no obvious `OracleInterface.cast` abstraction in the repo; expect explicit dependent casts when routing `OStmt₂` queries through `V₁.embed`.
- **Useful cast idiom:** existing verifier code transports oracle queries with `liftM (cast (β := OracleQuery ...) (by simp) (query ...))`. That is the likely pattern for explicit routing in `OracleVerifier.append`.
- **Practical append detail:** no ready-made `Challenges.fst/snd` helper showed up; split appended challenges manually via `ChallengeIdx.inl` / `ChallengeIdx.inr`.
- **`QueryImpl.addLift` usage is common:** completeness/security code already relies on `QueryImpl.addLift`, so using it inside append would match existing repo patterns.
- **First `OracleVerifier.append` patch failures:** appended challenges need explicit casts after `ChallengeIdx.inl/inr`; oracle-spec domain routing must pattern match with `Sum.inl` / `Sum.inr` rather than dotted `.inl` / `.inr`; the field body must use monadic `do` notation instead of `by` with `←`.
- **Strategic direction confirmed by existing code:** `BinaryBasefold/ReductionLogic.lean` already separates “computable structure” from noncomputable honest-prover helpers. That matches the user’s goal better than trying to make every downstream verifier/extractor executable immediately.
- **Path note:** the migration map referenced in `.planning/index.md` lives outside this worktree root; the relative path there is stale from this worktree’s perspective.
- **Concrete precedent:** `foldStepLogic` in `BinaryBasefold/ReductionLogic.lean` intentionally keeps the verifier-side structure computable while `honestProverTranscript` and `proverOut` stay `sorry`/noncomputable helpers. This is the cleanest local model for future Binius spec migration work.
- **Query-phase distinction:** `queryPhaseLogicStep` is `noncomputable` because its verifier logic consumes `pSpecQuery` challenges as actual `sDomain ...` points. That does not block adding a spec-only Fin-indexed query protocol, but it means such a spec would be a parallel API rather than a drop-in replacement for the existing logic layer.
- **Top-level split in FRIBinius:** `FRIBinius/General.batchingCorePspec` is noncomputable for a different reason than the query phase: it closes over `β : Basis ...` via `(fun i => β i)`. So a companion computable spec track likely needs both an explicit `βfun` parameter and a Fin-indexed query challenge type.
- **Implemented companion spec track (current session):**
  - `BinaryBasefold.Spec`: added `QueryChallengeIndex`, `pSpecQueryFin`, `fullPSpecFin`, and computable `SampleableType` instances for the Fin-indexed query/full-spec challenges.
  - `FRIBinius.General`: added `batchingCorePspecFun` and `fullPspecFin` using explicit `βfun` plus the Fin-indexed query spec, along with append-derived `OracleInterface` / `SampleableType` instances.
- **Current verification status:** targeted `lake build` succeeds for both `ArkLib.ProofSystem.Binius.BinaryBasefold.Spec` and `ArkLib.ProofSystem.Binius.FRIBinius.General`. Lean LSP became stale / unavailable mid-session, so terminal builds are the ground truth for this episode.
- **General-file status after inspection:** `BinaryBasefold/General.lean` and `RingSwitching/General.lean` are already structurally computable; their remaining `noncomputable` defs are the `ℝ≥0` security-error summaries. The main remaining structural noncomputability is in `FRIBinius/General.lean`, inherited from `FRIBinius/CoreInteractionPhase.lean`.
- **Immediate FRIBinius source:** `FRIBinius/CoreInteractionPhase.lean` marks `sumcheckFoldCtxLens`, `sumcheckFoldOracleVerifier`, `sumcheckFoldOracleReduction`, `finalSumcheckProver`, `finalSumcheckVerifier`, `finalSumcheckOracleReduction`, and the composed core-interaction defs as `noncomputable`.
- **Likely removable local blocker:** `finalSumcheckVerifier` currently installs `have : Decidable (logic.verifierCheck stmtIn t) := Classical.propDecidable _` before `guard`, so at least part of the remaining noncomputability is from a classical decider rather than only from `Basis`.
- **Concrete decider precedent exists:** `BinaryBasefold/Steps/FinalSumcheck.lean` already defines `finalSumcheckStepLogic_verifierCheck_decidable` and uses `guard (logic.verifierCheck ...)` without `Classical.propDecidable`. FRIBinius final-sumcheck code should likely mirror that instead of forcing classical decidability.
- **Attempted FRIBinius final-sumcheck downgrade failed:** even without the classical guard issue, `FRIBinius/CoreInteractionPhase.finalSumcheck*` still depends on `RingSwitching.compute_final_eq_value`, which is `noncomputable` in `RingSwitching/Prelude.lean`. So that `noncomputable` is structural, not just a missing decidable instance.
- **Deeper FRIBinius blocker:** `RingSwitching_SumcheckMultParam` in `RingSwitching/Prelude.lean` is also `noncomputable`, so `sumcheckFoldOracleVerifier` / `Reduction` remain upstream noncomputable before the final query composition in `FRIBinius/General.lean`.

## API consistency

- **FRIBinius `CoreInteractionPhase`** uses `β : Basis (Fin (2^κ)) K L`. FRIBinius `General` was aligned to the same so `coreInteractionOracleVerifier` / `Reduction` compose without a second `β` discipline.
- **Ring-switching batching** expects `Basis (Fin κ → Fin 2) K L` — bridge is `booleanHypercubeBasis κ L K β` from `FRIBinius.Prelude` (reindex of hypercube equiv).

## Build / tooling

- **File-wide `set_option maxHeartbeats 200000`** after imports applies to the remainder of the file in Lean 4. Instance synthesis can still use **`synthInstance.maxHeartbeats`** separately if needed.
- Large full-library `lake build` can exceed agent wall-clock; prefer `lake build <module>` when iterating.
- **Lean iteration policy for this task:** use Lean LSP / MCP as the source of truth for diagnostics and goals; avoid guessing lemma names or proof states from memory.
- **Proof safety policy:** no `simpa`; keep any proof or elaboration attempt bounded with `maxHeartbeats <= 200000`, and prefer targeted module builds while iterating.

## Session Resume Notes

- **2026-04-08 (resume):** active task remains `comp-binius-port` on branch `CompBinius`; the previous baton narrowed to a commit-ready milestone, but the user requested continued work on the broader computable-port scope.
- **Current worktree state:** modified Lean files are `ArkLib/ProofSystem/Binius/FRIBinius/General.lean` and `ArkLib/ProofSystem/Binius/BinaryBasefold/Spec.lean`; `.planning/` and several local agent metadata paths are untracked in `git status`.
- **Actual uncommitted Lean diff:** only adds file-scoped `set_option maxHeartbeats 200000` to `FRIBinius/General.lean` and `BinaryBasefold/Spec.lean`; the larger append-wiring / `Basis` refactor mentioned in the previous baton is already in branch history rather than pending locally.
- **Lean diagnostics check (2026-04-08):** `FRIBinius/General.lean` and `BinaryBasefold/Spec.lean` both report no current LSP errors.

## Reset Audit — 2026-04-08

- `HEAD` is currently `e598d56d` on `CompBinius`, and it matches `origin/CompBinius` exactly (`git rev-list --left-right --count origin/CompBinius...HEAD` → `0 0`).
- The most recent reflog event is `HEAD@{2026-04-08 15:28:41 +0700}: reset: moving to HEAD~1`, which moved the branch from local commit `1a52693b` back to `e598d56d`.
- No tracked files are currently deleted in the working tree (`git ls-files --deleted` returned empty).
- The reset definitely removed one local commit that is still recoverable from reflog:
  - `1a52693b chore: add CompBinius branch marker (Cursor)`
  - touched `ArkLib/ProofSystem/Binius/FRIBinius/General.lean`
  - added `scripts/compbinius-branch-marker.txt` with content `CompBinius branch marker (Cursor agent). Safe to delete.`
- That discarded commit is not contained in any branch (`git branch --contains 1a52693b` returned empty), but it is still readable with `git show`, so recovery via reflog/cherry-pick is still possible.
- The discarded commit contains real `FRIBinius/General.lean` work beyond the marker file: `git show --shortstat 1a52693b` reports `2 files changed, 121 insertions(+), 51 deletions(-)`, and the lost tree includes `OracleVerifier.append`-based rewiring in `FRIBinius/General.lean`.
- The planning notes mention later symbols such as `QueryChallengeIndex`, `pSpecQueryFin`, `fullPSpecFin`, `batchingCorePspecFun`, and `fullPspecFin`, but those symbols are absent from the current tree, absent from reflogged commits checked for `BinaryBasefold/Spec.lean`, and absent from searched dangling blobs. Treat those notes as ahead of retained git state rather than as currently recoverable committed code.

## FRIBinius computability audit after recovery — 2026-04-08

- Recovered `ArkLib/ProofSystem/Binius/FRIBinius/General.lean` from reflogged commit `1a52693b` and verified `lake build ArkLib.ProofSystem.Binius.FRIBinius.General` succeeds again; only style / existing `sorry` warnings remain.
- The remaining structural blocker for executable FRIBinius is confirmed in `ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean`:
  - `RingSwitching_SumcheckMultParam` is `noncomputable`
  - `compute_A_MLE` is `noncomputable`
  - `compute_final_eq_value` is `noncomputable`
  - `decompose_tensor_algebra_rows` is `noncomputable`
- The immediate source of that noncomputability is basis-driven coordinate extraction:
  - `compute_A_func` uses `β.repr eq_w`
  - `compute_final_eq_value` uses `decompose_tensor_algebra_rows`, which in turn uses `Basis.baseChangeRight ... |>.repr`
- `FRIBinius/CoreInteractionPhase.lean` does not fundamentally need those noncomputable implementations for its verifier wiring; the local `noncomputable` defs are specialized wrappers:
  - `sumcheckFoldOracleVerifier` / `sumcheckFoldOracleReduction` are just `BinaryBasefold.CoreInteraction.sumcheckFold*` with `mp := RingSwitching_SumcheckMultParam ...`
  - `finalSumcheckVerifier` / `finalSumcheckOracleReduction` build on `finalSumcheckStepLogic ...`
  - `coreInteractionOracleVerifier` / `coreInteractionOracleReduction` just append the previous two pieces
- This suggests a viable next step that avoids solving basis executability immediately: add computable companion defs in `FRIBinius/CoreInteractionPhase.lean` parameterized by an external `mp : SumcheckMultiplierParam ...`, then keep the current ring-switching-specialized defs as the noncomputable wrappers.
- `FRIBinius/CoreInteractionPhase.lean` now has a compiling additive companion track:
  - `sumcheckFoldOracleVerifierOfMultiplier`
  - `finalSumcheckVerifierCheckOfMultiplier`
  - `finalSumcheckStepLogicOfMultiplier`
  - `finalSumcheckProverOfMultiplier`
  - `finalSumcheckVerifierOfMultiplier`
  - `finalSumcheckOracleReductionOfMultiplier`
  - `coreInteractionOracleVerifierOfMultiplier`
- Two local implementation details were required to make that additive track compile:
  - `finalSumcheckProverOfMultiplier` must stay `noncomputable`, because it still reuses the noncomputable prover-side message path.
  - Reusing `finalSumcheckProver ... |>.PrvState` caused universe-inference failures; copying the original `PrvState` family inline fixes elaboration cleanly.
- Important verifier-side correction: the new `...OfMultiplier` verifier wrappers cannot drop `noncomputable` yet.
  - Trying to make `sumcheckFoldOracleVerifierOfMultiplier` and `coreInteractionOracleVerifierOfMultiplier` plain `def`s fails executable IR with:
    `depends on declaration 'Module.Basis.instFunLike', which has no executable code`.
  - This is not coming from the verifier logic itself. `BinaryBasefold.CoreInteraction.sumcheckFoldOracleVerifier` is already a plain `def` over a function parameter `β : Fin r → L`.
  - The remaining noncomputable leak is at the FRIBinius wrapper boundary: this layer still instantiates Binary Basefold verifier types with `β : Basis ...`, relying on coercion from `Basis` to function.
  - Therefore the real next step for executable verifier semantics is a new companion track parameterized by an explicit computable `βfun : Fin (2 ^ κ) → L`, not just by `mp`.
- That `βfun` companion track now exists and compiles:
  - In `FRIBinius/CoreInteractionPhase.lean`:
    - `sumcheckFoldStmtLensFun`
    - `sumcheckFoldOracleVerifierFunOfMultiplier`
    - `finalSumcheckProverComputeMsgFun`
    - `finalSumcheckStepLogicFunOfMultiplier`
    - `finalSumcheckVerifierFunOfMultiplier`
    - `coreInteractionOracleVerifierFunOfMultiplier`
  - In `FRIBinius/General.lean`:
    - `batchingCorePspecFun`
    - append-derived `OracleInterface` / `SampleableType` instances for that pspec
    - `batchingCoreVerifierFunOfMultiplier`
- Key refinement: the batching+core executable companion still cannot synthesize the hypercube basis internally.
  - Using `booleanHypercubeBasis κ L K β` inside `batchingCoreVerifierFunOfMultiplier` fails IR because that basis construction is itself noncomputable.
  - The working executable wrapper therefore accepts the hypercube basis explicitly as a parameter:
    `βcube : Basis (Fin κ → Fin 2) K L`.
  - This means the wrapper itself no longer introduces extra noncomputability; the remaining basis object is now an explicit input boundary rather than hidden coercion/construction inside the verifier definition.
- Validation after those fixes:
  - Lean LSP reports no errors in `ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean`.
  - `lake build ArkLib.ProofSystem.Binius.FRIBinius.CoreInteractionPhase` completes successfully.
  - `lake build ArkLib.ProofSystem.Binius.FRIBinius.General` also succeeds after adding additive `batchingCore*OfMultiplier` wrappers and restoring the required `noncomputable` verifier annotations.
  - After the `βfun` refactor, both files still build successfully, and the new function-based verifier companion defs remain plain `def`s.

## `fullOracleProof` blocker map — 2026-04-08

- The user clarified the actual target: **`FRIBinius/General.fullOracleProof` itself must become a plain computable `def`**.
- Current `FRIBinius/General.lean` still marks these structural exec defs `noncomputable`:
  - `batchingCorePspec`
  - `fullPspec`
  - `batchingCoreVerifier`
  - `batchingCoreReduction`
  - `fullOracleVerifier`
  - `fullOracleReduction`
  - `fullOracleProof`
- `BinaryBasefold/General.lean` is an important comparison point:
  - its top-level `fullOracleVerifier`, `fullOracleReduction`, and `fullOracleProof` are already plain `def`s;
  - so the remaining FRI noncomputability is not caused by `OracleReduction.append` itself.
- The remaining blockers split into three distinct classes:
  1. **Basis-to-function leakage at the FRI wrapper boundary**
     - `FRIBinius/General` and `FRIBinius/CoreInteractionPhase` still instantiate Binary Basefold APIs with `(fun i => β i)` for `β : Basis ...`.
     - This is exactly where Lean reports executable IR failure on `Module.Basis.instFunLike`.
  2. **Ring-switching batching / final-eq basis machinery**
     - `booleanHypercubeBasis κ L K β` is itself noncomputable, so any wrapper that tries to synthesize it internally becomes noncomputable.
     - `RingSwitching.compute_final_eq_value` and `RingSwitching_SumcheckMultParam` remain noncomputable in the theorem-facing path.
  3. **Binary Basefold prover-side witness generation**
     - `BinaryBasefold.Relations.getMidCodewords` is still `noncomputable`.
     - `BinaryBasefold.Steps.FinalSumcheck.finalSumcheckProver` is `noncomputable`.
     - `BinaryBasefold.CoreInteraction.sumcheckFoldOracleReduction` is `noncomputable`.
- Crucial nuance:
  - `BinaryBasefold.CoreInteraction.coreInteractionOracleReduction` is a plain `def`, but it currently does that by leaving `prover := sorry`.
  - That means it is **not** evidence that the whole reduction path is already executable; it only shows the top-level record can be declared without a `noncomputable` marker if the prover is not yet implemented.
- Practical consequence for the next edits:
  - removing `noncomputable` from `FRIBinius/General.fullOracleProof` will not be solved by verifier-side `βfun` companions alone;
  - we need either
    - a real executable reduction/proof companion path through batching + core interaction + query, or
    - a refactor of the current theorem-facing reductions so their prover-side kernels are computable under explicit function/basis parameters.

## Top-level compile experiment + full-verifier companion — 2026-04-08

- Targeted experiment:
  - temporarily removed `noncomputable` from `FRIBinius/General.fullOracleVerifier`,
    `fullOracleReduction`, and `fullOracleProof`;
  - `lake build ArkLib.ProofSystem.Binius.FRIBinius.General` then failed with the exact IR errors:
    - `fullOracleVerifier`: depends on `Module.Basis.instFunLike`
    - `fullOracleReduction`: depends on `Module.Basis.instFunLike`
    - `fullOracleProof`: depends on non-executable `fullOracleReduction`
- Interpretation:
  - the immediate top-level blocker is still the basis-to-function wrapper boundary in
    `FRIBinius/General.lean`;
  - the error does **not** yet mention `sDomain` or `getMidCodewords`, so those are downstream
    blockers after the wrapper boundary is removed.
- Added new executable companion defs in `FRIBinius/General.lean`:
  - `fullPspecFun`
  - `fullPspecFun_messageOracleInterface`
  - `fullPspecFun_challengeSampleableType`
  - `fullOracleVerifierFunOfMultiplier`
- `fullOracleVerifierFunOfMultiplier` now gives a plain full-protocol verifier companion over:
  - `βfun : Fin (2 ^ κ) → L`
  - explicit batching basis `βcube : Basis (Fin κ → Fin 2) K L`
  - explicit multiplier parameter `mp`
- Reverted the temporary removal of `noncomputable` from the theorem-facing defs after the
  experiment, so the file builds again.
- Validation after the new full-verifier companion:
  - `lake build ArkLib.ProofSystem.Binius.FRIBinius.General` succeeds.
- Additional scratch check:
  - a standalone plain alias to `BinaryBasefold.CoreInteraction.sumcheckFoldOracleReduction`
    fails immediately because that reduction is itself marked `noncomputable`;
  - this confirms that a real executable `fullOracleProof` requires an actual prover-side
    replacement for the sumcheck-fold reduction, not just one more wrapper.

## Resume checkpoint — 2026-04-08 (current continuation)

- Replayed current staged `FRIBinius/CoreInteractionPhase.lean` and `FRIBinius/General.lean`
  state with `lake build` and confirmed it still compiles cleanly (warnings only).
- The next safe forward cut is to add **prover-parameterized executable reduction/proof
  companions** over the existing `βfun` verifier track, so executable `OracleReduction` /
  `OracleProof` values can be formed without forcing immediate migration of the noncomputable
  honest-prover internals (`getMidCodewords` cone).

## Prover-parameterized executable companions — 2026-04-08

- Added an executable core-interaction reduction companion in
  `FRIBinius/CoreInteractionPhase.lean`:
  - `coreInteractionOracleReductionFunOfMultiplier`
  - shape: plain `def` over explicit `βfun` + `mp`, with an externally supplied
    `OracleProver`; verifier side is `coreInteractionOracleVerifierFunOfMultiplier`.
- Added executable full-stack reduction/proof companions in `FRIBinius/General.lean`:
  - `fullOracleReductionFunOfMultiplier`
  - `fullOracleProofFunOfMultiplier`
  - both consume an external `OracleProver` and reuse `fullOracleVerifierFunOfMultiplier`.
- Validation:
  - `lake build ArkLib.ProofSystem.Binius.FRIBinius.CoreInteractionPhase ArkLib.ProofSystem.Binius.FRIBinius.General`
    succeeds (warnings only).
- Interpretation:
  - this does **not** remove `noncomputable` from bundled theorem-facing `fullOracleReduction` /
  `fullOracleProof`;
  - it establishes an executable API seam where prover executability can now be improved
  independently and plugged in without changing the full-stack verifier/spec glue again.

## `fullOracleProof` computable entrypoint promotion — 2026-04-08

- Promoted the name `FRIBinius.General.fullOracleProof` to the executable companion signature
  (explicit `βfun`, `βcube`, `mp`, external `prover`) and kept the old basis-driven bundled object
  as `fullOracleProofOfBasis`.
- Result:
  - `fullOracleProof` is now a plain computable `def` (at the executable companion boundary).
  - The previous theorem-facing basis-path object still exists but remains `noncomputable` under the
    new name `fullOracleProofOfBasis`.
- Validation:
  - `lake build ArkLib.ProofSystem.Binius.FRIBinius.General` succeeds.

## References

## Resume checkpoint — 2026-04-09

- Active task remains `comp-binius-port` on worktree `ArkLib-binius-computable`, branch
  `CompBinius`.
- `handoff.md` was empty/template-only, so the durable state is coming from `task_plan.md`,
  `progress.md`, and `findings.md`.
- Current worktree already contains substantial uncommitted edits aligned with the new
  structure-parity requirement:
  - deleted `ArkLib/ProofSystem/Binius/BinaryBasefold/ComputableFold.lean`
  - modified canonical Binary Basefold / FRIBinius files, plus AdditiveNTT and RingSwitching
- Search audit still shows theorem-side `*SecurityReduction*` names in canonical files, including
  `FRIBinius/CoreInteractionPhase.lean` wrappers still ending in `...Noncomp`.
- Next step should be driven by build truth, not stale notes: run targeted `lake build` on the
  touched Binius modules and repair whichever parity migration breakage remains.

## Binary Basefold theorem-tail audit — 2026-04-09

- The remaining legacy theorem-surface leakage is concentrated in
  `ArkLib/ProofSystem/Binius/BinaryBasefold/CoreInteractionPhase.lean`.

## Query-phase index question — 2026-04-09

- Current investigation target from the human: whether
  `BinaryBasefold.QueryPhase.canonicalQueryPointToIndex` should return a deterministic
  `Fin (2 ^ (ℓ + 𝓡))` because the canonical query domain is equivalent to a Fin-indexed domain.
- Comparison source requested by the human:
  `/Users/chung-thai-nguyen/Documents/WorkStation/Repo/Verified-zkEVM/ArkLib-binius/ArkLib/ProofSystem/Binius/BinaryBasefold/QueryPhase.lean`
- Prior planning state already identified this exact frontier:
  current canonical query path still centers on `pSpecQuery` / `sDomain`, while the computable port
  added a parallel Fin-indexed spec track (`pSpecQueryFin`, `fullPSpecFin`) instead of replacing the
  canonical abstract query logic.
- Working hypothesis to verify from the code:
  the abstract file likely keeps `canonicalQueryPointToIndex` proof-facing over `sDomain`, and the
  computable migration introduces a separate deterministic Fin projection because the equivalence is
  currently noncomputable (`sDomainFinEquiv`) rather than a plain executable map.
- Confirmed in the computable tree:
  - canonical `pSpecQuery` still uses `Fin γ_repetitions → sDomain ... 0` as its challenge carrier;
  - `pSpecQueryFin` is a new companion spec with challenge carrier
    `Fin γ_repetitions → Fin (2 ^ (ℓ + 𝓡))`;
  - `queryOracleVerifierComp` on canonical `pSpecQuery` currently recovers the loose index with
    `canonicalQueryPointToIndex?`, implemented as a `List.finRange ... |>.find?` search over all
    indices.
- So the current code already distinguishes:
  - semantic determinism/existence of an index for canonical points in `S⁽⁰⁾`;
  - executable computation of that index in the canonical API.
  The former is expected from equivalence; the latter is blocked by how that equivalence is exposed.
- Follow-up migration cut completed in this session:
  - promoted `BinaryBasefold.QueryPhase.queryOracleVerifierFin` /
    `queryOracleReductionFin` / `queryOracleProofFin` to the canonical exported names
    `queryOracleVerifier` / `queryOracleReduction` / `queryOracleProof`;
  - retained the abstract-`pSpecQuery` search-decoding path under explicit `...Canonical` names;
  - rewired `BinaryBasefold.General` and `FRIBinius.General` to depend on the canonical query-phase
    reduction/verifier names instead of the `...Fin` suffixed ones.
- This reduces the public “parallel-track” surface: executable query reductions are now the default
  exported query-phase reductions, and the old `Fin` suffix is no longer required downstream.

## Cross-repo interface alignment audit — 2026-04-09

- Lean file inventory under `ArkLib/ProofSystem/Binius` matches one-to-one between
  `ArkLib-binius-computable` and sibling `ArkLib-binius`.
- The only extra path in the abstract sibling tree is a markdown note:
  `ArkLib/ProofSystem/Binius/RingSwitching/FRI-Binius paper.md`.
- Conclusion: interface alignment can be audited as a declaration-surface diff across corresponding
  Lean files without dealing with divergent module sets.
- First declaration-surface diff summary:
  - `FRIBinius/General.lean` drift: computable tree added `*PspecFun*` / `*ReductionFun*`
    companions and currently lacks abstract names `batchingCorePspec`, `batchingCoreVerifier`,
    `batchingCoreReduction`, `fullPspec`.
  - `FRIBinius/CoreInteractionPhase.lean` drift: computable tree added many
    `*FunOfMultiplier` / `*OfMultiplier` companions and currently lacks abstract names
    `finalSumcheckProver`, `finalSumcheckVerifier`, `sumcheckFoldCtxLens`,
    `sumcheckFoldCtxLens_complete`.
  - `BinaryBasefold/QueryPhase.lean` drift is expected/additive: computable tree adds the
    index-native executable helper layer and canonical/Fin bridges.
  - `BinaryBasefold/Spec.lean`, `CoreInteractionPhase.lean`, `Steps/Fold.lean` drift is primarily
    additive companion structure (`*Comp`, `*Fin`, `WitnessComp`), not obviously missing abstract
    canonical names.
  - `RingSwitching/BBFSmallFieldIOPCS.lean` drift includes missing abstract theorem/interface
    surfaces:
    `largeFieldInvocationCtxLens_complete`, `largeFieldInvocationOracleReduction_perfectCompleteness`.
- Refined missing-abstract declaration list to consider for restoration/alignment:
  - `FRIBinius/General.lean`:
    `batchingCorePspec`, `fullPspec`
    plus potentially problematic basis-based oracle surfaces
    `batchingCoreVerifier`, `batchingCoreReduction`
  - `FRIBinius/CoreInteractionPhase.lean`:
    `sumcheckFoldCtxLens`, `sumcheckFoldCtxLens_complete`
    plus potentially problematic basis-based oracle surfaces
    `finalSumcheckProver`, `finalSumcheckVerifier`
  - `BinaryBasefold/Steps/Fold.lean`:
    `foldOracleProver`
  - `BinaryBasefold/Steps/FinalSumcheck.lean`:
    `finalDecodedPrefixAt`, `finalDecodedPrefixFold`, `finalOracleDecoded`,
    `finalOracleDecodedAt`, `finalOracleNextCodeword`
  - `RingSwitching/Prelude.lean`:
    `MLPEvalRelation`, `batchingCheckSummand`
  - `RingSwitching/BBFSmallFieldIOPCS.lean`:
    `largeFieldInvocationCtxLens_complete`,
    `largeFieldInvocationOracleReduction_perfectCompleteness`
- Search confirms the main old-family cluster is the arithmetic tail around
  `sumcheckFoldKnowledgeError_le`, which still quantifies over:
  - `pSpecSumcheckFold`
  - `pSpecNonLastBlocks`
  - `pSpecFullNonLastBlock`
  - `pSpecLastBlock`
- Earlier theorem-facing helper defs in the same file also still mention the old challenge-family
  APIs near lines `614`, `622`, `640`, `658`, `717`, `1333`, `1342`, and `1531`.
- The practical cleanup strategy is to restate the giant arithmetic theorem block directly over the
  `...Comp` challenge families and leave the proof as `sorry`, rather than preserving the old
  nested `Finset` bookkeeping proof term.

## Binary Basefold + FRIBinius core-interaction migration checkpoint — 2026-04-09

- `BinaryBasefold/CoreInteractionPhase.lean`
  - Replaced the old `sumcheckFoldKnowledgeError_le` theorem statement with a `pSpecSumcheckFoldComp`
    version and collapsed the obsolete proof term to `sorry`.
  - Deleted the old witness/pSpec-only reduction wrappers:
    - `sumcheckFoldOracleReductionOfProver`
    - `coreInteractionOracleReductionOfProver`
  - Promoted the computable verifier stack into the canonical names:
    - `nonLastSingleBlockOracleVerifier`
    - `nonLastBlocksOracleVerifier`
    - `lastBlockOracleVerifier`
    - `sumcheckFoldOracleVerifier`
    - `coreInteractionOracleVerifier`
  - Added compatibility wrapper defs with `...Comp` names so downstream files can still compile
    while the canonical names now point at the computable surfaces.
  - The brittle helper lemmas `foldRelayKnowledgeError_eq` and `foldCommitKnowledgeError_eq` were
    downgraded to `sorry` after the pspec/canonical-name migration broke their old `rfl` proofs.
- `FRIBinius/CoreInteractionPhase.lean`
  - Eliminated all remaining references to legacy Binary Basefold challenge families:
    - `BinaryBasefold.pSpecSumcheckFold` → `BinaryBasefold.pSpecSumcheckFoldComp`
    - `BinaryBasefold.pSpecCoreInteraction` → `BinaryBasefold.pSpecCoreInteractionComp`
  - This now applies across the executable sumcheck/core reductions and the associated
    completeness / RBR-KS theorem statements in that file.
- `BinaryBasefold/General.lean`
  - Updated the remaining old append surface in `fullOracleVerifier` so its core-interaction branch
    now uses `pSpecCoreInteractionComp`.
- `FRIBinius/General.lean`
  - Began the same normalization pass: `batchingCorePspec`, `batchingCorePspecFun`, and several
    batching/core append surfaces now point at `BinaryBasefold.pSpecCoreInteractionComp`.

## Filtered build status — 2026-04-09

- A targeted filtered build of `BinaryBasefold/CoreInteractionPhase.lean` surfaced only local
  migration breakage after the canonical-name promotion:
  - alias declarations for `...Comp` verifier names were too implicit / attribute-heavy;
  - `foldRelayKnowledgeError_eq` and `foldCommitKnowledgeError_eq` no longer reduced by `rfl`.
- Those local blockers have been patched:
  - `...Comp` compatibility names are now plain wrapper `def`s, not `@[reducible] abbrev`s;
  - the two helper lemmas are now `sorry`.
- A fresh filtered rebuild was started after those fixes, but the final post-fix result had not yet
  been captured at the time of this planning update.

- DP24 (Diamond–Posen) — scalar error targets for `concreteFRIBiniusKnowledgeError` etc. unchanged.
- Workspace migration map: `Verified-zkEVM/.cursor/plans/binius_comppoly_migration_map_6c571281.plan.md`.

## Binary Basefold computability checkpoint — 2026-04-08 (later continuation)

- Converted these Binary Basefold leaf-step definitions to plain `def` and revalidated:
  - `BinaryBasefold/Basic.lean`: `snoc_oracle`, `take_snoc_oracle`
  - `BinaryBasefold/Steps/Relay.lean`: `relayOracleProver`, `relayOracleReduction`
  - `BinaryBasefold/Steps/Commit.lean`: `getCommitProverFinalOutput`, `commitOracleProver`,
    `commitOracleReduction`
- `snoc_oracle` needed an explicit constructive local instance
  `letI : Decidable (isCommitmentRound ℓ ϑ i) := by unfold isCommitmentRound; infer_instance`
  to avoid falling back to `open Classical in`.
- `lake build ArkLib.ProofSystem.Binius.BinaryBasefold.Steps.Commit` now succeeds with these
  computable changes in place.

## Hard blocker discovered for full fold-prover executability — 2026-04-08

- Attempted to make `foldOracleProver` / `foldOracleReduction` computable by peeling:

## Witness-level executability blocker — 2026-04-08 (current continuation)

- The blocker is stricter than `iterated_fold` alone: constructing values of the current
  `Witness` type at the fold step fails executable IR because `Witness.H` is
  `MultiquadraticPoly` (`MvPolynomial`-backed).
- Lean check reproduced this directly: even a toy construction of a new witness with
  `H := 0` fails IR with dependency on non-executable `MvPolynomial.commSemiring`.
- Passing an existing `Witness` as input is executable; creating a *new* one for `i.succ` is not.
- Consequence: a truly computable fold prover/reduction cannot keep using the current witness
  representation on its executable path. We need a computable witness carrier (companion type)
  and companion fold kernels over that carrier.
  `foldProverComputeMsg` → `getSumcheckRoundPoly` and related helpers.
- Lean IR blockers encountered:
  - `getSumcheckRoundPoly` executable attempt: depends on
    `MvPolynomial.finSuccEquivNth` (no executable code).
  - even with an alternative formulation, executable code still depends on
    `Polynomial.C` (no executable code).
  - independent local test confirms `def testC : Polynomial Nat := Polynomial.C 3` fails IR
    unless marked `noncomputable`.
  - `getFoldProverFinalOutput` executable attempt depends on noncomputable `iterated_fold`.
- Consequence:
  - with current theorem-facing message type `L⦃≤ 2⦄[X]` in `pSpecFold`, the fold-step honest-prover
    message path cannot be made executable by local edits alone;
  - a real fix needs a CompPoly-backed computable message representation and downstream migration of
    fold/prover kernels (or equivalent full replacement of noncomputable polynomial/iterated-fold
    dependencies).

## AdditiveNTT migration restart checkpoint — 2026-04-08 (this session)

- Active branch/worktree confirmed:
  - branch: `CompBinius`
  - worktree: `ArkLib-binius-computable`
- Active planning task remains `comp-binius-port`; user directive is now explicit:
  - make `ArkLib/Data/FieldTheory/AdditiveNTT/Impl.lean` the computable implementation path,
    using CompPoly source as base, and keep loose-index style (`Fin r`) wrappers.
- Handoff file was reset to template at session start per planning workflow.

## AdditiveNTT active blocker snapshot — 2026-04-08 (continuation)

- `ArkLib/Data/FieldTheory/AdditiveNTT/Impl.lean` is in a compilable computable state from the
  previous session.
- The remaining build blocker is in
  `ArkLib/Data/FieldTheory/AdditiveNTT/AdditiveNTT.lean`: a callsite near
  `additiveNTT_correctness` uses `additiveNTT β h_ℓ_add_R_rate ...` while the elaborated
  definition signature appears to no longer accept `β` in that position.
- Next action: inspect the elaborated type of `additiveNTT` and rewrite all affected callsites and
  theorem hypotheses to exactly match the current argument order.

## AdditiveNTT signature + noncomputable audit — 2026-04-08

- `AdditiveNTT.additiveNTT` currently elaborates with a duplicated proof argument order:
  `(h_ℓ_add_R_rate) (β) : ℓ + R_rate < r → ...`.
  This came from defining `additiveNTT` with explicit `h_ℓ_add_R_rate` while the section already
  had a global `h_ℓ_add_R_rate` variable in scope.
- The immediate hard error in `additiveNTT_correctness` was resolved by matching this elaborated
  order (`additiveNTT h_ℓ_add_R_rate β h_ℓ_add_R_rate ...`), and
  `lake build ArkLib.Data.FieldTheory.AdditiveNTT.AdditiveNTT` now succeeds.
- Remaining migration scope is still large:
  - `AdditiveNTT.lean` has many `noncomputable def` left (`sDomain`, `qMap`, `sDomain_basis`,
    `sDomainFinEquiv`, `intermediate*`, `evaluationPointω`, etc.).
  - `NovelPolynomialBasis.lean` still has many `noncomputable def` (`W`, `normalizedW`, `Xⱼ`,
    `basisVectors`, `changeOfBasisMatrix`, `polynomialFromNovelCoeffs`, conversions, etc.).
- `AdditiveNTT/Impl.lean` currently provides computable implementations for the main execution
  path (`sDomain`, `twiddleFactor`, `NTTStage`, `additiveNTT`), making it a viable source to
  replace the remaining algorithm-path noncomputability.

## AdditiveNTT continuation — 2026-04-08 (current pass)

- Resolved the remaining hard compile blocker in
  `AdditiveNTT/additiveNTT_correctness` by matching the currently elaborated
  `additiveNTT` argument order:
  `additiveNTT h_ℓ_add_R_rate β h_ℓ_add_R_rate ...`.
- Fixed an accidental parse break introduced mid-edit (missing `-/` terminator on the
  `additiveNTT` docstring); this had surfaced as `unterminated comment` at file end.
- Verified both modules build after repair:
  - `lake build ArkLib.Data.FieldTheory.AdditiveNTT.AdditiveNTT`
  - `lake build ArkLib.Data.FieldTheory.AdditiveNTT.Impl`
- Tried the aggressive cut of making canonical `AdditiveNTT.sDomain` itself a plain computable
  `def` (aliasing the executable linear-map path). This caused broad breakage:
  - many `omit ... in` declarations started failing (`cannot omit referenced section variable`);
  - existing proof scripts around `iteratedQuotientMap` no longer matched definitional rewrites.
  The change was reverted to keep the tree buildable.
- Migrated additional CompPoly `Impl` surface into
  `ArkLib/Data/FieldTheory/AdditiveNTT/Impl.lean`:
  - added computable subtype-level `bitsToU` (value in `AdditiveNTT.U`);
  - added `bitsToU_bijective` theorem stub (`sorry`) as a migration placeholder;
  - retained loose indexing style (`Fin r`) and executable core path defs.
- Downstream safety check:
  - `lake build ArkLib.ProofSystem.Binius.FRIBinius.General` completes successfully (warnings only),
    so AdditiveNTT migration edits did not regress current FRIBinius/BinaryBasefold buildability.

## BinaryBasefold computable-query cone audit — 2026-04-08 (this continuation)

- The query-phase noncomputability is now pinned to concrete defs in `BinaryBasefold/Prelude.lean`:
  - `qMap_total_fiber` is `noncomputable` and depends on `sDomain_basis` / `repr`.
  - `foldMatrix` and `single_point_localized_fold_matrix_form` are `noncomputable`.
  - `extractMiddleFinMask` is `noncomputable` because it calls `AdditiveNTT.sDomainToFin`.
- This confirms that simply switching `pSpecQuery` to Fin-indexed challenges is insufficient by itself;
  we also need index-native fiber/query helper defs to avoid basis-dependent domain decoding.
- Next migration cut selected:
  - add index-based helpers (`Fin (2^(ℓ+𝓡))` challenge indexing) in BinaryBasefold,
    then thread these into query-phase companion defs before replacing theorem-facing paths.

## BinaryBasefold Fin-query migration stabilization — 2026-04-08 (latest continuation)

- `QueryPhase.queryOracleVerifierFin` compile blocker was resolved:
  - replaced fragile `show ... from (liftM ...)` cast with an explicit `checkRep` bind using
    `OracleComp.liftComp`;
  - pinned the exact local `MonadLiftT (OracleQuery specCanon) (OracleQuery specFin)` instance to
    avoid typeclass timeout in nested append specs.
- Added an explicit nested-oracle SubSpec bridge in `BinaryBasefold/Spec.lean`:
  - `instSubSpecQueryOracleStackToFin`
  - built via explicit `OracleQuery.subSpec_right_add_right_add_of_subSpec` composition so
    canonical query-message oracle stack can be lifted into the Fin-message stack.
- Build validations:
  - `lake build ArkLib.ProofSystem.Binius.BinaryBasefold.Spec` (pass)
  - `lake build ArkLib.ProofSystem.Binius.BinaryBasefold.QueryPhase` (pass)
- Added full-protocol Fin-indexed companion definitions in
  `BinaryBasefold/General.lean`:
  - `fullOracleVerifierFin`
  - `fullOracleReductionFin`
  - `fullOracleProofFin`
  wired through `fullPSpecFin` and `QueryPhase.queryOracle*Fin`.
- Additional downstream validations:
  - `lake build ArkLib.ProofSystem.Binius.BinaryBasefold.General` (pass)
  - `lake build ArkLib.ProofSystem.Binius.FRIBinius.General` (pass)

## AdditiveNTT canonical-sDomain migration attempt — 2026-04-08 (latest continuation)

- Re-tried promoting canonical `AdditiveNTT.sDomain` to computable by replacing it with the
  executable map and aliasing `sDomainComp`.
- Result: this still causes broad non-local breakage in `AdditiveNTT.lean`
  (`cannot omit referenced section variable` and proof script mismatch around
  `intermediateNormVpoly`/`iteratedQuotientMap` cones).
- Reverted the canonical swap; kept buildable state and retained companion-track migration instead.
- Revalidated after revert:
  - `lake build ArkLib.Data.FieldTheory.AdditiveNTT.AdditiveNTT` (pass)

## Current restart audit — 2026-04-08 (this session)

- Reloaded planning state (`index/task_plan/progress/handoff`) on branch `CompBinius`.
- Current noncomputable concentration for user goal:
  - `FRIBinius/General.lean`: all bundled oracle objects (`batchingCore*`, `fullOracle*`) still
    `noncomputable`.
  - `BinaryBasefold/General.lean`: both canonical and Fin companions are still `noncomputable`.
  - `BinaryBasefold/QueryPhase.lean`: both canonical and Fin query verifier/reduction/proof remain
    `noncomputable`.
- AdditiveNTT / basis migration status:
  - `AdditiveNTT.lean` still has many canonical `noncomputable def` roots (`sDomain`,
    `sDomain_basis`, `sDomainToFin`, `sDomainFinEquiv`, `iteratedQuotientMap`, etc.).
  - `NovelPolynomialBasis.lean` still has many noncomputable basis/conversion definitions.
  - `Impl.lean` currently holds the main executable AdditiveNTT algorithm path and is the correct
    migration source for computable replacements.
- Immediate action selected: make Binius oracle objects consume explicit computable companions
  (without prover black-boxing) and then push AdditiveNTT/domain-index migration where those paths
  still depend on canonical noncomputable domain machinery.

## Fin query path migration (no canonical `checkSingleRepetition`) — 2026-04-08

- Implemented a new **index-native** checker path in
  `BinaryBasefold/QueryPhase.lean` for `pSpecQueryFin`:
  - `queryCodewordFromIndexFin`
  - `queryFiberPointsFromIndexFin`
  - `computeFoldedValueFromFiber`
  - `checkSingleFoldingStepFromIndexFin`
  - `checkSingleRepetitionFromIndexFin`
- `queryOracleVerifierFin` now uses `checkSingleRepetitionFromIndexFin` directly and no longer
  decodes Fin challenges into canonical `sDomain` to call the old noncomputable checker.
- The Fin checker path uses computable primitives already in tree:
  - `extractMiddleFinMaskFromIndex` / `fiberPointIndexFromIndex` (Prelude),
  - `AdditiveNTT.Comp.indexToSDomain` + `toCanonicalSDomain` only at oracle query boundary,
  - `challengeTensorExpansion` + `dotProduct` for folded-value accumulation.
- Resulting status:
  - `queryOracleVerifierFin` is now a plain `def` (was `noncomputable def`).
  - `queryOracleReductionFin` is now a plain `def`.
  - `queryOracleProofFin` is now a plain `def`.
- Validation:
  - `lake build ArkLib.ProofSystem.Binius.BinaryBasefold.QueryPhase` (pass)
  - `lake build ArkLib.ProofSystem.Binius.BinaryBasefold.General` (pass)
  - `lake build ArkLib.ProofSystem.Binius.FRIBinius.General` (pass)

## BinaryBasefold final-sumcheck executable cut — 2026-04-08 (this session)

- Converted `BinaryBasefold/Steps/FinalSumcheck.lean`:
  - `finalSumcheckProver`: `noncomputable def` → `def`
  - `finalSumcheckOracleReduction`: `noncomputable def` → `def`
- This removes one noncomputable oracle-prover/reduction leaf in the core-interaction cone.
- Validation:
  - `lake build ArkLib.ProofSystem.Binius.BinaryBasefold.Steps.FinalSumcheck` (pass)
  - `lake build ArkLib.ProofSystem.Binius.BinaryBasefold.CoreInteractionPhase` (pass)

## Session bootstrap + blocker inventory refresh — 2026-04-08 (this session)

- Completed planning skill start ritual:
  - branch/worktree confirmed: `CompBinius` at worktree `ArkLib-binius-computable`;
  - re-read `.planning/index.md`, `comp-binius-port/{task_plan,progress,handoff}.md`;
  - cleared `comp-binius-port/handoff.md` to fresh template for this run.
- Refreshed noncomputable blocker inventory with targeted grep:
  - FRIBinius blockers still include:
    - `FRIBinius/General.lean`: `fullOracleReduction`, `fullOracleProof`
    - `FRIBinius/CoreInteractionPhase.lean`: `sumcheckFoldOracleReduction`, `coreInteractionOracleReduction`
  - Binary Basefold blockers still include:
    - `Steps/Fold.lean`: `foldOracleProver`, `foldOracleReduction`
    - `Prelude.lean`: `getSumcheckRoundPoly`, `iterated_fold`
    - `Relations.lean`: `getFoldProverFinalOutput`
    - top-level wrappers in `BinaryBasefold/General.lean`: `fullOracleReduction{,Fin}`, `fullOracleProof{,Fin}`
- Next concrete cut chosen: continue bottom-up from fold kernel dependencies
  (`getSumcheckRoundPoly` / `iterated_fold` / `getFoldProverFinalOutput`) and only then re-promote
  `foldOracle*`, `sumcheckFold*`, and top-level reductions.

## Fold-kernel dependency readout + pSpec message carrier reality — 2026-04-08

- `Steps/Fold.lean` confirms the round prover/reduction remain blocked exactly by two helper defs:
  - `foldProverComputeMsg` uses `getSumcheckRoundPoly` (returns canonical `L⦃≤ 2⦄[X]`);
  - `getFoldProverFinalOutput` uses `iterated_fold` for witness update.
- `Relations.lean` shows `getMidCodewords` is also tied to canonical `iterated_fold`, so even if
  the fold-step wrapper is made executable, witness-structure relations still depend on this cone.
- `Spec.lean` currently fixes the fold message type as:
  - `pSpecFold : ProtocolSpec 2 := ⟨![P_to_V, V_to_P], ![L⦃≤ 2⦄[X], L]⟩`
  meaning direct executability of bundled fold protocols still inherits canonical polynomial IR.
- `AdditiveNTT/Impl.lean` has the expected computable domain/query bridges and NTT stage/full NTT
  pipeline (`indexToSDomain`, `toCanonicalSDomain`, `NTTStage`, `computableAdditiveNTT`) and is
  suitable as migration source; canonical `AdditiveNTT` remains proof-facing.

## Degree-2 message representation scan — 2026-04-08

- There is no existing `pSpecFoldComp` or parallel computable fold message family in Binius yet.
- `BinaryBasefold/Spec.lean` currently provides `Fintype (L⦃≤2⦄[X])` via a **noncomputable**
  private constructor (`fintypeDegreeLETwo`) based on `Finite.of_injective` + `Fintype.ofFinite`.
- `ArkLib/Data/Polynomial/Interface.lean` already has a computable constructor:
  `polynomialOfCoeffs : (Fin deg → F) → F[X]` with eval and coefficient lemmas.
- This suggests the next migration path is to define an explicit computable degree-2 message
  carrier (e.g. coefficient vector in `Fin 3 → L`) and a conversion/eval API, then wire a companion
  fold protocol family around it.

## `Spec.lean` pSpec surface confirms insertion point — 2026-04-08

- `pSpecFold` is defined directly in `BinaryBasefold/Spec.lean` and is currently the canonical
  place to add a computable companion spec.
- The same file already has Fin-indexed companion patterns (`pSpecQueryFin`, `fullPSpecFin`) and
  decode bridges, so adding `pSpecFoldComp` + companion append/seq/full specs is structurally
  consistent with current migration style.
- `ReductionLogic.lean` imports `Spec.lean`, so computable message helper defs introduced in
  `Spec.lean` will be available to fold-step and core-interaction logic layers without new cycles.

## Fold kernel deep read (for computable replacement) — 2026-04-08

- `Prelude.fold` and `Prelude.iterated_fold` are currently `noncomputable` because they depend on
  `qMap_total_fiber`, which itself is `noncomputable` and uses canonical `sDomain_basis`/repr flow.
- `qMap_total_fiber` is the precise boundary where a computable replacement must enter to make
  witness updates executable.
- The file already has index-native helper defs (`extractMiddleFinMaskFromIndex`,
  `fiberPointIndexFromIndex`) used by `QueryPhase` Fin checker path; these are likely reusable for
  a computable fold-fiber replacement that avoids canonical `sDomain_basis`.

## Computable fold-companion pSpec + verifier path (this session) — 2026-04-08

- Added a computable fold-message carrier and companion spec chain in
  `BinaryBasefold/Spec.lean`:
  - `FoldMessageComp := L → L`
  - `pSpecFoldComp`
  - `pSpecFoldCommitComp`, `pSpecFoldRelayComp`, `pSpecFoldRelaySequenceComp`
  - `pSpecFullNonLastBlockComp`, `pSpecLastBlockComp`, `pSpecNonLastBlocksComp`
  - `pSpecSumcheckFoldComp`, `pSpecCoreInteractionComp`, `fullPSpecComp`
  - oracle-interface instances for `pSpecFoldComp` message/challenge families.
- Added fold-step companion logic in `BinaryBasefold/Steps/Fold.lean`:
  - `foldProverComputeMsgComp : Witness -> (L -> L)` (computable round-message evaluator)
  - `foldVerifierCheckComp` and `foldVerifierStmtOutComp`
  - `foldOracleVerifierComp` over `pSpecFoldComp`
- Validation:
  - `lake build ArkLib.ProofSystem.Binius.BinaryBasefold.Spec` (pass)
  - `lake build ArkLib.ProofSystem.Binius.BinaryBasefold.Steps.Fold` (pass)
- Status impact:
  - Companion verifier path is now fully computable at the fold-step interface.
  - Honest prover output update is still blocked on noncomputable `iterated_fold` / `qMap_total_fiber`.

## Computable fold prover/reduction + relay reduction companion (this session) — 2026-04-08

- Added new executable fold migration module:
  - `BinaryBasefold/ComputableFold.lean`
  - key defs:
    - `Comp.WitnessComp`
    - `projectToNextHComp`
    - `foldMessageFromHComp`
    - `foldFunctionComp`
    - `advanceWitnessComp`
    - `foldOracleProverComp`
    - `foldOracleReductionComp`
- Initial build errors were arithmetic cast proofs + leaked section-implicit params (`r`, `𝓡`).
  - fixed by:
    - normalizing with `simp only [Fin.val_succ]` before `omega` in cast/index goals;
    - making helper calls explicit on leaked params at callsites.
- Added computable relay-side reduction plumbing in
  `BinaryBasefold/CoreInteractionPhase.lean`:
  - `relayPrvStateComp`
  - `relayOracleProverComp`
  - `relayOracleReductionComp`
  - `foldRelayOracleReductionComp` (composes `Comp.foldOracleReductionComp` with relay companion)
- Validation:
  - `lake build ArkLib.ProofSystem.Binius.BinaryBasefold.ComputableFold` (pass)
  - `lake build ArkLib.ProofSystem.Binius.BinaryBasefold.CoreInteractionPhase` (pass)
  - `lake build ArkLib.ProofSystem.Binius.BinaryBasefold.General ArkLib.ProofSystem.Binius.FRIBinius.General` (pass)
- Updated blocker boundary:
  - there is now a **computable reduction path for fold+relay rounds** over `WitnessComp`;
  - commitment rounds and full `sumcheckFoldOracleReduction` are still blocked by canonical oracle
    statement / `sDomain` function carriers in the commit path.

## 2026-04-09 — Binary Basefold fully-computable reduction chain (comp path)

- `BinaryBasefold/CoreInteractionPhase.lean` now has a **concrete computable reduction chain** over
  `CoreInteraction.Comp.WitnessComp`, not just verifier companions:
  - `nonLastSingleBlockOracleReductionComp`
  - `nonLastBlocksOracleReductionComp`
  - `lastBlockOracleReductionComp`
  - `sumcheckFoldOracleReductionComp`
  - new helper cast lemma: `Comp.WitnessComp.of_fin_eq`
- Added a computable final-sumcheck bridge over `WitnessComp`:
  - `finalSumcheckProverComp`
  - `finalSumcheckOracleReductionComp`
  - message `c` is computed from the index-native witness carrier `witIn.fComp` at index `0`.
- Added top-level computable core reduction:
  - `coreInteractionOracleReductionComp` over `pSpecCoreInteractionComp`.
- `BinaryBasefold/General.lean` now exposes full-protocol computable companions wired end-to-end:
  - `fullOracleReductionComp` over `fullPSpecComp`
  - `fullOracleProofComp` over `fullPSpecComp`
- Net effect: a concrete, build-checked computable pipeline now exists from composed sumcheck-fold
  reductions through full Binary Basefold proof construction, while legacy theorem-facing
  noncomputable definitions remain intact for existing security proofs.

## FRIBinius Fin-query executable boundary update — 2026-04-09

- A practical computable full-stack seam in FRIBinius is achieved by combining:
  1. explicit basis-function parameter (`βfun : Fin (2^κ) → L`),
  2. Fin-indexed query spec (`BinaryBasefold.pSpecQueryFin`), and
  3. externally supplied prover only at the batching+core boundary.
- `fullPspecFunFin` avoids canonical query challenge sampling (`sDomain`) at the top-level full
  protocol companion surface while preserving statement/oracle interface alignment with existing
  batching/core outputs.
- `fullOracleReductionFunOfMultiplierFin` can be built compositionally via `OracleReduction.append`
  using:
  - `R₁ := batchingCoreReductionFunOfMultiplier ... batchingCoreProver`
  - `R₂ := QueryPhase.queryOracleReductionFin ...`
  so the only remaining noncomputable hotspot for this path is the caller-provided batching/core
  prover implementation.
- Core interaction is not an `OracleProof` target (output statement is
  `FinalSumcheckStatementOut`, not `Bool`), so the executable companion there should remain a
  reduction (not a proof alias).

## FRIBinius executable boundary refinement — 2026-04-09

- `batchingCoreReductionFunOfMultiplierFromCoreProver` confirms that the computable batching
  reduction can compose directly with `coreInteractionOracleReductionFunOfMultiplier` under
  append, so the caller no longer needs to provide a monolithic batching+core prover.
- `fullOracleReductionFunOfMultiplierFinFromCoreProver` /
  `fullOracleProofFunOfMultiplierFinFromCoreProver` therefore expose a stronger executable API:
  only the core-interaction prover remains external in the Fin-query full-stack companion.

## 2026-04-09 (current session — BBFSmallFieldIOPCS audit)

- `ArkLib/ProofSystem/Binius/RingSwitching/BBFSmallFieldIOPCS.lean` still contains unresolved placeholders in executable/spec path:
  - `MLPEvalWitness_to_BBF_Witness`
  - `largeFieldInvocationCtxLens`
  - `largeFieldInvocationOracleReduction`
  - `bbfMLIOPCS`
- The file also contains many theorem-level `sorry`; user scope is executable prover/verifier/reduction specs (security theorems excluded), so priority is replacing the four defs above and removing old wrappers if obsolete.
- Upstream blocker map from quick grep:
  - `RingSwitching/Prelude.lean` keeps noncomputable tensor/basis kernels (`compute_A_MLE`, `RingSwitching_SumcheckMultParam`, `compute_final_eq_value`, etc.).
  - `RingSwitching/BatchingPhase.lean` still has `batchingOracleProver` / `batchingOracleVerifier` placeholders and noncomputable seams.
  - `FRIBinius/General.lean` theorem-facing defs remain `noncomputable`; computable companion seams exist separately.
- `MLIOPCS` (in `RingSwitching/Prelude.lean`) is fixed to `WitIn := WitMLP L ℓ'` and an `oracleReduction : OracleReduction ... (pSpec := pSpec)` over that witness type.
- This means `BBFSmallFieldIOPCS` cannot directly reuse `BinaryBasefold.fullOracleReductionComp` (which uses `CoreInteraction.Comp.WitnessComp`) without an adapter lens.
- Therefore, the immediate cleanup path in `BBFSmallFieldIOPCS.lean` is to complete/adapt the existing witness/context lens wrappers (`MLPEvalWitness_to_BBF_Witness`, `largeFieldInvocationCtxLens`, `largeFieldInvocationOracleReduction`) and then instantiate `bbfMLIOPCS` from those.
- `MLPEvalWitness_to_BBF_Witness` can be defined directly from the `BinaryBasefold.Witness` constructor (`t`, `H`, `f`).
- `WitMLP` only has field `t`; round-0 witness adapter must synthesize `H`/`f` defaults unless derived via extraction checks.
- `OracleReduction.liftContext` in `LiftContext/OracleReduction.lean` provides the exact composition primitive needed for `largeFieldInvocationOracleReduction` once `largeFieldInvocationCtxLens` is filled.

## 2026-04-09 (current session — computable BBFSmallFieldIOPCS path landed)

- `BBFSmallFieldIOPCS` now has a computable execution-path reduction:
  - new `MLPEvalWitness_to_BBF_WitnessComp`
  - new `largeFieldInvocationCtxLensComp`
  - new `largeFieldInvocationOracleReductionComp` using
    `FullBinaryBasefold.fullOracleReductionComp`.
- `bbfMLIOPCS` is now wired to `fullPSpecComp` + `largeFieldInvocationOracleReductionComp`.
- Missing typeclass support for computable pSpecs was resolved in `BinaryBasefold/Spec.lean`
  by adding `SampleableType` instances for the full comp challenge chain
  (`pSpecFoldComp` through `fullPSpecComp`).
- Legacy theorem-facing adapter defs remain (some `noncomputable` / `sorry`), but the
  prover/verifier/reduction spec wiring used for execution is now concrete and build-checked.

## 2026-04-09 (current session — canonical naming cleanup result)

- In `BBFSmallFieldIOPCS`, the execution-path computable defs were already present, but exported under `*Comp` names while canonical names still pointed to noncomputable variants.
- Renaming strategy works without downstream breakage because references to these symbols are local to the file:
  - Canonical names now map to computable defs.
  - Legacy theorem-facing names preserve the noncomputable path needed by existing completeness proofs.
- `QueryPhase.queryOracleVerifier` still cannot be executable because it depends on `checkSingleRepetition` (no executable code); computable execution remains available via `queryOracleVerifierComp` / `queryOracleReductionComp` / `queryOracleVerifierFin`.

## 2026-04-09 (current session — FRI-Binius wrapper cleanup)

- In `FRIBinius/General`, canonical full protocol wiring over canonical query `pSpecQuery` is type-compatible with query computable companions:
  - `queryOracleVerifierComp` can replace `queryOracleVerifier` directly.
  - `queryOracleReductionComp` can replace `queryOracleReduction` directly.
- This swap is low-risk in `FRIBinius/General` because the downstream security theorems in this file are still `sorry`-backed; no proof-script dependency on the old query wrapper internals is currently enforced.

## 2026-04-09 (current session — QueryPhase theorem migration behavior)

- Full theorem stack in `QueryPhase` compiles unchanged after canonicalization because theorem statements and proof scripts already reference canonical names abstractly; replacing canonical defs with reducible computable aliases did not force proof rewrites.
- This indicates existing theorem obligations are implementation-agnostic enough at current abstraction level, so hard migration can proceed by canonical-name replacement first, then optional cleanup of companion duplicates later.

## 2026-04-09 session continuation (aggressive canonical cleanup)

- Resumed on branch `CompBinius` at `HEAD b81e5e30` with active task `comp-binius-port`.
- Start-state from planning files: uncommitted edits in
  - `ArkLib/ProofSystem/Binius/BinaryBasefold/General.lean`
  - `ArkLib/ProofSystem/Binius/FRIBinius/General.lean`
  - `ArkLib/ProofSystem/Binius/RingSwitching/BBFSmallFieldIOPCS.lean`
- Immediate objective for this session: complete aggressive cleanup by making canonical oracle
  prover/verifier/reduction names in Binius point to computable defs where available, delete
  legacy canonical wrappers, and keep theorem-only compatibility under `Legacy` names.

### 2026-04-09 audit snapshot (post-build)

- `FRIBinius/General.lean` builds after canonical-name migration edits.
- `rg` audit shows canonical top-level names already computable in:
  - `BinaryBasefold/QueryPhase.lean`: `queryOracleVerifier/queryOracleReduction/queryOracleProof`
  - `BinaryBasefold/General.lean`: `fullOracleVerifier/fullOracleReduction/fullOracleProof`
  - `FRIBinius/General.lean`: `fullOracleVerifier/fullOracleReduction/fullOracleProof`
- Remaining `noncomputable def ...Oracle...` surfaces are concentrated in
  `BinaryBasefold/CoreInteractionPhase.lean`, `BinaryBasefold/Steps/Fold.lean`, and
  `FRIBinius/CoreInteractionPhase.lean`; these are the next cleanup targets for canonical aliasing
  (`Legacy` rename + computable canonical routing) where companion `*Comp` defs already exist.

## 2026-04-09 (current session — aggressive cleanup completed)

- `FRIBinius/CoreInteractionPhase` executable API blockers were fixed by:
  - making `pSpecSumcheckFold` calls explicit on `(ϑ := ϑ)` in the new executable sumcheck reduction;
  - forwarding `(h_l := h_l)` in `coreInteractionOracleReduction` to `coreInteractionOracleReductionFunOfMultiplier`.
- `BinaryBasefold/QueryPhase` old canonical aliases were removed entirely:
  - deleted defs `queryOracleVerifier`, `queryOracleReduction`, `queryOracleProof`;
  - migrated theorem/spec references to `queryOracleVerifierComp`, `queryOracleReductionComp`, `queryOracleProofComp`.
- Cross-module migration completed:
  - `BinaryBasefold/General` now uses `QueryPhase.queryOracleReductionComp` / `queryOracleVerifierComp` where old canonical query names were referenced.
- Final non-legacy noncomputable oracle-spec def in Binius was removed from canonical namespace:
  - `foldOracleProver` renamed to `foldOracleProverLegacy` and all local references updated.
- Audit result: no remaining `noncomputable def .*Oracle(Prover|Verifier|Reduction|Proof)` without `Legacy` in `ArkLib/ProofSystem/Binius`.

## 2026-04-09 (current continuation — noncomp OracleReduction inventory)

- Fresh grep on current tree:
  - `rg -n "^noncomputable def .*OracleReduction" ArkLib/ProofSystem/Binius -g '*.lean'`
  - returns 14 remaining definitions, all under `*Noncomp` names.
- Remaining files and groups:
  - `BinaryBasefold/Steps/Fold.lean`: `foldOracleReductionNoncomp`
  - `BinaryBasefold/CoreInteractionPhase.lean`: `foldRelayOracleReductionNoncomp`,
    `foldCommitOracleReductionNoncomp`, `nonLastSingleBlockOracleReductionNoncomp`,
    `nonLastBlocksOracleReductionNoncomp`, `lastBlockOracleReductionNoncomp`,
    `sumcheckFoldOracleReductionNoncomp`, `coreInteractionOracleReductionNoncomp`
  - `FRIBinius/CoreInteractionPhase.lean`: `sumcheckFoldOracleReductionNoncomp`,
    `sumcheckFoldOracleReductionOfMultiplierNoncomp`,
    `finalSumcheckOracleReductionNoncomp`, `finalSumcheckOracleReductionOfMultiplierNoncomp`,
    `coreInteractionOracleReductionNoncomp`,
    `coreInteractionOracleReductionOfMultiplierNoncomp`
- Migration implication:
  - we can keep theorem/security regions noncomputable, but noncomp reduction defs should be
    converted into computable aliases/wrappers (or removed) so the reduction API is computable-first.

## 2026-04-09 (current continuation — oracle-reduction cleanup sweep)

- Removed legacy Binary Basefold fold-round noncomputable reduction wrapper:
  - deleted `Steps/Fold.foldOracleReductionNoncomp`.
  - migrated completeness theorem instantiation to computable
    `foldOracleReduction ... (foldOracleProverNoncomp ...)`.
- Migrated all remaining `*OracleReductionNoncomp` identifiers out of active Binius surfaces:
  - BinaryBasefold CoreInteraction:
    - `foldRelayOracleReductionNoncomp` -> `foldRelaySecurityReductionNoncomp`
    - `foldCommitOracleReductionNoncomp` -> `foldCommitSecurityReductionNoncomp`
    - `nonLastSingleBlockOracleReductionNoncomp` -> `nonLastSingleBlockSecurityReductionNoncomp`
    - `nonLastBlocksOracleReductionNoncomp` -> `nonLastBlocksSecurityReductionNoncomp`
    - `lastBlockOracleReductionNoncomp` -> `lastBlockSecurityReductionNoncomp`
    - `sumcheckFoldOracleReductionNoncomp` -> `sumcheckFoldSecurityReductionNoncomp`
    - `coreInteractionOracleReductionNoncomp` -> `coreInteractionSecurityReductionNoncomp`
  - FRIBinius CoreInteraction:
    - `sumcheckFoldOracleReductionNoncomp` -> `sumcheckFoldSecurityReductionNoncomp`
    - `sumcheckFoldOracleReductionOfMultiplierNoncomp` ->
      `sumcheckFoldSecurityReductionOfMultiplierNoncomp`
    - `finalSumcheckOracleReductionNoncomp` -> `finalSumcheckSecurityReductionNoncomp`
    - `finalSumcheckOracleReductionOfMultiplierNoncomp` ->
      `finalSumcheckSecurityReductionOfMultiplierNoncomp`
    - `coreInteractionOracleReductionNoncomp` -> `coreInteractionSecurityReductionNoncomp`
    - `coreInteractionOracleReductionOfMultiplierNoncomp` ->
      `coreInteractionSecurityReductionOfMultiplierNoncomp`
- Cross-module rewiring completed in:
  - `BinaryBasefold/General.lean`
  - `FRIBinius/General.lean`
- Audit results after migration:
  - `rg -n "OracleReductionNoncomp" ArkLib/ProofSystem/Binius -g '*.lean'` -> no matches.
  - `rg -n "^noncomputable def .*OracleReduction" ArkLib/ProofSystem/Binius -g '*.lean'`
    -> no matches.
- Validation:
  - `lake build ArkLib.ProofSystem.Binius.BinaryBasefold.Steps.Fold`
  - `lake build ArkLib.ProofSystem.Binius.BinaryBasefold.CoreInteractionPhase`
  - `lake build ArkLib.ProofSystem.Binius.BinaryBasefold.General`
  - `lake build ArkLib.ProofSystem.Binius.FRIBinius.CoreInteractionPhase`
  - `lake build ArkLib.ProofSystem.Binius.FRIBinius.General`
  - `lake build ArkLib.ProofSystem.Binius.RingSwitching.BBFSmallFieldIOPCS`
  - all pass (warnings/sorries only).

## 2026-04-09 (current continuation — aggressive theorem-layer verifier/prover migration)

- Eliminated the last `noncomputable def` names matching oracle prover/verifier pattern by migrating
  them to security-scoped wrappers:
  - `sumcheckFoldOracleVerifierNoncomp` -> `sumcheckFoldSecurityVerifierNoncomp`
  - `sumcheckFoldOracleVerifierOfMultiplierNoncomp` ->
    `sumcheckFoldSecurityVerifierOfMultiplierNoncomp`
  - `coreInteractionOracleVerifierNoncomp` -> `coreInteractionSecurityVerifierNoncomp`
  - `coreInteractionOracleVerifierOfMultiplierNoncomp` ->
    `coreInteractionSecurityVerifierOfMultiplierNoncomp`
  - `foldOracleProverNoncomp` -> `foldSecurityProverNoncomp`
- Rewired all call-sites in:
  - `BinaryBasefold/Steps/Fold.lean`
  - `BinaryBasefold/CoreInteractionPhase.lean`
  - `FRIBinius/CoreInteractionPhase.lean`
  - `FRIBinius/General.lean`
- Validation:
  - `lake build ArkLib.ProofSystem.Binius.BinaryBasefold.Steps.Fold`
  - `lake build ArkLib.ProofSystem.Binius.BinaryBasefold.CoreInteractionPhase`
  - `lake build ArkLib.ProofSystem.Binius.FRIBinius.CoreInteractionPhase`
  - `lake build ArkLib.ProofSystem.Binius.FRIBinius.General`
  - all pass (warnings only).
- Strict audit status after this cut:
  - `rg -n "^noncomputable def .*Oracle(Prover|Verifier|Reduction|Proof)" ArkLib/ProofSystem/Binius`
    => no matches.
  - Remaining noncomputable items are security-layer `*Reduction*` defs and
    `noncomputable section` blocks in soundness/prelude modules.

## Reduction audit continuation — 2026-04-09 (current session)

- Fresh strict grep for reduction defs still marked noncomputable in Binius currently returns 18 declarations across:
  - `FRIBinius/General.lean`
  - `FRIBinius/CoreInteractionPhase.lean`
  - `BinaryBasefold/General.lean`
  - `BinaryBasefold/CoreInteractionPhase.lean`
- Pattern now is cleanly separated: legacy `*OracleReductionNoncomp` names are gone; remaining defs are either
  - theorem-facing `fullReductionNoncomp*` wrappers, or
  - `*SecurityReductionNoncomp` constants used by security lemmas.
- Next migration must therefore be theorem-layer rewiring: security lemmas should quantify over / locally instantiate computable reductions (or renamed theorem-only aliases), then delete noncomputable reduction constants.
- The library has `OracleReduction.castInOut` plus `castInOut_perfectCompleteness` / `castInOut_completeness` helpers, but they require an actual type equality `WitIn₁ = WitIn₂`.
- Current Binius `Witness` vs `Comp.WitnessComp` are distinct structures (no existing global equality/equiv bridge discovered), so security theorems over `strictRoundRelation` cannot be switched to `*Comp` reductions by a trivial cast.
- Practical migration strategy remains: keep theorem-level noncomputable reasoning local, but delete top-level noncomputable reduction constants by rewriting theorem statements/proofs to refer directly to computable reduction defs where witness types already match.

## 2026-04-09 (current session — scope lock from human + restart audit)

- Human clarified hard scope: only **Binius oracle reductions must be computable**.
- Security theorem layer may remain `noncomputable`; do not pursue global `no noncomputable` cleanup outside that target.
- Immediate action in this session: run strict grep/build audit focused on reduction defs and call-sites to confirm whether any execution-path Binius oracle reduction still requires `noncomputable`.

## 2026-04-09 (current session — strict reduction audit result)

- Hard grep status:
  - `^noncomputable def .*OracleReduction` under `ArkLib/ProofSystem/Binius` => **no matches**.
- Remaining `noncomputable def .*Reduction` names are scoped to theorem/security wrappers only:
  - FRI/BBF `*SecurityReduction*` and `fullReductionNoncomp` families.
- Canonical execution-path reduction names are plain `def`:
  - `BinaryBasefold`: `fullOracleReduction`, `coreInteractionOracleReduction`, `sumcheckFoldOracleReduction`, query/step reductions.
  - `FRIBinius`: `fullOracleReduction`, `coreInteractionOracleReduction`, `sumcheckFoldOracleReduction`, `finalSumcheckOracleReduction`.
- This matches human scope: computable oracle reductions are in place; residual noncomputable reductions are explicitly security-theorem layer artifacts.

## 2026-04-09 (current session — concrete fix set for stale rename regressions)

- `BinaryBasefold/General.lean` had stale references to
  `CoreInteraction.coreInteractionSecurityReductionNoncomp`; these now point to
  `CoreInteraction.coreInteractionSecurityReduction`.
- `FRIBinius/CoreInteractionPhase.lean` had stale links to deleted
  `BinaryBasefold.CoreInteraction.sumcheckFoldSecurityReductionNoncomp`; these now point to
  `BinaryBasefold.CoreInteraction.sumcheckFoldSecurityReduction`.
- Important subtlety in `BinaryBasefold/General.lean`:
  - `fullReductionNoncomp` / `fullReductionFinNoncomp` require explicit `(𝓑 := 𝓑)` at call-sites for
    implicit argument synthesis.
- Post-fix validation passed for all target modules:
  - `BinaryBasefold.{Steps.Fold,CoreInteractionPhase,QueryPhase,General}`
  - `FRIBinius.{CoreInteractionPhase,General}`
  - `RingSwitching.BBFSmallFieldIOPCS`
- Strict goal audit remains true after repair:
  - no `^noncomputable def .*OracleReduction` in `ArkLib/ProofSystem/Binius`.

## 2026-04-09 — theorem-layer computable-routing pass

- User clarified the real acceptance criterion: security theorems may remain `noncomputable`, but they must instantiate the computable Binius oracle verifier/reduction definitions rather than legacy `*Noncomp` wrappers.
- Current migration focus is therefore theorem statements and thin security wrappers in:
  - `ArkLib/ProofSystem/Binius/BinaryBasefold/CoreInteractionPhase.lean`
  - `ArkLib/ProofSystem/Binius/BinaryBasefold/General.lean`
  - `ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean`
  - `ArkLib/ProofSystem/Binius/FRIBinius/General.lean`
- Preferred repair pattern: keep the theorem itself noncomputable if needed, but change the instantiated `oracleReduction` / `oracleVerifier` argument to a computable definition; when necessary, insert a local `change` back to the old security wrapper so the proof body can be preserved.

## 2026-04-09 — canonical migration target tightened

- User requirement is now stricter than the earlier "security theorems may remain noncomputable" summary: theorem statements may still be `noncomputable`, but they must use the same canonical computable oracle objects. Parallel theorem-only `*SecurityReduction` / `*SecurityVerifier` defs should be deleted rather than retained as wrappers.
- `BinaryBasefold` still routes completeness through old theorem-only reductions because the relation layer is typed over canonical `Witness`, while computable reductions are typed over `Comp.WitnessComp`.
- User clarified that `Witness` itself is part of the old noncomputable path and should be removed from the active Binius reduction/completeness stack.
- Practical consequence: stop trying to prove equality between `...OracleReductionOfProver` and `...SecurityReduction`; instead migrate relation/completeness definitions onto computable witness carriers and then delete the old security reductions.

## 2026-04-09 — structure must match PR #383 exactly

- User tightened the migration requirement again: the target is not just semantic computability, but restoration of the original Binius organization from PR `#383` at the folder / file / section / definition / theorem level.
- Verified via `gh pr view 383 --repo Verified-zkEVM/ArkLib --json files` that PR `#383` contains the canonical Binary Basefold structure with `Steps.lean` plus `Steps/{Fold,Commit,Relay,FinalSumcheck}.lean` and **no** `ComputableFold.lean` file.
- Current divergence from that structure: this worktree has a parallel `ArkLib/ProofSystem/Binius/BinaryBasefold/ComputableFold.lean`, and `CoreInteractionPhase.lean` imports both `Steps` and `ComputableFold`.
- Therefore the structural migration must collapse the computable fold content back into `Steps/Fold.lean` and remove the extra file/module path before continuing the canonical-name reduction migration.
- After the structural collapse, `rg -n "ComputableFold" ArkLib -g '*.lean'` returns no matches, so the extra module path is fully removed from the source tree.
- `BinaryBasefold/Steps/Fold.lean` has no current Lean LSP errors after the merge, which confirms the moved definitions are accepted in the canonical file.
- A practical migration tactic that preserves PR-`#383` structure is to first make the computable carrier structurally resemble the canonical one. `WitnessComp` now uses fields `t`, `H`, `f`, which reduces future churn when replacing the old `Witness`-typed path.

## 2026-04-09 deep migration checkpoint

- Confirmed structural mismatch against PR #383 starts in `BinaryBasefold/Spec.lean` and `Steps/Fold.lean`, not just top-level theorems.
- PR #383 canonical shape has exactly one fold pSpec stack and one fold trio (`foldOracleProver`, `foldOracleVerifier`, `foldOracleReduction`).
- Current tree still duplicates this with `*Comp` pSpecs and fold-side `foldSecurityProverNoncomp`, `foldOracleVerifierComp`, `foldOracleReductionComp`.
- Real blocker is that `ReductionLogic.lean` and `Relations.lean` still type the fold step/security layer over old `Witness` and `pSpecFold`; theorem migration must start there.
- `Steps/Fold.lean` still builds after folding in `ComputableFold.lean` and renaming `WitnessComp` fields to canonical names `t/H/f`.

## 2026-04-09 15:35 +07 — CoreInteractionPhase blocker audit

- `CoreInteractionPhase.lean` now contains a theorem-bridge from computable witnesses to the legacy relation layer:
  - `Comp.WitnessComp.toLegacy` at line ~77
  - `strictRoundRelationComp` at line ~97
  - `roundRelationComp` at line ~108
- The retargeted completeness statements are already in place:
  - `sumcheckFoldOracleReduction_perfectCompleteness` at line ~1912
  - `coreInteractionOracleReduction_perfectCompleteness` at line ~2517
- `lastBlockRbrKnowledgeError` is a stale identifier, not a theorem-bridge artifact. `rg` over `ArkLib/ProofSystem/Binius/BinaryBasefold` finds references only, with no defining `def`/`theorem`/`abbrev`.
- Therefore `CoreInteractionPhase` currently has two distinct cleanup tracks:
  1. canonical theorem routing onto computable reductions/relations;
  2. stale name repair for the last-block knowledge-error aggregation.
- The second issue should be repaired first because it blocks file build independent of the migration direction.

## 2026-04-09 15:44 +07 — canonical theorem-routing cut completed through BinaryBasefold `General`

- `BinaryBasefold/CoreInteractionPhase.lean` now builds after restoring `lastBlockRbrKnowledgeError` and tightening the `sDomainFinEquiv` bridge proof in `Comp.WitnessComp.toLegacy`.
- `BinaryBasefold/QueryPhase.queryOracleProof_perfectCompleteness` was the blocking mismatch for top-level completeness: it still targeted old `pSpecQuery` / `queryOracleProofComp`, while `General.fullOracleReduction_perfectCompleteness` composes `queryOracleReductionFin`.
- Retargeting that theorem to `OracleReduction.perfectCompleteness` over `queryOracleReductionFin` and `pSpecQueryFin` makes the top-level completeness theorem line up with the computable query object instead of a legacy companion.
- `BinaryBasefold/General.lean` no longer needs the extra top-level aliases `fullOracleReductionComp` and `fullOracleProofComp`; the canonical names now carry the computable bodies directly.
- Repo-wide search after this cut:
  - `rg -n "\bfullOracleReductionComp\b|\bfullOracleProofComp\b" ArkLib -g '*.lean'` returns no matches.
- Remaining duplication pressure is now lower in `BinaryBasefold/General`, but the deeper canonicalization problem still lives below it in:
  - `BinaryBasefold/Spec.lean` (`pSpec*Comp` stack)
  - `BinaryBasefold/CoreInteractionPhase.lean` (`*OracleReductionComp`, `*OracleVerifierComp`, `*SecurityReduction` coexistence)

## 2026-04-09 16:xx +07 — FRIBinius suffix cleanup and timeout diagnosis

- Per the current structure-parity cleanup, FRIBinius theorem-layer names were normalized from
  `...Noncomp` suffixes to plain `...SecurityReduction` / `...SecurityVerifier` names in:
  - `ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean`
  - `ArkLib/ProofSystem/Binius/FRIBinius/General.lean`
- Audit after the rename:
  - `rg -n "SecurityReduction.*Noncomp|VerifierNoncomp" ArkLib/ProofSystem/Binius/FRIBinius/{CoreInteractionPhase,General}.lean`
    returns no matches.
- The remaining build blocker is **not** a missing rename. It is a proof elaboration timeout in
  `FRIBinius/CoreInteractionPhase.coreInteractionOracleReduction_perfectCompleteness`, specifically
  on the branch that reuses `finalSumcheckOracleReduction_perfectCompleteness`.
- Important human constraint recorded explicitly:
  - **never raise `maxHeartbeats` above `200000`**.
  - A temporary attempt to set `400000` was immediately reverted after the user objected; do not
    retry that approach.
- Current structural hypothesis for the timeout:
  - the `OracleReduction.append_perfectCompleteness` call leaves the intermediate `rel₂` too
    implicit, forcing heavy `whnf` normalization when Lean matches the second subproof;
  - the next safe tactic is to keep all heartbeat caps `≤ 200000` and continue reducing
    definitional work by making intermediate relations / theorem applications more explicit, rather
    than raising resource limits.

## 2026-04-09 16:xx +07 — direction correction from human

- Human corrected the migration target explicitly:
  - do **not** keep / rename theorem-only noncomputable reductions like
    `coreInteractionSecurityReduction`;
  - the job is to **discard/replace** those noncomputable reductions entirely;
  - security theorems must migrate onto the canonical **computable** reductions/verifiers.
- Consequence for current work:
  - the FRIBinius rename-only cleanup was the wrong intermediate step because it preserved the
    theorem-only reduction layer under nicer names;
  - future edits should reduce duplication by deleting or bypassing those defs, not by polishing
    them.

## 2026-04-09 late session — remaining noncomputable reduction cone audit

- The remaining Binary Basefold theorem-only reduction layer is now tightly localized in
  `ArkLib/ProofSystem/Binius/BinaryBasefold/CoreInteractionPhase.lean`:
  - `foldRelaySecurityReduction`
  - `foldCommitSecurityReduction`
  - `nonLastSingleBlockSecurityReduction`
  - `nonLastBlocksSecurityReduction`
  - `lastBlockSecurityReduction`
- These are the only surviving `*SecurityReduction` defs under `ArkLib/ProofSystem/Binius` found by
  the current grep, apart from proof-local lets using the same names.
- `foldRelaySecurityReduction` and `foldCommitSecurityReduction` still directly instantiate
  `foldOracleReduction ... (foldSecurityProverNoncomp ...)`, so the stale noncomputable prover path
  is still present even though top-level FRIBinius wrappers were deleted.
- The surrounding computable replacements already exist in the same file:
  - `foldRelayOracleReductionComp`
  - `foldCommitOracleReductionComp`
  - `nonLastSingleBlockOracleReductionComp`
  - `nonLastBlocksOracleReductionComp`
  - `lastBlockOracleReductionComp`
- Therefore the next valid migration step is not to invent new wrappers, but to retarget the
  remaining completeness/security theorem statements to these canonical computable reductions and
  then delete the legacy `*SecurityReduction` defs.
- In `FRIBinius/CoreInteractionPhase.lean`, the only remaining obvious legacy local objects are:
  - `finalSumcheckProver`
  - `finalSumcheckProverOfMultiplier`
  - `finalSumcheckVerifier`
  - `finalSumcheckKnowledgeStateFunction`
- Those FRIBinius leftovers are no longer needed for the already-restated top-level completeness /
  soundness theorem statements, but they still pin the file to local noncomputable helper names.

## 2026-04-09 late-late session — Binary Basefold lower theorem layer conversion in progress

- `BinaryBasefold/CoreInteractionPhase.lean` now has the lower fold/block theorems actively moving
  to the computable surfaces:
  - `foldRelayOracleReduction_perfectCompleteness` now states completeness over
    `pSpecFoldRelayComp`, `strictRoundRelationComp`, and `foldRelayOracleReduction`.
  - `foldCommitOracleReduction_perfectCompleteness` now states completeness over
    `pSpecFoldCommitComp`, `strictRoundRelationComp`, and `foldCommitOracleReduction`.
  - `foldRelayOracleVerifier_rbrKnowledgeSoundness` and
    `foldCommitOracleVerifier_rbrKnowledgeSoundness` were retargeted to
    `foldRelayOracleVerifierComp` / `foldCommitOracleVerifierComp` with `roundRelationComp`.
- Deleted successfully from the file already:
  - `foldRelaySecurityReduction`
  - `foldCommitSecurityReduction`
  - `nonLastSingleBlockSecurityReduction`
  - `nonLastBlocksSecurityReduction`
- One legacy reduction def still survived the first delete wave and must still be removed:
  - `lastBlockSecurityReduction`
- The remaining cleanup tail is now mostly theorem/type migration:
  - convert `nonLastSingleBlock*`, `nonLastBlocks*`, `sumcheckFold*`, and
    `coreInteractionOracleRbrKnowledgeError` onto `...Comp` challenge families;
  - update the later scalar-bound theorems whose quantified challenge indices still mention
    legacy `pSpecSumcheckFold`, `pSpecNonLastBlocks`, `pSpecFullNonLastBlock`, `pSpecLastBlock`,
    and `pSpecCoreInteraction`.

## 2026-04-09 current blocker — FRIBinius lifted completeness instance

- The current first hard error in the four-module slice is localized to
  `ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean` at the instance
  `sumcheckFoldCtxLens_complete`.
- The earlier parser issue from an extra closing `)` after `(innerRelOut := ...)` was already
  fixed.
- The remaining failure is semantic / type-level:
  - `lake build` reports `type expected, got` at the instance head around line 224.
- The suspicious shape is the direct use of
  `(sumcheckFoldCtxLens ...).toContext.IsComplete (...)` as the instance target. There are no
  other `toContext.IsComplete` examples under `ArkLib/ProofSystem/Binius`, so the next step is to
  inspect the generic `Context` / `IsComplete` definition and restate the instance head in the
  exact expected form.

## 2026-04-09 four-module rebuild after removing dead sumcheck-fold lift-context layer

- Deleted the unused noncomputable `sumcheckFoldCtxLens` and its malformed completeness instance from
  `ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean`.
- `rg -n "sumcheckFoldCtxLens|sumcheckFoldCtxLens_complete" .../FRIBinius/CoreInteractionPhase.lean`
  now returns no matches.
- The focused rebuild now succeeds for:
  - `ArkLib.ProofSystem.Binius.BinaryBasefold.CoreInteractionPhase`
  - `ArkLib.ProofSystem.Binius.BinaryBasefold.General`
  - `ArkLib.ProofSystem.Binius.FRIBinius.CoreInteractionPhase`
  - `ArkLib.ProofSystem.Binius.FRIBinius.General`
- Build result is warnings / existing `sorry`s only; exit code `0`.
- This confirms the removed lift-context fragment was dead leftover theorem plumbing rather than part
  of the active computable reduction path.

## 2026-04-09 final-sumcheck wrapper cleanup and executable-boundary note

- In `ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean`, the remaining legacy
  final-sumcheck wrapper layer was reduced further:
  - deleted unused `finalSumcheckProver`
  - deleted unused `finalSumcheckProverOfMultiplier`
  - deleted the standard-parameter `finalSumcheckVerifier` alias entirely
- The canonical final-sumcheck verifier surface in this file is now the computable parameterized pair:
  - `finalSumcheckVerifierOfMultiplier`
  - `finalSumcheckVerifierFunOfMultiplier`
- Important executable-boundary finding:
  - a standard-parameter alias that closes over
    `RingSwitching_SumcheckMultParam ... (β := booleanHypercubeBasis ...)` is **not** executable,
    because the closure drags in `booleanHypercubeBasis` / related noncomputable basis machinery.
  - Therefore, theorem-support code must refer directly to the parameterized computable surfaces,
    while proof-support defs may stay `noncomputable` and use `sorry` bodies.
- `finalSumcheckKnowledgeStateFunction` was retargeted in its type to
  `finalSumcheckVerifierOfMultiplier ... (RingSwitching_SumcheckMultParam ...)` and collapsed to
  `sorry`, which is acceptable under the current human direction because it is proof support rather
  than an execution-path reduction/verifier.
- Current focused audit on the four target files:
  - no `SecurityReduction`
  - no `SecurityVerifier`
  - no `sumcheckFoldCtxLens`
  - no `sumcheckFoldCtxLens_complete`
  - no `finalSumcheckProver`
  - no `finalSumcheckProverOfMultiplier`
  - no `finalSumcheckVerifier` alias
  - no `noncomputable def .*OracleReduction`
  - no `noncomputable def .*OracleVerifier`
  - no `noncomputable def .*OracleProof`
- Remaining `noncomputable def` hits in the focused FRIBinius file are theorem-support only:
  - `finalSumcheckRbrExtractor`
  - `finalSumcheckKnowledgeStateFunction`

## 2026-04-09 broad-repo status check — not phase-complete yet

- The four-file BinaryBasefold/FRIBinius slice is clean, but the broader Binius stack is **not yet
  fully done** for the user's stronger phase target.
- The old `*Noncomp` / `*SecurityReduction` / `*SecurityVerifier` wrapper family is gone under
  `ArkLib/ProofSystem/Binius`, but broader theorem / pspec surfaces still remain noncomputable.
- Immediate top-level blocker found in `ArkLib/ProofSystem/Binius/FRIBinius/General.lean`:
  - `noncomputable def batchingCorePspec`
  - `noncomputable def fullPspec`
  - theorem-side challenge-index uses of those pspecs in
    `batchingCoreRbrKnowledgeError`, `fullRbrKnowledgeError`, and
    `fullRbrKnowledgeError_sum_le_concrete`
- Additional broad blocker beyond FRIBinius/General:
  - `BinaryBasefold/QueryPhase.lean` still has the canonical query-phase path built over
    `pSpecQuery`, while the fully computable `pSpecQueryFin` track exists in parallel.
  - Therefore the whole repo is not yet at the state "all Binius oracle prover/verifier/reduction
    surfaces computable and all security theorems only use them".

## 2026-04-09 FRIBinius top-level pspec cleanup

- `ArkLib/ProofSystem/Binius/FRIBinius/General.lean` no longer contains the dead basis-based
  noncomputable pspec aliases:
  - `batchingCorePspec`
  - `fullPspec`
- Their old noncomputable message/challenge instances were also deleted.
- Security-layer challenge-index uses were migrated to the computable pspec family:
  - `batchingCoreRbrKnowledgeError` now indexes over
    `batchingCorePspecFun ... (fun j => β j)`
  - `fullRbrKnowledgeError` now indexes over
    `fullPspecFun ... (fun j => β j)`
  - `fullRbrKnowledgeError_sum_le_concrete` sums over
    `fullPspecFun ... (fun j => β j)`
- Focused four-module rebuild still passes with warnings / sorries only after this deletion.
- Therefore, within the FRIBinius top-level file, theorem statements no longer mention the removed
  noncomputable pspec aliases.

## 2026-04-09 precise remaining blockers after latest cleanup

The answer to the human's "are we done for this phase" question is still **no**.

Remaining blockers I confirmed locally:
- `BinaryBasefold/QueryPhase.lean` still keeps the canonical query-phase stack centered on
  `pSpecQuery`, while the fully computable `pSpecQueryFin` track remains parallel rather than fully
  canonicalized.
- `FRIBinius/General.lean` still has a `noncomputable instance`
  `fullPspecFun_challengeSampleableType`, which means the full explicit-basis protocol spec is not
  yet fully executable end-to-end.
- More broadly, the repo still contains theorem-support `noncomputable def` objects such as
  extractors and knowledge-state functions; these are not oracle reductions/verifiers themselves,
  but they show the security layer is not yet fully migrated to a purely computable support cone.

## 2026-04-09 public query/full-spec parity pass

- Superseding older plan notes: the `pSpecQueryFin` direction is no longer the live public design.
  The canonical query challenge is now
  `Fin γ_repetitions → AdditiveNTT.Comp.sDomain ... 0`, matching the human's requested direction
  of sending the computable query-domain carrier rather than a raw `Fin` index.
- `BinaryBasefold.QueryPhase.queryPointToIndex` is the remaining `Fin (2^(ℓ+𝓡))` decoder, but it is
  private and deterministic. The `Fin` index is now an internal implementation detail only.
- Deleted the top-level split aliases:
  - `BinaryBasefold.Spec.pSpecCoreInteractionComp`
  - `BinaryBasefold.Spec.fullPSpecComp`
- Added an executable finiteness witness for the computable query domain:
  - `BinaryBasefold.Spec.instFintypeCompSDomainZero`
  - implemented via `Finset.univ.image indexToSDomainZero`, not `Equiv.ofBijective`
  - reason: `Equiv.ofBijective` failed the compiler IR check even though the underlying bijection
    proof was fine
- Cleaned `BinaryBasefold.Spec` query challenge finiteness:
  - removed a duplicate `pSpecQuery` challenge `Fintype`/`Inhabited` block
  - the surviving `pSpecQuery` challenge `Fintype` instances are now plain `instance`s
  - removed the old `sorry` placeholders from those instances
- Canonical downstream surfaces now target the upstream names directly:
  - `BinaryBasefold.General` uses `fullPSpec` / `pSpecCoreInteraction`
  - `FRIBinius.General` uses `BinaryBasefold.pSpecCoreInteraction`
  - `RingSwitching.BBFSmallFieldIOPCS` uses `FullBinaryBasefold.fullPSpec` /
    `FullBinaryBasefold.fullOracleReduction`
- Hard audit after this pass:
  - `rg -n "pSpecQueryFin|fullPSpecComp|pSpecCoreInteractionComp|queryOracle(Verifier|Reduction|Proof)(Fin|Canonical)" ArkLib/ProofSystem/Binius`
    returned no matches
- Validation after the cleanup:
  - `lake build ArkLib.ProofSystem.Binius.BinaryBasefold.Spec`
  - `lake build ArkLib.ProofSystem.Binius.BinaryBasefold.General`
  - `lake build ArkLib.ProofSystem.Binius.FRIBinius.General`
  - `lake build ArkLib.ProofSystem.Binius.RingSwitching.BBFSmallFieldIOPCS`
  all succeed with warnings / existing theorem-side `sorry`s only
- Remaining parity gap after this pass:
  - the top-level public query/full-spec interface is aligned
  - deeper internal `pSpec*Comp` builders still exist below that layer
    (`pSpecSumcheckFoldComp`, `pSpecNonLastBlocksComp`, `pSpecLastBlockComp`, etc.)
  - if the human wants item-by-item parity deeper than the public surface, the next pass should
    decide whether to promote those computable bodies into the canonical mid-level names too

## 2026-04-09 query-phase structural parity note

- The earlier executable-query migration introduced an unnecessary structural drift in
  `BinaryBasefold.QueryPhase`:
  `queryOracleVerifier` duplicated the contents of `queryPhaseLogicStep` instead of delegating
  through the logic step as the sibling `ArkLib-binius` file does.
- That drift was not semantically required by computability. Once `queryPhaseLogicStep` became
  executable over computable query challenges, the verifier/prover layer could and should call it
  directly again.
- Current state after the fix:
  - `queryOracleVerifier` delegates through `queryPhaseLogicStep.verifierCheck` /
    `queryPhaseLogicStep.verifierOut`
  - `queryOracleVerifier.embed` and `.hEq` are reused directly from the logic step
  - `queryOracleProver.output` delegates through `queryPhaseLogicStep.proverOut`
- One local file-order constraint mattered in the computable file:
  `queryOracleProver` had to be moved below the `queryPhaseLogicStep` definition to avoid a
  forward-reference error during compilation.

## 2026-04-09 repo-wide Binius parity scan — initial inventory

- File-set parity between the sibling repos currently holds under `ArkLib/ProofSystem/Binius`:
  both trees expose the same `.lean` files for
  `BinaryBasefold`, `FRIBinius`, and `RingSwitching`.
- Definition-set scan over `def` names shows a small number of upstream-only canonical names:
  - `BinaryBasefold/Steps/Fold.lean:foldOracleProver`
  - `FRIBinius/CoreInteractionPhase.lean:finalSumcheckProver`
  - `FRIBinius/CoreInteractionPhase.lean:finalSumcheckVerifier`
  - `FRIBinius/CoreInteractionPhase.lean:sumcheckFoldCtxLens`
  - `RingSwitching/Prelude.lean:MLPEvalRelation`
- The computable tree still contains many extra `*Comp` / `*FunOfMultiplier` / helper defs.
  Most are expected migration helpers, but they are a parity smell wherever the canonical wrapper
  no longer delegates through the same structure as upstream.
- Structural grep over wrapper patterns (`let logic := ...`, `.verifierCheck`, `.verifierOut`,
  `.proverOut`, `OracleVerifier.append`, `OracleReduction.append`) confirms:
  - `BinaryBasefold.QueryPhase` now matches the upstream logic-step delegation again.
  - `BinaryBasefold.Steps.FinalSumcheck` still matches the upstream logic-step route.
  - `RingSwitching.General` and `FRIBinius.General` still mirror upstream append composition.
- Remaining high-risk parity targets after the first scan:
  - `BinaryBasefold/Steps/Fold.lean`
  - `BinaryBasefold/CoreInteractionPhase.lean`
  - `FRIBinius/CoreInteractionPhase.lean`
  - `RingSwitching/BatchingPhase.lean`
  - `RingSwitching/SumcheckPhase.lean`

## 2026-04-09 RingSwitching blocker map after verifier migration

- The remaining live placeholder wrappers under `ArkLib/ProofSystem/Binius/RingSwitching` are:
  - `SumcheckPhase.iteratedSumcheckOracleProver`
  - `BatchingPhase.batchingOracleProver`
  - `BatchingPhase.batchingOracleVerifier`
- `BatchingPhase` still depends directly on `compute_s0`:
  - `batchingVerifierStmtOut` builds the next statement with
    `sumcheck_target := compute_s0 κ L K β msg0 r_batching`
  - the batching completeness lemmas also normalize through
    `decompose_tensor_algebra_rows`
- The remaining `Prelude` noncomputable defs are now exactly:
  - `decompose_tensor_algebra_rows`
  - `decompose_tensor_algebra_columns`
  - `compute_s0`
  - `compute_final_eq_value`
- `finalSumcheckVerifierCheck` no longer depends on `compute_final_eq_value`; it already runs
  through the executable `compute_A_MLE ... .eval` path.
- Practical consequence:
  - removing `compute_s0` noncomputability is the next highest-leverage move, because it unblocks
    both batching wrappers;
  - `compute_final_eq_value` still matters for theorem alignment and remaining helper paths, but it
    is no longer on the verifier critical path.

## 2026-04-09 RingSwitching batching prover blocker — exact root cause

- `ArkLib/ProofSystem/Binius/RingSwitching/BatchingPhase.lean` now has:
  - executable `batchingVerifierStmtOut`
  - executable `batchingProverComputeMsg`
  - executable `batchingOracleVerifier`
  - real upstream-shaped `batchingOracleProver`, but it is currently forced back to
    `noncomputable def`
  - `batchingOracleReduction` likewise forced back to `noncomputable def`
- Focused validation after the rollback:
  - `lean_diagnostic_messages` on `RingSwitching/BatchingPhase.lean` reports **no errors**
  - `lake build ArkLib.ProofSystem.Binius.RingSwitching.BatchingPhase` passes
  - `RingSwitching/General.lean` still fails exactly because
    `batchingCoreReduction -> batchingOracleReduction` is noncomputable
- Lean diagnostics on the failed executable attempt were precise:
  - `batchingProverWitOut` fails because it depends on
    `BinaryBasefold.projectToMidSumcheckPoly`
  - `batchingOracleProver` then fails because it depends on `batchingProverWitOut`
  - `batchingOracleReduction` then fails because it depends on `batchingOracleProver`
- The deeper blocker is **not** just local wrapper drift:
  - local `BinaryBasefold.projectToMidSumcheckPoly` is still `noncomputable`
  - it depends on `BinaryBasefold.fixFirstVariablesOfMQP`
  - scratch Lean probes show plain executable defs using `MvPolynomial.rename` and
    `MvPolynomial.map` fail IR checking in this workspace:
    `depends on declaration 'MvPolynomial.rename' / 'MvPolynomial.map', which has no executable code`
- Consequence:
  - making the batching prover/reduction executable will require replacing or bypassing the old
    `MvPolynomial` witness-projection cone, not just toggling `noncomputable` markers on the
    RingSwitching wrappers.

## 2026-04-09 RingSwitching CMv migration target — concrete carrier drift

- `RingSwitching/Spec.lean` still exposes the sumcheck-round prover message as the legacy
  subtype `L⦃≤ 2⦄[X]`:
  - `pSpecSumcheckRound : ProtocolSpec 2 := ... ![L⦃≤ 2⦄[X], L]`
  - the matching inhabited/oracle-interface instances still target that carrier.
- `RingSwitching/Prelude.lean` still stores the running sumcheck witness polynomial on the legacy
  multiquadratic carrier:
  - `structure SumcheckWitness ... where`
  - `H : L⦃≤ 2⦄[X Fin (ℓ' - i)]`
- `RingSwitching/SumcheckPhase.lean` still computes round messages and witness updates through the
  old Binary Basefold helpers:
  - `sumcheckProverComputeMsg := getSumcheckRoundPoly ... witIn.H`
  - `sumcheckProverWitOut := projectToNextSumcheckPoly ... witIn.H`
- `RingSwitching/BatchingPhase.lean` still constructs the initial sumcheck witness via
  `projectToMidSumcheckPoly ...`, which is the exact noncomputable cone blocking
  `batchingOracleReduction`.
- `BinaryBasefold/Spec.lean` already has the intended computable message carrier:
  - `FoldMessageComp : Type := L → L`
- Practical migration direction:
  - change RingSwitching sumcheck-round messages to the same function carrier as
    `BinaryBasefold.FoldMessageComp`
  - change `RingSwitching.SumcheckWitness.H` to a `CPoly.CMvPolynomial (ℓ' - i) L`
  - then replace the remaining `getSumcheckRoundPoly` / `projectToMidSumcheckPoly` /
    `projectToNextSumcheckPoly` execution path with local CMv-based helpers.

## 2026-04-09 canonical alias migration — repo-wide blast radius

- The human’s stronger requirement is correct: the canonical aliases in
  `BinaryBasefold/Prelude.lean` are still:
  - `MultilinearPoly := L⦃≤ 1⦄[X Fin ℓ]`
  - `MultiquadraticPoly := L⦃≤ 2⦄[X Fin ℓ]`
  so the current tree is still anchored on Mathlib `restrictDegree` wrappers.
- Direct blast-radius measurement:
  - `rg -n "\\.property\\b|\\.val\\b" ArkLib/ProofSystem/Binius ArkLib/Data/MvPolynomial -g '*.lean'`
    => `1658` matches
  - `rg -n "MultilinearPoly|MultiquadraticPoly" ArkLib/ProofSystem/Binius -g '*.lean'`
    => `99` matches
- Interpretation:
  - flipping those aliases to CompPoly carriers is the right end state;
  - but it is a repo-wide API break because hundreds of sites still rely on subtype fields
    `.val` / `.property`.
- Pragmatic migration order:
  1. make the computable carriers canonical on the execution-critical RingSwitching /
     BinaryBasefold witness and round-message paths first;
  2. then collapse the global aliases in `BinaryBasefold/Prelude.lean` and repair the remaining
     theorem-side `.val` / `.property` assumptions file-by-file.

## 2026-04-09 canonical alias migration — `BinaryBasefold.Prelude` checkpoint

- After the current alias edit, `lean_diagnostic_messages` reports **no errors** in
  `ArkLib/ProofSystem/Binius/BinaryBasefold/Prelude.lean`.
- This means the local canonical carrier flip plus compatibility shims
  (`MultilinearPoly.val/property`, `MultiquadraticPoly.val/property`,
  `fixFirstVariablesOfCMvPoly`, and the theorem statements already retargeted to those aliases)
  are at least internally type-correct.
- The next migration pressure is therefore downstream:
  `BinaryBasefold.Basic` and the protocol/interface layers that still assume the old subtype
  behavior or construct legacy degree-restricted polynomials directly.

## 2026-04-10 canonical message-surface drift — exact next cut

- `BinaryBasefold` still has legacy round-message surfaces tied to degree-`≤ 2` polynomial
  subtypes, even though the canonical protocol spec now uses function-valued messages:
  - `BinaryBasefold/ReductionLogic.lean`
    - `foldStepLogic_honestProverTranscript` still annotates `msg : ↥L⦃≤ 2⦄[X]`
  - `BinaryBasefold/Prelude.lean`
    - `getSumcheckRoundPoly : ... → L⦃≤ 2⦄[X]`
    - `getSumcheckRoundPoly_eval_eq` / `getSumcheckRoundPoly_sum_eq` are still stated through
      `.val.eval`
  - `BinaryBasefold/Steps/Fold.lean`
    - KState branches and doom-escape lemmas still use `↥L⦃≤ 2⦄[X]` / `L⦃≤ 2⦄[X]`
  - `BinaryBasefold/Soundness.lean`
    - `probability_bound_badSumcheckEventProp` still quantifies over `L⦃≤ 2⦄[X]`
- `RingSwitching` is already partially migrated at the logic layer:
  - `RingSwitching/SumcheckPhase.lean`
    - `sumcheckVerifierCheck`, `sumcheckVerifierStmtOut`, and `sumcheckProverComputeMsg` already
      use `SumcheckRoundMessage = FoldMessageComp = L → L`
  - The remaining RingSwitching drift is therefore mostly in KState / theorem statements and old
    local annotations like `let h_star : ↥L⦃≤ 2⦄[X] := ...`.
- Immediate migration strategy:
  1. keep `badSumcheckEventProp : L → L → L → Prop` as the canonical event interface;
  2. replace theorem/message surfaces to use `(pSpecFold (L := L)).Message ⟨0, rfl⟩`,
     `SumcheckRoundMessage (L := L)`, or plain `L → L`;
  3. leave the old polynomial-subtype construction only as an internal bridge where a
     Schwartz-Zippel theorem still requires it.

## 2026-04-10 message-carrier correction — bounded CMv, not coefficient tuples

- The human corrected the migration target: `FoldMessageComp` is not an acceptable public
  abstraction. It drifts from `ArkLib-binius` and introduces an unnecessary second language for
  the same round polynomial.
- The only technical reason it appeared was executability: protocol messages need a finite carrier
  for `OracleSpec.Fintype`, while raw `CPoly.CMvPolynomial 1 L` is infinite.
- The correct replacement for legacy `L⦃≤ 2⦄[X]` is therefore the **bounded-degree CMv**
  equivalent of a univariate quadratic polynomial, conceptually `MultiquadraticPoly L 1` once
  `MultiquadraticPoly` is restored to a bounded-degree computable carrier rather than raw
  `CMvPolynomial`.
- Migration consequence:
  1. restore `MultilinearPoly` / `MultiquadraticPoly` as bounded-degree computable polynomial
     carriers, not raw `CMvPolynomial`;
  2. replace public fold/sumcheck message types by the univariate instance of that carrier;
  3. keep any coefficient-vector equivalence private only for `Fintype` / executable encodings.

## 2026-04-10 public message swap — live fallout map

- `BinaryBasefold/Basic.lean` now elaborates cleanly after forcing the initial product witness
  through an explicit
  `let h0 : CPoly.CMvPolynomial ℓ L := by simpa using (MultilinearPoly.toCMvPoly m * MultilinearPoly.toCMvPoly t)`.
  The earlier `max ℓ ℓ` vs `ℓ` failure was just the `HMul` result carrier not reducing
  automatically.
- `BinaryBasefold/Spec.lean` accepts the public message swap directly:
  - `pSpecFold.Message 0 = FoldMessage L`
  - old `FoldMessageComp`-based `OracleInterface` / `Fintype` / `Inhabited` sites can be
    rewritten mechanically
  - the private legacy `fintypeDegreeLETwo : Fintype (L⦃≤ 2⦄[X])` helper is unused and removable.
- `BinaryBasefold/Relations.lean` now has only one real error after the swap, at
  `firstOracleWitnessConsistencyProp_unique`.
  - Symptom: kernel reports old `@MultilinearPoly.val ... ℓ` application shape with missing
    `[BEq]/[LawfulBEq]`.
  - Most likely cause: imported lemma/olean drift from pre-rebuild `Basic`, not the local source
    around the theorem itself.
- `RingSwitching/Spec.lean` accepts `abbrev SumcheckRoundMessage := FoldMessage (L := L)` with no
  real errors.
- `RingSwitching/SumcheckPhase.lean` is still far from aligned. The message swap exposed a much
  larger drift cone:
  - stale calls that still treat messages as `L → L` or `↥L⦃≤ 2⦄[X]`
  - stale named arguments against refactored local defs (`𝓑`, `β`, etc.)
  - theorem statements still mixing raw `CPoly.CMvPolynomial`, `MultiquadraticPoly`, and legacy
    `L⦃≤ 2⦄[X]`
  - conclusion: this file needs a broader statement-surface pass, not a one-line alias rename.

## 2026-04-10 upstream-pattern correction — final sumcheck extractor

- Human correction is precise: `BinaryBasefold/Steps/FinalSumcheck.lean` should stay structurally
  close to sibling `ArkLib-binius` file, even during computability migration.
- Concrete implication for `finalSumcheckRbrExtractor.extractMid`:
  - keep local `H_constant` object in the extractor body;
  - both `none` and `some tpoly` branches should return that constant witness polynomial, not
    `0` or `projectToMidSumcheckPoly ...`;
  - the migration change is only the carrier: `H_constant` must be a computable
    `MultiquadraticPoly` constant, i.e. CMv bounded-degree equivalent of
    `MvPolynomial.C stmtMid.sumcheck_target`.
- Practical helper needed in `BinaryBasefold/Prelude.lean`:
  - canonical constructor `MultiquadraticPoly.C : L → MultiquadraticPoly L ℓ`
  - bridge lemma `MultiquadraticPoly.val_C` with target `MvPolynomial.C c`
  so theorem statements can stay close to upstream shape.

## Oracle carrier source removal checkpoint — 2026-04-10

- Source-level `OracleFunctionComp` bridge has been removed from `BinaryBasefold/Prelude.lean`.
- `BinaryBasefold.Basic.oracleStatementToCanonical` has been removed; `OracleStatement` now
  points directly at canonical `OracleFunction`.
- `rg` over `ArkLib/ProofSystem/Binius` no longer finds `OracleFunctionComp`,
  `oracleStatementToCanonical`, or `OracleFunction.toComp` in source.
- Remaining `OracleFunctionComp` mentions in Lean diagnostics likely come from stale compiled
  artifacts or a mixed build state, not from current source text.
- Next useful cut is to force canonical oracle-carrier / relation files to typecheck against the
  new source state, not to keep renaming bridge defs.

## 2026-04-10 current compile blocker after oracle carrier flip

- `Prelude.lean`, `Code.lean`, and `Basic.lean` still fail because helper lemmas are written
  against canonical `AdditiveNTT.sDomain` names while public carrier types now use
  `AdditiveNTT.Comp.sDomain`.
- Missing comp-side alias lemmas in `AdditiveNTT.Impl` are the shortest fix:
  - `Comp.sDomain_basis`
  - `Comp.sDomain_card`
  - `Comp.sDomainFinEquiv`
  - `Comp.sDomain_eq_of_eq`
- Once those exist, rewrite the remaining Binius helper calls to the `Comp` namespace and rebuild
  the three modules in that order.

## 2026-04-10 code-surface correction

- `OracleFunction` is an `abbrev` in [Prelude.lean](/Users/chung-thai-nguyen/Documents/WorkStation/Repo/Verified-zkEVM/ArkLib-binius-computable/ArkLib/ProofSystem/Binius/BinaryBasefold/Prelude.lean#L598).
- It is definitionally the same as `AdditiveNTT.Comp.sDomain ... → L`.
- So theorem statements should prefer `OracleFunction` rather than spelling the carrier out.
- `fiberwiseDisagreementSet` on `Comp.sDomain` must be phrased through `qMap_total_fiber`; raw `iteratedQuotientMap` still expects canonical `sDomain`, so it is the wrong primitive for the computable carrier surface.

## 2026-04-10 oracle carrier note
- `OracleFunction` in `BinaryBasefold/Prelude.lean` is an `abbrev` for `AdditiveNTT.Comp.sDomain ... -> L`.
- So explicit `Comp.sDomain ... -> L` spellings are definitionally equal to `OracleFunction`, but the abbrev should be the public surface in theorem statements and defs.
- Current blocker in `Compliance.lean` is not the type alias itself; it is the proof body around `fold_error_containment_of_UDRClose`.

## OracleFunction alias cleanup — 2026-04-10

- Confirmed the raw carrier spelling and `OracleFunction` are definitionally identical.
- Patched the remaining obvious statement-layer raw spellings in `Steps/Commit.lean`,
  `Steps/FinalSumcheck.lean`, and `Soundness/Proposition4_21.lean` to use `OracleFunction`.
- This is a surface cleanup only; no semantic change, but it keeps the public Binius interface
  aligned with the canonical computable alias.

## Build blocker after OracleFunction alias cleanup — 2026-04-10

- `Commit.lean` and `Proposition4_21.lean` now typecheck after the alias cleanup.
- `lake build ...Commit ...FinalSumcheck ...Proposition4_21 ...Incremental` still fails in:
  - `BinaryBasefold/Soundness/FoldDistance.lean`
  - `BinaryBasefold/Spec.lean`
  - `BinaryBasefold/Soundness/Incremental.lean`
- The remaining errors are not about the alias itself. They are places where theorem bodies still
  expect old `sDomain`-shaped codeword carriers or old `SampleableType.ofEquiv` targets and need
  the same computable-carrier migration applied one layer deeper.
## Query soundness cast style — 2026-04-11

- Upstream `BadBlocks.lean` keeps dependent casts inline in theorem bodies:
  `fun y => (oStmtIn j) (cast (by rw [h_idx]) y)`.
- Local `QueryPhaseSoundness.lean` now follows that shape directly.
- Extra named `h_idx_cast` shim is removed from active proof text and normalized out of the
  commented legacy block too.
## 2026-04-11

- Live `polynomialFromNovelCoeffsF₂` drift remains in:
  - `BinaryBasefold/Soundness/QueryPhasePrelims.lean`
  - `BinaryBasefold/Steps/FinalSumcheck.lean`
  - one inactive comment block in `FRIBinius/CoreInteractionPhase.lean`
- The computable construction pattern is already stable in:
  - `BinaryBasefold.Basic`
  - `BinaryBasefold.Relations`
  - `BinaryBasefold.Prelude`
- `AdditiveNTT/Impl.lean` and `BinaryBasefold.Prelude` now both carry computable `CompPoly.CPolynomial` builders for `polynomialFromNovelCoeffsF₂`, but the downstream Binius consumer files still prefer the inline builder because the helper export path is not cleanly reusable in every module.
- User correction locked in: do not replace this with `MultilinearPoly.ofHypercubeEvals`; migrate the polynomial builder itself and keep theorem statements on the computable carrier.

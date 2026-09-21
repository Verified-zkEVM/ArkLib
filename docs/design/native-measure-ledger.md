# Native-measure conversion ledger

The merged Lean 4.34 upgrade ([#903](https://github.com/Verified-zkEVM/ArkLib/pull/903))
converted consumers of VCVio's retiring scalar probability API
(`Pr[… | …]`, `probEvent`, `probOutput`, `probFailure`, `evalSPMF`/`𝒮[…]`, `NeverFail`,
and the PMF-based `IsUniformSpec`/`IsProbabilitySpec`) to the native measure API
`𝒟[…]` and `Pr{…}[…]`. Both stages require `./scripts/validate.sh --axioms` with
the existing zero-warning gate and axiom baseline unchanged.

The follow-up retirement campaign in [issue #904](https://github.com/Verified-zkEVM/ArkLib/issues/904)
converts ArkLib's independent Mathlib PMF toolkit and its coding-theory/protocol consumers.
It removes the old notation module and ToVCVio compatibility imports. The mandatory
`lake exe retiredsweep --require-empty` gate checks direct retired references in declaration types
and bodies; it cannot be weakened by a baseline.

## Ground rules

- Statements use `Pr{…}[…]` or `𝒟[…] s`. Losslessness is `IsProbabilityMeasure 𝒟[…]` or, for a
  generic monad, the trivially true event `Pr{let _ ← mx}[True] = 1`; `NeverFail` hypotheses on
  `ProbComp` values are vacuous and are deleted rather than translated.
- Invariants that hold on every execution are operational `support` statements; the probability
  interpretation enters only through `prEvent_eq_one_of_forall_mem_support` and its `OptionT`
  forms.
- Prefer public normalization equations across `simulateQ` / `OptionT` / `StateT` boundaries.
  Definitional normalization remains valid; reusable missing probability bounds belong upstream.
- Protocol statements do not acquire artificial discrete measurable-space assumptions. Proof-local
  discrete spaces are used where the existing discrete sampler semantics require them, including
  sampler transport in `OracleReduction/Cast.lean`.
- Import generic VCVio laws directly from their upstream owners. The former `ArkLib/ToVCVio/`
  compatibility tree is removed; do not recreate it or add replacement aliases.

## Admissible regression reasons

| Code | Reason |
|---|---|
| R1 | Subprobability honesty: a conditional bound reads `Pr{¬p}` where the scalar API wrote `1 - Pr[p]`; recovering the latter needs `prEvent_add_prEvent_not` plus losslessness. |
| R2 | A lower bound through an `OptionT` prefix needs the prefix's losslessness stated explicitly. |
| R3 | A support-versus-almost-everywhere bridge on a monad that is not `OracleComp`. |
| R4 | A proof-local `let : MeasurableSpace α := ⊤` to apply an `evalDist` lemma inside a `Pr{}` proof. |

These categories describe the broader retirement audit; they do not replace the build, warning,
regression-test, or axiom checks for this upgrade.

## Upstream prerequisites

Developed on VCVio branch `codex/arklib-native-prereqs` and landed on VCVio `main` through the
integration PR [#771](https://github.com/Verified-zkEVM/VCVio/pull/771) (which also carries the
content of #758/#763/#764); ArkLib pins `210d73fd85d4f1ab99e5a707a78238e3a0dfb8d6`.

| Family | Upstream home | Contents | Retires in ArkLib |
|---|---|---|---|
| U1 event algebra | `VCVio/EvalDist/ProbabilityBounds.lean` | `prEvent_or_le`, `prEvent_exists_le`, `prEvent_exists_finset_le`, `prEvent_exists_le_card_mul`, `prEvent_eq_prEvent_and_add_prEvent_and_not`, `prEvent_le_prEvent_add_prEvent_and_not`, `prEvent_and_le_left/right`; `prEvent_le_one`, `evalDist_apply_le_one` (simp) | `Probability.Pr_or_le`, `Pr_exists_le`, `Pr_add_split_by_complement`, `prob_le_one`, `Pr_le_Pr_of_implies`, `Pr_congr`, `prob_eq_zero_of_forall_not` |
| U2 support ↔ probability | `VCVio/OracleComp/EvalDist/Measure.lean`, `VCVio/EvalDist/Monad/Option.lean` | `prEvent_true_eq_one`, `prEvent_eq_one_of_forall_mem_support`, `prEvent_eq_zero_of_forall_mem_support`, `prEvent_eq_one_iff`, `prEvent_eq_zero_iff`, `prEvent_pos_iff`; `OptionT.prEvent_mk`, `OptionT.prEvent_mk_eq_one_iff`, `OptionT.prEvent_mk_eq_zero_iff`, `OptionT.prEvent_mk_pos_iff`, `OptionT.isProbabilityMeasure_mk_iff` | `probEvent_eq_one_iff`, `probEvent_eq_zero_iff`, `probEvent_pos_iff`, `one_le_probEvent_iff`, `OptionT.probFailure_eq`, `probFailure_eq_zero`, `probOutput_eq_zero_of_not_mem_support` |
| U3 conditioning | `VCVio/EvalDist/ProbabilityBounds.lean` | `prEvent_bind_le_of_forall_le`, `le_prEvent_bind_of_forall_le`, `prEvent_bind_le_prEvent_add_mul_prEvent_not`, `prEvent_bind_le_prEvent_of_forall_eq_zero`, `prEvent_bind_le_prEvent_add`, and `_of_support` forms through `MonadAttach` (`bind_eq_attach_bind`, `prEvent_true_attach`) | `probEvent_bind_le_of_forall_le`, `mul_le_probEvent_bind`, `probEvent_bind_le_probEvent(_add/_convex)`, `Pr_seq_le_of_forall_le`, `probEvent_bind_of_const` |
| U4 OptionT sequencing | `VCVio/EvalDist/Monad/Option.lean`, `VCVio/OracleComp/SimSemantics/StateT/Measure.lean` | `OptionT.mem_support_of_mem_support_lift`, `OptionT.mk_bind_eq_lift_bind`, `OptionT.prEvent_mk_bind_eq_one_of_support`, `OptionT.prEvent_mk_bind_le_of_forall_le`, `OptionT.prEvent_mk_simulateQ_run'_eq_one_of_support` | `ArkLib/ToVCVio/EvalDist/Instances/OptionT.lean`, `OptionT.probEvent_eq_one_of_simulateQ_support(_bind)`, the `change none ∈ support (StateT.run' (simulateQ …))` idiom, the `erw` chains in `Sumcheck/Spec/SingleRound.lean` |
| U5 normal forms | `VCVio/OracleComp/SimSemantics/OptionT/Basic.lean`, `VCVio/OracleComp/QueryTracking/LoggingOracle/Core.lean` | `simulateQ_optionT_pure`, `loggingOracle.map_fst_run_simulateQ`, `loggingOracle.run_simulateQ_optionT_pure` | `ArkLib/ToVCVio/OracleComp/{SimSemantics/SimulateQ,QueryTracking/LoggingOracle}.lean` |
| U6 uniform counting | `VCVio/OracleComp/Constructions/SampleableType/NativeMeasure.lean` | `prEvent_uniformSample_eq_one_iff/_eq_zero_iff/_pos_iff/_eq_singleton`, `prEvent_uniformSample_lt_div_iff/_le_div_iff/_eq_div_iff`, `div_lt/le_prEvent_uniformSample_iff`, `prEvent_uniformSample_eq_ofReal`, `prEvent_uniformSample_comp_of_bijective/_equiv/_pair_of_bijective/_prod/_fst/_finSnoc`; `prEvent_congr_of_evalDist_eq`, `prEvent_const_of_lossless`, `prEvent_const_of_not` | `prob_uniform_eq_card_filter_div_card` and boilerplate B1–B4, `Pr_uniform_equiv`, `Pr_map_eq`, `prob_split_uniform_sampling_of_(equiv_)prod`, `prob_split_last_uniform_sampling_of_finFun`, `prob_fin_succ_split`, `prob_marginalization_first_of_prod`, `prob_uniform_eq_ofReal`, `prob_uniform_singleton_finFun_eq`, the RbrGame `$ᵗ`↔`$ᵖ` bridge |
| U7 samplers | `VCVio/OracleComp/Constructions/SampleableType/Basic.lean`, `NativeMeasure.lean` | `SampleableType.subtype`, `SampleableType.finsetCoe` (noncomputable defs), `evalDist_uniformSample_inst_irrel`, `prEvent_uniformSample_inst_irrel` | `OracleReduction/Cast.lean` `𝒮[]` transport; enables `$ᵗ ↥U` for Finset/subtype sample spaces |

Regression test: `VCVioTest/EvalDist/EventBounds.lean` (native import guard, an `OptionT ProbComp`
game simulated from a sampled state, uniform counting thresholds, union bounds, conditioning).

The earlier plan listed structural uniform instances (U8) and transformer losslessness glue
(U9). These are not unresolved blockers for the current conversion: ArkLib uses native
`IsUniformMeasureSpec` instances where needed, and the pinned dependency supplies
`OptionT.isProbabilityMeasure_mk_iff` and the sequencing lemmas above.
The final proof-length audit identified dependent-product sampling and conditional uniform-event
conveniences. [VCVio #770](https://github.com/Verified-zkEVM/VCVio/pull/770) supplies them;
ArkLib pins VCVio `main` at `210d73fd85d4f1ab99e5a707a78238e3a0dfb8d6`, the squash merge of
[VCVio #771](https://github.com/Verified-zkEVM/VCVio/pull/771). That merge consolidated the whole
native-measure prerequisite stack onto `main`: #769 and #770, which had previously merged only into
the prerequisites branch, together with the `OracleSpec.{u, v}` generalizations and the AE
bind-event law found during this review. The prerequisite work was developed and validated on that
branch at `93cee8a1f25135436d96cab6bd89a0e5a4cf7660`, tree-identical to the validated #770 head
`c2ca892ec693bca9403a98111cc6f8f738b8c029`, before consolidation.

## Checkpoints

### Phase 1: Lean 4.34 and VCVio scalar probabilities (#903)

The first phase is the merge commit
`fa14552d40e793f2ea26e65c440306aae0c08a26`. Its actual first parent is
`68726031f01e0b79759dce718fce77ac81fb317a` (#906); using the earlier PR review base would
incorrectly charge already-merged work to #903. The comparison contains 179 changed files in all
and 174 changed Lean files. The source counts below cover every changed Lean file, including
comments and signatures, rather than only changed diff lines or proof bodies.

| Family | Changed files | Lines before | After | Δ | Primary kind of change |
|---|---:|---:|---:|---:|---|
| Commitments | 24 | 10857 | 10869 | +12 | VCVio scalar probability conversion, plus bump fixes |
| Coding theory | 54 | 41640 | 41650 | +10 | Lean/Mathlib compatibility; independent PMF surface deferred |
| Other algebra and data | 26 | 11786 | 11790 | +4 | Lean/Mathlib compatibility |
| Probability infrastructure | 2 | 899 | 899 | 0 | VCVio sampler/evaluation API conversion |
| Interaction | 2 | 385 | 386 | +1 | Native measure conversion |
| Oracle reductions | 21 | 12915 | 12986 | +71 | Native security games and sequential composition |
| Proof systems | 24 | 13538 | 13301 | -237 | Native protocol consumers plus bump fixes |
| ToCompPoly compatibility | 2 | 489 | 353 | -136 | Declarations absorbed upstream |
| ToMathlib compatibility | 7 | 1834 | 1827 | -7 | Lean/Mathlib compatibility |
| ToVCVio compatibility | 3 | 140 | 55 | -85 | Helpers moved upstream; import shells retained in this phase |
| Tests | 7 | 906 | 923 | +17 | Native probability acceptance and state-handoff regressions |
| Scripts | 2 | 175 | 399 | +224 | 225-line retirement inventory; linter adaptation -1 |
| **Total** | **174** | **95564** | **95438** | **-126** | |

At family granularity, the probability-facing paths (commitments, probability infrastructure,
interaction, oracle reductions, proof systems, ToVCVio, and their tests) total 83 files and
39640 → 39419 lines (-221). Compatibility-dominated coding/algebra/ToCompPoly/ToMathlib paths
total 89 files and 55749 → 55620 lines (-129). The scripts add 224 lines, almost entirely the
new inventory tool. These categories are an accounting aid: the mixed families also contain
ordinary Lean 4.34 repairs, so their raw source delta is not evidence that probability proofs
became shorter.

#### Phase 1 proof-size review

Proof-body counts use the same physical-line method as the phase-2 review below: include the line
containing the declaration's final `:= by`, preserve blank and comment lines inside the proof, and
stop before the next top-level docstring or declaration. Statement-only lines and trailing blank
lines are excluded; renamed declarations are matched manually. The following are the material
probability-facing increases at #903 and their size now. Every row was resolved by an ArkLib
call-site refactor that uses existing pinned APIs. The one exception is `run_preserves_measure`,
which needed the generic AE bind-event law that VCVio #771 added. No other new upstream law was
needed.

This proof-only convention differs from a coarse declaration-span count that stops only at the
next declaration and therefore charges the next theorem's docstring and separators to the prior
proof. For example, the latter reports `run_preserves_measure` as 16 → 26, while the proof-only
count is 13 → 23; the regression is +10 under either convention. The phase-1 and phase-2 tables
both use the proof-only count.

| File / declaration | Before #903 | #903 | Now | Accounting |
|---|---:|---:|---:|---|
| `OracleReduction/Security/RoundByRound.rbrKnowledgeSoundnessOneShot_implies_rbrKnowledgeSoundness` | 31 | 67 | 31 | Resolved: bind reassociation once, then goal-inferred `prEvent_mono`. |
| `OracleReduction/Composition/Sequential/Append/Completeness.completeness_iff_of_pure_verifier` | 14 | 32 | 14 | Resolved: `OptionT.lift` normal form, then `OptionT.prEvent_lift`/`prEvent_map` in one `simp only`. |
| `OracleReduction/Composition/Sequential/Append/Completeness.append_completeness_of_prover_factorization` | 32 | 46 | 28 | Resolved: goal-inferred `mul_le_prEvent_bind_of_forall`; the `q₁.2 → stage 2 → q₂.2` state handoff is unchanged. |
| `OracleReduction/Composition/Sequential/GuardedCompleteness.append_completeness_of_guarded_prover_factorization` | 27 | 41 | 23 | Resolved: same call-site refactor. |
| `OracleReduction/Composition/Sequential/GuardedCompleteness.prEvent_guarded_map` | 6 | 20 | 4 | Resolved: `OptionT.prEvent_bind_guard`. |
| `OracleReduction/Security/RbrGame.prEvent_optionT_simulateQ_addLift_getChallenge_first_bind_le_convex` | 22 | 33 | 29 | **R1** (+5): `prEvent_bind_le_prEvent_add_mul_prEvent_not` is the honest subprobability form and leaves `Pr{¬p}`; `1 - Pr{p}` is recovered from `prEvent_add_prEvent_not` and uniform-sampler losslessness under a proof-local discrete space (R4). **R2** (+2): a `change` exposes the `OptionT.lift` prefix so `OptionT.prEvent_lift` applies. |
| `Interaction/Oracle/Composition.run_preserves_measure` | 13 | 23 | 13 | Resolved by the upstream generic AE bind-event law (VCVio #771). |
| `ArkLibTest/.../SharedStateCounterexample.first_perfectCompleteness` | 5 | 15 | 4 | Resolved: native lift/map simplification. |
| `ArkLibTest/.../SharedStateCounterexample.second_perfectCompleteness` | 5 | 14 | 4 | Resolved: same. |
| `OracleReduction/Composition/Sequential/GuardedCompleteness.completeness_iff_of_guarded_verifier` | 24 | 32 | 24 | Resolved: one normal form instead of duplicated directions. |
| `Commitments/Functional/KZG/Binding.binding_game_ext_eq_binding_game` | 146 | 153 | 146 | Resolved: reverse `prEvent_map` on the projected condition, then `OptionT.ext` on the game; no separate program-equality statement. |
| `OracleReduction/Composition/Sequential/Append/Completeness.completeness_of_pure_states` | 9 | 15 | 6 | Resolved: goal-inferred bind lower bound. |
| `OracleReduction/Composition/Sequential/GuardedCompleteness.completeness_of_guarded_states` | 9 | 15 | 6 | Resolved: same. |
| `OracleReduction/Security/RbrGame.prEvent_simulateQ_addLift_getChallenge_bind_le` | 18 | 24 | 9 | Resolved: inferred arguments to bind-event monotonicity. |
| `OracleReduction/Security/RbrGame.prEvent_optionT_simulateQ_addLift_prefix_getChallenge_bind_le` | 46 | 49 | 13 | Resolved. |
| `OracleReduction/Security/RbrGame.prEvent_optionT_simulateQ_addLift_getChallenge_bind_some_le` | 26 | 28 | 13 | Resolved. |
| `OracleReduction/Security/Implications.rbrKnowledgeSoundness_implies_rbrSoundness` | 128 | 133 | 98 | Resolved: reassociation and state unfolding performed once. |

Counts are proof-body lines from the final `:= by` line, as defined above. The Lean 4.34
repairs that #903 made outside probability proofs are also back at or below their pre-#903 size:
`AffineGenerator.exists_line_bound` (71 → 75 → 69), `Bivariate.degreeY_le_degreeY_sub_degreeY`
(1 → 5 → 2; the remaining line is the `simp` call that replaces `grind`, which no longer closes the
goal), `PolishchukSpielman/Degrees.ps_degX_bound` (restored with `grind +qlia [natDegreeY,
Polynomial.natDegree_mul]`), `BCIKS20/ListDecoding/Extraction.pg_sum_natDegreeY_Rset_le_natDegreeY_Q`,
`Errors.mcaError_le_epsCa_of_pos_of_two_mul_lt_dist`, and
`Subfield/Algebra.fold_density_le_eps_ca_of_not_joint_proximity` (23 → 26 → 12). The test
`ArkLibTest/.../Completeness.rejecting_not_perfect` is back to 5 lines. Smaller probability-facing
rows (KZG `binding`, `t_sdh_game_eq`, FunctionBinding, `Security/Basic.completeness_relOut_mono`,
`Functional/Basic`, `KZG/Correctness`, `TerminalMeasure`, `TranscriptTree`, the Ajtai binding
reduction, and the sequential-composition tests) are at or below their pre-#903 size.

Checkpoint A6 is done. `ProofSystem/Sumcheck/Spec/SingleRound.reduction_perfectCompleteness`
now applies `Reduction.perfectCompleteness_of_run_support`. A local closed form for
`runToRound (Fin.last 2)` is built from `Prover.runToRound_succ`, `Prover.processRound_of_dir_eq_P_to_V`,
`Prover.processRound_of_dir_eq_V_to_P` and `FullTranscript.mk2_eq_snoc_snoc`, and the verifier guard
comes from the input relation. The proof body is 26 lines, including that closed form, down from
182 with 35 `erw` calls. It adds no assumption, helper declaration, admission or import, and it
removes the `backward.isDefEq.respectTransparency false` override that the old proof needed.

### Phase 2: independent PMF retirement (#904 follow-up)

The conversion starts from `fa14552d40e793f2ea26e65c440306aae0c08a26` (#903) and includes
`main` through `8b03d40a56ec827d223b78ccca0ce164a9231f6c` (#857 and #877).
The size comparison isolates migration files against #903; the unrelated additions on `main`
are not counted as migration changes.
Counts below cover complete changed Lean files in each family, including comments and signatures;
they are not counts of changed proof lines. Deleted files count as zero after conversion.

| Family | Changed files | Lines before | After | Δ |
|---|---:|---:|---:|---:|
| Probability toolkit | 4 | 1364 | 550 | -814 |
| Proximity generators | 6 | 2012 | 2035 | +23 |
| Other coding theory and Schwartz–Zippel | 49 | 32377 | 32278 | -99 |
| Protocol consumers | 12 | 7728 | 7703 | -25 |
| Oracle reductions | 7 | 5020 | 5007 | -13 |
| Serde and KZG | 4 | 1159 | 1163 | +4 |
| Deleted ToVCVio Lean modules | 7 | 200 | 0 | -200 |

The compatibility tree also loses its 64-line README. The root import file is regenerated.
The retirement inventory shrank from 186 declarations to zero across the final 499-module root.
No retired-probability baseline is introduced, and no warning exclusions are added.

#### Phase 2 proof-size review

This is a complete sweep of every theorem and lemma whose proof body is longer than at merge base
`8b03d40a56ec827d223b78ccca0ce164a9231f6c`. Proof bodies are counted from the final `:= by`
line. The sweep started with 42 grown rows. Two are now at or below their merge-base size:
`BCHKS25.rs_Lambda_le_card_of_epsCa_lt` (431 → 424), whose bounds are now stated on
`Pr{let z ← $ᵗ F}[Pevent z]` through `prEvent_uniformSample_eq_ofReal`; and the RbrGame convex
bound, covered in phase 1. `DG25/MainResults.interleaved_affine_gaps_imply_tensor_gaps` drops from
+9 to +2 because `Fin.snocEquiv` supplies the bijectivity proof.

None of the 40 remaining rows is a probability argument that got longer. Each grows by one to
three lines, and they have three causes, none of which is R1–R4.

**D1: instance search after the native sampler import (26 rows).** Converting `$ᵖ` to `$ᵗ` makes
these files import `VCVio.OracleComp.OracleSpec`. Its instances
`DecidableEq spec.Domain`/`DecidableEq (spec.Range t)` (`OracleSpec.lean:77–79`) combine with the
reducible `OracleSpec.ofFn` instance (`OracleSpec.lean:91`) to match every `DecidableEq α` goal.
This sends synthesis around the cycle `DecidableEq F → (ofFn ?).DecidableEq → DecidableEq F`
before it reaches `Classical.propDecidable`. The minimal reproducer
`import Mathlib.Algebra.Field.Basic` plus `example [Field F] (x y : F) : Decidable (x = y) := by
classical; infer_instance` succeeds. Adding `import VCVio.OracleComp.OracleSpec` makes it fail to
synthesize. The affected proofs therefore use explicit `let _ : DecidableEq α := Classical.decEq α`,
and in some cases explicit `@` instance arguments. The two `AffineSpaces/Basic` rows use `change`
in place of `simpa` because `simpa` reports a mismatch between types that print identically; a
hidden `Decidable` instance difference is inferred, not verified. Replacing the lets with `classical` was tried in all nine
multi-let files, and every one fails with a 20000-heartbeat typeclass timeout. The rows are:
`Frs/LineDecoding.exists_seed_pairwise_distinct_affine_lines` (+3),
`SchwartzZippelCounting.prob_eval_zero_le_div` (+3),
`BCIKS20/AffineSpaces/Basic.all_affine_elements_close` (+3) and
`average_proximity_implies_proximity_of_linear_subspace` (+2),
`Entropy/Counting.rsCode_disjoint_supported_of_small`, `JohnsonLower.rs_monomial_agreement_card_le_two_mul`,
`Powers/Incidence.powers_coefficients_eq_of_agree_on_distinct_seeds`,
`Subfield/Algebra.subfield_ca_interpolant_unique`,
`UniqueDecoding/Internal.rs_exists_oversized_bivariate_ab(_of_dimension)`,
`Errors.exists_forall_notMem_of_card_le`, `LineDecoding.affine_collision_injective`,
`LineDecoding.exists_outside_finite_union_submodules`,
`PolynomialGenerator.isMCAGenerator_of_isPolynomialGeneratorOf` (+2 each), and
`Frs.frs_mcaError_le_proof`, `JohnsonLower.is_binary_linearized_sub`,
`JohnsonLower.mv_polynomial_fin_exists_eval_ne_zero_of_total_degree_lt_card`,
`Subfield.subfield_ca_exists_good_center_nat`, `Subfield/Algebra.subfield_ca_generator_adjoin_eq_top`,
`GrandChallenges.lambda_eq_of_floor_eq`, `KKH26.exists_neg_transversal`,
`ReedSolomon.rs_codimension_one_list_size`, `BCIKS20/AffineSpaces.exists_large_of_finset_cover(')`,
`PolynomialGenerator.isMCAGenerator_of_isPolynomialGeneratorOfFull`, `Stir/Combine.master_lemma`
(+1 each). `exists_large_of_finset_cover'` shows the effect directly: it already begins with
`classical` and still needs the explicit `Classical.decEq α`.

**D2: statement and elaboration shape (9 rows, +1 or +2 each).**
- Two statements are generalized from `Fintype` to `Finite`, so the proof builds its own `Fintype`:
  `Entropy/Counting.epsCa_eq_one_of_all_folds_close_not_joint` and the private
  `GCXK25.linear_mca_relevant_pairs_card_le`.
- `Folding.dist_from_code_bound_of_correlated_agreement` replaces an `aesop` call that no longer
  closes the goal under the `Finite` hypothesis.
- `DG25/ReedSolomon.ReedSolomon_ProximityGapAffineLines_UniqueDecoding` uses
  `simpa only [bind_pure_comp, …]` because native `Pr{…}` elaborates to `do …; pure …` while the
  hypothesis is in `<$>` form.
- `InformationSetLowerBound.linear_mcaError_ge_information_set` adds `← ENNReal.coe_natCast` because
  the native counting lemma returns `ℝ≥0∞` casts, not `ℝ≥0` casts.
- `DG25/MainResults.interleaved_affine_gaps_imply_tensor_gaps` (+2) states its `Fin 1 → F`
  transport explicitly.
- `AffineSpaces/Basic.prob_uniform_shift_invariant`,
  `PolynomialGenerator.isMCAGenerator_univariatePowersGeneratorOn` and
  `ToyProblem/SoundnessBounds.exists_winningSetFor_ncard_ge_of_lambda_lt_card` grow only because of
  line wrapping around longer native lemma names or a new sampler binder.

**D3: retirement-gate explicit terms (5 rows, +1 each).** `Verifier.id_rbrSoundness` keeps
`intro …; exact Fin.elim0 i.1` rather than `simp [Verifier.id]`, and the four
`OracleComp.support_nonempty` applications (`TranscriptTree/Basic.not_isAccepting_of_no_outputs`,
`support_init_nonempty_of_prob_one`, `not_accepting_of_failure`, and
`CoordinateWiseSpecialSoundness/Composition.mem_of_pure_accepting`) pass
`OracleSpec.IsUniformMeasureSpec.inhabited` explicitly. The shorter forms elaborate, but the
default instance paths go through the retired `OracleSpec.IsUniformSpec.inhabited`,
`IsUniformSpec.toIsProbabilitySpec`, `PMF`/`SPMF` and `probOutput`, and `retiredsweep` rejects
them (verified). These rows go away when VCVio removes those instances under #532.

D1 has a single upstream fix: VCVio should stop `OracleSpec`'s `DecidableEq` instances from
matching arbitrary types, for example by lowering their priority or keying them on a
non-reducible head. After ArkLib pins that fix, the 26 D1 proofs can go back to `classical`. That
change belongs in a separate VCVio PR and is not part of this one.

The earlier phase-2 generator audit still holds:

| File / declaration | Before | After | Accounting |
|---|---:|---:|---|
| `ProximityGenerator/Basic.poly_gen_is_zero_evading` | 21 | 19 | Native event equality removes the PMF-map step. |
| `TensorGenerator.isMCAGenerator_tensorGenerator_of_moduleInterleavedCode` | 72 | 70 | Upstream conditional product bound. |
| `TensorGenerator.isMCAGenerator_tensorGenerator` | 51 | 47 | Upstream product and finite union bounds. |
| `PolynomialGenerator.isMCAGenerator_tensorGeneratorPi` | 51 | 51 | Native zero-event proof offsets explicit tail sampler setup. |
| `PolynomialGenerator.isMCAGenerator_tensorGeneratorPi_tight` | 57 | 57 | Same dependent-product setup and zero-event argument. |
| `ToyProblem/SoundnessBounds.exists_dotProduct_image_card_le` | 42 | 42 | Native mathematical corollary supplies the operational witness. |
| `ToyProblem/SoundnessBounds.exists_affine_image_card_le` | 39 | 39 | Native cardinality threshold avoids expanded ENNReal arithmetic. |

The mathematical collision-image theorem now takes a probability measure and an explicit
countable full-mass carrier. Its witness still has positive singleton mass. ToyProblem converts
that fact back to operational support before extracting sampled parameters; replacing it with
membership in an arbitrary full-measure set would weaken the result. The theorem remains
universe-polymorphic.

Validation also tests rejection of retired notation, retired declaration types and bodies,
private declarations, and attempts to bypass the strict gate with a covering baseline. Inert
strings and comments remain allowed. Existing admissions are retained, not discharged by this
migration; the axiom regression baseline must remain unchanged.

### Closure scope and scanner boundary

Issue #904 covers both phases: #903's VCVio scalar conversion and the follow-up retirement of
ArkLib's independent PMF surface. Its integration condition is met: the prerequisite stack landed
on VCVio `main` in [#771](https://github.com/Verified-zkEVM/VCVio/pull/771), and ArkLib pins that
main commit, `210d73fd85d4f1ab99e5a707a78238e3a0dfb8d6`. All phase-1 probability proofs are at or
below their pre-#903 size or carry an R1/R2/R4 reason, and checkpoint A6 is done. What remains
against #904's literal acceptance rule are the 40 phase-2 rows above: 26 grew because of the D1
instance-search defect in VCVio, 9 because of D2 statement or elaboration changes, and 5 because
of D3 explicit terms that keep retired VCVio instances out of the proofs. None of them
is R1–R4. Whether #904 closes with these rows documented, or stays open until the VCVio `OracleSpec`
instance fix is pinned and D1 is reverted, is a decision for the maintainers.

VCVio issue #532 has a broader repository-wide retirement scope. Landing the ArkLib prerequisite
slice and closing #904 will not close #532; VCVio must account for its other scalar/PMF consumers
and its own final retirement gates separately.

The scanner's claim is deliberately direct. `retiredsweep` imports the `ArkLib` root and reports
retired constants that occur directly in reportable `ArkLib.*` declaration types or bodies. It
does not report transitive retired dependencies, `ArkLibTest` declarations under its default root,
command-only references that elaborate no declaration, or compiler/macro-scoped auxiliary
declarations excluded by `isReportable`. The build-time syntax plugin independently rejects the
four retired notation token forms (`$ᵖ`, `Pr_{`, `Pr[`, and `𝒮[`), including locally defined
macros, but it is not a general identifier scan. The empty environment inventory, syntax fixtures,
source inspection, build, tests, warning gate, and axiom gate therefore establish complementary
claims; no one scanner is described as a complete transitive/source proof.

## Upstream gaps found during conversion

Native Boolean implication and union bounds, event monotonicity on support, a conditional product
lower bound, and the support-indexed additive bind bound are supplied by
[VCVio #769](https://github.com/Verified-zkEVM/VCVio/pull/769) for the Ajtai/Hachi reductions and
KZG event comparisons. Those lemmas reached `main` with #771, so the pin is an ordinary `main`
commit rather than a prerequisite branch. The Lean 4.34 bump (#903) deferred independent PMF
retirement; the follow-up now enforces an empty retirement inventory.

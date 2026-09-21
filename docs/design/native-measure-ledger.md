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

Developed on VCVio branch `codex/arklib-native-prereqs` (stacked on
`codex/measure-disagreement-prf-reader`, i.e. on top of #758/#763/#764).

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
ArkLib pins the squash merge `93cee8a1f25135436d96cab6bd89a0e5a4cf7660`, whose tree is
identical to the validated PR head `c2ca892ec693bca9403a98111cc6f8f738b8c029`.
VCVio #769 merged into the prerequisites branch, not VCVio `main`;
consolidating that upstream stack is separate from retiring ArkLib's own probability surface.

## Checkpoints

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

### Proof-size review

The generator family's remaining source increase is sampler declarations, signatures, and
explicit instance arguments, not longer mathematical arguments. The focused proof-body counts
below exclude theorem statements and docstrings and compare to #903:

| File / declaration | Before | After | Accounting |
|---|---:|---:|---|
| `ProximityGenerator/Basic.poly_gen_is_zero_evading` | 21 | 19 | Native event equality removes the PMF-map step. |
| `TensorGenerator.isMCAGenerator_tensorGenerator_of_moduleInterleavedCode` | 72 | 70 | Upstream conditional product bound. |
| `TensorGenerator.isMCAGenerator_tensorGenerator` | 51 | 47 | Upstream product and finite union bounds. |
| `PolynomialGenerator.isMCAGenerator_tensorGeneratorPi` | 51 | 51 | Native zero-event proof offsets explicit tail sampler setup. |
| `PolynomialGenerator.isMCAGenerator_tensorGeneratorPi_tight` | 57 | 57 | Same dependent-product setup and zero-event argument. |
| `ToyProblem/SoundnessBounds.exists_dotProduct_image_card_le` | 42 | 42 | Native mathematical corollary supplies the operational witness. |
| `ToyProblem/SoundnessBounds.exists_affine_image_card_le` | 39 | 39 | Native cardinality threshold avoids expanded ENNReal arithmetic. |

`RbrGame.prEvent_optionT_simulateQ_addLift_getChallenge_first_bind_le_convex` grows by four
proof lines (R1/R4): it explicitly proves that a uniform sampler's event and complement have
mass one, using a proof-local discrete measurable space. This avoids a simplifier-selected
retired probability instance. The four `support_nonempty` applications in transcript-tree and
coordinate-wise proofs explicitly select the native instance; their extra physical lines only
wrap that argument. The identity verifier proof eliminates an impossible challenge index.
The already-admitted lift-context theorem retains its admission and drops its unused preliminary
simplification. No new admission or baseline allowance is introduced.

The mathematical collision-image theorem now takes a probability measure and an explicit
countable full-mass carrier. Its witness still has positive singleton mass. ToyProblem converts
that fact back to operational support before extracting sampled parameters; replacing it with
membership in an arbitrary full-measure set would weaken the result. The theorem remains
universe-polymorphic.

Validation also tests rejection of retired notation, retired declaration types and bodies,
private declarations, and attempts to bypass the strict gate with a covering baseline. Inert
strings and comments remain allowed. Existing admissions are retained, not discharged by this
migration; the axiom regression baseline must remain unchanged.

## Upstream gaps found during conversion

Native Boolean implication and union bounds, event monotonicity on support, a conditional product
lower bound, and the support-indexed additive bind bound,
are supplied by [VCVio #769](https://github.com/Verified-zkEVM/VCVio/pull/769)
for the Ajtai/Hachi reductions and KZG event comparisons. The pin includes the prerequisite
branch above. The Lean 4.34 bump (#903) deferred independent PMF retirement; the follow-up
now enforces an empty retirement inventory.

# Native-measure conversion ledger

The Lean 4.34 upgrade converts consumers of VCVio's retiring scalar probability API
(`Pr[… | …]`, `probEvent`, `probOutput`, `probFailure`, `evalSPMF`/`𝒮[…]`, `NeverFail`,
and the PMF-based `IsUniformSpec`/`IsProbabilitySpec`) to the native measure API
`𝒟[…]` and `Pr{…}[…]`. The upgrade must pass `./scripts/validate.sh --axioms` with
the existing zero-warning gate and axiom baseline unchanged.

ArkLib's independent Mathlib `PMF` notation `Pr_{ let x ←$ᵖ S }[…]` is a separate,
deferred conversion. It does not use VCVio's deprecated compatibility layer and remains valid
on Lean 4.34. The optional `lake exe retiredsweep` inventory includes this broader work; an
empty inventory is the eventual full-retirement goal, not a prerequisite for this toolchain bump.
The broader campaign is tracked in [issue #904](https://github.com/Verified-zkEVM/ArkLib/issues/904).

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
- `ArkLib/ToVCVio/` retains compatibility imports needed by current clients. Further removal belongs
  to the full retirement campaign.

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

Still to do upstream (from the plan): U8 structural `IsUniformMeasureSpec` instances for
`spec + spec'` (fallback: local instance triple), U9 `IsProbabilityMeasure` glue for `StateT.run'`
and `OptionT.mk`.

## Checkpoints

| PR | Family | Files | Lines before | After | Δ | Retired refs before → after | Regressions (file:decl, +N, reason) |
|---|---|---|---|---|---|---|---|
| A0 | dependency bump | `lean-toolchain`, `lakefile.toml`, `lake-manifest.json`, mechanical fixes | — | — | — | (initial ledger size recorded here) | — |

## Upstream gaps found during conversion

Native Boolean implication and union bounds, event monotonicity on support, a conditional product
lower bound, and the support-indexed additive bind bound,
are supplied by [VCVio #769](https://github.com/Verified-zkEVM/VCVio/pull/769)
for the Ajtai/Hachi reductions and KZG event comparisons. The pin includes the prerequisite
branch above; the optional PMF retirement inventory is not a merge gate for this bump.

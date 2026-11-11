/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen
-/
module

public import ArkLib.OracleReduction.Execution

/-!
# Eager oracle sampling with VCVio

A fixed deterministic oracle is VCVio's `QueryImpl spec Id`. Sample that table using
`uniformSample`, then answer queries with `pure (table q)` under `simulateQ`.
There is no additional distribution structure: samplers have type `ProbComp α`.
CO25's permutation sampler retains `Equiv.Perm` so inverse answers are derived from the
same permutation. Its concrete samplers and interpreters live in `DuplexSponge/Defs.lean`.

This module provides finite sampling bridges and pointwise marginal laws without an
additional oracle-distribution wrapper.
-/

@[expose] public section

namespace OracleComp

/-- `sampler.IsFreshUniformSampler impl` means that, from every initial state, evaluating
`sampler` with `impl` has the same joint output-state distribution as a fresh uniform sample paired
with the unchanged initial state. This simultaneously captures uniformity, independence from the
initial state, state preservation, and absence of failure. -/
def IsFreshUniformSampler {ι σ α : Type} {spec : OracleSpec ι}
    [instSampleable : SampleableType α]
    (sampler : OracleComp spec α) (impl : QueryImpl spec (StateT σ ProbComp)) : Prop :=
  ∀ state, (simulateQ impl sampler).run state =ᵈ (do
    let value ← uniformSample _ (h := instSampleable)
    return (value, state))

end OracleComp

namespace OracleReduction

open OracleComp OracleSpec
open scoped ENNReal

variable {ι : Type}

/-! ## §1. Function-table carriers -/

/-- Explicit `SampleableType (α → β)` construction from `VCVCompatible` domain and range.

`(QueryImpl (α →ₒ β) Id)` is definitionally `α → β`. This remains a definition rather than a
global instance because `SampleableType` carries sampler data and VCVio already provides
function-specific sampling instances. -/
@[reducible] noncomputable def sampleableTypePiVCV
    {α β : Type} [VCVCompatible α] [VCVCompatible β] :
    SampleableType (α → β) := by
  letI : FinEnum α := VCVCompatible.toFinEnum
  letI : FinEnum β := VCVCompatible.toFinEnum
  letI : Nonempty (α → β) := ⟨fun _ => default⟩
  infer_instance


/-! ## Uniform-table marginal laws -/

section MarginalLaws

variable {spec : OracleSpec ι}

private noncomputable def mapRangeAt {spec : OracleSpec ι} (q : spec.Domain)
    (e : spec.Range q ≃ spec.Range q) : (QueryImpl spec Id) ≃ (QueryImpl spec Id) :=
  let _ : DecidableEq spec.Domain := Classical.typeDecidableEq _
  { toFun := fun g => Function.update g q (e (g q))
    invFun := fun g => Function.update g q (e.symm (g q))
    left_inv := by
      intro g
      funext q'
      by_cases h : q' = q
      · subst q'
        simp [Function.update]
      · simp [Function.update, h]
    right_inv := by
      intro g
      funext q'
      by_cases h : q' = q
      · subst q'
        simp [Function.update]
      · simp [Function.update, h] }

private lemma mapRangeAt_apply_self {spec : OracleSpec ι} (q : spec.Domain)
    (e : spec.Range q ≃ spec.Range q) (g : (QueryImpl spec Id)) :
    (mapRangeAt q e g) q = e (g q) := by
  let _ : DecidableEq spec.Domain := Classical.typeDecidableEq _
  simp [mapRangeAt, Function.update]

/-- Every value of a fixed query has the same probability under a uniformly sampled table:
swapping two values at that query is a bijection of tables. -/
private theorem prEvent_uniform_query_eq_eq
    [SampleableType (QueryImpl spec Id)] (q : spec.Domain)
    (y z : spec.Range q) :
    Pr{let g ← $ᵗ (QueryImpl spec Id)}[g q = y] =
      Pr{let g ← $ᵗ (QueryImpl spec Id)}[g q = z] := by
  classical
  rw [← SampleableType.prEvent_uniformSample_equiv (mapRangeAt q (Equiv.swap y z))
    (fun g : QueryImpl spec Id => g q = y)]
  refine prEvent_congr _ _ _ fun g => ?_
  rw [mapRangeAt_apply_self, Equiv.swap_apply_eq_iff, Equiv.swap_apply_left]

/-- Reading a fixed query from a uniformly sampled table has uniform marginal distribution. -/
theorem prEvent_uniform_query_eq
    [SampleableType (QueryImpl spec Id)] (q : spec.Domain)
    [Fintype (spec.Range q)] (y : spec.Range q) :
    Pr{let g ← $ᵗ (QueryImpl spec Id)}[g q = y] =
      (Fintype.card (spec.Range q) : ℝ≥0∞)⁻¹ := by
  let : MeasurableSpace (spec.Range q) := ⊤
  have hsum : ∑ z : spec.Range q, Pr{let g ← $ᵗ (QueryImpl spec Id)}[g q = z] = 1 := by
    let read : QueryImpl spec Id → spec.Range q := fun g => g q
    calc _ = ∑ z : spec.Range q, 𝒟[read <$> ($ᵗ (QueryImpl spec Id))] {z} :=
          Finset.sum_congr rfl fun z _ => by rw [← prEvent_eq_evalDist_singleton, prEvent_map]
      _ = 1 := by
        rw [MeasureTheory.sum_measure_singleton, Finset.coe_univ, MeasureTheory.measure_univ]
  have hconst : ∑ _z : spec.Range q, Pr{let g ← $ᵗ (QueryImpl spec Id)}[g q = y] = 1 := by
    rw [← hsum]
    exact Finset.sum_congr rfl fun z _ => prEvent_uniform_query_eq_eq q y z
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_comm] at hconst
  exact ENNReal.eq_inv_of_mul_eq_one_left hconst

/-- **Level 2.** Marginal at a single query is uniform over the range. -/
theorem prEvent_uniform_marginal
    [SampleableType (QueryImpl spec Id)] (q : spec.Domain)
    [Fintype (spec.Range q)] (y : spec.Range q) :
    Pr{let x ← (do let g ← $ᵗ (QueryImpl spec Id); pure (g q))}[x = y] =
      (Fintype.card (spec.Range q) : ℝ≥0∞)⁻¹ := by
  rw [← prEvent_uniform_query_eq q y]
  simp

end MarginalLaws

/-! ## Paper-named samplers

`D_ROM.sample` and `D_IP.sample` name uniform deterministic-table samplers using VCVio's types.
DSFS specializes them to encoded (Hyb1), decoded (Hyb2), and salted FS (Hyb3/4) queries.
These eager samplers do not replace the fixed oracle with fresh independent answers.
-/

section SamplingExamples

/-! ### `D_ROM.sample` — random-function constructor. -/

/-- Generic `D_ROM.sample` constructor for any random-function oracle spec:
uniformly sample one deterministic table realization. -/
@[reducible]
def D_ROM.sample {ι : Type} (spec : OracleSpec ι)
    [instSampleable : SampleableType (QueryImpl spec Id)] :
    ProbComp (QueryImpl spec Id) :=
  uniformSample _ (h := instSampleable)

/-! ### `D_IP.sample` — ideal-protocol Fiat-Shamir challenger.

The Fiat-Shamir challenge oracle (`fsChallengeOracle` / `srChallengeOracle`) is keyed by
`(challenge index, statement, prover-prefix)` and returns the round-`i` challenge type.
`D_IP.sample` samples a single deterministic such function.

DSFS Hyb3 / Hyb4 (salted) instantiate `D_IP.sample` with the *salted* statement type
`Statement := StmtIn × Salt`, i.e. `D_IP.sample (StmtIn × Salt) pSpec` (`D_IP_salted.sample` in
`DuplexSponge/Defs.lean`). `Salt` is the binary salt type `{0,1}^{δ⋆}`; the on-sponge salt
`Vector U δ` enters the oracle key only through `SaltCodec.encode = bin`. -/

/-- Bridge instance: granular `VCVCompatible` hypotheses on statement, message, and challenge
types suffice to derive `SampleableType (QueryImpl (fsChallengeOracle Statement pSpec) Id)`. -/
noncomputable instance instSampleableTypeFSChallengeOracle
    {n : ℕ} {pSpec : ProtocolSpec n} {Statement : Type}
    [VCVCompatible Statement]
    [∀ i, VCVCompatible (pSpec.Message i)]
    [∀ i, VCVCompatible (pSpec.Challenge i)] :
    SampleableType (QueryImpl (ProtocolSpec.fsChallengeOracle Statement pSpec) Id) := by
  -- Each prefix message type is definitionally the corresponding message type in `pSpec`.
  letI : ∀ k : Fin (n + 1), Fintype (pSpec.MessagesUpTo k) := fun k => by
    letI : ∀ i : pSpec.MessageIdxUpTo k, Fintype (pSpec.MessageUpTo k i) :=
      fun i => (inferInstance :
        Fintype (pSpec.Message ⟨i.1.castLE (by omega), i.property⟩))
    infer_instance
  -- The challenge-oracle domain is a sigma of a challenge index and its finite query type.
  letI : Fintype (ProtocolSpec.fsChallengeOracle Statement pSpec).Domain := by
    dsimp only [ProtocolSpec.fsChallengeOracle, ProtocolSpec.srChallengeOracle,
      OracleInterface.toOracleSpec, ProtocolSpec.challengeOracleInterfaceSR,
      OracleSpec.toPFunctor, OracleInterface.Query]
    infer_instance
  -- Spell out the dependent range family to keep synthesis from repeatedly unfolding the spec.
  letI : ∀ q : (ProtocolSpec.fsChallengeOracle Statement pSpec).Domain,
      Fintype ((ProtocolSpec.fsChallengeOracle Statement pSpec).Range q) :=
    fun q => (inferInstance : Fintype (pSpec.Challenge q.1))
  letI : Fintype (QueryImpl (ProtocolSpec.fsChallengeOracle Statement pSpec) Id) :=
    show Fintype ((q : (ProtocolSpec.fsChallengeOracle Statement pSpec).Domain) →
      (ProtocolSpec.fsChallengeOracle Statement pSpec).Range q) from Fintype.ofFinite _
  -- A challenge table is nonempty because every challenge response type is inhabited.
  letI : Nonempty (QueryImpl (ProtocolSpec.fsChallengeOracle Statement pSpec) Id) :=
    ⟨fun q => (default : pSpec.Challenge q.1)⟩
  apply SampleableType.ofFintype

/-- `D_IP.sample` over `fsChallengeOracle Statement pSpec`:
uniform random function from prover-prefix
queries to challenges. DSFS Hyb3 / Hyb4 use this with `Statement := StmtIn × Salt`. -/
@[reducible]
noncomputable def D_IP.sample {n : ℕ} (Statement : Type) (pSpec : ProtocolSpec n)
    [VCVCompatible Statement]
    [∀ i, VCVCompatible (pSpec.Message i)]
    [∀ i, VCVCompatible (pSpec.Challenge i)] :
    ProbComp (QueryImpl (ProtocolSpec.fsChallengeOracle Statement pSpec) Id) :=
  D_ROM.sample (instSampleable := instSampleableTypeFSChallengeOracle)

/-! ### `D_Σ` — §5.8 encoded-challenge oracle.

Paper `D_Σ` (Hyb1) has domain
`(i : pSpec.ChallengeIdx) × (StmtIn × Vector U δ × pSpec.EncodedMessagesBefore U i.1.castSucc)`
and range `Vector U (challengeSize i)`.

The concrete `gSpec` and `D_Sigma.sample` declarations live in `DuplexSponge/Defs.lean`; their
random-function construction is the same as `D_ROM.sample` / `D_IP.sample`. -/

/-! ### Hyb2 decoded challenge distribution.

Hyb2 samples `e_i` with the same input domain as `D_Σ`, but range `pSpec.Challenge i`
(`𝓜_{V,i}` in the paper). This is not `D_Σ`; it is the decoded verifier-message oracle family
from Eq. (53), concretely `eSpec` with distribution `D_e.sample` in `DuplexSponge/Defs.lean`. -/

end SamplingExamples

end OracleReduction

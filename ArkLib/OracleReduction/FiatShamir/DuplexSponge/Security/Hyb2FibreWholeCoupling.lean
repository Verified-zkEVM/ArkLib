/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen
-/

import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.Hyb2FibreSamplerNormalization

/-!
# Whole-execution H₁--H₂ fibre coupling

This module packages the table-fibre kernel at the observed revised-game boundary.
The target is Claim 5.22's exact adaptive coupling; in particular its result retains
the full ordered outer-query log rather than only the final public output.
-/

noncomputable section

open OracleComp OracleSpec ProtocolSpec

namespace DuplexSpongeFS.KeyLemma

open DuplexSpongeFS.ProverTransform DuplexSpongeFS.DSTraceStorage

variable {n : ℕ} {pSpec : ProtocolSpec n} {StmtIn U : Type}
  [SpongeUnit U] [SpongeSize] [VCVCompatible U] [VCVCompatible StmtIn]
  [∀ i, VCVCompatible (pSpec.Challenge i)] [∀ i, VCVCompatible (pSpec.Message i)]
  [codec : Codec pSpec U] {δ : ℕ} [DecidableEq StmtIn] [DecidableEq U]
  [Fintype U] [Nonempty U]
  [∀ i, Fintype (pSpec.Message i)] [∀ i, DecidableEq (pSpec.Message i)]
  [∀ i, Fintype (pSpec.Challenge i)] [∀ i, DecidableEq (pSpec.Challenge i)]

/-- The observed eager H₁ execution after fixing its complete encoded challenge table. -/
noncomputable def hyb1EagerObservedFromTable
    {ι StmtOut : Type} {oSpec : OracleSpec ι} {T_H T_P : Type}
    [LawfulTraceNablaImpl T_H T_P StmtIn U]
    (oSpecImpl : QueryImpl oSpec ProbComp)
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (maliciousProver : MaliciousProver oSpec pSpec StmtIn U δ)
    (table : OracleReduction.OracleFamily (gSpec (U := U) StmtIn pSpec δ)) :
    ProbComp (HybridGameRevisedObservation
      (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
      (pSpec := pSpec) (U := U) (δ := δ)
      (gSpec (U := U) StmtIn pSpec δ) T_H T_P PUnit) :=
  simulateQ
    (hyb1AmbientOuterImpl (oSpec := oSpec) (StmtIn := StmtIn)
      (pSpec := pSpec) (U := U) (δ := δ) oSpecImpl table)
    (hybridGameRevisedObserved (T_H := T_H) (T_P := T_P)
      (gImpl := hyb1GImpl (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ))
      V maliciousProver)

/-- The H₁ observed execution after first drawing H₂'s decoded table and then an eager
representative in its complete decoder fibre.  It is named separately so the two exact
Claim-5.22 equalities do not require the evaluator to unfold the entire game at once. -/
noncomputable def hyb1FibreEagerObservedDist
    {ι StmtOut : Type} {oSpec : OracleSpec ι} {T_H T_P : Type}
    [LawfulTraceNablaImpl T_H T_P StmtIn U]
    (oSpecImpl : QueryImpl oSpec ProbComp)
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (maliciousProver : MaliciousProver oSpec pSpec StmtIn U δ) :
    ProbComp (HybridGameRevisedObservation
      (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
      (pSpec := pSpec) (U := U) (δ := δ)
      (gSpec (U := U) StmtIn pSpec δ) T_H T_P PUnit) := do
  let observedTable ← uniformEncodedChallengeTable
    (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)
  let table ← decodedFibreUniformTable (StmtIn := StmtIn) (pSpec := pSpec)
    (U := U) (δ := δ)
    (decodeEncodedChallengeTable (U := U) StmtIn pSpec δ observedTable)
  hyb1EagerObservedFromTable (T_H := T_H) (T_P := T_P)
    (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)
    oSpecImpl V maliciousProver
    (projectDecodedFibreTable (pSpec := pSpec) (U := U)
      (decodeEncodedChallengeTable (U := U) StmtIn pSpec δ observedTable) table)

/-- The H₁ marginal of the witnessed joint table sampler used by Claim 5.22.  Keeping the
joint sampler named preserves the pointwise decoded-table equality needed by the H₂ side,
while this marginal is exactly the ordinary H₁ uniform-table experiment. -/
noncomputable def hyb1FibrePairObservedDist
    {ι StmtOut : Type} {oSpec : OracleSpec ι} {T_H T_P : Type}
    [LawfulTraceNablaImpl T_H T_P StmtIn U]
    (oSpecImpl : QueryImpl oSpec ProbComp)
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (maliciousProver : MaliciousProver oSpec pSpec StmtIn U δ) :
    ProbComp (HybridGameRevisedObservation
      (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
      (pSpec := pSpec) (U := U) (δ := δ)
      (gSpec (U := U) StmtIn pSpec δ) T_H T_P PUnit) := do
  let pair ← sampleEncodedTableFibrePair
    (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)
  hyb1EagerObservedFromTable (T_H := T_H) (T_P := T_P)
    (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)
    oSpecImpl V maliciousProver pair.representative

/-- The H₁ representative marginal of the joint fibre experiment, written without packaging the
unused H₂ table component.  Its explicit form lets the whole-table fibre law be applied without
unfolding the adaptive H₁ continuation. -/
noncomputable def hyb1FibreWitnessObservedDist
    {ι StmtOut : Type} {oSpec : OracleSpec ι} {T_H T_P : Type}
    [LawfulTraceNablaImpl T_H T_P StmtIn U]
    (oSpecImpl : QueryImpl oSpec ProbComp)
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (maliciousProver : MaliciousProver oSpec pSpec StmtIn U δ) :
    ProbComp (HybridGameRevisedObservation
      (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
      (pSpec := pSpec) (U := U) (δ := δ)
      (gSpec (U := U) StmtIn pSpec δ) T_H T_P PUnit) := do
  let observedTable ← uniformEncodedChallengeTable
    (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)
  let witness ← decodedFibreUniformWitness
    (encodedChallengeTableFintype
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ))
    (Classical.decEq _)
    (decodeEncodedChallengeTable (U := U) StmtIn pSpec δ observedTable)
  hyb1EagerObservedFromTable (T_H := T_H) (T_P := T_P)
    (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)
    oSpecImpl V maliciousProver witness.1

/-- The explicit witness marginal and the representative component of the joint table sample
are the same computation.  This is the missing middle equality of the axiom-clean Claim-5.22
route: the joint sample retains the decoded-table witness, while the witness form exposes the
same draw directly. -/
theorem evalDist_hyb1FibreWitnessObservedDist_eq_hyb1FibrePairObservedDist
    {ι StmtOut : Type} {oSpec : OracleSpec ι} {T_H T_P : Type}
    [LawfulTraceNablaImpl T_H T_P StmtIn U]
    (oSpecImpl : QueryImpl oSpec ProbComp)
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (maliciousProver : MaliciousProver oSpec pSpec StmtIn U δ) :
    𝒟[hyb1FibreWitnessObservedDist (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)
      oSpecImpl V maliciousProver] =
      𝒟[hyb1FibrePairObservedDist (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)
        oSpecImpl V maliciousProver] := by
  unfold hyb1FibreWitnessObservedDist hyb1FibrePairObservedDist
  exact evalDist_uniformEncodedTable_witness_bind_eq_pair
    (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)
    (fun _ witness => hyb1EagerObservedFromTable (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)
      oSpecImpl V maliciousProver witness.1)

/-- The H₁ marginal of Claim 5.22's joint sampler is the ordinary eager H₁ observed
experiment.  The continuation is the complete game, so the equality includes adaptive control
and the full raw outer log. -/
theorem evalDist_hyb1FibrePairObservedDist_eq_hyb1EagerObservedDist
    {ι StmtOut : Type} {oSpec : OracleSpec ι} {T_H T_P : Type}
    [LawfulTraceNablaImpl T_H T_P StmtIn U]
    (oSpecImpl : QueryImpl oSpec ProbComp)
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (maliciousProver : MaliciousProver oSpec pSpec StmtIn U δ) :
    𝒟[hyb1FibrePairObservedDist (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)
      oSpecImpl V maliciousProver] =
      𝒟[hyb1EagerObservedDist (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)
        oSpecImpl V maliciousProver] := by
  unfold hyb1FibrePairObservedDist hyb1EagerObservedDist hyb1EagerObservedFromTable
  exact evalDist_sampleEncodedTableFibrePair_representative_bind_eq_uniform
    (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)
    (fun table => simulateQ
      (hyb1AmbientOuterImpl (oSpec := oSpec) (StmtIn := StmtIn)
        (pSpec := pSpec) (U := U) (δ := δ) oSpecImpl table)
      (hybridGameRevisedObserved (T_H := T_H) (T_P := T_P)
        (gImpl := hyb1GImpl (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ))
        V maliciousProver))

/-- The eager table of all decoder-fibre cells is the witnessed representative table.  This
equality is pointwise below the outer uniform table draw and is therefore exact for the complete
adaptive observed H₁ execution. -/
theorem evalDist_hyb1FibreEagerObservedDist_eq_hyb1FibreWitnessObservedDist
    {ι StmtOut : Type} {oSpec : OracleSpec ι} {T_H T_P : Type}
    [LawfulTraceNablaImpl T_H T_P StmtIn U]
    (oSpecImpl : QueryImpl oSpec ProbComp)
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (maliciousProver : MaliciousProver oSpec pSpec StmtIn U δ) :
    𝒟[hyb1FibreEagerObservedDist (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)
      oSpecImpl V maliciousProver] =
      𝒟[hyb1FibreWitnessObservedDist (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)
        oSpecImpl V maliciousProver] := by
  unfold hyb1FibreEagerObservedDist hyb1FibreWitnessObservedDist
  exact evalDist_uniformEncodedTable_fibreEager_bind_eq_witness
    (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)
    (fun _ witness => hyb1EagerObservedFromTable (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)
      oSpecImpl V maliciousProver witness.1)

/-- The same eager-fibre H₁ execution written through the ordinary encoded-table fibre kernel.
This is the exact normal form used to join the live lazy realization to the joint-table sampler. -/
noncomputable def hyb1PreimageFibreObservedDist
    {ι StmtOut : Type} {oSpec : OracleSpec ι} {T_H T_P : Type}
    [LawfulTraceNablaImpl T_H T_P StmtIn U]
    (oSpecImpl : QueryImpl oSpec ProbComp)
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (maliciousProver : MaliciousProver oSpec pSpec StmtIn U δ) :
    ProbComp (HybridGameRevisedObservation
      (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
      (pSpec := pSpec) (U := U) (δ := δ)
      (gSpec (U := U) StmtIn pSpec δ) T_H T_P PUnit) := do
  let observedTable ← uniformEncodedChallengeTable
    (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)
  let table ← uniformEncodedTableInDecodedFibre
    (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)
    (decodeEncodedChallengeTable (U := U) StmtIn pSpec δ observedTable)
  hyb1EagerObservedFromTable (T_H := T_H) (T_P := T_P)
    (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)
    oSpecImpl V maliciousProver table

/-- The live eager fibre-table implementation has the ordinary encoded-table fibre law under
the whole observed H₁ continuation. -/
theorem evalDist_hyb1FibreEagerObservedDist_eq_hyb1PreimageFibreObservedDist
    {ι StmtOut : Type} {oSpec : OracleSpec ι} {T_H T_P : Type}
    [LawfulTraceNablaImpl T_H T_P StmtIn U]
    (oSpecImpl : QueryImpl oSpec ProbComp)
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (maliciousProver : MaliciousProver oSpec pSpec StmtIn U δ) :
    𝒟[hyb1FibreEagerObservedDist (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)
      oSpecImpl V maliciousProver] =
      𝒟[hyb1PreimageFibreObservedDist (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)
        oSpecImpl V maliciousProver] := by
  unfold hyb1FibreEagerObservedDist hyb1PreimageFibreObservedDist
  rw [evalDist_bind, evalDist_bind]
  apply bind_congr
  intro observedTable
  exact evalDist_decodedFibreUniformTable_project_bind_eq_uniformEncodedFibre
    (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)
    (decodeEncodedChallengeTable (U := U) StmtIn pSpec δ observedTable)
    (hyb1EagerObservedFromTable (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)
      oSpecImpl V maliciousProver)

/-- The live lazy fibre realization of the whole observed H₂ execution equals the explicit
eager-fibre H₁ experiment.  It preserves the full ordered outer log, not just public output. -/
theorem evalDist_hyb2FibreLazyObservedDist_eq_hyb1FibreEagerObservedDist
    {ι StmtOut : Type} {oSpec : OracleSpec ι} {T_H T_P : Type}
    [LawfulTraceNablaImpl T_H T_P StmtIn U]
    (oSpecImpl : QueryImpl oSpec ProbComp)
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (maliciousProver : MaliciousProver oSpec pSpec StmtIn U δ) :
    𝒟[hyb2FibreLazyObservedDist (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)
      oSpecImpl V maliciousProver] =
      𝒟[hyb1FibreEagerObservedDist (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)
        oSpecImpl V maliciousProver] := by
  unfold hyb2FibreLazyObservedDist hyb1FibreEagerObservedDist
  rw [evalDist_bind, evalDist_bind]
  apply bind_congr
  intro table
  exact evalDist_hyb2FibreLazyObserved_eq_hyb1EagerObserved
    (T_H := T_H) (T_P := T_P)
    (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)
    (decodeEncodedChallengeTable (U := U) StmtIn pSpec δ table)
    oSpecImpl V maliciousProver

/-- Claim 5.22's axiom-clean whole-execution normalizer: the lazy decoded-table H₂
execution has the same observed distribution as eager H₁.  The intermediate fibre forms
make the common table draw and its uniformly sampled encoded representative explicit. -/
theorem evalDist_hyb2FibreLazyObservedDist_eq_hyb1EagerObservedDist
    {ι StmtOut : Type} {oSpec : OracleSpec ι} {T_H T_P : Type}
    [LawfulTraceNablaImpl T_H T_P StmtIn U]
    (oSpecImpl : QueryImpl oSpec ProbComp)
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (maliciousProver : MaliciousProver oSpec pSpec StmtIn U δ) :
    𝒟[hyb2FibreLazyObservedDist (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)
      oSpecImpl V maliciousProver] =
      𝒟[hyb1EagerObservedDist (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)
        oSpecImpl V maliciousProver] := by
  calc
    𝒟[hyb2FibreLazyObservedDist (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)
      oSpecImpl V maliciousProver] =
        𝒟[hyb1FibreEagerObservedDist (T_H := T_H) (T_P := T_P)
          (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)
          oSpecImpl V maliciousProver] :=
      evalDist_hyb2FibreLazyObservedDist_eq_hyb1FibreEagerObservedDist
        (T_H := T_H) (T_P := T_P) (oSpecImpl := oSpecImpl) V maliciousProver
    _ = 𝒟[hyb1FibreWitnessObservedDist (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)
      oSpecImpl V maliciousProver] :=
      evalDist_hyb1FibreEagerObservedDist_eq_hyb1FibreWitnessObservedDist
        (T_H := T_H) (T_P := T_P) (oSpecImpl := oSpecImpl) V maliciousProver
    _ = 𝒟[hyb1FibrePairObservedDist (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)
      oSpecImpl V maliciousProver] :=
      evalDist_hyb1FibreWitnessObservedDist_eq_hyb1FibrePairObservedDist
        (T_H := T_H) (T_P := T_P) (oSpecImpl := oSpecImpl) V maliciousProver
    _ = 𝒟[hyb1EagerObservedDist (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)
      oSpecImpl V maliciousProver] :=
      evalDist_hyb1FibrePairObservedDist_eq_hyb1EagerObservedDist
        (T_H := T_H) (T_P := T_P) (oSpecImpl := oSpecImpl) V maliciousProver

end DuplexSpongeFS.KeyLemma

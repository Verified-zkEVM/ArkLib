/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.OracleReduction.Security.Basic
import ArkLib.ProofSystem.Sumcheck.Spec.General
import ArkLib.ProofSystem.Logup.Protocol
import ArkLib.ToVCVio.OracleComp.Coercions.SubSpec

/-!
# Shared LogUp Security Lemmas
-/

open scoped NNReal

namespace Logup

section Common

variable {ι : Type} (oSpec : OracleSpec ι)
variable (F : Type) [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
variable (n M : ℕ)
variable (params : ProtocolParams M)
variable {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))

omit [Fintype F] [DecidableEq F] [SampleableType F] in
/-- The protocol's concrete partial-sum groups partition the term indices `{0, ..., M}`. -/
theorem sum_protocolGroups (params : ProtocolParams M) (g : TermIdx M → F) :
    (∑ k : Fin params.numGroups, ∑ i ∈ params.group k, g i) = ∑ i : TermIdx M, g i := by
  classical
  have hℓ := params.sumSize_pos
  have hidx : ∀ i : TermIdx M, i.val / params.sumSize < params.numGroups := by
    intro i
    have hiM : i.val ≤ M := Nat.lt_succ_iff.mp i.isLt
    have hle : i.val / params.sumSize ≤ M / params.sumSize := Nat.div_le_div_right hiM
    rw [ProtocolParams.numGroups, Nat.add_div_right _ hℓ]
    omega
  rw [← Finset.sum_fiberwise Finset.univ
      (fun i : TermIdx M => (⟨i.val / params.sumSize, hidx i⟩ : Fin params.numGroups)) g]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  congr 1
  ext i
  simp only [ProtocolParams.group, Finset.mem_filter, Finset.mem_univ, true_and, Fin.ext_iff]
  constructor
  · rintro ⟨h1, h2⟩
    have ha : k.val ≤ i.val / params.sumSize := (Nat.le_div_iff_mul_le hℓ).mpr h1
    have hb : i.val / params.sumSize < k.val + 1 := (Nat.div_lt_iff_lt_mul hℓ).mpr h2
    omega
  · intro h
    exact ⟨(Nat.le_div_iff_mul_le hℓ).mp (by omega),
      (Nat.div_lt_iff_lt_mul hℓ).mp (by omega)⟩

omit [Fintype F] [DecidableEq F] [SampleableType F] in
theorem sum_piFinset_map_univ_eq_sum_hypercube
    (D : Fin 2 ↪ F) (f : (Fin n → F) → F) :
    (∑ x ∈ Fintype.piFinset fun _ : Fin n => Finset.univ.map D, f x) =
      ∑ u : (Fin n → Fin 2), f (fun j => D (u j)) := by
  let e : (Fin n → Fin 2) ↪ (Fin n → F) := Function.Embedding.arrowCongrRight D
  change (∑ x ∈ Fintype.piFinset fun _ : Fin n => Finset.univ.map D, f x) =
    ∑ u : (Fin n → Fin 2), f (e u)
  rw [← Finset.sum_map]
  congr 1
  ext x
  simp only [Fintype.mem_piFinset, Finset.mem_map, Finset.mem_univ, true_and]
  constructor
  · intro hx
    choose y hy using hx
    refine ⟨y, ?_⟩
    funext i
    exact hy i
  · rintro ⟨y, rfl⟩ i
    exact ⟨y i, rfl⟩

omit [Fintype F] [DecidableEq F] [SampleableType F] in
theorem logupSumcheckRelationInput_iff
    {stmt : StmtAfterOuter F n M params}
    {oStmt : ∀ i, OStmtAfterOuter F n M params i} :
    logupSumcheckRelationInput F n M params stmt oStmt ↔
      logupOuterSumcheckClaim F n M params stmt oStmt = 0 := by
  unfold logupSumcheckRelationInput Sumcheck.Spec.relationRound
  simp only [Fin.coe_ofNat_eq_mod, Nat.zero_mod, Nat.sub_zero, logupInitialSumcheckStatement,
    Set.mem_setOf_eq, Fin.elim0_append, logupSumcheckOracleStmt]
  change
    (∑ x ∈ Fintype.piFinset fun _ : Fin n => Finset.univ.map (booleanDomain F),
      MvPolynomial.eval ((x ∘ Fin.cast (by omega)) ∘ Fin.cast (by omega))
        (logupSumcheckPolynomial F n M params stmt oStmt).val) = 0 ↔
      logupOuterSumcheckClaim F n M params stmt oStmt = 0
  rw [sum_piFinset_map_univ_eq_sum_hypercube
    (F := F) (n := n) (D := booleanDomain F)
    (f := fun x =>
      MvPolynomial.eval ((x ∘ Fin.cast (by omega)) ∘ Fin.cast (by omega))
        (logupSumcheckPolynomial F n M params stmt oStmt).val)]
  change
    (∑ u : (Fin n → Fin 2),
        MvPolynomial.eval (fun i => (u i : F))
          (logupSumcheckPolynomial F n M params stmt oStmt).val) = 0 ↔
      logupOuterSumcheckClaim F n M params stmt oStmt = 0
  have hsum :
      (∑ u : (Fin n → Fin 2),
          MvPolynomial.eval (fun i => (u i : F))
            (logupSumcheckPolynomial F n M params stmt oStmt).val) =
        logupOuterSumcheckClaim F n M params stmt oStmt := by
    rw [logupOuterSumcheckClaim]
    apply Finset.sum_congr rfl
    intro u _
    simp only [logupSumcheckPolynomial]
  rw [hsum]

omit [Fintype F] [DecidableEq F] [SampleableType F] in
/-- If LogUp's outer algebra proves a zero sum, then the generic Sumcheck input relation is exactly
the claim sent to Sumcheck. -/
theorem logupSumcheckRelationInput_of_zero
    {stmt : StmtAfterOuter F n M params}
    {oStmt : ∀ i, OStmtAfterOuter F n M params i}
    (hZero : logupOuterSumcheckClaim F n M params stmt oStmt = 0) :
    logupSumcheckRelationInput F n M params stmt oStmt :=
  (logupSumcheckRelationInput_iff (F := F) (n := n) (M := M) (params := params)).2 hZero

omit σ init impl [DecidableEq F] [SampleableType F] in
/-- Simulating the scan-free outer verifier against concrete oracles leaves only the public
challenge data packaged as the outer statement. -/
theorem outerVerify_simulateQ_eq (stmt : StmtIn F n M) (oStmt : ∀ i, OStmtIn F n M i)
    (messages : ∀ i, (outerPSpec F n params).Message i)
    (challenges : ∀ i, (outerPSpec F n params).Challenge i) :
    simulateQ (OracleInterface.simOracle2 oSpec oStmt messages)
        ((outerVerifier oSpec F n M params).verify stmt challenges)
      = (do
          let x : F := challenges (outerChallengeXIdx F n M params)
          let batch : BatchingChallenge F n params.numGroups :=
            challenges (outerChallengeBatchIdx F n M params)
          pure { xChallenge := x, zChallenge := batch.1, batchingScalars := batch.2 } :
        OptionT (OracleComp oSpec) (StmtAfterOuter F n M params)) := by
  simp [outerVerifier, outerChallengeXIdx, outerChallengeBatchIdx]
  rfl

omit oSpec F n M params σ init impl [Field F] [Fintype F] [DecidableEq F] [SampleableType F] in
/-- Four-round unfolding of `Fin.induction`, used when expanding the outer protocol run. -/
theorem Fin.induction_four {motive : Fin 5 → Sort*} {zero : motive 0}
    {succ : ∀ i : Fin 4, motive i.castSucc → motive i.succ} :
    Fin.induction (motive := motive) zero succ (Fin.last 4)
      = succ 3 (succ 2 (succ 1 (succ 0 zero))) := rfl

end Common

end Logup

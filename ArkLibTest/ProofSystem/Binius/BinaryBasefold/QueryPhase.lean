/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

import ArkLib.ProofSystem.Binius.BinaryBasefold.QueryPhase

/-!
# Binary Basefold query controls

The strict input relation contains the zero polynomial and its zero oracle family.
The verifier executes every block on that family and rejects a final claimed constant of one.
-/
open Binius.BinaryBasefold Binius.BinaryBasefold.QueryPhase
open OracleSpec OracleComp ProtocolSpec AdditiveNTT Probability
noncomputable section
variable {r : ℕ} [NeZero r]
variable {L : Type} [Field L] [Fintype L] [DecidableEq L]
variable (𝔽q : Type) [Field 𝔽q]
local instance [Finite 𝔽q] : Fact (Nat.Prime (ringChar 𝔽q)) := ⟨CharP.prime_ringChar 𝔽q⟩
variable [Fintype 𝔽q] [DecidableEq 𝔽q] [Fact (Fintype.card 𝔽q = 2)]
variable [Algebra 𝔽q L]
variable (β : Fin r → L) [Fact (LinearIndependent 𝔽q β)] [Fact (β 0 = 1)]
variable {ℓ 𝓡 ϑ : ℕ} [NeZero ℓ] [NeZero 𝓡] [NeZero ϑ] {h_ℓ_add_R_rate : ℓ + 𝓡 < r}
variable [hdiv : Fact (ϑ ∣ ℓ)]

namespace Binius.BinaryBasefold.QueryPhaseTests
open MvPolynomial Polynomial

omit [DecidableEq 𝔽q] [Fact (Fintype.card 𝔽q = 2)] [Fact (β 0 = 1)] [NeZero ℓ] in
private lemma fold_zero (i : Fin r) {dest : Fin r} (steps : ℕ)
    (h : dest.val = i.val + steps) (hle : dest.val ≤ ℓ)
    (cs : Fin steps → L) :
    iteratedFold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i) (steps := steps)
      h hle (fun _ => 0) cs = fun _ => 0 := by
  rw [iteratedFold_eq_matrix_form]
  funext y
  simp [iteratedFoldMatrixForm, pointFoldMatrixForm,
    fiberEvaluations, Matrix.mulVec, dotProduct]

private def zeroOracles : ∀ j, OracleStatement 𝔽q β (ϑ := ϑ)
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ) j := fun _ _ => 0

omit [DecidableEq 𝔽q] [Fact (β 0 = 1)] in
private theorem zero_input_strict (stmt : FinalSumcheckStatementOut (L := L) (ℓ := ℓ)) :
    strictFinalSumcheckRelOut 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (({stmt with finalConstant := 0}, zeroOracles 𝔽q β), ()) := by
  refine ⟨0, ?_, ?_⟩
  · intro j
    simp only [polynomialFromNovelCoeffsF₂, polynomialFromNovelCoeffs,
      ZeroMemClass.coe_zero, map_zero, zero_mul,
      Finset.sum_const_zero]
    change (fun _ => (0 : L)) = _
    symm
    have hp (d : Fin r) : polyToOracleFunc 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (domainIdx := d) (P := (0 : L[X])) = fun _ => (0 : L) := by
      funext y
      simp [polyToOracleFunc]
    rw [hp]
    exact fold_zero 𝔽q β (ℓ := ℓ) (𝓡 := 𝓡)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) _ _ _ _ _
  · simp [zeroOracles, getLastOracle, fold_zero]

omit [Fact (Fintype.card 𝔽q = 2)] in
private lemma zero_step (γ : ℕ)
    (messages : ∀ i, (pSpecQuery 𝔽q β γ (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).Message i)
    (stmt : FinalSumcheckStatementOut (L := L) (ℓ := ℓ))
    (k : Fin (ℓ / ϑ)) (v : sDomain 𝔽q β h_ℓ_add_R_rate ⟨0, by omega⟩) :
    simulateQ (OracleInterface.simOracle2 []ₒ (zeroOracles 𝔽q β) messages)
      (checkSingleFoldingStep 𝔽q β (γ_repetitions := γ) (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) k 0 v stmt).run = pure (some 0) := by
  rw [checkSingleFoldingStep_simulate]
  simp [logicalQueryFiberPoints, zeroOracles, logicalComputeFoldedValue,
    pointFoldMatrixForm, Matrix.mulVec, dotProduct]

/-- The first oracle is zero; every later block has been replaced by a nonzero table. -/
private def corruptedOracles : ∀ j, OracleStatement 𝔽q β (ϑ := ϑ)
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ) j :=
  fun j _ => if j.val = 0 then 0 else 1

omit [Fact (Fintype.card 𝔽q = 2)] in
/-- A corrupted nonzero intermediate table fails the positive-block consistency guard. -/
example (h_two_blocks : 1 < ℓ / ϑ) (γ : ℕ)
    (messages : ∀ i, (pSpecQuery 𝔽q β γ (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).Message i)
    (stmt : FinalSumcheckStatementOut (L := L) (ℓ := ℓ))
    (v : sDomain 𝔽q β h_ℓ_add_R_rate ⟨0, by omega⟩) :
    simulateQ (OracleInterface.simOracle2 []ₒ (corruptedOracles 𝔽q β) messages)
      (checkSingleFoldingStep 𝔽q β (γ_repetitions := γ) (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨1, h_two_blocks⟩ 0 v stmt).run =
      pure none := by
  rw [checkSingleFoldingStep_simulate]
  simp [Nat.pos_of_neZero ϑ, logicalQueryFiberPoints, corruptedOracles, guard_eq]

omit [Fact (Fintype.card 𝔽q = 2)] in
private theorem repetition_rejects (γ : ℕ)
    (messages : ∀ i, (pSpecQuery 𝔽q β γ (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).Message i)
    (stmt : FinalSumcheckStatementOut (L := L) (ℓ := ℓ))
    (v : sDomain 𝔽q β h_ℓ_add_R_rate ⟨0, by omega⟩) :
    simulateQ (OracleInterface.simOracle2 []ₒ (zeroOracles 𝔽q β) messages)
      (checkSingleRepetition 𝔽q β (γ_repetitions := γ) (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) v stmt 1).run = pure none := by
  let so := OracleInterface.simOracle2 []ₒ (zeroOracles 𝔽q β
    (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)) messages
  change (simulateQ so (checkSingleRepetition 𝔽q β (γ_repetitions := γ) (ϑ := ϑ)
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate) v stmt 1) : OptionT (OracleComp []ₒ) Unit) =
      (OptionT.mk (pure none) : OptionT (OracleComp []ₒ) Unit)
  dsimp only [checkSingleRepetition]
  rw [simulateQ_optionT_bind]
  let body := fun (k : Fin (ℓ / ϑ)) (cur : L) => (do
    let next ← checkSingleFoldingStep 𝔽q β (γ_repetitions := γ) (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) k cur v stmt
    pure (ForInStep.yield next) : OptionT (OracleComp _) (ForInStep L))
  have hb (k : Fin (ℓ / ϑ)) : simulateQ so (body k 0).run =
      pure (some (ForInStep.yield (0 : L))) := by
    change (simulateQ so (body k 0) : OptionT (OracleComp []ₒ) (ForInStep L)) =
      (pure (ForInStep.yield (0 : L)) : OptionT (OracleComp []ₒ) (ForInStep L))
    dsimp only [body]
    rw [simulateQ_optionT_bind]
    have hz : (simulateQ so (checkSingleFoldingStep 𝔽q β
        (γ_repetitions := γ) (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) k 0 v stmt) :
        OptionT (OracleComp []ₒ) L) = (pure (0 : L) : OptionT (OracleComp []ₒ) L) :=
      zero_step 𝔽q β γ messages stmt k v
    rw [hz, pure_bind]
    rfl
  have hl := simulateQ_optionT_forIn_yield_pure_some so (List.finRange (ℓ / ϑ)) (0 : L) body hb
  have ht : (OptionT.mk (simulateQ so (forIn (List.finRange (ℓ / ϑ)) (0 : L) body :
      OptionT (OracleComp _) L).run) : OptionT (OracleComp []ₒ) L) =
      (pure (0 : L) : OptionT (OracleComp []ₒ) L) := hl
  change (OptionT.mk (simulateQ so (forIn (List.finRange (ℓ / ϑ)) (0 : L) body :
      OptionT (OracleComp _) L).run) >>= _) = _
  rw [ht, pure_bind]
  simp only [guard_eq, zero_ne_one, ↓reduceIte]
  exact simulateQ_optionT_failure so


example (stmt : FinalSumcheckStatementOut (L := L) (ℓ := ℓ))
    (chals : (pSpecQuery 𝔽q β 1 (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).Challenges) :
    let bad := {stmt with finalConstant := 1}
    let tr := FullTranscript.mk1 (pSpec := pSpecQuery 𝔽q β 1
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate)) (chals ⟨0, by rfl⟩)
    simulateQ (OracleInterface.simOracle2 []ₒ (zeroOracles 𝔽q β) tr.messages)
      ((queryOracleVerifier 𝔽q β (ϑ := ϑ) 1).verify
        (Oₛₒ := fun i : Empty => nomatch i) bad chals).run = pure none := by
  intro bad tr
  let so := OracleInterface.simOracle2 []ₒ (zeroOracles 𝔽q β
    (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)) tr.messages
  have hr : (simulateQ so (checkSingleRepetition 𝔽q β (γ_repetitions := 1) (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (tr.challenges ⟨0, by rfl⟩ 0) bad 1) :
      OptionT (OracleComp []ₒ) Unit) = (OptionT.mk (pure none) : OptionT (OracleComp []ₒ) Unit) :=
    repetition_rejects 𝔽q β 1 tr.messages bad (tr.challenges ⟨0, by rfl⟩ 0)
  change (simulateQ so ((queryOracleVerifier 𝔽q β (ϑ := ϑ) 1).verify
      (Oₛₒ := fun i : Empty => nomatch i) bad chals) : OptionT (OracleComp []ₒ) Bool) =
    (OptionT.mk (pure none) : OptionT (OracleComp []ₒ) Bool)
  dsimp only [queryOracleVerifier, OracleProofVerifier.ofVerify, queryPhaseLogicStep]
  simp only [show List.finRange 1 = [0] from rfl, List.forIn_cons, List.forIn_nil,
    simulateQ_optionT_bind, simulateQ_optionT_pure]
  rw [hr]
  rfl


/-- The query verifier accepts the strict zero input, with no loss of mass. -/
example (γ : ℕ) (stmt : FinalSumcheckStatementOut (L := L) (ℓ := ℓ))
    (chals : (pSpecQuery 𝔽q β γ (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).Challenges) :
    let tr := FullTranscript.mk1 (pSpec := pSpecQuery 𝔽q β γ
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate)) (chals ⟨0, rfl⟩)
    simulateQ (OracleInterface.simOracle2 []ₒ (zeroOracles 𝔽q β) tr.messages)
      ((queryOracleVerifier 𝔽q β (ϑ := ϑ) γ).verify
        (Oₛₒ := fun i : Empty => nomatch i) {stmt with finalConstant := 0} chals).run =
      pure (some true) :=
  queryOracleVerifier_simulate_honest 𝔽q β γ _ _ chals (zero_input_strict 𝔽q β stmt)

/-- The sampled honest protocol has probability one at the exhibited strict zero input. -/
example (γ : ℕ) (stmt : FinalSumcheckStatementOut (L := L) (ℓ := ℓ))
    {σ : Type} (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    let R := OracleReduction.toReduction (Oₛₒ := fun i : Empty => nomatch i)
      (queryOracleReduction 𝔽q β (ϑ := ϑ) γ (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
    let pImpl : QueryImpl ([]ₒ + [(pSpecQuery 𝔽q β γ
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).Challenge]ₒ'challengeOracleInterface)
      (StateT σ ProbComp) :=
        QueryImpl.addLift impl challengeQueryImpl
    Pr{let out ← OptionT.mk do
      let st ← init
      (simulateQ pImpl (R.run ({stmt with finalConstant := 0}, zeroOracles 𝔽q β) ()).run).run' st}[
        (out.2, out.1.2.2) ∈ acceptRejectOracleRel ∧ out.1.2.1 = out.2] = 1 := by
  have h := queryOracleReduction_perfectCompleteness 𝔽q β (ℓ := ℓ) (𝓡 := 𝓡) (ϑ := ϑ) γ
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate) init impl
  change Reduction.perfectCompleteness init impl
    (strictFinalSumcheckRelOut 𝔽q β (ϑ := ϑ)) acceptRejectOracleRel
    (OracleReduction.toReduction (Oₛₒ := fun i : Empty => nomatch i)
      (queryOracleReduction 𝔽q β (ϑ := ϑ) γ)) at h
  rw [Reduction.perfectCompleteness_eq_prob_one] at h
  exact h
    ({stmt with finalConstant := 0}, zeroOracles 𝔽q β) () (zero_input_strict 𝔽q β stmt)

end Binius.BinaryBasefold.QueryPhaseTests

/--
info: 'Binius.BinaryBasefold.QueryPhase.queryPhaseLogicStep_simulate_honest' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Binius.BinaryBasefold.QueryPhase.queryPhaseLogicStep_simulate_honest

/--
info: 'Binius.BinaryBasefold.QueryPhase.queryOracleVerifier_simulate_honest' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Binius.BinaryBasefold.QueryPhase.queryOracleVerifier_simulate_honest

/--
info: 'Binius.BinaryBasefold.QueryPhase.queryOracleReduction_perfectCompleteness' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Binius.BinaryBasefold.QueryPhase.queryOracleReduction_perfectCompleteness

/--
info: 'Binius.BinaryBasefold.QueryPhase.queryOracleVerifier_rbrKnowledgeSoundness'
depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Binius.BinaryBasefold.QueryPhase.queryOracleVerifier_rbrKnowledgeSoundness

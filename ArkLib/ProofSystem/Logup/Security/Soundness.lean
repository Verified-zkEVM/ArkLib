/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/
module

public import ArkLib.ProofSystem.Logup.Interaction.Execution
public import ArkLib.ProofSystem.Logup.Security.InitialSoundness
public import ArkLib.ProofSystem.Sumcheck.Interaction.ComputableSoundness

/-!
# Whole-program soundness of executable scalar weighted LogUp

Against every ordinary whole prover, the actual named uniform Boolean endpoint accepts false
mapped weighted balance with probability at most `(T * 2^n + n * (ell + 3)) / |E|`.
Original table realization is the source promise. No helper honesty, malicious losslessness,
nonvanishing denominator, assumed message kernel, or desired execution equality is a premise.

The cleared numerator is fixed from original data before alpha. Its root error is at most
`(T * 2^n - 1) / |E|`. Off those roots, actual effectful receiver/helper-sender binds precede the
independent joint challenge; residual-TABLE batching costs `n / |E| + 1 / |E|`. Outside the true
initial-relation event, the actual native complete verifier costs `n * (ell + 2) / |E|`.
Terminal authentication adds zero error. The root argument remains valid at denominator poles.

Balance and false balance refer explicitly to fibers AFTER the scalar ring map. Lookup counts,
tuple compression, honest completeness and prover resource accounting are separate consumers.
-/

@[expose] public section

namespace Logup.Interaction
open _root_.Interaction.Oracle OracleComp OracleSpec CompPoly
open scoped BigOperators ProbabilityTheory ENNReal
variable {B E : Type} [CommRing B] [Field E]

private theorem boolean_domain_perm :
    ([0, 1] : List E).Perm (Finset.univ.map (boolEmbedding E)).toList := by
  classical
  apply List.perm_of_nodup_nodup_toFinset_eq (by simp) (Finset.nodup_toList _)
  rw [Finset.toList_toFinset]
  ext x
  simp [Fin.exists_fin_two, eq_comm]

variable [DecidableEq E] [Fintype E] [SampleableType E] [BEq E] [LawfulBEq E]

set_option backward.isDefEq.respectTransparency false in
/-- With alpha and helpers fixed before the joint draw, the actual effectful joint response and
complete native suffix incur only the initial-relation error plus native Sumcheck error. -/
private theorem prob_joint_native_le (f : B →+* E) (n T ell : Nat) (cfg : Config n T ell)
    (data : Fin 2 × Fin T → CMlPolynomialEval B n) (alpha : E)
    (halpha : (clearedBalancePolynomial f data).eval alpha ≠ 0)
    (A : PFunctor.{0, 0}) (inputView : VirtualOracle (ofPFunctor A) (inputFamily f n T))
    (impl : QueryImpl (ofPFunctor A) Id)
    (hinput : inputView.eval impl = (inputFamily f n T).behaviorOfRealizations data)
    (helpers : Vector (CMlPolynomialEval E n) (T ⌈/⌉ ell))
    (next : ((Fin n → E) × (Fin (T ⌈/⌉ ell) → E)) → ProbComp
      (Prover.Strategy unifSpec (Sumcheck.Interaction.Computable.protocol E (ell + 2) n).tree
        (Sumcheck.Interaction.Computable.protocol E (ell + 2) n).roles (fun _ ↦ Unit))) :
    Pr{let accepted ← (do
      let joint ← $ᵗ ((Fin n → E) × (Fin (T ⌈/⌉ ell) → E))
      let continuation ← next joint
      Sumcheck.Interaction.Computable.executeWithFinalCheck E n (ell + 2) unifSpec ($ᵗ E) [0, 1]
        n 0 (Nat.zero_add n) (family (E := E) n ell).spec.toPFunctor
        (VirtualOracle.id (family (E := E) n ell)) (zeroStatement E n)
        ((qView f n T (T ⌈/⌉ ell) cfg.groups alpha joint.1 joint.2 ell A inputView).eval
          (Access.extendImpl A (helperInterface (E := E) n (T ⌈/⌉ ell)) impl helpers))
        continuation)}[accepted = true] ≤
      (n : ℝ≥0∞) / Fintype.card E + (Fintype.card E : ℝ≥0∞)⁻¹ +
        (n : ℝ≥0∞) * (ell + 2 : Nat) / Fintype.card E := by
  have hsplit := prEvent_bind_le_prEvent_add
    ($ᵗ ((Fin n → E) × (Fin (T ⌈/⌉ ell) → E)))
    (fun joint ↦ do
      let continuation ← next joint
      Sumcheck.Interaction.Computable.executeWithFinalCheck E n (ell + 2) unifSpec ($ᵗ E) [0, 1]
        n 0 (Nat.zero_add n) (family (E := E) n ell).spec.toPFunctor
        (VirtualOracle.id (family (E := E) n ell)) (zeroStatement E n)
        ((qView f n T (T ⌈/⌉ ell) cfg.groups alpha joint.1 joint.2 ell A inputView).eval
          (Access.extendImpl A (helperInterface (E := E) n (T ⌈/⌉ ell)) impl helpers))
        continuation)
    (fun joint ↦ Sumcheck.Interaction.MultivariateRound.closedRelation E n (ell + 2)
      (boolEmbedding E) 0 ⟨zeroStatement E n,
        (qView f n T (T ⌈/⌉ ell) cfg.groups alpha joint.1 joint.2 ell A inputView).eval
          (Access.extendImpl A (helperInterface (E := E) n (T ⌈/⌉ ell)) impl helpers)⟩)
    (fun accepted ↦ accepted = true)
    (ε := (n : ℝ≥0∞) * (ell + 2 : Nat) / Fintype.card E) ?_
  · exact hsplit.trans (add_le_add
      (prob_initial_relation_le cfg f data alpha halpha A inputView impl hinput helpers) le_rfl)
  · intro joint hfalse
    apply prEvent_bind_le_of_forall_le (next joint)
    intro continuation
    apply Sumcheck.Interaction.Computable.executeWithFinalCheck_soundness n (ell + 2) E
      (boolEmbedding E) [0, 1] boolean_domain_perm n 0 (Nat.zero_add n)
      (family (E := E) n ell).spec.toPFunctor (VirtualOracle.id (family (E := E) n ell))
      (zeroStatement E n)
      ((qView f n T (T ⌈/⌉ ell) cfg.groups alpha joint.1 joint.2 ell A inputView).eval
        (Access.extendImpl A (helperInterface (E := E) n (T ⌈/⌉ ell)) impl helpers))
      continuation (qPolynomial f n T (T ⌈/⌉ ell) cfg.groups alpha joint.1 joint.2 ell
        cfg.length_group_le data helpers)
    · rw [VirtualOracle.eval_id]
      exact qView_realizes f n T (T ⌈/⌉ ell) cfg.groups alpha joint.1 joint.2 ell
        cfg.length_group_le A inputView impl data hinput helpers
    · simpa only [VirtualOracle.eval_id, Fin.mk_zero] using hfalse

set_option backward.isDefEq.respectTransparency false in
/-- Every ordinary whole prover accepting false mapped weighted balance in the actual uniform
endpoint satisfies the complete scalar error bound. Private output may depend on the full path. -/
theorem uniformExecute_soundness (f : B →+* E) (n T ell : Nat) (cfg : Config n T ell)
    (A : PFunctor.{0, 0}) (inputView : VirtualOracle (ofPFunctor A) (inputFamily f n T))
    (impl : QueryImpl (ofPFunctor A) Id)
    (data : Fin 2 × Fin T → CMlPolynomialEval B n)
    (hinput : inputView.eval impl = (inputFamily f n T).behaviorOfRealizations data)
    {OutP : (protocol E n (T ⌈/⌉ ell) ell).tree.ExecutionPath → Type}
    (prover : Prover.Strategy unifSpec (protocol E n (T ⌈/⌉ ell) ell).tree
      (protocol E n (T ⌈/⌉ ell) ell).roles OutP)
    (hfalse : ∃ v,
      ((Finset.univ : Finset (Fin n → Fin 2)).product (Finset.univ : Finset (Fin T))).sumFiber
        (fun p ↦ f ((data (0, p.2)).get (finFunctionFinEquiv p.1)))
        (fun p ↦ f ((data (1, p.2)).get (finFunctionFinEquiv p.1))) v ≠ 0) :
    Pr{let accepted ← uniformExecute f n T ell cfg A inputView impl prover}[accepted = true] ≤
      ((T * 2 ^ n + n * (ell + 3) : Nat) : ℝ≥0∞) / Fintype.card E := by
  have hP : clearedBalancePolynomial f data ≠ 0 := by
    intro hzero
    obtain ⟨v, hv⟩ := hfalse
    exact hv ((clearedBalancePolynomial_eq_zero_iff f data).mp hzero v)
  have hroot : Pr{let alpha ← $ᵗ E}[(clearedBalancePolynomial f data).eval alpha = 0] ≤
      ((T * 2 ^ n - 1 : Nat) : ℝ≥0∞) / Fintype.card E := by
    simpa only [Polynomial.eval_zero] using Probability.prob_polynomial_eval_eq_le
      (q := 0) hP (natDegree_clearedBalancePolynomial_le f data)
      (show (0 : Polynomial E).natDegree ≤ T * 2 ^ n - 1 by simp)
  rw [uniformExecute, execute_eq_prefix_binds]
  refine (prEvent_bind_le_prEvent_add _ _
    (fun alpha ↦ (clearedBalancePolynomial f data).eval alpha = 0)
    (fun accepted ↦ accepted = true)
    (ε := (n : ℝ≥0∞) / Fintype.card E + (Fintype.card E : ℝ≥0∞)⁻¹ +
      (n : ℝ≥0∞) * (ell + 2 : Nat) / Fintype.card E) ?_).trans ?_
  · intro alpha halpha
    apply prEvent_bind_le_of_forall_le
    intro helperStage
    apply prEvent_bind_le_of_forall_le helperStage
    intro sent
    exact prob_joint_native_le f n T ell cfg data alpha halpha A inputView impl hinput
      sent.1 sent.2
  · apply (add_le_add hroot le_rfl).trans
    have hD : 0 < T * 2 ^ n := Nat.mul_pos cfg.total_pos (pow_pos (by decide) n)
    have hNat : T * 2 ^ n - 1 + n + 1 + n * (ell + 2) = T * 2 ^ n + n * (ell + 3) := by
      simp only [Nat.mul_add] at *
      omega
    apply le_of_eq
    calc
      ((T * 2 ^ n - 1 : Nat) : ℝ≥0∞) / Fintype.card E +
          ((n : ℝ≥0∞) / Fintype.card E + (Fintype.card E : ℝ≥0∞)⁻¹ +
            (n : ℝ≥0∞) * (ell + 2 : Nat) / Fintype.card E)
          = ((T * 2 ^ n - 1 + n + 1 + n * (ell + 2) : Nat) : ℝ≥0∞) /
            Fintype.card E := by
              push_cast
              simp only [ENNReal.add_div, one_div]
              ac_rfl
      _ = _ := by rw [hNat]

end Logup.Interaction

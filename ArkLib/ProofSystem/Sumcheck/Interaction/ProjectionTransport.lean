/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.ProofSystem.Sumcheck.Interaction.Projection

/-! # Transport of multivariate sum-check round relations -/

@[expose] public section

namespace Sumcheck.Interaction.SingleRound

open OracleComp OracleSpec Polynomial Finset
open _root_.Interaction.Oracle
open Spec.SingleRound

noncomputable section

variable (R : Type) [CommSemiring R]

variable (n deg : ℕ) {m : ℕ} (D : Fin m ↪ R)

/-- The projected polynomial satisfies the univariate sum claim of the input round. -/
theorem projected_sum_of_relationRound (i : Fin n)
    (stmt : Spec.StatementRound R n i.castSucc) (p : Spec.OracleStatement R n deg ())
    (h : ((stmt, fun _ => p), ()) ∈ Spec.relationRound R n deg D i.castSucc) :
    ((univ.map D).toList.map (fun x =>
      (projectedRoundPolynomial R n deg D i stmt.challenges p).val.eval x)).sum =
        stmt.target := by
  cases n with
  | zero => exact Fin.elim0 i
  | succ n =>
    have hlist := Multiset.sum_map_toList (univ.map D).1
      (fun a => (projectedRoundPolynomial R (n + 1) deg D i stmt.challenges p).val.eval a)
    change _ = ∑ a ∈ univ.map D, _ at hlist
    apply hlist.trans
    simp only [projectedRoundPolynomial, Polynomial.eval_finsetSum]
    refine (MvPolynomial.sum_eval_evalExcept_append (l := n - i) i stmt.challenges
      (fun _ => univ.map D) (by omega) p.val).trans ?_
    change (∑ z ∈ (univ.map D) ^ᶠ (n + 1 - i.val),
      p.val.eval (Fin.append stmt.challenges z ∘ Fin.cast (by simp))) = _ at h
    rw [Fin.sum_piFinset_cast _ (show n + 1 - i.val = (n - i.val) + 1 by omega)] at h
    rw [← h]
    apply Finset.sum_congr rfl
    intro x _
    congr 1
    rw [Fin.append_cast_right]
    rfl

/-- The projected sum claim and the current multivariate relation are equivalent. -/
theorem projected_sum_iff_relationRound (i : Fin n)
    (stmt : Spec.StatementRound R n i.castSucc) (p : Spec.OracleStatement R n deg ()) :
    ((univ.map D).toList.map (fun x =>
      (projectedRoundPolynomial R n deg D i stmt.challenges p).val.eval x)).sum =
        stmt.target ↔ ((stmt, fun _ => p), ()) ∈ Spec.relationRound R n deg D i.castSucc := by
  let total := ∑ x ∈ (univ.map D) ^ᶠ (n - i.val),
    p.val.eval (Fin.append stmt.challenges x ∘ Fin.cast (by simp))
  have h := projected_sum_of_relationRound R n deg D i
    ⟨total, stmt.challenges⟩ p (by rfl)
  change _ = total at h
  change _ = stmt.target ↔ total = stmt.target
  rw [h]

/-- Updating the target to the projected evaluation establishes the next multivariate round. -/
theorem relationRound_projected_output (i : Fin n)
    (stmt : Spec.StatementRound R n i.castSucc) (p : Spec.OracleStatement R n deg ())
    (r : R) :
    (((⟨(projectedRoundPolynomial R n deg D i stmt.challenges p).val.eval r,
      Fin.snoc stmt.challenges r⟩ : Spec.StatementRound R n i.succ), fun _ => p), ()) ∈
        Spec.relationRound R n deg D i.succ := by
  cases n with
  | zero => exact Fin.elim0 i
  | succ n =>
    change _ = (∑ x ∈ (univ.map D) ^ᶠ (n - i),
      p.val.evalExcept i (Fin.append stmt.challenges x ∘ Fin.cast (by simp; omega))).eval r
    simp only [Polynomial.eval_finsetSum, MvPolynomial.eval_evalExcept_append]
    change (∑ x ∈ (univ.map D) ^ᶠ (n + 1 - (i + 1)),
      p.val.eval (Fin.append (Fin.snoc stmt.challenges r) x ∘ Fin.cast (by simp; omega))) = _
    rw [Fin.sum_piFinset_cast (univ.map D)
      (show n + 1 - (i + 1) = n - i by omega)]
    apply Finset.sum_congr rfl
    intro x _
    congr 1
    rw [Fin.append_cast_right]
    rfl

/-- For an arbitrary next target, the successor relation is exactly projected evaluation. -/
theorem relationRound_output_iff (i : Fin n)
    (stmt : Spec.StatementRound R n i.castSucc) (p : Spec.OracleStatement R n deg ())
    (r target : R) :
    (((⟨target, Fin.snoc stmt.challenges r⟩ : Spec.StatementRound R n i.succ),
      fun _ => p), ()) ∈ Spec.relationRound R n deg D i.succ ↔
      (projectedRoundPolynomial R n deg D i stmt.challenges p).val.eval r = target := by
  have h := relationRound_projected_output R n deg D i stmt p r
  change (∑ x ∈ (univ.map D) ^ᶠ (n - i.succ.val),
    p.val.eval (Fin.append (Fin.snoc stmt.challenges r) x ∘ Fin.cast (by simp))) = _ at h
  change (∑ x ∈ (univ.map D) ^ᶠ (n - i.succ.val),
    p.val.eval (Fin.append (Fin.snoc stmt.challenges r) x ∘ Fin.cast (by simp))) = target ↔ _
  rw [h]

/-- Actual virtual-input execution is complete from the multivariate round relation. -/
theorem executeCore_projected_of_relationRound [DecidableEq R] {ι : Type}
    (ambient : OracleSpec ι) (i : Fin n) (stmt : Spec.StatementRound R n i.castSucc)
    (p : Spec.OracleStatement R n deg ()) (r : R)
    (h : ((stmt, fun _ => p), ()) ∈ Spec.relationRound R n deg D i.castSucc) :
    (fun run => run.closed.map (closedOutputRelation R deg)) <$>
      executeCore (claimReduction R deg ambient (univ.map D).toList r)
        (projectedInput R n deg D i stmt p) stmt.target
        (projectedRoundPolynomial R n deg D i stmt.challenges p) = pure (some True) := by
  exact executeCore_projected R n deg D ambient i stmt p r
    (projected_sum_of_relationRound R n deg D i stmt p h)

end
end Sumcheck.Interaction.SingleRound

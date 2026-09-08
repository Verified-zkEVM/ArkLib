/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.ProofSystem.Sumcheck.Interaction.Projection

/-! # Transport of multivariate sum-check round relations -/

namespace Sumcheck.Interaction.SingleRound

open OracleComp OracleSpec Polynomial Finset
open _root_.Interaction.Oracle
open Spec.SingleRound

noncomputable section

variable (R : Type) [CommSemiring R]

/-- Separate the first coordinate of a finite Cartesian-power sum. -/
theorem sum_cube_cons (S : Finset R) (k : ℕ) (f : (Fin (k + 1) → R) → R) :
    ∑ z ∈ S ^ᶠ (k + 1), f z = ∑ a ∈ S, ∑ y ∈ S ^ᶠ k, f (Fin.cons a y) := by
  classical
  rw [← Finset.sum_product S (S ^ᶠ k) (fun z => f (Fin.cons z.1 z.2))]
  apply Finset.sum_nbij' (fun z => (z 0, Fin.tail z))
    (fun z => Fin.cons z.1 z.2)
  · intro z hz
    simpa [Finset.mem_product, Fintype.mem_piFinset, Fin.forall_fin_succ, Fin.tail] using hz
  · intro z hz
    simpa [Finset.mem_product, Fintype.mem_piFinset, Fin.forall_fin_succ] using hz
  · intro z hz
    exact Fin.cons_self_tail z
  · intro z hz
    simp
  · intro z hz
    simp

omit [CommSemiring R] in
/-- Inserting the round challenge extends the fixed prefix by one coordinate. -/
theorem insertNth_roundSuffix (n : ℕ) (i : Fin (n + 1))
    (c : Fin i.castSucc → R) (x : Fin (n - i) → R) (r : R) :
    Fin.insertNth i r (roundSuffix R n i c x) =
      Fin.append (Fin.snoc c r) x ∘ Fin.cast (by simp; omega) := by
  funext j
  rcases lt_trichotomy j i with h | h | h
  · rw [Fin.insertNth_apply_below h]
    simp [roundSuffix, Fin.append, Fin.addCases, Fin.snoc,
      show j.val < i.val by exact h, le_of_lt h]
    congr 1
  · subst j
    simp [Fin.append, Fin.addCases, Fin.snoc]
  · rw [Fin.insertNth_apply_above h]
    simp only [roundSuffix, Fin.val_castSucc, Fin.append, Function.comp_apply,
      Fin.addCases, Fin.val_cast, Fin.val_pred, show ¬j.val - 1 < i.val by omega,
      ↓reduceDIte, Fin.cast_cast, eq_rec_constant, show ¬j.val < i.val + 1 by omega]
    congr 1
    apply Fin.ext
    simp
    omega

variable (n deg : ℕ) {m : ℕ} (D : Fin m ↪ R)

/-- Evaluation of the projected polynomial is the sum with the challenge prefix extended. -/
theorem projectedRoundPolynomial_eval (i : Fin (n + 1))
    (c : Fin i.castSucc → R) (p : Spec.OracleStatement R (n + 1) deg ()) (r : R) :
    (projectedRoundPolynomial R (n + 1) deg D i c p).val.eval r =
      ∑ x ∈ (univ.map D) ^ᶠ (n - i),
        p.val.eval (Fin.append (Fin.snoc c r) x ∘ Fin.cast (by simp; omega)) := by
  change Polynomial.eval r (∑ x ∈ (univ.map D) ^ᶠ (n - i),
    Polynomial.map (MvPolynomial.eval (roundSuffix R n i c x))
      (MvPolynomial.finSuccEquivNth R i p.val)) = _
  rw [Polynomial.eval_finsetSum]
  apply Finset.sum_congr rfl
  intro x hx
  rw [← MvPolynomial.eval_eq_eval_mv_eval_finSuccEquivNth, insertNth_roundSuffix]

/-- Reindexing a Cartesian-power sum along equality of its dimensions. -/
theorem sum_cube_cast (S : Finset R) {k l : ℕ} (h : k = l)
    (f : (Fin k → R) → R) :
    ∑ x ∈ S ^ᶠ k, f x = ∑ x ∈ S ^ᶠ l, f (x ∘ Fin.cast h) := by
  subst l
  rfl

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
    simp_rw [projectedRoundPolynomial_eval]
    change (∑ z ∈ (univ.map D) ^ᶠ (n + 1 - i.val),
      p.val.eval (Fin.append stmt.challenges z ∘ Fin.cast (by simp))) = _ at h
    rw [sum_cube_cast R _ (show n + 1 - i.val = (n - i.val) + 1 by omega),
      sum_cube_cons] at h
    rw [← h]
    apply Finset.sum_congr rfl
    intro a ha
    apply Finset.sum_congr rfl
    intro x hx
    congr 1
    rw [Fin.append_left_snoc, Fin.append_cast_right]
    rfl

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
    change (∑ x ∈ (univ.map D) ^ᶠ (n + 1 - (i.val + 1)),
      p.val.eval (Fin.append (Fin.snoc stmt.challenges r) x ∘ Fin.cast (by simp; omega))) = _
    rw [sum_cube_cast R _ (show n + 1 - (i.val + 1) = n - i.val by omega)]
    refine Eq.trans ?_ (projectedRoundPolynomial_eval R n deg D i stmt.challenges p r).symm
    apply Finset.sum_congr rfl
    intro x hx
    congr 1
    rw [Fin.append_cast_right]
    rfl

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

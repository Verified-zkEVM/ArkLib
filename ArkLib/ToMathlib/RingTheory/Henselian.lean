/-
Copyright (c) 2021 Johan Commelin. All rights reserved.
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Thomas Coratger
-/
module

public import Mathlib.RingTheory.Henselian
public import Mathlib.Tactic.LinearCombination

/-!
# Hensel's lemma without monicity in adically complete rings

In an `I`-adically complete ring, a simple root modulo `I` lifts to a root.
The polynomial need not be monic.
The lift is unique as soon as `I` lies in the Jacobson radical.

Newton's iteration `b ↦ b - f(b) / f'(b)` converges `I`-adically to the root.
The proof adapts Johan Commelin's proof in `Mathlib.RingTheory.Henselian`,
where the Newton iteration also works for arbitrary polynomials.
The lemma is intended for upstreaming to Mathlib.

## Main statements

* `IsAdicComplete.exists_isRoot_sub_mem`: a simple root modulo `I` lifts to a root.
* `Polynomial.eq_of_isRoot_of_sub_mem`: two such roots are equal when `I` lies in the
  Jacobson radical. This generalizes `IsLocalRing.eq_of_eval_eq_zero_of_not_isUnit_sub`,
  the case where `I` is the maximal ideal of a local ring.
* `IsAdicComplete.existsUnique_isRoot_sub_mem`: the lift is unique.
-/

@[expose] public section

open Polynomial

/-- Let `I` lie in the Jacobson radical of `R`, and let `f` be a polynomial over `R`.

Suppose `f'(a₀)` is a unit modulo `I`.
Then `f` has at most one root `a` with `a - a₀ ∈ I`. -/
theorem Polynomial.eq_of_isRoot_of_sub_mem {R : Type*} [CommRing R] {I : Ideal R}
    (hI : I ≤ Ring.jacobson R) {f : R[X]} {a₀ a b : R}
    (h₂ : IsUnit (Ideal.Quotient.mk I (f.derivative.eval a₀)))
    (ha : f.IsRoot a) (ha₀ : a - a₀ ∈ I) (hb : f.IsRoot b) (hb₀ : b - a₀ ∈ I) : a = b := by
  have := isLocalHom_of_le_jacobson hI
  obtain ⟨c, hc⟩ := exists_mul_sq_add_linear_part_eq_eval_add f b (a - b)
  rw [add_sub_cancel, ha.eq_zero, hb.eq_zero, add_zero] at hc
  -- The factor next to `a - b` is congruent to `f'(a₀)` modulo `I`, hence a unit.
  have hu : IsUnit (c * (a - b) + f.derivative.eval b) := by
    refine IsUnit.of_map (Ideal.Quotient.mk I) _ ?_
    convert h₂ using 1
    rw [Ideal.Quotient.eq]
    have hab : a - b ∈ I := by simpa using I.sub_mem ha₀ hb₀
    have hb' := SModEq.sub_mem.mp ((SModEq.sub_mem.mpr hb₀).eval f.derivative)
    convert I.add_mem (I.mul_mem_left c hab) hb' using 1
    ring
  rw [← sub_eq_zero, ← hu.mul_right_eq_zero]
  linear_combination hc

namespace IsAdicComplete

variable {R : Type*} [CommRing R] {I : Ideal R} [IsAdicComplete I R]

/-- Let `R` be `I`-adically complete and `f` a polynomial over `R`, not necessarily monic.

If `f(a₀) ∈ I` and `f'(a₀)` is a unit modulo `I`, then `f` has a root `a` with `a - a₀ ∈ I`. -/
theorem exists_isRoot_sub_mem (f : R[X]) (a₀ : R) (h₁ : f.eval a₀ ∈ I)
    (h₂ : IsUnit (Ideal.Quotient.mk I (f.derivative.eval a₀))) :
    ∃ a : R, f.IsRoot a ∧ a - a₀ ∈ I := by
  classical
  let f' := derivative f
  let c : ℕ → R := fun n => Nat.recOn n a₀ fun _ b => b - f.eval b * Ring.inverse (f'.eval b)
  have hc : ∀ n, c (n + 1) = c n - f.eval (c n) * Ring.inverse (f'.eval (c n)) := fun n => rfl
  have hc_mod : ∀ n, c n ≡ a₀ [SMOD I] := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => ?_
    rw [hc, sub_eq_add_neg, ← add_zero a₀]
    refine ih.add ?_
    rw [SModEq.zero, Ideal.neg_mem_iff]
    refine I.mul_mem_right _ ?_
    rw [← SModEq.zero] at h₁ ⊢
    exact (ih.eval f).trans h₁
  have hf'c : ∀ n, IsUnit (f'.eval (c n)) := by
    intro n
    have := isLocalHom_of_le_jacobson (IsAdicComplete.le_jacobson I)
    apply IsUnit.of_map (Ideal.Quotient.mk I)
    convert h₂ using 1
    exact SModEq.def.mp ((hc_mod n).eval _)
  have hfcI : ∀ n, f.eval (c n) ∈ I ^ (n + 1) := by
    intro n
    induction n with
    | zero => rw [zero_add, pow_one]; exact h₁
    | succ n ih => ?_
    rw [← taylor_eval_sub (c n), hc, sub_eq_add_neg, sub_eq_add_neg,
      add_neg_cancel_comm]
    rw [eval_eq_sum, sum_over_range' _ _ _ (lt_add_of_pos_right _ zero_lt_two), ←
      Finset.sum_range_add_sum_Ico _ (Nat.le_add_left _ _)]
    swap
    · intro i
      rw [zero_mul]
    refine Ideal.add_mem _ ?_ ?_
    · rw [← one_add_one_eq_two, Finset.sum_range_succ, Finset.range_one, Finset.sum_singleton,
        taylor_coeff_zero, taylor_coeff_one, pow_zero, pow_one, mul_one, mul_neg,
        mul_left_comm, Ring.mul_inverse_cancel _ (hf'c n), mul_one, add_neg_cancel]
      exact Ideal.zero_mem _
    · refine Submodule.sum_mem _ ?_
      simp only [Finset.mem_Ico]
      rintro i ⟨h2i, _⟩
      have aux : n + 2 ≤ i * (n + 1) := by trans 2 * (n + 1) <;> nlinarith only [h2i]
      refine Ideal.mul_mem_left _ _ (Ideal.pow_le_pow_right aux ?_)
      rw [pow_mul']
      exact Ideal.pow_mem_pow ((Ideal.neg_mem_iff _).2 <| Ideal.mul_mem_right _ _ ih) _
  have aux : ∀ m n, m ≤ n → c m ≡ c n [SMOD (I ^ m • ⊤ : Ideal R)] := by
    intro m n hmn
    rw [← Ideal.one_eq_top, Ideal.smul_eq_mul, mul_one]
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
    clear hmn
    induction k with
    | zero => rw [add_zero]
    | succ k ih => ?_
    rw [← add_assoc, hc, ← add_zero (c m), sub_eq_add_neg]
    refine ih.add ?_
    symm
    rw [SModEq.zero, Ideal.neg_mem_iff]
    refine Ideal.mul_mem_right _ _ (Ideal.pow_le_pow_right ?_ (hfcI _))
    rw [add_assoc]
    exact le_self_add
  obtain ⟨a, ha⟩ := IsPrecomplete.prec' c (aux _ _)
  refine ⟨a, ?_, ?_⟩
  · suffices ∀ n, f.eval a ≡ 0 [SMOD (I ^ n • ⊤ : Ideal R)] from IsHausdorff.haus' _ this
    intro n
    specialize ha n
    rw [← Ideal.one_eq_top, Ideal.smul_eq_mul, mul_one] at ha ⊢
    refine (ha.symm.eval f).trans ?_
    rw [SModEq.zero]
    exact Ideal.pow_le_pow_right le_self_add (hfcI _)
  · specialize ha (0 + 1)
    rw [hc, pow_one, ← Ideal.one_eq_top, Ideal.smul_eq_mul, mul_one, sub_eq_add_neg] at ha
    rw [← SModEq.sub_mem, ← add_zero a₀]
    refine ha.symm.trans (SModEq.rfl.add ?_)
    rw [SModEq.zero, Ideal.neg_mem_iff]
    exact Ideal.mul_mem_right _ _ h₁

/-- Let `R` be `I`-adically complete and `f` a polynomial over `R`, not necessarily monic.

If `f(a₀) ∈ I` and `f'(a₀)` is a unit modulo `I`, then `f` has exactly one root `a` with
`a - a₀ ∈ I`. -/
theorem existsUnique_isRoot_sub_mem (f : R[X]) (a₀ : R) (h₁ : f.eval a₀ ∈ I)
    (h₂ : IsUnit (Ideal.Quotient.mk I (f.derivative.eval a₀))) :
    ∃! a : R, f.IsRoot a ∧ a - a₀ ∈ I := by
  obtain ⟨a, ha, ha₀⟩ := exists_isRoot_sub_mem f a₀ h₁ h₂
  exact ⟨a, ⟨ha, ha₀⟩, fun b ⟨hb, hb₀⟩ ↦
    eq_of_isRoot_of_sub_mem (le_jacobson I) h₂ hb hb₀ ha ha₀⟩

end IsAdicComplete

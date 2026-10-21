/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.Chebyshev
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Push
public import Mathlib.Tactic.Ring

/-!
# Pairwise-intersection incidence bound

A finite family of sets, each with at least `A` elements and with pairwise intersections of
cardinality at most `D`, satisfies

`|T| * (A² - nD) ≤ n * (A - D)`

when the ambient type has `n` elements and the denominator is positive. The proof is the
elementary Cauchy--Schwarz count extracted from the Reed--Solomon weighted Johnson development at
commit `a5aa2677fee4e3a79d6bb05136631cce4a08587d`. It has no field, polynomial, or geometric
hypotheses.
-/

@[expose] public section

namespace Finset

/-- Exact Cauchy--Schwarz incidence bound for an indexed family of finite sets.

`T` is the finite family of indices and `S x` is the set attached to `x`. The ambient type `ι`
has cardinality `n = Fintype.card ι`. Every family member has at least `A` elements, while two
members with distinct indices intersect in at most `D` elements. The hypotheses `D ≤ A` and
`n * D < A²` make the agreement gap nonnegative and the Johnson denominator positive. -/
theorem card_mul_sq_sub_card_mul_le_of_inter_card_le
    -- The ambient finite type and the type indexing the family need not carry other structure.
    {κ ι : Type*} [Fintype ι] [DecidableEq ι]
    -- `T` chooses the family members and `S` assigns their finite subsets of the ambient type.
    (T : Finset κ) (S : κ → Finset ι) (A D : ℕ)
    -- The integral gap and denominator are in their natural mathematical range.
    (hDA : D ≤ A) (hpositive : Fintype.card ι * D < A * A)
    -- Each member is large, while distinct indexed members have small pairwise intersection.
    (hclose : ∀ x ∈ T, A ≤ (S x).card)
    (hpair : ∀ x ∈ T, ∀ y ∈ T, x ≠ y → ((S x) ∩ (S y)).card ≤ D) :
    -- This exact integral inequality is the division-free Johnson counting conclusion.
    T.card * (A * A - Fintype.card ι * D) ≤ Fintype.card ι * (A - D) := by
  classical
  let L : ℝ := T.card
  let n : ℝ := Fintype.card ι
  let a : ℝ := A
  let d : ℝ := D
  let Z : ℝ := ∑ x ∈ T, ((S x).card : ℝ)
  let Q : ℝ := ∑ x ∈ T, ∑ y ∈ T, (((S x) ∩ (S y)).card : ℝ)
  have hsum : Z = ∑ i : ι, ((T.filter fun x => i ∈ S x).card : ℝ) := by
    dsimp only [Z]
    calc
      (∑ x ∈ T, ((S x).card : ℝ)) =
          ∑ x ∈ T, ∑ i : ι, if i ∈ S x then (1 : ℝ) else 0 := by
            apply Finset.sum_congr rfl
            intro x hx
            symm
            simp
      _ = ∑ i : ι, ∑ x ∈ T, if i ∈ S x then (1 : ℝ) else 0 := by
            rw [Finset.sum_comm]
      _ = ∑ i : ι, ((T.filter fun x => i ∈ S x).card : ℝ) := by
            apply Finset.sum_congr rfl
            intro i hi
            exact Finset.sum_boole (R := ℝ) (fun x => i ∈ S x) T
  have hsquares :
      (∑ i : ι, ((T.filter fun x => i ∈ S x).card : ℝ) ^ 2) = Q := by
    dsimp only [Q]
    symm
    calc
      (∑ x ∈ T, ∑ y ∈ T, (((S x) ∩ (S y)).card : ℝ)) =
          ∑ x ∈ T, ∑ y ∈ T, ∑ i : ι,
            if i ∈ S x ∩ S y then (1 : ℝ) else 0 := by
              apply Finset.sum_congr rfl
              intro x hx
              apply Finset.sum_congr rfl
              intro y hy
              have h := Finset.sum_boole (R := ℝ)
                (fun i : ι => i ∈ S x ∩ S y) Finset.univ
              have hf : (Finset.univ.filter fun i : ι => i ∈ S x ∩ S y) = S x ∩ S y := by
                ext i
                simp
              rw [hf] at h
              exact h.symm
      _ = ∑ x ∈ T, ∑ i : ι, ∑ y ∈ T,
            if i ∈ S x ∩ S y then (1 : ℝ) else 0 := by
              apply Finset.sum_congr rfl
              intro x hx
              rw [Finset.sum_comm]
      _ = ∑ i : ι, ∑ x ∈ T, ∑ y ∈ T,
            if i ∈ S x ∩ S y then (1 : ℝ) else 0 := by
              rw [Finset.sum_comm]
      _ = ∑ i : ι, ∑ x ∈ T, ∑ y ∈ T,
            (if i ∈ S x then (1 : ℝ) else 0) *
              (if i ∈ S y then (1 : ℝ) else 0) := by
              apply Finset.sum_congr rfl
              intro i hi
              apply Finset.sum_congr rfl
              intro x hx
              apply Finset.sum_congr rfl
              intro y hy
              simp only [Finset.mem_inter]
              by_cases hix : i ∈ S x <;> by_cases hiy : i ∈ S y <;> simp [hix, hiy]
      _ = ∑ i : ι,
            (∑ x ∈ T, if i ∈ S x then (1 : ℝ) else 0) ^ 2 := by
              apply Finset.sum_congr rfl
              intro i hi
              rw [sq, Finset.sum_mul_sum]
      _ = ∑ i : ι, ((T.filter fun x => i ∈ S x).card : ℝ) ^ 2 := by
              apply Finset.sum_congr rfl
              intro i hi
              rw [Finset.sum_boole (R := ℝ) (fun x => i ∈ S x) T]
  have hZlower : L * a ≤ Z := by
    have h := Finset.sum_le_sum (fun x hx => show (A : ℝ) ≤ (S x).card by
      exact_mod_cast hclose x hx)
    simpa [L, a, Z] using h
  have hQupper : Q ≤ Z + L * (L - 1) * d := by
    have hrow : ∀ x ∈ T,
        (∑ y ∈ T, (((S x) ∩ (S y)).card : ℝ)) ≤
          (S x).card + (L - 1) * d := by
      intro x hx
      rw [(Finset.add_sum_erase T
        (fun y => (((S x) ∩ (S y)).card : ℝ)) hx).symm]
      have herase :
          (∑ y ∈ T.erase x, (((S x) ∩ (S y)).card : ℝ)) ≤ (L - 1) * d := by
        have hterms : ∀ y ∈ T.erase x,
            ((((S x) ∩ (S y)).card : ℕ) : ℝ) ≤ d := by
          intro y hy
          dsimp only [d]
          exact_mod_cast hpair x hx y (Finset.mem_of_mem_erase hy)
            (Ne.symm (Finset.ne_of_mem_erase hy))
        have h := Finset.sum_le_card_nsmul (T.erase x)
          (fun y => (((S x) ∩ (S y)).card : ℝ)) d hterms
        rw [nsmul_eq_mul] at h
        have hcard : ((T.erase x).card : ℝ) = L - 1 := by
          rw [Finset.card_erase_of_mem hx]
          have hone : 1 ≤ T.card := Finset.card_pos.mpr ⟨x, hx⟩
          push_cast [Nat.cast_sub hone]
          simp [L]
        simpa [hcard] using h
      simpa using add_le_add_left herase ((S x).card : ℝ)
    calc
      Q ≤ ∑ x ∈ T, (((S x).card : ℝ) + (L - 1) * d) := by
        exact Finset.sum_le_sum hrow
      _ = Z + L * (L - 1) * d := by
        simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
        simp [L, Z]
        ring
  have hCauchy : Z ^ 2 ≤ n * Q := by
    have h := sq_sum_le_card_mul_sum_sq
      (s := (Finset.univ : Finset ι))
      (f := fun i => ((T.filter fun x => i ∈ S x).card : ℝ))
    rw [← hsum, hsquares] at h
    simpa [n] using h
  have hLnonneg : 0 ≤ L := by positivity
  have hAnonneg : 0 ≤ a := by positivity
  have hnnonneg : 0 ≤ n := by positivity
  have hdnonneg : 0 ≤ d := by positivity
  have hreal : L * (a ^ 2 - n * d) ≤ n * (a - d) := by
    by_cases hLzero : L = 0
    · have hda : d ≤ a := by
        dsimp only [d, a]
        exact_mod_cast hDA
      rw [hLzero, zero_mul]
      exact mul_nonneg hnnonneg (sub_nonneg.mpr hda)
    have hLpos : 0 < L := lt_of_le_of_ne hLnonneg (Ne.symm hLzero)
    by_cases hsmall : L * a ≤ n
    · have hLone : 1 ≤ L := by
        have : 1 ≤ T.card := Nat.one_le_iff_ne_zero.mpr (by
          intro h
          apply hLzero
          simp [L, h])
        dsimp only [L]
        exact_mod_cast this
      have hfirst : 0 ≤ a * (n - L * a) :=
        mul_nonneg hAnonneg (sub_nonneg.mpr hsmall)
      have hsecond : 0 ≤ n * d * (L - 1) :=
        mul_nonneg (mul_nonneg hnnonneg hdnonneg) (sub_nonneg.mpr hLone)
      nlinarith only [hsmall, hfirst, hsecond]
    · have hlarge : n < L * a := lt_of_not_ge hsmall
      have hmono : (L * a) ^ 2 - n * (L * a) ≤ Z ^ 2 - n * Z := by
        have hzsub : 0 ≤ Z - L * a := sub_nonneg.mpr hZlower
        have hzsum : 0 ≤ Z + L * a - n := by nlinarith
        have hfactor : 0 ≤ (Z - L * a) * (Z + L * a - n) :=
          mul_nonneg hzsub hzsum
        nlinarith only [hfactor]
      have hkey : Z ^ 2 - n * Z ≤ n * (L * (L - 1) * d) := by
        calc
          Z ^ 2 - n * Z ≤ n * Q - n * Z := sub_le_sub_right hCauchy _
          _ ≤ n * (Z + L * (L - 1) * d) - n * Z :=
            sub_le_sub_right (mul_le_mul_of_nonneg_left hQupper hnnonneg) _
          _ = n * (L * (L - 1) * d) := by ring
      have hmulgoal :
          L * (L * (a ^ 2 - n * d)) ≤ L * (n * (a - d)) := by
        nlinarith only [hmono.trans hkey]
      exact le_of_mul_le_mul_left hmulgoal hLpos
  have hcastDen :
      ((A * A - Fintype.card ι * D : ℕ) : ℝ) = a ^ 2 - n * d := by
    rw [Nat.cast_sub hpositive.le]
    simp [a, n, d, pow_two]
  have hcastGap : ((A - D : ℕ) : ℝ) = a - d := by
    rw [Nat.cast_sub hDA]
  exact_mod_cast (show
    (T.card : ℝ) * (A * A - Fintype.card ι * D : ℕ) ≤
      (Fintype.card ι : ℝ) * (A - D : ℕ) by
    rw [hcastDen, hcastGap]
    simpa [L, n] using hreal)

end Finset

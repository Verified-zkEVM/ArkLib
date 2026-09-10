/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import ArkLib.ToMathlib.Combinatorics.DiscreteSimplex.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Tactic.Ring
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

/-!
# Exact finite moments of an ordinary simplex

Coordinate splitting gives natural-number sums over `OrdinarySimplex r S`, with its existing
stars-and-bars cardinality. These are finite counting identities, prior to normalization into
expectations. For `d = r + 1` and `C = (S + r).choose r`, the three identities are
`d * sum u_i = S*C`, `d*(d+1) * sum u_i*(u_i-1) = 2*S*(S-1)*C`, and
`d*(d+1) * sum u_i*u_j = S*(S-1)*C` for distinct coordinates. The formulas include budgets zero
and one and impose no lower bound on `S` relative to the dimension.

These are the core moments for a later weighted variance calculation. They do not assert a
continuous-volume approximation or that its finite-size correction meets an optimized constant.
-/

@[expose] public section

namespace DiscreteSimplex

noncomputable section

open scoped BigOperators

private theorem sum_update_add_coordinate {r : ℕ} (u : Fin r → ℕ) (i : Fin r) (b : ℕ) :
    (∑ j, Function.update u i b j) + u i = (∑ j, u j) + b := by
  rw [Finset.sum_update_of_mem (Finset.mem_univ i), Finset.sdiff_singleton_eq_erase]
  have h := Finset.sum_erase_add Finset.univ u (Finset.mem_univ i)
  omega

def splitCoordinate {r S : ℕ} (i : Fin r)
    (p : Σ u : OrdinarySimplex r (S + 1), Fin (u.1 i)) : OrdinarySimplex (r + 1) S :=
  ⟨Fin.lastCases p.2.val (Function.update p.1.1 i (p.1.1 i - (p.2.val + 1))), by
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.lastCases_castSucc, Fin.lastCases_last]
    have hsum := sum_update_add_coordinate p.1.1 i (p.1.1 i - (p.2.val + 1))
    have hbound := p.1.2
    have hlt := p.2.isLt
    omega⟩

def mergeCoordinate {r S : ℕ} (i : Fin r)
    (v : OrdinarySimplex (r + 1) S) : Σ u : OrdinarySimplex r (S + 1), Fin (u.1 i) :=
  ⟨⟨Function.update (fun j ↦ v.1 j.castSucc) i
      (v.1 i.castSucc + v.1 (Fin.last r) + 1), by
      have hsum := sum_update_add_coordinate (fun j ↦ v.1 j.castSucc) i
        (v.1 i.castSucc + v.1 (Fin.last r) + 1)
      have hbound := v.2
      rw [Fin.sum_univ_castSucc] at hbound
      omega⟩,
    ⟨v.1 (Fin.last r), by simp; omega⟩⟩

/-- Marking one of the units in coordinate `i` is equivalent to splitting that coordinate and
removing the marked unit. The new last coordinate records the units preceding the mark. -/
def simplexCoordinateSplitEquiv {r S : ℕ} (i : Fin r) :
    (Σ u : OrdinarySimplex r (S + 1), Fin (u.1 i)) ≃ OrdinarySimplex (r + 1) S where
  toFun := splitCoordinate i
  invFun := mergeCoordinate i
  left_inv p := by
    have hu : (mergeCoordinate i (splitCoordinate i p)).1 = p.1 := by
      apply Subtype.ext
      funext j
      by_cases hji : j = i
      · subst j
        simp only [mergeCoordinate, splitCoordinate, Function.update_self,
          Fin.lastCases_castSucc, Fin.lastCases_last]
        have := p.2.isLt
        omega
      · simp [mergeCoordinate, splitCoordinate, hji]
    apply Sigma.ext hu
    apply (Fin.heq_ext_iff (congrArg (fun u ↦ u.1 i) hu)).mpr
    simp [mergeCoordinate, splitCoordinate]
  right_inv v := by
    apply Subtype.ext
    funext j
    refine Fin.lastCases ?_ (fun j ↦ ?_) j
    · simp [mergeCoordinate, splitCoordinate]
    · by_cases hji : j = i
      · subst j
        simp [mergeCoordinate, splitCoordinate]
      · simp [mergeCoordinate, splitCoordinate]

/-- A coordinate never exceeds the simplex budget. -/
theorem ordinarySimplex_coordinate_le {r S : ℕ} (u : OrdinarySimplex r S) (i : Fin r) :
    u.1 i ≤ S :=
  (Finset.single_le_sum (fun j _ ↦ Nat.zero_le (u.1 j)) (Finset.mem_univ i)).trans u.2

/-- The unnormalized first moment is the cardinality of a simplex with one extra coordinate. -/
theorem sum_simplex_coordinate_succ {r S : ℕ} (i : Fin r) :
    (∑ u : OrdinarySimplex r (S + 1), u.1 i) =
      Fintype.card (OrdinarySimplex (r + 1) S) := by
  simpa only [Fintype.card_sigma, Fintype.card_fin] using
    Fintype.card_congr (simplexCoordinateSplitEquiv (S := S) i)

/-- Division-free first moment. Uniform normalization gives expectation `S / (r + 1)`. -/
theorem simplex_first_moment {r S : ℕ} (i : Fin r) :
    (r + 1) * (∑ u : OrdinarySimplex r S, u.1 i) =
      S * Fintype.card (OrdinarySimplex r S) := by
  cases S with
  | zero =>
    have hz : ∀ u : OrdinarySimplex r 0, u.1 i = 0 :=
      fun u ↦ Nat.eq_zero_of_le_zero (ordinarySimplex_coordinate_le u i)
    simp [hz]
  | succ S =>
    rw [sum_simplex_coordinate_succ, card_ordinarySimplex, card_ordinarySimplex]
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, Nat.mul_comm] using
      Nat.choose_succ_right_eq (S + 1 + r) r

/-- After splitting coordinate `i`, a different coordinate remains unchanged. -/
theorem sum_simplex_mixed_succ {r S : ℕ} (i j : Fin r) (hij : i ≠ j) :
    (∑ u : OrdinarySimplex r (S + 1), u.1 i * u.1 j) =
      ∑ v : OrdinarySimplex (r + 1) S, v.1 j.castSucc := by
  have h := Fintype.sum_equiv (simplexCoordinateSplitEquiv (S := S) i)
    (fun p ↦ p.1.1 j) (fun v ↦ v.1 j.castSucc) (fun p ↦ by
      change p.1.1 j = (splitCoordinate i p).1 j.castSucc
      simp [splitCoordinate, hij.symm])
  simpa [Fintype.sum_sigma, Nat.mul_comm] using h

/-- Splitting one marked unit leaves the sum of the two resulting coordinates. -/
theorem sum_simplex_factorial_succ {r S : ℕ} (i : Fin r) :
    (∑ u : OrdinarySimplex r (S + 1), u.1 i * (u.1 i - 1)) =
      (∑ v : OrdinarySimplex (r + 1) S, v.1 i.castSucc) +
        ∑ v : OrdinarySimplex (r + 1) S, v.1 (Fin.last r) := by
  have h := Fintype.sum_equiv (simplexCoordinateSplitEquiv (S := S) i)
    (fun p ↦ p.1.1 i - 1) (fun v ↦ v.1 i.castSucc + v.1 (Fin.last r)) (fun p ↦ by
      change p.1.1 i - 1 =
        (splitCoordinate i p).1 i.castSucc + (splitCoordinate i p).1 (Fin.last r)
      simp only [splitCoordinate, Fin.lastCases_castSucc,
        Function.update_self, Fin.lastCases_last]
      have := p.2.isLt
      omega)
  simpa [Fintype.sum_sigma, Finset.sum_add_distrib, Nat.mul_comm] using h

/-- Division-free mixed second moment at distinct coordinates. -/
theorem simplex_mixed_moment {r S : ℕ} (i j : Fin r) (hij : i ≠ j) :
    (r + 1) * (r + 2) * (∑ u : OrdinarySimplex r S, u.1 i * u.1 j) =
      S * (S - 1) * Fintype.card (OrdinarySimplex r S) := by
  cases S with
  | zero =>
    have hz : ∀ u : OrdinarySimplex r 0, u.1 i = 0 :=
      fun u ↦ Nat.eq_zero_of_le_zero (ordinarySimplex_coordinate_le u i)
    simp [hz]
  | succ S =>
    have hMass := simplex_first_moment (S := S + 1) i
    rw [sum_simplex_coordinate_succ] at hMass
    have hMoment := simplex_first_moment (S := S) j.castSucc
    rw [sum_simplex_mixed_succ i j hij]
    simp only [Nat.add_sub_cancel]
    calc
      (r + 1) * (r + 2) * (∑ v : OrdinarySimplex (r + 1) S, v.1 j.castSucc) =
          (r + 1) * ((r + 1 + 1) *
            (∑ v : OrdinarySimplex (r + 1) S, v.1 j.castSucc)) := by ring
      _ = (r + 1) * (S * Fintype.card (OrdinarySimplex (r + 1) S)) := by rw [hMoment]
      _ = S * ((r + 1) * Fintype.card (OrdinarySimplex (r + 1) S)) := by ring
      _ = (S + 1) * S * Fintype.card (OrdinarySimplex r (S + 1)) := by rw [hMass]; ring

/-- Division-free second falling-factorial moment. The factor two distinguishes repeated from
distinct coordinates and remains valid at budgets zero and one. -/
theorem simplex_factorial_moment {r S : ℕ} (i : Fin r) :
    (r + 1) * (r + 2) * (∑ u : OrdinarySimplex r S, u.1 i * (u.1 i - 1)) =
      2 * S * (S - 1) * Fintype.card (OrdinarySimplex r S) := by
  cases S with
  | zero =>
    have hz : ∀ u : OrdinarySimplex r 0, u.1 i = 0 :=
      fun u ↦ Nat.eq_zero_of_le_zero (ordinarySimplex_coordinate_le u i)
    simp [hz]
  | succ S =>
    have hMass := simplex_first_moment (S := S + 1) i
    rw [sum_simplex_coordinate_succ] at hMass
    have hMoment := simplex_first_moment (S := S) i.castSucc
    have hLast := simplex_first_moment (S := S) (Fin.last r)
    rw [sum_simplex_factorial_succ i]
    simp only [Nat.add_sub_cancel]
    calc
      (r + 1) * (r + 2) *
          ((∑ v : OrdinarySimplex (r + 1) S, v.1 i.castSucc) +
            ∑ v : OrdinarySimplex (r + 1) S, v.1 (Fin.last r)) =
          (r + 1) * (((r + 1 + 1) *
            (∑ v : OrdinarySimplex (r + 1) S, v.1 i.castSucc)) +
            (r + 1 + 1) * (∑ v : OrdinarySimplex (r + 1) S, v.1 (Fin.last r))) := by ring
      _ = (r + 1) * (S * Fintype.card (OrdinarySimplex (r + 1) S) +
            S * Fintype.card (OrdinarySimplex (r + 1) S)) := by rw [hMoment, hLast]
      _ = 2 * S * ((r + 1) * Fintype.card (OrdinarySimplex (r + 1) S)) := by ring
      _ = 2 * (S + 1) * S * Fintype.card (OrdinarySimplex r (S + 1)) := by rw [hMass]; ring


end
end DiscreteSimplex

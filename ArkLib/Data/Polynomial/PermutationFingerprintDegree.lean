/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import Mathlib.Algebra.MvPolynomial.CommRing
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Tactic.Ring
public import Lean.Elab.Tactic.Omega

/-!
# Degree cancellation for permutation fingerprints

The highest homogeneous parts of products of affine linear factors depend only on their
linear parts. Permuting these parts therefore lowers the degree of their difference.
-/

@[expose] public section

open scoped BigOperators
open MvPolynomial

namespace PermutationFingerprint

variable {R U V : Type*} [CommRing R]

/-- Adding constants to linear factors changes their product only below its top degree. -/
theorem totalDegree_prod_add_C_sub_prod_le (s : Finset U) (W : U → R)
    (p : U → MvPolynomial V R) (hp : ∀ u ∈ s, (p u).totalDegree ≤ 1) :
    (∏ u ∈ s, (C (W u) + p u) - ∏ u ∈ s, p u).totalDegree ≤ s.card - 1 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert u s hu ih =>
    have hps : ∀ u ∈ s, (p u).totalDegree ≤ 1 := fun v hv => hp v (by simp [hv])
    have hpu : (p u).totalDegree ≤ 1 := hp u (by simp)
    have hprod : (∏ v ∈ s, (C (W v) + p v)).totalDegree ≤ s.card := by
      refine (totalDegree_finsetProd _ _).trans ?_
      calc
        ∑ v ∈ s, (C (W v) + p v).totalDegree ≤ ∑ _v ∈ s, 1 := by
          apply Finset.sum_le_sum
          intro v hv
          exact (totalDegree_add _ _).trans (max_le (by simp) (hps v hv))
        _ = s.card := by simp
    rw [Finset.prod_insert hu, Finset.prod_insert hu, Finset.card_insert_of_notMem hu]
    rw [show (C (W u) + p u) * (∏ v ∈ s, (C (W v) + p v)) -
        p u * (∏ v ∈ s, p v) =
        C (W u) * (∏ v ∈ s, (C (W v) + p v)) +
        p u * ((∏ v ∈ s, (C (W v) + p v)) - ∏ v ∈ s, p v) by ring]
    refine (totalDegree_add _ _).trans (max_le ?_ ?_)
    · simpa using (totalDegree_mul (C (W u)) _).trans (by simpa using hprod)
    · by_cases hs : s = ∅
      · simp [hs]
      · have hcard : 0 < s.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hs)
        exact (totalDegree_mul _ _).trans (by have := ih hps; omega)

/-- Permuting the labels cancels the top degree of the two affine products. -/
theorem totalDegree_sub_permuted_prod_le [Fintype U] (W labels : U → R)
    (σ : Equiv.Perm U) :
    ((∏ u, (C (W u) + X (0 : Fin 2) * C (labels u) + X 1)) -
      ∏ u, (C (W u) + X (0 : Fin 2) * C (labels (σ u)) + X 1)).totalDegree ≤
      Fintype.card U - 1 := by
  classical
  cases subsingleton_or_nontrivial R with
  | inl h =>
    have hz : ((∏ u, (C (W u) + X (0 : Fin 2) * C (labels u) + X 1)) -
      ∏ u, (C (W u) + X (0 : Fin 2) * C (labels (σ u)) + X 1)) = 0 :=
      Subsingleton.elim _ _
    rw [hz]
    simp
  | inr h =>
    let p : U → MvPolynomial (Fin 2) R := fun u => X 0 * C (labels u) + X 1
    have hp (u : U) : (p u).totalDegree ≤ 1 := by
      exact (totalDegree_add _ _).trans (max_le
        ((totalDegree_mul _ _).trans (by simp)) (by simp))
    have ha := totalDegree_prod_add_C_sub_prod_le Finset.univ W p (fun u _ => hp u)
    have hb := totalDegree_prod_add_C_sub_prod_le Finset.univ W (p ∘ σ)
      (fun u _ => hp (σ u))
    have heq : (∏ u, p (σ u)) = ∏ u, p u := σ.prod_comp _ _ (by simp)
    have hid : ((∏ u, (C (W u) + X (0 : Fin 2) * C (labels u) + X 1)) -
        ∏ u, (C (W u) + X (0 : Fin 2) * C (labels (σ u)) + X 1)) =
        ((∏ u, (C (W u) + p u)) - ∏ u, p u) -
        ((∏ u, (C (W u) + p (σ u))) - ∏ u, p (σ u)) := by
      simp only [add_assoc]
      change ((∏ u, (C (W u) + p u)) - ∏ u, (C (W u) + p (σ u))) = _
      rw [heq]
      ring
    rw [hid]
    exact (totalDegree_sub _ _).trans (max_le ha hb)

end PermutationFingerprint

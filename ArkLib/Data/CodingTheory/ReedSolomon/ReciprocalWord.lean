/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module
public import ArkLib.Data.CodingTheory.Basic.Distance
public import Mathlib.Algebra.Polynomial.Roots

/-!
# Reciprocal words with a prescribed value at zero

Use `reciprocalWord a` for the word equal to `x⁻¹` away from zero and equal to the independently
chosen value `a` at zero. Keeping that value explicit prevents totalized field inversion from
silently fixing the pole coordinate in a coding-theoretic construction.

## Main result

`agree_reciprocalWord_le` proves that a polynomial of ordinary degree strictly below `k`
agrees with this word at at most `k + 1` field elements. Ordinary `degree` includes the zero
polynomial when `k = 0`; the theorem does not assume that the polynomial is nonzero.

Away from zero, agreement is equivalent to being a root of `X * P - 1`. This polynomial is
nonzero because its value at zero is `-1`, and has degree at most `k`. Its roots therefore
contribute at most `k` agreements. The separately assigned origin contributes at most one more.
The statement holds over any finite field, independently of characteristic.
-/

@[expose] public section

namespace ReedSolomon

open Polynomial

variable {F : Type*} [Field F] [DecidableEq F]

/-- Reciprocal away from zero, with an independently prescribed value at zero. -/
def reciprocalWord (a : F) (x : F) : F := if x = 0 then a else x⁻¹

@[simp] theorem reciprocalWord_zero (a : F) : reciprocalWord a 0 = a := by
  simp [reciprocalWord]

/-- Agreement with a reciprocal is detected by the roots of `X * P - 1`. -/
theorem reciprocalWord_eq_eval_iff {a x : F} (hx : x ≠ 0) (P : F[X]) :
    reciprocalWord a x = P.eval x ↔ (X * P - 1).eval x = 0 := by
  simp only [reciprocalWord, if_neg hx, eval_sub, eval_mul, eval_X, eval_one, sub_eq_zero]
  constructor
  · intro h
    rw [← h, mul_inv_cancel₀ hx]
  · intro h
    calc
      x⁻¹ = x⁻¹ * (x * P.eval x) := by rw [h, mul_one]
      _ = P.eval x := by rw [← mul_assoc, inv_mul_cancel₀ hx, one_mul]

/-- A reciprocal word agrees with any degree-`< k` polynomial on at most `k + 1` points.
The extra coordinate is the prescribed value at zero. -/
theorem agree_reciprocalWord_le [Fintype F] (a : F) (P : F[X]) (k : ℕ)
    (hP : P.degree < k) :
    Code.agree (reciprocalWord a) (fun x ↦ P.eval x) ≤ k + 1 := by
  classical
  let S : Finset F := Finset.univ.filter fun x ↦ reciprocalWord a x = P.eval x
  let R : F[X] := X * P - 1
  -- The auxiliary polynomial cannot vanish identically, including when P = 0.
  have hR : R ≠ 0 := by
    intro h
    have := congrArg (fun Q : F[X] ↦ Q.eval 0) h
    simp [R] at this
  have hdeg : R.natDegree ≤ k := by
    by_cases hp : P = 0
    · simp [R, hp]
    · have hd : P.natDegree < k := (natDegree_lt_iff_degree_lt hp).mpr hP
      calc
        R.natDegree ≤ max (X * P).natDegree (1 : F[X]).natDegree := natDegree_sub_le _ _
        _ ≤ k := by
          simp only [natDegree_one, max_zero]
          calc
            (X * P).natDegree ≤ (X : F[X]).natDegree + P.natDegree := natDegree_mul_le
            _ ≤ k := by rw [natDegree_X]; omega
  --
  -- Remove the pole before applying the polynomial root bound.
  have hroots : S.erase 0 ⊆ R.roots.toFinset := by
    intro x hx
    have hmem := Finset.mem_erase.mp hx
    apply Multiset.mem_toFinset.mpr
    apply (mem_roots hR).mpr
    exact (reciprocalWord_eq_eval_iff hmem.1 P).mp (Finset.mem_filter.mp hmem.2).2
  have hc : (S.erase 0).card ≤ k :=
    (Finset.card_le_card hroots).trans
      ((Multiset.toFinset_card_le _).trans ((card_roots' R).trans hdeg))
  --
  -- Restoring the origin can add only one agreement.
  have hS : S.card ≤ (S.erase 0).card + 1 := by
    by_cases hzero : 0 ∈ S
    · rw [Finset.card_erase_of_mem hzero]
      have := Finset.card_pos.mpr ⟨0, hzero⟩
      omega
    · rw [Finset.erase_eq_of_notMem hzero]
      omega
  exact hS.trans (Nat.add_le_add_right hc 1)

end ReedSolomon

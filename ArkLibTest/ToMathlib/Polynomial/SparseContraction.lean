/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.ToMathlib.Polynomial.SparseContraction
import Mathlib.Algebra.CharP.Basic
import Mathlib.Data.ZMod.Basic

/-!
# Acceptance client for `ArkLib.ToMathlib.Polynomial.SparseContraction`

The examples contract the sparse polynomial `X ^ 4 + 1` by `2`, show that the sparsity hypothesis
cannot be dropped (for `X`), check the `s = 0` boundary of `expand_contract_eq_self_iff`, show
that uniqueness fails for `s = 0`, recover a preimage from sparse Taylor data over `ZMod 2`, and
derive the source-shaped statements with `0 < s`.
-/

open Polynomial

namespace SparseContractionTest

/-- `X ^ 4 + 1` is sparse for `s = 2`, so it is the pullback of its contraction. -/
example : expand ℚ 2 (contract 2 (X ^ 4 + 1 : ℚ[X])) = X ^ 4 + 1 := by
  apply expand_contract_of_sparse
  intro i hi
  rw [coeff_add, coeff_X_pow, coeff_one]
  have h4 : i ≠ 4 := by rintro rfl; exact hi ⟨2, rfl⟩
  have h0 : i ≠ 0 := by rintro rfl; exact hi ⟨0, rfl⟩
  simp [h4, h0]

/-- The sparsity hypothesis is needed: `X` is not sparse for `s = 2`, and indeed it is not the
pullback of its contraction. -/
example : expand ℚ 2 (contract 2 (X : ℚ[X])) ≠ X := by
  rw [Ne, expand_contract_eq_self_iff]
  intro h
  simpa using h 1 (by norm_num)

/-- Boundary `s = 0`: the condition says that `P` is constant, and `C 3` qualifies. -/
example : expand ℚ 0 (contract 0 (C 3 : ℚ[X])) = C 3 := by
  apply expand_contract_of_sparse
  intro i hi
  simp only [zero_dvd_iff] at hi
  simp [coeff_C, hi]

/-- Boundary `s = 0`: the nonconstant `X` fails the condition. -/
example : expand ℚ 0 (contract 0 (X : ℚ[X])) ≠ X := by
  rw [Ne, expand_contract_eq_self_iff]
  intro h
  simpa using h 1 (by norm_num)

/-- A concrete unique preimage: `X ^ 4 + 1` has degree below `2 * 3`, and its unique preimage of
degree below `3` under `expand ℚ 2` is `X ^ 2 + 1`. -/
example : ∃! Q : ℚ[X], Q.degree < ↑(3 : ℕ) ∧ expand ℚ 2 Q = X ^ 4 + 1 := by
  refine ⟨X ^ 2 + 1, ⟨?_, ?_⟩, ?_⟩
  · compute_degree!
  · simp [← pow_mul]
  · intro Q hQ
    apply expand_injective (by norm_num : 0 < 2)
    rw [hQ.2]
    simp [← pow_mul]

/-- The hypothesis `s ≠ 0` of `existsUnique_expand_of_sparse` is needed: for `s = 0`, `P = 0`
and `k = 2`, both `0` and `X - 1` are preimages of degree below `2`. -/
example : ¬∃! Q : ℚ[X], Q.degree < ↑(2 : ℕ) ∧ expand ℚ 0 Q = 0 := by
  rintro ⟨Q, -, hQ⟩
  have h0 := hQ 0 ⟨by rw [degree_zero]; exact WithBot.bot_lt_coe 2, by simp⟩
  have h1 := hQ (X - 1) ⟨by compute_degree!, by simp⟩
  have : (X - 1 : ℚ[X]) = 0 := h1.trans h0.symm
  simpa using congrArg (eval 0) this

/-- Sparse Taylor data over `ZMod 2`: the Taylor expansion of `X ^ 2 + 1` at `1` is `X ^ 2`,
so `X ^ 2 + 1` has a unique preimage of degree below `2` under `expand (ZMod 2) 2`. -/
example : ∃! Q : (ZMod 2)[X], Q.degree < ↑(2 : ℕ) ∧ expand (ZMod 2) (2 ^ 1) Q = X ^ 2 + 1 := by
  apply existsUnique_expand_of_sparse_taylor 2 1 2 (X ^ 2 + 1) 1
  · intro i hi
    have hT : taylor (1 : ZMod 2) (X ^ 2 + 1) = X ^ 2 := by
      rw [taylor_apply, add_comp, pow_comp, X_comp, one_comp, C_1, add_pow_char, one_pow,
        add_assoc, CharTwo.add_self_eq_zero, add_zero]
    rw [hT, coeff_X_pow]
    have : i ≠ 2 := by rintro rfl; exact hi ⟨1, rfl⟩
    simp [this]
  · compute_degree!

section Source

variable {R : Type*} [CommRing R]

/-- Source statement `expand_contract_of_sparse`. -/
example {s : ℕ} (_hs : 0 < s) (P : R[X]) (hP : ∀ i : ℕ, ¬s ∣ i → P.coeff i = 0) :
    expand R s (contract s P) = P :=
  expand_contract_of_sparse s P hP

/-- Source statement `degree_contract_lt_of_degree_lt`. -/
example {s k : ℕ} (_hs : 0 < s) (P : R[X]) (hP : P.degree < ↑(s * k)) :
    (contract s P).degree < ↑k :=
  degree_contract_lt_of_degree_lt P hP

/-- Source statement `existsUnique_expand_of_sparse`. -/
example {s k : ℕ} (hs : 0 < s) (P : R[X]) (hsparse : ∀ i : ℕ, ¬s ∣ i → P.coeff i = 0)
    (hdegree : P.degree < ↑(s * k)) : ∃! Q : R[X], Q.degree < ↑k ∧ expand R s Q = P :=
  existsUnique_expand_of_sparse hs.ne' P hsparse hdegree

end Source

end SparseContractionTest

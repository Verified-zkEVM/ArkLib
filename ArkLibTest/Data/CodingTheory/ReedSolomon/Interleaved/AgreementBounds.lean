/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.Interleaved.AgreementBounds
import Mathlib.Algebra.Field.ZMod

/-!
# Interleaved Reed–Solomon list-size clients

These clients compute the packing into `F(Z)` on a pair, separate two tuples with
`tupleRatFunc_injective`, push a concrete codeword through `comp_mem_code_map`, derive the
source-shaped transfer of a scalar list bound over `F(Z)`, and show that the injective packing is
needed: over `ZMod 2` with one evaluation point, degree bound `1` and radius `1`, the two-fold
interleaved code has a list of four codewords while the scalar code has two codewords in total.
-/

open Code ReedSolomon Polynomial

namespace AgreementBoundsTest

-- Packing a pair gives `a + b Z`.
example (a b : ℚ) :
    tupleRatFunc ![a, b] =
      algebraMap ℚ (RatFunc ℚ) a + algebraMap ℚ (RatFunc ℚ) b * RatFunc.X := by
  simp [tupleRatFunc, Fin.sum_univ_two]

-- Packing separates `(1, 0)` from `(0, 1)`, that is `1` from `Z`.
example : tupleRatFunc ![(1 : ZMod 2), 0] ≠ tupleRatFunc ![0, 1] := by
  intro h
  have := congrFun (tupleRatFunc_injective h) 0
  simp at this

-- A Reed–Solomon codeword over `ZMod 2` stays a codeword over `F(Z)` on the mapped domain.
example (domain : Fin 3 ↪ ZMod 2) {k : ℕ} {w : Fin 3 → ZMod 2} (hw : w ∈ code domain k) :
    algebraMap (ZMod 2) (RatFunc (ZMod 2)) ∘ w ∈
      code (domain.trans ⟨algebraMap (ZMod 2) (RatFunc (ZMod 2)),
        (algebraMap (ZMod 2) (RatFunc (ZMod 2))).injective⟩) k :=
  comp_mem_code_map domain _ _ hw

-- Source shape: a list bound `L` for the scalar code over `F(Z)` bounds every interleaving.
example {F : Type} [Field F] {n k t L : ℕ} (domain : Fin n ↪ F) (δ : ℝ)
    (hscalar : Lambda (code (domain.trans ⟨algebraMap F (RatFunc F),
        (algebraMap F (RatFunc F)).injective⟩) k : Set (Fin n → RatFunc F)) δ ≤ L) :
    Lambda (interleavedCodeSet (κ := Fin t) (code domain k : Set (Fin n → F))) δ ≤ L :=
  (Lambda_interleaved_le_ratFunc domain k t δ).trans hscalar

/-- The single evaluation point `0` of `ZMod 2`. -/
def point : Fin 1 ↪ ZMod 2 := ⟨fun _ ↦ 0, fun a b _ ↦ Subsingleton.elim a b⟩

-- With one evaluation point and degree bound `1`, every word is a codeword: `w` is the constant
-- polynomial `w 0`.
theorem mem_code_point (w : Fin 1 → ZMod 2) : w ∈ code point 1 :=
  mem_code_iff_eval.mpr ⟨C (w 0), (degree_C_le).trans_lt (by decide),
    fun i ↦ by rw [Subsingleton.elim i 0]; simp⟩

-- Without an injective packing the comparison fails: `K = F`, `φ = id`, width two.
example :
    ¬ Lambda (interleavedCodeSet (κ := Fin 2) (code point 1 : Set (Fin 1 → ZMod 2))) 1 ≤
      Lambda (code point 1 : Set (Fin 1 → ZMod 2)) 1 := by
  classical
  intro h
  have hlow : (4 : ℕ∞) ≤
      Lambda (interleavedCodeSet (κ := Fin 2) (code point 1 : Set (Fin 1 → ZMod 2))) 1 := by
    have hlist : closeCodewordsRel
        (interleavedCodeSet (κ := Fin 2) (code point 1 : Set (Fin 1 → ZMod 2)))
          (fun _ _ ↦ 0) 1 = Set.univ := by
      refine Set.eq_univ_of_forall fun c ↦ ?_
      exact mem_closeCodewordsRel_iff.mpr
        ⟨fun j ↦ mem_code_point _, by exact_mod_cast relHammingDist_le_one⟩
    calc (4 : ℕ∞) = (Set.univ : Set (Fin 1 → Fin 2 → ZMod 2)).encard := by
          simp [Set.encard_univ, ENat.card_eq_coe_fintype_card]
      _ = _ := by rw [hlist]
      _ ≤ _ := encard_closeCodewordsRel_le_Lambda _ _ _
  have hup : Lambda (code point 1 : Set (Fin 1 → ZMod 2)) 1 ≤ 2 :=
    Lambda_le_iff_forall_encard_le.mpr fun f ↦
      (Set.encard_le_encard (Set.subset_univ _)).trans
        (by simp [Set.encard_univ, ENat.card_eq_coe_fintype_card])
  exact absurd (hlow.trans (h.trans hup)) (by decide)

-- The same comparison holds once the pair is packed into `F(Z)`.
example :
    Lambda (interleavedCodeSet (κ := Fin 2) (code point 1 : Set (Fin 1 → ZMod 2))) 1 ≤
      Lambda (code (point.trans ⟨algebraMap (ZMod 2) (RatFunc (ZMod 2)),
        (algebraMap (ZMod 2) (RatFunc (ZMod 2))).injective⟩) 1 :
          Set (Fin 1 → RatFunc (ZMod 2))) 1 :=
  Lambda_interleaved_le_ratFunc point 1 2 1

end AgreementBoundsTest

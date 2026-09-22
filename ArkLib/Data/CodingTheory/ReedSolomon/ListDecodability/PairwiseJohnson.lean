/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.JohnsonBound.Pairwise
public import ArkLib.Data.CodingTheory.ReedSolomon.AgreementList

/-!
# Pairwise Johnson bound for Reed–Solomon codes

This file specializes the arbitrary-alphabet pairwise Johnson theorem to Reed–Solomon codes.
Distinct evaluation words of degree-`< D + 1` agree in at most `D` coordinates, so the generic
code theorem gives the exact integral list-size bound

`⌊n(A - D) / (A² - nD)⌋`.

The polynomial statement transfers the same generic code bound through evaluation. It includes
all degree-at-most-`D` polynomials, including zero, over an arbitrary field.

The elementary counting argument is extracted from
`MutualCorrelatedAgreement/Johnson/WeightedCertificate.lean` at immutable source commit
`a5aa2677fee4e3a79d6bb05136631cce4a08587d`.
-/

@[expose] public section

namespace ReedSolomon

open Polynomial

noncomputable section

/-- A Reed–Solomon code satisfies the arbitrary-alphabet pairwise Johnson list-decoding bound.

`n > 0` is needed only to express the agreement threshold as the relative radius `1 - A / n`.
The integral counting theorem used here has no corresponding nonemptiness requirement. -/
theorem code_isListDecodable_pairwiseJohnson
    {F : Type*} [Field F] {n D A : ℕ}
    (domain : Fin n ↪ F) (hn : 0 < n)
    (hDA : D + 1 ≤ A) (hpositive : n * D < A * A) :
    Code.IsListDecodable ((code domain (D + 1) : Submodule F (Fin n → F)) : Set (Fin n → F))
      (1 - (A : ℝ) / n) (Code.pairwiseJohnsonListBound n D A : NNReal) := by
  classical
  let : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  let C : Set (Fin n → F) := code domain (D + 1)
  have hpair : ∀ c ∈ C, ∀ c' ∈ C, c ≠ c' → Code.agree c c' ≤ D := by
    intro c hc c' hc' hne
    have hlt := agree_lt_of_mem_code (n := D + 1)
      (show c ∈ code domain (D + 1) from hc)
      (show c' ∈ code domain (D + 1) from hc') hne
    omega
  have hgeneric := Code.isListDecodable_pairwiseJohnson C D A (by omega)
    (by simpa using hpositive) hpair
  simpa only [C, Fintype.card_fin] using hgeneric

open Classical in
/-- Exact integral pairwise Johnson bound for complete Reed–Solomon polynomial agreement lists.

The proof applies the arbitrary-code finite-family theorem to evaluation words. When `A ≤ n`,
evaluation is injective on degree-at-most-`D` polynomials because `D + 1 ≤ A`; when `n < A`, the
agreement list is empty. Thus no finiteness assumption on the field is required. -/
theorem closePolynomialSet_finite_and_ncard_le_pairwiseJohnson
    {F : Type*} [Field F] {n D A : ℕ}
    (domain : Fin n ↪ F) (received : Fin n → F)
    (hDA : D + 1 ≤ A) (hpositive : n * D < A * A) :
    (closePolynomialSet domain received (D + 1) A).Finite ∧
      (closePolynomialSet domain received (D + 1) A).ncard ≤
        Code.pairwiseJohnsonListBound n D A := by
  let candidates := closePolynomialSet domain received (D + 1) A
  let C : Set (Fin n → F) := code domain (D + 1)
  have hpair : ∀ c ∈ C, ∀ c' ∈ C, c ≠ c' → Code.agree c c' ≤ D := by
    intro c hc c' hc' hne
    have hlt := agree_lt_of_mem_code (n := D + 1)
      (show c ∈ code domain (D + 1) from hc)
      (show c' ∈ code domain (D + 1) from hc') hne
    omega
  have hfinset : ∀ T : Finset F[X], (∀ P ∈ T, P ∈ candidates) →
      T.card ≤ Code.pairwiseJohnsonListBound n D A := by
    intro T hT
    by_cases hAn : A ≤ n
    · let eval : F[X] → (Fin n → F) := evalOnPoints domain
      let U := T.image eval
      have hinj : Set.InjOn eval T := by
        intro P hP Q hQ heval
        apply Polynomial.eq_of_degrees_lt_of_eval_index_eq Finset.univ
          (by simpa using domain.injective)
        · exact (hT P hP).1.trans_le (by
            rw [Finset.card_univ, Fintype.card_fin]
            exact_mod_cast hDA.trans hAn)
        · exact (hT Q hQ).1.trans_le (by
            rw [Finset.card_univ, Fintype.card_fin]
            exact_mod_cast hDA.trans hAn)
        · intro i hi
          exact congrFun heval i
      have hcard : U.card = T.card := Finset.card_image_iff.mpr hinj
      rw [← hcard]
      have hU : ∀ c ∈ U, c ∈ C ∧ A ≤ Code.agree c received := by
        intro c hc
        rcases Finset.mem_image.mp hc with ⟨P, hP, rfl⟩
        refine ⟨evalOnPoints_mem_code_of_degree_lt (hT P hP).1, ?_⟩
        simpa only [card_polynomialAgreementSet] using (hT P hP).2
      have hgeneric := Code.finset_card_le_pairwiseJohnson C received D A (by omega)
        (by simpa using hpositive) hpair U hU
      simpa only [Fintype.card_fin] using hgeneric
    · have hempty : T = ∅ := by
        apply Finset.not_nonempty_iff_eq_empty.mp
        rintro ⟨P, hP⟩
        have hlarge := (hT P hP).2
        have hle : (polynomialAgreementSet domain received P).card ≤ n := by
          simpa using Finset.card_le_card
            (Finset.subset_univ (polynomialAgreementSet domain received P))
        omega
      simp [hempty]
  have hfinite : candidates.Finite :=
    Set.finite_of_forall_finset_card_le (R := ℕ) fun T hsub =>
      hfinset T fun P hP => hsub hP
  refine ⟨hfinite, ?_⟩
  rw [Set.ncard_eq_toFinset_card _ hfinite]
  exact hfinset hfinite.toFinset fun P hP => hfinite.mem_toFinset.mp hP

end

end ReedSolomon

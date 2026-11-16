/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Coratger
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.AffineCombiner.Basic
public import Mathlib.FieldTheory.RatFunc.Basic

/-!
# Exceptional challenges explained by one rational pair

Fix two rational functions `F₀, G₀`.

A challenge `(α, β)` is compatible with them when `F₀ + (α + β X) G₀` is a polynomial.

## Polynomial pairs within the degree bounds

An exceptional challenge loses at least two agreement points.

At each lost point `x`, the value `α + β x` is fixed by the pair.

Two points fix `(α, β)`, so at most `n choose 2` challenges are exceptional.

## Other pairs

The compatible challenges of degree at most `d` form a proper affine subspace of `F²`.

So there are at most `q` of them.

## Main statements

* `ReedSolomon.card_isAffineExceptional_add_mul_le`: the polynomial case.
* `ReedSolomon.card_ratFunc_combination_le`: the case outside the degree bounds.
* `ReedSolomon.card_isAffineExceptional_ratFunc_le`: every rational pair has at most
  `max q (n choose 2)` exceptional challenges.

## References

The results are Lemma 4.4 of [CWYZ26].

* [Chiesa, A., Weissenberg, G., Yogev, E., and Zheng, K. Z.,
    *Affine combiners for Reed–Solomon proximity gaps*][CWYZ26]
-/

@[expose] public section

namespace ReedSolomon

open Polynomial Finset

variable {F : Type*} [Field F] [DecidableEq F] {ι : Type*} [Fintype ι]

/-- Two challenges that both lose the point `i` take the same multiplier value there. -/
theorem eval_affineMultiplier_eq_of_mem_agreementLoss {domain : ι ↪ F} {f g : ι → F}
    {F₀ G₀ : F[X]} {α β α' β' : F} {i : ι}
    (h : i ∈ agreementLoss domain f g (affineMultiplier α β)
      (F₀ + affineMultiplier α β * G₀) F₀ G₀)
    (h' : i ∈ agreementLoss domain f g (affineMultiplier α' β')
      (F₀ + affineMultiplier α' β' * G₀) F₀ G₀) :
    α + β * domain i = α' + β' * domain i := by
  simp only [agreementLoss, mem_filter, mem_polynomialAgreementSet,
    combinedWord_affineMultiplier, eval_add, eval_mul, eval_affineMultiplier] at h h'
  obtain ⟨h1, h2⟩ := h
  obtain ⟨h1', -⟩ := h'
  have hG : G₀.eval (domain i) ≠ g i := by
    intro hG
    rw [hG] at h1
    exact h2.elim (fun h ↦ h (by linear_combination h1)) (fun h ↦ h hG)
  have : (α + β * domain i - (α' + β' * domain i)) * (G₀.eval (domain i) - g i) = 0 := by
    linear_combination h1 - h1'
  rcases mul_eq_zero.mp this with h | h
  · linear_combination h
  · exact absurd (sub_eq_zero.mp h) hG

open Classical in
/-- A polynomial pair within the degree bounds explains at most `n choose 2` challenges. -/
theorem card_isAffineExceptional_add_mul_le [Fintype F] (domain : ι ↪ F) (f g : ι → F)
    {d A : ℕ} (F₀ G₀ : F[X]) (hF : F₀.degree ≤ d) (hG : G₀.degree < d) :
    #{c : F × F | IsAffineExceptional domain f g d A 1 c.1 c.2
      (F₀ + affineMultiplier c.1 c.2 * G₀)} ≤ (Fintype.card ι).choose 2 := by
  set E : Finset (F × F) := {c : F × F | IsAffineExceptional domain f g d A 1 c.1 c.2
    (F₀ + affineMultiplier c.1 c.2 * G₀)}
  have hloss : ∀ c ∈ E, ∃ t ⊆ agreementLoss domain f g (affineMultiplier c.1 c.2)
      (F₀ + affineMultiplier c.1 c.2 * G₀) F₀ G₀, #t = 2 := by
    intro c hc
    have h := (mem_filter.mp hc).2.2.2 F₀ G₀ hF hG
    exact exists_subset_card_eq (by by_contra hlt; exact h ⟨rfl, by omega⟩)
  choose! t ht using hloss
  calc #E ≤ #(powersetCard 2 (univ : Finset ι)) := by
        refine card_le_card_of_injOn t (fun c hc ↦ ?_) (fun c hc c' hc' hcc' ↦ ?_)
        · simpa using (ht c hc).2
        obtain ⟨i, j, hij, hcij⟩ := card_eq_two.mp (ht c hc).2
        have hmem : ∀ k ∈ t c, c.1 + c.2 * domain k = c'.1 + c'.2 * domain k := fun k hk ↦
          eval_affineMultiplier_eq_of_mem_agreementLoss ((ht c hc).1 hk)
            ((ht c' hc').1 (hcc' ▸ hk))
        have hi := hmem i (by simp [hcij])
        have hj := hmem j (by simp [hcij])
        have hx : domain i - domain j ≠ 0 := sub_ne_zero.mpr (domain.injective.ne hij)
        have hβ : c.2 = c'.2 := by
          have : (c.2 - c'.2) * (domain i - domain j) = 0 := by linear_combination hi - hj
          exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_right hx)
        refine Prod.ext ?_ hβ
        rw [hβ] at hi
        linear_combination hi
    _ = (Fintype.card ι).choose 2 := by simp

omit [DecidableEq F] in
open Classical in
/-- Any other rational pair is compatible with at most `q` challenges.

Compatible means the combination is a polynomial of degree at most `d`. -/
theorem card_ratFunc_combination_le [Fintype F] {d : ℕ} (F₀ G₀ : RatFunc F)
    (h : ¬ ∃ F₁ G₁ : F[X], algebraMap F[X] (RatFunc F) F₁ = F₀ ∧
      algebraMap F[X] (RatFunc F) G₁ = G₀ ∧ F₁.degree ≤ d ∧ G₁.degree < d) :
    #{c : F × F | ∃ P : F[X], P.degree ≤ d ∧ algebraMap F[X] (RatFunc F) P =
      F₀ + algebraMap F[X] (RatFunc F) (affineMultiplier c.1 c.2) * G₀} ≤ Fintype.card F := by
  set S : Finset (F × F) := {c : F × F | ∃ P : F[X], P.degree ≤ d ∧
    algebraMap F[X] (RatFunc F) P =
      F₀ + algebraMap F[X] (RatFunc F) (affineMultiplier c.1 c.2) * G₀}
  -- The rational functions that are polynomials of degree at most `d`.
  set V : Submodule F (RatFunc F) :=
    (degreeLE F d).map ((Algebra.linearMap F[X] (RatFunc F)).restrictScalars F)
  have hV : ∀ r, r ∈ V ↔ ∃ P : F[X], P.degree ≤ d ∧ algebraMap F[X] (RatFunc F) P = r := by
    intro r
    simp [V, mem_degreeLE]
  set u : F × F → RatFunc F := fun c ↦
    F₀ + algebraMap F[X] (RatFunc F) (affineMultiplier c.1 c.2) * G₀
  set XG : RatFunc F := algebraMap F[X] (RatFunc F) X * G₀
  have hu : ∀ c, u c = F₀ + c.1 • G₀ + c.2 • XG := by
    intro c
    have hC : ∀ a : F, algebraMap F[X] (RatFunc F) (C a) = algebraMap F (RatFunc F) a :=
      fun a ↦ (IsScalarTower.algebraMap_apply F F[X] (RatFunc F) a).symm
    simp only [u, XG, affineMultiplier, map_add, map_mul, hC, Algebra.smul_def]
    ring
  have hS : ∀ c ∈ S, u c ∈ V := fun c hc ↦ (hV _).mpr (mem_filter.mp hc).2
  by_contra hlt
  push Not at hlt
  obtain ⟨c, hc, c', hc', hne, heq⟩ := exists_ne_map_eq_of_card_lt_of_maps_to
    (t := (univ : Finset F)) (f := Prod.fst) (by simpa using hlt) (by simp [Set.MapsTo])
  have hβ : c'.2 - c.2 ≠ 0 := sub_ne_zero.mpr fun h ↦ hne (Prod.ext heq h.symm)
  obtain ⟨c'', hc'', hα⟩ : ∃ c'' ∈ S, c''.1 - c.1 ≠ 0 := by
    by_contra! hall
    have hsub : S ⊆ (univ : Finset F).image fun b ↦ (c.1, b) := by
      intro e he
      simpa [Prod.ext_iff, eq_comm, sub_eq_zero] using hall e he
    exact absurd ((card_le_card hsub).trans card_image_le) (by simpa using hlt)
  have hXG : XG ∈ V := by
    have h := V.smul_mem (c'.2 - c.2)⁻¹ (V.sub_mem (hS c' hc') (hS c hc))
    convert h using 1
    rw [hu, hu, heq, eq_inv_smul_iff₀ hβ]
    module
  have hG : G₀ ∈ V := by
    have h := V.smul_mem (c''.1 - c.1)⁻¹
      (V.sub_mem (V.sub_mem (hS c'' hc'') (hS c hc)) (V.smul_mem (c''.2 - c.2) hXG))
    convert h using 1
    rw [hu, hu, eq_inv_smul_iff₀ hα]
    module
  have hF : F₀ ∈ V := by
    have h := V.sub_mem (V.sub_mem (hS c hc) (V.smul_mem c.1 hG)) (V.smul_mem c.2 hXG)
    convert h using 1
    rw [hu]
    module
  obtain ⟨F₁, hF₁, rfl⟩ := (hV _).mp hF
  obtain ⟨G₁, hG₁, rfl⟩ := (hV _).mp hG
  obtain ⟨Q, hQ, hQX⟩ := (hV _).mp hXG
  replace hQX : Q = G₁ * X := by
    apply RatFunc.algebraMap_injective F
    rw [hQX, map_mul, mul_comm]
  refine h ⟨F₁, G₁, rfl, rfl, hF₁, ?_⟩
  rcases eq_or_ne G₁ 0 with rfl | hG₁0
  · simp
  rw [hQX, degree_mul_X] at hQ
  rw [degree_eq_natDegree hG₁0] at hQ ⊢
  exact_mod_cast (show G₁.natDegree + 1 ≤ d by exact_mod_cast hQ)

open Classical in
/-- Every rational pair explains at most `max q (n choose 2)` exceptional challenges. -/
theorem card_isAffineExceptional_ratFunc_le [Fintype F] (domain : ι ↪ F) (f g : ι → F)
    {d A : ℕ} (F₀ G₀ : RatFunc F) :
    #{c : F × F | ∃ P : F[X], algebraMap F[X] (RatFunc F) P =
        F₀ + algebraMap F[X] (RatFunc F) (affineMultiplier c.1 c.2) * G₀ ∧
      IsAffineExceptional domain f g d A 1 c.1 c.2 P} ≤
      max (Fintype.card F) ((Fintype.card ι).choose 2) := by
  by_cases h : ∃ F₁ G₁ : F[X], algebraMap F[X] (RatFunc F) F₁ = F₀ ∧
      algebraMap F[X] (RatFunc F) G₁ = G₀ ∧ F₁.degree ≤ d ∧ G₁.degree < d
  · obtain ⟨F₁, G₁, rfl, rfl, hF, hG⟩ := h
    refine le_max_of_le_right ((card_le_card fun c hc ↦ ?_).trans
      (card_isAffineExceptional_add_mul_le domain f g (A := A) F₁ G₁ hF hG))
    obtain ⟨P, hP, hex⟩ := (mem_filter.mp hc).2
    rw [← map_mul, ← map_add, (RatFunc.algebraMap_injective F).eq_iff] at hP
    exact mem_filter.mpr ⟨mem_univ _, hP ▸ hex⟩
  · refine le_max_of_le_left ((card_le_card fun c hc ↦ ?_).trans
      (card_ratFunc_combination_le F₀ G₀ h))
    obtain ⟨P, hP, hex⟩ := (mem_filter.mp hc).2
    exact mem_filter.mpr ⟨mem_univ _, P, hex.1, hP⟩

end ReedSolomon

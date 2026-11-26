/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Coratger
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.AffineCombiner.Basic
public import Mathlib.FieldTheory.RatFunc.Basic

/-!
# Exceptional challenges for one rational pair

Fix rational functions `F₀, G₀` over a finite field of size `q` and a domain of size `n`.
A challenge `(α, β)` is compatible with this pair at degree bound `d` if
`F₀ + (α + β X) G₀` is a polynomial of degree at most `d`.
The results formalize Lemma 4.4 of [CWYZ26] for agreement loss one.
The [paper page](../../../../../../docs/kb/papers/CWYZ26.md) records their statement correspondence.

If `F₀, G₀` are polynomials of degrees `≤ d` and `< d`, an exceptional candidate loses at
least two agreement points with these witnesses.
At each lost point, the multiplier value is determined by the rational pair and received words.
Two distinct points determine `(α, β)`, so at most `n choose 2` challenges are exceptional.

For a pair outside these degree bounds, at most `q` challenges are compatible.
The proof shows that more than `q` compatible challenges would force both rational functions
to be polynomials within the witness degree bounds.
Combining the cases gives at most `max q (n choose 2)` exceptional challenges for any rational pair.

Each count is stated for challenges drawn from a finite type `K` through an injective map
`φ : K ↪ E`, so from any finite subset of `E`.
Subfields are the main example.
Words, witnesses and rational functions stay over `E`, and `q` becomes `|K|`.
A nonpolynomial pair then gives an affine equation over `E` with at most `|K|` solutions in `K²`.
The compatible challenges lie on one affine line of `E²`, which meets the image of `K²` in at
most `|K|` points.
This form serves the interleaved count of Theorem 5.2 of [CWYZ26].
The single-field Lemma 4.4 is the case of the identity embedding.

## Main statements

* `ReedSolomon.eval_affineMultiplier_eq_of_mem_agreementLoss`: a lost point fixes the multiplier.
* `ReedSolomon.card_isAffineExceptional_add_mul_map_le`: the polynomial witness case.
* `ReedSolomon.card_ratFunc_combination_map_le`: compatibility outside the witness degree
  bounds.
* `ReedSolomon.card_isAffineExceptional_ratFunc_map_le`: the bound for every rational pair.

## References

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

section Map

variable {K E : Type*} [Field E] [DecidableEq E]

open Classical in
/-- Let `φ : K ↪ E` be an injective map from a finite type, such as a subfield.
Let `n` be the domain size.
Assume `deg F₀ ≤ d` and `deg G₀ < d`.
At most `n choose 2` challenges `(α, β) ∈ K²` make `F₀ + (φ α + φ β X) G₀` exceptional.
The agreement loss is one. -/
theorem card_isAffineExceptional_add_mul_map_le [Fintype K] (domain : ι ↪ E) (f g : ι → E)
    (φ : K ↪ E) {d A : ℕ} (F₀ G₀ : E[X]) (hF : F₀.degree ≤ d) (hG : G₀.degree < d) :
    #{c : K × K | IsAffineExceptional domain f g d A 1 (φ c.1) (φ c.2)
      (F₀ + affineMultiplier (φ c.1) (φ c.2) * G₀)} ≤ (Fintype.card ι).choose 2 := by
  set S : Finset (K × K) := {c : K × K | IsAffineExceptional domain f g d A 1 (φ c.1) (φ c.2)
    (F₀ + affineMultiplier (φ c.1) (φ c.2) * G₀)}
  have hloss : ∀ c ∈ S, ∃ t ⊆ agreementLoss domain f g (affineMultiplier (φ c.1) (φ c.2))
      (F₀ + affineMultiplier (φ c.1) (φ c.2) * G₀) F₀ G₀, #t = 2 := by
    intro c hc
    have h := (mem_filter.mp hc).2.2.2 F₀ G₀ hF hG
    exact exists_subset_card_eq (by by_contra hlt; exact h ⟨rfl, by omega⟩)
  choose! t ht using hloss
  calc #S ≤ #(powersetCard 2 (univ : Finset ι)) := by
        refine card_le_card_of_injOn t (fun c hc ↦ ?_) (fun c hc c' hc' hcc' ↦ ?_)
        · simpa using (ht c hc).2
        obtain ⟨i, j, hij, hcij⟩ := card_eq_two.mp (ht c hc).2
        have hmem : ∀ k ∈ t c, φ c.1 + φ c.2 * domain k = φ c'.1 + φ c'.2 * domain k :=
          fun k hk ↦ eval_affineMultiplier_eq_of_mem_agreementLoss ((ht c hc).1 hk)
            ((ht c' hc').1 (hcc' ▸ hk))
        have hi := hmem i (by simp [hcij])
        have hj := hmem j (by simp [hcij])
        have hx : domain i - domain j ≠ 0 := sub_ne_zero.mpr (domain.injective.ne hij)
        have hβ : φ c.2 = φ c'.2 := by
          have : (φ c.2 - φ c'.2) * (domain i - domain j) = 0 := by linear_combination hi - hj
          exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_right hx)
        refine Prod.ext (φ.injective ?_) (φ.injective hβ)
        rw [hβ] at hi
        linear_combination hi
    _ = (Fintype.card ι).choose 2 := by simp

omit [DecidableEq E] in
open Classical in
/-- Let `φ : K ↪ E` be an injective map from a finite type, such as a subfield.
Assume `(F₀, G₀)` is not a pair of polynomials with `deg F₀ ≤ d` and `deg G₀ < d`.
At most `|K|` challenges `(α, β) ∈ K²` make `F₀ + (φ α + φ β X) G₀` polynomial of degree `≤ d`. -/
theorem card_ratFunc_combination_map_le [Fintype K] (φ : K ↪ E) {d : ℕ} (F₀ G₀ : RatFunc E)
    (h : ¬ ∃ F₁ G₁ : E[X], algebraMap E[X] (RatFunc E) F₁ = F₀ ∧
      algebraMap E[X] (RatFunc E) G₁ = G₀ ∧ F₁.degree ≤ d ∧ G₁.degree < d) :
    #{c : K × K | ∃ P : E[X], P.degree ≤ d ∧ algebraMap E[X] (RatFunc E) P =
      F₀ + algebraMap E[X] (RatFunc E) (affineMultiplier (φ c.1) (φ c.2)) * G₀} ≤
      Fintype.card K := by
  set S : Finset (K × K) := {c : K × K | ∃ P : E[X], P.degree ≤ d ∧
    algebraMap E[X] (RatFunc E) P =
      F₀ + algebraMap E[X] (RatFunc E) (affineMultiplier (φ c.1) (φ c.2)) * G₀}
  -- The rational functions that are polynomials of degree at most `d`.
  set V : Submodule E (RatFunc E) :=
    (degreeLE E d).map ((Algebra.linearMap E[X] (RatFunc E)).restrictScalars E)
  have hV : ∀ r, r ∈ V ↔ ∃ P : E[X], P.degree ≤ d ∧ algebraMap E[X] (RatFunc E) P = r := by
    intro r
    simp [V, mem_degreeLE]
  set u : K × K → RatFunc E := fun c ↦
    F₀ + algebraMap E[X] (RatFunc E) (affineMultiplier (φ c.1) (φ c.2)) * G₀
  set XG : RatFunc E := algebraMap E[X] (RatFunc E) X * G₀
  have hu : ∀ c, u c = F₀ + φ c.1 • G₀ + φ c.2 • XG := by
    intro c
    have hC : ∀ a : E, algebraMap E[X] (RatFunc E) (C a) = algebraMap E (RatFunc E) a :=
      fun a ↦ (IsScalarTower.algebraMap_apply E E[X] (RatFunc E) a).symm
    simp only [u, XG, affineMultiplier, map_add, map_mul, hC, Algebra.smul_def]
    ring
  have hS : ∀ c ∈ S, u c ∈ V := fun c hc ↦ (hV _).mpr (mem_filter.mp hc).2
  by_contra hlt
  push Not at hlt
  obtain ⟨c, hc, c', hc', hne, heq⟩ := exists_ne_map_eq_of_card_lt_of_maps_to
    (t := (univ : Finset K)) (f := Prod.fst) (by simpa using hlt) (by simp [Set.MapsTo])
  have hβ : φ c'.2 - φ c.2 ≠ 0 :=
    sub_ne_zero.mpr fun h ↦ hne (Prod.ext heq (φ.injective h).symm)
  obtain ⟨c'', hc'', hα⟩ : ∃ c'' ∈ S, φ c''.1 - φ c.1 ≠ 0 := by
    by_contra! hall
    have hsub : S ⊆ (univ : Finset K).image fun b ↦ (c.1, b) := by
      intro e he
      simpa [Prod.ext_iff, eq_comm, sub_eq_zero] using φ.injective (sub_eq_zero.mp (hall e he))
    exact absurd ((card_le_card hsub).trans card_image_le) (by simpa using hlt)
  have hXG : XG ∈ V := by
    have h := V.smul_mem (φ c'.2 - φ c.2)⁻¹ (V.sub_mem (hS c' hc') (hS c hc))
    convert h using 1
    rw [hu, hu, heq, eq_inv_smul_iff₀ hβ]
    module
  have hG : G₀ ∈ V := by
    have h := V.smul_mem (φ c''.1 - φ c.1)⁻¹
      (V.sub_mem (V.sub_mem (hS c'' hc'') (hS c hc)) (V.smul_mem (φ c''.2 - φ c.2) hXG))
    convert h using 1
    rw [hu, hu, eq_inv_smul_iff₀ hα]
    module
  have hF : F₀ ∈ V := by
    have h := V.sub_mem (V.sub_mem (hS c hc) (V.smul_mem (φ c.1) hG)) (V.smul_mem (φ c.2) hXG)
    convert h using 1
    rw [hu]
    module
  obtain ⟨F₁, hF₁, rfl⟩ := (hV _).mp hF
  obtain ⟨G₁, hG₁, rfl⟩ := (hV _).mp hG
  obtain ⟨Q, hQ, hQX⟩ := (hV _).mp hXG
  replace hQX : Q = G₁ * X := by
    apply RatFunc.algebraMap_injective E
    rw [hQX, map_mul, mul_comm]
  refine h ⟨F₁, G₁, rfl, rfl, hF₁, ?_⟩
  rcases eq_or_ne G₁ 0 with rfl | hG₁0
  · simp
  rw [hQX, degree_mul_X] at hQ
  rw [degree_eq_natDegree hG₁0] at hQ ⊢
  exact_mod_cast (show G₁.natDegree + 1 ≤ d by exact_mod_cast hQ)

open Classical in
/-- Let `φ : K ↪ E` be an injective map from a finite type, such as a subfield.
Let `n` be the domain size and `q = |K|`.
Fix any rational pair `(F₀, G₀)` over `E`.
Count the challenges `(α, β) ∈ K²` for which `F₀ + (φ α + φ β X) G₀` is an exceptional polynomial.
The agreement loss is one.
There are at most `max q (n choose 2)` such challenges. -/
theorem card_isAffineExceptional_ratFunc_map_le [Fintype K] (domain : ι ↪ E) (f g : ι → E)
    (φ : K ↪ E) {d A : ℕ} (F₀ G₀ : RatFunc E) :
    #{c : K × K | ∃ P : E[X], algebraMap E[X] (RatFunc E) P =
        F₀ + algebraMap E[X] (RatFunc E) (affineMultiplier (φ c.1) (φ c.2)) * G₀ ∧
      IsAffineExceptional domain f g d A 1 (φ c.1) (φ c.2) P} ≤
      max (Fintype.card K) ((Fintype.card ι).choose 2) := by
  by_cases h : ∃ F₁ G₁ : E[X], algebraMap E[X] (RatFunc E) F₁ = F₀ ∧
      algebraMap E[X] (RatFunc E) G₁ = G₀ ∧ F₁.degree ≤ d ∧ G₁.degree < d
  · obtain ⟨F₁, G₁, rfl, rfl, hF, hG⟩ := h
    refine le_max_of_le_right ((card_le_card fun c hc ↦ ?_).trans
      (card_isAffineExceptional_add_mul_map_le domain f g φ (A := A) F₁ G₁ hF hG))
    obtain ⟨P, hP, hex⟩ := (mem_filter.mp hc).2
    rw [← map_mul, ← map_add, (RatFunc.algebraMap_injective E).eq_iff] at hP
    exact mem_filter.mpr ⟨mem_univ _, hP ▸ hex⟩
  · refine le_max_of_le_left ((card_le_card fun c hc ↦ ?_).trans
      (card_ratFunc_combination_map_le φ F₀ G₀ h))
    obtain ⟨P, hP, hex⟩ := (mem_filter.mp hc).2
    exact mem_filter.mpr ⟨mem_univ _, P, hex.1, hP⟩

end Map

end ReedSolomon

/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Coratger
-/
module

public import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.AffineCombiner.RationalPair
public import ArkLib.Data.Finset.PairwiseIntersection
public import ArkLib.Data.Polynomial.SpecializationAvoidance

/-!
# Persistent exceptional challenges

A candidate is persistent when a rational function `G = H / L` explains many agreements.

Here `deg H ≤ d`, `deg L ≤ 1`, and `G` agrees with `g` at `B` agreement points.

Two distinct explaining pairs share at most `d + 1` points.

So the Johnson bound for set families limits the number of pairs.

Each pair explains at most `max q (n choose 2)` exceptional challenges.

## Main definitions

* `ReedSolomon.IsAffinePersistent`: persistence of a candidate at a threshold.

## Main statements

* `ReedSolomon.card_isAffineExceptional_persistent_le`: the count of persistent exceptional
  challenges.

## References

The count is Lemma 4.5 of [CWYZ26].

* [Chiesa, A., Weissenberg, G., Yogev, E., and Zheng, K. Z.,
    *Affine combiners for Reed–Solomon proximity gaps*][CWYZ26]
-/

@[expose] public section

namespace ReedSolomon

open Polynomial Finset

variable {F : Type*} [Field F] [DecidableEq F] {ι : Type*} [Fintype ι]

/-- `P` is persistent at threshold `B` for the challenge `(α, β)`.

Some `G = H / L`, with `deg H ≤ d`, `L ≠ 0` and `deg L ≤ 1`, agrees with `g` at `B` points.

These points agree with `P` and avoid the root of `L`.

The partner `F = P - (α + β X) G` then agrees with `f` there too. -/
def IsAffinePersistent (domain : ι ↪ F) (f g : ι → F) (d B : ℕ) (α β : F) (P : F[X]) : Prop :=
  ∃ H L : F[X], L ≠ 0 ∧ L.degree ≤ 1 ∧ H.degree ≤ d ∧
    B ≤ #{i ∈ polynomialAgreementSet domain (combinedWord domain f g (affineMultiplier α β)) P |
      L.eval (domain i) ≠ 0 ∧ H.eval (domain i) = L.eval (domain i) * g i}

/-- The agreement points of `P` where `L` does not vanish and `H = L g`. -/
private noncomputable def persistenceSet (domain : ι ↪ F) (f g : ι → F) (α β : F) (P H L : F[X]) :
    Finset ι :=
  {i ∈ polynomialAgreementSet domain (combinedWord domain f g (affineMultiplier α β)) P |
    L.eval (domain i) ≠ 0 ∧ H.eval (domain i) = L.eval (domain i) * g i}

/-- The rational pair `(P - (α + β X) H / L, H / L)`. -/
private noncomputable def persistentPair (α β : F) (P H L : F[X]) : RatFunc F × RatFunc F :=
  (algebraMap F[X] (RatFunc F) P - algebraMap F[X] (RatFunc F) (affineMultiplier α β) *
      (algebraMap F[X] (RatFunc F) H / algebraMap F[X] (RatFunc F) L),
    algebraMap F[X] (RatFunc F) H / algebraMap F[X] (RatFunc F) L)

open Classical in
/-- Persistent candidates with distinct rational pairs share at most `d + 1` points. -/
private theorem card_inter_persistenceSet_le {domain : ι ↪ F} {f g : ι → F} {d : ℕ}
    {α₀ β₀ α₁ β₁ : F} {P₀ H₀ L₀ P₁ H₁ L₁ : F[X]} (hP₀ : P₀.degree ≤ d) (hP₁ : P₁.degree ≤ d)
    (hL₀ : L₀ ≠ 0) (hL₁ : L₁ ≠ 0) (hL₀d : L₀.degree ≤ 1) (hL₁d : L₁.degree ≤ 1)
    (hH₀ : H₀.degree ≤ d) (hH₁ : H₁.degree ≤ d)
    (hne : persistentPair α₀ β₀ P₀ H₀ L₀ ≠ persistentPair α₁ β₁ P₁ H₁ L₁) :
    #(persistenceSet domain f g α₀ β₀ P₀ H₀ L₀ ∩ persistenceSet domain f g α₁ β₁ P₁ H₁ L₁) ≤
      d + 1 := by
  set s := persistenceSet domain f g α₀ β₀ P₀ H₀ L₀ ∩ persistenceSet domain f g α₁ β₁ P₁ H₁ L₁
  have hmem : ∀ i ∈ s, (P₀.eval (domain i) = f i + (α₀ + β₀ * domain i) * g i ∧
      H₀.eval (domain i) = L₀.eval (domain i) * g i) ∧
      (P₁.eval (domain i) = f i + (α₁ + β₁ * domain i) * g i ∧
      H₁.eval (domain i) = L₁.eval (domain i) * g i) := by
    intro i hi
    simp only [s, persistenceSet, mem_inter, mem_filter, mem_polynomialAgreementSet,
      combinedWord_affineMultiplier] at hi
    exact ⟨⟨hi.1.1, hi.1.2.2⟩, ⟨hi.2.1, hi.2.2.2⟩⟩
  have hinj : Set.InjOn domain (s : Set ι) := domain.injective.injOn
  have hL₀' : algebraMap F[X] (RatFunc F) L₀ ≠ 0 :=
    (map_ne_zero_iff _ (RatFunc.algebraMap_injective F)).mpr hL₀
  have hL₁' : algebraMap F[X] (RatFunc F) L₁ ≠ 0 :=
    (map_ne_zero_iff _ (RatFunc.algebraMap_injective F)).mpr hL₁
  have nP₀ := natDegree_le_of_degree_le hP₀
  have nP₁ := natDegree_le_of_degree_le hP₁
  have nH₀ := natDegree_le_of_degree_le hH₀
  have nH₁ := natDegree_le_of_degree_le hH₁
  have nL₀ : L₀.natDegree ≤ 1 := natDegree_le_of_degree_le hL₀d
  have nL₁ : L₁.natDegree ≤ 1 := natDegree_le_of_degree_le hL₁d
  have nA₀ : (affineMultiplier α₀ β₀).natDegree ≤ 1 :=
    natDegree_le_of_degree_le (degree_affineMultiplier_le α₀ β₀)
  have nA₁ : (affineMultiplier α₁ β₁).natDegree ≤ 1 :=
    natDegree_le_of_degree_le (degree_affineMultiplier_le α₁ β₁)
  by_cases hG : algebraMap F[X] (RatFunc F) H₀ / algebraMap F[X] (RatFunc F) L₀ =
      algebraMap F[X] (RatFunc F) H₁ / algebraMap F[X] (RatFunc F) L₁
  · -- Equal second components: the first components differ.
    set R := (P₀ - P₁) * L₀ - (affineMultiplier α₀ β₀ - affineMultiplier α₁ β₁) * H₀
    have hR : R ≠ 0 := by
      intro hR
      refine hne (Prod.ext ?_ hG)
      have hR' := congrArg (algebraMap F[X] (RatFunc F)) hR
      simp only [R, map_sub, map_mul, map_zero] at hR'
      simp only [persistentPair, ← hG]
      field_simp
      linear_combination hR'
    refine (card_le_natDegree_of_injOn_of_eval_eq_zero hR hinj fun i hi ↦ ?_).trans ?_
    · obtain ⟨⟨h0, h0'⟩, ⟨h1, -⟩⟩ := hmem i hi
      simp only [R, eval_sub, eval_mul, eval_affineMultiplier, h0, h1, h0']
      ring
    · refine (natDegree_sub_le _ _).trans (max_le ?_ ?_)
      · exact (natDegree_mul_le).trans (by have := natDegree_sub_le P₀ P₁; omega)
      · exact (natDegree_mul_le).trans (by
          have := natDegree_sub_le (affineMultiplier α₀ β₀) (affineMultiplier α₁ β₁); omega)
  · -- Distinct second components.
    set R := H₀ * L₁ - H₁ * L₀
    have hR : R ≠ 0 := by
      intro hR
      refine hG ?_
      have hR' := congrArg (algebraMap F[X] (RatFunc F)) hR
      simp only [R, map_sub, map_mul, map_zero] at hR'
      rw [div_eq_div_iff hL₀' hL₁']
      linear_combination hR'
    refine (card_le_natDegree_of_injOn_of_eval_eq_zero hR hinj fun i hi ↦ ?_).trans ?_
    · obtain ⟨⟨-, h0⟩, ⟨-, h1⟩⟩ := hmem i hi
      simp only [R, eval_sub, eval_mul, h0, h1]
      ring
    · refine (natDegree_sub_le _ _).trans (max_le ?_ ?_)
      · exact (natDegree_mul_le).trans (by omega)
      · exact (natDegree_mul_le).trans (by omega)

open Classical in
/-- There are at most `ℓ · max q (n choose 2)` persistent exceptional challenges.

The factor `ℓ = n (B - d - 1) / (B² - n (d + 1))` bounds the number of rational pairs. -/
theorem card_isAffineExceptional_persistent_le [Fintype F] (domain : ι ↪ F) (f g : ι → F)
    {d A B : ℕ} (hdB : d + 1 < B) (hJ : Fintype.card ι * (d + 1) < B ^ 2) :
    (#{c : F × F | ∃ P, IsAffineExceptional domain f g d A 1 c.1 c.2 P ∧
        IsAffinePersistent domain f g d B c.1 c.2 P} : ℝ) ≤
      (Fintype.card ι : ℝ) * ((B : ℝ) - d - 1) / ((B : ℝ) ^ 2 - Fintype.card ι * (d + 1)) *
        max (Fintype.card F : ℝ) ((Fintype.card ι).choose 2) := by
  set C : Finset (F × F) := {c : F × F | ∃ P, IsAffineExceptional domain f g d A 1 c.1 c.2 P ∧
    IsAffinePersistent domain f g d B c.1 c.2 P}
  set M := max (Fintype.card F) ((Fintype.card ι).choose 2)
  have hdata : ∀ c : F × F, ∃ P H L : F[X], c ∈ C →
      IsAffineExceptional domain f g d A 1 c.1 c.2 P ∧ L ≠ 0 ∧ L.degree ≤ 1 ∧ H.degree ≤ d ∧
        B ≤ #(persistenceSet domain f g c.1 c.2 P H L) := by
    intro c
    by_cases hc : c ∈ C
    · obtain ⟨P, hex, H, L, hL, hLd, hH, hB⟩ := (mem_filter.mp hc).2
      exact ⟨P, H, L, fun _ ↦ ⟨hex, hL, hLd, hH, hB⟩⟩
    · exact ⟨0, 0, 0, fun h ↦ absurd h hc⟩
  choose P H L hdata using hdata
  set π : F × F → RatFunc F × RatFunc F := fun c ↦ persistentPair c.1 c.2 (P c) (H c) (L c)
  set T := C.image π
  -- Each rational pair accounts for at most `M` challenges.
  have hfiber : ∀ p ∈ T, #{c ∈ C | π c = p} ≤ M := by
    intro p _
    refine (card_le_card fun c hc ↦ ?_).trans
      (card_isAffineExceptional_ratFunc_le domain f g (d := d) (A := A) p.1 p.2)
    rw [mem_filter] at hc ⊢
    refine ⟨mem_univ _, P c, ?_, (hdata c hc.1).1⟩
    rw [← hc.2]
    simp only [π, persistentPair]
    ring
  have hCT : #C ≤ M * #T := card_le_mul_card_image C M hfiber
  -- Distinct rational pairs have almost disjoint persistence sets.
  have hrep : ∀ p ∈ T, ∃ c ∈ C, π c = p := fun p hp ↦ mem_image.mp hp
  choose! rep hrepC hrepπ using hrep
  have hJT := card_mul_sq_sub_card_mul_le_of_inter_card_le T
    (fun p ↦ persistenceSet domain f g (rep p).1 (rep p).2 (P (rep p)) (H (rep p)) (L (rep p)))
    B (d + 1) (fun p hp ↦ (hdata _ (hrepC p hp)).2.2.2.2) fun p hp p' hp' hne ↦ by
      have h₀ := hdata _ (hrepC p hp)
      have h₁ := hdata _ (hrepC p' hp')
      refine card_inter_persistenceSet_le h₀.1.1 h₁.1.1 h₀.2.1 h₁.2.1 h₀.2.2.1 h₁.2.2.1
        h₀.2.2.2.1 h₁.2.2.2.1 fun h ↦ hne ?_
      rw [← hrepπ p hp, ← hrepπ p' hp']
      exact h
  -- Real arithmetic.
  have hBB : Fintype.card ι * (d + 1) ≤ B * B := by rw [← sq]; exact hJ.le
  have hden : (0 : ℝ) < (B : ℝ) ^ 2 - Fintype.card ι * (d + 1) := by
    rw [sub_pos]
    exact_mod_cast hJ
  have hT : (#T : ℝ) ≤ (Fintype.card ι : ℝ) * ((B : ℝ) - d - 1) /
      ((B : ℝ) ^ 2 - Fintype.card ι * (d + 1)) := by
    rw [le_div_iff₀ hden]
    have hJT' : ((#T * (B * B - Fintype.card ι * (d + 1)) : ℕ) : ℝ) ≤
        ((Fintype.card ι * (B - (d + 1)) : ℕ) : ℝ) := by exact_mod_cast hJT
    push_cast [Nat.cast_sub hBB, Nat.cast_sub hdB.le] at hJT'
    linear_combination hJT'
  calc (#C : ℝ) ≤ (#T : ℝ) * (M : ℝ) := by
        rw [mul_comm]; exact_mod_cast hCT
    _ ≤ _ := by
        rw [show (M : ℝ) = max (Fintype.card F : ℝ) ((Fintype.card ι).choose 2) by
          simp [M]]
        exact mul_le_mul_of_nonneg_right hT (by positivity)

end ReedSolomon

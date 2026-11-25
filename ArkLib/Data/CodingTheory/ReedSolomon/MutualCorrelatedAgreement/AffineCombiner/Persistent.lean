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

A rational function `G = H / L` explains an agreement of a candidate `P`
if `G` agrees with `g` there.
A candidate is persistent at threshold `B` if one such function explains at least `B` agreements.
The numerator has degree at most `d`, and the nonzero denominator has degree at most one.
Only points where `L` does not vanish count toward persistence.
The rational partner `F₀ = P - (α + β X) G` agrees with `f` at those points as well.
The degree bound on `P` is supplied by exceptionality, rather than the persistence predicate.

Write `n` for the domain size and `q` for the field size.
For candidates of degree at most `d`, distinct rational pairs have persistence sets with
at most `d + 1` common points.
Under `d + 1 ≤ B` and `n (d + 1) < B²`, the Johnson bound limits the number of pairs.
Each pair accounts for at most `max q (n choose 2)` exceptional challenges with agreement loss one.

The count is stated for challenges drawn from a finite type `K` through an injective map
`φ : K ↪ E`, so from any finite subset of `E`.
Subfields are the main example, and the identity embedding gives the single-field count.
Then `q` is `|K|`, while words and candidates stay over `E`.
This form serves the interleaved count of Theorem 5.2 of [CWYZ26].

The count formalizes Lemma 4.5 of [CWYZ26].
It bounds all persistent exceptional challenges, including any excluded challenges from the
paper's interpolation argument.
The [paper page](../../../../../../docs/kb/papers/CWYZ26.md) records the statement correspondence.

## Main definitions

* `ReedSolomon.affinePersistenceSet`: candidate agreements explained by `H / L`, excluding poles.
* `ReedSolomon.IsAffinePersistent`: persistence of a candidate at threshold `B`.

## Main statements

* `ReedSolomon.mem_affinePersistenceSet`: membership in the persistence set.
* `ReedSolomon.card_isAffineExceptional_persistent_map_le`: the persistent exceptional count for
  challenges from a finite subset of `E`.

## References

* [Chiesa, A., Weissenberg, G., Yogev, E., and Zheng, K. Z.,
    *Affine combiners for Reed–Solomon proximity gaps*][CWYZ26]
-/

@[expose] public section

namespace ReedSolomon

open Polynomial Finset

variable {F : Type*} [Field F] [DecidableEq F] {ι : Type*} [Fintype ι]

/-- The agreement points of `P` where `L` does not vanish and `H = L g`. -/
noncomputable def affinePersistenceSet (domain : ι ↪ F) (f g : ι → F) (α β : F) (P H L : F[X]) :
    Finset ι :=
  {i ∈ polynomialAgreementSet domain (combinedWord domain f g (affineMultiplier α β)) P |
    L.eval (domain i) ≠ 0 ∧ H.eval (domain i) = L.eval (domain i) * g i}

/-- A persistence point is a candidate agreement where `L` is nonzero and `H = L g`. -/
@[simp]
theorem mem_affinePersistenceSet (domain : ι ↪ F) (f g : ι → F) (α β : F)
    (P H L : F[X]) (i : ι) :
    i ∈ affinePersistenceSet domain f g α β P H L ↔
      P.eval (domain i) = f i + (α + β * domain i) * g i ∧
        L.eval (domain i) ≠ 0 ∧ H.eval (domain i) = L.eval (domain i) * g i := by
  simp [affinePersistenceSet]

/-- `P` is persistent at threshold `B` for challenge `(α, β)` if a rational function `G = H / L`
agrees with `g` on at least `B` candidate agreement points where `L` does not vanish.
The numerator and denominator satisfy `deg H ≤ d`, `L ≠ 0`, and `deg L ≤ 1`.
The partner `P - (α + β X) G` agrees with `f` there too.
This predicate imposes no degree bound on `P`. -/
def IsAffinePersistent (domain : ι ↪ F) (f g : ι → F) (d B : ℕ) (α β : F) (P : F[X]) : Prop :=
  ∃ H L : F[X], L ≠ 0 ∧ L.degree ≤ 1 ∧ H.degree ≤ d ∧
    B ≤ #(affinePersistenceSet domain f g α β P H L)

/-- The rational pair `(P - (α + β X) H / L, H / L)`. -/
private noncomputable def persistentPair (α β : F) (P H L : F[X]) : RatFunc F × RatFunc F :=
  (algebraMap F[X] (RatFunc F) P - algebraMap F[X] (RatFunc F) (affineMultiplier α β) *
      (algebraMap F[X] (RatFunc F) H / algebraMap F[X] (RatFunc F) L),
    algebraMap F[X] (RatFunc F) H / algebraMap F[X] (RatFunc F) L)

open Classical in
/-- Persistence sets for candidates of degree at most `d` with distinct rational pairs
have at most `d + 1` common points. -/
private theorem card_inter_affinePersistenceSet_le {domain : ι ↪ F} {f g : ι → F} {d : ℕ}
    {α₀ β₀ α₁ β₁ : F} {P₀ H₀ L₀ P₁ H₁ L₁ : F[X]} (hP₀ : P₀.degree ≤ d) (hP₁ : P₁.degree ≤ d)
    (hL₀ : L₀ ≠ 0) (hL₁ : L₁ ≠ 0) (hL₀d : L₀.degree ≤ 1) (hL₁d : L₁.degree ≤ 1)
    (hH₀ : H₀.degree ≤ d) (hH₁ : H₁.degree ≤ d)
    (hne : persistentPair α₀ β₀ P₀ H₀ L₀ ≠ persistentPair α₁ β₁ P₁ H₁ L₁) :
    #(affinePersistenceSet domain f g α₀ β₀ P₀ H₀ L₀ ∩
      affinePersistenceSet domain f g α₁ β₁ P₁ H₁ L₁) ≤
      d + 1 := by
  set s := affinePersistenceSet domain f g α₀ β₀ P₀ H₀ L₀ ∩
      affinePersistenceSet domain f g α₁ β₁ P₁ H₁ L₁
  have hmem : ∀ i ∈ s, (P₀.eval (domain i) = f i + (α₀ + β₀ * domain i) * g i ∧
      H₀.eval (domain i) = L₀.eval (domain i) * g i) ∧
      (P₁.eval (domain i) = f i + (α₁ + β₁ * domain i) * g i ∧
      H₁.eval (domain i) = L₁.eval (domain i) * g i) := by
    intro i hi
    simp only [s, mem_inter, mem_affinePersistenceSet] at hi
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
/-- Let `φ : K ↪ E` be an injective map from a finite type, such as a subfield.
Let `n = |ι|` and `q = |K|`.
Assume `d + 1 ≤ B` and `n (d + 1) < B²`, and set `ℓ = n (B - d - 1) / (B² - n (d + 1))`.
Count the challenges `(α, β) ∈ K²` for which `(φ α, φ β)` has a persistent exceptional candidate.
The agreement loss is one.
There are at most `ℓ · max q (n choose 2)` such challenges.
The count is cast to `ℝ`, and the arithmetic defining `ℓ` is real arithmetic. -/
theorem card_isAffineExceptional_persistent_map_le {K E : Type*} [Fintype K] [Field E]
    [DecidableEq E] (domain : ι ↪ E) (f g : ι → E) (φ : K ↪ E) {d A B : ℕ} (hdB : d + 1 ≤ B)
    (hJ : Fintype.card ι * (d + 1) < B ^ 2) :
    (#{c : K × K | ∃ P, IsAffineExceptional domain f g d A 1 (φ c.1) (φ c.2) P ∧
        IsAffinePersistent domain f g d B (φ c.1) (φ c.2) P} : ℝ) ≤
      (Fintype.card ι : ℝ) * ((B : ℝ) - d - 1) / ((B : ℝ) ^ 2 - Fintype.card ι * (d + 1)) *
        max (Fintype.card K : ℝ) ((Fintype.card ι).choose 2) := by
  set C : Finset (K × K) := {c : K × K | ∃ P,
    IsAffineExceptional domain f g d A 1 (φ c.1) (φ c.2) P ∧
      IsAffinePersistent domain f g d B (φ c.1) (φ c.2) P}
  set M := max (Fintype.card K) ((Fintype.card ι).choose 2)
  have hdata : ∀ c : K × K, ∃ P H L : E[X], c ∈ C →
      IsAffineExceptional domain f g d A 1 (φ c.1) (φ c.2) P ∧ L ≠ 0 ∧ L.degree ≤ 1 ∧
        H.degree ≤ d ∧ B ≤ #(affinePersistenceSet domain f g (φ c.1) (φ c.2) P H L) := by
    intro c
    by_cases hc : c ∈ C
    · obtain ⟨P, hex, H, L, hL, hLd, hH, hB⟩ := (mem_filter.mp hc).2
      exact ⟨P, H, L, fun _ ↦ ⟨hex, hL, hLd, hH, hB⟩⟩
    · exact ⟨0, 0, 0, fun h ↦ absurd h hc⟩
  choose P H L hdata using hdata
  set π : K × K → RatFunc E × RatFunc E := fun c ↦
    persistentPair (φ c.1) (φ c.2) (P c) (H c) (L c)
  have h := card_le_of_fiber_card_le_of_inter_card_le C π
    (fun c ↦ affinePersistenceSet domain f g (φ c.1) (φ c.2) (P c) (H c) (L c)) (M := M) hdB
    (by rw [← sq]; exact hJ) (fun c hc ↦ (hdata c hc).2.2.2.2) (fun c hc c' hc' hne ↦
      card_inter_affinePersistenceSet_le (hdata c hc).1.1 (hdata c' hc').1.1 (hdata c hc).2.1
        (hdata c' hc').2.1 (hdata c hc).2.2.1 (hdata c' hc').2.2.1 (hdata c hc).2.2.2.1
        (hdata c' hc').2.2.2.1 hne) fun c hc ↦ by
    -- Each rational pair accounts for at most `M` challenges.
    refine (card_le_card fun c' hc' ↦ ?_).trans
      (card_isAffineExceptional_ratFunc_map_le domain f g φ (d := d) (A := A) (π c).1 (π c).2)
    rw [mem_filter] at hc' ⊢
    refine ⟨mem_univ _, P c', ?_, (hdata c' hc'.1).1⟩
    rw [← hc'.2]
    simp only [π, persistentPair]
    ring
  convert h using 2 <;> push_cast [M] <;> ring

end ReedSolomon

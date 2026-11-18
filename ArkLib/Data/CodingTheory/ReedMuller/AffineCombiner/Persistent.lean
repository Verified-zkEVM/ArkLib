/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Coratger
-/
module

public import ArkLib.Data.CodingTheory.ReedMuller.AffineCombiner.RationalPair
public import ArkLib.Data.Finset.PairwiseIntersection

/-!
# Persistent exceptional coefficient vectors on a grid

Let `K₀ ⊆ F` be finite fields of sizes `q₀ ≤ q`, and let `n = q₀ᵏ` be the grid size.
A rational function `G = H / L_σ` explains an agreement of a candidate `P` if `G` agrees with `g`.
Here `deg H ≤ d`, the vector `σ ∈ F^{k+1}` is nonzero, and degrees are total degrees.
Only grid points where `L_σ` does not vanish count toward persistence.
The partner `P - L_α G` agrees with `f` at those points as well.

Two distinct rational pairs explain at most `(d + 1) q₀ᵏ⁻¹` common points.
This is the grid Schwartz–Zippel lemma applied to a nonzero polynomial of degree at most `d + 1`.
The Johnson bound then limits the number of rational pairs.
By Lemma A.1, each pair accounts for at most `max q (n choose (k + 1))` exceptional vectors.

This formalizes the persistent count `|P| ≤ ℓ max{q, (n choose (k + 1))}` of Appendix A of [CWYZ26].
The paper writes `ℓ = (a - b) / (a² - b)` with `a = B / n` and `b = (d + 1) / q₀`.
The statement here writes `ℓ = n (B - (d + 1) q₀ᵏ⁻¹) / (B² - n (d + 1) q₀ᵏ⁻¹)`.
The two agree for `k ≥ 1`.
At `k = 0` the hypotheses leave nothing to count, since the grid has one point.
Its hypotheses `(d + 1) q₀ᵏ⁻¹ < B` and `n (d + 1) q₀ᵏ⁻¹ < B²` are `b < a` and `b < a²`.
The persistent count includes any excluded vectors of the interpolation argument.

Exponents `k - 1` use subtraction in `ℕ`.
The [paper page](../../../../../docs/kb/papers/CWYZ26.md) records the correspondence.

## Main definitions

* `ReedMuller.affinePersistenceSet`: candidate agreements explained by `H / L_σ`, off the zeros
  of `L_σ`.
* `ReedMuller.IsAffinePersistent`: persistence of a candidate at threshold `B`.

## Main statements

* `ReedMuller.mem_affinePersistenceSet`: membership in the persistence set.
* `ReedMuller.card_isAffineExceptional_persistent_le`: the persistent exceptional count.

## References

* [Chiesa, A., Weissenberg, G., Yogev, E., and Zheng, K. Z.,
    *Affine combiners for Reed–Solomon proximity gaps*][CWYZ26]
-/

@[expose] public section

namespace ReedMuller

open MvPolynomial Finset

variable {K₀ : Type*} [Field K₀] [Fintype K₀] {F : Type*} [Field F] [DecidableEq F]
  [Algebra K₀ F] {k : ℕ}

/-- The agreement points of `P` with `f + L_α g` where `L_σ` does not vanish and `H = L_σ g`. -/
noncomputable def affinePersistenceSet (f g : (Fin k → K₀) → F) (α : Fin (k + 1) → F)
    (P H : MvPolynomial (Fin k) F) (σ : Fin (k + 1) → F) : Finset (Fin k → K₀) :=
  {z ∈ agreementSet (combinedWord f g (affineMultiplier α)) P |
    eval (gridPoint F z) (affineMultiplier σ) ≠ 0 ∧
      eval (gridPoint F z) H = eval (gridPoint F z) (affineMultiplier σ) * g z}

/-- A persistence point is a candidate agreement where `L_σ` is nonzero and `H = L_σ g`. -/
@[simp]
theorem mem_affinePersistenceSet (f g : (Fin k → K₀) → F) (α : Fin (k + 1) → F)
    (P H : MvPolynomial (Fin k) F) (σ : Fin (k + 1) → F) (z : Fin k → K₀) :
    z ∈ affinePersistenceSet f g α P H σ ↔
      eval (gridPoint F z) P = combinedWord f g (affineMultiplier α) z ∧
        eval (gridPoint F z) (affineMultiplier σ) ≠ 0 ∧
        eval (gridPoint F z) H = eval (gridPoint F z) (affineMultiplier σ) * g z := by
  simp [affinePersistenceSet]

/-- `P` is persistent at threshold `B` for the coefficient vector `α`.

That is, a rational function `G = H / L_σ` agrees with `g` on at least `B` points.

These points are agreements of `P` with `f + L_α g` where `L_σ` does not vanish.

Here `L_σ = σ₀ + σ₁ X₁ + ⋯ + σₖ Xₖ` with `σ ≠ 0`, and `H` has total degree at most `d`.

The partner `P - L_α G` agrees with `f` there too.

This predicate imposes no degree bound on `P`. -/
def IsAffinePersistent (f g : (Fin k → K₀) → F) (d B : ℕ) (α : Fin (k + 1) → F)
    (P : MvPolynomial (Fin k) F) : Prop :=
  ∃ H : MvPolynomial (Fin k) F, ∃ σ : Fin (k + 1) → F, σ ≠ 0 ∧ H.totalDegree ≤ d ∧
    B ≤ #(affinePersistenceSet f g α P H σ)

/-- The rational pair `(P - L_α H / L_σ, H / L_σ)`. -/
private noncomputable def persistentPair (α : Fin (k + 1) → F) (P H : MvPolynomial (Fin k) F)
    (σ : Fin (k + 1) → F) :
    FractionRing (MvPolynomial (Fin k) F) × FractionRing (MvPolynomial (Fin k) F) :=
  (algebraMap _ _ P - algebraMap _ _ (affineMultiplier α) *
      (algebraMap _ _ H / algebraMap _ _ (affineMultiplier σ)),
    algebraMap _ _ H / algebraMap _ _ (affineMultiplier σ))

/-- Take two candidates of total degree at most `d` with distinct rational pairs.

Their persistence sets have at most `(d + 1) q₀ᵏ⁻¹` common points, where `q₀ = |K₀|`. -/
private theorem card_inter_affinePersistenceSet_le [DecidableEq K₀] {f g : (Fin k → K₀) → F} {d : ℕ}
    {α₀ α₁ σ₀ σ₁ : Fin (k + 1) → F} {P₀ H₀ P₁ H₁ : MvPolynomial (Fin k) F}
    (hP₀ : P₀.totalDegree ≤ d) (hP₁ : P₁.totalDegree ≤ d) (hσ₀ : σ₀ ≠ 0) (hσ₁ : σ₁ ≠ 0)
    (hH₀ : H₀.totalDegree ≤ d) (hH₁ : H₁.totalDegree ≤ d)
    (hne : persistentPair α₀ P₀ H₀ σ₀ ≠ persistentPair α₁ P₁ H₁ σ₁) :
    #(affinePersistenceSet f g α₀ P₀ H₀ σ₀ ∩ affinePersistenceSet f g α₁ P₁ H₁ σ₁) ≤
      (d + 1) * Fintype.card K₀ ^ (k - 1) := by
  set ι := algebraMap (MvPolynomial (Fin k) F) (FractionRing (MvPolynomial (Fin k) F))
  have hι : Function.Injective ι := IsFractionRing.injective _ _
  set L₀ := affineMultiplier σ₀
  set L₁ := affineMultiplier σ₁
  have hL₀ : ι L₀ ≠ 0 :=
    (map_ne_zero_iff ι hι).mpr (by simpa using affineMultiplier_injective.ne hσ₀)
  have hL₁ : ι L₁ ≠ 0 :=
    (map_ne_zero_iff ι hι).mpr (by simpa using affineMultiplier_injective.ne hσ₁)
  have nL₀ : L₀.totalDegree ≤ 1 := totalDegree_affineMultiplier_le σ₀
  have nL₁ : L₁.totalDegree ≤ 1 := totalDegree_affineMultiplier_le σ₁
  have nA : (affineMultiplier α₀ - affineMultiplier α₁).totalDegree ≤ 1 :=
    (totalDegree_sub _ _).trans
      (max_le (totalDegree_affineMultiplier_le α₀) (totalDegree_affineMultiplier_le α₁))
  -- A nonzero polynomial of total degree at most `d + 1` vanishing on the intersection.
  obtain ⟨R, hR, hRdeg, hRzero⟩ : ∃ R : MvPolynomial (Fin k) F, R ≠ 0 ∧ R.totalDegree ≤ d + 1 ∧
      ∀ z ∈ affinePersistenceSet f g α₀ P₀ H₀ σ₀ ∩ affinePersistenceSet f g α₁ P₁ H₁ σ₁,
        eval (gridPoint F z) R = 0 := by
    by_cases hG : ι H₀ / ι L₀ = ι H₁ / ι L₁
    · -- Equal second components: the first components differ.
      refine ⟨(P₀ - P₁) * L₀ - (affineMultiplier α₀ - affineMultiplier α₁) * H₀, ?_, ?_, ?_⟩
      · intro hR
        refine hne (Prod.ext ?_ hG)
        have hR' := congrArg ι hR
        simp only [map_sub, map_mul, map_zero] at hR'
        have hP : ι P₀ - ι P₁ =
            (ι (affineMultiplier α₀) - ι (affineMultiplier α₁)) * (ι H₀ / ι L₀) := by
          rw [mul_div_assoc', eq_div_iff hL₀]
          linear_combination hR'
        change ι P₀ - ι (affineMultiplier α₀) * (ι H₀ / ι L₀) =
          ι P₁ - ι (affineMultiplier α₁) * (ι H₁ / ι L₁)
        rw [← hG]
        linear_combination hP
      · refine (totalDegree_sub _ _).trans (max_le ?_ ?_)
        · exact (totalDegree_mul _ _).trans (by
            have := (totalDegree_sub P₀ P₁).trans (max_le hP₀ hP₁); omega)
        · exact (totalDegree_mul _ _).trans (by omega)
      · intro z hz
        simp only [mem_inter, mem_affinePersistenceSet, combinedWord_apply] at hz
        obtain ⟨⟨h0, -, h0'⟩, ⟨h1, -, -⟩⟩ := hz
        simp only [map_sub, map_mul, h0, h1, h0', L₀]
        ring
    · -- Distinct second components.
      refine ⟨H₀ * L₁ - H₁ * L₀, ?_, ?_, ?_⟩
      · intro hR
        refine hG ?_
        have hR' := congrArg ι hR
        simp only [map_sub, map_mul, map_zero] at hR'
        rw [div_eq_div_iff hL₀ hL₁]
        linear_combination hR'
      · refine (totalDegree_sub _ _).trans (max_le ?_ ?_)
        · exact (totalDegree_mul _ _).trans (by omega)
        · exact (totalDegree_mul _ _).trans (by omega)
      · intro z hz
        simp only [mem_inter, mem_affinePersistenceSet] at hz
        obtain ⟨⟨-, -, h0⟩, ⟨-, -, h1⟩⟩ := hz
        simp only [map_sub, map_mul, h0, h1, L₀, L₁]
        ring
  -- The grid Schwartz–Zippel lemma.
  refine (card_le_card fun z hz ↦ mem_filter.mpr ⟨mem_univ _, hRzero z hz⟩).trans
    ((card_grid_eval_eq_zero_le (K₀ := K₀) hR).trans ?_)
  exact Nat.mul_le_mul_right _ hRdeg

open Classical in
/-- Let `K₀ ⊆ F` be finite fields of sizes `q₀` and `q`.

The grid `K₀ᵏ` has `n = q₀ᵏ` points, and words `f, g` on it take values in `F`.

Assume `(d + 1) q₀ᵏ⁻¹ < B` and `n (d + 1) q₀ᵏ⁻¹ < B²`.

Candidates have total degree at most `d` and at least `A` agreements with `f + L_α g`.

Count the vectors `α ∈ F^{k+1}` with an exceptional candidate that is persistent at threshold `B`.

There are at most `ℓ · max q (n choose (k + 1))` of them.

Exceptional means that no witnesses `P = F₀ + L_α G₀` have agreement loss at most `q₀ᵏ⁻¹`.

Here witnesses satisfy `deg F₀ ≤ d`, and `G₀ = 0` or `deg G₀ < d`, with total degrees.

Here `ℓ = n (B - (d + 1) q₀ᵏ⁻¹) / (B² - n (d + 1) q₀ᵏ⁻¹)`, in real arithmetic.

Exponents `k - 1` use subtraction in `ℕ`. -/
theorem card_isAffineExceptional_persistent_le [Fintype F] (f g : (Fin k → K₀) → F)
    {d A B : ℕ} (hdB : (d + 1) * Fintype.card K₀ ^ (k - 1) < B)
    (hJ : Fintype.card K₀ ^ k * ((d + 1) * Fintype.card K₀ ^ (k - 1)) < B ^ 2) :
    (#{α : Fin (k + 1) → F | ∃ P, IsAffineExceptional f g d A (Fintype.card K₀ ^ (k - 1)) α P ∧
        IsAffinePersistent f g d B α P} : ℝ) ≤
      (Fintype.card K₀ : ℝ) ^ k * ((B : ℝ) - (d + 1) * (Fintype.card K₀ : ℝ) ^ (k - 1)) /
          ((B : ℝ) ^ 2 - (Fintype.card K₀ : ℝ) ^ k * ((d + 1) * (Fintype.card K₀ : ℝ) ^ (k - 1))) *
        max (Fintype.card F : ℝ) ((Fintype.card K₀ ^ k).choose (k + 1)) := by
  classical
  set C : Finset (Fin (k + 1) → F) := {α | ∃ P, IsAffineExceptional f g d A
    (Fintype.card K₀ ^ (k - 1)) α P ∧ IsAffinePersistent f g d B α P}
  have hdata : ∀ α : Fin (k + 1) → F, ∃ P H : MvPolynomial (Fin k) F, ∃ σ : Fin (k + 1) → F,
      α ∈ C → IsAffineExceptional f g d A (Fintype.card K₀ ^ (k - 1)) α P ∧ σ ≠ 0 ∧
        H.totalDegree ≤ d ∧ B ≤ #(affinePersistenceSet f g α P H σ) := by
    intro α
    by_cases hα : α ∈ C
    · obtain ⟨P, hex, H, σ, hσ, hH, hB⟩ := (mem_filter.mp hα).2
      exact ⟨P, H, σ, fun _ ↦ ⟨hex, hσ, hH, hB⟩⟩
    · exact ⟨0, 0, 0, fun h ↦ absurd h hα⟩
  choose P H σ hdata using hdata
  set π := fun α ↦ persistentPair α (P α) (H α) (σ α)
  have h := card_le_of_fiber_card_le_of_inter_card_le C π
    (fun α ↦ affinePersistenceSet f g α (P α) (H α) (σ α))
    (M := max (Fintype.card F) ((Fintype.card K₀ ^ k).choose (k + 1))) hdB.le
    (by simpa [← sq] using hJ) (fun α hα ↦ (hdata α hα).2.2.2) (fun α hα α' hα' hne ↦
      card_inter_affinePersistenceSet_le (hdata α hα).1.1 (hdata α' hα').1.1 (hdata α hα).2.1
        (hdata α' hα').2.1 (hdata α hα).2.2.1 (hdata α' hα').2.2.1 hne) fun α hα ↦ by
    -- Each rational pair accounts for at most `max q (n choose (k + 1))` vectors (Lemma A.1).
    refine (card_le_card fun α' hα' ↦ ?_).trans
      (card_isAffineExceptional_fractionRing_le f g (d := d) (A := A) (π α).1 (π α).2)
    rw [mem_filter] at hα' ⊢
    refine ⟨mem_univ _, P α', ?_, (hdata α' hα'.1).1⟩
    rw [← hα'.2]
    simp only [π, persistentPair]
    ring
  convert h using 2 <;> simp [sq]

end ReedMuller

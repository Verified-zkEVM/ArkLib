/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Coratger
-/
module

public import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.AffineCombiner.PersistenceDescent
public import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.AffineCombiner.TaylorChart
public import ArkLib.Data.Polynomial.SpecializationAvoidance
public import ArkLib.ToMathlib.RingTheory.Nullstellensatz.AgreementIncidence

/-!
# Counting nonpersistent challenges in the Taylor chart

Fix polynomials `θⱼ`, indexed by a finite type `κ`, and the multipliers `L = ∑ⱼ aⱼ θⱼ`.
A challenge `a` with a simple root `P(X ^ s)` of a factor `R` along `L` gives a chart point.
Here `s` is a power of the exponential characteristic and `P` has degree at most `d`.
The point lies on the hypersurface `R(c, L(c), y₀) = 0`.

Each position `i` has a linear functional `Λᵢ` on polynomials and a target `Tᵢ(a)`.
The position agrees when `Λᵢ` of the reconstructed root is `Tᵢ(a)`.
High cuts are further functionals that every counted root satisfies.
They describe the image of the trace substitution for Reed–Muller codes.

Let `n` be the number of positions and `h` the `(Y, Z)`-degree of `R`.
Each counted point has at least `A` agreements.
The persistence threshold is `B`.
A nonzero difference of two multipliers vanishes at at most `e` positions.
So `e = 1` for Reed–Solomon codes and `e = n / q₀` for Reed–Muller codes.
Here `q₀` is the size of the subfield of the Reed–Muller grid.

A point is excluded when a regular point on another challenge shares `B + e` agreements.
The points off the excluded set number at most `h · (n · 2 s d h / (A - B - e + 1)) ^ |κ|`.
The subtraction is natural-number subtraction.
Each code converts exclusion into its own persistence notion.

For Reed–Solomon codes, `κ = Fin 2`, `θ = (1, X)`, `e = 1`, and there are no high cuts.
Their functional `Λᵢ` is evaluation at the position.
A Reed–Solomon excluded point is persistent after descent to the base field.

The excluded set is a predicate, with no algorithmic witness selection.

These statements are Claims 4.8 and 4.9 and Lemma 4.7 for one factor.
Appendix A uses them with `|κ| = k + 1` and the cut threshold `B + n / q₀`.
The paper intersects its algebraic sets with the image of the trace substitution.
The high cuts are the equations of that image, and they add no degree factor.

The Reed–Solomon count for one factor is the generic factor count of the exceptional count.

The [paper page](../../../../../../docs/kb/papers/CWYZ26.md) records the correspondence.

## Main definitions

* `ReedSolomon.SeparatesDegree`: the functionals determine polynomials of bounded degree.
* `ReedSolomon.chartExcluded`: points sharing `B + e` agreements with another challenge.
* `ReedSolomon.affineChartTarget`: the Reed–Solomon target of one position.

## Main statements

* `ReedSolomon.mem_chartExcluded`: membership in the excluded set.
* `ReedSolomon.separatesDegree_leval`: evaluations at distinct points determine polynomials.
* `ReedSolomon.eq_of_separatesDegree`: two points on the same challenge with `B + e` common
  agreements are equal.
* `ReedSolomon.regularLocus_subset_chartExcluded`: the regular points of a
  positive-dimensional component with `B + e` cuts belong to the excluded set.
* `ReedSolomon.card_le_of_regular_chartPoints`: the incidence count of regular chart points.
* `ReedSolomon.exists_chartExcluded_finset_card_le`: outside few challenges, every regular
  root with `A` agreements has an excluded chart point.
* `ReedSolomon.totalDegree_affineChartTarget_le` and
  `ReedSolomon.eval_map_eq_aeval_affineChartTarget_iff`: the Reed–Solomon targets.
* `ReedSolomon.isAffinePersistent_of_mem_chartExcluded`: a Reed–Solomon excluded point is
  persistent.

## References

* [Chiesa, A., Weissenberg, G., Yogev, E., and Zheng, K. Z.,
    *Affine combiners for Reed–Solomon proximity gaps*][CWYZ26], Claims 4.8 and 4.9,
    Lemma 4.7 and Appendix A.
-/

@[expose] public section

namespace ReedSolomon

open MvPolynomial
open scoped Finset

section Generic

variable {E : Type*} [Field E] {κ : Type*} {ι : Type*}

/-- The functionals determine polynomials of degree at most `d` from `threshold` positions.

Let `H` have degree at most `d` and be killed by every high cut.
If `Λᵢ H = 0` for `threshold` positions `i`, then `H = 0`. -/
def SeparatesDegree (highCuts : List (Polynomial E →ₗ[E] E)) (Λ : ι → Polynomial E →ₗ[E] E)
    (d threshold : ℕ) : Prop :=
  ∀ U : Finset ι, threshold ≤ #U → ∀ H : Polynomial E, H.degree ≤ d →
    (∀ Λ' ∈ highCuts, Λ' H = 0) → (∀ i ∈ U, Λ i H = 0) → H = 0

/-- Evaluations at distinct points determine polynomials of degree `d` from `d + 1` points. -/
theorem separatesDegree_leval {x : ι → E} (hx : x.Injective) {d threshold : ℕ}
    (hd : d < threshold) : SeparatesDegree [] (fun i ↦ Polynomial.leval (x i)) d threshold := by
  classical
  intro U hU H hH _ hzero
  refine Polynomial.eq_zero_of_degree_lt_of_eval_finset_eq_zero (U.image x) ?_ ?_
  · rw [Finset.card_image_of_injective _ hx]
    exact hH.trans_lt (by exact_mod_cast (by omega : d < #U))
  · intro y hy
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hy
    simpa using hzero i hi

variable [Fintype κ]

/-- Chart points on `B + e` agreements shared with a regular point on another challenge.

The reconstruction of the other point is also killed by every high cut. -/
def chartExcluded (c : E) (θ : κ → Polynomial E) (R : MvPolynomial AffineVar E)
    (s d B e : ℕ) (highCuts : List (Polynomial E →ₗ[E] E)) (Λ : ι → Polynomial E →ₗ[E] E)
    (target : ι → MvPolynomial κ E) : Set (ChartVar κ → E) :=
  {pt | ∃ U : Finset ι, B + e ≤ #U ∧
    (∀ i ∈ U, Λ i (chartPolynomial c θ R s d pt) = aeval (pt ∘ Sum.inr) (target i)) ∧
    ∃ pt' : ChartVar κ → E, aeval pt' (chartSeparant c θ R) ≠ 0 ∧
      (∀ Λ' ∈ highCuts, Λ' (chartPolynomial c θ R s d pt') = 0) ∧
      (∀ i ∈ U, Λ i (chartPolynomial c θ R s d pt') = aeval (pt' ∘ Sum.inr) (target i)) ∧
      pt' ∘ Sum.inr ≠ pt ∘ Sum.inr}

/-- A point is excluded when it shares `B + e` agreements with a regular point elsewhere. -/
@[simp] theorem mem_chartExcluded (c : E) (θ : κ → Polynomial E) (R : MvPolynomial AffineVar E)
    (s d B e : ℕ) (highCuts : List (Polynomial E →ₗ[E] E)) (Λ : ι → Polynomial E →ₗ[E] E)
    (target : ι → MvPolynomial κ E) (pt : ChartVar κ → E) :
    pt ∈ chartExcluded c θ R s d B e highCuts Λ target ↔ ∃ U : Finset ι, B + e ≤ #U ∧
      (∀ i ∈ U, Λ i (chartPolynomial c θ R s d pt) = aeval (pt ∘ Sum.inr) (target i)) ∧
      ∃ pt' : ChartVar κ → E, aeval pt' (chartSeparant c θ R) ≠ 0 ∧
        (∀ Λ' ∈ highCuts, Λ' (chartPolynomial c θ R s d pt') = 0) ∧
        (∀ i ∈ U, Λ i (chartPolynomial c θ R s d pt') = aeval (pt' ∘ Sum.inr) (target i)) ∧
        pt' ∘ Sum.inr ≠ pt ∘ Sum.inr :=
  Iff.rfl

/-- Two points on the same challenge with `B + e` common agreements are equal.

Assume the functionals determine polynomials of degree at most `d` from `B + e` positions.
Both reconstructions are killed by the high cuts and agree with the targets on `U`. -/
theorem eq_of_separatesDegree (c : E) (θ : κ → Polynomial E) (R : MvPolynomial AffineVar E)
    {s d B e : ℕ} {highCuts : List (Polynomial E →ₗ[E] E)} {Λ : ι → Polynomial E →ₗ[E] E}
    {target : ι → MvPolynomial κ E} (hsep : SeparatesDegree highCuts Λ d (B + e))
    (U : Finset ι) (hU : B + e ≤ #U) {pt pt' : ChartVar κ → E}
    (hhigh : ∀ Λ' ∈ highCuts, Λ' (chartPolynomial c θ R s d pt) = 0)
    (hhigh' : ∀ Λ' ∈ highCuts, Λ' (chartPolynomial c θ R s d pt') = 0)
    (hagree : ∀ i ∈ U, Λ i (chartPolynomial c θ R s d pt) = aeval (pt ∘ Sum.inr) (target i))
    (hagree' : ∀ i ∈ U, Λ i (chartPolynomial c θ R s d pt') = aeval (pt' ∘ Sum.inr) (target i))
    (hab : pt' ∘ Sum.inr = pt ∘ Sum.inr) : pt' = pt := by
  -- The difference of the reconstructions is killed by `B + e` functionals, so it vanishes.
  have hrec : chartPolynomial c θ R s d pt' = chartPolynomial c θ R s d pt := by
    refine sub_eq_zero.mp (hsep U hU _ ((Polynomial.degree_sub_le _ _).trans
      (max_le (degree_chartPolynomial_le c θ R s d pt')
        (degree_chartPolynomial_le c θ R s d pt))) (fun Λ' hΛ' ↦ ?_) fun i hi ↦ ?_)
    · rw [map_sub, hhigh' Λ' hΛ', hhigh Λ' hΛ', sub_self]
    · rw [map_sub, hagree' i hi, hagree i hi, hab, sub_self]
  funext v
  rcases v with ⟨j⟩ | ⟨j⟩
  · obtain rfl : j = 0 := Subsingleton.elim _ _
    rw [← eval_chartPolynomial_center c θ R s d pt', ← eval_chartPolynomial_center c θ R s d pt,
      hrec]
  · exact congrFun hab j

/-- A positive-dimensional prime with `B + e` agreement cuts has its regular points excluded.

Assume the separant is not in the prime ideal and every high cut lies in it.
Assume `2 s d - 1 ≤ τ`, with natural-number subtraction.
Assume the functionals determine polynomials of degree at most `d` from `B + e` positions.
The regular locus is infinite, and two of its points on the same challenge are equal. -/
theorem regularLocus_subset_chartExcluded [IsAlgClosed E] (c : E) (θ : κ → Polynomial E)
    (R : MvPolynomial AffineVar E) {s d τ B e : ℕ} (hτ : 2 * s * d - 1 ≤ τ)
    {highCuts : List (Polynomial E →ₗ[E] E)} {Λ : ι → Polynomial E →ₗ[E] E}
    {target : ι → MvPolynomial κ E} (hsep : SeparatesDegree highCuts Λ d (B + e))
    (J : Ideal (MvPolynomial (ChartVar κ) E)) (hJ : J.IsPrime)
    (hs : chartSeparant c θ R ∉ J)
    (hhigh : ∀ Λ' ∈ highCuts, chartFunctionalCut c θ R s d τ Λ' ∈ J)
    (hdim : 0 < (affineHilbertPolynomial J).natDegree)
    (hcuts : B + e ≤ {i | chartAgreementCut c θ R s d τ (Λ i) (rename Sum.inr (target i)) ∈
      J}.ncard) :
    {pt | pt ∈ zeroLocus E J ∧ aeval pt (chartSeparant c θ R) ≠ 0} ⊆
      chartExcluded c θ R s d B e highCuts Λ target := by
  classical
  set U := {pt | pt ∈ zeroLocus E J ∧ aeval pt (chartSeparant c θ R) ≠ 0}
  have hregular : IsLeftRegular (Ideal.Quotient.mk J (chartSeparant c θ R)) :=
    IsLeftCancelMulZero.mul_left_cancel_of_ne_zero (mt Ideal.Quotient.eq_zero_iff_mem.mp hs)
  have hinfinite : U.Infinite := fun hfin ↦ by
    have := (finite_principalOpen_iff_natDegree_affineHilbertPolynomial_eq_zero hregular).mp hfin
    omega
  obtain ⟨T, hT, hTJ⟩ : ∃ T : Finset ι, B + e ≤ #T ∧
      ∀ i ∈ T, chartAgreementCut c θ R s d τ (Λ i) (rename Sum.inr (target i)) ∈ J := by
    rcases Nat.eq_zero_or_pos (B + e) with h0 | hpos
    · exact ⟨∅, by simp [h0], by simp⟩
    · have hfin := Set.finite_of_ncard_pos (hpos.trans_le hcuts)
      exact ⟨hfin.toFinset, by rwa [← Set.ncard_eq_toFinset_card _ hfin],
        fun i hi ↦ hfin.mem_toFinset.mp hi⟩
  -- On the regular locus, the cuts in `J` and the high cuts say what the reconstruction does.
  have hcutU : ∀ pt ∈ U, ∀ i ∈ T,
      Λ i (chartPolynomial c θ R s d pt) = aeval (pt ∘ Sum.inr) (target i) := by
    intro pt hpt i hi
    rw [← aeval_rename, ← chartAgreementCut_eq_zero_iff c θ R hτ _ _ pt hpt.2]
    exact hpt.1 _ (hTJ i hi)
  have hhighU : ∀ pt ∈ U, ∀ Λ' ∈ highCuts, Λ' (chartPolynomial c θ R s d pt) = 0 :=
    fun pt hpt Λ' hΛ' ↦ (chartFunctionalCut_eq_zero_iff c θ R hτ Λ' pt hpt.2).mp
      (hpt.1 _ (hhigh Λ' hΛ'))
  intro pt hpt
  refine ⟨T, hT, hcutU pt hpt, ?_⟩
  by_contra! hsame
  -- Every regular point has the challenge of `pt`, so it is `pt`.
  refine hinfinite ((Set.finite_singleton pt).subset fun pt' hpt' ↦ ?_)
  exact eq_of_separatesDegree c θ R hsep T hT (hhighU pt hpt) (hhighU pt' hpt')
    (hcutU pt hpt) (hcutU pt' hpt') (hsame pt' hpt'.2 (hhighU pt' hpt') (hcutU pt' hpt'))

variable [Fintype ι]

/-- The regular chart points with `A` agreements, off the excluded set, are few.

Let `n` be the number of positions and `h` bound the `(Y, Z)`-degree of `R`.
Assume `1 ≤ d`, `1 ≤ s`, `1 ≤ B + e ≤ A ≤ n`, and targets of degree at most `s`.
Assume the functionals determine polynomials of degree at most `d` from `B + e` positions.
Each point of `S` lies on the chart hypersurface and is regular.
Its reconstruction is killed by every high cut.
The bound is `h · (n · 2 s d h / (A - B - e + 1)) ^ |κ|`, with natural-number subtraction. -/
theorem card_le_of_regular_chartPoints [IsAlgClosed E] (c : E) (θ : κ → Polynomial E)
    (R : MvPolynomial AffineVar E) {s d h A B e : ℕ} (hd : 1 ≤ d) (hs : 1 ≤ s) (hBe : 1 ≤ B + e)
    (hBA : B + e ≤ A) (hAn : A ≤ Fintype.card ι)
    (hR : R.weightedTotalDegree affineYZWeight ≤ h) (highCuts : List (Polynomial E →ₗ[E] E))
    (Λ : ι → Polynomial E →ₗ[E] E) (target : ι → MvPolynomial κ E)
    (htarget : ∀ i, (target i).totalDegree ≤ s) (hsep : SeparatesDegree highCuts Λ d (B + e))
    (S : Finset (ChartVar κ → E))
    (hS : ∀ pt ∈ S, aeval pt (chartEquation c θ R) = 0 ∧ aeval pt (chartSeparant c θ R) ≠ 0 ∧
      (∀ Λ' ∈ highCuts, Λ' (chartPolynomial c θ R s d pt) = 0) ∧
      pt ∉ chartExcluded c θ R s d B e highCuts Λ target)
    (hA : ∀ pt ∈ S, A ≤
      {i | Λ i (chartPolynomial c θ R s d pt) = aeval (pt ∘ Sum.inr) (target i)}.ncard) :
    (#S : ℚ) ≤ h * (((Fintype.card ι * (2 * s * d * h) : ℕ) : ℚ) /
      ((A - B - e + 1 : ℕ) : ℚ)) ^ Fintype.card κ := by
  classical
  obtain rfl | ⟨pt₀, hpt₀⟩ := S.eq_empty_or_nonempty
  · simp only [Finset.card_empty, Nat.cast_zero]
    positivity
  set τ := 2 * s * d - 1
  have hsepR : chartSeparant c θ R ≠ 0 := fun h0 ↦ (hS pt₀ hpt₀).2.1 (by rw [h0, map_zero])
  have hg : chartEquation c θ R ≠ 0 := fun h0 ↦
    hsepR (by rw [← pderiv_chartEquation, h0, map_zero])
  have hbound := card_le_of_agreement_off_excluded_of_hypersurface (K := E) hg
    (chartSeparant c θ R) (totalDegree_chartEquation_le c θ hR)
    (highCuts.map (chartFunctionalCut c θ R s d τ))
    (by
      simp only [List.mem_map]
      rintro _ ⟨Λ', -, rfl⟩
      exact totalDegree_chartFunctionalCut_le c θ hR hd hs Λ')
    (fun i ↦ chartAgreementCut c θ R s d τ (Λ i) (rename Sum.inr (target i)))
    (fun i ↦ totalDegree_chartAgreementCut_le c θ hR hd hs _
      ((totalDegree_rename_le _ _).trans (htarget i)))
    (L := B + e) (A := A) hBA (by omega)
    (chartExcluded c θ R s d B e highCuts Λ target)
    (fun J hJ hsJ _ hhigh hdim hL ↦ regularLocus_subset_chartExcluded c θ R le_rfl hsep J hJ hsJ
      (fun Λ' hΛ' ↦ hhigh _ (List.mem_map_of_mem hΛ')) hdim hL)
    S
    (by
      intro pt hpt
      obtain ⟨heq, hsp, hhigh, hex⟩ := hS pt hpt
      refine ⟨heq, hsp, ?_, hex⟩
      simp only [List.mem_map]
      rintro _ ⟨Λ', hΛ', rfl⟩
      exact (chartFunctionalCut_eq_zero_iff c θ R le_rfl Λ' pt hsp).mpr (hhigh Λ' hΛ'))
    (by
      intro pt hpt
      refine (hA pt hpt).trans_eq (congrArg Set.ncard (Set.ext fun i ↦ ?_))
      rw [Set.mem_ofPred_eq, Set.mem_ofPred_eq,
        chartAgreementCut_eq_zero_iff c θ R le_rfl _ _ pt (hS pt hpt).2.1, aeval_rename])
  have hσ : Nat.card (ChartVar κ) - 1 = Fintype.card κ := by
    simp [Nat.card_eq_fintype_card, Fintype.card_sum]
  rwa [hσ, ← Nat.sub_sub] at hbound

/-- Outside few challenges, every regular root with `A` agreements has an excluded chart point.

The challenges form a finite type, with injective coefficient vectors `a`.
Let `n` be the number of positions, `p` the exponential characteristic, and `s = p ^ r`.
Let `h` bound the `(Y, Z)`-degree of `R`.
Assume `1 ≤ d`, `1 ≤ B + e ≤ A ≤ n`, and targets of degree at most `s`.
Assume the functionals determine polynomials of degree at most `d` from `B + e` positions.
At most `h · (n · 2 s d h / (A - B - e + 1)) ^ |κ|` challenges are left out.
The subtraction is natural-number subtraction.
Take any other challenge and a root `P(X ^ s)` with `deg P ≤ d`, killed by the high cuts.
Some center `c` with nonzero separant puts its chart point in the excluded set. -/
theorem exists_chartExcluded_finset_card_le {Γ : Type*} [Finite Γ] [IsAlgClosed E]
    (θ : κ → Polynomial E) (R : MvPolynomial AffineVar E) (p r : ℕ) [ExpChar E p]
    {d h A B e : ℕ} (hd : 1 ≤ d) (hBe : 1 ≤ B + e) (hBA : B + e ≤ A) (hAn : A ≤ Fintype.card ι)
    (hR : R.weightedTotalDegree affineYZWeight ≤ h) (highCuts : List (Polynomial E →ₗ[E] E))
    (Λ : ι → Polynomial E →ₗ[E] E) (target : ι → MvPolynomial κ E)
    (htarget : ∀ i, (target i).totalDegree ≤ p ^ r)
    (hsep : SeparatesDegree highCuts Λ d (B + e)) (a : Γ → κ → E) (ha : a.Injective) :
    ∃ ex : Finset Γ, (#ex : ℚ) ≤ h * (((Fintype.card ι * (2 * p ^ r * d * h) : ℕ) : ℚ) /
        ((A - B - e + 1 : ℕ) : ℚ)) ^ Fintype.card κ ∧
      ∀ γ ∉ ex, ∀ P : Polynomial E, P.degree ≤ d →
        multiplierEval (familyMultiplier θ (a γ)) (Polynomial.expand E (p ^ r) P) R = 0 →
        multiplierEval (familyMultiplier θ (a γ)) (Polynomial.expand E (p ^ r) P)
          (pderiv none R) ≠ 0 →
        (∀ Λ' ∈ highCuts, Λ' P = 0) →
        A ≤ {i | Λ i P = aeval (a γ) (target i)}.ncard →
        ∃ c : E, (multiplierEval (familyMultiplier θ (a γ)) (Polynomial.expand E (p ^ r) P)
            (pderiv none R)).eval c ≠ 0 ∧
          chartPoint c (p ^ r) (a γ) P ∈ chartExcluded c θ R (p ^ r) d B e highCuts Λ target := by
  classical
  have := Fintype.ofFinite Γ
  set s := p ^ r
  -- A challenge is bad when some regular root with `A` agreements is never excluded.
  let Bad (γ : Γ) (P : Polynomial E) : Prop := P.degree ≤ d ∧
    multiplierEval (familyMultiplier θ (a γ)) (Polynomial.expand E s P) R = 0 ∧
    multiplierEval (familyMultiplier θ (a γ)) (Polynomial.expand E s P) (pderiv none R) ≠ 0 ∧
    (∀ Λ' ∈ highCuts, Λ' P = 0) ∧ A ≤ {i | Λ i P = aeval (a γ) (target i)}.ncard ∧
    ¬ ∃ c : E, (multiplierEval (familyMultiplier θ (a γ)) (Polynomial.expand E s P)
        (pderiv none R)).eval c ≠ 0 ∧
      chartPoint c s (a γ) P ∈ chartExcluded c θ R s d B e highCuts Λ target
  let ex : Finset Γ := {γ | ∃ P, Bad γ P}
  let w (γ : Γ) : Polynomial E := if hγ : ∃ P, Bad γ P then hγ.choose else 0
  have hw (γ) (hγ : γ ∈ ex) : Bad γ (w γ) := by
    have hγ' : ∃ P, Bad γ P := (Finset.mem_filter.mp hγ).2
    simpa only [w, hγ', ↓reduceDIte] using hγ'.choose_spec
  refine ⟨ex, ?_, fun γ hγ P hP hroot hsp hhigh hA ↦ ?_⟩
  · -- One center where every separant of a bad challenge is nonzero.
    obtain ⟨c, hc⟩ := Polynomial.exists_forall_eval_ne_zero ex _ fun γ hγ ↦ (hw γ hγ).2.2.1
    set pt : Γ → ChartVar κ → E := fun γ ↦ chartPoint c s (a γ) (w γ)
    have hinj : Set.InjOn pt ex := fun x _ y _ hxy ↦ ha (congrArg (· ∘ Sum.inr) hxy)
    have hrec (γ) (hγ : γ ∈ ex) : chartPolynomial c θ R s d (pt γ) = w γ :=
      chartPolynomial_point c θ R rfl (hw γ hγ).1 (hw γ hγ).2.1 (hc γ hγ)
    have hbound := card_le_of_regular_chartPoints c θ R hd
      (Nat.one_le_pow _ _ (expChar_pos E p)) hBe hBA hAn hR highCuts Λ target htarget hsep
      (ex.image pt)
      (by
        intro x hx
        obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.mp hx
        obtain ⟨-, hroot, -, hhigh, -, hnex⟩ := hw γ hγ
        refine ⟨?_, ?_, ?_, fun hex ↦ hnex ⟨c, hc γ hγ, hex⟩⟩
        · rw [aeval_chartEquation_point, hroot, Polynomial.eval_zero]
        · rw [aeval_chartSeparant_point]
          exact hc γ hγ
        · rw [hrec γ hγ]
          exact hhigh)
      (by
        intro x hx
        obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.mp hx
        rw [hrec γ hγ]
        exact (hw γ hγ).2.2.2.2.1)
    rwa [Finset.card_image_of_injOn hinj] at hbound
  · by_contra hnex
    exact hγ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, P, hP, hroot, hsp, hhigh, hA, hnex⟩)

end Generic

section Affine

variable {F : Type*} [Field F] {ι : Type*} {E : Type*} [Field E]

/-- The Reed–Solomon target `f(x) + (a₀ ^ s + x a₁ ^ s) g(x)` at the position `x`.

The received values and the position are mapped to `E`. -/
noncomputable def affineChartTarget (domain : ι ↪ F) (f g : ι → F) (φ : F →+* E) (s : ℕ)
    (i : ι) : MvPolynomial (Fin 2) E :=
  C (φ (f i)) + (X 0 ^ s + C (φ (domain i)) * X 1 ^ s) * C (φ (g i))

/-- The Reed–Solomon target has degree at most `s`. -/
theorem totalDegree_affineChartTarget_le (domain : ι ↪ F) (f g : ι → F) (φ : F →+* E) (s : ℕ)
    (i : ι) : (affineChartTarget domain f g φ s i).totalDegree ≤ s := by
  refine (totalDegree_add _ _).trans (max_le (by simp) ?_)
  refine (totalDegree_mul _ _).trans ?_
  rw [totalDegree_C, Nat.add_zero]
  refine (totalDegree_add _ _).trans (max_le ?_ ?_)
  · exact (totalDegree_pow _ _).trans (by simp [totalDegree_X])
  · refine (totalDegree_mul _ _).trans ?_
    rw [totalDegree_C, zero_add]
    exact (totalDegree_pow _ _).trans (by simp [totalDegree_X])

variable [DecidableEq F] [Fintype ι]

/-- At the Frobenius roots of `(φ α, φ β)`, the target is met exactly at an agreement position.

Here `p` is the exponential characteristic of `E` and `s = p ^ r`. -/
theorem eval_map_eq_aeval_affineChartTarget_iff (domain : ι ↪ F) (f g : ι → F) (φ : F →+* E)
    (p r : ℕ) [ExpChar E p] [PerfectRing E p] (α β : F) (P : Polynomial F) (i : ι) :
    (P.map φ).eval (φ (domain i)) = aeval ![(iterateFrobeniusEquiv E p r).symm (φ α),
        (iterateFrobeniusEquiv E p r).symm (φ β)] (affineChartTarget domain f g φ (p ^ r) i) ↔
      i ∈ polynomialAgreementSet domain (combinedWord domain f g (affineMultiplier α β)) P := by
  have hfr (x : E) : (iterateFrobeniusEquiv E p r).symm x ^ p ^ r = x := by
    rw [← iterateFrobeniusEquiv_def, RingEquiv.apply_symm_apply]
  simp only [affineChartTarget, map_add, map_mul, map_pow, aeval_C, aeval_X,
    Algebra.algebraMap_self, RingHom.id_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, hfr, polynomialAgreementSet, Finset.mem_filter, Finset.mem_univ,
    true_and, combinedWord_affineMultiplier, Polynomial.eval_map_apply]
  rw [← φ.injective.eq_iff]
  simp [map_add, map_mul, mul_comm]

/-- A regular root whose chart point is excluded is persistent.

Let `p` be the exponential characteristic of `E`, `s = p ^ r`, and `deg P ≤ d`.
The chart uses the family `(1, X)`, evaluations at the positions, and no high cuts.
The second challenge gives identities `P' - P = L g`, which descend to `F`.
Discarding at most one root of `L` leaves at least `B` agreements. -/
theorem isAffinePersistent_of_mem_chartExcluded [IsAlgClosed E] (domain : ι ↪ F)
    (f g : ι → F) (φ : F →+* E) (c : E) (R : MvPolynomial AffineVar E) (p r : ℕ) [ExpChar E p]
    {d B : ℕ} {α β : F} {P : Polynomial F} (hP : P.degree ≤ d)
    (hroot : multiplierEval (affineMultiplier ((iterateFrobeniusEquiv E p r).symm (φ α))
        ((iterateFrobeniusEquiv E p r).symm (φ β))) (Polynomial.expand E (p ^ r) (P.map φ)) R = 0)
    (hsep : (multiplierEval (affineMultiplier ((iterateFrobeniusEquiv E p r).symm (φ α))
        ((iterateFrobeniusEquiv E p r).symm (φ β))) (Polynomial.expand E (p ^ r) (P.map φ))
        (pderiv none R)).eval c ≠ 0)
    (hex : chartPoint c (p ^ r) ![(iterateFrobeniusEquiv E p r).symm (φ α),
        (iterateFrobeniusEquiv E p r).symm (φ β)] (P.map φ) ∈
      chartExcluded c affineFamily R (p ^ r) d B 1 [] (fun i ↦ Polynomial.leval (φ (domain i)))
        (affineChartTarget domain f g φ (p ^ r))) :
    IsAffinePersistent domain f g d B α β P := by
  set fr := (iterateFrobeniusEquiv E p r).symm
  have hfr (x : E) : fr x ^ p ^ r = x := by
    rw [← iterateFrobeniusEquiv_def, RingEquiv.apply_symm_apply]
  obtain ⟨T, hT, hcut, pt', -, -, hcut', hne⟩ := hex
  rw [chartPolynomial_point c affineFamily R rfl ((Polynomial.degree_map_le).trans hP)
    (by rwa [familyMultiplier_affineFamily]) (by rwa [familyMultiplier_affineFamily])] at hcut
  have hagree : T ⊆ polynomialAgreementSet domain (combinedWord domain f g
      (affineMultiplier α β)) P := fun i hi ↦
    (eval_map_eq_aeval_affineChartTarget_iff domain f g φ p r α β P i).mp (hcut i hi)
  -- The second challenge explains `g` on `T` by the ratio `(P' - P) / L`.
  set a' := pt' (.inr 0) ^ p ^ r - φ α
  set b' := pt' (.inr 1) ^ p ^ r - φ β
  set H := chartPolynomial c affineFamily R (p ^ r) d pt' - P.map φ
  have hL : affineMultiplier a' b' ≠ 0 := by
    intro hL0
    have h0 := congrArg (Polynomial.coeff · 0) hL0
    have h1 := congrArg (Polynomial.coeff · 1) hL0
    simp only [affineMultiplier, Polynomial.coeff_add, Polynomial.coeff_zero, Polynomial.coeff_C,
      Polynomial.coeff_C_mul, Polynomial.coeff_X_zero, Polynomial.coeff_X_one] at h0 h1
    apply hne
    have hroot' (x y : E) (h : x ^ p ^ r - y = 0) : x = fr y := by
      apply (iterateFrobeniusEquiv E p r).injective
      rw [iterateFrobeniusEquiv_def, RingEquiv.apply_symm_apply]
      exact sub_eq_zero.mp h
    funext j
    fin_cases j
    · exact hroot' _ _ (by simpa using h0)
    · exact hroot' _ _ (by simpa using h1)
  have hH : H.degree ≤ d := (Polynomial.degree_sub_le _ _).trans
    (max_le (degree_chartPolynomial_le c affineFamily R _ d pt')
      ((Polynomial.degree_map_le).trans hP))
  have hexplain : ∀ k : T, H.eval (φ (domain k)) =
      (affineMultiplier a' b').eval (φ (domain k)) * φ (g k) := by
    rintro ⟨i, hi⟩
    have h' := hcut' i hi
    have h := hagree hi
    simp only [polynomialAgreementSet, Finset.mem_filter, Finset.mem_univ, true_and,
      combinedWord_affineMultiplier] at h
    simp only [Polynomial.leval_apply, affineChartTarget, map_add, map_mul, map_pow, aeval_C,
      aeval_X, Algebra.algebraMap_self, RingHom.id_apply, Function.comp_apply] at h'
    simp only [H, Polynomial.eval_sub, h', Polynomial.eval_map_apply, h, eval_affineMultiplier,
      a', b', map_add, map_mul]
    ring
  obtain ⟨H₀, L₀, hL₀, hL₀1, hH₀, h₀⟩ := exists_lineRatioWitness_of_map φ
    (fun k : T ↦ domain k) (fun k : T ↦ g k) d hL (degree_affineMultiplier_le a' b') hH hexplain
  exact isAffinePersistent_of_commonAgreement domain f g T hT hagree hL₀ hL₀1 hH₀
    fun i hi ↦ h₀ ⟨i, hi⟩

end Affine

end ReedSolomon

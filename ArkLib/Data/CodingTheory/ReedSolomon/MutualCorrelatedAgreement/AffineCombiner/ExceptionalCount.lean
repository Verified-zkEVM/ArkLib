/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Coratger
-/
module

public import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.AffineCombiner.ChartIncidence
public import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.AffineCombiner.FrobeniusFactor
public import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.AffineCombiner.Interpolation
public import ArkLib.Data.MvPolynomial.WeightedDegree.Products
public import ArkLib.ToMathlib.MvPolynomial.PDeriv
public import ArkLib.ToMathlib.MvPolynomial.RadicalSplit
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# Counting exceptional challenges through the factors of the interpolant

A root of the interpolant along a challenge multiplier `L_γ` is counted over an algebraically
closed field `E`.
The interpolant splits into a content free of `Z` and irreducible factors of positive
`Z`-degree.
The content vanishes along few multipliers.
Each factor has few challenges with a root whose chart point is not excluded.
Summing over the factors bounds the challenges with a root that is not good.

The generic count takes the challenges as a finite type with injective multipliers.
Each Frobenius root of a multiplier is a family multiplier at chart coordinates.
Positions carry linear functionals `Λᵢ`, and high cuts restrict the counted roots.
The received words `u` and `v` give the agreement condition `Λᵢ P = uᵢ + Λᵢ(L_γ) vᵢ`.
Each code supplies its own conversion from an excluded chart point to persistence.

Let `n` be the number of positions, `D` the `(Y, Z)`-degree budget and `M` the `Z`-degree
budget.
Candidates have degree at most `d`, and counted roots have at least `A` agreements.
The persistence threshold is `B`.
The count takes a separation threshold `B + e`. The Reed–Solomon instance uses `e = 1`.
The Reed–Muller application takes `e = n / q₀`, where `q₀` is the size of the grid subfield.

The generic bound is `D² + (2 d M n / (A - B - e + 1)) ^ |κ| D ^ (|κ| + 1)`.
For Reed–Solomon codes, `|κ| = 2` and `e = 1`, which gives `D² + 4 d² M² D³ (n / (A - B))²`.
The Reed–Solomon interpolant is mapped from `F` into its algebraic closure.

Lemma 4.1 of [CWYZ26] splits the exceptional challenges into three sets.
The count covers the excluded set of Lemma 4.3 and the nonpersistent set of Lemma 4.7.
The persistent set enters the Reed–Solomon count as a given set of challenges.
The final numerics of Lemma 4.1 are not here.

Appendix A gives the bound `(2 ρ n M v) ^ (k + 1) D ^ (k + 2)` for Reed–Muller codes.
It is the generic bound at `|κ| = k + 1`, `d = ρ n` and `e = n / q₀`.
There `v = n / (A - B - e + 1)`.

The [paper page](../../../../../../docs/kb/papers/CWYZ26.md) records the correspondence.

## Main statements

* `ReedSolomon.exists_factorRoots_finset_card_le`: the count for one irreducible factor.
* `ReedSolomon.exists_interpolantRoots_finset_card_le`: outside few challenges, every root of
  the interpolant with `A` agreements is good.
* `ReedSolomon.exists_affineExceptional_finset_card_le_of_interpolant`: outside a given set and
  at most `D² + 4 d² M² D³ (n / (A - B))²` more challenges, no candidate is exceptional.

## References

* [Chiesa, A., Weissenberg, G., Yogev, E., and Zheng, K. Z.,
    *Affine combiners for Reed–Solomon proximity gaps*][CWYZ26], Lemmas 4.1, 4.3 and 4.7 and
    Appendix A.
-/

@[expose] public section

namespace ReedSolomon

open MvPolynomial
open scoped Finset

/-- If `δ + Σ h ≤ D`, then `δ + Σ h (h - 1) ≤ D²` and `Σ h ^ (k + 1) ≤ D ^ (k + 1)`. -/
private theorem budget_le {α : Type*} (s : Finset α) (h : α → ℕ) (k : ℕ) {δ D : ℕ}
    (hD : δ + ∑ c ∈ s, h c ≤ D) :
    δ + ∑ c ∈ s, h c * (h c - 1) ≤ D ^ 2 ∧ ∑ c ∈ s, h c ^ (k + 1) ≤ D ^ (k + 1) := by
  set H := ∑ c ∈ s, h c
  have hle : ∀ c ∈ s, h c ≤ H := fun c hc ↦ Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) hc
  have h2 : ∑ c ∈ s, h c * (h c - 1) ≤ H * (H - 1) := by
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum fun c hc ↦ Nat.mul_le_mul_left _ (Nat.sub_le_sub_right (hle c hc) 1)
  have hk : ∑ c ∈ s, h c ^ (k + 1) ≤ H ^ (k + 1) := by
    calc ∑ c ∈ s, h c ^ (k + 1) ≤ ∑ c ∈ s, h c * H ^ k :=
          Finset.sum_le_sum fun c hc ↦ by
            rw [pow_succ']
            exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (hle c hc) k)
      _ = H ^ (k + 1) := by rw [← Finset.sum_mul]; ring
  have hH : H ≤ D := le_of_add_le_right hD
  refine ⟨?_, hk.trans (Nat.pow_le_pow_left hH _)⟩
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hH
  have hδ : δ ≤ t := by omega
  have hHH : H * (H - 1) ≤ H * H := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
  nlinarith [Nat.le_mul_self t]

section Generic

variable {E : Type*} [Field E] {κ : Type*} [Fintype κ] {ι : Type*} [Fintype ι] {Γ : Type*}

/-- Outside few challenges, every root of one irreducible factor is good.

The challenges form a finite type with injective multipliers `L_γ`.
The received words `u` and `v` give the agreement condition `Λᵢ P = uᵢ + Λᵢ(L_γ) vᵢ`.
Let `p` be the exponential characteristic and `r` a Frobenius exponent.
Assume the Frobenius root of `L_γ` is the multiplier of the family `θ_r` at `a_r(γ)`.
Assume each `a_r` is injective.
Assume the targets `T_r` have degree at most `p ^ r`.
Assume `T_r` at `a_r(γ)` is `uᵢ + Λᵢ(L_γ) vᵢ`.
Assume `1 ≤ d` and `1 ≤ B + e ≤ A ≤ n`, where `n` is the number of positions.
Assume the functionals determine polynomials of degree at most `d` from `B + e` positions.
The factor has positive `Z`-degree at most `M` and `(Y, Z)`-degree at most `h`.
Assume an excluded chart point of a regular root `P(X ^ (p ^ r))` makes `P` good.
At most `h (h - 1) + (2 d M n / (A - B - e + 1)) ^ |κ| h ^ (|κ| + 1)` challenges are left out.
The subtraction is natural-number subtraction. -/
theorem exists_factorRoots_finset_card_le [Finite Γ] [IsAlgClosed E] (p : ℕ) [ExpChar E p]
    {Q : MvPolynomial AffineVar E} (hirr : Irreducible Q) (hpos : 0 < Q.degreeOf none)
    {d h A B e M : ℕ} (hd : 1 ≤ d) (hBe : 1 ≤ B + e) (hBA : B + e ≤ A) (hAn : A ≤ Fintype.card ι)
    (hQ : Q.weightedTotalDegree affineYZWeight ≤ h) (hM : Q.degreeOf none ≤ M)
    (mult : Γ → Polynomial E) (hmult : mult.Injective) (θ : ℕ → κ → Polynomial E)
    (a : ℕ → Γ → κ → E) (ha : ∀ r, (a r).Injective)
    (hθ : ∀ r γ, (mult γ).map ((iterateFrobeniusEquiv E p r).symm : E →+* E) =
      familyMultiplier (θ r) (a r γ))
    (highCuts : List (Polynomial E →ₗ[E] E)) (Λ : ι → Polynomial E →ₗ[E] E) (u v : ι → E)
    (target : ℕ → ι → MvPolynomial κ E) (htarget : ∀ r i, (target r i).totalDegree ≤ p ^ r)
    (hval : ∀ r γ i, aeval (a r γ) (target r i) = u i + Λ i (mult γ) * v i)
    (hsep : SeparatesDegree highCuts Λ d (B + e)) (Good : Γ → Polynomial E → Prop)
    (hgood : ∀ r (R : MvPolynomial AffineVar E) (c : E) γ (P : Polynomial E), P.degree ≤ d →
      multiplierEval (familyMultiplier (θ r) (a r γ)) (Polynomial.expand E (p ^ r) P) R = 0 →
      (multiplierEval (familyMultiplier (θ r) (a r γ)) (Polynomial.expand E (p ^ r) P)
        (pderiv none R)).eval c ≠ 0 →
      chartPoint c (p ^ r) (a r γ) P ∈
        chartExcluded c (θ r) R (p ^ r) d B e highCuts Λ (target r) → Good γ P) :
    ∃ ex : Finset Γ, (#ex : ℝ) ≤ ((h * (h - 1) : ℕ) : ℝ) +
        (2 * d * M * ((Fintype.card ι : ℝ) / (A - B - e + 1 : ℕ))) ^ Fintype.card κ *
          h ^ (Fintype.card κ + 1) ∧
      ∀ γ ∉ ex, ∀ P : Polynomial E, multiplierEval (mult γ) P Q = 0 → P.degree ≤ d →
        (∀ Λ' ∈ highCuts, Λ' P = 0) → A ≤ {i | Λ i P = u i + Λ i (mult γ) * v i}.ncard →
        Good γ P := by
  classical
  have := Fintype.ofFinite Γ
  obtain ⟨r, R, hRirr, hRder, hRdeg, hpr, -, hroot⟩ := exists_frobeniusFactor p hirr hpos
  set fr : E →+* E := ((iterateFrobeniusEquiv E p r).symm : E →+* E)
  have hRh : R.weightedTotalDegree affineYZWeight ≤ h := hRdeg.trans hQ
  -- The challenges where the discriminant of `R` vanishes.
  set disc := (Finset.univ : Finset Γ).filter fun γ ↦
    (affineDiscriminant R).eval ((mult γ).map fr) = 0
  have hdisc : #disc ≤ h * (h - 1) :=
    card_filter_affineDiscriminant_eq_zero_le (affineDiscriminant_ne_zero hRirr hRder) hRh _
      (fun γ ↦ (mult γ).map fr) ((Polynomial.map_injective fr fr.injective).comp hmult).injOn
  -- The challenges with a regular root whose chart point is not excluded.
  obtain ⟨ex, hex, hchart⟩ := exists_chartExcluded_finset_card_le (θ r) R p r hd hBe hBA hAn hRh
    highCuts Λ (target r) (htarget r) hsep (a r) (ha r)
  refine ⟨disc ∪ ex, ?_, fun γ hγ P hP hdeg hhigh hA ↦ ?_⟩
  · set k := Fintype.card κ
    set n : ℝ := (Fintype.card ι : ℝ)
    set w : ℝ := ((A - B - e : ℕ) : ℝ) + 1
    have hexR : (#ex : ℝ) ≤ h * ((((Fintype.card ι * (2 * p ^ r * d * h) : ℕ) : ℝ)) / w) ^ k := by
      have := (Rat.cast_le (K := ℝ)).mpr hex
      push_cast at this ⊢
      exact this
    have hprM : ((p ^ r : ℕ) : ℝ) ≤ M := by exact_mod_cast hpr.trans hM
    have hsplit : (h : ℝ) * ((((Fintype.card ι * (2 * p ^ r * d * h) : ℕ) : ℝ)) / w) ^ k =
        (2 * d * (p ^ r : ℕ) * (n / w)) ^ k * h ^ (k + 1) := by
      simp only [n]
      push_cast
      ring
    calc (#(disc ∪ ex) : ℝ) ≤ #disc + #ex := by exact_mod_cast Finset.card_union_le _ _
      _ ≤ ((h * (h - 1) : ℕ) : ℝ) + (2 * d * (p ^ r : ℕ) * (n / w)) ^ k * h ^ (k + 1) :=
          add_le_add (by exact_mod_cast hdisc) (hexR.trans_eq hsplit)
      _ ≤ _ := by
          have hw : ((A - B - e + 1 : ℕ) : ℝ) = w := by push_cast; rfl
          rw [hw]
          gcongr
  · have hcd : γ ∉ disc := fun h ↦ hγ (Finset.mem_union_left _ h)
    have hce : γ ∉ ex := fun h ↦ hγ (Finset.mem_union_right _ h)
    have hR := hroot _ _ hP
    have hsepR := multiplierEval_pderiv_ne_zero
      (MvPolynomial.degreeOf_pos_of_pderiv_ne_zero none hRder) hR
      (fun h0 ↦ hcd (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h0⟩))
    rw [hθ] at hR hsepR
    obtain ⟨c, hc, hexc⟩ := hchart γ hce P hdeg hR hsepR hhigh
      (hA.trans_eq (by simp_rw [hval]))
    exact hgood r R c γ P hdeg hR hc hexc

/-- Outside few challenges, every root of the interpolant with `A` agreements is good.

The interpolant `Q` over the algebraically closed field `E` is nonzero.
It has `(Y, Z)`-degree at most `D` and `Z`-degree at most `M`.
The challenges form a finite type with injective multipliers `L_γ`.
The received words `u` and `v` give the agreement condition `Λᵢ P = uᵢ + Λᵢ(L_γ) vᵢ`.
Let `p` be the exponential characteristic and `r` a Frobenius exponent.
Assume the Frobenius root of `L_γ` is the multiplier of the family `θ_r` at `a_r(γ)`.
Assume each `a_r` is injective.
Assume the targets `T_r` have degree at most `p ^ r`.
Assume `T_r` at `a_r(γ)` is `uᵢ + Λᵢ(L_γ) vᵢ`.
Assume `1 ≤ d` and `1 ≤ B + e ≤ A ≤ n`, where `n` is the number of positions.
Assume the functionals determine polynomials of degree at most `d` from `B + e` positions.
Assume an excluded chart point of a regular root `P(X ^ (p ^ r))` makes `P` good.
This holds for every irreducible factor `R` of `Q`.
At most `D² + (2 d M n / (A - B - e + 1)) ^ |κ| D ^ (|κ| + 1)` challenges are left out.
The subtraction is natural-number subtraction. -/
theorem exists_interpolantRoots_finset_card_le [Finite Γ] [IsAlgClosed E] (p : ℕ) [ExpChar E p]
    {Q : MvPolynomial AffineVar E} (hQ0 : Q ≠ 0) {d A B e D M : ℕ} (hd : 1 ≤ d) (hBe : 1 ≤ B + e)
    (hBA : B + e ≤ A) (hAn : A ≤ Fintype.card ι)
    (hD : Q.weightedTotalDegree affineYZWeight ≤ D) (hM : Q.degreeOf none ≤ M)
    (mult : Γ → Polynomial E) (hmult : mult.Injective) (θ : ℕ → κ → Polynomial E)
    (a : ℕ → Γ → κ → E) (ha : ∀ r, (a r).Injective)
    (hθ : ∀ r γ, (mult γ).map ((iterateFrobeniusEquiv E p r).symm : E →+* E) =
      familyMultiplier (θ r) (a r γ))
    (highCuts : List (Polynomial E →ₗ[E] E)) (Λ : ι → Polynomial E →ₗ[E] E) (u v : ι → E)
    (target : ℕ → ι → MvPolynomial κ E) (htarget : ∀ r i, (target r i).totalDegree ≤ p ^ r)
    (hval : ∀ r γ i, aeval (a r γ) (target r i) = u i + Λ i (mult γ) * v i)
    (hsep : SeparatesDegree highCuts Λ d (B + e)) (Good : Γ → Polynomial E → Prop)
    (hgood : ∀ r (R : MvPolynomial AffineVar E) (c : E) γ (P : Polynomial E), P.degree ≤ d →
      multiplierEval (familyMultiplier (θ r) (a r γ)) (Polynomial.expand E (p ^ r) P) R = 0 →
      (multiplierEval (familyMultiplier (θ r) (a r γ)) (Polynomial.expand E (p ^ r) P)
        (pderiv none R)).eval c ≠ 0 →
      chartPoint c (p ^ r) (a r γ) P ∈
        chartExcluded c (θ r) R (p ^ r) d B e highCuts Λ (target r) → Good γ P) :
    ∃ Ex : Finset Γ, (#Ex : ℝ) ≤ D ^ 2 +
        (2 * d * M * ((Fintype.card ι : ℝ) / (A - B - e + 1 : ℕ))) ^ Fintype.card κ *
          D ^ (Fintype.card κ + 1) ∧
      ∀ γ ∉ Ex, ∀ P : Polynomial E, multiplierEval (mult γ) P Q = 0 → P.degree ≤ d →
        (∀ Λ' ∈ highCuts, Λ' P = 0) → A ≤ {i | Λ i P = u i + Λ i (mult γ) * v i}.ncard →
        Good γ P := by
  classical
  have := Fintype.ofFinite Γ
  set k := Fintype.card κ
  set K : ℝ := (2 * d * M * ((Fintype.card ι : ℝ) / (A - B - e + 1 : ℕ))) ^ k with hK
  set S := positiveDegreeFactorClasses none Q
  let h : Associates (MvPolynomial AffineVar E) → ℕ :=
    fun c ↦ c.rep.weightedTotalDegree affineYZWeight
  set δ := (radicalContent none Q).weightedTotalDegree affineYZWeight
  -- The degree budgets of the factors.
  have hbudget : δ + ∑ c ∈ S, h c ≤ D :=
    (add_sum_positiveDegreeFactorClasses_le
      (fun x y hx hy ↦ weightedTotalDegree_mul affineYZWeight x y hx hy) none Q).trans hD
  have hMc : ∀ c ∈ S, c.rep.degreeOf none ≤ M := fun c hc ↦
    (Finset.single_le_sum (f := fun c ↦ c.rep.degreeOf none) (fun _ _ ↦ Nat.zero_le _) hc).trans
      ((le_of_add_le_right (add_sum_degreeOf_positiveDegreeFactorClasses_le none none Q)).trans hM)
  have hcontent : ∃ ex : Finset Γ, ((#ex : ℕ) : ℝ) ≤ (δ : ℝ) ∧
      ∀ γ ∉ ex, ∀ P : Polynomial E, multiplierEval (mult γ) P (radicalContent none Q) ≠ 0 := by
    -- The content is free of `Z`, so it vanishes along few multipliers.
    have hZ := degreeOf_radicalContent none Q
    refine ⟨(Finset.univ : Finset Γ).filter fun γ ↦
      multiplierEval (mult γ) 0 (radicalContent none Q) = 0, ?_, fun γ hγ P h0 ↦ ?_⟩
    · exact_mod_cast (card_filter_multiplierEval_eq_zero_le (radicalContent_ne_zero none Q) hZ
        Finset.univ mult hmult.injOn).trans
        (degreeOf_le_weightedTotalDegree affineYZWeight (some 1) (by simp) _)
    · refine hγ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩)
      rwa [multiplierEval_eq_of_degreeOf_none_eq_zero hZ _ 0 P]
  have hfactors : ∀ c ∈ S, ∃ ex : Finset Γ,
      ((#ex : ℕ) : ℝ) ≤ ((h c * (h c - 1) : ℕ) : ℝ) + K * (h c : ℝ) ^ (k + 1) ∧
      ∀ γ ∉ ex, ∀ P : Polynomial E, multiplierEval (mult γ) P c.rep = 0 → P.degree ≤ d →
        (∀ Λ' ∈ highCuts, Λ' P = 0) → A ≤ {i | Λ i P = u i + Λ i (mult γ) * v i}.ncard →
        Good γ P := fun c hc ↦
    exists_factorRoots_finset_card_le p (irreducible_rep_of_mem_positiveDegreeFactorClasses hc)
      (mem_positiveDegreeFactorClasses.mp hc).2 hd hBe hBA hAn le_rfl (hMc c hc) mult hmult θ a ha
      hθ highCuts Λ u v target htarget hval hsep Good hgood
  obtain ⟨ex, hex, hgoodex⟩ := exists_exceptional_of_factor_exceptional (α := ℝ) none hQ0
    (fun (γ : Γ) (P : Polynomial E) ↦ multiplierEval (mult γ) P)
    (fun γ P ↦ P.degree ≤ d → (∀ Λ' ∈ highCuts, Λ' P = 0) →
      A ≤ {i | Λ i P = u i + Λ i (mult γ) * v i}.ncard → Good γ P)
    (δ : ℝ) (fun c ↦ ((h c * (h c - 1) : ℕ) : ℝ) + K * (h c : ℝ) ^ (k + 1)) hcontent hfactors
  refine ⟨ex, ?_, fun γ hγ P hP ↦ hgoodex γ hγ P hP⟩
  obtain ⟨h2, hk⟩ := budget_le S h k hbudget
  have hK0 : 0 ≤ K := by positivity
  calc (#ex : ℝ) ≤ (δ : ℝ) + ∑ c ∈ S, (((h c * (h c - 1) : ℕ) : ℝ) + K * (h c : ℝ) ^ (k + 1)) :=
        hex
    _ = ((δ + ∑ c ∈ S, h c * (h c - 1) : ℕ) : ℝ) + K * ((∑ c ∈ S, h c ^ (k + 1) : ℕ) : ℝ) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum]
        push_cast
        ring
    _ ≤ ((D ^ 2 : ℕ) : ℝ) + K * ((D ^ (k + 1) : ℕ) : ℝ) := by gcongr
    _ = _ := by
        rw [hK]
        push_cast
        ring

end Generic

section Count

variable {F : Type*} [Field F] {ι : Type*}

/-- At the Frobenius roots of `(φ α, φ β)`, the target reads the Reed–Solomon agreement. -/
private theorem aeval_affineChartTarget_frobenius {E : Type*} [Field E] (domain : ι ↪ F)
    (f g : ι → F) (φ : F →+* E) (p : ℕ) [ExpChar E p] [PerfectRing E p] (r : ℕ)
    (c : F × F) (i : ι) :
    aeval ![(iterateFrobeniusEquiv E p r).symm (φ c.1),
        (iterateFrobeniusEquiv E p r).symm (φ c.2)] (affineChartTarget domain f g φ (p ^ r) i) =
      φ (f i) + Polynomial.leval (φ (domain i)) (affineMultiplier (φ c.1) (φ c.2)) * φ (g i) := by
  have hfr (x : E) : (iterateFrobeniusEquiv E p r).symm x ^ p ^ r = x := by
    rw [← iterateFrobeniusEquiv_def, RingEquiv.apply_symm_apply]
  simp only [affineChartTarget, map_add, map_mul, map_pow, aeval_C, aeval_X,
    Algebra.algebraMap_self, RingHom.id_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, hfr, Polynomial.leval_apply, eval_affineMultiplier]
  ring

variable [DecidableEq F] [Fintype ι]

/-- The agreement set of `P` along `α + β X`, read through `φ`. -/
private theorem ncard_leval_map_eq {E : Type*} [Field E] (domain : ι ↪ F) (f g : ι → F)
    (φ : F →+* E) (c : F × F) (P : Polynomial F) :
    {i | Polynomial.leval (φ (domain i)) (P.map φ) = φ (f i) +
        Polynomial.leval (φ (domain i)) (affineMultiplier (φ c.1) (φ c.2)) * φ (g i)}.ncard =
      #(polynomialAgreementSet domain (combinedWord domain f g (affineMultiplier c.1 c.2)) P) := by
  rw [← Set.ncard_coe_finset]
  congr 1
  ext i
  simp only [Finset.coe_filter, polynomialAgreementSet, Finset.mem_univ, true_and,
    combinedWord_affineMultiplier, Set.mem_ofPred_eq, Polynomial.leval_apply,
    Polynomial.eval_map_apply, eval_affineMultiplier]
  rw [← φ.injective.eq_iff]
  simp [map_add, map_mul, mul_comm]

/-- Over an algebraically closed extension, candidates outside few challenges are persistent. -/
private theorem exists_affinePersistent_of_map {E : Type*} [Field E] [IsAlgClosed E] [Finite F]
    (φ : F →+* E) (p : ℕ) [ExpChar E p] (domain : ι ↪ F) (f g : ι → F) {d A B m D M : ℕ}
    {Q : MvPolynomial AffineVar F} (hQ : IsMultiplierInterpolant domain f g 1 d A m D M Q)
    (hd : 1 ≤ d) (hdB : d ≤ B) (hBA : B < A) (hAn : A ≤ Fintype.card ι) :
    ∃ Ex : Finset (F × F), (#Ex : ℝ) ≤ D ^ 2 +
        (2 * d * M * ((Fintype.card ι : ℝ) / (A - B - 1 + 1 : ℕ))) ^ Fintype.card (Fin 2) *
          D ^ (Fintype.card (Fin 2) + 1) ∧
      ∀ c ∉ Ex, ∀ P, IsAffineExceptional domain f g d A 1 c.1 c.2 P →
        IsAffinePersistent domain f g d B c.1 c.2 P := by
  have hQE : MvPolynomial.map φ Q ≠ 0 :=
    (map_ne_zero_iff _ (MvPolynomial.map_injective φ φ.injective)).mpr hQ.ne_zero
  have hφ : Function.Injective fun c : F × F ↦ (φ c.1, φ c.2) := fun c c' hc ↦ by
    simp only [Prod.mk.injEq] at hc
    exact Prod.ext (φ.injective hc.1) (φ.injective hc.2)
  have hθ (r : ℕ) (c : F × F) :
      (affineMultiplier (φ c.1) (φ c.2)).map ((iterateFrobeniusEquiv E p r).symm : E →+* E) =
        familyMultiplier affineFamily ![(iterateFrobeniusEquiv E p r).symm (φ c.1),
          (iterateFrobeniusEquiv E p r).symm (φ c.2)] := by
    rw [map_affineMultiplier, familyMultiplier_affineFamily]
    rfl
  obtain ⟨Ex, hEx, hgood⟩ := exists_interpolantRoots_finset_card_le (κ := Fin 2) p hQE
    (d := d) (A := A) (B := B) (e := 1) hd (Nat.le_add_left 1 B)
    (Nat.succ_le_of_lt hBA) hAn
    ((Finset.sup_mono (MvPolynomial.support_map_subset φ Q)).trans hQ.yzDegree_le)
    ((degreeOf_map_of_injective φ.injective Q none).trans_le hQ.rootDegree_le)
    (fun c : F × F ↦ affineMultiplier (φ c.1) (φ c.2))
    (fun x y h ↦ hφ (affineMultiplier_injective h))
    (fun _ ↦ affineFamily)
    (fun r (c : F × F) ↦ ![(iterateFrobeniusEquiv E p r).symm (φ c.1),
      (iterateFrobeniusEquiv E p r).symm (φ c.2)])
    (injective_frobeniusPair φ p) hθ [] (fun i ↦ Polynomial.leval (φ (domain i)))
    (fun i ↦ φ (f i)) (fun i ↦ φ (g i)) (fun r ↦ affineChartTarget domain f g φ (p ^ r))
    (fun r ↦ totalDegree_affineChartTarget_le domain f g φ _)
    (aeval_affineChartTarget_frobenius domain f g φ p)
    (separatesDegree_leval (φ.injective.comp domain.injective) (Nat.lt_succ_of_le hdB))
    (fun (c : F × F) P' ↦ ∀ P : Polynomial F, P' = P.map φ →
      IsAffinePersistent domain f g d B c.1 c.2 P)
    (fun r R center c P' hP' hroot hcenter hex P hP ↦ by
      subst hP
      rw [familyMultiplier_affineFamily] at hroot hcenter
      exact isAffinePersistent_of_mem_chartExcluded domain f g φ center R p r
        (by rwa [Polynomial.degree_map] at hP') hroot hcenter hex)
  refine ⟨Ex, hEx, fun c hc P hP ↦ hgood c hc (P.map φ) ?_
    ((Polynomial.degree_map_le).trans hP.1) (by simp)
    ((hP.2.1.trans_eq (ncard_leval_map_eq domain f g φ c P).symm)) P rfl⟩
  have := congrArg (Polynomial.map φ) (hQ.vanish_affineMultiplier c.1 c.2 P hP.1 hP.2.1)
  rwa [map_multiplierEval, map_affineMultiplier, Polynomial.map_zero] at this

/-- Outside few challenges, no candidate is exceptional.

Assume `1 ≤ d ≤ B < A ≤ n` and an interpolant with budgets `m, D, M`.
At agreement loss one, the excluded set has size at most the size of a given set plus
`D² + 4 d² M² D³ (n / (A - B))²`.
Outside the given set, exceptional candidates must not be persistent. -/
theorem exists_affineExceptional_finset_card_le_of_interpolant [Finite F] (domain : ι ↪ F)
    (f g : ι → F) {d A B m D M : ℕ} {Q : MvPolynomial AffineVar F}
    (hQ : IsMultiplierInterpolant domain f g 1 d A m D M Q) (hd : 1 ≤ d) (hdB : d ≤ B) (hBA : B < A)
    (hAn : A ≤ Fintype.card ι) (Pset : Finset (F × F))
    (hPset : ∀ c ∉ Pset, ∀ P, IsAffineExceptional domain f g d A 1 c.1 c.2 P →
      ¬ IsAffinePersistent domain f g d B c.1 c.2 P) :
    ∃ Ex : Finset (F × F), (#Ex : ℝ) ≤ #Pset + D ^ 2 +
        4 * d ^ 2 * M ^ 2 * D ^ 3 * ((Fintype.card ι : ℝ) / (A - B : ℕ)) ^ 2 ∧
      ∀ c ∉ Ex, ∀ P, ¬ IsAffineExceptional domain f g d A 1 c.1 c.2 P := by
  classical
  obtain ⟨Ex, hEx, hgood⟩ := exists_affinePersistent_of_map
    (algebraMap F (AlgebraicClosure F)) (ringExpChar (AlgebraicClosure F)) domain f g hQ hd hdB
    hBA hAn
  refine ⟨Pset ∪ Ex, ?_, fun c hc P hP ↦
    hPset c (fun h ↦ hc (Finset.mem_union_left _ h)) P hP
      (hgood c (fun h ↦ hc (Finset.mem_union_right _ h)) P hP)⟩
  have hAB : A - B - 1 + 1 = A - B := by omega
  rw [hAB, Fintype.card_fin] at hEx
  calc (#(Pset ∪ Ex) : ℝ) ≤ #Pset + #Ex := by exact_mod_cast Finset.card_union_le _ _
    _ ≤ #Pset + (D ^ 2 + (2 * d * M * ((Fintype.card ι : ℝ) / (A - B : ℕ))) ^ 2 * D ^ (2 + 1)) :=
        add_le_add le_rfl hEx
    _ = _ := by ring

end Count

end ReedSolomon

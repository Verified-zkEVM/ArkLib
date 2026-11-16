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
public import ArkLib.ToMathlib.MvPolynomial.RadicalSplit
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# Counting exceptional challenges through the factors of the interpolant

An exceptional candidate makes the interpolant vanish along its challenge line.

Over the algebraic closure, the interpolant splits into a content free of `Z` and irreducible
factors of positive `Z`-degree.

The content vanishes on few lines, and each factor has few nonpersistent challenges.

Summing over the factors bounds the nonpersistent exceptional challenges.

## Main statements

* `ReedSolomon.exists_affineFactor_finset_card_le`: the count for one irreducible factor.
* `ReedSolomon.exists_affineExceptional_finset_card_le_of_interpolant`: outside a given set and
  at most `D² + 4 d² M² D³ (n / (A - B))²` more challenges, no candidate is exceptional.

## References

The count is Lemma 4.1 of [CWYZ26], without its final numerics.

* [Chiesa, A., Weissenberg, G., Yogev, E., and Zheng, K. Z.,
    *Affine combiners for Reed–Solomon proximity gaps*][CWYZ26]
-/

@[expose] public section

namespace ReedSolomon

open MvPolynomial
open scoped Finset

section Lines

variable {E : Type*} [Field E]

/-- A polynomial free of `Z` has the same evaluation along a line for every candidate. -/
theorem affineLineEval_eq_of_degreeOf_none_eq_zero {G : MvPolynomial AffineVar E}
    (hZ : G.degreeOf none = 0) (α β : E) (P P' : Polynomial E) :
    affineLineEval α β P G = affineLineEval α β P' G := by
  have hC : affineNested G = Polynomial.C ((affineNested G).coeff 0) :=
    Polynomial.eq_C_of_natDegree_eq_zero ((natDegree_affineNested G).trans hZ)
  rw [affineLineEval_eq_nested, affineLineEval_eq_nested, hC]
  simp

open Classical in
/-- The discriminant of `R` vanishes on at most `h (h - 1)` lines indexed injectively by `S`. -/
theorem card_filter_affineDiscriminant_eq_zero_le {F : Type*} {R : MvPolynomial AffineVar E}
    {h : ℕ} (hR0 : affineDiscriminant R ≠ 0) (hR : R.weightedTotalDegree affineYZWeight ≤ h)
    (S : Finset (F × F)) (φ : F × F → E × E) (hφ : φ.Injective) :
    #(S.filter fun c ↦
      (affineDiscriminant R).eval (affineMultiplier (φ c).1 (φ c).2) = 0) ≤ h * (h - 1) :=
  (Polynomial.card_le_natDegree_of_injOn_of_eval_eq_zero hR0
    (x := fun c ↦ affineMultiplier (φ c).1 (φ c).2)
    ((affineMultiplier_injective.comp hφ).injOn) fun _ hc ↦ (Finset.mem_filter.mp hc).2).trans
    (natDegree_affineDiscriminant_le hR)

end Lines


/-- If `δ + Σ h ≤ D`, then `δ + Σ h (h - 1) ≤ D²` and `Σ h³ ≤ D³`. -/
private theorem budget_le {α : Type*} (s : Finset α) (h : α → ℕ) {δ D : ℕ}
    (hD : δ + ∑ c ∈ s, h c ≤ D) :
    δ + ∑ c ∈ s, h c * (h c - 1) ≤ D ^ 2 ∧ ∑ c ∈ s, h c ^ 3 ≤ D ^ 3 := by
  set H := ∑ c ∈ s, h c
  have hle : ∀ c ∈ s, h c ≤ H := fun c hc ↦ Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) hc
  have h2 : ∑ c ∈ s, h c * (h c - 1) ≤ H * (H - 1) := by
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum fun c hc ↦ Nat.mul_le_mul_left _ (Nat.sub_le_sub_right (hle c hc) 1)
  have h3 : ∑ c ∈ s, h c ^ 3 ≤ H ^ 3 := by
    calc ∑ c ∈ s, h c ^ 3 ≤ ∑ c ∈ s, h c * H ^ 2 :=
          Finset.sum_le_sum fun c hc ↦ by
            rw [pow_succ']
            exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (hle c hc) 2)
      _ = H ^ 3 := by rw [← Finset.sum_mul]; ring
  have hH : H ≤ D := le_of_add_le_right hD
  refine ⟨?_, h3.trans (Nat.pow_le_pow_left hH 3)⟩
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hH
  have hδ : δ ≤ k := by omega
  have hHH : H * (H - 1) ≤ H * H := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
  nlinarith [Nat.le_mul_self k]

section Factor

variable {F : Type*} [Field F] [DecidableEq F] {ι : Type*} [Fintype ι]
variable {E : Type*} [Field E]

/-- Outside few challenges, every root along the line of one irreducible factor is persistent.

The factor has positive `Z`-degree at most `M` and `(Y, Z)`-degree at most `h`.

The roots counted are candidates of degree at most `d` with `A` agreements. -/
theorem exists_affineFactor_finset_card_le [Finite F] [IsAlgClosed E] (domain : ι ↪ F)
    (f g : ι → F) (φ : F →+* E) (p : ℕ) [ExpChar E p] [PerfectRing E p]
    {Q : MvPolynomial AffineVar E} (hirr : Irreducible Q) (hpos : 0 < Q.degreeOf none)
    {d h A B M : ℕ} (hd : 1 ≤ d) (hdB : d ≤ B) (hBA : B < A) (hAn : A ≤ Fintype.card ι)
    (hQ : Q.weightedTotalDegree affineYZWeight ≤ h) (hM : Q.degreeOf none ≤ M) :
    ∃ ex : Finset (F × F), (#ex : ℝ) ≤ ((h * (h - 1) : ℕ) : ℝ) +
        4 * d ^ 2 * M ^ 2 * h ^ 3 * ((Fintype.card ι : ℝ) / (A - B : ℕ)) ^ 2 ∧
      ∀ c ∉ ex, ∀ P : Polynomial F, affineLineEval (φ c.1) (φ c.2) (P.map φ) Q = 0 →
        P.degree ≤ d →
        A ≤ #(polynomialAgreementSet domain
          (combinedWord domain f g (affineMultiplier c.1 c.2)) P) →
        IsAffinePersistent domain f g d B c.1 c.2 P := by
  classical
  have := Fintype.ofFinite F
  obtain ⟨e, R, hRirr, hRder, hRdeg, hpe, hroot⟩ := exists_affineFrobeniusFactor p hirr hpos
  set fr := (iterateFrobeniusEquiv E p e).symm
  have hRh : R.weightedTotalDegree affineYZWeight ≤ h := hRdeg.trans hQ
  -- The lines where the discriminant of `R` vanishes.
  set ψ : F × F → E × E := fun c ↦ (fr (φ c.1), fr (φ c.2))
  have hψ : ψ.Injective := by
    intro c c' hc
    simp only [ψ, Prod.mk.injEq] at hc
    exact Prod.ext (φ.injective (fr.injective hc.1)) (φ.injective (fr.injective hc.2))
  set disc := (Finset.univ : Finset (F × F)).filter fun c ↦
    (affineDiscriminant R).eval (affineMultiplier (ψ c).1 (ψ c).2) = 0
  have hdisc : #disc ≤ h * (h - 1) :=
    card_filter_affineDiscriminant_eq_zero_le (affineDiscriminant_ne_zero hRirr hRder) hRh _ ψ hψ
  -- The nonpersistent challenges of `R`.
  obtain ⟨ex, hex, hgood⟩ :=
    exists_affineNonpersistent_finset_card_le domain f g φ p e R hd hdB hBA hAn hRh
  refine ⟨disc ∪ ex, ?_, fun c hc P hP hdeg hA ↦ ?_⟩
  · have hexR : (#ex : ℝ) ≤ h * (((Fintype.card ι * (2 * p ^ e * d * h) : ℕ) : ℝ) /
        ((A - B : ℕ) : ℝ)) ^ 2 := by
      have := (Rat.cast_le (K := ℝ)).mpr hex
      push_cast at this ⊢
      exact this
    have hpeM : ((p ^ e : ℕ) : ℝ) ≤ M := by exact_mod_cast hpe.trans hM
    calc (#(disc ∪ ex) : ℝ) ≤ #disc + #ex := by exact_mod_cast Finset.card_union_le _ _
      _ ≤ ((h * (h - 1) : ℕ) : ℝ) + h * (((Fintype.card ι * (2 * p ^ e * d * h) : ℕ) : ℝ) /
          ((A - B : ℕ) : ℝ)) ^ 2 := add_le_add (by exact_mod_cast hdisc) hexR
      _ ≤ _ := by
        refine add_le_add le_rfl ?_
        rw [div_pow, div_pow]
        push_cast at hpeM ⊢
        have : ((Fintype.card ι : ℝ) * (2 * p ^ e * d * h)) ^ 2 ≤
            ((Fintype.card ι : ℝ) * (2 * M * d * h)) ^ 2 := by gcongr
        calc (h : ℝ) * (((Fintype.card ι : ℝ) * (2 * p ^ e * d * h)) ^ 2 /
              ((A - B : ℕ) : ℝ) ^ 2)
            ≤ (h : ℝ) * (((Fintype.card ι : ℝ) * (2 * M * d * h)) ^ 2 /
              ((A - B : ℕ) : ℝ) ^ 2) := by gcongr
          _ = _ := by ring
  · have hcd : c ∉ disc := fun h ↦ hc (Finset.mem_union_left _ h)
    have hce : c ∉ ex := fun h ↦ hc (Finset.mem_union_right _ h)
    have hR := hroot _ _ _ hP
    refine hgood c hce P hdeg hR ?_ hA
    refine affineLineEval_pderiv_ne_zero (degreeOf_none_pos_of_pderiv_ne_zero hRder) hR ?_
    intro h0
    exact hcd (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h0⟩)

end Factor

section Count

variable {F : Type*} [Field F] [DecidableEq F] {ι : Type*} [Fintype ι]

/-- Outside few challenges, no candidate is exceptional.

The excluded challenges are those of a given set, outside which exceptional candidates are not
persistent, plus at most `D² + 4 d² M² D³ (n / (A - B))²` others. -/
theorem exists_affineExceptional_finset_card_le_of_interpolant [Finite F] (domain : ι ↪ F)
    (f g : ι → F) {d A B m D M : ℕ} {Q : MvPolynomial AffineVar F}
    (hQ : IsAffineInterpolant domain f g d A m D M Q) (hd : 1 ≤ d) (hdB : d ≤ B) (hBA : B < A)
    (hAn : A ≤ Fintype.card ι) (Pset : Finset (F × F))
    (hPset : ∀ c ∉ Pset, ∀ P, IsAffineExceptional domain f g d A 1 c.1 c.2 P →
      ¬ IsAffinePersistent domain f g d B c.1 c.2 P) :
    ∃ Ex : Finset (F × F), (#Ex : ℝ) ≤ #Pset + D ^ 2 +
        4 * d ^ 2 * M ^ 2 * D ^ 3 * ((Fintype.card ι : ℝ) / (A - B : ℕ)) ^ 2 ∧
      ∀ c ∉ Ex, ∀ P, ¬ IsAffineExceptional domain f g d A 1 c.1 c.2 P := by
  classical
  have := Fintype.ofFinite F
  let E := AlgebraicClosure F
  let φ : F →+* E := algebraMap F E
  let QE : MvPolynomial AffineVar E := MvPolynomial.map φ Q
  have hQE : QE ≠ 0 :=
    (map_ne_zero_iff _ (MvPolynomial.map_injective φ φ.injective)).mpr hQ.ne_zero
  set K : ℝ := 4 * d ^ 2 * M ^ 2 * ((Fintype.card ι : ℝ) / (A - B : ℕ)) ^ 2 with hK
  set S := positiveDegreeFactorClasses none QE
  let h : Associates (MvPolynomial AffineVar E) → ℕ :=
    fun c ↦ c.rep.weightedTotalDegree affineYZWeight
  set δ := (radicalContent none QE).weightedTotalDegree affineYZWeight
  -- The degree budgets of the factors.
  have hQED : QE.weightedTotalDegree affineYZWeight ≤ D :=
    (Finset.sup_mono (MvPolynomial.support_map_subset φ Q)).trans hQ.yzDegree_le
  have hbudget : δ + ∑ c ∈ S, h c ≤ D :=
    (add_sum_positiveDegreeFactorClasses_le
      (fun x y hx hy ↦ weightedTotalDegree_mul affineYZWeight x y hx hy) none QE).trans hQED
  have hM : ∀ c ∈ S, c.rep.degreeOf none ≤ M := fun c hc ↦
    (Finset.single_le_sum (f := fun c ↦ c.rep.degreeOf none) (fun _ _ ↦ Nat.zero_le _) hc).trans
      ((le_of_add_le_right (add_sum_degreeOf_positiveDegreeFactorClasses_le none none QE)).trans
        ((degreeOf_map_of_injective φ.injective Q none).trans_le hQ.rootDegree_le))
  have hcontent : ∃ ex : Finset (F × F), ((#ex : ℕ) : ℝ) ≤ (δ : ℝ) ∧
      ∀ c ∉ ex, ∀ P : Polynomial F,
        affineLineEval (φ c.1) (φ c.2) (P.map φ) (radicalContent none QE) ≠ 0 := by
    -- The content is free of `Z`, so it vanishes on few lines.
    have hZ := degreeOf_radicalContent none QE
    refine ⟨(Finset.univ : Finset (F × F)).filter fun c ↦
      affineLineEval (φ c.1) (φ c.2) 0 (radicalContent none QE) = 0, ?_, fun c hc P h0 ↦ ?_⟩
    · have := card_filter_affineLine_eq_zero_le (radicalContent_ne_zero none QE) hZ
        Finset.univ (fun c : F × F ↦ (φ c.1, φ c.2)) fun c c' hc ↦ by
          simp only [Prod.mk.injEq] at hc
          exact Prod.ext (φ.injective hc.1) (φ.injective hc.2)
      exact_mod_cast this.trans
        (degreeOf_le_weightedTotalDegree affineYZWeight (some 1) (by simp) _)
    · refine hc (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩)
      rwa [affineLineEval_eq_of_degreeOf_none_eq_zero hZ _ _ 0 (P.map φ)]
  have hfactors : ∀ c ∈ S, ∃ ex : Finset (F × F),
      ((#ex : ℕ) : ℝ) ≤ ((h c * (h c - 1) : ℕ) : ℝ) + K * (h c : ℝ) ^ 3 ∧
      ∀ w ∉ ex, ∀ P : Polynomial F, affineLineEval (φ w.1) (φ w.2) (P.map φ) c.rep = 0 →
        P.degree ≤ d → A ≤ #(polynomialAgreementSet domain
          (combinedWord domain f g (affineMultiplier w.1 w.2)) P) →
        IsAffinePersistent domain f g d B w.1 w.2 P := by
    intro c hc
    obtain ⟨ex, hex, hgood⟩ := exists_affineFactor_finset_card_le domain f g φ (ringExpChar E)
      (irreducible_rep_of_mem_positiveDegreeFactorClasses hc)
      (mem_positiveDegreeFactorClasses.mp hc).2 hd hdB hBA hAn le_rfl (hM c hc)
    refine ⟨ex, hex.trans (le_of_eq ?_), hgood⟩
    rw [hK]
    ring
  obtain ⟨ex, hex, hgood⟩ := exists_exceptional_of_factor_exceptional (α := ℝ) none hQE
    (fun (c : F × F) (P : Polynomial F) ↦ affineLineEval (φ c.1) (φ c.2) (P.map φ))
    (fun c P ↦ P.degree ≤ d →
      A ≤ #(polynomialAgreementSet domain (combinedWord domain f g (affineMultiplier c.1 c.2)) P) →
      IsAffinePersistent domain f g d B c.1 c.2 P)
    (δ : ℝ) (fun c ↦ ((h c * (h c - 1) : ℕ) : ℝ) + K * (h c : ℝ) ^ 3) hcontent hfactors
  refine ⟨Pset ∪ ex, ?_, fun c hc P hP ↦ ?_⟩
  · obtain ⟨h2, h3⟩ := budget_le S h hbudget
    have hK0 : 0 ≤ K := by positivity
    calc (#(Pset ∪ ex) : ℝ) ≤ #Pset + #ex := by exact_mod_cast Finset.card_union_le _ _
      _ ≤ #Pset + ((δ : ℝ) + ∑ c ∈ S, (((h c * (h c - 1) : ℕ) : ℝ) + K * (h c : ℝ) ^ 3)) :=
          add_le_add le_rfl hex
      _ = #Pset + (((δ + ∑ c ∈ S, h c * (h c - 1) : ℕ) : ℝ) +
          K * ((∑ c ∈ S, h c ^ 3 : ℕ) : ℝ)) := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum]
          push_cast
          ring
      _ ≤ #Pset + (((D ^ 2 : ℕ) : ℝ) + K * ((D ^ 3 : ℕ) : ℝ)) := by
          gcongr
      _ = _ := by
          rw [hK]
          push_cast
          ring
  · have hcP : c ∉ Pset := fun h ↦ hc (Finset.mem_union_left _ h)
    have hcex : c ∉ ex := fun h ↦ hc (Finset.mem_union_right _ h)
    refine hPset c hcP P hP (hgood c hcex P ?_ hP.1 hP.2.1)
    have := congrArg (Polynomial.map φ) (hQ.vanish c.1 c.2 P hP.1 hP.2.1)
    rwa [map_affineLineEval, Polynomial.map_zero] at this

end Count

end ReedSolomon

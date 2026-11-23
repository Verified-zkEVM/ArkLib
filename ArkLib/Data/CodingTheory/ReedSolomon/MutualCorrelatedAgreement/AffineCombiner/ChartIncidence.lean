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

A challenge with a nonpersistent root of a factor `R` gives a chart point `(y₀, a, b)`.
The point lies on `R(c, a + c b, y₀) = 0` and on at least `A` agreement cuts.
The incidence bound counts such points by `h · (n · 2 s d h / (A - B)) ^ 2`.
A positive-dimensional component on `B + 1` cuts supplies two distinct challenges,
whose reconstructions yield persistence after descent to the base field.

The agreement cuts are noncomputable polynomial constructions.
The excluded set is a predicate, with no algorithmic witness selection.

## Main definitions

* `ReedSolomon.affineChartAgreementCut`: a polynomial for one agreement position.
* `ReedSolomon.affineChartExcluded`: points sharing `B + 1` cuts with a different challenge.

## Main statements

* `ReedSolomon.regularLocus_subset_affineChartExcluded`: the regular points of a
  positive-dimensional component with `B + 1` cuts belong to the excluded set.
* `ReedSolomon.card_le_of_affineNonpersistent_roots`: the count for one factor.
* `ReedSolomon.exists_affineNonpersistent_finset_card_le`: outside a small set of challenges,
  every regular root of the factor with `A` agreements is persistent.

## References

* [Chiesa, A., Weissenberg, G., Yogev, E., and Zheng, K. Z.,
    *Affine combiners for Reed–Solomon proximity gaps*][CWYZ26], Claims 4.8 and 4.9 and
    Lemma 4.7 for one factor.
-/

@[expose] public section

namespace ReedSolomon

open MvPolynomial
open scoped Finset

variable {F : Type*} [Field F] {ι : Type*}
variable {E : Type*} [Field E]

/-- The agreement cut of the position `i`, with the received values mapped to `E`. -/
noncomputable def affineChartAgreementCut (domain : ι ↪ F) (f g : ι → F) (φ : F →+* E) (c : E)
    (R : MvPolynomial AffineVar E) (s d τ : ℕ) (i : ι) : MvPolynomial AffineChartVar E :=
  affineChartCut c R s d τ (φ (domain i)) (φ (f i)) (φ (g i))

/-- Chart points on `B + 1` cuts shared with a regular point on another challenge. -/
def affineChartExcluded (domain : ι ↪ F) (f g : ι → F) (φ : F →+* E) (c : E)
    (R : MvPolynomial AffineVar E) (s d τ B : ℕ) : Set (AffineChartVar → E) :=
  {pt | ∃ T : Finset ι, B + 1 ≤ #T ∧
    (∀ i ∈ T, aeval pt (affineChartAgreementCut domain f g φ c R s d τ i) = 0) ∧
    ∃ pt' : AffineChartVar → E, aeval pt' (affineChartSeparant c R) ≠ 0 ∧
      (∀ i ∈ T, aeval pt' (affineChartAgreementCut domain f g φ c R s d τ i) = 0) ∧
      pt' ∘ Sum.inr ≠ pt ∘ Sum.inr}

/-- For `2 s d - 1 ≤ τ`, two regular points on at least `B + 1 ≥ d + 1` common cuts
with the same challenge are equal. -/
theorem eq_of_affineChartAgreementCut (domain : ι ↪ F) (f g : ι → F) (φ : F →+* E) (c : E)
    (R : MvPolynomial AffineVar E) {s d τ B : ℕ} (hτ : 2 * s * d - 1 ≤ τ) (hdB : d ≤ B)
    (T : Finset ι) (hT : B + 1 ≤ #T) {pt pt' : AffineChartVar → E}
    (hS : aeval pt (affineChartSeparant c R) ≠ 0) (hS' : aeval pt' (affineChartSeparant c R) ≠ 0)
    (hcut : ∀ i ∈ T, aeval pt (affineChartAgreementCut domain f g φ c R s d τ i) = 0)
    (hcut' : ∀ i ∈ T, aeval pt' (affineChartAgreementCut domain f g φ c R s d τ i) = 0)
    (hab : pt' ∘ Sum.inr = pt ∘ Sum.inr) : pt' = pt := by
  classical
  have h0 : pt' (.inr 0) = pt (.inr 0) := congrFun hab 0
  have h1 : pt' (.inr 1) = pt (.inr 1) := congrFun hab 1
  -- The two reconstructions agree at the `B + 1` cut points, so they are equal.
  have hrec : affineChartPolynomial c R s d pt' = affineChartPolynomial c R s d pt := by
    have hinj : Set.InjOn (fun i ↦ φ (domain i)) (T : Set ι) :=
      fun i _ j _ hij ↦ domain.injective (φ.injective hij)
    refine Polynomial.eq_of_degree_sub_lt_of_eval_finset_eq (T.image fun i ↦ φ (domain i)) ?_ ?_
    · rw [Finset.card_image_of_injOn hinj]
      refine (Polynomial.degree_sub_le _ _).trans_lt ?_
      refine (max_le (degree_affineChartPolynomial_le c R s d pt')
        (degree_affineChartPolynomial_le c R s d pt)).trans_lt ?_
      exact_mod_cast (by omega : d < #T)
    · intro x hx
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
      rw [(affineChartCut_eq_zero_iff c R hτ _ _ _ pt' hS').mp (hcut' i hi),
        (affineChartCut_eq_zero_iff c R hτ _ _ _ pt hS).mp (hcut i hi), h0, h1]
  funext v
  rcases v with ⟨j⟩ | ⟨j⟩
  · obtain rfl : j = 0 := Subsingleton.elim _ _
    rw [← eval_affineChartPolynomial_center c R s d pt',
      ← eval_affineChartPolynomial_center c R s d pt, hrec]
  · exact congrFun hab j

/-- A positive-dimensional prime with `B + 1` agreement cuts has its regular points excluded.

Assume the separant is not in the prime ideal, `d ≤ B`, and `2 s d - 1 ≤ τ`.
The regular locus is infinite, and two of its points on the same challenge are equal. -/
theorem regularLocus_subset_affineChartExcluded [IsAlgClosed E] (domain : ι ↪ F)
    (f g : ι → F) (φ : F →+* E)
    (c : E) (R : MvPolynomial AffineVar E) {s d τ B : ℕ} (hτ : 2 * s * d - 1 ≤ τ)
    (hdB : d ≤ B) (J : Ideal (MvPolynomial AffineChartVar E)) (hJ : J.IsPrime)
    (hs : affineChartSeparant c R ∉ J) (hdim : 0 < (affineHilbertPolynomial J).natDegree)
    (hcuts : B + 1 ≤ {i | affineChartAgreementCut domain f g φ c R s d τ i ∈ J}.ncard) :
    {pt | pt ∈ zeroLocus E J ∧ aeval pt (affineChartSeparant c R) ≠ 0} ⊆
      affineChartExcluded domain f g φ c R s d τ B := by
  classical
  set U := {pt | pt ∈ zeroLocus E J ∧ aeval pt (affineChartSeparant c R) ≠ 0}
  have hregular : IsLeftRegular (Ideal.Quotient.mk J (affineChartSeparant c R)) :=
    IsLeftCancelMulZero.mul_left_cancel_of_ne_zero (mt Ideal.Quotient.eq_zero_iff_mem.mp hs)
  have hinfinite : U.Infinite := fun hfin ↦ by
    have := (finite_principalOpen_iff_natDegree_affineHilbertPolynomial_eq_zero hregular).mp hfin
    omega
  have hfin : {i | affineChartAgreementCut domain f g φ c R s d τ i ∈ J}.Finite :=
    Set.finite_of_ncard_pos (by omega)
  set T : Finset ι := hfin.toFinset
  have hT : B + 1 ≤ #T := by rwa [← Set.ncard_eq_toFinset_card _ hfin]
  have hcutU : ∀ pt ∈ U, ∀ i ∈ T,
      aeval pt (affineChartAgreementCut domain f g φ c R s d τ i) = 0 :=
    fun pt hpt i hi ↦ hpt.1 _ (hfin.mem_toFinset.mp hi)
  intro pt hpt
  refine ⟨T, hT, hcutU pt hpt, ?_⟩
  by_contra! hsame
  -- Every regular point has the challenge of `pt`, so it is `pt`.
  refine hinfinite ((Set.finite_singleton pt).subset fun pt' hpt' ↦ ?_)
  exact eq_of_affineChartAgreementCut domain f g φ c R hτ hdB T hT hpt.2 hpt'.2
    (hcutU pt hpt) (hcutU pt' hpt') (hsame pt' hpt'.2 (hcutU pt' hpt'))

variable [DecidableEq F] [Fintype ι]

/-- At the chart point of a regular root, a cut vanishes exactly at an agreement position. -/
theorem aeval_affineChartAgreementCut_point_eq_zero_iff [IsAlgClosed E] (domain : ι ↪ F)
    (f g : ι → F) (φ : F →+* E) (c : E) (R : MvPolynomial AffineVar E) (p e : ℕ) [ExpChar E p]
    {d : ℕ} {α β : F} {P : Polynomial F} (hP : P.degree ≤ d)
    (hroot : affineLineEval ((iterateFrobeniusEquiv E p e).symm (φ α))
      ((iterateFrobeniusEquiv E p e).symm (φ β)) (Polynomial.expand E (p ^ e) (P.map φ)) R = 0)
    (hsep : (affineLineEval ((iterateFrobeniusEquiv E p e).symm (φ α))
      ((iterateFrobeniusEquiv E p e).symm (φ β)) (Polynomial.expand E (p ^ e) (P.map φ))
        (pderiv none R)).eval c ≠ 0) (i : ι) :
    aeval (affineChartPoint c (p ^ e) ((iterateFrobeniusEquiv E p e).symm (φ α))
        ((iterateFrobeniusEquiv E p e).symm (φ β)) (P.map φ))
      (affineChartAgreementCut domain f g φ c R (p ^ e) d (2 * p ^ e * d - 1) i) = 0 ↔
      i ∈ polynomialAgreementSet domain (combinedWord domain f g (affineMultiplier α β)) P := by
  set fr := (iterateFrobeniusEquiv E p e).symm
  have hfr (x : E) : fr x ^ p ^ e = x := by
    rw [← iterateFrobeniusEquiv_def, RingEquiv.apply_symm_apply]
  have hS : aeval (affineChartPoint c (p ^ e) (fr (φ α)) (fr (φ β)) (P.map φ))
      (affineChartSeparant c R) ≠ 0 := by
    rwa [aeval_affineChartSeparant_point]
  rw [affineChartAgreementCut, affineChartCut_eq_zero_iff c R le_rfl _ _ _ _ hS,
    affineChartPolynomial_point c R rfl
      ((Polynomial.degree_map_le).trans hP) hroot hsep]
  simp only [affineChartPoint, Sum.elim_inr, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, hfr, polynomialAgreementSet, Finset.mem_filter, Finset.mem_univ,
    true_and, combinedWord_affineMultiplier, Polynomial.eval_map_apply]
  rw [← φ.injective.eq_iff]
  simp [map_add, map_mul, mul_comm]

/-- A regular root whose chart point is excluded is persistent.

The second challenge gives identities `P' - P = L g`, which descend to `F`.
Discarding at most one root of `L` leaves at least `B` regular agreements. -/
theorem isAffinePersistent_of_mem_affineChartExcluded [IsAlgClosed E] (domain : ι ↪ F)
    (f g : ι → F) (φ : F →+* E) (c : E) (R : MvPolynomial AffineVar E) (p e : ℕ) [ExpChar E p]
    {d B : ℕ} {α β : F} {P : Polynomial F} (hP : P.degree ≤ d)
    (hroot : affineLineEval ((iterateFrobeniusEquiv E p e).symm (φ α))
      ((iterateFrobeniusEquiv E p e).symm (φ β)) (Polynomial.expand E (p ^ e) (P.map φ)) R = 0)
    (hsep : (affineLineEval ((iterateFrobeniusEquiv E p e).symm (φ α))
      ((iterateFrobeniusEquiv E p e).symm (φ β)) (Polynomial.expand E (p ^ e) (P.map φ))
        (pderiv none R)).eval c ≠ 0)
    (hex : affineChartPoint c (p ^ e) ((iterateFrobeniusEquiv E p e).symm (φ α))
        ((iterateFrobeniusEquiv E p e).symm (φ β)) (P.map φ) ∈
      affineChartExcluded domain f g φ c R (p ^ e) d (2 * p ^ e * d - 1) B) :
    IsAffinePersistent domain f g d B α β P := by
  set fr := (iterateFrobeniusEquiv E p e).symm
  have hfr (x : E) : fr x ^ p ^ e = x := by
    rw [← iterateFrobeniusEquiv_def, RingEquiv.apply_symm_apply]
  obtain ⟨T, hT, hcut, pt', hS', hcut', hne⟩ := hex
  have hagree : T ⊆ polynomialAgreementSet domain (combinedWord domain f g
      (affineMultiplier α β)) P := fun i hi ↦
    (aeval_affineChartAgreementCut_point_eq_zero_iff domain f g φ c R p e hP hroot hsep i).mp
      (hcut i hi)
  -- The second challenge explains `g` on `T` by the ratio `(P' - P) / L`.
  set a' := pt' (.inr 0) ^ p ^ e - φ α
  set b' := pt' (.inr 1) ^ p ^ e - φ β
  set H := affineChartPolynomial c R (p ^ e) d pt' - P.map φ
  have hL : affineMultiplier a' b' ≠ 0 := by
    intro hL0
    have h0 := congrArg (fun p : Polynomial _ ↦ p.coeff 0) hL0
    have h1 := congrArg (fun p : Polynomial _ ↦ p.coeff 1) hL0
    simp only [affineMultiplier, Polynomial.coeff_add, Polynomial.coeff_zero, Polynomial.coeff_C,
      Polynomial.coeff_C_mul, Polynomial.coeff_X_zero, Polynomial.coeff_X_one] at h0 h1
    apply hne
    have hroot' (x y : E) (h : x ^ p ^ e - y = 0) : x = fr y := by
      apply (iterateFrobeniusEquiv E p e).injective
      rw [iterateFrobeniusEquiv_def, RingEquiv.apply_symm_apply]
      exact sub_eq_zero.mp h
    funext j
    fin_cases j
    · exact hroot' _ _ (by simpa using h0)
    · exact hroot' _ _ (by simpa using h1)
  have hH : H.degree ≤ d := (Polynomial.degree_sub_le _ _).trans
    (max_le (degree_affineChartPolynomial_le c R _ d pt') ((Polynomial.degree_map_le).trans hP))
  have hexplain : ∀ k : T, H.eval (φ (domain k)) =
      (affineMultiplier a' b').eval (φ (domain k)) * φ (g k) := by
    rintro ⟨i, hi⟩
    have h' := (affineChartCut_eq_zero_iff c R le_rfl _ _ _ pt' hS').mp (hcut' i hi)
    have h := hagree hi
    simp only [polynomialAgreementSet, Finset.mem_filter, Finset.mem_univ, true_and,
      combinedWord_affineMultiplier] at h
    simp only [H, Polynomial.eval_sub, h', Polynomial.eval_map_apply, h, eval_affineMultiplier,
      a', b', map_add, map_mul]
    ring
  obtain ⟨H₀, L₀, hL₀, hL₀1, hH₀, h₀⟩ := exists_lineRatioWitness_of_map φ
    (fun k : T ↦ domain k) (fun k : T ↦ g k) d hL (degree_affineMultiplier_le a' b') hH hexplain
  exact isAffinePersistent_of_commonAgreement domain f g T hT hagree hL₀ hL₀1 hH₀
    fun i hi ↦ h₀ ⟨i, hi⟩

/-- The set `S` of challenges with chosen simple, nonpersistent roots has bounded size.

Assume `1 ≤ d ≤ B < A ≤ n`, where `n` is the domain size.
For each `c ∈ S`, the chosen candidate `w c` has degree at most `d` and at least `A` agreements.
Its expansion is a simple, nonpersistent root of the factor along `c`.
The bound on `#S` is
`h · (n · 2 p^e d h / (A - B)) ^ 2`, where `h` bounds the factor's `(Y, Z)`-degree. -/
theorem card_le_of_affineNonpersistent_roots [IsAlgClosed E] (domain : ι ↪ F) (f g : ι → F)
    (φ : F →+* E) (p e : ℕ) [ExpChar E p] (R : MvPolynomial AffineVar E) {d h A B : ℕ}
    (hd : 1 ≤ d) (hdB : d ≤ B) (hBA : B < A) (hAn : A ≤ Fintype.card ι)
    (hR : R.weightedTotalDegree affineYZWeight ≤ h)
    (S : Finset (F × F)) (w : F × F → Polynomial F) (hdeg : ∀ c ∈ S, (w c).degree ≤ d)
    (hroot : ∀ c ∈ S, affineLineEval ((iterateFrobeniusEquiv E p e).symm (φ c.1))
      ((iterateFrobeniusEquiv E p e).symm (φ c.2))
        (Polynomial.expand E (p ^ e) ((w c).map φ)) R = 0)
    (hsep : ∀ c ∈ S, affineLineEval ((iterateFrobeniusEquiv E p e).symm (φ c.1))
      ((iterateFrobeniusEquiv E p e).symm (φ c.2))
        (Polynomial.expand E (p ^ e) ((w c).map φ)) (pderiv none R) ≠ 0)
    (hagree : ∀ c ∈ S, A ≤ #(polynomialAgreementSet domain
      (combinedWord domain f g (affineMultiplier c.1 c.2)) (w c)))
    (hnp : ∀ c ∈ S, ¬ IsAffinePersistent domain f g d B c.1 c.2 (w c)) :
    (#S : ℚ) ≤ h * (((Fintype.card ι * (2 * p ^ e * d * h) : ℕ) : ℚ) / ((A - B : ℕ) : ℚ)) ^ 2 := by
  classical
  obtain rfl | ⟨c₀, hc₀⟩ := S.eq_empty_or_nonempty
  · simp only [Finset.card_empty, Nat.cast_zero]
    positivity
  set fr := (iterateFrobeniusEquiv E p e).symm
  -- One center where every separant along a line of `S` is nonzero.
  obtain ⟨c, hc⟩ := Polynomial.exists_forall_eval_ne_zero S _ hsep
  set pt : F × F → AffineChartVar → E := fun x ↦
    affineChartPoint c (p ^ e) (fr (φ x.1)) (fr (φ x.2)) ((w x).map φ)
  have hinj : Set.InjOn pt S := by
    intro x _ y _ hxy
    have h0 := congrFun hxy (.inr 0)
    have h1 := congrFun hxy (.inr 1)
    simp only [pt, affineChartPoint, Sum.elim_inr, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one] at h0 h1
    exact Prod.ext (φ.injective (fr.injective h0)) (φ.injective (fr.injective h1))
  have hS (x) (hx : x ∈ S) : aeval (pt x) (affineChartSeparant c R) ≠ 0 := by
    rw [aeval_affineChartSeparant_point]
    exact hc x hx
  have hsepR : affineChartSeparant c R ≠ 0 := fun h0 ↦ hS c₀ hc₀ (by rw [h0, map_zero])
  have hg : affineChartEquation c R ≠ 0 := fun h0 ↦
    hsepR (by rw [← pderiv_affineChartEquation, h0, map_zero])
  have hbound := card_le_of_agreement_off_excluded_of_hypersurface (K := E) hg
    (affineChartSeparant c R) (totalDegree_affineChartEquation_le c hR) []
    (by simp) (affineChartAgreementCut domain f g φ c R (p ^ e) d (2 * p ^ e * d - 1))
    (fun i ↦ totalDegree_affineChartCut_le c hR hd (Nat.one_le_pow _ _ (expChar_pos E p)) _ _ _)
    (L := B + 1) (A := A) (by omega) (by omega)
    (affineChartExcluded domain f g φ c R (p ^ e) d (2 * p ^ e * d - 1) B)
    (fun J hJ hsJ _ _ hdim hL ↦
      regularLocus_subset_affineChartExcluded domain f g φ c R le_rfl hdB J hJ hsJ hdim hL)
    (S.image pt)
    (by
      intro x hx
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
      refine ⟨?_, hS y hy, by simp, fun hex ↦ hnp y hy ?_⟩
      · rw [aeval_affineChartEquation_point, hroot y hy, Polynomial.eval_zero]
      · exact isAffinePersistent_of_mem_affineChartExcluded domain f g φ c R p e (hdeg y hy)
          (hroot y hy) (hc y hy) hex)
    (by
      intro x hx
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
      refine (hagree y hy).trans_eq ?_
      rw [← Set.ncard_coe_finset]
      congr 1
      ext i
      exact (aeval_affineChartAgreementCut_point_eq_zero_iff domain f g φ c R p e (hdeg y hy)
        (hroot y hy) (hc y hy) i).symm)
  have hσ : Nat.card AffineChartVar - 1 = 2 := by simp [Nat.card_eq_fintype_card]
  have hAB : A - (B + 1) + 1 = A - B := by omega
  rwa [Finset.card_image_of_injOn hinj, hσ, hAB] at hbound

/-- Outside at most `h · (n · 2 p^e d h / (A - B)) ^ 2` challenges, candidates are persistent.

Assume `1 ≤ d ≤ B < A ≤ n`, where `n` is the domain size and `h` bounds the factor's
`(Y, Z)`-degree.
The guarantee covers every candidate of degree at most `d` with at least `A` agreements
whose expansion `P(X ^ (p ^ e))` is a simple root of the factor along the line. -/
theorem exists_affineNonpersistent_finset_card_le [Finite F] [IsAlgClosed E] (domain : ι ↪ F)
    (f g : ι → F) (φ : F →+* E) (p e : ℕ) [ExpChar E p] (R : MvPolynomial AffineVar E)
    {d h A B : ℕ} (hd : 1 ≤ d) (hdB : d ≤ B) (hBA : B < A) (hAn : A ≤ Fintype.card ι)
    (hR : R.weightedTotalDegree affineYZWeight ≤ h) :
    ∃ ex : Finset (F × F),
      (#ex : ℚ) ≤ h * (((Fintype.card ι * (2 * p ^ e * d * h) : ℕ) : ℚ) / ((A - B : ℕ) : ℚ)) ^ 2 ∧
      ∀ c ∉ ex, ∀ P : Polynomial F, P.degree ≤ d →
        affineLineEval ((iterateFrobeniusEquiv E p e).symm (φ c.1))
          ((iterateFrobeniusEquiv E p e).symm (φ c.2))
            (Polynomial.expand E (p ^ e) (P.map φ)) R = 0 →
        affineLineEval ((iterateFrobeniusEquiv E p e).symm (φ c.1))
          ((iterateFrobeniusEquiv E p e).symm (φ c.2))
            (Polynomial.expand E (p ^ e) (P.map φ)) (pderiv none R) ≠ 0 →
        A ≤ #(polynomialAgreementSet domain
          (combinedWord domain f g (affineMultiplier c.1 c.2)) P) →
        IsAffinePersistent domain f g d B c.1 c.2 P := by
  classical
  have := Fintype.ofFinite F
  set fr := (iterateFrobeniusEquiv E p e).symm
  -- A challenge is bad when some regular candidate with `A` agreements is not persistent.
  let Bad (c : F × F) (P : Polynomial F) : Prop := P.degree ≤ d ∧
    affineLineEval (fr (φ c.1)) (fr (φ c.2)) (Polynomial.expand E (p ^ e) (P.map φ)) R = 0 ∧
    affineLineEval (fr (φ c.1)) (fr (φ c.2)) (Polynomial.expand E (p ^ e) (P.map φ))
      (pderiv none R) ≠ 0 ∧
    A ≤ #(polynomialAgreementSet domain (combinedWord domain f g (affineMultiplier c.1 c.2)) P) ∧
    ¬ IsAffinePersistent domain f g d B c.1 c.2 P
  let ex : Finset (F × F) := {c | ∃ P, Bad c P}
  let w (c : F × F) : Polynomial F := if hc : ∃ P, Bad c P then hc.choose else 0
  have hw (c) (hc : c ∈ ex) : Bad c (w c) := by
    have hc' : ∃ P, Bad c P := (Finset.mem_filter.mp hc).2
    simpa only [w, hc', ↓reduceDIte] using hc'.choose_spec
  refine ⟨ex, card_le_of_affineNonpersistent_roots domain f g φ p e R hd hdB hBA hAn hR ex w
    (fun c hc ↦ (hw c hc).1) (fun c hc ↦ (hw c hc).2.1) (fun c hc ↦ (hw c hc).2.2.1)
    (fun c hc ↦ (hw c hc).2.2.2.1) (fun c hc ↦ (hw c hc).2.2.2.2), ?_⟩
  intro c hc P hP hroot hsep hA
  by_contra hnp
  exact hc (Finset.mem_filter.mpr ⟨Finset.mem_univ _, P, hP, hroot, hsep, hA, hnp⟩)

end ReedSolomon

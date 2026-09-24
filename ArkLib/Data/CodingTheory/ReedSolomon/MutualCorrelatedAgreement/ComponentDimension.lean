/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.Polynomial.Differential.TaylorChart
public import ArkLib.Data.Polynomial.Differential.RationalTaylorAlgebra
public import ArkLib.Data.Polynomial.Differential.TaylorChartAlgebra
public import ArkLib.Data.Polynomial.Differential.BaseChange
public import ArkLib.ToMathlib.MvPolynomial.PolynomialCoefficients
public import ArkLib.ToMathlib.RingTheory.MvPolynomial.CoefficientEvaluation
public import ArkLib.ToMathlib.RingTheory.MvPolynomial.AwayPresentation
public import ArkLib.ToMathlib.RingTheory.Nullstellensatz.AgreementIncidence
public import ArkLib.ToMathlib.RingTheory.Nullstellensatz.DimensionSensitiveIncidence
public import Mathlib.RingTheory.Localization.FractionRing
/-!
# Dimensions of retained Taylor-chart components

This module relates Taylor-chart coordinates to symbolic source coordinates after the initial
separant is inverted. It bounds the dimension of retained primes containing agreement equations
by mapping those equations to kernels of coefficient-evaluation maps. The resulting component
bounds provide the dimension hypotheses for hybrid agreement incidence.

## Main statements

* `chart_prime_affineHilbertPolynomial_natDegree_le_of_agreements_of_exponent` and
  `symbolicSource_prime_affineHilbertPolynomial_natDegree_le_of_polynomial_agreements_of_exponent`:
  retained-prime bounds from distinct agreement cuts.
* `chart_dimensionSensitive_component_of_exponent`,
  `symbolicSourcePolynomial_dimensionSensitive_component_of_exponent`, and
  `symbolicSource_dimensionSensitive_component_of_exponent`: hereditary component budgets.
* `finite_symbolicSource_agreementLocus_off_excluded_and_ncard_le_hybrid_of_exponent`:
  the hybrid incidence bound on a retained source locus.

## References

* [DKT26]
-/

@[expose] public section

open PolynomialDifferential

noncomputable section

namespace ReedSolomon

open Polynomial MvPolynomial

variable {F E : Type*} [Field F] [Field E] {n k K r : ℕ}

/-- The polynomial ring in the initial Taylor-jet coordinates. -/
abbrev ChartRing (r : ℕ) (E : Type*) [Field E] :=
  MvPolynomial (Fin (r + 1)) E

/-- The retained Taylor-chart ring localized away from the class of `s` modulo `P`. -/
abbrev ChartAway {r : ℕ} {E : Type*} [Field E]
    (P : Ideal (ChartRing r E)) (s : ChartRing r E) :=
  Localization.Away (Ideal.Quotient.mk P s)

private theorem commonTaylorNumeratorOver_self (center : E)
    (Q : DifferentialPolynomial E r) (K : ℕ) (l : Fin K) (τ : ℕ) :
    commonTaylorNumeratorOver (F := E) center Q τ l.val =
      commonTaylorNumerator center Q τ l.val := by
  simp only [commonTaylorNumeratorOver, commonTaylorNumerator, rationalTaylorNumeratorOver_eq]

/-- A jet coordinate in a localized ordinary Taylor chart. -/
def localizedChartJet (P : Ideal (ChartRing r E)) (s : ChartRing r E)
    (j : Fin (r + 1)) : ChartAway P s :=
  algebraMap (ChartRing r E ⧸ P) (ChartAway P s)
    (Ideal.Quotient.mk P (MvPolynomial.X j))

/-- The reconstructed centered coefficient in a localized ordinary Taylor chart. -/
def localizedChartCoefficient (center : E) (Q : DifferentialPolynomial E r) (K : ℕ)
    (P : Ideal (ChartRing r E)) (l : Fin K) (τ : ℕ) :
    ChartAway P (initialJetSeparant center Q) :=
  algebraMap (ChartRing r E ⧸ P) (ChartAway P (initialJetSeparant center Q))
      (Ideal.Quotient.mk P (commonTaylorNumerator center Q τ l.val)) *
    IsLocalization.Away.invSelf (Ideal.Quotient.mk P (initialJetSeparant center Q)) ^ τ

/-- Below the differential order, reconstructed coefficients recover the chart jets after the
separant has been inverted. -/
theorem localizedChartCoefficient_eq_jet_of_exponent
    (center : E) (Q : DifferentialPolynomial E r) (K τ : ℕ)
    (hτ : TaylorExponentSufficient r K τ) (hK : r < K)
    (P : Ideal (ChartRing r E)) (hP : P.IsPrime)
    (hs : initialJetSeparant center Q ∉ P) (l : Fin K) (hl : l.val ≤ r) :
    localizedChartCoefficient center Q K P l (τ := τ) =
      localizedChartJet P (initialJetSeparant center Q) ⟨l.val, by omega⟩ := by
  let s := initialJetSeparant center Q
  let L := ChartAway P s
  let _ : P.IsPrime := hP
  have hs0 : Ideal.Quotient.mk P s ≠ 0 := by
    intro hz
    exact hs (Ideal.Quotient.eq_zero_iff_mem.mp hz)
  let _ : IsDomain L := Localization.Away.isDomain hs0
  let Frac := FractionRing L
  let emb : L →+* Frac := algebraMap L Frac
  let x : Fin (r + 1) → Frac := fun j ↦ emb (localizedChartJet P s j)
  let φ : E →ₐ[E] Frac := Algebra.ofId E Frac
  let src : ChartRing r E →ₐ[E] Frac :=
    (IsScalarTower.toAlgHom E L Frac).comp
      ((IsScalarTower.toAlgHom E (ChartRing r E ⧸ P) L).comp (Ideal.Quotient.mkₐ E P))
  have hsrc : src = MvPolynomial.aeval x := by
    apply MvPolynomial.algHom_ext
    intro j
    simp only [src, x, localizedChartJet, AlgHom.comp_apply, MvPolynomial.aeval_X,
      IsScalarTower.toAlgHom_apply]
    rfl
  have heval (p : ChartRing r E) :
      emb (algebraMap (ChartRing r E ⧸ P) L (Ideal.Quotient.mk P p)) = aeval x p := by
    exact DFunLike.congr_fun hsrc p
  have hsepEval : aeval x
      (MvPolynomial.map φ.toRingHom (initialJetSeparant center Q)) =
      emb (algebraMap (ChartRing r E ⧸ P) L (Ideal.Quotient.mk P s)) :=
    (MvPolynomial.aeval_map_algebraMap Frac x _).trans (heval s).symm
  have hsepNe : aeval x
      (MvPolynomial.map φ.toRingHom (initialJetSeparant center Q)) ≠ 0 := by
    rw [hsepEval]
    exact ((IsLocalization.Away.algebraMap_isUnit (Ideal.Quotient.mk P s)).map emb).ne_zero
  have hrec := aeval_map_commonTaylorNumeratorOver_reconstruction_of_exponent φ center Q K τ
    hτ x hsepNe l
  have hnumEval : aeval x (MvPolynomial.map φ.toRingHom
      (commonTaylorNumeratorOver (F := E) center Q τ l.val)) =
      emb (algebraMap (ChartRing r E ⧸ P) L
        (Ideal.Quotient.mk P (commonTaylorNumerator center Q τ l.val))) := by
    rw [commonTaylorNumeratorOver_self]
    exact (MvPolynomial.aeval_map_algebraMap Frac x _).trans (heval _).symm
  have hcancel :
      emb (algebraMap (ChartRing r E ⧸ P) L (Ideal.Quotient.mk P s)) ^ τ *
          emb (IsLocalization.Away.invSelf (Ideal.Quotient.mk P s)) ^ τ = 1 := by
    rw [← mul_pow, ← map_mul, IsLocalization.Away.mul_invSelf, map_one, one_pow]
  have hjet := congrFun
    (polynomialJet_rationalTaylorPolynomial (φ center) (MvPolynomial.map φ.toRingHom Q)
      hK x) ⟨l.val, by omega⟩
  rw [polynomialJet, Polynomial.hasseJet_eq_taylor_coeff] at hjet
  apply IsFractionRing.injective L Frac
  rw [localizedChartCoefficient, map_mul, map_pow, ← hnumEval, hrec, hsepEval, mul_right_comm,
    hcancel, one_mul]
  exact hjet

/-- Map the first `k` reconstructed coefficients into a retained fixed Taylor chart. -/
def chartCoefficientMap (center : E) (Q : DifferentialPolynomial E r)
    (K k : ℕ) (hkK : k ≤ K) (P : Ideal (ChartRing r E)) (τ : ℕ) :
    MvPolynomial (Fin k) E →ₐ[E] ChartAway P (initialJetSeparant center Q) :=
  MvPolynomial.aeval fun l ↦
    localizedChartCoefficient center Q K P (Fin.castLE hkK l) (τ := τ)

/-- An algebra map out of a polynomial ring lands in the range of another one once every
variable does. -/
private theorem algHom_mem_range_of_X_mem {σ ι A : Type*} [CommRing A] [Algebra E A]
    (f : MvPolynomial σ E →ₐ[E] A) (Φ : MvPolynomial ι E →ₐ[E] A)
    (h : ∀ j, f (MvPolynomial.X j) ∈ Set.range Φ) (p : MvPolynomial σ E) :
    f p ∈ Set.range Φ := by
  induction p using MvPolynomial.induction_on with
  | C a => exact ⟨MvPolynomial.C a, by rw [MvPolynomial.algHom_C, MvPolynomial.algHom_C]⟩
  | add p q hp hq =>
      obtain ⟨p', hp'⟩ := hp
      obtain ⟨q', hq'⟩ := hq
      exact ⟨p' + q', by rw [map_add, map_add, hp', hq']⟩
  | mul_X p j hp =>
      obtain ⟨p', hp'⟩ := hp
      obtain ⟨x, hx⟩ := h j
      exact ⟨p' * x, by rw [map_mul, map_mul, hp', hx]⟩

/-- The first `k` reconstructed coefficients generate every chart coordinate after the
separant is inverted and the high reconstructed coefficients vanish. -/
theorem chartCoordinate_mem_range_chartCoefficientMap_of_exponent
    (center : E) (Q : DifferentialPolynomial E r) (K k τ : ℕ)
    (hτ : TaylorExponentSufficient r K τ) (hK : r < K) (hkK : k ≤ K)
    (P : Ideal (ChartRing r E)) (hP : P.IsPrime)
    (hs : initialJetSeparant center Q ∉ P)
    (hhigh : ∀ l : Fin K, k ≤ l.val →
      commonTaylorNumerator center Q τ l.val ∈ P)
    (p : ChartRing r E) :
    algebraMap (ChartRing r E ⧸ P) (ChartAway P (initialJetSeparant center Q))
        (Ideal.Quotient.mk P p) ∈
      Set.range (chartCoefficientMap center Q K k hkK P (τ := τ)) := by
  refine algHom_mem_range_of_X_mem
    ((IsScalarTower.toAlgHom E (ChartRing r E ⧸ P) _).comp (Ideal.Quotient.mkₐ E P)) _
    (fun j ↦ ?_) p
  by_cases hjk : j.val < k
  · exact ⟨MvPolynomial.X ⟨j.val, hjk⟩, (MvPolynomial.aeval_X _ _).trans
      (localizedChartCoefficient_eq_jet_of_exponent center Q K τ hτ hK P hP hs _
        (Nat.le_of_lt_succ j.isLt))⟩
  · refine ⟨0, Eq.symm ((localizedChartCoefficient_eq_jet_of_exponent center Q K τ hτ hK P hP hs
      ⟨j.val, by omega⟩ (Nat.le_of_lt_succ j.isLt)).symm.trans ?_ |>.trans (map_zero _).symm)⟩
    rw [localizedChartCoefficient, Ideal.Quotient.eq_zero_iff_mem.mpr
      (hhigh _ (Nat.le_of_not_gt hjk)), map_zero, zero_mul]

/-- Truncate a cleared agreement sum whose high terms vanish, then cancel the cleared power. -/
private theorem sum_castLE_mul_pow_eq_of_cleared {L : Type*} [CommRing L] {K k τ : ℕ}
    (hkK : k ≤ K) (a y s t : L) (u : Fin K → L)
    (hcut : (∑ l : Fin K, a ^ l.val * u l) - y * s ^ τ = 0)
    (hhigh : ∀ l : Fin K, k ≤ l.val → u l = 0) (hcancel : s ^ τ * t ^ τ = 1) :
    ∑ l : Fin k, a ^ l.val * (u (Fin.castLE hkK l) * t ^ τ) = y := by
  have hfull : ∑ l : Fin k, a ^ l.val * u (Fin.castLE hkK l) = y * s ^ τ := by
    rw [← sub_eq_zero.mp hcut, ← (finCongr (Nat.add_sub_of_le hkK)).sum_comp,
      Fin.sum_univ_add, add_eq_left.mpr (Finset.sum_eq_zero fun l _ ↦ by
        rw [hhigh _ (Nat.le_add_right k l.val), mul_zero])]
    rfl
  simp_rw [← mul_assoc]
  rw [← Finset.sum_mul, hfull, mul_assoc, hcancel, mul_one]

/-- A retained Taylor agreement cut becomes its ordinary coefficient-evaluation equation under
the fixed-chart coefficient map. -/
theorem fixedCoefficientEvaluation_mem_ker_chartCoefficientMap_of_exponent
    (center : E) (Q : DifferentialPolynomial E r) (K k τ : ℕ) (hkK : k ≤ K)
    (P : Ideal (ChartRing r E)) (α y : E)
    (hcut : taylorAgreementEquation center Q K α y (τ := τ) ∈ P)
    (hhigh : ∀ l : Fin K, k ≤ l.val →
      commonTaylorNumerator center Q τ l.val ∈ P) :
    fixedCoefficientEvaluation k (α - center) y ∈
      RingHom.ker (chartCoefficientMap center Q K k hkK P (τ := τ)).toRingHom := by
  let _ : DistribMulAction (ChartRing r E ⧸ P) (ChartRing r E ⧸ P) := inferInstance
  let s := initialJetSeparant center Q
  let L := ChartAway P s
  let src : ChartRing r E →ₐ[E] L :=
    (IsScalarTower.toAlgHom E (ChartRing r E ⧸ P) L).comp (Ideal.Quotient.mkₐ E P)
  have hcut0 : src (taylorAgreementEquation center Q K α y (τ := τ)) = 0 := by
    change algebraMap (ChartRing r E ⧸ P) L
      (Ideal.Quotient.mk P (taylorAgreementEquation center Q K α y (τ := τ))) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hcut, map_zero]
  have hhigh0 (l : Fin K) (hl : k ≤ l.val) :
      src (commonTaylorNumerator center Q τ l.val) = 0 := by
    change algebraMap (ChartRing r E ⧸ P) L
      (Ideal.Quotient.mk P
        (commonTaylorNumerator center Q τ l.val)) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr (hhigh l hl), map_zero]
  have hcancel : src s ^ τ *
      IsLocalization.Away.invSelf (Ideal.Quotient.mk P s) ^ τ = 1 := by
    have hbase : src s * IsLocalization.Away.invSelf (Ideal.Quotient.mk P s) = 1 :=
      IsLocalization.Away.mul_invSelf (S := L) (Ideal.Quotient.mk P s)
    simpa only [mul_pow, one_pow] using congrArg (fun q : L ↦ q ^ τ) hbase
  have hcutEq :
      (∑ l : Fin K, (algebraMap E L (α - center)) ^ l.val *
        src (commonTaylorNumerator center Q τ l.val)) -
          algebraMap E L y * src s ^ τ = 0 := by
    simpa only [taylorAgreementEquation, map_sub, map_sum, map_mul, map_pow,
      MvPolynomial.algHom_C] using hcut0
  have hlocalized :
      (∑ l : Fin k, (algebraMap E L (α - center)) ^ l.val *
        localizedChartCoefficient center Q K P (Fin.castLE hkK l) (τ := τ)) =
          algebraMap E L y :=
    sum_castLE_mul_pow_eq_of_cleared hkK _ _ _ _
      (fun l : Fin K ↦ src (commonTaylorNumerator center Q τ l.val)) hcutEq hhigh0 hcancel
  change chartCoefficientMap center Q K k hkK P (τ := τ)
    (fixedCoefficientEvaluation k (α - center) y) = 0
  rw [fixedCoefficientEvaluation, map_sub, map_sum]
  simp only [chartCoefficientMap, map_mul, map_pow, MvPolynomial.aeval_C, MvPolynomial.aeval_X]
  exact sub_eq_zero.mpr hlocalized

/-- A retained fixed Taylor-chart prime containing `c` distinct agreement cuts has dimension at
most `k-c`.  The proof reuses the ordinary Vandermonde quotient bound and the generic
localization comparison used by the source-coordinate theorem. -/
theorem chart_prime_affineHilbertPolynomial_natDegree_le_of_agreements_of_exponent
    (center : E) (Q : DifferentialPolynomial E r) (K k c τ : ℕ)
    (hτ : TaylorExponentSufficient r K τ) (hK : r < K)
    (hkK : k ≤ K)
    (P : Ideal (ChartRing r E)) (hP : P.IsPrime)
    (hs : initialJetSeparant center Q ∉ P)
    (hhigh : ∀ l : Fin K, k ≤ l.val →
      commonTaylorNumerator center Q τ l.val ∈ P)
    (α : Fin c ↪ E) (y : Fin c → E)
    (hcut : ∀ i, taylorAgreementEquation center Q K (α i) (y i) (τ := τ) ∈ P) :
    (affineHilbertPolynomial P).natDegree ≤ k - c := by
  classical
  let s := initialJetSeparant center Q
  have hs0 : Ideal.Quotient.mk P s ≠ 0 := by
    intro hz
    exact hs (Ideal.Quotient.eq_zero_iff_mem.mp hz)
  let Φ := chartCoefficientMap center Q K k hkK P (τ := τ)
  let J : Ideal (MvPolynomial (Fin k) E) := RingHom.ker Φ.toRingHom
  let β : Fin c ↪ E :=
    ⟨fun i ↦ α i - center, fun i j hij ↦ α.injective (sub_left_injective hij)⟩
  have heval (i : Fin c) : fixedCoefficientEvaluation k (β i) (y i) ∈ J := by
    exact fixedCoefficientEvaluation_mem_ker_chartCoefficientMap_of_exponent
      center Q K k τ hkK P (α i) (y i) (hcut i) hhigh
  have hJdim : (affineHilbertPolynomial J).natDegree ≤ k - c :=
    natDegree_affineHilbertPolynomial_le_of_fixedCoefficientEvaluation_mem β y heval
  have hregular : IsLeftRegular (Ideal.Quotient.mk P s) := by
    rw [isLeftRegular_iff_isRegular]
    exact isRegular_iff_ne_zero.mpr hs0
  exact natDegree_affineHilbertPolynomial_le_of_away_range P s hregular Φ
    (chartCoordinate_mem_range_chartCoefficientMap_of_exponent
      center Q K k τ hτ hK hkK P hP hs hhigh) hJdim


/-- A positive-dimensional retained fixed-chart prime has dimension plus its number of
agreement cuts bounded by the coefficient count. -/
theorem chart_dimensionSensitive_component_of_exponent
    (center : E) (Q : DifferentialPolynomial E r) (K k n τ : ℕ)
    (hτ : TaylorExponentSufficient r K τ) (hK : r < K) (hkK : k ≤ K)
    (P : Ideal (ChartRing r E)) (hP : P.IsPrime)
    (hs : initialJetSeparant center Q ∉ P)
    (hhigh : ∀ l : Fin K, k ≤ l.val →
      commonTaylorNumerator center Q τ l.val ∈ P)
    (α : Fin n ↪ E) (y : Fin n → E)
    (hd : 0 < (affineHilbertPolynomial P).natDegree) :
    let cuts : Fin n → ChartRing r E := fun i ↦
      taylorAgreementEquation center Q K (α i) (y i) (τ := τ)
    (affineHilbertPolynomial P).natDegree + {i | cuts i ∈ P}.ncard ≤ k := by
  classical
  dsimp only
  let s := initialJetSeparant center Q
  let Φ := chartCoefficientMap center Q K k hkK P (τ := τ)
  let J : Ideal (MvPolynomial (Fin k) E) := RingHom.ker Φ.toRingHom
  let β : Fin n ↪ E :=
    ⟨fun i ↦ α i - center, fun i j hij ↦ α.injective (sub_left_injective hij)⟩
  have heval (i : Fin n)
      (hi : taylorAgreementEquation center Q K (α i) (y i) (τ := τ) ∈ P) :
      fixedCoefficientEvaluation k (α i - center) (y i) ∈ J := by
    exact fixedCoefficientEvaluation_mem_ker_chartCoefficientMap_of_exponent
      center Q K k τ hkK P (α i) (y i) hi hhigh
  have hregular : IsLeftRegular (Ideal.Quotient.mk P s) := by
    rw [isLeftRegular_iff_isRegular]
    exact isRegular_iff_ne_zero.mpr (by
      intro hz
      exact hs (Ideal.Quotient.eq_zero_iff_mem.mp hz))
  have hdegree : (affineHilbertPolynomial P).natDegree ≤
      (affineHilbertPolynomial J).natDegree :=
    natDegree_affineHilbertPolynomial_le_of_away_range P s hregular Φ
      (chartCoordinate_mem_range_chartCoefficientMap_of_exponent
        center Q K k τ hτ hK hkK P hP hs hhigh) le_rfl
  have hJdim : 0 < (affineHilbertPolynomial J).natDegree := by omega
  have hJbound := natDegree_affineHilbertPolynomial_add_ncard_le_of_fixedCoefficientEvaluation
    β y hJdim
  have hsubset : {i | taylorAgreementEquation center Q K (α i) (y i) (τ := τ) ∈ P} ⊆
      {i | fixedCoefficientEvaluation k (β i) (y i) ∈ J} := by
    intro i hi
    exact heval i hi
  have hcount := Set.ncard_le_ncard hsubset (Set.toFinite _)
  exact (Nat.add_le_add hdegree hcount).trans hJbound

/-- The polynomial ring in the challenge and initial Taylor-jet coordinates. -/
abbrev SourceRing (r : ℕ) (E : Type*) [Field E] :=
  MvPolynomial (Option (Fin (r + 1))) E

/-- The retained symbolic source ring localized away from the class of `s` modulo `P`. -/
abbrev SourceAway {r : ℕ} {E : Type*} [Field E]
    (P : Ideal (SourceRing r E)) (s : SourceRing r E) :=
  Localization.Away (Ideal.Quotient.mk P s)

/-- The challenge coordinate in a retained source localization. -/
def localizedSourceChallenge (P : Ideal (SourceRing r E)) (s : SourceRing r E) :
    SourceAway P s :=
  algebraMap (SourceRing r E ⧸ P) (SourceAway P s)
    (Ideal.Quotient.mk P (MvPolynomial.X none))

/-- A source jet coordinate in a retained source localization. -/
def localizedSourceJet (P : Ideal (SourceRing r E)) (s : SourceRing r E)
    (j : Fin (r + 1)) : SourceAway P s :=
  algebraMap (SourceRing r E ⧸ P) (SourceAway P s)
    (Ideal.Quotient.mk P (MvPolynomial.X (some j)))

/-- The `l`-th reconstructed centered coefficient in the source localization. -/
def localizedSourceCoefficient (center : E) (Q : DifferentialPolynomial E[X] r) (K : ℕ)
    (P : Ideal (SourceRing r E)) (l : Fin K) (τ : ℕ := 2 * K) :
    SourceAway P (jointInitialJetSeparant center Q) :=
  algebraMap (SourceRing r E ⧸ P)
      (SourceAway P (jointInitialJetSeparant center Q))
      (Ideal.Quotient.mk P (jointCommonTaylorNumerator center Q τ l)) *
    IsLocalization.Away.invSelf
      (Ideal.Quotient.mk P (jointInitialJetSeparant center Q)) ^ τ

/-- Evaluating a flattened source polynomial first evaluates its polynomial coefficients at the
challenge coordinate. -/
private theorem aeval_optionEquivRight_symm {A : Type*} [CommRing A] [Algebra E A]
    (x : Option (Fin (r + 1)) → A) (p : MvPolynomial (Fin (r + 1)) E[X]) :
    aeval x ((MvPolynomial.optionEquivRight E (Fin (r + 1))).symm p) =
      aeval (fun j ↦ x (some j)) (MvPolynomial.map (Polynomial.aeval (x none)).toRingHom p) := by
  induction p using MvPolynomial.induction_on with
  | C p =>
      rw [MvPolynomial.optionEquivRight_symm_C, ← Polynomial.aeval_algHom_apply]
      simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p j hp =>
      simp only [map_mul, hp, MvPolynomial.optionEquivRight_symm_X, MvPolynomial.aeval_X,
        MvPolynomial.map_X]

/-- Below the differential order, the reconstructed coefficients recover the actual jet
coordinates in the retained source localization. -/
theorem localizedSourceCoefficient_eq_jet_of_exponent
    (center : E) (Q : DifferentialPolynomial E[X] r) (K τ : ℕ)
    (hτ : TaylorExponentSufficient r K τ) (hK : r < K)
    (P : Ideal (SourceRing r E)) (hP : P.IsPrime)
    (hs : jointInitialJetSeparant center Q ∉ P)
    (l : Fin K) (hl : l.val ≤ r) :
    localizedSourceCoefficient center Q K P l (τ := τ) =
      localizedSourceJet P (jointInitialJetSeparant center Q)
        ⟨l.val, by omega⟩ := by
  let s := jointInitialJetSeparant center Q
  let L := SourceAway P s
  let _ : P.IsPrime := hP
  have hs0 : Ideal.Quotient.mk P s ≠ 0 := by
    intro h
    exact hs (Ideal.Quotient.eq_zero_iff_mem.mp h)
  let _ : IsDomain L := Localization.Away.isDomain hs0
  let Frac := FractionRing L
  let emb : L →+* Frac := algebraMap L Frac
  let x : Option (Fin (r + 1)) → Frac
    | none => emb (localizedSourceChallenge P s)
    | some j => emb (localizedSourceJet P s j)
  let sourceHom : SourceRing r E →ₐ[E] Frac :=
    (IsScalarTower.toAlgHom E L Frac).comp
      ((IsScalarTower.toAlgHom E (SourceRing r E ⧸ P) L).comp
        (Ideal.Quotient.mkₐ E P))
  have hsourceHom : sourceHom = MvPolynomial.aeval x := by
    apply MvPolynomial.algHom_ext
    intro j
    cases j <;>
      simp only [sourceHom, x, localizedSourceChallenge, localizedSourceJet, emb,
        AlgHom.comp_apply, MvPolynomial.aeval_X, IsScalarTower.toAlgHom_apply] <;> rfl
  have heval (p : SourceRing r E) :
      emb (algebraMap (SourceRing r E ⧸ P) L (Ideal.Quotient.mk P p)) = aeval x p := by
    exact DFunLike.congr_fun hsourceHom p
  let φ : E[X] →ₐ[E] Frac := Polynomial.aeval (x none)
  have hflatten (p : MvPolynomial (Fin (r + 1)) E[X]) :
      aeval x ((MvPolynomial.optionEquivRight E (Fin (r + 1))).symm p) =
        aeval (fun j ↦ x (some j)) (MvPolynomial.map φ.toRingHom p) :=
    aeval_optionEquivRight_symm x p
  have hsepEval : aeval (fun j ↦ x (some j))
      (MvPolynomial.map φ.toRingHom
        (initialJetSeparant (Polynomial.C center : E[X]) Q)) =
        emb (algebraMap (SourceRing r E ⧸ P) L (Ideal.Quotient.mk P s)) :=
    (hflatten _).symm.trans (heval s).symm
  have hsepNe : aeval (fun j ↦ x (some j))
      (MvPolynomial.map φ.toRingHom
        (initialJetSeparant (Polynomial.C center : E[X]) Q)) ≠ 0 := by
    rw [hsepEval]
    exact ((IsLocalization.Away.algebraMap_isUnit (Ideal.Quotient.mk P s)).map emb).ne_zero
  have hrec := aeval_map_commonTaylorNumeratorOver_reconstruction_of_exponent φ
    (Polynomial.C center) Q K τ hτ (fun j ↦ x (some j)) hsepNe l
  have hnumEval : aeval (fun j ↦ x (some j))
      (MvPolynomial.map φ.toRingHom
        (commonTaylorNumeratorOver (F := E) (Polynomial.C center : E[X]) Q τ l.val)) =
        emb (algebraMap (SourceRing r E ⧸ P) L
          (Ideal.Quotient.mk P (jointCommonTaylorNumerator center Q τ l))) :=
    (hflatten _).symm.trans (heval _).symm
  have hcancel :
      emb (algebraMap (SourceRing r E ⧸ P) L (Ideal.Quotient.mk P s)) ^ τ *
          emb (IsLocalization.Away.invSelf (Ideal.Quotient.mk P s)) ^ τ = 1 := by
    rw [← mul_pow, ← map_mul, IsLocalization.Away.mul_invSelf, map_one, one_pow]
  have hjet := congrFun
    (polynomialJet_rationalTaylorPolynomial (φ (Polynomial.C center))
      (MvPolynomial.map φ.toRingHom Q) hK (fun j ↦ x (some j))) ⟨l.val, by omega⟩
  rw [polynomialJet, Polynomial.hasseJet_eq_taylor_coeff] at hjet
  apply IsFractionRing.injective L Frac
  rw [localizedSourceCoefficient, map_mul, map_pow, ← hnumEval, hrec, hsepEval, mul_right_comm,
    hcancel, one_mul]
  exact hjet

/-- Map the challenge and the first `k` reconstructed coefficients into a retained source
localization. -/
def sourceCoefficientMap (center : E) (Q : DifferentialPolynomial E[X] r)
    (K k : ℕ) (hkK : k ≤ K) (P : Ideal (SourceRing r E)) (τ : ℕ := 2 * K) :
    MvPolynomial (Option (Fin k)) E →ₐ[E]
      SourceAway P (jointInitialJetSeparant center Q) :=
  MvPolynomial.aeval fun
    | none => localizedSourceChallenge P (jointInitialJetSeparant center Q)
    | some l => localizedSourceCoefficient center Q K P (Fin.castLE hkK l) (τ := τ)

/-- The challenge and first `k` reconstructed coefficients generate every ordinary source
coordinate inside the retained localization.  Jet coordinates below `k` are reconstructed
coefficients; those at or above `k` vanish because the actual retained prime contains every high
numerator cut. -/
theorem sourceCoordinate_mem_range_sourceCoefficientMap_of_exponent
    (center : E) (Q : DifferentialPolynomial E[X] r) (K k τ : ℕ)
    (hτ : TaylorExponentSufficient r K τ) (hK : r < K) (hkK : k ≤ K)
    (P : Ideal (SourceRing r E)) (hP : P.IsPrime)
    (hs : jointInitialJetSeparant center Q ∉ P)
    (hhigh : ∀ l : Fin K, k ≤ l.val →
      jointCommonTaylorNumerator center Q τ l ∈ P)
    (p : SourceRing r E) :
    algebraMap (SourceRing r E ⧸ P)
      (SourceAway P (jointInitialJetSeparant center Q)) (Ideal.Quotient.mk P p) ∈
        Set.range (sourceCoefficientMap center Q K k hkK P (τ := τ)) := by
  refine algHom_mem_range_of_X_mem
    ((IsScalarTower.toAlgHom E (SourceRing r E ⧸ P) _).comp (Ideal.Quotient.mkₐ E P)) _
    (fun j ↦ ?_) p
  rcases j with _ | j
  · exact ⟨MvPolynomial.X none, MvPolynomial.aeval_X _ _⟩
  by_cases hjk : j.val < k
  · exact ⟨MvPolynomial.X (some ⟨j.val, hjk⟩), (MvPolynomial.aeval_X _ _).trans
      (localizedSourceCoefficient_eq_jet_of_exponent center Q K τ hτ hK P hP hs _
        (Nat.le_of_lt_succ j.isLt))⟩
  · refine ⟨0, Eq.symm ((localizedSourceCoefficient_eq_jet_of_exponent center Q K τ hτ hK P hP
      hs ⟨j.val, by omega⟩ (Nat.le_of_lt_succ j.isLt)).symm.trans ?_ |>.trans (map_zero _).symm)⟩
    rw [localizedSourceCoefficient, Ideal.Quotient.eq_zero_iff_mem.mpr
      (hhigh _ (Nat.le_of_not_gt hjk)), map_zero, zero_mul]

/-- A retained polynomial-valued symbolic agreement cut becomes the corresponding coefficient
evaluation equation under the source coefficient map. -/
theorem polynomialCoefficientEvaluation_mem_ker_sourceCoefficientMap_of_exponent
    (center : E) (Q : DifferentialPolynomial E[X] r) (K k τ : ℕ) (hkK : k ≤ K)
    (P : Ideal (SourceRing r E))
    (α : E) (received : E[X])
    (hcut : jointTaylorAgreementEquation center Q K τ (Polynomial.C α) received ∈ P)
    (hhigh : ∀ l : Fin K, k ≤ l.val →
      jointCommonTaylorNumerator center Q τ l ∈ P) :
    polynomialCoefficientEvaluation k (α - center) received ∈
      RingHom.ker (sourceCoefficientMap center Q K k hkK P (τ := τ)).toRingHom := by
  let _ : DistribMulAction (SourceRing r E ⧸ P) (SourceRing r E ⧸ P) := inferInstance
  let s := jointInitialJetSeparant center Q
  let L := SourceAway P s
  let src : SourceRing r E →ₐ[E] L :=
    (IsScalarTower.toAlgHom E (SourceRing r E ⧸ P) L).comp (Ideal.Quotient.mkₐ E P)
  have hcut0 : src (jointTaylorAgreementEquation center Q K τ (Polynomial.C α) received) = 0 := by
    change algebraMap (SourceRing r E ⧸ P) L
      (Ideal.Quotient.mk P
        (jointTaylorAgreementEquation center Q K τ (Polynomial.C α) received)) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hcut, map_zero]
  have hhigh0 (l : Fin K) (hl : k ≤ l.val) :
      src (jointCommonTaylorNumerator center Q τ l) = 0 := by
    change algebraMap (SourceRing r E ⧸ P) L
      (Ideal.Quotient.mk P (jointCommonTaylorNumerator center Q τ l)) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr (hhigh l hl), map_zero]
  have hcancel : src s ^ τ *
      IsLocalization.Away.invSelf (Ideal.Quotient.mk P s) ^ τ = 1 := by
    have hbase : src s * IsLocalization.Away.invSelf (Ideal.Quotient.mk P s) = 1 := by
      exact IsLocalization.Away.mul_invSelf (S := L) (Ideal.Quotient.mk P s)
    simpa only [mul_pow, one_pow] using congrArg (fun q : L ↦ q ^ τ) hbase
  let ψ : E[X] →ₐ[E] L := Polynomial.aeval (src (MvPolynomial.X none))
  have hsrcFlatten (p : MvPolynomial (Fin (r + 1)) E[X]) :
      src ((MvPolynomial.optionEquivRight E (Fin (r + 1))).symm p) =
        aeval (fun j ↦ src (MvPolynomial.X (some j))) (MvPolynomial.map ψ.toRingHom p) :=
    (DFunLike.congr_fun (MvPolynomial.aeval_unique src) _).trans
      (aeval_optionEquivRight_symm _ p)
  have hnum (l : Fin K) :
      aeval (fun j ↦ src (MvPolynomial.X (some j)))
        (MvPolynomial.map ψ.toRingHom
          (commonTaylorNumeratorOver (F := E) (Polynomial.C center) Q τ l.val)) =
        src (jointCommonTaylorNumerator center Q τ l) := by
    exact (hsrcFlatten
      (commonTaylorNumeratorOver (F := E) (Polynomial.C center) Q τ l.val)).symm
  have hsep :
      aeval (fun j ↦ src (MvPolynomial.X (some j)))
        (MvPolynomial.map ψ.toRingHom
          (initialJetSeparant (Polynomial.C center) Q)) = src s := by
    exact (hsrcFlatten (initialJetSeparant (Polynomial.C center) Q)).symm
  have hcutEq :
      (∑ l : Fin K, (algebraMap E L (α - center)) ^ l.val *
        src (jointCommonTaylorNumerator center Q τ l)) -
          ψ received * src s ^ τ = 0 := by
    rw [jointTaylorAgreementEquation, taylorAgreementEquationOver] at hcut0
    rw [hsrcFlatten] at hcut0
    simp only [map_sub, map_sum, map_mul, map_pow, MvPolynomial.map_C] at hcut0
    simp only [MvPolynomial.aeval_C] at hcut0
    simp_rw [hnum] at hcut0
    rw [hsep] at hcut0
    change (∑ l : Fin K, (ψ (Polynomial.C α) - ψ (Polynomial.C center)) ^ l.val *
        src (jointCommonTaylorNumerator center Q τ l)) -
      ψ received * src s ^ τ = 0 at hcut0
    have hx : ψ (Polynomial.C α) - ψ (Polynomial.C center) =
        algebraMap E L (α - center) := by
      simp [ψ]
    rw [hx] at hcut0
    exact hcut0
  have hlocalized :
      (∑ l : Fin k, (algebraMap E L (α - center)) ^ l.val *
        localizedSourceCoefficient center Q K P (Fin.castLE hkK l) (τ := τ)) =
          received.eval₂ (algebraMap E L) (localizedSourceChallenge P s) :=
    sum_castLE_mul_pow_eq_of_cleared hkK _ (ψ received) _ _
      (fun l : Fin K ↦ src (jointCommonTaylorNumerator center Q τ l)) hcutEq hhigh0 hcancel
  let Φ := sourceCoefficientMap center Q K k hkK P (τ := τ)
  change Φ (polynomialCoefficientEvaluation k (α - center) received) = 0
  have hC (a : E) : Φ (MvPolynomial.C a) =
      algebraMap E (SourceAway P (jointInitialJetSeparant center Q)) a := by
    simp [Φ, sourceCoefficientMap]
  have hX (j : Option (Fin k)) : Φ (MvPolynomial.X j) =
      match j with
      | none => localizedSourceChallenge P (jointInitialJetSeparant center Q)
      | some l => localizedSourceCoefficient center Q K P (Fin.castLE hkK l) (τ := τ) := by
    simp [Φ, sourceCoefficientMap]
  rw [polynomialCoefficientEvaluation, map_sub]
  have hreceived :=
    Polynomial.hom_eval₂ received MvPolynomial.C Φ.toRingHom (MvPolynomial.X none)
  change Φ (received.eval₂ MvPolynomial.C (MvPolynomial.X none)) =
    received.eval₂ (Φ.toRingHom.comp MvPolynomial.C) (Φ (MvPolynomial.X none)) at hreceived
  rw [hreceived]
  have hmap : Φ.toRingHom.comp MvPolynomial.C =
      algebraMap E (SourceAway P (jointInitialJetSeparant center Q)) := by
    ext a
    exact hC a
  rw [hmap]
  simp only [map_sum, map_mul, hC, hX]
  simp_rw [map_pow]
  exact sub_eq_zero.mpr hlocalized

/-- A retained source prime containing `c` agreement cuts at distinct evaluation points has
dimension at most `k + 1 - c`.

The proof first passes to the kernel of the coefficient map before localization.  Vandermonde
elimination bounds that ordinary coefficient quotient by `k + 1 - c`.  It then pulls the source
separant back through the coefficient map and localizes both quotients there; the resulting map
onto the actual retained source localization is surjective. -/
theorem
    symbolicSource_prime_affineHilbertPolynomial_natDegree_le_of_polynomial_agreements_of_exponent
    (center : E) (Q : DifferentialPolynomial E[X] r) (K k c τ : ℕ)
    (hτ : TaylorExponentSufficient r K τ)
    (hK : r < K) (hkK : k ≤ K) (hck : c ≤ k)
    (P : Ideal (SourceRing r E)) (hP : P.IsPrime)
    (hs : jointInitialJetSeparant center Q ∉ P)
    (hhigh : ∀ l : Fin K, k ≤ l.val →
      jointCommonTaylorNumerator center Q τ l ∈ P)
    (α : Fin c ↪ E) (received : Fin c → E[X])
    (hcut : ∀ i,
      jointTaylorAgreementEquation center Q K τ (Polynomial.C (α i)) (received i) ∈ P) :
    (affineHilbertPolynomial P).natDegree ≤ k + 1 - c := by
  classical
  let s := jointInitialJetSeparant center Q
  let _ : P.IsPrime := hP
  have hs0 : Ideal.Quotient.mk P s ≠ 0 := by
    intro h
    exact hs (Ideal.Quotient.eq_zero_iff_mem.mp h)
  let Φ := sourceCoefficientMap center Q K k hkK P (τ := τ)
  let J : Ideal (MvPolynomial (Option (Fin k)) E) := RingHom.ker Φ.toRingHom
  let β : Fin c ↪ E :=
    ⟨fun i ↦ α i - center, fun i j hij ↦ α.injective (sub_left_injective hij)⟩
  have heval (i : Fin c) :
      polynomialCoefficientEvaluation k (β i) (received i) ∈ J := by
    exact polynomialCoefficientEvaluation_mem_ker_sourceCoefficientMap_of_exponent
      center Q K k τ hkK P (α i) (received i) (hcut i) hhigh
  have hJdim : (affineHilbertPolynomial J).natDegree ≤ k + 1 - c :=
    natDegree_affineHilbertPolynomial_le_of_polynomialCoefficientEvaluation_mem
      hck β received heval
  have hregular : IsLeftRegular (Ideal.Quotient.mk P s) := by
    rw [isLeftRegular_iff_isRegular]
    exact isRegular_iff_ne_zero.mpr hs0
  exact natDegree_affineHilbertPolynomial_le_of_away_range P s hregular Φ
    (sourceCoordinate_mem_range_sourceCoefficientMap_of_exponent
      center Q K k τ hτ hK hkK P hP hs hhigh) hJdim


/-- Hereditary joint coefficient-space budget for every actual retained source prime.
In dimensions at least two, all identically vanishing agreement cuts can be used in the
Vandermonde quotient.  If there were more than `k`, any chosen `k` of them would already force
dimension at most one. -/
theorem symbolicSourcePolynomial_dimensionSensitive_component_of_exponent
    (center : E) (Q : DifferentialPolynomial E[X] r) (K k n τ : ℕ)
    (hτ : TaylorExponentSufficient r K τ) (hK : r < K) (hkK : k ≤ K)
    (P : Ideal (SourceRing r E)) (hP : P.IsPrime)
    (hs : jointInitialJetSeparant center Q ∉ P)
    (hhigh : ∀ l : Fin K, k ≤ l.val → jointCommonTaylorNumerator center Q τ l ∈ P)
    (α : Fin n ↪ E) (received : Fin n → E[X]) :
    let cuts : Fin n → MvPolynomial (Option (Fin (r + 1))) E := fun i ↦
      jointTaylorAgreementEquation center Q K τ (Polynomial.C (α i)) (received i)
    (affineHilbertPolynomial P).natDegree ≤ k + 1 ∧
      (1 < (affineHilbertPolynomial P).natDegree →
        {i | cuts i ∈ P}.ncard ≤ k + 1 - (affineHilbertPolynomial P).natDegree) := by
  classical
  dsimp only
  let cuts : Fin n → MvPolynomial (Option (Fin (r + 1))) E := fun i ↦
    jointTaylorAgreementEquation center Q K τ (Polynomial.C (α i)) (received i)
  let s := jointInitialJetSeparant center Q
  let Φ := sourceCoefficientMap center Q K k hkK P (τ := τ)
  let J : Ideal (MvPolynomial (Option (Fin k)) E) := RingHom.ker Φ.toRingHom
  have hregular : IsLeftRegular (Ideal.Quotient.mk P s) := by
    rw [isLeftRegular_iff_isRegular]
    apply isRegular_iff_ne_zero.mpr
    intro hz
    exact hs (Ideal.Quotient.eq_zero_iff_mem.mp hz)
  have hdegree : (affineHilbertPolynomial P).natDegree ≤
      (affineHilbertPolynomial J).natDegree :=
    natDegree_affineHilbertPolynomial_le_of_away_range P s hregular Φ
      (sourceCoordinate_mem_range_sourceCoefficientMap_of_exponent
        center Q K k τ hτ hK hkK P hP hs hhigh) le_rfl
  let α0 : Fin 0 ↪ E := ⟨Fin.elim0, fun i ↦ Fin.elim0 i⟩
  have hdim : (affineHilbertPolynomial P).natDegree ≤ k + 1 := by
    have h :=
      symbolicSource_prime_affineHilbertPolynomial_natDegree_le_of_polynomial_agreements_of_exponent
        center Q K k 0 τ hτ hK hkK (by omega) P hP hs hhigh α0 (fun _ ↦ 0)
        (fun i ↦ Fin.elim0 i)
    simpa using h
  refine ⟨hdim, fun hd ↦ ?_⟩
  have hJdim : 1 < (affineHilbertPolynomial J).natDegree := by omega
  let β : Fin n ↪ E :=
    ⟨fun i ↦ α i - center, fun i j hij ↦ α.injective (sub_left_injective hij)⟩
  have hJbound := natDegree_affineHilbertPolynomial_add_ncard_le_of_polynomialCoefficientEvaluation
    β (fun i ↦ received i) {i | cuts i ∈ P}
    (fun i hi ↦ polynomialCoefficientEvaluation_mem_ker_sourceCoefficientMap_of_exponent
      center Q K k τ hkK P (α i) (received i) hi hhigh) hJdim
  have hJbound' : (affineHilbertPolynomial J).natDegree +
      {i | cuts i ∈ P}.ncard ≤ k + 1 := by
    simpa only [cuts] using hJbound
  have hbound : (affineHilbertPolynomial P).natDegree + {i | cuts i ∈ P}.ncard ≤ k + 1 :=
    (Nat.add_le_add_right hdegree _).trans hJbound'
  exact (Nat.le_sub_iff_add_le hdim).2 (by simpa [Nat.add_comm] using hbound)


/-- Affine received-line specialization of the arbitrary-polynomial hereditary component
bound. -/
theorem symbolicSource_dimensionSensitive_component_of_exponent
    (center : E) (Q : DifferentialPolynomial E[X] r) (K k n τ : ℕ)
    (hτ : TaylorExponentSufficient r K τ) (hK : r < K) (hkK : k ≤ K)
    (P : Ideal (SourceRing r E)) (hP : P.IsPrime)
    (hs : jointInitialJetSeparant center Q ∉ P)
    (hhigh : ∀ l : Fin K, k ≤ l.val →
      jointCommonTaylorNumerator center Q τ l ∈ P)
    (α : Fin n ↪ E) (f g : Fin n → E) :
    let cuts : Fin n → MvPolynomial (Option (Fin (r + 1))) E := fun i ↦
      jointTaylorAgreementEquation center Q K τ (Polynomial.C (α i))
        (Polynomial.C (f i) + Polynomial.X * Polynomial.C (g i))
    (affineHilbertPolynomial P).natDegree ≤ k + 1 ∧
    (1 < (affineHilbertPolynomial P).natDegree →
      {i | cuts i ∈ P}.ncard ≤ k + 1 - (affineHilbertPolynomial P).natDegree) := by
  exact symbolicSourcePolynomial_dimensionSensitive_component_of_exponent
    center Q K k n τ hτ hK hkK P hP hs hhigh α
    (fun i ↦ Polynomial.C (f i) + Polynomial.X * Polynomial.C (g i))

/-- Order-one, degree-one-message specialization.  This explicit caller checks the boundary
`r = k = 1`: every two-dimensional retained source prime contains no agreement cut identically,
while all positive-dimensional retained primes have dimension at most two. -/
theorem firstOrder_symbolicSource_dimensionSensitive_component_of_exponent
    (center : E) (Q : DifferentialPolynomial E[X] 1) (K n τ : ℕ)
    (hτ : TaylorExponentSufficient 1 K τ) (hK : 1 < K)
    (P : Ideal (SourceRing 1 E)) (hP : P.IsPrime)
    (hs : jointInitialJetSeparant center Q ∉ P)
    (hhigh : ∀ l : Fin K, 1 ≤ l.val →
      jointCommonTaylorNumerator center Q τ l ∈ P)
    (α : Fin n ↪ E) (f g : Fin n → E) :
    let cuts : Fin n → MvPolynomial (Option (Fin 2)) E := fun i ↦
      jointTaylorAgreementEquation center Q K τ (Polynomial.C (α i))
        (Polynomial.C (f i) + Polynomial.X * Polynomial.C (g i))
    (affineHilbertPolynomial P).natDegree ≤ 2 ∧
      (1 < (affineHilbertPolynomial P).natDegree → {i | cuts i ∈ P}.ncard = 0) := by
  dsimp only
  have h := symbolicSource_dimensionSensitive_component_of_exponent center Q K 1 n τ hτ hK
    (by omega) P hP hs hhigh α f g
  rcases h with ⟨hdim, hcuts⟩
  refine ⟨by simpa using hdim, fun hd ↦ ?_⟩
  have hbound := hcuts hd
  have hdimEq : (affineHilbertPolynomial P).natDegree = 2 := by omega
  rw [hdimEq] at hbound
  have hzero :
      {i | jointTaylorAgreementEquation center Q K τ (Polynomial.C (α i))
        (Polynomial.C (f i) + Polynomial.X * Polynomial.C (g i)) ∈ P}.ncard ≤ 0 := by
    simpa [hdimEq] using hbound
  exact Nat.eq_zero_of_le_zero hzero

/-- The high-agreement part of one retained source component, outside the terminal graph locus,
is finite and has the hybrid joint incidence bound.  The first factor uses the graph-recognition
threshold `L`; when the component has dimension two, the second factor is the direct
coefficient-space ratio at threshold `k`. -/
theorem finite_symbolicSource_agreementLocus_off_excluded_and_ncard_le_hybrid_of_exponent
    [IsAlgClosed E]
    (center : E) (Q : DifferentialPolynomial E[X] r) (K k n τ L A b : ℕ)
    (hτ : TaylorExponentSufficient r K τ) (hK : r < K) (hkK : k ≤ K)
    (hLA : L ≤ A) (hkA : k ≤ A)
    (P : Ideal (SourceRing r E)) (hP : P.IsPrime)
    (hhigh : ∀ l : Fin K, k ≤ l.val →
      jointCommonTaylorNumerator center Q τ l ∈ P)
    (α : Fin n ↪ E) (f g : Fin n → E)
    (hdeg : ∀ i, (jointTaylorAgreementEquation center Q K τ (Polynomial.C (α i))
      (Polynomial.C (f i) + Polynomial.X * Polynomial.C (g i))).totalDegree ≤ b)
    (excluded : Set (Option (Fin (r + 1)) → E))
    (hterminal : ∀ J : Ideal (SourceRing r E),
      P ≤ J → J.IsPrime → jointInitialJetSeparant center Q ∉ J →
      0 < (affineHilbertPolynomial J).natDegree →
      L ≤ {i | jointTaylorAgreementEquation center Q K τ (Polynomial.C (α i))
        (Polynomial.C (f i) + Polynomial.X * Polynomial.C (g i)) ∈ J}.ncard →
      {x | x ∈ zeroLocus E J ∧ aeval x (jointInitialJetSeparant center Q) ≠ 0} ⊆ excluded) :
    let cuts : Fin n → MvPolynomial (Option (Fin (r + 1))) E := fun i ↦
      jointTaylorAgreementEquation center Q K τ (Polynomial.C (α i))
        (Polynomial.C (f i) + Polynomial.X * Polynomial.C (g i))
    let T := {x : Option (Fin (r + 1)) → E |
      x ∈ zeroLocus E P ∧ aeval x (jointInitialJetSeparant center Q) ≠ 0 ∧
        x ∉ excluded ∧ A ≤ {i | aeval x (cuts i) = 0}.ncard}
    T.Finite ∧ (T.ncard : ℚ) ≤ affineDegree P *
      hybridDimensionSensitiveIncidenceProduct n A L k b
        (affineHilbertPolynomial P).natDegree := by
  classical
  dsimp only
  let cuts : Fin n → MvPolynomial (Option (Fin (r + 1))) E := fun i ↦
    jointTaylorAgreementEquation center Q K τ (Polynomial.C (α i))
      (Polynomial.C (f i) + Polynomial.X * Polynomial.C (g i))
  let s := jointInitialJetSeparant center Q
  have : P.IsPrime := hP
  have hdimension (J : Ideal (SourceRing r E)) (hPJ : P ≤ J) (hJ : J.IsPrime)
      (hsJ : s ∉ J) (hdJ : 1 < (affineHilbertPolynomial J).natDegree) :
      (affineHilbertPolynomial J).natDegree + {i | cuts i ∈ J}.ncard ≤ k + 1 := by
    obtain ⟨_, hcuts⟩ := symbolicSource_dimensionSensitive_component_of_exponent
      center Q K k n τ hτ hK hkK J hJ hsJ
        (fun l hl ↦ hPJ (hhigh l hl)) α f g
    have hcount := hcuts hdJ
    have hcount' : {i | cuts i ∈ J}.ncard ≤
        k + 1 - (affineHilbertPolynomial J).natDegree := by
      simpa only [cuts] using hcount
    omega
  have hterminal' (J : Ideal (SourceRing r E)) (hPJ : P ≤ J) (hJ : J.IsPrime)
      (hsJ : s ∉ J) (hdJ : 0 < (affineHilbertPolynomial J).natDegree)
      (hcuts : L ≤ {i | cuts i ∈ J}.ncard) :
      {x | x ∈ zeroLocus E J ∧ aeval x s ≠ 0} ⊆ excluded := by
    exact hterminal J hPJ hJ hsJ hdJ hcuts
  simpa only [Fintype.card_fin, cuts, s] using
    (finite_and_ncard_le_hybridDimensionSensitiveIncidenceProduct_of_agreement_off_excluded
      (K := E) (P := P) s cuts hdeg hLA hkA excluded hdimension hterminal')


end ReedSolomon

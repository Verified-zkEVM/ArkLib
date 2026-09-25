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

/-- In a domain `L`, if `u` inverts the evaluated initial separant, then the common numerators
cleared by `u ^ τ` recover the jets below the differential order. -/
private theorem aeval_map_commonTaylorNumeratorOver_mul_pow_eq_jet {A L : Type*} [CommRing A]
    [Algebra E A] [CommRing L] [IsDomain L] [Algebra E L] (φ : A →ₐ[E] L) (center : A)
    (Q : DifferentialPolynomial A r) (K τ : ℕ) (hτ : TaylorExponentSufficient r K τ)
    (hK : r < K) (y : Fin (r + 1) → L) (u : L)
    (hu : aeval y (MvPolynomial.map φ.toRingHom (initialJetSeparant center Q)) * u = 1)
    (l : Fin K) (hl : l.val ≤ r) :
    aeval y (MvPolynomial.map φ.toRingHom (commonTaylorNumeratorOver (F := E) center Q τ l.val)) *
      u ^ τ = y ⟨l.val, by omega⟩ := by
  let Frac := FractionRing L
  let ψ : A →ₐ[E] Frac := (IsScalarTower.toAlgHom E L Frac).comp φ
  let x : Fin (r + 1) → Frac := fun j ↦ algebraMap L Frac (y j)
  have hmap (p : MvPolynomial (Fin (r + 1)) A) :
      algebraMap L Frac (aeval y (MvPolynomial.map φ.toRingHom p)) =
        aeval x (MvPolynomial.map ψ.toRingHom p) := by
    induction p using MvPolynomial.induction_on with
    | C a => simp [ψ]
    | add p q hp hq => simp only [map_add, hp, hq]
    | mul_X p j hp => simp only [map_mul, hp, MvPolynomial.map_X, MvPolynomial.aeval_X, x]
  have hsep : aeval x (MvPolynomial.map ψ.toRingHom (initialJetSeparant center Q)) *
      algebraMap L Frac u = 1 := by
    rw [← hmap, ← map_mul, hu, map_one]
  have hrec := aeval_map_commonTaylorNumeratorOver_reconstruction_of_exponent ψ center Q K τ
    hτ x (left_ne_zero_of_mul_eq_one hsep) l
  have hjet := congrFun (polynomialJet_rationalTaylorPolynomial (ψ center)
    (MvPolynomial.map ψ.toRingHom Q) hK x) ⟨l.val, by omega⟩
  rw [polynomialJet, Polynomial.hasseJet_eq_taylor_coeff] at hjet
  apply IsFractionRing.injective L Frac
  rw [map_mul, map_pow, hmap, hrec, hjet, mul_right_comm, ← mul_pow, hsep, one_pow, one_mul]

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
  let _ : P.IsPrime := hP
  let _ : IsDomain (ChartAway P s) :=
    Localization.Away.isDomain fun hz ↦ hs (Ideal.Quotient.eq_zero_iff_mem.mp hz)
  let g : ChartRing r E →ₐ[E] ChartAway P s :=
    (IsScalarTower.toAlgHom E (ChartRing r E ⧸ P) _).comp (Ideal.Quotient.mkₐ E P)
  have hg (p : ChartRing r E) :
      aeval (fun j ↦ g (MvPolynomial.X j))
        (MvPolynomial.map (Algebra.ofId E (ChartAway P s)).toRingHom p) = g p :=
    (MvPolynomial.aeval_map_algebraMap _ _ p).trans
      (DFunLike.congr_fun (MvPolynomial.aeval_unique g) p).symm
  have key := aeval_map_commonTaylorNumeratorOver_mul_pow_eq_jet (Algebra.ofId E _) center Q K τ
    hτ hK _ (IsLocalization.Away.invSelf (Ideal.Quotient.mk P s))
    (by rw [hg]; exact IsLocalization.Away.mul_invSelf (Ideal.Quotient.mk P s)) l hl
  rw [hg, commonTaylorNumeratorOver_self] at key
  exact key

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

/-- An algebra map that kills a Taylor agreement cut and every high numerator, and whose separant
image has inverse `u`, kills the fixed coefficient evaluation at the cleared low numerators. -/
private theorem aeval_fixedCoefficientEvaluation_eq_zero {L : Type*} [CommRing L] [Algebra E L]
    (g : ChartRing r E →ₐ[E] L) (u : L) (center : E) (Q : DifferentialPolynomial E r)
    (K k τ : ℕ) (hkK : k ≤ K) (α y : E) (v : Fin k → L)
    (hv : ∀ l, v l = g (commonTaylorNumerator center Q τ (Fin.castLE hkK l).val) * u ^ τ)
    (hcut : g (taylorAgreementEquation center Q K α y (τ := τ)) = 0)
    (hhigh : ∀ l : Fin K, k ≤ l.val → g (commonTaylorNumerator center Q τ l.val) = 0)
    (hu : g (initialJetSeparant center Q) * u = 1) :
    aeval v (fixedCoefficientEvaluation k (α - center) y) = 0 := by
  have hcutEq :
      (∑ l : Fin K, (algebraMap E L (α - center)) ^ l.val *
        g (commonTaylorNumerator center Q τ l.val)) -
          algebraMap E L y * g (initialJetSeparant center Q) ^ τ = 0 := by
    simpa only [taylorAgreementEquation, map_sub, map_sum, map_mul, map_pow,
      MvPolynomial.algHom_C] using hcut
  have hlocalized := sum_castLE_mul_pow_eq_of_cleared hkK _ _ _ u
    (fun l : Fin K ↦ g (commonTaylorNumerator center Q τ l.val)) hcutEq hhigh
    (by rw [← mul_pow, hu, one_pow])
  rw [fixedCoefficientEvaluation, map_sub, map_sum]
  simp only [map_mul, map_pow, MvPolynomial.aeval_C, MvPolynomial.aeval_X, hv]
  exact sub_eq_zero.mpr hlocalized

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
  let s := initialJetSeparant center Q
  let g : ChartRing r E →ₐ[E] ChartAway P s :=
    (IsScalarTower.toAlgHom E (ChartRing r E ⧸ P) _).comp (Ideal.Quotient.mkₐ E P)
  have hg (p : ChartRing r E) (hp : p ∈ P) : g p = 0 :=
    show algebraMap (ChartRing r E ⧸ P) (ChartAway P s) (Ideal.Quotient.mk P p) = 0 by
      rw [Ideal.Quotient.eq_zero_iff_mem.mpr hp, map_zero]
  change chartCoefficientMap center Q K k hkK P (τ := τ)
    (fixedCoefficientEvaluation k (α - center) y) = 0
  exact aeval_fixedCoefficientEvaluation_eq_zero g
    (IsLocalization.Away.invSelf (Ideal.Quotient.mk P s)) center Q K k τ hkK α y _
    (fun _ ↦ rfl) (hg _ hcut) (fun l hl ↦ hg _ (hhigh l hl))
    (IsLocalization.Away.mul_invSelf (S := ChartAway P s) (Ideal.Quotient.mk P s))

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
  let _ : P.IsPrime := hP
  let _ : IsDomain (SourceAway P s) :=
    Localization.Away.isDomain fun hz ↦ hs (Ideal.Quotient.eq_zero_iff_mem.mp hz)
  let g : SourceRing r E →ₐ[E] SourceAway P s :=
    (IsScalarTower.toAlgHom E (SourceRing r E ⧸ P) _).comp (Ideal.Quotient.mkₐ E P)
  have hflat (p : MvPolynomial (Fin (r + 1)) E[X]) :
      aeval (fun j ↦ g (MvPolynomial.X (some j)))
        (MvPolynomial.map (Polynomial.aeval (g (MvPolynomial.X none))).toRingHom p) =
        g ((MvPolynomial.optionEquivRight E (Fin (r + 1))).symm p) :=
    ((DFunLike.congr_fun (MvPolynomial.aeval_unique g) _).trans
      (aeval_optionEquivRight_symm _ p)).symm
  have key := aeval_map_commonTaylorNumeratorOver_mul_pow_eq_jet
    (Polynomial.aeval (g (MvPolynomial.X none))) (Polynomial.C center) Q K τ hτ hK _
    (IsLocalization.Away.invSelf (Ideal.Quotient.mk P s))
    (by rw [hflat]; exact IsLocalization.Away.mul_invSelf (Ideal.Quotient.mk P s)) l hl
  rw [hflat] at key
  exact key

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

/-- An algebra map that kills a polynomial-valued agreement cut and every high numerator, and
whose separant image has inverse `u`, kills the polynomial coefficient evaluation at the challenge
image and the cleared low numerators. -/
private theorem aeval_polynomialCoefficientEvaluation_eq_zero {L : Type*} [CommRing L]
    [Algebra E L] (g : SourceRing r E →ₐ[E] L) (u : L) (center : E)
    (Q : DifferentialPolynomial E[X] r) (K k τ : ℕ) (hkK : k ≤ K) (α : E) (received : E[X])
    (v : Option (Fin k) → L) (hvnone : v none = g (MvPolynomial.X none))
    (hvsome : ∀ l, v (some l) =
      g (jointCommonTaylorNumerator center Q τ (Fin.castLE hkK l)) * u ^ τ)
    (hcut : g (jointTaylorAgreementEquation center Q K τ (Polynomial.C α) received) = 0)
    (hhigh : ∀ l : Fin K, k ≤ l.val → g (jointCommonTaylorNumerator center Q τ l) = 0)
    (hu : g (jointInitialJetSeparant center Q) * u = 1) :
    aeval v (polynomialCoefficientEvaluation k (α - center) received) = 0 := by
  let s := jointInitialJetSeparant center Q
  let ψ : E[X] →ₐ[E] L := Polynomial.aeval (g (MvPolynomial.X none))
  have hflat (p : MvPolynomial (Fin (r + 1)) E[X]) :
      g ((MvPolynomial.optionEquivRight E (Fin (r + 1))).symm p) =
        aeval (fun j ↦ g (MvPolynomial.X (some j))) (MvPolynomial.map ψ.toRingHom p) :=
    (DFunLike.congr_fun (MvPolynomial.aeval_unique g) _).trans
      (aeval_optionEquivRight_symm _ p)
  have hnum (l : Fin K) :
      aeval (fun j ↦ g (MvPolynomial.X (some j)))
        (MvPolynomial.map ψ.toRingHom
          (commonTaylorNumeratorOver (F := E) (Polynomial.C center) Q τ l.val)) =
        g (jointCommonTaylorNumerator center Q τ l) :=
    (hflat _).symm
  have hsep :
      aeval (fun j ↦ g (MvPolynomial.X (some j)))
        (MvPolynomial.map ψ.toRingHom
          (initialJetSeparant (Polynomial.C center) Q)) = g s :=
    (hflat _).symm
  have hcutEq :
      (∑ l : Fin K, (algebraMap E L (α - center)) ^ l.val *
        g (jointCommonTaylorNumerator center Q τ l)) -
          ψ received * g s ^ τ = 0 := by
    rw [jointTaylorAgreementEquation, taylorAgreementEquationOver, hflat] at hcut
    simp only [map_sub, map_sum, map_mul, map_pow, MvPolynomial.map_C] at hcut
    simp only [MvPolynomial.aeval_C] at hcut
    simp_rw [hnum] at hcut
    rw [hsep] at hcut
    change (∑ l : Fin K, (ψ (Polynomial.C α) - ψ (Polynomial.C center)) ^ l.val *
        g (jointCommonTaylorNumerator center Q τ l)) -
      ψ received * g s ^ τ = 0 at hcut
    have hx : ψ (Polynomial.C α) - ψ (Polynomial.C center) =
        algebraMap E L (α - center) := by
      simp [ψ]
    rw [hx] at hcut
    exact hcut
  have hlocalized := sum_castLE_mul_pow_eq_of_cleared hkK _ (ψ received) _ u
    (fun l : Fin K ↦ g (jointCommonTaylorNumerator center Q τ l)) hcutEq hhigh
    (by rw [← mul_pow, hu, one_pow])
  have hreceived : aeval v (received.eval₂ MvPolynomial.C (MvPolynomial.X none)) = ψ received := by
    rw [← MvPolynomial.algebraMap_eq, ← Polynomial.aeval_def, ← Polynomial.aeval_algHom_apply,
      MvPolynomial.aeval_X, hvnone]
  rw [polynomialCoefficientEvaluation, map_sub, hreceived, map_sum]
  simp only [map_mul, map_pow, MvPolynomial.aeval_C, MvPolynomial.aeval_X, hvsome]
  exact sub_eq_zero.mpr hlocalized

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
  let s := jointInitialJetSeparant center Q
  let g : SourceRing r E →ₐ[E] SourceAway P s :=
    (IsScalarTower.toAlgHom E (SourceRing r E ⧸ P) _).comp (Ideal.Quotient.mkₐ E P)
  have hg (p : SourceRing r E) (hp : p ∈ P) : g p = 0 :=
    show algebraMap (SourceRing r E ⧸ P) (SourceAway P s) (Ideal.Quotient.mk P p) = 0 by
      rw [Ideal.Quotient.eq_zero_iff_mem.mpr hp, map_zero]
  change sourceCoefficientMap center Q K k hkK P (τ := τ)
    (polynomialCoefficientEvaluation k (α - center) received) = 0
  exact aeval_polynomialCoefficientEvaluation_eq_zero g
    (IsLocalization.Away.invSelf (Ideal.Quotient.mk P s)) center Q K k τ hkK α received _ rfl
    (fun _ ↦ rfl) (hg _ hcut) (fun l hl ↦ hg _ (hhigh l hl))
    (IsLocalization.Away.mul_invSelf (S := SourceAway P s) (Ideal.Quotient.mk P s))

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

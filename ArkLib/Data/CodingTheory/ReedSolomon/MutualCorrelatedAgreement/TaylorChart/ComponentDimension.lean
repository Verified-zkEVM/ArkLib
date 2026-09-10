/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.TaylorChart.ComponentAgreement
public import
  ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.Symbolic.TaylorWitnessEmbedding
public import ArkLib.ToMathlib.AlgebraicGeometry.Incidence.Agreement
public import ArkLib.ToMathlib.AlgebraicGeometry.Incidence.DimensionSensitive
public import ArkLib.ToMathlib.AlgebraicGeometry.Incidence.EvaluationDimension
public import ArkLib.ToMathlib.AlgebraicGeometry.PrincipalCut.Polynomial
public import Mathlib.RingTheory.Localization.FractionRing
/-!
# Dimensions of retained Taylor-chart components

The dimension-sensitive incidence induction needs a hereditary statement about every retained
source prime, after the initial equation, the nonlinear high-coefficient cuts, and any earlier
agreement cuts have been imposed.  This module proves that statement on the actual source locus.

On the separant principal open, the challenge and first `k` reconstructed coefficients generate
the source localization.  Reconstructed coefficients below the differential order recover the
source jets; jets at indices at least `k` vanish by the retained high cuts.  For `c` distinct
agreement cuts, their images lie in the kernel of the polynomial-valued coefficient-evaluation
map.  A
Vandermonde argument first bounds the ordinary coefficient quotient by `k + 1 - c`; localizing
both quotients at the pulled-back separant then gives the same bound for the retained source
prime in the correct direction.  The construction keeps a common sufficient Taylor exponent
`τ` throughout and includes the boundary `r = k = 1`.

The resulting hereditary bound feeds a hybrid incidence induction: dimensions at least two use
the coefficient-space threshold, while dimension one uses the existing excluded-graph threshold.
The older fixed-threshold first-order theorem remains as a compatibility result.
-/

@[expose] public section

open PolynomialDifferential

noncomputable section

namespace ReedSolomon

open Polynomial MvPolynomial HiddenDerivative AffineHilbert

variable {F E : Type*} [Field F] [Field E] {n k K r : ℕ}

abbrev ChartRing (r : ℕ) (E : Type*) [Field E] :=
  MvPolynomial (Fin (r + 1)) E

abbrev ChartAway {r : ℕ} {E : Type*} [Field E]
    (P : Ideal (ChartRing r E)) (s : ChartRing r E) :=
  Localization.Away (Ideal.Quotient.mk P s)

private theorem commonTaylorNumeratorOver_self (center : E)
    (Q : DifferentialPolynomial E r) (K : ℕ) (l : Fin K) (τ : ℕ) :
    commonTaylorNumeratorOver (F := E) center Q K l (τ := τ) =
      commonTaylorNumerator center Q K l (τ := τ) := by
  have h := map_commonTaylorNumeratorOver_eq (AlgHom.id E E) center Q K l τ
  have hid : (AlgHom.id E E).toRingHom = RingHom.id E := rfl
  rw [hid, MvPolynomial.map_id, MvPolynomial.map_id] at h
  exact h

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
      (Ideal.Quotient.mk P (commonTaylorNumerator center Q K l (τ := τ))) *
    IsLocalization.Away.invSelf (Ideal.Quotient.mk P (initialJetSeparant center Q)) ^ τ

set_option maxHeartbeats 800000 in
-- The fraction-field comparison expands a symbolic Taylor reconstruction identity.
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
      (MvPolynomial.map φ.toRingHom (initialJetSeparantOver center Q)) =
      emb (algebraMap (ChartRing r E ⧸ P) L (Ideal.Quotient.mk P s)) := by
    change aeval x (MvPolynomial.map (algebraMap E Frac)
      (initialJetSeparant center Q)) = _
    rw [MvPolynomial.aeval_map_algebraMap]
    exact (heval s).symm
  have hsepNe : aeval x
      (MvPolynomial.map φ.toRingHom (initialJetSeparantOver center Q)) ≠ 0 := by
    rw [hsepEval]
    intro hz
    have hone := IsLocalization.Away.mul_invSelf (S := L) (Ideal.Quotient.mk P s)
    have hz' : algebraMap (ChartRing r E ⧸ P) L (Ideal.Quotient.mk P s) = 0 := by
      apply IsFractionRing.injective L Frac
      simpa only [map_zero] using hz
    rw [hz', zero_mul] at hone
    exact zero_ne_one hone
  have hrec := aeval_map_commonTaylorNumeratorOver_reconstruction_of_exponent φ center Q
    K τ hτ x hsepNe l
  have hnumEval : aeval x (MvPolynomial.map φ.toRingHom
      (commonTaylorNumeratorOver (F := E) center Q K l (τ := τ))) =
      emb (algebraMap (ChartRing r E ⧸ P) L
        (Ideal.Quotient.mk P (commonTaylorNumerator center Q K l (τ := τ)))) := by
    change aeval x (MvPolynomial.map (algebraMap E Frac)
      (commonTaylorNumeratorOver (F := E) center Q K l (τ := τ))) = _
    rw [MvPolynomial.aeval_map_algebraMap]
    rw [commonTaylorNumeratorOver_self]
    exact (heval (commonTaylorNumerator center Q K l (τ := τ))).symm
  apply IsFractionRing.injective L Frac
  simp only [localizedChartCoefficient, localizedChartJet, map_mul, map_pow]
  rw [heval (commonTaylorNumerator center Q K l (τ := τ)),
    heval (MvPolynomial.X ⟨l.val, by omega⟩)]
  rw [← heval (commonTaylorNumerator center Q K l (τ := τ)),
    ← hnumEval, hrec, hsepEval]
  have hcancel :
      emb (algebraMap (ChartRing r E ⧸ P) L (Ideal.Quotient.mk P s)) ^ τ *
          emb (IsLocalization.Away.invSelf (Ideal.Quotient.mk P s)) ^ τ = 1 := by
    have hbase : emb (algebraMap (ChartRing r E ⧸ P) L (Ideal.Quotient.mk P s)) *
        emb (IsLocalization.Away.invSelf (Ideal.Quotient.mk P s)) = 1 := by
      rw [← map_mul, IsLocalization.Away.mul_invSelf, map_one]
    simpa only [mul_pow, one_pow] using congrArg (fun q : Frac ↦ q ^ τ) hbase
  calc
    emb (algebraMap (ChartRing r E ⧸ P) L (Ideal.Quotient.mk P s)) ^ τ *
        (Polynomial.taylor (φ center)
          (rationalTaylorPolynomial (φ center) (MvPolynomial.map φ.toRingHom Q) K x)).coeff
            l.val *
        emb (IsLocalization.Away.invSelf (Ideal.Quotient.mk P s)) ^ τ =
      (Polynomial.taylor (φ center)
          (rationalTaylorPolynomial (φ center) (MvPolynomial.map φ.toRingHom Q) K x)).coeff
            l.val *
        (emb (algebraMap (ChartRing r E ⧸ P) L (Ideal.Quotient.mk P s)) ^ τ *
          emb (IsLocalization.Away.invSelf (Ideal.Quotient.mk P s)) ^ τ) := by ring
    _ = (Polynomial.taylor (φ center)
          (rationalTaylorPolynomial (φ center) (MvPolynomial.map φ.toRingHom Q) K x)).coeff
            l.val := by rw [hcancel, mul_one]
    _ = x (⟨l.val, by omega⟩ : Fin (r + 1)) := by
      have hjet := congrFun
        (polynomialJet_rationalTaylorPolynomial (φ center) (MvPolynomial.map φ.toRingHom Q)
          K hK x) ⟨l.val, by omega⟩
      rw [polynomialJet, Polynomial.hasseJet_eq_taylor_coeff] at hjet
      simpa only using hjet
    _ = MvPolynomial.aeval x
        (MvPolynomial.X (⟨l.val, by omega⟩ : Fin (r + 1))) := by
      simp only [MvPolynomial.aeval_X]

/-- Map the first `k` reconstructed coefficients into a retained fixed Taylor chart. -/
def chartCoefficientMap (center : E) (Q : DifferentialPolynomial E r)
    (K k : ℕ) (hkK : k ≤ K) (P : Ideal (ChartRing r E)) (τ : ℕ) :
    MvPolynomial (Fin k) E →ₐ[E] ChartAway P (initialJetSeparant center Q) :=
  MvPolynomial.eval₂AlgHom E fun l ↦
    localizedChartCoefficient center Q K P (Fin.castLE hkK l) (τ := τ)

/-- The first `k` reconstructed coefficients generate every chart coordinate after the
separant is inverted and the high reconstructed coefficients vanish. -/
theorem chartCoordinate_mem_range_chartCoefficientMap_of_exponent
    (center : E) (Q : DifferentialPolynomial E r) (K k τ : ℕ)
    (hτ : TaylorExponentSufficient r K τ) (hK : r < K) (hkK : k ≤ K)
    (P : Ideal (ChartRing r E)) (hP : P.IsPrime)
    (hs : initialJetSeparant center Q ∉ P)
    (hhigh : ∀ l : Fin K, k ≤ l.val →
      commonTaylorNumerator center Q K l (τ := τ) ∈ P)
    (p : ChartRing r E) :
    algebraMap (ChartRing r E ⧸ P) (ChartAway P (initialJetSeparant center Q))
        (Ideal.Quotient.mk P p) ∈
      Set.range (chartCoefficientMap center Q K k hkK P (τ := τ)) := by
  induction p using MvPolynomial.induction_on with
  | C a =>
      refine ⟨MvPolynomial.C a, ?_⟩
      rw [show Ideal.Quotient.mk P (MvPolynomial.C a) =
        algebraMap E (ChartRing r E ⧸ P) a by
          rw [← Ideal.Quotient.mk_algebraMap]
          rfl]
      simpa [chartCoefficientMap] using
        (IsScalarTower.algebraMap_apply E (ChartRing r E ⧸ P)
          (ChartAway P (initialJetSeparant center Q)) a)
  | add p q hp hq =>
      obtain ⟨p', hp'⟩ := hp
      obtain ⟨q', hq'⟩ := hq
      refine ⟨p' + q', ?_⟩
      rw [map_add, hp', hq', map_add, map_add]
  | mul_X p j hp =>
      obtain ⟨p', hp'⟩ := hp
      by_cases hjk : j.val < k
      · let l : Fin k := ⟨j.val, hjk⟩
        refine ⟨p' * MvPolynomial.X l, ?_⟩
        rw [map_mul, hp', map_mul, map_mul]
        simp only [chartCoefficientMap, MvPolynomial.eval₂AlgHom_X]
        congr 1
        apply localizedChartCoefficient_eq_jet_of_exponent center Q K τ hτ hK P hP hs
        dsimp only [l, Fin.castLE]
        omega
      · have hkj : k ≤ j.val := Nat.le_of_not_gt hjk
        let l : Fin K := ⟨j.val, by omega⟩
        have hcoeffZero : localizedChartCoefficient center Q K P l (τ := τ) = 0 := by
          simp only [localizedChartCoefficient]
          rw [Ideal.Quotient.eq_zero_iff_mem.mpr (hhigh l hkj), map_zero, zero_mul]
        have hjetZero : localizedChartJet P (initialJetSeparant center Q) j = 0 := by
          rw [← localizedChartCoefficient_eq_jet_of_exponent center Q K τ hτ hK P hP hs l
            (by dsimp only [l]; omega)]
          exact hcoeffZero
        refine ⟨0, ?_⟩
        rw [map_zero, map_mul, map_mul]
        change 0 = _ * localizedChartJet P (initialJetSeparant center Q) j
        rw [hjetZero, mul_zero]

set_option maxHeartbeats 800000 in
-- Normalizing the cleared Taylor equation expands a finite coefficient sum.
/-- A retained Taylor agreement cut becomes its ordinary coefficient-evaluation equation under
the fixed-chart coefficient map. -/
theorem fixedCoefficientEvaluation_mem_ker_chartCoefficientMap_of_exponent
    (center : E) (Q : DifferentialPolynomial E r) (K k τ : ℕ) (hkK : k ≤ K)
    (P : Ideal (ChartRing r E)) (α y : E)
    (hcut : taylorAgreementEquation center Q K α y (τ := τ) ∈ P)
    (hhigh : ∀ l : Fin K, k ≤ l.val →
      commonTaylorNumerator center Q K l (τ := τ) ∈ P) :
    fixedCoefficientEvaluation k (α - center) y ∈
      RingHom.ker (chartCoefficientMap center Q K k hkK P (τ := τ)).toRingHom := by
  let s := initialJetSeparant center Q
  let L := ChartAway P s
  let src : ChartRing r E →ₐ[E] L :=
    (IsScalarTower.toAlgHom E (ChartRing r E ⧸ P) L).comp (Ideal.Quotient.mkₐ E P)
  have hcut0 : src (taylorAgreementEquation center Q K α y (τ := τ)) = 0 := by
    change algebraMap (ChartRing r E ⧸ P) L
      (Ideal.Quotient.mk P (taylorAgreementEquation center Q K α y (τ := τ))) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hcut, map_zero]
  have hhigh0 (l : Fin K) (hl : k ≤ l.val) :
      src (commonTaylorNumerator center Q K l (τ := τ)) = 0 := by
    change algebraMap (ChartRing r E ⧸ P) L
      (Ideal.Quotient.mk P
        (commonTaylorNumerator center Q K l (τ := τ))) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr (hhigh l hl), map_zero]
  have hcancel : src s ^ τ *
      IsLocalization.Away.invSelf (Ideal.Quotient.mk P s) ^ τ = 1 := by
    have hbase : src s * IsLocalization.Away.invSelf (Ideal.Quotient.mk P s) = 1 :=
      IsLocalization.Away.mul_invSelf (S := L) (Ideal.Quotient.mk P s)
    simpa only [mul_pow, one_pow] using congrArg (fun q : L ↦ q ^ τ) hbase
  have hcutEq :
      (∑ l : Fin K, (algebraMap E L (α - center)) ^ l.val *
        src (commonTaylorNumerator center Q K l (τ := τ))) -
          algebraMap E L y * src s ^ τ = 0 := by
    simpa [taylorAgreementEquation] using hcut0
  have hsplit (u : Fin K → L) :
      (∑ l : Fin K, u l) =
        (∑ l : Fin k, u (Fin.castLE hkK l)) +
          ∑ l : Fin (K - k), u ⟨k + l.val, by omega⟩ := by
    let e : Fin (k + (K - k)) ≃ Fin K := finCongr (Nat.add_sub_of_le hkK)
    rw [← Equiv.sum_comp e, Fin.sum_univ_add]
    congr 1
  let u : Fin K → L := fun l ↦
    (algebraMap E L (α - center)) ^ l.val *
      src (commonTaylorNumerator center Q K l (τ := τ))
  have htail : (∑ l : Fin (K - k), u ⟨k + l.val, by omega⟩) = 0 := by
    apply Finset.sum_eq_zero
    intro l _
    rw [show u ⟨k + l.val, by omega⟩ =
      (algebraMap E L (α - center)) ^ (k + l.val) *
        src (commonTaylorNumerator center Q K
          ⟨k + l.val, by omega⟩ (τ := τ)) from rfl,
      hhigh0 _ (by simp), mul_zero]
  have hfirst :
      (∑ l : Fin k, (algebraMap E L (α - center)) ^ l.val *
        src (commonTaylorNumerator center Q K
          (Fin.castLE hkK l) (τ := τ))) = algebraMap E L y * src s ^ τ := by
    have hfull := sub_eq_zero.mp hcutEq
    rw [hsplit u, htail, add_zero] at hfull
    exact hfull
  let invPow : L := IsLocalization.Away.invSelf (Ideal.Quotient.mk P s) ^ τ
  have hlocalized :
      (∑ l : Fin k, (algebraMap E L (α - center)) ^ l.val *
        localizedChartCoefficient center Q K P (Fin.castLE hkK l) (τ := τ)) =
          algebraMap E L y := by
    change (∑ l : Fin k, (algebraMap E L (α - center)) ^ l.val *
        (src (commonTaylorNumerator center Q K
          (Fin.castLE hkK l) (τ := τ)) * invPow)) = algebraMap E L y
    rw [show (∑ l : Fin k, (algebraMap E L (α - center)) ^ l.val *
        (src (commonTaylorNumerator center Q K
          (Fin.castLE hkK l) (τ := τ)) * invPow)) =
      (∑ l : Fin k, (algebraMap E L (α - center)) ^ l.val *
        src (commonTaylorNumerator center Q K
          (Fin.castLE hkK l) (τ := τ))) * invPow by
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro l _
          ring]
    rw [hfirst]
    calc
      algebraMap E L y * src s ^ τ * invPow =
          algebraMap E L y * (src s ^ τ * invPow) := by ring
      _ = algebraMap E L y := by rw [show src s ^ τ * invPow = 1 from hcancel, mul_one]
  let Φ := chartCoefficientMap center Q K k hkK P (τ := τ)
  change Φ (fixedCoefficientEvaluation k (α - center) y) = 0
  have hC (a : E) : Φ (MvPolynomial.C a) =
      algebraMap E (ChartAway P (initialJetSeparant center Q)) a := by
    simp [Φ, chartCoefficientMap]
  have hX (l : Fin k) : Φ (MvPolynomial.X l) =
      localizedChartCoefficient center Q K P (Fin.castLE hkK l) (τ := τ) := by
    simp [Φ, chartCoefficientMap]
  rw [fixedCoefficientEvaluation, map_sub, map_sum]
  simp only [map_mul, map_pow, hC, hX]
  exact sub_eq_zero.mpr (by simpa only [L] using hlocalized)

/-- A retained fixed Taylor-chart prime containing `c` distinct agreement cuts has dimension at
most `k-c`.  The proof reuses the ordinary Vandermonde quotient bound and the generic
localization comparison used by the source-coordinate theorem. -/
theorem chart_prime_hilbertPolynomial_natDegree_le_of_agreements_of_exponent
    (center : E) (Q : DifferentialPolynomial E r) (K k c τ : ℕ)
    (hτ : TaylorExponentSufficient r K τ) (hK : r < K)
    (hkK : k ≤ K) (hck : c ≤ k)
    (P : Ideal (ChartRing r E)) (hP : P.IsPrime)
    (hs : initialJetSeparant center Q ∉ P)
    (hhigh : ∀ l : Fin K, k ≤ l.val →
      commonTaylorNumerator center Q K l (τ := τ) ∈ P)
    (α : Fin c ↪ E) (y : Fin c → E)
    (hcut : ∀ i, taylorAgreementEquation center Q K (α i) (y i) (τ := τ) ∈ P) :
    (hilbertPolynomial P).natDegree ≤ k - c := by
  classical
  let s := initialJetSeparant center Q
  let L := ChartAway P s
  let _ : P.IsPrime := hP
  have hs0 : Ideal.Quotient.mk P s ≠ 0 := by
    intro hz
    exact hs (Ideal.Quotient.eq_zero_iff_mem.mp hz)
  let _ : IsDomain L := Localization.Away.isDomain hs0
  let Φ := chartCoefficientMap center Q K k hkK P (τ := τ)
  let J : Ideal (MvPolynomial (Fin k) E) := RingHom.ker Φ.toRingHom
  have hJ : J.IsPrime := RingHom.ker_isPrime Φ.toRingHom
  let β : Fin c ↪ E :=
    ⟨fun i ↦ α i - center, fun i j hij ↦ α.injective (sub_left_injective hij)⟩
  have heval (i : Fin c) : fixedCoefficientEvaluation k (β i) (y i) ∈ J := by
    exact fixedCoefficientEvaluation_mem_ker_chartCoefficientMap_of_exponent
      center Q K k τ hkK P (α i) (y i) (hcut i) hhigh
  have hJdim : (hilbertPolynomial J).natDegree ≤ k - c :=
    fixedCoefficientEvaluation_hilbertPolynomial_natDegree_le hck β y hJ.ne_top heval
  obtain ⟨t, ht⟩ := chartCoordinate_mem_range_chartCoefficientMap_of_exponent
    center Q K k τ hτ hK hkK P hP hs hhigh s
  have ht' : Φ t = algebraMap (ChartRing r E ⧸ P) L (Ideal.Quotient.mk P s) := ht
  have htJ : t ∉ J := by
    intro htmem
    have htzero : Φ t = 0 := htmem
    rw [ht'] at htzero
    have hone := IsLocalization.Away.mul_invSelf (S := L) (Ideal.Quotient.mk P s)
    rw [htzero, zero_mul] at hone
    exact zero_ne_one hone
  let qΦ : (MvPolynomial (Fin k) E ⧸ J) →ₐ[E] L :=
    Ideal.Quotient.liftₐ J Φ fun p hp ↦ hp
  have hqt : qΦ (Ideal.Quotient.mk J t) =
      algebraMap (ChartRing r E ⧸ P) L (Ideal.Quotient.mk P s) := by
    rw [show qΦ (Ideal.Quotient.mk J t) = Φ t by rfl]
    exact ht'
  have hqtUnit : IsUnit (qΦ (Ideal.Quotient.mk J t)) := by
    apply isUnit_iff_exists_inv.mpr
    refine ⟨IsLocalization.Away.invSelf (Ideal.Quotient.mk P s), ?_⟩
    rw [hqt]
    exact IsLocalization.Away.mul_invSelf (S := L) (Ideal.Quotient.mk P s)
  let gRing : Localization.Away (Ideal.Quotient.mk J t) →+* L :=
    IsLocalization.Away.lift (g := qΦ.toRingHom) (Ideal.Quotient.mk J t) hqtUnit
  let locMap : Localization.Away (Ideal.Quotient.mk J t) →ₐ[E] L :=
    { toRingHom := gRing
      commutes' := by
        intro a
        change gRing (algebraMap E (Localization.Away (Ideal.Quotient.mk J t)) a) =
          algebraMap E L a
        rw [IsScalarTower.algebraMap_apply E (MvPolynomial (Fin k) E ⧸ J)
          (Localization.Away (Ideal.Quotient.mk J t))]
        rw [show gRing (algebraMap (MvPolynomial (Fin k) E ⧸ J)
          (Localization.Away (Ideal.Quotient.mk J t))
          (algebraMap E (MvPolynomial (Fin k) E ⧸ J) a)) =
            qΦ (algebraMap E (MvPolynomial (Fin k) E ⧸ J) a) by
          exact IsLocalization.Away.lift_eq
            (S := Localization.Away (Ideal.Quotient.mk J t))
            (g := qΦ.toRingHom) (Ideal.Quotient.mk J t) hqtUnit _]
        exact qΦ.commutes a }
  have hlocMap : Function.Surjective locMap := by
    intro z
    obtain ⟨m, a, hza⟩ := IsLocalization.Away.surj (Ideal.Quotient.mk P s) z
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    obtain ⟨p, hp⟩ := chartCoordinate_mem_range_chartCoefficientMap_of_exponent
      center Q K k τ hτ hK hkK P hP hs hhigh a
    let x : Localization.Away (Ideal.Quotient.mk J t) :=
      Localization.mk (Ideal.Quotient.mk J p) ⟨Ideal.Quotient.mk J t ^ m, m, rfl⟩
    refine ⟨x, ?_⟩
    have hbase : algebraMap (ChartRing r E ⧸ P) L (Ideal.Quotient.mk P s) *
        IsLocalization.Away.invSelf (Ideal.Quotient.mk P s) = 1 :=
      IsLocalization.Away.mul_invSelf (S := L) (Ideal.Quotient.mk P s)
    have hz : algebraMap (ChartRing r E ⧸ P) L (Ideal.Quotient.mk P a) *
        IsLocalization.Away.invSelf (Ideal.Quotient.mk P s) ^ m = z := by
      have h := congrArg
        (fun q : L ↦ q * IsLocalization.Away.invSelf (Ideal.Quotient.mk P s) ^ m) hza
      simpa only [← mul_pow, hbase, one_pow, mul_one, mul_assoc] using h.symm
    have hqbase : qΦ (Ideal.Quotient.mk J t) *
        IsLocalization.Away.invSelf (Ideal.Quotient.mk P s) = 1 := by
      rw [hqt]
      exact hbase
    change gRing x = z
    rw [show gRing x = qΦ (Ideal.Quotient.mk J p) *
        IsLocalization.Away.invSelf (Ideal.Quotient.mk P s) ^ m by
      dsimp only [gRing, x]
      exact Localization.awayLift_mk qΦ.toRingHom (Ideal.Quotient.mk J t)
        (Ideal.Quotient.mk J p) (IsLocalization.Away.invSelf (Ideal.Quotient.mk P s))
          hqbase m]
    rw [show qΦ (Ideal.Quotient.mk J p) = Φ p by rfl, hp]
    exact hz
  exact retainedPrime_hilbertPolynomial_natDegree_le_of_coefficientLocalization
    hJ htJ hJdim hP hs locMap hlocMap

/-- Every positive-dimensional retained fixed-chart prime satisfies the hereditary
coefficient-space budget used by product incidence. -/
theorem chart_dimensionSensitive_component_of_exponent
    (center : E) (Q : DifferentialPolynomial E r) (K k n τ : ℕ)
    (hτ : TaylorExponentSufficient r K τ) (hK : r < K) (hkK : k ≤ K)
    (P : Ideal (ChartRing r E)) (hP : P.IsPrime)
    (hs : initialJetSeparant center Q ∉ P)
    (hhigh : ∀ l : Fin K, k ≤ l.val →
      commonTaylorNumerator center Q K l (τ := τ) ∈ P)
    (α : Fin n ↪ E) (y : Fin n → E)
    (hd : 0 < (hilbertPolynomial P).natDegree) :
    let cuts : Fin n → ChartRing r E := fun i ↦
      taylorAgreementEquation center Q K (α i) (y i) (τ := τ)
    (hilbertPolynomial P).natDegree ≤ k ∧
      (cutsInIdeal P cuts).card ≤ k - (hilbertPolynomial P).natDegree := by
  classical
  dsimp only
  let cuts : Fin n → ChartRing r E := fun i ↦
    taylorAgreementEquation center Q K (α i) (y i) (τ := τ)
  let Bad := cutsInIdeal P cuts
  have hpartial (indices : Finset (Fin n)) (hcard : indices.card ≤ k)
      (hsub : indices ⊆ Bad) :
      (hilbertPolynomial P).natDegree ≤ k - indices.card := by
    let sample : Fin indices.card ↪ Fin n :=
      ⟨fun j ↦ (indices.equivFin.symm j).val,
        fun i j hij ↦ indices.equivFin.symm.injective (Subtype.ext hij)⟩
    let α' : Fin indices.card ↪ E :=
      ⟨fun j ↦ α (sample j), fun i j hij ↦ sample.injective (α.injective hij)⟩
    apply chart_prime_hilbertPolynomial_natDegree_le_of_agreements_of_exponent
      center Q K k indices.card τ hτ hK hkK hcard P hP hs hhigh α'
        (fun j ↦ y (sample j))
    intro j
    change cuts (sample j) ∈ P
    rw [← mem_cutsInIdeal]
    exact hsub (indices.equivFin.symm j).property
  have hdim : (hilbertPolynomial P).natDegree ≤ k := by
    simpa using hpartial ∅ (by simp) (by simp)
  refine ⟨hdim, ?_⟩
  change Bad.card ≤ k - (hilbertPolynomial P).natDegree
  by_cases hBadk : Bad.card ≤ k
  · have hle := hpartial Bad hBadk le_rfl
    omega
  · have hkBad : k ≤ Bad.card := by omega
    obtain ⟨indices, hindices, hcard⟩ := Finset.exists_subset_card_eq hkBad
    have hle := hpartial indices (by omega) hindices
    rw [hcard] at hle
    omega

abbrev SourceRing (r : ℕ) (E : Type*) [Field E] :=
  MvPolynomial (Option (Fin (r + 1))) E

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
    SourceAway P (symbolicSourceSeparant center Q) :=
  algebraMap (SourceRing r E ⧸ P)
      (SourceAway P (symbolicSourceSeparant center Q))
      (Ideal.Quotient.mk P (symbolicSourceNumerator center Q K l (τ := τ))) *
    IsLocalization.Away.invSelf
      (Ideal.Quotient.mk P (symbolicSourceSeparant center Q)) ^ τ

/-- Below the differential order, the reconstructed coefficients recover the actual jet
coordinates in the retained source localization. -/
theorem localizedSourceCoefficient_eq_jet_of_exponent
    (center : E) (Q : DifferentialPolynomial E[X] r) (K τ : ℕ)
    (hτ : TaylorExponentSufficient r K τ) (hK : r < K)
    (P : Ideal (SourceRing r E)) (hP : P.IsPrime)
    (hs : symbolicSourceSeparant center Q ∉ P)
    (l : Fin K) (hl : l.val ≤ r) :
    localizedSourceCoefficient center Q K P l (τ := τ) =
      localizedSourceJet P (symbolicSourceSeparant center Q)
        ⟨l.val, by omega⟩ := by
  let s := symbolicSourceSeparant center Q
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
      aeval x (MvPolynomial.flattenChallenge p) =
        aeval (fun j ↦ x (some j)) (MvPolynomial.map φ.toRingHom p) := by
    induction p using MvPolynomial.induction_on with
    | C p =>
        rw [MvPolynomial.flattenChallenge_C, ← Polynomial.aeval_algHom_apply]
        simp [φ]
    | add p q hp hq => simp only [map_add, hp, hq]
    | mul_X p j hp =>
        simp only [map_mul, hp, MvPolynomial.flattenChallenge_X, MvPolynomial.aeval_X,
          MvPolynomial.map_X]
  have hsepEval : aeval (fun j ↦ x (some j))
      (MvPolynomial.map φ.toRingHom
        (initialJetSeparantOver (Polynomial.C center : E[X]) Q)) =
        emb (algebraMap (SourceRing r E ⧸ P) L (Ideal.Quotient.mk P s)) := by
    rw [← hflatten (initialJetSeparantOver (Polynomial.C center : E[X]) Q)]
    exact (heval s).symm
  have hsepNe : aeval (fun j ↦ x (some j))
      (MvPolynomial.map φ.toRingHom
        (initialJetSeparantOver (Polynomial.C center : E[X]) Q)) ≠ 0 := by
    rw [hsepEval]
    have hLne : algebraMap (SourceRing r E ⧸ P) L (Ideal.Quotient.mk P s) ≠ 0 := by
      intro hz
      have hone := IsLocalization.Away.mul_invSelf (S := L) (Ideal.Quotient.mk P s)
      rw [hz, zero_mul] at hone
      exact zero_ne_one hone
    intro hz
    apply hLne
    apply IsFractionRing.injective L Frac
    simpa only [map_zero] using hz
  have hrec := aeval_map_commonTaylorNumeratorOver_reconstruction_of_exponent φ
    (Polynomial.C center) Q K τ hτ (fun j ↦ x (some j)) hsepNe l
  have hnumEval : aeval (fun j ↦ x (some j))
      (MvPolynomial.map φ.toRingHom
        (commonTaylorNumeratorOver (F := E) (Polynomial.C center : E[X]) Q K l (τ := τ))) =
        emb (algebraMap (SourceRing r E ⧸ P) L
          (Ideal.Quotient.mk P (symbolicSourceNumerator center Q K l (τ := τ)))) := by
    rw [← hflatten
      (commonTaylorNumeratorOver (F := E) (Polynomial.C center : E[X]) Q K l (τ := τ))]
    exact (heval (symbolicSourceNumerator center Q K l (τ := τ))).symm
  apply IsFractionRing.injective L Frac
  rw [show algebraMap L Frac = emb from rfl]
  simp only [localizedSourceCoefficient, localizedSourceJet, map_mul, map_pow]
  rw [heval (symbolicSourceNumerator center Q K l (τ := τ)),
    heval (MvPolynomial.X (some ⟨l.val, by omega⟩))]
  rw [← heval (symbolicSourceNumerator center Q K l (τ := τ)), ← hnumEval]
  rw [hsepEval] at hrec
  rw [hrec]
  have hcancel :
      emb (algebraMap (SourceRing r E ⧸ P) L (Ideal.Quotient.mk P s)) ^ τ *
          emb (IsLocalization.Away.invSelf (Ideal.Quotient.mk P s)) ^ τ = 1 := by
    have hbase : emb (algebraMap (SourceRing r E ⧸ P) L (Ideal.Quotient.mk P s)) *
        emb (IsLocalization.Away.invSelf (Ideal.Quotient.mk P s)) = 1 := by
      rw [← map_mul, IsLocalization.Away.mul_invSelf, map_one]
    simpa only [mul_pow, one_pow] using congrArg (fun q : Frac ↦ q ^ τ) hbase
  dsimp only [s] at hcancel
  calc
    emb (algebraMap (SourceRing r E ⧸ P) L
          (Ideal.Quotient.mk P (symbolicSourceSeparant center Q))) ^ τ *
        ((Polynomial.taylor (φ (Polynomial.C center))
          (rationalTaylorPolynomial (φ (Polynomial.C center))
            (MvPolynomial.map φ.toRingHom Q) K (fun j ↦ x (some j)))).coeff l.val) *
        emb (IsLocalization.Away.invSelf
          (Ideal.Quotient.mk P (symbolicSourceSeparant center Q))) ^ τ =
        ((Polynomial.taylor (φ (Polynomial.C center))
          (rationalTaylorPolynomial (φ (Polynomial.C center))
            (MvPolynomial.map φ.toRingHom Q) K (fun j ↦ x (some j)))).coeff l.val) *
          (emb (algebraMap (SourceRing r E ⧸ P) L
            (Ideal.Quotient.mk P (symbolicSourceSeparant center Q))) ^ τ *
            emb (IsLocalization.Away.invSelf
              (Ideal.Quotient.mk P (symbolicSourceSeparant center Q))) ^ τ) := by ring
    _ = (Polynomial.taylor (φ (Polynomial.C center))
          (rationalTaylorPolynomial (φ (Polynomial.C center))
            (MvPolynomial.map φ.toRingHom Q) K (fun j ↦ x (some j)))).coeff l.val := by
      rw [hcancel, mul_one]
    _ = (MvPolynomial.aeval x)
        (MvPolynomial.X (some (⟨l.val, by omega⟩ : Fin (r + 1)))) := by
      simp only [MvPolynomial.aeval_X]
      have hjet := congrFun
        (polynomialJet_rationalTaylorPolynomial (φ (Polynomial.C center))
          (MvPolynomial.map φ.toRingHom Q) K hK
          (fun j ↦ x (some j))) ⟨l.val, by omega⟩
      rw [polynomialJet, Polynomial.hasseJet_eq_taylor_coeff] at hjet
      exact hjet

/-- Map the challenge and the first `k` reconstructed coefficients into a retained source
localization. -/
def sourceCoefficientMap (center : E) (Q : DifferentialPolynomial E[X] r)
    (K k : ℕ) (hkK : k ≤ K) (P : Ideal (SourceRing r E)) (τ : ℕ := 2 * K) :
    MvPolynomial (Option (Fin k)) E →ₐ[E]
      SourceAway P (symbolicSourceSeparant center Q) :=
  MvPolynomial.eval₂AlgHom E fun
    | none => localizedSourceChallenge P (symbolicSourceSeparant center Q)
    | some l => localizedSourceCoefficient center Q K P (Fin.castLE hkK l) (τ := τ)

/-- The challenge and first `k` reconstructed coefficients generate every ordinary source
coordinate inside the retained localization.  Jet coordinates below `k` are reconstructed
coefficients; those at or above `k` vanish because the actual retained prime contains every high
numerator cut. -/
theorem sourceCoordinate_mem_range_sourceCoefficientMap_of_exponent
    (center : E) (Q : DifferentialPolynomial E[X] r) (K k τ : ℕ)
    (hτ : TaylorExponentSufficient r K τ) (hK : r < K) (hkK : k ≤ K)
    (P : Ideal (SourceRing r E)) (hP : P.IsPrime)
    (hs : symbolicSourceSeparant center Q ∉ P)
    (hhigh : ∀ l : Fin K, k ≤ l.val →
      symbolicSourceNumerator center Q K l (τ := τ) ∈ P)
    (p : SourceRing r E) :
    algebraMap (SourceRing r E ⧸ P)
      (SourceAway P (symbolicSourceSeparant center Q)) (Ideal.Quotient.mk P p) ∈
        Set.range (sourceCoefficientMap center Q K k hkK P (τ := τ)) := by
  induction p using MvPolynomial.induction_on with
  | C a =>
      refine ⟨MvPolynomial.C a, ?_⟩
      rw [show Ideal.Quotient.mk P (MvPolynomial.C a) =
        algebraMap E (SourceRing r E ⧸ P) a by
          rw [← Ideal.Quotient.mk_algebraMap]
          rfl]
      simpa [sourceCoefficientMap] using
        (IsScalarTower.algebraMap_apply E (SourceRing r E ⧸ P)
          (SourceAway P (symbolicSourceSeparant center Q)) a)
  | add p q hp hq =>
      obtain ⟨p', hp'⟩ := hp
      obtain ⟨q', hq'⟩ := hq
      refine ⟨p' + q', ?_⟩
      rw [map_add, hp', hq', map_add, map_add]
  | mul_X p j hp =>
      obtain ⟨p', hp'⟩ := hp
      cases j with
      | none =>
          refine ⟨p' * MvPolynomial.X none, ?_⟩
          rw [map_mul, hp', map_mul, map_mul]
          simp [sourceCoefficientMap, localizedSourceChallenge]
      | some j =>
          by_cases hjk : j.val < k
          · let l : Fin k := ⟨j.val, hjk⟩
            refine ⟨p' * MvPolynomial.X (some l), ?_⟩
            rw [map_mul, hp', map_mul, map_mul]
            simp only [sourceCoefficientMap, MvPolynomial.eval₂AlgHom_X]
            congr 1
            apply localizedSourceCoefficient_eq_jet_of_exponent center Q K τ hτ hK P hP hs
            dsimp only [l, Fin.castLE]
            omega
          · have hkj : k ≤ j.val := Nat.le_of_not_gt hjk
            let l : Fin K := ⟨j.val, by omega⟩
            have hcoeffZero : localizedSourceCoefficient center Q K P l (τ := τ) = 0 := by
              simp only [localizedSourceCoefficient]
              rw [Ideal.Quotient.eq_zero_iff_mem.mpr (hhigh l hkj), map_zero,
                zero_mul]
            have hjetZero :
                localizedSourceJet P (symbolicSourceSeparant center Q) j = 0 := by
              rw [← localizedSourceCoefficient_eq_jet_of_exponent center Q K τ hτ hK P hP hs l (by
                dsimp only [l]
                omega)]
              exact hcoeffZero
            refine ⟨0, ?_⟩
            rw [map_zero, map_mul, map_mul]
            change 0 = _ * localizedSourceJet P (symbolicSourceSeparant center Q) j
            rw [hjetZero, mul_zero]

set_option maxHeartbeats 800000 in
-- Expanding the flattened symbolic agreement and normalizing the finite sum is elaboration-heavy.
/-- A retained polynomial-valued symbolic agreement cut becomes the corresponding coefficient
evaluation equation under the source coefficient map. -/
theorem polynomialCoefficientEvaluation_mem_ker_sourceCoefficientMap_of_exponent
    (center : E) (Q : DifferentialPolynomial E[X] r) (K k τ : ℕ) (hkK : k ≤ K)
    (P : Ideal (SourceRing r E)) (hP : P.IsPrime)
    (hs : symbolicSourceSeparant center Q ∉ P)
    (α : E) (received : E[X])
    (hcut : symbolicSourcePolynomialAgreement center Q K α received (τ := τ) ∈ P)
    (hhigh : ∀ l : Fin K, k ≤ l.val →
      symbolicSourceNumerator center Q K l (τ := τ) ∈ P) :
    polynomialCoefficientEvaluation k (α - center) received ∈
      RingHom.ker (sourceCoefficientMap center Q K k hkK P (τ := τ)).toRingHom := by
  let s := symbolicSourceSeparant center Q
  let L := SourceAway P s
  let _ : P.IsPrime := hP
  have hs0 : Ideal.Quotient.mk P s ≠ 0 := by
    intro h
    exact hs (Ideal.Quotient.eq_zero_iff_mem.mp h)
  let _ : IsDomain L := Localization.Away.isDomain hs0
  let src : SourceRing r E →ₐ[E] L :=
    (IsScalarTower.toAlgHom E (SourceRing r E ⧸ P) L).comp (Ideal.Quotient.mkₐ E P)
  have hcut0 : src (symbolicSourcePolynomialAgreement center Q K α received (τ := τ)) = 0 := by
    change algebraMap (SourceRing r E ⧸ P) L
      (Ideal.Quotient.mk P
        (symbolicSourcePolynomialAgreement center Q K α received (τ := τ))) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hcut, map_zero]
  have hhigh0 (l : Fin K) (hl : k ≤ l.val) :
      src (symbolicSourceNumerator center Q K l (τ := τ)) = 0 := by
    change algebraMap (SourceRing r E ⧸ P) L
      (Ideal.Quotient.mk P (symbolicSourceNumerator center Q K l (τ := τ))) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr (hhigh l hl), map_zero]
  have hcancel : src s ^ τ *
      IsLocalization.Away.invSelf (Ideal.Quotient.mk P s) ^ τ = 1 := by
    have hbase : src s * IsLocalization.Away.invSelf (Ideal.Quotient.mk P s) = 1 := by
      exact IsLocalization.Away.mul_invSelf (S := L) (Ideal.Quotient.mk P s)
    simpa only [mul_pow, one_pow] using congrArg (fun q : L ↦ q ^ τ) hbase
  let ψ : E[X] →ₐ[E] L := Polynomial.aeval (src (MvPolynomial.X none))
  have hsrcFlatten (p : MvPolynomial (Fin (r + 1)) E[X]) :
      src (MvPolynomial.flattenChallenge p) =
        aeval (fun j ↦ src (MvPolynomial.X (some j))) (MvPolynomial.map ψ.toRingHom p) := by
    induction p using MvPolynomial.induction_on with
    | C p =>
        rw [MvPolynomial.flattenChallenge_C, ← Polynomial.aeval_algHom_apply]
        simp [ψ]
    | add p q hp hq => simp only [map_add, hp, hq]
    | mul_X p j hp =>
        simp only [map_mul, hp, MvPolynomial.flattenChallenge_X, MvPolynomial.aeval_X,
          MvPolynomial.map_X]
  have hnum (l : Fin K) :
      aeval (fun j ↦ src (MvPolynomial.X (some j)))
        (MvPolynomial.map ψ.toRingHom
          (commonTaylorNumeratorOver (F := E) (Polynomial.C center) Q K l (τ := τ))) =
        src (symbolicSourceNumerator center Q K l (τ := τ)) := by
    exact (hsrcFlatten
      (commonTaylorNumeratorOver (F := E) (Polynomial.C center) Q K l (τ := τ))).symm
  have hsep :
      aeval (fun j ↦ src (MvPolynomial.X (some j)))
        (MvPolynomial.map ψ.toRingHom
          (initialJetSeparantOver (Polynomial.C center) Q)) = src s := by
    exact (hsrcFlatten (initialJetSeparantOver (Polynomial.C center) Q)).symm
  have hcutEq :
      (∑ l : Fin K, (algebraMap E L (α - center)) ^ l.val *
        src (symbolicSourceNumerator center Q K l (τ := τ))) -
          ψ received * src s ^ τ = 0 := by
    rw [symbolicSourcePolynomialAgreement] at hcut0
    change src (MvPolynomial.flattenChallenge
      (taylorAgreementEquationOver (F := E) (Polynomial.C center) Q K
        (Polynomial.C α) received
        (τ := τ))) = 0 at hcut0
    rw [hsrcFlatten] at hcut0
    simp only [taylorAgreementEquationOver, map_sub, map_sum, map_mul, map_pow,
      MvPolynomial.map_C] at hcut0
    simp only [MvPolynomial.aeval_C] at hcut0
    simp_rw [hnum] at hcut0
    rw [hsep] at hcut0
    change (∑ l : Fin K, (ψ (Polynomial.C α) - ψ (Polynomial.C center)) ^ l.val *
        src (symbolicSourceNumerator center Q K l (τ := τ))) -
      ψ received * src s ^ τ = 0 at hcut0
    have hx : ψ (Polynomial.C α) - ψ (Polynomial.C center) =
        algebraMap E L (α - center) := by
      simp [ψ]
    rw [hx] at hcut0
    exact hcut0
  have hsplit (u : Fin K → L) :
      (∑ l : Fin K, u l) =
        (∑ l : Fin k, u (Fin.castLE hkK l)) +
          ∑ l : Fin (K - k), u ⟨k + l.val, by omega⟩ := by
    let e : Fin (k + (K - k)) ≃ Fin K := finCongr (Nat.add_sub_of_le hkK)
    rw [← Equiv.sum_comp e, Fin.sum_univ_add]
    congr 1
  let u : Fin K → L := fun l ↦
    (algebraMap E L (α - center)) ^ l.val *
      src (symbolicSourceNumerator center Q K l (τ := τ))
  have htail : (∑ l : Fin (K - k), u ⟨k + l.val, by omega⟩) = 0 := by
    apply Finset.sum_eq_zero
    intro l _
    have hkl : k ≤ (⟨k + l.val, by omega⟩ : Fin K).val := by simp
    rw [show u ⟨k + l.val, by omega⟩ =
      (algebraMap E L (α - center)) ^ (k + l.val) *
        src (symbolicSourceNumerator center Q K ⟨k + l.val, by omega⟩ (τ := τ)) from rfl,
      hhigh0 _ hkl, mul_zero]
  have hfirst :
      (∑ l : Fin k, (algebraMap E L (α - center)) ^ l.val *
        src (symbolicSourceNumerator center Q K (Fin.castLE hkK l) (τ := τ))) =
          ψ received * src s ^ τ := by
    have hfull := sub_eq_zero.mp hcutEq
    rw [hsplit u, htail, add_zero] at hfull
    exact hfull
  let invPow : L :=
    IsLocalization.Away.invSelf (Ideal.Quotient.mk P s) ^ τ
  have hcoeff (l : Fin k) :
      localizedSourceCoefficient center Q K P (Fin.castLE hkK l) (τ := τ) =
        src (symbolicSourceNumerator center Q K (Fin.castLE hkK l) (τ := τ)) * invPow := by
    rfl
  have hlocalized :
      (∑ l : Fin k, (algebraMap E L (α - center)) ^ l.val *
        localizedSourceCoefficient center Q K P (Fin.castLE hkK l) (τ := τ)) =
          received.eval₂ (algebraMap E L) (localizedSourceChallenge P s) := by
    simp_rw [hcoeff]
    rw [show (∑ l : Fin k, (algebraMap E L (α - center)) ^ l.val *
        (src (symbolicSourceNumerator center Q K (Fin.castLE hkK l) (τ := τ)) * invPow)) =
      (∑ l : Fin k, (algebraMap E L (α - center)) ^ l.val *
        src (symbolicSourceNumerator center Q K (Fin.castLE hkK l) (τ := τ))) * invPow by
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro l _
          ring]
    rw [hfirst]
    calc
      ψ received * src s ^ τ * invPow =
          ψ received * (src s ^ τ * invPow) := by ring
      _ = ψ received := by
        rw [show src s ^ τ * invPow = 1 from hcancel, mul_one]
      _ = received.eval₂ (algebraMap E L) (localizedSourceChallenge P s) := by
        rfl
  let Φ := sourceCoefficientMap center Q K k hkK P (τ := τ)
  change Φ (polynomialCoefficientEvaluation k (α - center) received) = 0
  have hC (a : E) : Φ (MvPolynomial.C a) =
      algebraMap E (SourceAway P (symbolicSourceSeparant center Q)) a := by
    simp [Φ, sourceCoefficientMap]
  have hX (j : Option (Fin k)) : Φ (MvPolynomial.X j) =
      match j with
      | none => localizedSourceChallenge P (symbolicSourceSeparant center Q)
      | some l => localizedSourceCoefficient center Q K P (Fin.castLE hkK l) (τ := τ) := by
    simp [Φ, sourceCoefficientMap]
  rw [polynomialCoefficientEvaluation, map_sub]
  have hreceived :=
    Polynomial.hom_eval₂ received MvPolynomial.C Φ.toRingHom (MvPolynomial.X none)
  change Φ (received.eval₂ MvPolynomial.C (MvPolynomial.X none)) =
    received.eval₂ (Φ.toRingHom.comp MvPolynomial.C) (Φ (MvPolynomial.X none)) at hreceived
  rw [hreceived]
  have hmap : Φ.toRingHom.comp MvPolynomial.C =
      algebraMap E (SourceAway P (symbolicSourceSeparant center Q)) := by
    ext a
    exact hC a
  rw [hmap]
  simp only [map_sum, map_mul, hC, hX]
  simp_rw [map_pow]
  exact sub_eq_zero.mpr hlocalized


/-- An affine received-line cut is the corresponding specialization of
`polynomialCoefficientEvaluation_mem_ker_sourceCoefficientMap_of_exponent`. -/
theorem coefficientEvaluation_mem_ker_sourceCoefficientMap_of_exponent
    (center : E) (Q : DifferentialPolynomial E[X] r) (K k τ : ℕ) (hkK : k ≤ K)
    (P : Ideal (SourceRing r E)) (hP : P.IsPrime)
    (hs : symbolicSourceSeparant center Q ∉ P)
    (α f g : E)
    (hcut : symbolicSourceAgreement center Q K α f g (τ := τ) ∈ P)
    (hhigh : ∀ l : Fin K, k ≤ l.val →
      symbolicSourceNumerator center Q K l (τ := τ) ∈ P) :
    affineCoefficientEvaluation k (α - center) f g ∈
      RingHom.ker (sourceCoefficientMap center Q K k hkK P (τ := τ)).toRingHom := by
  apply polynomialCoefficientEvaluation_mem_ker_sourceCoefficientMap_of_exponent
    center Q K k τ hkK P hP hs α
      (Polynomial.C f + Polynomial.X * Polynomial.C g)
  · simpa only [symbolicSourceAgreement, symbolicSourcePolynomialAgreement] using hcut
  · exact hhigh

/-- A retained source prime containing `c` agreement cuts at distinct evaluation points has
dimension at most `k + 1 - c`.

The proof first passes to the kernel of the coefficient map before localization.  Vandermonde
elimination bounds that ordinary coefficient quotient by `k + 1 - c`.  It then pulls the source
separant back through the coefficient map and localizes both quotients there; the resulting map
onto the actual retained source localization is surjective. -/
theorem symbolicSource_prime_hilbertPolynomial_natDegree_le_of_polynomial_agreements_of_exponent
    (center : E) (Q : DifferentialPolynomial E[X] r) (K k c τ : ℕ)
    (hτ : TaylorExponentSufficient r K τ)
    (hK : r < K) (hkK : k ≤ K) (hck : c ≤ k)
    (P : Ideal (SourceRing r E)) (hP : P.IsPrime)
    (hs : symbolicSourceSeparant center Q ∉ P)
    (hhigh : ∀ l : Fin K, k ≤ l.val →
      symbolicSourceNumerator center Q K l (τ := τ) ∈ P)
    (α : Fin c ↪ E) (received : Fin c → E[X])
    (hcut : ∀ i,
      symbolicSourcePolynomialAgreement center Q K (α i) (received i) (τ := τ) ∈ P) :
    (hilbertPolynomial P).natDegree ≤ k + 1 - c := by
  classical
  let s := symbolicSourceSeparant center Q
  let L := SourceAway P s
  let _ : P.IsPrime := hP
  have hs0 : Ideal.Quotient.mk P s ≠ 0 := by
    intro h
    exact hs (Ideal.Quotient.eq_zero_iff_mem.mp h)
  let _ : IsDomain L := Localization.Away.isDomain hs0
  let Φ := sourceCoefficientMap center Q K k hkK P (τ := τ)
  let J : Ideal (MvPolynomial (Option (Fin k)) E) := RingHom.ker Φ.toRingHom
  have hJ : J.IsPrime := RingHom.ker_isPrime Φ.toRingHom
  let β : Fin c ↪ E :=
    ⟨fun i ↦ α i - center, fun i j hij ↦ α.injective (sub_left_injective hij)⟩
  have heval (i : Fin c) :
      polynomialCoefficientEvaluation k (β i) (received i) ∈ J := by
    exact polynomialCoefficientEvaluation_mem_ker_sourceCoefficientMap_of_exponent
      center Q K k τ hkK P hP hs (α i) (received i) (hcut i) hhigh
  have hJdim : (hilbertPolynomial J).natDegree ≤ k + 1 - c :=
    polynomialCoefficientEvaluation_hilbertPolynomial_natDegree_le
      hck β received hJ.ne_top heval
  obtain ⟨t, ht⟩ := sourceCoordinate_mem_range_sourceCoefficientMap_of_exponent
    center Q K k τ hτ hK hkK P hP hs hhigh s
  have ht' : Φ t =
      algebraMap (SourceRing r E ⧸ P) L (Ideal.Quotient.mk P s) := ht
  have htJ : t ∉ J := by
    intro htmem
    have htzero : Φ t = 0 := htmem
    rw [ht'] at htzero
    have hone := IsLocalization.Away.mul_invSelf (S := L) (Ideal.Quotient.mk P s)
    rw [htzero, zero_mul] at hone
    exact zero_ne_one hone
  let qΦ : (MvPolynomial (Option (Fin k)) E ⧸ J) →ₐ[E] L :=
    Ideal.Quotient.liftₐ J Φ fun p hp ↦ hp
  have hqt : qΦ (Ideal.Quotient.mk J t) =
      algebraMap (SourceRing r E ⧸ P) L (Ideal.Quotient.mk P s) := by
    rw [show qΦ (Ideal.Quotient.mk J t) = Φ t by rfl]
    exact ht'
  have hqtUnit : IsUnit (qΦ (Ideal.Quotient.mk J t)) := by
    apply isUnit_iff_exists_inv.mpr
    refine ⟨IsLocalization.Away.invSelf (Ideal.Quotient.mk P s), ?_⟩
    rw [hqt]
    exact IsLocalization.Away.mul_invSelf (S := L) (Ideal.Quotient.mk P s)
  let gRing : Localization.Away (Ideal.Quotient.mk J t) →+* L :=
    IsLocalization.Away.lift (g := qΦ.toRingHom) (Ideal.Quotient.mk J t) hqtUnit
  let locMap : Localization.Away (Ideal.Quotient.mk J t) →ₐ[E] L :=
    { toRingHom := gRing
      commutes' := by
        intro a
        change gRing (algebraMap E (Localization.Away (Ideal.Quotient.mk J t)) a) =
          algebraMap E L a
        rw [IsScalarTower.algebraMap_apply E
          (MvPolynomial (Option (Fin k)) E ⧸ J)
          (Localization.Away (Ideal.Quotient.mk J t))]
        rw [show gRing (algebraMap (MvPolynomial (Option (Fin k)) E ⧸ J)
          (Localization.Away (Ideal.Quotient.mk J t))
          (algebraMap E (MvPolynomial (Option (Fin k)) E ⧸ J) a)) =
            qΦ (algebraMap E (MvPolynomial (Option (Fin k)) E ⧸ J) a) by
          exact IsLocalization.Away.lift_eq
            (S := Localization.Away (Ideal.Quotient.mk J t))
            (g := qΦ.toRingHom) (Ideal.Quotient.mk J t) hqtUnit _]
        exact qΦ.commutes a }
  have hlocMap : Function.Surjective locMap := by
    intro y
    obtain ⟨n, a, hya⟩ := IsLocalization.Away.surj (Ideal.Quotient.mk P s) y
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    obtain ⟨p, hp⟩ := sourceCoordinate_mem_range_sourceCoefficientMap_of_exponent
      center Q K k τ hτ hK hkK P hP hs hhigh a
    let x : Localization.Away (Ideal.Quotient.mk J t) :=
      Localization.mk (Ideal.Quotient.mk J p)
        ⟨Ideal.Quotient.mk J t ^ n, n, rfl⟩
    refine ⟨x, ?_⟩
    have hbase :
        algebraMap (SourceRing r E ⧸ P) L (Ideal.Quotient.mk P s) *
            IsLocalization.Away.invSelf (Ideal.Quotient.mk P s) = 1 :=
      IsLocalization.Away.mul_invSelf (S := L) (Ideal.Quotient.mk P s)
    have hy :
        algebraMap (SourceRing r E ⧸ P) L (Ideal.Quotient.mk P a) *
            IsLocalization.Away.invSelf (Ideal.Quotient.mk P s) ^ n = y := by
      have h := congrArg
        (fun w : L ↦ w * IsLocalization.Away.invSelf (Ideal.Quotient.mk P s) ^ n) hya
      simpa only [← mul_pow, hbase, one_pow, mul_one, mul_assoc] using h.symm
    have hqbase : qΦ (Ideal.Quotient.mk J t) *
        IsLocalization.Away.invSelf (Ideal.Quotient.mk P s) = 1 := by
      rw [hqt]
      exact hbase
    change gRing x = y
    rw [show gRing x = qΦ (Ideal.Quotient.mk J p) *
        IsLocalization.Away.invSelf (Ideal.Quotient.mk P s) ^ n by
      dsimp only [gRing, x]
      exact Localization.awayLift_mk qΦ.toRingHom (Ideal.Quotient.mk J t)
        (Ideal.Quotient.mk J p) (IsLocalization.Away.invSelf (Ideal.Quotient.mk P s))
          hqbase n]
    rw [show qΦ (Ideal.Quotient.mk J p) = Φ p by rfl, hp]
    exact hy
  exact retainedPrime_hilbertPolynomial_natDegree_le_of_coefficientLocalization
    hJ htJ hJdim hP hs locMap hlocMap

/-- Affine received-line specialization of the arbitrary-polynomial retained-source dimension
bound. -/
theorem symbolicSource_prime_hilbertPolynomial_natDegree_le_of_agreements_of_exponent
    (center : E) (Q : DifferentialPolynomial E[X] r) (K k c τ : ℕ)
    (hτ : TaylorExponentSufficient r K τ)
    (hK : r < K) (hkK : k ≤ K) (hck : c ≤ k)
    (P : Ideal (SourceRing r E)) (hP : P.IsPrime)
    (hs : symbolicSourceSeparant center Q ∉ P)
    (hhigh : ∀ l : Fin K, k ≤ l.val →
      symbolicSourceNumerator center Q K l (τ := τ) ∈ P)
    (α : Fin c ↪ E) (f g : Fin c → E)
    (hcut : ∀ i,
      symbolicSourceAgreement center Q K (α i) (f i) (g i) (τ := τ) ∈ P) :
    (hilbertPolynomial P).natDegree ≤ k + 1 - c := by
  apply symbolicSource_prime_hilbertPolynomial_natDegree_le_of_polynomial_agreements_of_exponent
    center Q K k c τ hτ hK hkK hck P hP hs hhigh α
    (fun i ↦ Polynomial.C (f i) + Polynomial.X * Polynomial.C (g i))
  intro i
  simpa only [symbolicSourceAgreement, symbolicSourcePolynomialAgreement] using hcut i

/-- The actual retained source prime satisfies the joint coefficient-space hereditary budget,
unless its entire regular principal open belongs to the supplied persistent-graph locus.

This is the application premise for dimension-sensitive incidence with parameter `k + 1`: the
extra coordinate is the retained challenge. -/
theorem symbolicSource_dimensionSensitive_component_or_excluded_of_exponent
    (center : E) (Q : DifferentialPolynomial E[X] r) (K k n τ : ℕ)
    (hτ : TaylorExponentSufficient r K τ) (hK : r < K) (hkK : k ≤ K)
    (P : Ideal (SourceRing r E)) (hP : P.IsPrime)
    (hs : symbolicSourceSeparant center Q ∉ P)
    (hhigh : ∀ l : Fin K, k ≤ l.val →
      symbolicSourceNumerator center Q K l (τ := τ) ∈ P)
    (α : Fin n ↪ E) (f g : Fin n → E)
    (excluded : Set (Option (Fin (r + 1)) → E))
    (hterminal : k ≤ (cutsInIdeal P fun i ↦
      symbolicSourceAgreement center Q K (α i) (f i) (g i) (τ := τ)).card →
      principalOpenZeroLocus P (symbolicSourceSeparant center Q) ⊆ excluded) :
    (hilbertPolynomial P).natDegree ≤ k + 1 ∧
      ((cutsInIdeal P fun i ↦
          symbolicSourceAgreement center Q K (α i) (f i) (g i) (τ := τ)).card ≤
        k + 1 - (hilbertPolynomial P).natDegree ∨
       principalOpenZeroLocus P (symbolicSourceSeparant center Q) ⊆ excluded) := by
  classical
  let cuts : Fin n → MvPolynomial (Option (Fin (r + 1))) E := fun i ↦
    symbolicSourceAgreement center Q K (α i) (f i) (g i) (τ := τ)
  change (hilbertPolynomial P).natDegree ≤ k + 1 ∧
    ((cutsInIdeal P cuts).card ≤ k + 1 - (hilbertPolynomial P).natDegree ∨
      principalOpenZeroLocus P (symbolicSourceSeparant center Q) ⊆ excluded)
  let α0 : Fin 0 ↪ E := ⟨Fin.elim0, fun i ↦ Fin.elim0 i⟩
  let f0 : Fin 0 → E := Fin.elim0
  have hdim : (hilbertPolynomial P).natDegree ≤ k + 1 := by
    simpa only [Nat.sub_zero] using
      (symbolicSource_prime_hilbertPolynomial_natDegree_le_of_agreements_of_exponent
        center Q K k 0 τ hτ hK hkK (by omega) P hP hs hhigh α0 f0 f0
          (fun i ↦ Fin.elim0 i))
  refine ⟨hdim, ?_⟩
  by_cases hc : (cutsInIdeal P cuts).card ≤ k
  · let sample : Fin (cutsInIdeal P cuts).card ↪ Fin n :=
      ⟨fun j ↦ ((cutsInIdeal P cuts).equivFin.symm j).val,
        fun i j hij ↦ (cutsInIdeal P cuts).equivFin.symm.injective (Subtype.ext hij)⟩
    let α' : Fin (cutsInIdeal P cuts).card ↪ E :=
      ⟨fun j ↦ α (sample j), fun i j hij ↦ sample.injective (α.injective hij)⟩
    let f' : Fin (cutsInIdeal P cuts).card → E := fun j ↦ f (sample j)
    let g' : Fin (cutsInIdeal P cuts).card → E := fun j ↦ g (sample j)
    have hcuts (j : Fin (cutsInIdeal P cuts).card) :
        symbolicSourceAgreement center Q K (α' j) (f' j) (g' j) (τ := τ) ∈ P := by
      change cuts (sample j) ∈ P
      rw [← mem_cutsInIdeal]
      exact ((cutsInIdeal P cuts).equivFin.symm j).property
    have hd := symbolicSource_prime_hilbertPolynomial_natDegree_le_of_agreements_of_exponent
      center Q K k (cutsInIdeal P cuts).card τ hτ hK hkK hc P hP hs hhigh
        α' f' g' hcuts
    left
    omega
  · right
    apply hterminal
    change k ≤ (cutsInIdeal P cuts).card
    omega

/-- Hereditary joint coefficient-space budget for every actual retained source prime.
In dimensions at least two, all identically vanishing agreement cuts can be used in the
Vandermonde quotient.  If there were more than `k`, any chosen `k` of them would already force
dimension at most one. -/
theorem symbolicSourcePolynomial_dimensionSensitive_component_of_exponent
    (center : E) (Q : DifferentialPolynomial E[X] r) (K k n τ : ℕ)
    (hτ : TaylorExponentSufficient r K τ) (hK : r < K) (hkK : k ≤ K)
    (P : Ideal (SourceRing r E)) (hP : P.IsPrime)
    (hs : symbolicSourceSeparant center Q ∉ P)
    (hhigh : ∀ l : Fin K, k ≤ l.val →
      symbolicSourceNumerator center Q K l (τ := τ) ∈ P)
    (α : Fin n ↪ E) (received : Fin n → E[X]) :
    let cuts : Fin n → MvPolynomial (Option (Fin (r + 1))) E := fun i ↦
      symbolicSourcePolynomialAgreement center Q K (α i) (received i) (τ := τ)
    (hilbertPolynomial P).natDegree ≤ k + 1 ∧
      (1 < (hilbertPolynomial P).natDegree →
        (cutsInIdeal P cuts).card ≤ k + 1 - (hilbertPolynomial P).natDegree) := by
  classical
  dsimp only
  let cuts : Fin n → MvPolynomial (Option (Fin (r + 1))) E := fun i ↦
    symbolicSourcePolynomialAgreement center Q K (α i) (received i) (τ := τ)
  have hpartial (indices : Finset (Fin n)) (hcard : indices.card ≤ k)
      (hsub : indices ⊆ cutsInIdeal P cuts) :
      (hilbertPolynomial P).natDegree ≤ k + 1 - indices.card := by
    let sample : Fin indices.card ↪ Fin n :=
      ⟨fun j ↦ (indices.equivFin.symm j).val,
        fun i j hij ↦ indices.equivFin.symm.injective (Subtype.ext hij)⟩
    let α' : Fin indices.card ↪ E :=
      ⟨fun j ↦ α (sample j), fun i j hij ↦ sample.injective (α.injective hij)⟩
    let received' : Fin indices.card → E[X] := fun j ↦ received (sample j)
    apply
      symbolicSource_prime_hilbertPolynomial_natDegree_le_of_polynomial_agreements_of_exponent
        center Q K k indices.card τ hτ hK hkK hcard P hP hs hhigh α' received'
    intro j
    change cuts (sample j) ∈ P
    rw [← mem_cutsInIdeal]
    exact hsub (indices.equivFin.symm j).property
  have hdim : (hilbertPolynomial P).natDegree ≤ k + 1 := by
    simpa using hpartial ∅ (by simp) (by simp)
  refine ⟨hdim, fun hd ↦ ?_⟩
  let Bad := cutsInIdeal P cuts
  change Bad.card ≤ k + 1 - (hilbertPolynomial P).natDegree
  by_cases hBadk : Bad.card ≤ k
  · have hbound := hpartial Bad hBadk le_rfl
    omega
  · have hkBad : k ≤ Bad.card := by omega
    obtain ⟨indices, hindices, hcard⟩ := Finset.exists_subset_card_eq hkBad
    have hle := hpartial indices (by omega) hindices
    rw [hcard] at hle
    omega

/-- Affine received-line specialization of the arbitrary-polynomial hereditary component
bound. -/
theorem symbolicSource_dimensionSensitive_component_of_exponent
    (center : E) (Q : DifferentialPolynomial E[X] r) (K k n τ : ℕ)
    (hτ : TaylorExponentSufficient r K τ) (hK : r < K) (hkK : k ≤ K)
    (P : Ideal (SourceRing r E)) (hP : P.IsPrime)
    (hs : symbolicSourceSeparant center Q ∉ P)
    (hhigh : ∀ l : Fin K, k ≤ l.val →
      symbolicSourceNumerator center Q K l (τ := τ) ∈ P)
    (α : Fin n ↪ E) (f g : Fin n → E) :
    let cuts : Fin n → MvPolynomial (Option (Fin (r + 1))) E := fun i ↦
      symbolicSourceAgreement center Q K (α i) (f i) (g i) (τ := τ)
    (hilbertPolynomial P).natDegree ≤ k + 1 ∧
      (1 < (hilbertPolynomial P).natDegree →
        (cutsInIdeal P cuts).card ≤ k + 1 - (hilbertPolynomial P).natDegree) := by
  simpa only [symbolicSourceAgreement, symbolicSourcePolynomialAgreement] using
    (symbolicSourcePolynomial_dimensionSensitive_component_of_exponent
      center Q K k n τ hτ hK hkK P hP hs hhigh α
        (fun i ↦ Polynomial.C (f i) + Polynomial.X * Polynomial.C (g i)))

/-- Order-one, degree-one-message specialization.  This explicit caller checks the boundary
`r = k = 1`: every two-dimensional retained source prime contains no agreement cut identically,
while all positive-dimensional retained primes have dimension at most two. -/
theorem firstOrder_symbolicSource_dimensionSensitive_component_of_exponent
    (center : E) (Q : DifferentialPolynomial E[X] 1) (K n τ : ℕ)
    (hτ : TaylorExponentSufficient 1 K τ) (hK : 1 < K)
    (P : Ideal (SourceRing 1 E)) (hP : P.IsPrime)
    (hs : symbolicSourceSeparant center Q ∉ P)
    (hhigh : ∀ l : Fin K, 1 ≤ l.val →
      symbolicSourceNumerator center Q K l (τ := τ) ∈ P)
    (α : Fin n ↪ E) (f g : Fin n → E) :
    let cuts : Fin n → MvPolynomial (Option (Fin 2)) E := fun i ↦
      symbolicSourceAgreement center Q K (α i) (f i) (g i) (τ := τ)
    (hilbertPolynomial P).natDegree ≤ 2 ∧
      (1 < (hilbertPolynomial P).natDegree → (cutsInIdeal P cuts).card = 0) := by
  dsimp only
  have h := symbolicSource_dimensionSensitive_component_of_exponent center Q K 1 n τ hτ hK
    (by omega) P hP hs hhigh α f g
  rcases h with ⟨hdim, hcuts⟩
  refine ⟨by simpa using hdim, fun hd ↦ ?_⟩
  have hbound := hcuts hd
  have hdimEq : (hilbertPolynomial P).natDegree = 2 := by omega
  rw [hdimEq] at hbound
  simpa using hbound

/-- The high-agreement part of one retained source component, outside the terminal graph locus,
is finite and has the hybrid joint incidence bound.  The first factor uses the graph-recognition
threshold `L`; when the component has dimension two, the second factor is the direct
coefficient-space ratio at threshold `k`. -/
theorem finite_symbolicSource_agreementLocus_off_excluded_and_ncard_le_hybrid_of_exponent
    [IsAlgClosed E]
    (center : E) (Q : DifferentialPolynomial E[X] r) (K k n τ L A b : ℕ)
    (hτ : TaylorExponentSufficient r K τ) (hK : r < K) (hkK : k ≤ K)
    (hLA : L ≤ A) (hkA : k ≤ A) (hAn : A ≤ n)
    (P : Ideal (SourceRing r E)) (hP : P.IsPrime)
    (hs : symbolicSourceSeparant center Q ∉ P)
    (hhigh : ∀ l : Fin K, k ≤ l.val →
      symbolicSourceNumerator center Q K l (τ := τ) ∈ P)
    (α : Fin n ↪ E) (f g : Fin n → E)
    (hdeg : ∀ i, (symbolicSourceAgreement center Q K (α i) (f i) (g i)
      (τ := τ)).totalDegree ≤ b)
    (excluded : Set (Option (Fin (r + 1)) → E))
    (hterminal : ∀ J : Ideal (SourceRing r E),
      P ≤ J → J.IsPrime → symbolicSourceSeparant center Q ∉ J →
      0 < (hilbertPolynomial J).natDegree →
      L ≤ (cutsInIdeal J fun i ↦
        symbolicSourceAgreement center Q K (α i) (f i) (g i) (τ := τ)).card →
      principalOpenZeroLocus J (symbolicSourceSeparant center Q) ⊆ excluded) :
    let cuts : Fin n → MvPolynomial (Option (Fin (r + 1))) E := fun i ↦
      symbolicSourceAgreement center Q K (α i) (f i) (g i) (τ := τ)
    let T := {x : Option (Fin (r + 1)) → E |
      x ∈ principalOpenZeroLocus P (symbolicSourceSeparant center Q) ∧ x ∉ excluded ∧
        A ≤ (agreementIndices cuts x).card}
    T.Finite ∧ (T.ncard : ℚ) ≤ affineDegree P *
      hybridDimensionSensitiveIncidenceProduct n A L k b
        (hilbertPolynomial P).natDegree := by
  classical
  dsimp only
  let cuts : Fin n → MvPolynomial (Option (Fin (r + 1))) E := fun i ↦
    symbolicSourceAgreement center Q K (α i) (f i) (g i) (τ := τ)
  apply finite_agreementLocus_off_excluded_and_ncard_le_hybrid hP hs cuts hdeg
    hLA hkA hAn excluded
  · intro J hPJ hJ hsJ hdJ
    exact symbolicSource_dimensionSensitive_component_of_exponent center Q K k n τ hτ hK
      hkK J hJ hsJ (fun l hl ↦ hPJ (hhigh l hl)) α f g
  · intro J hPJ hJ hsJ hdJ hcutsJ
    exact hterminal J hPJ hJ hsJ hdJ hcutsJ

/-- A prime containing the nonzero initial source equation has dimension at most `r + 1`.
This applies after any further retained high-coefficient or agreement cuts. -/
theorem symbolicSource_prime_hilbertPolynomial_natDegree_le
    (center : E) (Q : DifferentialPolynomial E[X] r)
    (P : Ideal (MvPolynomial (Option (Fin (r + 1))) E))
    (hP : P.IsPrime) (hinit0 : symbolicSourceInitialEquation center Q ≠ 0)
    (hinit : symbolicSourceInitialEquation center Q ∈ P) :
    (hilbertPolynomial P).natDegree ≤ r + 1 := by
  let I : Ideal (MvPolynomial (Option (Fin (r + 1))) E) :=
    Ideal.span {symbolicSourceInitialEquation center Q}
  have hIP : I ≤ P := by
    rw [Ideal.span_le]
    simpa only [Set.singleton_subset_iff]
  have hIproper : I ≠ ⊤ := by
    intro htop
    apply hP.ne_top
    apply top_unique
    rw [← htop]
    exact hIP
  have hIdegree : (hilbertPolynomial I).natDegree + 1 = r + 2 := by
    simpa only [I, Finite.card_option, Nat.card_fin] using
      hilbertPolynomial_span_singleton_natDegree_add_one hinit0 hIproper
  have hdegree : (hilbertPolynomial P).natDegree ≤ (hilbertPolynomial I).natDegree :=
    (hilbertPolynomial_degree_and_leadingCoeff_antitone hIP hP.ne_top).1
  omega


end ReedSolomon

/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
  ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.Symbolic.TaylorWitnessEmbedding
public import
  ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.Geometry.SolutionEmbedding
public import
  ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.Geometry.HighCutGeometry
public import ArkLib.ToMathlib.AlgebraicGeometry.Incidence.ProductBounds
public import ArkLib.ToMathlib.AlgebraicGeometry.Incidence.EvaluationDimension
public import ArkLib.ToMathlib.AlgebraicGeometry.PrincipalCut.Polynomial
public import Mathlib.RingTheory.Localization.FractionRing
/-!
# Dimension-sensitive counting on regular Taylor charts

On the separant principal open, the first reconstructed coefficients generate the localized
chart. Vandermonde elimination supplies the hereditary dimension budget needed by the
fixed-word incidence theorem. This module belongs to the reusable HiddenDerivative geometry
layer and has no mutual-agreement dependency.
-/

@[expose] public section

open PolynomialDifferential

noncomputable section

namespace ReedSolomon.HiddenDerivative

open Polynomial MvPolynomial AffineHilbert

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


/-- Product-form incidence for a finite set of regular high-cut jets.  The nonlinear Taylor cuts
are charged through the retained-family Bezout potential, while agreement cuts contribute the
dimension-sensitive evaluation product. -/
theorem finite_regularHighCutJets_card_le_dimensionSensitive_of_exponent
    [IsAlgClosed E]
    (center : E) (Q : DifferentialPolynomial E r) (K k τ : ℕ)
    (hτ : TaylorExponentSufficient r K τ) (hK : r < K) (hkK : k ≤ K)
    (hsep : initialJetSeparant center Q ≠ 0)
    (hv : 0 < Q.weightedTotalDegree (fun i ↦ i.elim (0 : ℕ) (fun _ ↦ 1)))
    {n A : ℕ} (domain : Fin n ↪ E) (received : Fin n → E)
    (hkA : k ≤ A) (hAn : A ≤ n)
    (hproduct : ∀ d ≤ r, dimensionSensitiveIncidenceProduct n A k 1 d ≤
      dimensionSensitiveIncidenceProduct n A k 1 r)
    (S : Finset (Fin (r + 1) → E))
    (hS : ∀ jet ∈ S,
      aeval jet (initialJetEquation center Q) = 0 ∧
      aeval jet (initialJetSeparant center Q) ≠ 0 ∧
      ∀ l : {l : Fin K // k ≤ l.val},
        aeval jet (commonTaylorNumerator center Q K l.val (τ := τ)) = 0)
    (hA : ∀ jet ∈ S, A ≤ (agreementIndices
      (fun i ↦ taylorAgreementEquation center Q K (domain i) (received i) (τ := τ))
        jet).card) :
    (S.card : ℚ) ≤
      (Q.weightedTotalDegree (fun i ↦ i.elim (0 : ℕ) (fun _ ↦ 1)) : ℕ) *
        (rationalTaylorCutDegreeBound Q K (τ := τ) : ℚ) ^ r *
          dimensionSensitiveIncidenceProduct n A k 1 r := by
  classical
  let B := rationalTaylorCutDegreeBound Q K (τ := τ)
  let T := highTaylorPrimeFamily center Q K k (τ := τ)
  let cuts : Fin n → MvPolynomial (Fin (r + 1)) E := fun i ↦
    taylorAgreementEquation center Q K (domain i) (received i) (τ := τ)
  have hinit : initialJetEquation center Q ≠ 0 :=
    initialJetEquation_ne_zero_of_separant_ne_zero center Q hsep
  have hspec := highTaylorPrimeFamily_spec (F := E) (E := E) center Q K k (τ := τ)
  have hcoverNat : S.card ≤ ∑ P ∈ T, (componentPoints S P).card := by
    calc
      S.card ≤ (T.biUnion fun P ↦ componentPoints S P).card := by
        apply Finset.card_le_card
        intro jet hjet
        obtain ⟨P, hPT, hjetP⟩ := hspec.2 jet
          (hS jet hjet).1 (hS jet hjet).2.1 (hS jet hjet).2.2
        exact Finset.mem_biUnion.mpr ⟨P, hPT, by
          rw [mem_componentPoints]
          exact ⟨hjet, hjetP⟩⟩
      _ ≤ ∑ P ∈ T, (componentPoints S P).card := Finset.card_biUnion_le
  have hcomponent : ∀ P ∈ T, ((componentPoints S P).card : ℚ) ≤
      affineDegree P * (B : ℚ) ^ (hilbertPolynomial P).natDegree *
        dimensionSensitiveIncidenceProduct n A k 1 r := by
    intro P hPT
    have hPspec := hspec.1 P hPT
    have hbound := affineAgreementIncidence_bound_dimensionSensitive hPspec.1 hPspec.2.1
      cuts (fun i ↦ totalDegree_taylorAgreementEquation_le_of_exponent
        center Q hv K τ hτ _ _) hkA hAn
      (fun J hPJ hJ hsJ hdJ ↦ chart_dimensionSensitive_component_of_exponent
        center Q K k n τ hτ hK hkK J hJ hsJ
          (fun l hl ↦ hPJ (hPspec.2.2 (by
            rw [highTaylorCutsIdeal]
            exact Ideal.subset_span ⟨⟨l, hl⟩, rfl⟩))) domain received hdJ)
      (componentPoints S P)
      (fun jet hjet ↦ by
        rw [mem_componentPoints] at hjet
        exact ⟨hjet.2, (hS jet hjet.1).2.1⟩)
      (fun jet hjet ↦ by rw [mem_componentPoints] at hjet; exact hA jet hjet.1)
    refine hbound.trans ?_
    rw [dimensionSensitiveIncidenceProduct_eq_pow_mul]
    calc
      affineDegree P * ((B : ℚ) ^ (hilbertPolynomial P).natDegree *
          dimensionSensitiveIncidenceProduct n A k 1 (hilbertPolynomial P).natDegree) =
        (affineDegree P * (B : ℚ) ^ (hilbertPolynomial P).natDegree) *
          dimensionSensitiveIncidenceProduct n A k 1 (hilbertPolynomial P).natDegree := by ring
      _ ≤ (affineDegree P * (B : ℚ) ^ (hilbertPolynomial P).natDegree) *
          dimensionSensitiveIncidenceProduct n A k 1 r :=
        mul_le_mul_of_nonneg_left (hproduct _
          (highTaylorPrimeFamily_hilbertPolynomial_natDegree_le
            center Q K k (τ := τ) hinit hPT))
          (mul_nonneg (affineDegree_nonneg P) (by positivity))
      _ = affineDegree P * (B : ℚ) ^ (hilbertPolynomial P).natDegree *
          dimensionSensitiveIncidenceProduct n A k 1 r := rfl
  have hpotential := sum_highTaylorPrimeFamily_affineDegree_mul_pow_le_of_exponent
    center Q hsep hv K k τ hτ
  calc
    (S.card : ℚ) ≤ ∑ P ∈ T, ((componentPoints S P).card : ℚ) := by
      exact_mod_cast hcoverNat
    _ ≤ ∑ P ∈ T, affineDegree P * (B : ℚ) ^ (hilbertPolynomial P).natDegree *
        dimensionSensitiveIncidenceProduct n A k 1 r := Finset.sum_le_sum hcomponent
    _ = (∑ P ∈ T, affineDegree P * (B : ℚ) ^ (hilbertPolynomial P).natDegree) *
        dimensionSensitiveIncidenceProduct n A k 1 r := by rw [Finset.sum_mul]
    _ ≤ ((Q.weightedTotalDegree (fun i ↦ i.elim (0 : ℕ) (fun _ ↦ 1)) : ℕ) *
        (B : ℚ) ^ r) * dimensionSensitiveIncidenceProduct n A k 1 r :=
      mul_le_mul_of_nonneg_right hpotential
        (dimensionSensitiveIncidenceProduct_nonneg n A k 1 r)
    _ = _ := rfl

open Classical in
/-- A finite family of regular degree-`< k` differential roots over an arbitrary field obeys
the dimension-sensitive fixed-word product.  The Taylor numerator degree is charged once through
the image/component potential, separately from the linear evaluation cuts. -/
theorem finite_regular_solutions_card_le_dimensionSensitive
    {F : Type*} [Field F] {r : ℕ}
    (Q : DifferentialPolynomial F r) (K k : ℕ) (hK : r < K) (hkK : k ≤ K)
    (hv : 0 < Q.weightedTotalDegree (fun i ↦ i.elim (0 : ℕ) (fun _ ↦ 1)))
    {n A : ℕ} (domain : Fin n ↪ F) (received : Fin n → F)
    (hkA : k ≤ A) (hAn : A ≤ n)
    (S : Finset (Polynomial F))
    (hdegree : ∀ P ∈ S, P.degree < k)
    (hsol : ∀ P ∈ S, differentialSpecialization Q P = 0)
    (hsep : ∀ P ∈ S, differentialSpecialization (separant Q (Fin.last r)) P ≠ 0)
    (hbin : ∀ i, r < i → i < K → (i.choose r : F) ≠ 0)
    (hagree : ∀ P ∈ S,
      A ≤ (Finset.univ.filter fun i ↦ P.eval (domain i) = received i).card) :
    (S.card : ℚ) ≤
      (Q.weightedTotalDegree (fun i ↦ i.elim (0 : ℕ) (fun _ ↦ 1)) : ℕ) *
        (rationalTaylorCutDegreeBound Q K : ℚ) ^ r *
          dimensionSensitiveIncidenceProduct n A k 1 r := by
  classical
  let E := AlgebraicClosure F
  let f := algebraMap F E
  let QE := MvPolynomial.map f Q
  obtain ⟨center, J, hcard, hJ⟩ := exists_regular_solution_jet_family
    f Q K k hkK S domain received hdegree hsol hsep hbin hagree
  by_cases hJempty : J = ∅
  · have hScard : S.card = 0 := by simpa [hJempty] using hcard.symm
    rw [hScard, Nat.cast_zero]
    exact mul_nonneg
      (mul_nonneg (Nat.cast_nonneg _) (by positivity))
      (dimensionSensitiveIncidenceProduct_nonneg n A k 1 r)
  have hsepE : initialJetSeparant center QE ≠ 0 := by
    obtain ⟨jet, hjet⟩ := Finset.nonempty_iff_ne_empty.mpr hJempty
    intro hz
    exact (hJ jet hjet).2.1 (by rw [hz, map_zero])
  have hvE : 0 < QE.weightedTotalDegree (fun i ↦ i.elim (0 : ℕ) (fun _ ↦ 1)) := by
    rwa [totalJetDegree_map_eq f Q]
  let domainE : Fin n ↪ E := domain.trans ⟨f, f.injective⟩
  have hcount := finite_regularHighCutJets_card_le_dimensionSensitive_of_exponent
    center QE K k (2 * K) (taylorExponentSufficient_two_mul r K) hK hkK hsepE hvE
    domainE (fun i ↦ f (received i)) hkA hAn
    (fun d hd ↦ dimensionSensitiveIncidenceProduct_mono_dimension
      n A k 1 d r hAn Nat.zero_lt_one hd) J
    (fun jet hjet ↦ ⟨(hJ jet hjet).1, (hJ jet hjet).2.1,
      fun l ↦ (hJ jet hjet).2.2.1 l.val l.property⟩)
    (fun jet hjet ↦ (hJ jet hjet).2.2.2)
  rw [hcard] at hcount
  simpa only [QE, rationalTaylorCutDegreeBound, totalJetDegree_map_eq f Q] using hcount

end ReedSolomon.HiddenDerivative

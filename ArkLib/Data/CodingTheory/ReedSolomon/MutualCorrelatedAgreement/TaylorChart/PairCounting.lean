/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.TaylorChart.ComponentRecognition
public import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.Pairs.Family
public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.Geometry.HighCutGeometry
/-!
# Counting admissible correlated pairs in a Taylor chart

An admissible pair carries literal identities along its affine initial-jet graph, including
every reconstructed Taylor coefficient. One ordinary extension-field scalar retains all
separants and separates a finite pair family, so the existing high-cut jet bound applies.
-/

@[expose] public section

open PolynomialDifferential


noncomputable section

namespace ReedSolomon

open Polynomial MvPolynomial HiddenDerivative AffineHilbert
open scoped BigOperators

variable {F E : Type*} [Field F] [Field E] {n r : ℕ}

/-- Restriction to the affine initial-jet graph of a base-field polynomial pair. -/
def chartPairPullback (iota : F →+* E) (center : E) (pair : F[X] × F[X]) :
    MvPolynomial (Option (Fin (r + 1))) E →ₐ[E] E[X] :=
  affineGraphPullback (polynomialJet center (pair.1.map iota))
    (polynomialJet center (pair.2.map iota))

/-- The affine initial jet at one ordinary scalar. -/
def chartPairJet (iota : F →+* E) (center z : E) (pair : F[X] × F[X]) :
    Fin (r + 1) → E :=
  fun j ↦ polynomialJet center (pair.1.map iota) j +
    z * polynomialJet center (pair.2.map iota) j

/-- Admissibility consists of explicit degree, agreement, and polynomial graph identities. -/
structure IsAdmissibleChartPair [DecidableEq F] (domain : Fin n ↪ F) (f g : Fin n → F)
    (iota : F →+* E) (center : E) (Q : DifferentialPolynomial E[X] r)
    (K k L : ℕ) (pair : F[X] × F[X]) : Prop where
  degree_left : pair.1.degree < k
  degree_right : pair.2.degree < k
  common : L ≤ (commonPolynomialAgreementSet domain f g pair.1 pair.2).card
  initial : chartPairPullback iota center pair (symbolicSourceInitialEquation center Q) = 0
  high : ∀ l : Fin K, k ≤ l.val →
    chartPairPullback iota center pair (symbolicSourceNumerator center Q K l) = 0
  regular : chartPairPullback iota center pair (symbolicSourceSeparant center Q) ≠ 0
  reconstruction : ∀ l : Fin K,
    chartPairPullback iota center pair
      (symbolicSourceReconstructionError center Q K (pair.1.map iota) (pair.2.map iota) l) = 0

/-- Graph restriction of a retained symbolic polynomial specializes its coefficients first. -/
theorem eval_chartPairPullback_symbolic (iota : F →+* E) (center z : E)
    (pair : F[X] × F[X]) (p : MvPolynomial (Fin (r + 1)) E[X]) :
    (chartPairPullback iota center pair ((optionEquivRight E _).symm p)).eval z =
      aeval (chartPairJet iota center z pair) (MvPolynomial.map (Polynomial.evalRingHom z) p) := by
  rw [chartPairPullback, eval_affineGraphPullback, aeval_optionEquivRight_symm]
  rfl

/-- A specialized correlated pair retains the original message-degree bound. -/
theorem degree_correlatedPairSpecialization_lt (iota : F →+* E) (z : E)
    (pair : F[X] × F[X]) {k : ℕ} (h₀ : pair.1.degree < k) (h₁ : pair.2.degree < k) :
    (correlatedPairSpecialization iota z pair).degree < k := by
  apply (Polynomial.degree_add_le _ _).trans_lt
  exact max_lt (Polynomial.degree_map_le.trans_lt h₀)
    ((show (Polynomial.C z * pair.2.map iota).degree ≤ (pair.2.map iota).degree by
      simpa only [Polynomial.smul_eq_C_mul] using Polynomial.degree_smul_le z
        (pair.2.map iota)).trans_lt (Polynomial.degree_map_le.trans_lt h₁))

/-- The finite Taylor coefficients of a specialized pair are affine in the scalar. -/
theorem coeff_taylor_correlatedPairSpecialization (iota : F →+* E) (center z : E)
    (pair : F[X] × F[X]) (l : ℕ) :
    (Polynomial.taylor center (correlatedPairSpecialization iota z pair)).coeff l =
      (Polynomial.taylor center (pair.1.map iota)).coeff l +
        z * (Polynomial.taylor center (pair.2.map iota)).coeff l := by
  rw [correlatedPairSpecialization, ← Polynomial.smul_eq_C_mul, map_add, map_smul]
  simp only [Polynomial.coeff_add, Polynomial.coeff_smul, smul_eq_mul]

/-- Evaluation of all cleared reconstruction identities identifies the actual polynomial. -/
theorem IsAdmissibleChartPair.specialize [DecidableEq F]
    {domain : Fin n ↪ F} {f g : Fin n → F} {iota : F →+* E} {center : E}
    {Q : DifferentialPolynomial E[X] r} {K k L : ℕ} {pair : F[X] × F[X]}
    (hp : IsAdmissibleChartPair domain f g iota center Q K k L pair)
    (hkK : k ≤ K) (z : E)
    (hz : (chartPairPullback iota center pair (symbolicSourceSeparant center Q)).eval z ≠ 0) :
    let Qz := MvPolynomial.map (Polynomial.evalRingHom z) Q
    let jet := chartPairJet iota center z pair
    aeval jet (initialJetEquation center Qz) = 0 ∧
      aeval jet (initialJetSeparant center Qz) ≠ 0 ∧
      (∀ l : Fin K, k ≤ l.val → aeval jet (commonTaylorNumerator center Qz K l) = 0) ∧
      rationalTaylorPolynomial center Qz K jet = correlatedPairSpecialization iota z pair := by
  let Qz := MvPolynomial.map (Polynomial.evalRingHom z) Q
  let jet : Fin (r + 1) → E := chartPairJet iota center z pair
  have hsep : aeval jet (initialJetSeparant center Qz) ≠ 0 := by
    rw [symbolicSourceSeparant, eval_chartPairPullback_symbolic] at hz
    rw [map_initialJetSeparantOver,
      show (Polynomial.evalRingHom z) (Polynomial.C center) = center from Polynomial.eval_C] at hz
    exact hz
  have hinit : aeval jet (initialJetEquation center Qz) = 0 := by
    have h := congrArg (fun p : E[X] ↦ p.eval z) hp.initial
    rw [symbolicSourceInitialEquation, eval_chartPairPullback_symbolic] at h
    rw [map_initialJetEquationOver,
      show (Polynomial.evalRingHom z) (Polynomial.C center) = center from Polynomial.eval_C,
      Polynomial.eval_zero] at h
    exact h
  have hhigh : ∀ l : Fin K, k ≤ l.val →
      aeval jet (commonTaylorNumerator center Qz K l) = 0 := by
    intro l hl
    have h := congrArg (fun p : E[X] ↦ p.eval z) (hp.high l hl)
    rw [symbolicSourceNumerator, eval_chartPairPullback_symbolic] at h
    simpa only [eval_commonTaylorNumeratorOver, Polynomial.eval_zero] using h
  refine ⟨hinit, hsep, hhigh, ?_⟩
  apply Polynomial.taylor_injective center
  ext l
  by_cases hl : l < K
  · have h := congrArg (fun p : E[X] ↦ p.eval z) (hp.reconstruction ⟨l, hl⟩)
    rw [chartPairPullback, eval_affineGraphPullback] at h
    simp only [symbolicSourceReconstructionError, map_sub, map_mul, map_pow, map_add,
      MvPolynomial.aeval_C, MvPolynomial.aeval_X, Algebra.algebraMap_self, RingHom.id_apply,
      symbolicSourceNumerator, symbolicSourceSeparant, aeval_optionEquivRight_symm,
      affineGraphPoint, Option.elim_none, Option.elim_some, Polynomial.eval_zero] at h
    change aeval jet (MvPolynomial.map (Polynomial.evalRingHom z)
        (commonTaylorNumeratorOver (F := E) (Polynomial.C center) Q K ⟨l, hl⟩)) -
      (aeval jet (MvPolynomial.map (Polynomial.evalRingHom z)
        (initialJetSeparantOver (Polynomial.C center) Q))) ^ (2 * K) *
      ((Polynomial.taylor center (pair.1.map iota)).coeff l +
        z * (Polynomial.taylor center (pair.2.map iota)).coeff l) = 0 at h
    rw [eval_commonTaylorNumeratorOver, map_initialJetSeparantOver,
      show (Polynomial.evalRingHom z) (Polynomial.C center) = center from Polynomial.eval_C] at h
    change aeval jet (commonTaylorNumerator center Qz K ⟨l, hl⟩) -
      (aeval jet (initialJetSeparant center Qz)) ^ (2 * K) * _ = 0 at h
    rw [aeval_commonTaylorNumerator _ _ _ _ _ hsep] at h
    have he := (mul_eq_zero.mp (show (aeval jet (initialJetSeparant center Qz)) ^ (2*K) *
        (rationalTaylorCoefficient center Qz jet l -
          ((Polynomial.taylor center (pair.1.map iota)).coeff l +
            z * (Polynomial.taylor center (pair.2.map iota)).coeff l)) = 0 by
      linear_combination h)).resolve_left (pow_ne_zero _ hsep)
    rw [rationalTaylorPolynomial, coeff_taylor_centeredCoefficientPrefix, if_pos hl,
      coeff_taylor_correlatedPairSpecialization]
    exact sub_eq_zero.mp he
  · have hleft := degree_rationalTaylorPolynomial_lt_of_high_cuts center Qz K k jet hsep hhigh
    have hright := degree_correlatedPairSpecialization_lt iota z pair hp.degree_left hp.degree_right
    have hkl : (k : WithBot ℕ) ≤ l := by exact_mod_cast (show k ≤ l by omega)
    rw [Polynomial.coeff_eq_zero_of_degree_lt (by
        simpa only [Polynomial.degree_taylor] using hleft.trans_le hkl),
      Polynomial.coeff_eq_zero_of_degree_lt (by
        simpa only [Polynomial.degree_taylor] using hright.trans_le hkl)]

private theorem jetDegree_pos_of_initialSeparant_ne_zero (center : E)
    (Q : DifferentialPolynomial E r) (hS : initialJetSeparant center Q ≠ 0) :
    0 < Q.weightedTotalDegree (fun i ↦ i.elim 0 (fun _ ↦ 1)) := by
  by_contra! h
  have hdeg : (initialJetEquation center Q).totalDegree = 0 :=
    Nat.eq_zero_of_le_zero ((totalDegree_initialJetEquation_le center Q).trans h)
  have hC := totalDegree_eq_zero_iff_eq_C.mp hdeg
  have hd := pderiv_initialJetEquation center Q (Fin.last r)
  rw [hC, pderiv_C] at hd
  exact hS hd.symm

/-- A finite family of explicit admissible pair graphs satisfies the sharp ordinary-chart
bound at one common regular scalar. No full differential-solution premise is assumed. -/
theorem admissibleChartPairs_card_le [DecidableEq F] [IsAlgClosed E]
    (domain : Fin n ↪ F) (f g : Fin n → F) (iota : F →+* E)
    (center : E) (Q : DifferentialPolynomial E[X] r) (K k L v : ℕ)
    (hK : r < K) (hkK : k ≤ K) (hk : 0 < k) (hkL : k ≤ L) (hLn : L ≤ n)
    (hjet : Q.weightedTotalDegree (fun i ↦ i.elim 0 (fun _ ↦ 1)) ≤ v)
    (pairs : Finset (F[X] × F[X]))
    (hpairs : ∀ pair ∈ pairs, IsAdmissibleChartPair domain f g iota center Q K k L pair) :
    (pairs.card : ℚ) ≤ (v : ℚ) *
      ((((n * (1 + 2 * K * (v - 1)) : ℕ) : ℚ) / ((L - k + 1 : ℕ) : ℚ)) ^ r) := by
  classical
  by_cases hempty : pairs = ∅
  · subst pairs
    simp only [Finset.card_empty, Nat.cast_zero]
    positivity
  let aux := pairs.image fun pair ↦
    chartPairPullback iota center pair (symbolicSourceSeparant center Q)
  obtain ⟨z, _, hinj, havoid⟩ := exists_correlatedPairSpecialization_injOn_avoiding_roots
    iota pairs ∅ aux (by
      intro R hR
      obtain ⟨pair, hp, rfl⟩ := Finset.mem_image.mp hR
      exact (hpairs pair hp).regular)
  let Qz := MvPolynomial.map (Polynomial.evalRingHom z) Q
  let jets : Finset (Fin (r + 1) → E) := pairs.image (chartPairJet iota center z)
  have hspec (pair : F[X] × F[X]) (hp : pair ∈ pairs) :=
    (hpairs pair hp).specialize hkK z
      (havoid _ (Finset.mem_image.mpr ⟨pair, hp, rfl⟩))
  have hjetinj : Set.InjOn (chartPairJet (r := r) iota center z) (↑pairs) := by
    intro p hp q hq heq
    apply hinj hp hq
    rw [← (hspec p hp).2.2.2, ← (hspec q hq).2.2.2, heq]
  have hcard : jets.card = pairs.card := Finset.card_image_of_injOn hjetinj
  obtain ⟨pair₀, hp₀⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
  have hsep : initialJetSeparant center Qz ≠ 0 := by
    intro hz
    exact (hspec pair₀ hp₀).2.1 (by rw [hz]; simp)
  have hvz := jetDegree_pos_of_initialSeparant_ne_zero center Qz hsep
  let domainE : Fin n ↪ E := ⟨fun i ↦ iota (domain i), iota.injective.comp domain.injective⟩
  let received : Fin n → E := fun i ↦ iota (f i) + z * iota (g i)
  have hbound := finite_regularHighCutJets_card_le center Qz K k hK hsep hvz
    domainE received hk hkL hLn jets (by
      intro jet hj
      obtain ⟨pair, hp, rfl⟩ := Finset.mem_image.mp hj
      exact ⟨(hspec pair hp).1, (hspec pair hp).2.1,
        fun l ↦ (hspec pair hp).2.2.1 l.val l.property⟩) (by
      intro jet hj
      obtain ⟨pair, hp, rfl⟩ := Finset.mem_image.mp hj
      apply (hpairs pair hp).common.trans
      apply Finset.card_le_card
      intro i hi
      rw [mem_agreementIndices, taylorAgreementEquation_eq_zero_iff _ _ _ _
        (hspec pair hp).2.1, (hspec pair hp).2.2.2]
      have hi' : pair.1.eval (domain i) = f i ∧ pair.2.eval (domain i) = g i := by
        simpa only [commonPolynomialAgreementSet, Finset.mem_filter, Finset.mem_univ,
          true_and] using hi
      change (correlatedPairSpecialization iota z pair).eval (iota (domain i)) =
        iota (f i) + z * iota (g i)
      simp only [correlatedPairSpecialization, Polynomial.eval_add,
        Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_map_apply, hi'.1, hi'.2])
  rw [hcard] at hbound
  apply hbound.trans
  have hvle : Qz.weightedTotalDegree (fun i ↦ i.elim 0 (fun _ ↦ 1)) ≤ v := by
    apply Finset.sup_le_iff.mpr
    intro m hm
    exact (le_weightedTotalDegree _
      (support_map_subset (Polynomial.evalRingHom z) Q hm)).trans hjet
  have hB : rationalTaylorCutDegreeBound Qz K ≤ 1 + 2 * K * (v - 1) := by
    unfold rationalTaylorCutDegreeBound
    exact Nat.add_le_add_left (Nat.mul_le_mul_left _ (Nat.sub_le_sub_right hvle 1)) 1
  apply mul_le_mul
  · exact_mod_cast hvle
  · apply pow_le_pow_left₀ (by positivity)
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact_mod_cast Nat.mul_le_mul_left n hB
  · positivity
  · positivity

/-- The explicit finite sample-pair family filtered by the chart identities. -/
def admissibleChartPairFamily [DecidableEq F]
    (domain : Fin n ↪ F) (f g : Fin n → F) (iota : F →+* E)
    (center : E) (Q : DifferentialPolynomial E[X] r) (K k L : ℕ) :
    Finset (F[X] × F[X]) := by
  classical
  exact (correlatedPairFamily domain f g k).filter
    (IsAdmissibleChartPair domain f g iota center Q K k L)

/-- When `k ≤ L`, the finite family contains every admissible pair and only those pairs. -/
theorem mem_admissibleChartPairFamily_iff [DecidableEq F]
    (domain : Fin n ↪ F) (f g : Fin n → F) (iota : F →+* E)
    (center : E) (Q : DifferentialPolynomial E[X] r) (K k L : ℕ)
    (hkL : k ≤ L) (pair : F[X] × F[X]) :
    pair ∈ admissibleChartPairFamily domain f g iota center Q K k L ↔
      IsAdmissibleChartPair domain f g iota center Q K k L pair := by
  classical
  simp only [admissibleChartPairFamily, Finset.mem_filter]
  constructor
  · exact And.right
  · intro hp
    exact ⟨mem_correlatedPairFamily_of_commonAgreement domain f g pair.1 pair.2
      hp.degree_left hp.degree_right (hkL.trans hp.common), hp⟩

/-- All admissible pairs are counted by the sharp ordinary-chart bound. -/
theorem admissibleChartPairFamily_card_le [DecidableEq F] [IsAlgClosed E]
    (domain : Fin n ↪ F) (f g : Fin n → F) (iota : F →+* E)
    (center : E) (Q : DifferentialPolynomial E[X] r) (K k L v : ℕ)
    (hK : r < K) (hkK : k ≤ K) (hk : 0 < k) (hkL : k ≤ L) (hLn : L ≤ n)
    (hjet : Q.weightedTotalDegree (fun i ↦ i.elim 0 (fun _ ↦ 1)) ≤ v) :
    ((admissibleChartPairFamily domain f g iota center Q K k L).card : ℚ) ≤ (v : ℚ) *
      ((((n * (1 + 2 * K * (v - 1)) : ℕ) : ℚ) / ((L - k + 1 : ℕ) : ℚ)) ^ r) := by
  apply admissibleChartPairs_card_le domain f g iota center Q K k L v hK hkK hk hkL hLn
    hjet
  intro pair hp
  exact (mem_admissibleChartPairFamily_iff domain f g iota center Q K k L hkL pair).mp hp

end ReedSolomon

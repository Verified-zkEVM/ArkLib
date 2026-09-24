/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.GraphLineComponent
public import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.TaylorChart.PointRecognition
public import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.Pairs.Family
public import ArkLib.Data.Polynomial.Differential.BaseChange
public import ArkLib.Data.Polynomial.Differential.TaylorChartAlgebra
public import ArkLib.Data.Polynomial.Differential.TaylorChartIncidence

/-!
# Counting admissible correlated pairs in a Taylor chart

An admissible polynomial pair determines a regular point of the joint Taylor chart after
specializing its challenge coordinate. The resulting jets retain the pair's agreement set, so
the high-cut incidence bound gives a sharp count for finite families of admissible pairs.

## Main statements

* `IsAdmissibleChartPair` and `admissibleChartPairFamily` specify pairs satisfying the chart
  identities and common-agreement condition.
* `IsAdmissibleChartPair.specialize` identifies the specialized pair with the rational Taylor
  reconstruction at every regular challenge.
* `admissibleChartPairs_card_le` and `admissibleChartPairFamily_card_le` bound the number of
  admissible pairs by the regular high-cut incidence estimate.

## References

* [DKT26]
-/

@[expose] public section

open Polynomial MvPolynomial PolynomialDifferential
open scoped BigOperators

namespace ReedSolomon

noncomputable section

variable {F E : Type*} [Field F] [Field E] {n r : ℕ}

/-- Restriction of a joint Taylor polynomial to the affine graph of a polynomial pair. -/
def chartPairPullback (iota : F →+* E) (center : E) (pair : F[X] × F[X]) :
    MvPolynomial (Option (Fin (r + 1))) E →ₐ[E] E[X] :=
  MvPolynomial.aeval (affinePairCurve center (pair.1.map iota) (pair.2.map iota))

/-- The initial jet of a polynomial pair at one challenge scalar. -/
def chartPairJet (iota : F →+* E) (center z : E) (pair : F[X] × F[X]) :
    Fin (r + 1) → E :=
  fun j ↦ polynomialJet center (pair.1.map iota) j +
    z * polynomialJet center (pair.2.map iota) j

/-- Admissibility records degree, common agreement, and joint Taylor-chart identities. -/
structure IsAdmissibleChartPair [DecidableEq F] (domain : Fin n ↪ F) (f g : Fin n → F)
    (iota : F →+* E) (center : E) (Q : DifferentialPolynomial E[X] r)
    (K k L : ℕ) (pair : F[X] × F[X]) : Prop where
  degree_left : pair.1.degree < k
  degree_right : pair.2.degree < k
  common : L ≤ (commonPolynomialAgreementSet domain f g pair.1 pair.2).card
  initial : chartPairPullback iota center pair (jointInitialJetEquation center Q) = 0
  high : ∀ l : Fin K, k ≤ l.val →
    chartPairPullback iota center pair (jointCommonTaylorNumerator center Q (2 * K) l) = 0
  regular : chartPairPullback iota center pair (jointInitialJetSeparant center Q) ≠ 0
  reconstruction : ∀ l : Fin K,
    chartPairPullback iota center pair
      (jointTaylorReconstructionError center Q (2 * K) (pair.1.map iota)
        (pair.2.map iota) l) = 0

private theorem eval_chartPairPullback_joint (iota : F →+* E) (center z : E)
    (pair : F[X] × F[X]) (p : MvPolynomial (Option (Fin (r + 1))) E) :
    (chartPairPullback iota center pair p).eval z =
      aeval (fun j ↦ (affinePairCurve (r := r) center
        (pair.1.map iota) (pair.2.map iota) j).eval z) p := by
  let curve : Option (Fin (r + 1)) → E[X] :=
    affinePairCurve (r := r) center (pair.1.map iota) (pair.2.map iota)
  have hcomp : (Polynomial.aeval z).comp (MvPolynomial.aeval curve) =
      MvPolynomial.aeval (fun j ↦ (curve j).eval z) := by
    apply MvPolynomial.algHom_ext
    intro j
    cases j <;> simp [curve, affinePairCurve]
  exact DFunLike.congr_fun hcomp p

/-- Evaluating the affine graph pullback is the same as specializing its challenge coordinate
and then evaluating its initial-jet coordinates. -/
theorem eval_chartPairPullback_symbolic (iota : F →+* E) (center z : E)
    (pair : F[X] × F[X]) (p : MvPolynomial (Fin (r + 1)) E[X]) :
    (chartPairPullback iota center pair ((optionEquivRight E _).symm p)).eval z =
      aeval (chartPairJet iota center z pair) (MvPolynomial.map (Polynomial.evalRingHom z) p) := by
  rw [eval_chartPairPullback_joint]
  have hEval : (Polynomial.aeval z).toRingHom = Polynomial.evalRingHom z := by
    ext a <;> simp [Polynomial.evalRingHom]
  have hsome (j : Fin (r + 1)) :
      (affinePairCurve (r := r) center (pair.1.map iota) (pair.2.map iota)
        (some j)).eval z = chartPairJet (r := r) iota center z pair j := by
    simp [affinePairCurve, chartPairJet]
    ring
  have hzero : (affinePairCurve (r := r) center
      (pair.1.map iota) (pair.2.map iota) none).eval z = z := by
    simp [affinePairCurve]
  rw [aeval_optionEquivRight_symm, hzero, hEval]
  simp only [hsome]

/-- A specialized correlated pair retains the original message-degree bound. -/
theorem degree_correlatedPairSpecialization_lt (iota : F →+* E) (z : E)
    (pair : F[X] × F[X]) {k : ℕ} (h₀ : pair.1.degree < k) (h₁ : pair.2.degree < k) :
    (correlatedPairSpecialization iota z pair).degree < k := by
  apply (Polynomial.degree_add_le _ _).trans_lt
  exact max_lt (Polynomial.degree_map_le.trans_lt h₀)
    ((show (Polynomial.C z * pair.2.map iota).degree ≤ (pair.2.map iota).degree by
      simpa only [Polynomial.smul_eq_C_mul] using Polynomial.degree_smul_le z
        (pair.2.map iota)).trans_lt (Polynomial.degree_map_le.trans_lt h₁))

/-- The Taylor coefficients of a specialized pair are affine in its challenge scalar. -/
theorem coeff_taylor_correlatedPairSpecialization (iota : F →+* E) (center z : E)
    (pair : F[X] × F[X]) (l : ℕ) :
    (Polynomial.taylor center (correlatedPairSpecialization iota z pair)).coeff l =
      (Polynomial.taylor center (pair.1.map iota)).coeff l +
        z * (Polynomial.taylor center (pair.2.map iota)).coeff l := by
  rw [correlatedPairSpecialization, ← Polynomial.smul_eq_C_mul, map_add, map_smul]
  simp only [Polynomial.coeff_add, Polynomial.coeff_smul, smul_eq_mul]

/-- Every cleared reconstruction identity identifies the rational Taylor polynomial with the
specialized pair whenever the initial separant is nonzero. -/
theorem IsAdmissibleChartPair.specialize [DecidableEq F]
    {domain : Fin n ↪ F} {f g : Fin n → F} {iota : F →+* E} {center : E}
    {Q : DifferentialPolynomial E[X] r} {K k L : ℕ} {pair : F[X] × F[X]}
    (hp : IsAdmissibleChartPair domain f g iota center Q K k L pair)
    (hkK : k ≤ K) (z : E)
    (hz : (chartPairPullback iota center pair (jointInitialJetSeparant center Q)).eval z ≠ 0) :
    let Qz := MvPolynomial.map (Polynomial.evalRingHom z) Q
    let jet := chartPairJet (r := r) iota center z pair
    aeval jet (initialJetEquation center Qz) = 0 ∧
      aeval jet (initialJetSeparant center Qz) ≠ 0 ∧
      (∀ l : Fin K, k ≤ l.val →
        aeval jet (commonTaylorNumerator center Qz (2 * K) l) = 0) ∧
      rationalTaylorPolynomial center Qz K jet = correlatedPairSpecialization iota z pair := by
  let Qz := MvPolynomial.map (Polynomial.evalRingHom z) Q
  let jet := chartPairJet (r := r) iota center z pair
  let point : Option (Fin (r + 1)) → E := fun j ↦ j.elim z jet
  let φ : E[X] →ₐ[E] E := Polynomial.aeval z
  have hφ : φ.toRingHom = Polynomial.evalRingHom z := by
    ext a <;> simp [φ, Polynomial.evalRingHom]
  have hQz : MvPolynomial.map φ.toRingHom Q = Qz := by rw [hφ]
  have hQzEval : MvPolynomial.map (Polynomial.aeval z).toRingHom Q = Qz := by
    rw [hφ]
  have hpoint : (fun j ↦
      (affinePairCurve (r := r) center (pair.1.map iota) (pair.2.map iota) j).eval z) =
      point := by
    funext j
    cases j with
    | none => simp [point, affinePairCurve]
    | some j =>
      simp [point, jet, affinePairCurve, chartPairJet]
      ring
  have hsepPoint : aeval point (jointInitialJetSeparant center Q) ≠ 0 := by
    have h := hz
    rw [eval_chartPairPullback_joint, hpoint] at h
    simpa only [Polynomial.eval_zero] using h
  have hsep : aeval jet (initialJetSeparant center Qz) ≠ 0 := by
    rw [aeval_jointInitialJetSeparant] at hsepPoint
    simp only [point, Option.elim_none, Option.elim_some] at hsepPoint
    rw [hQz] at hsepPoint
    exact hsepPoint
  have hinitPoint : aeval point (jointInitialJetEquation center Q) = 0 := by
    have h := congrArg (fun p : E[X] ↦ p.eval z) hp.initial
    rw [eval_chartPairPullback_joint, hpoint, Polynomial.eval_zero] at h
    simpa using h
  have hinit : aeval jet (initialJetEquation center Qz) = 0 := by
    rw [jointInitialJetEquation, aeval_optionEquivRight_symm] at hinitPoint
    simp only [point, Option.elim_none, Option.elim_some] at hinitPoint
    rw [map_initialJetEquation,
      show (Polynomial.aeval z).toRingHom (Polynomial.C center) = center by simp,
      hQz] at hinitPoint
    exact hinitPoint
  have hhigh : ∀ l : Fin K, k ≤ l.val →
      aeval jet (commonTaylorNumerator center Qz (2 * K) l) = 0 := by
    intro l hl
    have h := congrArg (fun p : E[X] ↦ p.eval z) (hp.high l hl)
    rw [eval_chartPairPullback_joint, hpoint] at h
    rw [jointCommonTaylorNumerator, aeval_optionEquivRight_symm] at h
    simp only [point, Option.elim_none, Option.elim_some] at h
    rw [map_commonTaylorNumeratorOver_eq (φ := Polynomial.aeval z),
      show (Polynomial.aeval z) (Polynomial.C center) = center by simp, hQz] at h
    simpa using h
  refine ⟨hinit, hsep, hhigh, ?_⟩
  apply Polynomial.taylor_injective center
  ext l
  by_cases hl : l < K
  · have h := congrArg (fun p : E[X] ↦ p.eval z) (hp.reconstruction ⟨l, hl⟩)
    rw [eval_chartPairPullback_joint, hpoint, Polynomial.eval_zero] at h
    simp only [jointTaylorReconstructionError, map_sub, map_mul, map_pow, map_add,
      MvPolynomial.aeval_C, MvPolynomial.aeval_X, Algebra.algebraMap_self,
      RingHom.id_apply] at h
    rw [aeval_jointCommonTaylorNumerator, aeval_jointInitialJetSeparant] at h
    simp only [point, Option.elim_none, Option.elim_some, jet, hQzEval] at h
    have hlExponent : 2 * (l - r) - 1 ≤ 2 * K := by
      have hsub : l - r ≤ K := (Nat.sub_le _ _).trans (Nat.le_of_lt hl)
      calc
        2 * (l - r) - 1 ≤ 2 * (l - r) := Nat.sub_le _ _
        _ ≤ 2 * K := Nat.mul_le_mul_left 2 hsub
    have hcoeff := aeval_commonTaylorNumerator center Qz jet hlExponent hsep
    have hlinear := coeff_taylor_correlatedPairSpecialization iota center z pair l
    rw [hcoeff] at h
    have hmul :
        (aeval jet (initialJetSeparant center Qz)) ^ (2 * K) *
          (rationalTaylorCoefficient center Qz jet l -
            ((Polynomial.taylor center (pair.1.map iota)).coeff l +
              z * (Polynomial.taylor center (pair.2.map iota)).coeff l)) = 0 := by
      linear_combination h
    have hzero := (mul_eq_zero.mp hmul).resolve_left (pow_ne_zero _ hsep)
    rw [rationalTaylorPolynomial, coeff_taylor_centeredCoefficientPrefix,
      ite_eq_left hl, hlinear]
    exact sub_eq_zero.mp hzero
  · have hleft := degree_rationalTaylorPolynomial_lt center Qz
      (taylorExponentSufficient_two_mul r K) k jet hsep (by
        intro j hkl hjK
        exact hhigh ⟨j, hjK⟩ hkl)
    have hright := degree_correlatedPairSpecialization_lt iota z pair
      hp.degree_left hp.degree_right
    have hkl : (k : WithBot ℕ) ≤ l := by exact_mod_cast (show k ≤ l by omega)
    rw [Polynomial.coeff_eq_zero_of_degree_lt (by
        simpa only [Polynomial.degree_taylor] using hleft.trans_le hkl),
      Polynomial.coeff_eq_zero_of_degree_lt (by
        simpa only [Polynomial.degree_taylor] using hright.trans_le hkl)]

/-- A finite family of admissible pair graphs obeys the sharp ordinary Taylor-chart bound. -/
theorem admissibleChartPairs_card_le [DecidableEq F] [IsAlgClosed E]
    (domain : Fin n ↪ F) (f g : Fin n → F) (iota : F →+* E)
    (center : E) (Q : DifferentialPolynomial E[X] r) (K k L v : ℕ)
    (hK : r < K) (hkK : k ≤ K) (hk : 0 < k) (hkL : k ≤ L) (hLn : L ≤ n)
    (hjet : Q.weightedTotalDegree (fun i ↦ i.elim 0 (fun _ ↦ 1)) ≤ v)
    (pairs : Finset (F[X] × F[X]))
    (hpairs : ∀ pair ∈ pairs,
      IsAdmissibleChartPair domain f g iota center Q K k L pair) :
    (pairs.card : ℚ) ≤ (v : ℚ) *
      ((((n * (1 + 2 * K * (v - 1)) : ℕ) : ℚ) / ((L - k + 1 : ℕ) : ℚ)) ^ r) := by
  classical
  by_cases hempty : pairs = ∅
  · subst pairs
    simp only [Finset.card_empty, Nat.cast_zero]
    positivity
  let auxiliary := pairs.image fun pair ↦
    chartPairPullback iota center pair (jointInitialJetSeparant center Q)
  obtain ⟨z, _, hinj, havoid⟩ :=
    exists_correlatedPairSpecialization_injOn_avoiding_roots iota pairs ∅ auxiliary (by
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
  let domainE : Fin n ↪ E := ⟨fun i ↦ iota (domain i), iota.injective.comp domain.injective⟩
  let received : Fin n → E := fun i ↦ iota (f i) + z * iota (g i)
  have hLkn : L - k + 1 ≤ n := by omega
  have hbound := card_le_of_highTaylorCuts_of_agreement center Qz
    (taylorExponentSufficient_two_mul r K) hK domainE received domainE.injective hkL
    (by simpa using hLkn) jets (by
      intro jet hj
      obtain ⟨pair, hp, rfl⟩ := Finset.mem_image.mp hj
      exact ⟨(hspec pair hp).1, (hspec pair hp).2.1,
        fun l hl hlK ↦ (hspec pair hp).2.2.1 ⟨l, hlK⟩ hl⟩) (by
      intro jet hj
      obtain ⟨pair, hp, rfl⟩ := Finset.mem_image.mp hj
      apply (hpairs pair hp).common.trans
      have hsubset : (commonPolynomialAgreementSet domain f g pair.1 pair.2 :
          Set (Fin n)) ⊆
          {i | aeval (chartPairJet (r := r) iota center z pair)
            (taylorAgreementEquation center Qz K (2 * K) (domainE i) (received i)) = 0} := by
        intro i hi
        have hi' : pair.1.eval (domain i) = f i ∧ pair.2.eval (domain i) = g i := by
          have hiFin : i ∈ commonPolynomialAgreementSet domain f g pair.1 pair.2 := by
            simpa using hi
          exact (mem_commonPolynomialAgreementSet domain f g pair.1 pair.2 i).mp hiFin
        exact (taylorAgreementEquation_eq_zero_iff center Qz
          (taylorExponentSufficient_two_mul r K) (chartPairJet (r := r) iota center z pair)
          (hspec pair hp).2.1 (domainE i) (received i)).2 (by
            rw [(hspec pair hp).2.2.2]
            change (correlatedPairSpecialization iota z pair).eval (iota (domain i)) =
              iota (f i) + z * iota (g i)
            simp only [correlatedPairSpecialization, Polynomial.eval_add,
              Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_map_apply, hi'.1,
              hi'.2])
      calc
        (commonPolynomialAgreementSet domain f g pair.1 pair.2).card =
            (commonPolynomialAgreementSet domain f g pair.1 pair.2 : Set (Fin n)).ncard := by
          simp
        _ ≤ _ := Set.ncard_le_ncard hsubset)
  rw [hcard] at hbound
  have hweight : (fun i : JetVariable r ↦ i.elim 0 (fun _ ↦ 1)) = jetDegreeWeight := by
    funext i
    cases i <;> rfl
  have hjetQ : jetTotalDegree Q ≤ v := by
    change Q.weightedTotalDegree jetDegreeWeight ≤ v
    rw [← hweight]
    exact hjet
  have hvle : jetTotalDegree Qz ≤ v :=
    (jetTotalDegree_map_le (Polynomial.evalRingHom z) Q).trans hjetQ
  have hB : rationalTaylorCutDegreeBound Qz (2 * K) ≤ 1 + 2 * K * (v - 1) := by
    unfold rationalTaylorCutDegreeBound
    exact Nat.add_le_add_left (Nat.mul_le_mul_left _ (Nat.sub_le_sub_right hvle 1)) 1
  apply hbound.trans
  apply mul_le_mul
  · exact_mod_cast hvle
  · apply pow_le_pow_left₀ (by positivity)
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact_mod_cast (show Fintype.card (Fin n) * rationalTaylorCutDegreeBound Qz (2 * K) ≤
      n * (1 + 2 * K * (v - 1)) by simpa using Nat.mul_le_mul_left n hB)
  · positivity
  · positivity

/-- The finite admissible-pair family contains only degree-bounded pairs with sufficient
common agreement, together with their chart identities. -/
def admissibleChartPairFamily [DecidableEq F]
    (domain : Fin n ↪ F) (f g : Fin n → F) (iota : F →+* E)
    (center : E) (Q : DifferentialPolynomial E[X] r) (K k L : ℕ) :
    Finset (F[X] × F[X]) := by
  classical
  exact (correlatedPairFamily domain f g k).filter
    (IsAdmissibleChartPair domain f g iota center Q K k L)

/-- Membership in the finite family is equivalent to admissibility when `k ≤ L`. -/
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

/-- All admissible pairs in the finite family satisfy the ordinary Taylor-chart bound. -/
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

end

end ReedSolomon

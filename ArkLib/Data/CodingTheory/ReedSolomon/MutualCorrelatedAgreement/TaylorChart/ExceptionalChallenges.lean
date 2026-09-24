/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.TaylorChart.Incidence
public import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.Pairs.ExceptionalSet
/-!
# Finite bad challenges for a symbolic Taylor chart

Regular chart points outside admissible pair graphs and exceptional correlated-pair challenges
give a bound on finite sets of challenges whose reconstructed polynomials do not have exact
agreement sets from a polynomial pair.

## Main statements

* `ReedSolomon.finite_symbolicTaylorChart_badChallenges_card_le` bounds the number of such
  challenges by the sum of the chart-incidence and exceptional-pair bounds.

## References

* [DKT26]
-/

@[expose] public section

open Polynomial MvPolynomial PolynomialDifferential

namespace ReedSolomon

noncomputable section

variable {F E : Type*} [Field F] [Field E] {n r : ℕ}

private theorem jointInitial_eval (center z : E) (Q : DifferentialPolynomial E[X] r)
    (jet : Fin (r + 1) → E) :
    aeval (fun i ↦ i.elim z jet) (jointInitialJetEquation center Q) =
    aeval jet (initialJetEquation center (MvPolynomial.map (Polynomial.evalRingHom z) Q)) := by
  have hφ : (Polynomial.aeval z).toRingHom = Polynomial.evalRingHom z := by
    ext a <;> simp [Polynomial.evalRingHom]
  rw [jointInitialJetEquation, aeval_optionEquivRight_symm, map_initialJetEquation]
  simp only [Option.elim_none, Option.elim_some]
  rw [hφ]
  rw [show (Polynomial.evalRingHom z) (Polynomial.C center) = center from Polynomial.eval_C]

private theorem jointSeparant_eval (center z : E) (Q : DifferentialPolynomial E[X] r)
    (jet : Fin (r + 1) → E) :
    aeval (fun i ↦ i.elim z jet) (jointInitialJetSeparant center Q) =
      aeval jet (initialJetSeparant center (MvPolynomial.map (Polynomial.evalRingHom z) Q)) := by
  have hφ : (Polynomial.aeval z).toRingHom = Polynomial.evalRingHom z := by
    ext a <;> simp [Polynomial.evalRingHom]
  simpa only [Option.elim_none, Option.elim_some, hφ] using
    aeval_jointInitialJetSeparant center Q (fun i ↦ i.elim z jet)

private theorem jointNumerator_eval (center z : E) (Q : DifferentialPolynomial E[X] r)
    (K : ℕ) (l : Fin K) (jet : Fin (r + 1) → E) :
    aeval (fun i ↦ i.elim z jet) (jointCommonTaylorNumerator center Q (2 * K) l) =
      aeval jet
        (commonTaylorNumerator center (MvPolynomial.map (Polynomial.evalRingHom z) Q)
          (2 * K) l) := by
  have hφ : (Polynomial.aeval z).toRingHom = Polynomial.evalRingHom z := by
    ext a <;> simp [Polynomial.evalRingHom]
  simpa only [Option.elim_none, Option.elim_some, hφ] using
    aeval_jointCommonTaylorNumerator center Q (2 * K) l (fun i ↦ i.elim z jet)

private theorem jointInitial_ne_zero_of_regular (center z : E)
    (Q : DifferentialPolynomial E[X] r) (jet : Fin (r + 1) → E)
    (hs : aeval jet (initialJetSeparant center
      (MvPolynomial.map (Polynomial.evalRingHom z) Q)) ≠ 0) :
    jointInitialJetEquation center Q ≠ 0 := by
  have hs' : initialJetSeparant center (MvPolynomial.map (Polynomial.evalRingHom z) Q) ≠ 0 := by
    intro hzero
    exact hs (by rw [hzero]; simp)
  have hi := initialJetEquation_ne_zero_of_initialJetSeparant_ne_zero center _ hs'
  intro hzero
  have he : initialJetEquation (Polynomial.C center) Q = 0 := by
    apply (optionEquivRight E (Fin (r + 1))).symm.injective
    simpa only [jointInitialJetEquation, map_zero] using hzero
  have hm := congrArg (MvPolynomial.map (Polynomial.evalRingHom z)) he
  rw [map_initialJetEquation, map_zero,
    show (Polynomial.evalRingHom z) (Polynomial.C center) = center from Polynomial.eval_C] at hm
  exact hi hm

/-- Distinct challenges with regular symbolic Taylor charts and no exact admissible-pair
agreement representation satisfy the combined incidence and exceptional-pair bound. -/
theorem finite_symbolicTaylorChart_badChallenges_card_le [DecidableEq F] [DecidableEq E]
    [IsAlgClosed E] (domain : Fin n ↪ F) (f g : Fin n → F) (iota : F →+* E)
    (center : E) (Q : DifferentialPolynomial E[X] r) (K k L A v h : ℕ)
    (hK : r < K) (hkK : k ≤ K) (hk : 0 < k) (hkL : k ≤ L)
    (hLA : L ≤ A) (hAn : A ≤ n) (hv : 0 < v)
    (hjet : Q.weightedTotalDegree (fun i ↦ i.elim 0 (fun _ ↦ 1)) ≤ v)
    (hheight : CoeffNatDegreeLE Q h)
    (challenges : Finset E) (witness : E → E[X]) (jet : E → Fin (r + 1) → E)
    (hchart : ∀ z ∈ challenges,
      let Qz := MvPolynomial.map (Polynomial.evalRingHom z) Q
      (witness z).degree < k ∧
        aeval (jet z) (initialJetEquation center Qz) = 0 ∧
        aeval (jet z) (initialJetSeparant center Qz) ≠ 0 ∧
        (∀ l : Fin K, k ≤ l.val →
          aeval (jet z) (commonTaylorNumerator center Qz (2 * K) l) = 0) ∧
        rationalTaylorPolynomial center Qz K (jet z) = witness z)
    (hagree : ∀ z ∈ challenges,
      A ≤ (polynomialAgreementSet (domain.trans ⟨iota, iota.injective⟩)
        (fun i ↦ iota (f i) + z * iota (g i)) (witness z)).card)
    (hbad : ∀ z ∈ challenges, ¬ ∃ pair : F[X] × F[X],
      pair.1.degree < k ∧ pair.2.degree < k ∧
      witness z = correlatedPairSpecialization iota z pair ∧
      polynomialAgreementSet (domain.trans ⟨iota, iota.injective⟩)
        (fun i ↦ iota (f i) + z * iota (g i)) (witness z) =
          commonPolynomialAgreementSet domain f g pair.1 pair.2) :
    (challenges.card : ℚ) ≤ ((v + h : ℕ) : ℚ) *
      ((((n * (1 + 2 * K * (v - 1 + h)) : ℕ) : ℚ) /
        ((A - L + 1 : ℕ) : ℚ)) ^ (r + 1)) +
      ((n - L : ℕ) : ℚ) * ((v : ℚ) *
        ((((n * (1 + 2 * K * (v - 1)) : ℕ) : ℚ) /
          ((L - k + 1 : ℕ) : ℚ)) ^ r)) := by
  classical
  let pairs := admissibleChartPairFamily domain f g iota center Q K k L
  have hpair (p : F[X] × F[X]) (hp : p ∈ pairs) :=
    (mem_admissibleChartPairFamily_iff domain f g iota center Q K k L hkL p).mp hp
  obtain ⟨exceptional, hexc, hexact⟩ := exists_exceptional_correlatedPairFamily
    (L := L) domain f g iota pairs (fun p hp ↦ (hpair p hp).common)
  let remaining := challenges \ exceptional
  let point : E → Option (Fin (r + 1)) → E := fun z i ↦ i.elim z (jet z)
  have hpointinj : Function.Injective point := by
    intro z z' heq
    exact congrFun heq none
  let S := remaining.image point
  have hcard : S.card = remaining.card := Finset.card_image_of_injective _ hpointinj
  have hoff (z : E) (hz : z ∈ remaining) :
      point z ∉ admissibleChartPairGraphLocus domain f g iota center Q K k L := by
    obtain ⟨hzc, hze⟩ := Finset.mem_sdiff.mp hz
    change ¬ ∃ pair : F[X] × F[X], IsAdmissibleChartPair domain f g iota center Q K k L pair ∧
      ∃ z', point z = fun j ↦
        (affinePairCurve center (pair.1.map iota) (pair.2.map iota) j).eval z'
    intro hgraph
    obtain ⟨pair, hp, z', heq⟩ := hgraph
    have hz' : z' = z := by
      have h := congrFun heq none
      simpa only [point, Option.elim_none, affinePairCurve, Polynomial.eval_X] using h.symm
    have hpoint : point z = fun j ↦
        (affinePairCurve center (pair.1.map iota) (pair.2.map iota) j).eval z := by
      simpa only [hz'] using heq
    have hjetEq : jet z = chartPairJet iota center z pair := by
      funext j
      have h := congrFun hpoint (some j)
      simp only [point, Option.elim_some, affinePairCurve, Polynomial.eval_add, Polynomial.eval_C,
        Polynomial.eval_mul, Polynomial.eval_X] at h
      simpa only [chartPairJet] using h
    have hsepPoint : aeval (point z) (jointInitialJetSeparant center Q) ≠ 0 := by
      rw [jointSeparant_eval]
      exact (hchart z hzc).2.2.1
    have hregular :
        (chartPairPullback iota center pair (jointInitialJetSeparant center Q)).eval z ≠ 0 := by
      rw [eval_chartPairPullback_joint, ← hpoint]
      exact hsepPoint
    have hspec := hp.specialize hkK z hregular
    have hw : witness z = correlatedPairSpecialization iota z pair := by
      rw [← (hchart z hzc).2.2.2.2, hjetEq]
      exact hspec.2.2.2
    have hpmem : pair ∈ pairs :=
      (mem_admissibleChartPairFamily_iff domain f g iota center Q K k L hkL pair).mpr hp
    exact hbad z hzc ⟨pair, hp.degree_left, hp.degree_right, hw,
      by rw [hw]; exact hexact pair hpmem z hze⟩
  have hoffbound : (remaining.card : ℚ) ≤ ((v + h : ℕ) : ℚ) *
      ((((n * (1 + 2 * K * (v - 1 + h)) : ℕ) : ℚ) /
        ((A - L + 1 : ℕ) : ℚ)) ^ (r + 1)) := by
    by_cases hempty : remaining = ∅
    · rw [hempty, Finset.card_empty, Nat.cast_zero]
      positivity
    obtain ⟨z₀, hz₀⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
    have hzc := (Finset.mem_sdiff.mp hz₀).1
    have hi := jointInitial_ne_zero_of_regular center z₀ Q (jet z₀) (hchart z₀ hzc).2.2.1
    rw [← hcard]
    apply finite_regularJointTaylorChartPoints_off_admissiblePairGraphs_card_le_of_jetDegree
      (K := K) (k := k) (L := L) (A := A) (v := v) (h := h) domain f g iota center Q
      hK hkL hLA (by omega) hi (by
        have hweight : (fun i : JetVariable r ↦ i.elim 0 (fun _ ↦ 1)) = jetDegreeWeight := by
          funext i
          cases i <;> rfl
        change Q.weightedTotalDegree jetDegreeWeight ≤ v
        rw [← hweight]
        exact hjet) hheight S
    · intro x hx
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hx
      have hzc := (Finset.mem_sdiff.mp hz).1
      have hsepPoint : aeval (point z) (jointInitialJetSeparant center Q) ≠ 0 := by
        rw [jointSeparant_eval]
        exact (hchart z hzc).2.2.1
      refine ⟨(jointInitial_eval center z Q (jet z)).trans (hchart z hzc).2.1,
        hsepPoint, ?_, hoff z hz⟩
      intro l hl
      rw [jointNumerator_eval]
      exact (hchart z hzc).2.2.2.1 l hl
    · intro x hx
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hx
      have hzc := (Finset.mem_sdiff.mp hz).1
      have hsepPoint : aeval (point z) (jointInitialJetSeparant center Q) ≠ 0 := by
        rw [jointSeparant_eval]
        exact (hchart z hzc).2.2.1
      calc
        A ≤ (polynomialAgreementSet (domain.trans ⟨iota, iota.injective⟩)
            (fun i ↦ iota (f i) + z * iota (g i)) (witness z)).card := hagree z hzc
        _ = (polynomialAgreementSet (domain.trans ⟨iota, iota.injective⟩)
            (fun i ↦ iota (f i) + z * iota (g i)) (witness z) : Set (Fin n)).ncard :=
          (Set.ncard_coe_finset _).symm
        _ ≤ {i | aeval (point z) (jointTaylorAgreementEquation center Q K (2 * K)
            (Polynomial.C (iota (domain i)))
            (Polynomial.C (iota (f i)) + Polynomial.X * Polynomial.C (iota (g i)))) = 0}.ncard :=
          Set.ncard_le_ncard (by
          intro i hi
          have hi' := (mem_polynomialAgreementSet ..).mp hi
          change (witness z).eval (iota (domain i)) =
            iota (f i) + z * iota (g i) at hi'
          have hiff := aeval_jointTaylorAgreementEquation_eq_zero_iff center Q K (2 * K)
            (taylorExponentSufficient_two_mul r K) (point z) hsepPoint
            (iota (domain i)) (iota (f i)) (iota (g i))
          apply hiff.mpr
          simpa only [point, Option.elim_none, Option.elim_some,
            (hchart z hzc).2.2.2.2] using hi')
  have hpairbound : (pairs.card : ℚ) ≤ (v : ℚ) *
      ((((n * (1 + 2 * K * (v - 1)) : ℕ) : ℚ) /
        ((L - k + 1 : ℕ) : ℚ)) ^ r) := by
    simpa [pairs, Nat.ne_of_gt hk] using
      admissibleChartPairFamily_card_le domain f g iota center Q K k L v hK hkK hkL
        (hLA.trans hAn) hjet
  have hexcbound : (exceptional.card : ℚ) ≤ ((n - L : ℕ) : ℚ) *
      ((v : ℚ) * ((((n * (1 + 2 * K * (v - 1)) : ℕ) : ℚ) /
        ((L - k + 1 : ℕ) : ℚ)) ^ r)) := by
    have he : (exceptional.card : ℚ) ≤ (pairs.card : ℚ) * ((n - L : ℕ) : ℚ) := by
      exact_mod_cast (show exceptional.card ≤ pairs.card * (n - L) by
        simpa only [Fintype.card_fin] using hexc)
    apply he.trans
    have hm := mul_le_mul_of_nonneg_right hpairbound
      (show (0 : ℚ) ≤ ((n - L : ℕ) : ℚ) by positivity)
    simpa only [pairs, mul_comm] using hm
  have hcover : challenges.card ≤ remaining.card + exceptional.card := by
    have he := Finset.card_sdiff_add_card_inter challenges exceptional
    have hi := Finset.card_le_card (Finset.inter_subset_right :
      challenges ∩ exceptional ⊆ exceptional)
    dsimp only [remaining]
    omega
  have hcoverQ : (challenges.card : ℚ) ≤ (remaining.card : ℚ) + (exceptional.card : ℚ) := by
    exact_mod_cast hcover
  exact hcoverQ.trans (add_le_add hoffbound hexcbound)

end

end ReedSolomon

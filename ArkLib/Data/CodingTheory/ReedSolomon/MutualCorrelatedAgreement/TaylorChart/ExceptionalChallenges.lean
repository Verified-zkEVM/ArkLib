/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.TaylorChart.Incidence
public import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.Pairs.ExceptionalSet
/-!
# Finite bad challenges for one symbolic chart

Outside the simultaneous accidental-agreement set, a bad witness cannot lie on an
admissible pair graph. Its challenge coordinate embeds the remaining challenges into the
off-graph incidence problem. The bound combines that incidence count with the pair count.
-/

@[expose] public section

open PolynomialDifferential


noncomputable section

namespace ReedSolomon

open Polynomial MvPolynomial HiddenDerivative AffineHilbert

variable {F E : Type*} [Field F] [Field E] {n r : ℕ}

private theorem source_initial_eval (center z : E) (Q : DifferentialPolynomial E[X] r)
    (jet : Fin (r + 1) → E) :
    aeval (fun i ↦ i.elim z jet) (symbolicSourceInitialEquation center Q) =
      aeval jet (initialJetEquation center (MvPolynomial.map (Polynomial.evalRingHom z) Q)) := by
  rw [symbolicSourceInitialEquation, aeval_optionEquivRight_symm,
    map_initialJetEquationOver]
  simp only [Option.elim_none, Option.elim_some]
  rw [show (Polynomial.evalRingHom z) (Polynomial.C center) = center from Polynomial.eval_C]
  rfl

private theorem source_separant_eval (center z : E) (Q : DifferentialPolynomial E[X] r)
    (jet : Fin (r + 1) → E) :
    aeval (fun i ↦ i.elim z jet) (symbolicSourceSeparant center Q) =
      aeval jet (initialJetSeparant center (MvPolynomial.map (Polynomial.evalRingHom z) Q)) := by
  rw [symbolicSourceSeparant, aeval_optionEquivRight_symm,
    map_initialJetSeparantOver]
  simp only [Option.elim_none, Option.elim_some]
  rw [show (Polynomial.evalRingHom z) (Polynomial.C center) = center from Polynomial.eval_C]
  rfl

private theorem source_numerator_eval (center z : E) (Q : DifferentialPolynomial E[X] r)
    (K : ℕ) (l : Fin K) (jet : Fin (r + 1) → E) :
    aeval (fun i ↦ i.elim z jet) (symbolicSourceNumerator center Q K l) =
      aeval jet (commonTaylorNumerator center
        (MvPolynomial.map (Polynomial.evalRingHom z) Q) K l) := by
  rw [symbolicSourceNumerator, aeval_optionEquivRight_symm, eval_commonTaylorNumeratorOver]
  rfl

private theorem source_agreement_eval (center z alpha a b : E)
    (Q : DifferentialPolynomial E[X] r) (K : ℕ) (jet : Fin (r + 1) → E) :
    aeval (fun i ↦ i.elim z jet) (symbolicSourceAgreement center Q K alpha a b) =
      aeval jet (taylorAgreementEquation center
        (MvPolynomial.map (Polynomial.evalRingHom z) Q) K alpha (a + z * b)) := by
  rw [symbolicSourceAgreement, aeval_optionEquivRight_symm]
  simp only [Option.elim_none, Option.elim_some]
  have hm : MvPolynomial.map (Polynomial.evalRingHom z)
      (taylorAgreementEquationOver (F := E) (Polynomial.C center) Q K
        (Polynomial.C alpha) (Polynomial.C a + Polynomial.X * Polynomial.C b)) =
      taylorAgreementEquation center (MvPolynomial.map (Polynomial.evalRingHom z) Q)
        K alpha (a + z * b) := by
    let φ : E[X] →ₐ[E] E := Polynomial.aeval z
    have hφ : φ.toRingHom = Polynomial.evalRingHom z := by ext a <;> simp [φ]
    have hc : φ (Polynomial.C center) = center := by simp [φ]
    have hx : φ (Polynomial.C alpha) = alpha := by simp [φ]
    have hy : φ (Polynomial.C a + Polynomial.X * Polynomial.C b) = a + z * b := by
      change (Polynomial.aeval z) (Polynomial.C a + Polynomial.X * Polynomial.C b) = _
      simp only [map_add, map_mul, Polynomial.aeval_C, Polynomial.aeval_X,
        Algebra.algebraMap_self, RingHom.id_apply]
    have he := map_taylorAgreementEquationOver_eq φ
      (Polynomial.C center) Q K (Polynomial.C alpha)
      (Polynomial.C a + Polynomial.X * Polynomial.C b)
    rw [hφ, hc, hx] at he
    exact he.trans (congrArg
      (taylorAgreementEquation center (MvPolynomial.map (Polynomial.evalRingHom z) Q) K alpha)
      hy)
  rw [hm]

private theorem source_initial_ne_zero_of_regular (center z : E)
    (Q : DifferentialPolynomial E[X] r) (jet : Fin (r + 1) → E)
    (hs : aeval jet (initialJetSeparant center
      (MvPolynomial.map (Polynomial.evalRingHom z) Q)) ≠ 0) :
    symbolicSourceInitialEquation center Q ≠ 0 := by
  have hs' : initialJetSeparant center (MvPolynomial.map (Polynomial.evalRingHom z) Q) ≠ 0 := by
    intro hzero
    exact hs (by rw [hzero]; simp)
  have hi := initialJetEquation_ne_zero_of_separant_ne_zero center _ hs'
  intro hzero
  have he : initialJetEquationOver (Polynomial.C center) Q = 0 := by
    apply (optionEquivRight E (Fin (r + 1))).symm.injective
    simpa only [symbolicSourceInitialEquation, map_zero] using hzero
  have hm := congrArg (MvPolynomial.map (Polynomial.evalRingHom z)) he
  rw [map_initialJetEquationOver, map_zero,
    show (Polynomial.evalRingHom z) (Polynomial.C center) = center from Polynomial.eval_C] at hm
  exact hi hm

/-- Distinct bad challenges for an actual fixed-center symbolic chart satisfy the combined
off-graph and accidental-agreement bound. Witness reconstruction and chart equations are
explicit; no differential-solution or abstract graph-counting premise is used. -/
theorem finite_sourceChart_bad_challenges_card_le [DecidableEq F] [DecidableEq E] [IsAlgClosed E]
    (domain : Fin n ↪ F) (f g : Fin n → F) (iota : F →+* E)
    (center : E) (Q : DifferentialPolynomial E[X] r) (K k L A v h : ℕ)
    (hK : r < K) (hkK : k ≤ K) (hk : 0 < k) (hkL : k ≤ L)
    (hLA : L ≤ A) (hAn : A ≤ n) (hv : 0 < v)
    (hjet : Q.weightedTotalDegree (fun i ↦ i.elim 0 (fun _ ↦ 1)) ≤ v)
    (hheight : ChallengeHeightLE Q h)
    (challenges : Finset E) (witness : E → E[X]) (jet : E → Fin (r + 1) → E)
    (hchart : ∀ z ∈ challenges,
      let Qz := MvPolynomial.map (Polynomial.evalRingHom z) Q
      (witness z).degree < k ∧
        aeval (jet z) (initialJetEquation center Qz) = 0 ∧
        aeval (jet z) (initialJetSeparant center Qz) ≠ 0 ∧
        (∀ l : Fin K, k ≤ l.val → aeval (jet z) (commonTaylorNumerator center Qz K l) = 0) ∧
        rationalTaylorPolynomial center Qz K (jet z) = witness z)
    (hagree : ∀ z ∈ challenges,
      A ≤ (polynomialAgreementSet (mappedDomain domain iota)
        (fun i ↦ iota (f i) + z * iota (g i)) (witness z)).card)
    (hbad : ∀ z ∈ challenges, ¬ ∃ pair : F[X] × F[X],
      pair.1.degree < k ∧ pair.2.degree < k ∧
      witness z = correlatedPairSpecialization iota z pair ∧
      polynomialAgreementSet (mappedDomain domain iota)
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
      point z ∉ sourceChartPairLocus domain f g iota center Q K k L := by
    obtain ⟨hzc, hze⟩ := Finset.mem_sdiff.mp hz
    rintro ⟨pair, hp, heq⟩
    have hjetEq : jet z = chartPairJet iota center z pair := by
      funext j
      exact congrFun heq (some j)
    have hs := (hchart z hzc).2.2.1
    have hregular :
        (chartPairPullback iota center pair (symbolicSourceSeparant center Q)).eval z ≠ 0 := by
      rw [chartPairPullback, eval_affineGraphPullback]
      rw [← show point z = affineGraphPoint
        (polynomialJet (d := r) center (pair.1.map iota))
        (polynomialJet (d := r) center (pair.2.map iota)) z from heq]
      rw [source_separant_eval]
      exact hs
    have hrec := (hp.specialize hkK z hregular).2.2.2
    have hw : witness z = correlatedPairSpecialization iota z pair := by
      rw [← (hchart z hzc).2.2.2.2, hjetEq]
      exact hrec
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
    have hi := source_initial_ne_zero_of_regular center z₀ Q (jet z₀)
      (hchart z₀ hzc).2.2.1
    rw [← hcard]
    apply finite_sourceChart_points_off_pairs_card_le_of_source domain f g iota center Q
      hK hkL (hk.trans_le hkL) hLA hAn hi hv hjet hheight S
    · intro x hx
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hx
      have hzc := (Finset.mem_sdiff.mp hz).1
      refine ⟨?_, ?_, ?_, hoff z hz⟩
      · exact (source_initial_eval center z Q (jet z)).trans (hchart z hzc).2.1
      · rw [source_separant_eval]
        exact (hchart z hzc).2.2.1
      · intro l hl
        rw [source_numerator_eval]
        exact (hchart z hzc).2.2.2.1 l hl
    · intro x hx
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hx
      have hzc := (Finset.mem_sdiff.mp hz).1
      apply (hagree z hzc).trans
      apply Finset.card_le_card
      intro i hi
      rw [mem_agreementIndices, source_agreement_eval,
        taylorAgreementEquation_eq_zero_iff _ _ _ _ (hchart z hzc).2.2.1,
        (hchart z hzc).2.2.2.2]
      exact (Finset.mem_filter.mp hi).2
  have hpairbound := admissibleChartPairFamily_card_le domain f g iota center Q K k L v
    hK hkK hk hkL (hLA.trans hAn) hjet
  have hexcbound : (exceptional.card : ℚ) ≤ ((n - L : ℕ) : ℚ) *
      ((v : ℚ) * ((((n * (1 + 2 * K * (v - 1)) : ℕ) : ℚ) /
        ((L - k + 1 : ℕ) : ℚ)) ^ r)) := by
    have he : (exceptional.card : ℚ) ≤ (pairs.card : ℚ) * ((n - L : ℕ) : ℚ) := by
      exact_mod_cast hexc
    apply he.trans
    have hm := mul_le_mul_of_nonneg_left hpairbound
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

end ReedSolomon

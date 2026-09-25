/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.PowerBatchedSharpRegularAgreement
public import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.TaylorChart.DerivativeTupleCounting
public import ArkLib.Data.CodingTheory.HiddenDerivative.Parameters.FirstOrder.StageCharges
public import ArkLib.Data.Polynomial.Differential.RationalTaylorBidegree
public import ArkLib.ToMathlib.RingTheory.Nullstellensatz.CappedBidegreeIncidence

/-!
# Derivative-capped power-batched agreement bounds

The first-order power-batched incidence bound uses the actual derivative degree of the defining
equation and the common Taylor cuts. Tuple counting then gives finite bounds for regular bad
challenges and a bounded exceptional set.

## Main statements

* `finite_powerBatched_regular_points_off_graphs_card_le_derivativeCapped_of_exponent`
  bounds regular joint points outside admissible tuple graphs.
* `finite_powerBatchedBadChallenges_card_le_derivativeCapped_of_exponent` and
  `finite_regularPowerBatchedBadChallenges_card_le_derivativeCapped_of_exponent` bound finite
  families of bad challenges at a positive Taylor exponent.
* The corresponding `identityPair` theorems give these bounds for degree-one messages at
  exponent zero.
* `exists_exceptional_regularPowerBatchedAgreement_derivativeCapped_of_exponent` and
  `exists_exceptional_regularPowerBatchedAgreement_identityPair` give bounded exceptional sets.

## References

* [DKTZ26]
-/

@[expose] public section

open Polynomial MvPolynomial PolynomialDifferential ReedSolomon.HiddenDerivative
open scoped BigOperators

noncomputable section

namespace ReedSolomon

variable {F E : Type*} [Field F] [Field E] {n ℓ : ℕ}

/-- Exact dimension-sensitive incidence outside admissible tuple graphs at a sufficient Taylor
exponent, with the derivative degree of the defining equation kept separate from its total jet
degree. -/
theorem
    finite_powerBatched_regular_points_off_graphs_card_le_derivativeCapped_of_exponent
    [DecidableEq F] [IsAlgClosed E]
    (domain : Fin n ↪ F) (w : Fin (ℓ + 1) → Fin n → F) (iota : F →+* E)
    (center : E) (Q : DifferentialPolynomial E[X] 1) (K k L A v u h τ : ℕ)
    (hτ : TaylorExponentSufficient 1 K τ) (hτpos : 0 < τ)
    (hK : 1 < K) (hkK : k ≤ K) (hkL : k ≤ L) (hLA : L ≤ A)
    (hD : 0 < ℓ + h) (hv : 0 < v) (hu : 0 < u) (huv : u ≤ v)
    (hinit : jointInitialJetEquation center Q ≠ 0)
    (hjet : jetTotalDegree Q ≤ v) (hheight : CoeffNatDegreeLE Q h)
    (hderiv : Q.degreeOf (some 1) ≤ u)
    (S : Finset (Option (Fin 2) → E))
    (hS : ∀ x ∈ S, aeval x (jointInitialJetEquation center Q) = 0 ∧
      aeval x (jointInitialJetSeparant center Q) ≠ 0 ∧
      (∀ l : Fin K, k ≤ l.val →
        aeval x (jointCommonTaylorNumerator center Q τ l) = 0) ∧
      x ∉ admissibleChartTupleGraphLocus domain w iota center Q K k L τ)
    (hA : ∀ x ∈ S, A ≤ {i | aeval x (jointTaylorAgreementEquation center Q K τ
      (Polynomial.C (iota (domain i)))
      (powerBatchedCoordinate (fun t ↦ iota (w t i)))) = 0}.ncard) :
    (S.card : ℚ) ≤ (firstOrderCurveJointStageOne K ℓ h v u τ : ℚ) *
      (((n - L + 1 : ℕ) : ℚ) / ((A - L + 1 : ℕ) : ℚ)) *
        (((n - k + 1 : ℕ) : ℚ) / ((A - k + 1 : ℕ) : ℚ)) := by
  classical
  by_cases hempty : S = ∅
  · subst S
    simp only [Finset.card_empty, Nat.cast_zero]
    positivity
  obtain ⟨x₀, hx₀⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
  let g := jointInitialJetEquation center Q
  let s := jointInitialJetSeparant center Q
  let high := regularPowerBatchedHighCuts center Q K k τ
  let cuts : Fin n → MvPolynomial (Option (Fin 2)) E := fun i ↦
    jointTaylorAgreementEquation center Q K τ (Polynomial.C (iota (domain i)))
      (powerBatchedCoordinate (fun t ↦ iota (w t i)))
  let a := regularPowerBatchedCutChallengeDegree ℓ K h (τ := τ)
  let b := regularPowerBatchedCutJetDegree K v (τ := τ)
  let c := firstOrderTaylorDerivativeCap K v u τ
  have ha : 0 < a := by
    dsimp [a, regularPowerBatchedCutChallengeDegree]
    by_cases hℓ : 0 < ℓ
    · omega
    · have hh : 0 < h := by omega
      exact Nat.add_pos_right ℓ (Nat.mul_pos hτpos hh)
  have hb : 0 < b := by
    dsimp [b, regularPowerBatchedCutJetDegree]
    omega
  have hc : 0 < c := firstOrderTaylorDerivativeCap_pos (by omega)
  have hcb : c ≤ b := firstOrderTaylorDerivativeCap_le_totalCap K v u τ
  have hproper : Ideal.span ({g} : Set (MvPolynomial (Option (Fin 2)) E)) ≠ ⊤ := by
    apply Ideal.span_singleton_ne_top
    intro hg
    have heval : IsUnit (aeval x₀ g) := hg.map (MvPolynomial.aeval x₀)
    rw [(hS x₀ hx₀).1] at heval
    exact not_isUnit_zero heval
  have hgBase : g ∈ restrictCappedBidegree (Fin 2) E (Fin.last 1) h v u := by
    have hmem := initialJetEquation_mem_restrictCappedBidegree center Q h v u
      hheight hjet hderiv
    rw [mem_restrictCappedBidegree] at hmem ⊢
    intro m hm
    have hm' := hmem m hm
    exact ⟨hm'.1, hm'.2.1, hm'.2.2.trans (Nat.min_le_right _ _)⟩
  have hsBase : s ∈ restrictCappedBidegree (Fin 2) E (Fin.last 1) h v u := by
    have hmem := initialJetSeparant_mem_restrictCappedBidegree center Q h v u
      hheight hjet hderiv
    have hmem' : s ∈ restrictCappedBidegree (Fin 2) E (Fin.last 1) h (v - 1)
        (min (v - 1) (u - 1)) := by
      simpa only [s, jointInitialJetSeparant] using hmem
    rw [mem_restrictCappedBidegree] at hmem' ⊢
    intro m hm
    have hm' := hmem' m hm
    exact ⟨hm'.1, hm'.2.1.trans (by omega),
      hm'.2.2.trans ((Nat.min_le_right _ _).trans (Nat.sub_le _ _))⟩
  have hgAB : g ∈ restrictCappedBidegree (Fin 2) E (Fin.last 1) a b c := by
    rw [mem_restrictCappedBidegree] at hgBase ⊢
    intro m hm
    have hm' := hgBase m hm
    have hha : h ≤ a := by
      dsimp [a, regularPowerBatchedCutChallengeDegree]
      exact (Nat.le_mul_of_pos_left h hτpos).trans (Nat.le_add_left _ _)
    have hvb : v ≤ b := by
      dsimp [b, regularPowerBatchedCutJetDegree]
      calc
        v = (v - 1) + 1 := by omega
        _ ≤ τ * (v - 1) + 1 := Nat.add_le_add_right
          (Nat.le_mul_of_pos_left _ hτpos) _
        _ = 1 + τ * (v - 1) := by omega
    have huTaylor : u - 1 ≤ τ * (u - 1) := Nat.le_mul_of_pos_left _ hτpos
    have hKoffset : 1 ≤ K - 1 := by omega
    have hux : u ≤ τ * (u - 1) + (K - 1) := by
      calc
        u = (u - 1) + 1 := by omega
        _ ≤ τ * (u - 1) + (K - 1) := Nat.add_le_add huTaylor hKoffset
    have huc : u ≤ c := by
      dsimp [c, firstOrderTaylorDerivativeCap, firstOrderTaylorTotalCap,
        regularPowerBatchedCutJetDegree]
      exact le_min (huv.trans hvb) hux
    refine ⟨?_, ?_, ?_⟩
    · exact hm'.1.trans hha
    · exact hm'.2.1.trans hvb
    · exact hm'.2.2.trans huc
  have hsAB : s ∈ restrictCappedBidegree (Fin 2) E (Fin.last 1) a b c := by
    rw [mem_restrictCappedBidegree] at hsBase ⊢
    intro m hm
    have hm' := hsBase m hm
    have hha : h ≤ a := by
      dsimp [a, regularPowerBatchedCutChallengeDegree]
      exact (Nat.le_mul_of_pos_left h hτpos).trans (Nat.le_add_left _ _)
    have hvb : v ≤ b := by
      dsimp [b, regularPowerBatchedCutJetDegree]
      calc
        v = (v - 1) + 1 := by omega
        _ ≤ τ * (v - 1) + 1 := Nat.add_le_add_right
          (Nat.le_mul_of_pos_left _ hτpos) _
        _ = 1 + τ * (v - 1) := by omega
    have huTaylor : u - 1 ≤ τ * (u - 1) := Nat.le_mul_of_pos_left _ hτpos
    have hKoffset : 1 ≤ K - 1 := by omega
    have hux : u ≤ τ * (u - 1) + (K - 1) := by
      calc
        u = (u - 1) + 1 := by omega
        _ ≤ τ * (u - 1) + (K - 1) := Nat.add_le_add huTaylor hKoffset
    have huc : u ≤ c := by
      dsimp [c, firstOrderTaylorDerivativeCap, firstOrderTaylorTotalCap,
        regularPowerBatchedCutJetDegree]
      exact le_min (huv.trans hvb) hux
    refine ⟨hm'.1.trans hha, hm'.2.1.trans hvb, hm'.2.2.trans huc⟩
  have hhigh : ∀ f ∈ high, f ∈ restrictCappedBidegree (Fin 2) E (Fin.last 1) a b c := by
    intro f hf
    simp only [high, regularPowerBatchedHighCuts, List.mem_map, Finset.mem_toList,
      Finset.mem_filter, Finset.mem_univ, true_and] at hf
    obtain ⟨l, _, rfl⟩ := hf
    have hmem := commonTaylorNumeratorOver_mem_restrictCappedBidegree center Q h v u K τ
      hτ hheight hv hjet (by omega) hderiv l
    have hcap : min (1 + τ * (v - 1)) (τ * (u - 1) + l.val) ≤ c := by
      dsimp [c, firstOrderTaylorDerivativeCap, firstOrderTaylorTotalCap]
      apply min_le_min
      · exact le_rfl
      · gcongr
        omega
    have ha' : τ * h ≤ a := by
      dsimp [a, regularPowerBatchedCutChallengeDegree]
      exact Nat.le_add_left _ _
    have hmem' := hmem
    rw [mem_restrictCappedBidegree] at hmem' ⊢
    intro m hm
    have hm' := hmem' m hm
    refine ⟨hm'.1.trans ha', hm'.2.1.trans (by
      dsimp [b, regularPowerBatchedCutJetDegree]
      exact le_rfl), hm'.2.2.trans hcap⟩
  have hcuts : ∀ i, cuts i ∈ restrictCappedBidegree (Fin 2) E (Fin.last 1) a b c := by
    intro i
    have hmem := taylorAgreementEquationOver_mem_restrictCappedBidegree
      (center := center) (x := iota (domain i))
      (powerBatchedCoordinate (fun t ↦ iota (w t i))) Q ℓ h v u K τ hτ
      (powerBatchedCoordinate_natDegree_le _) hheight hv (by omega) hjet hderiv
    have hcap : min (1 + τ * (v - 1)) (τ * (u - 1) + (K - 1)) ≤ c := by
      dsimp [c, firstOrderTaylorDerivativeCap, firstOrderTaylorTotalCap]
      rfl
    have hmem' := hmem
    rw [mem_restrictCappedBidegree] at hmem' ⊢
    intro m hm
    have hm' := hmem' m hm
    refine ⟨by simpa [a, regularPowerBatchedCutChallengeDegree] using hm'.1,
      by simpa [b, regularPowerBatchedCutJetDegree] using hm'.2.1,
      hm'.2.2.trans hcap⟩
  have hdim : ∀ J : Ideal (MvPolynomial (Option (Fin 2)) E),
      J.IsPrime → s ∉ J → g ∈ J → (∀ f ∈ high, f ∈ J) →
      0 < (affineHilbertPolynomial J).natDegree →
      (affineHilbertPolynomial J).natDegree ≤ k + 1 ∧
        (1 < (affineHilbertPolynomial J).natDegree →
      ({i | cuts i ∈ J}.ncard) ≤ k + 1 - (affineHilbertPolynomial J).natDegree) := by
    intro J hJ hsJ hgJ hhighJ hdJ
    have hhigh' : ∀ l : Fin K, k ≤ l.val →
        jointCommonTaylorNumerator center Q τ l ∈ J := by
      intro l hl
      apply hhighJ
      simp only [high, regularPowerBatchedHighCuts, List.mem_map, Finset.mem_toList,
        Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨l, hl, rfl⟩
    have hcomponent := symbolicSourcePolynomial_dimensionSensitive_component_of_exponent
      center Q K k n τ hτ hK hkK J hJ hsJ hhigh' (domain.trans ⟨iota, iota.injective⟩)
      (fun i ↦ powerBatchedCoordinate (fun t ↦ iota (w t i)))
    simpa only [cuts, Function.Embedding.trans_apply,
      Function.Embedding.coeFn_mk] using hcomponent
  have hterminal : ∀ J : Ideal (MvPolynomial (Option (Fin 2)) E),
      J.IsPrime → s ∉ J → g ∈ J → (∀ f ∈ high, f ∈ J) →
      0 < (affineHilbertPolynomial J).natDegree →
      L ≤ ({i | cuts i ∈ J}.ncard) →
      {x | x ∈ zeroLocus E J ∧ aeval x s ≠ 0} ⊆
        admissibleChartTupleGraphLocus domain w iota center Q K k L τ := by
    intro J hJ hsJ hgJ hhighJ hdJ hcutsJ
    apply principalOpen_subset_admissibleChartTupleGraphLocus
      domain w iota center Q K k L τ hK hkL hτ J hJ
    · simpa only [s] using hsJ
    · exact hdJ
    · simpa only [g] using hgJ
    · intro l hl
      apply hhighJ
      simp only [high, regularPowerBatchedHighCuts, List.mem_map, Finset.mem_toList,
        Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨l, hl, rfl⟩
    · simpa only [cuts] using hcutsJ
  have hA' : ∀ x ∈ S, A ≤ {i | aeval x (cuts i) = 0}.ncard := by
    intro x hx
    simpa only [cuts] using hA x hx
  have hbound := MvPolynomial.cappedBidegreeHypersurface_incidence_off_excluded_hybrid_two
    ha hb hc hLA (hkL.trans hLA) g s hinit hproper hgBase hgAB hsAB high hhigh cuts hcuts
      (admissibleChartTupleGraphLocus domain w iota center Q K k L τ) hdim hterminal S
      (by
        intro x hx
        refine ⟨(hS x hx).1, (hS x hx).2.1, ?_, (hS x hx).2.2.2⟩
        intro f hf
        simp only [high, regularPowerBatchedHighCuts, List.mem_map, Finset.mem_toList,
          Finset.mem_filter, Finset.mem_univ, true_and] at hf
        obtain ⟨l, hl, rfl⟩ := hf
        exact (hS x hx).2.2.1 l hl) hA'
  have hdegree : firstOrderCurveJointStageOne K ℓ h v u τ =
      MvPolynomial.cappedBidegreeMixedVolume h v u a b c := by
    simp only [firstOrderCurveJointStageOne, firstOrderTaylorTotalCap,
      firstOrderTaylorDerivativeCap, regularPowerBatchedCutChallengeDegree,
      regularPowerBatchedCutJetDegree, a, b, c]
  simpa only [hdegree] using hbound

open Classical in
/-- Combine derivative-capped off-graph incidence with derivative-capped tuple counting and the
exact accidental-root contribution of retained tuples. -/
private theorem finite_powerBatchedBadChallenges_card_le_of_derivativeCapped_components
    [IsAlgClosed E]
    (domain : Fin n ↪ F) (w : Fin (ℓ + 1) → Fin n → F) (iota : F →+* E)
    (center : E) (Q : DifferentialPolynomial E[X] 1) (K k L A v u τ : ℕ)
    (hτ : TaylorExponentSufficient 1 K τ) (hkK : k ≤ K) (hkL : k ≤ L)
    (htupleBound : ∀ T : Finset (Fin (ℓ + 1) → F[X]),
      (∀ P ∈ T, IsAdmissibleChartTupleAtExponent domain w iota center Q K k L τ P) →
      (T.card : ℚ) ≤ (firstOrderCurveFiberStageOne K v u τ : ℚ) *
        (((n - k + 1 : ℕ) : ℚ) / ((L - k + 1 : ℕ) : ℚ)))
    (offBound : ℚ)
    (hoffBound : ∀ S : Finset (Option (Fin 2) → E),
      (∀ x ∈ S, aeval x (jointInitialJetEquation center Q) = 0 ∧
        aeval x (jointInitialJetSeparant center Q) ≠ 0 ∧
        (∀ l : Fin K, k ≤ l.val →
          aeval x (jointCommonTaylorNumerator center Q τ l) = 0) ∧
        x ∉ admissibleChartTupleGraphLocus domain w iota center Q K k L τ) →
      (∀ x ∈ S, A ≤ {i | aeval x (jointTaylorAgreementEquation center Q K τ
        (Polynomial.C (iota (domain i)))
        (powerBatchedCoordinate (fun t ↦ iota (w t i)))) = 0}.ncard) →
      (S.card : ℚ) ≤ offBound)
    (challenges : Finset E) (witness : E → E[X]) (jet : E → Fin 2 → E)
    (hchart : ∀ z ∈ challenges,
      let Qz := MvPolynomial.map (Polynomial.evalRingHom z) Q
      (witness z).degree < k ∧
        aeval (jet z) (initialJetEquation center Qz) = 0 ∧
        aeval (jet z) (initialJetSeparant center Qz) ≠ 0 ∧
        (∀ l : Fin K, k ≤ l.val →
          aeval (jet z) (commonTaylorNumerator center Qz τ l.val) = 0) ∧
        rationalTaylorPolynomial center Qz K (jet z) = witness z)
    (hagree : ∀ z ∈ challenges,
      A ≤ (polynomialAgreementSet (domain.trans ⟨iota, iota.injective⟩)
        (powerBatchedWord (fun t i ↦ iota (w t i)) z) (witness z)).card)
    (hbad : ∀ z ∈ challenges,
      ¬ HasExactPowerAgreement domain w iota k z (witness z)) :
    (challenges.card : ℚ) ≤ offBound +
      ((ℓ * (n - L) : ℕ) : ℚ) *
        (firstOrderCurveFiberStageOne K v u τ : ℚ) *
          (((n - k + 1 : ℕ) : ℚ) / ((L - k + 1 : ℕ) : ℚ)) := by
  let tupleBound := (firstOrderCurveFiberStageOne K v u τ : ℚ) *
    (((n - k + 1 : ℕ) : ℚ) / ((L - k + 1 : ℕ) : ℚ))
  have hbound := finite_powerBatchedBadChallenges_card_le_of_tuple_bound_of_exponent
    domain w iota center Q K k L A τ hτ hkK hkL tupleBound htupleBound offBound hoffBound
    challenges witness jet hchart hagree hbad
  simpa only [tupleBound, mul_assoc] using hbound

/-! ### Challenge bounds -/

/-- First-order regular agreement budget using the actual derivative degree of the equation and
the common Taylor cuts. -/
def regularPowerBatchedDerivativeCappedBoundTwo
    (n ℓ K k L A v u h τ : ℕ) : ℚ :=
  (firstOrderCurveJointStageOne K ℓ h v u τ : ℚ) *
      (((n - L + 1 : ℕ) : ℚ) / ((A - L + 1 : ℕ) : ℚ)) *
        (((n - k + 1 : ℕ) : ℚ) / ((A - k + 1 : ℕ) : ℚ)) +
    ((ℓ * (n - L) : ℕ) : ℚ) *
      (firstOrderCurveFiberStageOne K v u τ : ℚ) *
        (((n - k + 1 : ℕ) : ℚ) / ((L - k + 1 : ℕ) : ℚ))

open Classical in
/-- Every finite family of fixed-center regular first-order bad challenges satisfies the
derivative-capped budget at a sufficient Taylor exponent. -/
theorem finite_powerBatchedBadChallenges_card_le_derivativeCapped_of_exponent
    [IsAlgClosed E]
    (domain : Fin n ↪ F) (w : Fin (ℓ + 1) → Fin n → F) (iota : F →+* E)
    (center : E) (Q : DifferentialPolynomial E[X] 1) (K k L A v u h τ : ℕ)
    (hτ : TaylorExponentSufficient 1 K τ) (hτpos : 0 < τ)
    (hK : 1 < K) (hkK : k ≤ K) (hkL : k ≤ L)
    (hLA : L ≤ A) (hAn : A ≤ n) (hD : 0 < ℓ + h) (hv : 0 < v)
    (hu : 0 < u) (huv : u ≤ v)
    (hjet : jetTotalDegree Q ≤ v) (hheight : CoeffNatDegreeLE Q h)
    (hderiv : Q.degreeOf (some 1) ≤ u)
    (challenges : Finset E) (witness : E → E[X]) (jet : E → Fin 2 → E)
    (hchart : ∀ z ∈ challenges,
      let Qz := MvPolynomial.map (Polynomial.evalRingHom z) Q
      (witness z).degree < k ∧
        aeval (jet z) (initialJetEquation center Qz) = 0 ∧
        aeval (jet z) (initialJetSeparant center Qz) ≠ 0 ∧
        (∀ l : Fin K, k ≤ l.val →
          aeval (jet z) (commonTaylorNumerator center Qz τ l.val) = 0) ∧
        rationalTaylorPolynomial center Qz K (jet z) = witness z)
    (hagree : ∀ z ∈ challenges,
      A ≤ (polynomialAgreementSet (domain.trans ⟨iota, iota.injective⟩)
        (powerBatchedWord (fun t i ↦ iota (w t i)) z) (witness z)).card)
    (hbad : ∀ z ∈ challenges,
      ¬ HasExactPowerAgreement domain w iota k z (witness z)) :
    (challenges.card : ℚ) ≤
      regularPowerBatchedDerivativeCappedBoundTwo n ℓ K k L A v u h τ := by
  by_cases hempty : challenges = ∅
  · subst challenges
    simp only [Finset.card_empty, Nat.cast_zero]
    unfold regularPowerBatchedDerivativeCappedBoundTwo
    positivity
  obtain ⟨z₀, hz₀⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
  have hinit := jointInitialJetEquation_ne_zero_of_regular center z₀ Q (jet z₀)
    (hchart z₀ hz₀).2.2.1
  have hw : (fun i : Option (Fin 2) ↦ i.elim 0 (fun _ ↦ 1)) =
      jetDegreeWeight (d := 1) := by
    funext i
    cases i <;> rfl
  have hweighted : Q.weightedTotalDegree (fun i ↦ i.elim 0 (fun _ ↦ 1)) ≤ v := by
    simpa only [jetTotalDegree, hw] using hjet
  unfold regularPowerBatchedDerivativeCappedBoundTwo
  apply finite_powerBatchedBadChallenges_card_le_of_derivativeCapped_components
    domain w iota center Q K k L A v u τ hτ hkK hkL
      (fun T hT ↦ admissibleChartTuples_card_le_derivativeCapped_of_exponent
        domain w iota center Q K k L v u τ hτ hτpos hK hkK hkL
          (hLA.trans hAn) hu huv hweighted hderiv T hT)
      ((firstOrderCurveJointStageOne K ℓ h v u τ : ℚ) *
        (((n - L + 1 : ℕ) : ℚ) / ((A - L + 1 : ℕ) : ℚ)) *
          (((n - k + 1 : ℕ) : ℚ) / ((A - k + 1 : ℕ) : ℚ)))
      (fun S hS hA ↦
        finite_powerBatched_regular_points_off_graphs_card_le_derivativeCapped_of_exponent
        domain w iota center Q K k L A v u h τ hτ hτpos hK hkK hkL hLA
          hD hv hu huv hinit hjet hheight hderiv S hS hA)
      challenges witness jet hchart hagree hbad

/-- Every finite family of regular first-order bad challenges satisfies the derivative-capped
budget at a sufficient Taylor exponent. -/
theorem finite_regularPowerBatchedBadChallenges_card_le_derivativeCapped_of_exponent
    [IsAlgClosed E]
    (domain : Fin n ↪ F) (w : Fin (ℓ + 1) → Fin n → F) (iota : F →+* E)
    (Q : DifferentialPolynomial E[X] 1) (K k L A v u h τ : ℕ)
    (hτ : TaylorExponentSufficient 1 K τ) (hτpos : 0 < τ)
    (hK : 1 < K) (hkK : k ≤ K) (hkL : k ≤ L)
    (hLA : L ≤ A) (hAn : A ≤ n) (hD : 0 < ℓ + h) (hv : 0 < v)
    (hu : 0 < u) (huv : u ≤ v)
    (hjet : jetTotalDegree Q ≤ v) (hheight : CoeffNatDegreeLE Q h)
    (hderiv : Q.degreeOf (some 1) ≤ u)
    (hbin : ∀ i, 1 < i → i < K → (i.choose 1 : E) ≠ 0)
    (S : Finset E)
    (hS : ↑S ⊆ regularPowerBatchedBadChallenges domain w iota Q k A) :
    (S.card : ℚ) ≤ regularPowerBatchedDerivativeCappedBoundTwo n ℓ K k L A v u h τ := by
  classical
  apply finite_regularPowerBatchedBadChallenges_card_le_of_fixed_center_of_exponent
    domain w iota Q K k A τ hkK hbin
      (regularPowerBatchedDerivativeCappedBoundTwo n ℓ K k L A v u h τ) ?_ S hS
  intro center challenges witness jet hchart hagree hbad
  exact finite_powerBatchedBadChallenges_card_le_derivativeCapped_of_exponent
    domain w iota center Q K k L A v u h τ hτ hτpos hK hkK hkL hLA hAn hD hv
      hu huv hjet hheight hderiv challenges witness jet hchart hagree hbad

open Classical in
/-- A single derivative-capped exceptional set works for every regular first-order solution at a
sufficient Taylor exponent. -/
theorem exists_exceptional_regularPowerBatchedAgreement_derivativeCapped_of_exponent
    [IsAlgClosed E]
    (domain : Fin n ↪ F) (w : Fin (ℓ + 1) → Fin n → F) (iota : F →+* E)
    (Q : DifferentialPolynomial E[X] 1) (K k L A v u h τ : ℕ)
    (hτ : TaylorExponentSufficient 1 K τ) (hτpos : 0 < τ)
    (hK : 1 < K) (hkK : k ≤ K) (hkL : k ≤ L)
    (hLA : L ≤ A) (hAn : A ≤ n) (hD : 0 < ℓ + h) (hv : 0 < v)
    (hu : 0 < u) (huv : u ≤ v)
    (hjet : jetTotalDegree Q ≤ v) (hheight : CoeffNatDegreeLE Q h)
    (hderiv : Q.degreeOf (some 1) ≤ u)
    (hbin : ∀ i, 1 < i → i < K → (i.choose 1 : E) ≠ 0) :
    ∃ exceptional : Finset E,
      (exceptional.card : ℚ) ≤
        regularPowerBatchedDerivativeCappedBoundTwo n ℓ K k L A v u h τ ∧
      ∀ z ∉ exceptional, ∀ P : E[X], P.degree < k →
        A ≤ (polynomialAgreementSet (domain.trans ⟨iota, iota.injective⟩)
          (powerBatchedWord (fun t i ↦ iota (w t i)) z) P).card →
        differentialSpecialization (challengeSpecialization Q z) P = 0 →
        differentialSpecialization
          (separant (challengeSpecialization Q z) (Fin.last 1)) P ≠ 0 →
        HasExactPowerAgreement domain w iota k z P := by
  classical
  have hfinite :
      (regularPowerBatchedBadChallenges domain w iota Q k A).Finite := by
    apply Set.finite_of_forall_finset_card_le (R := ℚ) fun S hS ↦
      finite_regularPowerBatchedBadChallenges_card_le_derivativeCapped_of_exponent
        domain w iota Q K k L A v u h τ hτ hτpos hK hkK hkL hLA hAn hD hv
        hu huv hjet hheight hderiv hbin S hS
  refine ⟨hfinite.toFinset, ?_, ?_⟩
  · apply finite_regularPowerBatchedBadChallenges_card_le_derivativeCapped_of_exponent
      domain w iota Q K k L A v u h τ hτ hτpos hK hkK hkL hLA hAn hD hv
      hu huv hjet hheight hderiv hbin
    exact fun z hz ↦ hfinite.mem_toFinset.mp hz
  · intro z hz P hdegree hagree hsol hsep
    by_contra hbad
    apply hz
    exact hfinite.mem_toFinset.mpr ⟨P, hdegree, hagree, hsol, hsep, hbad⟩

open Classical in
/-- Every finite family of fixed-center regular degree-one bad challenges satisfies the
identity-pair derivative-capped budget. -/
theorem finite_powerBatchedBadChallenges_card_le_identityPair
    [IsAlgClosed E]
    (domain : Fin n ↪ F) (w : Fin (ℓ + 1) → Fin n → F) (iota : F →+* E)
    (center : E) (Q : DifferentialPolynomial E[X] 1) (L A v u h : ℕ)
    (hL : 2 ≤ L) (hLA : L ≤ A) (hAn : A ≤ n) (hℓ : 0 < ℓ) (hv : 0 < v)
    (hjet : jetTotalDegree Q ≤ v) (hheight : CoeffNatDegreeLE Q h)
    (challenges : Finset E) (witness : E → E[X]) (jet : E → Fin 2 → E)
    (hchart : ∀ z ∈ challenges,
      let Qz := MvPolynomial.map (Polynomial.evalRingHom z) Q
      (witness z).degree < 2 ∧
        aeval (jet z) (initialJetEquation center Qz) = 0 ∧
        aeval (jet z) (initialJetSeparant center Qz) ≠ 0 ∧
        (∀ l : Fin 2, 2 ≤ l.val →
          aeval (jet z) (commonTaylorNumerator center Qz 0 l.val) = 0) ∧
        rationalTaylorPolynomial center Qz 2 (jet z) = witness z)
    (hagree : ∀ z ∈ challenges,
      A ≤ (polynomialAgreementSet (domain.trans ⟨iota, iota.injective⟩)
        (powerBatchedWord (fun t i ↦ iota (w t i)) z) (witness z)).card)
    (hbad : ∀ z ∈ challenges,
      ¬ HasExactPowerAgreement domain w iota 2 z (witness z)) :
    (challenges.card : ℚ) ≤
      regularPowerBatchedDerivativeCappedBoundTwo n ℓ 2 2 L A v u h 0 := by
  by_cases hempty : challenges = ∅
  · subst challenges
    simp only [Finset.card_empty, Nat.cast_zero]
    unfold regularPowerBatchedDerivativeCappedBoundTwo
    positivity
  obtain ⟨z₀, hz₀⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
  have hinit := jointInitialJetEquation_ne_zero_of_regular center z₀ Q (jet z₀)
    (hchart z₀ hz₀).2.2.1
  have hτ : TaylorExponentSufficient 1 2 0 := by
    simpa using taylorExponentSufficient_firstOrder_tight 1
  have hdegree : firstOrderCurveJointStageOne 2 ℓ h v u 0 =
      regularPowerBatchedInitialMixedDegreeTwo ℓ 2 v h (τ := 0) := by
    unfold firstOrderCurveJointStageOne regularPowerBatchedInitialMixedDegreeTwo
    rw [cappedBidegreeMixedVolume_eq (by simp [firstOrderTaylorDerivativeCap,
      firstOrderTaylorTotalCap])]
    simp [firstOrderTaylorTotalCap, firstOrderTaylorDerivativeCap,
      regularPowerBatchedCutJetDegree, regularPowerBatchedCutChallengeDegree]
    all_goals ring
  have hoff (S : Finset (Option (Fin 2) → E))
      (hS : ∀ x ∈ S, aeval x (jointInitialJetEquation center Q) = 0 ∧
        aeval x (jointInitialJetSeparant center Q) ≠ 0 ∧
        (∀ l : Fin 2, 2 ≤ l.val → aeval x (jointCommonTaylorNumerator center Q 0 l) = 0) ∧
        x ∉ admissibleChartTupleGraphLocus domain w iota center Q 2 2 L 0)
      (hA : ∀ x ∈ S, A ≤ {i | aeval x (jointTaylorAgreementEquation center Q 2 0
        (Polynomial.C (iota (domain i)))
        (powerBatchedCoordinate (fun t ↦ iota (w t i)))) = 0}.ncard) :
      (S.card : ℚ) ≤ (firstOrderCurveJointStageOne 2 ℓ h v u 0 : ℚ) *
        (((n - L + 1 : ℕ) : ℚ) / ((A - L + 1 : ℕ) : ℚ)) *
          (((n - 2 + 1 : ℕ) : ℚ) / ((A - 2 + 1 : ℕ) : ℚ)) := by
    have hpoint :=
      finite_powerBatched_regular_points_off_admissible_graphs_card_le_firstOrder_of_exponent
      domain w iota center Q 2 2 L A v h 0 hτ (by
        simpa [regularPowerBatchedCutChallengeDegree] using hℓ) (by omega) le_rfl hL hLA hv
        hinit hjet hheight S hS hA
    simpa only [hdegree] using hpoint
  have htupleBound (T : Finset (Fin (ℓ + 1) → F[X]))
      (hT : ∀ P ∈ T,
        IsAdmissibleChartTupleAtExponent domain w iota center Q 2 2 L 0 P) :
      (T.card : ℚ) ≤ (firstOrderCurveFiberStageOne 2 v u 0 : ℚ) *
        (((n - 2 + 1 : ℕ) : ℚ) / ((L - 2 + 1 : ℕ) : ℚ)) := by
    have htuple := admissibleChartTuples_card_le_dimensionSensitive_of_exponent
      domain w iota center Q 2 2 L v 0 hτ (by omega) le_rfl hL (hLA.trans hAn) hjet T hT
    simpa [dimensionSensitiveIncidenceProduct, firstOrderCurveFiberStageOne,
      firstOrderTaylorTotalCap, firstOrderTaylorDerivativeCap, cappedDegreeMixedVolume] using
      htuple
  have hbound := finite_powerBatchedBadChallenges_card_le_of_derivativeCapped_components
    domain w iota center Q 2 2 L A v u 0 hτ le_rfl hL htupleBound
      ((firstOrderCurveJointStageOne 2 ℓ h v u 0 : ℚ) *
        (((n - L + 1 : ℕ) : ℚ) / ((A - L + 1 : ℕ) : ℚ)) *
          (((n - 2 + 1 : ℕ) : ℚ) / ((A - 2 + 1 : ℕ) : ℚ))) hoff
      challenges witness jet hchart hagree hbad
  simpa only [regularPowerBatchedDerivativeCappedBoundTwo] using hbound

/-- Every finite family of regular degree-one bad challenges satisfies the identity-pair
derivative-capped budget. -/
theorem finite_regularPowerBatchedBadChallenges_card_le_identityPair
    [IsAlgClosed E]
    (domain : Fin n ↪ F) (w : Fin (ℓ + 1) → Fin n → F) (iota : F →+* E)
    (Q : DifferentialPolynomial E[X] 1) (L A v u h : ℕ)
    (hL : 2 ≤ L) (hLA : L ≤ A) (hAn : A ≤ n) (hℓ : 0 < ℓ) (hv : 0 < v)
    (hjet : jetTotalDegree Q ≤ v) (hheight : CoeffNatDegreeLE Q h)
    (S : Finset E)
    (hS : ↑S ⊆ regularPowerBatchedBadChallenges domain w iota Q 2 A) :
    (S.card : ℚ) ≤
      regularPowerBatchedDerivativeCappedBoundTwo n ℓ 2 2 L A v u h 0 := by
  classical
  have hτ : TaylorExponentSufficient 1 2 0 := by
    simpa using taylorExponentSufficient_firstOrder_tight 1
  apply finite_regularPowerBatchedBadChallenges_card_le_of_fixed_center_of_exponent
    domain w iota Q 2 2 A 0 le_rfl (by omega)
      (regularPowerBatchedDerivativeCappedBoundTwo n ℓ 2 2 L A v u h 0) ?_ S hS
  intro center challenges witness jet hchart hagree hbad
  exact finite_powerBatchedBadChallenges_card_le_identityPair
    domain w iota center Q L A v u h hL hLA hAn hℓ hv hjet hheight
      challenges witness jet hchart hagree hbad

open Classical in
/-- Outside one bounded set, every regular degree-one solution has exact power agreement at
Taylor exponent zero. -/
theorem exists_exceptional_regularPowerBatchedAgreement_identityPair
    [IsAlgClosed E]
    (domain : Fin n ↪ F) (w : Fin (ℓ + 1) → Fin n → F) (iota : F →+* E)
    (Q : DifferentialPolynomial E[X] 1) (L A v u h : ℕ)
    (hL : 2 ≤ L) (hLA : L ≤ A) (hAn : A ≤ n) (hv : 0 < v)
    (hjet : jetTotalDegree Q ≤ v) (hheight : CoeffNatDegreeLE Q h) :
    ∃ exceptional : Finset E,
      (exceptional.card : ℚ) ≤
        regularPowerBatchedDerivativeCappedBoundTwo n ℓ 2 2 L A v u h 0 ∧
      ∀ z ∉ exceptional, ∀ P : E[X], P.degree < 2 →
        A ≤ (polynomialAgreementSet (domain.trans ⟨iota, iota.injective⟩)
          (powerBatchedWord (fun t i ↦ iota (w t i)) z) P).card →
        differentialSpecialization (challengeSpecialization Q z) P = 0 →
        differentialSpecialization
          (separant (challengeSpecialization Q z) (Fin.last 1)) P ≠ 0 →
        HasExactPowerAgreement domain w iota 2 z P := by
  classical
  by_cases hℓzero : ℓ = 0
  · subst ℓ
    refine ⟨∅, ?_, ?_⟩
    · simp only [Finset.card_empty, Nat.cast_zero]
      unfold regularPowerBatchedDerivativeCappedBoundTwo
      positivity
    · intro z _ P hdegree hagree _ _
      exact hasExactPowerAgreement_singleton domain w iota 2 z P hdegree
        (hL.trans (hLA.trans hagree))
  have hℓ : 0 < ℓ := Nat.pos_of_ne_zero hℓzero
  have hfinite :
      (regularPowerBatchedBadChallenges domain w iota Q 2 A).Finite := by
    apply Set.finite_of_forall_finset_card_le (R := ℚ) fun S hS ↦
      finite_regularPowerBatchedBadChallenges_card_le_identityPair
        domain w iota Q L A v u h hL hLA hAn hℓ hv hjet hheight S hS
  refine ⟨hfinite.toFinset, ?_, ?_⟩
  · apply finite_regularPowerBatchedBadChallenges_card_le_identityPair
      domain w iota Q L A v u h hL hLA hAn hℓ hv hjet hheight
    exact fun z hz ↦ hfinite.mem_toFinset.mp hz
  · intro z hz P hdegree hagree hsol hsep
    by_contra hbad
    apply hz
    exact hfinite.mem_toFinset.mpr ⟨P, hdegree, hagree, hsol, hsep, hbad⟩

end ReedSolomon

end

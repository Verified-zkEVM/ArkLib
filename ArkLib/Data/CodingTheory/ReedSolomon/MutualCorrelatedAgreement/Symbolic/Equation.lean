/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.Symbolic.JetPrefix
public import
ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.Symbolic.RegularEquation
public import
  ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.Symbolic.CoefficientExtension
/-!
# Symbolic line transfer with an arbitrary interpolation height

A sound symbolic equation gives one exceptional set for all close polynomial witnesses.
The budget uses its supplied challenge height and each separant stage's actual jet degree
and differential order. This separates the geometric transfer from the construction of
an interpolation certificate.

## Reading the statement

* `Q` is a polynomial in the evaluation variable and the formal derivatives, with
  polynomial coefficients in the challenge. `hheight` bounds those coefficient degrees.
* `hsound` says that every sufficiently agreeing message is a differential root of the
  specialized equation. It is the interpolation input, not an agreement conclusion.
* `K` is the Taylor truncation length, `k` the message dimension, `A` the requested
  agreement, and `L` the retained pairs' common-agreement threshold.
* Each stage contributes `regularSymbolicMCABound` with its actual jet degree and order.
  The separate `h` term excludes roots of the terminal obstruction.
* The finite exceptional set is chosen before both the challenge and the close message.
  `HasExactCorrelatedPair` gives equality of full agreement sets with a base-field pair.

This uses the proved ordinary source-incidence bound. It does not assert the manuscript's
sharper bidegree-image or cap-sensitive concrete numerical bound.
-/

@[expose] public section

open PolynomialDifferential


noncomputable section

namespace ReedSolomon.HiddenDerivative.SymbolicReceivedInterpolation

open Polynomial MvPolynomial SymbolicSeparantChain SymbolicJetPrefix ReedSolomon

universe u

variable {F E : Type u} [Field F] [Field E] [DecidableEq F] [DecidableEq E]
  [IsAlgClosed E] {n A k ν d : ℕ} {domain : Fin n ↪ F} {f g : Fin n → F}

/-- Transfer a nonzero sound symbolic equation to exact line agreement, retaining its
arbitrary height and every actual separant-stage degree. The soundness assumption concerns
only vanishing of the equation; the conclusion constructs the correlated base-field pair. -/
theorem exists_exceptional_symbolicLineMCA_of_equation
    (Q : DifferentialPolynomial F[X] d) (iota : F →+* E)
    (h : ℕ) (hne : Q ≠ 0) (hweight : jetWeight Q ≤ ν)
    (hheight : ∀ u, (MvPolynomial.coeff u Q).natDegree ≤ h)
    (hsound : ∀ z, ∀ P : E[X], P.degree < k →
      A ≤ (polynomialAgreementSet (mappedDomain domain iota)
        (fun i ↦ iota (f i) + z * iota (g i)) P).card →
      differentialSpecialization (map (Polynomial.eval₂RingHom iota z) Q) P = 0)
    (K L : ℕ) (hK : d < K) (hkK : k ≤ K) (hk : 0 < k) (hkL : k ≤ L)
    (hLA : L ≤ A) (hAn : A ≤ n)
    (hchar : ringChar F = 0 ∨ ν < ringChar F)
    (hbin : ∀ r ≤ d, ∀ i, r < i → i < K → (i.choose r : F) ≠ 0) :
    ∃ stages terminal, Chain Q stages terminal ∧
      ∃ exceptional : Finset E,
        (exceptional.card : ℚ) ≤ (h : ℚ) +
          ∑ stage ∈ stages.toFinset,
            regularSymbolicMCABound n stage.2.val K k L A (jetWeight stage.1) h ∧
        ∀ z ∉ exceptional, ∀ P : E[X], P.degree < k →
          A ≤ (polynomialAgreementSet (mappedDomain domain iota)
            (fun i ↦ iota (f i) + z * iota (g i)) P).card →
          HasExactCorrelatedPair domain f g iota k z P := by
  classical
  obtain ⟨stages, terminal, hc⟩ :=
    exists_symbolic_chain Q hne (hchar.imp_right (fun ht ↦ hweight.trans_lt ht))
  obtain ⟨base, hbase, hcover⟩ := hc.exists_exceptional_regular_coverage hheight iota
  have hstage : ∀ stage : Stage F[X] d, ∃ exceptional : Finset E,
      stage ∈ stages →
        (exceptional.card : ℚ) ≤
          regularSymbolicMCABound n stage.2.val K k L A (jetWeight stage.1) h ∧
        ∀ z ∉ exceptional, ∀ P : E[X], P.degree < k →
          A ≤ (polynomialAgreementSet (mappedDomain domain iota)
            (fun i ↦ iota (f i) + z * iota (g i)) P).card →
          differentialSpecialization (map (Polynomial.eval₂RingHom iota z) stage.1) P = 0 →
          differentialSpecialization
            (separant (map (Polynomial.eval₂RingHom iota z) stage.1) stage.2) P ≠ 0 →
          HasExactCorrelatedPair domain f g iota k z P := by
    intro stage
    by_cases hs : stage ∈ stages
    · obtain ⟨pres, _, hw, _, hh⟩ := exists_stage_presentation hc
        hheight stage hs
      have hstageWeight : jetWeight (extendSymbolicCoefficients iota pres.equation) ≤
          jetWeight stage.1 :=
        (jetWeight_extendSymbolicCoefficients_le iota pres.equation).trans
          hw.le
      have hstagePositive : 0 < jetWeight stage.1 :=
        ((isHighestActiveJet_of_highestActiveJet_eq_some
          (hc.stage_contract stage hs).2.1).1).trans_le
            (jetDegree_le_jetWeight stage.1 stage.2)
      have hbins : ∀ i, stage.2.val < i → i < K → (i.choose stage.2.val : E) ≠ 0 := by
        intro i hi hiK hzero
        apply hbin stage.2.val (Fin.is_le stage.2) i hi hiK
        apply iota.injective
        simpa only [map_natCast, map_zero] using hzero
      obtain ⟨ex, hb, he⟩ := exists_exceptional_regularSymbolicLineMCA domain f g iota
        (extendSymbolicCoefficients iota pres.equation) K k L A (jetWeight stage.1) h
        ((Fin.is_le stage.2).trans_lt hK) hkK hk hkL hLA hAn hstagePositive hstageWeight
        (challengeHeightLE_extendSymbolicCoefficients iota pres.equation hh) hbins
      refine ⟨ex, fun _ ↦ ⟨hb, ?_⟩⟩
      intro z hz P hp ha hsol hsep
      apply he z hz P hp ha
      · change differentialSpecialization
          (map (Polynomial.evalRingHom z) (extendSymbolicCoefficients iota pres.equation))
            P = 0
        rw [specialize_extendSymbolicCoefficients, pres.specialization]
        exact hsol
      · change differentialSpecialization
          (separant (map (Polynomial.evalRingHom z)
            (extendSymbolicCoefficients iota pres.equation)) (Fin.last stage.2.val)) P ≠ 0
        rw [specialize_extendSymbolicCoefficients, pres.separant_specialization]
        exact hsep
    · exact ⟨∅, fun h ↦ (hs h).elim⟩
  choose ex hex using hstage
  refine ⟨stages, terminal, hc, base ∪ stages.toFinset.biUnion ex, ?_, ?_⟩
  · calc
      ((base ∪ stages.toFinset.biUnion ex).card : ℚ) ≤
          (base.card : ℚ) + ((stages.toFinset.biUnion ex).card : ℚ) := by
        exact_mod_cast Finset.card_union_le base (stages.toFinset.biUnion ex)
      _ ≤ (h : ℚ) +
          ∑ stage ∈ stages.toFinset, ((ex stage).card : ℚ) := by
        apply add_le_add
        · exact_mod_cast hbase
        · exact_mod_cast Finset.card_biUnion_le
      _ ≤ _ := by
        apply add_le_add_right
        apply Finset.sum_le_sum
        intro stage hs
        exact (hex stage (List.mem_toFinset.mp hs)).1
  · intro z hz P hp ha
    have hzbase : z ∉ base := fun hm ↦ hz (Finset.mem_union_left _ hm)
    obtain ⟨stage, hs, hsol, hsep⟩ := hcover z hzbase P (hsound z P hp ha)
    apply (hex stage hs).2 z (fun hm ↦ hz (Finset.mem_union_right _
      (Finset.mem_biUnion.mpr ⟨stage, List.mem_toFinset.mpr hs, hm⟩))) P hp ha hsol hsep

end ReedSolomon.HiddenDerivative.SymbolicReceivedInterpolation

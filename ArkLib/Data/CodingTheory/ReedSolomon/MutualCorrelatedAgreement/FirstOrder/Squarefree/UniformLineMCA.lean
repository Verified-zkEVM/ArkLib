/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.FirstOrder.AutomaticHybrid
public import
ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.FirstOrder.Squarefree.UniformMCA
/-!
# Uniform squarefree first-order line agreement

This module connects the height-276 support `(12, 4, 23)` and the exact squarefree hybrid
count to the arbitrary-field line-agreement semantics.  Interpolation happens over the base
field, root analysis happens over an algebraic closure, and the equation-restricted result and
exceptional set descend back to the base field.  The resulting exceptional set precedes both
the challenge and the candidate polynomial and preserves the full agreement set.
-/

@[expose] public section

open PolynomialDifferential Polynomial

namespace ReedSolomon

open HiddenDerivative MvPolynomial HiddenDerivative.SymbolicSeparantChain
  HiddenDerivative.SymbolicWeightedSupportInterpolation

noncomputable section

set_option autoImplicit false

private theorem squarefreeJetWeight_map_eq
    {F E : Type*} [Field F] [Field E] (iota : F →+* E)
    (Q : DifferentialPolynomial F[X] 1) :
    jetWeight (MvPolynomial.map (Polynomial.mapRingHom iota) Q) = jetWeight Q := by
  unfold jetWeight MvPolynomial.weightedTotalDegree
  rw [MvPolynomial.support_map_of_injective Q
    (Polynomial.map_injective iota iota.injective)]

open Classical in
/-- For `k ≥ 2`, the height-276 squarefree certificate gives one base-field exceptional set
of size at most `1325775 n²`, uniformly for every challenge and every close degree-`< k`
candidate.  The recovered pair has equality with the candidate's complete agreement set. -/
theorem exists_uniformFirstOrder_squarefree_lineMCA_of_two_le
    {F : Type*} [Field F] [DecidableEq F]
    (n k A : ℕ) (domain : Fin n ↪ F) (f g : Fin n → F)
    (hn : 2 ≤ n) (hk : 2 ≤ k) (hAn : A ≤ n)
    (hgap : (k : ℝ) + (6 / 25 : ℝ) * n ≤ A)
    (hchar : ringChar F = 0 ∨ max (k - 1) 4 < ringChar F) :
    ∃ exceptional : Finset F,
      (exceptional.card : ℝ) ≤ 1325775 * (n : ℝ) ^ 2 ∧
      ∀ z ∉ exceptional, ∀ P : F[X], P.degree < k →
        A ≤ (polynomialAgreementSet domain (fun i ↦ f i + z * g i) P).card →
        HasExactCorrelatedPair domain f g (RingHom.id F) k z P := by
  classical
  let interpolationD := k - 1
  let recoveryD := k - 1
  have hgapNat : 25 * k + 6 * n ≤ 25 * A := by
    exact_mod_cast (show (25 : ℝ) * k + 6 * n ≤ 25 * A by nlinarith)
  obtain ⟨hInterpolationD, hbudget, hkInterpolationD, hheight⟩ :=
    uniformFirstOrderMCA_parameters n k A hk hAn hgapNat
  have hcert : Nonempty (FirstOrderSymbolicCertificate (F := F)
      interpolationD A 12 4 23 k 276 domain f g
        (firstOrderColumns (D := interpolationD) (A := A) (m := 12) (M := 4) (μ := 23))) :=
    exists_finite_firstOrder_symbolic_certificate_of_heightSlotCount
      (Nat.zero_lt_of_lt hInterpolationD) hbudget hkInterpolationD domain f g hheight
  obtain ⟨cert⟩ := hcert
  let curve := cert.toCurve
  let E := AlgebraicClosure F
  let iota : F →+* E := algebraMap F E
  let QE := MvPolynomial.map (Polynomial.mapRingHom iota) curve.Q
  have hQE : QE ≠ 0 := by
    intro hz
    apply curve.nonzero
    exact MvPolynomial.map_injective (Polynomial.mapRingHom iota)
      (Polynomial.map_injective iota iota.injective) (by simpa only [map_zero] using hz)
  have hweightE : jetWeight QE ≤ 23 := by
    simpa only [QE, squarefreeJetWeight_map_eq] using curve.jetWeight_le
  have hdegreeE : jetDegree QE (1 : Fin 2) ≤ 4 := by
    simpa only [QE, jetDegree_map_eq (Polynomial.mapRingHom iota)
      (Polynomial.map_injective iota iota.injective)] using curve.jetDegree_one_le
  have hheightE : ChallengeHeightLE QE 276 :=
    HiddenDerivative.ChallengeHeightLE.map_coefficients iota curve.challengeDegree_le
  have hRecoveryD : 1 ≤ recoveryD := by dsimp only [recoveryD]; omega
  have hRecoveryDA : recoveryD < A := by
    dsimp only [recoveryD]
    omega
  have hcharRecovery : ringChar F = 0 ∨ max recoveryD 4 < ringChar F := by
    simpa only [recoveryD] using hchar
  obtain ⟨extensionExceptional, hraw, _, _, hgood⟩ :=
    exists_exceptional_firstOrder_hybrid domain f g iota QE hQE hweightE hdegreeE
      hheightE hRecoveryD hRecoveryDA hAn (by norm_num) (by norm_num) hcharRecovery
  obtain ⟨exceptional, hcard, hbase⟩ :=
    exists_exceptional_equation_correlatedAgreement_descend
      domain f g iota curve.Q k A extensionExceptional (by
        intro z hz P hP hagree hroot
        have hkEq : recoveryD + 1 = k := by dsimp only [recoveryD]; omega
        have hPk : P.degree < ((recoveryD + 1 : ℕ) : WithBot ℕ) := by
          rw [hkEq]
          exact hP
        rw [← hkEq]
        apply exactCorrelatedPair_of_powerAgreement_one domain ![f, g] iota z P
        apply hgood z hz P hPk
        · rw [powerBatchedWord_pair_eq]
          exact hagree
        · exact hroot)
  have hsound : ∀ z : F, ∀ P : F[X], P.degree < k →
      A ≤ (polynomialAgreementSet domain (powerBatchedWord ![f, g] z) P).card →
      differentialSpecialization (challengeSpecialization curve.Q z) P = 0 := by
    intro z P hP hagree
    have hline : powerBatchedWord ![f, g] z = (fun i ↦ f i + z * g i) := by
      funext i
      simp [powerBatchedWord, Fin.sum_univ_two]
    have hagreeLine : A ≤
        (polynomialAgreementSet domain (fun i ↦ f i + z * g i) P).card := by
      rwa [hline] at hagree
    have hs := (cert.specialization_sound (RingHom.id F) z).2
      (polynomialAgreementSet domain (fun i ↦ f i + z * g i) P) P hP hagreeLine
      (fun i hi ↦ (Finset.mem_filter.mp hi).2)
    have heval : Polynomial.eval₂RingHom (RingHom.id F) z =
        (Polynomial.aeval z).toRingHom := by
      apply Polynomial.ringHom_ext
      · intro x
        simp
      · simp
    have hcurveQ : curve.Q = cert.Q := rfl
    rw [challengeSpecialization, ← heval, hcurveQ]
    exact hs
  refine ⟨exceptional, ?_, ?_⟩
  · have hcardReal : (exceptional.card : ℝ) ≤ extensionExceptional.card := by
      exact_mod_cast hcard
    apply hcardReal.trans (hraw.trans ?_)
    have hgapRecovery : 25 * recoveryD + 6 * n ≤ 25 * A := by
      dsimp only [recoveryD]
      omega
    exact uniformFirstOrderMCA_hybridEOptimizedRaw_le_ceiling
      hn hRecoveryD hRecoveryDA hAn hgapRecovery
  · intro z hz P hP hagree
    apply hbase z hz P hP hagree
    have hline : powerBatchedWord ![f, g] z = (fun i ↦ f i + z * g i) := by
      funext i
      simp [powerBatchedWord, Fin.sum_univ_two]
    apply hsound z P hP
    rwa [hline]

end

end ReedSolomon

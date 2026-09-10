/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.Symbolic.CurveSupportCertificate
public import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.Symbolic.JetPrefix

/-!
# Actual separant stages of a symbolic curve certificate

The curve certificate provides regular-stage coverage outside a single terminal exceptional
set. The stage list retains actual derivative orders and individual jet-degree caps.
Batching increases only the challenge-height budget; the characteristic condition concerns
the jet cap, not the batching degree.
-/

@[expose] public section

noncomputable section

open PolynomialDifferential

namespace ReedSolomon.HiddenDerivative.SymbolicReceivedCurve

open Polynomial MvPolynomial SymbolicSeparantChain

universe u

variable {F : Type u} [Field F] {n A k ℓ ν d h : ℕ}
  {domain : Fin n ↪ F} {w : Fin n → F[X]}

/-- Universal nonvanishing under specialization implies the symbolic equation is nonzero. -/
theorem Certificate.nonzero (cert : Certificate.{u, u} F A k ℓ ν d h domain w) : cert.Q ≠ 0 := by
  intro hzero
  have h := (cert.specialization_sound (RingHom.id F) 0).1
  rw [hzero, map_zero] at h
  exact h rfl

/-- The support cap bounds the actual jet weight used by separant descent. -/
theorem Certificate.jetWeight_le (cert : Certificate.{u, u} F A k ℓ ν d h domain w) :
    jetWeight cert.Q ≤ ν := by
  apply Finset.sup_le_iff.mpr
  intro u hu
  have h := cert.totalJetDegree_le u hu
  simpa [totalJetDegree, Finsupp.degree_eq_sum, Finsupp.weight_apply,
    Finsupp.sum_fintype] using h

/-- The terminal exceptional set uses the height certified by the interpolation theorem. -/
theorem Certificate.challengeHeight_le (cert : Certificate.{u, u} F A k ℓ ν d h domain w) :
    ∀ u, (MvPolynomial.coeff u cert.Q).natDegree ≤ h :=
  cert.challengeDegree_le

/-- Construct the actual symbolic derivative chain from a proved curve certificate. -/
theorem Certificate.exists_separant_chain (cert : Certificate.{u, u} F A k ℓ ν d h domain w)
    (hchar : ringChar F = 0 ∨ ν < ringChar F) :
    ∃ stages terminal, Chain cert.Q stages terminal := by
  apply exists_symbolic_chain cert.Q cert.nonzero
  exact hchar.imp_right (fun h ↦ cert.jetWeight_le.trans_lt h)

/-- One exceptional set covers every close polynomial simultaneously. Outside it each such
polynomial solves a listed equation with nonzero separant, after any scalar extension. -/
theorem Certificate.exists_exceptional_stage_coverage
    (cert : Certificate.{u, u} F A k ℓ ν d h domain w)
    {stages : List (Stage F[X] d)} {terminal : DifferentialPolynomial F[X] d}
    (hc : Chain cert.Q stages terminal) {E : Type u} [Field E] (ι : F →+* E) :
    ∃ exceptional : Finset E, exceptional.card ≤ h ∧
      ∀ z ∉ exceptional, ∀ (indices : Finset (Fin n)) (P : E[X]),
        P.degree < k → A ≤ indices.card →
        (∀ i ∈ indices, P.eval (ι (domain i)) = (w i).eval₂ ι z) →
        ∃ stage ∈ stages,
          differentialSpecialization
            (MvPolynomial.map (Polynomial.eval₂RingHom ι z) stage.1) P = 0 ∧
          differentialSpecialization
            (separant (MvPolynomial.map (Polynomial.eval₂RingHom ι z) stage.1)
              stage.2) P ≠ 0 := by
  obtain ⟨exceptional, hcard, hcover⟩ :=
    hc.exists_exceptional_regular_coverage cert.challengeHeight_le ι
  refine ⟨exceptional, hcard, ?_⟩
  intro z hz indices P hdegree hcard hagree
  exact hcover z hz P ((cert.specialization_sound ι z).2.2 indices P
    hdegree hcard hagree)

end ReedSolomon.HiddenDerivative.SymbolicReceivedCurve

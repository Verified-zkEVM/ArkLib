/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.ListDecodability.Capacity.EquationBound
public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.Symbolic.CurveSupportCertificate

/-! # Whole-list bounds from constant received-curve certificates -/

@[expose] public section

noncomputable section

namespace ReedSolomon

open Polynomial PolynomialDifferential HiddenDerivative

universe u

open Classical in
/-- Specialize one universally nonzero symbolic equation to explain the entire close list. -/
theorem close_list_bound_of_curve_certificate_of_jetCharacteristic {F : Type u} [Field F]
    {n k A K d ν H : ℕ} {δ : ℝ}
    (domain : Fin n ↪ F) (received : Fin n → F)
    (cert : SymbolicReceivedCurve.Certificate.{u, u} F A k 0 ν d H domain
      (fun i ↦ Polynomial.C (received i)))
    (hk : 0 < k) (hkK : k ≤ K) (hdK : d < K) (hKn : K ≤ n)
    (hkA : k ≤ A) (hAn : A ≤ n) (hν : 0 < ν) (hδ : 0 < δ)
    (hgap : (k : ℝ) + δ * n ≤ A)
    (hchar : ringChar F = 0 ∨ max (K - 1) ν < ringChar F) :
    (closePolynomialSet domain received k A).Finite ∧
      ((closePolynomialSet domain received k A).ncard : ℝ) ≤
        (ν : ℝ) ^ 2 * (2 * ν / δ) ^ d * n ^ d := by
  obtain ⟨hQ, hdegree, hsound⟩ := cert.specialization_sound (RingHom.id F) (0 : F)
  apply close_list_bound_of_equation domain received _ hQ hdegree hk hkK hdK hKn
    hkA hAn hν hδ hgap hchar
  intro P hP
  apply hsound (Finset.univ.filter fun i ↦ P.eval (domain i) = received i) P hP.1 hP.2
  intro i hi
  simpa only [RingHom.id_apply, Polynomial.eval₂_C] using
    (Finset.mem_filter.mp hi).2

end ReedSolomon

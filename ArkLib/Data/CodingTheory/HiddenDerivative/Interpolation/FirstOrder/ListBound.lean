/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.FirstOrder.CurveCertificate
public import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.FirstOrder.HeightCounting
public import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.FirstOrder.CurveHeightCounting
public import ArkLib.Data.CodingTheory.HiddenDerivative.Parameters.FirstOrder.AgreementCounting

/-!
# Cap-sensitive list bounds from first-order certificates

Finite first-order symbolic certificates bound any finite family of polynomials that meet a degree
and agreement threshold. Shifted coefficient-slot surplus constructs such certificates and gives
the sharp and dimension-sensitive first-order list bounds.

## Main statements

* `firstOrder_finite_agreement_solutions_card_le_tight_of_exponent` gives the
  dimension-sensitive bound for any sufficient Taylor exponent.
* `firstOrder_finite_agreement_solutions_card_le_tight` uses the standard exponent `2 * K - 3`.
* `firstOrder_finite_agreement_solutions_card_le_sharp` gives the uniform cap-sensitive bound.
* `finite_firstOrder_list_bound_of_heightSlotCount_sharp` and
  `finite_firstOrder_list_bound_of_shiftedHeightSlotCount_tight` derive these bounds from a
  shifted-slot surplus.

## References

* [DKTZ26]
-/

@[expose] public section

open PolynomialDifferential Polynomial

noncomputable section

namespace ReedSolomon.HiddenDerivative

universe u

variable {F : Type u} [Field F]

open Classical in
/-- A symbolic first-order certificate bounds every finite family of accepted polynomials by the
dimension-sensitive list charge whenever the Taylor exponent is sufficient. -/
theorem firstOrder_finite_agreement_solutions_card_le_tight_of_exponent
    {D A m M μ k h n N K : ℕ}
    {τ : ℕ}
    (domain : Fin n ↪ F) (received : Fin n → F)
    (columns : Fin N → SourceColumn 1)
    (cert : FirstOrderSymbolicCertificate.{u, u} (F := F) D A m M μ k h domain received
      (fun _ ↦ 0) columns)
    (hτ : ∀ r ≤ 1, TaylorExponentSufficient r K τ)
    (hK : 1 < K) (hkK : k ≤ K)
    (hk : 0 < k) (hkA : k ≤ A) (hAn : A ≤ n)
    (hchar : ringChar F = 0 ∨ max (K - 1) μ < ringChar F)
    (S : Finset F[X])
    (hS : ∀ P ∈ S, P.degree < k ∧
      A ≤ ({i : Fin n | P.eval (domain i) = received i} : Set (Fin n)).ncard) :
    (S.card : ℚ) ≤ firstOrderTightListWeight n A k K τ μ M := by
  classical
  let φ := Polynomial.eval₂RingHom (RingHom.id F) 0
  let Q : DifferentialPolynomial F 1 := MvPolynomial.map φ cert.Q
  obtain ⟨hQ, hsound⟩ := cert.specialization_sound (RingHom.id F) 0
  have hdegreeQ : jetTotalDegree Q ≤ μ := by
    rw [jetTotalDegree_le_iff]
    intro u hu
    have huQ : u ∈ cert.Q.support := MvPolynomial.support_map_subset φ cert.Q hu
    simpa [totalJetDegree, Finsupp.degree_eq_sum, Finsupp.some_apply] using
      cert.totalJetDegree_le u huQ
  have hfirstQ : jetDegree Q (1 : Fin 2) ≤ M := by
    apply MvPolynomial.degreeOf_le_iff.mpr
    intro exponent hexponent
    have hsource : exponent ∈ cert.Q.support :=
      MvPolynomial.support_map_subset φ cert.Q hexponent
    have hcap := cert.firstJetDegree_le exponent hsource
    have hfirst : exponent (some (⟨1, by omega⟩ : Fin 2)) ≤ M := by
      simpa only [firstJetExponent_eq_coordinates Nat.one_pos,
        jetExponentCoordinatesEquiv_apply] using hcap
    have hcoord : (⟨1, by omega⟩ : Fin 2) = 1 := Fin.ext rfl
    simpa only [hcoord] using hfirst
  have hsol : ∀ P ∈ S, differentialSpecialization Q P = 0 := by
    intro P hP
    let indices := Finset.univ.filter fun i ↦ P.eval (domain i) = received i
    have hagreement :
        ({i : Fin n | P.eval (domain i) = received i} : Set (Fin n)) =
          (indices : Set (Fin n)) := by
      ext i
      simp [indices]
    have hcard : A ≤ indices.card := by
      have h := (hS P hP).2
      rw [hagreement, Set.ncard_coe_finset] at h
      exact h
    apply hsound indices P (hS P hP).1 hcard
    intro i hi
    simpa using (Finset.mem_filter.mp hi).2
  exact finite_firstOrder_agreement_solutions_card_le_tight_of_exponent
    Q K k μ M τ hQ hdegreeQ hfirstQ hτ domain received hK hkK hk hkA hAn hchar S hsol
    (by
      intro P hP
      exact hS P hP)

open Classical in
/-- The standard exponent `2 * K - 3` gives the dimension-sensitive bound for every finite family
of accepted polynomials. -/
theorem firstOrder_finite_agreement_solutions_card_le_tight
    {D A m M μ k h n N K : ℕ}
    (domain : Fin n ↪ F) (received : Fin n → F)
    (columns : Fin N → SourceColumn 1)
    (cert : FirstOrderSymbolicCertificate.{u, u} (F := F) D A m M μ k h domain received
      (fun _ ↦ 0) columns)
    (hK : 1 < K) (hkK : k ≤ K)
    (hk : 0 < k) (hkA : k ≤ A) (hAn : A ≤ n)
    (hchar : ringChar F = 0 ∨ max (K - 1) μ < ringChar F)
    (S : Finset F[X])
    (hS : ∀ P ∈ S, P.degree < k ∧
      A ≤ ({i : Fin n | P.eval (domain i) = received i} : Set (Fin n)).ncard) :
    (S.card : ℚ) ≤ firstOrderTightListWeight n A k K (2 * K - 3) μ M := by
  exact firstOrder_finite_agreement_solutions_card_le_tight_of_exponent
    domain received columns cert
    (fun r _ ↦ taylorExponentSufficient_two_mul_sub_three r K)
    hK hkK hk hkA hAn hchar S hS

open Classical in
/-- A symbolic first-order certificate gives the uniform cap-sensitive bound for every finite
family of accepted polynomials. -/
theorem firstOrder_finite_agreement_solutions_card_le_sharp
    {D A m M μ k h n N K : ℕ}
    (domain : Fin n ↪ F) (received : Fin n → F)
    (columns : Fin N → SourceColumn 1)
    (cert : FirstOrderSymbolicCertificate.{u, u} (F := F) D A m M μ k h domain received
      (fun _ ↦ 0) columns)
    (hK : 1 < K) (hkK : k ≤ K)
    (hk : 0 < k) (hkA : k ≤ A) (hAn : A ≤ n)
    (hchar : ringChar F = 0 ∨ max (K - 1) μ < ringChar F)
    (S : Finset F[X])
    (hS : ∀ P ∈ S, P.degree < k ∧
      A ≤ ({i : Fin n | P.eval (domain i) = received i} : Set (Fin n)).ncard) :
    (S.card : ℚ) ≤
      ((n * firstOrderListWeight K μ M : ℕ) : ℚ) / ((A - k + 1 : ℕ) : ℚ) := by
  have hτ : ∀ r ≤ 1, TaylorExponentSufficient r K (2 * K) := by
    intro r hr
    exact taylorExponentSufficient_two_mul r K
  have hcount := firstOrder_finite_agreement_solutions_card_le_tight_of_exponent
    domain received columns cert hτ hK hkK hk hkA hAn hchar S hS
  exact hcount.trans (firstOrderTightListWeight_two_mul_le n A k K μ M hk hkA hAn)

open Classical in
/-- A shifted-slot surplus constructs a first-order certificate and gives the uniform
cap-sensitive finite-list bound. -/
theorem finite_firstOrder_list_bound_of_heightSlotCount_sharp
    {D A m M μ k h n K : ℕ}
    (hD : 0 < D) (hbudget : 0 < m * A) (hkD : k ≤ D + 1)
    (domain : Fin n ↪ F) (received : Fin n → F)
    (hheight : firstOrderCurveShiftedRowSlotBound D A m M μ n 1 h <
      firstOrderCurveShiftedHeightSlotCount D A m M μ 1 h)
    (hK : 1 < K) (hkK : k ≤ K)
    (hk : 0 < k) (hkA : k ≤ A) (hAn : A ≤ n)
    (hchar : ringChar F = 0 ∨ max (K - 1) μ < ringChar F)
    (S : Finset F[X])
    (hS : ∀ P ∈ S, P.degree < k ∧
      A ≤ ({i : Fin n | P.eval (domain i) = received i} : Set (Fin n)).ncard) :
    (S.card : ℚ) ≤
      ((n * firstOrderListWeight K μ M : ℕ) : ℚ) / ((A - k + 1 : ℕ) : ℚ) := by
  have hcert : Nonempty (FirstOrderSymbolicCertificate.{u, u} (F := F)
      D A m M μ k h domain received (fun _ ↦ 0)
        (firstOrderColumns (D := D) (A := A) (m := m) (M := M) (μ := μ))) :=
    exists_finite_firstOrder_symbolic_certificate_of_heightSlotCount
      hD hbudget hkD domain received (fun _ ↦ 0) hheight
  obtain ⟨cert⟩ := hcert
  exact firstOrder_finite_agreement_solutions_card_le_sharp domain received
    (firstOrderColumns (D := D) (A := A) (m := m) (M := M) (μ := μ)) cert
      hK hkK hk hkA hAn hchar S hS

open Classical in
/-- A shifted-slot surplus constructs a first-order certificate and gives the
dimension-sensitive finite-list bound for any sufficient Taylor exponent. -/
theorem finite_firstOrder_list_bound_of_shiftedHeightSlotCount_tight
    {D A m M μ k h n K : ℕ}
    (hD : 0 < D) (hbudget : 0 < m * A) (hkD : k ≤ D + 1)
    (domain : Fin n ↪ F) (received : Fin n → F)
    (hheight : firstOrderCurveShiftedRowSlotBound D A m M μ n 1 h <
      firstOrderCurveShiftedHeightSlotCount D A m M μ 1 h)
    (hK : 1 < K) (hkK : k ≤ K)
    (hk : 0 < k) (hkA : k ≤ A) (hAn : A ≤ n)
    (hchar : ringChar F = 0 ∨ max (K - 1) μ < ringChar F)
    (S : Finset F[X])
    (hS : ∀ P ∈ S, P.degree < k ∧
      A ≤ ({i : Fin n | P.eval (domain i) = received i} : Set (Fin n)).ncard) :
    (S.card : ℚ) ≤ firstOrderTightListWeight n A k K (2 * K - 3) μ M := by
  have hcert : Nonempty (FirstOrderSymbolicCertificate.{u, u} (F := F)
      D A m M μ k h domain received (fun _ ↦ 0)
        (firstOrderColumns (D := D) (A := A) (m := m) (M := M) (μ := μ))) :=
    exists_finite_firstOrder_symbolic_certificate_of_heightSlotCount
      hD hbudget hkD domain received (fun _ ↦ 0) hheight
  obtain ⟨cert⟩ := hcert
  exact firstOrder_finite_agreement_solutions_card_le_tight domain received
    (firstOrderColumns (D := D) (A := A) (m := m) (M := M) (μ := μ)) cert
    hK hkK hk hkA hAn hchar S hS

end ReedSolomon.HiddenDerivative

/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Parameters.TaylorCutoff
public import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Parameters.GeometricCounting
public import ArkLib.Data.CodingTheory.ReedSolomon.AgreementList
public import
  ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.Counting.TaylorCharZeroSolutions
/-!
# The prescribed field-independent all-rate polynomial list bound

This is the explicit small-gap bound of [DKTZ26, Corollary A.7], supplying the
field-independent list-size clause of Theorem 1.1. The underlying differential-root
estimate is Theorem A.6. No decoding-time claim is made here.

## References

* [Dao, Kominers, Thaler, and Zheng, *Reed--Solomon List Decoding and Mutual Correlated Agreement
  up to Capacity*][DKTZ26], Theorem A.6 and Corollary A.7.
-/

@[expose] public section

open PolynomialDifferential


noncomputable section
namespace ReedSolomon
open HiddenDerivative
open HiddenDerivative.SymbolicReceivedInterpolation
variable {F : Type*} [Field F]

open Classical in
/-- Every finite family of sufficiently close polynomials obeys the prescribed
field-independent bound in characteristic zero or at least the block length. -/
theorem prescribed_geometric_finite_list_bound
    (δ : ℝ) (n k : ℕ) (domain : Fin n ↪ F) (received : Fin n → F)
    (hδ : 0 < δ) (hδ' : δ < 1 / 4) (hk : 0 < k)
    (hblock : 8 * Nat.ceil
      (100 * (Nat.ceil (Real.exp ((27 / 10) / δ)) : ℝ) ^ 2 *
        harmonicNumber (Nat.ceil (Real.exp ((27 / 10) / δ)) - 1)) ≤ n)
    (hA : agreementThreshold δ n k ≤ n) (hchar : ringChar F = 0 ∨ n ≤ ringChar F)
    (S : Finset (Polynomial F))
    (hS : ∀ P ∈ S, IsAgreementSolution domain received k (agreementThreshold δ n k) P) :
    let d := Nat.ceil (Real.exp ((27 / 10) / δ))
    let m := Nat.ceil (100 * (d : ℝ) ^ 2 * harmonicNumber (d - 1))
    (S.card : ℝ) ≤ 4 * (m : ℝ) ^ 2 * (4 * m / δ) ^ d * n ^ d := by
  classical
  let A := agreementThreshold δ n k
  let d := Nat.ceil (Real.exp ((27 / 10) / δ))
  let m := Nat.ceil (100 * (d : ℝ) ^ 2 * harmonicNumber (d - 1))
  let ν := 2 * m - 1
  let K := max k (Nat.floor (δ * n / 2))
  obtain ⟨hn, _hm, hν, hνm, hνn, hdK, hkK, hKn, hkA, hgap⟩ :=
    prescribed_geometric_parameters δ n k hδ hδ' hk hblock hA
  obtain ⟨cert⟩ := exists_prescribed_symbolic_weightedSupport_certificate
    δ n k domain received (fun _ ↦ 0) hδ hδ' hk hblock hA
  let Q : DifferentialPolynomial F d :=
    MvPolynomial.map (Polynomial.eval₂RingHom (RingHom.id F) 0) cert.Q
  obtain ⟨hQ, hdegreeQ, hsound⟩ := cert.specialization_sound (RingHom.id F) 0
  have hsol : ∀ P ∈ S, differentialSpecialization Q P = 0 := by
    intro P hP
    let indices := Finset.univ.filter fun i ↦ P.eval (domain i) = received i
    apply hsound indices P (hS P hP).1 (hS P hP).2
    intro i hi
    simpa using (Finset.mem_filter.mp hi).2
  have hbin : ∀ r, r ≤ d → ∀ i, r < i → i < K → (i.choose r : F) ≠ 0 := by
    intro r _ i hri hiK
    exact binomial_pivots_of_characteristic
      (hchar.imp_right (fun h ↦ hKn.trans h)) r i hri hiK
  have hcount : (S.card : ℚ) ≤ (ν : ℚ) ^ 2 *
      ((((n * (1 + 2 * K * (ν - 1)) : ℕ) : ℚ) /
        ((A - k + 1 : ℕ) : ℚ)) ^ d) := by
    rcases hchar with hzero | hpos
    · have : CharP F 0 := hzero ▸ inferInstanceAs (CharP F (ringChar F))
      have : CharZero F := CharP.charP_to_charZero F
      exact finite_agreement_solutions_card_le_charZero Q K k ν hdK hkK hQ hdegreeQ
        domain received hk hkA hA hbin S hsol hS
    · have hcontract : IsBelowCharacteristic (k - 1) Q :=
        geometric_below_characteristic Q hk (hkA.trans hA) hνn hdegreeQ hpos
      exact finite_agreement_solutions_card_le Q K k ν hdK hkK hQ hcontract hdegreeQ
        domain received hk hkA hA hbin S hsol hS
  exact geometric_count_le_manuscript_bound hn hν hνm hδ hKn hkA hgap hcount

open Classical in
/-- The entire close polynomial list is finite and satisfies the prescribed bound. -/
theorem prescribed_geometric_close_list_bound
    (δ : ℝ) (n k : ℕ) (domain : Fin n ↪ F) (received : Fin n → F)
    (hδ : 0 < δ) (hδ' : δ < 1 / 4) (hk : 0 < k)
    (hblock : 8 * Nat.ceil
      (100 * (Nat.ceil (Real.exp ((27 / 10) / δ)) : ℝ) ^ 2 *
        harmonicNumber (Nat.ceil (Real.exp ((27 / 10) / δ)) - 1)) ≤ n)
    (hA : agreementThreshold δ n k ≤ n) (hchar : ringChar F = 0 ∨ n ≤ ringChar F) :
    let d := Nat.ceil (Real.exp ((27 / 10) / δ))
    let m := Nat.ceil (100 * (d : ℝ) ^ 2 * harmonicNumber (d - 1))
    (closePolynomialSet domain received k (agreementThreshold δ n k)).Finite ∧
      ((closePolynomialSet domain received k (agreementThreshold δ n k)).ncard : ℝ) ≤
        4 * (m : ℝ) ^ 2 * (4 * m / δ) ^ d * n ^ d := by
  classical
  have hfin := closePolynomialSet_finite domain received
    (show k ≤ agreementThreshold δ n k from Nat.le_add_right _ _)
  refine ⟨hfin, ?_⟩
  rw [Set.ncard_eq_toFinset_card _ hfin]
  apply prescribed_geometric_finite_list_bound δ n k domain received hδ hδ' hk hblock hA hchar
  intro P hP
  have hp := hfin.mem_toFinset.mp hP
  exact hp

end ReedSolomon

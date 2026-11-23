/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.AgreementList
public import ArkLib.Data.CodingTheory.HiddenDerivative.Parameters.WeightedSupport.Capacity
import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.Symbolic.WeightedSupportCertificate

/-!
# Prescribed geometric bounds for Reed–Solomon agreement lists

The prescribed weighted-support parameters produce a differential equation that vanishes on every
polynomial in the agreement list. A positive gap between message dimension and agreement threshold
then gives a field-independent geometric bound for finite sublists and for the complete list in
characteristic zero or characteristic at least the block length.

## Main statements

* `prescribed_geometric_finite_list_bound`: the bound for every finite sublist.
* `prescribed_geometric_close_list_bound`: finiteness and the bound for the complete list.

## References

* [DKT26]
-/

@[expose] public section

open PolynomialDifferential
open Polynomial
open ReedSolomon.HiddenDerivative
open ReedSolomon.HiddenDerivative.WeightedSupportParameters

noncomputable section

namespace ReedSolomon

variable {F : Type*} [Field F]

open Classical in
/-- Every finite sublist of the prescribed close-polynomial set satisfies the
field-independent geometric bound. -/
theorem prescribed_geometric_finite_list_bound
    (δ : ℝ) (n k : ℕ) (domain : Fin n ↪ F) (received : Fin n → F)
    (hδ : 0 < δ) (hδmax : δ < 1 / 4)
    (hblock :
      let d := Nat.ceil (Real.exp (xi / δ))
      let m := Nat.ceil (100 * (d : ℝ) ^ 2 * harmonic (d - 1))
      8 * m ≤ n)
    (hA : capacityAgreementThreshold δ n k ≤ n) (hchar : ringChar F = 0 ∨ n ≤ ringChar F)
    (S : Finset F[X])
    (hS : ∀ P ∈ S, P ∈ closePolynomialSet domain received k (capacityAgreementThreshold δ n k)) :
    let d := Nat.ceil (Real.exp (xi / δ))
    let m := Nat.ceil (100 * (d : ℝ) ^ 2 * harmonic (d - 1))
    (S.card : ℝ) ≤ 4 * (m : ℝ) ^ 2 * (4 * m / δ) ^ d * n ^ d := by
  classical
  let A := capacityAgreementThreshold δ n k
  let d := Nat.ceil (Real.exp (xi / δ))
  let m := Nat.ceil (100 * (d : ℝ) ^ 2 * harmonic (d - 1))
  let ν := 2 * m - 1
  let K := max k (Nat.floor (δ * n / 2))
  obtain ⟨hn, hm, -, hνm, hνn, hdK, hkK, hKn, hkA, hgap⟩ :=
    prescribed_geometric_parameters δ n k hδ hδmax hblock hA
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · have hzero (P : F[X]) (hP : P ∈ S) : P = 0 := by
      simpa only [Polynomial.degreeLT_zero, Submodule.mem_bot] using
        (Polynomial.mem_degreeLT.mpr (hS P hP).1)
    have hcard : (S.card : ℝ) ≤ 1 := by
      exact_mod_cast Finset.card_le_one.mpr
        (fun P hP Q hQ ↦ (hzero P hP).trans (hzero Q hQ).symm)
    have hmOne : (1 : ℝ) ≤ m := by exact_mod_cast (show 1 ≤ m from hm)
    have hnOne : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n from hn)
    have hbase : (1 : ℝ) ≤ 4 * m / δ := (le_div_iff₀ hδ).mpr (by linarith)
    exact hcard.trans (one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le (by nlinarith : (1 : ℝ) ≤ 4 * m ^ 2)
        (one_le_pow₀ hbase)) (one_le_pow₀ hnOne))
  obtain ⟨cert⟩ := exists_prescribed_symbolic_weightedSupport_certificate
    δ n k domain received (fun _ ↦ 0) hδ hδmax hblock
  let Q : DifferentialPolynomial F d :=
    MvPolynomial.map (Polynomial.eval₂RingHom (RingHom.id F) 0) cert.Q
  obtain ⟨hQ, hdegreeQ, hsound⟩ := cert.specialization_sound (RingHom.id F) 0
  have hchar' : ringChar F = 0 ∨ max (K - 1) ν < ringChar F := by
    rcases hchar with hz | hpos
    · exact Or.inl hz
    · have hmax : max (K - 1) ν < n := max_lt_iff.mpr ⟨by omega, hνn⟩
      exact Or.inr (hmax.trans_le hpos)
  let accepts : F[X] → Prop := fun P ↦ P ∈ closePolynomialSet domain received k A
  have hagreement : ∀ P, accepts P ↔
      P.degree < k ∧ A ≤ (Finset.univ.filter fun i ↦
        P.eval (domain i) = received i).card := by
    intro P
    simp [accepts, closePolynomialSet, polynomialAgreementSet]
  have hsolution : ∀ P ∈ S, differentialSpecialization Q P = 0 := by
    intro P hP
    let indices := Finset.univ.filter fun i ↦ P.eval (domain i) = received i
    have hclose := hS P hP
    apply hsound indices P hclose.1 hclose.2
    intro i hi
    simpa [indices, receivedLine] using (Finset.mem_filter.mp hi).2
  have hcount := finite_solutions_card_le_sq_totalJetDegree_of_agreementGap
    Q K k ν hdK hkK hQ hdegreeQ domain received hk hkA hA hKn hgap hδ hchar'
    accepts hagreement S hsolution hS
  change (S.card : ℝ) ≤ 4 * (m : ℝ) ^ 2 * (4 * m / δ) ^ d * n ^ d
  have hνm' : (ν : ℝ) ≤ 2 * m := by
    norm_cast
  have hfactor : (ν : ℝ) ^ 2 ≤ 4 * (m : ℝ) ^ 2 := by nlinarith
  have hbase : 2 * (ν : ℝ) / δ ≤ 4 * (m : ℝ) / δ := by
    apply div_le_div_of_nonneg_right
    · nlinarith
    · exact hδ.le
  calc
    (S.card : ℝ) ≤ (ν : ℝ) ^ 2 * (2 * ν / δ) ^ d * n ^ d := hcount
    _ ≤ 4 * (m : ℝ) ^ 2 * (4 * m / δ) ^ d * n ^ d := by
      gcongr

open Classical in
/-- The complete prescribed close-polynomial set is finite and satisfies the
field-independent geometric bound. -/
theorem prescribed_geometric_close_list_bound
    (δ : ℝ) (n k : ℕ) (domain : Fin n ↪ F) (received : Fin n → F)
    (hδ : 0 < δ) (hδmax : δ < 1 / 4)
    (hblock :
      let d := Nat.ceil (Real.exp (xi / δ))
      let m := Nat.ceil (100 * (d : ℝ) ^ 2 * harmonic (d - 1))
      8 * m ≤ n)
    (hchar : ringChar F = 0 ∨ n ≤ ringChar F) :
    let d := Nat.ceil (Real.exp (xi / δ))
    let m := Nat.ceil (100 * (d : ℝ) ^ 2 * harmonic (d - 1))
    (closePolynomialSet domain received k (capacityAgreementThreshold δ n k)).Finite ∧
      ((closePolynomialSet domain received k (capacityAgreementThreshold δ n k)).ncard : ℝ) ≤
        4 * (m : ℝ) ^ 2 * (4 * m / δ) ^ d * n ^ d := by
  by_cases hA : capacityAgreementThreshold δ n k ≤ n
  swap
  · have hempty : closePolynomialSet domain received k
        (capacityAgreementThreshold δ n k) = ∅ := by
      apply Set.eq_empty_of_forall_notMem
      intro P hP
      have hcard : (polynomialAgreementSet domain received P).card ≤ n := by
        simpa only [Fintype.card_fin] using
          Finset.card_le_univ (polynomialAgreementSet domain received P)
      exact hA (hP.2.trans hcard)
    rw [hempty]
    refine ⟨Set.finite_empty, ?_⟩
    simp only [Set.ncard_empty, Nat.cast_zero]
    positivity
  classical
  have hfinite := closePolynomialSet_finite domain received
    (show k ≤ capacityAgreementThreshold δ n k from Nat.le_add_right _ _)
  refine ⟨hfinite, ?_⟩
  rw [Set.ncard_eq_toFinset_card _ hfinite]
  exact prescribed_geometric_finite_list_bound δ n k domain received hδ hδmax hblock hA
    hchar hfinite.toFinset (fun P hP ↦ hfinite.mem_toFinset.mp hP)

end ReedSolomon

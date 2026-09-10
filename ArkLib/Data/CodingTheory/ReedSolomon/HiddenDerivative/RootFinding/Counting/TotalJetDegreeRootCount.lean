/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
  ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.FiniteField.TotalDegreeWitness
public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.FiniteField.Extension
public import Mathlib.Algebra.MvPolynomial.SchwartzZippel
/-!
# Total-jet-degree differential root count

First-nonzero chain witnesses inject into zeros of the original specialized equation.
Centers with identically zero specialization contribute no witnesses. Thus Schwartz--Zippel
charges the original total jet degree once, with no individual-degree or chain-length factor.

## References

* [Dao, Kominers, Thaler, and Zheng, *Reed--Solomon List Decoding and Mutual Correlated Agreement
  up to Capacity*][DKTZ26], total-jet-degree witness counting for the `4m` list prefactor.
-/

@[expose] public section

open PolynomialDifferential


namespace ReedSolomon.HiddenDerivative

noncomputable section

open Polynomial

variable {F : Type*} [Field F] {d D : ℕ}

/-- Total degree in jet variables only: the distinguished X variable has weight zero. -/
def jetTotalDegree (Q : DifferentialPolynomial F d) : ℕ :=
  Q.weightedTotalDegree (fun v => match v with | none => 0 | some _ => 1)

/-- Support-wise characterization of the total jet degree, for interpolation support bounds. -/
theorem jetTotalDegree_le_iff (Q : DifferentialPolynomial F d) (Δ : ℕ) :
    jetTotalDegree Q ≤ Δ ↔ ∀ u ∈ Q.support, (∑ j : Fin (d + 1), u (some j)) ≤ Δ := by
  classical
  unfold jetTotalDegree MvPolynomial.weightedTotalDegree
  simp [Finset.sup_le_iff, Finsupp.weight_apply, Finsupp.sum_fintype]

/-- Every individual jet degree is bounded by total jet degree. -/
theorem jetDegree_le_total (Q : DifferentialPolynomial F d) (j : Fin (d + 1)) :
    jetDegree Q j ≤ jetTotalDegree Q := by
  classical
  apply MvPolynomial.degreeOf_le_iff.mpr
  intro u hu
  have hb := (jetTotalDegree_le_iff Q _).mp le_rfl u hu
  exact (Finset.single_le_sum (fun k _ => Nat.zero_le (u (some k)))
    (Finset.mem_univ j)).trans hb

/-- Every active separant decreases total jet degree by at least one. -/
theorem separant_total_le (Q : DifferentialPolynomial F d) (j : Fin (d + 1)) :
    jetTotalDegree (separant Q j) ≤ jetTotalDegree Q - 1 := by
  exact weightedTotalDegree_pderiv_le_sub
    (fun v : JetVariable d => match v with | none => 0 | some _ => 1) (some j) Q

/-- Partial specialization cannot increase total degree in jet variables. -/
theorem totalDegree_jetFiberHom_le (Q : DifferentialPolynomial F d) (a : F) :
    (jetFiberHom a Q).totalDegree ≤ jetTotalDegree Q := by
  classical
  conv_lhs => rw [MvPolynomial.as_sum Q]
  rw [map_sum]
  apply MvPolynomial.totalDegree_finsetSum_le
  intro u hu
  rw [jetFiberHom, MvPolynomial.eval₂Hom_monomial]
  refine (MvPolynomial.totalDegree_mul _ _).trans ?_
  rw [MvPolynomial.totalDegree_C, zero_add]
  refine (MvPolynomial.totalDegree_finsetProd _ _).trans ?_
  calc
    ∑ v ∈ u.support, ((match v with
      | none => MvPolynomial.C a
      | some j => MvPolynomial.X j) ^ u v).totalDegree
        ≤ ∑ v ∈ u.support, u v * (match v with | none => 0 | some _ => 1) := by
          apply Finset.sum_le_sum
          intro v _
          cases v with
          | none => simpa using MvPolynomial.totalDegree_pow (MvPolynomial.C a) (u none)
          | some j => simp
    _ = Finsupp.weight (fun v : JetVariable d => match v with | none => 0 | some _ => 1) u := by
      simp [Finsupp.weight_apply, Finsupp.sum]
    _ ≤ jetTotalDegree Q := MvPolynomial.le_weightedTotalDegree _ hu

open Classical in
/-- Finite-grid total-degree zero bound, with no division in the result. -/
theorem card_jet_zeros_le [Fintype F] (Q : MvPolynomial (Fin (d + 1)) F) (hQ : Q ≠ 0) :
    (Finset.univ.filter fun jet => MvPolynomial.eval jet Q = 0).card ≤
      Q.totalDegree * Fintype.card F ^ d := by
  classical
  have h := MvPolynomial.schwartz_zippel_totalDegree hQ (Finset.univ : Finset F)
  simp only [Finset.card_univ, Fintype.piFinset_univ] at h
  have hS : (0 : ℚ≥0) < Fintype.card F := by exact_mod_cast Fintype.card_pos
  have hpow : (0 : ℚ≥0) < (Fintype.card F : ℚ≥0) ^ (d + 1) := pow_pos hS _
  rw [div_le_div_iff₀ hpow hS] at h
  rw [pow_succ] at h
  rw [← mul_assoc] at h
  have hc := (mul_le_mul_iff_left₀ hS).mp h
  exact_mod_cast hc

open Classical in
/-- All first-nonzero chain witnesses above one center fit in the original equation's
 total-degree grid budget, including the identically zero fiber case. -/
theorem card_chainWitness_fiber_le [Fintype F]
    (Q : DifferentialPolynomial F d) (hD : D < ringChar F)
    (roots : Finset (BoundedSolution Q D)) (a : F) :
    (roots.filter fun P : BoundedSolution Q D => ChainWitness Q P.polynomial a).card ≤
      jetTotalDegree Q * Fintype.card F ^ d := by
  classical
  let good := roots.filter fun P : BoundedSolution Q D => ChainWitness Q P.polynomial a
  by_cases hz : jetFiberHom a Q = 0
  · have he : good = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro P hP
      exact (Finset.mem_filter.mp hP).2.jetFiber_ne_zero hz
    simp only [good] at he
    rw [he]
    simp
  · have hi : Set.InjOn
        (fun P : BoundedSolution Q D => polynomialJet (d := d) a P.polynomial) good := by
      intro P hP P' hP' hjet
      apply Subtype.ext
      apply Subtype.ext
      exact (Finset.mem_filter.mp hP).2.polynomial_eq (Finset.mem_filter.mp hP').2
        P.degree_le P'.degree_le hD hjet
    have hc : good.card ≤
        (Finset.univ.filter fun jet => MvPolynomial.eval jet (jetFiberHom a Q) = 0).card := by
      rw [← Finset.card_image_of_injOn hi]
      apply Finset.card_le_card
      intro jet hj
      obtain ⟨P, hP, rfl⟩ := Finset.mem_image.mp hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [eval_jetFiberHom]
      exact (Finset.mem_filter.mp hP).2.evaluation_eq_zero
    exact hc.trans ((card_jet_zeros_le _ hz).trans
      (Nat.mul_le_mul_right _ (totalDegree_jetFiberHom_le Q a)))

/-- Division-free differential root bound with the original total jet degree and the generic
separant budget. Truncated subtraction makes the statement valid even for small witness fields. -/
theorem boundedSolution_sub_mul_le_totalJetDegree [Finite F]
    (Q : DifferentialPolynomial F d) (H Δ : ℕ)
    (hQ : Q ≠ 0) (hchar : IsBelowCharacteristic D Q)
    (hWeight : differentialWeightedDegree D Q - (D - d) ≤ H)
    (hDegree : jetTotalDegree Q ≤ Δ) :
    (Nat.card F - H) * Nat.card (BoundedSolution Q D) ≤ Δ * Nat.card F ^ (d + 1) := by
  classical
  let := Fintype.ofFinite F
  let := Fintype.ofFinite (BoundedSolution Q D)
  let roots : Finset (BoundedSolution Q D) := Finset.univ
  have hex := fun P : BoundedSolution Q D => exists_chainWitness_polynomial Q hQ hchar P
  choose R hR hdeg hcover using hex
  let bad := fun P : BoundedSolution Q D => Finset.univ.filter fun a => (R P).eval a = 0
  have hbad : ∀ P ∈ roots, (bad P).card ≤ H := by
    intro P _
    have hsets : (↑(bad P) : Set F) = (R P).rootSet F := by
      ext a
      simp [bad, Polynomial.mem_rootSet_of_ne (hR P), Polynomial.aeval_def]
    calc
      (bad P).card = Set.ncard (↑(bad P) : Set F) := (Set.ncard_coe_finset _).symm
      _ = Set.ncard ((R P).rootSet F) := congrArg Set.ncard hsets
      _ ≤ (R P).natDegree := Polynomial.ncard_rootSet_le _ _
      _ ≤ H := (hdeg P).trans hWeight
  have hcount := witness_counting_pow_le_of_bad roots (Finset.univ : Finset F) bad
    (fun P a => ChainWitness Q P.polynomial a) H Δ d hbad
    (by
      intro P _ a _ ha
      apply hcover P a
      simpa only [bad, Finset.mem_filter, Finset.mem_univ, true_and] using ha)
    (by
      intro a _
      exact (card_chainWitness_fiber_le Q hchar.1 roots a).trans
        (Nat.mul_le_mul_right _ hDegree))
  simpa only [roots, Finset.card_univ, ← Nat.card_eq_fintype_card, pow_succ,
    Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hcount

/-- Once half the field avoids the separant budget, the bound is twice the total jet degree,
with no extra factor for the number of variables or the derivative chain. -/
theorem natCard_boundedSolution_le_two_totalJetDegree [Finite F]
    (Q : DifferentialPolynomial F d) (H Δ : ℕ)
    (hQ : Q ≠ 0) (hchar : IsBelowCharacteristic D Q)
    (hWeight : differentialWeightedDegree D Q - (D - d) ≤ H)
    (hDegree : jetTotalDegree Q ≤ Δ) (hlarge : 2 * H ≤ Nat.card F) :
    Nat.card (BoundedSolution Q D) ≤ 2 * Δ * Nat.card F ^ d := by
  have hc := boundedSolution_sub_mul_le_totalJetDegree Q H Δ hQ hchar hWeight hDegree
  have hhalf : Nat.card F ≤ 2 * (Nat.card F - H) := by omega
  apply Nat.le_of_mul_le_mul_left ?_ (Nat.card_pos (α := F))
  calc
    Nat.card F * Nat.card (BoundedSolution Q D) ≤
        (2 * (Nat.card F - H)) * Nat.card (BoundedSolution Q D) :=
      Nat.mul_le_mul_right _ hhalf
    _ = 2 * ((Nat.card F - H) * Nat.card (BoundedSolution Q D)) := by ring
    _ ≤ 2 * (Δ * Nat.card F ^ (d + 1)) := Nat.mul_le_mul_left 2 hc
    _ = _ := by rw [pow_succ]; ring

end
end ReedSolomon.HiddenDerivative

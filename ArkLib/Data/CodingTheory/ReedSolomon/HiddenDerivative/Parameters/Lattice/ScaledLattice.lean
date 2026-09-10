/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kai Zhe Zheng, Pratyush Mishra
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.Space
public import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.Counting
public import ArkLib.ToMathlib.Combinatorics.DiscreteSimplex.Basic
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Finsupp.Multiset
public import Mathlib.Data.Nat.Factorial.BigOperators
public import Mathlib.Data.Sym.Card
public import Mathlib.Logic.Equiv.Fin.Basic


/-!
# Scaled exponent lattices

This file provides the combinatorial scaled lattice and its measure-free
cardinality bounds. Coordinate `i` has anisotropic cost `i + 1`.

The definitions and proofs are adapted, with permission, from Kai Zhe
Zheng's `rs-ld-mca` formalization at commit
`9699ee7a6143f6efe1d8cfed84998a4f8c79c40f`. The free-order extension was
contributed through PR 1 by Pratyush Mishra at commit
`b1e346fc39780adb442ed2504a316b32702b97af`; its metadata records Codex as
author and Pratyush Mishra as committer. The project-owner permission
attestation is recorded in `docs/kb/sources/rs-ld-mca/PERMISSION.md`.
-/

@[expose] public section

open PolynomialDifferential


open DiscreteSimplex

namespace ReedSolomon
namespace HiddenDerivative

noncomputable section

open scoped BigOperators

/-- Compatibility name for the canonical tuple of higher-jet exponents. -/
abbrev ScaledExponent (d : ℕ) := HigherJetTuple d

/-- The coordinatewise remainder box for division by the scaled weights.
Its cardinality is `(d - 1)!`. -/
abbrev ScaledResidue (d : ℕ) :=
  (i : Fin (d - 1)) → Fin (i.val + 1)

/-- Total maximum coordinatewise remainder in `ScaledResidue d`. -/
def scaledRemainderSlack (d : ℕ) : ℕ :=
  ∑ i : Fin (d - 1), i.val

/-- Compatibility name for the canonical ordinary degree. -/
abbrev scaledOrdinaryDegree {d : ℕ} (c : ScaledExponent d) : ℕ :=
  higherJetTupleDegree c

/-- Compatibility name for the canonical anisotropic weight. -/
abbrev scaledWeight {d : ℕ} (c : ScaledExponent d) : ℕ :=
  higherJetTupleWeight c

/-- Compatibility name for the canonical finite ambient box. -/
abbrev scaledExponentBox (d z : ℕ) : Finset (ScaledExponent d) :=
  higherJetTupleBox d z

/-- Compatibility name for the canonical executable anisotropic simplex. -/
abbrev scaledExponentFinset (d z : ℕ) : Finset (ScaledExponent d) :=
  weightedHigherJetTuples d z

/-- The part of the anisotropic simplex that also has ordinary degree at
most `S`.  This is the finite set used by the repaired shell argument. -/
def goodScaledExponentFinset (d z S : ℕ) : Finset (ScaledExponent d) :=
  (scaledExponentFinset d z).filter fun c ↦ scaledOrdinaryDegree c ≤ S

/-- Bundled lattice points of scaled weight at most `z`. -/
abbrev BoundedScaledExponent (d z : ℕ) :=
  ↥(scaledExponentFinset d z)

/-- Bundled points satisfying both cutoffs. -/
abbrev GoodScaledExponent (d z S : ℕ) :=
  ↥(goodScaledExponentFinset d z S)

/-- Compatibility name for the canonical weighted higher-jet count. -/
abbrev scaledExponentCount (d z : ℕ) : ℕ :=
  weightedHigherJetCount d z

/-- Number of points satisfying both the scaled and ordinary degree
budgets. -/
def goodScaledExponentCount (d z S : ℕ) : ℕ :=
  (goodScaledExponentFinset d z S).card

@[simp]
theorem mem_scaledExponentBox {d z : ℕ} {c : ScaledExponent d} :
    c ∈ scaledExponentBox d z ↔ ∀ i, c i ≤ z := by
  simp [scaledExponentBox, higherJetTupleBox]

/-- Every coordinate is at most the scaled weight. -/
theorem scaledExponent_coordinate_le_weight {d : ℕ} (c : ScaledExponent d)
    (i : Fin (d - 1)) :
    c i ≤ scaledWeight c := by
  calc
    c i ≤ (i.val + 1) * c i :=
      Nat.le_mul_of_pos_left _ (Nat.succ_pos _)
    _ ≤ ∑ j, (j.val + 1) * c j :=
      Finset.single_le_sum (f := fun j : Fin (d - 1) ↦ (j.val + 1) * c j)
        (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ i)
    _ = scaledWeight c := rfl

@[simp]
theorem mem_scaledExponentFinset {d z : ℕ} {c : ScaledExponent d} :
    c ∈ scaledExponentFinset d z ↔ scaledWeight c ≤ z := by
  exact mem_weightedHigherJetTuples

@[simp]
theorem mem_goodScaledExponentFinset {d z S : ℕ} {c : ScaledExponent d} :
    c ∈ goodScaledExponentFinset d z S ↔
      scaledWeight c ≤ z ∧ scaledOrdinaryDegree c ≤ S := by
  simp [goodScaledExponentFinset]

theorem goodScaledExponentFinset_subset (d z S : ℕ) :
    goodScaledExponentFinset d z S ⊆ scaledExponentFinset d z := by
  intro c hc
  exact (Finset.mem_filter.mp hc).1

theorem goodScaledExponentCount_le (d z S : ℕ) :
    goodScaledExponentCount d z S ≤ scaledExponentCount d z := by
  exact Finset.card_le_card (goodScaledExponentFinset_subset d z S)

theorem scaledExponentFinset_mono (d : ℕ) {z z' : ℕ} (hzz' : z ≤ z') :
    scaledExponentFinset d z ⊆ scaledExponentFinset d z' := by
  intro c hc
  exact mem_scaledExponentFinset.mpr
    ((mem_scaledExponentFinset.mp hc).trans hzz')

theorem scaledExponentCount_mono (d : ℕ) {z z' : ℕ} (hzz' : z ≤ z') :
    scaledExponentCount d z ≤ scaledExponentCount d z' := by
  exact Finset.card_le_card (scaledExponentFinset_mono d hzz')

theorem goodScaledExponentFinset_mono (d : ℕ) {z z' S S' : ℕ}
    (hzz' : z ≤ z') (hSS' : S ≤ S') :
    goodScaledExponentFinset d z S ⊆ goodScaledExponentFinset d z' S' := by
  intro c hc
  rw [mem_goodScaledExponentFinset] at hc ⊢
  exact ⟨hc.1.trans hzz', hc.2.trans hSS'⟩

theorem goodScaledExponentCount_mono (d : ℕ) {z z' S S' : ℕ}
    (hzz' : z ≤ z') (hSS' : S ≤ S') :
    goodScaledExponentCount d z S ≤ goodScaledExponentCount d z' S' := by
  exact Finset.card_le_card
    (goodScaledExponentFinset_mono d hzz' hSS')

/-- Ordinary degree never exceeds anisotropic weight. -/
theorem scaledOrdinaryDegree_le_scaledWeight {d : ℕ} (c : ScaledExponent d) :
    scaledOrdinaryDegree c ≤ scaledWeight c := by
  unfold scaledOrdinaryDegree scaledWeight
  exact Finset.sum_le_sum fun i _ ↦
    Nat.le_mul_of_pos_left _ (Nat.succ_pos _)

/-- If the ordinary-degree cutoff is at least the weight cutoff, it removes no
points. -/
theorem goodScaledExponentFinset_eq_of_le {d z S : ℕ} (hzS : z ≤ S) :
    goodScaledExponentFinset d z S = scaledExponentFinset d z := by
  apply Finset.filter_eq_self.mpr
  intro c hc
  exact (scaledOrdinaryDegree_le_scaledWeight c).trans
    ((mem_scaledExponentFinset.mp hc).trans hzS)

theorem goodScaledExponentCount_eq_of_le {d z S : ℕ} (hzS : z ≤ S) :
    goodScaledExponentCount d z S = scaledExponentCount d z := by
  simp [goodScaledExponentCount, scaledExponentCount, weightedHigherJetCount,
    goodScaledExponentFinset_eq_of_le hzS]

/-! ## Bridge to the interpolation-space exponent representation -/

/-- On the finite coordinate type, ordinary functions and finitely supported
functions carry exactly the same exponent data. -/
noncomputable def scaledExponentEquivHigherJet (d : ℕ) :
    ScaledExponent d ≃ HigherJetExponent d :=
  Finsupp.equivFunOnFinite.symm

@[simp]
theorem scaledExponentEquivHigherJet_apply (d : ℕ)
    (c : ScaledExponent d) (i : Fin (d - 1)) :
    scaledExponentEquivHigherJet d c i = c i := by
  simp [scaledExponentEquivHigherJet]

@[simp]
theorem scaledExponentEquivHigherJet_weight {d : ℕ}
    (c : ScaledExponent d) :
    higherJetWeight (scaledExponentEquivHigherJet d c) = scaledWeight c := by
  rw [higherJetWeight, Finsupp.weight_apply,
    Finsupp.sum_fintype _ _ (fun i ↦ by simp)]
  simp [scaledWeight, higherJetTupleWeight, scaledExponentEquivHigherJet,
    smul_eq_mul, mul_comm]

@[simp]
theorem scaledExponentEquivHigherJet_degree {d : ℕ}
    (c : ScaledExponent d) :
    higherJetDegree (scaledExponentEquivHigherJet d c) =
      scaledOrdinaryDegree c := by
  simp [higherJetDegree, scaledOrdinaryDegree, higherJetTupleDegree,
    Finsupp.degree_eq_sum, scaledExponentEquivHigherJet]

/-- The finite function model and the `Finsupp` model of the good higher-jet
exponents are equivalent, including both budget predicates. -/
noncomputable def goodScaledExponentEquivGoodHigher (d W C : ℕ) :
    GoodScaledExponent d W C ≃ ↥(goodHigherExponents d W C) :=
  (scaledExponentEquivHigherJet d).subtypeEquiv fun c ↦ by
    simp [GoodHigherExponent]

theorem goodScaledExponentCount_eq_card_goodHigherExponents (d W C : ℕ) :
    goodScaledExponentCount d W C = (goodHigherExponents d W C).card := by
  rw [goodScaledExponentCount, ← Fintype.card_coe,
    ← Fintype.card_coe]
  exact Fintype.card_congr (goodScaledExponentEquivGoodHigher d W C)

/-- The scaled function model also computes the canonical executable weighted
higher-jet count when the ordinary cutoff is inactive. -/
theorem scaledExponentCount_eq_weightedHigherJetCount (d W : ℕ) :
    scaledExponentCount d W = weightedHigherJetCount d W := rfl

/-! ## The remainder box -/

/-- The quotient/remainder box has one factor of each size `1, ..., d-1`. -/
theorem card_scaledResidue (d : ℕ) :
    Fintype.card (ScaledResidue d) = (d - 1).factorial := by
  rw [Fintype.card_pi]
  simp only [Fintype.card_fin]
  calc
    (∏ i : Fin (d - 1), (i.val + 1)) =
        ∏ i ∈ Finset.range (d - 1), (i + 1) := by
      simpa using
        Fin.prod_univ_eq_prod_range (fun i : ℕ ↦ i + 1) (d - 1)
    _ = (d - 1).factorial :=
      Finset.prod_range_add_one_eq_factorial (d - 1)

/-! ## Quotient and remainder embeddings -/

/-- Coordinatewise quotient and remainder.  The quotient has scaled weight
at most the original ordinary sum. -/
def ordinaryToScaledWithResidue (d z : ℕ)
    (a : OrdinarySimplex (d - 1) z) :
    BoundedScaledExponent d z × ScaledResidue d :=
  ⟨⟨fun i ↦ a.1 i / (i.val + 1), by
      apply mem_scaledExponentFinset.mpr
      calc
        scaledWeight (fun i ↦ a.1 i / (i.val + 1)) =
            ∑ i, (i.val + 1) * (a.1 i / (i.val + 1)) := rfl
        _ ≤ ∑ i, a.1 i :=
          Finset.sum_le_sum fun i _ ↦ Nat.mul_div_le (a.1 i) (i.val + 1)
        _ ≤ z := a.2⟩,
    fun i ↦ ⟨a.1 i % (i.val + 1),
      Nat.mod_lt _ (Nat.succ_pos i.val)⟩⟩

theorem ordinaryToScaledWithResidue_injective (d z : ℕ) :
    Function.Injective (ordinaryToScaledWithResidue d z) := by
  intro a b hab
  apply Subtype.ext
  funext i
  apply (Nat.divModEquiv (i.val + 1)).injective
  apply Prod.ext
  · simpa [ordinaryToScaledWithResidue] using
      congrArg (fun p ↦ p.1.1 i) hab
  · apply Fin.ext
    simpa [ordinaryToScaledWithResidue] using
      congrArg (fun p ↦ (p.2 i).val) hab

/-- The quotient/remainder embedding gives the lower cardinal comparison. -/
theorem card_ordinarySimplex_le_scaled_mul_factorial (d z : ℕ) :
    Fintype.card (OrdinarySimplex (d - 1) z) ≤
      scaledExponentCount d z * (d - 1).factorial := by
  calc
    Fintype.card (OrdinarySimplex (d - 1) z) ≤
        Fintype.card (BoundedScaledExponent d z × ScaledResidue d) :=
      Fintype.card_le_of_injective _
        (ordinaryToScaledWithResidue_injective d z)
    _ = scaledExponentCount d z * (d - 1).factorial := by
      rw [Fintype.card_prod, card_scaledResidue]
      simp [scaledExponentCount, weightedHigherJetCount]

/-- Recombine a scaled quotient and its remainder.  The possible remainders
enlarge the ordinary sum budget by `scaledRemainderSlack d`. -/
def scaledWithResidueToOrdinary (d z : ℕ)
    (p : BoundedScaledExponent d z × ScaledResidue d) :
    OrdinarySimplex (d - 1) (z + scaledRemainderSlack d) :=
  ⟨fun i ↦ (Nat.divModEquiv (i.val + 1)).symm (p.1.1 i, p.2 i), by
    change (∑ i : Fin (d - 1),
      (Nat.divModEquiv (i.val + 1)).symm (p.1.1 i, p.2 i)) ≤ _
    simp only [Nat.divModEquiv_symm_apply]
    rw [Finset.sum_add_distrib]
    apply Nat.add_le_add
    · simpa [scaledWeight, higherJetTupleWeight, Nat.mul_comm] using
        (mem_scaledExponentFinset.mp p.1.2)
    · unfold scaledRemainderSlack
      exact Finset.sum_le_sum fun i _ ↦ Nat.le_of_lt_succ (p.2 i).2⟩

theorem scaledWithResidueToOrdinary_injective (d z : ℕ) :
    Function.Injective (scaledWithResidueToOrdinary d z) := by
  rintro ⟨c, r⟩ ⟨c', r'⟩ h
  have hfun :
      (scaledWithResidueToOrdinary d z (c, r)).1 =
        (scaledWithResidueToOrdinary d z (c', r')).1 :=
    congrArg Subtype.val h
  apply Prod.ext
  · apply Subtype.ext
    funext i
    have hi := congrFun hfun i
    have hp : (c.1 i, r i) = (c'.1 i, r' i) :=
      (Nat.divModEquiv (i.val + 1)).symm.injective hi
    exact congrArg Prod.fst hp
  · funext i
    have hi := congrFun hfun i
    have hp : (c.1 i, r i) = (c'.1 i, r' i) :=
      (Nat.divModEquiv (i.val + 1)).symm.injective hi
    exact congrArg Prod.snd hp

/-- The reverse quotient/remainder embedding gives the upper cardinal
comparison. -/
theorem scaled_mul_factorial_le_card_ordinarySimplex (d z : ℕ) :
    scaledExponentCount d z * (d - 1).factorial ≤
      Fintype.card
        (OrdinarySimplex (d - 1) (z + scaledRemainderSlack d)) := by
  calc
    scaledExponentCount d z * (d - 1).factorial =
        Fintype.card (BoundedScaledExponent d z × ScaledResidue d) := by
      rw [Fintype.card_prod, card_scaledResidue]
      simp [scaledExponentCount, weightedHigherJetCount]
    _ ≤ Fintype.card
          (OrdinarySimplex (d - 1) (z + scaledRemainderSlack d)) :=
      Fintype.card_le_of_injective _
        (scaledWithResidueToOrdinary_injective d z)

/-- The largest total remainder plus the `d-1` stars-and-bars shifts is the
triangular number occurring in the manuscript's upper bound. -/
theorem scaledRemainderSlack_add_dimension (d : ℕ) :
    scaledRemainderSlack d + (d - 1) = d * (d - 1) / 2 := by
  cases d with
  | zero => simp [scaledRemainderSlack]
  | succ k =>
      change (∑ i : Fin k, i.val) + k = (k + 1) * k / 2
      calc
        (∑ i : Fin k, i.val) + k =
            (∑ i ∈ Finset.range k, i) + k := by
          congr 1
          simpa using Fin.sum_univ_eq_sum_range (fun i : ℕ ↦ i) k
        _ = ∑ i ∈ Finset.range (k + 1), i := by
          rw [Finset.sum_range_succ]
        _ = (k + 1) * k / 2 := by
          simpa using Finset.sum_range_id (k + 1)

/-! ## Integer lattice sandwich -/

/-- The ordinary simplex contains enough points to dominate the `r`-cube
after multiplying its cardinality by `r!`. -/
theorem pow_le_factorial_mul_card_ordinarySimplex (r z : ℕ) :
    z ^ r ≤ r.factorial * Fintype.card (OrdinarySimplex r z) := by
  rw [card_ordinarySimplex,
    ← Nat.ascFactorial_eq_factorial_mul_choose z r,
    Nat.ascFactorial_eq_prod_range]
  calc
    z ^ r = ∏ _i ∈ Finset.range r, z := by simp
    _ ≤ ∏ i ∈ Finset.range r, (z + 1 + i) := by
      exact Finset.prod_le_prod' fun i hi ↦ by
        have hir : i < r := Finset.mem_range.mp hi
        omega

/-- Conversely, the factorial-scaled ordinary simplex fits in the cube whose
side length is its budget plus its dimension. -/
theorem factorial_mul_card_ordinarySimplex_le_pow (r z : ℕ) :
    r.factorial * Fintype.card (OrdinarySimplex r z) ≤ (z + r) ^ r := by
  rw [card_ordinarySimplex,
    ← Nat.ascFactorial_eq_factorial_mul_choose z r,
    Nat.ascFactorial_eq_prod_range]
  calc
    (∏ i ∈ Finset.range r, (z + 1 + i)) ≤
        ∏ _i ∈ Finset.range r, (z + r) := by
      exact Finset.prod_le_prod' fun i hi ↦ by
        have hir : i < r := Finset.mem_range.mp hi
        omega
    _ = (z + r) ^ r := by simp

/-- Measure-free lower lattice estimate. -/
theorem pow_le_scaledExponentCount_mul_factorial_sq (d z : ℕ) :
    z ^ (d - 1) ≤
      scaledExponentCount d z * ((d - 1).factorial ^ 2) := by
  calc
    z ^ (d - 1) ≤
        (d - 1).factorial *
          Fintype.card (OrdinarySimplex (d - 1) z) :=
      pow_le_factorial_mul_card_ordinarySimplex (d - 1) z
    _ ≤ (d - 1).factorial *
          (scaledExponentCount d z * (d - 1).factorial) :=
      Nat.mul_le_mul_left _
        (card_ordinarySimplex_le_scaled_mul_factorial d z)
    _ = scaledExponentCount d z * ((d - 1).factorial ^ 2) := by
      simp [pow_two, Nat.mul_assoc, Nat.mul_comm]

/-- Measure-free upper lattice estimate.  Together with
`pow_le_scaledExponentCount_mul_factorial_sq`, this is the exact integer form
of the anisotropic simplex volume sandwich. -/
theorem scaledExponentCount_mul_factorial_sq_le_pow (d z : ℕ) :
    scaledExponentCount d z * ((d - 1).factorial ^ 2) ≤
      (z + d * (d - 1) / 2) ^ (d - 1) := by
  calc
    scaledExponentCount d z * ((d - 1).factorial ^ 2) =
        (scaledExponentCount d z * (d - 1).factorial) *
          (d - 1).factorial := by
      simp [pow_two, Nat.mul_assoc]
    _ ≤ Fintype.card
          (OrdinarySimplex (d - 1) (z + scaledRemainderSlack d)) *
            (d - 1).factorial :=
      Nat.mul_le_mul_right _
        (scaled_mul_factorial_le_card_ordinarySimplex d z)
    _ = (d - 1).factorial *
          Fintype.card
            (OrdinarySimplex (d - 1) (z + scaledRemainderSlack d)) := by
      rw [Nat.mul_comm]
    _ ≤ (z + scaledRemainderSlack d + (d - 1)) ^ (d - 1) :=
      factorial_mul_card_ordinarySimplex_le_pow
        (d - 1) (z + scaledRemainderSlack d)
    _ = (z + d * (d - 1) / 2) ^ (d - 1) := by
      rw [Nat.add_assoc, scaledRemainderSlack_add_dimension]

/-- The two-sided integer lattice sandwich in one statement. -/
theorem scaledExponentCount_factorial_sq_sandwich (d z : ℕ) :
    z ^ (d - 1) ≤
        scaledExponentCount d z * ((d - 1).factorial ^ 2) ∧
      scaledExponentCount d z * ((d - 1).factorial ^ 2) ≤
        (z + d * (d - 1) / 2) ^ (d - 1) :=
  ⟨pow_le_scaledExponentCount_mul_factorial_sq d z,
    scaledExponentCount_mul_factorial_sq_le_pow d z⟩

end
end HiddenDerivative
end ReedSolomon

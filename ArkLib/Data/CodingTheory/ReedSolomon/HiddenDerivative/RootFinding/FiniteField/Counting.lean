/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Finite witness counting for differential roots

This file isolates the finite double-counting step in differential root bounds. Given a relation
between roots and witnesses, a lower bound on the number of witnesses for each root and an upper
bound on the number of roots for each witness imply a bound on the total number of roots.

The root-finding specialization retains truncated natural subtraction in the factor `S - H`.
Consequently it does not need an assumption `H ≤ S`: when there are more exceptional points than
witness points, the lower bound degenerates safely to zero.
-/

@[expose] public section

namespace ReedSolomon
namespace HiddenDerivative

/-! ### Generic finite incidence counting -/

/-- Double-count a finite relation from uniform bounds on its two kinds of fibers.

Every element of `left` is related to at least `lower` elements of `right`, while every element of
`right` is related to at most `upper` elements of `left`. The conclusion follows by counting the
same incidence relation first over `left` and then over `right`. -/
theorem lower_mul_card_le_card_mul_of_fiber_bounds
    {L R : Type*} (left : Finset L) (right : Finset R) (related : L → R → Prop)
    [DecidableRel related] (lower upper : ℕ)
    (hLower : ∀ x ∈ left, lower ≤ (right.filter (related x)).card)
    (hUpper : ∀ y ∈ right, (left.filter fun x ↦ related x y).card ≤ upper) :
    lower * left.card ≤ right.card * upper := by
  calc
    lower * left.card = ∑ _x ∈ left, lower := by simp [Nat.mul_comm]
    _ ≤ ∑ x ∈ left, (right.filter (related x)).card :=
      Finset.sum_le_sum fun x hx ↦ hLower x hx
    _ = ∑ x ∈ left, ∑ y ∈ right, if related x y then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro x _hx
      exact (Finset.sum_boole (related x) right).symm
    _ = ∑ y ∈ right, ∑ x ∈ left, if related x y then 1 else 0 :=
      Finset.sum_comm
    _ = ∑ y ∈ right, (left.filter fun x ↦ related x y).card := by
      apply Finset.sum_congr rfl
      intro y _hy
      exact Finset.sum_boole (fun x ↦ related x y) left
    _ ≤ ∑ _y ∈ right, upper :=
      Finset.sum_le_sum fun y hy ↦ hUpper y hy
    _ = right.card * upper := by simp

/-! ### Coverage outside root-dependent bad sets -/

/-- Derive the incidence bound from a root-dependent set of bad witnesses.

For each root, at most `H` witnesses are bad and every available witness outside that bad set is
good. Bad sets may depend on the root and may contain elements outside `witnesses`; only their
cardinality is used. This is the form needed when bad witnesses are roots of a separant specialized
along the candidate solution. -/
theorem witness_counting_le_of_bad
    {Root Witness : Type*}
    (roots : Finset Root) (witnesses : Finset Witness) (bad : Root → Finset Witness)
    (isGood : Root → Witness → Prop) [DecidableRel isGood] (H upper : ℕ)
    (hBadCard : ∀ root ∈ roots, (bad root).card ≤ H)
    (hCoverage :
      ∀ root ∈ roots, ∀ witness ∈ witnesses, witness ∉ bad root → isGood root witness)
    (hWitnessFibers :
      ∀ witness ∈ witnesses, (roots.filter fun root ↦ isGood root witness).card ≤ upper) :
    (witnesses.card - H) * roots.card ≤ witnesses.card * upper := by
  classical
  apply lower_mul_card_le_card_mul_of_fiber_bounds roots witnesses isGood
    (witnesses.card - H) upper
  · intro root hroot
    calc
      witnesses.card - H ≤ witnesses.card - (bad root).card :=
        Nat.sub_le_sub_left (hBadCard root hroot) witnesses.card
      _ ≤ (witnesses \ bad root).card := Finset.le_card_sdiff (bad root) witnesses
      _ ≤ (witnesses.filter (isGood root)).card := by
        apply Finset.card_le_card
        intro witness hwitness
        rw [Finset.mem_sdiff] at hwitness
        rw [Finset.mem_filter]
        exact ⟨hwitness.1, hCoverage root hroot witness hwitness.1 hwitness.2⟩
  · exact hWitnessFibers

/-- Root-counting specialization of `witness_counting_le_of_bad` with the per-witness bound
`Δ * S ^ d`, where `S` is exactly the cardinality of the witness set. -/
theorem witness_counting_pow_le_of_bad
    {Root Witness : Type*}
    (roots : Finset Root) (witnesses : Finset Witness) (bad : Root → Finset Witness)
    (isGood : Root → Witness → Prop) [DecidableRel isGood] (H Δ d : ℕ)
    (hBadCard : ∀ root ∈ roots, (bad root).card ≤ H)
    (hCoverage :
      ∀ root ∈ roots, ∀ witness ∈ witnesses, witness ∉ bad root → isGood root witness)
    (hWitnessFibers :
      ∀ witness ∈ witnesses,
        (roots.filter fun root ↦ isGood root witness).card ≤ Δ * witnesses.card ^ d) :
    (witnesses.card - H) * roots.card ≤
      witnesses.card * Δ * witnesses.card ^ d := by
  simpa [Nat.mul_assoc] using
    witness_counting_le_of_bad roots witnesses bad isGood H (Δ * witnesses.card ^ d)
      hBadCard hCoverage hWitnessFibers

/-! ### Root-and-witness specialization -/

/-- Division-free witness bound used by differential root counting.

There are at most `S` available witnesses. Every root has at least `S - H` good witnesses, and
each witness belongs to at most `Δ * S ^ d` roots. No comparison between `H` and `S` is required;
the natural subtraction makes the conclusion valid at the degenerate boundary `S ≤ H`. -/
theorem witness_counting_le
    {Root Witness : Type*} (roots : Finset Root) (witnesses : Finset Witness)
    (isGood : Root → Witness → Prop) [DecidableRel isGood] (S H Δ d : ℕ)
    (hWitnessCard : witnesses.card ≤ S)
    (hRootFibers : ∀ root ∈ roots, S - H ≤ (witnesses.filter (isGood root)).card)
    (hWitnessFibers :
      ∀ witness ∈ witnesses,
        (roots.filter fun root ↦ isGood root witness).card ≤ Δ * S ^ d) :
    (S - H) * roots.card ≤ S * Δ * S ^ d := by
  calc
    (S - H) * roots.card ≤ witnesses.card * (Δ * S ^ d) :=
      lower_mul_card_le_card_mul_of_fiber_bounds roots witnesses isGood (S - H) (Δ * S ^ d)
        hRootFibers hWitnessFibers
    _ ≤ S * (Δ * S ^ d) := Nat.mul_le_mul_right (Δ * S ^ d) hWitnessCard
    _ = S * Δ * S ^ d := by simp [Nat.mul_assoc]

/-- When the bad-witness bound is strictly smaller than the witness-space size, the positive
factor `S - H` can be moved to a natural-number quotient. This is the nonvacuous form used to
extract an explicit root-cardinality bound. -/
theorem card_le_div_of_witness_counting
    {Root Witness : Type*} (roots : Finset Root) (witnesses : Finset Witness)
    (isGood : Root → Witness → Prop) [DecidableRel isGood] (S H Δ d : ℕ)
    (hBadLt : H < S) (hWitnessCard : witnesses.card ≤ S)
    (hRootFibers : ∀ root ∈ roots, S - H ≤ (witnesses.filter (isGood root)).card)
    (hWitnessFibers :
      ∀ witness ∈ witnesses,
        (roots.filter fun root ↦ isGood root witness).card ≤ Δ * S ^ d) :
    roots.card ≤ (S * Δ * S ^ d) / (S - H) := by
  apply (Nat.le_div_iff_mul_le (Nat.sub_pos_of_lt hBadLt)).2
  simpa [Nat.mul_comm] using
    witness_counting_le roots witnesses isGood S H Δ d hWitnessCard hRootFibers hWitnessFibers

/-! ### Boundary canaries -/

namespace CountingCanary

private abbrev asymmetricRelation (root : Fin 2) (witness : Fin 3) : Prop :=
  root.val ≤ witness.val

private instance : DecidableRel asymmetricRelation :=
  fun _root _witness ↦ inferInstance

/-- The two projections of this relation have different fibre profiles. These exact cardinalities
make swapping the root and witness orientations a detectable error. -/
example :
    ((Finset.univ : Finset (Fin 3)).filter (asymmetricRelation 0)).card = 3 ∧
      ((Finset.univ : Finset (Fin 3)).filter (asymmetricRelation 1)).card = 2 ∧
      ((Finset.univ : Finset (Fin 2)).filter fun root ↦ asymmetricRelation root 0).card = 1 ∧
      ((Finset.univ : Finset (Fin 2)).filter fun root ↦ asymmetricRelation root 1).card = 2 := by
  decide

/-- With `H > S`, truncated subtraction makes the total inequality vacuous. -/
example {Root : Type*} (roots : Finset Root) (Δ d : ℕ) :
    (3 - 4) * roots.card ≤ 3 * Δ * 3 ^ d := by
  simp

/-- The boundary `H = S` is vacuous for the same reason. -/
example {Root : Type*} (roots : Finset Root) (S Δ d : ℕ) :
    (S - S) * roots.card ≤ S * Δ * S ^ d := by
  simp

/-- An empty root set satisfies the incidence inequality without any positivity assumption. -/
example (S H Δ d : ℕ) :
    (S - H) * (∅ : Finset PUnit).card ≤ S * Δ * S ^ d := by
  simp

/-- The asymmetric relation has a genuinely positive lower factor when `S = 3` and `H = 1`.
Both root fibres have at least two witnesses, while every witness fibre has at most two roots. -/
example :
    (3 - 1) * (Finset.univ : Finset (Fin 2)).card ≤ 3 * 2 * 3 ^ 0 := by
  exact witness_counting_le (Finset.univ : Finset (Fin 2))
    (Finset.univ : Finset (Fin 3)) asymmetricRelation 3 1 2 0 (by decide) (by decide) (by decide)

private abbrev badByRoot (root : Fin 2) : Finset (Fin 2) :=
  {root}

private abbrev goodAwayFromRoot (root witness : Fin 2) : Prop :=
  witness ≠ root

private instance : DecidableRel goodAwayFromRoot :=
  fun _root _witness ↦ inferInstance

/-- Different roots can have different exceptional witnesses while sharing the same bound `H`.
The bad sets here are provably unequal, so this canary rejects a global-bad-set interface. -/
example : badByRoot 0 ≠ badByRoot 1 := by
  decide

/-- Root-dependent singleton bad sets and their complements attain the incidence bound exactly. -/
example :
    ((Finset.univ : Finset (Fin 2)).card - 1) *
        (Finset.univ : Finset (Fin 2)).card ≤
      (Finset.univ : Finset (Fin 2)).card * 1 := by
  exact witness_counting_le_of_bad (Finset.univ : Finset (Fin 2))
    (Finset.univ : Finset (Fin 2)) badByRoot goodAwayFromRoot 1 1
    (by decide) (by decide) (by decide)

/-- With one witness, no bad witnesses, and zero good roots over that witness, coverage forces the
root set to be empty. This exercises the nonvacuous `H < S` boundary. -/
example {Root : Type*} [DecidableEq Root] (roots : Finset Root)
    (bad : Root → Finset PUnit) (isGood : Root → PUnit → Prop) [DecidableRel isGood]
    (hBadCard : ∀ root ∈ roots, (bad root).card ≤ 0)
    (hCoverage :
      ∀ root ∈ roots, ∀ witness ∈ ({PUnit.unit} : Finset PUnit),
        witness ∉ bad root → isGood root witness)
    (hWitnessFibers :
      ∀ witness ∈ ({PUnit.unit} : Finset PUnit),
        (roots.filter fun root ↦ isGood root witness).card ≤ 0) :
    roots = ∅ := by
  have hCount := witness_counting_le_of_bad roots ({PUnit.unit} : Finset PUnit) bad isGood 0 0
    hBadCard hCoverage hWitnessFibers
  have hCard : roots.card = 0 := by simpa using hCount
  exact Finset.card_eq_zero.mp hCard

/-- At derivative order zero, the power factor specializes to one and the bound reduces to the
expected `S * Δ` incidence bound. -/
example {Root Witness : Type*}
    (roots : Finset Root) (witnesses : Finset Witness) (bad : Root → Finset Witness)
    (isGood : Root → Witness → Prop) [DecidableRel isGood] (H Δ : ℕ)
    (hBadCard : ∀ root ∈ roots, (bad root).card ≤ H)
    (hCoverage :
      ∀ root ∈ roots, ∀ witness ∈ witnesses, witness ∉ bad root → isGood root witness)
    (hWitnessFibers :
      ∀ witness ∈ witnesses, (roots.filter fun root ↦ isGood root witness).card ≤ Δ) :
    (witnesses.card - H) * roots.card ≤ witnesses.card * Δ := by
  simpa using witness_counting_pow_le_of_bad roots witnesses bad isGood H Δ 0
    hBadCard hCoverage (fun witness hwitness ↦ by simpa using hWitnessFibers witness hwitness)

end CountingCanary

end HiddenDerivative
end ReedSolomon

/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fintype.EquivFin

/-!
# Uniform thresholds for a finite family of rate bins

This module isolates the theorem-independent quantifier bookkeeping used when finitely many local
decoding statements are combined into one all-rate statement.  A local statement may choose a
derivative order and a block-length threshold separately for each rate bin.  Taking the two finite
maxima moves both choices in front of the later instance parameters.

Concretely, `exists_uniform_pair_of_exists` implements the quantifier exchange

`(∀ i, ∃ d N, P i d N)`

into

`∃ dMax NMax, ∀ i, ∃ d ≤ dMax, ∃ N ≤ NMax, P i d N`.

The theorem does not assume that `P` is monotone: it retains the original local witnesses.  A
caller with a monotone theorem can subsequently enlarge those witnesses to the selected maxima.
The arithmetic lemmas at the end record a representative consumer.  If every local threshold
already bounds its bin's block count and quadratic budget, then the single conditions
`NMax ≤ n` and `n ≤ q` imply, for every bin, `B < q` and `m * A ≤ q ^ 2`.  The derivative condition
is handled analogously by requiring the uniform derivative maximum to be strictly below `K`.
`exists_two_stage_uniform_thresholds` additionally protects the selected derivative order by `2`
before evaluating the per-bin block-length thresholds at that shared order.

No interpolation, root-counting, or list-decoding conclusion is asserted here.  Those conclusions
remain explicit parameters of downstream theorems.
-/

namespace ReedSolomon
namespace AllRateListDecoding
namespace UniformThresholds

noncomputable section

/-- The maximum of a natural-valued quantity over a finite type.  It is `0` for an empty type.

For an empty index type this is only an upper bound; this module deliberately makes no claim that
the maximum is attained. -/
def familyMaximum {ι : Type*} [Fintype ι] (value : ι → ℕ) : ℕ :=
  Finset.univ.sup value

/-- A finite-family maximum protected by a caller-chosen absolute lower bound. -/
def protectedFamilyMaximum {ι : Type*} [Fintype ι] (minimum : ℕ) (value : ι → ℕ) : ℕ :=
  max minimum (familyMaximum value)

/-- The protected maximum is at least its absolute lower bound. -/
lemma minimum_le_protectedFamilyMaximum {ι : Type*} [Fintype ι]
    (minimum : ℕ) (value : ι → ℕ) :
    minimum ≤ protectedFamilyMaximum minimum value :=
  Nat.le_max_left _ _

/-- Every member of a finite family is bounded by `familyMaximum`. -/
lemma le_familyMaximum {ι : Type*} [Fintype ι] (value : ι → ℕ) (i : ι) :
    value i ≤ familyMaximum value := by
  exact Finset.le_sup (Finset.mem_univ i)

/-- Every family member is bounded by the protected maximum. -/
lemma le_protectedFamilyMaximum {ι : Type*} [Fintype ι]
    (minimum : ℕ) (value : ι → ℕ) (i : ι) :
    value i ≤ protectedFamilyMaximum minimum value :=
  (le_familyMaximum value i).trans (Nat.le_max_right _ _)

/-- `familyMaximum` is below any common upper bound. -/
lemma familyMaximum_le {ι : Type*} [Fintype ι] (value : ι → ℕ) {bound : ℕ}
    (hbound : ∀ i, value i ≤ bound) :
    familyMaximum value ≤ bound := by
  exact Finset.sup_le fun i _ => hbound i

/-- A pointwise upper bound may be checked against the selected family maximum. -/
lemma familyMaximum_le_iff {ι : Type*} [Fintype ι] (value : ι → ℕ) (bound : ℕ) :
    familyMaximum value ≤ bound ↔ ∀ i, value i ≤ bound := by
  constructor
  · intro h i
    exact (le_familyMaximum value i).trans h
  · exact familyMaximum_le value

/-- Simultaneously select uniform upper bounds for two natural-valued finite families. -/
theorem exists_uniform_pair {ι : Type*} [Finite ι] (first second : ι → ℕ) :
    ∃ firstMax secondMax : ℕ,
      (∀ i, first i ≤ firstMax) ∧ (∀ i, second i ≤ secondMax) := by
  let _ := Fintype.ofFinite ι
  exact ⟨familyMaximum first, familyMaximum second,
    le_familyMaximum first, le_familyMaximum second⟩

/-- Move finite per-bin existential choices in front of the bin quantifier.

The conclusion retains the original witnesses because no monotonicity property of `P` is needed.
Thus this theorem is suitable both for threshold-like witnesses and for parameters whose exact
value is used by a downstream conclusion. -/
theorem exists_uniform_pair_of_exists {ι : Type*} [Finite ι]
    (P : ι → ℕ → ℕ → Prop) (hlocal : ∀ i, ∃ first second, P i first second) :
    ∃ firstMax secondMax : ℕ, ∀ i,
      ∃ first, first ≤ firstMax ∧ ∃ second, second ≤ secondMax ∧ P i first second := by
  classical
  let _ := Fintype.ofFinite ι
  let first : ι → ℕ := fun i => (hlocal i).choose
  let second : ι → ℕ := fun i => ((hlocal i).choose_spec).choose
  refine ⟨familyMaximum first, familyMaximum second, fun i => ?_⟩
  refine ⟨first i, le_familyMaximum first i, second i, le_familyMaximum second i, ?_⟩
  exact ((hlocal i).choose_spec).choose_spec

/-- A finite family of eventual predicates has one common threshold.

This is the proposition-valued counterpart of `familyMaximum`: the local conclusions remain
opaque theorem parameters, and only their natural-number thresholds are combined. -/
theorem exists_uniform_of_finite {ι : Type*} [Finite ι] (P : ι → ℕ → Prop)
    (hlocal : ∀ i, ∃ threshold, ∀ n, threshold ≤ n → P i n) :
    ∃ threshold, ∀ i n, threshold ≤ n → P i n := by
  classical
  let _ := Fintype.ofFinite ι
  let localThreshold : ι → ℕ := fun i => (hlocal i).choose
  refine ⟨familyMaximum localThreshold, fun i n hn => ?_⟩
  exact (hlocal i).choose_spec n ((le_familyMaximum localThreshold i).trans hn)

/-- Select a derivative order first, then select a block-length threshold after substituting that
global derivative order into every bin's threshold function.

The conclusion has the V2 quantifier order
`∃ derivOrder, 2 ≤ derivOrder ∧ (∀ i, localOrder i ≤ derivOrder) ∧
  ∃ N, ∀ i, localN i derivOrder ≤ N`.
In particular, `N` is not selected separately at incompatible local derivative orders. -/
theorem exists_two_stage_uniform_thresholds {ι : Type*} [Finite ι]
    (localOrder : ι → ℕ) (localThreshold : ι → ℕ → ℕ) :
    ∃ derivOrder : ℕ, 2 ≤ derivOrder ∧ (∀ i, localOrder i ≤ derivOrder) ∧
      ∃ blockLengthThreshold : ℕ,
        ∀ i, localThreshold i derivOrder ≤ blockLengthThreshold := by
  let _ := Fintype.ofFinite ι
  let derivOrder := protectedFamilyMaximum 2 localOrder
  let blockLengthThreshold := familyMaximum (fun i => localThreshold i derivOrder)
  exact ⟨derivOrder, minimum_le_protectedFamilyMaximum 2 localOrder,
    le_protectedFamilyMaximum 2 localOrder, blockLengthThreshold,
    le_familyMaximum (fun i => localThreshold i derivOrder)⟩

/-- A local derivative order is strictly below `K` when its family maximum is. -/
lemma derivativeOrder_lt_of_uniform {ι : Type*} [Fintype ι]
    (derivativeOrder : ι → ℕ) {K : ℕ} (hK : familyMaximum derivativeOrder < K) (i : ι) :
    derivativeOrder i < K :=
  (le_familyMaximum derivativeOrder i).trans_lt hK

/-- A local strict block bound remains strict after passing through a uniform threshold and then
to a field size: `B i < N i ≤ NMax ≤ n ≤ q`. -/
lemma blockCount_lt_fieldSize_of_uniform {ι : Type*} [Fintype ι]
    (threshold blockCount : ι → ℕ) {blockLength fieldSize : ℕ}
    (hBlockCount : ∀ i, blockCount i < threshold i)
    (hThreshold : familyMaximum threshold ≤ blockLength)
    (hFieldSize : blockLength ≤ fieldSize) (i : ι) :
    blockCount i < fieldSize := by
  exact (hBlockCount i).trans_le
    ((le_familyMaximum threshold i).trans (hThreshold.trans hFieldSize))

/-- A local quadratic budget remains valid after passing through a uniform threshold and then to
the field size: `m i * A i ≤ N i ^ 2 ≤ NMax ^ 2 ≤ n ^ 2 ≤ q ^ 2`. -/
lemma quadraticBudget_le_fieldSize_sq_of_uniform {ι : Type*} [Fintype ι]
    (threshold multiplicity area : ι → ℕ) {blockLength fieldSize : ℕ}
    (hBudget : ∀ i, multiplicity i * area i ≤ threshold i ^ 2)
    (hThreshold : familyMaximum threshold ≤ blockLength)
    (hFieldSize : blockLength ≤ fieldSize) (i : ι) :
    multiplicity i * area i ≤ fieldSize ^ 2 := by
  have hLocal : threshold i ≤ fieldSize :=
    (le_familyMaximum threshold i).trans (hThreshold.trans hFieldSize)
  exact (hBudget i).trans (Nat.pow_le_pow_left hLocal 2)

/-- One uniform derivative maximum and one uniform block-length maximum discharge the standard
three side conditions for every member of a finite family.

Quantifier order is explicit: all five per-bin families and the two maxima are fixed before the
instance parameters `K`, `blockLength`, and `fieldSize`.  The caller supplies only the local
bounds and the later inequalities `derivativeMaximum < K` and
`blockLengthThreshold ≤ blockLength ≤ fieldSize`. -/
theorem representative_conditions_of_uniform_thresholds
    {ι : Type*} [Fintype ι]
    (derivativeOrder threshold blockCount multiplicity area : ι → ℕ)
    {K blockLength fieldSize : ℕ}
    (hDerivative : familyMaximum derivativeOrder < K)
    (hBlockCount : ∀ i, blockCount i < threshold i)
    (hBudget : ∀ i, multiplicity i * area i ≤ threshold i ^ 2)
    (hThreshold : familyMaximum threshold ≤ blockLength)
    (hFieldSize : blockLength ≤ fieldSize) :
    ∀ i, derivativeOrder i < K ∧ blockCount i < fieldSize ∧
      multiplicity i * area i ≤ fieldSize ^ 2 := by
  intro i
  exact ⟨derivativeOrder_lt_of_uniform derivativeOrder hDerivative i,
    blockCount_lt_fieldSize_of_uniform threshold blockCount hBlockCount hThreshold hFieldSize i,
    quadraticBudget_le_fieldSize_sq_of_uniform
      threshold multiplicity area hBudget hThreshold hFieldSize i⟩

/-- Lift caller-supplied, per-bin side conditions at `n` to a later field size `q ≥ n`.

The hypotheses make the separation of responsibilities explicit.  This module chooses a common
threshold and performs monotone arithmetic; the caller must prove the donor-specific facts
`d < K i n`, `B i n < n`, and `m i * A i n ≤ n ^ 2` once `n` clears the local threshold. -/
theorem representative_conditions_of_eventual_uniform
    {ι : Type*} [Fintype ι]
    (derivOrder : ℕ) (localThreshold : ι → ℕ)
    (K blockCount area : ι → ℕ → ℕ) (multiplicity : ι → ℕ)
    {blockLength fieldSize : ℕ}
    (hLocal : ∀ i n, localThreshold i ≤ n →
      derivOrder < K i n ∧ blockCount i n < n ∧
        multiplicity i * area i n ≤ n ^ 2)
    (hThreshold : familyMaximum localThreshold ≤ blockLength)
    (hFieldSize : blockLength ≤ fieldSize) :
    ∀ i, derivOrder < K i blockLength ∧ blockCount i blockLength < fieldSize ∧
      multiplicity i * area i blockLength ≤ fieldSize ^ 2 := by
  intro i
  have hClears : localThreshold i ≤ blockLength :=
    (le_familyMaximum localThreshold i).trans hThreshold
  rcases hLocal i blockLength hClears with ⟨hDerivative, hBlockCount, hBudget⟩
  exact ⟨hDerivative, hBlockCount.trans_le hFieldSize,
    hBudget.trans (Nat.pow_le_pow_left hFieldSize 2)⟩

/-- Canary for fold direction and the empty-family default: the maximum of `[2, 9, 4]` is `9`. -/
example :
    familyMaximum (fun i : Fin 3 => if i = 0 then 2 else if i = 1 then 9 else 4) = 9 := by
  decide

/-- Canary for the consumer-shaped theorem at the boundary `N = n = q = 2`.  The strict block
count conclusion and the non-strict quadratic conclusion must both survive the lift to `q`. -/
example : ∀ _i : Fin 1, (1 : ℕ) < 2 ∧ (1 : ℕ) < 2 ∧ (2 : ℕ) * 2 ≤ 2 ^ 2 := by
  apply representative_conditions_of_eventual_uniform
    (derivOrder := 1) (localThreshold := fun _ : Fin 1 => 2)
    (K := fun _ _ => 2) (blockCount := fun _ _ => 1)
    (area := fun _ _ => 2) (multiplicity := fun _ => 2)
    (blockLength := 2) (fieldSize := 2)
  · intro _ n hn
    refine ⟨by decide, (show 1 < 2 by decide).trans_le hn, ?_⟩
    exact (show 2 * 2 ≤ 2 ^ 2 by decide).trans (Nat.pow_le_pow_left hn 2)
  · apply familyMaximum_le
    intro _
    exact le_rfl
  · exact le_rfl

end
end UniformThresholds
end AllRateListDecoding
end ReedSolomon

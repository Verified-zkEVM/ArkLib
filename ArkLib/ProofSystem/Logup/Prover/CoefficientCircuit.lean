/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
module

public import ArkLib.ProofSystem.Logup.Algebra.Grouped
public import ArkLib.ToCompPoly.Univariate.ArithmeticFractionFoldCost

/-!
# Padded coefficients for the grouped constraint circuit

The circuit consumes already bound denominator, weight, helper, and equality-kernel rows.
It keeps padding through every operation and interprets as a formal polynomial, including
when denominator polynomials vanish. No polynomial evaluation is used to identify coefficients.
-/

@[expose] public section

open CompPoly CPolynomial
namespace Logup.Prover.CoefficientCircuit

variable {R : Type*} [CommRing R] {T K : ℕ}

/-- Cross-multiply one group of already bound coefficient rows. -/
def groupFractionRaw (group : List (Fin T))
    (denominator weight : Vector (Raw R) T) : FractionPair (Raw R) :=
  Raw.fractionSum (group.map fun i => ⟨weight.get i, denominator.get i⟩)

/-- Multiply a helper row by its group denominator and subtract its numerator. -/
def residualRaw (group : List (Fin T)) (denominator weight : Vector (Raw R) T)
    (helper : Raw R) : Raw R :=
  let fraction := groupFractionRaw group denominator weight
  Raw.subRaw (Raw.mulRaw helper fraction.denominator) fraction.numerator

/-- Stream weighted residual coefficients through a single padded accumulator. -/
def batchRaw (indices : List (Fin K)) (groups : Vector (List (Fin T)) K)
    (lambda : Vector R K) (denominator weight : Vector (Raw R) T)
    (helper : Vector (Raw R) K) (acc : Raw R) : Raw R :=
  indices.foldl (fun a k => Raw.addRaw a (Raw.smul (lambda.get k)
    (residualRaw (groups.get k) denominator weight (helper.get k)))) acc

/-- An initially empty streamed batch equals the padded sum of its weighted residuals. -/
theorem batchRaw_eq_sumRaw (indices : List (Fin K)) (groups : Vector (List (Fin T)) K)
    (lambda : Vector R K) (denominator weight : Vector (Raw R) T)
    (helper : Vector (Raw R) K) :
    batchRaw indices groups lambda denominator weight helper #[] =
      Raw.sumRaw (indices.map fun k => Raw.smul (lambda.get k)
        (residualRaw (groups.get k) denominator weight (helper.get k))) := by
  simp only [batchRaw, Raw.sumRaw, List.foldl_map]

/-- Reconstruct padded coefficients from the helper sum and kernel-weighted residuals. -/
def circuitRaw (groups : Vector (List (Fin T)) K) (kernel : Raw R)
    (lambda : Vector R K) (denominator weight : Vector (Raw R) T)
    (helper : Vector (Raw R) K) : Raw R :=
  Raw.addRaw (Raw.sumRaw ((List.finRange K).map helper.get))
    (Raw.mulRaw kernel
      (batchRaw (List.finRange K) groups lambda denominator weight helper #[]))

/-- Formal interpretation preserves the denominator-table fraction fold. -/
theorem toPoly_groupFractionRaw (group : List (Fin T)) (alpha : R)
    (denominator weight : Vector (Raw R) T) (value : Fin T → Polynomial R)
    (hden : ∀ i, Raw.toPoly (denominator.get i) = Polynomial.C alpha - value i) :
    FractionPair.map Raw.toPoly (groupFractionRaw group denominator weight) =
      groupFraction group (Polynomial.C alpha) value (fun i => Raw.toPoly (weight.get i)) := by
  rw [groupFractionRaw, Raw.map_toPoly_fractionSum, List.map_map]
  unfold groupFraction
  congr 1
  apply List.map_congr_left
  intro i _
  apply FractionPair.ext
  · rfl
  · exact hden i

/-- Formal interpretation preserves the local denominator-cleared residual. -/
theorem toPoly_residualRaw (group : List (Fin T)) (alpha : R)
    (denominator weight : Vector (Raw R) T) (helper : Raw R) (value : Fin T → Polynomial R)
    (hden : ∀ i, Raw.toPoly (denominator.get i) = Polynomial.C alpha - value i) :
    Raw.toPoly (residualRaw group denominator weight helper) =
      groupResidual group (Polynomial.C alpha) value (fun i => Raw.toPoly (weight.get i))
        (Raw.toPoly helper) := by
  have hg := toPoly_groupFractionRaw group alpha denominator weight value hden
  have hn := congrArg FractionPair.numerator hg
  have hd := congrArg FractionPair.denominator hg
  simp only [FractionPair.map] at hn hd
  simp only [residualRaw, Raw.toPoly_subRaw, Raw.toPoly_mulRaw, groupResidual, hn, hd]

/-- Formal interpretation preserves the complete grouped circuit with a supplied kernel. -/
theorem toPoly_circuitRaw (groups : Vector (List (Fin T)) K) (alpha : R) (kernel : Raw R)
    (lambda : Vector R K) (denominator weight : Vector (Raw R) T) (helper : Vector (Raw R) K)
    (value : Fin T → Polynomial R)
    (hden : ∀ i, Raw.toPoly (denominator.get i) = Polynomial.C alpha - value i) :
    Raw.toPoly (circuitRaw groups kernel lambda denominator weight helper) =
      reconstructWithKernel groups (Polynomial.C alpha) (Raw.toPoly kernel)
        (fun k => Polynomial.C (lambda.get k)) value (fun i => Raw.toPoly (weight.get i))
        (fun k => Raw.toPoly (helper.get k)) := by
  simp only [circuitRaw, batchRaw_eq_sumRaw, Raw.toPoly_addRaw, Raw.toPoly_sumRaw,
    Raw.toPoly_mulRaw,
    List.map_map, Function.comp_def, Raw.toPoly_smul,
    toPoly_residualRaw (alpha := alpha) (value := value) (hden := hden)]
  rw [← Fin.sum_univ_def, ← Fin.sum_univ_def]
  rfl

/-- Without an original value table, the same circuit can be interpreted using zero alpha
and negated denominator polynomials. This identity is formal and has no pole hypotheses. -/
theorem toPoly_circuitRaw_denominator (groups : Vector (List (Fin T)) K) (kernel : Raw R)
    (lambda : Vector R K) (denominator weight : Vector (Raw R) T)
    (helper : Vector (Raw R) K) :
    Raw.toPoly (circuitRaw groups kernel lambda denominator weight helper) =
      reconstructWithKernel groups 0 (Raw.toPoly kernel)
        (fun k => Polynomial.C (lambda.get k)) (fun i => -Raw.toPoly (denominator.get i))
        (fun i => Raw.toPoly (weight.get i)) (fun k => Raw.toPoly (helper.get k)) := by
  simpa only [map_zero] using toPoly_circuitRaw groups 0 kernel lambda denominator weight
    helper (fun i => -Raw.toPoly (denominator.get i)) (by intro i; simp)

/-- An affine group retains at most one more coefficient than its occurrence count. -/
theorem size_groupFractionRaw_le (group : List (Fin T))
    (denominator weight : Vector (Raw R) T)
    (hden : ∀ i, (denominator.get i).size ≤ 2)
    (hweight : ∀ i, (weight.get i).size ≤ 2) :
    (groupFractionRaw group denominator weight).numerator.size ≤ group.length + 1 ∧
      (groupFractionRaw group denominator weight).denominator.size ≤ group.length + 1 := by
  have h := Raw.size_fractionSum_le
    (group.map fun i => (⟨weight.get i, denominator.get i⟩ : FractionPair (Raw R))) (by
      intro p hp
      obtain ⟨i, _, rfl⟩ := List.mem_map.mp hp
      exact ⟨hweight i, hden i⟩)
  simpa only [groupFractionRaw, List.length_map] using h

/-- An affine helper increases its group's padded width by at most one. -/
theorem size_residualRaw_le (group : List (Fin T))
    (denominator weight : Vector (Raw R) T) (helper : Raw R)
    (hden : ∀ i, (denominator.get i).size ≤ 2)
    (hweight : ∀ i, (weight.get i).size ≤ 2) (hhelper : helper.size ≤ 2) :
    (residualRaw group denominator weight helper).size ≤ group.length + 2 := by
  have hg := size_groupFractionRaw_le group denominator weight hden hweight
  have hm := Raw.size_mulRaw_le helper (groupFractionRaw group denominator weight).denominator
  rw [residualRaw, Raw.size_subRaw]
  apply max_le <;> omega

/-- Bounded affine residuals preserve the batch accumulator width after every prefix. -/
theorem size_batchRaw_le (indices : List (Fin K))
    (groups : Vector (List (Fin T)) K) (lambda : Vector R K)
    (denominator weight : Vector (Raw R) T) (helper : Vector (Raw R) K) (acc : Raw R)
    (ell : ℕ) (hgroups : ∀ k, (groups.get k).length ≤ ell)
    (hden : ∀ i, (denominator.get i).size ≤ 2)
    (hweight : ∀ i, (weight.get i).size ≤ 2)
    (hhelper : ∀ k, (helper.get k).size ≤ 2) (hacc : acc.size ≤ ell + 2) :
    (batchRaw indices groups lambda denominator weight helper acc).size ≤ ell + 2 := by
  induction indices generalizing acc with
  | nil => exact hacc
  | cons k indices ih =>
    apply ih
    rw [Raw.size_addRaw, Raw.size_smul]
    apply max_le hacc
    exact (size_residualRaw_le _ _ _ _ hden hweight (hhelper k)).trans
      (by have := hgroups k; omega)


/-- Bounded groups and affine rows give at most `ell + 3` stored coefficients, even for
empty groups, zero denominators, and padded zero rows. -/
theorem size_circuitRaw_le (groups : Vector (List (Fin T)) K) (kernel : Raw R)
    (lambda : Vector R K) (denominator weight : Vector (Raw R) T)
    (helper : Vector (Raw R) K) (ell : ℕ)
    (hgroups : ∀ k, (groups.get k).length ≤ ell)
    (hden : ∀ i, (denominator.get i).size ≤ 2)
    (hweight : ∀ i, (weight.get i).size ≤ 2)
    (hhelper : ∀ k, (helper.get k).size ≤ 2) (hkernel : kernel.size ≤ 2) :
    (circuitRaw groups kernel lambda denominator weight helper).size ≤ ell + 3 := by
  have hh : (Raw.sumRaw ((List.finRange K).map helper.get)).size ≤ 2 := by
    apply Raw.size_sumRaw_le
    intro p hp
    obtain ⟨k, _, rfl⟩ := List.mem_map.mp hp
    exact hhelper k
  have hb : (Raw.sumRaw ((List.finRange K).map fun k =>
      Raw.smul (lambda.get k)
        (residualRaw (groups.get k) denominator weight (helper.get k)))).size ≤ ell + 2 := by
    apply Raw.size_sumRaw_le
    intro p hp
    obtain ⟨k, _, rfl⟩ := List.mem_map.mp hp
    rw [Raw.size_smul]
    exact (size_residualRaw_le _ _ _ _ hden hweight (hhelper k)).trans
      (by have := hgroups k; omega)
  have hm := Raw.size_mulRaw_le kernel
    (Raw.sumRaw ((List.finRange K).map fun k =>
      Raw.smul (lambda.get k)
        (residualRaw (groups.get k) denominator weight (helper.get k))))
  rw [circuitRaw, batchRaw_eq_sumRaw, Raw.size_addRaw]
  apply max_le <;> omega

section Arithmetic

open OracleComp OracleSpec

variable {F : Type} [CommRing F] [Inv F] [DecidableEq F]

/-- Execute the group fraction circuit without canonicalizing either coefficient array. -/
def groupFractionProgram (group : List (Fin T))
    (denominator weight : Vector (Raw F) T) :
    OracleComp (ArithmeticSpec F) (FractionPair (Raw F)) :=
  Arithmetic.fractionSum (group.map fun i => ⟨weight.get i, denominator.get i⟩)

/-- Execute a helper residual with its affine helper factor on the left. -/
def residualProgram (group : List (Fin T)) (denominator weight : Vector (Raw F) T)
    (helper : Raw F) : OracleComp (ArithmeticSpec F) (Raw F) := do
  let fraction ← groupFractionProgram group denominator weight
  let product ← Arithmetic.mulRaw helper fraction.denominator
  let residual ← Arithmetic.subRaw product.val fraction.numerator
  pure residual.val

/-- Executing the group program returns the explicit padded group fraction. -/
theorem profileArithmetic_groupFractionProgram_fst (group : List (Fin T))
    (denominator weight : Vector (Raw F) T) :
    (profileArithmetic (groupFractionProgram group denominator weight)).1 =
      groupFractionRaw group denominator weight :=
  Arithmetic.profileArithmetic_fractionSum_fst _

/-- Executing the residual program returns the explicit padded residual. -/
theorem profileArithmetic_residualProgram_fst (group : List (Fin T))
    (denominator weight : Vector (Raw F) T) (helper : Raw F) :
    (profileArithmetic (residualProgram group denominator weight helper)).1 =
      residualRaw group denominator weight helper := by
  simp [residualProgram, profileArithmetic_bind, profileArithmetic_groupFractionProgram_fst,
    residualRaw]

/-- Accumulate weighted residuals as they are computed, retaining one batch accumulator. -/
def batchFromProgram (indices : List (Fin K)) (groups : Vector (List (Fin T)) K)
    (lambda : Vector F K) (denominator weight : Vector (Raw F) T)
    (helper : Vector (Raw F) K) (acc : Raw F) :
    OracleComp (ArithmeticSpec F) (Raw F) :=
  indices.foldlM (fun a k => do
    Arithmetic.tick
    let residual ← residualProgram (groups.get k) denominator weight (helper.get k)
    let weighted ← Arithmetic.smulRaw (lambda.get k) residual
    let next ← Arithmetic.addRaw a weighted.val
    pure next.val) acc

/-- The streamed batch accumulator refines the corresponding padded left fold. -/
theorem profileArithmetic_batchFromProgram_fst (indices : List (Fin K))
    (groups : Vector (List (Fin T)) K) (lambda : Vector F K)
    (denominator weight : Vector (Raw F) T) (helper : Vector (Raw F) K) (acc : Raw F) :
    (profileArithmetic
      (batchFromProgram indices groups lambda denominator weight helper acc)).1 =
      indices.foldl (fun a k => Raw.addRaw a (Raw.smul (lambda.get k)
        (residualRaw (groups.get k) denominator weight (helper.get k)))) acc := by
  induction indices generalizing acc with
  | nil => rfl
  | cons k indices ih =>
    simp only [batchFromProgram, List.foldlM_cons, profileArithmetic_bind,
      profileArithmetic_tick, profileArithmetic_residualProgram_fst,
      profileArithmetic_certified_val, profileArithmetic_pure, List.foldl_cons]
    exact ih _

/-- Execute the grouped coefficient circuit. Residuals are streamed into one batch array;
no list of residual coefficient arrays is constructed. -/
def circuitProgram (groups : Vector (List (Fin T)) K) (kernel : Raw F)
    (lambda : Vector F K) (denominator weight : Vector (Raw F) T)
    (helper : Vector (Raw F) K) : OracleComp (ArithmeticSpec F) (Raw F) := do
  let helpers ← Arithmetic.sumRaw ((List.finRange K).map helper.get)
  let batch ← batchFromProgram (List.finRange K) groups lambda denominator weight helper #[]
  let product ← Arithmetic.mulRaw kernel batch
  let result ← Arithmetic.addRaw helpers product.val
  pure result.val

/-- Executing the streamed arithmetic circuit returns precisely its padded coefficients. -/
theorem profileArithmetic_circuitProgram_fst (groups : Vector (List (Fin T)) K)
    (kernel : Raw F) (lambda : Vector F K) (denominator weight : Vector (Raw F) T)
    (helper : Vector (Raw F) K) :
    (profileArithmetic (circuitProgram groups kernel lambda denominator weight helper)).1 =
      circuitRaw groups kernel lambda denominator weight helper := by
  simp only [circuitProgram, profileArithmetic_bind, Arithmetic.profileArithmetic_sumRaw_fst,
    profileArithmetic_batchFromProgram_fst, profileArithmetic_certified_val,
    profileArithmetic_pure]
  simp only [circuitRaw, batchRaw, Raw.sumRaw, List.foldl_map]

end Arithmetic

end Logup.Prover.CoefficientCircuit

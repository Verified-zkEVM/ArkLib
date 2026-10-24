/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
module

public import ArkLib.ProofSystem.Logup.Prover.CoefficientCircuit

/-!
# Instruction profiles of the grouped coefficient circuit

The equations follow the executed residual and accumulation programs. Bounds are per
instruction coordinate and retain both the sum of squared group lengths and the cost of
adding to a possibly wide batch accumulator. Positive nonempty partitions admit the simpler
linear bound in occurrences times maximum group size. Allocation, indexing, and final
coefficient normalization are outside these profiles.
-/

@[expose] public section

open CompPoly CPolynomial OracleComp OracleSpec
namespace Logup.Prover.CoefficientCircuit
variable {F : Type} [CommRing F] [Inv F] [DecidableEq F] {T K : ℕ}

/-- A residual charges its fraction fold, helper product, and padded subtraction. -/
theorem profileArithmetic_residualProgram (group : List (Fin T))
    (denominator weight : Vector (Raw F) T) (helper : Raw F) :
    (profileArithmetic (residualProgram group denominator weight helper)).2 =
      (profileArithmetic (groupFractionProgram group denominator weight)).2 +
      (profileArithmetic (Arithmetic.mulRaw helper
        (groupFractionRaw group denominator weight).denominator)).2 +
      (profileArithmetic (Arithmetic.subRaw
        (Raw.mulRaw helper (groupFractionRaw group denominator weight).denominator)
        (groupFractionRaw group denominator weight).numerator)).2 := by
  simp only [residualProgram, profileArithmetic_bind, profileArithmetic_certified_val,
    profileArithmetic_groupFractionProgram_fst, profileArithmetic_pure, add_zero, add_assoc]
  rw [profileArithmetic_groupFractionProgram_fst]
  rw [profileArithmetic_certified_val (Arithmetic.mulRaw helper _)]

/-- Every supported residual instruction count is quadratic in its group occurrence count. -/
theorem profileArithmetic_residualProgram_le (group : List (Fin T))
    (denominator weight : Vector (Raw F) T) (helper : Raw F)
    (hden : ∀ i, (denominator.get i).size ≤ 2)
    (hweight : ∀ i, (weight.get i).size ≤ 2) (hhelper : helper.size ≤ 2)
    (kind : ArithmeticCostKind) :
    (profileArithmetic (residualProgram group denominator weight helper)).2 kind ≤
      if kind = .add ∨ kind = .mul ∨ kind = .sub ∨ kind = .coefficientRead ∨
        kind = .metadata then 100 * (group.length + 1) ^ 2 else 0 := by
  have hf := Arithmetic.profileArithmetic_fractionSum_le
    (group.map fun i => (⟨weight.get i, denominator.get i⟩ : FractionPair (Raw F)))
    (by
      intro p hp
      obtain ⟨i, _, rfl⟩ := List.mem_map.mp hp
      exact ⟨hweight i, hden i⟩) kind
  have hm := Arithmetic.profileArithmetic_mulRaw_le_of_size_le_two helper
    (groupFractionRaw group denominator weight).denominator hhelper kind
  have hs := size_groupFractionRaw_le group denominator weight hden hweight
  have hp := Raw.size_mulRaw_le helper
    (groupFractionRaw group denominator weight).denominator
  have hmax : max
      (Raw.mulRaw helper (groupFractionRaw group denominator weight).denominator).size
      (groupFractionRaw group denominator weight).numerator.size ≤ group.length + 2 :=
    max_le (by omega) (by omega)
  rw [profileArithmetic_residualProgram]
  change (profileArithmetic (Arithmetic.fractionSum _)).2 _ + _ + _ ≤ _
  cases kind <;>
    simp only [Arithmetic.profileArithmetic_subRaw, List.length_map,
      reduceCtorEq, or_true, or_false, or_self, ite_true, ite_false] at hf hm ⊢ <;>
      first | omega | nlinarith


/-- The empty streamed accumulation performs no primitive requests. -/
theorem profileArithmetic_batchFromProgram_nil (groups : Vector (List (Fin T)) K)
    (lambda : Vector F K) (denominator weight : Vector (Raw F) T)
    (helper : Vector (Raw F) K) (acc : Raw F) :
    (profileArithmetic (batchFromProgram [] groups lambda denominator weight helper acc)).2 =
      0 := rfl

/-- Each batch step charges its tick, residual, scalar product, and actual-width addition. -/
theorem profileArithmetic_batchFromProgram_cons (k : Fin K) (indices : List (Fin K))
    (groups : Vector (List (Fin T)) K) (lambda : Vector F K)
    (denominator weight : Vector (Raw F) T) (helper : Vector (Raw F) K) (acc : Raw F) :
    (profileArithmetic
      (batchFromProgram (k :: indices) groups lambda denominator weight helper acc)).2 =
      arithmeticCost (ArithmeticOp.metadata : ArithmeticOp F) +
      (profileArithmetic
        (residualProgram (groups.get k) denominator weight (helper.get k))).2 +
      (profileArithmetic (Arithmetic.smulRaw (lambda.get k)
        (residualRaw (groups.get k) denominator weight (helper.get k)))).2 +
      (profileArithmetic (Arithmetic.addRaw acc (Raw.smul (lambda.get k)
        (residualRaw (groups.get k) denominator weight (helper.get k))))).2 +
      (profileArithmetic (batchFromProgram indices groups lambda denominator weight helper
        (Raw.addRaw acc (Raw.smul (lambda.get k)
          (residualRaw (groups.get k) denominator weight (helper.get k)))))).2 := by
  simp only [batchFromProgram, List.foldlM_cons, profileArithmetic_bind,
    profileArithmetic_certified_val, profileArithmetic_residualProgram_fst,
    profileArithmetic_tick, profileArithmetic_pure, add_zero, add_assoc]
  rw [profileArithmetic_residualProgram_fst]
  rw [profileArithmetic_certified_val (Arithmetic.smulRaw (lambda.get k) _)]

/-- Batch instruction counts retain the squared group sizes and maximum accumulator width. -/
theorem profileArithmetic_batchFromProgram_le (indices : List (Fin K))
    (groups : Vector (List (Fin T)) K) (lambda : Vector F K)
    (denominator weight : Vector (Raw F) T) (helper : Vector (Raw F) K) (acc : Raw F)
    (ell : ℕ) (hgroups : ∀ k, (groups.get k).length ≤ ell)
    (hden : ∀ i, (denominator.get i).size ≤ 2)
    (hweight : ∀ i, (weight.get i).size ≤ 2)
    (hhelper : ∀ k, (helper.get k).size ≤ 2) (hacc : acc.size ≤ ell + 2)
    (kind : ArithmeticCostKind) :
    (profileArithmetic
      (batchFromProgram indices groups lambda denominator weight helper acc)).2 kind ≤
      if kind = .add ∨ kind = .mul ∨ kind = .sub ∨ kind = .coefficientRead ∨
        kind = .metadata then
        (indices.map fun k => 100 * ((groups.get k).length + 1) ^ 2).sum +
          5 * indices.length * (ell + 3) else 0 := by
  induction indices generalizing acc with
  | nil =>
    rw [profileArithmetic_batchFromProgram_nil]
    cases kind <;> simp
  | cons k indices ih =>
    have hr := profileArithmetic_residualProgram_le (groups.get k) denominator weight
      (helper.get k) hden hweight (hhelper k) kind
    have hs : (residualRaw (groups.get k) denominator weight (helper.get k)).size ≤ ell + 2 :=
      (size_residualRaw_le _ _ _ _ hden hweight (hhelper k)).trans
        (by have := hgroups k; omega)
    have hn : (Raw.addRaw acc (Raw.smul (lambda.get k)
        (residualRaw (groups.get k) denominator weight (helper.get k)))).size ≤ ell + 2 := by
      rw [Raw.size_addRaw, Raw.size_smul]
      exact max_le hacc hs
    have ht := ih _ hn
    rw [profileArithmetic_batchFromProgram_cons]
    have hm := max_le hacc hs
    cases kind <;>
      simp only [Pi.add_apply, Arithmetic.profileArithmetic_smulRaw,
        Arithmetic.profileArithmetic_addRaw, Raw.size_smul, arithmeticCost,
        ArithmeticOp.costKind, List.map_cons, List.sum_cons, List.length_cons,
        reduceCtorEq, or_true, or_false, or_self, ite_true, ite_false,
        Nat.add_mul, Nat.mul_add, Nat.mul_assoc] at hr ht ⊢ <;> omega

/-- The complete profile consists of helper summation, streamed batching, and the final product
and addition, all at their actual retained widths. -/
theorem profileArithmetic_circuitProgram (groups : Vector (List (Fin T)) K)
    (kernel : Raw F) (lambda : Vector F K) (denominator weight : Vector (Raw F) T)
    (helper : Vector (Raw F) K) :
    (profileArithmetic (circuitProgram groups kernel lambda denominator weight helper)).2 =
      (profileArithmetic (Arithmetic.sumRaw ((List.finRange K).map helper.get))).2 +
      (profileArithmetic
        (batchFromProgram (List.finRange K) groups lambda denominator weight helper #[])).2 +
      (profileArithmetic (Arithmetic.mulRaw kernel
        (Raw.sumRaw ((List.finRange K).map fun k => Raw.smul (lambda.get k)
          (residualRaw (groups.get k) denominator weight (helper.get k)))))).2 +
      (profileArithmetic (Arithmetic.addRaw (Raw.sumRaw ((List.finRange K).map helper.get))
        (Raw.mulRaw kernel (Raw.sumRaw ((List.finRange K).map fun k => Raw.smul (lambda.get k)
          (residualRaw (groups.get k) denominator weight (helper.get k))))))).2 := by
  simp only [circuitProgram, profileArithmetic_bind, profileArithmetic_certified_val,
    Arithmetic.profileArithmetic_sumRaw_fst, profileArithmetic_batchFromProgram_fst,
    profileArithmetic_pure, Raw.sumRaw, List.foldl_map, add_zero, add_assoc]
  rw [profileArithmetic_batchFromProgram_fst, Arithmetic.profileArithmetic_sumRaw_fst]
  rw [profileArithmetic_certified_val (Arithmetic.mulRaw kernel _)]
  have hbatch :
      List.foldl Raw.addRaw #[] ((List.finRange K).map fun k => Raw.smul (lambda.get k)
        (residualRaw (groups.get k) denominator weight (helper.get k))) =
      (List.finRange K).foldl (fun a k => Raw.addRaw a (Raw.smul (lambda.get k)
        (residualRaw (groups.get k) denominator weight (helper.get k)))) #[] :=
    List.foldl_map
  rw [hbatch]
  rfl

/-- The general circuit bound includes empty groups and the cost of adding to a wide accumulator.
All unlisted primitive instruction coordinates are zero. -/
theorem profileArithmetic_circuitProgram_le (groups : Vector (List (Fin T)) K)
    (kernel : Raw F) (lambda : Vector F K) (denominator weight : Vector (Raw F) T)
    (helper : Vector (Raw F) K) (ell : ℕ)
    (hgroups : ∀ k, (groups.get k).length ≤ ell)
    (hden : ∀ i, (denominator.get i).size ≤ 2)
    (hweight : ∀ i, (weight.get i).size ≤ 2)
    (hhelper : ∀ k, (helper.get k).size ≤ 2) (hkernel : kernel.size ≤ 2)
    (kind : ArithmeticCostKind) :
    (profileArithmetic (circuitProgram groups kernel lambda denominator weight helper)).2 kind ≤
      if kind = .add ∨ kind = .mul ∨ kind = .sub ∨ kind = .coefficientRead ∨
        kind = .metadata then
        ((List.finRange K).map fun k => 100 * ((groups.get k).length + 1) ^ 2).sum +
          20 * (K + 1) * (ell + 3) else 0 := by
  have hh := Arithmetic.profileArithmetic_sumRaw_le
    ((List.finRange K).map helper.get) 2 (by
      intro p hp
      obtain ⟨k, _, rfl⟩ := List.mem_map.mp hp
      exact hhelper k) kind
  have hb := profileArithmetic_batchFromProgram_le (List.finRange K) groups lambda
    denominator weight helper #[] ell hgroups hden hweight hhelper (by simp) kind
  have hbs := size_batchRaw_le (List.finRange K) groups lambda denominator weight helper
    #[] ell hgroups hden hweight hhelper (by simp)
  rw [batchRaw_eq_sumRaw] at hbs
  have hhs : (Raw.sumRaw ((List.finRange K).map helper.get)).size ≤ 2 := by
    apply Raw.size_sumRaw_le
    intro p hp
    obtain ⟨k, _, rfl⟩ := List.mem_map.mp hp
    exact hhelper k
  have hm := Arithmetic.profileArithmetic_mulRaw_le_of_size_le_two kernel
    (Raw.sumRaw ((List.finRange K).map fun k => Raw.smul (lambda.get k)
      (residualRaw (groups.get k) denominator weight (helper.get k)))) hkernel kind
  have hp := Raw.size_mulRaw_le kernel
    (Raw.sumRaw ((List.finRange K).map fun k => Raw.smul (lambda.get k)
      (residualRaw (groups.get k) denominator weight (helper.get k))))
  have hmax : max (Raw.sumRaw ((List.finRange K).map helper.get)).size
      (Raw.mulRaw kernel (Raw.sumRaw ((List.finRange K).map fun k => Raw.smul (lambda.get k)
        (residualRaw (groups.get k) denominator weight (helper.get k))))).size ≤ ell + 3 :=
    max_le (by omega) (by omega)
  rw [profileArithmetic_circuitProgram]
  cases kind <;>
    simp only [Pi.add_apply, Arithmetic.profileArithmetic_addRaw, List.length_map,
      List.length_finRange, reduceCtorEq, or_true, or_false, or_self, ite_true, ite_false,
      Nat.add_mul, Nat.mul_add, Nat.mul_assoc] at hh hb hm ⊢ <;> omega

/-- For a positive nonempty partition, each supported instruction count is bounded by a constant
times the occurrence count times the maximum group size. -/
theorem profileArithmetic_circuitProgram_le_of_partition
    (groups : Vector (List (Fin T)) K) (kernel : Raw F) (lambda : Vector F K)
    (denominator weight : Vector (Raw F) T) (helper : Vector (Raw F) K) (ell : ℕ)
    (hT : 0 < T) (hell : 0 < ell)
    (hgroups : ∀ k, (groups.get k).length ≤ ell)
    (hnonempty : ∀ k, 0 < (groups.get k).length)
    (htotal : ((List.finRange K).map fun k => (groups.get k).length).sum = T)
    (hden : ∀ i, (denominator.get i).size ≤ 2)
    (hweight : ∀ i, (weight.get i).size ≤ 2)
    (hhelper : ∀ k, (helper.get k).size ≤ 2) (hkernel : kernel.size ≤ 2)
    (kind : ArithmeticCostKind) :
    (profileArithmetic (circuitProgram groups kernel lambda denominator weight helper)).2 kind ≤
      if kind = .add ∨ kind = .mul ∨ kind = .sub ∨ kind = .coefficientRead ∨
        kind = .metadata then 600 * T * ell else 0 := by
  have hc := profileArithmetic_circuitProgram_le groups kernel lambda denominator weight
    helper ell hgroups hden hweight hhelper hkernel kind
  have hs : ((List.finRange K).map fun k => 100 * ((groups.get k).length + 1) ^ 2).sum ≤
      400 * ell * T := by
    calc
      _ ≤ ((List.finRange K).map fun k => 400 * ell * (groups.get k).length).sum := by
        apply List.sum_le_sum
        intro k _
        have hp := hnonempty k
        have hb := Nat.mul_le_mul_right (groups.get k).length (hgroups k)
        nlinarith
      _ = 400 * ell * T := by rw [List.sum_map_mul_left, htotal]
  have hK : K ≤ T := by
    have hcount := List.sum_le_sum (l := List.finRange K)
      (f := fun _ => 1) (g := fun k => (groups.get k).length)
      (fun k _ => hnonempty k)
    simpa [htotal] using hcount
  have ha : K + 1 ≤ 2 * T := by omega
  have hb : ell + 3 ≤ 4 * ell := by omega
  have hm := Nat.mul_le_mul ha hb
  split_ifs at hc ⊢ <;> nlinarith

end Logup.Prover.CoefficientCircuit

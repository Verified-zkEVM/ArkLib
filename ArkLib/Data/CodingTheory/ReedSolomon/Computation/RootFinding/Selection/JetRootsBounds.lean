/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.Computation.RootFinding.Selection.JetRootsMachine
/-!
# Enumeration bounds without an augmented alphabet exponent

Repeated nonempty axes admit a bound in the ordinary alphabet-size power. This avoids applying
the generic Cartesian augmented-size bound, whose base would be one larger than the alphabet.
-/

@[expose] public section

namespace ReedSolomon.HiddenDerivative.JetRootsMachine

open Polynomial Matrix List

variable {F : Type*}

/-- Mathematical jet list; all tuple cells are constructed by the actual Cartesian machine. -/
def tuples (u : List F) (m : ℕ) : List (List F) :=
  CartesianProductMachine.productSpec (List.replicate m u)

/-- The exact number of jets is the ordinary alphabet-size power. -/
theorem tuples_length (u : List F) (m : ℕ) : (tuples u m).length = u.length ^ m := by
  simp [tuples, CartesianProductMachine.productSpec_length]

/-- Every enumerated tuple has the requested physical width. -/
theorem tuples_width (u : List F) (m : ℕ) (js : List F) (h : js ∈ tuples u m) :
    js.length = m := by
  simpa using CartesianProductMachine.productSpec_width h

/-- A duplicate-free alphabet yields duplicate-free jet tuples. -/
theorem tuples_nodup (u : List F) (m : ℕ) (hu : u.Nodup) : (tuples u m).Nodup := by
  apply CartesianProductMachine.productSpec_nodup
  intro a ha
  have heq := (List.mem_replicate.mp ha).2
  simpa [heq] using hu

private theorem processFuel_repeat (u : List F) (hq : 0 < u.length) (m : ℕ)
    (ps : List (List F)) (hp : 0 < ps.length) :
    CartesianProductMachine.processFuel (List.replicate m u) ps ≤
      8 * (m + 1) * u.length ^ m * ps.length := by
  induction m generalizing ps with
  | zero => simp [CartesianProductMachine.processFuel]; omega
  | succ m ih =>
      have hp' : 0 < (CartesianProductMachine.extendSpec u ps).length := by
        rw [CartesianProductMachine.extendSpec_length]
        exact Nat.mul_pos hq hp
      have ht := ih (CartesianProductMachine.extendSpec u ps) hp'
      rw [CartesianProductMachine.extendSpec_length] at ht
      have hqpow : 1 ≤ u.length ^ m := Nat.one_le_pow _ _ hq
      have hstep : u.length * (3 * ps.length + 2) + 3 ≤
          8 * u.length * ps.length := by nlinarith
      have hscale : 8 * u.length * ps.length ≤
          8 * u.length * ps.length * u.length ^ m := by
        simpa using Nat.mul_le_mul_left (8 * u.length * ps.length) hqpow
      calc
        CartesianProductMachine.processFuel (List.replicate (m + 1) u) ps =
            u.length * (3 * ps.length + 2) + 3 +
              CartesianProductMachine.processFuel (List.replicate m u)
                (CartesianProductMachine.extendSpec u ps) := rfl
        _ ≤ 8 * u.length * ps.length * u.length ^ m +
            8 * (m + 1) * u.length ^ m * (u.length * ps.length) :=
          Nat.add_le_add (hstep.trans hscale) ht
        _ = _ := by rw [pow_succ]; ring

/-- Cartesian construction for repeated nonempty axes has only the ordinary jet exponent. -/
theorem productFuel_le (u : List F) (hq : 0 < u.length) (m : ℕ) :
    CartesianProductMachine.constructionFuel (List.replicate m u) ≤
      10 * (m + 1) * u.length ^ m := by
  have hp := processFuel_repeat u hq m ([[]] : List (List F)) (by simp)
  have hpow : 1 ≤ u.length ^ m := Nat.one_le_pow _ _ hq
  simp only [List.length_cons, List.length_nil, Nat.zero_add, Nat.mul_one] at hp
  simp only [CartesianProductMachine.constructionFuel, List.length_replicate,
    List.reverse_replicate]
  nlinarith

variable [Field F] [DecidableEq F]

/-- A proof-only input used to state budgets by physical width; dispatch never constructs it. -/
def budgetInput (input : Input F) (D : ℕ) : RegularRootMachine.Input F :=
  rootInput input (List.replicate (D + 1) 0)
/-- Uniform fuel per prepared jet, including output-cell collection and its later reversal. -/
def itemFuel (input : Input F) (D L n : ℕ) : ℕ :=
  RegularRootMachine.fuel (budgetInput input D) D L n + D + 11
/-- Uniform full primitive work per jet, retaining preparation, root execution and wrappers. -/
def itemWork (input : Input F) (D L n : ℕ) : ℕ :=
  RegularRootMachine.workBound (budgetInput input D) D L n +
    3 * RegularRootMachine.fuel (budgetInput input D) D L n +
      40 * (D + input.order + 2) + 3 * (D + 5) + 30
/-- Complete host budget has exactly the number-of-jets exponent. -/
def fuel (input : Input F) (D L n : ℕ) : ℕ :=
  input.alphabet.length ^ (input.order + 1) *
    (itemFuel input D L n + 32 * (input.order + 2)) + 3
/-- Complete primitive work has no additional derivative-dependent exponent. -/
def workBound (input : Input F) (D L n : ℕ) : ℕ :=
  input.alphabet.length ^ (input.order + 1) *
    (itemWork input D L n + 512 * (input.order + 2)) + 10

omit [DecidableEq F] in
/-- Prepared vectors of equal physical width have identical root fuel and work bounds. -/
theorem root_budgets (input : Input F) (D L n : ℕ) (cs : List F)
    (h : cs.length = D + 1) :
    RegularRootMachine.fuel (rootInput input cs) D L n =
      RegularRootMachine.fuel (budgetInput input D) D L n ∧
    RegularRootMachine.workBound (rootInput input cs) D L n =
      RegularRootMachine.workBound (budgetInput input D) D L n := by
  simp only [RegularRootMachine.fuel, RegularRootMachine.workBound,
    RegularRootMachine.suffixFuel, RegularRootMachine.suffixWork, RegularRootMachine.zeroWork,
    ResidualZeroMachine.fuel, RegularLiftMachine.fuel, RegularLiftMachine.workBound,
    RegularLiftMachine.stageFuel, RegularLiftMachine.stageWork,
    DirectCoefficientMachine.fuel, DirectCoefficientMachine.workBound,
    ResidualCoefficientMachine.fuel, ResidualCoefficientMachine.workBound,
    ResidualSystemMachine.fuel, ResidualSystemMachine.workBound, ResidualBatchMachine.fuel,
    ResidualBatchMachine.cost, ResidualBatchMachine.itemCost, ResidualBatchMachine.singleFuel,
    ResidualBatchMachine.singleCost, ResidualBatchMachine.sampleInput, ResidualSampleMachine.fuel,
    ResidualSampleMachine.cost, ResidualSampleMachine.jetFuel, ResidualSampleMachine.scalarFuel,
    budgetInput, rootInput, List.length_replicate, h]
  trivial

/-- Addition preserves the total primitive ledger. -/
theorem total_add (a b : Cost) : totalCost (a + b) = totalCost a + totalCost b := by
  simp only [totalCost, RegularRootMachine.totalCost, RegularLiftMachine.totalCost,
    DirectCoefficientMachine.totalCost, ResidualCoefficientMachine.totalCost,
    ResidualCoefficientMachine.cost_add, PivotSelectionMachine.totalCost,
    PivotEliminationMachine.cost_add, RowReductionMachine.cost_add]
  omega

/-- Every callee dispatch costs three retained-root operations. -/
theorem total_wrapper (n : ℕ) : totalCost (wrapperCost n) = 3 * n := by
  simp [totalCost, RegularRootMachine.totalCost, RegularLiftMachine.totalCost,
    DirectCoefficientMachine.totalCost, ResidualCoefficientMachine.totalCost,
    wrapperCost, RegularRootMachine.wrapperCost, RegularLiftMachine.wrapperCost,
    DirectCoefficientMachine.wrapperCost, ResidualCoefficientMachine.wrapperCost,
    PivotSelectionMachine.totalCost]
  omega

/-- Enumeration embedding retains all categories. -/
theorem total_enumeration (c : CartesianProductMachine.Cost) :
    totalCost (enumerationCost c) = c.total := by
  simp only [totalCost, RegularRootMachine.totalCost, RegularLiftMachine.totalCost,
    DirectCoefficientMachine.totalCost, ResidualCoefficientMachine.totalCost, enumerationCost,
    PivotSelectionMachine.totalCost, CartesianProductMachine.Cost.total]
  omega

/-- Preparation embedding retains every zero constant and allocation charge. -/
theorem total_preparation (c : JetPreparationMachine.Cost) :
    totalCost (preparationCost c) = c.total := by
  simp only [totalCost, RegularRootMachine.totalCost, RegularLiftMachine.totalCost,
    DirectCoefficientMachine.totalCost, ResidualCoefficientMachine.totalCost, preparationCost,
    RegularRootMachine.shiftCost, CenterShiftMachine.preparationCost,
    PivotSelectionMachine.totalCost, JetPreparationMachine.Cost.total, JetHornerMachine.Cost.total]
  omega

/-- Fixed local instructions retain all declared administrative categories. -/
theorem total_charge (d n o : ℕ) : totalCost (charge d n o) = 1 + d + n + o := by
  simp only [totalCost, RegularRootMachine.totalCost, RegularLiftMachine.totalCost,
    DirectCoefficientMachine.totalCost, ResidualCoefficientMachine.totalCost, charge,
    PivotSelectionMachine.totalCost]
  omega

/-- Exact ledger for counting a materialized alphabet cursor and its final handoff. -/
def countCost (n : ℕ) : Cost := ⟨⟨⟨0, 0, n, 4 * n, 0⟩, 0, 0, 0, n⟩, 0⟩
/-- Exact ledger for allocating repeated bounds and initializing the axes callee. -/
def boundsCost (m : ℕ) : Cost := ⟨⟨⟨0, 0, m + 1, 5 * m + 3, 0⟩, 0, 0, 0, 2 * m + 1⟩, 0⟩

omit [DecidableEq F] in
/-- Counting visits every supplied alphabet cell; its length is not a free instruction. -/
theorem count_trace (input : Input F) (D L : ℕ) (cursor : List F) (q : ℕ) (xs : List F) :
    Trace input D L (cursor.length + 1) (.count cursor q xs) (countCost (cursor.length + 1))
      (.bounds (input.order + 1) (q + cursor.length) [] xs) := by
  induction cursor generalizing q with
  | nil => simpa [countCost, charge] using
      Trace.cons (Step.counted (input := input) (D := D) (L := L)) (Trace.nil _)
  | cons a as ih =>
      convert Trace.cons Step.count (ih (q + 1)) using 1 <;>
        simp [countCost, charge, Nat.add_assoc] <;> omega

omit [DecidableEq F] in
/-- Every repeated-bound cell is explicitly allocated. -/
theorem bounds_trace (input : Input F) (D L m q : ℕ) (bs : List ℕ) (xs : List F) :
    Trace input D L (m + 1) (.bounds m q bs xs) (boundsCost m)
      (.axes xs (.start (List.replicate m q ++ bs))) := by
  induction m generalizing bs with
  | zero => simpa [boundsCost, charge] using
      Trace.cons (Step.bounded (input := input) (D := D) (L := L)) (Trace.nil _)
  | succ m ih =>
      convert Trace.cons Step.bound (ih (q :: bs)) using 1
      · ext <;> simp [boundsCost, charge] <;> omega
      · simp only [List.replicate_succ', List.append_assoc, List.singleton_append]

omit [DecidableEq F] in
/-- The entire counted-axis/product prefix reaches the actual tuple consumer with sharp bounds. -/
theorem enumeration_trace (input : Input F) (D L : ℕ) (xs : List F)
    (hq : 0 < input.alphabet.length) :
    ∃ steps c, Trace input D L steps (.start xs) c
      (.scan (tuples input.alphabet (input.order + 1)) [] xs) ∧
      steps ≤ 32 * (input.order + 2) * input.alphabet.length ^ (input.order + 1) ∧
      totalCost c ≤ 512 * (input.order + 2) * input.alphabet.length ^ (input.order + 1) := by
  let m := input.order + 1
  let q := input.alphabet.length
  have hvalid : ∀ n ∈ List.replicate m q, n ≤ input.alphabet.length := by
    intro n hn
    simpa only [(List.mem_replicate.mp hn).2] using Nat.le_refl q
  obtain ⟨ca, ha, hca⟩ := PrefixAxesMachine.success_runFuel input.alphabet
    (List.replicate m q) hvalid
  have has : PrefixAxesMachine.axesSpec input.alphabet (List.replicate m q) =
      List.replicate m input.alphabet := by simp [PrefixAxesMachine.axesSpec, q]
  rw [has] at ha
  obtain ⟨na, hna, hta⟩ := PrefixAxesMachine.runFuel_refines input.alphabet
    (PrefixAxesMachine.constructionFuel (List.replicate m q)) (.start (List.replicate m q))
  rw [ha] at hta
  obtain ⟨cp, hp, hcp⟩ := CartesianProductMachine.construction_runFuel
    (List.replicate m input.alphabet)
  obtain ⟨np, hnp, htp⟩ := CartesianProductMachine.runFuel_refines
    (CartesianProductMachine.constructionFuel (List.replicate m input.alphabet))
    (.start (List.replicate m input.alphabet))
  rw [hp] at htp
  have hpBound := productFuel_le input.alphabet hq m
  have hc := count_trace input D L input.alphabet 0 xs
  simp only [Nat.zero_add] at hc
  have hb := bounds_trace input D L m q [] xs
  simp only [List.append_nil] at hb
  have ht := Trace.cons Step.start (hc.trans (hb.trans ((lift_axes input D L xs hta).trans
    (Trace.cons Step.axesDone ((lift_product input D L xs htp).trans
      (Trace.cons Step.productDone (Trace.nil _)))))))
  have hpow : 1 ≤ q ^ m := Nat.one_le_pow _ _ hq
  have hqpow : q ≤ q ^ m := le_self_pow hq (by dsimp [m]; omega)
  have haxesFuel : PrefixAxesMachine.constructionFuel (List.replicate m q) =
      2 * (m * q) + 5 * m + 4 := by simp [PrefixAxesMachine.constructionFuel]
  rw [haxesFuel] at hna
  have hacost : ca.total ≤ 128 * (m * q + m + 1) := by simpa using hca
  refine ⟨_, _, ht, ?_, ?_⟩
  · change _ ≤ 32 * (m + 1) * q ^ m
    dsimp [q] at hqpow hpow ⊢
    dsimp [m] at haxesFuel
    nlinarith [Nat.mul_le_mul_left m hqpow, Nat.mul_le_mul_left m hpow]
  · simp only [total_add, total_charge, total_wrapper, total_enumeration]
    have hcCost : totalCost (countCost (input.alphabet.length + 1)) =
        6 * (q + 1) := by
      simp [countCost, totalCost, RegularRootMachine.totalCost, RegularLiftMachine.totalCost,
        DirectCoefficientMachine.totalCost, ResidualCoefficientMachine.totalCost,
        PivotSelectionMachine.totalCost, q]
      omega
    have hbCost : totalCost (boundsCost m) = 8 * m + 5 := by
      simp [boundsCost, totalCost, RegularRootMachine.totalCost, RegularLiftMachine.totalCost,
        DirectCoefficientMachine.totalCost, ResidualCoefficientMachine.totalCost,
        PivotSelectionMachine.totalCost]
      omega
    rw [hcCost, hbCost]
    change 6 + (6 * (q + 1) + (8 * m + 5 +
      (ca.total + 3 * na + (5 + (cp.total + 3 * np + (5 + 0)))))) ≤
        512 * (m + 1) * q ^ m
    change CartesianProductMachine.constructionFuel (List.replicate m input.alphabet) ≤
      10 * (m + 1) * q ^ m at hpBound
    nlinarith [Nat.mul_le_mul_left m hqpow, Nat.mul_le_mul_left m hpow]

end ReedSolomon.HiddenDerivative.JetRootsMachine

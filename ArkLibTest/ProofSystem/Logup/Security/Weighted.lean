/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/
import ArkLib.ProofSystem.Logup.Security.Weighted
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.NormNum.Prime
import Lean.Compiler.IR

/-! # Actual whole scalar endpoint: pole and genuine native-round false-input bounds -/

open Interaction.Oracle OracleComp OracleSpec CompPoly Logup.Interaction
open scoped BigOperators ProbabilityTheory ENNReal

namespace LogupWeightedTest

abbrev F := ZMod 17
instance : Fact (Nat.Prime 17) := ⟨by decide⟩
def cfg (n : Nat) : Config n 1 1 := ⟨#v[[0]], by decide⟩
def data (n : Nat) (i : Fin 2 × Fin 1) : CMlPolynomialEval F n :=
  Vector.replicate (2 ^ n) (if i.1 = 0 then 0 else 1)
abbrev access (n : Nat) := (inputFamily (RingHom.id F) n 1).spec.toPFunctor
def impl (n : Nat) : QueryImpl (ofPFunctor (access n)) Id :=
  (inputFamily (RingHom.id F) n 1).behaviorOfRealizations (data n)
def view (n : Nat) : VirtualOracle (ofPFunctor (access n)) (inputFamily (RingHom.id F) n 1) :=
  VirtualOracle.id _
theorem realizes (n : Nat) : (view n).eval (impl n) =
    (inputFamily (RingHom.id F) n 1).behaviorOfRealizations (data n) :=
  VirtualOracle.eval_id (impl n)

/-- The denominator pole alpha0 is not a bad root when there is one occurrence of weight1. -/
theorem zero_numerator : clearedBalancePolynomial (RingHom.id F) (data 0) = 1 := by
  have hocc : ((Finset.univ : Finset (Fin 0 → Fin 2)).product
      (Finset.univ : Finset (Fin 1))) = {(Fin.elim0, 0)} := by decide
  rw [clearedBalancePolynomial, hocc, PartialFractions.clearedNumerator]
  simp [data]

/-- The native-round example has two occurrences and a genuinely nonzero root polynomial. -/
theorem one_numerator : clearedBalancePolynomial (RingHom.id F) (data 1) =
    Polynomial.C 2 * Polynomial.X := by
  have hocc : ((Finset.univ : Finset (Fin 1 → Fin 2)).product
      (Finset.univ : Finset (Fin 1))) =
      {((fun _ ↦ 0), 0), ((fun _ ↦ 1), 0)} := by decide
  have hne : (fun _ : Fin 1 ↦ (0 : Fin 2)) ≠ (fun _ ↦ 1) := by decide
  rw [clearedBalancePolynomial, hocc, PartialFractions.clearedNumerator]
  simp [data, hne, Ne.symm hne, Polynomial.C_ofNat, two_mul]

/-- The exact named endpoint bound is satisfiable and below1 for EVERY whole private-output
prover, including alpha-adaptive helpers and effectful receiver/sender continuations. -/
theorem zero_bound
    {OutP : (protocol F 0 ((1 : Nat) ⌈/⌉ 1) 1).tree.ExecutionPath → Type}
    (prover : Prover.Strategy unifSpec (protocol F 0 ((1 : Nat) ⌈/⌉ 1) 1).tree
      (protocol F 0 ((1 : Nat) ⌈/⌉ 1) 1).roles OutP) :
    Pr{let accepted ← (uniformExecute (RingHom.id F) 0 1 1 (cfg 0)
      (access 0) (view 0) (impl 0) prover)}[accepted = true] ≤ (17 : ℝ≥0∞)⁻¹ := by
  have h := uniformExecute_soundness (RingHom.id F) 0 1 1 (cfg 0)
    (access 0) (view 0) (impl 0) (data 0) (realizes 0) prover ⟨0, by decide⟩
  simpa only [Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.cast_one, Nat.cast_ofNat,
    ZMod.card, one_div] using h

/-- One actual native round contributes the native degree term; the whole bound is6/17. -/
theorem one_bound
    {OutP : (protocol F 1 ((1 : Nat) ⌈/⌉ 1) 1).tree.ExecutionPath → Type}
    (prover : Prover.Strategy unifSpec (protocol F 1 ((1 : Nat) ⌈/⌉ 1) 1).tree
      (protocol F 1 ((1 : Nat) ⌈/⌉ 1) 1).roles OutP) :
    Pr{let accepted ← (uniformExecute (RingHom.id F) 1 1 1 (cfg 1)
      (access 1) (view 1) (impl 1) prover)}[accepted = true] ≤ (6 : ℝ≥0∞) / 17 := by
  have h := uniformExecute_soundness (RingHom.id F) 1 1 1 (cfg 1)
    (access 1) (view 1) (impl 1) (data 1) (realizes 1) prover ⟨0, by decide⟩
  simpa only [Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.cast_ofNat, ZMod.card] using h

example : (17 : ℝ≥0∞)⁻¹ < 1 := by norm_num
example : (6 : ℝ≥0∞) / 17 < 1 := by
  simpa only [ENNReal.div_self (a := (17 : ℝ≥0∞)) (by norm_num) (by norm_num)] using
    ENNReal.div_lt_div_right (c := (17 : ℝ≥0∞)) (by norm_num) (by norm_num)
    (show (6 : ℝ≥0∞) < 17 by norm_num)

/-- An ordinary zero-round whole prover retains a nontrivial private return value. -/
def zeroProver {ι : Type} (ambient : OracleSpec ι) :
    Prover.Strategy ambient (protocol F 0 1 1).tree (protocol F 0 1 1).roles (fun _ ↦ F) :=
  fun (alpha : F) ↦ pure (pure ⟨#v[#v[0]], fun joint ↦ pure (alpha + joint.2 0)⟩)

/-- A genuine coefficient-message native round, followed by its actual receiver response. -/
def oneProver {ι : Type} (ambient : OracleSpec ι) :
    Prover.Strategy ambient (protocol F 1 1 1).tree (protocol F 1 1 1).roles (fun _ ↦ F) :=
  fun (alpha : F) ↦ pure (pure ⟨#v[#v[0,0]], fun joint ↦ pure (pure
    ⟨(⟨0, by simp⟩ : Sumcheck.Impl.Representation.Message F 3),
      fun choice ↦ match choice with
      | none => pure (alpha + joint.1 0 + joint.2 0)
      | some r => pure (alpha + joint.1 0 + joint.2 0 + r)⟩)⟩)

def zeroUniformEndpoint : ProbComp Bool :=
  uniformExecute (RingHom.id F) 0 1 1 (cfg 0) (access 0) (view 0) (impl 0) (zeroProver unifSpec)
def oneUniformEndpoint : ProbComp Bool :=
  uniformExecute (RingHom.id F) 1 1 1 (cfg 1) (access 1) (view 1) (impl 1) (oneProver unifSpec)

abbrev fixedSpec : OracleSpec Unit := Unit →ₒ F

def zeroFixedEndpoint (alpha lambda : F) : Bool :=
  simulateQ (fun _ ↦ 0 : QueryImpl fixedSpec Id)
    (execute (RingHom.id F) 0 1 1 (cfg 0) fixedSpec (pure alpha)
      (pure (Fin.elim0, fun _ ↦ lambda)) (pure 0) (access 0) (view 0) (impl 0)
      (zeroProver fixedSpec))

namespace TwoRounds

abbrev F := ZMod 257
instance : Fact (Nat.Prime 257) := ⟨by norm_num⟩
def cfg : Config 2 3 1 := (Config.create? 2 3 1).get (by decide)
def data (i : Fin 2 × Fin 3) : CMlPolynomialEval F 2 :=
  Vector.replicate 4 (if i.1 = 0 then 0 else if i.2 = 0 then 1 else 0)
abbrev access := (inputFamily (RingHom.id F) 2 3).spec.toPFunctor
def impl : QueryImpl (ofPFunctor access) Id :=
  (inputFamily (RingHom.id F) 2 3).behaviorOfRealizations data
def view : VirtualOracle (ofPFunctor access) (inputFamily (RingHom.id F) 2 3) := VirtualOracle.id _
theorem realizes : view.eval impl =
    (inputFamily (RingHom.id F) 2 3).behaviorOfRealizations data := VirtualOracle.eval_id impl

/-- Two actual native rounds and three indexed groups give the scoped20/257 ledger. -/
theorem bound
    {OutP : (protocol F 2 ((3 : Nat) ⌈/⌉ 1) 1).tree.ExecutionPath → Type}
    (prover : Prover.Strategy unifSpec (protocol F 2 ((3 : Nat) ⌈/⌉ 1) 1).tree
      (protocol F 2 ((3 : Nat) ⌈/⌉ 1) 1).roles OutP) :
    Pr{let accepted ← (uniformExecute (RingHom.id F) 2 3 1 cfg
      access view impl prover)}[accepted = true] ≤ (20 : ℝ≥0∞) / 257 := by
  have h := uniformExecute_soundness (RingHom.id F) 2 3 1 cfg
    access view impl data realizes prover ⟨0, by decide⟩
  simpa only [Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.cast_ofNat, ZMod.card] using h

example : (20 : ℝ≥0∞) / 257 < 1 := by
  simpa only [ENNReal.div_self (a := (257 : ℝ≥0∞)) (by norm_num) (by norm_num)] using
    ENNReal.div_lt_div_right (c := (257 : ℝ≥0∞)) (by norm_num) (by norm_num)
    (show (20 : ℝ≥0∞) < 257 by norm_num)

end TwoRounds

open Lean Elab Command

run_cmd do
  for alpha in List.finRange 17 do
    for lambda in List.finRange 17 do
      unless zeroFixedEndpoint alpha.val lambda.val == (lambda.val == 0) do
        throwError "actual complete pole-safe zero-round acceptance is not exactly lambda0"
  let poleRoots := (List.finRange 17).filter (fun lambda ↦ zeroFixedEndpoint 0 lambda.val)
  unless poleRoots.length == 1 do
    throwError "actual pole denominator event does not have one accepting lambda"

run_cmd do
  for name in #[``zeroProver, ``oneProver, ``zeroUniformEndpoint, ``oneUniformEndpoint,
      ``zeroFixedEndpoint] do
    unless (Lean.IR.findEnvDecl (← getEnv) name).isSome do
      throwError "missing actual weighted security endpoint IR: {name}"
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``uniformExecute_soundness, ``realizes, ``zero_numerator, ``one_numerator,
      ``zero_bound, ``one_bound, ``TwoRounds.realizes, ``TwoRounds.bound] do
    unless (← collectAxioms name).all allowed.contains do
      throwError "weighted whole-execution bound has an unexpected axiom: {name}"

end LogupWeightedTest

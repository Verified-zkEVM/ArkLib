/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/
import ArkLib.ProofSystem.Logup.Lookup.Security
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.NormNum.Prime
import CompPoly.Univariate.ToPoly.Degree
import Lean.Compiler.IR

/-! # Actual scalar multiplicity-prefix soundness and ordinary prover effects -/

open _root_.Interaction.Oracle OracleComp OracleSpec CompPoly Logup.Lookup
open scoped ProbabilityTheory ENNReal
open Lean Elab Command

namespace LogupLookupSecurityTest

/-- Scripted zero messages exercise actual native trees without an honest-message premise. -/
def zeroNative {R : Type} [CommRing R] {ι : Type} (ambient : OracleSpec ι) (deg : Nat) :
    (count : Nat) →
      Prover.Strategy ambient (Sumcheck.Interaction.Computable.protocol R deg count).tree
      (Sumcheck.Interaction.Computable.protocol R deg count).roles (fun _ => Nat)
  | 0 => (7 : Nat)
  | count + 1 => pure ⟨(⟨0, by simp⟩ : Sumcheck.Impl.Representation.Message R deg),
      fun choice => match choice with
      | none => pure (7 : Nat)
      | some _ => pure (zeroNative ambient deg count)⟩

def zeroWeighted {R : Type} [CommRing R] {ι : Type} (ambient : OracleSpec ι) (n K ell : Nat) :
    Prover.Strategy ambient (Logup.Interaction.protocol R n K ell).tree
      (Logup.Interaction.protocol R n K ell).roles (fun _ => Nat) :=
  fun _ => pure (pure ⟨Vector.replicate K (Vector.replicate (2 ^ n) 0),
    fun _ => pure (zeroNative ambient (ell + 2) n)⟩)

def zeroWhole {B E : Type} [CommRing B] [CommRing E] {ι : Type} (ambient : OracleSpec ι)
    (f : B →+* E) (n M P ell : Nat) :
    Prover.Strategy ambient (protocol f n M P ell).tree
      (protocol f n M P ell).roles (fun _ => Nat) :=
  pure ⟨Vector.replicate P (Vector.replicate (2 ^ n) 0),
    zeroWeighted ambient n ((M + P) ⌈/⌉ ell) ell⟩

namespace Seventeen
abbrev F := ZMod 17
instance : Fact (Nat.Prime 17) := ⟨by decide⟩
def f : F →+* F := RingHom.id F

def cfg : Config F 1 1 2 1 := (Config.create? F 1 1 2 1 17).get (by decide)
/-- False membership uses the entire declared two-piece collection. -/
def data : Data F 1 1 2 := Sum.elim (fun _ => #v[0, 0])
  (fun p => if p = 0 then #v[1, 1] else #v[2, 2])
abbrev access := (valuesFamily f 1 1 2).spec.toPFunctor
def impl : QueryImpl (ofPFunctor access) Id := (valuesFamily f 1 1 2).behaviorOfRealizations data
def view : VirtualOracle (ofPFunctor access) (valuesFamily f 1 1 2) := VirtualOracle.id _
theorem realizes : view.eval impl = (valuesFamily f 1 1 2).behaviorOfRealizations data :=
  VirtualOracle.eval_id impl
theorem false_language : ¬ InLanguage data := by unfold InLanguage; decide

theorem bound {OutP : (protocol f 1 1 2 1).tree.ExecutionPath → Type}
    (prover : Prover.Strategy unifSpec (protocol f 1 1 2 1).tree
      (protocol f 1 1 2 1).roles OutP) :
    Pr{let accepted ← uniformExecute f 1 1 2 1 cfg access view impl prover}[accepted = true] ≤
      (10 : ℝ≥0∞) / 17 := by
  have h := uniformExecute_soundness f 1 1 2 1 cfg access view impl data realizes
    prover false_language
  simpa only [Nat.reducePow, Nat.reduceAdd, Nat.reduceMul, Nat.cast_ofNat, ZMod.card] using h

theorem bound_lt_one : (10 : ℝ≥0∞) / 17 < 1 := by
  simpa only [ENNReal.div_self (a := (17 : ℝ≥0∞)) (by norm_num) (by norm_num)] using
    ENNReal.div_lt_div_right (c := (17 : ℝ≥0∞)) (by norm_num) (by norm_num)
      (show (10 : ℝ≥0∞) < 17 by norm_num)

def uniformEndpoint : ProbComp Bool :=
  uniformExecute f 1 1 2 1 cfg access view impl (zeroWhole unifSpec f 1 1 2 1)

example : (Config.create? F 1 0 1 1 17).isSome = true := by decide
example : (Config.create? F 1 1 0 1 17).isSome = true := by decide
example : (Config.create? F 1 0 0 1 17).isSome = false := by decide
example : (Config.create? F 1 1 2 0 17).isSome = false := by decide

end Seventeen

namespace TwoRounds
abbrev F := ZMod 257
instance : Fact (Nat.Prime 257) := ⟨by norm_num⟩
def f : F →+* F := RingHom.id F
def cfg : Config F 2 2 1 1 := (Config.create? F 2 2 1 1 257).get (by decide)
def data : Data F 2 2 1 := Sum.elim
  (fun _ => Vector.replicate 4 0) (fun _ => Vector.replicate 4 1)
abbrev access := (valuesFamily f 2 2 1).spec.toPFunctor
def impl : QueryImpl (ofPFunctor access) Id := (valuesFamily f 2 2 1).behaviorOfRealizations data
def view : VirtualOracle (ofPFunctor access) (valuesFamily f 2 2 1) := VirtualOracle.id _
theorem realizes : view.eval impl = (valuesFamily f 2 2 1).behaviorOfRealizations data :=
  VirtualOracle.eval_id impl
theorem false_language : ¬ InLanguage data := by unfold InLanguage; decide

/-- This instantiates the actual scalar adapter, including its pre-alpha multiplicity sender. -/
theorem bound {OutP : (protocol f 2 2 1 1).tree.ExecutionPath → Type}
    (prover : Prover.Strategy unifSpec (protocol f 2 2 1 1).tree
      (protocol f 2 2 1 1).roles OutP) :
    Pr{let accepted ← uniformExecute f 2 2 1 1 cfg access view impl prover}[accepted = true] ≤
      (20 : ℝ≥0∞) / 257 := by
  have h := uniformExecute_soundness f 2 2 1 1 cfg access view impl data realizes
    prover false_language
  simpa only [Nat.reducePow, Nat.reduceAdd, Nat.reduceMul, Nat.cast_ofNat, ZMod.card] using h

theorem bound_lt_one : (20 : ℝ≥0∞) / 257 < 1 := by
  simpa only [ENNReal.div_self (a := (257 : ℝ≥0∞)) (by norm_num) (by norm_num)] using
    ENNReal.div_lt_div_right (c := (257 : ℝ≥0∞)) (by norm_num) (by norm_num)
      (show (20 : ℝ≥0∞) < 257 by norm_num)

def uniformEndpoint : ProbComp Bool :=
  uniformExecute f 2 2 1 1 cfg access view impl (zeroWhole unifSpec f 2 2 1 1)
end TwoRounds

namespace Effects
open Seventeen (F)
def f : F →+* F := RingHom.id F
def cfg : Config F 1 1 1 2 := (Config.create? F 1 1 1 2 17).get (by decide)
def data (_ : Fin 1 ⊕ Fin 1) : CMlPolynomialEval F 1 := #v[0, 0]
abbrev access := (valuesFamily f 1 1 1).spec.toPFunctor
def impl : QueryImpl (ofPFunctor access) Id := (valuesFamily f 1 1 1).behaviorOfRealizations data
def view : VirtualOracle (ofPFunctor access) (valuesFamily f 1 1 1) := VirtualOracle.id _

abbrev ambientSpec : OracleSpec (Fin 10) := Fin 10 →ₒ F
def event (i : Fin 10) : OracleComp ambientSpec F := liftM (ambientSpec.query i)
def jointDraw : OracleComp ambientSpec ((Fin 1 → F) × (Fin 1 → F)) := do
  let z ← event 4
  let lambda ← event 5
  return (fun _ => z, fun _ => lambda)
def handler : QueryImpl ambientSpec (StateM (List Nat)) := fun i => do
  modify (· ++ [i.val])
  return ![3, 2, 7, 11, 3, 4, 13, 17, 5, 19] i

/-- Actual private effects surround the initial send and every receiver/sender continuation. -/
def prover (msg : Sumcheck.Impl.Representation.Message F 4) :
    Prover.Strategy ambientSpec (protocol f 1 1 1 2).tree
      (protocol f 1 1 1 2).roles (fun _ => F) := do
  let first ← event 0
  return ⟨#v[#v[1, 1]], fun (alpha : F) => do
    let a ← event 2
    return do
      let b ← event 3
      return ⟨#v[#v[0, 0]], fun (joint : (Fin 1 → F) × (Fin 1 → F)) => do
        let c ← event 6
        return do
          let d ← event 7
          let finish (r : F) : OracleComp ambientSpec F := do
            let e ← event 9
            return first + a + b + c + d + e + alpha + joint.1 0 + joint.2 0 + r
          return ⟨msg, fun choice => match choice with
            | none => finish 0
            | some r => finish r⟩⟩⟩

def run (msg : Sumcheck.Impl.Representation.Message F 4) : Bool × List Nat :=
  (simulateQ handler (execute f 1 1 1 2 cfg ambientSpec (event 1) jointDraw (event 8)
    access view impl (prover msg))).run []

def decomposed (msg : Sumcheck.Impl.Representation.Message F 4) : Bool × List Nat :=
  (simulateQ handler (do
    let sent ← prover msg
    Logup.Interaction.execute f 1 2 2 cfg.weighted ambientSpec (event 1) jointDraw (event 8)
      (Access.extend access (multiplicityInterface f 1 1))
      (weightedView f 1 1 1 access view)
      (Access.extendImpl access (multiplicityInterface f 1 1) impl sent.1)
      (OutP := fun _ => F) sent.2)).run []

theorem actual_bind (msg : Sumcheck.Impl.Representation.Message F 4) :
    run msg = decomposed msg := by
  exact congrArg (fun program => (simulateQ handler program).run [])
    (execute_eq_sender_bind f 1 1 1 2 cfg ambientSpec (event 1) jointDraw (event 8)
      access view impl (prover msg))

/-- The private result type genuinely depends on the actual initial multiplicity realization. -/
def Output (path : (protocol f 1 1 1 2).tree.ExecutionPath) : Type :=
  let tables : Vector (CMlPolynomialEval F 1) 1 := path.1
  Fin (((tables[0])[0]).val + 1)

def dependentProver (msg : Sumcheck.Impl.Representation.Message F 4) :
    Prover.Strategy ambientSpec (protocol f 1 1 1 2).tree
      (protocol f 1 1 1 2).roles Output :=
  Interaction.StrategyOver.TwoParty.Focal.mapOutput
    (fun path _ => (⟨0, Nat.succ_pos _⟩ : Output (TypeTree.ExecutionPath.ofTypeTreePath path)))
    (prover msg)

def dependentRun (msg : Sumcheck.Impl.Representation.Message F 4) : Bool × List Nat :=
  (simulateQ handler (execute f 1 1 1 2 cfg ambientSpec (event 1) jointDraw (event 8)
    access view impl (dependentProver msg))).run []

def zeroMessage : Sumcheck.Impl.Representation.Message F 4 := ⟨0, by simp⟩
def badMessage : Sumcheck.Impl.Representation.Message F 4 :=
  ⟨1, by rw [CPolynomial.degree_one]; norm_num⟩
end Effects

run_cmd do
  unless Effects.run Effects.zeroMessage == (true, [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]) do
    throwError "actual scalar lookup endpoint lost multiplicity-before-alpha effects"
  unless Effects.run Effects.badMessage == (false, [0, 1, 2, 3, 4, 5, 6, 7, 9]) do
    throwError "actual scalar lookup abort drew a round challenge or lost private abort response"
  unless Effects.decomposed Effects.zeroMessage == Effects.run Effects.zeroMessage do
    throwError "actual sender decomposition changed accepted execution"
  unless Effects.decomposed Effects.badMessage == Effects.run Effects.badMessage do
    throwError "actual sender decomposition changed abort execution"

run_cmd do
  unless Effects.dependentRun Effects.zeroMessage == Effects.run Effects.zeroMessage do
    throwError "dependent private output changed actual accepted scalar execution"
  unless Effects.dependentRun Effects.badMessage == Effects.run Effects.badMessage do
    throwError "dependent private output changed actual scalar abort effects"

run_cmd do
  for name in #[``Config.create?, ``protocol, ``verifier, ``execute, ``uniformExecute,
      ``zeroNative, ``zeroWeighted, ``zeroWhole, ``Seventeen.uniformEndpoint,
      ``TwoRounds.uniformEndpoint, ``Effects.prover, ``Effects.run, ``Effects.decomposed,
      ``Effects.dependentProver, ``Effects.dependentRun] do
    unless (Lean.IR.findEnvDecl (← getEnv) name).isSome do
      throwError "missing actual scalar lookup protocol executable IR: {name}"
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``Config.isSome_create?, ``execute_eq_sender_bind, ``uniformExecute_soundness,
      ``Seventeen.realizes, ``Seventeen.false_language, ``Seventeen.bound, ``Seventeen.bound_lt_one,
      ``TwoRounds.realizes, ``TwoRounds.false_language, ``TwoRounds.bound, ``TwoRounds.bound_lt_one,
      ``Effects.actual_bind] do
    unless (← collectAxioms name).all allowed.contains do
      throwError "scalar lookup whole execution has an unexpected axiom: {name}"

end LogupLookupSecurityTest

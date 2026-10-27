/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/
import ArkLibTest.ProofSystem.Logup.Lookup.Prover
import ArkLibTest.ProofSystem.Logup.Lookup.Tuple.Prover
import Lean.Compiler.IR

/-! # Native gates for the selected measured scalar and tuple defaults

The substantive fixtures retain actual histograms/helpers and nonzero formal native messages.
Adversarial wrappers change the sent data while preserving the original private continuation.
The real extension samplers use separate zero-weight fixtures that accept at every alpha/beta,
including poles. Deterministic zero limbs exercise those poles without changing the sampler.
-/

open Interaction.Oracle OracleComp OracleSpec CompPoly
namespace LogupMeasuredRuntime

/-- Alter only the first retained oracle table, preserving its original private continuation. -/
def changeFirst {E : Type} [Add E] [One E] {n K : Nat} (change : Bool)
    (tables : Vector (CMlPolynomialEval E n) K) : Vector (CMlPolynomialEval E n) K :=
  tables.mapIdx fun i table => if change && i == 0 then Vector.map (· + 1) table else table

def nativeEffects {E : Type} [CommRing E] {ι : Type} (ambient : OracleSpec ι)
    (effect : OracleComp ambient Unit)
    (prover : Prover.Strategy ambient
      (Sumcheck.Interaction.Computable.protocol E 3 1).tree
      (Sumcheck.Interaction.Computable.protocol E 3 1).roles (fun _ => Unit)) :
    Prover.Strategy ambient (Sumcheck.Interaction.Computable.protocol E 3 1).tree
      (Sumcheck.Interaction.Computable.protocol E 3 1).roles (fun _ => Unit) := do
  let sent ← prover
  return ⟨sent.1, fun
    | none => do
      let out ← sent.2 none
      effect
      return out
    | some r => do
      let out ← sent.2 (some r)
      effect
      return out⟩

def weightedEffects {E : Type} [CommRing E] {ι : Type} (ambient : OracleSpec ι)
    (K : Nat) (changeHelper : Bool) (effect : OracleComp ambient Unit)
    (prover : Prover.Strategy ambient (Logup.Interaction.protocol E 1 K 1).tree
      (Logup.Interaction.protocol E 1 K 1).roles (fun _ => Unit)) :
    Prover.Strategy ambient (Logup.Interaction.protocol E 1 K 1).tree
      (Logup.Interaction.protocol E 1 K 1).roles (fun _ => Unit) := fun alpha => do
  let afterAlpha ← prover alpha
  return do
    let sent ← afterAlpha
    let helper := changeFirst changeHelper sent.1
    return ⟨helper, fun joint => do
      let native ← sent.2 joint
      return nativeEffects ambient effect native⟩

namespace Scalar
open LogupScalarHonestTest.Small

def prover (changeMu changeHelper effects : Bool) :
    Prover.Strategy ambient combined.tree combined.roles (fun _ => Unit) := do
  let sent ← Logup.Lookup.Honest.prover f cfg data indices ambient
  let mu := changeFirst changeMu sent.1
  return ⟨mu, weightedEffects ambient 3 changeHelper
    (if effects then (event 0).map fun _ => () else pure ()) sent.2⟩

def run (changeMu changeHelper effects : Bool) : OracleComp ambient Result :=
  executeStrategiesLogged ambient combined.tree combined.roles combined.oracles access impl
    (prover changeMu changeHelper effects)
    (Logup.Lookup.verifier f 1 1 2 1 cfg ambient (event 0) joint (event 5) access view)
def summary (alpha : F) (changeMu changeHelper effects : Bool) :=
  summarize ((simulateQ (logger alpha) (run changeMu changeHelper effects)).run [])
def firstHelper (result : Result) : F :=
  let tables : Vector (CMlPolynomialEval F 1) 3 := result.path.2.2.1
  (tables.get 0).get 0
def helper (alpha : F) (change : Bool) : F :=
  firstHelper ((simulateQ (logger alpha) (run false change false)).run []).1
end Scalar

namespace Tuple
open LogupTupleHonestTest.Small

def prover (changeMu changeHelper effects : Bool) :
    Prover.Strategy ambient combined.tree combined.roles (fun _ => Unit) := do
  let sent ← Logup.Lookup.Tuple.Honest.prover f cfg prepared indices ambient
  let mu := changeFirst changeMu sent.1
  return ⟨mu, fun beta => do
    let weighted ← sent.2 beta
    if effects then let _ ← event 3; pure () else pure ()
    return weightedEffects ambient 4 changeHelper
      (if effects then (event 0).map fun _ => () else pure ()) weighted⟩

def run (changeMu changeHelper effects : Bool) : OracleComp ambient Result :=
  executeStrategiesLogged ambient combined.tree combined.roles combined.oracles access impl
    (prover changeMu changeHelper effects)
    (Logup.Lookup.Tuple.verifier f 1 1 3 2 1 cfg ambient
      (event 0) (event 1) joint (event 3) access view)
def summary (beta alpha : F) (changeMu changeHelper effects : Bool) :=
  summarize ((simulateQ (logger beta alpha) (run changeMu changeHelper effects)).run [])
def firstHelper (result : Result) : F :=
  let tables : Vector (CMlPolynomialEval F 1) 4 := result.path.2.2.2.1
  (tables.get 0).get 0
def helper (beta alpha : F) (change : Bool) : F :=
  firstHelper ((simulateQ (logger beta alpha) (run false change false)).run []).1
end Tuple

namespace TupleDuplicate
open LogupTupleHonestTest.Small (F f)
open LogupTupleDefaultTest.TwoRound

def indices : Vector (Fin 12) 4 := #v[0,4,0,4]
theorem valid : Logup.Lookup.ValidIndices prepared.keyData indices := by
  unfold Logup.Lookup.ValidIndices
  decide

def endpoint : Bool := simulateQ handler (Logup.Lookup.Tuple.execute f 2 1 3 2 1 cfg empty
  (pure 1) (pure 5) (pure joint) (pure 5) access
  (VirtualOracle.id (Logup.Lookup.Tuple.coefficientFamily f 2 1 3 2)) impl
  (Logup.Lookup.Tuple.Honest.prover f cfg prepared indices empty))
end TupleDuplicate

namespace Uniform
abbrev B := KoalaBear.Field
abbrev E := KoalaBear.Ext6
def f : B →+* E := algebraMap B E
def cfg : Logup.Lookup.Config B 1 0 1 1 :=
  (Logup.Lookup.Config.create? B 1 0 1 1 KoalaBear.fieldSize).get (by decide)
def data : Logup.Lookup.Data B 1 0 1 := Sum.elim Fin.elim0 (fun _ => #v[7,0])
def indices : Vector (Fin 2) 0 := #v[]
abbrev scalarAccess := (Logup.Lookup.valuesFamily f 1 0 1).spec.toPFunctor
def scalarImpl : QueryImpl (ofPFunctor scalarAccess) Id :=
  (Logup.Lookup.valuesFamily f 1 0 1).behaviorOfRealizations data
def scalar : ProbComp Bool := Logup.Lookup.uniformExecute f 1 0 1 1 cfg scalarAccess
  (VirtualOracle.id (Logup.Lookup.valuesFamily f 1 0 1)) scalarImpl
  (Logup.Lookup.Honest.prover f cfg data indices unifSpec)

def schema : TaggedTuple.Schema B 1 2 :=
  (TaggedTuple.Schema.mk? #v[2] #v[3]).get (by decide)
def layout : Logup.Lookup.Tuple.ProviderLayout 1 1 :=
  (Logup.Lookup.Tuple.ProviderLayout.create? 1 1 #[0]).get (by decide)
def keys : Vector (CMlPolynomialEval schema.Key 1) 1 :=
  #v[#v[⟨0,#v[0,2]⟩,⟨0,#v[4,5]⟩]]
def prepared : Logup.Lookup.Tuple.PreparedProvider schema layout 1 0 :=
  Logup.Lookup.Tuple.PreparedProvider.prepare schema layout keys (by decide)
abbrev tupleAccess := (Logup.Lookup.Tuple.coefficientFamily f 1 0 1 2).spec.toPFunctor
def tupleImpl : QueryImpl (ofPFunctor tupleAccess) Id :=
  (Logup.Lookup.Tuple.coefficientFamily f 1 0 1 2).behaviorOfRealizations
    (fun sj => prepared.coefficientTable sj.1 sj.2)
def tuple : ProbComp Bool := Logup.Lookup.Tuple.uniformExecute f 1 0 1 2 1 cfg tupleAccess
  (VirtualOracle.id (Logup.Lookup.Tuple.coefficientFamily f 1 0 1 2)) tupleImpl
  (Logup.Lookup.Tuple.Honest.prover f cfg prepared indices unifSpec)

def zeroTrace : QueryImpl unifSpec (StateM (List Nat)) := fun n => do
  modify (· ++ [n])
  return ⟨0, Nat.zero_lt_succ n⟩
end Uniform

/-- Mutate a zero-round helper while retaining the selected native continuation. -/
def zeroHelper {E : Type} [CommRing E] {ι : Type} (ambient : OracleSpec ι) (K : Nat)
    (prover : Prover.Strategy ambient (Logup.Interaction.protocol E 0 K 1).tree
      (Logup.Interaction.protocol E 0 K 1).roles (fun _ => Unit)) :
    Prover.Strategy ambient (Logup.Interaction.protocol E 0 K 1).tree
      (Logup.Interaction.protocol E 0 K 1).roles (fun _ => Unit) := fun alpha => do
  let afterAlpha ← prover alpha
  return do
    let sent ← afterAlpha
    return ⟨changeFirst true sent.1, sent.2⟩

namespace ScalarZero
open LogupScalarHonestTest.ZeroRound

def prover : Prover.Strategy ambient (Logup.Lookup.protocol f 0 1 2 1).tree
    (Logup.Lookup.protocol f 0 1 2 1).roles (fun _ => Unit) := do
  let sent ← Logup.Lookup.Honest.prover f cfg data indices ambient
  return ⟨sent.1, zeroHelper ambient 3 sent.2⟩
def endpoint : Bool × Nat := (simulateQ logger (Logup.Lookup.execute f 0 1 2 1 cfg ambient
  (pure 2) (pure (Fin.elim0, (![4,9,6] : Fin 3 → F))) round access view impl prover)).run 0
end ScalarZero

namespace TupleZero
open LogupTupleHonestTest.ZeroRound

def prover : Prover.Strategy ambient (Logup.Lookup.Tuple.protocol f 0 1 2 1).tree
    (Logup.Lookup.Tuple.protocol f 0 1 2 1).roles (fun _ => Unit) := do
  let sent ← Logup.Lookup.Tuple.Honest.prover f cfg prepared indices ambient
  return ⟨sent.1, fun beta => do
    let weighted ← sent.2 beta
    return zeroHelper ambient 3 weighted⟩
def endpoint : Bool × List Nat :=
  (simulateQ (LogupTupleHonestTest.Small.logger 1 5)
    (Logup.Lookup.Tuple.execute f 0 1 2 0 1 cfg ambient
      (LogupTupleHonestTest.Small.event 0) (LogupTupleHonestTest.Small.event 1) joint
      (LogupTupleHonestTest.Small.event 3) access view impl prover)).run []
end TupleZero

def check (label : String) (condition : Bool) : IO Unit :=
  unless condition do throw (IO.userError label)

/-- This exact suite is shared by classic acceptance and the existing compiled executable. -/
def deterministicChecks : IO Unit := do
  let scalar := ArithmeticLookupTests.Small.summary 2
  check "measured scalar lost actual histogram/cubic/source trace"
    (scalar == (true, (#v[#v[0,0],#v[1,1]], #[0,9,11,14]), 11, [0,1,2,3,4,5]))
  check "measured scalar cubic vanished off the Boolean cube"
    (CPolynomial.Raw.evalHornerSeeded 5 scalar.2.1.2 == 13)
  let scalarMu := Scalar.summary 2 true false false
  check "measured scalar retained-mu forgery accepted or skipped terminal authentication"
    (!scalarMu.1 && scalarMu.2.1.2 == scalar.2.1.2 && scalarMu.2.2.1 == 11 &&
      scalarMu.2.2.2 == [0,1,2,3,4,5])
  let scalarHelper := Scalar.summary 2 false true false
  check "measured scalar retained-helper forgery accepted or message was not retained"
    (!scalarHelper.1 && scalarHelper.2.1.2 == scalar.2.1.2 && scalarHelper.2.2.1 == 11 &&
      scalarHelper.2.2.2 == [0,1,2,3,4,5] && Scalar.helper 2 true == Scalar.helper 2 false + 1)
  let scalarEffects := Scalar.summary 2 false false true
  check "measured scalar lost post-native private effect"
    (scalarEffects.1 && scalarEffects.2.2.2 == [0,1,2,3,4,5,0])
  check "measured scalar lost private effect after public abort"
    (Scalar.summary 5 false false true ==
      (false, (#v[#v[0,0],#v[1,1]], #[13,10,4,7]), 2, [0,1,2,3,4,0]))
  check "measured scalar duplicate-witness two-round endpoint lost nonzero Q21"
    (ArithmeticLookupTests.TwoRound.summary == (true,2) &&
      LogupScalarHonestTest.TwoRound.originalFinal == 21 &&
      LogupScalarHonestTest.TwoRound.mu == #v[#v[2,2,2,2]])
  check "measured scalar zero-round terminal authentication failed"
    (ArithmeticLookupTests.ZeroRound.summary 2 == (true,0) && ScalarZero.endpoint == (false,0))
  let tuple := LogupTupleDefaultTest.Small.summary 1 5
  check "measured tuple lost actual histogram/cubic/source trace"
    (tuple == (true, (#v[#v[1,0],#v[1,0],#v[0,0]], 1, #[8,14,16,5]), 22, [0,1,2,3]))
  check "measured tuple cubic vanished off the Boolean cube"
    (CPolynomial.Raw.evalHornerSeeded 5 tuple.2.1.2.2 == 15)
  check "measured tuple rejected a true lookup at a colliding beta"
    ((LogupTupleDefaultTest.Small.summary 0 5).1)
  let tupleMu := Tuple.summary 1 5 true false false
  check "measured tuple retained-mu forgery accepted or skipped terminal authentication"
    (!tupleMu.1 && tupleMu.2.1.2.2 == tuple.2.1.2.2 && tupleMu.2.2.1 == 22 &&
      tupleMu.2.2.2 == [0,1,2,3])
  let tupleHelper := Tuple.summary 1 5 false true false
  check "measured tuple retained-helper forgery accepted or message was not retained"
    (!tupleHelper.1 && tupleHelper.2.1.2.2 == tuple.2.1.2.2 && tupleHelper.2.2.1 == 22 &&
      tupleHelper.2.2.2 == [0,1,2,3] && Tuple.helper 1 5 true == Tuple.helper 1 5 false + 1)
  check "measured tuple beta/native private effects changed"
    ((Tuple.summary 1 5 false false true).1 &&
      (Tuple.summary 1 5 false false true).2.2.2 == [0,3,1,2,3,0])
  check "measured tuple lost beta/private abort response"
    (!(Tuple.summary 0 0 false false true).1 &&
      (Tuple.summary 0 0 false false true).2.2.2 == [0,3,1,2,0])
  check "measured tuple two-round endpoint or nonzero terminal message changed"
    (LogupTupleDefaultTest.TwoRound.endpoint && TupleDuplicate.endpoint &&
      (LogupTupleDefaultTest.TwoRound.recorded #v[some 5,some 5]).2.2.1.getLast?.any
        (fun q => Sumcheck.Impl.Representation.evaluate LogupTupleHonestTest.Small.F 3 q 5 == 12))
  check "measured tuple zero-round retained-helper authentication failed"
    (LogupTupleDefaultTest.ZeroRound.summary 1 5 == (true,[0,1,2]) &&
      TupleZero.endpoint == (false,[0,1,2]))
  let scalarPole := (simulateQ Uniform.zeroTrace Uniform.scalar).run []
  let tuplePole := (simulateQ Uniform.zeroTrace Uniform.tuple).run []
  check "measured scalar named uniform pole path did not use exactly 24 existing base limbs"
    (scalarPole.1 && scalarPole.2.length == 24 &&
      scalarPole.2.all (· == KoalaBear.fieldSize - 1))
  check "measured tuple named uniform pole path did not use exactly 30 existing base limbs"
    (tuplePole.1 && tuplePole.2.length == 30 &&
      tuplePole.2.all (· == KoalaBear.fieldSize - 1))
  IO.println "measured scalar/tuple defaults: all 19 deterministic native checks passed"

open Lean Elab Command in
run_cmd do
  liftIO deterministicChecks
  unless (← collectAxioms ``TupleDuplicate.valid).all
      (#[``propext, ``Classical.choice, ``Quot.sound]).contains do
    throwError "unexpected duplicate-index fixture axiom"
  for name in #[``Scalar.run, ``Tuple.run, ``ScalarZero.endpoint, ``TupleZero.endpoint,
      ``TupleDuplicate.endpoint, ``Uniform.scalar, ``Uniform.tuple, ``deterministicChecks] do
    unless (Lean.IR.findEnvDecl (← getEnv) name).isSome do
      throwError "missing measured runtime external caller IR: {name}"
end LogupMeasuredRuntime

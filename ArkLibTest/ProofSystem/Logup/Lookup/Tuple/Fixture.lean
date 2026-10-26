/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/
import ArkLib.ProofSystem.Logup.Lookup.Tuple.Execution
import ArkLib.Interaction.Oracle.LoggedExecution
import Mathlib.Algebra.Field.ZMod
import CompPoly.Univariate.ToPoly.Degree

/-! # Actual tuple prefix fixtures with retained sources and private effects -/

open _root_.Interaction.Oracle OracleComp OracleSpec CompPoly Logup.Lookup Logup.Lookup.Tuple
namespace LogupTupleProtocolFixture
abbrev F := ZMod 17
instance : Fact (Nat.Prime 17) := ⟨by decide⟩
def f : F →+* F := RingHom.id F

def schema : TaggedTuple.Schema F 2 2 :=
  (TaggedTuple.Schema.mk? #v[2, 1] #v[2, 3]).get (by decide)
def layout : ProviderLayout 2 2 := ⟨#v[0, 1]⟩
def keys : Vector (CMlPolynomialEval schema.Key 1) 3 :=
  #v[#v[⟨0, #v[0, 1]⟩, ⟨1, #v[0]⟩],
    #v[⟨0, #v[0, 0]⟩, ⟨0, #v[0, 0]⟩], #v[⟨1, #v[0]⟩, ⟨1, #v[0]⟩]]
def prepared : PreparedProvider schema layout 1 1 :=
  PreparedProvider.prepare schema layout keys (by decide)
def cfg : Logup.Lookup.Config F 1 1 2 1 :=
  (Logup.Lookup.Config.create? F 1 1 2 1 17).get (by decide)
def mu : Vector (CMlPolynomialEval F 1) 2 := #v[#v[0, 0], #v[2, 0]]
abbrev access := (coefficientFamily f 1 1 2 2).spec.toPFunctor
def impl : QueryImpl (ofPFunctor access) Id :=
  (coefficientFamily f 1 1 2 2).behaviorOfRealizations
    (fun sj => prepared.coefficientTable sj.1 sj.2)
def view : VirtualOracle (ofPFunctor access) (coefficientFamily f 1 1 2 2) := VirtualOracle.id _

theorem realizes : view.eval impl = (coefficientFamily f 1 1 2 2).behaviorOfRealizations
    (fun sj => prepared.coefficientTable sj.1 sj.2) := VirtualOracle.eval_id impl
theorem false_lookup : ¬ InLanguage prepared.keyData := by unfold InLanguage; decide

abbrev combined := Tuple.protocol f 1 1 2 1
abbrev Message := Sumcheck.Impl.Representation.Message F 3

def affine (slope intercept : F) : Message :=
  ⟨CPolynomial.ofArray #[intercept, slope], by
    have hsize := CPolynomial.Raw.Trim.size_le_size (#[intercept, slope] : Array F)
    change (CPolynomial.ofArray #[intercept, slope]).val.size ≤ 2 at hsize
    generalize h : (CPolynomial.ofArray #[intercept, slope]).val.size = size at *
    cases size with
    | zero => simp [CPolynomial.degree, h]
    | succ size => simp only [CPolynomial.degree, h]; exact_mod_cast (show size ≤ 3 by omega)⟩

def helpers (beta : F) : Vector (CMlPolynomialEval F 1) 3 :=
  if beta = 0 then #v[#v[9, 9], #v[0, 0], #v[16, 0]]
  else #v[#v[16, 16], #v[0, 0], #v[2, 0]]
def correctMessage (beta : F) : Message := if beta = 0 then affine 1 8 else affine 15 1

abbrev ambientSpec : OracleSpec (Fin 12) := Fin 12 →ₒ F
def event (i : Fin 12) : OracleComp ambientSpec F := liftM (ambientSpec.query i)
def jointDraw : OracleComp ambientSpec ((Fin 1 → F) × (Fin 3 → F)) := do
  let z ← event 6
  let l ← event 7
  return (fun _ => z, fun k => l + k.val)
def value (beta : F) (i : Fin 12) : F :=
  if i = 1 then beta else if i = 3 then 2 else if i = 6 then 3
  else if i = 7 then 4 else if i = 10 then 5 else (i.val + 1 : Nat)
def logger (beta : F) : QueryImpl ambientSpec (StateM (List Nat)) := fun i => do
  modify (· ++ [i.val])
  return value beta i

def prover (message : F → Message) :
    Prover.Strategy ambientSpec combined.tree combined.roles (fun _ => F) := do
  let first ← event 0
  return ⟨mu, fun (beta : F) => do
    let b ← event 2
    return fun (alpha : F) => do
      let a ← event 4
      return do
        let h ← event 5
        return ⟨helpers beta, fun (joint : (Fin 1 → F) × (Fin 3 → F)) => do
          let j ← event 8
          return do
            let s ← event 9
            let finish (r : F) : OracleComp ambientSpec F := do
              let last ← event 11
              return first + b + a + h + j + s + last + beta + alpha + joint.1 0 + joint.2 0 + r
            return ⟨message beta, fun choice => match choice with
              | none => finish 0
              | some r => finish r⟩⟩⟩

def endpoint (beta : F) (message : F → Message) : Bool × List Nat :=
  (simulateQ (logger beta) (Tuple.execute f 1 1 2 2 1 cfg ambientSpec (event 1) (event 3)
    jointDraw (event 10) access view impl (prover message))).run []

def decomposed (beta : F) (message : F → Message) : Bool × List Nat :=
  (simulateQ (logger beta) (do
    let sent ← prover message
    let b ← event 1
    let continuation ← sent.2 b
    Logup.Interaction.execute (RingHom.id F) 1 3 1 cfg.weighted ambientSpec (event 3) jointDraw
      (event 10) (Access.extend access (multiplicityInterface f 1 2))
      (Tuple.weightedView f 1 1 2 2 b access view)
      (Access.extendImpl access (multiplicityInterface f 1 2) impl sent.1)
      (OutP := fun _ => F) continuation)).run []

set_option backward.isDefEq.respectTransparency false in
theorem actual_bind (beta : F) (message : F → Message) :
    endpoint beta message = decomposed beta message :=
  congrArg (fun program : OracleComp ambientSpec Bool => (simulateQ (logger beta) program).run [])
    (execute_eq_sender_beta_bind f 1 1 2 2 1 cfg ambientSpec (event 1) (event 3) jointDraw
      (event 10) access view impl (prover message))

abbrev Result := LoggedResult combined.tree combined.oracles access (fun _ => F) (fun _ => Bool)
def run (message : F → Message) : OracleComp ambientSpec Result :=
  executeStrategiesLogged ambientSpec combined.tree combined.roles
    combined.oracles access impl (prover message)
    (Tuple.verifier f 1 1 2 2 1 cfg ambientSpec (event 1) (event 3) jointDraw (event 10)
      access view)
def observed (beta : F) (message : F → Message) : Result × List Nat :=
  (simulateQ (logger beta) (run message)).run []

def summarize (result : Result × List Nat) : Bool × F × Nat × List Nat :=
  (result.1.verifierOut, result.1.proverOut, result.1.sourceLog.length, result.2)
def summary (beta : F) (message : F → Message) : Bool × F × Nat × List Nat :=
  summarize (observed beta message)

abbrev finalAccess := Access.extend
  (Access.extend (Access.extend access (multiplicityInterface f 1 2))
    (Logup.Interaction.helperInterface (E := F) 1 3))
  (Sumcheck.Interaction.Native.Core.messageInterface F Message
    (Sumcheck.Impl.Representation.evaluate F 3))
def encodeEntry (entry : (query : finalAccess.A) × finalAccess.B query) : Nat × F :=
  match entry with
  | ⟨.inl (.inl (.inl q)), answer⟩ => ((finSumFinEquiv q.1.1).val * 3 + q.1.2.val, answer)
  | ⟨.inl (.inl (.inr q)), answer⟩ => (100 + q.1.val, answer)
  | ⟨.inl (.inr q), answer⟩ => (200 + q.1.val, answer)
  | ⟨.inr _, answer⟩ => (300, answer)
def encodeSource (path : combined.tree.ExecutionPath) :
    QueryLog (ofPFunctor (TypeTree.accessAfter combined.tree combined.oracles access
      path.toBranchPath)) → List (Nat × F) := by
  rcases path with ⟨mu, beta, alpha, helper, joint, message, choice, stop⟩
  cases choice <;> exact fun log => log.map encodeEntry

def observations (beta : F) (message : F → Message) : List (Nat × F) :=
  let r := (observed beta message).1
  encodeSource r.path r.sourceLog

def Output (path : combined.tree.ExecutionPath) : Type :=
  let msg : Vector (CMlPolynomialEval F 1) 2 := path.1
  let beta : F := path.2.1
  Fin ((msg[1][0]).val + beta.val + 1)
def dependentProver (message : F → Message) :
    Prover.Strategy ambientSpec combined.tree combined.roles Output :=
  Interaction.StrategyOver.TwoParty.Focal.mapOutput
    (fun path _ => (⟨0, Nat.succ_pos _⟩ : Output (TypeTree.ExecutionPath.ofTypeTreePath path)))
    (prover message)
def dependentRun (beta : F) (message : F → Message) : Bool × List Nat :=
  (simulateQ (logger beta) (Tuple.execute f 1 1 2 2 1 cfg ambientSpec (event 1) (event 3)
    jointDraw (event 10) access view impl (dependentProver message))).run []

def abortLogger (beta : F) : QueryImpl ambientSpec (OptionT (StateM (List Nat))) := fun i =>
  (show StateM (List Nat) (Option F) from do
    modify (· ++ [i.val])
    return if i = 2 then none else some (value beta i))
def betaAbort (beta : F) : Option Bool × List Nat :=
  ((simulateQ (abortLogger beta) (Tuple.execute f 1 1 2 2 1 cfg ambientSpec (event 1) (event 3)
    jointDraw (event 10) access view impl (prover correctMessage))).run).run []

namespace ZeroRound

def schema : TaggedTuple.Schema F 1 0 :=
  (TaggedTuple.Schema.mk? #v[0] #v[0]).get (by decide)
def layout : ProviderLayout 1 1 := ⟨#v[0]⟩
def prepared : PreparedProvider schema layout 0 0 :=
  PreparedProvider.prepare schema layout #v[#v[⟨0, #v[]⟩]] (by decide)
def cfg : Logup.Lookup.Config F 0 0 1 1 :=
  (Logup.Lookup.Config.create? F 0 0 1 1 17).get (by decide)
abbrev access := (coefficientFamily f 0 0 1 0).spec.toPFunctor
def impl : QueryImpl (ofPFunctor access) Id :=
  (coefficientFamily f 0 0 1 0).behaviorOfRealizations
    (fun sj => prepared.coefficientTable sj.1 sj.2)
def view : VirtualOracle (ofPFunctor access) (coefficientFamily f 0 0 1 0) := VirtualOracle.id _
abbrev combined := Tuple.protocol f 0 0 1 1

def prover (h : F) : Prover.Strategy ambientSpec combined.tree combined.roles (fun _ => F) := do
  let first ← event 0
  return ⟨#v[#v[0]], fun (beta : F) => do
    let b ← event 2
    return fun (alpha : F) => do
      let a ← event 4
      return do
        let s ← event 5
        return ⟨#v[#v[h]], fun (joint : (Fin 0 → F) × (Fin 1 → F)) => do
          let j ← event 8
          let last ← event 11
          return first + b + a + s + j + last + beta + alpha + joint.2 0⟩⟩
def jointDraw : OracleComp ambientSpec ((Fin 0 → F) × (Fin 1 → F)) := do
  let l ← event 7
  return (Fin.elim0, fun _ => l)
def endpoint (h : F) : Bool × List Nat :=
  (simulateQ (logger 3) (Tuple.execute f 0 0 1 0 1 cfg ambientSpec (event 1) (event 3)
    jointDraw (event 10) access view impl (prover h))).run []
abbrev Result := LoggedResult combined.tree combined.oracles access (fun _ => F) (fun _ => Bool)
def observed (h : F) : Result × List Nat :=
  (simulateQ (logger 3) (executeStrategiesLogged ambientSpec combined.tree combined.roles
    combined.oracles access impl (prover h)
    (Tuple.verifier f 0 0 1 0 1 cfg ambientSpec (event 1) (event 3) jointDraw (event 10)
      access view))).run []
def summarize (result : Result × List Nat) : Bool × Nat × List Nat :=
  (result.1.verifierOut, result.1.sourceLog.length, result.2)
def summary (h : F) : Bool × Nat × List Nat := summarize (observed h)
end ZeroRound

namespace SameShape

def cfg : Logup.Lookup.Config F 1 1 2 2 :=
  (Logup.Lookup.Config.create? F 1 1 2 2 17).get (by decide)
abbrev combined := Tuple.protocol f 1 1 2 2
abbrev Message := Sumcheck.Impl.Representation.Message F 4

def widen (q : LogupTupleProtocolFixture.Message) : Message :=
  ⟨q.val, q.property.trans (by decide)⟩
def honestHelpers : Vector (CMlPolynomialEval F 1) 2 := #v[#v[9, 9], #v[16, 0]]
def wrongHelpers : Vector (CMlPolynomialEval F 1) 2 := #v[#v[9, 9], #v[8, 8]]

-- Both retained messages have exactly the same nested vector type. The wrong helper belongs to
-- a different placement of mu=[1, 1], while the actual pre - beta source retains mu=[2, 0].
def prover (wrong : Bool) :
    Prover.Strategy ambientSpec combined.tree combined.roles (fun _ => Unit) :=
  pure ⟨mu, fun (_ : F) => pure (fun (_ : F) => pure (pure
    ⟨if wrong then wrongHelpers else honestHelpers,
      fun (_ : (Fin 1 → F) × (Fin 2 → F)) => pure (pure
        ⟨if wrong then (⟨0, by simp⟩ : Message) else widen (affine 1 8),
          fun choice => match choice with
          | none => pure ()
          | some _ => pure ()⟩)⟩))⟩

def handler : QueryImpl ambientSpec Id := fun _ => (0 : F)
def endpoint (wrong : Bool) : Bool :=
  simulateQ handler (Tuple.execute f 1 1 2 2 2 cfg ambientSpec (pure 0) (pure 2)
    (pure (fun _ => 3, ![4, 6])) (pure 5) access view impl (prover wrong))
end SameShape

end LogupTupleProtocolFixture

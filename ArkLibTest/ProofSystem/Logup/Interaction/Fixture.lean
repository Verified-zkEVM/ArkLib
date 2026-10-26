/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/
import ArkLib.ProofSystem.Logup.Interaction.Protocol
import ArkLib.Interaction.Oracle.LoggedExecution
import ArkLib.Data.Probability.KoalaBear

/-! # Shared executable weighted LogUp fixtures

The two equal value columns carry opposite nonzero weights. The zero helper realizes Q=0 for
all challenges, including poles. Scripted messages test the native terminal check; they are not
an implementation of the general honest coefficient prover. The native runtime and acceptance
caller share these definitions.
-/

open Interaction.Oracle OracleComp OracleSpec CompPoly
open Logup.Interaction

namespace LogupRuntimeFixture

abbrev Base := KoalaBear.Field
abbrev E := KoalaBear.Ext6

def embedding : Base →+* E := algebraMap Base E

def cfg : Config 1 2 2 := (Config.create? 1 2 2).get (by decide)

def data (i : Fin 2 × Fin 2) : CMlPolynomialEval Base 1 :=
  if i.1 = 0 then #v[0, 0] else if i.2 = 0 then #v[1, 1] else #v[-1, -1]

def helpers (h : E) : Vector (CMlPolynomialEval E 1) 1 := #v[#v[h, h]]

abbrev access := (inputFamily embedding 1 2).spec.toPFunctor

def impl : QueryImpl (ofPFunctor access) Id :=
  (inputFamily embedding 1 2).behaviorOfRealizations data

def view : VirtualOracle (ofPFunctor access) (inputFamily embedding 1 2) := VirtualOracle.id _

theorem realizes : view.eval impl = (inputFamily embedding 1 2).behaviorOfRealizations data :=
  VirtualOracle.eval_id impl

abbrev combined := protocol E 1 1 2
abbrev Message := Sumcheck.Impl.Representation.Message E 4

/-- Two coefficient entries suffice for the scripted degree-four-bound messages. -/
def affine (a b : E) : Message :=
  ⟨CPolynomial.ofArray #[b, a], by
    have hsize := CPolynomial.Raw.Trim.size_le_size (#[b, a] : Array E)
    change (CPolynomial.ofArray #[b, a]).val.size ≤ 2 at hsize
    generalize h : (CPolynomial.ofArray #[b, a]).val.size = size at *
    cases size with
    | zero => simp [CPolynomial.degree, h]
    | succ size =>
      simp only [CPolynomial.degree, h]
      exact_mod_cast (show size ≤ 4 by omega)⟩

/-- Both receiver responses and both sender programs perform actual private effects. -/
def prover {ι : Type} {ambient : OracleSpec ι} (effect : Fin 5 → OracleComp ambient E)
    (h : E) (q : Message) :
    Prover.Strategy ambient combined.tree combined.roles (fun _ => E) := fun (alpha : E) => do
  let a ← effect 0
  return do
    let b ← effect 1
    return ⟨helpers h, fun joint => do
      let c ← effect 2
      return do
        let d ← effect 3
        return ⟨q, fun choice => match choice with
          | none => do
            let e ← effect 4
            return a+b+c+d+e+alpha+joint.1 0+joint.2 0
          | some r => do
            let e ← effect 4
            return a+b+c+d+e+alpha+joint.1 0+joint.2 0+r⟩⟩

abbrev ambientSpec : OracleSpec (Fin 9) := Fin 9 →ₒ E

def event (i : Fin 9) : OracleComp ambientSpec E := liftM (ambientSpec.query i)

def privateEffect (i : Fin 5) : OracleComp ambientSpec E :=
  event (![1, 2, 5, 6, 8] i)

def jointDraw : OracleComp ambientSpec ((Fin 1 → E) × (Fin 1 → E)) := do
  let z ← event 3
  let lambda ← event 4
  return (fun _ => z, fun _ => lambda)

def logger : QueryImpl ambientSpec (StateM (List Nat)) := fun i => do
  modify (· ++ [i.val])
  return ![2, 7, 11, 3, 4, 13, 17, 5, 19] i

abbrev Result := LoggedResult combined.tree combined.oracles access (fun _ => E) (fun _ => Bool)

def run (h : E) (q : Message) : OracleComp ambientSpec Result :=
  executeStrategiesLogged ambientSpec combined.tree combined.roles combined.oracles access impl
    (prover privateEffect h q)
    (verifier embedding 1 2 2 cfg ambientSpec (event 0) jointDraw (event 7) access view)

def observed (h : E) (q : Message) : Result × List Nat :=
  (simulateQ logger (run h q)).run []

def summarize (result : Result × List Nat) : Bool × E × Nat × List Nat :=
  (result.1.verifierOut, result.1.proverOut, result.1.sourceLog.length, result.2)

def summary (h : E) (q : Message) : Bool × E × Nat × List Nat := summarize (observed h q)

abbrev finalAccess := Access.extend
  (Access.extend access (helperInterface (E := E) 1 1))
  (Sumcheck.Interaction.Native.Core.messageInterface E Message
    (Sumcheck.Impl.Representation.evaluate E 4))

def encodeEntry (entry : (query : finalAccess.A) × finalAccess.B query) : Nat × E :=
  match entry with
  | ⟨.inl (.inl t), answer⟩ => (2*t.1.1.val+t.1.2.val, answer)
  | ⟨.inl (.inr _), answer⟩ => (4, answer)
  | ⟨.inr _, answer⟩ => (5, answer)

def encodeSource (path : combined.tree.ExecutionPath) :
    QueryLog (ofPFunctor (TypeTree.accessAfter combined.tree combined.oracles access
      path.toBranchPath)) → List (Nat × E) := by
  rcases path with ⟨alpha, helper, joint, message, choice, stop⟩
  cases choice with
  | none => exact fun log => log.map encodeEntry
  | some r => exact fun log => log.map encodeEntry

def observations (h : E) (q : Message) : List (Nat × E) :=
  let result := (observed h q).1
  encodeSource result.path result.sourceLog

def endpoint (h : E) (q : Message) : Bool × List Nat :=
  (simulateQ logger (execute embedding 1 2 2 cfg ambientSpec (event 0) jointDraw (event 7)
    access view impl (prover privateEffect h q))).run []

/-- The named endpoint uses the existing extension-field sampler and the same generic verifier. -/
def uniformEndpoint : ProbComp Bool :=
  uniformExecute embedding 1 2 2 cfg access view impl
    (prover (fun _ => pure 0) 0 (affine 0 0))

namespace ZeroRound

def cfg : Config 0 2 2 := (Config.create? 0 2 2).get (by decide)
def data (i : Fin 2 × Fin 2) : CMlPolynomialEval Base 0 :=
  if i.1 = 0 then #v[0] else if i.2 = 0 then #v[1] else #v[-1]
abbrev access := (inputFamily embedding 0 2).spec.toPFunctor
def impl : QueryImpl (ofPFunctor access) Id :=
  (inputFamily embedding 0 2).behaviorOfRealizations data
def view : VirtualOracle (ofPFunctor access) (inputFamily embedding 0 2) := VirtualOracle.id _
abbrev combined := protocol E 0 1 2

def jointDraw : OracleComp ambientSpec ((Fin 0 → E) × (Fin 1 → E)) := do
  let lambda ← event 4
  return (Fin.elim0, fun _ => lambda)

def prover (h : E) :
    Prover.Strategy ambientSpec combined.tree combined.roles (fun _ => E) := fun (alpha : E) => do
  let a ← privateEffect 0
  return do
    let b ← privateEffect 1
    return ⟨#v[#v[h]], fun joint => do
      let c ← privateEffect 2
      return a+b+c+alpha+joint.2 0⟩

abbrev Result := LoggedResult combined.tree combined.oracles access (fun _ => E) (fun _ => Bool)

def run (h : E) : OracleComp ambientSpec Result :=
  executeStrategiesLogged ambientSpec combined.tree combined.roles combined.oracles access impl
    (prover h)
    (verifier embedding 0 2 2 cfg ambientSpec (event 0) jointDraw (event 7) access view)

def summarize (result : Result × List Nat) : Bool × E × Nat × List Nat :=
  (result.1.verifierOut, result.1.proverOut, result.1.sourceLog.length, result.2)

def summary (h : E) : Bool × E × Nat × List Nat :=
  summarize ((simulateQ logger (run h)).run [])

end ZeroRound

end LogupRuntimeFixture

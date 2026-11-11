/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Interaction.Core.Composition

/-!
# Components that are not run outputs live in their own universes

Ambient oracle indices, input oracle indices, output oracle indices, input statements and input
witnesses each take their own universe. The instances below put an oracle index in `Type 1`
with responses in `Type 0`, an input statement in `Type 2` and an input witness in `Type 1`,
while moves, run outputs and oracle responses stay in `Type 0`. They typecheck against
`Verifier`, `OracleVerifier`, `Reduction`, both appends, the oracle routing laws and an oracle run.
A run returns the output oracle data `∀ j, B p j`, so the run's output index is in `Type 0`.
-/

open PFunctor PFunctor.FreeM Interaction.Core Interaction.Oracle OracleComp

namespace Interaction.Core.UniverseCanaryTests

/-- Ambient oracles indexed by types, answering in `Bool`: the index lies in `Type 1`. -/
abbrev bigAmbient : OracleSpec.{1, 0} Type := Type →ₒ Bool

/-- An ambient oracle with an index in `Type 0`, which a prover can query. -/
abbrev smallAmbient : OracleSpec.{0, 0} Unit := Unit →ₒ Bool

/-- A natural number answers the unit query with itself. -/
@[reducible]
def natInterface : OracleInterface Nat where
  Query := Unit
  toOC.spec := Unit →ₒ Nat
  toOC.impl _ := read

/-- Input oracles indexed by types (`Type 1`) with natural-number data (`Type 0`). -/
@[instance_reducible]
def bigInputs : OracleFamily.{1, 0, 0} Type (fun _ => Nat) := ⟨fun _ => natInterface⟩

/-- The protocol with no rounds. -/
abbrev done : Protocol := .pure ⟨⟩

/-- The oracle protocol with no rounds. -/
abbrev oracleDone : OracleProtocol := .pure ⟨⟩

/-! ### Plain verifiers and reductions -/

/-- A plain verifier with an ambient index in `Type 1` and an input statement in `Type 2`. -/
def plainVerifier : Verifier bigAmbient done (Type 1) (fun _ => Bool) where
  decide _ _ _ := liftM (bigAmbient.query Nat)

/-- A suffix whose input statement is the prefix's `Bool` output. -/
def plainSuffix : Verifier bigAmbient done Bool (fun _ => Bool) where
  decide b _ _ := pure (!b)

/-- Plain append with the large ambient index and input statement. -/
def plainAppend : Verifier bigAmbient (done.append (fun _ => done)) (Type 1) (fun _ => Bool) :=
  plainVerifier.append (fun _ => plainSuffix)

/-- A reduction with an input statement in `Type 2` and an input witness in `Type 1`. The ambient
index stays in `Type 0`, because the prover runs in `OracleComp smallAmbient`. -/
def reduction : Reduction smallAmbient done (Type 1) Type (fun _ => Unit) (fun _ => PUnit) where
  prover _ _ := pure ⟨⟩
  verifier := { decide := fun _ _ _ => pure () }

/-! ### Oracle verifiers -/

/-- An oracle verifier whose ambient, input and output indices lie in `Type 1` and whose input
statement lies in `Type 2`. It queries the input oracle at index `Nat`. -/
def oracleVerifier : OracleVerifier bigAmbient oracleDone (Type 1) (fun _ => Nat) bigInputs
    (fun _ => bigInputs) where
  decide _ p _ := by
    cases p
    exact liftM ((bigAmbient + (sumFamily bigInputs (pathFamily oracleDone ⟨⟩)).spec).query
      (.inr ⟨.inl Nat, ()⟩))
  outputMap _ p _ := OracleMap.embedding (sumFamily bigInputs (pathFamily oracleDone p))
    (fun X => .inl X)

/-- A suffix whose middle oracle family is indexed by types. -/
def oracleSuffix : OracleVerifier bigAmbient oracleDone Nat (fun _ => Nat) bigInputs
    (fun _ => bigInputs) where
  decide n _ _ := pure (n + 1)
  outputMap _ p _ := OracleMap.embedding (sumFamily bigInputs (pathFamily oracleDone p))
    (fun X => .inl X)

/-- The composite output map ignores the intermediate statement, so any certificate holds. -/
def oracleCompatible :
    OracleVerifier.OutputCompatibility oracleVerifier (fun _ => oracleSuffix) where
  outputMap stmt p v :=
    (oracleSuffix.outputMap 0 (Path.split oracleDone (fun _ => oracleDone) p).2
      (View.split oracleDone (fun _ => oracleDone) p v).2).comp
      (OracleVerifier.suffixRoute oracleVerifier stmt p v)
  agrees _ _ _ _ _ _ := rfl

/-- Oracle append with large ambient, input, middle and output indices. -/
def oracleAppend := oracleVerifier.append (fun _ => oracleSuffix) oracleCompatible

/-- The oracle routing law at large indices. -/
theorem oracleAppend_decideWith (stmt : Type 1)
    (p : Path (oracleDone.append (fun _ => oracleDone)))
    (v : View (oracleDone.append (fun _ => oracleDone)) p)
    (data : ∀ i, (sumFamily bigInputs
      (pathFamily (oracleDone.append (fun _ => oracleDone)) p)).Realization i) :
    oracleAppend.decideWith stmt p v data =
      oracleVerifier.decideWith stmt (Path.split oracleDone (fun _ => oracleDone) p).1
          (View.split oracleDone (fun _ => oracleDone) p v).1
          ((OracleVerifier.prefixRoute (inputs := bigInputs) p).f data) >>= fun
        | none => pure none
        | some mid => oracleSuffix.decideWith mid
            (Path.split oracleDone (fun _ => oracleDone) p).2
            (View.split oracleDone (fun _ => oracleDone) p v).2
            ((OracleVerifier.suffixRoute oracleVerifier stmt p v).f data) :=
  OracleVerifier.append_decideWith _ _ _ _ _ _ _

/-- Routing through an oracle map with a large input index agrees with materialized data. -/
theorem embedding_simulate_eq (x : Type → Nat) {α : Type}
    (program : OracleComp (bigInputs.reindex (fun X : Type => X)).spec α) :
    simulateQ (bigInputs.behaviorOfRealizations x)
        (simulateQ (OracleMap.embedding bigInputs (fun X : Type => X)).impl program) =
      simulateQ ((bigInputs.reindex (fun X : Type => X)).behaviorOfRealizations
        ((OracleMap.embedding bigInputs (fun X : Type => X)).f x)) program :=
  OracleMap.simulate_eq _ x program

/-! ### An oracle run with a large input index -/

/-- One natural-number output oracle with an index in `Type 0`, as a run requires. -/
@[instance_reducible]
def smallOutputs : OracleFamily.{0, 0, 0} Unit (fun _ => Nat) := ⟨fun _ => natInterface⟩

/-- An oracle verifier that a prover can run against. Its ambient index and output index are in
`Type 0`, while its input oracle index and input statement stay in `Type 1` and `Type 2`. -/
def runnable : OracleVerifier smallAmbient oracleDone (Type 1) (fun _ => Nat) bigInputs
    (fun _ => smallOutputs) where
  decide _ p _ := by
    cases p
    exact liftM ((smallAmbient + (sumFamily bigInputs (pathFamily oracleDone ⟨⟩)).spec).query
      (.inr ⟨.inl Bool, ()⟩))
  outputMap _ p _ := OracleMap.embedding (sumFamily bigInputs (pathFamily oracleDone p))
    (fun _ => .inl Bool)

/-- The ambient oracle answers `true`; the protocol has no challenges. -/
def handler : QueryImpl (smallAmbient + challengeSpec oracleSig oracleDone) Id
  | .inl _ => true
  | .inr c => c.val.elim

/-- The prover of the protocol with no rounds. -/
def idle : Prover oracleSig smallAmbient oracleDone (fun _ => PUnit) := pure ⟨⟩

/-- The run on input data that is `3` at every type. -/
def observation := simulateQ handler (runnable.run (Type 0) (fun _ => 3) idle)

/-- The run answers the input query at index `Bool` from the data, and the output oracle at `()`
is the input oracle at `Bool`. -/
example : observation.2.2.map (fun out => (out.1, out.2 ())) = some (3, 3) := rfl

end Interaction.Core.UniverseCanaryTests

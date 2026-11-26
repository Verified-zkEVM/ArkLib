/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Interaction.Composition

/-!
# Oracle bundles, families and queries in their own universes

Statements, witnesses, ambient oracle indices, output oracle indices, moves and run outputs lie
in `Type`. Input oracle indices, input and output oracle query types and the query types of
oracle nodes keep their own universes until the later migration steps of record D2. The instances
below put an input oracle index in `Type 1`, input oracle queries in `Type 1` and output oracle
queries in `Type 2`, with data and responses in `Type 0`. They typecheck against
`OracleVerifier`, the oracle append, the oracle routing laws and oracle runs. A run returns the
output oracle data `∀ j, B p j`. The security definitions take their data in `Type`, so this file
does not instantiate them.
-/
open PFunctor PFunctor.FreeM Interaction Interaction.Oracle OracleComp

namespace Interaction.UniverseCanaryTests

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
abbrev oracleDone : OracleProtocol.{0, 0} := .pure ⟨⟩

/-- Routing through an oracle map with a large input index agrees with materialized data. -/
theorem embedding_simulate_eq (x : Type → Nat) {α : Type}
    (program : OracleComp (bigInputs.reindex (fun X : Type => X)).spec α) :
    simulateQ (bigInputs.behaviorOfRealizations x)
        (simulateQ (OracleMap.embedding bigInputs (fun X : Type => X)).impl program) =
      simulateQ ((bigInputs.reindex (fun X : Type => X)).behaviorOfRealizations
        ((OracleMap.embedding bigInputs (fun X : Type => X)).f x)) program :=
  OracleMap.simulate_eq (OracleMap.embedding bigInputs (fun X : Type => X)) x program

/-! ### An oracle run with a large input index -/

/-- One natural-number output oracle with an index in `Type 0`, as a run requires. -/
@[instance_reducible]
def smallOutputs : OracleFamily.{0, 0, 0} Unit (fun _ => Nat) := ⟨fun _ => natInterface⟩

/-- An oracle verifier that a prover can run against. Its ambient index, output index and
statement are in `Type 0`, while its input oracle index stays in `Type 1`. -/
def runnable : OracleVerifier smallAmbient oracleDone Unit (fun _ => Nat) bigInputs
    (fun _ => smallOutputs) where
  decide _ p _ := by
    cases p
    exact liftM ((smallAmbient + (pathBundle bigInputs oracleDone ⟨⟩).spec).query
      (.inr (.inl ⟨Bool, ()⟩)))
  outputMap _ _ _ := (OracleMap.embedding bigInputs (fun _ : Unit => Bool)).comp
    (OracleMap.fst _ _)

/-- The ambient oracle answers `true`; the protocol has no challenges. -/
def handler : QueryImpl (smallAmbient + challengeSpec oracleSig oracleDone) Id
  | .inl _ => true
  | .inr c => c.val.elim

/-- The prover of the protocol with no rounds. -/
def idle : Prover oracleSig smallAmbient oracleDone (fun _ => PUnit) := pure ⟨⟩

/-- The run on input data that is `3` at every type. -/
def observation := simulateQ handler (runnable.run () (fun _ => 3) idle)

/-- The run answers the input query at index `Bool` from the data, and the output oracle at `()`
is the input oracle at `Bool`. -/
example : observation.2.2.map (fun out => (out.1, out.2 ())) = some (3, 3) := rfl

/-! ### Input and output query types in their own universes -/

/-- A natural number answers every query `X : Type` with itself. The query type `Type` lies in
`Type 1`, while the data and the responses lie in `Type 0`. -/
@[reducible]
def typeQueries : OracleInterface.{0, 1} Nat where
  Query := Type
  toOC.spec := Type →ₒ Nat
  toOC.impl _ := read

/-- A natural number answers every query `X : Type 1` with itself; the query type lies in
`Type 2`. -/
@[reducible]
def bigTypeQueries : OracleInterface.{0, 2} Nat where
  Query := Type 1
  toOC.spec := Type 1 →ₒ Nat
  toOC.impl _ := read

/-- One input oracle whose queries are types, with natural-number data and responses. -/
@[instance_reducible]
def typeQueryInputs : OracleFamily.{0, 0, 1} Unit (fun _ => Nat) := ⟨fun _ => typeQueries⟩

/-- One oracle whose queries lie in `Type 1`, a query universe different from the inputs'. -/
@[instance_reducible]
def bigQueryOracles : OracleFamily.{0, 0, 2} Unit (fun _ => Nat) := ⟨fun _ => bigTypeQueries⟩

/-- The output oracle answers each query by asking the input oracle at `Nat`. -/
def forwardQueries (p : Path oracleDone) :
    OracleMap (pathBundle typeQueryInputs oracleDone p) (OracleBundle.ofFamily bigQueryOracles)
    where
  f x _ := x.1 ()
  impl _ := (OracleMap.fst typeQueryInputs (oracleMessageFamily oracleDone p)).impl ⟨(), Nat⟩
  law _ _ := rfl

/-- An oracle verifier whose input queries lie in `Type 1` and whose output queries lie in
`Type 2`, while its moves, its result and all oracle responses lie in `Type 0`. It queries its
input at the type `Bool`. -/
def typeQueryVerifier : OracleVerifier smallAmbient oracleDone Unit (fun _ => Nat)
    typeQueryInputs (fun _ => bigQueryOracles) where
  decide _ p _ := by
    cases p
    exact liftM ((smallAmbient + (pathBundle typeQueryInputs oracleDone ⟨⟩).spec).query
      (.inr (.inl ⟨(), Bool⟩)))
  outputMap _ p _ := forwardQueries p

/-- The run answers the input query at the type `Bool` from the data `5`, and the output oracle
answers a query in `Type 1` with the same value. -/
example :
    (simulateQ handler (typeQueryVerifier.run () (fun _ => 5) idle)).2.2.map
      (fun out => (out.1, bigQueryOracles.behaviorOfRealizations out.2 ⟨(), Type⟩)) =
      some ((5, 5) : Nat × Nat) := rfl

/-- A suffix whose input oracle has queries in `Type 2` and whose output oracle has queries in
`Type 0`. It adds one to its input statement after querying its input at the type `Type`. -/
def typeQuerySuffix : OracleVerifier smallAmbient oracleDone Nat (fun _ => Nat)
    bigQueryOracles (fun _ => smallOutputs) where
  decide n p _ := by
    cases p
    exact (fun m => n + m) <$> liftM
      ((smallAmbient + (pathBundle bigQueryOracles oracleDone ⟨⟩).spec).query
        (.inr (.inl ⟨(), Type⟩)))
  outputMap _ p _ :=
    { f := fun x _ => x.1 ()
      impl := fun _ =>
        (OracleMap.fst bigQueryOracles (oracleMessageFamily oracleDone p)).impl ⟨(), Type⟩
      law := fun _ _ => rfl }

/-- The composite output map ignores the intermediate statement, so any certificate holds. -/
def typeQueryCompatible :
    OracleVerifier.OutputCompatibility typeQueryVerifier (fun _ => typeQuerySuffix) where
  outputMap stmt p v :=
    (typeQuerySuffix.outputMap 0 (Path.split oracleDone (fun _ => oracleDone) p).2
      (View.split oracleDone (fun _ => oracleDone) p v).2).comp
      (OracleVerifier.suffixRoute typeQueryVerifier stmt p v)
  agrees _ _ _ _ _ _ := rfl

/-- Oracle append whose input, middle and output query types lie in three different universes. -/
def typeQueryAppend := typeQueryVerifier.append (fun _ => typeQuerySuffix) typeQueryCompatible

/-- The oracle routing law when the input, middle and output query universes differ. -/
theorem typeQueryAppend_decideWith (stmt : Unit)
    (p : Path (oracleDone.append (fun _ => oracleDone)))
    (v : View (oracleDone.append (fun _ => oracleDone)) p)
    (data : (pathBundle typeQueryInputs (oracleDone.append (fun _ => oracleDone)) p).Data) :
    typeQueryAppend.decideWith stmt p v data =
      typeQueryVerifier.decideWith stmt (Path.split oracleDone (fun _ => oracleDone) p).1
          (View.split oracleDone (fun _ => oracleDone) p v).1
          ((OracleVerifier.prefixRoute (inputs := typeQueryInputs) p).f data) >>= fun
        | none => pure none
        | some mid => typeQuerySuffix.decideWith mid
            (Path.split oracleDone (fun _ => oracleDone) p).2
            (View.split oracleDone (fun _ => oracleDone) p v).2
            ((OracleVerifier.suffixRoute typeQueryVerifier stmt p v).f data) :=
  OracleVerifier.append_decideWith _ _ _ _ _ _ _

/-! ### Independent oracle-node queries -/

/-- The default leaves retain the original protocol carrier by definitional equality. -/
example : OracleProtocol.{0, 1} = FreeM OraclePoly.{0, 1} PUnit.{1} := rfl

/-- A nontrivial leaf type is an actual return type of the authored tree. -/
def returningTree : OracleProtocol.{0, 1} Nat := .pure 23

/-- The explicit leaf parameter stores a value that can be read from the tree. -/
example : (match returningTree with | .pure n => n | .liftBind _ _ => 0) = 23 := rfl

/-- A small payload with queries in `Type 1` is attached to an actual oracle node. -/
def typeQueryProtocol : OracleProtocol.{0, 1} :=
  .liftBind (.oracle Nat typeQueries) (fun _ => .pure ⟨⟩)

end Interaction.UniverseCanaryTests

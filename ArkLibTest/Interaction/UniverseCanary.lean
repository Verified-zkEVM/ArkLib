/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Interaction.Composition

/-!
# Oracle bundles at `Type`

Bundle routing, append and runs use data in `Type`. The final examples check the default and
explicit leaf types of oracle protocols.
-/
open PFunctor PFunctor.FreeM Interaction Interaction.Oracle OracleComp

namespace Interaction.UniverseCanaryTests

/-- An ambient oracle with an index in `Type 0`, which a prover can query. -/
abbrev smallAmbient : OracleSpec.{0, 0} Unit := Unit →ₒ Bool

/-- A natural number answers the unit query with itself. -/
@[reducible]
def natInterface : OracleInterface Nat where
  Query := Unit
  spec := Unit →ₒ Nat
  answer m _ := m

/-- Input oracles indexed by Boolean values with natural-number data. -/
@[instance_reducible]
def bigInputs : OracleFamily Bool (fun _ => Nat) := ⟨fun _ => natInterface⟩

/-- The protocol with no rounds. -/
abbrev done : Protocol := .pure ⟨⟩

/-- The oracle protocol with no rounds. -/
abbrev oracleDone : OracleProtocol := .pure ⟨⟩

/-- Routing through an oracle map agrees with materialized data. -/
theorem embedding_simulate_eq (x : Bool → Nat) {α : Type}
    (program : OracleComp (bigInputs.reindex (fun X : Bool => X)).spec α) :
    simulateQ (bigInputs.behaviorOfRealizations x)
        (simulateQ (OracleMap.embedding bigInputs (fun X : Bool => X)).impl program) =
      simulateQ ((bigInputs.reindex (fun X : Bool => X)).behaviorOfRealizations
        ((OracleMap.embedding bigInputs (fun X : Bool => X)).f x)) program :=
  OracleMap.simulate_eq (OracleMap.embedding bigInputs (fun X : Bool => X)) x program

/-! ### An oracle run at `Type` -/

/-- One natural-number output oracle with an index in `Type 0`, as a run requires. -/
@[instance_reducible]
def smallOutputs : OracleFamily Unit (fun _ => Nat) := ⟨fun _ => natInterface⟩

/-- An oracle verifier with all indices, data and statements in `Type`. -/
def runnable : OracleVerifier smallAmbient oracleDone Unit (fun _ => Nat) bigInputs
    (fun _ => smallOutputs) where
  decide _ p _ := by
    cases p
    exact liftM ((smallAmbient + (pathBundle bigInputs oracleDone ⟨⟩).spec).query
      (.inr (.inl ⟨true, ()⟩)))
  outputMap _ _ _ := (OracleMap.embedding bigInputs (fun _ : Unit => true)).comp
    (OracleMap.fst _ _)

/-- The ambient oracle answers `true`; the protocol has no challenges. -/
def handler : QueryImpl (smallAmbient + challengeSpec oracleSig oracleDone) Id
  | .inl _ => true
  | .inr c => c.val.elim

/-- The prover of the protocol with no rounds. -/
def idle : Prover oracleSig smallAmbient oracleDone (fun _ => PUnit) := pure ⟨⟩

/-- The run on input data that is `3` at every index. -/
def observation := simulateQ handler (runnable.run () (fun _ => 3) idle)

/-- The run answers the input query at index `true` from the data, and the output oracle at `()`
is the input oracle at `true`. -/
example : observation.2.2.map (fun out => (out.1, out.2 ())) = some (3, 3) := rfl

/-! ### Distinct input and output query types -/

/-- A natural number answers every Boolean query with itself. -/
@[reducible]
def bigTypeQueries : OracleInterface Nat where
  Query := Bool
  spec := Bool →ₒ Nat
  answer m _ := m

/-- One input oracle with unit queries and natural-number data and responses. -/
@[instance_reducible]
def typeQueryInputs : OracleFamily Unit (fun _ => Nat) := ⟨fun _ => natInterface⟩

/-- One oracle with Boolean queries, distinct from the input's unit queries. -/
@[instance_reducible]
def bigQueryOracles : OracleFamily Unit (fun _ => Nat) := ⟨fun _ => bigTypeQueries⟩

/-- The output oracle answers each query by asking the input oracle at `()`. -/
def forwardQueries (p : Path oracleDone) :
    OracleMap (pathBundle typeQueryInputs oracleDone p) (OracleBundle.ofFamily bigQueryOracles)
    where
  f x _ := x.1 ()
  impl _ := (OracleMap.fst typeQueryInputs (oracleMessageBundle oracleDone p)).impl ⟨(), ()⟩
  law _ _ := rfl

/-- An oracle verifier with unit input queries and Boolean output queries, all at `Type`. -/
def typeQueryVerifier : OracleVerifier smallAmbient oracleDone Unit (fun _ => Nat)
    typeQueryInputs (fun _ => bigQueryOracles) where
  decide _ p _ := by
    cases p
    exact liftM ((smallAmbient + (pathBundle typeQueryInputs oracleDone ⟨⟩).spec).query
      (.inr (.inl ⟨(), ()⟩)))
  outputMap _ p _ := forwardQueries p

/-- The run answers the unit input query from the data `5`, and the output oracle
answers a Boolean query with the same value. -/
example :
    (simulateQ handler (typeQueryVerifier.run () (fun _ => 5) idle)).2.2.map
      (fun out => (out.1, bigQueryOracles.behaviorOfRealizations out.2 ⟨(), true⟩)) =
      some ((5, 5) : Nat × Nat) := rfl

/-- A suffix with Boolean input queries and unit output queries.
It adds the input oracle answer to its statement. -/
def typeQuerySuffix : OracleVerifier smallAmbient oracleDone Nat (fun _ => Nat)
    bigQueryOracles (fun _ => smallOutputs) where
  decide n p _ := by
    cases p
    exact (fun m => n + m) <$> liftM
      ((smallAmbient + (pathBundle bigQueryOracles oracleDone ⟨⟩).spec).query
        (.inr (.inl ⟨(), true⟩)))
  outputMap _ p _ :=
    { f := fun x _ => x.1 ()
      impl := fun _ =>
        (OracleMap.fst bigQueryOracles (oracleMessageBundle oracleDone p)).impl ⟨(), true⟩
      law := fun _ _ => rfl }

/-- The composite output map ignores the intermediate statement, so any certificate holds. -/
def typeQueryCompatible :
    OracleVerifier.OutputCompatibility typeQueryVerifier (fun _ => typeQuerySuffix) where
  outputMap stmt p v :=
    (typeQuerySuffix.outputMap 0 (Path.split oracleDone (fun _ => oracleDone) p).2
      (View.split oracleDone (fun _ => oracleDone) p v).2).comp
      (OracleVerifier.suffixRoute typeQueryVerifier stmt p v)
  agrees _ _ _ _ _ _ := rfl

/-- Oracle append with unit input, Boolean middle and unit output query types. -/
def typeQueryAppend := typeQueryVerifier.append (fun _ => typeQuerySuffix) typeQueryCompatible

/-- The oracle routing law with distinct query carriers at stage boundaries. -/
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

/-! ### Leaf types of oracle protocols -/

/-- The default leaves retain the original protocol carrier by definitional equality. -/
example : OracleProtocol = FreeM OraclePoly Unit := rfl

/-- A nontrivial leaf type is an actual return type of the authored tree. -/
def returningTree : OracleProtocol Nat := .pure 23

/-- The explicit leaf parameter stores a value that can be read from the tree. -/
example : (match returningTree with | .pure n => n | .liftBind _ _ => 0) = 23 := rfl

end Interaction.UniverseCanaryTests

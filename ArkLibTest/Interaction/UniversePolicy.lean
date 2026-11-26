/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Interaction.Composition
import ArkLib.Interaction.Security.Knowledge
import ArkLib.Interaction.Security.RoundByRound

/-!
# The universe policy of record D2

Record D2 (`docs/design/interaction-rebuild/D2-ownership-and-universes.md`, "Universe policy")
puts data in `Type` and descriptions of data in `Type 1`, keeps one adversary universe that the
model argument determines and the result universe of a generic monad, and leaves generic code over
an arbitrary `P : PFunctor` in PolyFun's universes. This file checks each promise:

* the vocabulary has no universe parameters and needs no universe annotation at a use;
* generic protocol code runs at a large polynomial `P : PFunctor.{u + 1, u}`, where a move can be
  a type;
* an `AdversaryModel` whose adversaries lie in `Type 1` instantiates the security definitions
  with no annotation;
* the generic draw and soundness APIs take a monad `m : Type → Type 1`.

The last sections check oracle bundles, routing, append and runs with all data in `Type`, and the
leaf types of oracle protocols.
-/

open PFunctor PFunctor.FreeM Interaction Interaction.Oracle OracleComp OracleSpec
open TwoParty TwoParty.Lens
open scoped ENNReal

universe u

namespace Interaction.UniversePolicyTests

/-! ### The vocabulary has no universe parameters -/

/-- Fail unless each named constant has no universe parameters. -/
def checkMonomorphic (names : List Lean.Name) : Lean.Elab.Command.CommandElabM Unit := do
  let env ← Lean.getEnv
  for n in names do
    match env.find? n with
    | none => throwError "unknown constant {n}"
    | some ci =>
      unless ci.levelParams.isEmpty do
        throwError "{n} has universe parameters {ci.levelParams}"

run_cmd checkMonomorphic [``Interaction.Protocol, ``Interaction.OracleProtocol,
    ``Interaction.PlainPos, ``Interaction.PlainPoly, ``Interaction.OraclePos,
    ``Interaction.OraclePoly, ``Interaction.plainSig, ``Interaction.oracleSig,
    ``Interaction.viewSig, ``Interaction.eraseOracle, ``Interaction.rolePoly0,
    ``OracleInterface, ``emptySpec0,
    ``Interaction.OracleBundle, ``Interaction.Oracle.ClaimFamily,
    ``Interaction.Oracle.Problem, ``Interaction.Oracle.Relation,
    ``Interaction.OracleVerifier, ``Interaction.Verifier]

/-- A constant without arguments takes no universe annotation. -/
def zeroComp : OracleComp emptySpec0 Nat := pure 3

/-- Its lemma names the same constant. A rewrite with it needs no annotation either. -/
theorem zeroComp_eq : zeroComp = pure 3 := rfl

run_cmd checkMonomorphic [``zeroComp, ``zeroComp_eq]

/-- A protocol with one message and one challenge, written with no annotation. -/
def twoMoves : Protocol :=
  .liftBind (.message Nat) fun _ => .liftBind (.challenge Bool) fun _ => .pure ⟨⟩

/-- Its transcripts are data in `Type`. -/
example : Type := Transcript plainSig twoMoves

/-- The protocol types are the free monads over the position polynomials, at `Type 1`. -/
example : (Protocol : Type 1) = FreeM PlainPoly Unit := rfl

example : (OracleProtocol : Type 1) = FreeM OraclePoly Unit := rfl

/-- The signatures land in the role polynomial at `Type`. -/
example : (plainSig : PFunctor.Lens PlainPoly rolePoly0) = plainSig := rfl

/-- The owner of each plain position is fixed by the signature. -/
example (X : Type) : owner plainSig (.message X) = .sender := rfl

example (C : Type) : owner plainSig (.challenge C) = .receiver := rfl

/-- A hypothesis and a goal that name the same round-by-round knowledge soundness statement
elaborate at the same universes. The hypothesis therefore closes the goal. -/
example {P : PFunctor.{1, 0}} (l : PFunctor.Lens P rolePoly0) {S : Type} {Win : S → Type}
    (s : FreeM P Unit) {W : S → Transcript l s → Type} (admissible : S → Prop)
    (relIn : (stmt : S) → Win stmt → Prop)
    (validOutput : (stmt : S) → (tr : Transcript l s) → W stmt tr → Prop)
    (draw : PrefixDraw l ProbComp s) (ε : PrefixError l s)
    (h : rbrKnowledgeSoundness l s admissible relIn validOutput draw ε) :
    rbrKnowledgeSoundness l s admissible relIn validOutput draw ε := h

/-! ### Generic code at a large polynomial -/

section LargePolynomial

variable {P : PFunctor.{u + 1, u}} (l : PFunctor.Lens P rolePoly.{u})

/-- Node splitting of an appended protocol holds over any polynomial in `PFunctor.{u + 1, u}`. -/
example (s₁ : FreeM P PUnit) (s₂ : Path s₁ → FreeM P PUnit) (n : Node (s₁.append s₂)) :
    Node.appendJoin s₁ s₂ (Node.appendSplit s₁ s₂ n) = n :=
  Node.appendJoin_appendSplit s₁ s₂ n

/-- Transcript append and split are inverse at a large polynomial. -/
example (s₁ : FreeM P PUnit) (s₂ : Path s₁ → FreeM P PUnit) (tr₁ : Transcript l s₁)
    (tr₂ : Transcript l (s₂ tr₁.path)) :
    Transcript.split s₁ s₂ (Transcript.append s₁ s₂ tr₁ tr₂) = ⟨tr₁, tr₂⟩ :=
  Transcript.split_append s₁ s₂ tr₁ tr₂

/-- The challenge specification of a large protocol answers each node with a move in `Type u`. -/
example (s : FreeM P PUnit) : OracleSpec.{u, u} (ChallengeNode l s) := challengeSpec l s

end LargePolynomial

/-- The rest of `sendsAType` after the prover sends the type `α`: one challenge in `α`. -/
abbrev afterType (α : Type) : FreeM rolePoly.{1} PUnit.{2} :=
  .liftBind (.receiver, ULift.{1} α) fun _ => .pure ⟨⟩

/-- A protocol over `rolePoly.{1}` whose first move is a type, sent by the prover. The second
move is a value of that type. -/
abbrev sendsAType : FreeM rolePoly.{1} PUnit.{2} :=
  .liftBind (.sender, Type) afterType

/-- A transcript that sends `Nat` and then the challenge `5`. -/
def sendsNat : Transcript (PFunctor.Lens.id rolePoly.{1}) sendsAType :=
  PathAlong.cons (PFunctor.Lens.id rolePoly.{1}) (Role.sender, Type) afterType Nat
    (PathAlong.cons (PFunctor.Lens.id rolePoly.{1}) (Role.receiver, ULift.{1} Nat)
      (fun _ => FreeM.pure PUnit.unit) (ULift.up 5) PUnit.unit)

/-- The transcript's first move is the type that the prover sent. -/
example :
    PathAlong.head (PFunctor.Lens.id rolePoly.{1}) (Role.sender, Type) afterType sendsNat = Nat :=
  rfl

/-- The challenge node of the second move is a node at `Type 1`. Its draw returns a value in
`Type 1`. -/
example : (challengeSpec (PFunctor.Lens.id rolePoly.{1}) sendsAType
    ⟨Sum.inr (Sigma.mk Nat (Sum.inl PUnit.unit)), rfl⟩ : Type 1) = ULift.{1} Nat := rfl

/-! ### An adversary in `Type 1` -/

section LargeAdversary

/-- An adversary that carries its own carrier type, as a quantum prover carries its registers.
It is in `Type 1`. -/
structure CarrierAdversary : Type 1 where
  /-- The adversary's carrier. -/
  Carrier : Type
  /-- The adversary's state. -/
  state : Carrier
  /-- The claim it outputs. -/
  claim : Carrier → Bool

/-- Every statement is attacked by a carrier adversary; the outcome is its claim. -/
noncomputable def carrierModel : AdversaryModel Unit Bool where
  Adv _ := CarrierAdversary
  outcome _ a := MeasureTheory.Measure.dirac (a.claim a.state)
  mass_le_one _ _ := by simp

/-- The model's adversary universe is `1`, which Lean reads from `Adv`. -/
example : (carrierModel.Adv () : Type 1) = CarrierAdversary := rfl

/-- A statement problem whose language is empty. -/
def emptyLanguage : StatementProblem Unit where
  Witness _ _ := PEmpty
  admissible _ _ := True
  rel _ _ _ := False
  rel_admissible _ _ _ h := h.elim

/-- An output problem whose language is all of `Bool`. -/
def anyBool : Problem (⟨fun _ : Unit => Bool⟩ : ClaimFamily Unit) where
  Witness _ _ := Unit
  admissible _ _ := True
  rel _ _ _ := True
  rel_admissible _ _ _ _ := trivial

/-- Soundness at the large model needs no universe annotation. Every outcome's mass is at most
one. Soundness therefore holds with error one. -/
example : soundness carrierModel emptyLanguage anyBool (fun _ => ()) (fun b => some b) 1 := by
  intro _ _ _ a
  exact (MeasureTheory.measure_mono (Set.subset_univ _)).trans (carrierModel.mass_le_one _ a)

/-- The extraction interface of the large model has extractors in `Type 1`, with no annotation. -/
noncomputable def carrierExtraction : ExtractionInterface carrierModel (fun _ => Unit) where
  Ext := CarrierAdversary → Unit
  experiment ext _ a := (MeasureTheory.Measure.dirac (a.claim a.state)).map
    fun b => (b, some (ext a))
  cost _ _ _ := 0

example : (carrierExtraction.Ext : Type 1) = (CarrierAdversary → Unit) := rfl

end LargeAdversary

/-! ### A monad with a larger result universe -/

section LargeMonad

/-- `Except Type` is a monad `Type → Type 1`. Draw splitting runs in it with no annotation. -/
example {P : PFunctor.{1, 0}} (l : PFunctor.Lens P rolePoly0)
    (s₁ : FreeM P Unit) (s₂ : Path s₁ → FreeM P Unit)
    (draw₁ : (c : ChallengeNode l s₁) → Except Type (challengeSpec l s₁ c))
    (draw₂ : (p : Path s₁) → (c : ChallengeNode l (s₂ p)) →
      Except Type (challengeSpec l (s₂ p) c)) :
    prefixDraw l s₁ s₂ (combineDraw l s₁ s₂ draw₁ draw₂) = draw₁ :=
  prefixDraw_combineDraw l s₁ s₂ draw₁ draw₂

/-- Soundness of a plain run interpreted in a monad `Type → Type 1` with no annotation. -/
example {m : Type → Type 1} [Monad m] [EvalDistSemantics m] {ι S : Type}
    {ambient : OracleSpec ι} {s : Protocol} {T : Path s → Type} (V : Verifier ambient s S T)
    (run : {α : Type} → OracleComp (ambient + challengeSpec plainSig s) α → m α)
    (input : StatementProblem S) (output : PathProblem s T) (ε : ℝ≥0∞) : Prop :=
  V.soundnessUsing run input output ε

end LargeMonad

/-! ### Oracle bundles at `Type` -/

/-- An ambient oracle that a prover can query. -/
abbrev smallAmbient : OracleSpec Unit := Unit →ₒ Bool

/-- A natural number answers the unit query with itself. -/
@[reducible]
def natInterface : OracleInterface Nat where
  Query := Unit
  spec := Unit →ₒ Nat
  answer m _ := m

/-- The natural-number input oracle at each Boolean index. -/
abbrev bigInputSlot (_ : Bool) : OracleBundle := OracleBundle.of Nat natInterface

/-- Input oracles indexed by Boolean values with natural-number data. -/
@[instance_reducible]
def bigInputs : OracleBundle := OracleBundle.indexed bigInputSlot

/-- The oracle protocol with no rounds. -/
abbrev oracleDone : OracleProtocol := .pure ⟨⟩

/-- Routing through an oracle map agrees with materialized data. -/
theorem reindex_simulate_eq (x : Bool → Nat) {α : Type}
    (program : OracleComp (OracleBundle.indexed (bigInputSlot ∘ fun X : Bool => X)).spec α) :
    simulateQ (bigInputs.answer x)
        (simulateQ (OracleMap.reindex bigInputSlot (fun X : Bool => X)).impl program) =
      simulateQ ((OracleBundle.indexed (bigInputSlot ∘ fun X : Bool => X)).answer
        ((OracleMap.reindex bigInputSlot (fun X : Bool => X)).f x)) program :=
  OracleMap.simulate_eq (OracleMap.reindex bigInputSlot (fun X : Bool => X)) x program

/-! ### An oracle run at `Type` -/

/-- One natural-number output oracle with a unit index. -/
@[instance_reducible]
def smallOutputs : OracleBundle :=
  OracleBundle.ofIndexed (fun _ : Unit => Nat) fun _ => natInterface

/-- An oracle verifier with all indices, data and statements in `Type`. -/
def runnable : OracleVerifier smallAmbient oracleDone Unit (fun _ => Nat) bigInputs
    (fun _ => smallOutputs) where
  decide _ p _ := by
    cases p
    exact liftM ((smallAmbient + (pathBundle bigInputs oracleDone ⟨⟩).spec).query
      (.inr (.inl ⟨true, ()⟩)))
  outputMap _ _ _ := (OracleMap.reindex bigInputSlot (fun _ : Unit => true)).comp
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
def typeQueryInputs : OracleBundle :=
  OracleBundle.ofIndexed (fun _ : Unit => Nat) fun _ => natInterface

/-- One oracle with Boolean queries, distinct from the input's unit queries. -/
@[instance_reducible]
def bigQueryOracles : OracleBundle :=
  OracleBundle.ofIndexed (fun _ : Unit => Nat) fun _ => bigTypeQueries

/-- The output oracle answers each query by asking the input oracle at `()`. -/
def forwardQueries (p : Path oracleDone) :
    OracleMap (pathBundle typeQueryInputs oracleDone p) bigQueryOracles where
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
      (fun out => (out.1, bigQueryOracles.answer out.2 ⟨(), true⟩)) =
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

/-- The composite output map ignores the intermediate statement. Any certificate holds. -/
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

end Interaction.UniversePolicyTests

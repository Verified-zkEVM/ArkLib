/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Interaction.Oracle.Reassociation
public import VCVio.OracleComp.EvalDist

/-!
# Finite heterogeneous stage composition

A finite chain of passive oracle verifiers composes into one passive oracle verifier through
right-associated `OracleVerifier.append`: the first stage is appended to the composed rest.
The first stage has a fixed protocol. The path of the stages before a later stage selects it.
That path records the prover's public messages and nothing else, so only those messages directly
select a later stage. Challenges, oracle messages and earlier verdicts do not select it directly.
A prover can choose its messages after seeing a challenge, so a challenge can still affect the
choice of a later stage through the prover. The statement types and oracle bundles at the stage
boundaries may all differ, and may depend on the same paths.

The structural restrictions on a stage are these: every bundle query happens in the final
decision, and each challenge comes from a draw program indexed by the challenge node,
`(c : ChallengeNode oracleSig s) → OracleComp ambient _`. A draw program reads neither the input
oracles nor the oracle messages. The types do not make the challenges public-coin. A draw runs in
`OracleComp ambient`, the interface the prover also uses, so under a stateful interpretation of
`ambient` a draw can return a value that the prover wrote. A client that needs public-coin
challenges, for example uniformly random verifier messages, states that as a separate condition on
the draws and on the interpretation of `ambient`.

The composed execution runs the interactions of all stages, then folds the decisions. Each
stage's decision receives the statement that the previous decision accepted, and a rejection makes
the composite reject. A rejecting decision does not skip any interaction. `StageChain.run` is the
core run `OracleVerifier.run` of the composed verifier, with the challenge queries answered by the
stages' draws. `StageChain.run_cons` states that it is the run of the binary append of the first
stage and the composed rest. `OracleVerifier.run_append` splits that run into the two interactions
and the two decisions.
`StageChain.then` concatenates two chains. `StageChain.decideOn_then` and
`StageChain.outputOn_then` split a chain at any stage: on every run, the composed verifier of a
concatenation decides and exports output data as the append of the composed verifiers of its two
parts.

A chain is given in two parts. `StageChain` is the plan: the protocols, verifiers and draws of the
stages. `StageChain.Compatibility` is the evidence: at every boundary, an
`OracleVerifier.OutputCompatibility` certificate between the stage's verifier and the composed
verifier of the stages after it. `StageChain.verifier` builds the composed verifier from both, by
recursion on the plan. The certificates are general, so output maps may read the input statement.
`OutputCompatibility.ofStatement` gives a certificate from a function of the input statement, the
composed path and the view that every accepted intermediate statement equals.
`StageChain.StatementFree` is the special case in which no output map reads its input statement.
`StageChain.compose` computes the evidence from the plan instead of storing it in the plan's
constructors. The inductive type then does not refer to the verifier computed from it.

Every oracle bundle of a chain has its queries, responses and data in `Type`.

The invariant laws `StageChain.decideWith_accepts_of_deterministic`,
`StageChain.decideWith_accepts_of_onSupport` and `StageChain.decideWith_accepts_of_almostSurely`
derive a property of the composed decision from one hypothesis per stage boundary. They concern
the fold of the decisions after all interactions. The almost-sure law reads probabilities from the
`OracleSpec.AnswerMeasure` instance on `ambient`, which is a chosen measure on the ambient answers.
-/

@[expose] public section

namespace Interaction
open PFunctor FreeM TwoParty.Lens OracleComp Oracle

namespace OracleVerifier

section Adapters

variable {ι : Type} {ambient : OracleSpec ι} {s : OracleProtocol.{0, 0}} {S : Type}
  {T : Path s → Type} {inputs inputs' : OracleBundle}
  {outputs : Path s → OracleBundle}
  {outputs' : Path s → OracleBundle}

/-- Read the inputs through an oracle map from other inputs. The decision routes its input queries
through the map, and the output map reads the mapped input data. -/
def comapInputs (V : OracleVerifier ambient s S T inputs outputs)
    (r : OracleMap inputs' inputs) :
    OracleVerifier ambient s S T inputs' outputs where
  decide stmt p v := OptionT.mk
    (simulateQ ((r.par (OracleMap.id _)).withAmbient ambient) (V.decide stmt p v).run)
  outputMap stmt p v := (V.outputMap stmt p v).comp (r.par (OracleMap.id _))

/-- Export the outputs through an oracle map at every path. The decision is unchanged. -/
def mapOutputs (V : OracleVerifier ambient s S T inputs outputs)
    (r : (p : Path s) → OracleMap (outputs p) (outputs' p)) :
    OracleVerifier ambient s S T inputs outputs' where
  decide := V.decide
  outputMap stmt p v := (r p).comp (V.outputMap stmt p v)

/-- Reading the inputs through an oracle map decides as the original verifier on the mapped data.
-/
theorem comapInputs_decideWith (V : OracleVerifier ambient s S T inputs outputs)
    (r : OracleMap inputs' inputs) (stmt : S)
    (p : Path s) (v : View s p) (data : (pathBundle inputs' s p).Data) :
    (V.comapInputs r).decideWith stmt p v data = V.decideWith stmt p v (r.f data.1, data.2) :=
  OracleMap.simulate_withAmbient (r.par (OracleMap.id _)) data _

/-- Reading the inputs through an oracle map exports the original output data of the mapped data.
-/
theorem comapInputs_outputData (V : OracleVerifier ambient s S T inputs outputs)
    (r : OracleMap inputs' inputs) (stmt : S)
    (p : Path s) (v : View s p) (data : (pathBundle inputs' s p).Data) :
    ((V.comapInputs r).outputMap stmt p v).f data =
      (V.outputMap stmt p v).f (r.f data.1, data.2) := rfl

/-- Exporting the outputs through oracle maps keeps the decision. -/
theorem mapOutputs_decideWith (V : OracleVerifier ambient s S T inputs outputs)
    (r : (p : Path s) → OracleMap (outputs p) (outputs' p)) :
    (V.mapOutputs r).decideWith = V.decideWith := rfl

/-- Exporting the outputs through oracle maps applies them to the original output data. -/
theorem mapOutputs_outputData (V : OracleVerifier ambient s S T inputs outputs)
    (r : (p : Path s) → OracleMap (outputs p) (outputs' p)) (stmt : S) (p : Path s) (v : View s p)
    (data : (pathBundle inputs s p).Data) :
    ((V.mapOutputs r).outputMap stmt p v).f data = (r p).f ((V.outputMap stmt p v).f data) :=
  rfl

end Adapters

/-- Reading the inputs through an oracle map runs as the original verifier on the mapped input
data. The equality holds after the decision's bundle queries are answered from the supplied data.
It does not count the source queries that the map issues for each routed query; a bound on those
is a separate statement. -/
theorem comapInputs_run {ι : Type} {ambient : OracleSpec ι} {s : OracleProtocol.{0, 0}}
    {S : Type} {T : Path s → Type} {inputs inputs' : OracleBundle}
    {outputs : Path s → OracleBundle}
    {Out : Transcript oracleSig s → Type}
    (V : OracleVerifier ambient s S T inputs outputs)
    (r : OracleMap inputs' inputs) (stmt : S)
    (data : inputs'.Data) (prover : Prover oracleSig ambient s Out) :
    (V.comapInputs r).run stmt data prover = V.run stmt (r.f data) prover := by
  rw [OracleVerifier.run_eq, OracleVerifier.run_eq]
  refine _root_.bind_congr fun z => ?_
  obtain ⟨tr, out, _⟩ := z
  change (simulateQ _ (OptionT.mk (simulateQ ((r.par (OracleMap.id _)).withAmbient ambient)
    (V.decide stmt _ _).run)).run >>= _) = _
  rw [OptionT.run_mk, OracleMap.simulate_withAmbient_addLift]
  rfl

variable {ι : Type} {ambient : OracleSpec ι}
  {inputs : OracleBundle}
  {s₁ : OracleProtocol.{0, 0}} {s₂ : Path s₁ → OracleProtocol.{0, 0}} {S : Type}
  {T : Path s₁ → Type} {U : (p : Path s₁) → Path (s₂ p) → Type}
  {middle : Path s₁ → OracleBundle}
  {outputs : (p₁ : Path s₁) → Path (s₂ p₁) → OracleBundle}

/-- The output map of an appended verifier whose component output maps do not read their input
statements. The prefix map routes the inputs, and the suffix map reads the routed inputs and the
suffix messages. -/
def appendOutputMap
    (map₁ : (p : Path s₁) → View s₁ p →
      OracleMap (pathBundle inputs s₁ p) (middle p))
    (map₂ : (p₁ : Path s₁) → (p₂ : Path (s₂ p₁)) → View (s₂ p₁) p₂ →
      OracleMap (pathBundle (middle p₁) (s₂ p₁) p₂) (outputs p₁ p₂))
    (p : Path (s₁.append s₂)) (v : View (s₁.append s₂) p) :
    OracleMap (pathBundle inputs (s₁.append s₂) p) (splitOutputs outputs p) :=
  (map₂ (Path.split s₁ s₂ p).1 (Path.split s₁ s₂ p).2 (View.split s₁ s₂ p v).2).comp
    (((map₁ (Path.split s₁ s₂ p).1 (View.split s₁ s₂ p v).1).par
      (OracleMap.id (OracleBundle.ofFamily (oracleMessageFamily _ (Path.split s₁ s₂ p).2)))).comp
      (splitPathBundle (inputs := inputs) p))

/-- Compatibility when neither output map reads its input statement. The composite output map is
`appendOutputMap`, so it reads neither the input statement nor the intermediate one. -/
def OutputCompatibility.ofStatementFree (V₁ : OracleVerifier ambient s₁ S T inputs middle)
    (V₂ : (p : Path s₁) → OracleVerifier ambient (s₂ p) (T p) (U p) (middle p) (outputs p))
    (map₁ : (p : Path s₁) → View s₁ p →
      OracleMap (pathBundle inputs s₁ p) (middle p))
    (h₁ : ∀ stmt, V₁.outputMap stmt = map₁)
    (map₂ : (p₁ : Path s₁) → (p₂ : Path (s₂ p₁)) → View (s₂ p₁) p₂ →
      OracleMap (pathBundle (middle p₁) (s₂ p₁) p₂) (outputs p₁ p₂))
    (h₂ : ∀ p₁ mid, (V₂ p₁).outputMap mid = map₂ p₁) :
    OutputCompatibility V₁ V₂ where
  outputMap _ := appendOutputMap map₁ map₂
  agrees stmt p v data mid _ := by
    simp only [appendOutputMap, suffixRoute, h₁, h₂]
    rfl

section DecisionLaws

variable (V₁ : OracleVerifier ambient s₁ S T inputs middle)
  (V₂ : (p : Path s₁) → OracleVerifier ambient (s₂ p) (T p) (U p) (middle p) (outputs p))
  (compatible : OutputCompatibility V₁ V₂) (stmt : S) (p : Path (s₁.append s₂))
  (v : View (s₁.append s₂) p) (data : (pathBundle inputs (s₁.append s₂) p).Data)

/-- A rejecting prefix decision makes the appended decision reject. Both interactions have run
before either decision; only the suffix decision is skipped. -/
theorem append_decideWith_of_reject
    (h : V₁.decideWith stmt (Path.split s₁ s₂ p).1 (View.split s₁ s₂ p v).1
      ((prefixRoute (inputs := inputs) p).f data) = pure none) :
    (V₁.append V₂ compatible).decideWith stmt p v data = pure none := by
  rw [append_decideWith, h, LawfulMonad.pure_bind]

/-- A deterministic acceptance propagates: if the prefix decision accepts `mid` and the suffix
decision accepts `out` from `mid`, the appended decision accepts `out`. -/
theorem append_decideWith_of_accept (mid : T (Path.split s₁ s₂ p).1)
    (out : U (Path.split s₁ s₂ p).1 (Path.split s₁ s₂ p).2)
    (h : V₁.decideWith stmt (Path.split s₁ s₂ p).1 (View.split s₁ s₂ p v).1
      ((prefixRoute (inputs := inputs) p).f data) = pure (some mid))
    (hrest : (V₂ (Path.split s₁ s₂ p).1).decideWith mid (Path.split s₁ s₂ p).2
      (View.split s₁ s₂ p v).2 ((suffixRoute V₁ stmt p v).f data) = pure (some out)) :
    (V₁.append V₂ compatible).decideWith stmt p v data = pure (some out) := by
  rw [append_decideWith, h, LawfulMonad.pure_bind]
  exact hrest

/-- An invariant propagates over the support. Suppose every possible prefix result is an accepted
statement satisfying `Mid`, and every possible suffix result from such a statement is an accepted
statement satisfying `Post`. Then so is every possible result of the appended decision. -/
theorem append_decideWith_accepts_of_onSupport (Mid : T (Path.split s₁ s₂ p).1 → Prop)
    (Post : U (Path.split s₁ s₂ p).1 (Path.split s₁ s₂ p).2 → Prop)
    (h : ∀ r ∈ support (V₁.decideWith stmt (Path.split s₁ s₂ p).1 (View.split s₁ s₂ p v).1
      ((prefixRoute (inputs := inputs) p).f data)), ∃ mid, r = some mid ∧ Mid mid)
    (hrest : ∀ mid, Mid mid →
      ∀ r ∈ support ((V₂ (Path.split s₁ s₂ p).1).decideWith mid (Path.split s₁ s₂ p).2
        (View.split s₁ s₂ p v).2 ((suffixRoute V₁ stmt p v).f data)),
        ∃ out, r = some out ∧ Post out) :
    ∀ r ∈ support ((V₁.append V₂ compatible).decideWith stmt p v data),
      ∃ out, r = some out ∧ Post out := by
  intro r hr
  rw [append_decideWith] at hr
  simp only [mem_support_bind_iff] at hr
  obtain ⟨first, hfirst, hr⟩ := hr
  obtain ⟨mid, rfl, hmid⟩ := h first hfirst
  exact hrest mid hmid r hr

/-- An invariant propagates almost surely. The prefix decision accepts with `Mid` almost surely.
From every statement satisfying `Mid`, the suffix decision accepts with `Post` almost surely.
Then the appended decision accepts with `Post` almost surely. The ambient oracles carry an answer
measure, and both statement spaces are measurable and discrete. -/
theorem append_decideWith_accepts_of_almostSurely [ambient.AnswerMeasure]
    [MeasurableSpace (T (Path.split s₁ s₂ p).1)]
    [DiscreteMeasurableSpace (T (Path.split s₁ s₂ p).1)]
    [MeasurableSpace (U (Path.split s₁ s₂ p).1 (Path.split s₁ s₂ p).2)]
    [DiscreteMeasurableSpace (U (Path.split s₁ s₂ p).1 (Path.split s₁ s₂ p).2)]
    (Mid : T (Path.split s₁ s₂ p).1 → Prop)
    (Post : U (Path.split s₁ s₂ p).1 (Path.split s₁ s₂ p).2 → Prop)
    (h : 𝒟[V₁.decideWith stmt (Path.split s₁ s₂ p).1 (View.split s₁ s₂ p v).1
      ((prefixRoute (inputs := inputs) p).f data)] {r | ∃ mid, r = some mid ∧ Mid mid} = 1)
    (hrest : ∀ mid, Mid mid →
      𝒟[(V₂ (Path.split s₁ s₂ p).1).decideWith mid (Path.split s₁ s₂ p).2
        (View.split s₁ s₂ p v).2 ((suffixRoute V₁ stmt p v).f data)]
        {r | ∃ out, r = some out ∧ Post out} = 1) :
    𝒟[(V₁.append V₂ compatible).decideWith stmt p v data]
      {r | ∃ out, r = some out ∧ Post out} = 1 := by
  rw [append_decideWith]
  refine OracleComp.evalDist_bind_apply_eq_one_of_ae _ _ MeasurableSet.of_discrete ?_
  filter_upwards [(MeasureTheory.ae_iff_prob_eq_one Measurable.of_discrete).mpr h] with r hr
  obtain ⟨mid, rfl, hmid⟩ := hr
  exact hrest mid hmid

end DecisionLaws

end OracleVerifier

/-! ## Chains of stages -/

/-- The plan of a finite chain of passive oracle verifiers from the input statement type `S` and
the input oracle bundle `inputs`.

`nil` is the empty chain. `cons s V draw rest` runs the protocol `s`, whose challenges are answered
by `draw`, and then, at each path `p` of `s`, the chain `rest p`. The verifier `V` accepts a
statement of type `T p` with the oracle bundle `middle p`, which are the inputs of `rest p`.
The draw is any program over `ambient` indexed by the challenge node. Public-coin sampling is not
part of this type; a client that needs it states it separately.
Statement types lie in `Type`, and every oracle bundle of
the chain has its queries in `Type`. `StageChain.Compatibility` gives the evidence that
composes the verifiers. -/
inductive StageChain {ι : Type} (ambient : OracleSpec ι) :
    (S : Type) → OracleBundle → Type 1 where
  /-- No stages. -/
  | nil {S : Type} (inputs : OracleBundle) :
      StageChain ambient S inputs
  /-- A first stage, then the remaining stages selected by its path. -/
  | cons {S : Type} {inputs : OracleBundle}
      (s : OracleProtocol.{0, 0}) {T : Path s → Type} {middle : Path s → OracleBundle}
      (verifier : OracleVerifier ambient s S T inputs middle)
      (draw : (c : ChallengeNode oracleSig s) → OracleComp ambient (challengeSpec oracleSig s c))
      (rest : (p : Path s) → StageChain ambient (T p) (middle p)) :
      StageChain ambient S inputs

namespace StageChain

variable {ι : Type} {ambient : OracleSpec ι}

/-- The composed protocol: the first stage's protocol, followed at each of its paths by the
composed protocol of the remaining stages. -/
def protocol {S : Type} {inputs : OracleBundle} :
    StageChain ambient S inputs → OracleProtocol.{0, 0}
  | .nil _ => .pure ⟨⟩
  | .cons s _ _ rest => s.append fun p => (rest p).protocol

/-- The composed output statement type at a path. It is the input statement type for no stages,
and otherwise the output of the remaining stages at the split path. -/
def Out {S : Type} {inputs : OracleBundle} :
    (c : StageChain ambient S inputs) → Path c.protocol → Type
  | .nil _, _ => S
  | .cons _ _ _ rest, p =>
    splitFamily (s₂ := fun p => (rest p).protocol) (fun p₁ => (rest p₁).Out) p

/-- The composed output oracle bundle at a path. It is the inputs for no stages, and otherwise the
output bundle of the remaining stages at the split path. -/
def outputs {S : Type} {inputs : OracleBundle} :
    (c : StageChain ambient S inputs) → Path c.protocol → OracleBundle
  | .nil inputs, _ => inputs
  | .cons s _ _ rest, p =>
    (rest (Path.split s (fun p => (rest p).protocol) p).1).outputs
      (Path.split s (fun p => (rest p).protocol) p).2

/-- The verifier of no stages: it accepts the input statement and exports the inputs. -/
def nilVerifier {S : Type} (inputs : OracleBundle) :
    OracleVerifier ambient (nil (ambient := ambient) (S := S) inputs).protocol S
      (nil (ambient := ambient) (S := S) inputs).Out inputs
      (nil (ambient := ambient) (S := S) inputs).outputs where
  decide stmt _ _ := pure stmt
  outputMap _ _ _ := OracleMap.fst _ _

/-- The evidence type of a chain together with the composed verifier it determines. For no stages
there is no evidence. For a first stage, the evidence has two parts: evidence for the remaining
stages at each path, and a compatibility certificate between the first stage's verifier and the
composed verifiers of the rest. The composed verifier is their binary append. -/
def compose {S : Type} {inputs : OracleBundle} :
    (c : StageChain ambient S inputs) →
      (E : Type 1) × (E → OracleVerifier ambient c.protocol S c.Out inputs c.outputs)
  | .nil inputs => ⟨PUnit, fun _ => nilVerifier inputs⟩
  | .cons _ V _ rest =>
    ⟨(e : ∀ p, (rest p).compose.1) ×
        OracleVerifier.OutputCompatibility V fun p => (rest p).compose.2 (e p),
      fun e => V.append (s₂ := fun p => (rest p).protocol)
        (fun p => (rest p).compose.2 (e.1 p)) e.2⟩

/-- The evidence that composes a chain: an output compatibility certificate at every stage
boundary. -/
abbrev Compatibility {S : Type} {inputs : OracleBundle} (c : StageChain ambient S inputs) :
    Type 1 :=
  c.compose.1

/-- The composed passive oracle verifier of a chain with its compatibility evidence. -/
def verifier {S : Type} {inputs : OracleBundle}
    (c : StageChain ambient S inputs) (e : c.Compatibility) :
    OracleVerifier ambient c.protocol S c.Out inputs c.outputs :=
  c.compose.2 e

/-- The composed challenge implementation, which combines the stages' draws along the path of the
earlier stages. -/
def draw {S : Type} {inputs : OracleBundle} :
    (c : StageChain ambient S inputs) → (ch : ChallengeNode oracleSig c.protocol) →
      OracleComp ambient (challengeSpec oracleSig c.protocol ch)
  | .nil _, ch => ch.val.elim
  | .cons s _ draw₁ rest, ch =>
    combineDraw oracleSig s (fun p => (rest p).protocol) draw₁ (fun p => (rest p).draw) ch

/-- The composed challenge queries answered by the stages' draws; shared queries stay shared. -/
def challengeImpl {S : Type} {inputs : OracleBundle}
    (c : StageChain ambient S inputs) :
    QueryImpl (ambient + challengeSpec oracleSig c.protocol) (OracleComp ambient) :=
  QueryImpl.id' ambient + c.draw

/-- Run every stage's interaction against a prover of the composed protocol, then fold the
decisions. The verdict is the composed accepted statement with the composed output data, or
`none` if a decision rejects. -/
def run {S : Type} {inputs : OracleBundle}
    (c : StageChain ambient S inputs) (e : c.Compatibility) (stmt : S) (data : inputs.Data)
    {Out : Transcript oracleSig c.protocol → Type}
    (prover : Prover oracleSig ambient c.protocol Out) :
    OracleComp ambient
      (Outcome oracleSig c.protocol Out (OracleVerifier.Output c.Out c.outputs)) :=
  simulateQ c.challengeImpl ((c.verifier e).run stmt data prover)

/-! ## Statement-free output maps -/

/-- Output maps that do not read the input statement, for every stage of a chain. At a first
stage, this is a map with the equation that the stage's output map is that map at every
statement, together with such maps for the remaining stages at each path. -/
def StatementFree {S : Type} {inputs : OracleBundle} : StageChain ambient S inputs → Type
  | .nil _ => PUnit
  | @StageChain.cons _ _ _ inputs s _ middle V _ rest =>
    (map : (p : Path s) → View s p →
        OracleMap (pathBundle inputs s p) (middle p)) ×'
      (∀ stmt, V.outputMap stmt = map) ×' ∀ p, (rest p).StatementFree

/-- The composed output map of statement-free stage maps. For no stages it forwards the inputs;
otherwise it is `appendOutputMap` of the first stage's map and the composed map of the rest. -/
def StatementFree.map {S : Type} {inputs : OracleBundle} :
    (c : StageChain ambient S inputs) → c.StatementFree → (p : Path c.protocol) →
      View c.protocol p →
        OracleMap (pathBundle inputs c.protocol p) (c.outputs p)
  | .nil _, _, _, _ => OracleMap.fst _ _
  | .cons _ _ _ rest, m, p, v =>
    OracleVerifier.appendOutputMap (s₂ := fun p => (rest p).protocol) m.1
      (fun p₁ => StatementFree.map (rest p₁) (m.2.2 p₁)) p v

/-- The compatibility evidence of statement-free stage maps, with the equation that the composed
verifier's output map is `StatementFree.map` at every statement. -/
def StatementFree.certify {S : Type} {inputs : OracleBundle} :
    (c : StageChain ambient S inputs) → (m : c.StatementFree) →
      {e : c.Compatibility // ∀ stmt, (c.verifier e).outputMap stmt = StatementFree.map c m}
  | .nil _, _ => ⟨⟨⟩, fun _ => rfl⟩
  | .cons _ V _ rest, m =>
    ⟨⟨fun p => (certify (rest p) (m.2.2 p)).1,
      OracleVerifier.OutputCompatibility.ofStatementFree V _ m.1 m.2.1
        (fun p => StatementFree.map (rest p) (m.2.2 p))
        fun p => (certify (rest p) (m.2.2 p)).2⟩, fun _ => rfl⟩

/-- The compatibility evidence of statement-free stage maps. -/
abbrev StatementFree.compatibility {S : Type} {inputs : OracleBundle}
    {c : StageChain ambient S inputs} (m : c.StatementFree) :
    c.Compatibility :=
  (StatementFree.certify c m).1

/-- With statement-free stage maps, the composed output map does not read the input statement. -/
theorem StatementFree.outputMap_eq {S : Type} {inputs : OracleBundle}
    {c : StageChain ambient S inputs} (m : c.StatementFree)
    (stmt : S) : (c.verifier m.compatibility).outputMap stmt = StatementFree.map c m :=
  (StatementFree.certify c m).2 stmt

section Laws

variable {S : Type} {inputs : OracleBundle}
  (s : OracleProtocol.{0, 0}) {T : Path s → Type} {middle : Path s → OracleBundle}
  (V : OracleVerifier ambient s S T inputs middle)
  (draw₁ : (c : ChallengeNode oracleSig s) → OracleComp ambient (challengeSpec oracleSig s c))
  (rest : (p : Path s) → StageChain ambient (T p) (middle p))
  (e : (p : Path s) → (rest p).Compatibility)
  (compatible : OracleVerifier.OutputCompatibility V fun p => (rest p).verifier (e p))

/-- The composed protocol of a chain with a first stage. -/
@[simp] theorem protocol_cons :
    (cons s V draw₁ rest).protocol = s.append fun p => (rest p).protocol := rfl

/-- The composed verifier of a chain with a first stage is a binary append. It appends that
stage's verifier and the composed verifiers of the rest, with the certificate of the evidence. -/
theorem verifier_cons :
    (cons s V draw₁ rest).verifier ⟨e, compatible⟩ =
      V.append (fun p => (rest p).verifier (e p)) compatible := rfl

/-- The composed draws of a chain with a first stage combine that stage's draws with the composed
draws of the rest. -/
theorem draw_cons :
    (cons s V draw₁ rest).draw =
      combineDraw oracleSig s (fun p => (rest p).protocol) draw₁ fun p => (rest p).draw := rfl

/-- The run of a chain with a first stage is the core run of a binary append. It appends that
stage's verifier and the composed rest, and the combined draws answer the challenges.
`OracleVerifier.run_append` splits it into the first stage's interaction, the rest's interaction,
the first decision and, after its acceptance only, the rest's decision. This is the split after
the first stage, not a split at an arbitrary stage. -/
theorem run_cons (stmt : S) (data : inputs.Data)
    {Out : Transcript oracleSig (s.append fun p => (rest p).protocol) → Type}
    (prover : Prover oracleSig ambient (s.append fun p => (rest p).protocol) Out) :
    (cons s V draw₁ rest).run ⟨e, compatible⟩ stmt data prover =
      simulateQ (QueryImpl.id' ambient +
          combineDraw oracleSig s (fun p => (rest p).protocol) draw₁ fun p => (rest p).draw)
        ((V.append (fun p => (rest p).verifier (e p)) compatible).run stmt data prover) := rfl

/-- A rejecting first decision makes the composed decision reject. The interactions of the
remaining stages have already run; only their decisions are skipped. -/
theorem decideWith_cons_of_reject (stmt : S) (p : Path (s.append fun p => (rest p).protocol))
    (v : View _ p) (data : (pathBundle inputs (s.append fun p => (rest p).protocol) p).Data)
    (h : V.decideWith stmt (Path.split s _ p).1 (View.split s _ p v).1
      ((OracleVerifier.prefixRoute (inputs := inputs) p).f data) = pure none) :
    ((cons s V draw₁ rest).verifier ⟨e, compatible⟩).decideWith stmt p v data = pure none :=
  OracleVerifier.append_decideWith_of_reject V _ compatible stmt p v data h

end Laws

/-- With no stages, the composed decision accepts the input statement. -/
@[simp] theorem decideWith_nil {S : Type} (inputs : OracleBundle)
    (e : (nil (ambient := ambient) (S := S) inputs).Compatibility) (stmt : S)
    (p : Path (nil (ambient := ambient) (S := S) inputs).protocol) (v : View _ p)
    (data : (pathBundle inputs (nil (ambient := ambient) (S := S) inputs).protocol p).Data) :
    ((nil (ambient := ambient) (S := S) inputs).verifier e).decideWith stmt p v data =
      pure (some stmt) := by
  simp only [OracleVerifier.decideWith, verifier, compose, nilVerifier]
  exact simulateQ_pure _ _

/-- With no stages, the composed output data is the input data. -/
@[simp] theorem outputData_nil {S : Type} (inputs : OracleBundle)
    (e : (nil (ambient := ambient) (S := S) inputs).Compatibility) (stmt : S)
    (p : Path (nil (ambient := ambient) (S := S) inputs).protocol) (v : View _ p)
    (data : (pathBundle inputs (nil (ambient := ambient) (S := S) inputs).protocol p).Data) :
    (((nil (ambient := ambient) (S := S) inputs).verifier e).outputMap stmt p v).f data =
      data.1 := rfl

/-- A chain of one stage decides as that stage: its composed decision is the stage's decision at
the split path, on the data that `prefixRoute` selects. -/
theorem decideWith_one {S : Type} {inputs : OracleBundle}
    (s : OracleProtocol.{0, 0}) {T : Path s → Type} {middle : Path s → OracleBundle}
    (V : OracleVerifier ambient s S T inputs middle)
    (draw₁ : (c : ChallengeNode oracleSig s) → OracleComp ambient (challengeSpec oracleSig s c))
    (e : (p : Path s) → (nil (ambient := ambient) (S := T p) (middle p)).Compatibility)
    (compatible : OracleVerifier.OutputCompatibility V fun p =>
      (nil (ambient := ambient) (S := T p) (middle p)).verifier (e p))
    (stmt : S)
    (p : Path (s.append fun p => (nil (ambient := ambient) (S := T p) (middle p)).protocol))
    (v : View _ p) (data : (pathBundle inputs
      (s.append fun p => (nil (ambient := ambient) (S := T p) (middle p)).protocol) p).Data) :
    ((cons s V draw₁ fun p => nil (middle p)).verifier ⟨e, compatible⟩).decideWith stmt p v data =
      V.decideWith stmt (Path.split s _ p).1 (View.split s _ p v).1
        ((OracleVerifier.prefixRoute (inputs := inputs) p).f data) := by
  refine (OracleVerifier.append_decideWith V _ compatible stmt p v data).trans ?_
  refine (_root_.bind_congr fun r => ?_).trans (_root_.bind_pure _)
  cases r with
  | none => rfl
  | some mid => exact decideWith_nil _ _ _ _ _ _

/-! ## Invariants over a chain -/

/-- A property at every stage boundary of a chain. `P` gives it on the boundary statement type,
indexed by the paths of the stages up to that boundary. For a first stage, it is the property at
that stage's output at each of its paths, together with the properties of the remaining stages
there. The boundary before the first stage is not included. -/
def Boundaries (P : Type → Type) {S : Type} {inputs : OracleBundle} :
    StageChain ambient S inputs → Type
  | .nil _ => PUnit
  | @StageChain.cons _ _ _ _ s T _ _ _ rest =>
    ((p : Path s) → P (T p)) × ((p : Path s) → (rest p).Boundaries P)

/-- The property at the final boundary of a chain at a composed path. It is the entry property
for no stages, and otherwise the final property of the remaining stages at the split path. -/
def Boundaries.final {P : Type → Type} {S : Type} {inputs : OracleBundle} :
    (c : StageChain ambient S inputs) → P S → c.Boundaries P → (p : Path c.protocol) → P (c.Out p)
  | .nil _, pre, _, _ => pre
  | .cons s _ _ rest, _, b, p =>
    final (rest (Path.split s (fun p => (rest p).protocol) p).1)
      (b.1 (Path.split s (fun p => (rest p).protocol) p).1)
      (b.2 (Path.split s (fun p => (rest p).protocol) p).1)
      (Path.split s (fun p => (rest p).protocol) p).2

/-- Every stage decision deterministically accepts a statement satisfying the predicate after it.
This holds from every input statement satisfying the predicate before it, at every path, view and
bundle data. -/
def AcceptsDeterministically {S : Type} {inputs : OracleBundle} :
    (c : StageChain ambient S inputs) → (S → Prop) → c.Boundaries (· → Prop) → Prop
  | .nil _, _, _ => True
  | .cons _ V _ rest, pre, b =>
    (∀ stmt, pre stmt → ∀ p v data,
      ∃ mid, V.decideWith stmt p v data = pure (some mid) ∧ b.1 p mid) ∧
    ∀ p, (rest p).AcceptsDeterministically (b.1 p) (b.2 p)

/-- Every possible result of every stage decision is an accepted statement satisfying the
predicate after it. This holds from every input statement satisfying the predicate before it, at
every path, view and bundle data. -/
def AcceptsOnSupport {S : Type} {inputs : OracleBundle} :
    (c : StageChain ambient S inputs) → (S → Prop) → c.Boundaries (· → Prop) → Prop
  | .nil _, _, _ => True
  | .cons _ V _ rest, pre, b =>
    (∀ stmt, pre stmt → ∀ p v data, ∀ r ∈ support (V.decideWith stmt p v data),
      ∃ mid, r = some mid ∧ b.1 p mid) ∧
    ∀ p, (rest p).AcceptsOnSupport (b.1 p) (b.2 p)

/-- The deterministic chain law. Suppose every stage decision deterministically accepts a
statement satisfying its boundary predicate. The composed decision folds the stage decisions after
all interactions. It then deterministically accepts a statement satisfying the final predicate. -/
theorem decideWith_accepts_of_deterministic {S : Type} {inputs : OracleBundle} :
    (c : StageChain ambient S inputs) → (e : c.Compatibility) → (pre : S → Prop) →
      (b : c.Boundaries (· → Prop)) → c.AcceptsDeterministically pre b → (stmt : S) → pre stmt →
      (p : Path c.protocol) → (v : View c.protocol p) →
      (data : (pathBundle inputs c.protocol p).Data) →
      ∃ out, (c.verifier e).decideWith stmt p v data = pure (some out) ∧
        Boundaries.final c pre b p out
  | .nil _, e, _, _, _, stmt, hstmt, p, v, data => ⟨stmt, decideWith_nil _ e stmt p v data, hstmt⟩
  | .cons s V _ rest, e, _, b, h, stmt, hstmt, p, v, data => by
    obtain ⟨mid, hmid, hpred⟩ := h.1 stmt hstmt (Path.split s _ p).1 (View.split s _ p v).1
      ((OracleVerifier.prefixRoute (inputs := inputs) p).f data)
    obtain ⟨out, hout, hfinal⟩ := decideWith_accepts_of_deterministic (rest (Path.split s _ p).1)
      (e.1 (Path.split s _ p).1) (b.1 (Path.split s _ p).1) (b.2 (Path.split s _ p).1)
      (h.2 (Path.split s _ p).1) mid hpred (Path.split s _ p).2 (View.split s _ p v).2
      ((OracleVerifier.suffixRoute V stmt p v).f data)
    exact ⟨out, OracleVerifier.append_decideWith_of_accept V _ e.2 stmt p v data mid out
      hmid hout, hfinal⟩

/-- The support chain law. Suppose every possible result of every stage decision is an accepted
statement satisfying its boundary predicate. The composed decision is the fold of the stage
decisions after all interactions. Then every possible result of the composed decision is an
accepted statement satisfying the final predicate. -/
theorem decideWith_accepts_of_onSupport {S : Type} {inputs : OracleBundle} :
    (c : StageChain ambient S inputs) → (e : c.Compatibility) → (pre : S → Prop) →
      (b : c.Boundaries (· → Prop)) → c.AcceptsOnSupport pre b → (stmt : S) → pre stmt →
      (p : Path c.protocol) → (v : View c.protocol p) →
      (data : (pathBundle inputs c.protocol p).Data) →
      ∀ r ∈ support ((c.verifier e).decideWith stmt p v data),
        ∃ out, r = some out ∧ Boundaries.final c pre b p out
  | .nil _, e, _, _, _, stmt, hstmt, p, v, data => by
    intro r hr
    rw [decideWith_nil] at hr
    exact ⟨stmt, OracleComp.eq_of_mem_support_pure _ hr, hstmt⟩
  | .cons s V _ rest, e, _, b, h, stmt, hstmt, p, v, data =>
    OracleVerifier.append_decideWith_accepts_of_onSupport V _ e.2 stmt p v data
      (b.1 (Path.split s _ p).1) _
      (h.1 stmt hstmt (Path.split s _ p).1 (View.split s _ p v).1
        ((OracleVerifier.prefixRoute (inputs := inputs) p).f data))
      fun mid hmid => decideWith_accepts_of_onSupport (rest (Path.split s _ p).1)
        (e.1 (Path.split s _ p).1) (b.1 (Path.split s _ p).1) (b.2 (Path.split s _ p).1)
        (h.2 (Path.split s _ p).1) mid hmid (Path.split s _ p).2 (View.split s _ p v).2
        ((OracleVerifier.suffixRoute V stmt p v).f data)

/-- An event on a type with a discrete measurable structure, which the almost-sure chain law
carries at every stage boundary. -/
structure DiscreteEvent (α : Type) where
  /-- The measurable structure. -/
  measurableSpace : MeasurableSpace α
  /-- Every set is measurable. -/
  discrete : @DiscreteMeasurableSpace α measurableSpace
  /-- The event. -/
  holds : α → Prop

/-- Every stage decision accepts a statement in the event after it almost surely. This holds from
every input statement satisfying the predicate before it, at every path, view and bundle data.
Each boundary event carries the measurable structure of its statement type. -/
def AcceptsAlmostSurely [ambient.AnswerMeasure] {S : Type} {inputs : OracleBundle} :
    (c : StageChain ambient S inputs) → (S → Prop) → c.Boundaries DiscreteEvent → Prop
  | .nil _, _, _ => True
  | .cons _ V _ rest, pre, b =>
    (∀ stmt, pre stmt → ∀ p v data,
      letI := (b.1 p).measurableSpace
      𝒟[V.decideWith stmt p v data] {r | ∃ mid, r = some mid ∧ (b.1 p).holds mid} = 1) ∧
    ∀ p, (rest p).AcceptsAlmostSurely (b.1 p).holds (b.2 p)

/-- The almost-sure chain law. Suppose every stage decision accepts a statement in its boundary
event almost surely. Then the composed decision, the fold of the stage decisions after all
interactions, accepts a statement in the final event almost surely. The boundary events carry the
discrete measurable structures, and the entry event `pre` gives the structure of the input
statement type.

Probabilities are taken under the `OracleSpec.AnswerMeasure` instance on `ambient`: each ambient
query is answered independently from the measure that instance chooses for it. The law can hold
when the support law fails, because a rejection can lie in the structural support of a decision
and still have probability zero under the chosen measure. It describes a stateless ambient
interpretation. A persistent runtime with private state needs its own compatibility statement or
invariant relating it to the chosen measure. -/
theorem decideWith_accepts_of_almostSurely [ambient.AnswerMeasure] {S : Type}
    {inputs : OracleBundle} :
    (c : StageChain ambient S inputs) → (e : c.Compatibility) → (pre : DiscreteEvent S) →
      (b : c.Boundaries DiscreteEvent) → c.AcceptsAlmostSurely pre.holds b → (stmt : S) →
      pre.holds stmt → (p : Path c.protocol) → (v : View c.protocol p) →
      (data : (pathBundle inputs c.protocol p).Data) →
      letI := (Boundaries.final c pre b p).measurableSpace
      𝒟[(c.verifier e).decideWith stmt p v data]
        {r | ∃ out, r = some out ∧ (Boundaries.final c pre b p).holds out} = 1
  | .nil _, e, pre, _, _, stmt, hstmt, p, v, data => by
    have key : ∀ {α : Type} (_ : MeasurableSpace α) (x : OracleComp ambient (Option α)) (a : α)
        (P : α → Prop), x = pure (some a) → P a → 𝒟[x] {r | ∃ out, r = some out ∧ P out} = 1 := by
      intro α _ x a P hx ha
      subst hx
      rw [evalDist_pure]
      exact MeasureTheory.Measure.dirac_apply_of_mem ⟨a, rfl, ha⟩
    exact key _ _ stmt _ (decideWith_nil _ e stmt p v data) hstmt
  | .cons s V _ rest, e, pre, b, h, stmt, hstmt, p, v, data => by
    let _ := (b.1 (Path.split s _ p).1).measurableSpace
    have := (b.1 (Path.split s _ p).1).discrete
    let _ : MeasurableSpace ((rest (Path.split s _ p).1).Out (Path.split s _ p).2) :=
      (Boundaries.final (rest (Path.split s _ p).1) (b.1 (Path.split s _ p).1)
        (b.2 (Path.split s _ p).1) (Path.split s _ p).2).measurableSpace
    have : DiscreteMeasurableSpace ((rest (Path.split s _ p).1).Out (Path.split s _ p).2) :=
      (Boundaries.final (rest (Path.split s _ p).1) (b.1 (Path.split s _ p).1)
        (b.2 (Path.split s _ p).1) (Path.split s _ p).2).discrete
    exact OracleVerifier.append_decideWith_accepts_of_almostSurely V _ e.2 stmt p v data
      (b.1 (Path.split s _ p).1).holds _
      (h.1 stmt hstmt (Path.split s _ p).1 (View.split s _ p v).1
        ((OracleVerifier.prefixRoute (inputs := inputs) p).f data))
      fun mid hmid => decideWith_accepts_of_almostSurely (rest (Path.split s _ p).1)
        (e.1 (Path.split s _ p).1) (b.1 (Path.split s _ p).1) (b.2 (Path.split s _ p).1)
        (h.2 (Path.split s _ p).1) mid hmid (Path.split s _ p).2 (View.split s _ p v).2
        ((OracleVerifier.suffixRoute V stmt p v).f data)

/-! ## Splitting a chain at any stage

`StageChain.then` concatenates a chain `c` with a suffix `k`, which gives a chain at every leaf of
`c`. `StageChain.protocol_then` states that the composed protocol of the concatenation is the
append of the composed protocol of `c` and the composed protocols of the suffix chains.
`StageChain.decideOn_then` and `StageChain.outputOn_then` split the composed verifier of the
concatenation: on a run, it decides and exports output data as the append of the composed
verifier of `c` and the composed verifiers of the suffix chains. The concatenation and the two
parts carry their own compatibility evidence. The certificate at the boundary between `c` and the
suffix is new in the concatenation. The evidence of the concatenation is not built from the
evidence of the parts. -/

section Then

attribute [local implicit_reducible] projectPathAlong projectPathAlongLocalMap
  Displayed.LocalMap.toHom Displayed.LocalMap.toHomFun

/-- A chain to run after the chain `c`, given at every leaf of `c`. With no stages it is a chain
from the input statement type and the inputs. With a first stage it is a suffix of the remaining
stages at each path of that stage. `suffixAt` reads the chain at a leaf path, and `Suffix.ofFun`
builds a suffix from a chain at every leaf path. -/
def Suffix {S : Type} {inputs : OracleBundle} :
    StageChain ambient S inputs → Type 1
  | .nil (S := S) inputs => StageChain ambient S inputs
  | .cons s _ _ rest => (p : Path s) → (rest p).Suffix

/-- The chain of a suffix at a leaf path of `c`. It starts from the composed output statement type
and the composed output bundle of `c` at that path. -/
def suffixAt {S : Type} {inputs : OracleBundle} :
    (c : StageChain ambient S inputs) → c.Suffix → (p : Path c.protocol) →
      StageChain ambient (c.Out p) (c.outputs p)
  | .nil _, k, _ => k
  | .cons s _ _ rest, k, p =>
    (rest (Path.split s (fun p => (rest p).protocol) p).1).suffixAt
      (k (Path.split s (fun p => (rest p).protocol) p).1)
      (Path.split s (fun p => (rest p).protocol) p).2

/-- Concatenation: the stages of `c`, followed at each leaf by the chain of the suffix there. -/
def «then» {S : Type} {inputs : OracleBundle} :
    (c : StageChain ambient S inputs) → c.Suffix → StageChain ambient S inputs
  | .nil _, k => k
  | .cons s V draw rest, k => .cons s V draw fun p => (rest p).then (k p)

/-- The composed protocol of a concatenation is the composed protocol of the prefix chain,
followed at each leaf by the composed protocol of the suffix there. -/
theorem protocol_then {S : Type} {inputs : OracleBundle} :
    (c : StageChain ambient S inputs) → (k : c.Suffix) →
      (c.then k).protocol = c.protocol.append fun p => (c.suffixAt k p).protocol
  | .nil _, _ => rfl
  | .cons s _ _ rest, k =>
    (congrArg s.append (funext fun p => protocol_then (rest p) (k p))).trans
      (append_append_split s (fun p => (rest p).protocol)
        fun p q => ((rest p).suffixAt (k p) q).protocol).symm

/-- Concatenating after no stages gives the suffix. -/
@[simp] theorem nil_then {S : Type} (inputs : OracleBundle)
    (k : (nil (ambient := ambient) (S := S) inputs).Suffix) :
    (nil inputs).then k = k := rfl

/-- The suffix with no stages at every leaf. -/
def Suffix.nil {S : Type} {inputs : OracleBundle} :
    (c : StageChain ambient S inputs) → c.Suffix
  | .nil inputs => StageChain.nil inputs
  | .cons _ _ _ rest => fun p => Suffix.nil (rest p)

/-- Concatenating no stages at every leaf gives the chain. -/
@[simp] theorem then_suffixNil {S : Type} {inputs : OracleBundle} :
    (c : StageChain ambient S inputs) → c.then (Suffix.nil c) = c
  | .nil _ => rfl
  | .cons s V draw rest => congrArg (cons s V draw) (funext fun p => then_suffixNil (rest p))

/-- The suffix with no stages has no stages at every leaf. -/
@[simp] theorem suffixAt_suffixNil {S : Type} {inputs : OracleBundle} :
    (c : StageChain ambient S inputs) → (p : Path c.protocol) →
      c.suffixAt (Suffix.nil c) p = .nil (c.outputs p)
  | .nil _, _ => rfl
  | .cons _ _ _ rest, _ => suffixAt_suffixNil (rest _) _


/-- The decision of a composed verifier does not depend on the compatibility evidence. -/
theorem decide_verifier {S : Type} {inputs : OracleBundle} :
    (c : StageChain ambient S inputs) → (e e' : c.Compatibility) →
      (c.verifier e).decide = (c.verifier e').decide
  | .nil _, _, _ => rfl
  | .cons _ V _ rest, e, e' =>
    OracleVerifier.append_decide_congr V e.2 e'.2 fun p => decide_verifier (rest p) (e.1 p) (e'.1 p)

/-- The decision of a concatenation on a run, packaged with its statement type, and the equality of
that statement type with the suffix's. This is the induction behind `decideOn_then`. -/
theorem then_decideOn_sigma {S : Type} {inputs : OracleBundle} :
    (c : StageChain ambient S inputs) → (k : c.Suffix) →
    (tr₁ : Transcript oracleSig c.protocol) →
    (tr₂ : Transcript oracleSig (c.suffixAt k tr₁.path).protocol) →
    (tr : Transcript oracleSig (c.then k).protocol) →
    HEq tr (Transcript.append c.protocol (fun p => (c.suffixAt k p).protocol) tr₁ tr₂) →
    (c.then k).Out tr.path = (c.suffixAt k tr₁.path).Out tr₂.path ∧
    ∀ (e : (c.then k).Compatibility) (e₁ : c.Compatibility)
      (ek : (c.suffixAt k tr₁.path).Compatibility) (stmt : S) (data : inputs.Data),
      (⟨_, ((c.then k).verifier e).decideOn stmt data tr⟩ :
        (β : Type) × OracleComp ambient (Option β)) =
      ⟨_, (c.verifier e₁).decideOn stmt data tr₁ >>= fun
        | none => pure none
        | some mid => ((c.suffixAt k tr₁.path).verifier ek).decideOn mid
            ((c.verifier e₁).outputOn stmt data tr₁) tr₂⟩
  | .nil _, k, tr₁, tr₂, tr, h => by
    obtain rfl : tr = tr₂ := eq_of_heq h
    refine ⟨rfl, fun e e₁ ek stmt data => congrArg (Sigma.mk _) ?_⟩
    refine (congrFun (congrFun (congrFun (OracleVerifier.decideOn_eq_of_decide_eq
      (decide_verifier k e ek)) stmt) data) tr).trans ?_
    have h0 : ((nil (ambient := ambient) (S := S) _).verifier e₁).decideOn stmt data tr₁ =
        pure (some stmt) := decideWith_nil _ _ _ _ _ _
    rw [h0]
    symm
    exact LawfulMonad.pure_bind (m := OracleComp ambient) (some stmt) _
  | .cons s V draw rest, k, tr₁, tr₂, tr, h => by
    obtain ⟨trA, trB, rfl⟩ : ∃ a b, tr₁ = Transcript.append s (fun p => (rest p).protocol) a b :=
      ⟨_, _, (Transcript.append_split _ _ tr₁).symm⟩
    obtain ⟨trA', trC, rfl⟩ :
        ∃ a b, tr = Transcript.append s (fun p => ((rest p).then (k p)).protocol) a b :=
      ⟨_, _, (Transcript.append_split _ _ tr).symm⟩
    have hz := Transcript.split_path_append s (fun p => (rest p).protocol) trA trB
    obtain ⟨tr₂', htr₂⟩ : ∃ x : Transcript oracleSig
        ((rest trA.path).suffixAt (k trA.path) trB.path).protocol, HEq tr₂ x :=
      ⟨_, (cast_heq (congrArg (fun z : (p : Path s) × Path (rest p).protocol =>
        Transcript oracleSig ((rest z.1).suffixAt (k z.1) z.2).protocol) hz) tr₂).symm⟩
    have hTA := Transcript.append_append_heq s (fun p => (rest p).protocol)
      (fun p q => ((rest p).suffixAt (k p) q).protocol) trA trB tr₂ tr₂' htr₂
    obtain ⟨hA, hC⟩ := Transcript.eq_and_heq_of_append_heq
      (funext fun p => protocol_then (rest p) (k p)) (h.trans hTA)
    subst trA'
    obtain ⟨ihOut, ih⟩ := then_decideOn_sigma (rest trA.path) (k trA.path) trB tr₂' trC hC
    have hX : (⟨Path.split s (fun p => (rest p).protocol)
        (Transcript.append s (fun p => (rest p).protocol) trA trB).path, tr₂⟩ :
        (z : (p : Path s) × Path (rest p).protocol) ×
          Transcript oracleSig ((rest z.1).suffixAt (k z.1) z.2).protocol) =
        ⟨⟨trA.path, trB.path⟩, tr₂'⟩ :=
      Sigma.ext hz htr₂
    have hOutR := congrArg (fun X : (z : (p : Path s) × Path (rest p).protocol) ×
        Transcript oracleSig ((rest z.1).suffixAt (k z.1) z.2).protocol =>
      ((rest X.1.1).suffixAt (k X.1.1) X.1.2).Out X.2.path) hX
    have hOutL := congrArg (fun z : (p : Path s) × Path ((rest p).then (k p)).protocol =>
      ((rest z.1).then (k z.1)).Out z.2)
      (Transcript.split_path_append s (fun p => ((rest p).then (k p)).protocol) trA trC)
    refine ⟨hOutL.trans (ihOut.trans hOutR.symm), fun e e₁ ek stmt data => ?_⟩
    obtain ⟨ek', hek⟩ : ∃ x : ((rest trA.path).suffixAt (k trA.path) trB.path).Compatibility,
        HEq ek x :=
      ⟨_, (cast_heq (congrArg (fun z : (p : Path s) × Path (rest p).protocol =>
        ((rest z.1).suffixAt (k z.1) z.2).Compatibility) hz) ek).symm⟩
    have hct := OracleVerifier.append_decideOn_bind
      (Y := fun p q => Transcript oracleSig ((rest p).suffixAt (k p) q).protocol ×
        ((rest p).suffixAt (k p) q).Compatibility)
      (Z := fun p q y => ((rest p).suffixAt (k p) q).Out y.1.path)
      V (fun p => (rest p).verifier (e₁.1 p)) e₁.2
      (fun p q y mid d => (((rest p).suffixAt (k p) q).verifier y.2).decideOn mid d y.1)
      stmt data trA trB (tr₂, ek) (tr₂', ek')
      (heq_prod_mk (Y₁ := fun z : (p : Path s) × Path (rest p).protocol =>
          Transcript oracleSig ((rest z.1).suffixAt (k z.1) z.2).protocol)
        (Y₂ := fun z : (p : Path s) × Path (rest p).protocol =>
          ((rest z.1).suffixAt (k z.1) z.2).Compatibility) hz htr₂ hek)
    have hl := OracleVerifier.append_decideOn_sigma V
      (fun p => ((rest p).then (k p)).verifier (e.1 p)) e.2 stmt data trA trC
    refine hl.trans (Eq.trans ?_ (Eq.trans hct.symm ?_))
    · refine sigma_bind_congr ihOut _ fun o => ?_
      cases o with
      | none => exact sigma_pure_none ihOut
      | some m =>
        refine (ih (e.1 trA.path) (e₁.1 trA.path) ek' m (V.outputOn stmt data trA)).trans ?_
        refine congrArg (Sigma.mk _) (congrArg (_ >>= ·) (funext fun o' => ?_))
        cases o' <;> rfl
    · refine congrArg (Sigma.mk _) (congrArg (_ >>= ·) (funext fun o => ?_))
      cases o <;> rfl


/-- On a run that the composed verifier accepts, the composed output data does not depend on the
compatibility evidence. -/
theorem outputOn_eq_of_accepts {S : Type} {inputs : OracleBundle} :
    (c : StageChain ambient S inputs) → (e e' : c.Compatibility) → (stmt : S) →
    (data : inputs.Data) → (tr : Transcript oracleSig c.protocol) →
    (∃ out, some out ∈ support ((c.verifier e).decideOn stmt data tr)) →
    (c.verifier e).outputOn stmt data tr = (c.verifier e').outputOn stmt data tr
  | .nil _, _, _, _, _, _, _ => rfl
  | .cons s V _ rest, e, e', stmt, data, tr, hacc => by
    obtain ⟨trA, trB, rfl⟩ : ∃ a b, tr = Transcript.append s (fun p => (rest p).protocol) a b :=
      ⟨_, _, (Transcript.append_split _ _ tr).symm⟩
    obtain ⟨out, hout⟩ := hacc
    obtain ⟨out', -, hout'⟩ := exists_mem_support_of_sigma_eq
      (OracleVerifier.append_decideOn_sigma V (fun p => (rest p).verifier (e.1 p)) e.2 stmt data
        trA trB) hout
    rw [mem_support_bind_iff] at hout'
    obtain ⟨o, ho, hout'⟩ := hout'
    cases o with
    | none => simp at hout'
    | some m =>
      exact eq_of_heq (((OracleVerifier.append_outputOn V _ e.2 stmt data trA trB m ho).trans
        (heq_of_eq (outputOn_eq_of_accepts (rest trA.path) (e.1 _) (e'.1 _) m
          (V.outputOn stmt data trA) trB ⟨out', hout'⟩))).trans
        (OracleVerifier.append_outputOn V _ e'.2 stmt data trA trB m ho).symm)

/-- The output data of a concatenation on a run, once the prefix chain accepts `mid` and the
suffix chain accepts from `mid`, is the output data of the suffix chain. This is the statement
behind `outputOn_then`. -/
theorem then_outputOn_heq {S : Type} {inputs : OracleBundle} :
    (c : StageChain ambient S inputs) → (k : c.Suffix) →
    (tr₁ : Transcript oracleSig c.protocol) →
    (tr₂ : Transcript oracleSig (c.suffixAt k tr₁.path).protocol) →
    (tr : Transcript oracleSig (c.then k).protocol) →
    HEq tr (Transcript.append c.protocol (fun p => (c.suffixAt k p).protocol) tr₁ tr₂) →
    ∀ (e : (c.then k).Compatibility) (e₁ : c.Compatibility)
      (ek : (c.suffixAt k tr₁.path).Compatibility) (stmt : S) (data : inputs.Data)
      (mid : c.Out tr₁.path), some mid ∈ support ((c.verifier e₁).decideOn stmt data tr₁) →
      (∃ out, some out ∈ support (((c.suffixAt k tr₁.path).verifier ek).decideOn mid
        ((c.verifier e₁).outputOn stmt data tr₁) tr₂)) →
      HEq (((c.then k).verifier e).outputOn stmt data tr)
        (((c.suffixAt k tr₁.path).verifier ek).outputOn mid
          ((c.verifier e₁).outputOn stmt data tr₁) tr₂)
  | .nil _, k, tr₁, tr₂, tr, h => by
    obtain rfl : tr = tr₂ := eq_of_heq h
    intro e e₁ ek stmt data mid hmid hacc
    have h0 : ((nil (ambient := ambient) (S := S) _).verifier e₁).decideOn stmt data tr₁ =
        pure (some stmt) := decideWith_nil _ _ _ _ _ _
    rw [h0] at hmid
    obtain rfl : mid = stmt := Option.some.inj (eq_of_mem_support_pure hmid)
    exact heq_of_eq (outputOn_eq_of_accepts k ek e _ _ _ hacc).symm
  | .cons s V _ rest, k, tr₁, tr₂, tr, h => by
    intro e e₁ ek stmt data mid hmid hacc
    obtain ⟨trA, trB, rfl⟩ : ∃ a b, tr₁ = Transcript.append s (fun p => (rest p).protocol) a b :=
      ⟨_, _, (Transcript.append_split _ _ tr₁).symm⟩
    obtain ⟨trA', trC, rfl⟩ :
        ∃ a b, tr = Transcript.append s (fun p => ((rest p).then (k p)).protocol) a b :=
      ⟨_, _, (Transcript.append_split _ _ tr).symm⟩
    have hz := Transcript.split_path_append s (fun p => (rest p).protocol) trA trB
    obtain ⟨tr₂', htr₂⟩ : ∃ x : Transcript oracleSig
        ((rest trA.path).suffixAt (k trA.path) trB.path).protocol, HEq tr₂ x :=
      ⟨_, (cast_heq (congrArg (fun z : (p : Path s) × Path (rest p).protocol =>
        Transcript oracleSig ((rest z.1).suffixAt (k z.1) z.2).protocol) hz) tr₂).symm⟩
    have hTA := Transcript.append_append_heq s (fun p => (rest p).protocol)
      (fun p q => ((rest p).suffixAt (k p) q).protocol) trA trB tr₂ tr₂' htr₂
    obtain ⟨hA, hC⟩ := Transcript.eq_and_heq_of_append_heq
      (funext fun p => protocol_then (rest p) (k p)) (h.trans hTA)
    subst trA'
    obtain ⟨ek', hek⟩ : ∃ x : ((rest trA.path).suffixAt (k trA.path) trB.path).Compatibility,
        HEq ek x :=
      ⟨_, (cast_heq (congrArg (fun z : (p : Path s) × Path (rest p).protocol =>
        ((rest z.1).suffixAt (k z.1) z.2).Compatibility) hz) ek).symm⟩
    obtain ⟨mid', hmid', hsupp⟩ := exists_mem_support_of_sigma_eq
      (OracleVerifier.append_decideOn_sigma V (fun p => (rest p).verifier (e₁.1 p)) e₁.2 stmt
        data trA trB) hmid
    rw [mem_support_bind_iff] at hsupp
    obtain ⟨o, ho, hsupp⟩ := hsupp
    cases o with
    | none => simp at hsupp
    | some m =>
      have hd := OracleVerifier.append_outputOn V (fun p => (rest p).verifier (e₁.1 p)) e₁.2
        stmt data trA trB m ho
      have hX : (⟨Path.split s (fun p => (rest p).protocol)
          (Transcript.append s (fun p => (rest p).protocol) trA trB).path,
          (tr₂, ek, mid, ((cons s V _ rest).verifier e₁).outputOn stmt data
            (Transcript.append s (fun p => (rest p).protocol) trA trB))⟩ :
          (z : (p : Path s) × Path (rest p).protocol) ×
            Transcript oracleSig ((rest z.1).suffixAt (k z.1) z.2).protocol ×
            ((rest z.1).suffixAt (k z.1) z.2).Compatibility × (rest z.1).Out z.2 ×
            ((rest z.1).outputs z.2).Data) =
          ⟨⟨trA.path, trB.path⟩, (tr₂', ek', mid',
            ((rest trA.path).verifier (e₁.1 _)).outputOn m (V.outputOn stmt data trA) trB)⟩ :=
        Sigma.ext hz (heq_tuple4
          (Y₁ := fun z : (p : Path s) × Path (rest p).protocol =>
            Transcript oracleSig ((rest z.1).suffixAt (k z.1) z.2).protocol)
          (Y₂ := fun z : (p : Path s) × Path (rest p).protocol =>
            ((rest z.1).suffixAt (k z.1) z.2).Compatibility)
          (Y₃ := fun z : (p : Path s) × Path (rest p).protocol => (rest z.1).Out z.2)
          (Y₄ := fun z : (p : Path s) × Path (rest p).protocol =>
            ((rest z.1).outputs z.2).Data) hz htr₂ hek hmid' hd)
      have hacc' := (congrArg (fun X : (z : (p : Path s) × Path (rest p).protocol) ×
            Transcript oracleSig ((rest z.1).suffixAt (k z.1) z.2).protocol ×
            ((rest z.1).suffixAt (k z.1) z.2).Compatibility × (rest z.1).Out z.2 ×
            ((rest z.1).outputs z.2).Data =>
          ∃ out, some out ∈ support ((((rest X.1.1).suffixAt (k X.1.1) X.1.2).verifier
            X.2.2.1).decideOn X.2.2.2.1 X.2.2.2.2 X.2.1)) hX).mp hacc
      refine (OracleVerifier.append_outputOn V (fun p => ((rest p).then (k p)).verifier (e.1 p))
        e.2 stmt data trA trC m ho).trans ((then_outputOn_heq (rest trA.path) (k trA.path) trB
          tr₂' trC hC (e.1 _) (e₁.1 _) ek' m (V.outputOn stmt data trA) mid' hsupp hacc').trans ?_)
      exact (congr_arg_heq (fun X : (z : (p : Path s) × Path (rest p).protocol) ×
            Transcript oracleSig ((rest z.1).suffixAt (k z.1) z.2).protocol ×
            ((rest z.1).suffixAt (k z.1) z.2).Compatibility × (rest z.1).Out z.2 ×
            ((rest z.1).outputs z.2).Data =>
          (((rest X.1.1).suffixAt (k X.1.1) X.1.2).verifier X.2.2.1).outputOn X.2.2.2.1
            X.2.2.2.2 X.2.1) hX).symm


/-- The suffix that runs the chain `k p` at each leaf path `p` of `c`. -/
def Suffix.ofFun {S : Type} {inputs : OracleBundle} :
    (c : StageChain ambient S inputs) →
      ((p : Path c.protocol) → StageChain ambient (c.Out p) (c.outputs p)) → c.Suffix
  | .nil _, k => k ⟨⟩
  | .cons s _ _ rest, k => fun p₁ => Suffix.ofFun (rest p₁) fun p₂ =>
    cast (congrArg (fun z : (p : Path s) × Path (rest p).protocol =>
        StageChain ambient ((rest z.1).Out z.2) ((rest z.1).outputs z.2))
      (Path.split_append s (fun p => (rest p).protocol) p₁ p₂))
      (k (Path.append s (fun p => (rest p).protocol) p₁ p₂))

/-- The suffix built from a chain at every leaf path gives back that chain at each leaf path. -/
@[simp] theorem suffixAt_ofFun {S : Type} {inputs : OracleBundle} :
    (c : StageChain ambient S inputs) →
    (k : (p : Path c.protocol) → StageChain ambient (c.Out p) (c.outputs p)) →
    (p : Path c.protocol) → c.suffixAt (Suffix.ofFun c k) p = k p
  | .nil _, _, ⟨⟩ => rfl
  | .cons s _ _ rest, k, p =>
    (suffixAt_ofFun (rest _) _ _).trans
      (eq_of_heq ((cast_heq _ _).trans
        (congr_arg_heq k (Path.append_split s (fun p => (rest p).protocol) p))))

/-- The final decision type of a concatenation on a run is the final decision type of the suffix
chain on the suffix part of the run. -/
theorem Out_then {S : Type} {inputs : OracleBundle} (c : StageChain ambient S inputs) (k : c.Suffix)
    (tr₁ : Transcript oracleSig c.protocol)
    (tr₂ : Transcript oracleSig (c.suffixAt k tr₁.path).protocol)
    (tr : Transcript oracleSig (c.then k).protocol)
    (h : HEq tr (Transcript.append c.protocol (fun p => (c.suffixAt k p).protocol) tr₁ tr₂)) :
    (c.then k).Out tr.path = (c.suffixAt k tr₁.path).Out tr₂.path :=
  (then_decideOn_sigma c k tr₁ tr₂ tr h).1

/-- Split a stage chain at any stage, for the final decision. The composed verifier of the
concatenation `c.then k` decides on a run `tr` as the append of the composed verifier of `c` and
the composed verifiers of the suffix chains decides on the corresponding run of the appended
protocol. The hypothesis `h` transports `tr` along `protocol_then`. The concatenation and the two
parts carry their own compatibility evidence, and the decision does not depend on it. -/
theorem decideOn_then {S : Type} {inputs : OracleBundle} (c : StageChain ambient S inputs)
    (k : c.Suffix)
    (e : (c.then k).Compatibility) (e₁ : c.Compatibility)
    (ek : (p : Path c.protocol) → (c.suffixAt k p).Compatibility)
    (compatible : OracleVerifier.OutputCompatibility (c.verifier e₁)
      fun p => (c.suffixAt k p).verifier (ek p))
    (stmt : S) (data : inputs.Data) (tr₁ : Transcript oracleSig c.protocol)
    (tr₂ : Transcript oracleSig (c.suffixAt k tr₁.path).protocol)
    (tr : Transcript oracleSig (c.then k).protocol)
    (h : HEq tr (Transcript.append c.protocol (fun p => (c.suffixAt k p).protocol) tr₁ tr₂)) :
    HEq (((c.then k).verifier e).decideOn stmt data tr)
      (((c.verifier e₁).append (fun p => (c.suffixAt k p).verifier (ek p)) compatible).decideOn
        stmt data (Transcript.append c.protocol (fun p => (c.suffixAt k p).protocol) tr₁ tr₂)) := by
  have hl := (then_decideOn_sigma c k tr₁ tr₂ tr h).2 e e₁ (ek tr₁.path) stmt data
  have hr := OracleVerifier.append_decideOn_sigma (c.verifier e₁)
    (fun p => (c.suffixAt k p).verifier (ek p)) compatible stmt data tr₁ tr₂
  refine (Sigma.mk.inj_iff.mp (hl.trans (Eq.trans ?_ hr.symm))).2
  refine congrArg (Sigma.mk _) (congrArg (_ >>= ·) (funext fun o => ?_))
  cases o <;> rfl

/-- Split a stage chain at any stage, for the output data. On a run that the concatenation
accepts, the composed verifier of `c.then k` exports the same output data as the append of the
composed verifier of `c` and the composed verifiers of the suffix chains on the corresponding run
of the appended protocol. -/
theorem outputOn_then {S : Type} {inputs : OracleBundle} (c : StageChain ambient S inputs)
    (k : c.Suffix)
    (e : (c.then k).Compatibility) (e₁ : c.Compatibility)
    (ek : (p : Path c.protocol) → (c.suffixAt k p).Compatibility)
    (compatible : OracleVerifier.OutputCompatibility (c.verifier e₁)
      fun p => (c.suffixAt k p).verifier (ek p))
    (stmt : S) (data : inputs.Data) (tr₁ : Transcript oracleSig c.protocol)
    (tr₂ : Transcript oracleSig (c.suffixAt k tr₁.path).protocol)
    (tr : Transcript oracleSig (c.then k).protocol)
    (h : HEq tr (Transcript.append c.protocol (fun p => (c.suffixAt k p).protocol) tr₁ tr₂))
    (hacc : ∃ out, some out ∈ support (((c.then k).verifier e).decideOn stmt data tr)) :
    HEq (((c.then k).verifier e).outputOn stmt data tr)
      (((c.verifier e₁).append (fun p => (c.suffixAt k p).verifier (ek p)) compatible).outputOn
        stmt data (Transcript.append c.protocol (fun p => (c.suffixAt k p).protocol) tr₁ tr₂)) := by
  obtain ⟨out, hout⟩ := hacc
  obtain ⟨out', -, hout'⟩ := exists_mem_support_of_sigma_eq
    ((then_decideOn_sigma c k tr₁ tr₂ tr h).2 e e₁ (ek tr₁.path) stmt data) hout
  rw [mem_support_bind_iff] at hout'
  obtain ⟨o, ho, hout'⟩ := hout'
  cases o with
  | none => simp at hout'
  | some mid =>
    exact (then_outputOn_heq c k tr₁ tr₂ tr h e e₁ (ek tr₁.path) stmt data mid ho
      ⟨out', hout'⟩).trans (OracleVerifier.append_outputOn (c.verifier e₁)
        (fun p => (c.suffixAt k p).verifier (ek p)) compatible stmt data tr₁ tr₂ mid ho).symm


end Then

end StageChain

end Interaction

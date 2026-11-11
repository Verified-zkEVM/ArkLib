/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Interaction.Core.Oracle.Routing
public import VCVio.OracleComp.EvalDist

/-!
# Finite heterogeneous stage composition

A finite chain of passive oracle verifiers composes into one passive oracle verifier through
`OracleVerifier.append`. The first stage has a fixed protocol. Every later stage is selected by
the shape path of the stages before it, which records the prover's public messages and nothing
else: challenges and oracle payloads never select a later stage, and neither does an earlier
verdict. The statement types and oracle families at the stage boundaries may all differ, and may
depend on the same shape paths.

The composed execution runs the interactions of all stages, then folds the decisions: each stage's
decision receives the statement that the previous decision accepted, and a rejection makes the
composite reject. A rejecting decision does not skip any interaction. `Stages.run` is the core run
`OracleVerifier.run` of the composed verifier, with the challenge queries answered by the stages'
draws. `Stages.run_cons` states that it is the run of the binary append of the first stage and the
composed rest, which `OracleVerifier.run_append` splits into the two interactions and the two
decisions.

A stage's output map does not read the stage's input statement. In the composed execution that
statement is the result of the previous decision, which runs after every interaction; an output
map sees the public view and queries the resources of the path, as `OracleVerifier.append`
requires of a composite output map.
-/

@[expose] public section

universe u w uI uS wI wJ wK

namespace Interaction.Core
open PFunctor FreeM TwoParty.Lens OracleComp Oracle

namespace OracleVerifier

variable {ι : Type u} {I : Type uI} {ambient : OracleSpec.{u, u} ι} {A : I → Type u}
  {inputs : OracleFamily.{uI, u, wI} I A}
  {s₁ : OracleProtocol.{u}} {s₂ : Path s₁ → OracleProtocol.{u}} {S : Type uS}
  {T : Path s₁ → Type u} {U : (p : Path s₁) → Path (s₂ p) → Type u}
  {J : Path s₁ → Type u} {B : (p : Path s₁) → J p → Type u}
  {middle : (p : Path s₁) → OracleFamily.{u, u, wJ} (J p) (B p)}
  {K : (p : Path s₁) → Path (s₂ p) → Type u}
  {C : (p₁ : Path s₁) → (p₂ : Path (s₂ p₁)) → K p₁ p₂ → Type u}
  {outputs : (p₁ : Path s₁) → (p₂ : Path (s₂ p₁)) → OracleFamily.{u, u, wK} (K p₁ p₂) (C p₁ p₂)}

/-- The output map of an appended verifier whose component output maps do not read their input
statements: the prefix map routes the inputs, and the suffix map reads the routed inputs and the
suffix messages. -/
def appendMap
    (map₁ : (p : Path s₁) → View s₁ p →
      OracleMap (pathResources inputs s₁ p) (Resources.ofFamily (middle p)))
    (map₂ : (p₁ : Path s₁) → (p₂ : Path (s₂ p₁)) → View (s₂ p₁) p₂ →
      OracleMap (pathResources (middle p₁) (s₂ p₁) p₂) (Resources.ofFamily (outputs p₁ p₂)))
    (p : Path (s₁.append s₂)) (v : View (s₁.append s₂) p) :
    OracleMap (pathResources inputs (s₁.append s₂) p)
      (Resources.ofFamily (splitOutputs outputs p)) :=
  (map₂ (Path.split s₁ s₂ p).1 (Path.split s₁ s₂ p).2 (View.split s₁ s₂ p v).2).comp
    (((map₁ (Path.split s₁ s₂ p).1 (View.split s₁ s₂ p v).1).par
      (OracleMap.id (Resources.ofFamily (pathFamily _ (Path.split s₁ s₂ p).2)))).comp
      (resources (inputs := inputs) p))

/-- Compatibility when neither output map reads its input statement. The composite output map is
`appendMap`, so it reads neither the input statement nor the intermediate one. -/
def OutputCompatibility.ofStatementFree (V₁ : OracleVerifier ambient s₁ S T inputs middle)
    (V₂ : (p : Path s₁) → OracleVerifier ambient (s₂ p) (T p) (U p) (middle p) (outputs p))
    (map₁ : (p : Path s₁) → View s₁ p →
      OracleMap (pathResources inputs s₁ p) (Resources.ofFamily (middle p)))
    (h₁ : ∀ stmt, V₁.outputMap stmt = map₁)
    (map₂ : (p₁ : Path s₁) → (p₂ : Path (s₂ p₁)) → View (s₂ p₁) p₂ →
      OracleMap (pathResources (middle p₁) (s₂ p₁) p₂) (Resources.ofFamily (outputs p₁ p₂)))
    (h₂ : ∀ p₁ mid, (V₂ p₁).outputMap mid = map₂ p₁) :
    OutputCompatibility V₁ V₂ where
  outputMap _ := appendMap map₁ map₂
  agrees stmt p v data mid _ := by
    simp only [appendMap, suffixRoute, h₁, h₂]
    rfl

section DecisionLaws

variable (V₁ : OracleVerifier ambient s₁ S T inputs middle)
  (V₂ : (p : Path s₁) → OracleVerifier ambient (s₂ p) (T p) (U p) (middle p) (outputs p))
  (compatible : OutputCompatibility V₁ V₂) (stmt : S) (p : Path (s₁.append s₂))
  (v : View (s₁.append s₂) p) (data : (pathResources inputs (s₁.append s₂) p).Data)

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

/-- An invariant propagates over the support: if every possible prefix result is an accepted
statement satisfying `Mid`, and every possible suffix result from such a statement is an accepted
statement satisfying `Post`, so is every possible result of the appended decision. -/
theorem append_decideWith_preserves_support (Mid : T (Path.split s₁ s₂ p).1 → Prop)
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

/-- An invariant propagates almost surely: almost-sure acceptance with `Mid` by the prefix
decision and, from every statement satisfying `Mid`, almost-sure acceptance with `Post` by the
suffix decision give almost-sure acceptance with `Post` by the appended decision. The ambient
oracles carry an answer measure, and both statement spaces are measurable and discrete. -/
theorem append_decideWith_preserves_measure [ambient.AnswerMeasure]
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

/-- A finite chain of passive oracle verifiers from the input statement type `S` and the input
oracle family `inputs`.

`nil` is the empty chain. `cons s V map _ draw rest` runs the protocol `s`, whose challenges are
answered by `draw`, and then, at each shape path `p` of `s`, the chain `rest p`. The verifier `V`
accepts a statement of type `T p` with the oracle family `middle p`, which are the inputs of
`rest p`; its output map is `map`, which does not read the input statement. Statement types live
in the computation universe `u`, and every oracle family of the chain has its queries in one
universe `w`. -/
inductive Stages {ι : Type u} (ambient : OracleSpec.{u, u} ι) :
    (S : Type u) → {I : Type u} → {A : I → Type u} → OracleFamily.{u, u, w} I A →
      Type (max (u + 1) (w + 1)) where
  /-- No stages. -/
  | nil {S : Type u} {I : Type u} {A : I → Type u} (inputs : OracleFamily.{u, u, w} I A) :
      Stages ambient S inputs
  /-- A first stage, then the remaining stages selected by its shape path. -/
  | cons {S : Type u} {I : Type u} {A : I → Type u} {inputs : OracleFamily.{u, u, w} I A}
      (s : OracleProtocol.{u}) {T : Path s → Type u} {J : Path s → Type u}
      {B : (p : Path s) → J p → Type u}
      {middle : (p : Path s) → OracleFamily.{u, u, w} (J p) (B p)}
      (verifier : OracleVerifier ambient s S T inputs middle)
      (map : (p : Path s) → View s p →
        OracleMap (pathResources inputs s p) (Resources.ofFamily (middle p)))
      (outputMap_eq : ∀ stmt, verifier.outputMap stmt = map)
      (draw : (c : ChallengeNode oracleSig s) → OracleComp ambient (challengeSpec oracleSig s c))
      (rest : (p : Path s) → Stages ambient (T p) (middle p)) :
      Stages ambient S inputs

namespace Stages

variable {ι : Type u} {ambient : OracleSpec.{u, u} ι}

/-- The composed protocol: the first stage's protocol, followed at each of its shape paths by the
composed protocol of the remaining stages. -/
def protocol {S : Type u} {I : Type u} {A : I → Type u} {inputs : OracleFamily.{u, u, w} I A} :
    Stages ambient S inputs → OracleProtocol.{u}
  | .nil _ => .pure ⟨⟩
  | .cons s _ _ _ _ rest => s.append fun p => (rest p).protocol

/-- The composed output statement type at a shape path: the input statement type for no stages,
and otherwise the output of the remaining stages at the split path. -/
def Out {S : Type u} {I : Type u} {A : I → Type u} {inputs : OracleFamily.{u, u, w} I A} :
    (c : Stages ambient S inputs) → Path c.protocol → Type u
  | .nil _, _ => S
  | .cons _ _ _ _ _ rest, p =>
    splitFamily (s₂ := fun p => (rest p).protocol) (fun p₁ => (rest p₁).Out) p

/-- The index type of the composed output oracle family at a shape path. -/
def OutIdx {S : Type u} {I : Type u} {A : I → Type u} {inputs : OracleFamily.{u, u, w} I A} :
    (c : Stages ambient S inputs) → Path c.protocol → Type u
  | .nil (I := I) _, _ => I
  | .cons _ _ _ _ _ rest, p =>
    splitFamily (s₂ := fun p => (rest p).protocol) (fun p₁ => (rest p₁).OutIdx) p

/-- The data types of the composed output oracle family at a shape path. -/
def OutData {S : Type u} {I : Type u} {A : I → Type u} {inputs : OracleFamily.{u, u, w} I A} :
    (c : Stages ambient S inputs) → (p : Path c.protocol) → c.OutIdx p → Type u
  | .nil (A := A) _, _ => A
  | .cons s _ _ _ _ rest, p =>
    (rest (Path.split s (fun p => (rest p).protocol) p).1).OutData
      (Path.split s (fun p => (rest p).protocol) p).2

/-- The composed output oracle family at a shape path: the inputs for no stages, and otherwise the
output family of the remaining stages at the split path. -/
def outputs {S : Type u} {I : Type u} {A : I → Type u} {inputs : OracleFamily.{u, u, w} I A} :
    (c : Stages ambient S inputs) → (p : Path c.protocol) →
      OracleFamily.{u, u, w} (c.OutIdx p) (c.OutData p)
  | .nil inputs, _ => inputs
  | .cons s _ _ _ _ rest, p =>
    (rest (Path.split s (fun p => (rest p).protocol) p).1).outputs
      (Path.split s (fun p => (rest p).protocol) p).2

/-- The composed output map. For no stages it forwards the inputs; otherwise it is `appendMap` of
the first stage's map and the composed map of the remaining stages. -/
def map {S : Type u} {I : Type u} {A : I → Type u} {inputs : OracleFamily.{u, u, w} I A} :
    (c : Stages ambient S inputs) → (p : Path c.protocol) → View c.protocol p →
      OracleMap (pathResources inputs c.protocol p) (Resources.ofFamily (c.outputs p))
  | .nil _, _, _ => OracleMap.fst _ _
  | .cons _ _ map₁ _ _ rest, p, v =>
    OracleVerifier.appendMap (s₂ := fun p => (rest p).protocol) map₁
      (fun p₁ => (rest p₁).map) p v

/-- The composed decision. For no stages it accepts the input statement; otherwise it is the
decision of the binary append of the first stage's verifier and the composed rest. -/
def decide {S : Type u} {I : Type u} {A : I → Type u} {inputs : OracleFamily.{u, u, w} I A} :
    (c : Stages ambient S inputs) → S → (p : Path c.protocol) → View c.protocol p →
      OptionT (OracleComp (ambient + (pathResources inputs c.protocol p).spec)) (c.Out p)
  | .nil _, stmt, _, _ => pure stmt
  | .cons _ V map₁ h₁ _ rest, stmt, p, v =>
    (V.append (s₂ := fun p => (rest p).protocol)
      (fun p₁ => ⟨(rest p₁).decide, fun _ => (rest p₁).map⟩)
      (OracleVerifier.OutputCompatibility.ofStatementFree V _ map₁ h₁
        (fun p₁ => (rest p₁).map) fun _ _ => rfl)).decide stmt p v

/-- The composed passive oracle verifier. -/
def verifier {S : Type u} {I : Type u} {A : I → Type u} {inputs : OracleFamily.{u, u, w} I A}
    (c : Stages ambient S inputs) :
    OracleVerifier ambient c.protocol S c.Out inputs c.outputs where
  decide := c.decide
  outputMap _ := c.map

/-- The composed challenge implementation, which combines the stages' draws along the shape path
of the earlier stages. -/
def draw {S : Type u} {I : Type u} {A : I → Type u} {inputs : OracleFamily.{u, u, w} I A} :
    (c : Stages ambient S inputs) → (ch : ChallengeNode oracleSig c.protocol) →
      OracleComp ambient (challengeSpec oracleSig c.protocol ch)
  | .nil _, ch => ch.val.elim
  | .cons s _ _ _ draw₁ rest, ch =>
    combineDraw oracleSig s (fun p => (rest p).protocol) draw₁ (fun p => (rest p).draw) ch

/-- The composed challenge queries answered by the stages' draws; shared queries stay shared. -/
def handler {S : Type u} {I : Type u} {A : I → Type u} {inputs : OracleFamily.{u, u, w} I A}
    (c : Stages ambient S inputs) :
    QueryImpl (ambient + challengeSpec oracleSig c.protocol) (OracleComp ambient) :=
  QueryImpl.id' ambient + c.draw

/-- Run every stage's interaction against a prover of the composed protocol, then fold the
decisions. The verdict is the composed accepted statement with the composed output data, or
`none` if a decision rejects. -/
def run {S : Type u} {I : Type u} {A : I → Type u} {inputs : OracleFamily.{u, u, w} I A}
    (c : Stages ambient S inputs) (stmt : S) (data : ∀ i, A i)
    {Out : PathAlong oracleSig c.protocol → Type u}
    (prover : Prover oracleSig ambient c.protocol Out) :
    OracleComp ambient
      (Observation oracleSig c.protocol Out (OracleVerifier.Output c.Out c.OutData)) :=
  simulateQ c.handler (c.verifier.run stmt data prover)

section Laws

variable {S : Type u} {I : Type u} {A : I → Type u} {inputs : OracleFamily.{u, u, w} I A}
  (s : OracleProtocol.{u}) {T : Path s → Type u} {J : Path s → Type u}
  {B : (p : Path s) → J p → Type u}
  {middle : (p : Path s) → OracleFamily.{u, u, w} (J p) (B p)}
  (V : OracleVerifier ambient s S T inputs middle)
  (map₁ : (p : Path s) → View s p →
    OracleMap (pathResources inputs s p) (Resources.ofFamily (middle p)))
  (h₁ : ∀ stmt, V.outputMap stmt = map₁)
  (draw₁ : (c : ChallengeNode oracleSig s) → OracleComp ambient (challengeSpec oracleSig s c))
  (rest : (p : Path s) → Stages ambient (T p) (middle p))

/-- The composed protocol of a chain with a first stage. -/
@[simp] theorem protocol_cons :
    (cons s V map₁ h₁ draw₁ rest).protocol = s.append fun p => (rest p).protocol := rfl

/-- The output-map compatibility of the first stage with the composed rest. -/
abbrev compatible : OracleVerifier.OutputCompatibility V fun p => (rest p).verifier :=
  OracleVerifier.OutputCompatibility.ofStatementFree V _ map₁ h₁ (fun p => (rest p).map)
    fun _ _ => rfl

/-- The composed verifier of a chain with a first stage is the binary append of that stage's
verifier and the composed verifier of the rest. -/
theorem verifier_cons :
    (cons s V map₁ h₁ draw₁ rest).verifier =
      V.append (fun p => (rest p).verifier) (compatible s V map₁ h₁ rest) := rfl

/-- The composed draws of a chain with a first stage combine that stage's draws with the composed
draws of the rest. -/
theorem draw_cons :
    (cons s V map₁ h₁ draw₁ rest).draw =
      combineDraw oracleSig s (fun p => (rest p).protocol) draw₁ fun p => (rest p).draw := rfl

/-- The run of a chain with a first stage is the core run of the binary append of that stage's
verifier and the composed rest, with the challenges answered by the combined draws.
`OracleVerifier.run_append` splits it into the first stage's interaction, the rest's interaction,
the first decision and, after its acceptance only, the rest's decision. -/
theorem run_cons (stmt : S) (data : ∀ i, A i)
    {Out : PathAlong oracleSig (s.append fun p => (rest p).protocol) → Type u}
    (prover : Prover oracleSig ambient (s.append fun p => (rest p).protocol) Out) :
    (cons s V map₁ h₁ draw₁ rest).run stmt data prover =
      simulateQ (QueryImpl.id' ambient +
          combineDraw oracleSig s (fun p => (rest p).protocol) draw₁ fun p => (rest p).draw)
        ((V.append (fun p => (rest p).verifier) (compatible s V map₁ h₁ rest)).run stmt data
          prover) := rfl

/-- A rejecting first decision makes the composed decision reject. The interactions of the
remaining stages have already run; only their decisions are skipped. The invariant laws
`OracleVerifier.append_decideWith_of_accept`, `OracleVerifier.append_decideWith_preserves_support`
and `OracleVerifier.append_decideWith_preserves_measure` apply to a chain through
`verifier_cons`. -/
theorem decideWith_cons_of_reject (stmt : S) (p : Path (s.append fun p => (rest p).protocol))
    (v : View _ p) (data : (pathResources inputs (s.append fun p => (rest p).protocol) p).Data)
    (h : V.decideWith stmt (Path.split s _ p).1 (View.split s _ p v).1
      ((OracleVerifier.prefixRoute (inputs := inputs) p).f data) = pure none) :
    (cons s V map₁ h₁ draw₁ rest).verifier.decideWith stmt p v data = pure none :=
  OracleVerifier.append_decideWith_of_reject V _ (compatible s V map₁ h₁ rest) stmt p v data h

end Laws

/-- With no stages, the composed decision accepts the input statement. -/
@[simp] theorem decideWith_nil {S : Type u} {I : Type u} {A : I → Type u}
    (inputs : OracleFamily.{u, u, w} I A) (stmt : S) (p : Path (nil (ambient := ambient) (S := S)
      inputs).protocol) (v : View _ p) (data : (pathResources inputs (nil (ambient := ambient)
        (S := S) inputs).protocol p).Data) :
    (nil (ambient := ambient) (S := S) inputs).verifier.decideWith stmt p v data =
      pure (some stmt) := by
  simp only [OracleVerifier.decideWith, verifier, decide]
  exact simulateQ_pure _ _

/-- With no stages, the composed output data is the input data. -/
@[simp] theorem map_nil {S : Type u} {I : Type u} {A : I → Type u}
    (inputs : OracleFamily.{u, u, w} I A) (p : Path (nil (ambient := ambient) (S := S)
      inputs).protocol) (v : View _ p) (data : (pathResources inputs (nil (ambient := ambient)
        (S := S) inputs).protocol p).Data) :
    ((nil (ambient := ambient) (S := S) inputs).map p v).f data = data.1 := rfl

/-- A chain of one stage decides as that stage: its composed decision is the stage's decision at
the split path, on the data that `prefixRoute` selects. -/
theorem decideWith_one {S : Type u} {I : Type u} {A : I → Type u}
    {inputs : OracleFamily.{u, u, w} I A}
    (s : OracleProtocol.{u}) {T : Path s → Type u} {J : Path s → Type u}
    {B : (p : Path s) → J p → Type u}
    {middle : (p : Path s) → OracleFamily.{u, u, w} (J p) (B p)}
    (V : OracleVerifier ambient s S T inputs middle)
    (map₁ : (p : Path s) → View s p →
      OracleMap (pathResources inputs s p) (Resources.ofFamily (middle p)))
    (h₁ : ∀ stmt, V.outputMap stmt = map₁)
    (draw₁ : (c : ChallengeNode oracleSig s) → OracleComp ambient (challengeSpec oracleSig s c))
    (stmt : S)
    (p : Path (s.append fun p => (nil (ambient := ambient) (S := T p) (middle p)).protocol))
    (v : View _ p) (data : (pathResources inputs
      (s.append fun p => (nil (ambient := ambient) (S := T p) (middle p)).protocol) p).Data) :
    (cons s V map₁ h₁ draw₁ fun p => nil (middle p)).verifier.decideWith stmt p v data =
      V.decideWith stmt (Path.split s _ p).1 (View.split s _ p v).1
        ((OracleVerifier.prefixRoute (inputs := inputs) p).f data) := by
  refine (OracleVerifier.append_decideWith V _ (compatible s V map₁ h₁ _) stmt p v data).trans ?_
  refine (_root_.bind_congr fun r => ?_).trans (_root_.bind_pure _)
  cases r with
  | none => rfl
  | some mid => exact decideWith_nil _ _ _ _ _

end Stages

end Interaction.Core

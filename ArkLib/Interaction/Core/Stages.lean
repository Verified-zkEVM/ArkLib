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

A chain is given in two parts. `Stages` is the plan: the protocols, verifiers and draws of the
stages. `Stages.Compatibility` is the evidence: at every boundary, an
`OracleVerifier.OutputCompatibility` certificate between the stage's verifier and the composed
verifier of the stages after it. `Stages.verifier` builds the composed verifier from both, by
recursion on the plan. The certificates are general, so output maps may read the input statement;
`OutputCompatibility.ofStatement` gives one when the intermediate statement is public.
`Stages.StatementFree` is the special case in which no output map reads its input statement. The
evidence is computed from the plan, rather than stored in the plan's constructors, so that the
inductive type does not refer to the verifier computed from it.

Every oracle family of a chain has its queries in one universe `w`, because a recursive occurrence
of an inductive type has the universe parameters of the type. This is a choice of representation:
the binary append keeps independent query universes, and families with smaller query universes
enter a chain through `Interaction.Oracle.OracleFamily.liftQueries`:
`OracleVerifier.liftInputs` and `OracleVerifier.liftOutputs` adapt a stage, and
`OracleVerifier.lowerOutputs` recovers the original family of the chain's output. These adapters
leave the data, the decisions and the output data unchanged.

The invariant laws `Stages.decideWith_accepts`, `Stages.decideWith_preserves_support` and
`Stages.decideWith_preserves_measure` derive a property of the composed decision from one
hypothesis per stage boundary. They concern the fold of the decisions after all interactions.
-/

@[expose] public section

universe u w w' uι uI uI' uJ uS wI wI' wJ wK

namespace Interaction.Core
open PFunctor FreeM TwoParty.Lens OracleComp Oracle

/-! ## Query universes -/

/-- The same oracle family with each query type lifted to a larger universe. The data, the
responses and the answers are unchanged. -/
def _root_.Interaction.Oracle.OracleFamily.liftQueries {I : Type uI} {A : I → Type u}
    (F : OracleFamily.{uI, u, wI} I A) : OracleFamily.{uI, u, max wI w'} I A where
  interface i :=
    { Query := ULift.{w'} (F.interface i).Query
      toOC :=
        { spec := fun q => (F.interface i).toOC.spec q.down
          impl := fun q => (F.interface i).toOC.impl q.down } }

namespace OracleMap

variable {I : Type uI} {A : I → Type u}

/-- Answer the queries of a family by the corresponding lifted queries. -/
def lowerQueries (F : OracleFamily.{uI, u, wI} I A) :
    OracleMap (Resources.ofFamily (F.liftQueries.{u, w', uI, wI})) (Resources.ofFamily F) where
  f x := x
  impl q := liftM ((F.liftQueries.{u, w', uI, wI}).spec.query ⟨q.1, ULift.up q.2⟩)
  law _ _ := rfl

/-- Answer the lifted queries of a family by the original queries. -/
def liftQueries (F : OracleFamily.{uI, u, wI} I A) :
    OracleMap (Resources.ofFamily F) (Resources.ofFamily (F.liftQueries.{u, w', uI, wI})) where
  f x := x
  impl q := liftM (F.spec.query ⟨q.1, q.2.down⟩)
  law _ _ := rfl

end OracleMap

namespace OracleVerifier

section Adapters

variable {ι : Type uι} {ambient : OracleSpec.{uι, u} ι} {s : OracleProtocol.{u}} {S : Type uS}
  {T : Path s → Type u} {I : Type uI} {A : I → Type u} {I' : Type uI'} {A' : I' → Type u}
  {inputs : OracleFamily.{uI, u, wI} I A} {inputs' : OracleFamily.{uI', u, wI'} I' A'}
  {J : Path s → Type uJ} {B : (p : Path s) → J p → Type u}
  {outputs : (p : Path s) → OracleFamily.{uJ, u, wJ} (J p) (B p)}
  {outputs' : (p : Path s) → OracleFamily.{uJ, u, wK} (J p) (B p)}

/-- Read the inputs through an oracle map from other inputs. The decision routes its input queries
through the map, and the output map reads the mapped input data. -/
def comapInputs (V : OracleVerifier ambient s S T inputs outputs)
    (r : OracleMap (Resources.ofFamily inputs') (Resources.ofFamily inputs)) :
    OracleVerifier ambient s S T inputs' outputs where
  decide stmt p v := OptionT.mk
    (simulateQ ((r.par (OracleMap.id _)).withAmbient ambient) (V.decide stmt p v).run)
  outputMap stmt p v := (V.outputMap stmt p v).comp (r.par (OracleMap.id _))

/-- Export the outputs through an oracle map at every shape path. The decision is unchanged. -/
def mapOutputs (V : OracleVerifier ambient s S T inputs outputs)
    (r : (p : Path s) → OracleMap (Resources.ofFamily (outputs p))
      (Resources.ofFamily (outputs' p))) :
    OracleVerifier ambient s S T inputs outputs' where
  decide := V.decide
  outputMap stmt p v := (r p).comp (V.outputMap stmt p v)

/-- Reading the inputs through an oracle map decides as the original verifier on the mapped data.
-/
theorem comapInputs_decideWith (V : OracleVerifier ambient s S T inputs outputs)
    (r : OracleMap (Resources.ofFamily inputs') (Resources.ofFamily inputs)) (stmt : S)
    (p : Path s) (v : View s p) (data : (pathResources inputs' s p).Data) :
    (V.comapInputs r).decideWith stmt p v data = V.decideWith stmt p v (r.f data.1, data.2) :=
  OracleMap.simulate_withAmbient (r.par (OracleMap.id _)) data _

/-- Reading the inputs through an oracle map exports the original output data of the mapped data.
-/
theorem comapInputs_outputData (V : OracleVerifier ambient s S T inputs outputs)
    (r : OracleMap (Resources.ofFamily inputs') (Resources.ofFamily inputs)) (stmt : S)
    (p : Path s) (v : View s p) (data : (pathResources inputs' s p).Data) :
    ((V.comapInputs r).outputMap stmt p v).f data =
      (V.outputMap stmt p v).f (r.f data.1, data.2) := rfl

/-- Exporting the outputs through oracle maps keeps the decision. -/
theorem mapOutputs_decideWith (V : OracleVerifier ambient s S T inputs outputs)
    (r : (p : Path s) → OracleMap (Resources.ofFamily (outputs p))
      (Resources.ofFamily (outputs' p))) :
    (V.mapOutputs r).decideWith = V.decideWith := rfl

/-- Exporting the outputs through oracle maps applies them to the original output data. -/
theorem mapOutputs_outputData (V : OracleVerifier ambient s S T inputs outputs)
    (r : (p : Path s) → OracleMap (Resources.ofFamily (outputs p))
      (Resources.ofFamily (outputs' p))) (stmt : S) (p : Path s) (v : View s p)
    (data : (pathResources inputs s p).Data) :
    ((V.mapOutputs r).outputMap stmt p v).f data = (r p).f ((V.outputMap stmt p v).f data) :=
  rfl

/-- Accept the inputs with their queries lifted to a larger universe. -/
abbrev liftInputs (V : OracleVerifier ambient s S T inputs outputs) :
    OracleVerifier ambient s S T (inputs.liftQueries.{u, w', uI, wI}) outputs :=
  V.comapInputs (OracleMap.lowerQueries inputs)

/-- Export the outputs with their queries lifted to a larger universe. -/
abbrev liftOutputs (V : OracleVerifier ambient s S T inputs outputs) :
    OracleVerifier ambient s S T inputs fun p => (outputs p).liftQueries.{u, w', uJ, wJ} :=
  V.mapOutputs fun p => OracleMap.liftQueries (outputs p)

/-- Export the original outputs of a verifier whose outputs have lifted queries. -/
abbrev lowerOutputs
    (V : OracleVerifier ambient s S T inputs fun p => (outputs p).liftQueries.{u, w', uJ, wJ}) :
    OracleVerifier ambient s S T inputs outputs :=
  V.mapOutputs fun p => OracleMap.lowerQueries (outputs p)

/-- Lifting the input queries keeps the decision on the same data. -/
theorem liftInputs_decideWith (V : OracleVerifier ambient s S T inputs outputs) (stmt : S)
    (p : Path s) (v : View s p) (data : (pathResources inputs s p).Data) :
    (V.liftInputs.{u, w', uι, uI, uJ, uS, wI, wJ}).decideWith stmt p v data =
      V.decideWith stmt p v data :=
  V.comapInputs_decideWith (OracleMap.lowerQueries inputs) stmt p v data

/-- Lifting the input queries keeps the output data of the same data. -/
theorem liftInputs_outputData (V : OracleVerifier ambient s S T inputs outputs) (stmt : S)
    (p : Path s) (v : View s p) (data : (pathResources inputs s p).Data) :
    ((V.liftInputs.{u, w', uι, uI, uJ, uS, wI, wJ}).outputMap stmt p v).f data =
      (V.outputMap stmt p v).f data := rfl

/-- Lifting the output queries keeps the output data. -/
theorem liftOutputs_outputData (V : OracleVerifier ambient s S T inputs outputs) (stmt : S)
    (p : Path s) (v : View s p) (data : (pathResources inputs s p).Data) :
    ((V.liftOutputs.{u, w', uι, uI, uJ, uS, wI, wJ}).outputMap stmt p v).f data =
      (V.outputMap stmt p v).f data := rfl

/-- Lowering the output queries keeps the output data. -/
theorem lowerOutputs_outputData
    (V : OracleVerifier ambient s S T inputs fun p => (outputs p).liftQueries.{u, w', uJ, wJ})
    (stmt : S) (p : Path s) (v : View s p) (data : (pathResources inputs s p).Data) :
    ((lowerOutputs V).outputMap stmt p v).f data = (V.outputMap stmt p v).f data := rfl

end Adapters

/-- Reading the inputs through an oracle map runs as the original verifier on the mapped input
data. -/
theorem comapInputs_run {ι : Type u} {ambient : OracleSpec.{u, u} ι} {s : OracleProtocol.{u}}
    {S : Type uS} {T : Path s → Type u} {I : Type uI} {A : I → Type u} {I' : Type uI'}
    {A' : I' → Type u} {inputs : OracleFamily.{uI, u, wI} I A}
    {inputs' : OracleFamily.{uI', u, wI'} I' A'} {J : Path s → Type u}
    {B : (p : Path s) → J p → Type u} {outputs : (p : Path s) → OracleFamily.{u, u, wJ} (J p) (B p)}
    {Out : PathAlong oracleSig s → Type u}
    (V : OracleVerifier ambient s S T inputs outputs)
    (r : OracleMap (Resources.ofFamily inputs') (Resources.ofFamily inputs)) (stmt : S)
    (data : ∀ i, A' i) (prover : Prover oracleSig ambient s Out) :
    (V.comapInputs r).run stmt data prover = V.run stmt (r.f data) prover := by
  unfold OracleVerifier.run
  refine _root_.bind_congr fun z => ?_
  obtain ⟨tr, out, _⟩ := z
  change (simulateQ _ (OptionT.mk (simulateQ ((r.par (OracleMap.id _)).withAmbient ambient)
    (V.decide stmt _ _).run)).run >>= _) = _
  rw [OptionT.run_mk, OracleMap.simulate_withAmbient_addLift]
  rfl

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

/-! ## Chains of stages -/

/-- The plan of a finite chain of passive oracle verifiers from the input statement type `S` and
the input oracle family `inputs`.

`nil` is the empty chain. `cons s V draw rest` runs the protocol `s`, whose challenges are answered
by `draw`, and then, at each shape path `p` of `s`, the chain `rest p`. The verifier `V` accepts a
statement of type `T p` with the oracle family `middle p`, which are the inputs of `rest p`.
Statement types and index types live in the computation universe `u`, and every oracle family of
the chain has its queries in one universe `w`. `Stages.Compatibility` gives the evidence that
composes the verifiers. -/
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
  | .cons s _ _ rest => s.append fun p => (rest p).protocol

/-- The composed output statement type at a shape path: the input statement type for no stages,
and otherwise the output of the remaining stages at the split path. -/
def Out {S : Type u} {I : Type u} {A : I → Type u} {inputs : OracleFamily.{u, u, w} I A} :
    (c : Stages ambient S inputs) → Path c.protocol → Type u
  | .nil _, _ => S
  | .cons _ _ _ rest, p =>
    splitFamily (s₂ := fun p => (rest p).protocol) (fun p₁ => (rest p₁).Out) p

/-- The index type of the composed output oracle family at a shape path. -/
def OutIdx {S : Type u} {I : Type u} {A : I → Type u} {inputs : OracleFamily.{u, u, w} I A} :
    (c : Stages ambient S inputs) → Path c.protocol → Type u
  | .nil (I := I) _, _ => I
  | .cons _ _ _ rest, p =>
    splitFamily (s₂ := fun p => (rest p).protocol) (fun p₁ => (rest p₁).OutIdx) p

/-- The data types of the composed output oracle family at a shape path. -/
def OutData {S : Type u} {I : Type u} {A : I → Type u} {inputs : OracleFamily.{u, u, w} I A} :
    (c : Stages ambient S inputs) → (p : Path c.protocol) → c.OutIdx p → Type u
  | .nil (A := A) _, _ => A
  | .cons s _ _ rest, p =>
    (rest (Path.split s (fun p => (rest p).protocol) p).1).OutData
      (Path.split s (fun p => (rest p).protocol) p).2

/-- The composed output oracle family at a shape path: the inputs for no stages, and otherwise the
output family of the remaining stages at the split path. -/
def outputs {S : Type u} {I : Type u} {A : I → Type u} {inputs : OracleFamily.{u, u, w} I A} :
    (c : Stages ambient S inputs) → (p : Path c.protocol) →
      OracleFamily.{u, u, w} (c.OutIdx p) (c.OutData p)
  | .nil inputs, _ => inputs
  | .cons s _ _ rest, p =>
    (rest (Path.split s (fun p => (rest p).protocol) p).1).outputs
      (Path.split s (fun p => (rest p).protocol) p).2

/-- The verifier of no stages: it accepts the input statement and exports the inputs. -/
def nilVerifier {S : Type u} {I : Type u} {A : I → Type u} (inputs : OracleFamily.{u, u, w} I A) :
    OracleVerifier ambient (nil (ambient := ambient) (S := S) inputs).protocol S
      (nil (ambient := ambient) (S := S) inputs).Out inputs
      (nil (ambient := ambient) (S := S) inputs).outputs where
  decide stmt _ _ := pure stmt
  outputMap _ _ _ := OracleMap.fst _ _

/-- The evidence type of a chain together with the composed verifier it determines. For no stages
there is no evidence. For a first stage, the evidence is evidence for the remaining stages at each
shape path and a compatibility certificate between the first stage's verifier and the composed
verifiers of the rest; the composed verifier is their binary append. -/
def compose {S : Type u} {I : Type u} {A : I → Type u} {inputs : OracleFamily.{u, u, w} I A} :
    (c : Stages ambient S inputs) →
      (E : Type (max (u + 1) w)) × (E → OracleVerifier ambient c.protocol S c.Out inputs c.outputs)
  | .nil inputs => ⟨PUnit, fun _ => nilVerifier inputs⟩
  | .cons _ V _ rest =>
    ⟨(e : ∀ p, (rest p).compose.1) ×
        OracleVerifier.OutputCompatibility V fun p => (rest p).compose.2 (e p),
      fun e => V.append (s₂ := fun p => (rest p).protocol)
        (fun p => (rest p).compose.2 (e.1 p)) e.2⟩

/-- The evidence that composes a chain: an output compatibility certificate at every stage
boundary. -/
abbrev Compatibility {S : Type u} {I : Type u} {A : I → Type u}
    {inputs : OracleFamily.{u, u, w} I A} (c : Stages ambient S inputs) : Type (max (u + 1) w) :=
  c.compose.1

/-- The composed passive oracle verifier of a chain with its compatibility evidence. -/
def verifier {S : Type u} {I : Type u} {A : I → Type u} {inputs : OracleFamily.{u, u, w} I A}
    (c : Stages ambient S inputs) (e : c.Compatibility) :
    OracleVerifier ambient c.protocol S c.Out inputs c.outputs :=
  c.compose.2 e

/-- The composed challenge implementation, which combines the stages' draws along the shape path
of the earlier stages. -/
def draw {S : Type u} {I : Type u} {A : I → Type u} {inputs : OracleFamily.{u, u, w} I A} :
    (c : Stages ambient S inputs) → (ch : ChallengeNode oracleSig c.protocol) →
      OracleComp ambient (challengeSpec oracleSig c.protocol ch)
  | .nil _, ch => ch.val.elim
  | .cons s _ draw₁ rest, ch =>
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
    (c : Stages ambient S inputs) (e : c.Compatibility) (stmt : S) (data : ∀ i, A i)
    {Out : PathAlong oracleSig c.protocol → Type u}
    (prover : Prover oracleSig ambient c.protocol Out) :
    OracleComp ambient
      (Observation oracleSig c.protocol Out (OracleVerifier.Output c.Out c.OutData)) :=
  simulateQ c.handler ((c.verifier e).run stmt data prover)

/-! ## Statement-free output maps -/

/-- Output maps that do not read the input statement, for every stage of a chain: at a first
stage, a map with the equation that the stage's output map is that map at every statement, and
such maps for the remaining stages at each shape path. -/
def StatementFree {S : Type u} {I : Type u} {A : I → Type u}
    {inputs : OracleFamily.{u, u, w} I A} : Stages ambient S inputs → Type (max u w)
  | .nil _ => PUnit
  | @Stages.cons _ _ _ _ _ inputs s _ _ _ middle V _ rest =>
    (map : (p : Path s) → View s p →
        OracleMap (pathResources inputs s p) (Resources.ofFamily (middle p))) ×'
      (∀ stmt, V.outputMap stmt = map) ×' ∀ p, (rest p).StatementFree

/-- The composed output map of statement-free stage maps. For no stages it forwards the inputs;
otherwise it is `appendMap` of the first stage's map and the composed map of the rest. -/
def StatementFree.map {S : Type u} {I : Type u} {A : I → Type u}
    {inputs : OracleFamily.{u, u, w} I A} :
    (c : Stages ambient S inputs) → c.StatementFree → (p : Path c.protocol) →
      View c.protocol p →
        OracleMap (pathResources inputs c.protocol p) (Resources.ofFamily (c.outputs p))
  | .nil _, _, _, _ => OracleMap.fst _ _
  | .cons _ _ _ rest, m, p, v =>
    OracleVerifier.appendMap (s₂ := fun p => (rest p).protocol) m.1
      (fun p₁ => StatementFree.map (rest p₁) (m.2.2 p₁)) p v

/-- The compatibility evidence of statement-free stage maps, with the equation that the composed
verifier's output map is `StatementFree.map` at every statement. -/
def StatementFree.certify {S : Type u} {I : Type u} {A : I → Type u}
    {inputs : OracleFamily.{u, u, w} I A} :
    (c : Stages ambient S inputs) → (m : c.StatementFree) →
      {e : c.Compatibility // ∀ stmt, (c.verifier e).outputMap stmt = StatementFree.map c m}
  | .nil _, _ => ⟨⟨⟩, fun _ => rfl⟩
  | .cons _ V _ rest, m =>
    ⟨⟨fun p => (certify (rest p) (m.2.2 p)).1,
      OracleVerifier.OutputCompatibility.ofStatementFree V _ m.1 m.2.1
        (fun p => StatementFree.map (rest p) (m.2.2 p))
        fun p => (certify (rest p) (m.2.2 p)).2⟩, fun _ => rfl⟩

/-- The compatibility evidence of statement-free stage maps. -/
abbrev StatementFree.compatibility {S : Type u} {I : Type u} {A : I → Type u}
    {inputs : OracleFamily.{u, u, w} I A} {c : Stages ambient S inputs} (m : c.StatementFree) :
    c.Compatibility :=
  (StatementFree.certify c m).1

/-- With statement-free stage maps, the composed output map does not read the input statement. -/
theorem StatementFree.outputMap_eq {S : Type u} {I : Type u} {A : I → Type u}
    {inputs : OracleFamily.{u, u, w} I A} {c : Stages ambient S inputs} (m : c.StatementFree)
    (stmt : S) : (c.verifier m.compatibility).outputMap stmt = StatementFree.map c m :=
  (StatementFree.certify c m).2 stmt

section Laws

variable {S : Type u} {I : Type u} {A : I → Type u} {inputs : OracleFamily.{u, u, w} I A}
  (s : OracleProtocol.{u}) {T : Path s → Type u} {J : Path s → Type u}
  {B : (p : Path s) → J p → Type u}
  {middle : (p : Path s) → OracleFamily.{u, u, w} (J p) (B p)}
  (V : OracleVerifier ambient s S T inputs middle)
  (draw₁ : (c : ChallengeNode oracleSig s) → OracleComp ambient (challengeSpec oracleSig s c))
  (rest : (p : Path s) → Stages ambient (T p) (middle p))
  (e : (p : Path s) → (rest p).Compatibility)
  (compatible : OracleVerifier.OutputCompatibility V fun p => (rest p).verifier (e p))

/-- The composed protocol of a chain with a first stage. -/
@[simp] theorem protocol_cons :
    (cons s V draw₁ rest).protocol = s.append fun p => (rest p).protocol := rfl

/-- The composed verifier of a chain with a first stage is the binary append of that stage's
verifier and the composed verifiers of the rest, with the certificate of the evidence. -/
theorem verifier_cons :
    (cons s V draw₁ rest).verifier ⟨e, compatible⟩ =
      V.append (fun p => (rest p).verifier (e p)) compatible := rfl

/-- The composed draws of a chain with a first stage combine that stage's draws with the composed
draws of the rest. -/
theorem draw_cons :
    (cons s V draw₁ rest).draw =
      combineDraw oracleSig s (fun p => (rest p).protocol) draw₁ fun p => (rest p).draw := rfl

/-- The run of a chain with a first stage is the core run of the binary append of that stage's
verifier and the composed rest, with the challenges answered by the combined draws.
`OracleVerifier.run_append` splits it into the first stage's interaction, the rest's interaction,
the first decision and, after its acceptance only, the rest's decision. This is the split after
the first stage, not a split at an arbitrary stage. -/
theorem run_cons (stmt : S) (data : ∀ i, A i)
    {Out : PathAlong oracleSig (s.append fun p => (rest p).protocol) → Type u}
    (prover : Prover oracleSig ambient (s.append fun p => (rest p).protocol) Out) :
    (cons s V draw₁ rest).run ⟨e, compatible⟩ stmt data prover =
      simulateQ (QueryImpl.id' ambient +
          combineDraw oracleSig s (fun p => (rest p).protocol) draw₁ fun p => (rest p).draw)
        ((V.append (fun p => (rest p).verifier (e p)) compatible).run stmt data prover) := rfl

/-- A rejecting first decision makes the composed decision reject. The interactions of the
remaining stages have already run; only their decisions are skipped. -/
theorem decideWith_cons_of_reject (stmt : S) (p : Path (s.append fun p => (rest p).protocol))
    (v : View _ p) (data : (pathResources inputs (s.append fun p => (rest p).protocol) p).Data)
    (h : V.decideWith stmt (Path.split s _ p).1 (View.split s _ p v).1
      ((OracleVerifier.prefixRoute (inputs := inputs) p).f data) = pure none) :
    ((cons s V draw₁ rest).verifier ⟨e, compatible⟩).decideWith stmt p v data = pure none :=
  OracleVerifier.append_decideWith_of_reject V _ compatible stmt p v data h

end Laws

/-- With no stages, the composed decision accepts the input statement. -/
@[simp] theorem decideWith_nil {S : Type u} {I : Type u} {A : I → Type u}
    (inputs : OracleFamily.{u, u, w} I A) (e : (nil (ambient := ambient) (S := S)
      inputs).Compatibility) (stmt : S) (p : Path (nil (ambient := ambient) (S := S)
      inputs).protocol) (v : View _ p) (data : (pathResources inputs (nil (ambient := ambient)
        (S := S) inputs).protocol p).Data) :
    ((nil (ambient := ambient) (S := S) inputs).verifier e).decideWith stmt p v data =
      pure (some stmt) := by
  simp only [OracleVerifier.decideWith, verifier, compose, nilVerifier]
  exact simulateQ_pure _ _

/-- With no stages, the composed output data is the input data. -/
@[simp] theorem outputData_nil {S : Type u} {I : Type u} {A : I → Type u}
    (inputs : OracleFamily.{u, u, w} I A) (e : (nil (ambient := ambient) (S := S)
      inputs).Compatibility) (stmt : S) (p : Path (nil (ambient := ambient) (S := S)
      inputs).protocol) (v : View _ p) (data : (pathResources inputs (nil (ambient := ambient)
        (S := S) inputs).protocol p).Data) :
    (((nil (ambient := ambient) (S := S) inputs).verifier e).outputMap stmt p v).f data =
      data.1 := rfl

/-- A chain of one stage decides as that stage: its composed decision is the stage's decision at
the split path, on the data that `prefixRoute` selects. -/
theorem decideWith_one {S : Type u} {I : Type u} {A : I → Type u}
    {inputs : OracleFamily.{u, u, w} I A}
    (s : OracleProtocol.{u}) {T : Path s → Type u} {J : Path s → Type u}
    {B : (p : Path s) → J p → Type u}
    {middle : (p : Path s) → OracleFamily.{u, u, w} (J p) (B p)}
    (V : OracleVerifier ambient s S T inputs middle)
    (draw₁ : (c : ChallengeNode oracleSig s) → OracleComp ambient (challengeSpec oracleSig s c))
    (e : (p : Path s) → (nil (ambient := ambient) (S := T p) (middle p)).Compatibility)
    (compatible : OracleVerifier.OutputCompatibility V fun p =>
      (nil (ambient := ambient) (S := T p) (middle p)).verifier (e p))
    (stmt : S)
    (p : Path (s.append fun p => (nil (ambient := ambient) (S := T p) (middle p)).protocol))
    (v : View _ p) (data : (pathResources inputs
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

/-- A property at every stage boundary of a chain, given by `P` on the boundary statement type
and indexed by the shape paths of the stages up to that boundary. For a first stage, it is the
property at that stage's output at each of its shape paths and the properties of the remaining
stages there. The boundary before the first stage is not included. -/
def Boundaries (P : Type u → Type u) {S : Type u} {I : Type u} {A : I → Type u}
    {inputs : OracleFamily.{u, u, w} I A} : Stages ambient S inputs → Type u
  | .nil _ => PUnit
  | @Stages.cons _ _ _ _ _ _ s T _ _ _ _ _ rest =>
    ((p : Path s) → P (T p)) × ((p : Path s) → (rest p).Boundaries P)

/-- The property at the final boundary of a chain at a composed shape path: the entry property
for no stages, and otherwise the final property of the remaining stages at the split path. -/
def Boundaries.final {P : Type u → Type u} {S : Type u} {I : Type u} {A : I → Type u}
    {inputs : OracleFamily.{u, u, w} I A} :
    (c : Stages ambient S inputs) → P S → c.Boundaries P → (p : Path c.protocol) → P (c.Out p)
  | .nil _, pre, _, _ => pre
  | .cons s _ _ rest, _, b, p =>
    final (rest (Path.split s (fun p => (rest p).protocol) p).1)
      (b.1 (Path.split s (fun p => (rest p).protocol) p).1)
      (b.2 (Path.split s (fun p => (rest p).protocol) p).1)
      (Path.split s (fun p => (rest p).protocol) p).2

/-- Every stage decision deterministically accepts a statement satisfying the predicate after it,
from every input statement satisfying the predicate before it, at every shape path, view and
resource value. -/
def DeterministicSteps {S : Type u} {I : Type u} {A : I → Type u}
    {inputs : OracleFamily.{u, u, w} I A} :
    (c : Stages ambient S inputs) → (S → Prop) → c.Boundaries (· → Prop) → Prop
  | .nil _, _, _ => True
  | .cons _ V _ rest, pre, b =>
    (∀ stmt, pre stmt → ∀ p v data,
      ∃ mid, V.decideWith stmt p v data = pure (some mid) ∧ b.1 p mid) ∧
    ∀ p, (rest p).DeterministicSteps (b.1 p) (b.2 p)

/-- Every possible result of every stage decision is an accepted statement satisfying the
predicate after it, from every input statement satisfying the predicate before it, at every shape
path, view and resource value. -/
def SupportSteps {S : Type u} {I : Type u} {A : I → Type u}
    {inputs : OracleFamily.{u, u, w} I A} :
    (c : Stages ambient S inputs) → (S → Prop) → c.Boundaries (· → Prop) → Prop
  | .nil _, _, _ => True
  | .cons _ V _ rest, pre, b =>
    (∀ stmt, pre stmt → ∀ p v data, ∀ r ∈ support (V.decideWith stmt p v data),
      ∃ mid, r = some mid ∧ b.1 p mid) ∧
    ∀ p, (rest p).SupportSteps (b.1 p) (b.2 p)

/-- The deterministic chain law: if every stage decision deterministically accepts a statement
satisfying its boundary predicate, then the composed decision, the fold of the stage decisions
after all interactions, deterministically accepts a statement satisfying the final predicate. -/
theorem decideWith_accepts {S : Type u} {I : Type u} {A : I → Type u}
    {inputs : OracleFamily.{u, u, w} I A} :
    (c : Stages ambient S inputs) → (e : c.Compatibility) → (pre : S → Prop) →
      (b : c.Boundaries (· → Prop)) → c.DeterministicSteps pre b → (stmt : S) → pre stmt →
      (p : Path c.protocol) → (v : View c.protocol p) →
      (data : (pathResources inputs c.protocol p).Data) →
      ∃ out, (c.verifier e).decideWith stmt p v data = pure (some out) ∧
        Boundaries.final c pre b p out
  | .nil _, e, _, _, _, stmt, hstmt, p, v, data => ⟨stmt, decideWith_nil _ e stmt p v data, hstmt⟩
  | .cons s V _ rest, e, _, b, h, stmt, hstmt, p, v, data => by
    obtain ⟨mid, hmid, hpred⟩ := h.1 stmt hstmt (Path.split s _ p).1 (View.split s _ p v).1
      ((OracleVerifier.prefixRoute (inputs := inputs) p).f data)
    obtain ⟨out, hout, hfinal⟩ := decideWith_accepts (rest (Path.split s _ p).1)
      (e.1 (Path.split s _ p).1) (b.1 (Path.split s _ p).1) (b.2 (Path.split s _ p).1)
      (h.2 (Path.split s _ p).1) mid hpred (Path.split s _ p).2 (View.split s _ p v).2
      ((OracleVerifier.suffixRoute V stmt p v).f data)
    exact ⟨out, OracleVerifier.append_decideWith_of_accept V _ e.2 stmt p v data mid out
      hmid hout, hfinal⟩

/-- The support chain law: if every possible result of every stage decision is an accepted
statement satisfying its boundary predicate, then every possible result of the composed decision,
the fold of the stage decisions after all interactions, is an accepted statement satisfying the
final predicate. -/
theorem decideWith_preserves_support {S : Type u} {I : Type u} {A : I → Type u}
    {inputs : OracleFamily.{u, u, w} I A} :
    (c : Stages ambient S inputs) → (e : c.Compatibility) → (pre : S → Prop) →
      (b : c.Boundaries (· → Prop)) → c.SupportSteps pre b → (stmt : S) → pre stmt →
      (p : Path c.protocol) → (v : View c.protocol p) →
      (data : (pathResources inputs c.protocol p).Data) →
      ∀ r ∈ support ((c.verifier e).decideWith stmt p v data),
        ∃ out, r = some out ∧ Boundaries.final c pre b p out
  | .nil _, e, _, _, _, stmt, hstmt, p, v, data => by
    intro r hr
    rw [decideWith_nil] at hr
    exact ⟨stmt, OracleComp.eq_of_mem_support_pure _ hr, hstmt⟩
  | .cons s V _ rest, e, _, b, h, stmt, hstmt, p, v, data =>
    OracleVerifier.append_decideWith_preserves_support V _ e.2 stmt p v data
      (b.1 (Path.split s _ p).1) _
      (h.1 stmt hstmt (Path.split s _ p).1 (View.split s _ p v).1
        ((OracleVerifier.prefixRoute (inputs := inputs) p).f data))
      fun mid hmid => decideWith_preserves_support (rest (Path.split s _ p).1)
        (e.1 (Path.split s _ p).1) (b.1 (Path.split s _ p).1) (b.2 (Path.split s _ p).1)
        (h.2 (Path.split s _ p).1) mid hmid (Path.split s _ p).2 (View.split s _ p v).2
        ((OracleVerifier.suffixRoute V stmt p v).f data)

/-- An event on a type with a discrete measurable structure, which the almost-sure chain law
carries at every stage boundary. -/
structure DiscreteEvent (α : Type u) where
  /-- The measurable structure. -/
  measurableSpace : MeasurableSpace α
  /-- Every set is measurable. -/
  discrete : @DiscreteMeasurableSpace α measurableSpace
  /-- The event. -/
  holds : α → Prop

/-- Every stage decision accepts a statement in the event after it almost surely, from every input
statement satisfying the predicate before it, at every shape path, view and resource value. Each
boundary event carries the measurable structure of its statement type. -/
def MeasureSteps [ambient.AnswerMeasure] {S : Type u} {I : Type u} {A : I → Type u}
    {inputs : OracleFamily.{u, u, w} I A} :
    (c : Stages ambient S inputs) → (S → Prop) → c.Boundaries DiscreteEvent → Prop
  | .nil _, _, _ => True
  | .cons _ V _ rest, pre, b =>
    (∀ stmt, pre stmt → ∀ p v data,
      letI := (b.1 p).measurableSpace
      𝒟[V.decideWith stmt p v data] {r | ∃ mid, r = some mid ∧ (b.1 p).holds mid} = 1) ∧
    ∀ p, (rest p).MeasureSteps (b.1 p).holds (b.2 p)

/-- The almost-sure chain law: if every stage decision accepts a statement in its boundary event
almost surely, then the composed decision, the fold of the stage decisions after all
interactions, accepts a statement in the final event almost surely. The ambient oracles carry an
answer measure; the boundary events carry the discrete measurable structures, and the entry event
`pre` gives the structure of the input statement type. -/
theorem decideWith_preserves_measure [ambient.AnswerMeasure] {S : Type u} {I : Type u}
    {A : I → Type u} {inputs : OracleFamily.{u, u, w} I A} :
    (c : Stages ambient S inputs) → (e : c.Compatibility) → (pre : DiscreteEvent S) →
      (b : c.Boundaries DiscreteEvent) → c.MeasureSteps pre.holds b → (stmt : S) →
      pre.holds stmt → (p : Path c.protocol) → (v : View c.protocol p) →
      (data : (pathResources inputs c.protocol p).Data) →
      letI := (Boundaries.final c pre b p).measurableSpace
      𝒟[(c.verifier e).decideWith stmt p v data]
        {r | ∃ out, r = some out ∧ (Boundaries.final c pre b p).holds out} = 1
  | .nil _, e, pre, _, _, stmt, hstmt, p, v, data => by
    have key : ∀ {α : Type u} (_ : MeasurableSpace α) (x : OracleComp ambient (Option α)) (a : α)
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
    exact OracleVerifier.append_decideWith_preserves_measure V _ e.2 stmt p v data
      (b.1 (Path.split s _ p).1).holds _
      (h.1 stmt hstmt (Path.split s _ p).1 (View.split s _ p v).1
        ((OracleVerifier.prefixRoute (inputs := inputs) p).f data))
      fun mid hmid => decideWith_preserves_measure (rest (Path.split s _ p).1)
        (e.1 (Path.split s _ p).1) (b.1 (Path.split s _ p).1) (b.2 (Path.split s _ p).1)
        (h.2 (Path.split s _ p).1) mid hmid (Path.split s _ p).2 (View.split s _ p v).2
        ((OracleVerifier.suffixRoute V stmt p v).f data)

end Stages

end Interaction.Core

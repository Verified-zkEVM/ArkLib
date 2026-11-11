/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Interaction.Core.OracleVerifier
public import PolyFun.Interaction.TwoParty.Lens.Compose

/-!
# Sequential interaction

Prover composition constructs the suffix in the prefix leaf action. Samplers combine without
running decisions at the seam. Decisions fold only after the whole interaction. Oracle routing
uses the prefix output map, and the composed decision equals the prefix decision followed by the
suffix decision on routed data. Closure of output maps requires an explicit compatibility
certificate for the intermediate statements the prefix decision can accept, because that decision
may depend on ambient queries.
-/

@[expose] public section

universe u uA

namespace Interaction.Core
open PFunctor FreeM TwoParty.Lens OracleComp Oracle

attribute [local implicit_reducible] projectPathAlong projectPathAlongLocalMap
  Displayed.LocalMap.toHom Displayed.LocalMap.toHomFun owner Node Node.position challengeSpec

-- `Fiber`, `project_split` and `splitFiber` are generic in the polynomial and the lens; they are
-- candidates for PolyFun's path ledger, with `View.split` and `PlainView.split` remaining here.

/-- A transcript over a fixed shape, for any interaction signature. -/
abbrev Fiber {P : PFunctor.{uA, u}} (l : PFunctor.Lens P rolePoly.{u})
    (s : FreeM P PUnit.{u + 1}) (p : Path s) :=
  {tr : PathAlong l s // projectPathAlong l s tr = p}

/-- Projection commutes with the prefix decomposition of a full transcript. -/
theorem project_split {P : PFunctor.{uA, u}} (l : PFunctor.Lens P rolePoly.{u})
    (s₁ : FreeM P PUnit.{u + 1}) (s₂ : Path s₁ → FreeM P PUnit.{u + 1})
    (tr : PathAlong l (s₁.append s₂)) :
    (let z := PathAlong.split l s₁ s₂ tr
     (⟨projectPathAlong l s₁ z.1, projectPathAlong l _ z.2⟩ :
       (p : Path s₁) × Path (s₂ p))) =
      Path.split s₁ s₂ (projectPathAlong l (s₁.append s₂) tr) := by
  let z := PathAlong.split l s₁ s₂ tr
  have h := congrArg (Path.split s₁ s₂)
    (PathAlong.projectPathAlong_append l s₁ s₂ z.1 z.2)
  simpa only [z, PathAlong.append_split, Path.split_append] using h.symm

/-- Split views along the shape split. Only the view transcripts are transported. -/
def splitFiber {P : PFunctor.{uA, u}} (l : PFunctor.Lens P rolePoly.{u})
    (s₁ : FreeM P PUnit.{u + 1}) (s₂ : Path s₁ → FreeM P PUnit.{u + 1})
    (p : Path (s₁.append s₂)) (v : Fiber l (s₁.append s₂) p) :
    Fiber l s₁ (Path.split s₁ s₂ p).1 ×
      Fiber l (s₂ (Path.split s₁ s₂ p).1) (Path.split s₁ s₂ p).2 := by
  rcases v with ⟨tr, rfl⟩
  let z := PathAlong.split l s₁ s₂ tr
  have h := project_split l s₁ s₂ tr
  exact h ▸ (show Fiber l s₁ (projectPathAlong l s₁ z.1) ×
    Fiber l (s₂ (projectPathAlong l s₁ z.1)) (projectPathAlong l _ z.2) from
      (⟨z.1, rfl⟩, ⟨z.2, rfl⟩))

/-- Split the oracle verifier's public view. -/
abbrev View.split := splitFiber viewSig

/-- Split a plain public transcript. -/
abbrev PlainView.split := splitFiber plainSig

/-- The output family of an appended protocol: at a path of the appended tree, the suffix's
output at the split path. PolyFun's `Path.LiftAppend` is the same family by `liftAppend_split`;
the split form lets a composed decision return the suffix's output without a transport. -/
abbrev splitFamily {P : PFunctor.{uA, u}} {s₁ : FreeM P PUnit.{u + 1}}
    {s₂ : Path s₁ → FreeM P PUnit.{u + 1}} (U : (p : Path s₁) → Path (s₂ p) → Type u)
    (p : Path (s₁.append s₂)) : Type u :=
  U (Path.split s₁ s₂ p).1 (Path.split s₁ s₂ p).2

/-- Plain terminal decisions fold after both interactions have finished. The prefix's output type
may depend on the prefix path, and the composite's output at an appended path is the suffix's
output at the split path. -/
def Verifier.append {ι : Type u} {ambient : OracleSpec.{u, u} ι}
    {s₁ : Protocol.{u}} {s₂ : Path s₁ → Protocol.{u}} {S : Type u} {T : Path s₁ → Type u}
    {U : (p : Path s₁) → Path (s₂ p) → Type u}
    (V₁ : Verifier ambient s₁ S T) (V₂ : (p : Path s₁) → Verifier ambient (s₂ p) (T p) (U p)) :
    Verifier ambient (s₁.append s₂) S (splitFamily U) where
  decide stmt p v := do
    let z := Path.split s₁ s₂ p
    let views := PlainView.split s₁ s₂ p v
    let mid ← V₁.decide stmt z.1 views.1
    (V₂ z.1).decide mid z.2 views.2

/-- The exact end-decided fold, including skipping the second decision on rejection. -/
theorem Verifier.append_decide {ι : Type u} {ambient : OracleSpec.{u, u} ι}
    {s₁ : Protocol.{u}} {s₂ : Path s₁ → Protocol.{u}} {S : Type u} {T : Path s₁ → Type u}
    {U : (p : Path s₁) → Path (s₂ p) → Type u}
    (V₁ : Verifier ambient s₁ S T) (V₂ : (p : Path s₁) → Verifier ambient (s₂ p) (T p) (U p))
    (stmt : S) (p : Path (s₁.append s₂)) (v : PlainView (s₁.append s₂) p) :
    (V₁.append V₂).decide stmt p v = (do
      let mid ← V₁.decide stmt (Path.split s₁ s₂ p).1 (PlainView.split s₁ s₂ p v).1
      (V₂ (Path.split s₁ s₂ p).1).decide mid (Path.split s₁ s₂ p).2
        (PlainView.split s₁ s₂ p v).2) := rfl

/-- Provers compose using PolyFun's effectful suffix constructor in the leaf action. -/
abbrev Prover.append := @Focal.compFlat

/-- The sampler of a concatenation, with its pure prefix end, uses counterpart append. -/
def appendSampler {P : PFunctor.{uA, u}} {l : PFunctor.Lens P rolePoly.{u}}
    {m : Type u → Type u} [Monad m]
    (s₁ : FreeM P PUnit.{u + 1}) (s₂ : Path s₁ → FreeM P PUnit.{u + 1})
    (draw₁ : (c : ChallengeNode l s₁) → m (challengeSpec l s₁ c))
    (draw₂ : (p : Path s₁) → (c : ChallengeNode l (s₂ p)) → m (challengeSpec l (s₂ p) c)) :
    Counterpart l m (s₁.append s₂) (fun _ => PUnit) :=
  Counterpart.appendFlat (samplerEnd l s₁ draw₁)
    (fun tr _ => sampler l _ (draw₂ (projectPathAlong l s₁ tr)))

/-- Combine challenge implementations using only the canonical prefix path. -/
def combineDraw {P : PFunctor.{uA, u}} (l : PFunctor.Lens P rolePoly.{u})
    {m : Type u → Type u} :
    (s₁ : FreeM P PUnit.{u + 1}) → (s₂ : Path s₁ → FreeM P PUnit.{u + 1}) →
    ((c : ChallengeNode l s₁) → m (challengeSpec l s₁ c)) →
    ((p : Path s₁) → (c : ChallengeNode l (s₂ p)) → m (challengeSpec l (s₂ p) c)) →
    (c : ChallengeNode l (s₁.append s₂)) → m (challengeSpec l (s₁.append s₂) c)
  | .pure _, _, _, draw₂, c => draw₂ ⟨⟩ c
  | .liftBind _ _, _, draw₁, _, ⟨.inl x, h⟩ => draw₁ ⟨.inl x, h⟩
  | .liftBind _ next, s₂, draw₁, draw₂, ⟨.inr ⟨b, c⟩, h⟩ =>
    combineDraw l (next b) (fun p => s₂ ⟨b, p⟩)
      (fun c => draw₁ ⟨.inr ⟨b, c.val⟩, c.property⟩)
      (fun p => draw₂ ⟨b, p⟩) ⟨c, h⟩

/-- Appending samplers equals sampling the appended tree with the combined implementation. -/
theorem appendSampler_eq {m : Type u → Type u} [Monad m] [LawfulMonad m]
    (s₁ : Protocol.{u}) (s₂ : Path s₁ → Protocol.{u})
    (draw₁ : (c : ChallengeNode plainSig s₁) → m (challengeSpec plainSig s₁ c))
    (draw₂ : (p : Path s₁) → (c : ChallengeNode plainSig (s₂ p)) →
      m (challengeSpec plainSig (s₂ p) c)) :
    appendSampler s₁ s₂ draw₁ draw₂ = sampler plainSig (s₁.append s₂)
      (combineDraw plainSig s₁ s₂ draw₁ draw₂) := by
  induction s₁ using FreeM.rec with
  | pure a => rfl
  | liftBind a next ih =>
    cases a <;>
      simp only [appendSampler, Counterpart.appendFlat, sampler, samplerEnd,
        FreeM.append_liftBind, PureEnd.graft, PureEnd.toStrategy, PureEnd.mapOutput,
        owner, plainSig, Choice, Move, Choice.map, combineDraw,
        LawfulApplicative.map_pure, Functor.map_map]
    · congr 1
      funext x
      exact ih x (fun p => s₂ ⟨x, p⟩)
        (fun c => draw₁ ⟨.inr ⟨x, c.val⟩, c.property⟩)
        (fun p => draw₂ ⟨x, p⟩)
    · congr 1
      funext x
      congr 1
      exact ih PUnit.unit (fun p => s₂ ⟨PUnit.unit, p⟩)
        (fun c => draw₁ ⟨.inr ⟨PUnit.unit, c.val⟩, c.property⟩)
        (fun p => draw₂ ⟨PUnit.unit, p⟩)

/-- Appending samplers equals sampling the appended tree with the combined implementation. -/
theorem appendOracleSampler_eq {m : Type u → Type u} [Monad m] [LawfulMonad m]
    (s₁ : OracleProtocol.{u}) (s₂ : Path s₁ → OracleProtocol.{u})
    (draw₁ : (c : ChallengeNode oracleSig s₁) → m (challengeSpec oracleSig s₁ c))
    (draw₂ : (p : Path s₁) → (c : ChallengeNode oracleSig (s₂ p)) →
      m (challengeSpec oracleSig (s₂ p) c)) :
    appendSampler s₁ s₂ draw₁ draw₂ = sampler oracleSig (s₁.append s₂)
      (combineDraw oracleSig s₁ s₂ draw₁ draw₂) := by
  induction s₁ using FreeM.rec with
  | pure a => rfl
  | liftBind a next ih =>
    cases a <;>
      simp only [appendSampler, Counterpart.appendFlat, sampler, samplerEnd,
        FreeM.append_liftBind, PureEnd.graft, PureEnd.toStrategy, PureEnd.mapOutput,
        owner, oracleSig, Choice, Move, Choice.map, combineDraw,
        LawfulApplicative.map_pure, Functor.map_map]
    · congr 1
      funext x
      exact ih x (fun p => s₂ ⟨x, p⟩)
        (fun c => draw₁ ⟨.inr ⟨x, c.val⟩, c.property⟩)
        (fun p => draw₂ ⟨x, p⟩)
    · congr 1
      funext x
      congr 1
      exact ih PUnit.unit (fun p => s₂ ⟨PUnit.unit, p⟩)
        (fun c => draw₁ ⟨.inr ⟨PUnit.unit, c.val⟩, c.property⟩)
        (fun p => draw₂ ⟨PUnit.unit, p⟩)
    · congr 1
      funext x
      exact ih PUnit.unit (fun p => s₂ ⟨PUnit.unit, p⟩)
        (fun c => draw₁ ⟨.inr ⟨PUnit.unit, c.val⟩, c.property⟩)
        (fun p => draw₂ ⟨PUnit.unit, p⟩)

/-- Composed execution preserves seam effects in their actual order. -/
theorem run_appendSampler {P : PFunctor.{uA, u}} {l : PFunctor.Lens P rolePoly.{u}}
    {m : Type u → Type u} [Monad m] [LawfulMonad m]
    {s₁ : FreeM P PUnit.{u + 1}} {s₂ : Path s₁ → FreeM P PUnit.{u + 1}}
    {Mid : PathAlong l s₁ → Type u} {Out : PathAlong l (s₁.append s₂) → Type u}
    (p : Focal l m s₁ Mid)
    (f : (tr : PathAlong l s₁) → Mid tr → m (Focal l m
      (s₂ (projectPathAlong l s₁ tr)) (fun tail => Out (PathAlong.append l s₁ s₂ tr tail))))
    (draw₁ : (c : ChallengeNode l s₁) → m (challengeSpec l s₁ c))
    (draw₂ : (p : Path s₁) → (c : ChallengeNode l (s₂ p)) → m (challengeSpec l (s₂ p) c)) :
    TwoParty.Lens.run (s₁.append s₂) (Prover.append p f) (appendSampler s₁ s₂ draw₁ draw₂) =
      (do
        let ⟨tr, mid, _⟩ ← TwoParty.Lens.run s₁ p (sampler l s₁ draw₁)
        let next ← f tr mid
        let ⟨tail, out, terminal⟩ ← TwoParty.Lens.run _ next
          (sampler l _ (draw₂ (projectPathAlong l s₁ tr)))
        pure ⟨PathAlong.append l s₁ s₂ tr tail, out, terminal⟩) :=
  run_compFlat_appendFlat p f (samplerEnd l s₁ draw₁) _

/-- An arbitrary composed prover splits with its actual continuation and private memory. -/
theorem run_splitSampler {P : PFunctor.{uA, u}} {l : PFunctor.Lens P rolePoly.{u}}
    {m : Type u → Type u} [Monad m] [LawfulMonad m]
    {s₁ : FreeM P PUnit.{u + 1}} {s₂ : Path s₁ → FreeM P PUnit.{u + 1}}
    {Out : PathAlong l (s₁.append s₂) → Type u}
    (p : Focal l m (s₁.append s₂) Out)
    (draw₁ : (c : ChallengeNode l s₁) → m (challengeSpec l s₁ c))
    (draw₂ : (p : Path s₁) → (c : ChallengeNode l (s₂ p)) → m (challengeSpec l (s₂ p) c)) :
    TwoParty.Lens.run (s₁.append s₂) p (appendSampler s₁ s₂ draw₁ draw₂) = (do
      let ⟨tr, next, _⟩ ← TwoParty.Lens.run s₁ (Focal.splitPrefix p) (sampler l s₁ draw₁)
      let ⟨tail, out, terminal⟩ ← TwoParty.Lens.run _ next
        (sampler l _ (draw₂ (projectPathAlong l s₁ tr)))
      pure ⟨PathAlong.append l s₁ s₂ tr tail, out, terminal⟩) :=
  run_appendFlat_splitPrefix p (samplerEnd l s₁ draw₁) _

/-- Split the oracle resources of an arbitrary completed appended path. -/
def splitOracles : (s₁ : OracleProtocol.{u}) → (s₂ : Path s₁ → OracleProtocol.{u}) →
    (p : Path (s₁.append s₂)) →
    OracleMap (pathFamily (s₁.append s₂) p)
      (sumFamily (pathFamily s₁ (Path.split s₁ s₂ p).1)
        (pathFamily (s₂ (Path.split s₁ s₂ p).1) (Path.split s₁ s₂ p).2))
  | .pure _, s₂, p => oracles_split (.pure ⟨⟩) s₂ ⟨⟩ p
  | .liftBind (.message _) next, s₂, ⟨x, p⟩ =>
    splitOracles (next x) (fun q => s₂ ⟨x, q⟩) p
  | .liftBind (.challenge _) next, s₂, ⟨x, p⟩ =>
    splitOracles (next x) (fun q => s₂ ⟨x, q⟩) p
  | .liftBind (.oracle _ I) next, s₂, ⟨x, p⟩ =>
    (OracleMap.unassoc (singletonFamily I)
      (pathFamily (next x) (Path.split (next x) (fun q => s₂ ⟨x, q⟩) p).1)
      (pathFamily _ (Path.split (next x) (fun q => s₂ ⟨x, q⟩) p).2)).comp
      ((OracleMap.embedding (singletonFamily I) id).sum
        (splitOracles (next x) (fun q => s₂ ⟨x, q⟩) p))

/-- Preserve ambient queries while routing resource queries through an oracle map. -/
def OracleMap.withAmbient {ι I J : Type u} (ambient : OracleSpec.{u, u} ι)
    {A : I → Type u} {B : J → Type u}
    {In : OracleFamily.{u, u, u} I A} {Out : OracleFamily.{u, u, u} J B}
    (route : OracleMap In Out) : QueryImpl (ambient + Out.spec) (OracleComp (ambient + In.spec))
  | .inl q => liftM ((ambient + In.spec).query (.inl q))
  | .inr q => simulateQ
    (fun r => liftM ((ambient + In.spec).query (.inr r))) (route.impl q)

/-- Routing through a map and answering from data agrees with answering from the mapped data. -/
theorem OracleMap.simulate_withAmbient {ι I J : Type u} {ambient : OracleSpec.{u, u} ι}
    {A : I → Type u} {B : J → Type u}
    {In : OracleFamily.{u, u, u} I A} {Out : OracleFamily.{u, u, u} J B}
    (route : OracleMap In Out) (x : ∀ i, A i) {α : Type u}
    (program : OracleComp (ambient + Out.spec) α) :
    simulateQ (QueryImpl.addLift (QueryImpl.id' ambient) (In.behaviorOfRealizations x) :
        QueryImpl (ambient + In.spec) (OracleComp ambient))
        (simulateQ (route.withAmbient ambient) program) =
      simulateQ (QueryImpl.addLift (QueryImpl.id' ambient)
        (Out.behaviorOfRealizations (route.f x)) :
        QueryImpl (ambient + Out.spec) (OracleComp ambient)) program := by
  refine QueryImpl.simulateQ_simulateQ_eq_of_apply (fun q => ?_) program
  rcases q with q | q
  · simp [OracleMap.withAmbient]
  · simp only [OracleMap.withAmbient, QueryImpl.addLift_def, QueryImpl.liftTarget_self]
    rw [QueryImpl.simulateQ_simulateQ_eq_of_apply
      (impl := (In.behaviorOfRealizations x).liftTarget (OracleComp ambient))
      (fun r => QueryImpl.simulateQ_add_query_right _ _ r), simulateQ_liftTarget, route.law]
    rfl

namespace OracleVerifier
variable {ι I : Type u} {ambient : OracleSpec.{u, u} ι} {A : I → Type u}
  {inputs : OracleFamily.{u, u, u} I A}
  {s₁ : OracleProtocol.{u}} {s₂ : Path s₁ → OracleProtocol.{u}} {S : Type u}
  {T : Path s₁ → Type u} {U : (p : Path s₁) → Path (s₂ p) → Type u}
  {J : Path s₁ → Type u} {B : (p : Path s₁) → J p → Type u}
  {middle : (p : Path s₁) → OracleFamily.{u, u, u} (J p) (B p)}
  {K : (p : Path s₁) → Path (s₂ p) → Type u}
  {C : (p₁ : Path s₁) → (p₂ : Path (s₂ p₁)) → K p₁ p₂ → Type u}
  {outputs : (p₁ : Path s₁) → (p₂ : Path (s₂ p₁)) → OracleFamily.{u, u, u} (K p₁ p₂) (C p₁ p₂)}

/-- Reassociate inputs and both sets of messages into prefix resources and suffix messages. -/
def resources (p : Path (s₁.append s₂)) :=
  (OracleMap.unassoc inputs (pathFamily s₁ (Path.split s₁ s₂ p).1)
    (pathFamily _ (Path.split s₁ s₂ p).2)).comp
    ((OracleMap.embedding inputs id).sum (splitOracles s₁ s₂ p))

/-- Prefix decisions see the original inputs and only prefix messages. -/
def prefixRoute (p : Path (s₁.append s₂)) :=
  (OracleMap.embedding _ Sum.inl).comp (resources (inputs := inputs) p)

/-- Suffix input queries use the prefix map at the prefix path; suffix message queries retain
their own slots. -/
def suffixRoute (V₁ : OracleVerifier ambient s₁ S T inputs middle)
    (stmt : S) (p : Path (s₁.append s₂)) (v : View (s₁.append s₂) p) :=
  ((V₁.outputMap stmt (Path.split s₁ s₂ p).1 (View.split s₁ s₂ p v).1).sum
    (OracleMap.embedding (pathFamily _ (Path.split s₁ s₂ p).2) id)).comp
      (resources (inputs := inputs) p)

/-- The output oracle family of an appended oracle protocol: at a path of the appended tree, the
suffix's output family at the split path. -/
abbrev splitOutputs
    (outputs : (p₁ : Path s₁) → (p₂ : Path (s₂ p₁)) → OracleFamily.{u, u, u} (K p₁ p₂) (C p₁ p₂))
    (p : Path (s₁.append s₂)) :
    OracleFamily.{u, u, u} (splitFamily K p)
      (C (Path.split s₁ s₂ p).1 (Path.split s₁ s₂ p).2) :=
  outputs (Path.split s₁ s₂ p).1 (Path.split s₁ s₂ p).2

/-- A composite output map must represent every intermediate statement the prefix can accept.

The condition concerns the actual prefix decision on the same view, with its resource queries
answered from the routed input data and every ambient answer allowed. Statements the prefix cannot
return impose no condition. The condition is still needed because the prefix decision can query
ambient oracles, whereas output maps cannot.
-/
structure OutputCompatibility (V₁ : OracleVerifier ambient s₁ S T inputs middle)
    (V₂ : (p : Path s₁) → OracleVerifier ambient (s₂ p) (T p) (U p) (middle p) (outputs p)) where
  /-- The composite output map, which sees only the statement, the path and the view. -/
  outputMap : S → (p : Path (s₁.append s₂)) → View (s₁.append s₂) p →
    OracleMap (sumFamily inputs (pathFamily (s₁.append s₂) p)) (splitOutputs outputs p)
  /-- On every accepted intermediate statement it agrees with the suffix's map after routing. -/
  agrees : ∀ stmt p v data mid,
    some mid ∈ support (V₁.decideWith stmt (Path.split s₁ s₂ p).1 (View.split s₁ s₂ p v).1
      ((prefixRoute (inputs := inputs) p).f data)) →
    (outputMap stmt p v).f data =
      ((V₂ (Path.split s₁ s₂ p).1).outputMap mid (Path.split s₁ s₂ p).2
        (View.split s₁ s₂ p v).2).f ((suffixRoute V₁ stmt p v).f data)

/-- Compatibility from a public intermediate statement that every accepted prefix result equals. -/
def OutputCompatibility.ofStatement (V₁ : OracleVerifier ambient s₁ S T inputs middle)
    (V₂ : (p : Path s₁) → OracleVerifier ambient (s₂ p) (T p) (U p) (middle p) (outputs p))
    (mid : S → (p : Path (s₁.append s₂)) → View (s₁.append s₂) p → T (Path.split s₁ s₂ p).1)
    (accepted : ∀ stmt p v data t,
      some t ∈ support (V₁.decideWith stmt (Path.split s₁ s₂ p).1 (View.split s₁ s₂ p v).1
        ((prefixRoute (inputs := inputs) p).f data)) → t = mid stmt p v) :
    OutputCompatibility V₁ V₂ where
  outputMap stmt p v :=
    ((V₂ (Path.split s₁ s₂ p).1).outputMap (mid stmt p v) (Path.split s₁ s₂ p).2
      (View.split s₁ s₂ p v).2).comp (suffixRoute V₁ stmt p v)
  agrees stmt p v data t h := by
    rw [accepted stmt p v data t h]
    rfl

/-- Fold passive decisions at the end, routing all suffix resource queries through the prefix.
The composite's output statement and output oracle family at an appended path are the suffix's
at the split path. -/
def append (V₁ : OracleVerifier ambient s₁ S T inputs middle)
    (V₂ : (p : Path s₁) → OracleVerifier ambient (s₂ p) (T p) (U p) (middle p) (outputs p))
    (compatible : OutputCompatibility V₁ V₂) :
    OracleVerifier ambient (s₁.append s₂) S (splitFamily U) inputs
      (splitOutputs outputs) where
  decide stmt p v := OptionT.mk do
    let z := Path.split s₁ s₂ p
    let views := View.split s₁ s₂ p v
    let mid ← simulateQ ((prefixRoute (inputs := inputs) p).withAmbient ambient)
      (V₁.decide stmt z.1 views.1).run
    match mid with
    | none => pure none
    | some mid => do
      simulateQ ((suffixRoute V₁ stmt p v).withAmbient ambient)
        ((V₂ z.1).decide mid z.2 views.2).run
  outputMap := compatible.outputMap

/-- The composed decision is the prefix decision followed by the suffix decision on routed data.

Ambient queries keep their order: those of the prefix decision precede those of the suffix.
-/
theorem append_decideWith (V₁ : OracleVerifier ambient s₁ S T inputs middle)
    (V₂ : (p : Path s₁) → OracleVerifier ambient (s₂ p) (T p) (U p) (middle p) (outputs p))
    (compatible : OutputCompatibility V₁ V₂) (stmt : S) (p : Path (s₁.append s₂))
    (v : View (s₁.append s₂) p)
    (data : ∀ i, (sumFamily inputs (pathFamily (s₁.append s₂) p)).Realization i) :
    (V₁.append V₂ compatible).decideWith stmt p v data =
      V₁.decideWith stmt (Path.split s₁ s₂ p).1 (View.split s₁ s₂ p v).1
          ((prefixRoute (inputs := inputs) p).f data) >>= fun
        | none => pure none
        | some mid => (V₂ (Path.split s₁ s₂ p).1).decideWith mid (Path.split s₁ s₂ p).2
            (View.split s₁ s₂ p v).2 ((suffixRoute V₁ stmt p v).f data) := by
  simp only [decideWith, append, OptionT.run_mk, simulateQ_bind]
  congr 1
  · exact OracleMap.simulate_withAmbient _ _ _
  · funext mid
    cases mid with
    | none => simp
    | some mid => exact OracleMap.simulate_withAmbient _ _ _

end OracleVerifier
end Interaction.Core

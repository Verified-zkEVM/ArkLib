/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Interaction.Core.Composition

/-!
# Routing an appended oracle run

Running a composed passive oracle verifier against an arbitrary prover of the appended protocol
splits into the prefix interaction and the suffix interaction, then the prefix decision on the
data that `prefixRoute` selects, then, after a prefix acceptance only, the suffix decision on the
data that `suffixRoute` selects. The returned output data is the composite output map applied to
the inputs and all payloads of the same run. The statement is an equality of open oracle
programs, so the order of ambient and challenge queries is preserved exactly.

In an appended run, the prefix decision's resources are the inputs and the payloads of the
prefix transcript alone.
-/

@[expose] public section

universe u uA

namespace Interaction.Core
open PFunctor FreeM TwoParty.Lens OracleComp Oracle

/-- Routing through a map and answering from data agrees with answering from the mapped data,
for any interpretation of the ambient queries. -/
theorem OracleMap.simulate_withAmbient_addLift {ι κ I J : Type u}
    {ambient : OracleSpec.{u, u} ι} {full : OracleSpec.{u, u} κ}
    {A : I → Type u} {B : J → Type u}
    {In : OracleFamily.{u, u, u} I A} {Out : OracleFamily.{u, u, u} J B}
    (lift : QueryImpl ambient (OracleComp full)) (route : OracleMap In Out) (x : ∀ i, A i)
    {α : Type u} (program : OracleComp (ambient + Out.spec) α) :
    simulateQ (QueryImpl.addLift lift (In.behaviorOfRealizations x) :
        QueryImpl (ambient + In.spec) (OracleComp full))
        (simulateQ (route.withAmbient ambient) program) =
      simulateQ (QueryImpl.addLift lift (Out.behaviorOfRealizations (route.f x)) :
        QueryImpl (ambient + Out.spec) (OracleComp full)) program := by
  refine QueryImpl.simulateQ_simulateQ_eq_of_apply (fun q => ?_) program
  rcases q with q | q
  · simp [OracleMap.withAmbient]
  · simp only [OracleMap.withAmbient, QueryImpl.addLift_def]
    rw [QueryImpl.simulateQ_simulateQ_eq_of_apply
      (impl := (In.behaviorOfRealizations x).liftTarget (OracleComp full))
      (fun r => QueryImpl.simulateQ_add_query_right _ _ r), simulateQ_liftTarget, route.law]
    rfl

/-- Component paths of an appended protocol with data for both component oracle families. -/
abbrev SplitData (s₁ : OracleProtocol.{u}) (s₂ : Path s₁ → OracleProtocol.{u}) :=
  (z : (p : Path s₁) × Path (s₂ p)) ×
    (∀ i, (sumFamily (pathFamily s₁ z.1) (pathFamily (s₂ z.1) z.2)).Realization i)

/-- Splitting the oracles of an appended path recovers the routed component data. -/
theorem splitOracles_append : (s₁ : OracleProtocol.{u}) →
    (s₂ : Path s₁ → OracleProtocol.{u}) → (p₁ : Path s₁) → (p₂ : Path (s₂ p₁)) →
    (x : ∀ i, OracleData (s₁.append s₂) (Path.append s₁ s₂ p₁ p₂) i) →
    (⟨Path.split s₁ s₂ (Path.append s₁ s₂ p₁ p₂),
      (splitOracles s₁ s₂ (Path.append s₁ s₂ p₁ p₂)).f x⟩ : SplitData s₁ s₂) =
      ⟨⟨p₁, p₂⟩, (oracles_split s₁ s₂ p₁ p₂).f x⟩
  | .pure _, _, ⟨⟩, _, _ => rfl
  | .liftBind (.message X) next, s₂, ⟨b, p₁⟩, p₂, x =>
    congrArg (fun z : SplitData (next b) (fun p => s₂ ⟨b, p⟩) =>
      (⟨⟨⟨b, z.1.1⟩, z.1.2⟩, z.2⟩ : SplitData (.liftBind (.message X) next) s₂))
      (splitOracles_append (next b) (fun p => s₂ ⟨b, p⟩) p₁ p₂ x)
  | .liftBind (.challenge X) next, s₂, ⟨b, p₁⟩, p₂, x =>
    congrArg (fun z : SplitData (next b) (fun p => s₂ ⟨b, p⟩) =>
      (⟨⟨⟨b, z.1.1⟩, z.1.2⟩, z.2⟩ : SplitData (.liftBind (.challenge X) next) s₂))
      (splitOracles_append (next b) (fun p => s₂ ⟨b, p⟩) p₁ p₂ x)
  | .liftBind (.oracle X I) next, s₂, ⟨b, p₁⟩, p₂, x => by
    have ih := congrArg (fun z : SplitData (next b) (fun p => s₂ ⟨b, p⟩) =>
      (⟨⟨⟨b, z.1.1⟩, z.1.2⟩, sumData (sumData (fun i => x (.inl i))
          (fun j => z.2 (.inl j))) (fun k => z.2 (.inr k))⟩ :
        SplitData (.liftBind (.oracle X I) next) s₂))
      (splitOracles_append (next b) (fun p => s₂ ⟨b, p⟩) p₁ p₂ (fun j => x (.inr j)))
    refine Eq.trans ?_ (ih.trans ?_)
    · refine Sigma.ext rfl (heq_of_eq ?_)
      funext i
      rcases i with (i | i) | i <;> rfl
    · refine Sigma.ext rfl (heq_of_eq ?_)
      funext i
      rcases i with (i | i) | i <;> rfl

/-- In an appended run, the payloads routed to either component are that component's own. -/
theorem splitOracles_payloads (s₁ : OracleProtocol.{u}) (s₂ : Path s₁ → OracleProtocol.{u})
    (tr₁ : PathAlong oracleSig s₁)
    (tr₂ : PathAlong oracleSig (s₂ (projectPathAlong oracleSig s₁ tr₁))) :
    (⟨Path.split s₁ s₂
        (projectPathAlong oracleSig _ (PathAlong.append oracleSig s₁ s₂ tr₁ tr₂)),
      (splitOracles s₁ s₂
        (projectPathAlong oracleSig _ (PathAlong.append oracleSig s₁ s₂ tr₁ tr₂))).f
        (payloads _ (PathAlong.append oracleSig s₁ s₂ tr₁ tr₂))⟩ : SplitData s₁ s₂) =
      ⟨⟨projectPathAlong oracleSig s₁ tr₁, projectPathAlong oracleSig _ tr₂⟩,
        sumData (payloads s₁ tr₁) (payloads _ tr₂)⟩ := by
  have h := congrArg (fun d : PathData (s₁.append s₂) =>
      (⟨Path.split s₁ s₂ d.1, (splitOracles s₁ s₂ d.1).f d.2⟩ : SplitData s₁ s₂))
    (payloads_append s₁ s₂ tr₁ tr₂)
  refine h.trans ((splitOracles_append s₁ s₂ _ _ _).trans ?_)
  rw [oracles_split_append]

namespace OracleVerifier
variable {ι I J K : Type u} {ambient : OracleSpec.{u, u} ι}
  {A : I → Type u} {B : J → Type u} {C : K → Type u}
  {inputs : OracleFamily.{u, u, u} I A} {middle : OracleFamily.{u, u, u} J B}
  {outputs : OracleFamily.{u, u, u} K C}
  {s₁ : OracleProtocol.{u}} {s₂ : Path s₁ → OracleProtocol.{u}} {S T U : Type u}

/-- In an appended run, the prefix decision's resources are the inputs and the prefix payloads:
every prefix-slot query routed by `prefixRoute` is answered as `payloadImpl s₁ tr₁` answers it. -/
theorem prefixRoute_payload (data : ∀ i, A i) (tr₁ : PathAlong oracleSig s₁)
    (tr₂ : PathAlong oracleSig (s₂ (projectPathAlong oracleSig s₁ tr₁))) :
    (⟨(Path.split s₁ s₂
        (projectPathAlong oracleSig _ (PathAlong.append oracleSig s₁ s₂ tr₁ tr₂))).1,
      (prefixRoute (inputs := inputs)
        (projectPathAlong oracleSig _ (PathAlong.append oracleSig s₁ s₂ tr₁ tr₂))).f
        (sumData data (payloads _ (PathAlong.append oracleSig s₁ s₂ tr₁ tr₂)))⟩ :
      (p : Path s₁) × (∀ i, (sumFamily inputs (pathFamily s₁ p)).Realization i)) =
      ⟨projectPathAlong oracleSig s₁ tr₁, sumData data (payloads s₁ tr₁)⟩ := by
  have h := congrArg (fun z : SplitData s₁ s₂ =>
      (⟨z.1.1, sumData data (fun j => z.2 (.inl j))⟩ :
        (p : Path s₁) × (∀ i, (sumFamily inputs (pathFamily s₁ p)).Realization i)))
    (splitOracles_payloads s₁ s₂ tr₁ tr₂)
  refine Eq.trans ?_ h
  refine Sigma.ext rfl (heq_of_eq ?_)
  funext i
  rcases i with i | i <;> rfl

/-- A composed oracle run splits into the prefix interaction and the suffix interaction, followed
by the prefix decision on the data `prefixRoute` selects and, after prefix acceptance only, the
suffix decision on the data `suffixRoute` selects. The output data is the composite output map
on the inputs and all payloads of the same run. Ambient and challenge queries keep their order. -/
theorem run_append (V₁ : OracleVerifier ambient s₁ S T inputs middle)
    (V₂ : (p : Path s₁) → OracleVerifier ambient (s₂ p) T U middle outputs)
    (compatible : OutputCompatibility V₁ V₂) (stmt : S) (data : ∀ i, A i)
    {Out : PathAlong oracleSig (s₁.append s₂) → Type u}
    (prover : Prover oracleSig ambient (s₁.append s₂) Out) :
    let full := ambient + challengeSpec oracleSig (s₁.append s₂)
    let toFull : QueryImpl ambient (OracleComp full) := fun q => liftM (full.query (.inl q))
    let draw : (c : ChallengeNode oracleSig (s₁.append s₂)) →
        OracleComp full (challengeSpec oracleSig (s₁.append s₂) c) :=
      fun c => liftM (full.query (.inr c))
    (V₁.append V₂ compatible).run stmt data prover = (do
      let ⟨tr₁, next, _⟩ ← TwoParty.Lens.run s₁ (Focal.splitPrefix (prover.simulate toFull))
        (sampler oracleSig s₁ (prefixDraw oracleSig s₁ s₂ draw))
      let ⟨tr₂, out, _⟩ ← TwoParty.Lens.run _ next
        (sampler oracleSig _ (suffixDraw oracleSig s₁ s₂ draw (projectPathAlong oracleSig s₁ tr₁)))
      let tr := PathAlong.append oracleSig s₁ s₂ tr₁ tr₂
      let p := projectPathAlong oracleSig _ tr
      let v := toView _ tr
      let resources := sumData data (payloads _ tr)
      let mid ← simulateQ (QueryImpl.addLift toFull
          ((sumFamily inputs (pathFamily s₁ (Path.split s₁ s₂ p).1)).behaviorOfRealizations
            ((prefixRoute (inputs := inputs) p).f resources)))
        (V₁.decide stmt (Path.split s₁ s₂ p).1 (View.split s₁ s₂ p v).1).run
      match mid with
      | none => pure ⟨tr, out, none⟩
      | some mid => do
        let verdict ← simulateQ (QueryImpl.addLift toFull
            ((sumFamily middle (pathFamily _ (Path.split s₁ s₂ p).2)).behaviorOfRealizations
              ((suffixRoute V₁ stmt p v).f resources)))
          ((V₂ (Path.split s₁ s₂ p).1).decide mid (Path.split s₁ s₂ p).2
            (View.split s₁ s₂ p v).2).run
        pure ⟨tr, out, verdict.map fun u => (u, (compatible.outputMap stmt p v).f resources)⟩) := by
  intro full toFull draw
  simp only [OracleVerifier.run]
  rw [sampler_append_eq, run_splitSampler]
  simp only [bind_assoc]
  refine bind_congr fun x => ?_
  obtain ⟨tr₁, next, _⟩ := x
  refine bind_congr fun y => ?_
  obtain ⟨tr₂, out, _⟩ := y
  refine (pure_bind _ _).trans ?_
  simp only [append, OptionT.run_mk, simulateQ_bind, bind_assoc]
  erw [OracleMap.simulate_withAmbient_addLift]
  refine bind_congr fun mid => ?_
  cases mid with
  | none => simp
  | some mid =>
    erw [OracleMap.simulate_withAmbient_addLift]
    rfl

end OracleVerifier
end Interaction.Core

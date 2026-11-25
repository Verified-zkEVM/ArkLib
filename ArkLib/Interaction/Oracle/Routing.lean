/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Interaction.Composition

/-!
# Routing an appended oracle run

This file runs a composed passive oracle verifier against an arbitrary prover of the appended
protocol. The run splits into four parts. The prefix interaction and the suffix interaction come
first. The prefix decision follows, on the data that `prefixRoute` selects. Only if the prefix
accepts, the suffix decision runs last, on the data that `suffixRoute` selects. The returned output
data is the composite output map applied to
the inputs and all oracle messages of the same run. The statement is an equality of open oracle
programs, so the order of ambient and challenge queries is preserved exactly.

In an appended run, the prefix decision's bundle consists of the inputs and the oracle messages of
the prefix transcript alone.
-/

@[expose] public section

namespace Interaction
open PFunctor FreeM TwoParty.Lens OracleComp Oracle

/-- Component paths of an appended protocol with data for both component oracle families. -/
abbrev SplitOracleMessages (s₁ : OracleProtocol.{0, 0}) (s₂ : Path s₁ → OracleProtocol.{0, 0}) :=
  (z : (p : Path s₁) × Path (s₂ p)) ×
    (∀ i, (sumFamily (oracleMessageFamily s₁ z.1) (oracleMessageFamily (s₂ z.1) z.2)).Realization i)

/-- Splitting the oracles of an appended path recovers the routed component data. -/
theorem splitOracleMessages_append : (s₁ : OracleProtocol.{0, 0}) →
    (s₂ : Path s₁ → OracleProtocol.{0, 0}) → (p₁ : Path s₁) → (p₂ : Path (s₂ p₁)) →
    (x : ∀ i, OracleMessage (s₁.append s₂) (Path.append s₁ s₂ p₁ p₂) i) →
    (⟨Path.split s₁ s₂ (Path.append s₁ s₂ p₁ p₂),
      (splitOracleMessages s₁ s₂ (Path.append s₁ s₂ p₁ p₂)).f x⟩ : SplitOracleMessages s₁ s₂) =
      ⟨⟨p₁, p₂⟩, (oracleMessageFamily_split s₁ s₂ p₁ p₂).f x⟩
  | .pure _, _, ⟨⟩, _, _ => rfl
  | .liftBind (.message X) next, s₂, ⟨b, p₁⟩, p₂, x =>
    congrArg (fun z : SplitOracleMessages (next b) (fun p => s₂ ⟨b, p⟩) =>
      (⟨⟨⟨b, z.1.1⟩, z.1.2⟩, z.2⟩ : SplitOracleMessages (.liftBind (.message X) next) s₂))
      (splitOracleMessages_append (next b) (fun p => s₂ ⟨b, p⟩) p₁ p₂ x)
  | .liftBind (.challenge X) next, s₂, ⟨b, p₁⟩, p₂, x =>
    congrArg (fun z : SplitOracleMessages (next b) (fun p => s₂ ⟨b, p⟩) =>
      (⟨⟨⟨b, z.1.1⟩, z.1.2⟩, z.2⟩ : SplitOracleMessages (.liftBind (.challenge X) next) s₂))
      (splitOracleMessages_append (next b) (fun p => s₂ ⟨b, p⟩) p₁ p₂ x)
  | .liftBind (.oracle X I) next, s₂, ⟨b, p₁⟩, p₂, x => by
    have ih := congrArg (fun z : SplitOracleMessages (next b) (fun p => s₂ ⟨b, p⟩) =>
      (⟨⟨⟨b, z.1.1⟩, z.1.2⟩, sumData (sumData (fun i => x (.inl i))
          (fun j => z.2 (.inl j))) (fun k => z.2 (.inr k))⟩ :
        SplitOracleMessages (.liftBind (.oracle X I) next) s₂))
      (splitOracleMessages_append (next b) (fun p => s₂ ⟨b, p⟩) p₁ p₂ (fun j => x (.inr j)))
    refine Eq.trans ?_ (ih.trans ?_)
    · refine Sigma.ext rfl (heq_of_eq ?_)
      funext i
      rcases i with (i | i) | i <;> rfl
    · refine Sigma.ext rfl (heq_of_eq ?_)
      funext i
      rcases i with (i | i) | i <;> rfl

/-- In an appended run, the oracle messages routed to either component are that component's
own. -/
theorem splitOracleMessages_oracleMessages (s₁ : OracleProtocol.{0, 0})
    (s₂ : Path s₁ → OracleProtocol.{0, 0})
    (tr₁ : Transcript oracleSig s₁)
    (tr₂ : Transcript oracleSig (s₂ tr₁.path)) :
    (⟨Path.split s₁ s₂
        (Transcript.path (Transcript.append s₁ s₂ tr₁ tr₂)),
      (splitOracleMessages s₁ s₂
        (Transcript.path (Transcript.append s₁ s₂ tr₁ tr₂))).f
        (oracleMessages _ (Transcript.append s₁ s₂ tr₁ tr₂))⟩ : SplitOracleMessages s₁ s₂) =
      ⟨⟨tr₁.path, tr₂.path⟩,
        sumData (oracleMessages s₁ tr₁) (oracleMessages _ tr₂)⟩ := by
  have h := congrArg (fun d : PathWithOracleMessages (s₁.append s₂) =>
      (⟨Path.split s₁ s₂ d.1, (splitOracleMessages s₁ s₂ d.1).f d.2⟩ : SplitOracleMessages s₁ s₂))
    (oracleMessages_append s₁ s₂ tr₁ tr₂)
  refine h.trans ((splitOracleMessages_append s₁ s₂ _ _ _).trans ?_)
  rw [oracleMessageFamily_split_append]

namespace OracleVerifier
variable {ι : Type} {ambient : OracleSpec ι}
  {inputs : OracleBundle}
  {s₁ : OracleProtocol.{0, 0}} {s₂ : Path s₁ → OracleProtocol.{0, 0}} {S : Type}
  {T : Path s₁ → Type} {U : (p : Path s₁) → Path (s₂ p) → Type}
  {middle : Path s₁ → OracleBundle}
  {outputs : (p₁ : Path s₁) → Path (s₂ p₁) → OracleBundle}

/-- In an appended run, the prefix decision's bundle consists of the inputs and the prefix oracle
messages: every prefix-slot query routed by `prefixRoute` is answered as
`oracleMessageImpl s₁ tr₁` answers it. -/
theorem prefixRoute_oracleMessages (data : inputs.Data) (tr₁ : Transcript oracleSig s₁)
    (tr₂ : Transcript oracleSig (s₂ tr₁.path)) :
    (⟨(Path.split s₁ s₂
        (Transcript.path (Transcript.append s₁ s₂ tr₁ tr₂))).1,
      (prefixRoute (inputs := inputs)
        (Transcript.path (Transcript.append s₁ s₂ tr₁ tr₂))).f
        (data, oracleMessages _ (Transcript.append s₁ s₂ tr₁ tr₂))⟩ :
      (p : Path s₁) × (pathBundle inputs s₁ p).Data) =
      ⟨tr₁.path, (data, oracleMessages s₁ tr₁)⟩ := by
  have h := congrArg (fun z : SplitOracleMessages s₁ s₂ =>
      (⟨z.1.1, (data, fun j => z.2 (.inl j))⟩ :
        (p : Path s₁) × (pathBundle inputs s₁ p).Data))
    (splitOracleMessages_oracleMessages s₁ s₂ tr₁ tr₂)
  refine Eq.trans ?_ h
  refine Sigma.ext rfl (heq_of_eq ?_)
  rfl

/-- A composed oracle run splits into the prefix interaction and the suffix interaction, followed
by the prefix decision on the data `prefixRoute` selects. Only if the prefix accepts, the suffix
decision follows, on the data `suffixRoute` selects. The output data is the composite output map
on the inputs and all oracle messages of the same run. Ambient and challenge queries keep their
order. Intermediate and final statements and oracle bundles may depend on their public paths. -/
theorem run_append (V₁ : OracleVerifier ambient s₁ S T inputs middle)
    (V₂ : (p : Path s₁) → OracleVerifier ambient (s₂ p) (T p) (U p) (middle p) (outputs p))
    (compatible : OutputCompatibility V₁ V₂) (stmt : S) (data : inputs.Data)
    {Out : Transcript oracleSig (s₁.append s₂) → Type}
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
        (sampler oracleSig _ (suffixDraw oracleSig s₁ s₂ draw (Transcript.path tr₁)))
      let tr := Transcript.append s₁ s₂ tr₁ tr₂
      let p := tr.path
      let v := toView _ tr
      let pathData := (data, oracleMessages _ tr)
      let mid ← simulateQ (QueryImpl.addLift toFull
          ((pathBundle inputs s₁ (Path.split s₁ s₂ p).1).answer
            ((prefixRoute (inputs := inputs) p).f pathData)))
        (V₁.decide stmt (Path.split s₁ s₂ p).1 (View.split s₁ s₂ p v).1).run
      match mid with
      | none => pure ⟨tr, out, none⟩
      | some mid => do
        let verdict ← simulateQ (QueryImpl.addLift toFull
            ((pathBundle (middle (Path.split s₁ s₂ p).1)
              _ (Path.split s₁ s₂ p).2).answer
              ((suffixRoute V₁ stmt p v).f pathData)))
          ((V₂ (Path.split s₁ s₂ p).1).decide mid (Path.split s₁ s₂ p).2
            (View.split s₁ s₂ p v).2).run
        pure ⟨tr, out, verdict.map fun u => (u, (compatible.outputMap stmt p v).f pathData)⟩) := by
  intro full toFull draw
  simp only [OracleVerifier.run_eq]
  rw [sampler_append_eq, run_splitSampler]
  simp only [bind_assoc]
  refine bind_congr fun x => ?_
  obtain ⟨tr₁, next, _⟩ := x
  refine bind_congr fun y => ?_
  obtain ⟨tr₂, out, _⟩ := y
  refine (pure_bind _ _).trans ?_
  simp only [append, OptionT.run_mk, simulateQ_bind, bind_assoc]
  erw [OracleMap.simulate_withAmbient_addLift toFull
    (prefixRoute (inputs := inputs)
      (Transcript.path (Transcript.append s₁ s₂ tr₁ tr₂)))
    (data, oracleMessages _ (Transcript.append s₁ s₂ tr₁ tr₂))]
  refine bind_congr fun mid => ?_
  cases mid with
  | none => simp
  | some mid =>
    erw [OracleMap.simulate_withAmbient_addLift toFull
      (suffixRoute V₁ stmt
        (Transcript.path (Transcript.append s₁ s₂ tr₁ tr₂))
        (toView _ (Transcript.append s₁ s₂ tr₁ tr₂)))
      (data, oracleMessages _ (Transcript.append s₁ s₂ tr₁ tr₂))]

end OracleVerifier
end Interaction

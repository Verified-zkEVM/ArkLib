/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Interaction.Core.Oracle.Routing
import ArkLibTest.Interaction.Core.Oracle.DependentRouting

/-! The prefix exports `input false + sent.1` and hides input slot `true`. The suffix samples a
challenge, sends one oracle, and sees only the export and its own message. The composed run keeps
the prover's private memory and ambient order, and its output data is the export of the same run.
A prefix-slot query routed by `prefixRoute` is answered from the prefix payload. -/

open PFunctor PFunctor.FreeM Interaction.Core Interaction.Oracle Interaction.TwoParty.Lens
  OracleComp

namespace Interaction.Core.RoutingTests

/-- Ambient queries carry tags; the trace handler records each tag and answers with it. -/
abbrev ambient : OracleSpec Nat := Nat →ₒ Nat

/-- Two scalar input slots; slot `true` is never exported. -/
@[instance_reducible] def inputs : OracleFamily.{0, 0, 0} Bool (fun _ => Nat) :=
  ⟨fun _ => OracleInterface.instDefault⟩

/-- Input data: slot `false` holds 3, slot `true` holds the hidden value. -/
def inputData (hidden : Nat) : ∀ _ : Bool, Nat
  | false => 3
  | true => hidden

/-- Only the first coordinate of a sent pair is observable. -/
@[reducible] def firstInterface : OracleInterface (Nat × Nat) where
  Query := Unit
  toOC.spec := fun _ => Nat
  toOC.impl _ := do return (← read).1

/-- The prefix sends one pair oracle. -/
@[instance_reducible] def firstProtocol : OracleProtocol :=
  .liftBind (.oracle (Nat × Nat) firstInterface) (fun _ => .pure ⟨⟩)

/-- The suffix samples a challenge, then sends one scalar oracle. -/
@[instance_reducible] def secondProtocol : OracleProtocol :=
  .liftBind (.challenge Nat) (fun _ =>
    .liftBind (.oracle Nat OracleInterface.instDefault) (fun _ => .pure ⟨⟩))

/-- The prefix oracle send followed by the challenged suffix. -/
abbrev combined : OracleProtocol := firstProtocol.append (fun _ => secondProtocol)

/-- One exported scalar oracle. -/
@[instance_reducible] def exported : OracleFamily.{0, 0, 0} PUnit (fun _ => Nat) :=
  ⟨fun _ => OracleInterface.instDefault⟩

/-- The prefix resources on its only path. -/
abbrev prefixResources := pathResources inputs firstProtocol ⟨⟨⟩, ⟨⟩⟩

/-- Export input slot `false` plus the observable coordinate of the prefix message. -/
def exportMap : OracleMap prefixResources exported where
  f x _ := (show Nat from x.1 false) + (show Nat × Nat from x.2 (.inl ⟨⟩)).1
  impl _ := do
    let a : Nat ← liftM (prefixResources.spec.query (.inl ⟨false, ()⟩))
    let b : Nat ← liftM (prefixResources.spec.query (.inr ⟨.inl ⟨⟩, ()⟩))
    pure (a + b)
  law x q := by
    simp only [simulateQ_bind]
    rfl

/-- Interpret the raw resource signature, recording visible input, hidden input and sent-slot
requests distinctly. The hidden slot is present and would be recorded if it were queried. -/
def exportTraceHandler (old hidden visible secret : Nat) :
    QueryImpl prefixResources.spec (StateM (List Nat)) := fun q => do
  let label := match q with
    | .inl ⟨false, _⟩ => 0
    | .inl ⟨true, _⟩ => 1
    | .inr _ => 2
  modify (· ++ [label])
  pure (prefixResources.answer
    ((fun b => if b then hidden else old), payloads firstProtocol ⟨(visible, secret), ⟨⟩⟩) q)

/-- Every exported request reads the visible input followed by the sent oracle, exactly once.
The complete trace omits label 1, so the hidden input is never queried, even and in particular
when its value equals a visible answer. -/
theorem exportMap_raw_trace (old hidden visible secret : Nat) :
    (simulateQ (exportTraceHandler old hidden visible secret) (exportMap.impl ⟨⟨⟩, ()⟩)).run [] =
      (old + visible, [0, 2]) := rfl

/-- The hidden request is absent from the actual raw trace for every realization. -/
theorem exportMap_hidden_not_queried (old hidden visible secret : Nat) :
    1 ∉ ((simulateQ (exportTraceHandler old hidden visible secret)
      (exportMap.impl ⟨⟨⟩, ()⟩)).run []).2 := by
  rw [exportMap_raw_trace]
  change 1 ∉ ([0, 2] : List Nat)
  decide

/-- The prefix decision records 10 and returns the observable coordinate of its message. -/
def prefixVerifier :
    OracleVerifier ambient firstProtocol Unit (fun _ => Nat) inputs (fun _ => exported) where
  decide _ p _ := by
    rcases p with ⟨⟨⟩, ⟨⟩⟩
    exact do
      let _ ← liftM ((ambient + prefixResources.spec).query (.inl 10))
      let n : Nat ← liftM ((ambient + prefixResources.spec).query (.inr (.inr ⟨.inl ⟨⟩, ()⟩)))
      pure n
  outputMap _ p _ := by
    rcases p with ⟨⟨⟩, ⟨⟩⟩
    exact exportMap

/-- The suffix resources on its only shape path. -/
abbrev suffixResources := pathResources exported secondProtocol ⟨⟨⟩, ⟨⟨⟩, ⟨⟩⟩⟩

/-- The suffix records 30, reads the export and its own message, records 40 and 60, and accepts
when the export and the message agree, claiming the prefix's returned value together with its own
message. -/
def suffixVerifier : OracleVerifier ambient secondProtocol Nat (fun _ => Nat × Nat) exported
    (fun _ => exported) where
  decide stmt p _ := by
    rcases p with ⟨⟨⟩, ⟨⟨⟩, ⟨⟩⟩⟩
    exact OptionT.mk do
      let _ ← liftM ((ambient + suffixResources.spec).query (.inl 30))
      let e : Nat ← liftM ((ambient + suffixResources.spec).query (.inr (.inl ⟨⟨⟩, ()⟩)))
      let m : Nat ← liftM ((ambient + suffixResources.spec).query (.inr (.inr ⟨.inl ⟨⟩, ()⟩)))
      let _ ← liftM ((ambient + suffixResources.spec).query (.inl 40))
      let _ ← liftM ((ambient + suffixResources.spec).query (.inl 60))
      pure (if e = m then some (stmt, m) else none)
  outputMap _ p _ := OracleMap.fst _ _

/-- The composite output map is the suffix output map after `suffixRoute`. -/
def compatible : OracleVerifier.OutputCompatibility prefixVerifier (fun _ => suffixVerifier) where
  outputMap stmt p v :=
    (suffixVerifier.outputMap 0 (Path.split firstProtocol (fun _ => secondProtocol) p).2
      (View.split firstProtocol (fun _ => secondProtocol) p v).2).comp
      (OracleVerifier.suffixRoute prefixVerifier stmt p v)
  agrees _ _ _ _ _ _ := rfl

/-- Compose the prefix and suffix verifiers with the routed output map. -/
def composed := prefixVerifier.append (fun _ => suffixVerifier) compatible

/-- The prefix prover records 1, sends `(20, secret)`, and keeps `secret` as private memory. -/
def prefixProver (secret : Nat) :
    Prover oracleSig ambient firstProtocol (fun _ => Nat) := do
  let _ ← liftM (ambient.query 1)
  pure ⟨(20, secret), pure secret⟩

/-- The suffix prover records 20 at the seam. After the challenge it queries 50, echoes the
challenge, and keeps `memory + challenge + answer` as private output. -/
def suffixProver (memory : Nat) :
    OracleComp ambient (Prover oracleSig ambient secondProtocol (fun _ => Nat)) := do
  let _ ← liftM (ambient.query 20)
  pure (pure fun c => do
    let answer : Nat ← liftM (ambient.query 50)
    pure ⟨c, pure (memory + (show Nat from c) + answer)⟩)

/-- The whole prover, built by `Prover.append`. -/
def prover (secret : Nat) : Prover oracleSig ambient combined (fun _ => Nat) :=
  Prover.append (prefixProver secret) (fun _ memory => suffixProver memory)

/-- Record ambient tags and answer each with its tag; answer the suffix challenge with 23. -/
def traceHandler : QueryImpl (ambient + challengeSpec oracleSig combined) (StateM (List Nat))
  | .inl n => do modify (· ++ [n]); pure n
  | .inr ⟨.inl _, h⟩ => nomatch h
  | .inr ⟨.inr ⟨_, .inl _⟩, _⟩ => pure (23 : Nat)
  | .inr ⟨.inr ⟨_, .inr ⟨_, .inl _⟩⟩, h⟩ => nomatch h
  | .inr ⟨.inr ⟨_, .inr ⟨_, .inr ⟨_, n⟩⟩⟩, _⟩ => n.elim

/-- Run the composed verifier and retain the ambient query history. -/
def observed (hidden secret : Nat) :=
  (simulateQ traceHandler (composed.run () (inputData hidden) (prover secret))).run []

/-- The private output, the claim with its output data, and the ambient history of one run. -/
def resultSummary (hidden secret : Nat) : Nat × Option ((Nat × Nat) × Nat) × List Nat :=
  let result := observed hidden secret
  (result.1.2.1, result.1.2.2.map (fun z => (z.1, z.2 ⟨⟩)), result.2)

/-! Additional passive composition coverage. Both verifier decisions follow the whole
interaction. The challenge is sampled independently of resources. The disposition inventory
records the retired export-derived message and its former schedule explicitly; it does not
identify this example with that contract or with a produced-prefix availability certificate. -/
example (hidden secret : Nat) : resultSummary hidden secret =
    (secret + 23 + 50, some ((20, 23), 23), [1, 20, 50, 10, 30, 40, 60]) := by
  unfold resultSummary observed composed
  rw [OracleVerifier.run_append]
  rfl

/-- A fresh pair is sent before the suffix's public-coin challenge. -/
@[instance_reducible] def closingSuffix : OracleProtocol :=
  .liftBind (.oracle (Nat × Nat) firstInterface) (fun _ =>
    .liftBind (.challenge Nat) (fun _ => .pure ⟨⟩))

/-- The prefix send followed by the fresh send and challenge, in that order. -/
abbrev closingProtocol := firstProtocol.append (fun _ => closingSuffix)

/-- Resources after the fresh pair and challenge. -/
abbrev closingResources := pathResources exported closingSuffix ⟨⟨⟩, ⟨⟨⟩, ⟨⟩⟩⟩

/-- The final export adds the prefix export to the fresh observable coordinate. -/
def closingMap : OracleMap closingResources exported where
  f x _ := x.1 ⟨⟩ + (show Nat × Nat from x.2 (.inl ⟨⟩)).1
  impl _ := do
    let old : Nat ← liftM (closingResources.spec.query (.inl ⟨⟨⟩, ()⟩))
    let fresh : Nat ← liftM (closingResources.spec.query (.inr ⟨.inl ⟨⟩, ()⟩))
    pure (old + fresh)
  law _ _ := by
    simp only [simulateQ_bind]
    rfl

/-- The suffix decides from its export and its fresh pair after the whole interaction. -/
def closingVerifier : OracleVerifier ambient closingSuffix Nat (fun _ => Nat) exported
    (fun _ => exported) where
  decide _ p _ := by
    rcases p with ⟨⟨⟩, ⟨⟨⟩, ⟨⟩⟩⟩
    exact do
      let _ ← liftM ((ambient + closingResources.spec).query (.inl 30))
      let old : Nat ← liftM ((ambient + closingResources.spec).query (.inr (.inl ⟨⟨⟩, ()⟩)))
      let fresh : Nat ← liftM ((ambient + closingResources.spec).query
        (.inr (.inr ⟨.inl ⟨⟩, ()⟩)))
      let _ ← liftM ((ambient + closingResources.spec).query (.inl 40))
      let _ ← liftM ((ambient + closingResources.spec).query (.inl 60))
      pure (old + fresh)
  outputMap _ p _ := by
    rcases p with ⟨⟨⟩, ⟨⟨⟩, ⟨⟩⟩⟩
    exact closingMap

/-- The composite export is computed from the same prefix and suffix resources. -/
def closingCompatible :
    OracleVerifier.OutputCompatibility prefixVerifier (fun _ => closingVerifier) where
  outputMap stmt p view :=
    (closingVerifier.outputMap 0 (Path.split firstProtocol (fun _ => closingSuffix) p).2
      (View.split firstProtocol (fun _ => closingSuffix) p view).2).comp
        (OracleVerifier.suffixRoute prefixVerifier stmt p view)
  agrees _ _ _ _ _ _ := rfl

/-- Both concrete pairs are sent before the challenge is received; private memory survives. -/
def closingProver (secret : Nat) : Prover oracleSig ambient closingProtocol (fun _ => Nat) :=
  Prover.append (s₂ := fun _ => closingSuffix)
    (do
      let _ ← liftM (ambient.query 1)
      pure ⟨(11, secret), pure secret⟩)
    (fun _ memory => do
      let _ ← liftM (ambient.query 20)
      pure (pure ⟨(5, secret), pure fun challenge => do
        let answer : Nat ← liftM (ambient.query 50)
        pure (memory + (show Nat from challenge) + answer)⟩))

/-- The challenge service answers 23 without querying the input or either sent pair. -/
def closingHandler : QueryImpl (ambient + challengeSpec oracleSig closingProtocol)
    (StateM (List Nat))
  | .inl tag => do modify (· ++ [tag]); pure tag
  | .inr ⟨.inl _, h⟩ => nomatch h
  | .inr ⟨.inr ⟨_, .inl _⟩, h⟩ => nomatch h
  | .inr ⟨.inr ⟨_, .inr ⟨_, .inl _⟩⟩, _⟩ => pure (23 : Nat)
  | .inr ⟨.inr ⟨_, .inr ⟨_, .inr ⟨_, n⟩⟩⟩, _⟩ => n.elim

/-- The final claim and export both use input 7, prefix message 11 and fresh message 5.
The hidden input and both private coordinates remain arbitrary; no resource read selects a draw. -/
theorem closing_source_contract (hidden secret : Nat) :
    (fun z => (z.1.2.1, z.1.2.2.map (fun c => (c.1, c.2 ⟨⟩)), z.2))
      ((simulateQ closingHandler
        ((prefixVerifier.append (fun _ => closingVerifier) closingCompatible).run ()
          (fun b => if b then hidden else 7) (closingProver secret))).run []) =
      (secret + 23 + 50, some (23, 23), [1, 20, 50, 10, 30, 40, 60]) := by
  rw [OracleVerifier.run_append]
  rfl

-- Executable samples of the same summary.
run_cmd do
  for hidden in [0, 1000] do
    for secret in [0, 7] do
      unless resultSummary hidden secret ==
          (secret + 23 + 50, some ((20, 23), 23), [1, 20, 50, 10, 30, 40, 60]) do
        throwError "the composed run summary is wrong: {resultSummary hidden secret}"

-- SourceRoutingExample SR3: the routing theorem instantiated at the ordinary whole prover.
/-- The routing theorem accepts the ordinary whole prover, built by `Prover.append`, and the
actual input data. -/
example (hidden secret : Nat) :=
  OracleVerifier.run_append prefixVerifier (fun _ => suffixVerifier) compatible ()
    (inputData hidden) (prover secret)

/-! Additional prefix-routing coverage: on an appended transcript built from separate
prefix and suffix transcripts, the routed prefix data is the prefix transcript's own payload. -/

/-- The prefix transcript with observable value 20 and a private second coordinate. -/
def prefixTranscript (secret : Nat) : PathAlong oracleSig firstProtocol := ⟨(20, secret), ⟨⟩⟩

/-- The suffix transcript with challenge 23 and scalar message 23. -/
def suffixTranscript : PathAlong oracleSig secondProtocol :=
  ⟨(23 : Nat), ⟨(23 : Nat), ⟨⟩⟩⟩

example (hidden secret : Nat) :
    (⟨(Path.split firstProtocol (fun _ => secondProtocol)
        (projectPathAlong oracleSig combined
          (PathAlong.append oracleSig firstProtocol (fun _ => secondProtocol)
            (prefixTranscript secret) suffixTranscript))).1,
      (OracleVerifier.prefixRoute (inputs := inputs)
        (projectPathAlong oracleSig combined
          (PathAlong.append oracleSig firstProtocol (fun _ => secondProtocol)
            (prefixTranscript secret) suffixTranscript))).f
        (inputData hidden, payloads combined
          (PathAlong.append oracleSig firstProtocol (fun _ => secondProtocol)
            (prefixTranscript secret) suffixTranscript))⟩ :
      (p : FreeM.Path firstProtocol) ×
        (pathResources inputs firstProtocol p).Data) =
      ⟨projectPathAlong oracleSig firstProtocol (prefixTranscript secret),
        (inputData hidden, payloads firstProtocol (prefixTranscript secret))⟩ :=
  OracleVerifier.prefixRoute_payload (s₂ := fun _ => secondProtocol) (inputData hidden)
    (prefixTranscript secret) suffixTranscript

end Interaction.Core.RoutingTests

/-! SourceRoutingExample SR4: the routing declarations stay axiom-clean. -/
run_cmd do
  for decl in [``Interaction.Core.OracleVerifier.run_append,
      ``Interaction.Core.OracleVerifier.prefixRoute_payload,
      ``Interaction.Core.splitOracles_payloads, ``Interaction.Core.sampler_append_eq,
      ``Interaction.Core.OracleMap.simulate_withAmbient_addLift] do
    for ax in ← Lean.collectAxioms decl do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "unexpected axiom {ax} in {decl}"

namespace Interaction.Core.DependentRoutingTests

/-- The zero branch of the split-run law retains the unit statement and scalar oracle. -/
example : observed 0 = (true, 13, some (0, 0)) := by
  unfold observed composite
  rw [OracleVerifier.run_append]
  rfl

/-- The nonzero branch of the split-run law retains the natural statement and pair oracle. -/
example : observed 7 = (false, 29, some (7, 7)) := by
  unfold observed composite
  rw [OracleVerifier.run_append]
  rfl

end Interaction.Core.DependentRoutingTests

universe uι uI uJ v wI wJ wK

/-- Ambient routing permits independent index universes and a larger lawful target monad. -/
example {ι : Type uι} {I : Type uI} {J : Type uJ}
    {ambient : OracleSpec.{uι, 0} ι} {m : Type → Type v} [Monad m] [LawfulMonad m]
    {A : I → Type} {B : J → Type}
    {inputs : OracleFamily.{uI, 0, wI} I A} {outputs : OracleFamily.{uJ, 0, wJ} J B}
    (handler : QueryImpl ambient m) (route : OracleMap inputs outputs) (data : ∀ i, A i)
    {α : Type} (program : OracleComp (ambient + outputs.spec) α) :
    simulateQ (QueryImpl.addLift handler (inputs.behaviorOfRealizations data) :
        QueryImpl (ambient + inputs.spec) m)
        (simulateQ (route.withAmbient ambient) program) =
      simulateQ (QueryImpl.addLift handler (outputs.behaviorOfRealizations (route.f data)) :
        QueryImpl (ambient + outputs.spec) m) program :=
  OracleMap.simulate_withAmbient_addLift handler route data program

/-- Split execution accepts large input statements and oracle indices while its final outputs
remain in the run universe. Both output families may depend on their paths. -/
example {s₁ : OracleProtocol} {s₂ : Path s₁ → OracleProtocol}
    {I : Type 1} {A : I → Type} {inputs : OracleFamily.{1, 0, wI} I A} {S : Type 3}
    {T : Path s₁ → Type} {U : (p : Path s₁) → Path (s₂ p) → Type}
    {J : Path s₁ → Type 2} {B : (p : Path s₁) → J p → Type}
    {middle : (p : Path s₁) → OracleFamily.{2, 0, wJ} (J p) (B p)}
    {K : (p : Path s₁) → Path (s₂ p) → Type}
    {C : (p : Path s₁) → (q : Path (s₂ p)) → K p q → Type}
    {outputs : (p : Path s₁) → (q : Path (s₂ p)) → OracleFamily.{0, 0, wK} (K p q) (C p q)}
    {ambient : OracleSpec Nat}
    (V₁ : OracleVerifier ambient s₁ S T inputs middle)
    (V₂ : (p : Path s₁) → OracleVerifier ambient (s₂ p) (T p) (U p) (middle p) (outputs p))
    (compatible : OracleVerifier.OutputCompatibility V₁ V₂) (stmt : S) (data : ∀ i, A i)
    {Out : PathAlong oracleSig (s₁.append s₂) → Type}
    (prover : Prover oracleSig ambient (s₁.append s₂) Out) :=
  OracleVerifier.run_append V₁ V₂ compatible stmt data prover


universe u uX uY dX dY

/-- Ambient routing permits independent resource index and data universes. -/
example {ι : Type uι} {ambient : OracleSpec.{uι, u} ι}
    {m : Type u → Type v} [Monad m] [LawfulMonad m]
    {inputs : Resources.{u, uX, dX}} {outputs : Resources.{u, uY, dY}}
    (handler : QueryImpl ambient m) (route : OracleMap inputs outputs) (data : inputs.Data)
    {α : Type u} (program : OracleComp (ambient + outputs.spec) α) :
    simulateQ (QueryImpl.addLift handler (inputs.answer data) :
        QueryImpl (ambient + inputs.spec) m)
        (simulateQ (route.withAmbient ambient) program) =
      simulateQ (QueryImpl.addLift handler (outputs.answer (route.f data)) :
        QueryImpl (ambient + outputs.spec) m) program :=
  OracleMap.simulate_withAmbient_addLift handler route data program

/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Interaction.Core.Oracle.Routing

/-! The prefix exports `input false + sent.1` and hides input slot `true`. The suffix samples a
challenge, sends one oracle, and sees only the export and its own message. The composed run keeps
the prover's private memory and ambient order, and its output data is the export of the same run.
A prefix-slot query routed by `prefixRoute` is answered from the prefix payload. -/

open PFunctor PFunctor.FreeM Interaction.Core Interaction.Oracle Interaction.TwoParty.Lens
  OracleComp

namespace Interaction.Core.RoutingTests

/-- Ambient queries carry tags, which the trace handler records. -/
abbrev ambient : OracleSpec Nat := Nat →ₒ PUnit

/-- Two scalar input slots; slot `true` is never exported. -/
@[instance_reducible] def inputs : OracleFamily Bool (fun _ => Nat) :=
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

abbrev combined : OracleProtocol := firstProtocol.append (fun _ => secondProtocol)

/-- One exported scalar oracle. -/
@[instance_reducible] def exported : OracleFamily PUnit (fun _ => Nat) :=
  ⟨fun _ => OracleInterface.instDefault⟩

/-- The prefix resources on its only path. -/
abbrev prefixResources := sumFamily inputs (pathFamily firstProtocol ⟨⟨⟩, ⟨⟩⟩)

/-- Export input slot `false` plus the observable coordinate of the prefix message. -/
def exportMap : OracleMap prefixResources exported where
  f x _ := (show Nat from x (.inl false)) + (show Nat × Nat from x (.inr (.inl ⟨⟩))).1
  impl _ := do
    let a : Nat ← liftM (prefixResources.spec.query ⟨.inl false, ()⟩)
    let b : Nat ← liftM (prefixResources.spec.query ⟨.inr (.inl ⟨⟩), ()⟩)
    pure (a + b)
  law x q := by
    simp only [simulateQ_bind]
    rfl

/-- The prefix decision records 10 and returns the observable coordinate of its message. -/
def prefixVerifier : OracleVerifier ambient firstProtocol Unit Nat inputs exported where
  decide _ p _ := by
    rcases p with ⟨⟨⟩, ⟨⟩⟩
    exact do
      let _ ← liftM ((ambient + prefixResources.spec).query (.inl 10))
      let n : Nat ← liftM ((ambient + prefixResources.spec).query (.inr ⟨.inr (.inl ⟨⟩), ()⟩))
      pure n
  outputMap _ p _ := by
    rcases p with ⟨⟨⟩, ⟨⟩⟩
    exact exportMap

/-- The suffix resources on its only shape path. -/
abbrev suffixResources := sumFamily exported (pathFamily secondProtocol ⟨⟨⟩, ⟨⟨⟩, ⟨⟩⟩⟩)

/-- The suffix records 30, reads the export and its own message, and accepts when they agree,
claiming the prefix's returned value together with its own message. -/
def suffixVerifier : OracleVerifier ambient secondProtocol Nat (Nat × Nat) exported exported where
  decide stmt p _ := by
    rcases p with ⟨⟨⟩, ⟨⟨⟩, ⟨⟩⟩⟩
    exact OptionT.mk do
      let _ ← liftM ((ambient + suffixResources.spec).query (.inl 30))
      let e : Nat ← liftM ((ambient + suffixResources.spec).query (.inr ⟨.inl ⟨⟩, ()⟩))
      let m : Nat ← liftM ((ambient + suffixResources.spec).query (.inr ⟨.inr (.inl ⟨⟩), ()⟩))
      pure (if e = m then some (stmt, m) else none)
  outputMap _ p _ := OracleMap.embedding (sumFamily exported (pathFamily secondProtocol p))
    (fun _ => .inl ⟨⟩)

/-- The composite output map is the suffix output map after `suffixRoute`. -/
def compatible : OracleVerifier.OutputCompatibility prefixVerifier (fun _ => suffixVerifier) where
  outputMap stmt p v :=
    (suffixVerifier.outputMap 0 (Path.split firstProtocol (fun _ => secondProtocol) p).2
      (View.split firstProtocol (fun _ => secondProtocol) p v).2).comp
      (OracleVerifier.suffixRoute prefixVerifier stmt p v)
  agrees _ _ _ _ _ _ := rfl

def composed := prefixVerifier.append (fun _ => suffixVerifier) compatible

/-- The prefix prover records 1, sends `(20, secret)`, and keeps `secret` as private memory. -/
def prefixProver (secret : Nat) :
    Prover oracleSig ambient firstProtocol (fun _ => Nat) := do
  let _ ← liftM (ambient.query 1)
  pure ⟨(20, secret), pure secret⟩

/-- The suffix prover records 20 at the seam, then 50 before echoing the challenge. -/
def suffixProver (memory : Nat) :
    OracleComp ambient (Prover oracleSig ambient secondProtocol (fun _ => Nat)) := do
  let _ ← liftM (ambient.query 20)
  pure (pure fun c => do
    let _ ← liftM (ambient.query 50)
    pure ⟨c, pure (memory + (show Nat from c))⟩)

/-- The whole prover, built by `Prover.append`. -/
def prover (secret : Nat) : Prover oracleSig ambient combined (fun _ => Nat) :=
  Prover.append (prefixProver secret) (fun _ memory => suffixProver memory)

/-- Record ambient tags; answer the suffix challenge with 23. -/
def traceHandler : QueryImpl (ambient + challengeSpec oracleSig combined) (StateM (List Nat))
  | .inl n => modify (· ++ [n])
  | .inr ⟨.inl _, h⟩ => nomatch h
  | .inr ⟨.inr ⟨_, .inl _⟩, _⟩ => pure (23 : Nat)
  | .inr ⟨.inr ⟨_, .inr ⟨_, .inl _⟩⟩, h⟩ => nomatch h
  | .inr ⟨.inr ⟨_, .inr ⟨_, .inr ⟨_, n⟩⟩⟩, _⟩ => n.elim

def observed (hidden secret : Nat) :=
  (simulateQ traceHandler (composed.run () (inputData hidden) (prover secret))).run []

/-! SourceRoutingExample SR1, restated: the composed oracle verifier is `OracleVerifier.append`
with a prefix output map that exports `input false + sent.1` and hides input `true`. The frozen
verifier's mid-run effects 10, 30 and 40 become effects of the end decisions (passive verifier),
and the suffix challenge is sampled rather than computed from the export.

QueryBounds 14, restated: the frozen row checks that an old query's join name survives inclusion
into the terminal context. Names are retired, so the check is that the prefix decision's query to
its message slot, routed by `prefixRoute` in the appended run, is answered from the prefix
payload: the prefix returns `sent.1 = 20`, which the suffix claim carries. -/
run_cmd do
  for hidden in [0, 1000] do
    let (obs, trace) := observed hidden 7
    unless trace == [1, 20, 50, 10, 30] do
      throwError "prover or decision effects were lost or reordered: {trace}"
    unless obs.2.1 == 7 + 23 do throwError "the prover's private memory was lost"
    match obs.2.2 with
    | none => throwError "the composed decision rejected"
    | some (claim, data) =>
      unless claim.1 == 20 do
        throwError "the routed prefix slot was not answered from the prefix payload: {claim.1}"
      unless claim.2 == 23 do throwError "the suffix message is wrong: {claim.2}"
      unless data ⟨⟩ == 23 do throwError "the composite output is not the export of this run"

/-- SourceRoutingExample SR3: the routing theorem accepts the ordinary whole prover, built by
`Prover.append`, and the actual input data. -/
example (hidden secret : Nat) :=
  OracleVerifier.run_append prefixVerifier (fun _ => suffixVerifier) compatible ()
    (inputData hidden) (prover secret)

/-! QueryBounds 14, restated (statement level): on an appended transcript built from separate
prefix and suffix transcripts, the routed prefix data is the prefix transcript's own payload. -/

def prefixTranscript (secret : Nat) : PathAlong oracleSig firstProtocol := ⟨(20, secret), ⟨⟩⟩

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
        (sumData (inputData hidden) (payloads combined
          (PathAlong.append oracleSig firstProtocol (fun _ => secondProtocol)
            (prefixTranscript secret) suffixTranscript)))⟩ :
      (p : FreeM.Path firstProtocol) ×
        (∀ i, (sumFamily inputs (pathFamily firstProtocol p)).Realization i)) =
      ⟨projectPathAlong oracleSig firstProtocol (prefixTranscript secret),
        sumData (inputData hidden) (payloads firstProtocol (prefixTranscript secret))⟩ :=
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

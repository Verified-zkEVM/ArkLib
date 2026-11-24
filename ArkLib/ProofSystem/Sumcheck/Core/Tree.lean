/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.ProofSystem.Sumcheck.Core.SingleRound

/-! # The fixed Sumcheck tree

The full run has one polynomial message and one challenge per variable. Messages and
challenges do not select shape. The sampler leaves the challenge distribution to its handler.
-/

@[expose] public section

namespace Sumcheck.Core

open Polynomial PFunctor FreeM Interaction.Core Interaction.TwoParty.Lens

variable (R : Type) [CommSemiring R] (deg : ℕ)

/-- The `n`-round Sumcheck protocol: `n` copies of `round R deg`. -/
@[reducible]
def protocol : ℕ → OracleProtocol.{0}
  | 0 => .pure ⟨⟩
  | n + 1 => .liftBind (.oracle (R⦃≤ deg⦄[X]) inferInstance) fun _ =>
      .liftBind (.challenge R) fun _ => protocol n

/-- One more round is one oracle node and one challenge node before the remaining rounds. -/
theorem protocol_succ (n : ℕ) : protocol R deg (n + 1) =
    .liftBind (.oracle (R⦃≤ deg⦄[X]) inferInstance) fun _ =>
      .liftBind (.challenge R) fun _ => protocol R deg n := rfl

/-- The unique shape path of the `n`-round protocol. -/
def protocolPath : (n : ℕ) → Path (protocol R deg n)
  | 0 => ⟨⟩
  | n + 1 => ⟨⟨⟩, ⟨⟨⟩, protocolPath n⟩⟩

/-- Challenges never select shape: every shape path of the protocol is the unique one. -/
theorem protocolPath_eq : ∀ (n : ℕ) (p : Path (protocol R deg n)), p = protocolPath R deg n
  | 0, ⟨⟩ => rfl
  | n + 1, ⟨⟨⟩, ⟨⟨⟩, p⟩⟩ => by
    rw [protocolPath_eq n p]
    rfl

variable {R deg}

/-- Every full transcript projects to the unique shape path, whatever its messages and
challenges. -/
theorem project_eq_protocolPath {n : ℕ} (tr : Transcript oracleSig (protocol R deg n)) :
    tr.path = protocolPath R deg n :=
  protocolPath_eq R deg n _

/-- Prepend one round to a transcript of the remaining rounds. -/
def consTranscript {n : ℕ} (msg : R⦃≤ deg⦄[X]) (chal : R)
    (tail : Transcript oracleSig (protocol R deg n)) :
    Transcript oracleSig (protocol R deg (n + 1)) := ⟨msg, ⟨chal, tail⟩⟩

/-- The round polynomial of the first round of a transcript. -/
def headMessage {n : ℕ} (tr : Transcript oracleSig (protocol R deg (n + 1))) : R⦃≤ deg⦄[X] :=
  tr.1

/-- The challenge of the first round of a transcript. -/
def headChallenge {n : ℕ} (tr : Transcript oracleSig (protocol R deg (n + 1))) : R := tr.2.1

/-- The transcript of the remaining rounds. -/
def tailTranscript {n : ℕ} (tr : Transcript oracleSig (protocol R deg (n + 1))) :
    Transcript oracleSig (protocol R deg n) := tr.2.2

@[simp] theorem headMessage_consTranscript {n : ℕ} (msg : R⦃≤ deg⦄[X]) (chal : R)
    (tail : Transcript oracleSig (protocol R deg n)) :
    headMessage (consTranscript msg chal tail) = msg := rfl

@[simp] theorem headChallenge_consTranscript {n : ℕ} (msg : R⦃≤ deg⦄[X]) (chal : R)
    (tail : Transcript oracleSig (protocol R deg n)) :
    headChallenge (consTranscript msg chal tail) = chal := rfl

@[simp] theorem tailTranscript_consTranscript {n : ℕ} (msg : R⦃≤ deg⦄[X]) (chal : R)
    (tail : Transcript oracleSig (protocol R deg n)) :
    tailTranscript (consTranscript msg chal tail) = tail := rfl

/-- A transcript is determined by its first round and its tail. -/
theorem consTranscript_eta {n : ℕ} (tr : Transcript oracleSig (protocol R deg (n + 1))) :
    consTranscript (headMessage tr) (headChallenge tr) (tailTranscript tr) = tr := rfl

section Uniform

/-- Every challenge of the protocol is a ring element, so it can be sampled uniformly. Oracle
nodes are not challenge nodes, and each challenge node of one more round is the first round's
challenge or a challenge of the remaining rounds. -/
@[instance_reducible]
def challengeSampleable (R : Type) [CommSemiring R] [SampleableType R] (deg : ℕ) :
    (k : ℕ) → (c : ChallengeNode oracleSig (protocol R deg k)) →
      SampleableType (challengeSpec oracleSig (protocol R deg k) c)
  | 0, ⟨n, _⟩ => nomatch n
  | _ + 1, ⟨.inl _, h⟩ => nomatch h
  | _ + 1, ⟨.inr ⟨_, .inl _⟩, _⟩ => inferInstanceAs (SampleableType R)
  | k + 1, ⟨.inr ⟨_, .inr ⟨_, c⟩⟩, h⟩ => challengeSampleable R deg k ⟨c, h⟩

/-- Uniform sampling at every challenge node of the fixed protocol. -/
instance (R : Type) [CommSemiring R] [SampleableType R] (deg k : ℕ) :
    ∀ c, SampleableType (challengeSpec oracleSig (protocol R deg k) c) :=
  challengeSampleable R deg k

end Uniform

variable (R deg)
open OracleComp OracleSpec Interaction.Oracle

/-- Lift the queries of the remaining rounds to a replicated protocol with one more round. -/
def tailLift (k : ℕ) (p : Path (protocol R deg k)) :
    QueryImpl (oracleMessageSpec (protocol R deg k) p)
      (OracleComp (oracleMessageSpec (protocol R deg (k + 1)) ⟨⟨⟩, ⟨⟨⟩, p⟩⟩)) :=
  fun q => liftM
    ((oracleMessageSpec (protocol R deg (k + 1)) ⟨⟨⟩, ⟨⟨⟩, p⟩⟩).query ⟨.inr q.1, q.2⟩)

/-- Lift the round-message queries into the queries of the final decision: the ambient oracle
and the path's oracle bundle. The interaction-layer `indexedVerifier` and the compatibility
`verifier` both use this lift. -/
def decisionLift (n : ℕ) {ι : Type} (ambient : OracleSpec ι) (p : Path (protocol R deg n)) :
    QueryImpl (oracleMessageSpec (protocol R deg n) p)
      (OracleComp (ambient + (pathBundle (polyFamily R deg n) (protocol R deg n) p).spec)) :=
  fun q => liftM ((ambient +
    (pathBundle (polyFamily R deg n) (protocol R deg n) p).spec).query (.inr (.inr q)))

variable {R deg}

/-- Answering the lifted message queries from the run's data, with ambient queries answered in
any lawful monad, is a pure computation of the transcript's oracle messages. -/
theorem simulateQ_decisionLift_monad {n : ℕ} {ι : Type} {ambient : OracleSpec ι}
    {m : Type → Type} [Monad m] [LawfulMonad m]
    (impl : QueryImpl ambient m) (p : Path (protocol R deg n))
    (data : ∀ i, PolynomialData R n deg i) (pl : ∀ i, OracleMessage (protocol R deg n) p i)
    {α : Type} (oa : OracleComp (oracleMessageSpec (protocol R deg n) p) α) :
    simulateQ (QueryImpl.addLift impl ((pathBundle (polyFamily R deg n) (protocol R deg n)
      p).answer (data, pl))) (simulateQ (decisionLift R deg n ambient p) oa) =
      (pure (simulateQ ((oracleMessageFamily (protocol R deg n) p).behaviorOfRealizations pl) oa) :
        m α) := by
  refine (QueryImpl.simulateQ_simulateQ_eq_of_apply
    (impl := ((oracleMessageFamily (protocol R deg n) p).behaviorOfRealizations pl).liftTarget m)
    (fun t => ?_) oa).trans ?_
  · simp only [QueryImpl.addLift_def]
    exact QueryImpl.simulateQ_add_query_right _ _ _
  · rw [simulateQ_liftTarget]
    rfl

end Sumcheck.Core

/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.ProofSystem.Sumcheck.Core.SingleRound
public import ArkLib.ProofSystem.Sumcheck.Core.MessageTree

/-! # The fixed Sumcheck tree

The full run has one polynomial message and one public challenge per variable. Messages and
challenges do not select shape. The sampler leaves the challenge distribution to its handler.
-/

@[expose] public section

namespace Sumcheck.Core

open Polynomial PFunctor FreeM Interaction.Core Interaction.TwoParty.Lens

variable (R : Type) [CommSemiring R] (deg : ℕ)

/-- The `n`-round Sumcheck protocol: `n` copies of `round R deg`. -/
@[reducible]
def protocol (n : ℕ) : OracleProtocol.{0} :=
  Interpreted.protocol R R⦃≤ deg⦄[X] (fun q r => q.val.eval r) n

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

/-- Splitting one round from a replicated protocol recovers the remaining shape path. -/
theorem split_protocol_succ_suffix {k : ℕ} (msg : R⦃≤ deg⦄[X]) (r : R)
    (tail : PathAlong oracleSig (protocol R deg k)) :
    (Path.split (protocol R deg 1) (fun _ => protocol R deg k)
      (projectPathAlong oracleSig (protocol R deg (k + 1)) ⟨msg, r, tail⟩)).2 =
        projectPathAlong oracleSig (protocol R deg k) tail := split_round_suffix msg r tail

/-- Every full transcript projects to the unique shape path, whatever its messages and
challenges. -/
theorem project_eq_protocolPath {n : ℕ} (tr : PathAlong oracleSig (protocol R deg n)) :
    projectPathAlong oracleSig (protocol R deg n) tr = protocolPath R deg n :=
  protocolPath_eq R deg n _

/-- Prepend one round to a transcript of the remaining rounds. -/
def consTranscript {n : ℕ} (msg : R⦃≤ deg⦄[X]) (chal : R)
    (tail : PathAlong oracleSig (protocol R deg n)) :
    PathAlong oracleSig (protocol R deg (n + 1)) := ⟨msg, ⟨chal, tail⟩⟩

/-- The round polynomial of the first round of a transcript. -/
def headMessage {n : ℕ} (tr : PathAlong oracleSig (protocol R deg (n + 1))) : R⦃≤ deg⦄[X] :=
  tr.1

/-- The challenge of the first round of a transcript. -/
def headChallenge {n : ℕ} (tr : PathAlong oracleSig (protocol R deg (n + 1))) : R := tr.2.1

/-- The transcript of the remaining rounds. -/
def tailTranscript {n : ℕ} (tr : PathAlong oracleSig (protocol R deg (n + 1))) :
    PathAlong oracleSig (protocol R deg n) := tr.2.2

@[simp] theorem headMessage_consTranscript {n : ℕ} (msg : R⦃≤ deg⦄[X]) (chal : R)
    (tail : PathAlong oracleSig (protocol R deg n)) :
    headMessage (consTranscript msg chal tail) = msg := rfl

@[simp] theorem headChallenge_consTranscript {n : ℕ} (msg : R⦃≤ deg⦄[X]) (chal : R)
    (tail : PathAlong oracleSig (protocol R deg n)) :
    headChallenge (consTranscript msg chal tail) = chal := rfl

@[simp] theorem tailTranscript_consTranscript {n : ℕ} (msg : R⦃≤ deg⦄[X]) (chal : R)
    (tail : PathAlong oracleSig (protocol R deg n)) :
    tailTranscript (consTranscript msg chal tail) = tail := rfl

/-- A transcript is determined by its first round and its tail. -/
theorem consTranscript_eta {n : ℕ} (tr : PathAlong oracleSig (protocol R deg (n + 1))) :
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
open OracleComp OracleSpec

/-- Lift the queries of the remaining rounds to a replicated protocol with one more round. -/
def tailLift (k : ℕ) (p : Path (protocol R deg k)) :
    QueryImpl (oracles (protocol R deg k) p)
      (OracleComp (oracles (protocol R deg (k + 1)) ⟨⟨⟩, ⟨⟨⟩, p⟩⟩)) :=
  fun q => liftM
    ((oracles (protocol R deg (k + 1)) ⟨⟨⟩, ⟨⟨⟩, p⟩⟩).query ⟨.inr q.1, q.2⟩)


end Sumcheck.Core

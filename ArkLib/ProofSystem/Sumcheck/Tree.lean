/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.ProofSystem.Sumcheck.SingleRound
public import ArkLib.ProofSystem.Sumcheck.InterpretedPath

/-! # The fixed Sumcheck tree

The full run has one polynomial message and one challenge per variable. Messages and
challenges do not select shape. The sampler leaves the challenge distribution to its handler.
-/

@[expose] public section

namespace Sumcheck

open Polynomial PFunctor FreeM Interaction Interaction.TwoParty.Lens

variable (R : Type) [CommSemiring R] (deg : ℕ)

/-- The `n`-round Sumcheck protocol: `n` copies of `round R deg`. -/
@[reducible]
def protocol (n : ℕ) : OracleProtocol.{0} :=
  Interpreted.protocol R R⦃≤ deg⦄[X] (fun q r => q.val.eval r) n

/-- One more round is one oracle node and one challenge node before the remaining rounds. -/
theorem protocol_succ (n : ℕ) : protocol R deg (n + 1) =
    .liftBind (.oracle (R⦃≤ deg⦄[X]) inferInstance) fun _ =>
      .liftBind (.challenge R) fun _ => protocol R deg n := rfl

variable {R deg}

/-- Splitting one round from a replicated protocol recovers the remaining shape path. -/
theorem split_protocol_succ_suffix {k : ℕ} (msg : R⦃≤ deg⦄[X]) (r : R)
    (tail : Transcript oracleSig (protocol R deg k)) :
    (Path.split (protocol R deg 1) (fun _ => protocol R deg k)
      (Transcript.path (l := oracleSig) (s := (protocol R deg (k + 1))) ⟨msg, r, tail⟩)).2 =
        tail.path := split_round_suffix msg r tail

/-- Every full transcript projects to the unique shape path, whatever its messages and
challenges. -/
theorem project_eq_shape {n : ℕ} (tr : Transcript oracleSig (protocol R deg n)) :
    tr.path = Interpreted.shape n :=
  Interpreted.shape_unique n _

omit [CommSemiring R] in
/-- Prepend one round to a transcript of the remaining rounds, at any message carrier. -/
def consTranscript {M : Type} {eval : M → R → R} {n : ℕ} (msg : M) (chal : R)
    (tail : Transcript oracleSig (Interpreted.protocol R M eval n)) :
    Transcript oracleSig (Interpreted.protocol R M eval (n + 1)) := ⟨msg, ⟨chal, tail⟩⟩

omit [CommSemiring R] in
/-- The head message of a prepended round is its message. -/
@[simp] theorem message_consTranscript {M : Type} {eval : M → R → R} {n : ℕ} (msg : M)
    (chal : R) (tail : Transcript oracleSig (Interpreted.protocol R M eval n)) :
    Interpreted.message (consTranscript msg chal tail) = msg := rfl

omit [CommSemiring R] in
/-- The head challenge of a prepended round is its challenge. -/
@[simp] theorem challenge_consTranscript {M : Type} {eval : M → R → R} {n : ℕ} (msg : M)
    (chal : R) (tail : Transcript oracleSig (Interpreted.protocol R M eval n)) :
    Interpreted.challenge (consTranscript msg chal tail) = chal := rfl

omit [CommSemiring R] in
/-- The tail of a prepended round is the given transcript. -/
@[simp] theorem tail_consTranscript {M : Type} {eval : M → R → R} {n : ℕ} (msg : M)
    (chal : R) (tail : Transcript oracleSig (Interpreted.protocol R M eval n)) :
    Interpreted.tail (consTranscript msg chal tail) = tail := rfl

omit [CommSemiring R] in
/-- A transcript is determined by its first round and its tail. -/
theorem consTranscript_eta {M : Type} {eval : M → R → R} {n : ℕ}
    (tr : Transcript oracleSig (Interpreted.protocol R M eval (n + 1))) :
    consTranscript (Interpreted.message tr) (Interpreted.challenge tr) (Interpreted.tail tr) = tr :=
  rfl

section Uniform

/-- Every challenge of the protocol is a ring element, so it can be sampled uniformly: the
interpreted tree's construction at polynomial evaluation. -/
@[instance_reducible]
def challengeSampleable (R : Type) [CommSemiring R] [SampleableType R] (deg k : ℕ) :
    (c : ChallengeNode oracleSig (protocol R deg k)) →
      SampleableType (challengeSpec oracleSig (protocol R deg k) c) :=
  Interpreted.challengeSampleable R _ _ k

/-- Uniform sampling at every challenge node of the fixed protocol. -/
instance (R : Type) [CommSemiring R] [SampleableType R] (deg k : ℕ) :
    ∀ c, SampleableType (challengeSpec oracleSig (protocol R deg k) c) :=
  challengeSampleable R deg k

end Uniform

variable (R deg)
open OracleComp OracleSpec Interaction.Oracle

/-- Lift the round-message queries into the queries of the final decision: the ambient oracle
and the path's oracle bundle. This is the path lift `pathLift` with the input polynomial family.
The interaction-layer `indexedVerifier` and the compatibility `verifier` both use this lift. -/
def decisionLift (n : ℕ) {ι : Type} (ambient : OracleSpec ι) (p : Path (protocol R deg n)) :
    QueryImpl (oracleMessageSpec (protocol R deg n) p)
      (OracleComp (ambient + (pathBundle (polynomialFamily R n deg) (protocol R deg n) p).spec)) :=
  pathLift ambient (polynomialFamily R n deg) p

variable {R deg}

/-- Answering the lifted message queries from the run's data, with ambient queries answered in
any lawful monad, is a pure computation of the transcript's oracle messages. -/
theorem simulateQ_decisionLift_monad {n : ℕ} {ι : Type} {ambient : OracleSpec ι}
    {m : Type → Type} [Monad m] [LawfulMonad m]
    (impl : QueryImpl ambient m) (p : Path (protocol R deg n))
    (data : ∀ i, PolynomialData R n deg i) (pl : ∀ i, OracleMessage (protocol R deg n) p i)
    {α : Type} (oa : OracleComp (oracleMessageSpec (protocol R deg n) p) α) :
    simulateQ (QueryImpl.addLift impl ((pathBundle (polynomialFamily R n deg) (protocol R deg n)
      p).answer (data, pl))) (simulateQ (decisionLift R deg n ambient p) oa) =
      (pure (simulateQ ((oracleMessageFamily (protocol R deg n) p).behaviorOfRealizations pl) oa) :
        m α) :=
  simulateQ_pathLift (inputs := polynomialFamily R n deg) impl p data pl oa

end Sumcheck

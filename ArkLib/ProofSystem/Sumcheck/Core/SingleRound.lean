/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Interaction.Core.Composition
public import ArkLib.ProofSystem.Sumcheck.Core.Types

/-!
# One Sumcheck round in the interaction layer

A round is a fixed two-node oracle protocol. The prover sends its round polynomial as an oracle
message with evaluation queries, and the verifier replies with one challenge in the ring. Both
carriers are fixed by the protocol parameters, so neither the message nor the challenge selects
the remaining protocol.

The honest round strategy has a `pure` slot at the challenge node and a `pure` leaf. It reacts to
the challenge only by choosing its pure continuation, as the legacy `receiveChallenge` does.

-/

@[expose] public section

universe uI wI

namespace Sumcheck.Core

open Polynomial PFunctor FreeM Interaction.Core Interaction.TwoParty.Lens Interaction.Oracle

variable (R : Type) [CommSemiring R] (deg : ℕ)

omit [CommSemiring R] in
/-- Evaluation queries at ring points on the message carrier `M`, answered by `eval`. -/
@[reducible]
def evalInterface (M : Type) (eval : M → R → R) : OracleInterface M where
  Query := R
  toOC.spec := R →ₒ R
  toOC.impl point := do return eval (← read) point

omit [CommSemiring R] in
/-- One round over the message carrier `M`: an oracle for the round message with evaluation
queries answered by `eval`, then one ring challenge. -/
@[reducible]
def roundOn (M : Type) (eval : M → R → R) : OracleProtocol.{0} :=
  .liftBind (.oracle M (evalInterface R M eval)) fun _ =>
    .liftBind (.challenge R) fun _ => .pure ⟨⟩

/-- One round: an evaluation oracle for the round polynomial, then one ring challenge. -/
@[implicit_reducible]
def round : OracleProtocol.{0} :=
  .liftBind (.oracle (R⦃≤ deg⦄[X]) inferInstance) fun _ =>
    .liftBind (.challenge R) fun _ => .pure ⟨⟩

/-- The unique shape path of a round. Neither move selects a branch. -/
def roundPath : Path (round R deg) := ⟨⟨⟩, ⟨⟨⟩, ⟨⟩⟩⟩

/-- Every shape path of a round is the unique one. -/
theorem roundPath_eq (p : Path (round R deg)) : p = roundPath R deg := by
  rcases p with ⟨⟨⟩, ⟨⟨⟩, ⟨⟩⟩⟩
  rfl

variable {R deg}

/-- The full transcript of a round with the given message and challenge. -/
def roundTranscript (msg : R⦃≤ deg⦄[X]) (chal : R) : PathAlong oracleSig (round R deg) :=
  ⟨msg, ⟨chal, ⟨⟩⟩⟩

/-- The round polynomial recorded in a round transcript. -/
def roundMessage (tr : PathAlong oracleSig (round R deg)) : R⦃≤ deg⦄[X] := tr.1

/-- The challenge recorded in a round transcript. -/
def roundChallenge (tr : PathAlong oracleSig (round R deg)) : R := tr.2.1

/-- The message of a round transcript is the message it was built from. -/
@[simp] theorem roundMessage_roundTranscript (msg : R⦃≤ deg⦄[X]) (chal : R) :
    roundMessage (roundTranscript msg chal) = msg := rfl

/-- The challenge of a round transcript is the challenge it was built from. -/
@[simp] theorem roundChallenge_roundTranscript (msg : R⦃≤ deg⦄[X]) (chal : R) :
    roundChallenge (roundTranscript msg chal) = chal := rfl

/-- A round transcript is determined by its message and challenge. -/
theorem roundTranscript_eta (tr : PathAlong oracleSig (round R deg)) :
    roundTranscript (roundMessage tr) (roundChallenge tr) = tr := by
  rcases tr with ⟨msg, ⟨chal, ⟨⟩⟩⟩
  rfl

/-- Every round transcript projects to the unique shape path, whatever its moves. -/
theorem project_roundTranscript (msg : R⦃≤ deg⦄[X]) (chal : R) :
    projectPathAlong oracleSig (round R deg) (roundTranscript msg chal) = roundPath R deg :=
  roundPath_eq R deg _

/-- The verifier view of a round records the challenge and erases the message. -/
def viewChallenge {p : Path (round R deg)} (v : View (round R deg) p) : R := v.1.2.1

/-- The challenge in the view of a transcript is the transcript's challenge. -/
@[simp] theorem viewChallenge_toView (tr : PathAlong oracleSig (round R deg)) :
    viewChallenge (toView (round R deg) tr) = roundChallenge tr := rfl

/-- The challenge node of a round, named by shape branches alone. -/
def roundChallengeNode : ChallengeNode oracleSig (round R deg) := ⟨.inr ⟨⟨⟩, .inl ⟨⟩⟩, rfl⟩

/-- The honest round strategy: send `msg`, then continue purely with the received challenge.

The slot at the challenge node and the leaf are `pure`. The only possibly effectful slot is the
first one, which is also `pure` here. -/
def roundProver {m : Type → Type} [Monad m] {Out : PathAlong oracleSig (round R deg) → Type}
    (msg : R⦃≤ deg⦄[X]) (next : (chal : R) → Out (roundTranscript msg chal)) :
    Focal oracleSig m (round R deg) Out :=
  pure ⟨msg, pure fun chal => pure (next chal)⟩

/-- Projection of a round followed by a suffix erases the round's two private branches. -/
@[simp] theorem project_append_round {s : OracleProtocol} (msg : R⦃≤ deg⦄[X]) (chal : R)
    (tail : PathAlong oracleSig s) :
    projectPathAlong oracleSig ((round R deg).append fun _ => s) ⟨msg, ⟨chal, tail⟩⟩ =
      ⟨⟨⟩, ⟨⟨⟩, projectPathAlong oracleSig s tail⟩⟩ := rfl

section Run

attribute [local implicit_reducible] projectPathAlong projectPathAlongLocalMap
  Displayed.LocalMap.toHom Displayed.LocalMap.toHomFun owner Node Node.position challengeSpec
  roundTranscript

/-- Splitting the shape of a round followed by a suffix recovers the suffix shape. -/
theorem split_round_suffix {s : OracleProtocol} (msg : R⦃≤ deg⦄[X]) (chal : R)
    (tail : PathAlong oracleSig s) :
    (Path.split (round R deg) (fun _ => s)
      (projectPathAlong oracleSig _ ⟨msg, ⟨chal, tail⟩⟩)).2 =
        projectPathAlong oracleSig s tail := rfl

/-- The sampler of a round has a pure slot at the message node and draws at the challenge node. -/
theorem samplerEnd_round {m : Type → Type} [Monad m]
    (draw : (c : ChallengeNode oracleSig (round R deg)) → m (challengeSpec oracleSig _ c)) :
    samplerEnd oracleSig (round R deg) draw =
      (pure fun _ => (fun chal => ⟨chal, ⟨⟩⟩) <$> draw roundChallengeNode :
        m ((_ : R⦃≤ deg⦄[X]) → m ((_ : R) × PUnit))) := rfl

/-- Running the honest round against the sampler draws once and records the honest message. -/
theorem run_roundProver {m : Type → Type} [Monad m] [LawfulMonad m]
    {Out : PathAlong oracleSig (round R deg) → Type}
    (msg : R⦃≤ deg⦄[X]) (next : (chal : R) → Out (roundTranscript msg chal))
    (draw : (c : ChallengeNode oracleSig (round R deg)) → m (challengeSpec oracleSig _ c)) :
    Interaction.TwoParty.Lens.run (round R deg) (roundProver msg next)
        (sampler oracleSig (round R deg) draw) =
      (fun chal => ⟨roundTranscript msg chal, next chal, ⟨⟩⟩) <$> draw roundChallengeNode := by
  change Interaction.TwoParty.Lens.run (.liftBind _ _) _ _ = _
  simp only [sampler, PureEnd.toStrategy, samplerEnd_round]
  simp only [run_node, roundProver, owner, oracleSig, Choice, Move, Choice.map, step,
    Schedule.seq, PureEnd.mapOutput, LawfulMonad.pure_bind, LawfulApplicative.map_pure,
    bind_map_left]
  simp only [FreeM.pure_eq_pure, run_done, LawfulApplicative.map_pure, Functor.map_map,
    LawfulMonad.bind_pure_comp]
  simp only [liftBind_eq, bind_eq_bind, Displayed.pure_eq]
  exact (Functor.map_map _ _ _).trans rfl

end Run

section Routing
variable {s : OracleProtocol}

/-- The view of a round followed by `s` splits into the round's view and the view of `s`. -/
theorem split_toView_round (msg : R⦃≤ deg⦄[X]) (chal : R) (tail : PathAlong oracleSig s) :
    View.split (round R deg) (fun _ => s) _
        (toView ((round R deg).append fun _ => s) ⟨msg, ⟨chal, tail⟩⟩) =
      (toView (round R deg) ⟨msg, ⟨chal, ⟨⟩⟩⟩, toView s tail) := by
  have h := splitFiber_val viewSig (round R deg) (fun _ => s) _
    (show Fiber viewSig _ _ from toView ((round R deg).append fun _ => s) ⟨msg, ⟨chal, tail⟩⟩)
  exact Prod.ext (Subtype.ext h.1) (Subtype.ext (eq_of_heq h.2))


variable {I : Type uI} {A : I → Type}
  (inputs : Interaction.Oracle.OracleFamily.{uI, 0, wI} I A)

/-- The first round of a transcript of a round followed by `s`. -/
def appendHead (tr : PathAlong oracleSig ((round R deg).append fun _ => s)) :
    PathAlong oracleSig (round R deg) :=
  ⟨tr.1, ⟨tr.2.1, ⟨⟩⟩⟩

/-- The transcript of `s` after the first round. -/
def appendTail (tr : PathAlong oracleSig ((round R deg).append fun _ => s)) :
    PathAlong oracleSig s :=
  tr.2.2

/-- The first round of a run of a round followed by `s` sees the inputs and its own message. -/
theorem prefixRoute_round (x : ∀ i, A i) (msg : R⦃≤ deg⦄[X]) (chal : R)
    (tail : PathAlong oracleSig s) :
    (OracleVerifier.prefixRoute (inputs := inputs) (s₁ := round R deg) (s₂ := fun _ => s)
        (projectPathAlong oracleSig _ ⟨msg, ⟨chal, tail⟩⟩)).f
        ((x, payloads ((round R deg).append fun _ => s) ⟨msg, ⟨chal, tail⟩⟩)) =
      (x, payloads (round R deg) ⟨msg, ⟨chal, ⟨⟩⟩⟩) := by
  refine Prod.ext ?_ ?_
  · rfl
  · funext i
    rcases i with i | i
    · rfl
    · exact i.elim

end Routing

end Sumcheck.Core

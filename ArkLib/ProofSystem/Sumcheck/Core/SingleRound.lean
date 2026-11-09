/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Interaction.Core.Composition
public import ArkLib.ProofSystem.Sumcheck.Spec.PolynomialInterface

/-!
# One Sumcheck round in the interaction layer

A round is a fixed two-node oracle protocol. The prover sends its round polynomial as an oracle
message with evaluation queries, and the verifier replies with one challenge in the ring. Both
carriers are fixed by the protocol parameters, so neither the message nor the challenge selects
the remaining protocol.

The honest round strategy has a `pure` slot at the challenge node and a `pure` leaf. It reacts to
the challenge only by choosing its pure continuation, as the legacy `receiveChallenge` does.

A round of a multivariate statement sees the multivariate input through `projectionMap`, the
oracle map from the multivariate polynomial to the univariate round polynomial. Its data map is
the legacy `Spec.SingleRound.projectedRoundPolynomial`, and its query implementation is the legacy
`Spec.SingleRound.simulateProjectedRoundPolynomial`, which answers a univariate evaluation query
with one multivariate query per point of the remaining domain.
-/

@[expose] public section

namespace Sumcheck.Core

open Polynomial PFunctor FreeM Interaction.Core Interaction.TwoParty.Lens Interaction.Oracle

variable (R : Type) [CommSemiring R] (deg : ℕ)

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

@[simp] theorem roundMessage_roundTranscript (msg : R⦃≤ deg⦄[X]) (chal : R) :
    roundMessage (roundTranscript msg chal) = msg := rfl

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

/-! ## The projection map -/

section Projection

variable (R deg) (n : ℕ) {d : ℕ} (D : Fin d ↪ R)

/-- The univariate round polynomial with evaluation queries. -/
noncomputable def messageFamily : OracleFamily Unit (Spec.SingleRound.Simple.OStmtIn R deg) :=
  ⟨fun _ => inferInstance⟩

/-- The projection of the multivariate input to the univariate polynomial of round `i`: the sum of
the input over the remaining domain, with the earlier variables fixed to the statement's
challenges. A univariate evaluation query makes one multivariate query per remaining point. -/
noncomputable def projectionMap (i : Fin n) (stmt : Spec.StatementRound R n i.castSucc) :
    OracleMap (Spec.polynomialFamily R n deg) (messageFamily R deg) where
  f x _ := Spec.SingleRound.projectedRoundPolynomial R n deg D i stmt.challenges (x ())
  impl := Spec.SingleRound.simulateProjectedRoundPolynomial R n deg D i stmt
  law x q := Spec.SingleRound.simulateProjectedRoundPolynomial_eq R n deg D i stmt x q

variable {R deg n D}

/-- The projected data is the legacy projected round polynomial. -/
@[simp] theorem projectionMap_f (i : Fin n) (stmt : Spec.StatementRound R n i.castSucc)
    (x : ∀ j, Spec.OracleStatement R n deg j) (u : Unit) :
    (projectionMap R deg n D i stmt).f x u =
      Spec.SingleRound.projectedRoundPolynomial R n deg D i stmt.challenges (x ()) := rfl

/-- Answering a projected query from the multivariate input evaluates the projected round
polynomial at the query point. -/
theorem simulateQ_projectionMap (i : Fin n) (stmt : Spec.StatementRound R n i.castSucc)
    (x : ∀ j, Spec.OracleStatement R n deg j) (r : R) :
    simulateQ ((Spec.polynomialFamily R n deg).behaviorOfRealizations x)
        ((projectionMap R deg n D i stmt).impl ⟨(), r⟩) =
      (Spec.SingleRound.projectedRoundPolynomial R n deg D i stmt.challenges (x ())).val.eval
        r :=
  (projectionMap R deg n D i stmt).law x ⟨(), r⟩

end Projection

section Run

attribute [local implicit_reducible] projectPathAlong projectPathAlongLocalMap
  Displayed.LocalMap.toHom Displayed.LocalMap.toHomFun owner Node Node.position challengeSpec
  roundTranscript

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

end Sumcheck.Core

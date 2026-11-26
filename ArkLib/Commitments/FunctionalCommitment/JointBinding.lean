/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Commitments.FunctionalCommitment.OneMessage
public import ArkLib.Interaction.Composition

/-!
# Function binding for functional commitments

The adversary sends each claim after it has seen the challenges from all preceding openings.
One prover controls the resulting interaction. The verifier checks the claims in order after
the last opening, so its oracle calls cannot influence the prover's later claims.
-/

@[expose] public section

open OracleComp OracleSpec Interaction PFunctor FreeM
open scoped ENNReal

namespace FunctionalCommitment

variable {ι : Type} {ambient : OracleSpec.{0, 0} ι} {Data : Type} {I : OracleInterface Data}
variable (FC : FunctionalCommitment ambient Data I)

/-- The prover sends a query and claimed answer before each opening. -/
def chain : ℕ → Protocol
  | 0 => .pure ()
  | k + 1 => .liftBind (.message ((q : I.Query) × I.spec q)) fun qr =>
      (FC.openSpec qr.1).append fun _ => chain k

/-- The adversary chooses a commitment and one prover for the entire chain. -/
abbrev JointAdversary (L : ℕ) :=
  FC.PP → OracleComp (unifSpec + ambient)
    (FC.Cm × Prover plainSig (unifSpec + ambient) (FC.chain L) (fun _ => PUnit))

namespace JointBinding

/-- The sampler draws a value for each challenge occurrence in the protocol. -/
abbrev Draw (s : Protocol) :=
  (c : ChallengeNode plainSig s) → OracleComp (unifSpec + ambient) (challengeSpec plainSig s c)

/-- The opening sampler uses the game's private coins. -/
abbrev openingDraw (chal : FC.ChallengeSampler) (q : I.Query) :
    Draw (ambient := ambient) (FC.openSpec q) :=
  fun c => liftComp (chal q c) (unifSpec + ambient)

/-- The chain uses the sampler for the query sent at each claim node. -/
def chainDraw (chal : FC.ChallengeSampler) :
    (L : ℕ) → Draw (ambient := ambient) (FC.chain L)
  | 0, c => c.val.elim
  | _ + 1, ⟨.inl _, h⟩ => nomatch h
  | k + 1, ⟨.inr ⟨qr, c⟩, h⟩ =>
    combineDraw plainSig (FC.openSpec qr.1) (fun _ => FC.chain k)
      (openingDraw FC chal qr.1) (fun _ => chainDraw chal k) ⟨c, h⟩

/-- Each completed opening records the claim and its protocol transcript. -/
abbrev Opening :=
  (qr : (q : I.Query) × I.spec q) × Transcript plainSig (FC.openSpec qr.1)

/-- The claim messages and opening transcripts partition the chain transcript in index order. -/
def openings : (L : ℕ) → Transcript plainSig (FC.chain L) → Fin L → Opening FC
  | 0, _ => Fin.elim0
  | k + 1, ⟨qr, tr⟩ =>
    let parts := Transcript.split (FC.openSpec qr.1) (fun _ => FC.chain k) tr
    Fin.cons ⟨qr, parts.1⟩ (openings k parts.2)

/-- The joint prover runs once and supplies the transcript of every opening. -/
def collect (chal : FC.ChallengeSampler) (L : ℕ)
    (P : Prover plainSig (unifSpec + ambient) (FC.chain L) (fun _ => PUnit)) :
    OracleComp (unifSpec + ambient) (Fin L → Opening FC) :=
  (fun r => openings FC L r.1) <$> TwoParty.Lens.run (FC.chain L) P
    (sampler plainSig _ (chainDraw FC chal L))

/-- The verifier checks a single recorded opening. -/
def decision (pp : FC.PP) (cm : FC.Cm) (o : Opening FC) :
    OracleComp (unifSpec + ambient) Bool :=
  Option.isSome <$> ((FC.verifier o.1.1).liftAmbient.decide (pp, cm, o.1.2)
    (Transcript.path o.2) (toPlainView _ o.2)).run

/-- The verifier checks every recorded opening before the game tests consistency. -/
noncomputable def checkOpenings {L : ℕ} (pp : FC.PP) (cm : FC.Cm)
    (os : Fin L → Opening FC) : OracleComp (unifSpec + ambient) Bool := do
  let verdicts ← Fin.mOfFn L fun i => decision FC pp cm (os i)
  return decide (∀ i, verdicts i = true) && noConsistentData (fun i => (os i).1)

end JointBinding

open JointBinding

/-- The adversary runs its prover once. After the full transcript is available, the verifier
checks every opening in index order. The adversary wins if all openings pass and no data agrees
with every claim. Even an empty chain runs the prover's terminal action. -/
noncomputable def functionBindingGame (chal : FC.ChallengeSampler) (L : ℕ)
    (A : FC.JointAdversary L) : OracleComp (unifSpec + ambient) Bool := do
  let pp ← FC.setup
  let (cm, P) ← A pp
  let os ← collect FC chal L P
  checkOpenings FC pp cm os

/-- The experiment interprets the game using the shared oracle state that `init` samples. -/
noncomputable def functionBindingExperiment {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl ambient (StateT σ ProbComp)) (chal : FC.ChallengeSampler) (L : ℕ)
    (A : FC.JointAdversary L) : ProbComp Bool :=
  runGame init impl (FC.functionBindingGame chal L A)

/-- The advantage measures the probability that the adversary wins. -/
noncomputable def functionBindingAdvantage {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl ambient (StateT σ ProbComp)) (chal : FC.ChallengeSampler) (L : ℕ)
    (A : FC.JointAdversary L) : ℝ≥0∞ :=
  Pr{let b ← FC.functionBindingExperiment init impl chal L A}[b = true]

/-- Every joint adversary in `Adv` wins with probability at most `ε`. -/
def FunctionBinding {σ : Type} (init : ProbComp σ) (impl : QueryImpl ambient (StateT σ ProbComp))
    (chal : FC.ChallengeSampler) (L : ℕ) (Adv : Set (FC.JointAdversary L)) (ε : ℝ≥0∞) : Prop :=
  ∀ A ∈ Adv, FC.functionBindingAdvantage init impl chal L A ≤ ε

/-- The prover follows a list of claims and opening strategies fixed in advance. -/
def JointBinding.fixedProver : (L : ℕ) → (Fin L → FC.Claim) →
    Prover plainSig (unifSpec + ambient) (FC.chain L) (fun _ => PUnit)
  | 0, _ => pure ⟨⟩
  | k + 1, cs => pure ⟨⟨(cs 0).1, (cs 0).2.1⟩,
      Prover.append (s₁ := FC.openSpec (cs 0).1) (s₂ := fun _ => FC.chain k)
        (Out := fun _ => PUnit) (cs 0).2.2 fun _ _ =>
          pure (fixedProver k fun i => cs i.succ)⟩

variable {FC} in
/-- The fixed adversary sends its chosen claims in order and runs the corresponding provers. -/
def FixedClaimAdversary.toJoint {L : ℕ} (A : FC.FixedClaimAdversary L) : FC.JointAdversary L :=
  fun pp => (fun out => (out.1, fixedProver FC L out.2)) <$> A pp

namespace JointBinding

private abbrev openingRun (chal : FC.ChallengeSampler) (c : FC.Claim) :=
  TwoParty.Lens.run (FC.openSpec c.1) c.2.2 (sampler plainSig _ (openingDraw FC chal c.1))

private abbrev recorded (c : FC.Claim) (tr : Transcript plainSig (FC.openSpec c.1)) :
    Opening FC := ⟨⟨c.1, c.2.1⟩, tr⟩

private theorem run_fixedProver_bind {β : Type} (chal : FC.ChallengeSampler) :
    ∀ (L : ℕ) (cs : Fin L → FC.Claim)
      (g : (Fin L → Opening FC) → OracleComp (unifSpec + ambient) β),
    (TwoParty.Lens.run (FC.chain L) (fixedProver FC L cs)
      (sampler plainSig _ (chainDraw FC chal L)) >>= fun r => g (openings FC L r.1)) =
    (piMOfFn L (fun i => openingRun FC chal (cs i)) >>= fun runs =>
      g (fun i => recorded FC (cs i) (runs i).1))
  | 0, cs, g => by
    simp only [chain, fixedProver, piMOfFn, LawfulMonad.pure_bind]
    erw [TwoParty.Lens.run_done]
    change (pure PUnit.unit >>= fun _ => (pure () : OracleComp (unifSpec + ambient) Unit) >>=
      fun _ => pure _) >>= _ = _
    simp only [LawfulMonad.pure_bind]
    congr 1
    funext i
    exact i.elim0
  | k + 1, cs, g => by
    refine (run_sampler_sender (l := plainSig) (a := .message ((q : I.Query) × I.spec q))
      (next := fun qr => (FC.openSpec qr.1).append fun _ => FC.chain k)
      rfl _ _ _).trans ?_
    simp only [fixedProver]
    change (TwoParty.Lens.run _
      (Prover.append (s₁ := FC.openSpec (cs 0).1) (s₂ := fun _ => FC.chain k)
        (Out := fun _ => PUnit) (cs 0).2.2 (fun _ _ => pure (fixedProver FC k fun i => cs i.succ)))
      (sampler plainSig _ (combineDraw plainSig _ _ (openingDraw FC chal (cs 0).1)
        (fun _ => chainDraw FC chal k))) >>= _) = _
    rw [← appendSampler_eq, run_appendSampler]
    simp only [LawfulMonad.pure_bind, bind_assoc, piMOfFn]
    refine bind_congr fun head => ?_
    simp only [openings, Transcript.split_append]
    rw [run_fixedProver_bind chal k (fun i => cs i.succ)
      (fun rest => g (Fin.cons (recorded FC (cs 0) head.1) rest))]
    refine bind_congr fun tail => congrArg g ?_
    funext i
    cases i using Fin.cases <;> simp [recorded]

end JointBinding

/-- The joint game against a fixed adversary runs exactly the fixed-claim game, including all
challenge draws and ambient queries. -/
theorem functionBindingGame_toJoint (chal : FC.ChallengeSampler) (L : ℕ)
    (A : FC.FixedClaimAdversary L) :
    FC.functionBindingGame chal L A.toJoint =
      FC.fixedClaimBindingGame chal L A := by
  simp only [functionBindingGame, FixedClaimAdversary.toJoint, fixedClaimBindingGame,
    collect, bind_map_left]
  refine bind_congr fun pp => bind_congr fun out => ?_
  rw [run_fixedProver_bind]
  simp only [interact, mOfFn_map_eq_map_piMOfFn, bind_map_left, checkOpenings,
    decision, recorded, openingRun]

/-- The fixed adversary has the same advantage when it sends its claims through the chain. -/
theorem functionBindingAdvantage_toJoint {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl ambient (StateT σ ProbComp)) (chal : FC.ChallengeSampler) (L : ℕ)
    (A : FC.FixedClaimAdversary L) :
    FC.functionBindingAdvantage init impl chal L A.toJoint =
      FC.fixedClaimBindingAdvantage init impl chal L A := by
  simp only [functionBindingAdvantage, functionBindingExperiment, functionBindingGame_toJoint,
    fixedClaimBindingAdvantage, fixedClaimBindingExperiment]

namespace JointBinding
open TwoParty.Lens

section Replay

variable {m : Type → Type} [Monad m]

/-- The replay prover sends the recorded messages of an opening with no challenge nodes. -/
def replayOpening :
    (s : Protocol) → IsEmpty (ChallengeNode plainSig s) → Transcript plainSig s →
      Focal plainSig m s (fun _ => PUnit)
  | .pure _, _, _ => pure ⟨⟩
  | .liftBind (.message _) next, h, ⟨x, tr⟩ =>
    pure ⟨x, replayOpening (next x) ⟨fun c => h.false ⟨.inr ⟨x, c.val⟩, c.property⟩⟩ tr⟩
  | .liftBind (.challenge _) _, h, _ => (h.false ⟨.inl ⟨⟩, rfl⟩).elim

/-- The runner recovers the recorded transcript without oracle calls. -/
private theorem run_replayOpening [LawfulMonad m] (s : Protocol)
    (h : IsEmpty (ChallengeNode plainSig s)) (tr : Transcript plainSig s)
    (draw : (c : ChallengeNode plainSig s) → m (challengeSpec plainSig s c)) :
    TwoParty.Lens.run s (replayOpening s h tr) (sampler plainSig s draw) =
      pure ⟨tr, ⟨⟩, ⟨⟩⟩ := by
  induction s using FreeM.rec with
  | pure a =>
    cases a
    cases tr
    simp [replayOpening, sampler, samplerEnd, PureEnd.toStrategy, PureEnd.mapOutput]
  | liftBind a next ih =>
    cases a with
    | message X =>
      obtain ⟨x, tr⟩ := tr
      rw [← _root_.bind_pure (TwoParty.Lens.run _ _ _)]
      erw [run_sampler_sender (l := plainSig) (a := .message X) (next := next) rfl]
      change (pure (α := (y : X) × Focal plainSig m (next y) (fun _ => PUnit)) _ >>= _) = _
      rw [LawfulMonad.pure_bind]
      erw [ih x]
      rw [LawfulMonad.pure_bind]
    | challenge C =>
      exact (h.false ⟨.inl ⟨⟩, rfl⟩).elim

end Replay

end JointBinding

/-- An opening has no challenges when its sampler has no node at which it can draw.
This includes every branch the prover can select by sending a message. -/
def NoOpeningChallenges : Prop := ∀ q, IsEmpty (ChallengeNode plainSig (FC.openSpec q))

namespace JointBinding

/-- The sampler has an empty domain at every query of a challenge-free scheme. -/
def emptySampler (h : FC.NoOpeningChallenges) : FC.ChallengeSampler :=
  fun q c => ((h q).false c).elim

/-- The fixed adversary pairs each claim with the prover that replays its opening. -/
def replayClaim (h : FC.NoOpeningChallenges) (o : Opening FC) : FC.Claim :=
  ⟨o.1.1, o.1.2, replayOpening _ (h o.1.1) o.2⟩

end JointBinding

variable {FC} in
/-- The joint adversary runs its challenge-free prover before returning the commitment and
claims. Each fixed prover then replays its transcript without any further oracle calls. -/
def JointAdversary.toFixedClaim {L : ℕ} (A : FC.JointAdversary L)
    (h : FC.NoOpeningChallenges) : FC.FixedClaimAdversary L := fun pp => do
  let (cm, P) ← A pp
  let os ← collect FC (emptySampler FC h) L P
  return (cm, fun i => replayClaim FC h (os i))

/-- With no challenge nodes, the fixed game runs the joint prover's effects in their original
order, and the verifier checks the same transcripts in both games. -/
theorem fixedClaimBindingGame_toFixedClaim (chal : FC.ChallengeSampler) (L : ℕ)
    (A : FC.JointAdversary L) (h : FC.NoOpeningChallenges) :
    FC.fixedClaimBindingGame chal L (A.toFixedClaim h) =
      FC.functionBindingGame chal L A := by
  have hs : emptySampler FC h = chal := by
    funext q c
    exact ((h q).false c).elim
  simp only [fixedClaimBindingGame, JointAdversary.toFixedClaim, hs, bind_assoc,
    LawfulMonad.pure_bind, functionBindingGame]
  refine bind_congr fun pp => bind_congr fun out => bind_congr fun os => ?_
  simp only [interact, replayClaim, run_replayOpening, LawfulApplicative.map_pure,
    Fin.mOfFn_pure, LawfulMonad.pure_bind, checkOpenings, decision]

/-- A joint adversary against challenge-free openings keeps its advantage under translation
to a fixed-claim adversary. -/
theorem fixedClaimBindingAdvantage_toFixedClaim {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl ambient (StateT σ ProbComp)) (chal : FC.ChallengeSampler) (L : ℕ)
    (A : FC.JointAdversary L) (h : FC.NoOpeningChallenges) :
    FC.fixedClaimBindingAdvantage init impl chal L (A.toFixedClaim h) =
      FC.functionBindingAdvantage init impl chal L A := by
  simp only [fixedClaimBindingAdvantage, fixedClaimBindingExperiment,
    fixedClaimBindingGame_toFixedClaim, functionBindingAdvantage, functionBindingExperiment]

section OneMessage

variable {PP Cm Aux : Type} {Proof : I.Query → Type}
variable (setup : OracleComp (unifSpec + ambient) PP)
  (commit : PP → Data → OracleComp (unifSpec + ambient) (Cm × Aux))
  (prove : PP → Cm → Data → Aux → (q : I.Query) → OracleComp (unifSpec + ambient) (Proof q))
  (check : PP → Cm → (q : I.Query) → I.spec q → Proof q → OracleComp ambient Bool)

/-- A one-message opening gives the prover the only move. -/
theorem noOpeningChallenges_oneMessage :
    (oneMessage setup commit prove check).NoOpeningChallenges := by
  intro q
  constructor
  rintro ⟨c, h⟩
  rcases c with _ | ⟨_, c⟩
  · cases h
  · exact c.elim

/-- On a one-message scheme the translated fixed adversary has the joint adversary's advantage. -/
theorem fixedClaimBindingAdvantage_toFixedClaim_oneMessage {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl ambient (StateT σ ProbComp))
    (chal : (oneMessage setup commit prove check).ChallengeSampler) (L : ℕ)
    (A : (oneMessage setup commit prove check).JointAdversary L) :
    (oneMessage setup commit prove check).fixedClaimBindingAdvantage init impl chal L
      (A.toFixedClaim (noOpeningChallenges_oneMessage setup commit prove check)) =
    (oneMessage setup commit prove check).functionBindingAdvantage init impl chal L A :=
  fixedClaimBindingAdvantage_toFixedClaim _ _ _ _ _ _ _

end OneMessage

end FunctionalCommitment

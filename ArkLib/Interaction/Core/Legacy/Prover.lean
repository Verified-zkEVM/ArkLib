/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Interaction.Core.Legacy.Protocol
public import ArkLib.Interaction.Core.Reduction
public import ArkLib.OracleReduction.Basic

/-!
# Legacy provers as focal strategies

A legacy prover keeps a private state between rounds. This file turns it into a focal strategy on
the plain tree of its protocol, slot for slot:

* at a message round, the node slot runs `sendMessage` and returns the message and next state;
* at a challenge round, the node slot runs `receiveChallenge`, whose effect does not see the
  challenge and returns a continuation from the challenge to the next state;
* the leaf action runs `output`.

The file also indexes the challenge nodes of the tree by the legacy challenge indices, and builds
the public-coin sampler whose draws come from a source of legacy challenges, such as the legacy
challenge oracle `[pSpec.Challenge]ₒ`.
-/

@[expose] public section

namespace Interaction.Core.Legacy
open PFunctor FreeM TwoParty.Lens OracleComp OracleSpec ProtocolSpec

variable {n : ℕ} {pSpec : ProtocolSpec n}

/-- A receiver node of the plain tree is a challenge round. -/
theorem dir_eq_of_owner : {d : Direction} → {T : Type} →
    owner plainSig (plainPos d T) = .receiver → d = .V_to_P
  | .P_to_V, _, h => nomatch h
  | .V_to_P, _, _ => rfl

/-- A sender node of the plain tree is a message round. -/
theorem dir_eq_of_owner_sender : {d : Direction} → {T : Type} →
    owner plainSig (plainPos d T) = .sender → d = .P_to_V
  | .P_to_V, _, _ => rfl
  | .V_to_P, _, h => nomatch h

/-! ### Challenge nodes and legacy challenge indices -/

/-- The legacy challenge index of a challenge node in the tree from round `k`. -/
def challengeRound : (k m : ℕ) → (h : k + m = n) →
    ChallengeNode plainSig (suffix pSpec k m h) → pSpec.ChallengeIdx
  | _, 0, _, c => c.val.elim
  | k, _ + 1, _, ⟨.inl _, hc⟩ => ⟨⟨k, by omega⟩, dir_eq_of_owner hc⟩
  | k, m + 1, _, ⟨.inr ⟨_, c⟩, hc⟩ => challengeRound (k + 1) m _ ⟨c, hc⟩

/-- The move at a challenge node is the legacy challenge of its round. -/
def challengeMove : (k m : ℕ) → (h : k + m = n) →
    (c : ChallengeNode plainSig (suffix pSpec k m h)) →
    challengeSpec plainSig (suffix pSpec k m h) c ≃
      pSpec.Challenge (challengeRound k m h c)
  | _, 0, _, c => c.val.elim
  | _, _ + 1, _, ⟨.inl _, _⟩ => plainMoveEquiv _ _
  | k, m + 1, _, ⟨.inr ⟨_, c⟩, hc⟩ => challengeMove (k + 1) m _ ⟨c, hc⟩

/-- Draw at a challenge node from a source of legacy challenges, indexed by legacy round. -/
def legacyDraw {M : Type → Type} [Functor M]
    (src : (i : pSpec.ChallengeIdx) → M (pSpec.Challenge i)) (k m : ℕ) (h : k + m = n)
    (c : ChallengeNode plainSig (suffix pSpec k m h)) :
    M (challengeSpec plainSig (suffix pSpec k m h) c) :=
  (challengeMove k m h c).symm <$> src (challengeRound k m h c)

/-- The public-coin sampler of the plain tree from round `k`. -/
def samplerFrom {M : Type → Type} [Monad M]
    (src : (i : pSpec.ChallengeIdx) → M (pSpec.Challenge i)) (k m : ℕ) (h : k + m = n) :
    Counterpart plainSig M (suffix pSpec k m h) (fun _ => PUnit) :=
  sampler plainSig (suffix pSpec k m h) (legacyDraw src k m h)

/-- The public-coin sampler of the plain tree, drawing each challenge from `src`. -/
abbrev legacySampler {M : Type → Type} [Monad M]
    (pSpec : ProtocolSpec n) (src : (i : pSpec.ChallengeIdx) → M (pSpec.Challenge i)) :
    Counterpart plainSig M (protocol pSpec) (fun _ => PUnit) :=
  samplerFrom src 0 n (Nat.zero_add n)

/-- The legacy challenge oracle as a source of challenges. -/
abbrev challengeOracle {ι : Type} (oSpec : OracleSpec ι) (pSpec : ProtocolSpec n)
    (i : pSpec.ChallengeIdx) : OracleComp (oSpec + [pSpec.Challenge]ₒ) (pSpec.Challenge i) :=
  liftM (pSpec.getChallenge i)

/-! ### The prover embedding -/

section Prover

variable {ι : Type} {oSpec : OracleSpec ι} {StmtIn WitIn StmtOut WitOut : Type}

/-- The prover's node slot at round `j`, for direction `d`. A message round runs `sendMessage`;
a challenge round runs `receiveChallenge`, which returns a continuation. -/
def roundSlot (P : _root_.Prover oSpec StmtIn WitIn StmtOut WitOut pSpec) (j : Fin n) :
    (d : Direction) → (hd : pSpec.dir j = d) → P.PrvState j.castSucc →
    OracleComp oSpec (Choice .focal (owner plainSig (plainPos d (pSpec.«Type» j)))
      (Move plainSig (plainPos d (pSpec.«Type» j))) (fun _ => P.PrvState j.succ))
  | .P_to_V, hd, st => (fun r => ⟨r.1, r.2⟩) <$> P.sendMessage ⟨j, hd⟩ st
  | .V_to_P, hd, st => P.receiveChallenge ⟨j, hd⟩ st

/-- The embedded prover from round `k`, started in the legacy state before round `k`. -/
def embedFrom (P : _root_.Prover oSpec StmtIn WitIn StmtOut WitOut pSpec) :
    (k m : ℕ) → (h : k + m = n) → P.PrvState ⟨k, by omega⟩ →
    Core.Prover plainSig oSpec (suffix pSpec k m h) (fun _ => StmtOut × WitOut)
  | k, 0, h, st => P.output (cast (congrArg P.PrvState (Fin.ext h)) st)
  | k, m + 1, h, st =>
    Choice.map .focal _ (fun _ st' => embedFrom P (k + 1) m (by omega) st') <$>
      roundSlot P ⟨k, by omega⟩ (pSpec.dir ⟨k, by omega⟩) rfl st

/-- The embedded honest prover. -/
def embedProver (P : _root_.Prover oSpec StmtIn WitIn StmtOut WitOut pSpec) (stmt : StmtIn)
    (wit : WitIn) :
    Core.Prover plainSig oSpec (protocol pSpec) (fun _ => StmtOut × WitOut) :=
  embedFrom P 0 n (Nat.zero_add n) (P.input (stmt, wit))

end Prover

end Interaction.Core.Legacy

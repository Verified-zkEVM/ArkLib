/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.ProofSystem.Sumcheck.Core.SingleRound
public import PolyFun.PFunctor.Free.Replicate

/-!
# The Sumcheck protocol and its honest prover in the interaction layer

The `n`-round protocol replicates the fixed round tree `n` times. Its carriers do not depend on
the round index, the challenge history or the running target, so every shape path is the same.

The honest prover is a dependent fold over the number of remaining rounds. Its state at `k`
remaining rounds is a `RoundState`: a round index `i` with `i + k = n`, the legacy statement
`Spec.StatementRound R n i` and the multivariate polynomial. Indexing by the remaining count makes
`protocol R deg (k + 1)` unfold definitionally to one round followed by `protocol R deg k`, so the
fold needs no casts on trees or transcripts. Every slot of the prover is `pure`, including the slot
at each challenge node and the leaf, as in the legacy `receiveChallenge` and output.

The main results are the closed form of the run against any sampler, `run_foldRounds`, and its
invariance under simulation of the ambient oracle, `simulate_foldRounds`.
-/

@[expose] public section

namespace Sumcheck.Core

open Polynomial PFunctor FreeM Interaction.Core Interaction.TwoParty.Lens

variable (R : Type) [CommSemiring R] (deg : ℕ)

/-- The `n`-round Sumcheck protocol: `n` copies of `round R deg`. -/
@[implicit_reducible]
def protocol (n : ℕ) : OracleProtocol.{0} := FreeM.replicate ⟨⟩ (round R deg) n

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

/-! ## Folding pure rounds -/

section Fold

variable {m : Type → Type} [Monad m]

/-- One round with every slot `pure`: send `msg`, then continue with the received challenge. -/
def consProver {k : ℕ} {Out : PathAlong oracleSig (protocol R deg (k + 1)) → Type}
    (msg : R⦃≤ deg⦄[X])
    (next : (chal : R) → Focal oracleSig m (protocol R deg k)
      (fun tail => Out (consTranscript msg chal tail))) :
    Focal oracleSig m (protocol R deg (k + 1)) Out :=
  pure ⟨msg, pure fun chal => next chal⟩

variable {State : ℕ → Type} {Out : Type}

/-- A dependent fold of pure rounds over the number of remaining rounds.

At `k + 1` remaining rounds the state determines the message, and each challenge determines the
state for the remaining `k` rounds. After the last round `finish` produces the pure output. -/
def foldRounds (msg : (k : ℕ) → State (k + 1) → R⦃≤ deg⦄[X])
    (next : (k : ℕ) → State (k + 1) → R → State k) (finish : State 0 → Out) :
    (k : ℕ) → State k → Focal oracleSig m (protocol R deg k) (fun _ => Out)
  | 0, st => (pure (finish st) : m Out)
  | k + 1, st => consProver (msg k st) fun chal => foldRounds msg next finish k (next k st chal)

end Fold

variable {State : ℕ → Type}

/-- The transcript produced by a fold of pure rounds on the given challenges. -/
def foldTranscript (msg : (k : ℕ) → State (k + 1) → R⦃≤ deg⦄[X])
    (next : (k : ℕ) → State (k + 1) → R → State k) :
    (k : ℕ) → State k → (Fin k → R) → PathAlong oracleSig (protocol R deg k)
  | 0, _, _ => ⟨⟩
  | k + 1, st, chals => consTranscript (msg k st) (chals 0)
      (foldTranscript msg next k (next k st (chals 0)) (Fin.tail chals))

/-- The final state of a fold of pure rounds on the given challenges. -/
def foldState (next : (k : ℕ) → State (k + 1) → R → State k) :
    (k : ℕ) → State k → (Fin k → R) → State 0
  | 0, st, _ => st
  | k + 1, st, chals => foldState next k (next k st (chals 0)) (Fin.tail chals)

/-! ## Running against the sampler -/

section Run

attribute [local implicit_reducible] projectPathAlong projectPathAlongLocalMap
  Displayed.LocalMap.toHom Displayed.LocalMap.toHomFun owner Node Node.position challengeSpec
  consTranscript FreeM.replicate

/-- The challenge node of the first round, named by shape branches alone. -/
def headNode (k : ℕ) : ChallengeNode oracleSig (protocol R deg (k + 1)) :=
  ⟨.inr ⟨⟨⟩, .inl ⟨⟩⟩, rfl⟩

/-- Restrict a challenge implementation to the remaining rounds. -/
def tailDraw {m : Type → Type} {k : ℕ}
    (draw : (c : ChallengeNode oracleSig (protocol R deg (k + 1))) →
      m (challengeSpec oracleSig _ c)) :
    (c : ChallengeNode oracleSig (protocol R deg k)) → m (challengeSpec oracleSig _ c) :=
  fun c => draw ⟨.inr ⟨⟨⟩, .inr ⟨⟨⟩, c.val⟩⟩, c.property⟩

/-- Draw the challenges of all rounds in order. -/
def drawChallenges {m : Type → Type} [Monad m] : (k : ℕ) →
    ((c : ChallengeNode oracleSig (protocol R deg k)) → m (challengeSpec oracleSig _ c)) →
    m (Fin k → R)
  | 0, _ => pure Fin.elim0
  | k + 1, draw => do
    let chal : R ← draw (headNode k)
    let rest ← drawChallenges k (tailDraw draw)
    pure (Fin.cons chal rest)

/-- The sampler of one more round has a pure message slot and draws at the challenge node. -/
theorem samplerEnd_succ {m : Type → Type} [Monad m] (k : ℕ)
    (draw : (c : ChallengeNode oracleSig (protocol R deg (k + 1))) →
      m (challengeSpec oracleSig _ c)) :
    samplerEnd oracleSig (protocol R deg (k + 1)) draw =
      (pure fun _ => (fun chal =>
          ⟨chal, samplerEnd oracleSig (protocol R deg k) (tailDraw draw)⟩) <$>
        draw (headNode k) :
        m ((_ : R⦃≤ deg⦄[X]) → m ((_ : R) ×
          PureEnd oracleSig m .counterpart (protocol R deg k) (fun _ => PUnit)))) := rfl

/-- Running one pure round draws its challenge and then runs the remaining rounds. -/
theorem run_consProver {m : Type → Type} [Monad m] [LawfulMonad m] (k : ℕ)
    {Out : PathAlong oracleSig (protocol R deg (k + 1)) → Type}
    (msg : R⦃≤ deg⦄[X])
    (next : (chal : R) → Focal oracleSig m (protocol R deg k)
      (fun tail => Out (consTranscript msg chal tail)))
    (draw : (c : ChallengeNode oracleSig (protocol R deg (k + 1))) →
      m (challengeSpec oracleSig _ c)) :
    Interaction.TwoParty.Lens.run (protocol R deg (k + 1)) (consProver msg next)
        (sampler oracleSig (protocol R deg (k + 1)) draw) = (do
      let chal ← draw (headNode k)
      let ⟨tail, out, u⟩ ← Interaction.TwoParty.Lens.run (protocol R deg k) (next chal)
        (sampler oracleSig (protocol R deg k) (tailDraw draw))
      pure ⟨consTranscript msg chal tail, out, u⟩) := by
  change Interaction.TwoParty.Lens.run (.liftBind _ _) _ _ = _
  simp only [sampler, PureEnd.toStrategy, samplerEnd_succ]
  simp only [run_node, consProver, owner, oracleSig, Choice, Move, Choice.map, step,
    Schedule.seq, PureEnd.mapOutput, LawfulMonad.pure_bind, LawfulApplicative.map_pure,
    bind_map_left, FreeM.append_liftBind]
  simp only [LawfulMonad.bind_assoc, LawfulMonad.pure_bind]
  exact (_root_.bind_map_left (m := m) _ _ _).trans rfl

/-- Closed form of a fold of pure rounds against the sampler: the transcript and output are
pure functions of the drawn challenges. -/
theorem run_foldRounds {m : Type → Type} [Monad m] [LawfulMonad m] {Out : Type}
    (msg : (k : ℕ) → State (k + 1) → R⦃≤ deg⦄[X])
    (next : (k : ℕ) → State (k + 1) → R → State k) (finish : State 0 → Out) (k : ℕ)
    (st : State k)
    (draw : (c : ChallengeNode oracleSig (protocol R deg k)) → m (challengeSpec oracleSig _ c)) :
    Interaction.TwoParty.Lens.run (protocol R deg k) (foldRounds msg next finish k st)
        (sampler oracleSig (protocol R deg k) draw) =
      (fun chals => ⟨foldTranscript msg next k st chals,
        finish (foldState next k st chals), ⟨⟩⟩) <$> drawChallenges k draw := by
  induction k with
  | zero =>
    refine (run_done (l := oracleSig) (OutP := fun _ => Out) (OutC := fun _ => PUnit)
      (pure (finish st)) (pure ⟨⟩)).trans ?_
    simp [drawChallenges]
    rfl
  | succ k ih =>
    simp only [foldRounds, run_consProver, ih]
    simp only [drawChallenges, foldTranscript, foldState]
    refine Eq.trans ?_ (_root_.map_bind (m := m) _ _ _).symm
    refine bind_congr fun chal => ?_
    simp only [LawfulMonad.bind_pure_comp, Functor.map_map]
    rfl

/-- Simulating the ambient oracle leaves a fold of pure rounds unchanged. -/
theorem simulate_foldRounds {ι : Type} {ambient : OracleSpec ι} {m : Type → Type} [Monad m]
    [LawfulMonad m] (impl : QueryImpl ambient m) {Out : Type}
    (msg : (k : ℕ) → State (k + 1) → R⦃≤ deg⦄[X])
    (next : (k : ℕ) → State (k + 1) → R → State k) (finish : State 0 → Out) (k : ℕ)
    (st : State k) :
    Prover.simulate impl (foldRounds (m := OracleComp ambient) msg next finish k st) =
      foldRounds (m := m) msg next finish k st := by
  induction k with
  | zero => exact (Prover.simulate_done impl _).trans (simulateQ_pure impl _)
  | succ k ih =>
    refine (Prover.simulate_node impl _ _ _).trans ?_
    simp only [foldRounds, consProver, simulateQ_pure, LawfulApplicative.map_pure]
    refine congrArg pure (Sigma.ext rfl (heq_of_eq ?_))
    change Prover.simulate impl _ = _
    refine (Prover.simulate_node impl _ _ _).trans ?_
    simp only [simulateQ_pure, LawfulApplicative.map_pure]
    exact congrArg pure (funext fun _ => ih _)

end Run

/-! ## The honest Sumcheck prover -/

section Honest

variable (R deg) (n : ℕ)

/-- The honest prover's state with `k` rounds remaining. The round index `round` satisfies
`round + k = n`, so the state type does not change the protocol shape. -/
structure RoundState (k : ℕ) where
  /-- The index of the next round, or `n` after the last round. -/
  round : Fin (n + 1)
  /-- The round index and the remaining count add up to the number of variables. -/
  round_add : round.val + k = n
  /-- The legacy statement at the current round. -/
  statement : Spec.StatementRound R n round
  /-- The multivariate polynomial being summed. -/
  poly : Spec.OracleStatement R n deg ()

/-- The prover output: the legacy output statement, the output oracle statement and the unit
witness. -/
abbrev HonestOutput :=
  (Spec.StatementRound R n (Fin.last n) × (∀ i, Spec.OracleStatement R n deg i)) × Unit

variable {R deg n}

/-- The round being played when `k + 1` rounds remain. -/
def RoundState.index {k : ℕ} (st : RoundState R deg n (k + 1)) : Fin n :=
  ⟨st.round.val, by have := st.round_add; omega⟩

variable {d : ℕ} (D : Fin d ↪ R)

/-- The honest round polynomial: the legacy projected round polynomial. -/
noncomputable def honestMessage (k : ℕ) (st : RoundState R deg n (k + 1)) : R⦃≤ deg⦄[X] :=
  Sumcheck.Spec.SingleRound.projectedRoundPolynomial R n deg D st.index
    st.statement.challenges st.poly

/-- The legacy statement update: the new target is the round polynomial at the challenge, and the
challenge is appended to the history. -/
noncomputable def nextState (msg : (k : ℕ) → RoundState R deg n (k + 1) → R⦃≤ deg⦄[X])
    (k : ℕ) (st : RoundState R deg n (k + 1)) (chal : R) : RoundState R deg n k where
  round := st.index.succ
  round_add := by
    have := st.round_add
    change st.round.val + 1 + k = n
    omega
  statement := ⟨(msg k st).val.eval chal, Fin.snoc st.statement.challenges chal⟩
  poly := st.poly

/-- Read the legacy output from the state after the last round. -/
def finishState (st : RoundState R deg n 0) : HonestOutput R deg n :=
  ((⟨st.statement.target, fun j => st.statement.challenges (Fin.cast (by
      have := st.round_add; simp only [Fin.val_last]; omega) j)⟩, fun _ => st.poly), ())

/-- The initial state: round `0` with the input statement and polynomial. -/
def initState (stmt : Spec.StatementRound R n 0) (oStmt : ∀ i, Spec.OracleStatement R n deg i) :
    RoundState R deg n n :=
  ⟨0, Nat.zero_add n, stmt, oStmt ()⟩

/-- The honest Sumcheck prover. Every slot is `pure` and the output is pure. -/
noncomputable def honestProver {m : Type → Type} [Monad m]
    (stmt : Spec.StatementRound R n 0) (oStmt : ∀ i, Spec.OracleStatement R n deg i) :
    Focal oracleSig m (protocol R deg n) (fun _ => HonestOutput R deg n) :=
  foldRounds (honestMessage D) (nextState (honestMessage D)) finishState n (initState stmt oStmt)

/-- The honest transcript on the given challenges. -/
noncomputable def honestTranscript (stmt : Spec.StatementRound R n 0)
    (oStmt : ∀ i, Spec.OracleStatement R n deg i) (chals : Fin n → R) :
    PathAlong oracleSig (protocol R deg n) :=
  foldTranscript (honestMessage D) (nextState (honestMessage D)) n (initState stmt oStmt) chals

/-- The honest prover output on the given challenges. -/
noncomputable def honestOutput (stmt : Spec.StatementRound R n 0)
    (oStmt : ∀ i, Spec.OracleStatement R n deg i) (chals : Fin n → R) : HonestOutput R deg n :=
  finishState (foldState (nextState (honestMessage D)) n (initState stmt oStmt) chals)

/-- Closed form of the honest run: draw every challenge, then return the honest transcript and
output. -/
theorem run_honestProver {m : Type → Type} [Monad m] [LawfulMonad m]
    (stmt : Spec.StatementRound R n 0) (oStmt : ∀ i, Spec.OracleStatement R n deg i)
    (draw : (c : ChallengeNode oracleSig (protocol R deg n)) → m (challengeSpec oracleSig _ c)) :
    Interaction.TwoParty.Lens.run (protocol R deg n) (honestProver D stmt oStmt)
        (sampler oracleSig (protocol R deg n) draw) =
      (fun chals => ⟨honestTranscript D stmt oStmt chals, honestOutput D stmt oStmt chals, ⟨⟩⟩) <$>
        drawChallenges n draw :=
  run_foldRounds _ _ _ n _ draw

/-- Simulating the ambient oracle leaves the honest prover unchanged. -/
theorem simulate_honestProver {ι : Type} {ambient : OracleSpec ι} {m : Type → Type} [Monad m]
    [LawfulMonad m] (impl : QueryImpl ambient m)
    (stmt : Spec.StatementRound R n 0) (oStmt : ∀ i, Spec.OracleStatement R n deg i) :
    Prover.simulate impl (honestProver (m := OracleComp ambient) D stmt oStmt) =
      honestProver (m := m) D stmt oStmt :=
  simulate_foldRounds impl _ _ _ n _

end Honest

end Sumcheck.Core

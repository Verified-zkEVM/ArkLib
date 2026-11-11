/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.ProofSystem.Sumcheck.Core.Protocol
public import ArkLib.ProofSystem.Sumcheck.Spec.SingleRound

/-! # Compatibility of honest round strategies with legacy statements -/

@[expose] public section
namespace Sumcheck.Core
open Polynomial PFunctor FreeM Interaction.Core Interaction.TwoParty.Lens
variable {R : Type} [CommSemiring R] {deg : ℕ}

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

/-- The honest round polynomial: the legacy projected round polynomial. It is noncomputable
because the projection works on the Mathlib multivariate polynomial; an executable counterpart on
CompPoly carriers is `Sumcheck.Impl.Computable.projectedStatementMessage`, which
`Sumcheck.Impl.Computable.projectedStatementMessage_eq` identifies with the projection. -/
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

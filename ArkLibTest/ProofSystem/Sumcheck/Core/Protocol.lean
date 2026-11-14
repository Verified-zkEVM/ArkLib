/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.ProofSystem.Sumcheck.Core.LegacyProtocol
import Mathlib.Algebra.Field.ZMod

/-!
# Sumcheck rounds and replication in the interaction layer

Challenges never select shape, zero rounds is the leaf, the honest prover's slots are `pure`, and
honest runs have the stated closed form.
-/

namespace Sumcheck.Core.ProtocolTest

open Polynomial PFunctor FreeM Interaction.Core Interaction.TwoParty.Lens

abbrev F := ZMod 5

/-! ## Shape independence -/

/-- Two rounds with different messages and challenges have the same shape path. -/
example (msg₁ msg₂ : F⦃≤ 1⦄[X]) (c₁ c₂ : F) :
    projectPathAlong oracleSig (round F 1) (roundTranscript msg₁ c₁) =
      projectPathAlong oracleSig (round F 1) (roundTranscript msg₂ c₂) := rfl

/-- Any two runs, whatever their messages and challenge histories, have the same shape path. -/
example (tr₁ tr₂ : PathAlong oracleSig (protocol F 1 3)) :
    projectPathAlong oracleSig (protocol F 1 3) tr₁ =
      projectPathAlong oracleSig (protocol F 1 3) tr₂ := by
  rw [project_eq_shape, project_eq_shape]

/-- The challenge carrier at every round is the field, whatever was drawn before. -/
example (k : ℕ) (draw : (c : ChallengeNode oracleSig (protocol F 1 (k + 1))) →
    Id (challengeSpec oracleSig _ c)) :
    (draw (headNode k) : F) = draw (headNode k) := rfl

/-- The view of a transcript keeps the challenge and forgets the message. -/
example (msg₁ msg₂ : F⦃≤ 1⦄[X]) (c : F) :
    viewChallenge (toView (round F 1) (roundTranscript msg₁ c)) =
      viewChallenge (toView (round F 1) (roundTranscript msg₂ c)) := rfl

/-! ## Zero rounds -/

example : protocol F 1 0 = .pure ⟨⟩ := rfl

example (p : Path (protocol F 1 0)) : p = Interpreted.shape 0 := Interpreted.shape_unique 0 p

/-- With zero rounds the honest prover only returns its pure output. -/
example {d : ℕ} (D : Fin d ↪ F) (stmt : Spec.StatementRound F 0 0)
    (oStmt : ∀ i, Spec.OracleStatement F 0 1 i) :
    honestProver (m := Id) D stmt oStmt = (pure (finishState (initState stmt oStmt)) : Id _) :=
  rfl

/-- With zero rounds the honest run draws nothing. -/
example {d : ℕ} (D : Fin d ↪ F) (stmt : Spec.StatementRound F 0 0)
    (oStmt : ∀ i, Spec.OracleStatement F 0 1 i)
    (draw : (c : ChallengeNode oracleSig (protocol F 1 0)) → Id (challengeSpec oracleSig _ c)) :
    Interaction.TwoParty.Lens.run (protocol F 1 0) (honestProver D stmt oStmt)
        (sampler oracleSig (protocol F 1 0) draw) =
      (pure ⟨⟨⟩, finishState (initState stmt oStmt), ⟨⟩⟩ : Id _) :=
  run_honestProver D stmt oStmt draw

/-! ## Pure slots -/

/-- The honest prover's first round sends the projected polynomial in a pure slot, and its
challenge slot is pure. -/
example {d : ℕ} (D : Fin d ↪ F) (n : ℕ) (stmt : Spec.StatementRound F (n + 1) 0)
    (oStmt : ∀ i, Spec.OracleStatement F (n + 1) 1 i) {m : Type → Type} [Monad m] :
    honestProver (m := m) D stmt oStmt =
      pure ⟨honestMessage D n (initState stmt oStmt), pure fun chal =>
        foldRounds (honestMessage D) (nextState (honestMessage D)) finishState n
          (nextState (honestMessage D) n (initState stmt oStmt) chal)⟩ := rfl

/-- The honest message is the legacy projected round polynomial. -/
example {d : ℕ} (D : Fin d ↪ F) (n : ℕ) (stmt : Spec.StatementRound F (n + 1) 0)
    (oStmt : ∀ i, Spec.OracleStatement F (n + 1) 1 i) :
    honestMessage D n (initState stmt oStmt) =
      Spec.SingleRound.projectedRoundPolynomial F (n + 1) 1 D 0 stmt.challenges (oStmt ()) := rfl

/-! ## Closed forms -/

/-- One round records the honest message and the drawn challenge. -/
example (msg : F⦃≤ 1⦄[X])
    (draw : (c : ChallengeNode oracleSig (round F 1)) → Id (challengeSpec oracleSig _ c))
    (h : draw roundChallengeNode = (3 : F)) :
    Interaction.TwoParty.Lens.run (round F 1)
        (roundProver (Out := fun _ => F) msg fun chal => chal + 1)
        (sampler oracleSig (round F 1) draw) =
      (pure ⟨roundTranscript msg 3, (4 : F), ⟨⟩⟩ : Id _) := by
  rw [run_roundProver, h]
  rfl

/-- The honest transcript records every drawn challenge in order. -/
example {d : ℕ} (D : Fin d ↪ F) (stmt : Spec.StatementRound F 2 0)
    (oStmt : ∀ i, Spec.OracleStatement F 2 1 i) (chals : Fin 2 → F) :
    Interpreted.challenge (honestTranscript D stmt oStmt chals) = chals 0 ∧
      Interpreted.challenge (Interpreted.tail (honestTranscript D stmt oStmt chals)) = chals 1 :=
  ⟨rfl, rfl⟩

/-- The honest output records the challenges as the legacy output statement's history. -/
example {d : ℕ} (D : Fin d ↪ F) (stmt : Spec.StatementRound F 2 0)
    (oStmt : ∀ i, Spec.OracleStatement F 2 1 i) (chals : Fin 2 → F) (j : Fin 2) :
    (honestOutput D stmt oStmt chals).1.1.challenges j = chals j := by
  fin_cases j <;> rfl

end Sumcheck.Core.ProtocolTest

run_cmd do
  for decl in [``Sumcheck.Core.project_eq_shape, ``Sumcheck.Core.run_roundProver,
      ``Sumcheck.Core.run_consProver, ``Sumcheck.Core.run_foldRounds,
      ``Sumcheck.Core.simulate_foldRounds, ``Sumcheck.Core.run_honestProver,
      ``Sumcheck.Core.simulate_honestProver, ``Interaction.Core.Prover.simulate_node] do
    for ax in ← Lean.collectAxioms decl do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "unexpected axiom {ax} in {decl}"

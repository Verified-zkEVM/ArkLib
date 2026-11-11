/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLibTest.ProofSystem.Sumcheck.Core.Rounds
import ArkLib.ProofSystem.Sumcheck.Core.Composition

/-!
# Single Sumcheck rounds as composable oracle verifiers

Instances of `Sumcheck.Core.Composition` on the bilinear input `1 + 2 X₀ + 3 X₁ + 4 X₀ X₁` over
`ZMod 17`, which sums to `1` over `{0, 1}²`.

* The round-`0` projection map sends the input to the honest first message `5 + 8 X`, and answers
  a projected query at `x` with `5 + 8 x` from the input.
* The standalone round with that projection as output oracle, run on the honest message with the
  challenge `3`, accepts `⟨12, ![3]⟩` with output oracle `5 + 8 X`. The accepted claim is in the
  round's output relation, and with the original input in the round-`1` relation.
* The round-`0` check appended to the one-round verifier of the rest runs as the two-round
  Sumcheck verifier against every composed prover.
-/

namespace Sumcheck.Core.CompositionTest

open Polynomial PFunctor FreeM Interaction.Core Interaction.TwoParty.Lens Interaction.Oracle
  OracleComp OracleSpec ProtocolSpec Sumcheck.Core.RoundsTest

section UnequalUniverses

variable (clientAmbient : OracleSpec Unit) {I : Type 1} {A : I → Type}
  (inputs : OracleFamily.{1, 0, 1} I A)
  {J : Type} {B : J → Type} (outputs : OracleFamily.{0, 0, 1} J B)
  (check : Type 1 → (Spec.SingleRound.pSpec ℕ 1).Challenges →
    OptionT (OracleComp [(Spec.SingleRound.pSpec ℕ 1).Message]ₒ) ℕ)
  (out : Type 1 → (p : Path (round ℕ 1)) → View (round ℕ 1) p →
    OracleMap (pathResources inputs (round ℕ 1) p) (Resources.ofFamily outputs))

/-- A large input statement and resource queries can produce a small round output. -/
def largeInputVerifier :
    OracleVerifier clientAmbient (round ℕ 1) (Type 1) (fun _ => ℕ) inputs
      (fun _ => outputs) :=
  checkVerifier clientAmbient inputs check out

-- These ordinary-import clients exercise the decision, execution and append APIs too.
#check decideWith_checkVerifier clientAmbient inputs check out
#check run_checkVerifier clientAmbient inputs check out
#check suffixRoute_round clientAmbient inputs check out
#check decideWith_append_checkVerifier clientAmbient inputs check out
#check run_append_checkVerifier clientAmbient inputs check out

end UnequalUniverses

noncomputable section

-- Migration row: Sumcheck Interaction/Projection #3.

/-- The projection of `bilinear` in round `0` is the honest first message. -/
theorem projection_bilinear :
    (projectionMap K 1 2 D₂ 0 ⟨1, Fin.elim0⟩).f (fun _ => bilinear) () = firstMsg := rfl

/-- A projected query at `x` is answered from `bilinear` with `5 + 8 x`. -/
theorem projection_answer (x : K) :
    simulateQ ((Spec.polynomialFamily K 2 1).behaviorOfRealizations fun _ => bilinear)
      ((projectionMap K 1 2 D₂ 0 ⟨1, Fin.elim0⟩).impl ⟨(), x⟩) = 5 + 8 * x :=
  (simulateQ_projectionMap 0 ⟨1, Fin.elim0⟩ (fun _ => bilinear) x).trans (projected_eval x)

/-- The round-`0` check on the honest first message at the challenge `3` accepts `⟨12, ![3]⟩`. -/
theorem projected_verdict :
    checkVerdict (roundCheck K 1 2 D₂ ambient 0) ⟨1, Fin.elim0⟩ (roundTranscript firstMsg 3) =
      some ⟨12, ![3]⟩ := by
  refine (projectedVerifier_relation (D := D₂) (ambient := ambient) 0 ⟨1, Fin.elim0⟩
    (fun _ => bilinear) bilinear_relation 3).1.trans ?_
  change some (⟨firstMsg.val.eval 3, Fin.snoc (Fin.elim0 : Fin 0 → K) 3⟩ :
    Spec.StatementRound K 2 (Fin.succ 0)) = _
  rw [projected_eval]
  congr 2
  exact funext fun i => by fin_cases i; rfl

/-- Every challenge of a round ranges over `K`. -/
theorem round_range (c : ChallengeNode oracleSig (round K 1)) :
    challengeSpec oracleSig (round K 1) c = K := by
  obtain ⟨n, h⟩ := c
  rcases n with _ | ⟨_, _ | ⟨_, n⟩⟩
  · cases h
  · rfl
  · cases n

-- Migration rows: Sumcheck Interaction/Projection #7, #8, ProjectionTransport #2.

/-- A handler that answers every challenge with `3`. The ambient oracle is never queried. -/
def answerThree : QueryImpl (ambient + challengeSpec oracleSig (round K 1)) Id
  | .inl _ => pure ()
  | .inr c => pure (cast (round_range c).symm (3 : K))

/-- The standalone round on `bilinear` with the challenge `3` accepts `⟨12, ![3]⟩`, with the
projected round polynomial `5 + 8 X` as output oracle. -/
theorem run_projected_bilinear :
    simulateQ answerThree ((fun obs => obs.2.2) <$>
      (projectedVerifier 2 D₂ ambient 0).run ⟨1, Fin.elim0⟩ (fun _ => bilinear)
        (roundProver (Out := fun _ => Unit) firstMsg fun _ => ())) =
      some (⟨12, ![3]⟩, fun _ => firstMsg) := by
  rw [run_projectedVerifier_roundProver, Functor.map_map]
  change Option.map _ (checkVerdict (roundCheck K 1 2 D₂ ambient 0) ⟨1, Fin.elim0⟩
    (roundTranscript firstMsg 3)) = _
  rw [projected_verdict]
  rfl

/-- The accepted claim of the standalone round: `(12, 3)` with the projected polynomial is in the
round's output relation, and `⟨12, ![3]⟩` with the original input is in the round-`1` relation. -/
theorem projected_relation :
    (((12, 3), fun _ => firstMsg), ()) ∈ Spec.SingleRound.Simple.outputRelation K 1 ∧
      ((⟨12, ![3]⟩, fun _ => bilinear), ()) ∈ Spec.relationRound K 2 1 D₂ (0 : Fin 2).succ := by
  obtain ⟨-, h₁, h₂⟩ := projectedVerifier_relation (D := D₂) (ambient := ambient) 0
    ⟨1, Fin.elim0⟩ (fun _ => bilinear) bilinear_relation 3
  have e : firstMsg.val.eval 3 = 12 := by rw [projected_eval]; decide
  have hv : (Fin.snoc (Fin.elim0 : Fin 0 → K) 3 : Fin 1 → K) = ![3] :=
    funext fun i => by fin_cases i; rfl
  have hq : Spec.SingleRound.projectedRoundPolynomial K 2 1 D₂ 0 Fin.elim0 bilinear = firstMsg :=
    projection_bilinear
  dsimp only at h₁ h₂
  rw [hq, e] at h₁ h₂
  rw [hv] at h₂
  exact ⟨h₁, h₂⟩

-- Migration row: Sumcheck Interaction/Protocol #7.

/-- The append equivalence at two rounds on `bilinear`: the round-`0` check appended to the
one-round verifier of the rest, run against any composed prover, is the two-round verifier. -/
theorem run_append_bilinear {Mid : PathAlong oracleSig (round K 1) → Type}
    {Out : PathAlong oracleSig (protocol K 1 2) → Type}
    (p : Prover oracleSig ambient (round K 1) Mid)
    (f : (tr : PathAlong oracleSig (round K 1)) → Mid tr →
      OracleComp ambient (Prover oracleSig ambient (protocol K 1 1)
        fun tail => Out (PathAlong.append oracleSig (round K 1) (fun _ => protocol K 1 1) tr
          tail))) :
    ((checkVerifier ambient (Spec.polynomialFamily K 2 1)
        (foldHead (roundCheck K 1 2 D₂ ambient)) fun _ p _ => inputSlot _ p).append
        (fun _ => legacyFoldVerifier K 1 ambient (Spec.polynomialFamily K 2 1) 1
          (Spec.StatementRound K 2 ∘ Fin.succ) fun i => roundCheck K 1 2 D₂ ambient i.succ)
        (foldCompatibility K 1 ambient _ 1 _ _)).run ⟨1, Fin.elim0⟩ (fun _ => bilinear)
        (Interaction.Core.Prover.append (s₂ := fun _ => protocol K 1 1) (Out := Out) p f) =
      (verifier K 1 2 D₂ ambient).run ⟨1, Fin.elim0⟩ (fun _ => bilinear)
        (Interaction.Core.Prover.append (s₂ := fun _ => protocol K 1 1) (Out := Out) p f) :=
  run_append_verifier D₂ 1 ⟨1, Fin.elim0⟩ (fun _ => bilinear) p f

/-- The relation is checked on the verdict returned by this same standalone projected run. -/
theorem run_projected_relation :
    simulateQ answerThree ((fun obs => obs.2.2.map fun out =>
        (((out.1.target, out.1.challenges ⟨0, by decide⟩), out.2), ()) ∈
          Spec.SingleRound.Simple.outputRelation K 1) <$>
      (projectedVerifier 2 D₂ ambient 0).run ⟨1, Fin.elim0⟩ (fun _ => bilinear)
        (roundProver (Out := fun _ => Unit) firstMsg fun _ => ())) = some True := by
  rw [run_projectedVerifier_roundProver, Functor.map_map]
  erw [simulateQ_map, simulateQ_spec_query]
  change Option.map _ ((checkVerdict (roundCheck K 1 2 D₂ ambient 0) ⟨1, Fin.elim0⟩
    (roundTranscript firstMsg 3)).map _) = _
  rw [projected_verdict]
  change some ((((12, 3), fun _ => firstMsg), ()) ∈
    Spec.SingleRound.Simple.outputRelation K 1) = some True
  exact congrArg some (propext ⟨fun _ => trivial, fun _ => projected_relation.1⟩)

end

run_cmd
  for decl in [``Sumcheck.Core.CompositionTest.projection_bilinear,
      ``Sumcheck.Core.CompositionTest.projection_answer,
      ``Sumcheck.Core.CompositionTest.projected_verdict,
      ``Sumcheck.Core.CompositionTest.round_range,
      ``Sumcheck.Core.CompositionTest.run_projected_bilinear,
      ``Sumcheck.Core.CompositionTest.projected_relation,
      ``Sumcheck.Core.CompositionTest.run_projected_relation,
      ``Sumcheck.Core.CompositionTest.run_append_bilinear,
      ``Sumcheck.Core.projectionMap, ``Sumcheck.Core.simulateQ_projectionMap,
      ``Sumcheck.Core.run_projectedVerifier_roundProver,
      ``Sumcheck.Core.projectedVerifier_relation, ``Sumcheck.Core.run_append_verifier] do
    for ax in ← Lean.collectAxioms decl do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "unexpected axiom {ax} in {decl}"

end Sumcheck.Core.CompositionTest

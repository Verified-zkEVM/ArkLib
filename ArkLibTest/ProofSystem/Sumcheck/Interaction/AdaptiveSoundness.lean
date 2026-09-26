/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.ProofSystem.Sumcheck.Interaction.AdaptiveSoundness
import Mathlib.Algebra.Field.ZMod

/-! # Randomized adaptive execution regressions

Two rounds use both the reached public target and private state. An explicit execution equation
checks the order of all four draws and retains the original oracle behavior.
-/

namespace Sumcheck.Interaction.MultivariateRound.AdaptiveTest

open OracleComp OracleSpec Polynomial
open _root_.Interaction.Oracle

noncomputable section

instance : Fact (Nat.Prime 17) := ⟨by decide⟩

/-- An affine message with its actual degree certificate. -/
def affine (a b : ZMod 17) : SingleRound.Message (ZMod 17) 1 :=
  ⟨C a * X + C b, Polynomial.mem_degreeLE.mpr
    (degree_add_le_of_degree_le (degree_C_mul_X_le a) (degree_C_le.trans zero_le_one))⟩

/-- The original zero behavior is independent of both adversarial messages. -/
def original : (polynomialFamily (ZMod 17) 2 1).Behavior := fun _ => (0 : ZMod 17)

/-- The singleton-domain sum claim starts false. -/
def initial : ClosedClaim (Spec.StatementRound (ZMod 17) 2 0)
    (polynomialFamily (ZMod 17) 2 1) := ⟨⟨1, Fin.elim0⟩, original⟩

/-- Each draw updates private state, which controls the next sent polynomial's slope. -/
def messages (i : Fin 2) (stmt : Spec.StatementRound (ZMod 17) 2 i.castSucc)
    (state : ZMod 17) : ProbComp (SingleRound.Message (ZMod 17) 1 × ZMod 17) := do
  let a ← $ᵗ (ZMod 17)
  return (affine (a + state) stmt.target, a + state)

/-- No draw is made for an empty interval, and private state is retained. -/
example : executeAdaptiveRounds (ZMod 17) 2 1 (ZMod 17) 0 0 (by decide) [0]
    initial 7 messages = pure (some (initial, 7)) := rfl

set_option backward.isDefEq.respectTransparency false in
/-- Each message precedes its challenge; the second message uses the reached target and state. -/
theorem two_rounds :
    executeAdaptiveRounds (ZMod 17) 2 1 (ZMod 17) 0 2 (by decide) [0]
      initial 0 messages = (do
        let a ← $ᵗ (ZMod 17)
        let r ← $ᵗ (ZMod 17)
        let b ← $ᵗ (ZMod 17)
        let s ← $ᵗ (ZMod 17)
        return some ((⟨⟨(b + a) * s + (a * r + 1), ![r, s]⟩, original⟩ :
          ClosedClaim (Spec.StatementRound (ZMod 17) 2 2)
            (polynomialFamily (ZMod 17) 2 1)), b + a)) := by
  simp only [executeAdaptiveRounds, OrderedExecution.run, adaptiveStages_run]
  simp only [executeCore_sampled_closed_eq]
  simp only [messages, map_eq_bind_pure_comp, bind_assoc, pure_bind]
  have hvec (r s : ZMod 17) : Fin.snoc (Fin.snoc Fin.elim0 r) s = ![r, s] := by
    funext i
    fin_cases i <;> rfl
  simp [affine, initial, hvec]

set_option backward.isDefEq.respectTransparency false in
/-- A failed first sum check keeps its message/challenge draws and skips the second round. -/
theorem rejection_skips_suffix :
    executeAdaptiveRounds (ZMod 17) 2 1 (ZMod 17) 0 2 (by decide) []
      initial 0 messages = (do
        let _ ← $ᵗ (ZMod 17)
        let _ ← $ᵗ (ZMod 17)
        return none) := by
  simp only [executeAdaptiveRounds, OrderedExecution.run, adaptiveStages_run]
  simp only [executeCore_sampled_closed_eq]
  simp only [messages, map_eq_bind_pure_comp, bind_assoc, pure_bind]
  simp [initial]

/-- The public theorem accepts a concrete false input and a stateful randomized kernel. -/
example :
    let D : Fin 1 ↪ ZMod 17 := ⟨fun _ => 0, fun _ _ _ => Subsingleton.elim _ _⟩
    Pr{let result ← (executeAdaptiveRounds (ZMod 17) 2 1 (ZMod 17) 0 2 (by decide)
      (Finset.univ.map D).toList initial 0 messages)}[
      ∃ output, result = some output ∧ closedRelation (ZMod 17) 2 1 D 2 output.1] ≤
        (2 : ENNReal) * (1 / 17) := by
  intro D
  simpa using executeAdaptiveRounds_soundness 2 1 (ZMod 17) (ZMod 17) D 0 2 (by decide)
    0 initial 0 messages (by
      funext q
      change (0 : ZMod 17) = MvPolynomial.eval q.2 0
      simp) (by simp [closedRelation, initial, original])

/--
info: 'Sumcheck.Interaction.MultivariateRound.executeAdaptiveRounds_soundness' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms executeAdaptiveRounds_soundness

end
end Sumcheck.Interaction.MultivariateRound.AdaptiveTest

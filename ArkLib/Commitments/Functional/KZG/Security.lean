/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Commitments.Functional.KZG.FunctionBinding.Wins

/-!
# KZG binding: game-level bounds

This file states KZG evaluation binding and function binding as games, and bounds each game by
VCVio's `TSDH.experiment` or `ARSDH.experiment` run on an explicit reduction.

Both games sample the trapdoor `τ` with `SDH.sampleTrapdoor F`, as the VCVio experiments do, and
give the adversary `committerKey g₁ τ n` and `verifierKey g₂ τ`. These are by definition the
reference strings `(fun i => τ ^ (i : ℕ) • g₁)` and `![g₂, τ • g₂]` that the VCVio experiments
build inline (`committerKey_eq` and `verifierKey_eq`).

* In the evaluation-binding game the adversary returns a commitment `cm`, a point `q` and two
  openings `(r₁, π₁)` and `(r₂, π₂)`. It wins when both openings are accepted and `r₁ ≠ r₂`.
* In the function-binding game the adversary returns a commitment `cm` and a list of openings.
  It wins when every opening is accepted and no coefficient vector of length `n + 1` fits all of
  them.

Each reduction runs the adversary once on the keys it receives and post-processes the output:
`evalBindingAdversary` with `evalBindingReduction`, and `functionBindingAdversary` with
`FunctionBinding.functionBindingReduction`. It samples nothing. The bounds couple the two
experiments on the shared trapdoor and adversary output and apply the pointwise lemmas
`evalBindingReduction_wins` and `FunctionBinding.functionBindingReduction_wins`.

A Lean function has no resource bound, and both assumptions fail for an adversary that searches
for the trapdoor. The corollaries therefore assume the hardness bound only over an explicit class
of adversaries that contains the reduction.

## Main statements

* `KZG.evalBinding_le_tsdh`, `KZG.evalBinding_le_of_tsdh`: evaluation binding from t-SDH.
* `KZG.functionBinding_le_arsdh`, `KZG.functionBinding_le_of_arsdh`: function binding from
  ARSDH.

## References

* [Kate, A., Zaverucha, G. M., and Goldberg, I., *Polynomial Commitments*][KZG10TR]
* [Chiesa, A., Guan, Z., Knabenhans, C., and Yu, Z.,
  *On the Fiat–Shamir Security of Succinct Arguments from Functional Commitments*][CGKY25]
-/

@[expose] public section

open OracleComp
open scoped ENNReal

namespace KZG

variable {F : Type} [Field F]
variable {G₁ G₂ Gₜ : Type} [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
  [AddCommGroup Gₜ] [Module F Gₜ]
variable {n : ℕ}

/-- The committer key is the first-source reference string of `TSDH.experiment` and
`ARSDH.experiment`. -/
theorem committerKey_eq (g₁ : G₁) (τ : F) (n : ℕ) :
    committerKey g₁ τ n = fun i : Fin (n + 1) => τ ^ (i : ℕ) • g₁ :=
  rfl

/-- The verifier key is the second-source reference string of `TSDH.experiment` and
`ARSDH.experiment`. -/
theorem verifierKey_eq (g₂ : G₂) (τ : F) : verifierKey g₂ τ = ![g₂, τ • g₂] :=
  rfl

section EvaluationBinding

/-- An evaluation-binding adversary receives the committer and verifier keys and returns a
commitment `cm`, a point `q` and two openings: `(cm, q, r₁, π₁, r₂, π₂)`. -/
abbrev EvalBindingAdversary (F G₁ G₂ : Type) (n : ℕ) :=
  (Fin (n + 1) → G₁) → (Fin 2 → G₂) → ProbComp (G₁ × F × F × G₁ × F × G₁)

/-- Whether an evaluation-binding output wins: both openings are accepted and the values differ. -/
def evalBindingWins [DecidableEq F] [DecidableEq Gₜ] (e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ) (g₁ : G₁)
    (vk : Fin 2 → G₂) : G₁ × F × F × G₁ × F × G₁ → Bool
  | (cm, q, r₁, π₁, r₂, π₂) =>
    verifyOpening e g₁ vk cm q r₁ π₁ && verifyOpening e g₁ vk cm q r₂ π₂ && r₁ != r₂

/-- The evaluation-binding game: sample the trapdoor, run the adversary on the keys, and check
the output with `evalBindingWins`. -/
noncomputable def evalBindingExperiment [Fintype F] [DecidableEq F] [DecidableEq Gₜ]
    (e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ) (g₁ : G₁) (g₂ : G₂) (A : EvalBindingAdversary F G₁ G₂ n) :
    ProbComp Bool := do
  let τ ← SDH.sampleTrapdoor F
  let out ← A (committerKey g₁ τ n) (verifierKey g₂ τ)
  return evalBindingWins e g₁ (verifierKey g₂ τ) out

/-- The t-SDH reduction: run the evaluation-binding adversary once and answer with
`evalBindingReduction`. -/
def evalBindingAdversary (A : EvalBindingAdversary F G₁ G₂ n) : TSDH.Adversary F G₁ G₂ n :=
  fun ck vk => (fun out : G₁ × F × F × G₁ × F × G₁ =>
    evalBindingReduction out.2.1 out.2.2.1 out.2.2.2.1 out.2.2.2.2.1 out.2.2.2.2.2) <$> A ck vk

end EvaluationBinding

section FunctionBinding

open FunctionBinding

/-- A function-binding adversary receives the committer and verifier keys and returns a
commitment and a list of openings `(q, r, π)`. -/
abbrev FunctionBindingAdversary (F G₁ G₂ : Type) (n : ℕ) :=
  (Fin (n + 1) → G₁) → (Fin 2 → G₂) → ProbComp (G₁ × List (Opening F G₁))

/-- Whether a function-binding output wins: every opening is accepted and no coefficient vector
of length `n + 1` fits all openings. -/
def functionBindingWins [Fintype F] [DecidableEq F] [DecidableEq Gₜ] (e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ)
    (g₁ : G₁) (vk : Fin 2 → G₂) (out : G₁ × List (Opening F G₁)) : Bool :=
  out.2.all (fun o => verifyOpening e g₁ vk out.1 o.1 o.2.1 o.2.2) &&
    decide (¬ ∃ c : Fin (n + 1) → F, ∀ o ∈ out.2, evaluate c o.1 = o.2.1)

/-- The function-binding game: sample the trapdoor, run the adversary on the keys, and check
the output with `functionBindingWins`. -/
noncomputable def functionBindingExperiment [Fintype F] [DecidableEq F] [DecidableEq Gₜ]
    (e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ) (g₁ : G₁) (g₂ : G₂) (A : FunctionBindingAdversary F G₁ G₂ n) :
    ProbComp Bool := do
  let τ ← SDH.sampleTrapdoor F
  let out ← A (committerKey g₁ τ n) (verifierKey g₂ τ)
  return functionBindingWins (n := n) e g₁ (verifierKey g₂ τ) out

/-- The ARSDH reduction: run the function-binding adversary once and answer with
`functionBindingReduction pts ck vk`. -/
def functionBindingAdversary [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂]
    (pts : Fin (n + 2) ↪ F) (A : FunctionBindingAdversary F G₁ G₂ n) :
    ARSDH.Adversary F G₁ G₂ n :=
  fun ck vk => (fun out : G₁ × List (Opening F G₁) =>
    functionBindingReduction pts ck vk out.1 out.2) <$> A ck vk

end FunctionBinding

section Bounds

variable [Fintype F] [DecidableEq F] [DecidableEq Gₜ]
variable {e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ} {g₁ : G₁} {g₂ : G₂}

/-- **Evaluation binding reduces to t-SDH.** If `e g₁ g₂ ≠ 0` and `g₁` generates `G₁`, every
evaluation-binding adversary wins at most as often as its reduction `evalBindingAdversary A`
wins `TSDH.experiment`. -/
theorem evalBinding_le_tsdh (he : e g₁ g₂ ≠ 0) (hg₁ : Function.Surjective (· • g₁ : F → G₁))
    (A : EvalBindingAdversary F G₁ G₂ n) :
    Pr{let b ← evalBindingExperiment e g₁ g₂ A}[b = true] ≤
      Pr{let b ← TSDH.experiment g₁ g₂ (evalBindingAdversary A)}[b = true] := by
  unfold evalBindingExperiment TSDH.experiment evalBindingAdversary
  simp only [bind_map_left]
  refine prEvent_bind_mono_of_forall_le _ _ _ (· = true) (· = true) fun τ => ?_
  refine prEvent_bind_mono_of_forall_le _ _ _ (· = true) (· = true) fun out => ?_
  refine prEvent_pure_le_pure _ _ _ _ fun h => ?_
  obtain ⟨cm, q, r₁, π₁, r₂, π₂⟩ := out
  simp only [evalBindingWins, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
  simpa only [decide_eq_true_eq] using evalBindingReduction_wins he hg₁ τ h.1.1 h.1.2 h.2

/-- **Evaluation binding from t-SDH over an adversary class.** If every adversary in `Adv` wins
`TSDH.experiment` with probability at most `ε`, and `Adv` contains the reduction
`evalBindingAdversary A`, then `A` wins the evaluation-binding game with probability at most
`ε`. -/
theorem evalBinding_le_of_tsdh (he : e g₁ g₂ ≠ 0)
    (hg₁ : Function.Surjective (· • g₁ : F → G₁)) {Adv : Set (TSDH.Adversary F G₁ G₂ n)}
    {ε : ℝ≥0∞} (hε : ∀ B ∈ Adv, Pr{let b ← TSDH.experiment g₁ g₂ B}[b = true] ≤ ε)
    (A : EvalBindingAdversary F G₁ G₂ n) (hA : evalBindingAdversary A ∈ Adv) :
    Pr{let b ← evalBindingExperiment e g₁ g₂ A}[b = true] ≤ ε :=
  (evalBinding_le_tsdh he hg₁ A).trans (hε _ hA)

/-- **Function binding reduces to ARSDH.** If `e g₁ g₂ ≠ 0` and `g₁` generates `G₁`, every
function-binding adversary wins at most as often as its reduction
`functionBindingAdversary pts A` wins `ARSDH.experiment`, for any `n + 2` distinct points
`pts`. -/
theorem functionBinding_le_arsdh [DecidableEq G₁] [DecidableEq G₂] (he : e g₁ g₂ ≠ 0)
    (hg₁ : Function.Surjective (· • g₁ : F → G₁)) (pts : Fin (n + 2) ↪ F)
    (A : FunctionBindingAdversary F G₁ G₂ n) :
    Pr{let b ← functionBindingExperiment e g₁ g₂ A}[b = true] ≤
      Pr{let b ← ARSDH.experiment g₁ g₂ (functionBindingAdversary pts A)}[b = true] := by
  unfold functionBindingExperiment ARSDH.experiment functionBindingAdversary
  simp only [bind_map_left]
  refine prEvent_bind_mono_of_forall_le _ _ _ (· = true) (· = true) fun τ => ?_
  refine prEvent_bind_mono_of_forall_le _ _ _ (· = true) (· = true) fun out => ?_
  refine prEvent_pure_le_pure _ _ _ _ fun h => ?_
  obtain ⟨cm, os⟩ := out
  simp only [functionBindingWins, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  simp only [decide_eq_true_eq]
  exact FunctionBinding.functionBindingReduction_wins he hg₁ τ pts h.1 h.2

/-- **Function binding from ARSDH over an adversary class.** If every adversary in `Adv` wins
`ARSDH.experiment` with probability at most `ε`, and `Adv` contains the reduction
`functionBindingAdversary pts A`, then `A` wins the function-binding game with probability at
most `ε`. -/
theorem functionBinding_le_of_arsdh [DecidableEq G₁] [DecidableEq G₂] (he : e g₁ g₂ ≠ 0)
    (hg₁ : Function.Surjective (· • g₁ : F → G₁)) (pts : Fin (n + 2) ↪ F)
    {Adv : Set (ARSDH.Adversary F G₁ G₂ n)} {ε : ℝ≥0∞}
    (hε : ∀ B ∈ Adv, Pr{let b ← ARSDH.experiment g₁ g₂ B}[b = true] ≤ ε)
    (A : FunctionBindingAdversary F G₁ G₂ n) (hA : functionBindingAdversary pts A ∈ Adv) :
    Pr{let b ← functionBindingExperiment e g₁ g₂ A}[b = true] ≤ ε :=
  (functionBinding_le_arsdh he hg₁ pts A).trans (hε _ hA)

end Bounds

end KZG

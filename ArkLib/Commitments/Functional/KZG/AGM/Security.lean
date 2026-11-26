/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Commitments.Functional.KZG.AGM.Reduction
public import ArkLib.Commitments.Functional.KZG.AGM.Sampling

/-!
# KZG AGM extractability and binding from PairingDLog

Extractability, evaluation binding, and function binding reduce to `(n, 1)`-PairingDLog,
with an additive `1 / |F|` for changing the trapdoor distribution. Extraction reads the
commitment's explanation; only the discrete-logarithm reduction invokes the root finder.

References: [KZG10TR]; Fuchsbauer, Kiltz, and Loss, *The Algebraic Group Model and its
Applications*, CRYPTO 2018.
-/

@[expose] public section

open CompPoly OracleComp OracleSpec
open scoped ENNReal

namespace KZG.AGM

variable {F G₁ G₂ Gₜ D : Type} [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
  [AddCommGroup Gₜ] [Module F Gₜ] [DecidableEq G₂] [DecidableEq Gₜ] {n : ℕ}
  {e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ} {g₁ : G₁} {g₂ : G₂}

omit [Fintype F] [DecidableEq F] [SampleableType F] [DecidableEq G₂] in
/-- The second-source powers in PairingDLog are precisely the KZG verifier key. -/
theorem powers_eq_verifierKey (g₂ : G₂) (x : F) :
    (fun j : Fin (1 + 1) => x ^ (j : ℕ) • g₂) = verifierKey g₂ x := by
  funext j
  fin_cases j <;> simp [verifierKey]

/-- Extractability against algebraic adversaries reduces to `(n, 1)`-PairingDLog.
The extractor reads coefficients and the reduction finds roots; no source-group generator
surjectivity is required. -/
theorem extract_le_pairingDLog (he : e g₁ g₂ ≠ 0)
    (roots : CPolynomial F → List F)
    (hroots : ∀ p, p ≠ 0 → ∀ a, p.eval a = 0 → a ∈ roots p)
    (claims : D → List (F × F)) (A : Adversary F G₁ G₂ D) :
    Pr{let b ← extractExperiment (n := n) e g₁ g₂ claims A}[b = true] ≤
      Pr{let b ← PairingDLog.experiment g₁ g₂ (reduction (n := n) g₂ roots claims A)}[b = true] +
        1 / (Fintype.card F : ℝ≥0∞) := by
  unfold extractExperiment
  refine (sampleTrapdoor_event_le
    (fun τ => do
      let out ← run A (committerKey g₁ τ n) (verifierKey g₂ τ)
      return extractWins (n := n) e g₁ (verifierKey g₂ τ) claims out) (· = true)).trans ?_
  refine add_le_add ?_ le_rfl
  unfold PairingDLog.experiment reduction
  simp only [bind_map_left, powers_eq_verifierKey]
  refine prEvent_bind_mono_of_forall_le _ _ _ (· = true) (· = true) fun τ => ?_
  refine prEvent_bind_mono_of_forall_le_of_support _ _ _ (· = true) (· = true)
    fun out hout => ?_
  refine prEvent_pure_le_pure _ _ _ _ fun hwin => ?_
  apply decide_eq_true
  exact recover_eq he roots claims τ out
    (trapdoor_mem_candidates he roots hroots claims τ out (run_valid A _ _ out hout) hwin)

omit [Fintype F] [SampleableType F] [DecidableEq G₂] in
/-- Two accepted openings with different values cannot both agree with the extractor. -/
theorem evalBindingWins_implies_extract (vk : Fin 2 → G₂)
    (out : Output F G₁ G₂ (F × F × F))
    (h : evalBindingWins e g₁ vk (point out 0, out.value.data.1, out.value.data.2.1,
      point out 1, out.value.data.2.2, point out 2) = true) :
    extractWins (n := n) e g₁ vk evalClaims out = true := by
  simp only [evalBindingWins, Bool.and_eq_true, bne_iff_ne] at h
  have hbad : out.value.data.2.1 ≠ evaluate (coefficients (n := n) out 0) out.value.data.1 ∨
      out.value.data.2.2 ≠ evaluate (coefficients (n := n) out 0) out.value.data.1 := by
    by_contra hn
    simp only [not_or, not_not] at hn
    exact h.2 (hn.1.trans hn.2.symm)
  simp [extractWins, openings, evalClaims, List.ofFn_succ, h.1.1, h.1.2, hbad]

omit [SampleableType F] [DecidableEq G₂] in
/-- A function-binding winner has an accepted opening inconsistent with the commitment's own
coefficient vector, since that vector is among those quantified over by the existing game. -/
theorem functionBindingWins_implies_extract (vk : Fin 2 → G₂)
    (out : Output F G₁ G₂ (List (F × F)))
    (h : functionBindingWins (n := n) e g₁ vk (point out 0, openings id out) = true) :
    extractWins (n := n) e g₁ vk id out = true := by
  simp only [functionBindingWins, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  have hn := h.2
  simp only [not_exists, not_forall] at hn
  obtain ⟨o, ho, hbad⟩ := hn (coefficients (n := n) out 0)
  simp only [extractWins, List.any_eq_true]
  refine ⟨o, ho, ?_⟩
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨h.1 o ho, Ne.symm hbad⟩

/-- Evaluation binding in the existing KZG game against the forgetful algebraic adversary. -/
theorem evalBinding_le_pairingDLog (he : e g₁ g₂ ≠ 0)
    (roots : CPolynomial F → List F)
    (hroots : ∀ p, p ≠ 0 → ∀ a, p.eval a = 0 → a ∈ roots p)
    (A : Adversary F G₁ G₂ (F × F × F)) :
    Pr{let b ← evalBindingExperiment e g₁ g₂ (toEvalBindingAdversary (n := n) A)}[b = true] ≤
      Pr{let b ← (PairingDLog.experiment g₁ g₂
        (reduction (n := n) g₂ roots evalClaims A))}[b = true] +
        1 / (Fintype.card F : ℝ≥0∞) := by
  refine le_trans ?_ (extract_le_pairingDLog he roots hroots evalClaims A)
  unfold evalBindingExperiment toEvalBindingAdversary extractExperiment
  simp only [bind_map_left]
  refine prEvent_bind_mono_of_forall_le _ _ _ (· = true) (· = true) fun τ => ?_
  refine prEvent_bind_mono_of_forall_le _ _ _ (· = true) (· = true) fun out => ?_
  exact prEvent_pure_le_pure _ _ _ _ (evalBindingWins_implies_extract (n := n) _ out)

/-- Function binding in the existing KZG game against the forgetful algebraic adversary. -/
theorem functionBinding_le_pairingDLog (he : e g₁ g₂ ≠ 0)
    (roots : CPolynomial F → List F)
    (hroots : ∀ p, p ≠ 0 → ∀ a, p.eval a = 0 → a ∈ roots p)
    (A : Adversary F G₁ G₂ (List (F × F))) :
    Pr{let b ← (functionBindingExperiment e g₁ g₂
      (toFunctionBindingAdversary (n := n) A))}[b = true] ≤
      Pr{let b ← (PairingDLog.experiment g₁ g₂
        (reduction (n := n) g₂ roots id A))}[b = true] +
        1 / (Fintype.card F : ℝ≥0∞) := by
  refine le_trans ?_ (extract_le_pairingDLog he roots hroots id A)
  unfold functionBindingExperiment toFunctionBindingAdversary extractExperiment
  simp only [bind_map_left]
  refine prEvent_bind_mono_of_forall_le _ _ _ (· = true) (· = true) fun τ => ?_
  refine prEvent_bind_mono_of_forall_le _ _ _ (· = true) (· = true) fun out => ?_
  exact prEvent_pure_le_pure _ _ _ _ (functionBindingWins_implies_extract (n := n) _ out)

end KZG.AGM

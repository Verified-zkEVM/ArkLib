/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Commitments.Functional.KZG.AGM.FirstReduction

/-!
# KZG binding via first-claim recovery

Both existing binding games reduce to `(n, 1)`-PairingDLog using at most `n + 1` candidate
checks. Changing nonzero trapdoor sampling to uniform sampling costs `1 / |F|`.

References: [KZG10TR]; Fuchsbauer–Kiltz–Loss, CRYPTO 2018.
-/

@[expose] public section

open CompPoly OracleComp OracleSpec
open scoped ENNReal

namespace KZG.AGM

variable {F G₁ G₂ Gₜ D : Type} [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
  [AddCommGroup Gₜ] [Module F Gₜ] [DecidableEq G₂] [DecidableEq Gₜ] {n : ℕ}
  {e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ} {g₁ : G₁} {g₂ : G₂}

/-- Any Boolean event implying the binding witness reduces by first-claim recovery. -/
theorem binding_le_pairingDLog_first (he : e g₁ g₂ ≠ 0)
    (roots : CPolynomial F → List F)
    (hroots : ∀ p, p ≠ 0 → ∀ a, p.eval a = 0 → a ∈ roots p)
    (claims : D → List (F × F)) (A : Adversary F G₁ G₂ D)
    (win : (Fin 2 → G₂) → Output F G₁ G₂ D → Bool)
    (hwin : ∀ vk out, win vk out = true → bindingWitness (n := n) e g₁ vk claims out) :
    Pr{let b ← (do
      let τ ← SDH.sampleTrapdoor F
      let out ← run A (committerKey g₁ τ n) (verifierKey g₂ τ)
      pure (win (verifierKey g₂ τ) out))}[b = true] ≤
      Pr{let b ← (PairingDLog.experiment g₁ g₂
        (reductionFirst (n := n) g₂ roots claims A))}[b = true] +
          1 / (Fintype.card F : ℝ≥0∞) := by
  refine (sampleTrapdoor_event_le
    (fun τ => do
      let out ← run A (committerKey g₁ τ n) (verifierKey g₂ τ)
      return win (verifierKey g₂ τ) out) (· = true)).trans ?_
  refine add_le_add ?_ le_rfl
  unfold PairingDLog.experiment reductionFirst
  simp only [bind_map_left, powers_eq_verifierKey]
  refine prEvent_bind_mono_of_forall_le _ _ _ (· = true) (· = true) fun τ => ?_
  refine prEvent_bind_mono_of_forall_le_of_support _ _ _ (· = true) (· = true)
    fun out hout => ?_
  refine prEvent_pure_le_pure _ _ _ _ fun hw => ?_
  apply decide_eq_true
  exact recoverFirst_eq he roots claims τ out
    (trapdoor_mem_candidatesFirst he roots hroots claims τ out (run_valid A _ _ out hout)
      (hwin _ _ hw))

omit [Fintype F] [SampleableType F] [DecidableEq G₂] in
/-- An evaluation-binding winner supplies the all-accepted binding witness. -/
theorem evalBindingWins_bindingWitness (vk : Fin 2 → G₂)
    (out : Output F G₁ G₂ (F × F × F))
    (h : evalBindingWins e g₁ vk (point out 0, out.value.data.1, out.value.data.2.1,
      point out 1, out.value.data.2.2, point out 2) = true) :
    bindingWitness (n := n) e g₁ vk evalClaims out := by
  have hx := evalBindingWins_implies_extract (n := n) vk out h
  simp only [evalBindingWins, Bool.and_eq_true, bne_iff_ne] at h
  constructor
  · simp [openings, evalClaims, List.ofFn_succ, h.1.1, h.1.2]
  · simp only [extractWins, openings, List.any_eq_true, List.mem_ofFn] at hx
    obtain ⟨o, ⟨i, rfl⟩, hi⟩ := hx
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hi
    exact ⟨i, hi.2⟩

omit [SampleableType F] [DecidableEq G₂] in
/-- A function-binding winner supplies the all-accepted binding witness. -/
theorem functionBindingWins_bindingWitness (vk : Fin 2 → G₂)
    (out : Output F G₁ G₂ (List (F × F)))
    (h : functionBindingWins (n := n) e g₁ vk (point out 0, openings id out) = true) :
    bindingWitness (n := n) e g₁ vk id out := by
  have hx := functionBindingWins_implies_extract (n := n) vk out h
  constructor
  · simp only [functionBindingWins, Bool.and_eq_true] at h
    exact List.all_eq_true.mp h.1
  · simp only [extractWins, openings, List.any_eq_true, List.mem_ofFn] at hx
    obtain ⟨o, ⟨i, rfl⟩, hi⟩ := hx
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hi
    exact ⟨i, hi.2⟩

/-- Evaluation binding reduces to first-claim recovery without source-group surjectivity. -/
theorem evalBinding_le_pairingDLog_first (he : e g₁ g₂ ≠ 0)
    (roots : CPolynomial F → List F)
    (hroots : ∀ p, p ≠ 0 → ∀ a, p.eval a = 0 → a ∈ roots p)
    (A : Adversary F G₁ G₂ (F × F × F)) :
    Pr{let b ← (evalBindingExperiment e g₁ g₂ (toEvalBindingAdversary (n := n) A))}[b = true] ≤
      Pr{let b ← (PairingDLog.experiment g₁ g₂
        (reductionFirst (n := n) g₂ roots evalClaims A))}[b = true] +
          1 / (Fintype.card F : ℝ≥0∞) := by
  simpa only [evalBindingExperiment, toEvalBindingAdversary, bind_map_left] using
    binding_le_pairingDLog_first he roots hroots evalClaims A
      (fun vk out => evalBindingWins e g₁ vk (point out 0, out.value.data.1,
        out.value.data.2.1, point out 1, out.value.data.2.2, point out 2))
      (evalBindingWins_bindingWitness (n := n))

/-- Function binding reduces to first-claim recovery without source-group surjectivity. -/
theorem functionBinding_le_pairingDLog_first (he : e g₁ g₂ ≠ 0)
    (roots : CPolynomial F → List F)
    (hroots : ∀ p, p ≠ 0 → ∀ a, p.eval a = 0 → a ∈ roots p)
    (A : Adversary F G₁ G₂ (List (F × F))) :
    Pr{let b ← (functionBindingExperiment e g₁ g₂
      (toFunctionBindingAdversary (n := n) A))}[b = true] ≤
      Pr{let b ← (PairingDLog.experiment g₁ g₂
        (reductionFirst (n := n) g₂ roots id A))}[b = true] +
          1 / (Fintype.card F : ℝ≥0∞) := by
  simpa only [functionBindingExperiment, toFunctionBindingAdversary, bind_map_left] using
    binding_le_pairingDLog_first he roots hroots id A
      (fun vk out => functionBindingWins (n := n) e g₁ vk (point out 0, openings id out))
      (functionBindingWins_bindingWitness (n := n))

end KZG.AGM

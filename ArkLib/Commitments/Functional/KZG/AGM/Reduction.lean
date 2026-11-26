/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Commitments.Functional.KZG.AGM.Adversary
public import ArkLib.Commitments.Functional.KZG.AGM.Polynomial
public import VCVio.CryptoFoundations.HardnessAssumptions.PairingDLog

/-!
# KZG extraction reduces to two-source discrete logarithms

The reduction searches opening-polynomial roots and selects the trapdoor using the verifier key.
This works even for constant commitments (`n = 0`).

References: [KZG10TR]; Fuchsbauer, Kiltz, and Loss, *The Algebraic Group Model and its
Applications*, CRYPTO 2018.
-/

@[expose] public section

open CompPoly OracleComp

namespace KZG.AGM

variable {F G₁ G₂ Gₜ D : Type} [Field F] [DecidableEq F]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
  [AddCommGroup Gₜ] [Module F Gₜ] {n : ℕ}

/-- An accepted opening disagrees with the coefficient-reading extractor. -/
def extractWins [DecidableEq Gₜ] (e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ) (g₁ : G₁)
    (vk : Fin 2 → G₂) (claims : D → List (F × F)) (out : Output F G₁ G₂ D) : Bool :=
  (openings claims out).any fun o =>
    verifyOpening e g₁ vk (point out 0) o.1 o.2.1 o.2.2 &&
      decide (o.2.1 ≠ evaluate (coefficients (n := n) out 0) o.1)

/-- The extractor just reads the commitment's coefficients; it performs no root finding. -/
noncomputable def extractExperiment [Fintype F] [DecidableEq Gₜ]
    (e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ) (g₁ : G₁) (g₂ : G₂)
    (claims : D → List (F × F)) (A : Adversary F G₁ G₂ D) : ProbComp Bool := do
  let τ ← SDH.sampleTrapdoor F
  let out ← run A (committerKey g₁ τ n) (verifierKey g₂ τ)
  return extractWins (n := n) e g₁ (verifierKey g₂ τ) claims out

/-- Collect roots of every opening equation, without testing acceptance. -/
def candidates (roots : CPolynomial F → List F) (claims : D → List (F × F))
    (out : Output F G₁ G₂ D) : List F :=
  (List.ofFn fun i : Fin (claims out.value.data).length =>
    let zv := (claims out.value.data)[i]
    openingPolynomial (coefficients (n := n) out 0) (coefficients out (i.val + 1))
      zv.1 zv.2).flatMap roots

/-- Select the first root matching the second verifier-key entry, or zero if none matches. -/
def recover [DecidableEq G₂] (g₂ : G₂) (vk : Fin 2 → G₂)
    (roots : CPolynomial F → List F) (claims : D → List (F × F))
    (out : Output F G₁ G₂ D) : F :=
  ((candidates (n := n) roots claims out).find? fun r => decide (r • g₂ = vk 1)).getD 0

/-- A plain scalar-output program, suitable for composition with generic-to-algebraic
translation. -/
def reduction [DecidableEq G₂] (g₂ : G₂) (roots : CPolynomial F → List F)
    (claims : D → List (F × F)) (A : Adversary F G₁ G₂ D) :
    PairingDLog.Adversary F G₁ G₂ n 1 :=
  fun ck vk => recover (n := n) g₂ vk roots claims <$> run A ck vk

/-- A winning algebraic output places the trapdoor among the candidate roots. -/
theorem trapdoor_mem_candidates [DecidableEq Gₜ]
    {e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ} {g₁ : G₁} {g₂ : G₂} (he : e g₁ g₂ ≠ 0)
    (roots : CPolynomial F → List F)
    (hroots : ∀ p, p ≠ 0 → ∀ a, p.eval a = 0 → a ∈ roots p)
    (claims : D → List (F × F)) (τ : F) (out : Output F G₁ G₂ D)
    (hvalid : out.Valid (initialInput (committerKey g₁ τ n) (verifierKey g₂ τ)).groups)
    (hwin : extractWins (n := n) e g₁ (verifierKey g₂ τ) claims out = true) :
    τ ∈ candidates (n := n) roots claims out := by
  simp only [extractWins, openings, List.any_eq_true, List.mem_ofFn] at hwin
  obtain ⟨o, ⟨i, rfl⟩, hi⟩ := hwin
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hi
  have hc := point_eq_commit out (committerKey g₁ τ n) (verifierKey g₂ τ) hvalid
  rw [hc 0, hc (i.val + 1)] at hi
  have hp := accepted_opening_root he (coefficients out 0) (coefficients out (i.val + 1))
    τ _ _ hi.1 hi.2
  apply List.mem_flatMap.mpr
  refine ⟨_, List.mem_ofFn.mpr ⟨i, rfl⟩, hroots _ hp.1 τ hp.2⟩

/-- The verifier-key root test identifies the trapdoor, including when `n = 0`. -/
theorem recover_eq [DecidableEq G₂]
    {e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ} {g₁ : G₁} {g₂ : G₂} (he : e g₁ g₂ ≠ 0)
    (roots : CPolynomial F → List F) (claims : D → List (F × F))
    (τ : F) (out : Output F G₁ G₂ D)
    (hm : τ ∈ candidates (n := n) roots claims out) :
    recover (n := n) g₂ (verifierKey g₂ τ) roots claims out = τ := by
  unfold recover
  cases hf : (candidates (n := n) roots claims out).find?
      (fun r => decide (r • g₂ = (verifierKey g₂ τ) 1)) with
  | none =>
      have hn := List.find?_eq_none.mp hf τ hm
      simp [verifierKey] at hn
  | some r =>
      have hr := List.find?_some hf
      have hr' : r • g₂ = τ • g₂ := by
        simpa [verifierKey] using of_decide_eq_true hr
      exact smul_right_injective_of_pairing_ne_zero he hr'

end KZG.AGM

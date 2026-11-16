/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Coratger
-/

import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.AffineCombiner.Probability
import Mathlib.Algebra.Field.ZMod

/-! # Acceptance clients for the affine-combiner probability and code interfaces -/

open Polynomial ReedSolomon CoreDefinitions
open scoped ProbabilityTheory

section Algebra

variable {F ι : Type} [Field F] [DecidableEq F] [Fintype ι]

-- This client has neither a sampler nor a decidable equality on the coordinate type.
open Classical in
example (domain : ι ↪ F) (f g : ι → F) (L P F₀ G₀ : F[X]) :
    agreementLoss domain f g L P F₀ G₀ =
      (polynomialAgreementSet domain (combinedWord domain f g L) P).filter
        (fun i ↦ ¬ (F₀.eval (domain i) = f i ∧ G₀.eval (domain i) = g i)) := by
  classical
  rw [agreementLoss_eq_sdiff]
  ext i
  simp

-- The first word is an arbitrary function; callers need no interpolation witness.
example (domain : ι ↪ F) (f : ι → F) (G₀ : F[X]) {d A s : ℕ}
    (hG : G₀.degree < d) (α β : F) (P : F[X]) :
    ¬ IsAffineExceptional domain f (fun i ↦ G₀.eval (domain i)) d A s α β P :=
  not_isAffineExceptional_of_eval f G₀ hG α β P

-- No inequality between the threshold and the degree is required for compatibility.
example (domain : ι ↪ F) (f g : ι → F) (d A : ℕ) (α : F) :
    (∃ P, IsScalarExceptional domain f g d A 0 α P) ↔
      Code.IsProjectionBad (AffineLineGenerator F) (code domain (d + 1)) A α ![f, g] :=
  exists_isScalarExceptional_zero_iff_isProjectionBad domain f g d A α

-- The degree offset is visible in the public code-membership interface.
example (domain : ι ↪ F) (F₀ G₀ : F[X]) {d : ℕ}
    (hF : F₀.degree ≤ d) (hG : G₀.degree < d) :
    evalOnPoints domain F₀ ∈ code domain (d + 1) ∧ evalOnPoints domain G₀ ∈ code domain d :=
  affine_witnesses_mem_code domain F₀ G₀ hF hG

end Algebra

private instance : Fact (Nat.Prime 5) := ⟨by decide⟩

private def fullDomain : ZMod 5 ↪ ZMod 5 := Function.Embedding.refl _

-- This lower bound targets the pre-existing MCA API, at nonzero degree and radius.
example : (3 : ENNReal) / 5 ≤
    mcaError (AffineLineGenerator (ZMod 5)) (code fullDomain 2) (2 / 5 : ℝ) := by
  have h := mcaError_affineLine_ge_of_threshold fullDomain (d := 1) (A := 3)
    (2 / 5) (by norm_num) (by norm_num [ZMod.card]) (by norm_num [ZMod.card])
  norm_num [ZMod.card, ENNReal.ofReal_div_of_pos] at h
  exact h

-- The new error has exactly the old error's value, with the inclusive degree translated.
example : scalarMcaError fullDomain 1 3 0 =
    mcaError (AffineLineGenerator (ZMod 5)) (code fullDomain 2) (2 / 5 : ℝ) := by
  exact scalarMcaError_zero_eq_mcaError fullDomain 1 3 (2 / 5) (by norm_num [ZMod.card])

-- The sampling interface uses native probabilities and the same canonical error.
example (f g : ZMod 5 → ZMod 5) :
    Pr{let c ← $ᵗ (ZMod 5 × ZMod 5)}[∃ P,
      IsAffineExceptional fullDomain f g 1 3 1 c.1 c.2 P] ≤
        affineMcaError fullDomain 1 3 1 :=
  prob_isAffineExceptional_le fullDomain f g 1 3 1

#print axioms ReedSolomon.scalarMcaError_zero_eq_mcaError
#print axioms ReedSolomon.mcaError_affineLine_ge_of_threshold
#print axioms ReedSolomon.affineMcaError_eq_iSup_prob

/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Coratger
-/

import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.AffineCombiner.Probability
import Mathlib.Algebra.Field.ZMod

/-! # Acceptance clients for the affine-combiner probability and code interfaces -/

open Polynomial ReedSolomon CoreDefinitions

section Algebra

variable {F ι : Type} [Field F] [DecidableEq F] [Fintype ι]

-- This client has neither a sampler nor a decidable equality on the coordinate type.
example (domain : ι ↪ F) (f g : ι → F) (L P F₀ G₀ : F[X]) :
    agreementLoss domain f g L P F₀ G₀ =
      (polynomialAgreementSet domain (combinedWord domain f g L) P).filter
        (fun i ↦ ¬ (F₀.eval (domain i) = f i ∧ G₀.eval (domain i) = g i)) := by
  classical
  rw [agreementLoss_eq_sdiff]
  ext i
  simp

end Algebra

private instance : Fact (Nat.Prime 5) := ⟨by decide⟩

private def fullDomain : ZMod 5 ↪ ZMod 5 := Function.Embedding.refl _

-- This lower bound concerns `CoreDefinitions.mcaError` at nonzero degree and radius.
example : (3 : ENNReal) / 5 ≤
    mcaError (AffineLineGenerator (ZMod 5)) (code fullDomain 2) (2 / 5 : ℝ) := by
  have h := le_mcaError_affineLine_of_ceil_eq fullDomain (d := 1) (A := 3)
    (2 / 5) (by norm_num) (by norm_num [ZMod.card]) (by norm_num [ZMod.card])
  norm_num [ZMod.card, ENNReal.ofReal_div_of_pos] at h
  exact h

-- The scalar error equals `CoreDefinitions.mcaError` at the matching integer threshold.
example : scalarMcaError fullDomain 1 3 0 =
    mcaError (AffineLineGenerator (ZMod 5)) (code fullDomain 2) (2 / 5 : ℝ) := by
  exact scalarMcaError_zero_eq_mcaError fullDomain 1 3 (2 / 5) (by norm_num [ZMod.card])

/-- info: 'ReedSolomon.scalarMcaError_zero_eq_mcaError' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReedSolomon.scalarMcaError_zero_eq_mcaError
/-- info: 'ReedSolomon.le_mcaError_affineLine_of_ceil_eq' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReedSolomon.le_mcaError_affineLine_of_ceil_eq
/-- info: 'ReedSolomon.affineMcaError_eq_iSup_prob' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReedSolomon.affineMcaError_eq_iSup_prob

-- The set-difference characterization accepts the caller's equality instance.
example {F ι : Type*} [Field F] [DecidableEq F] [Fintype ι] [DecidableEq ι]
    (domain : ι ↪ F) (f g : ι → F) (L P F₀ G₀ : Polynomial F) :
    agreementLoss domain f g L P F₀ G₀ =
      polynomialAgreementSet domain (combinedWord domain f g L) P \
        commonPolynomialAgreementSet domain f g F₀ G₀ :=
  agreementLoss_eq_sdiff domain f g L P F₀ G₀

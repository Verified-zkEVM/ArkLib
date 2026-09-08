/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

import ArkLib.ProofSystem.RingSwitching.Packing.FullFamily.Phase

/-!
# Separation under an explicit commitment functionality premise

The public claims, input oracles, and slice message are fixed before drawing the challenge.
Although the bad event quantifies over packed witnesses after that draw, the functionality
premise identifies every such witness with one fixed polynomial. Injective transport
into the challenge algebra then reduces the event to the batching strategy's collision bound.
-/

noncomputable section

namespace RingSwitching.Packing.FullFamily

open MvPolynomial Probability ProbabilityTheory
open scoped NNReal ENNReal

variable {B : Type} [CommRing B] (data : PackingData B) (m : ℕ)
  {C : Type} [CommRing C] [Algebra B C] [Algebra data.P C] [IsScalarTower B data.P C]
  (bat : BatchingStrategy C data.ιE) (pc : PackedCommitment data.P m)

/-- The intermediate state after the prover's slice message. -/
def beforeChallenge (α : data.ιP → data.E) (r : Fin m → data.E)
    (oStmt : ∀ j, pc.OStmt j) (s : data.ιE → data.P) (p : data.P⦃≤ 1⦄[X Fin m]) : Prop :=
  data.claimConsistent α s ∧ pc.commitsTo oStmt p ∧ (s, p) ∈ data.sliceRel m r

/-- The final state after the verifier's batching challenge. -/
def afterChallenge (α : data.ιP → data.E) (r : Fin m → data.E)
    (oStmt : ∀ j, pc.OStmt j) (s : data.ιE → data.P) (c : bat.Challenge)
    (p : data.P⦃≤ 1⦄[X Fin m]) : Prop :=
  data.claimConsistent α s ∧ pc.commitsTo oStmt p ∧
    (target data bat s c, p) ∈ data.sumcheckClaimRel m r (bat.weight c)

/-- Fixed-prefix bad-transition bound with no challenge-dependent witness choice hidden in it. -/
theorem badEvent_le (hfunctional : pc.Functional) (hinj : Function.Injective (algebraMap data.P C))
    (α : data.ιP → data.E) (r : Fin m → data.E) (oStmt : ∀ j, pc.OStmt j)
    (s : data.ιE → data.P) :
    Pr_{ let c ←$ᵖ bat.Challenge }[
      ∃ p, ¬ beforeChallenge data m pc α r oStmt s p ∧
        afterChallenge data m bat pc α r oStmt s c p] ≤ (bat.error : ℝ≥0∞) := by
  classical
  by_cases hlive : ∃ p₀, pc.commitsTo oStmt p₀ ∧ data.claimConsistent α s ∧
      (s, p₀) ∉ data.sliceRel m r
  · obtain ⟨p₀, hcommit, _, hslice⟩ := hlive
    have hne : s ≠ honestSlices data m r p₀ := fun h => hslice fun u => congrFun h u
    refine (Pr_le_Pr_of_implies _ _ _ ?_).trans
      (bat.separates_map (algebraMap data.P C) hinj s (honestSlices data m r p₀) hne)
    rintro c ⟨p, _, _, hcommit', hsum⟩
    obtain rfl : p = p₀ := hfunctional hcommit' hcommit
    have hhonest := data.sumcheckClaim_of_slices
      (honestSlices_mem_sliceRel data m r p) (bat.weight c)
    exact hsum.trans hhonest.symm
  · push Not at hlive
    refine le_of_eq_of_le (prob_eq_zero_of_forall_not _ _ ?_) zero_le
    rintro c ⟨p, hnot, hc, hcommit, _⟩
    exact hnot ⟨hc, hcommit, hlive p hcommit hc⟩

end RingSwitching.Packing.FullFamily

end

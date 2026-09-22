/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

module

public import ArkLib.ProofSystem.Fri.Spec.Execution

/-!
# Soundness of the executable FRI query checks

We apply the agreement argument to the actual committed oracle history and executable
local checks. The tradeoff threshold is independent of the input's distance, as in [GMW25].

## References

* [Garreta, A., Mohnblatt, N., Wagner, B., *A Simplified Round-by-round Soundness Proof
  of FRI*][GMW25]
-/

@[expose] public section

namespace Fri.Spec

open Domain Polynomial ProximityGap ReedSolomon OracleComp Finset
open scoped ProbabilityTheory

variable {F : Type} [NonBinaryField F] [Fintype F] [DecidableEq F]
variable {n k : ℕ} {ω : SmoothCosetFftDomain n F}
variable (s : Fin (k + 1) → ℕ+) (d : ℕ+)

/-- A finite domain index as the subtype-valued initial query used by the verifier. -/
def initialQuery (z : Fin (2 ^ n)) : (ω.subdomain 0).toFinset :=
  ⟨ω z, by rw [CosetFftDomain.subdomain_zero_eq_self]; exact CosetFftDomain.mem_toFinset_self⟩

/-- No folding challenge in the retained commitment history is bad. -/
def SafeHistory (o : ∀ j, FinalOracleStatement s ω j) (α : FinalStatement F k)
    (θ : ℝ) : Prop :=
  ∀ i : Fin (k + 1), ¬ FoldingAgreementFailure
    (ω.subdomain (foldingPrefix s i.castSucc))
    (fun z ↦ committedFunction s o i.castSucc (ω.subdomain (foldingPrefix s i.castSucc) z))
    (s i).val (foldingDegree s d i.succ) θ (α i)

/-- The initial word, reindexed without changing its values. -/
def initialWord (o : ∀ j, FinalOracleStatement s ω j) : Fin (2 ^ n) → F :=
  fun z ↦ committedFunction s o 0 (ω z)

/-- The positions at which every executable local check accepts. -/
noncomputable def acceptingQueries (hs : (∑ j, (s j).val) ≤ n)
    (o : ∀ j, FinalOracleStatement s ω j) (α : FinalStatement F k) :
    Finset (Fin (2 ^ n)) := by
  classical
  exact univ.filter fun z ↦ ∀ i, simulateQ
    (OracleInterface.simOracle0 (FinalOracleStatement s ω) o)
    (QueryRound.checkRound s hs (finalPolynomial s o) (α i) i (initialQuery z)) = true

/-- Large sets of accepting executable queries agree with an original codeword. -/
theorem exists_codeword_agree_of_acceptingQueries
    (hs : (∑ j, (s j).val) ≤ n) (o : ∀ j, FinalOracleStatement s ω j)
    (α : FinalStatement F k) (θ : ℝ) (hsafe : SafeHistory s d o α θ)
    (hdegree : (finalPolynomial s o).natDegree < d.val)
    (S : Finset (Fin (2 ^ n))) (hS : S ⊆ acceptingQueries s hs o α)
    (hlarge : (2 ^ n : ℝ) * (1 - θ) ≤ S.card) :
    ∃ u ∈ code ω (2 ^ (∑ j, (s j).val) * d.val),
      ∀ z ∈ S, u z = initialWord s o z := by
  classical
  have hcheck : ∀ z ∈ S, ∀ i : Fin (k + 1),
      foldValue (ω.subdomain (foldingPrefix s i.castSucc))
        (fun y ↦ committedFunction s o i.castSucc (ω.subdomain (foldingPrefix s i.castSucc) y))
        (s i).val (α i) (ω z ^ (2 ^ foldingPrefix s i.succ)) =
      committedFunction s o i.succ (ω z ^ (2 ^ foldingPrefix s i.succ)) := by
    intro z hz i
    exact (QueryRound.eval_checkRound_iff_schedule s hs o (α i) i (initialQuery z)).mp
      ((mem_filter.mp (hS hz)).2 i)
  obtain ⟨q, hq, hagree⟩ := exists_polynomial_agree_on_schedule s d ω hs
    (committedFunction s o) α θ hsafe S hlarge (finalPolynomial s o).toPoly
    (by simpa only [CompPoly.CPolynomial.natDegree_toPoly] using hdegree)
    (fun z _ ↦ by simp [CompPoly.CPolynomial.eval_toPoly]) hcheck 0
  refine ⟨fun z ↦ q.eval (ω z), ?_, ?_⟩
  · rw [mem_code_iff_exists_polynomial_of_ne_zero]
    exact ⟨q, by simpa [foldingDegree] using hq, rfl⟩
  · simpa only [foldingPrefix_zero, pow_zero, pow_one, initialWord] using hagree

/-- Soundness density for the existing executable checks against an arbitrary history. -/
theorem acceptingQueries_density_le
    (hs : (∑ j, (s j).val) ≤ n) (o : ∀ j, FinalOracleStatement s ω j)
    (α : FinalStatement F k) (θ δ : ℝ) (hsafe : SafeHistory s d o α θ)
    (hdegree : (finalPolynomial s o).natDegree < d.val)
    (hdist : ∀ u ∈ code ω (2 ^ (∑ j, (s j).val) * d.val),
      δ ≤ (Code.relHammingDist (initialWord s o) u : ℝ)) :
    ((acceptingQueries s hs o α).card : ℝ) / 2 ^ n ≤ 1 - min θ δ := by
  apply accepting_density_le_of_agreement ω (initialWord s o) _ θ δ _ hdist
  exact exists_codeword_agree_of_acceptingQueries s d hs o α θ hsafe hdegree
    (acceptingQueries s hs o α) (fun _ h ↦ h)

/-- Independent uniform repetitions of the executable checks have the updated query error. -/
theorem queryChecks_soundness
    (hs : (∑ j, (s j).val) ≤ n) (o : ∀ j, FinalOracleStatement s ω j)
    (α : FinalStatement F k) (θ δ : ℝ) (t : ℕ) (hsafe : SafeHistory s d o α θ)
    (hdegree : (finalPolynomial s o).natDegree < d.val)
    (hdist : ∀ u ∈ code ω (2 ^ (∑ j, (s j).val) * d.val),
      δ ≤ (Code.relHammingDist (initialWord s o) u : ℝ)) :
    Pr{let zs ←$ᵗ (Fin t → Fin (2 ^ n))}[
      ∀ j, zs j ∈ acceptingQueries s hs o α] ≤
      ENNReal.ofReal (1 - min θ δ) ^ t := by
  rw [Probability.prob_uniform_pi_mem_finset_eq]
  apply pow_le_pow_left' _ t
  have h := ENNReal.ofReal_le_ofReal
    (acceptingQueries_density_le s d hs o α θ δ hsafe hdegree hdist)
  simpa [ENNReal.ofReal_div_of_pos, show (0 : ℝ) < 2 ^ n by positivity] using h

end Fri.Spec

import ArkLib.OracleReduction.Security.Basic
import ArkLib.ProofSystem.Logup.Protocol

/-!
# LogUp Soundness

Soundness target for Protocol 2 of Haböck's LogUp lookup argument (Cryptology ePrint Archive,
Paper 2022/1530, <https://eprint.iacr.org/2022/1530>).
-/

open scoped NNReal

namespace Logup

section Soundness

variable {ι : Type} (oSpec : OracleSpec ι)
variable (F : Type) [Field F] [Fintype F] [DecidableEq F] [Fact ((-1 : F) ≠ 1)]
  [SampleableType F]
variable (n M : ℕ)
variable (params : ProtocolParams M)
variable {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))

/-- Paper-shaped soundness error for the LogUp outer checks plus the embedded sumcheck error. -/
noncomputable def logupSoundnessError (F : Type) [Fintype F] (n M : ℕ) (params : ProtocolParams M)
    (sumcheckSoundnessError : ℝ≥0) : ℝ≥0 :=
  ((((M + 1) * Fintype.card (Hypercube n) - 1 : ℕ) : ℝ≥0) /
      ((Fintype.card F - Fintype.card (Hypercube n) : ℕ) : ℝ≥0)) +
    (((params.numGroups + 1 : ℕ) : ℝ≥0) / (Fintype.card F : ℝ≥0)) +
      sumcheckSoundnessError

/-- Main ArkLib soundness theorem for LogUp Protocol 2. -/
theorem logup_soundness (sumcheckSoundnessError : ℝ≥0) :
    (logupVerifier oSpec F n M params).soundness init impl
      (inputRelation F n M).language outputRelation.language
      (logupSoundnessError F n M params sumcheckSoundnessError) := by
  sorry

end Soundness

end Logup

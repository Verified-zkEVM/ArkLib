import ArkLib.OracleReduction.Security.Basic
import ArkLib.ProofSystem.Sumcheck.Spec.General

/-!
# Full Oracle Sum-check Completeness (LogUp-local)

Perfect completeness for the full oracle sum-check reduction, which LogUp's embedded phase needs but
`General.lean` does not provide (it has the full *non-oracle* and single-round oracle versions only).

Placeholder: currently a `sorry`, to be replaced by the proved theorem and ideally upstreamed.
-/

namespace Sumcheck

open Polynomial MvPolynomial OracleSpec OracleComp ProtocolSpec Finset

namespace Spec

variable (R : Type) [CommSemiring R] (deg : ℕ) {m : ℕ} (D : Fin m ↪ R) (n : ℕ)
variable {ι : Type} (oSpec : OracleSpec ι)
variable [DecidableEq R] [SampleableType R]
variable {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}

/-- Perfect completeness for the full sum-check oracle reduction.

Prove by `seqCompose_perfectCompleteness` over `SingleRound.oracleReduction_perfectCompleteness`,
as `reduction_perfectCompleteness` does for the non-oracle version. -/
theorem oracleReduction_perfectCompleteness :
    (oracleReduction R deg D n oSpec).perfectCompleteness init impl
      (relationRound R n deg D 0) (relationRound R n deg D (.last n)) :=
  OracleReduction.seqCompose_perfectCompleteness
    (rel := relationRound R n deg D)
    (R := SingleRound.oracleReduction R n deg D oSpec)
    (h := fun i => SingleRound.oracleReduction_perfectCompleteness i)

end Spec

end Sumcheck

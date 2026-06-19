import ArkLib.OracleReduction.Security.Basic
import ArkLib.ProofSystem.Sumcheck.Spec.General

/-!
# Full Oracle Sum-check Completeness (LogUp-local)

LogUp-local completeness bridge for the full oracle sumcheck reduction used by Protocol 2 of
Haböck's LogUp paper (Cryptology ePrint Archive, Paper 2022/1530,
<https://eprint.iacr.org/2022/1530>).

`ArkLib.ProofSystem.Sumcheck.Spec.General` provides the full non-oracle and single-round oracle
perfect-completeness theorems. LogUp needs the full composed oracle version for its embedded
sumcheck phase, so this file states the composed theorem by chaining the single-round result with
`OracleReduction.seqCompose_perfectCompleteness`.

This file is intentionally LogUp-local for now; the theorem is a candidate for upstreaming into the
generic sumcheck development.
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

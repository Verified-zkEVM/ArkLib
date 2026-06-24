/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.ProofSystem.Sumcheck.Interaction.SingleRound
import ArkLib.Interaction.Oracle.Program

open Interaction.TwoParty

/-!
# Sum-check single-round programmatic verifier

Additive experiment for the programmatic verifier shape. The stable one-round
reduction remains in `SingleRound`.
-/

namespace Sumcheck

open Interaction CompPoly CPoly OracleComp OracleSpec

section

variable {R : Type} [BEq R] [CommSemiring R] [LawfulBEq R] [Nontrivial R] {deg : ℕ}

/-- One-round sum-check verifier in the programmatic verifier shape.

The verifier-local terminal computation remains in `Verifier.Program.done`
instead of being flattened into the preceding public receiver node. -/
noncomputable def roundVerifierProgrammatic
    {ι : Type} {oSpec : OracleSpec.{0, 0} ι}
    {m_dom : ℕ} (D : Fin m_dom → R)
    (numVars : ℕ)
    (sampleChallenge : OracleComp oSpec R) :
    Interaction.Oracle.Verifier.Programmatic oSpec
      (RoundClaim R)
      (fun _ => roundSpec R deg)
      (fun _ => roundRoles R deg)
      (fun _ => roundOracleDeco R deg)
      (fun _ => PUnit)
      (fun _ => Sumcheck.PolyFamily R deg (numVars + 1))
      (fun _ _ => Option (RoundClaim R))
      (fun _ _ => Sumcheck.PolyFamily R deg (numVars + 1)) where
  toProgram := fun target _stmt =>
    .oracle <|
      .publicReceiver
        (by
          let access := Interaction.Oracle.Verifier.AccessFamily.ambient (oSpec := oSpec)
            (OStmtIn := Sumcheck.PolyFamily R deg (numVars + 1))
          letI :=
            access.instMonad
              ([]ₒ + @OracleInterface.spec (CDegreeLE R deg) inferInstance)
          change OracleComp
            ((oSpec + [Sumcheck.PolyFamily R deg (numVars + 1)]ₒ) +
              ([]ₒ + @OracleInterface.spec (CDegreeLE R deg) inferInstance))
            ((_ : R) × RoundClaim R × R)
          exact do
            let total ← (Finset.univ : Finset (Fin m_dom)).toList.foldlM
              (fun (acc : R) (j : Fin m_dom) => do
                let val : R ← oracle_query[CDegreeLE R deg] (D j)
                pure (acc + val))
              (0 : R)
            let chal : R ← liftM sampleChallenge
            pure ⟨chal, (target, total)⟩)
        (fun chal checked =>
          .done <| by
            let access := Interaction.Oracle.Verifier.AccessFamily.ambient (oSpec := oSpec)
              (OStmtIn := Sumcheck.PolyFamily R deg (numVars + 1))
            letI :=
              access.instMonad
                ([]ₒ + @OracleInterface.spec (CDegreeLE R deg) inferInstance)
            change OracleComp
              ((oSpec + [Sumcheck.PolyFamily R deg (numVars + 1)]ₒ) +
                ([]ₒ + @OracleInterface.spec (CDegreeLE R deg) inferInstance))
              (Interaction.Oracle.Verifier.TerminalOutput
                (RoundClaim R)
                (fun _ => roundSpec R deg)
                (fun _ => roundOracleDeco R deg)
                (fun _ => Sumcheck.PolyFamily R deg (numVars + 1))
                (fun _ _ => Option (RoundClaim R))
                (fun _ _ => Sumcheck.PolyFamily R deg (numVars + 1))
                target ⟨PUnit.unit, ⟨chal, PUnit.unit⟩⟩)
            exact do
              let nextClaim ←
                if checked.2 == checked.1 then do
                  let polyAtChal : R ← oracle_query[CDegreeLE R deg] chal
                  pure (some polyAtChal)
                else
                  pure none
              pure {
                stmt := nextClaim
                simulate := fun q =>
                  liftM <| ([Sumcheck.PolyFamily R deg (numVars + 1)]ₒ).query q
              })

/-- One-round sum-check oracle reduction with a programmatic verifier. -/
noncomputable def roundProgrammaticReduction
    {ι : Type} {oSpec : OracleSpec.{0, 0} ι}
    {m_dom : ℕ} (D : Fin m_dom → R)
    (numVars : ℕ)
    (sampleChallenge : OracleComp oSpec R) :
    Interaction.Oracle.Reduction.Programmatic oSpec
      (RoundClaim R)
      (fun _ => roundSpec R deg)
      (fun _ => roundRoles R deg)
      (fun _ => roundOracleDeco R deg)
      (fun _ => PUnit)
      (fun _ => Sumcheck.PolyFamily R deg (numVars + 1))
      (fun _ => PUnit)
      (fun _ _ => Option (RoundClaim R))
      (fun _ _ => Sumcheck.PolyFamily R deg (numVars + 1))
      (fun _ _ => PUnit) where
  prover := (roundReduction (R := R) (deg := deg) (oSpec := oSpec)
    D numVars sampleChallenge).prover
  verifier := roundVerifierProgrammatic (R := R) (deg := deg) D numVars sampleChallenge

end

end Sumcheck

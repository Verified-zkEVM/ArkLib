/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.ProofSystem.Sumcheck.Interaction.Defs
import ArkLib.Interaction.Oracle.Core

/-!
# Interaction-Native Sum-Check: Oracle Round Primitives

This module defines the oracle-native building blocks for the continuation-based
sum-check refactor.

The key design choice is that the protocol keeps the **original multivariate
polynomial** as its long-lived oracle statement. Each round derives the current
residual polynomial from the existing challenge prefix, but the oracle family
itself stays fixed across the whole protocol.

## Main Definitions

- `PolyStmt` / `PolyFamily`: the fixed original polynomial oracle.
- `roundOracleDecoration`: the sender's round polynomial message is queryable as
  an oracle.
- `oracleVerifierStep`: single-round oracle verifier for a live claim.
- `oracleVerifierStepOption`: single-round oracle verifier for the chained
  `Option` claim used by the full protocol after a previous rejection.
-/

namespace Sumcheck

open Interaction Interaction.OracleDecoration CompPoly CPoly OracleComp OracleSpec

section

variable (R : Type) [BEq R] [CommSemiring R] [LawfulBEq R] [Nontrivial R]
variable (deg : ℕ)

/-- Oracle decoration for one round: the prover's univariate round polynomial is
queryable via its evaluation oracle interface. -/
def roundOracleDecoration :
    OracleDecoration (roundSpec R deg) (roundRoles R deg) :=
  ⟨instOracleInterfaceCDegreeLE, fun _ => fun _ => ⟨⟩⟩

/-- The live-claim oracle verifier for one round of sum-check.

The verifier observes the prover's round polynomial, queries it on the domain,
checks the sum against the current target, samples a challenge, and returns the
next claim on success. -/
noncomputable def oracleVerifierStep
    {ι : Type} {oSpec : OracleSpec ι}
    {ιₛᵢ : Type} (OStmtIn : ιₛᵢ → Type)
    [∀ i, OracleInterface (OStmtIn i)]
    {ιₐ : Type} (accSpec : OracleSpec ιₐ)
    {m_dom : ℕ} (D : Fin m_dom → R) (target : RoundClaim R)
    (sampleChallenge : OracleComp oSpec R) :
    OracleCounterpart oSpec OStmtIn
      (fun {ιₐ} (_accSpec : OracleSpec ιₐ) => Option (RoundClaim R))
      (roundSpec R deg) (roundRoles R deg) (roundOracleDecoration R deg)
      accSpec :=
  let oiSpec := @OracleInterface.spec (CDegreeLE R deg) instOracleInterfaceCDegreeLE
  fun _ =>
    let receiverStep :
        OracleComp (oSpec + [OStmtIn]ₒ + (accSpec + oiSpec))
          ((_ : R) × Option (RoundClaim R)) := do
        let total ← (Finset.univ : Finset (Fin m_dom)).toList.foldlM
          (fun (acc : R) (j : Fin m_dom) => do
            let val : R ← liftM <| oiSpec.query (D j)
            pure (acc + val))
          (0 : R)
        let chal : R ← liftM sampleChallenge
        if total == target then do
          let polyAtChal : R ← liftM <| oiSpec.query chal
          let nextClaim : Option (RoundClaim R) := some polyAtChal
          pure ⟨chal, nextClaim⟩
        else
          let nextClaim : Option (RoundClaim R) := none
          pure ⟨chal, nextClaim⟩
    receiverStep

/-- The chained oracle verifier for one round of sum-check.

Once a previous round has rejected, later rounds keep the same interaction shape
but preserve the rejecting `none` state. -/
noncomputable def oracleVerifierStepOption
    {ι : Type} {oSpec : OracleSpec ι}
    {ιₛᵢ : Type} (OStmtIn : ιₛᵢ → Type)
    [∀ i, OracleInterface (OStmtIn i)]
    {ιₐ : Type} (accSpec : OracleSpec ιₐ)
    {m_dom : ℕ} (D : Fin m_dom → R) (target : Option (RoundClaim R))
    (sampleChallenge : OracleComp oSpec R) :
    OracleCounterpart oSpec OStmtIn
      (fun {ιₐ} (_accSpec : OracleSpec ιₐ) => Option (RoundClaim R))
      (roundSpec R deg) (roundRoles R deg) (roundOracleDecoration R deg)
      accSpec :=
  match target with
  | none =>
      let oiSpec := @OracleInterface.spec (CDegreeLE R deg) instOracleInterfaceCDegreeLE
      fun _ =>
        let receiverStep :
            OracleComp (oSpec + [OStmtIn]ₒ + (accSpec + oiSpec))
              ((_ : R) × Option (RoundClaim R)) := do
            let chal : R ← liftM sampleChallenge
            let nextClaim : Option (RoundClaim R) := none
            pure ⟨chal, nextClaim⟩
        receiverStep
  | some target =>
      oracleVerifierStep (R := R) (deg := deg) OStmtIn accSpec D target sampleChallenge

end

end Sumcheck

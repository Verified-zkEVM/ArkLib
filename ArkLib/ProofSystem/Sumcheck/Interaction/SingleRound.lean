/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.ProofSystem.Sumcheck.Interaction.Oracle
import ArkLib.Interaction.Oracle.Execution
import ArkLib.Interaction.Choreo

open Interaction.TwoParty

/-!
# Sum-Check Single Round

This module defines the single-round sum-check oracle reduction on
`Interaction.Oracle.Spec`.
-/

namespace Sumcheck

open Interaction CompPoly CPoly OracleComp OracleSpec

section

variable {R : Type} [BEq R] [CommSemiring R] [LawfulBEq R] [Nontrivial R] {deg : ℕ}

/-- Advance a residual polynomial by fixing its first variable to the sampled
challenge. This is the stateful prover update for one sum-check round. -/
def stepResidual (chal : R)
    {numVars : ℕ} (poly : Sumcheck.PolyStmt R deg (numVars + 1)) :
    Sumcheck.PolyStmt R deg numVars :=
  ⟨CMvPolynomial.partialEvalFirst chal poly.1,
    CMvPolynomial.partialEvalFirst_individualDegreeLE chal poly.1 poly.2⟩

/-- The honest round polynomial computed from the current active residual. -/
def honestRoundPoly {m_dom : ℕ} (D : Fin m_dom → R)
    {numVars : ℕ}
    (poly : Sumcheck.PolyStmt R deg (numVars + 1)) :
    CDegreeLE R deg :=
  ⟨CMvPolynomial.roundPoly D numVars poly.1,
    CMvPolynomial.roundPoly_natDegree_le D poly.1 (fun mono hmono =>
      poly.2 ⟨0, by omega⟩ mono hmono)⟩

/-- Full one-round sum-check reduction program.

The `program` field is the executable choreography: it determines the protocol
shape and both endpoints. The same package also includes initialization,
terminal output projection, and the output-oracle `simulate` implementation,
which is reduction semantics rather than endpoint behavior. -/
noncomputable def roundProgram
    {ι : Type} {oSpec : OracleSpec.{0, 0} ι}
    {m_dom : ℕ} (D : Fin m_dom → R)
    (numVars : ℕ)
    (sampleChallenge : OracleComp oSpec R) :
    Interaction.Choreo.OracleScoped.ReductionProgram oSpec
      (RoundClaim R)
      (fun _ => PUnit)
      (fun _ => Sumcheck.PolyFamily R deg (numVars + 1))
      (fun _ => PUnit) :=
  oracle_reduction_begin
    prover_state _shared => Sumcheck.PolyStmt R deg (numVars + 1) ;;
    verifier_state _shared => RoundClaim R ;;
    prover_result _shared =>
      Sumcheck.PolyStmt R deg (numVars + 1) × CDegreeLE R deg × R ;;
    verifier_result _shared => Option (RoundClaim R) ;;
    prover_init _shared sWithOracles _witness => sWithOracles.oracleStmt () ;;
    verifier_init shared _stmt => shared ;;
    prover_oracle[CDegreeLE R deg] sentPoly from poly =>
      let sentPoly := honestRoundPoly (R := R) (deg := deg) D poly
      send sentPoly keeping (poly, sentPoly)
    ;;
    verifier_send[R] chal from target => do
      let total ← (Finset.univ : Finset (Fin m_dom)).toList.foldlM
        (fun (acc : R) (j : Fin m_dom) => do
          let val : R ← oracle_query[CDegreeLE R deg] (D j)
          pure (acc + val))
        (0 : R)
      let chal : R ← liftM sampleChallenge
      send chal keeping (target, total)
    ;;
    oracle_reduction_end
      prover ⟨poly, sentPoly⟩ => (poly, sentPoly, chal) ;;
      verifier checked => do
        if checked.2 == checked.1 then do
          let polyAtChal : R ← oracle_query[CDegreeLE R deg] chal
          pure (some polyAtChal)
        else
          pure none
    ;;
    statement_out _shared _pt => Option (RoundClaim R) ;;
    output_oracle _shared _pt =>
      index PUnit ;;
      statement Sumcheck.PolyFamily R deg (numVars + 1) ;;
      interface _i => inferInstance ;;
      simulate q =>
        liftM <| ([Sumcheck.PolyFamily R deg (numVars + 1)]ₒ).query q
    ;;
    witness_out _shared _pt => PUnit ;;
    prover_output _shared _pt out =>
      let nextClaim : Option (RoundClaim R) := some (CPolynomial.eval out.2.2 out.2.1.1)
      ⟨⟨nextClaim, fun _ => out.1⟩, PUnit.unit⟩ ;;
    verifier_output _shared _pt result => result

/-- One-round sum-check oracle reduction.

The input oracle statement is the degree-bounded polynomial being checked. The
prover has no separate polynomial witness; its current residual is read from the
oracle statement and updated internally across the round. Both endpoint
strategies, protocol shape, and output-oracle simulation are projected from
`roundProgram`. -/
noncomputable def roundReduction
    {ι : Type} {oSpec : OracleSpec.{0, 0} ι}
    {m_dom : ℕ} (D : Fin m_dom → R)
    (numVars : ℕ)
    (sampleChallenge : OracleComp oSpec R) :
    Interaction.Oracle.Reduction oSpec
      (RoundClaim R)
      (fun _ => roundSpec R deg)
      (fun _ => roundRoles R deg)
      (fun _ => roundOracleDeco R deg)
      (fun _ => PUnit)
      (fun _ => Sumcheck.PolyFamily R deg (numVars + 1))
      (fun _ => PUnit)
      (fun _ _ => Option (RoundClaim R))
      (fun _ _ => Sumcheck.PolyFamily R deg (numVars + 1))
      (fun _ _ => PUnit) :=
  (roundProgram (R := R) (deg := deg) (oSpec := oSpec)
    D numVars sampleChallenge).toReduction

/-- The executable single-round reduction program generates the ordinary
one-round oracle protocol shape. -/
theorem roundProgram_protocol
    {ι : Type} {oSpec : OracleSpec.{0, 0} ι}
    {m_dom : ℕ} (D : Fin m_dom → R)
    (numVars : ℕ)
    (sampleChallenge : OracleComp oSpec R)
    (target : RoundClaim R) :
    (roundProgram (R := R) (deg := deg) D numVars sampleChallenge).protocol target =
      roundProtocol R deg :=
  rfl

end

end Sumcheck

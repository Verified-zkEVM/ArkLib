/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ProofSystem.Sumcheck.Interaction.General

/-!
# Interaction-Native Sum-Check Examples

This module records the end-to-end interaction-native Sumcheck surface. The
examples deliberately use the public reductions from `General`: the oracle
statement is the original polynomial family throughout the protocol, while the
stateful variant threads the prover's private residual polynomial as witness
state.
-/

namespace Sumcheck

open Interaction Interaction.OracleDecoration CompPoly CPoly OracleComp OracleSpec

section

variable {R : Type} [BEq R] [CommSemiring R] [LawfulBEq R] [Nontrivial R]
variable (deg n : Nat)
variable {ι : Type} {oSpec : OracleSpec ι}
variable {m_dom : Nat} (D : Fin m_dom → R)
variable (sampleChallenge : OracleComp oSpec R)

/-- The public end-to-end interaction-native Sumcheck reduction. -/
noncomputable example :
    OracleReduction oSpec
      (RoundClaim R)
      (fun _ => Sumcheck.fullSpec R deg n)
      (fun _ => Sumcheck.fullRoles R deg n)
      (fun _ => Sumcheck.fullOD (R := R) (deg := deg) n)
      (fun _ => PUnit)
      (fun _ => Sumcheck.PolyFamily R deg n)
      (fun _ => PUnit)
      (fun _ _ => Option (RoundClaim R))
      (fun _ _ => Sumcheck.PolyFamily R deg n)
      (fun _ _ => PUnit) :=
  Sumcheck.sumcheckReduction (R := R) (deg := deg) n D sampleChallenge

/-- The same public protocol with the prover's residual polynomial threaded
privately as witness state. -/
noncomputable example :
    OracleReduction oSpec
      (RoundClaim R)
      (fun _ => Sumcheck.fullSpec R deg n)
      (fun _ => Sumcheck.fullRoles R deg n)
      (fun _ => Sumcheck.fullOD (R := R) (deg := deg) n)
      (fun _ => PUnit)
      (fun _ => Sumcheck.PolyFamily R deg n)
      (fun _ => Sumcheck.PolyStmt R deg n)
      (fun _ _ => Option (RoundClaim R))
      (fun _ _ => Sumcheck.PolyFamily R deg n)
      (fun _ _ => Sumcheck.PolyStmt R deg 0) :=
  Sumcheck.sumcheckReductionStateful (R := R) (deg := deg) n D sampleChallenge

end

end Sumcheck

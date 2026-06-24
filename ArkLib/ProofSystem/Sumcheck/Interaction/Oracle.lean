/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.ProofSystem.Sumcheck.Interaction.Defs
import ArkLib.Interaction.Oracle.Core
import ArkLib.Interaction.Oracle.Protocol

open Interaction.TwoParty

/-!
# Sum-Check Oracle Round Primitives

This module defines the one-round sum-check oracle surface on the
`Interaction.Oracle.Spec` API.

The round polynomial is an `.oracle` node, so the verifier's
`PublicTranscript` records only the oracle-round marker, not the polynomial
message itself. The polynomial is accessed through `Oracle.Spec.QueryHandle`.
The verifier's challenge is a `.public` receiver node.
-/

namespace Sumcheck

open Interaction CompPoly CPoly OracleComp OracleSpec

section

variable (R : Type) [BEq R] [CommSemiring R] [LawfulBEq R]
variable (deg : ℕ)

/-- Decorated oracle protocol for one round: the prover provides the round
polynomial as an oracle message, then the verifier samples a public challenge. -/
def roundProtocol : Interaction.Oracle.Spec.Protocol :=
  Interaction.Oracle.Spec.Protocol.oracle (CDegreeLE R deg)
    (Interaction.Oracle.Spec.Protocol.public .receiver R fun _ =>
      Interaction.Oracle.Spec.Protocol.done)

/-- Oracle-spec shape for one sum-check oracle round. -/
abbrev roundSpec : Interaction.Oracle.Spec :=
  (roundProtocol R deg).spec

/-- Role decoration for one sum-check round. The oracle polynomial node is
implicitly prover-owned; the only public node is the verifier challenge. -/
abbrev roundRoles : Interaction.Oracle.Spec.RoleDeco (roundSpec R deg) :=
  (roundProtocol R deg).roles

/-- Oracle decoration for one round: the prover's univariate round polynomial is
queryable via its evaluation oracle interface. -/
abbrev roundOracleDeco : Interaction.Oracle.Spec.OracleDeco (roundSpec R deg) :=
  (roundProtocol R deg).oracleDeco

/-- Forgetting oracle handles recovers the plain interaction projection. -/
@[simp]
theorem roundSpec_toInteractionSpec :
    (roundSpec R deg).toInteractionSpec = underlyingRoundSpec R deg :=
  rfl

/-- Forgetting oracle handles recovers the plain role projection. -/
@[simp]
theorem roundRoles_toSpecRoles :
    (roundSpec R deg).toSpecRoles (roundRoles R deg) = underlyingRoundRoles R deg :=
  rfl

/-- Public transcript of an oracle round. It contains the oracle-round marker
and the verifier challenge, but not the prover's oracle polynomial message. -/
abbrev RoundPublicTranscript :=
  Interaction.Oracle.Spec.PublicTranscript (roundSpec R deg)

/-- Extract the verifier challenge from an oracle round public transcript. -/
abbrev roundChallenge (pt : RoundPublicTranscript R deg) : R :=
  pt.2.1

end

end Sumcheck

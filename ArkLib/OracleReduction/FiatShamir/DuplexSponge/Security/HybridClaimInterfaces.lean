/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen
-/
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.Statement.ConcreteHybrids

/-!
# Paper-critical Section 5 hybrid-claim interfaces

This file is deliberately the boundary between the top-down proof of Lemma 5.1 and the four
lower-layer hybrid arguments.  Each declaration has exactly the corresponding revised-paper
statement over the concrete games.  The temporary proofs below are explicit proof obligations,
not hypotheses added to Lemma 5.1 and not replacements for the executable hybrid construction.

The intended proof dependency order is:

1. Lemma 5.25 and the lazy first-stop coupling prove Claim 5.21;
2. the Core-only image-fibre coupling proves Claim 5.22, without decoder surjectivity;
3. the adaptive partial-codec coupling proves Claim 5.23; and
4. Claim 5.23 plus the private-shadow and stopped-extension arguments prove Claim 5.24.

Keeping those obligations here makes `KeyLemma.lean` a genuinely top-down arithmetic endpoint
while preserving the exact mathematical work still required below it.
-/

noncomputable section

open OracleComp OracleSpec ProtocolSpec

namespace DuplexSpongeFS.KeyLemma

open DuplexSpongeFS.DSTraceStorage

variable {n : ℕ} {pSpec : ProtocolSpec n} {ι : Type} {oSpec : OracleSpec ι}
  {StmtIn StmtOut : Type}
  [VCVCompatible StmtIn] [∀ i, VCVCompatible (pSpec.Challenge i)]
  {U : Type} [SpongeUnit U] [SpongeSize] [VCVCompatible U]
  [∀ i, VCVCompatible (pSpec.Message i)] [codec : CodecCore pSpec U]
  [Section5Nonempty pSpec]
  {δ : Nat} {Salt : Type} [VCVCompatible Salt] [SaltCodec U δ Salt]
  [DecidableEq StmtIn] [DecidableEq U]
  {T_H T_P : Type} [LawfulTraceNablaImpl T_H T_P StmtIn U]

/-- **Claim 5.21.** The ideal-permutation and direct-D2SQuery experiments have distance at most
the stateful first-stop bound.  Its pending proof constructs the actual H₀/H₁ joint execution,
using Lemma 5.25 to identify the stateful replay and Lemma 5.8 to charge its first stop. -/
theorem claim_5_21
    [DecidableEq ι]
    (oSpecImpl : QueryImpl oSpec ProbComp)
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (maliciousProver : MaliciousProver oSpec pSpec StmtIn U δ)
    (tₕ tₚ tₚᵢ : ℕ) :
    Statement.Claim521 (StmtIn := StmtIn) (StmtOut := StmtOut) (oSpec := oSpec)
      (pSpec := pSpec) (U := U) (δ := δ) (Salt := Salt) (T_H := T_H) (T_P := T_P)
      oSpecImpl V maliciousProver tₕ tₚ tₚᵢ := by
  sorry

/-- **Claim 5.22.** The H₁/H₂ image-fibre reparameterization is exact.  The pending proof is the
adaptive, insertion-log-preserving Core-only coupling based on equation (46a); it never assumes
that a challenge decoder is surjective. -/
theorem claim_5_22
    (oSpecImpl : QueryImpl oSpec ProbComp)
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (maliciousProver : MaliciousProver oSpec pSpec StmtIn U δ) :
    Statement.Claim522 (StmtIn := StmtIn) (StmtOut := StmtOut) (oSpec := oSpec)
      (pSpec := pSpec) (U := U) (δ := δ) (Salt := Salt) (T_H := T_H) (T_P := T_P)
      oSpecImpl V maliciousProver := by
  sorry

/-- **Claim 5.23.** The adaptive partial-codec coupling of H₂, H₃, and the H₄ table exists under
the source forward-query budget.  Its pending proof exposes only image fibres and charges every
out-of-image attempt to its explicit codec-bad event. -/
theorem claim_5_23
    [DecidableEq ι]
    (oSpecImpl : QueryImpl oSpec ProbComp)
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (maliciousProver : MaliciousProver oSpec pSpec StmtIn U δ)
    (tₚ : ℕ) :
    Statement.Claim523 (StmtIn := StmtIn) (StmtOut := StmtOut) (oSpec := oSpec)
      (pSpec := pSpec) (U := U) (δ := δ) (Salt := Salt) (T_H := T_H) (T_P := T_P)
      oSpecImpl V maliciousProver tₚ := by
  sorry

/-- **Claim 5.24.** The H₂/H₄ comparison pays the codec term from Claim 5.23 exactly once and
the stateful stopped-permutation envelope `D(T,N_𝒱)`.  The pending proof combines the private
shadow with conditional averaging of Lemma 5.8b over codec-conditioned histories. -/
theorem claim_5_24
    [DecidableEq ι]
    (oSpecImpl : QueryImpl oSpec ProbComp)
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (maliciousProver : MaliciousProver oSpec pSpec StmtIn U δ)
    (tₕ tₚ tₚᵢ : ℕ) :
    Statement.Claim524 (StmtIn := StmtIn) (StmtOut := StmtOut) (oSpec := oSpec)
      (pSpec := pSpec) (U := U) (δ := δ) (Salt := Salt) (T_H := T_H) (T_P := T_P)
      oSpecImpl V maliciousProver tₕ tₚ tₚᵢ := by
  sorry

end DuplexSpongeFS.KeyLemma

/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen
-/

import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.Statement.ConcreteHybrids
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.DecodedFibreCoupling
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.Hyb2ImageFibreKernel
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.Hyb2LogCoupling

/-!
# Claim 5.22: Core-only image-fibre coupling

This is the direct proof route for revised Claim 5.22.  It deliberately contains no total
decoder assumption.  The single temporary gap below is the operational refinement from the
live `d2sDecodedBridgeImplCacheOfImage` runner to the image-fibre cache while retaining its
observed line-4 log.  It is the only remaining premise needed to construct the concrete joint
execution in `Statement.Hyb12ImageFibreCoupling`.

The paper proof decomposes as follows:

1. `sampleImageFibreTablePair` jointly samples an encoded table, its decoded image table, and
   a uniform representative in each image fibre.
2. `evalDist_sampleImageFibreTablePair_representative_bind_eq_uniform` proves equation (46a):
   the representative table has the H₁ uniform encoded-table marginal.
3. `evalDist_decodedFibreLazyImpl_eq_eager` proves the adaptive first-query/repeated-key cache
   law for the decoded image table.
4. `Hyb2LogCoupling` transports the decoded occurrences, their order, and their multiplicity to
   the H₂ line-4 observation.  The residual hit/miss laws in `ProverTransform` identify the
   live partial bridge with this cache on the image branch.

Thus no out-of-image value is ever lifted in Claim 5.22; it cannot silently require decoder
surjectivity.  The out-of-image branch belongs to the later Claim 5.23 codec coupling.
-/

noncomputable section

namespace DuplexSpongeFS.KeyLemma

open OracleComp OracleSpec ProtocolSpec
open DuplexSpongeFS.TraceTransform
open DuplexSpongeFS.DSTraceStorage

variable {n : ℕ} {pSpec : ProtocolSpec n} {ι : Type} {oSpec : OracleSpec ι}
  {StmtIn StmtOut : Type}
  [VCVCompatible StmtIn] [∀ i, VCVCompatible (pSpec.Challenge i)]
  {U : Type} [SpongeUnit U] [SpongeSize] [VCVCompatible U]
  [∀ i, VCVCompatible (pSpec.Message i)] [codec : CodecCore pSpec U]
  {δ : Nat} {Salt : Type} [VCVCompatible Salt] [SaltCodec U δ Salt]
  [DecidableEq StmtIn] [DecidableEq U]
  {T_H T_P : Type} [LawfulTraceNablaImpl T_H T_P StmtIn U]

/-- **Temporary operational endpoint gap.**  This is not a strengthened public assumption:
the theorem is stated under precisely `CodecCore` and its required construction is fixed by the
four-step image-fibre argument documented above.  It will be replaced by that construction
before `KeyLemma.lemma_5_1_inner` can be accepted as complete. -/
theorem hyb12_imageFibreCoupling
    (oSpecImpl : QueryImpl oSpec ProbComp)
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (maliciousProver : MaliciousProver oSpec pSpec StmtIn U δ) :
    Statement.Hyb12ImageFibreCoupling (StmtIn := StmtIn) (StmtOut := StmtOut) (oSpec := oSpec)
      (pSpec := pSpec) (U := U) (δ := δ) (Salt := Salt) (T_H := T_H) (T_P := T_P)
      oSpecImpl V maliciousProver := by
  sorry

/-- Revised Claim 5.22 on the actual H₁ and H₂ experiments.  Its only unfinished dependency is
the explicit Core-only operational coupling above; the probability-theoretic endpoint is proved
in `Statement.claim522_of_hyb12ImageFibreCoupling`. -/
theorem claim522_imageFibre
    [Section5Nonempty pSpec]
    (oSpecImpl : QueryImpl oSpec ProbComp)
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (maliciousProver : MaliciousProver oSpec pSpec StmtIn U δ) :
    Statement.Claim522 (StmtIn := StmtIn) (StmtOut := StmtOut) (oSpec := oSpec)
      (pSpec := pSpec) (U := U) (δ := δ) (Salt := Salt) (T_H := T_H) (T_P := T_P)
      oSpecImpl V maliciousProver :=
  Statement.claim522_of_hyb12ImageFibreCoupling (StmtIn := StmtIn) (StmtOut := StmtOut)
    (oSpec := oSpec) (pSpec := pSpec) (U := U) (δ := δ) (Salt := Salt) (T_H := T_H)
    (T_P := T_P) oSpecImpl V maliciousProver
    (hyb12_imageFibreCoupling (StmtIn := StmtIn) (StmtOut := StmtOut) (oSpec := oSpec)
      (pSpec := pSpec) (U := U) (δ := δ) (Salt := Salt) (T_H := T_H) (T_P := T_P)
      oSpecImpl V maliciousProver)

end DuplexSpongeFS.KeyLemma

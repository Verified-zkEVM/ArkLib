/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen
-/

import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.BadEventsProb.Paper

/-!
# Public façade for CO25 Lemma 5.8 bad-event probability bound

This module re-exports the split `BadEventsProb/*` proof stack and keeps the public theorem
`lemma_5_8` at the original import path.
-/

open OracleComp OracleSpec ProtocolSpec

open scoped ENNReal

namespace DuplexSpongeFS

namespace BadEventDS

open DuplexSpongeFS.DSTraceStorage

variable {StmtIn : Type} {n : ℕ} {pSpec : ProtocolSpec n}
  {U : Type} [SpongeUnit U] [SpongeSize]

variable (trace : QueryLog (duplexSpongeChallengeOracle StmtIn U))


variable {StmtOut : Type}
  [VCVCompatible StmtIn] [∀ i, VCVCompatible (pSpec.Challenge i)]
  [codec : Codec pSpec U] {δ : ℕ} [DecidableEq StmtIn] [DecidableEq U]
  [VCVCompatible U] [SampleableType U]
  [∀ i, Fintype (pSpec.Message i)]
  [∀ i, DecidableEq (pSpec.Message i)]
  {T_H : Type} {T_P : Type}
  [LawfulTraceNablaImpl T_H T_P StmtIn U]

variable [Fintype U] [Nonempty U]

set_option linter.unusedDecidableInType false in
/-- CO25 Lemma 5.8 — Bad-event probability bound (paper-faithful eager statement), assembled from
the proven finite-target union-bound arithmetic (`probEvent_E_le_lemma5_8Bound`) and the
per-side base-trace-length and per-index-freshness obligations above. -/
theorem lemma_5_8
    (V : Verifier []ₒ StmtIn StmtOut pSpec)
    (maliciousProver : MaliciousProver []ₒ pSpec StmtIn U δ)
    (tₕ tₚ tₚᵢ : ℕ)
    (hδR : δ ≤ SpongeSize.R)
    (hMaliciousBound : IsLemma5_8QueryBound
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) maliciousProver tₕ tₚ tₚᵢ)
    (hTp : tₚ ≥ pSpec.totalNumPermQueries) :
    max
        (Pr[ fun (tr : QueryLog (duplexSpongeChallengeOracle StmtIn U) ×
                      QueryLog (duplexSpongeChallengeOracle StmtIn U)) =>
              E (tr.1 ++ tr.2) |
          lemma5_8SpongeTraceDist
            (StmtIn := StmtIn) (StmtOut := StmtOut)
            (n := n) (pSpec := pSpec) (U := U) (δ := δ)
            (initSponge := (D_𝔖 StmtIn U).sample)
            (implSponge := (D_𝔖 StmtIn U).eagerImpl) V maliciousProver])
        (Pr[ fun (tr : QueryLog (duplexSpongeChallengeOracle StmtIn U) ×
                      QueryLog (duplexSpongeChallengeOracle StmtIn U)) =>
              E (tr.1 ++ tr.2) |
          lemma5_8SigmaTraceDist
            (T_H := T_H) (T_P := T_P) (δ := δ)
            (StmtIn := StmtIn) (StmtOut := StmtOut)
            (n := n) (pSpec := pSpec) (U := U) V maliciousProver])
      ≤ ENNReal.ofReal (lemma5_8Bound U tₕ tₚ tₚᵢ pSpec.totalNumPermQueries) := by
  refine max_le ?_ ?_
  · exact probEvent_E_le_lemma5_8Bound_all_first
      (exp := lemma5_8SpongeTraceDist (StmtIn := StmtIn) (StmtOut := StmtOut) (n := n)
        (pSpec := pSpec) (U := U) (δ := δ) (initSponge := (D_𝔖 StmtIn U).sample)
        (implSponge := (D_𝔖 StmtIn U).eagerImpl) V maliciousProver)
      (f := fun tr => tr.1 ++ tr.2)
      (tₕ := tₕ) (tₚ := tₚ) (tₚᵢ := tₚᵢ) (L := pSpec.totalNumPermQueries)
      (h_basetrace_len :=
        lemma5_8_sponge_length V maliciousProver tₕ tₚ tₚᵢ hδR hMaliciousBound hTp)
      (hh := lemma5_8_sponge_E_h_first_at V maliciousProver)
      (hp := lemma5_8_sponge_E_p_first_at V maliciousProver)
      (hpi := lemma5_8_sponge_E_pinv_first_at V maliciousProver)
      (hfunc := lemma5_8_sponge_E_func_first_at V maliciousProver)
  · exact probEvent_E_le_lemma5_8Bound_all_first
      (exp := lemma5_8SigmaTraceDist (T_H := T_H) (T_P := T_P) (δ := δ) (StmtIn := StmtIn)
        (StmtOut := StmtOut) (n := n) (pSpec := pSpec) (U := U) V maliciousProver)
      (f := fun tr => tr.1 ++ tr.2)
      (tₕ := tₕ) (tₚ := tₚ) (tₚᵢ := tₚᵢ) (L := pSpec.totalNumPermQueries)
      (h_basetrace_len :=
        lemma5_8_sigma_length V maliciousProver tₕ tₚ tₚᵢ hδR hMaliciousBound hTp)
      (hh := lemma5_8_sigma_E_h_first_at V maliciousProver)
      (hp := lemma5_8_sigma_E_p_first_at V maliciousProver)
      (hpi := lemma5_8_sigma_E_pinv_first_at V maliciousProver)
      (hfunc := lemma5_8_sigma_E_func_first_at V maliciousProver)

end BadEventDS

end DuplexSpongeFS

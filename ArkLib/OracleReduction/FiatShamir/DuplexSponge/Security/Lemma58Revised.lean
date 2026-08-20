/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen
-/

import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.D2SFirstBadRefinement
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.BadEventsProb.Core
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.BadEventsProb.Function
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.BadEventsProb.Hash
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.BadEventsProb.PermForward
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.BadEventsProb.PermInverse

/-!
# Revised Lemma 5.8 endpoints

The corrected stateful first-bad proof is deliberately exposed as independent ideal, direct-D2S,
and stopped-verifier endpoints. Their common numerical bound is the paper's Lemma 5.8 bound.
-/

namespace DuplexSpongeFS.BadEventDS

open OracleComp OracleSpec ProtocolSpec
open DuplexSpongeFS.DSTraceStorage
open scoped ENNReal

variable {n : ℕ} {pSpec : ProtocolSpec n} {StmtIn StmtOut U : Type}
  [SpongeUnit U] [SpongeSize] [VCVCompatible U] [VCVCompatible StmtIn]
  [∀ i, VCVCompatible (pSpec.Challenge i)] [codec : CodecCore pSpec U] {δ : ℕ}
  {T_H T_P : Type} [LawfulTraceNablaImpl T_H T_P StmtIn U]
  [Fintype U] [Nonempty U] [SampleableType U] [∀ i, Fintype (pSpec.Message i)]
  [∀ i, DecidableEq (pSpec.Message i)]

set_option linter.unusedDecidableInType false in
/-- Corrected Lemma 5.8a on the ideal-permutation experiment, with the exact stateful verifier
count `N_𝒱 = verifierPermCallCount pSpec δ`.  This is deliberately independent of the obsolete
Σ-simulator compatibility theorem. -/
theorem lemma_5_8_revised_ideal_exact
    (V : Verifier []ₒ StmtIn StmtOut pSpec)
    (maliciousProver : MaliciousProver []ₒ pSpec StmtIn U δ)
    (tₕ tₚ tₚᵢ : ℕ)
    (hBound : IsLemma5_8QueryBound maliciousProver tₕ tₚ tₚᵢ) :
    Pr[ fun (tr : QueryLog (duplexSpongeChallengeOracle StmtIn U) ×
                  QueryLog (duplexSpongeChallengeOracle StmtIn U)) =>
          E (tr.1 ++ tr.2) |
      lemma5_8SpongeTraceDist
        (StmtIn := StmtIn) (StmtOut := StmtOut) (n := n) (pSpec := pSpec) (U := U) (δ := δ)
        (initSponge := (D_𝔖 StmtIn U).sample)
        (implSponge := (D_𝔖 StmtIn U).eagerImpl) V maliciousProver]
      ≤ ENNReal.ofReal (lemma5_8Bound U tₕ tₚ tₚᵢ
        (verifierPermCallCount (pSpec := pSpec) (δ := δ))) := by
  exact probEvent_E_le_lemma5_8Bound_all_first
    (exp := lemma5_8SpongeTraceDist (StmtIn := StmtIn) (StmtOut := StmtOut) (n := n)
      (pSpec := pSpec) (U := U) (δ := δ) (initSponge := (D_𝔖 StmtIn U).sample)
      (implSponge := (D_𝔖 StmtIn U).eagerImpl) V maliciousProver)
    (f := fun tr => tr.1 ++ tr.2)
    (tₕ := tₕ) (tₚ := tₚ) (tₚᵢ := tₚᵢ)
    (L := verifierPermCallCount (pSpec := pSpec) (δ := δ))
    (h_basetrace_len := lemma5_8_sponge_length_exact V maliciousProver tₕ tₚ tₚᵢ hBound)
    (hh := lemma5_8_sponge_E_h_first_at V maliciousProver)
    (hp := lemma5_8_sponge_E_p_first_at V maliciousProver)
    (hpi := lemma5_8_sponge_E_pinv_first_at V maliciousProver)
    (hfunc := lemma5_8_sponge_E_func_first_at V maliciousProver)

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
/-- The ideal-permutation half of Lemma 5.8a in the paper's exact stateful notation
`B(T + 1 + N_𝒱)`, where `T = tₕ + tₚ + tₚᵢ`. -/
theorem lemma_5_8_revised_ideal_badEventBound_exact
    (V : Verifier []ₒ StmtIn StmtOut pSpec)
    (maliciousProver : MaliciousProver []ₒ pSpec StmtIn U δ)
    (tₕ tₚ tₚᵢ : ℕ)
    (hBound : IsLemma5_8QueryBound maliciousProver tₕ tₚ tₚᵢ) :
    Pr[ fun (tr : QueryLog (duplexSpongeChallengeOracle StmtIn U) ×
                  QueryLog (duplexSpongeChallengeOracle StmtIn U)) =>
          E (tr.1 ++ tr.2) |
      lemma5_8SpongeTraceDist
        (StmtIn := StmtIn) (StmtOut := StmtOut) (n := n) (pSpec := pSpec) (U := U) (δ := δ)
        (initSponge := (D_𝔖 StmtIn U).sample)
        (implSponge := (D_𝔖 StmtIn U).eagerImpl) V maliciousProver] ≤
      ENNReal.ofReal (Statement.badEventBound U
        (tₕ + tₚ + tₚᵢ + verifierPermCallCount (pSpec := pSpec) (δ := δ) + 1)) := by
  calc
    _ ≤ ENNReal.ofReal (lemma5_8Bound U tₕ tₚ tₚᵢ
        (verifierPermCallCount (pSpec := pSpec) (δ := δ))) :=
      lemma_5_8_revised_ideal_exact V maliciousProver tₕ tₚ tₚᵢ hBound
    _ = _ := by
      rw [Statement.legacyLemma58Bound_eq_badEventBound]
      congr 2
      omega

end DuplexSpongeFS.BadEventDS

namespace DuplexSpongeFS.KeyLemma

alias lemma_5_8_revised_monitorStop_exact :=
  hyb1FullSampledOuterGame_monitorStop_le_badEventBound

/-- Corrected Lemma 5.8a on the sampled revised-D2SQuery experiment, written directly as the
paper event on the completed terminal trace. -/
alias lemma_5_8_revised_terminalBad_exact :=
  hyb1FullSampledOuterGame_terminalBad_le_badEventBound

/-- Corrected Lemma 5.8b: the stopped stateful verifier extension after an adaptive prover
prefix.  This is the paper's sharper `D(T, N_𝒱)` first-event conclusion.  The required
`Section5Nonempty` instance is the explicit no-empty-action normal form. -/
alias lemma_5_8_revised_stopped_extension_exact :=
  hyb1LiveDirect_monitorStop_after_adaptiveProver_le_Dcap

/-- The global Lemma-5.8 `B(T + 1 + N_𝒱)` consequence of the stopped extension.  It is kept
separate from `lemma_5_8_revised_stopped_extension_exact`, since the latter must retain the
strictly sharper `D` conclusion used by the paper's verifier coupling. -/
alias lemma_5_8_revised_stopped_extension_le_badEventBound :=
  hyb1LiveDirect_monitorStop_after_adaptiveProver_le_badEventBound

end DuplexSpongeFS.KeyLemma

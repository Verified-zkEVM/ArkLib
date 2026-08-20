/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen
-/

import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.BadEventsProb.Infrastructure

/-!
# Functional-conflict bounds for Lemma 5.8
-/

open OracleComp OracleSpec ProtocolSpec

set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.unusedSectionVars false

open scoped ENNReal

namespace DuplexSpongeFS

namespace BadEventDS

open DuplexSpongeFS.DSTraceStorage

variable {StmtIn : Type} {n : ℕ} {pSpec : ProtocolSpec n}
  {U : Type} [SpongeUnit U] [SpongeSize]

variable (trace : QueryLog (duplexSpongeChallengeOracle StmtIn U))


variable {StmtOut : Type}
  [VCVCompatible StmtIn] [∀ i, VCVCompatible (pSpec.Challenge i)]
  [codec : CodecCore pSpec U] {δ : ℕ} [DecidableEq StmtIn] [DecidableEq U]
  [VCVCompatible U] [SampleableType U]
  [∀ i, Fintype (pSpec.Message i)]
  [∀ i, DecidableEq (pSpec.Message i)]
  {T_H : Type} {T_P : Type}
  [LawfulTraceNablaImpl T_H T_P StmtIn U]


section PerIndexCollisionBounds

variable [Fintype U] [Nonempty U]

/-! #### Function-violation (E_func) reduction


`E_func_at·j` fires when the permutation entry at `j` conflicts with an *earlier* entry `j' < j`
sharing a domain/pre-image but disagreeing on the value.  This is covered by the `≤ j` pairwise
function conflicts, giving the `j/|Σ|^c` count.  (On the sponge side `E_func` is impossible —
`lemma5_8_sponge_E_func_at` — because `p` is a genuine bijection.) -/
section FunctionViolationReduction

/-- The function-conflict of base positions `j` and `j'`: `j` is a permutation entry, and `j'`
shares its normalized permutation input but disagrees on the mapped value. -/
def funcConflictAt (bt : QueryLog (duplexSpongeChallengeOracle StmtIn U)) (j j' : ℕ) : Prop :=
  ∃ stateIn stateOut : CanonicalSpongeState U,
    (bt[j]? = some ⟨.inr (.inl stateIn), stateOut⟩ ∧
      ((∃ sO1, bt[j']? = some ⟨.inr (.inl stateIn), sO1⟩ ∧ sO1 ≠ stateOut) ∨
       (∃ sO2, bt[j']? = some ⟨.inr (.inr sO2), stateIn⟩ ∧ sO2 ≠ stateOut))) ∨
    (bt[j]? = some ⟨.inr (.inr stateOut), stateIn⟩ ∧
      ((∃ sI1, bt[j']? = some ⟨.inr (.inr stateOut), sI1⟩ ∧ sI1 ≠ stateIn) ∨
       (∃ sI2, bt[j']? = some ⟨.inr (.inl sI2), stateOut⟩ ∧ sI2 ≠ stateIn)))

/-- Sponge `E_func` bound: `Pr[E_func_at · j] ≤ j/|Σ|^c` — in fact `= 0` (`p` genuine function). -/
lemma lemma5_8_sponge_E_func_at
    (V : Verifier []ₒ StmtIn StmtOut pSpec)
    (maliciousProver : MaliciousProver []ₒ pSpec StmtIn U δ) (j : ℕ) :
    Pr[ fun tr => E_func_at (tr.1 ++ tr.2) j |
        lemma5_8SpongeTraceDist (StmtIn := StmtIn) (StmtOut := StmtOut) (n := n) (pSpec := pSpec)
          (U := U) (δ := δ) (initSponge := (D_𝔖 StmtIn U).sample)
          (implSponge := (D_𝔖 StmtIn U).eagerImpl) V maliciousProver]
      ≤ (j : ℝ≥0∞) / capacitySpaceSize (U := U) := by
  -- The sponge permutation is a genuine function ⇒ `E_func` never fires ⇒ the probability is `0`.
  refine le_trans (le_of_eq (probEvent_eq_zero ?_)) (zero_le')
  intro tr htr
  -- Destructure the experiment support and read off the sampled realization `s₀`.
  rw [lemma5_8SpongeTraceDist, lemma5_8ProjectedTraceDistAbortable, mem_support_bind_iff] at htr
  obtain ⟨s₀, _, htr⟩ := htr
  rw [mem_support_bind_iff] at htr
  obtain ⟨proverResult, hpr, htr⟩ := htr
  have hProver := spongeConsistent_of_mem_support (s₀, []) hpr
  obtain ⟨res, s₁, trP⟩ := proverResult
  have hProverCons : ∀ e ∈ trP, wideSpongeConsistent s₀ e := fun e he =>
    (hProver.2 e he).resolve_left (by simp)
  have htrP := projectTraceLog_spongeConsistent s₀ trP hProverCons
  rcases res with _ | ⟨stmtIn, proof⟩
  · -- Abort: `tr = (project trP, [])`.
    rw [mem_support_pure_iff] at htr
    subst htr
    refine E_func_at_false_of_consistent s₀ _ (fun e he => ?_) j
    have he2 := (getBaseTrace_sublist _).subset he
    rw [List.append_nil] at he2
    exact htrP e he2
  · -- Success: the verifier runs on the same carrier `s₁ = s₀`.
    rw [mem_support_bind_iff] at htr
    obtain ⟨verifierResult, hvr, htr⟩ := htr
    rw [mem_support_pure_iff] at htr
    subst htr
    have hs : s₁ = s₀ := hProver.1
    subst s₁
    have hVerifCons : ∀ e ∈ verifierResult.2.2, wideSpongeConsistent s₀ e := fun e he =>
      (spongeConsistent_of_mem_support (s₀, []) hvr |>.2 e he).resolve_left (by simp)
    have htrV := projectTraceLog_spongeConsistent s₀ verifierResult.2.2 hVerifCons
    refine E_func_at_false_of_consistent s₀ _ (fun e he => ?_) j
    rcases List.mem_append.mp ((getBaseTrace_sublist _).subset he) with h | h
    · exact htrP e h
    · exact htrV e h

/-- Sponge `E_func` bound, refined to the earliest bad index. -/
lemma lemma5_8_sponge_E_func_first_at
    (V : Verifier []ₒ StmtIn StmtOut pSpec)
    (maliciousProver : MaliciousProver []ₒ pSpec StmtIn U δ) (j : ℕ) :
    Pr[ fun tr => E_first_at (tr.1 ++ tr.2) j ∧ E_func_at (tr.1 ++ tr.2) j |
        lemma5_8SpongeTraceDist (StmtIn := StmtIn) (StmtOut := StmtOut) (n := n)
          (pSpec := pSpec) (U := U) (δ := δ) (initSponge := (D_𝔖 StmtIn U).sample)
          (implSponge := (D_𝔖 StmtIn U).eagerImpl) V maliciousProver]
      ≤ (j : ℝ≥0∞) / capacitySpaceSize (U := U) :=
  le_trans
    (probEvent_and_left_le _ _ _)
    (lemma5_8_sponge_E_func_at (StmtIn := StmtIn) (StmtOut := StmtOut) (n := n)
      (pSpec := pSpec) (U := U) (δ := δ) V maliciousProver j)

end FunctionViolationReduction

end PerIndexCollisionBounds

end BadEventDS

end DuplexSpongeFS

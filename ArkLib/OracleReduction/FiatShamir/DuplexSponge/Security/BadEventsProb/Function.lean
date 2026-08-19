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
  [codec : Codec pSpec U] {δ : ℕ} [DecidableEq StmtIn] [DecidableEq U]
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

/-- A pairwise functionality witness only reads positions `j' < j` and `j`; it is consequently
invariant under any common prefix through `j`. -/
lemma funcConflictAt_iff_of_take_eq
    {bt₁ bt₂ : QueryLog (duplexSpongeChallengeOracle StmtIn U)}
    {j j' : ℕ} (hprefix : bt₁.take (j + 1) = bt₂.take (j + 1))
    (hj' : j' < j) :
    funcConflictAt bt₁ j j' ↔ funcConflictAt bt₂ j j' := by
  unfold funcConflictAt
  have hj : j < j + 1 := Nat.lt_succ_self j
  have hj'lt : j' < j + 1 := Nat.lt_trans hj' hj
  rw [getElem?_eq_of_take_eq hprefix hj, getElem?_eq_of_take_eq hprefix hj'lt]

/-- The first-bad pairwise functionality event is prefix-local once entry `j` exists. -/
lemma E_first_at_and_funcConflictAt_iff_of_getBaseTrace_append_eq
    {trace trace' : QueryLog (duplexSpongeChallengeOracle StmtIn U)}
    {extra : QueryLog (duplexSpongeChallengeOracle StmtIn U)} {j j' : ℕ}
    (hbt : getBaseTrace trace' = getBaseTrace trace ++ extra)
    (hj : j < (getBaseTrace trace).length)
    (hj' : j' < j) :
    (E_first_at trace' j ∧ funcConflictAt (getBaseTrace trace') j j') ↔
      (E_first_at trace j ∧ funcConflictAt (getBaseTrace trace) j j') := by
  have hfirst := E_first_at_iff_of_getBaseTrace_append_eq hbt hj
  have htake :
      (getBaseTrace trace').take (j + 1) = (getBaseTrace trace).take (j + 1) := by
    rw [hbt, List.take_append_of_le_length (Nat.succ_le_iff.mpr hj)]
  exact and_congr hfirst (funcConflictAt_iff_of_take_eq htake hj')

/-- **Reduction (E_func).** `E_func_at·j` is covered by one of the `≤ j` pairwise function conflicts. -/
lemma E_func_at_imp_funcConflict
    (trace : QueryLog (duplexSpongeChallengeOracle StmtIn U)) (j : ℕ) (h : E_func_at trace j) :
    ∃ j' ∈ Finset.range j, funcConflictAt (getBaseTrace trace) j j' := by
  classical
  obtain ⟨hj, sIn, sOut, hbody⟩ := h
  rcases hbody with ⟨hbtj, j', hlt, hconf⟩ | ⟨hbtj, j', hlt, hconf⟩
  · refine ⟨(j' : ℕ), Finset.mem_range.mpr (Fin.lt_def.mp hlt), sIn, sOut, Or.inl ⟨?_, ?_⟩⟩
    · rw [List.getElem?_eq_getElem hj]; exact congrArg some hbtj
    · rcases hconf with ⟨sO1, he, hne⟩ | ⟨sO2, he, hne⟩
      · exact Or.inl ⟨sO1, by rw [List.getElem?_eq_getElem j'.2]; exact congrArg some he, hne⟩
      · exact Or.inr ⟨sO2, by rw [List.getElem?_eq_getElem j'.2]; exact congrArg some he, hne⟩
  · refine ⟨(j' : ℕ), Finset.mem_range.mpr (Fin.lt_def.mp hlt), sIn, sOut, Or.inr ⟨?_, ?_⟩⟩
    · rw [List.getElem?_eq_getElem hj]; exact congrArg some hbtj
    · rcases hconf with ⟨sI1, he, hne⟩ | ⟨sI2, he, hne⟩
      · exact Or.inl ⟨sI1, by rw [List.getElem?_eq_getElem j'.2]; exact congrArg some he, hne⟩
      · exact Or.inr ⟨sI2, by rw [List.getElem?_eq_getElem j'.2]; exact congrArg some he, hne⟩

/-- **Foundational sigma pairwise forward-functional collision bound.**
At a first bad index, each fixed earlier position can explain a forward functional conflict with
probability at most one fresh capacity guess.

This is the sigma analogue of the hash/permutation Fresh contracts, specialized to the
function-violation branch.  It packages the lazy `Cache_p`/`tr_∇` state analysis and the
single fresh capacity sample that remains after conditioning on the no-prior-bad prefix. -/
lemma sigma_funcConflictAt_core_gap
    (V : Verifier []ₒ StmtIn StmtOut pSpec)
    (maliciousProver : MaliciousProver []ₒ pSpec StmtIn U δ)
    (j j' : ℕ) (hj' : j' < j) :
    Pr[ fun tr => E_first_at (tr.1 ++ tr.2) j ∧
        funcConflictAt (getBaseTrace (tr.1 ++ tr.2)) j j' |
        lemma5_8SigmaTraceDist (T_H := T_H) (T_P := T_P) (δ := δ) (StmtIn := StmtIn)
          (StmtOut := StmtOut) (n := n) (pSpec := pSpec) (U := U) V maliciousProver]
      ≤ 1 / capacitySpaceSize (U := U) := by
  sorry

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


/-- **Sigma backward-functional first-witness exclusion.** Under the conditional prefix invariant
of Lemma C, the simulator's inverse lookup either returns the recorded preimage or a prior output
collision has already raised `E_dup`; hence a backward `E_func` cannot be the earliest bad witness.
The proof bridges the final D2SQuery state mirror to the ordered base trace. -/
lemma sigma_first_func_bwd_zero_core_gap
    (V : Verifier []ₒ StmtIn StmtOut pSpec)
    (maliciousProver : MaliciousProver []ₒ pSpec StmtIn U δ)
    (j : ℕ) :
    Pr[ fun tr => E_first_at (tr.1 ++ tr.2) j ∧ E_func_bwd_at (tr.1 ++ tr.2) j |
        lemma5_8SigmaTraceDist (T_H := T_H) (T_P := T_P) (δ := δ) (StmtIn := StmtIn)
          (StmtOut := StmtOut) (n := n) (pSpec := pSpec) (U := U) V maliciousProver]
      = 0 := by
  refine probEvent_eq_zero ?_
  intro tr htr hbad
  rcases hbad with ⟨hFirst, hBwd⟩
  obtain ⟨j', hj'lt, hPrior⟩ :=
    sigma_support_bwdHasPriorBad
      (T_H := T_H) (T_P := T_P) (StmtIn := StmtIn) (StmtOut := StmtOut)
      (n := n) (pSpec := pSpec) (U := U) (δ := δ) V maliciousProver htr j hBwd
  exact hFirst.2 j' hj'lt hPrior

lemma sigma_first_func_fwd_bound_core_gap
    (V : Verifier []ₒ StmtIn StmtOut pSpec)
    (maliciousProver : MaliciousProver []ₒ pSpec StmtIn U δ)
    (j : ℕ) :
    Pr[ fun tr => E_first_at (tr.1 ++ tr.2) j ∧ E_func_fwd_at (tr.1 ++ tr.2) j |
        lemma5_8SigmaTraceDist (T_H := T_H) (T_P := T_P) (δ := δ) (StmtIn := StmtIn)
          (StmtOut := StmtOut) (n := n) (pSpec := pSpec) (U := U) V maliciousProver]
      ≤ (j : ℝ≥0∞) / capacitySpaceSize (U := U) := by
  let exp :=
    lemma5_8SigmaTraceDist (T_H := T_H) (T_P := T_P) (δ := δ) (StmtIn := StmtIn)
      (StmtOut := StmtOut) (n := n) (pSpec := pSpec) (U := U) V maliciousProver
  calc
    Pr[ fun tr => E_first_at (tr.1 ++ tr.2) j ∧ E_func_fwd_at (tr.1 ++ tr.2) j | exp]
        ≤ ∑ _j' ∈ Finset.range j, (1 / capacitySpaceSize (U := U)) := by
      apply probEvent_finite_cover_le_sum exp (Finset.range j)
        (fun tr => E_first_at (tr.1 ++ tr.2) j ∧ E_func_fwd_at (tr.1 ++ tr.2) j)
        (fun j' tr => E_first_at (tr.1 ++ tr.2) j ∧
          funcConflictAt (getBaseTrace (tr.1 ++ tr.2)) j j')
        (fun _ => 1 / capacitySpaceSize (U := U))
      · intro tr hEvent
        rcases hEvent with ⟨hFirst, hFwd⟩
        have hFunc : E_func_at (tr.1 ++ tr.2) j :=
          (E_func_at_iff_fwd_or_bwd (trace := tr.1 ++ tr.2) (j := j)).mpr (Or.inl hFwd)
        obtain ⟨j', hj'mem, hConflict⟩ :=
          E_func_at_imp_funcConflict (trace := tr.1 ++ tr.2) j hFunc
        exact ⟨j', hj'mem, hFirst, hConflict⟩
      · intro j' hj'mem
        exact sigma_funcConflictAt_core_gap
          (T_H := T_H) (T_P := T_P) (StmtIn := StmtIn) (StmtOut := StmtOut)
          (n := n) (pSpec := pSpec) (U := U) (δ := δ)
          V maliciousProver j j' (Finset.mem_range.mp hj'mem)
    _ = (j : ℝ≥0∞) / capacitySpaceSize (U := U) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        simp only [div_eq_mul_inv, one_mul]

lemma lemma5_8_sigma_E_func_bwd_first_at
    (V : Verifier []ₒ StmtIn StmtOut pSpec)
    (maliciousProver : MaliciousProver []ₒ pSpec StmtIn U δ) (j : ℕ) :
    Pr[ fun tr => E_first_at (tr.1 ++ tr.2) j ∧ E_func_bwd_at (tr.1 ++ tr.2) j |
        lemma5_8SigmaTraceDist (T_H := T_H) (T_P := T_P) (δ := δ) (StmtIn := StmtIn)
          (StmtOut := StmtOut) (n := n) (pSpec := pSpec) (U := U) V maliciousProver]
      = 0 :=
  sigma_first_func_bwd_zero_core_gap (T_H := T_H) (T_P := T_P)
    (StmtIn := StmtIn) (StmtOut := StmtOut) (n := n) (pSpec := pSpec)
    (U := U) (δ := δ) V maliciousProver j

/-- **Sigma forward-functional first-witness bound.** At the earliest bad index, only the original
CO25 forward Cache_p conflict remains. Its `Cache_p ∩ tr` counting argument gives the same
`j / |Σ|^c` contribution as the paper. -/
lemma lemma5_8_sigma_E_func_fwd_first_at
    (V : Verifier []ₒ StmtIn StmtOut pSpec)
    (maliciousProver : MaliciousProver []ₒ pSpec StmtIn U δ) (j : ℕ) :
    Pr[ fun tr => E_first_at (tr.1 ++ tr.2) j ∧ E_func_fwd_at (tr.1 ++ tr.2) j |
        lemma5_8SigmaTraceDist (T_H := T_H) (T_P := T_P) (δ := δ) (StmtIn := StmtIn)
          (StmtOut := StmtOut) (n := n) (pSpec := pSpec) (U := U) V maliciousProver]
      ≤ (j : ℝ≥0∞) / capacitySpaceSize (U := U) :=
  sigma_first_func_fwd_bound_core_gap (T_H := T_H) (T_P := T_P)
    (StmtIn := StmtIn) (StmtOut := StmtOut) (n := n) (pSpec := pSpec)
    (U := U) (δ := δ) V maliciousProver j

/-- Sigma `E_func` bound at the earliest bad index, assembled from the forward bound and the
backward-zero exclusion. -/
lemma lemma5_8_sigma_E_func_first_at
    (V : Verifier []ₒ StmtIn StmtOut pSpec)
    (maliciousProver : MaliciousProver []ₒ pSpec StmtIn U δ) (j : ℕ) :
    Pr[ fun tr => E_first_at (tr.1 ++ tr.2) j ∧ E_func_at (tr.1 ++ tr.2) j |
        lemma5_8SigmaTraceDist (T_H := T_H) (T_P := T_P) (δ := δ) (StmtIn := StmtIn)
          (StmtOut := StmtOut) (n := n) (pSpec := pSpec) (U := U) V maliciousProver]
      ≤ (j : ℝ≥0∞) / capacitySpaceSize (U := U) := by
  let exp :=
    lemma5_8SigmaTraceDist (T_H := T_H) (T_P := T_P) (δ := δ) (StmtIn := StmtIn)
      (StmtOut := StmtOut) (n := n) (pSpec := pSpec) (U := U) V maliciousProver
  calc
    Pr[ fun tr => E_first_at (tr.1 ++ tr.2) j ∧ E_func_at (tr.1 ++ tr.2) j | exp]
        ≤ Pr[ fun tr =>
            (E_first_at (tr.1 ++ tr.2) j ∧ E_func_fwd_at (tr.1 ++ tr.2) j) ∨
              (E_first_at (tr.1 ++ tr.2) j ∧ E_func_bwd_at (tr.1 ++ tr.2) j) | exp] := by
          apply probEvent_mono
          intro tr _ hEvent
          rcases hEvent with ⟨hFirst, hFunc⟩
          rcases (E_func_at_iff_fwd_or_bwd (trace := tr.1 ++ tr.2) (j := j)).mp hFunc
            with hFwd | hBwd
          · exact Or.inl ⟨hFirst, hFwd⟩
          · exact Or.inr ⟨hFirst, hBwd⟩
    _ ≤ Pr[ fun tr => E_first_at (tr.1 ++ tr.2) j ∧ E_func_fwd_at (tr.1 ++ tr.2) j | exp]
          + Pr[ fun tr => E_first_at (tr.1 ++ tr.2) j ∧ E_func_bwd_at (tr.1 ++ tr.2) j | exp] :=
        probEvent_or_le _ _ _
    _ = Pr[ fun tr => E_first_at (tr.1 ++ tr.2) j ∧ E_func_fwd_at (tr.1 ++ tr.2) j | exp] + 0 := by
        rw [lemma5_8_sigma_E_func_bwd_first_at (T_H := T_H) (T_P := T_P)
          (StmtIn := StmtIn) (StmtOut := StmtOut) (n := n) (pSpec := pSpec)
          (U := U) (δ := δ) V maliciousProver j]
    _ ≤ (j : ℝ≥0∞) / capacitySpaceSize (U := U) + 0 := by
        exact add_le_add
          (lemma5_8_sigma_E_func_fwd_first_at (T_H := T_H) (T_P := T_P)
            (StmtIn := StmtIn) (StmtOut := StmtOut) (n := n) (pSpec := pSpec)
            (U := U) (δ := δ) V maliciousProver j)
          le_rfl
    _ = (j : ℝ≥0∞) / capacitySpaceSize (U := U) := by
        rw [add_zero]

end FunctionViolationReduction

end PerIndexCollisionBounds

end BadEventDS

end DuplexSpongeFS

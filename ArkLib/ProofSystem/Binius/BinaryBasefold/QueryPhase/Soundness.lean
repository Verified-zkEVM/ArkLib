/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Quang Dao
-/
module

public import ArkLib.ProofSystem.Binius.BinaryBasefold.QueryPhase.Execution
public import ArkLib.ProofSystem.Binius.BinaryBasefold.Soundness.QueryPhaseSoundness
public import ArkLib.OracleReduction.LogicStep

/-!
# Binary Basefold query-phase soundness

Successful execution implies the logical consistency checks for every repetition. If the final
folding relation fails, both folding consistency and the accumulated bad event are absent. The
query extraction-failure probability is then at most
`(1/2 + 1/(2·2^𝓡))^γ_repetitions`, by independent repeated sampling.

The repeated-query bound corresponds to archived DP24 Proposition 4.24, conditioned on the
absence of bad events; it is not an unconditional proximity claim.

## References

* [Diamond, B. E., and Posen, J., *Polylogarithmic Proofs for Multilinears over Binary
  Towers*][DP24]
-/

@[expose] public section

open OracleSpec

namespace Binius.BinaryBasefold.QueryPhase

noncomputable section
open OracleSpec _root_.OracleComp
open AdditiveNTT Polynomial MvPolynomial ProtocolSpec
open Probability

variable {r : ℕ} [NeZero r]
variable {L : Type} [Field L] [Fintype L] [DecidableEq L]
variable (𝔽q : Type) [Field 𝔽q]
local instance [Finite 𝔽q] : Fact (Nat.Prime (ringChar 𝔽q)) :=
  ⟨CharP.prime_ringChar 𝔽q⟩
variable [Fintype 𝔽q] [DecidableEq 𝔽q]
  [hF₂ : Fact (Fintype.card 𝔽q = 2)]
variable [Algebra 𝔽q L]
variable (β : Fin r → L) [hβ_lin_indep : Fact (LinearIndependent 𝔽q β)]
  [h_β₀_eq_1 : Fact (β 0 = 1)]
variable {ℓ 𝓡 ϑ : ℕ} (γ_repetitions : ℕ) [NeZero ℓ] [NeZero 𝓡] [NeZero ϑ]
variable {h_ℓ_add_R_rate : ℓ + 𝓡 < r}
variable [hdiv : Fact (ϑ ∣ ℓ)]

open scoped NNReal ProbabilityTheory

section FinalQueryRoundIOR

omit [Fact (Fintype.card 𝔽q = 2)] in
private theorem step_closed_success (γ : ℕ)
    (oStmt : ∀ j, OracleStatement 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ) j)
    (messages : ∀ i, (pSpecQuery 𝔽q β γ (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).Message i)
    (k : Fin (ℓ / ϑ)) (v : sDomain 𝔽q β h_ℓ_add_R_rate ⟨0, by omega⟩)
    (cur next : L) (stmt : FinalSumcheckStatementOut (L := L) (ℓ := ℓ))
    (h : some next ∈ support
      (simulateQ (OracleInterface.simOracle2.{0, 0, 0, 0, 0} []ₒ oStmt messages)
        (checkSingleFoldingStep 𝔽q β (γ_repetitions := γ) (ϑ := ϑ)
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) k cur v stmt).run)) :
    (k.val * ϑ > 0 → cur = logicalQueryFiberPoints 𝔽q β oStmt k v
      (extractMiddleFinMask 𝔽q β v ⟨k.val * ϑ, by
        have hh := k_succ_mul_ϑ_le_ℓ_₂ (k := k)
        omega⟩ ϑ)) ∧
    next = logicalComputeFoldedValue 𝔽q β k v stmt
      (logicalQueryFiberPoints 𝔽q β oStmt k v) := by
  classical
  rw [checkSingleFoldingStep_simulate] at h
  by_cases hk : k.val * ϑ > 0
  · by_cases hc : cur = logicalQueryFiberPoints 𝔽q β oStmt k v
        (extractMiddleFinMask 𝔽q β v ⟨k.val * ϑ, by
          have hh := k_succ_mul_ϑ_le_ℓ_₂ (k := k)
          omega⟩ ϑ)
    · exact ⟨fun _ => hc, by simpa [hk, hc, guard_eq] using h⟩
    · simp [hk, hc, guard_eq] at h
  · exact ⟨fun hpos => False.elim (hk hpos), by simpa [hk, guard_eq] using h⟩

private def closedStep (γ : ℕ)
    (oStmt : ∀ j, OracleStatement 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ) j)
    (messages : ∀ i, (pSpecQuery 𝔽q β γ (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).Message i)
    (v : sDomain 𝔽q β h_ℓ_add_R_rate ⟨0, by omega⟩)
    (stmt : FinalSumcheckStatementOut (L := L) (ℓ := ℓ))
    (k : Fin (ℓ / ϑ)) (cur : L) : OptionT (OracleComp.{0, 0, 0} []ₒ) L :=
  OptionT.mk (simulateQ (OracleInterface.simOracle2.{0, 0, 0, 0, 0} []ₒ oStmt messages)
    (checkSingleFoldingStep 𝔽q β (γ_repetitions := γ) (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) k cur v stmt).run)

private def PrefixInvariant
    (oStmt : ∀ j, OracleStatement 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ) j)
    (v : sDomain 𝔽q β h_ℓ_add_R_rate ⟨0, by omega⟩)
    (stmt : FinalSumcheckStatementOut (L := L) (ℓ := ℓ)) (i : ℕ) (cur : L) : Prop :=
  (∀ j : Fin (ℓ / ϑ), j.val < i → LogicalCheckSingleFoldingStep 𝔽q β oStmt j v stmt) ∧
    (∀ j : Fin (ℓ / ϑ), j.val + 1 = i → cur =
      logicalComputeFoldedValue 𝔽q β j v stmt (logicalQueryFiberPoints 𝔽q β oStmt j v))

omit [Fact (Fintype.card 𝔽q = 2)] in
private theorem prefixInv_step (γ : ℕ)
    (oStmt : ∀ j, OracleStatement 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ) j)
    (messages : ∀ i, (pSpecQuery 𝔽q β γ (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).Message i)
    (k : Fin (ℓ / ϑ)) (v : sDomain 𝔽q β h_ℓ_add_R_rate ⟨0, by omega⟩)
    (cur next : L) (stmt : FinalSumcheckStatementOut (L := L) (ℓ := ℓ))
    (hinv : PrefixInvariant 𝔽q β oStmt v stmt k.val cur)
    (h : some next ∈ support (closedStep 𝔽q β γ oStmt messages v stmt k cur).run) :
    PrefixInvariant 𝔽q β oStmt v stmt (k.val + 1) next := by
  have hs := step_closed_success 𝔽q β γ oStmt messages k v cur next stmt h
  have hkcheck : LogicalCheckSingleFoldingStep 𝔽q β oStmt k v stmt := by
    dsimp only [LogicalCheckSingleFoldingStep]
    split_ifs with hk
    · have hkpos : 0 < k.val := Nat.pos_of_mul_pos_right hk
      exact (hinv.2 ⟨k.val - 1, by omega⟩ (by dsimp only; omega)).symm.trans (hs.1 hk)
  constructor
  · intro j hj
    by_cases heq : j = k
    · simpa only [heq] using hkcheck
    · have hne : j.val ≠ k.val := fun hval => heq (Fin.ext hval)
      exact hinv.1 j (by omega)
  · intro j hj
    have heq : j = k := Fin.ext (by omega)
    simpa only [heq] using hs.2

omit [Fact (Fintype.card 𝔽q = 2)] in
private theorem closed_fold_prefix (γ : ℕ)
    (oStmt : ∀ j, OracleStatement 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ) j)
    (messages : ∀ i, (pSpecQuery 𝔽q β γ (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).Message i)
    (v : sDomain 𝔽q β h_ℓ_add_R_rate ⟨0, by omega⟩)
    (stmt : FinalSumcheckStatementOut (L := L) (ℓ := ℓ))
    (pref xs : List (Fin (ℓ / ϑ)))
    (hlist : List.finRange (ℓ / ϑ) = pref ++ xs)
    (cur final : L) (hinv : PrefixInvariant 𝔽q β oStmt v stmt pref.length cur)
    (h : final ∈ support (xs.foldlM
      (fun c k => closedStep 𝔽q β γ oStmt messages v stmt k c) cur)) :
    PrefixInvariant 𝔽q β oStmt v stmt (ℓ / ϑ) final := by
  induction xs generalizing pref cur with
  | nil =>
    have hlen : pref.length = ℓ / ϑ := by
      have := congrArg List.length hlist
      simpa using this.symm
    have hfinal : final = cur := by simpa using h
    simpa only [hfinal, hlen] using hinv
  | cons k xs ih =>
    have hlen : pref.length < (List.finRange (ℓ / ϑ)).length := by
      rw [hlist]
      simp
    have hget : (List.finRange (ℓ / ϑ))[pref.length] = k := by
      simp [hlist]
    have hk : k.val = pref.length := by
      simpa using (congrArg Fin.val hget).symm
    rw [List.foldlM_cons, mem_support_bind_iff] at h
    obtain ⟨next, hstep, hrest⟩ := h
    apply ih (pref ++ [k]) (by simpa [List.append_assoc] using hlist) next
    · have hs := prefixInv_step 𝔽q β γ oStmt messages k v cur next stmt
        (by simpa only [hk] using hinv) hstep
      simpa only [List.length_append, List.length_singleton, hk] using hs
    · exact hrest

omit [Fact (Fintype.card 𝔽q = 2)] in
private theorem repetition_simulate (γ : ℕ)
    (oStmt : ∀ j, OracleStatement 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ) j)
    (messages : ∀ i, (pSpecQuery 𝔽q β γ (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).Message i)
    (v : sDomain 𝔽q β h_ℓ_add_R_rate ⟨0, by omega⟩)
    (stmt : FinalSumcheckStatementOut (L := L) (ℓ := ℓ)) (final : L) :
    simulateQ (OracleInterface.simOracle2.{0, 0, 0, 0, 0} []ₒ oStmt messages)
      (checkSingleRepetition 𝔽q β (γ_repetitions := γ) (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) v stmt final).run =
    (do
      let c ← (List.finRange (ℓ / ϑ)).foldlM
        (fun c k => closedStep 𝔽q β γ oStmt messages v stmt k c) 0
      guard (c = final) : OptionT (OracleComp.{0, 0, 0} []ₒ) Unit).run := by
  classical
  change (simulateQ (OracleInterface.simOracle2.{0, 0, 0, 0, 0} []ₒ oStmt messages)
    (checkSingleRepetition 𝔽q β (γ_repetitions := γ) (ϑ := ϑ)
      v stmt final) : OptionT (OracleComp.{0, 0, 0} []ₒ) Unit) = _
  dsimp only [checkSingleRepetition]
  rw [simulateQ_optionT_bind, simulateQ_optionT_list_forIn]
  simp only [simulateQ_optionT_bind, simulateQ_optionT_pure, Fin.eta]
  have hloop : (forIn (List.finRange (ℓ / ϑ)) (0 : L) (fun k c => do
      let next ← closedStep 𝔽q β γ oStmt messages v stmt k c
      pure (ForInStep.yield next)) : OptionT (OracleComp.{0, 0, 0} []ₒ) L) =
      (List.finRange (ℓ / ϑ)).foldlM
        (fun c k => closedStep 𝔽q β γ oStmt messages v stmt k c) 0 := by
    simpa only [map_eq_bind_pure_comp, Function.comp_def, bind_pure] using
      (List.forIn_yield_eq_foldlM
        (fun k c => closedStep 𝔽q β γ oStmt messages v stmt k c)
        (fun _ _ x => x) (0 : L) (l := List.finRange (ℓ / ϑ)))
  simp only [closedStep, OptionT.mk, OptionT.run] at hloop
  rw [hloop]
  congr 1
  funext c
  by_cases hc : c = final <;> simp [guard_eq, hc, simulateQ_optionT_failure]

omit [Fact (Fintype.card 𝔽q = 2)] in
private theorem repetition_closed_success (γ : ℕ)
    (oStmt : ∀ j, OracleStatement 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ) j)
    (messages : ∀ i, (pSpecQuery 𝔽q β γ (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).Message i)
    (v : sDomain 𝔽q β h_ℓ_add_R_rate ⟨0, by omega⟩)
    (stmt : FinalSumcheckStatementOut (L := L) (ℓ := ℓ)) (final : L)
    (h : some () ∈ support (simulateQ
      (OracleInterface.simOracle2.{0, 0, 0, 0, 0} []ₒ oStmt messages)
      (checkSingleRepetition 𝔽q β (γ_repetitions := γ) (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) v stmt final).run)) :
    LogicalCheckSingleRepetition 𝔽q β oStmt v stmt final := by
  classical
  rw [repetition_simulate] at h
  have h' : () ∈ support (do
      let c ← (List.finRange (ℓ / ϑ)).foldlM
        (fun c k => closedStep 𝔽q β γ oStmt messages v stmt k c) 0
      guard (c = final) : OptionT (OracleComp.{0, 0, 0} []ₒ) Unit) := by
    simpa only [OptionT.mem_support_iff] using h
  rw [mem_support_bind_iff] at h'
  obtain ⟨c, hloop, hguard⟩ := h'
  have hc : c = final := by
    by_contra hne
    simp [guard_eq, hne] at hguard
  have hinv := closed_fold_prefix 𝔽q β γ oStmt messages v stmt []
    (List.finRange (ℓ / ϑ)) (by simp) 0 c
    (by constructor <;> intro j hj <;> dsimp only [List.length_nil] at hj <;> omega) hloop
  intro k
  dsimp only [LogicalStepCondition]
  split_ifs with hk
  · exact hinv.1 ⟨k.val, hk⟩ hk
  · have hpos : 0 < ℓ / ϑ := Nat.div_pos
      (Nat.le_of_dvd (Nat.pos_of_neZero ℓ) (Fact.out : ϑ ∣ ℓ))
      (Nat.pos_of_neZero ϑ)
    exact (hinv.2 ⟨ℓ / ϑ - 1, by omega⟩ (by dsimp only; omega)).symm.trans hc

private def closedRepetition (γ : ℕ)
    (oStmt : ∀ j, OracleStatement 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ) j)
    (messages : ∀ i, (pSpecQuery 𝔽q β γ (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).Message i)
    (v : sDomain 𝔽q β h_ℓ_add_R_rate ⟨0, by omega⟩)
    (stmt : FinalSumcheckStatementOut (L := L) (ℓ := ℓ)) (final : L) :
    OptionT (OracleComp.{0, 0, 0} []ₒ) Unit :=
  OptionT.mk (simulateQ (OracleInterface.simOracle2.{0, 0, 0, 0, 0} []ₒ oStmt messages)
    (checkSingleRepetition 𝔽q β (γ_repetitions := γ) (ϑ := ϑ)
      v stmt final).run)

omit [Fact (Fintype.card 𝔽q = 2)] in
private theorem query_each_success (γ : ℕ)
    (oStmt : ∀ j, OracleStatement 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ) j)
    (tr : FullTranscript (pSpecQuery 𝔽q β γ (h_ℓ_add_R_rate := h_ℓ_add_R_rate)))
    (stmt : FinalSumcheckStatementOut (L := L) (ℓ := ℓ)) (xs : List (Fin γ))
    (h : PUnit.unit ∈ support (forIn xs PUnit.unit (fun rep _ => do
      let _ ← closedRepetition 𝔽q β γ oStmt tr.messages
        (tr.challenges ⟨0, rfl⟩ rep) stmt stmt.finalConstant
      pure (ForInStep.yield PUnit.unit)) : OptionT (OracleComp.{0, 0, 0} []ₒ) PUnit)) :
    ∀ rep ∈ xs, () ∈ support (closedRepetition 𝔽q β γ oStmt tr.messages
      (tr.challenges ⟨0, rfl⟩ rep) stmt stmt.finalConstant) := by
  let f := fun rep => closedRepetition 𝔽q β γ oStmt tr.messages
    (tr.challenges ⟨0, rfl⟩ rep) stmt stmt.finalConstant
  change PUnit.unit ∈ support (forIn xs PUnit.unit (fun rep _ => do
    let _ ← f rep
    pure (ForInStep.yield PUnit.unit)) : OptionT (OracleComp.{0, 0, 0} []ₒ) PUnit) at h
  change ∀ rep ∈ xs, () ∈ support (f rep)
  induction xs with
  | nil => simp
  | cons a xs ih =>
    rw [List.forIn_cons, mem_support_bind_iff] at h
    obtain ⟨step, hstep, hrest⟩ := h
    rw [mem_support_bind_iff] at hstep
    obtain ⟨u, hfa, hstep⟩ := hstep
    have heq : step = ForInStep.yield PUnit.unit := by simpa using hstep
    subst step
    intro b hb
    rcases List.mem_cons.mp hb with heq | hmem
    · subst b
      simpa using hfa
    · exact ih hrest b hmem

private theorem query_check_simulate (γ : ℕ)
    (oStmt : ∀ j, OracleStatement 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ) j)
    (tr : FullTranscript (pSpecQuery 𝔽q β γ (h_ℓ_add_R_rate := h_ℓ_add_R_rate)))
    (stmt : FinalSumcheckStatementOut (L := L) (ℓ := ℓ)) :
    (simulateQ (OracleInterface.simOracle2.{0, 0, 0, 0, 0} []ₒ oStmt tr.messages)
      ((queryPhaseLogicStep 𝔽q β (ϑ := ϑ) γ).verifierCheck stmt tr) :
      OptionT (OracleComp.{0, 0, 0} []ₒ) Bool) =
    (do
      for rep in List.finRange γ do
        let _ ← (OptionT.mk (simulateQ
          (OracleInterface.simOracle2.{0, 0, 0, 0, 0} []ₒ oStmt tr.messages)
          (checkSingleRepetition 𝔽q β (γ_repetitions := γ) (ϑ := ϑ)
            (tr.challenges ⟨0, rfl⟩ rep) stmt stmt.finalConstant).run) :
              OptionT (OracleComp.{0, 0, 0} []ₒ) Unit)
      pure true : OptionT (OracleComp.{0, 0, 0} []ₒ) Bool) := by
  dsimp only [queryPhaseLogicStep]
  rw [simulateQ_optionT_bind, simulateQ_optionT_list_forIn]
  simp only [simulateQ_optionT_bind, simulateQ_optionT_pure, OptionT.mk, OptionT.run]

private theorem query_check_closed_success (γ : ℕ)
    (oStmt : ∀ j, OracleStatement 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ) j)
    (tr : FullTranscript (pSpecQuery 𝔽q β γ (h_ℓ_add_R_rate := h_ℓ_add_R_rate)))
    (stmt : FinalSumcheckStatementOut (L := L) (ℓ := ℓ)) (out : Bool)
    (h : out ∈ support (m := OptionT (OracleComp.{0, 0, 0} []ₒ))
      (simulateQ (OracleInterface.simOracle2.{0, 0, 0, 0, 0} []ₒ oStmt tr.messages)
      ((queryPhaseLogicStep 𝔽q β (ϑ := ϑ) γ).verifierCheck stmt tr) :
      OptionT (OracleComp.{0, 0, 0} []ₒ) Bool)) :
    out = true ∧ ∀ rep : Fin γ,
      LogicalCheckSingleRepetition 𝔽q β oStmt (tr.challenges ⟨0, rfl⟩ rep)
        stmt stmt.finalConstant := by
  rw [query_check_simulate, mem_support_bind_iff] at h
  obtain ⟨u, hloop, hout⟩ := h
  refine ⟨by simpa using hout, ?_⟩
  intro rep
  have hrep := query_each_success 𝔽q β γ oStmt tr stmt (List.finRange γ)
    (by simpa only [closedRepetition] using hloop) rep (by simp)
  apply repetition_closed_success 𝔽q β γ oStmt tr.messages
    (tr.challenges ⟨0, rfl⟩ rep) stmt stmt.finalConstant
  simpa only [OptionT.mem_support_iff, closedRepetition, OptionT.run_mk] using hrep

private theorem verifier_closed_success (γ : ℕ)
    (oStmt : ∀ j, OracleStatement 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ) j)
    (tr : FullTranscript (pSpecQuery 𝔽q β γ (h_ℓ_add_R_rate := h_ℓ_add_R_rate)))
    (stmt : FinalSumcheckStatementOut (L := L) (ℓ := ℓ))
    (out : Bool) (oOut : Empty → Unit)
    (h : some (out, oOut) ∈ support
      (Verifier.run (stmt, oStmt) tr
        (OracleVerifier.toVerifier (Oₛₒ := fun i : Empty => nomatch i)
          (queryOracleVerifier 𝔽q β (ϑ := ϑ) γ))).run) :
    out = true ∧ ∀ rep : Fin γ,
      LogicalCheckSingleRepetition 𝔽q β oStmt (tr.challenges ⟨0, rfl⟩ rep)
        stmt stmt.finalConstant := by
  have htr : FullTranscript.mk1 (pSpec := pSpecQuery 𝔽q β γ)
      (tr.challenges ⟨0, rfl⟩) = tr := by
    funext i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    rfl
  dsimp only [Verifier.run, OracleVerifier.toVerifier, OptionT.run_mk] at h
  rw [OptionT.run_mk, support_map, Set.mem_image] at h
  obtain ⟨maybe, hcheck, heq⟩ := h
  cases maybe with
  | none => simp at heq
  | some b =>
    have hb : b = out := congrArg Prod.fst (Option.some.inj heq)
    dsimp only [queryOracleVerifier, OracleProofVerifier.ofVerify] at hcheck
    rw [htr] at hcheck
    change some b ∈ support (simulateQ
      (OracleInterface.simOracle2.{0, 0, 0, 0, 0} []ₒ oStmt tr.messages)
      ((do
        let _ ← (queryPhaseLogicStep 𝔽q β (ϑ := ϑ) γ).verifierCheck stmt tr
        pure true) : OptionT _ Bool).run) at hcheck
    have h' : b ∈ support (m := OptionT (OracleComp.{0, 0, 0} []ₒ)) (do
      let _ ← (simulateQ (OracleInterface.simOracle2.{0, 0, 0, 0, 0} []ₒ oStmt tr.messages)
        ((queryPhaseLogicStep 𝔽q β (ϑ := ϑ) γ).verifierCheck stmt tr) :
        OptionT (OracleComp.{0, 0, 0} []ₒ) Bool)
      pure true : OptionT (OracleComp.{0, 0, 0} []ₒ) Bool) := by
      have ht : b ∈ support (m := OptionT (OracleComp.{0, 0, 0} []ₒ))
          (simulateQ (OracleInterface.simOracle2.{0, 0, 0, 0, 0} []ₒ oStmt tr.messages)
            ((do
              let _ ← (queryPhaseLogicStep 𝔽q β (ϑ := ϑ) γ).verifierCheck stmt tr
              pure true) : OptionT _ Bool) : OptionT (OracleComp.{0, 0, 0} []ₒ) Bool) := by
        simpa only [OptionT.mem_support_iff, OptionT.run, OptionT.mk] using hcheck
      rw [simulateQ_optionT_bind] at ht
      simpa only [simulateQ_optionT_pure] using ht
    rw [mem_support_bind_iff] at h'
    obtain ⟨checked, hchecked, htrue⟩ := h'
    have hbt : b = true := by simpa using htrue
    exact ⟨hb.symm.trans hbt,
      (query_check_closed_success 𝔽q β γ oStmt tr stmt checked hchecked).2⟩

-- StateT support reflection compares the projected materialized verifier run.
set_option backward.isDefEq.respectTransparency false in
/-- Successful query-verifier execution forces every logical proximity check.
The conclusion includes the returned verdict and the materialized empty oracle family. -/
theorem logicalProximityChecksSpec_of_mem_support_verifier_run
    (γ_repetitions : ℕ) {σ : Type}
    (impl : QueryImpl []ₒ (StateT σ ProbComp))
    (stmtIn : FinalSumcheckStatementOut (L := L) (ℓ := ℓ))
    (oStmtIn : ∀ j, OracleStatement 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ) j)
    (tr : FullTranscript (pSpecQuery 𝔽q β γ_repetitions
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate)))
    (s : σ) (stmtOut : Bool) (oStmtOut : Empty → Unit)
    (h_mem_V_run_support : (stmtOut, oStmtOut) ∈ support
      (OptionT.mk (Prod.fst <$> (simulateQ impl
        (Verifier.run (stmtIn, oStmtIn) tr
          (OracleVerifier.toVerifier (Oₛₒ := fun i : Empty => nomatch i)
            (queryOracleVerifier 𝔽q β (ϑ := ϑ) γ_repetitions)))).run s))) :
    stmtOut = true ∧
      oStmtOut = OracleVerifier.materializeOutput
        (Oₛₒ := fun i : Empty => nomatch i)
        (queryOracleVerifier 𝔽q β (ϑ := ϑ) γ_repetitions)
        tr.challenges oStmtIn tr.messages ∧
      ∀ rep : Fin γ_repetitions,
        LogicalCheckSingleRepetition 𝔽q β oStmtIn
          (tr.challenges ⟨0, rfl⟩ rep) stmtIn stmtIn.finalConstant := by
  have hclosed : some (stmtOut, oStmtOut) ∈ support
      (Verifier.run (stmtIn, oStmtIn) tr
        (OracleVerifier.toVerifier (Oₛₒ := fun i : Empty => nomatch i)
          (queryOracleVerifier 𝔽q β (ϑ := ϑ) γ_repetitions))).run := by
    apply support_simulateQ_run'_subset impl _ s
    simpa only [OptionT.mem_support_iff, StateT.run'_eq, OptionT.run, OptionT.mk] using
      h_mem_V_run_support
  have hlogical := verifier_closed_success 𝔽q β γ_repetitions
    oStmtIn tr stmtIn stmtOut oStmtOut hclosed
  exact ⟨hlogical.1, Subsingleton.elim _ _, hlogical.2⟩

open scoped NNReal

/-- The round-by-round extractor for the query phase.
It transports `Unit` witnesses; the remaining folding checks are carried by
`QueryKnowledgeState`. -/
noncomputable def queryRbrExtractor :
  Extractor.RoundByRound []ₒ
    (StmtIn := (FinalSumcheckStatementOut (L:=L) (ℓ:=ℓ))
      × (∀ j, OracleStatement 𝔽q β (ϑ:=ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ) j))
    (WitIn := Unit)
    Unit
    (pSpec := pSpecQuery 𝔽q β γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
    (fun _ => Unit) where
  extractIn := fun _ w => w
  extractMid := fun _ _ _ witMidSucc => witMidSucc
  extractOut := fun _ _ _ => ()

/-- Before the query challenge the final folding relation holds; afterwards every sampled
proximity check holds and the returned verdict is true. -/
def QueryKnowledgeState (m : Fin (1 + 1))
    (tr : ProtocolSpec.Transcript m
      (pSpecQuery 𝔽q β γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate)))
    (stmtIn : FinalSumcheckStatementOut (L := L) (ℓ := ℓ))
    (witMid : Unit)
    (oStmtIn : ∀ j, OracleStatement 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ) j) : Prop :=
  match m with
  | ⟨0, _⟩ => -- Same as last KState of finalSumcheck reduction (= relIn)
    Binius.BinaryBasefold.FinalSumcheckRelated 𝔽q β
      (input := ⟨⟨stmtIn, oStmtIn⟩, witMid⟩)
  | ⟨1, _⟩ => -- After V sends γ challenges: proximity tests must pass
    let γ_challenges : Fin γ_repetitions → sDomain 𝔽q β h_ℓ_add_R_rate ⟨0, by omega⟩ :=
      tr.challenges ⟨0, rfl⟩
    LogicalProximityChecksSpec 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (ϑ := ϑ) (γ_repetitions := γ_repetitions) (γ_challenges := γ_challenges)
      (finalConstant := stmtIn.finalConstant) (oStmt := oStmtIn) (stmt := stmtIn)

/-- The knowledge state function for the query phase -/
noncomputable def queryKnowledgeStateFunction {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
  (queryOracleVerifier 𝔽q β (ϑ:=ϑ) γ_repetitions).KnowledgeStateFunction init impl
  (Oₛₒ := fun i : Empty => nomatch i)
  (relIn := finalSumcheckRelOut 𝔽q β (ϑ:=ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) )
  (relOut := acceptRejectOracleRel)
  (extractor := queryRbrExtractor 𝔽q β (ϑ:=ϑ)
    γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate)) where
  toFun := fun m ⟨stmtIn, oStmtIn⟩ tr witMid =>
    QueryKnowledgeState 𝔽q β (ϑ:=ϑ) (γ_repetitions:=γ_repetitions)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (m:=m) (tr:=tr) (stmtIn:=stmtIn) (witMid:=witMid) (oStmtIn:=oStmtIn)
  toFun_empty := fun ⟨stmtIn, oStmtIn⟩ witMid h => h
  toFun_next := fun m hDir ⟨stmtMid, oStmtMid⟩ tr msg witMid => by
    simp only [ne_eq, reduceCtorEq, not_false_eq_true, Matrix.cons_val_fin_one,
      Direction.not_V_to_P_eq_P_to_V] at hDir
  toFun_full := fun ⟨stmtIn, oStmtIn⟩ tr witOut probEvent_relOut_gt_0 => by
    simp only [StateT.run'_eq, gt_iff_lt, OracleComp.OptionT.prEvent_mk_pos_iff,
      Prod.exists] at probEvent_relOut_gt_0
    rcases probEvent_relOut_gt_0 with ⟨stmtOut, oStmtOut, h_output_mem_V_run_support, h_relOut⟩
    have h_output_mem_V_run_support' :
        some (stmtOut, oStmtOut) ∈
          support (do
              let s ← init
              Prod.fst <$>
                (simulateQ impl
                  (Verifier.run (stmtIn, oStmtIn) tr
                    (OracleVerifier.toVerifier (Oₛₒ := fun i : Empty => nomatch i)
                      (pSpec := pSpecQuery 𝔽q β γ_repetitions)
                      (queryOracleVerifier 𝔽q β (ϑ := ϑ) γ_repetitions
                        (h_ℓ_add_R_rate := h_ℓ_add_R_rate))))).run s) := by
      exact h_output_mem_V_run_support
    simp only [support_bind, Set.mem_iUnion, exists_prop] at h_output_mem_V_run_support'
    rcases h_output_mem_V_run_support' with ⟨s, hs_init, h_output_mem_V_run_support_with_s⟩
    -- Apply the main lemma connecting verifier support to logical proximity checks
    have h_res := logicalProximityChecksSpec_of_mem_support_verifier_run
      (impl := impl) (stmtIn := stmtIn) (oStmtIn := oStmtIn) (tr := tr)
      (s := s) (stmtOut := stmtOut) (oStmtOut := oStmtOut)
      (h_mem_V_run_support := by
        rw [OptionT.mem_support_iff]
        dsimp only [OptionT.mk, OptionT.run]
        exact h_output_mem_V_run_support_with_s
      )
    -- The lemma gives us:
    exact h_res.2.2

open Classical in
open scoped OracleSpec.PrimitiveQuery in
/-- The query challenge causes extraction failure with probability at most the repeated-query
error bound, for every fixed input and preceding transcript. -/
lemma prEvent_rbrExtractionFailureEvent_le_queryRbrKnowledgeError {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl []ₒ (StateT σ ProbComp))
    (stmtIn_oStmtIn : (FinalSumcheckStatementOut (L := L) (ℓ := ℓ)) ×
      (∀ j, OracleStatement 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ) j))
    (transcript : (pSpecQuery 𝔽q β γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).Transcript
      (⟨0, rfl⟩ : (pSpecQuery 𝔽q β γ_repetitions
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).ChallengeIdx).1.castSucc) :
    Pr{ let y ← $ᵗ (Fin γ_repetitions → sDomain 𝔽q β h_ℓ_add_R_rate 0) }[
      rbrExtractionFailureEvent
        (kSF := queryKnowledgeStateFunction 𝔽q β (ϑ:=ϑ) γ_repetitions init impl)
        (extractor := queryRbrExtractor 𝔽q β (ϑ:=ϑ) γ_repetitions
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
        ⟨0, rfl⟩ stmtIn_oStmtIn transcript y ] ≤
      queryRbrKnowledgeError 𝔽q β γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨0, rfl⟩ := by
  classical
  change Pr{ let y ← $ᵗ (Fin γ_repetitions → sDomain 𝔽q β h_ℓ_add_R_rate 0) }[
    rbrExtractionFailureEvent
      (kSF := queryKnowledgeStateFunction 𝔽q β (ϑ:=ϑ) γ_repetitions init impl)
      (extractor := queryRbrExtractor 𝔽q β (ϑ:=ϑ) γ_repetitions
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
      ⟨0, rfl⟩ stmtIn_oStmtIn transcript y ] ≤
    ↑(queryRbrKnowledgeErrorSingleRepetition (𝓡 := 𝓡) ^ γ_repetitions)
  have hP_eq : ∀ y : Fin γ_repetitions → sDomain 𝔽q β h_ℓ_add_R_rate 0,
      rbrExtractionFailureEvent
        (kSF := queryKnowledgeStateFunction 𝔽q β (ϑ:=ϑ) γ_repetitions init impl)
        (extractor := queryRbrExtractor 𝔽q β (ϑ:=ϑ) γ_repetitions
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
        ⟨0, rfl⟩ stmtIn_oStmtIn transcript y ↔
        (¬ FinalSumcheckRelated 𝔽q β
            (input := ⟨⟨stmtIn_oStmtIn.1, stmtIn_oStmtIn.2⟩, ()⟩) ∧
          ∀ rep : Fin γ_repetitions,
            LogicalCheckSingleRepetition 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
              stmtIn_oStmtIn.2 (y rep) stmtIn_oStmtIn.1 stmtIn_oStmtIn.1.finalConstant) := by
    intro y
    simp only [rbrExtractionFailureEvent, queryRbrExtractor, queryKnowledgeStateFunction,
      QueryKnowledgeState, LogicalProximityChecksSpec, Fin.isValue,
      Fin.castSucc_zero, Fin.succ_zero_eq_one]
    simp only [FullTranscript.challenges, Transcript.concat, Fin.isValue]
    constructor
    · rintro ⟨_, h⟩; exact h
    · intro h; exact ⟨(), h⟩
  rw [prEvent_congr _ _ _ hP_eq]
  -- Bound `A ∧ (∀ rep, B (y rep))` by dropping `A` and applying the γ-fold product bound.
  by_cases hA : FinalSumcheckRelated 𝔽q β
      (input := ⟨⟨stmtIn_oStmtIn.1, stmtIn_oStmtIn.2⟩, ()⟩)
  · -- `A` false: the extraction-failure event never holds, so the probability is `0`.
    have h_false : ∀ y : Fin γ_repetitions → sDomain 𝔽q β h_ℓ_add_R_rate 0,
        (¬ FinalSumcheckRelated 𝔽q β
              (input := ⟨⟨stmtIn_oStmtIn.1, stmtIn_oStmtIn.2⟩, ()⟩) ∧
            ∀ rep : Fin γ_repetitions,
              LogicalCheckSingleRepetition 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
                stmtIn_oStmtIn.2 (y rep) stmtIn_oStmtIn.1 stmtIn_oStmtIn.1.finalConstant)
          ↔ False :=
      fun y => iff_false_intro (fun hy => hy.1 hA)
    rw [prEvent_congr _ _ _ h_false, prEvent_false]
    exact zero_le
  · -- `¬ A`: the two negated the fixed-input proximity bound hold (De Morgan).
    rw [FinalSumcheckRelated, FinalSumcheckFoldingState, not_or] at hA
    obtain ⟨h_not_consistent, h_no_bad⟩ := hA
    -- Drop the constant conjunct `A` (which holds), reducing to the all-repetitions event.
    calc Pr{ let y ← $ᵗ (Fin γ_repetitions → sDomain 𝔽q β h_ℓ_add_R_rate 0) }[
            ¬ FinalSumcheckRelated 𝔽q β
                (input := ⟨⟨stmtIn_oStmtIn.1, stmtIn_oStmtIn.2⟩, ()⟩) ∧
              ∀ rep : Fin γ_repetitions,
                LogicalCheckSingleRepetition 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
                  stmtIn_oStmtIn.2 (y rep) stmtIn_oStmtIn.1 stmtIn_oStmtIn.1.finalConstant ]
        ≤ Pr{ let y ← $ᵗ (Fin γ_repetitions → sDomain 𝔽q β h_ℓ_add_R_rate 0) }[
              ∀ rep : Fin γ_repetitions,
                LogicalCheckSingleRepetition 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
                  stmtIn_oStmtIn.2 (y rep) stmtIn_oStmtIn.1 stmtIn_oStmtIn.1.finalConstant ] := by
          apply prEvent_mono
          intro y hy
          exact hy.2
      _ ≤ (queryRbrKnowledgeErrorSingleRepetition (𝓡 := 𝓡)) ^ γ_repetitions := by
          let P : sDomain 𝔽q β h_ℓ_add_R_rate 0 → Prop := fun v =>
            LogicalCheckSingleRepetition 𝔽q β
            (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
            stmtIn_oStmtIn.2 v stmtIn_oStmtIn.1 stmtIn_oStmtIn.1.finalConstant
          have h_single := prob_logicalCheckSingleRepetition_le 𝔽q β
            stmtIn_oStmtIn.1 stmtIn_oStmtIn.2 h_not_consistent h_no_bad
          have h_product := prob_uniform_pi_mem_finset_eq
            (Finset.univ.filter P) γ_repetitions
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h_product
          rw [h_product]
          apply pow_le_pow_left'
          simpa only [SampleableType.prEvent_uniformSample] using h_single
      _ = ↑(queryRbrKnowledgeErrorSingleRepetition (𝓡 := 𝓡) ^ γ_repetitions) := by
          rw [ENNReal.coe_pow]
/-- Round-by-round knowledge soundness for the oracle-query verifier.
The fixed input and empty prefix precede its fresh family of query points. -/
theorem queryOracleVerifier_rbrKnowledgeSoundness {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    (OracleVerifier.toVerifier (Oₛₒ := fun i : Empty => nomatch i)
      (queryOracleVerifier 𝔽q β (ϑ := ϑ) γ_repetitions)).rbrKnowledgeSoundness
      init impl
      (relIn := finalSumcheckRelOut 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
      (relOut := acceptRejectOracleRel)
      (rbrKnowledgeError := queryRbrKnowledgeError 𝔽q β γ_repetitions
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate)) := by
  classical
  refine ⟨fun _ => Unit,
    queryRbrExtractor 𝔽q β (ϑ := ϑ) γ_repetitions,
    queryKnowledgeStateFunction 𝔽q β (ϑ := ϑ) γ_repetitions init impl, ?_⟩
  intro stmt j tr
  have hj : j = ⟨0, rfl⟩ := Subsingleton.elim _ _
  subst j
  have h := prEvent_rbrExtractionFailureEvent_le_queryRbrKnowledgeError (𝔽q := 𝔽q) (β := β)
    (ϑ := ϑ) (γ_repetitions := γ_repetitions) (init := init) (impl := impl)
    (stmtIn_oStmtIn := stmt) (transcript := tr)
  exact (SampleableType.prEvent_uniformSample_inst_irrel _ _ _).le.trans h

end FinalQueryRoundIOR
end
end Binius.BinaryBasefold.QueryPhase

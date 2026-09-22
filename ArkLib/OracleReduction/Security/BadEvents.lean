/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.OracleReduction.Security.RoundByRound

/-!
# Round-by-round soundness from persistent bad events

A state becomes true when the input is in the language or a challenge has caused a bad
event. Events are predicates of the prefix ending at that challenge, so subsequent prover
messages cannot create events retroactively. This construction uses the existing protocol
execution and state-function definitions.
-/

open OracleComp OracleSpec ProtocolSpec
open scoped NNReal

namespace ProtocolSpec.Transcript

variable {n : ℕ} {pSpec : ProtocolSpec n}

/-- Read a round known to be present in a partial transcript. -/
def read {m : Fin (n + 1)} (tr : Transcript m pSpec) (j : Fin n)
    (h : j.val < m.val) : pSpec.«Type» j := tr ⟨j.val, h⟩

@[simp]
theorem read_concat_lt {m : Fin n} (tr : Transcript m.castSucc pSpec)
    (msg : pSpec.«Type» m) (j : Fin n) (hj : j.val < m.val) :
    read (tr.concat msg) j (by simp only [Fin.val_succ]; omega) = read tr j hj := by
  exact Fin.snoc_castSucc
    (α := fun i : Fin (m.val + 1) ↦ pSpec.«Type» ⟨i.val, by omega⟩) msg tr ⟨j.val, hj⟩

@[simp]
theorem read_concat_last {m : Fin n} (tr : Transcript m.castSucc pSpec)
    (msg : pSpec.«Type» m) : read (tr.concat msg) m (by simp) = msg := by
  exact Fin.snoc_last
    (α := fun i : Fin (m.val + 1) ↦ pSpec.«Type» ⟨i.val, by omega⟩) msg tr

/-- Restrict a partial transcript to an earlier cutoff in the same protocol. -/
def restrict {a b : Fin (n + 1)} (h : a.val ≤ b.val) (tr : Transcript b pSpec) :
    Transcript a pSpec := fun i ↦ tr ⟨i.val, Nat.lt_of_lt_of_le i.isLt h⟩

@[simp]
theorem restrict_refl {a : Fin (n + 1)} (tr : Transcript a pSpec) :
    restrict le_rfl tr = tr := rfl

@[simp]
theorem restrict_restrict {a b c : Fin (n + 1)} (hab : a.val ≤ b.val)
    (hbc : b.val ≤ c.val) (tr : Transcript c pSpec) :
    restrict hab (restrict hbc tr) = restrict (hab.trans hbc) tr := rfl

@[simp]
theorem read_restrict {a b : Fin (n + 1)} (hab : a.val ≤ b.val)
    (tr : Transcript b pSpec) (j : Fin n) (hj : j.val < a.val) :
    read (restrict hab tr) j hj = read tr j (hj.trans_le hab) := rfl

/-- Appending a message does not change an already fixed prefix. -/
@[simp]
theorem restrict_concat {a : Fin (n + 1)} {b : Fin n}
    (h : a.val ≤ b.val) (tr : Transcript b.castSucc pSpec) (msg : pSpec.«Type» b) :
    restrict (show a.val ≤ b.succ.val by simp only [Fin.val_succ]; omega)
      (tr.concat msg) = restrict h tr := by
  funext i
  exact Fin.snoc_castSucc
    (α := fun j : Fin (b.val + 1) ↦ pSpec.«Type» ⟨j.val, by omega⟩)
    msg tr ⟨i.val, Nat.lt_of_lt_of_le i.isLt h⟩

end ProtocolSpec.Transcript

namespace Verifier

variable {ι : Type} {oSpec : OracleSpec ι} {StmtIn StmtOut : Type}
variable {n : ℕ} {pSpec : ProtocolSpec n}
variable (langIn : Set StmtIn)
variable (bad : (i : pSpec.ChallengeIdx) → StmtIn → Transcript i.val.succ pSpec → Prop)

/-- The input is valid or a bad challenge has already occurred. -/
def badEventState (m : Fin (n + 1)) (stmt : StmtIn) (tr : Transcript m pSpec) : Prop :=
  stmt ∈ langIn ∨ ∃ i : pSpec.ChallengeIdx, ∃ h : i.val.val < m.val,
    bad i stmt (tr.restrict (by simp only [Fin.val_succ]; omega))

@[simp]
theorem badEventState_zero (stmt : StmtIn) (tr : Transcript 0 pSpec) :
    badEventState langIn bad 0 stmt tr ↔ stmt ∈ langIn := by
  simp [badEventState]

/-- A newly true state must arise at the just-appended challenge. -/
theorem badEventState_new {m : Fin n} (stmt : StmtIn)
    (tr : Transcript m.castSucc pSpec) (msg : pSpec.«Type» m)
    (hbefore : ¬ badEventState langIn bad m.castSucc stmt tr)
    (hafter : badEventState langIn bad m.succ stmt (tr.concat msg)) :
    ∃ h : pSpec.dir m = .V_to_P, bad ⟨m, h⟩ stmt (tr.concat msg) := by
  rcases hafter with hlang | ⟨i, hi, hbad⟩
  · exact (hbefore (Or.inl hlang)).elim
  by_cases hlt : i.val.val < m.val
  · have hold : badEventState langIn bad m.castSucc stmt tr := by
      refine Or.inr ⟨i, hlt, ?_⟩
      have hprefix : i.val.succ.val ≤ m.val := by simp only [Fin.val_succ]; omega
      rw [Transcript.restrict_concat hprefix] at hbad
      exact hbad
    exact (hbefore hold).elim
  · have him : i.val = m := Fin.ext (by simp only [Fin.val_succ] at hi; omega)
    rcases i with ⟨i, hdir⟩
    dsimp only at him
    subst i
    exact ⟨hdir, by simpa only [Transcript.restrict_refl] using hbad⟩

/-- Prover messages cannot create a bad-challenge state. -/
theorem badEventState_prover_next (m : Fin n) (hm : pSpec.dir m = .P_to_V)
    (stmt : StmtIn) (tr : Transcript m.castSucc pSpec)
    (hbefore : ¬ badEventState langIn bad m.castSucc stmt tr) (msg : pSpec.«Type» m) :
    ¬ badEventState langIn bad m.succ stmt (tr.concat msg) := by
  intro hafter
  obtain ⟨hdir, _⟩ := badEventState_new langIn bad stmt tr msg hbefore hafter
  simp [hm] at hdir

variable {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
variable (langOut : Set StmtOut) (verifier : Verifier oSpec StmtIn StmtOut pSpec)

/-- Construct a state function once rejection in the absence of bad events is established. -/
def stateFunctionOfBadEvents
    (hterminal : ∀ stmt (tr : pSpec.FullTranscript), stmt ∉ langIn →
      (∀ i : pSpec.ChallengeIdx, ¬ bad i stmt
        (Transcript.restrict (b := Fin.last n)
          (by simp only [Fin.val_succ, Fin.val_last]; omega) tr)) →
      Pr[ (· ∈ langOut) | OptionT.mk do
        (simulateQ impl (verifier.run stmt tr)).run' (← init)] = 0) :
    verifier.StateFunction init impl langIn langOut where
  toFun := badEventState langIn bad
  toFun_empty := fun stmt ↦ (badEventState_zero langIn bad stmt default).symm
  toFun_next := badEventState_prover_next langIn bad
  toFun_full := by
    intro stmt tr h
    apply hterminal stmt tr
    · exact fun hlang ↦ h (Or.inl hlang)
    · intro i hi
      exact h (Or.inr ⟨i, i.val.isLt, hi⟩)

variable [∀ i, SampleableType (pSpec.Challenge i)]

/-- Conditional bounds on fresh bad events imply actual round-by-round soundness,
including against arbitrary adaptive provers via ArkLib's existing worst-case bridge. -/
theorem rbrSoundness_of_badEvents
    (hterminal : ∀ stmt (tr : pSpec.FullTranscript), stmt ∉ langIn →
      (∀ i : pSpec.ChallengeIdx, ¬ bad i stmt
        (Transcript.restrict (b := Fin.last n)
          (by simp only [Fin.val_succ, Fin.val_last]; omega) tr)) →
      Pr[ (· ∈ langOut) | OptionT.mk do
        (simulateQ impl (verifier.run stmt tr)).run' (← init)] = 0)
    (ε : pSpec.ChallengeIdx → ℝ≥0)
    (hbound : ∀ stmt ∉ langIn, ∀ i : pSpec.ChallengeIdx,
      ∀ tr : Transcript i.val.castSucc pSpec,
      ¬ badEventState langIn bad i.val.castSucc stmt tr →
      Pr[ fun c ↦ bad i stmt (tr.concat c) | $ᵗ (pSpec.Challenge i)] ≤ ε i) :
    verifier.rbrSoundness init impl langIn langOut ε := by
  apply rbrSoundnessWorstCase_implies_rbrSoundness
  refine ⟨stateFunctionOfBadEvents langIn bad init impl langOut verifier hterminal, ?_⟩
  intro stmt hstmt i tr
  change Pr[ fun c ↦ ¬ badEventState langIn bad i.val.castSucc stmt tr ∧
    badEventState langIn bad i.val.succ stmt (tr.concat c) | $ᵗ (pSpec.Challenge i)] ≤ _
  by_cases hb : badEventState langIn bad i.val.castSucc stmt tr
  · simp [hb]
  · apply le_trans _ (hbound stmt hstmt i tr hb)
    apply probEvent_mono''
    intro c hc
    obtain ⟨hdir, hbad⟩ := badEventState_new langIn bad stmt tr c hc.1 hc.2
    exact hbad

end Verifier

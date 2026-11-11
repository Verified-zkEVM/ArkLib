/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
module

public import ArkLib.ProofSystem.RingSwitching.Packing.ProductSumcheck.Basic
public import ArkLib.ProofSystem.RingSwitching.RoundVerifiers
public import ArkLib.OracleReduction.Security.GuardedRoundByRound
public import ArkLib.OracleReduction.LogicStep

/-!
# The terminal same-commitment opening check

After every sumcheck variable is fixed, the prover sends the packed evaluation over C. The
verifier checks its product with the public multiplier and forwards the value on the same
commitment oracles. The protocol also covers zero variables. The deterministic step adds no
challenge error.
-/

@[expose] public section

noncomputable section
namespace RingSwitching.Packing.ProductSumcheck.Terminal
open Probability OracleSpec OracleComp ProtocolSpec MvPolynomial ProbabilityTheory
variable {P C Context : Type} [CommRing P] [CommRing C] [Algebra P C] {m : ℕ}
  (multiplier : Multiplier Context C m) (pc : PackedCommitment P m)

/-- The packed C-evaluation is sent as one clear message. -/
def pSpec (C : Type) : ProtocolSpec 1 := pSpecMessage C

instance : ∀ i, OracleInterface ((pSpec C).Message i) :=
  inferInstanceAs (∀ i, OracleInterface ((pSpecMessage C).Message i))

instance : ∀ i, SampleableType ((pSpec C).Challenge i)
  | ⟨0, h⟩ => nomatch h

/-- The only verifier equation, valid also when the multiplier is zero. -/
def check (stmt : Statement Context C (Fin.last m)) (v : C) : Prop :=
  stmt.target = multiplier.evaluate stmt.ctx stmt.challenges * v

/-- Preserve the complete challenge point and forward the packed evaluation itself. -/
def nextStatement (stmt : Statement Context C (Fin.last m)) (v : C) : Context × ((Fin m → C) × C) :=
  (stmt.ctx, (stmt.challenges, v))

/-- The honest prover preserves the packed polynomial and commitment oracle. -/
def proverForOracles {ι : Type} (OStmt : ι → Type) :
    OracleProver []ₒ (Statement Context C (Fin.last m)) OStmt
    P⦃≤ 1⦄[X Fin m] (Context × ((Fin m → C) × C)) OStmt P⦃≤ 1⦄[X Fin m] (pSpec C) where
  PrvState _ := ((Statement Context C (Fin.last m)) × (∀ j, OStmt j)) ×
    P⦃≤ 1⦄[X Fin m]
  input := id
  sendMessage
    | ⟨0, _⟩ => fun st => pure (aeval st.1.1.challenges st.2.val, st)
  receiveChallenge
    | ⟨0, h⟩ => nomatch h
  output st := pure ((nextStatement st.1.1 (aeval st.1.1.challenges st.2.val), st.1.2), st.2)

/-- Send the packed evaluation with unchanged oracle values. -/
def prover := proverForOracles (P := P) (C := C) (Context := Context) (m := m) pc.OStmt

open scoped Classical in
/-- A failed product check aborts the oracle verifier. -/
def verifier : OracleVerifier []ₒ (Statement Context C (Fin.last m)) pc.OStmt
    (Context × ((Fin m → C) × C)) pc.OStmt (pSpec C) :=
  messageRoundOracleVerifier (check multiplier) nextStatement

/-- The terminal reduction ends at the original commitment's evaluation relation over C. -/
def reduction : OracleReduction []ₒ (Statement Context C (Fin.last m)) pc.OStmt
    P⦃≤ 1⦄[X Fin m] (Context × ((Fin m → C) × C)) pc.OStmt P⦃≤ 1⦄[X Fin m] (pSpec C) :=
  ⟨prover pc, verifier multiplier pc⟩

open scoped Classical in
/-- The deterministic guarded form required by checked sequential composition. -/
def guardedForm : (verifier multiplier pc).toVerifier.GuardedForm :=
  messageRoundOracleVerifierGuardedForm (check multiplier) nextStatement

omit [Algebra P C] in
open scoped Classical in
/-- The terminal guarded form checks the multiplier equation. -/
theorem guardedForm_check (stmt : Statement Context C (Fin.last m) × (∀ j, pc.OStmt j))
    (tr : FullTranscript (pSpec C)) :
    (guardedForm multiplier pc).check stmt tr =
      decide (check multiplier stmt.1 (tr.messages ⟨0, rfl⟩)) := rfl

omit [Algebra P C] in
/-- The terminal guarded form forwards the evaluation and the input commitment oracles. -/
theorem guardedForm_out (stmt : Statement Context C (Fin.last m) × (∀ j, pc.OStmt j))
    (tr : FullTranscript (pSpec C)) :
    (guardedForm multiplier pc).out stmt tr =
      (nextStatement stmt.1 (tr.messages ⟨0, rfl⟩), stmt.2) := rfl


open scoped Classical in
omit [Algebra P C] in
/-- Exact materialized execution, including absorbing rejection and oracle forwarding. -/
theorem verifier_verify (stmt : Statement Context C (Fin.last m)) (ost : ∀ j, pc.OStmt j)
    (tr : FullTranscript (pSpec C)) :
    (verifier multiplier pc).toVerifier.verify (stmt, ost) tr =
      (if check multiplier stmt (tr.messages ⟨0, rfl⟩) then
        pure (nextStatement stmt (tr.messages ⟨0, rfl⟩), ost) else failure) := by
  have h := (guardedForm multiplier pc).verify_eq (stmt, ost) tr
  rw [guardedForm_check, guardedForm_out] at h
  simpa only [decide_eq_true_eq] using h

instance : (prover (C := C) (Context := Context) pc).OutputIsPure where
  output_is_pure := ⟨fun st =>
    ((nextStatement st.1.1 (aeval st.1.1.challenges st.2.val), st.1.2), st.2), fun _ => rfl⟩

/-- The terminal input relation supplies the honest multiplier equation. -/
theorem check_aeval_of_mem_rel {stmt : Statement Context C (Fin.last m)} {ost : ∀ j, pc.OStmt j}
    {p : P⦃≤ 1⦄[X Fin m]} (h : ((stmt, ost), p) ∈ rel multiplier pc (Fin.last m)) :
    check multiplier stmt (aeval stmt.challenges p.val) := by
  rw [check, multiplier.evaluate_eq]
  exact ((rel_last multiplier pc stmt ost p).mp h).1

/-- Honest output is an opening of the same P-polynomial against the same oracles. -/
theorem nextStatement_mem_evalRelWithContext {stmt : Statement Context C (Fin.last m)} {ost : ∀
    j, pc.OStmt j}
    {p : P⦃≤ 1⦄[X Fin m]} (h : ((stmt, ost), p) ∈ rel multiplier pc (Fin.last m)) :
    ((nextStatement stmt (aeval stmt.challenges p.val), ost), p) ∈
      (pc.evalRelWithContext Context) :=
  ⟨rfl, h.2⟩

/-- A correct accepted opening supplies the exact terminal input witness without cancellation. -/
theorem mem_rel_last_of_check (stmt : Statement Context C (Fin.last m)) (ost : ∀ j, pc.OStmt j)
    (v : C) (p : P⦃≤ 1⦄[X Fin m]) (hc : check multiplier stmt v)
    (ho : ((nextStatement stmt v, ost), p) ∈ (pc.evalRelWithContext Context)) :
    ((stmt, ost), p) ∈ rel multiplier pc (Fin.last m) := by
  apply (rel_last multiplier pc stmt ost p).mpr
  rw [check, multiplier.evaluate_eq] at hc
  exact ⟨hc.trans (congrArg ((multiplier stmt.ctx).val.eval stmt.challenges * ·) ho.1), ho.2⟩

/-- The sole-message transcript. -/
def transcript (v : C) : FullTranscript (pSpec C) := fun | ⟨0, _⟩ => v

/-- Honest execution sends the challenge-algebra evaluation and preserves the packed witness. -/
theorem prover_run (stmt : Statement Context C (Fin.last m)) (ost : ∀ j, pc.OStmt j)
    (p : P⦃≤ 1⦄[X Fin m]) :
    (prover pc).run (stmt, ost) p =
      pure (transcript (aeval stmt.challenges p.val),
        (nextStatement stmt (aeval stmt.challenges p.val), ost), p) := by
  have h0 : (pSpec C).dir 0 = .P_to_V := rfl
  simp only [Prover.run, Prover.runToRound, Fin.induction_one,
    Prover.processRound_of_dir_eq_P_to_V 0 h0]
  simp only [prover, proverForOracles, pure_bind, liftM_pure]
  congr 1
  apply Prod.ext
  · funext i
    fin_cases i
    rfl
  · rfl

open scoped Classical in
/-- Complete execution retains failure and the true forwarded value. -/
theorem reduction_run (stmt : Statement Context C (Fin.last m)) (ost : ∀ j, pc.OStmt j)
    (p : P⦃≤ 1⦄[X Fin m]) :
    ((reduction multiplier pc).toReduction.run (stmt, ost) p).run =
      pure (if check multiplier stmt (aeval stmt.challenges p.val) then
        some ((transcript (aeval stmt.challenges p.val),
          (nextStatement stmt (aeval stmt.challenges p.val), ost), p),
          (nextStatement stmt (aeval stmt.challenges p.val), ost)) else none) := by
  rw [Reduction.run_eq_of_guarded_verifier _ (guardedForm multiplier pc)]
  change ((prover pc).run (stmt, ost) p >>= _) = _
  rw [prover_run, pure_bind]
  by_cases hc : check multiplier stmt (aeval stmt.challenges p.val) <;>
    simp [guardedForm_check, guardedForm_out, transcript, FullTranscript.messages, hc]

/-- Perfect completeness for arbitrary initial state distributions, over commutative rings. -/
theorem perfectCompleteness {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    (reduction multiplier pc).perfectCompleteness init impl
      (rel multiplier pc (Fin.last m)) (pc.evalRelWithContext Context) := by
  classical
  apply Reduction.perfectCompleteness_of_guarded_prover_support _ (guardedForm multiplier pc)
  intro ⟨stmt, ost⟩ p hIn q hq
  change q ∈ support ((prover pc).run (stmt, ost) p) at hq
  rw [prover_run] at hq
  have hq := OracleComp.eq_of_mem_support_pure _ hq
  subst q
  refine ⟨?_, nextStatement_mem_evalRelWithContext multiplier pc hIn, rfl⟩
  exact decide_eq_true (check_aeval_of_mem_rel multiplier pc hIn)

/-- A positive-probability related output determines the accepted product check and opening. -/
theorem check_and_mem_of_prEvent_pos {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl []ₒ (StateT σ ProbComp))
    (stmt : Statement Context C (Fin.last m)) (ost : ∀ j, pc.OStmt j)
    (tr : FullTranscript (pSpec C)) (p : P⦃≤ 1⦄[X Fin m])
    (h : Pr{let out ← OptionT.mk do
      (simulateQ impl ((verifier multiplier pc).toVerifier.run (stmt, ost) tr)).run'
        (← init)}[(out, p) ∈ (pc.evalRelWithContext Context)] > 0) :
    check multiplier stmt (tr.messages ⟨0, rfl⟩) ∧
      ((nextStatement stmt (tr.messages ⟨0, rfl⟩), ost), p) ∈ (pc.evalRelWithContext Context) := by
  classical
  obtain ⟨hc, hrel⟩ := (guardedForm multiplier pc).check_and_of_prEvent_pos h
  exact ⟨of_decide_eq_true hc, hrel⟩

/-- The original packed polynomial is the witness at every terminal prefix. -/
abbrev WitMid (_i : Fin 2) : Type := P⦃≤ 1⦄[X Fin m]

/-- The terminal extractor preserves the original packed polynomial. -/
def extractor :
    Extractor.RoundByRound []ₒ
      (StmtIn := Statement Context C (Fin.last m) × (∀ j, pc.OStmt j))
      (WitIn := P⦃≤ 1⦄[X Fin m]) (WitOut := P⦃≤ 1⦄[X Fin m])
      (pSpec := pSpec C) (WitMid := WitMid (P := P) (m := m)) where
  extractIn := fun _ w => w
  extractMid _ _ _ p := p
  extractOut _ _ p := p

/-- The knowledge states retain the accepted product guard and exact same-commitment opening. -/
def knowledgeStateFunction {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    (verifier multiplier pc).KnowledgeStateFunction init impl
      (rel multiplier pc (Fin.last m)) (pc.evalRelWithContext Context) (extractor (Context :=
        Context) pc) where
  toFun
    | ⟨0, _⟩ => fun stmt _ p => (stmt, p) ∈ rel multiplier pc (Fin.last m)
    | ⟨1, _⟩ => fun stmt tr p => check multiplier stmt.1 (tr 0) ∧
      ((nextStatement stmt.1 (tr 0), stmt.2), p) ∈ (pc.evalRelWithContext Context)
  toFun_empty _ _ h := h
  toFun_next
    | ⟨0, _⟩ => fun _ stmt _tr v p h => mem_rel_last_of_check multiplier pc stmt.1 stmt.2 v p h.1
      h.2
  toFun_full stmt tr p h := check_and_mem_of_prEvent_pos multiplier pc init impl stmt.1 stmt.2 tr
    p h

/-- Exact round-by-round knowledge soundness with no challenge error, including when
m is zero. -/
theorem rbrKnowledgeSoundnessWith {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    Verifier.rbrKnowledgeSoundnessWith init impl
      (rel multiplier pc (Fin.last m)) (pc.evalRelWithContext Context) (verifier multiplier
        pc).toVerifier
      (WitMid (P := P) (m := m)) (extractor (Context := Context) pc)
      (knowledgeStateFunction multiplier pc init impl) (fun _ => 0) := by
  intro stmt i tr
  rcases i with ⟨⟨i, hi⟩, hdir⟩
  have : i = 0 := by omega
  subst i
  contradiction

end RingSwitching.Packing.ProductSumcheck.Terminal

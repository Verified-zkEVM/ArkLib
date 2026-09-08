/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ProofSystem.RingSwitching.Packing.Tail.Basic
import ArkLib.ProofSystem.RingSwitching.RoundVerifiers
import ArkLib.OracleReduction.Security.CoordinateWiseSpecialSoundness.Guarded
import ArkLib.OracleReduction.Composition.Sequential.GuardedCompleteness

/-!
# The terminal same-commitment opening check

After every sumcheck variable is fixed, the prover sends the packed evaluation over C. The
verifier checks its product with the public multiplier and forwards the value on the same
commitment oracles. The zero-variable case uses this very same protocol. No cancellation or
field assumption is needed, and the deterministic step adds no challenge error.
-/

noncomputable section
namespace RingSwitching.Packing.Tail.Terminal
open OracleSpec OracleComp ProtocolSpec MvPolynomial ProbabilityTheory
variable {P C Context : Type} [CommRing P] [CommRing C] [Algebra P C] {m : ℕ}
  (multiplier : Context → C⦃≤ 1⦄[X Fin m]) (pc : PackedCommitment P m)

/-- The packed C-evaluation is sent as one clear message. -/
def pSpec (C : Type) : ProtocolSpec 1 := pSpecMessage C

instance : ∀ i, OracleInterface ((pSpec C).Message i) :=
  inferInstanceAs (∀ i, OracleInterface ((pSpecMessage C).Message i))

instance : ∀ i, SampleableType ((pSpec C).Challenge i)
  | ⟨0, h⟩ => nomatch h

/-- The only verifier equation, valid also when the multiplier is zero. -/
def check (stmt : Statement Context C (Fin.last m)) (v : C) : Prop :=
  stmt.target = (multiplier stmt.ctx).val.eval stmt.challenges * v

/-- Preserve the complete challenge point and forward the packed evaluation itself. -/
def nextStatement (stmt : Statement Context C (Fin.last m)) (v : C) : (Fin m → C) × C :=
  (stmt.challenges, v)

/-- The honest prover retains the original polynomial and the actual commitment oracle. -/
def prover : OracleProver []ₒ (Statement Context C (Fin.last m)) pc.OStmt
    P⦃≤ 1⦄[X Fin m] ((Fin m → C) × C) pc.OStmt P⦃≤ 1⦄[X Fin m] (pSpec C) where
  PrvState _ := ((Statement Context C (Fin.last m)) × (∀ j, pc.OStmt j)) ×
    P⦃≤ 1⦄[X Fin m]
  input := id
  sendMessage
    | ⟨0, _⟩ => fun st => pure (aeval st.1.1.challenges st.2.val, st)
  receiveChallenge
    | ⟨0, h⟩ => nomatch h
  output st := pure ((nextStatement st.1.1 (aeval st.1.1.challenges st.2.val), st.1.2), st.2)

open scoped Classical in
/-- A failed product check aborts the actual oracle verifier. -/
def verifier : OracleVerifier []ₒ (Statement Context C (Fin.last m)) pc.OStmt
    ((Fin m → C) × C) pc.OStmt (pSpec C) :=
  guardedMessageRoundOracleVerifier (check multiplier) nextStatement

/-- The terminal reduction ends at the original commitment's evaluation relation over C. -/
def reduction : OracleReduction []ₒ (Statement Context C (Fin.last m)) pc.OStmt
    P⦃≤ 1⦄[X Fin m] ((Fin m → C) × C) pc.OStmt P⦃≤ 1⦄[X Fin m] (pSpec C) :=
  ⟨prover pc, verifier multiplier pc⟩

open scoped Classical in
omit [Algebra P C] in
/-- Exact materialized execution, including absorbing rejection and oracle forwarding. -/
theorem verifier_verify (stmt : Statement Context C (Fin.last m)) (ost : ∀ j, pc.OStmt j)
    (tr : FullTranscript (pSpec C)) :
    (verifier multiplier pc).toVerifier.verify (stmt, ost) tr =
      (if check multiplier stmt (tr.messages ⟨0, rfl⟩) then
        pure (nextStatement stmt (tr.messages ⟨0, rfl⟩), ost) else failure) := by
  apply guardedMessageRoundOracleVerifier_verify

open scoped Classical in
/-- The deterministic guarded form required by checked sequential composition. -/
def guardedForm : (verifier multiplier pc).toVerifier.GuardedForm where
  check stmt tr := decide (check multiplier stmt.1 (tr.messages ⟨0, rfl⟩))
  out stmt tr := (nextStatement stmt.1 (tr.messages ⟨0, rfl⟩), stmt.2)
  verify_eq stmt tr := by rw [verifier_verify]; simp

instance : (prover (C := C) (Context := Context) pc).OutputIsPure where
  output_is_pure := ⟨fun st =>
    ((nextStatement st.1.1 (aeval st.1.1.challenges st.2.val), st.1.2), st.2), fun _ => rfl⟩

/-- The terminal input relation supplies the honest multiplier equation. -/
theorem honest_check {stmt : Statement Context C (Fin.last m)} {ost : ∀ j, pc.OStmt j}
    {p : P⦃≤ 1⦄[X Fin m]} (h : ((stmt, ost), p) ∈ rel multiplier pc (Fin.last m)) :
    check multiplier stmt (aeval stmt.challenges p.val) :=
  ((rel_last multiplier pc stmt ost p).mp h).1

/-- Honest output is an opening of the same P-polynomial against the same oracles. -/
theorem honest_relOut {stmt : Statement Context C (Fin.last m)} {ost : ∀ j, pc.OStmt j}
    {p : P⦃≤ 1⦄[X Fin m]} (h : ((stmt, ost), p) ∈ rel multiplier pc (Fin.last m)) :
    ((nextStatement stmt (aeval stmt.challenges p.val), ost), p) ∈ pc.evalRel := ⟨rfl, h.2⟩

/-- A correct accepted opening supplies the exact terminal input witness without cancellation. -/
theorem readback (stmt : Statement Context C (Fin.last m)) (ost : ∀ j, pc.OStmt j)
    (v : C) (p : P⦃≤ 1⦄[X Fin m]) (hc : check multiplier stmt v)
    (ho : ((nextStatement stmt v, ost), p) ∈ pc.evalRel) :
    ((stmt, ost), p) ∈ rel multiplier pc (Fin.last m) := by
  apply (rel_last multiplier pc stmt ost p).mpr
  exact ⟨hc.trans (congrArg ((multiplier stmt.ctx).val.eval stmt.challenges * ·) ho.1), ho.2⟩

/-- The sole-message transcript. -/
def transcript (v : C) : FullTranscript (pSpec C) := fun | ⟨0, _⟩ => v

/-- Actual honest execution sends the C-evaluation and preserves its P witness. -/
theorem prover_run (stmt : Statement Context C (Fin.last m)) (ost : ∀ j, pc.OStmt j)
    (p : P⦃≤ 1⦄[X Fin m]) :
    (prover pc).run (stmt, ost) p =
      pure (transcript (aeval stmt.challenges p.val),
        (nextStatement stmt (aeval stmt.challenges p.val), ost), p) := by
  have h0 : (pSpec C).dir 0 = .P_to_V := rfl
  simp only [Prover.run, Prover.runToRound, Fin.induction_one,
    Prover.processRound_of_dir_eq_P_to_V 0 h0]
  simp only [prover, pure_bind, liftM_pure]
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
    simp [guardedForm, transcript, FullTranscript.messages, hc]

/-- Perfect completeness for arbitrary initial state distributions, over commutative rings. -/
theorem perfectCompleteness {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    (reduction multiplier pc).perfectCompleteness init impl
      (rel multiplier pc (Fin.last m)) pc.evalRel := by
  classical
  apply Reduction.perfectCompleteness_of_run_support
  intro stmt p hIn x hx
  rw [reduction_run, if_pos (honest_check multiplier pc hIn)] at hx
  have hx := OracleComp.eq_of_mem_support_pure _ hx
  subst x
  exact ⟨_, rfl, honest_relOut multiplier pc hIn, rfl⟩

/-- Positive probability of a related output pins the actual accepted guard and opening. -/
theorem positive_output {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl []ₒ (StateT σ ProbComp))
    (stmt : Statement Context C (Fin.last m)) (ost : ∀ j, pc.OStmt j)
    (tr : FullTranscript (pSpec C)) (p : P⦃≤ 1⦄[X Fin m])
    (h : Pr[ fun out => (out, p) ∈ pc.evalRel |
      OptionT.mk do (simulateQ impl
        ((verifier multiplier pc).toVerifier.run (stmt, ost) tr)).run' (← init)] > 0) :
    check multiplier stmt (tr.messages ⟨0, rfl⟩) ∧
      ((nextStatement stmt (tr.messages ⟨0, rfl⟩), ost), p) ∈ pc.evalRel := by
  classical
  rw [gt_iff_lt, probEvent_pos_iff] at h
  obtain ⟨out, hout, hrel⟩ := h
  rw [OptionT.mem_support_iff] at hout
  simp only [Verifier.run, verifier_verify] at hout
  by_cases hc : check multiplier stmt (tr.messages ⟨0, rfl⟩)
  · rw [if_pos hc] at hout
    change some out ∈ support (init >>= fun _ => pure (some
      (nextStatement stmt (tr.messages ⟨0, rfl⟩), ost))) at hout
    simp only [support_bind_const, support_pure, Set.mem_ofPred_eq] at hout
    obtain rfl := Option.some.inj hout.1
    exact ⟨hc, hrel⟩
  · rw [if_neg hc] at hout
    change some out ∈ support (init >>= fun _ => pure none) at hout
    simp at hout

/-- The original packed polynomial is the witness at every terminal prefix. -/
abbrev WitMid (_i : Fin 2) : Type := P⦃≤ 1⦄[X Fin m]

/-- The terminal extractor preserves the original packed polynomial. -/
def extractor :
    Extractor.RoundByRound []ₒ
      (StmtIn := Statement Context C (Fin.last m) × (∀ j, pc.OStmt j))
      (WitIn := P⦃≤ 1⦄[X Fin m]) (WitOut := P⦃≤ 1⦄[X Fin m])
      (pSpec := pSpec C) (WitMid := WitMid (P := P) (m := m)) where
  eqIn := rfl
  extractMid _ _ _ p := p
  extractOut _ _ p := p

/-- The knowledge states retain the accepted product guard and exact same-commitment opening. -/
def knowledgeStateFunction {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    (verifier multiplier pc).KnowledgeStateFunction init impl
      (rel multiplier pc (Fin.last m)) pc.evalRel (extractor (Context := Context) pc) where
  toFun
    | ⟨0, _⟩ => fun stmt _ p => (stmt, p) ∈ rel multiplier pc (Fin.last m)
    | ⟨1, _⟩ => fun stmt tr p => check multiplier stmt.1 (tr 0) ∧
      ((nextStatement stmt.1 (tr 0), stmt.2), p) ∈ pc.evalRel
  toFun_empty _ _ := Iff.rfl
  toFun_next
    | ⟨0, _⟩ => fun _ stmt _tr v p h => readback multiplier pc stmt.1 stmt.2 v p h.1 h.2
  toFun_full stmt tr p h := positive_output multiplier pc init impl stmt.1 stmt.2 tr p h

/-- Exact worst-case knowledge with no challenge error, including when m is zero. -/
theorem rbrKnowledgeSoundnessWorstCaseWith {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    Verifier.rbrKnowledgeSoundnessWorstCaseWith init impl
      (rel multiplier pc (Fin.last m)) pc.evalRel (verifier multiplier pc).toVerifier
      (WitMid (P := P) (m := m)) (extractor (Context := Context) pc)
      (knowledgeStateFunction multiplier pc init impl) (fun _ => 0) := by
  intro stmt i tr
  rcases i with ⟨⟨i, hi⟩, hdir⟩
  have : i = 0 := by omega
  subst i
  contradiction

end RingSwitching.Packing.Tail.Terminal

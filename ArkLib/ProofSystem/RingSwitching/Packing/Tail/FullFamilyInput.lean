/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ProofSystem.RingSwitching.Packing.Tail.SeqCompose
import ArkLib.ProofSystem.RingSwitching.Packing.FullFamily.Phase

/-!
# The exact full-family output to sumcheck-input adapter

The public opening point, batching challenge, and target already determine the sumcheck input.
This zero-round adapter merely installs the empty challenge prefix. It preserves the original
P-polynomial and every original oracle statement; its relation bridge is proved algebraically.
-/

noncomputable section
namespace RingSwitching.Packing.FullFamilyTail
open OracleSpec OracleComp ProtocolSpec MvPolynomial
variable {B : Type} [CommRing B] (data : PackingData B) (m : ℕ)
  {C : Type} [CommRing C] [Algebra B C] [Algebra data.P C]
  (bat : BatchingStrategy C data.ιE) (pc : PackedCommitment data.P m)

/-- The full-family retained point and batching challenge determine the public multiplier. -/
def multiplier (ctx : (Fin m → data.E) × bat.Challenge) : C⦃≤ 1⦄[X Fin m] :=
  data.multiplier ctx.1 (bat.weight ctx.2)

/-- The actual initial tail statement uses the existing target and an empty challenge prefix. -/
def initialStatement (stmt : FullFamily.Output data m bat) :
    Tail.Statement ((Fin m → data.E) × bat.Challenge) C (0 : Fin (m + 1)) :=
  ⟨stmt.1, Fin.elim0, stmt.2⟩

/-- The full-family output and the initial sumcheck claim are the same algebraic relation. -/
theorem initialStatement_rel (stmt : FullFamily.Output data m bat) (ost : ∀ j, pc.OStmt j)
    (p : data.P⦃≤ 1⦄[X Fin m]) :
    ((initialStatement data m bat stmt, ost), p) ∈ Tail.rel (multiplier data m bat) pc 0 ↔
      ((stmt, ost), p) ∈ FullFamily.relOut data m bat pc := by
  rw [initialStatement, Tail.rel_zero]
  have heval (y : Fin m → Fin 2) : aeval (y : Fin m → C) p.val =
      algebraMap data.P C (p.val.eval (y : Fin m → data.P)) := by
    simpa only [MvPolynomial.aeval_def, Function.comp_def, map_natCast] using
      (MvPolynomial.eval₂_comp (algebraMap data.P C) (y : Fin m → data.P) p.val).symm
  simp only [heval]
  rfl

/-- The zero-round prover reformats the public input and keeps the same packed witness. -/
def adapterProver : OracleProver []ₒ (FullFamily.Output data m bat) pc.OStmt
    data.P⦃≤ 1⦄[X Fin m]
    (Tail.Statement ((Fin m → data.E) × bat.Challenge) C (0 : Fin (m + 1))) pc.OStmt
    data.P⦃≤ 1⦄[X Fin m] !p[] where
  PrvState _ := (FullFamily.Output data m bat × (∀ j, pc.OStmt j)) ×
    data.P⦃≤ 1⦄[X Fin m]
  input := id
  sendMessage j := nomatch j
  receiveChallenge j := nomatch j
  output st := pure ((initialStatement data m bat st.1.1, st.1.2), st.2)

/-- The zero-round verifier installs the empty prefix and forwards the original oracle family. -/
def adapterVerifier : OracleVerifier []ₒ (FullFamily.Output data m bat) pc.OStmt
    (Tail.Statement ((Fin m → data.E) × bat.Challenge) C (0 : Fin (m + 1))) pc.OStmt !p[] where
  verify stmt _ := pure (initialStatement data m bat stmt)
  outputOracle := .inl {
    embed := ⟨fun j => Sum.inl j, fun _ _ h => Sum.inl.inj h⟩
    hEq := fun _ => rfl
    outputInterface_heq := fun _ => HEq.rfl }

/-- The actual input-format adapter, with no protocol messages or challenges. -/
def adapterReduction : OracleReduction []ₒ (FullFamily.Output data m bat) pc.OStmt
    data.P⦃≤ 1⦄[X Fin m]
    (Tail.Statement ((Fin m → data.E) × bat.Challenge) C (0 : Fin (m + 1))) pc.OStmt
    data.P⦃≤ 1⦄[X Fin m] !p[] :=
  ⟨adapterProver data m bat pc, adapterVerifier data m bat pc⟩

omit [Algebra B C] [Algebra data.P C] in
/-- The adapter's actual materialized output preserves the entire oracle collection. -/
theorem adapterVerifier_verify (stmt : FullFamily.Output data m bat)
    (ost : ∀ j, pc.OStmt j) (tr : FullTranscript !p[]) :
    (adapterVerifier data m bat pc).toVerifier.verify (stmt, ost) tr =
      pure (initialStatement data m bat stmt, ost) := rfl

/-- The zero-round input adapter has no guard to reject. -/
def adapterGuardedForm : (adapterVerifier data m bat pc).toVerifier.GuardedForm where
  check _ _ := true
  out stmt _ := (initialStatement data m bat stmt.1, stmt.2)
  verify_eq _ _ := rfl

instance : (adapterProver data m bat pc).OutputIsPure where
  output_is_pure := ⟨fun st => ((initialStatement data m bat st.1.1, st.1.2), st.2), fun _ => rfl⟩

omit [Algebra B C] [Algebra data.P C] in
/-- Actual honest execution only reformats the input, with an empty transcript. -/
theorem adapterProver_run (stmt : FullFamily.Output data m bat) (ost : ∀ j, pc.OStmt j)
    (p : data.P⦃≤ 1⦄[X Fin m]) :
    (adapterProver data m bat pc).run (stmt, ost) p =
      pure (default, (initialStatement data m bat stmt, ost), p) := rfl

/-- The input adapter is perfectly complete from every oracle-state distribution. -/
theorem adapter_perfectCompleteness {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    (adapterReduction data m bat pc).perfectCompleteness init impl
      (FullFamily.relOut data m bat pc) (Tail.rel (multiplier data m bat) pc 0) := by
  apply Reduction.perfectCompleteness_of_run_support
  intro stmt p h x hx
  change x ∈ _root_.support (pure (some
    (((default : FullTranscript !p[]), (initialStatement data m bat stmt.1, stmt.2), p),
      (initialStatement data m bat stmt.1, stmt.2)))) at hx
  obtain rfl := OracleComp.eq_of_mem_support_pure _ hx
  exact ⟨_, rfl, (initialStatement_rel data m bat pc stmt.1 stmt.2 p).mpr h, rfl⟩

/-- Positive related output pins the exact reformatted input and unchanged oracles. -/
theorem adapter_positive_output {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl []ₒ (StateT σ ProbComp))
    (stmt : FullFamily.Output data m bat) (ost : ∀ j, pc.OStmt j)
    (tr : FullTranscript !p[]) (p : data.P⦃≤ 1⦄[X Fin m])
    (h : Pr[ fun out => (out, p) ∈ Tail.rel (multiplier data m bat) pc 0 |
      OptionT.mk do (simulateQ impl
        ((adapterVerifier data m bat pc).toVerifier.run (stmt, ost) tr)).run' (← init)] > 0) :
    ((initialStatement data m bat stmt, ost), p) ∈ Tail.rel (multiplier data m bat) pc 0 := by
  rw [gt_iff_lt, probEvent_pos_iff] at h
  obtain ⟨out, hout, hrel⟩ := h
  rw [OptionT.mem_support_iff] at hout
  change some out ∈ _root_.support (init >>= fun _ => pure (some
    (initialStatement data m bat stmt, ost))) at hout
  simp only [support_bind_const, support_pure, Set.mem_ofPred_eq] at hout
  obtain rfl := Option.some.inj hout.1
  exact hrel

/-- The packed polynomial is the witness at the only empty-protocol prefix. -/
abbrev AdapterWitness (_i : Fin 1) : Type := data.P⦃≤ 1⦄[X Fin m]

/-- The zero-round extractor preserves the same committed polynomial. -/
def adapterExtractor :
    Extractor.RoundByRound []ₒ (StmtIn := FullFamily.Output data m bat × (∀ j, pc.OStmt j))
      (WitIn := data.P⦃≤ 1⦄[X Fin m]) (WitOut := data.P⦃≤ 1⦄[X Fin m])
      (pSpec := !p[]) (WitMid := AdapterWitness data m) where
  eqIn := rfl
  extractMid j := nomatch j
  extractOut _ _ p := p

/-- Knowledge of the reformatted output reads back the full-family batched claim exactly. -/
def adapterKnowledgeStateFunction {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    (adapterVerifier data m bat pc).KnowledgeStateFunction init impl
      (FullFamily.relOut data m bat pc) (Tail.rel (multiplier data m bat) pc 0)
      (adapterExtractor data m bat pc) where
  toFun _ stmt _ p := (stmt, p) ∈ FullFamily.relOut data m bat pc
  toFun_empty _ _ := Iff.rfl
  toFun_next j := nomatch j
  toFun_full stmt tr p h := (initialStatement_rel data m bat pc stmt.1 stmt.2 p).mp
    (adapter_positive_output data m bat pc init impl stmt.1 stmt.2 tr p h)

/-- Reformatting a public claim uses no challenge and adds no knowledge error. -/
theorem adapter_rbrKnowledgeSoundnessWorstCaseWith {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    Verifier.rbrKnowledgeSoundnessWorstCaseWith init impl
      (FullFamily.relOut data m bat pc) (Tail.rel (multiplier data m bat) pc 0)
      (adapterVerifier data m bat pc).toVerifier (AdapterWitness data m)
      (adapterExtractor data m bat pc) (adapterKnowledgeStateFunction data m bat pc init impl)
      (fun _ => 0) := by
  intro _ j
  exact Fin.elim0 j.1

end RingSwitching.Packing.FullFamilyTail

/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.ProofSystem.Spartan.Algebra.Realization
public import ArkLib.ProofSystem.Component.CheckClaim
public import ArkLib.OracleReduction.Security.GuardedRoundByRound

/-!
# Spartan's terminal oracle verifier

The verifier queries the three matrix extensions at the row and column points and the witness
extension at the low column coordinates. The retained oracle family is unchanged.
-/

@[expose] public section

namespace Spartan.Terminal

open OracleComp OracleInterface ProtocolSpec Realization

variable {R : Type} [CommRing R] (pp : PublicParams)

/-- The executable matrix-extension oracle interface. -/
@[instance_reducible]
def matrixInterface (i : R1CS.MatrixIdx) :
    OracleInterface (R1CS.OracleStatement R pp.toSizeR1CS i) where
  Query := (Fin pp.ℓ_m → R) × (Fin pp.ℓ_n → R)
  toOC.spec := fun _ => R
  toOC.impl q := do return matrixEval (← read) q.1 q.2

/-- The executable witness-extension oracle interface. -/
@[instance_reducible]
def witnessInterface : OracleInterface (R1CS.Witness R pp.toSizeR1CS) where
  Query := Fin pp.ℓ_w → R
  toOC.spec := fun _ => R
  toOC.impl q := do return tableEval (← read) q

instance oracleInterface : ∀ i, OracleInterface (OracleStatement (R := R) pp i) := by
  letI : ∀ i, OracleInterface (R1CS.OracleStatement R pp.toSizeR1CS i) := matrixInterface pp
  letI : OracleInterface (R1CS.Witness R pp.toSizeR1CS) := witnessInterface pp
  exact fun i => OracleInterface.instRecType i

variable {ι : Type} (oSpec : OracleSpec ι) [DecidableEq R]

/-- Compute the second virtual evaluation with three matrix queries and one witness query. -/
def queryValue (stmt : FinalStatement (R := R) pp) :
    OracleComp [OracleStatement (R := R) pp]ₒ R := do
  let a ← query (spec := [OracleStatement (R := R) pp]ₒ) ⟨.inl .A, (stmt.r_x, stmt.r_y)⟩
  let b ← query (spec := [OracleStatement (R := R) pp]ₒ) ⟨.inl .B, (stmt.r_x, stmt.r_y)⟩
  let c ← query (spec := [OracleStatement (R := R) pp]ₒ) ⟨.inl .C, (stmt.r_x, stmt.r_y)⟩
  let w ← query (spec := [OracleStatement (R := R) pp]ₒ) ⟨.inr 0, witnessPoint pp stmt.r_y⟩
  return terminalValue pp stmt.x stmt.r_y stmt.ρ (fun i => match i with
    | .A => a | .B => b | .C => c) w

/-- The terminal verifier retains every matrix and witness oracle. -/
def finalVerifier : OracleVerifier oSpec (FinalStatement (R := R) pp)
    (OracleStatement (R := R) pp) Unit (OracleStatement (R := R) pp) !p[] where
  verify stmt _ := do
    let value ← (liftM (queryValue pp stmt) : OracleComp
      (oSpec + ([OracleStatement (R := R) pp]ₒ + [(!p[] : ProtocolSpec 0).Message]ₒ)) R)
    guard (value = stmt.e)
    return ()
  outputOracle := .inl (CheckClaim.outputEmbedding (OracleStatement (R := R) pp))

/-- The no-message prover forwards the retained oracle family. -/
def finalProver : OracleProver oSpec (FinalStatement (R := R) pp)
    (OracleStatement (R := R) pp) Unit Unit (OracleStatement (R := R) pp) Unit !p[] where
  PrvState := fun _ => (∀ i, OracleStatement (R := R) pp i)
  input := fun s => s.1.2
  sendMessage := fun i => nomatch i
  receiveChallenge := fun i => nomatch i
  output := fun o => pure (((), o), ())

/-- The terminal oracle reduction. -/
def finalReduction : OracleReduction oSpec (FinalStatement (R := R) pp)
    (OracleStatement (R := R) pp) Unit Unit (OracleStatement (R := R) pp) Unit !p[] where
  prover := finalProver pp oSpec
  verifier := finalVerifier pp oSpec

/-- The terminal input relation. -/
def relIn : Set (((FinalStatement (R := R) pp) ×
    (∀ i, OracleStatement (R := R) pp i)) × Unit) :=
  {s | terminalRelation pp s.1.1 s.1.2}

/-- The terminal output relation imposes no further check. -/
def relOut : Set ((Unit × (∀ i, OracleStatement (R := R) pp i)) × Unit) := Set.univ

/-- Materialized oracle identities are preserved. -/
theorem materializeOutput (o : ∀ i, OracleStatement (R := R) pp i)
    (tr : (!p[] : ProtocolSpec 0).FullTranscript) :
    (finalVerifier pp oSpec).materializeOutput tr.challenges o tr.messages = o := by
  rfl

omit [DecidableEq R] in
/-- The query program evaluates the semantic second virtual polynomial. -/
theorem queryValue_realizes (stmt : FinalStatement (R := R) pp)
    (o : ∀ i, OracleStatement (R := R) pp i) :
    simulateQ (simOracle0 (OracleStatement (R := R) pp) o) (queryValue pp stmt) =
      pure (MvPolynomial.eval stmt.r_y (Algebra.secondVirtual (fun i => o (.inl i))
        (R1CS.𝕫 stmt.x (o (.inr 0))) stmt.r_x stmt.ρ)) := by
  change pure (terminalValue pp stmt.x stmt.r_y stmt.ρ
    (fun i => match i with
      | .A => matrixEval (o (.inl .A)) stmt.r_x stmt.r_y
      | .B => matrixEval (o (.inl .B)) stmt.r_x stmt.r_y
      | .C => matrixEval (o (.inl .C)) stmt.r_x stmt.r_y)
    (tableEval (o (.inr 0)) (witnessPoint pp stmt.r_y))) =
    (pure (MvPolynomial.eval stmt.r_y (Algebra.secondVirtual (fun i => o (.inl i))
      (R1CS.𝕫 stmt.x (o (.inr 0))) stmt.r_x stmt.ρ)) : Id R)
  congr 1
  convert secondVirtual_realizes pp stmt.x (fun i => o (.inl i)) (o (.inr 0))
    stmt.r_x stmt.ρ stmt.r_y using 1
  congr 1
  funext i
  cases i <;> rfl

omit [DecidableEq R] in
/-- Lifting the terminal query program into the verifier preserves its evaluation. -/
theorem queryValue_lift_realizes (stmt : FinalStatement (R := R) pp)
    (o : ∀ i, OracleStatement (R := R) pp i)
    (messages : (!p[] : ProtocolSpec 0).Messages) :
    simulateQ (simOracle2 oSpec o messages)
        (liftM (queryValue pp stmt) : OracleComp
          (oSpec + ([OracleStatement (R := R) pp]ₒ + [(!p[] : ProtocolSpec 0).Message]ₒ)) R) =
      pure (MvPolynomial.eval stmt.r_y (Algebra.secondVirtual (fun i => o (.inl i))
        (R1CS.𝕫 stmt.x (o (.inr 0))) stmt.r_x stmt.ρ)) := by
  exact congrArg (fun v : R => (pure v : OracleComp oSpec R))
    (queryValue_realizes pp stmt o)

open Classical in
/-- The verifier accepts exactly the semantic terminal equation. -/
theorem finalVerifier_run_iff (stmt : FinalStatement (R := R) pp)
    (o : ∀ i, OracleStatement (R := R) pp i)
    (tr : (!p[] : ProtocolSpec 0).FullTranscript) :
    (finalVerifier pp oSpec).toVerifier.run (stmt, o) tr =
      if terminalRelation pp stmt o then pure ((), o) else failure := by
  simp only [Verifier.run, OracleVerifier.toVerifier, finalVerifier]
  erw [OptionT.run_bind, OptionT.run_monadLift]
  simp only [Option.elimM, bind_map_left]
  erw [simulateQ_bind]
  erw [queryValue_lift_realizes]
  simp only [pure_bind, Option.elim_some]
  unfold terminalRelation
  split_ifs <;> simp_all [guard] <;> rfl

/-- The terminal arithmetic evaluated against materialized oracle tables. -/
def checkValue (stmt : FinalStatement (R := R) pp)
    (o : ∀ i, OracleStatement (R := R) pp i) : R :=
  terminalValue pp stmt.x stmt.r_y stmt.ρ
    (fun i => matrixEval (o (.inl i)) stmt.r_x stmt.r_y)
    (tableEval (o (.inr 0)) (witnessPoint pp stmt.r_y))

omit [DecidableEq R] in
/-- The materialized arithmetic equals the semantic polynomial evaluation. -/
theorem checkValue_eq (stmt : FinalStatement (R := R) pp)
    (o : ∀ i, OracleStatement (R := R) pp i) :
    checkValue pp stmt o = MvPolynomial.eval stmt.r_y
      (Algebra.secondVirtual (fun i => o (.inl i))
        (R1CS.𝕫 stmt.x (o (.inr 0))) stmt.r_x stmt.ρ) :=
  secondVirtual_realizes pp stmt.x _ _ stmt.r_x stmt.ρ stmt.r_y

/-- Guarded form of the materialized terminal verifier. -/
def guardedForm : (finalVerifier (R := R) pp oSpec).toVerifier.GuardedForm where
  check s _ := decide (checkValue pp s.1 s.2 = s.1.e)
  out s _ := ((), s.2)
  verify_eq s tr := by
    classical
    rcases s with ⟨stmt, o⟩
    rw [show (finalVerifier pp oSpec).toVerifier.verify (stmt, o) tr =
      (finalVerifier pp oSpec).toVerifier.run (stmt, o) tr from rfl,
      finalVerifier_run_iff]
    simp only [checkValue_eq, terminalRelation, decide_eq_true_eq]
    split_ifs <;> simp_all

variable {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))

/-- A terminal knowledge state records the semantic terminal equation. -/
def knowledgeStateFunction :
    (finalVerifier (R := R) pp oSpec).toVerifier.KnowledgeStateFunction init impl
      (relIn pp) (relOut pp) Extractor.RoundByRound.unit where
  toFun _ s _ _ := terminalRelation pp s.1 s.2
  toFun_empty _ _ h := h
  toFun_next i := Fin.elim0 i
  toFun_full s tr _ h := by
    have hc := ((guardedForm pp oSpec).check_and_of_prEvent_pos h).1
    simpa only [guardedForm, decide_eq_true_eq, checkValue_eq, terminalRelation] using hc

/-- The unit extractor certifies the terminal verifier with fixed-prefix error zero. -/
theorem finalVerifier_rbrKnowledgeSoundnessWith :
    (finalVerifier (R := R) pp oSpec).toVerifier.rbrKnowledgeSoundnessWith init impl
      (relIn pp) (relOut pp) (fun _ => Unit) Extractor.RoundByRound.unit
      (knowledgeStateFunction pp oSpec init impl) (fun _ => 0) := by
  intro _ i
  exact Fin.elim0 i.1

/-- The terminal verifier has fixed-prefix round-by-round knowledge error zero. -/
theorem finalVerifier_rbrKnowledgeSoundness :
    (finalVerifier (R := R) pp oSpec).toVerifier.rbrKnowledgeSoundness init impl
      (relIn pp) (relOut pp) (fun _ => 0) := by
  exact ⟨fun _ => Unit, Extractor.RoundByRound.unit,
    knowledgeStateFunction pp oSpec init impl,
    finalVerifier_rbrKnowledgeSoundnessWith pp oSpec init impl⟩

/-- The terminal oracle reduction is perfectly complete for the semantic terminal equation. -/
theorem finalReduction_perfectCompleteness :
    (finalReduction (R := R) pp oSpec).perfectCompleteness init impl (relIn pp) (relOut pp) := by
  classical
  apply Reduction.perfectCompleteness_of_run_support
  intro s w h x hx
  have hs : terminalRelation pp s.1 s.2 := h
  have hp : (finalProver pp oSpec).run s w = pure (default, (((), s.2), ())) := by
    rfl
  have hv : (finalVerifier pp oSpec).toVerifier.run s default = pure ((), s.2) := by
    rcases s with ⟨stmt, o⟩
    rw [finalVerifier_run_iff, ite_eq_left hs]
  have hrun : ((finalReduction pp oSpec).toReduction.run s w).run =
      pure (some ((default, (((), s.2), ())), ((), s.2))) := by
    rw [Reduction.run_run_eq_bind]
    change (do
      let p ← (finalProver pp oSpec).run s w
      let out ← liftComp ((finalVerifier pp oSpec).toVerifier.run s p.1).run _
      pure (out.map (fun v => (p, v)))) = _
    rw [hp, pure_bind, hv]
    rfl
  rw [hrun, support_pure, Set.mem_singleton_iff] at hx
  subst x
  exact ⟨_, rfl, Set.mem_univ _, rfl⟩

end Spartan.Terminal

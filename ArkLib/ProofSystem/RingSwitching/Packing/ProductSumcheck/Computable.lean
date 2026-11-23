/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
module

public import ArkLib.ProofSystem.RingSwitching.Packing.ProductSumcheck.SeqCompose
public import ArkLib.OracleReduction.Composition.Sequential.General
public import ArkLib.OracleReduction.Composition.Sequential.IsPure
public import ArkLib.ProofSystem.Sumcheck.Impl.Representation
public import ArkLib.ToCompPoly.Multilinear.Basic
public import CompPoly.Univariate.ToPoly.Degree
public import Mathlib.Algebra.Polynomial.Degree.SmallDegree

/-!
# Product sumcheck over Boolean evaluation tables

The prover interpolates the two multilinear factors separately on each remaining
Boolean face, then sums their quadratic products. This uses no division, including in
characteristic two. The verifier evaluates the received coefficient array directly.
Interpreting each array as a polynomial preserves the verifier's decision on any
transcript, including transcripts that fail a check.
-/

@[expose] public section

namespace RingSwitching.Packing.ProductSumcheck.Computable

open CompPoly MvPolynomial
open OracleSpec OracleComp ProtocolSpec CoordinateWise.ScalarRound
open scoped BigOperators

variable {C Context : Type} [CommRing C] {m : ℕ}

@[no_expose] private def evalTableAt {n : ℕ}
    (table : (Fin n → Fin 2) → C) (r : Vector C n) : C :=
  CMlPolynomialEval.evalMle (.ofFn fun j => table (finFunctionFinEquiv.symm j)) r

/-- Evaluate a Boolean table by recursively interpolating its multilinear extension. -/
@[no_expose]
def evalTable {n : ℕ} (table : (Fin n → Fin 2) → C) (r : Fin n → C) : C :=
  evalTableAt table (.ofFn r)

/-- The runtime table evaluator agrees with the polynomial multilinear extension. -/
theorem evalTable_eq {n : ℕ} (table : (Fin n → Fin 2) → C) (r : Fin n → C) :
    evalTable table r = (MLE table).eval r := by
  rw [evalTable, evalTableAt, CMlPolynomialEval.eval_mle_eq_eval,
    CMlPolynomialEval.eval_eq_MvPolynomial_MLE]

private theorem evalTable_append_bool {n k : ℕ} (table : (Fin (n + k) → Fin 2) → C)
    (r : Fin n → C) (z : Fin k → Fin 2) :
    evalTable (fun b => table (Fin.append b z)) r =
      evalTable table (Fin.append r (z : Fin k → C)) := by
  rw [evalTable_eq, evalTable_eq, MLE_eval, MLE_eval, ← (Fin.appendEquiv n k).sum_comp]
  simp only [Fintype.sum_prod_type, Fin.appendEquiv_apply]
  refine Finset.sum_congr rfl fun b _ => ?_
  simp_rw [show ∀ y : Fin k → Fin 2, ((Fin.append b y : Fin (n + k) → Fin 2) :
      Fin (n + k) → C) = Fin.append (b : Fin n → C) (y : Fin k → C)
    from fun _ => (Fin.append_comp fun x : Fin 2 => (x : C)).symm, eqTilde_append]
  simp only [eqTilde, eqPolynomial_eval_zeroOne]
  rw [Finset.sum_eq_single z]
  · simp [Fin.appendEquiv]
  · intro y _ hy
    simp [Ne.symm hy]
  · simp

private theorem evalTable_append_cast {n k : ℕ} (h : m = n + k)
    (table : (Fin m → Fin 2) → C) (r : Fin n → C) (z : Fin k → Fin 2) :
    evalTable (fun b => table (Fin.append b z ∘ Fin.cast h)) r =
      evalTable table (Fin.append r (z : Fin k → C) ∘ Fin.cast h) := by
  subst m
  simpa using evalTable_append_bool table r z

/-- Evaluate only the challenge prefix of the Boolean face with fixed suffix. -/
@[no_expose] private def evalFace (i : ℕ) (hi : i ≤ m) (r : Vector C i)
    (x : Fin (m - i) → Fin 2)
    (table : (Fin m → Fin 2) → C) : C :=
  evalTableAt (fun b => table (Fin.append b x ∘ Fin.cast (by omega))) r

private theorem evalFace_eq (i : ℕ) (hi : i ≤ m) (r : Fin i → C) (x : Fin (m - i) → Fin 2)
    (table : (Fin m → Fin 2) → C) :
    evalFace i hi (Vector.ofFn r) x table = (MLE table).eval (hypercubePoint m i r x) := by
  change evalTable (fun b => table (Fin.append b x ∘ Fin.cast (by omega))) r = _
  rw [evalTable_append_cast, evalTable_eq, hypercubePoint_eq_append m i hi]

section Prover
variable [BEq C] [LawfulBEq C]

/-- The affine polynomial with given values at 0 and 1. -/
@[no_expose] private def affine (a b : C) : CPolynomial C :=
  CPolynomial.ofFn ![a, b - a]

private theorem affine_toPoly (a b : C) :
    (affine a b).toPoly = Polynomial.C (b - a) * Polynomial.X + Polynomial.C a := by
  ext (_ | _ | j)
  · simp [affine, ← CPolynomial.coeff_toPoly, CPolynomial.coeff_ofFn]
  · simp [affine, ← CPolynomial.coeff_toPoly, CPolynomial.coeff_ofFn]
  · simp [affine, ← CPolynomial.coeff_toPoly, CPolynomial.coeff_ofFn,
      show ¬j + 1 + 1 < 2 by omega]

private theorem affine_degree (a b : C) : (affine a b).degree ≤ 1 := by
  rw [CPolynomial.degree_le_iff_coeff_zero]
  intro k hk
  have : ¬k < 2 := by
    have : 1 < k := WithBot.coe_lt_coe.mp hk
    omega
  simp [affine, CPolynomial.coeff_ofFn, this]

/-- The restriction of a multilinear factor to the free coordinate of a Boolean face. -/
@[no_expose] private def factor (i : Fin m) (table : (Fin m → Fin 2) → C) (r : Vector C i)
    (x : Fin (m - (i + 1)) → Fin 2) : CPolynomial C :=
  let face (b : Fin 2) : Fin (m - i) → Fin 2 :=
    Fin.cons b x ∘ finCongr (by omega)
  affine (evalFace i i.isLt.le r (face 0) table) (evalFace i i.isLt.le r (face 1) table)

/-- The honest quadratic message from the Boolean tables of the two multilinear factors.
All suffix faces reuse one materialized challenge prefix. -/
@[no_expose]
def roundMessage (i : Fin m) (a p : (Fin m → Fin 2) → C) (r : Fin i → C) :
    Sumcheck.Impl.Representation.Message C 2 :=
  let prefixPoint := Vector.ofFn r
  ⟨∑ x, factor i a prefixPoint x * factor i p prefixPoint x, by
    rw [CPolynomial.degree_toPoly, CPolynomial.toPoly_sum, ← Polynomial.mem_degreeLE]
    refine Submodule.sum_mem _ fun x _ => Polynomial.mem_degreeLE.mpr ?_
    rw [← CPolynomial.degree_toPoly]
    apply (CPolynomial.degree_mul_le _ _).trans
    exact (add_le_add (affine_degree _ _) (affine_degree _ _)).trans_eq (by norm_num)⟩

private theorem affine_eq (q : Polynomial C) (hq : q.degree ≤ 1) :
    (affine (q.eval 0) (q.eval 1)).toPoly = q := by
  rw [affine_toPoly]
  have h0 : q.eval 0 = q.coeff 0 := q.coeff_zero_eq_eval_zero.symm
  have h1 : q.eval 1 = q.coeff 1 + q.coeff 0 := by
    conv_lhs => rw [Polynomial.eq_X_add_C_of_degree_le_one hq]
    simp
  rw [h0, h1, add_sub_cancel_right]
  exact (Polynomial.eq_X_add_C_of_degree_le_one hq).symm

private theorem factor_toPoly {n : ℕ} (i : Fin (n + 1)) (table : (Fin (n + 1) → Fin 2) → C)
    (r : Fin i → C) (x : Fin (n + 1 - (i + 1)) → Fin 2) :
    (factor i table (Vector.ofFn r) x).toPoly =
      (MLE table).evalExcept i (hypercubeSuffix i r x) := by
  unfold factor
  simp only [evalFace_eq, hypercubePoint_cons, Fin.val_zero, Nat.cast_zero, Fin.val_one,
    Nat.cast_one]
  have hpoint (t : C) :
      (MLE table).eval (hypercubePoint (n + 1) (i + 1) (Fin.snoc r t) x) =
        ((MLE table).evalExcept i (hypercubeSuffix i r x)).eval t := by
    rw [eval_evalExcept, hypercubeSuffix, Fin.insertNth_append_cast i r _ t (by omega),
      hypercubePoint_eq_append _ _ i.isLt]
  rw [hpoint, hpoint]
  exact affine_eq _ (Polynomial.mem_degreeLE.mp
    (evalExcept_mem_degreeLE i _ (MLE_mem_restrictDegree table)))

omit [BEq C] [LawfulBEq C] in
private theorem table_MLE_eq_map {P : Type} [CommRing P] [Algebra P C]
    (p : (Fin m → Fin 2) → C) (Q : P⦃≤ 1⦄[X Fin m])
    (hp : ∀ b, p b = aeval (b : Fin m → C) Q.val) :
    MLE p = map (algebraMap P C) Q.val := by
  apply Eq.symm
  refine eq_MLE_of_degreeOf_le_one_of_eval_zeroOne_eq p _ (fun j => ?_) (fun b => ?_)
  · exact degreeOf_le_iff.mpr fun _ h => Q.property (support_map_subset _ _ h) j
  · rw [hp b, eval_map, aeval_def]

/-- The honest runtime message interprets as the specified degree-two round polynomial. -/
theorem roundMessage_toMessage {P : Type} [CommRing P] [Algebra P C]
    (i : Fin m) (a p : (Fin m → Fin 2) → C) (r : Fin i → C)
    (A : C⦃≤ 1⦄[X Fin m]) (Q : P⦃≤ 1⦄[X Fin m])
    (ha : ∀ b, a b = A.val.eval (b : Fin m → C))
    (hp : ∀ b, p b = aeval (b : Fin m → C) Q.val) :
    Sumcheck.Impl.Representation.toMessage C 2 (roundMessage i a p r) =
      ProductSumcheck.roundMessage i (productPoly A Q) r := by
  have ha' : MLE a = A.val :=
    (eq_MLE_of_degreeOf_le_one_of_eval_zeroOne_eq a A.val
      ((mem_restrictDegree_iff_degreeOf_le _ _).mp A.property)
      fun b => (ha b).symm).symm
  have hp' := table_MLE_eq_map p Q hp
  cases m with
  | zero => exact i.elim0
  | succ n =>
    apply Subtype.ext
    rw [Sumcheck.Impl.Representation.toMessage_val]
    change (∑ x, factor i a (Vector.ofFn r) x * factor i p (Vector.ofFn r) x).toPoly =
      ∑ x, (A.val * map (algebraMap P C) Q.val).evalExcept i (hypercubeSuffix i r x)
    rw [CPolynomial.toPoly_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [CPolynomial.toPoly_mul, factor_toPoly, factor_toPoly, ha', hp']
    simp only [evalExcept_eq_eval₂_insertNth, eval₂_mul]

end Prover

section Verifier
variable [BEq C]

/-- Test the sum of the message's Boolean evaluations against the current claim. -/
def roundCheck (i : Fin m) (stmt : Statement Context C i.castSucc)
    (g : Sumcheck.Impl.Representation.Message C 2) : Bool :=
  let eval := Sumcheck.Impl.Representation.evaluate C 2 g
  eval 0 + eval 1 == stmt.target

/-- Extend the prefix by the challenge and set the target to the message's evaluation. -/
def roundNext (i : Fin m) (stmt : Statement Context C i.castSucc)
    (g : Sumcheck.Impl.Representation.Message C 2) (c : C) : Statement Context C i.succ :=
  ⟨stmt.ctx, Fin.snoc stmt.challenges c, Sumcheck.Impl.Representation.evaluate C 2 g c⟩

/-- Check the two Boolean evaluations and, on acceptance, append the challenge. -/
def verifyRound (i : Fin m) (stmt : Statement Context C i.castSucc)
    (g : Sumcheck.Impl.Representation.Message C 2) (c : C) : Option (Statement Context C i.succ) :=
  if roundCheck i stmt g then some (roundNext i stmt g c) else none

open scoped Classical in
/-- Decoding any executable message preserves the round's guard and next statement. -/
theorem verifyRound_eq [LawfulBEq C] (i : Fin m) (stmt : Statement Context C i.castSucc)
    (g : Sumcheck.Impl.Representation.Message C 2) (c : C) :
    let g' := Sumcheck.Impl.Representation.toMessage C 2 g
    verifyRound i stmt g c =
      if Round.check i stmt g' then
        some (Round.nextStatement i stmt g' c)
      else none := by
  simp only [verifyRound, roundCheck, roundNext, Round.check, Round.nextStatement, beq_iff_eq,
    Sumcheck.Impl.Representation.evaluate_eq]
  split <;> rename_i h <;> simp [h]

/-- Test the terminal product at the complete challenge point. -/
def terminalCheck (evaluateMultiplier : Context → (Fin m → C) → C)
    (stmt : Statement Context C (Fin.last m)) (v : C) : Bool :=
  stmt.target == evaluateMultiplier stmt.ctx stmt.challenges * v

/-- Check the terminal multiplication and forward the same evaluation claim on acceptance. -/
def verifyTerminal (evaluateMultiplier : Context → (Fin m → C) → C)
    (stmt : Statement Context C (Fin.last m)) (v : C) : Option (Context × ((Fin m → C) × C)) :=
  if terminalCheck evaluateMultiplier stmt v then
    some (Terminal.nextStatement stmt v)
  else none

open scoped Classical in
/-- A runtime multiplier evaluator with the specified values preserves the terminal decision. -/
theorem verifyTerminal_eq [LawfulBEq C] (evaluateMultiplier : Context → (Fin m → C) → C)
    (multiplier : Sumcheck.Structured.Multiplier Context C m)
    (h : ∀ ctx r, evaluateMultiplier ctx r = multiplier.evaluate ctx r)
    (stmt : Statement Context C (Fin.last m)) (v : C) :
    verifyTerminal evaluateMultiplier stmt v =
      if Terminal.check multiplier stmt v then some (Terminal.nextStatement stmt v) else none := by
  simp only [verifyTerminal, terminalCheck, Terminal.check, beq_iff_eq, h]
  split <;> rename_i hguard <;> simp [hguard]

end Verifier

/-- The terminal prover evaluates the packed table at the final challenge point. -/
def terminalMessage (p : (Fin m → Fin 2) → C) (stmt : Statement Context C (Fin.last m)) : C :=
  evalTable p stmt.challenges

/-- The packed table evaluates to the terminal message of the polynomial prover. -/
theorem terminalMessage_eq {P : Type} [CommRing P] [Algebra P C]
    (p : (Fin m → Fin 2) → C) (Q : P⦃≤ 1⦄[X Fin m])
    (hp : ∀ b, p b = aeval (b : Fin m → C) Q.val)
    (stmt : Statement Context C (Fin.last m)) :
    terminalMessage p stmt = aeval stmt.challenges Q.val := by
  rw [terminalMessage, evalTable_eq, table_MLE_eq_map p Q hp, eval_map, aeval_def]

section Honest
variable {P : Type} [CommRing P] [Algebra P C] [BEq C] [LawfulBEq C]
  (multiplier : Sumcheck.Structured.Multiplier Context C m) (pc : PackedCommitment P m)

/-- With correctly represented factors, an honest round succeeds in the next residual relation. -/
theorem verifyRound_honest (i : Fin m) (stmt : Statement Context C i.castSucc)
    (ost : ∀ j, pc.OStmt j) (Q : P⦃≤ 1⦄[X Fin m]) (c : C)
    (a p : (Fin m → Fin 2) → C)
    (ha : ∀ b, a b = (multiplier stmt.ctx).val.eval (b : Fin m → C))
    (hp : ∀ b, p b = aeval (b : Fin m → C) Q.val)
    (hrel : ((stmt, ost), Q) ∈ rel multiplier pc i.castSucc) :
    let out := Round.nextStatement i stmt (Round.honestMessage multiplier i stmt Q) c
    verifyRound i stmt (roundMessage i a p stmt.challenges) c = some out ∧
      ((out, ost), Q) ∈ rel multiplier pc i.succ := by
  refine ⟨?_, Round.nextStatement_mem_rel multiplier pc i hrel c⟩
  rw [verifyRound_eq]
  rw [roundMessage_toMessage i a p stmt.challenges (multiplier stmt.ctx) Q ha hp]
  exact ite_eq_left (Round.check_honestMessage_of_mem_rel multiplier pc i hrel)

/-- The honest terminal message is accepted at the original commitment's evaluation relation. -/
theorem verifyTerminal_honest (evaluateMultiplier : Context → (Fin m → C) → C)
    (hEvaluate : ∀ ctx r, evaluateMultiplier ctx r = multiplier.evaluate ctx r)
    (stmt : Statement Context C (Fin.last m)) (ost : ∀ j, pc.OStmt j)
    (Q : P⦃≤ 1⦄[X Fin m]) (p : (Fin m → Fin 2) → C)
    (hp : ∀ b, p b = aeval (b : Fin m → C) Q.val)
    (hrel : ((stmt, ost), Q) ∈ rel multiplier pc (Fin.last m)) :
    let out := Terminal.nextStatement stmt (aeval stmt.challenges Q.val)
    verifyTerminal evaluateMultiplier stmt (terminalMessage p stmt) = some out ∧
      ((out, ost), Q) ∈ pc.evalRelWithContext Context := by
  refine ⟨?_, Terminal.nextStatement_mem_evalRelWithContext multiplier pc hrel⟩
  rw [terminalMessage_eq p Q hp stmt, verifyTerminal_eq _ multiplier hEvaluate]
  exact ite_eq_left (Terminal.check_aeval_of_mem_rel multiplier pc hrel)

end Honest

/-! ## Oracle reductions -/

/-- A clear quadratic coefficient array followed by one scalar challenge. -/
abbrev roundPSpec (C : Type) [CommRing C] : ProtocolSpec 2 :=
  pSpecScalar (Sumcheck.Impl.Representation.Message C 2) C

instance : ∀ j, OracleInterface ((roundPSpec C).Message j) :=
  letI : OracleInterface (Sumcheck.Impl.Representation.Message C 2) := OracleInterface.instDefault
  inferInstance

instance [SampleableType C] : ∀ j, SampleableType ((roundPSpec C).Challenge j)
  | ⟨0, h⟩ => nomatch h
  | ⟨1, _⟩ => inferInstanceAs (SampleableType C)

section OracleRounds
variable {ι : Type} (OStmt : ι → Type)

/-- The first-round input, the sent message, and then the verifier's challenge. -/
def RoundState (i : Fin m) : Fin 3 → Type
  | ⟨0, _⟩ => (Statement Context C i.castSucc × (∀ j, OStmt j)) × ((Fin m → Fin 2) → C)
  | ⟨1, _⟩ =>
      ((Statement Context C i.castSucc × (∀ j, OStmt j)) × ((Fin m → Fin 2) → C)) ×
        Sumcheck.Impl.Representation.Message C 2
  | ⟨2, _⟩ =>
      (((Statement Context C i.castSucc × (∀ j, OStmt j)) × ((Fin m → Fin 2) → C)) ×
        Sumcheck.Impl.Representation.Message C 2) × C

/-- Send the honest quadratic and retain the same packed table and oracles. -/
def roundProver [BEq C] [LawfulBEq C] (i : Fin m) (a : Context → (Fin m → Fin 2) → C) :
    OracleProver []ₒ (Statement Context C i.castSucc) OStmt ((Fin m → Fin 2) → C)
      (Statement Context C i.succ) OStmt ((Fin m → Fin 2) → C) (roundPSpec C) where
  PrvState := RoundState OStmt i
  input := id
  sendMessage
    | ⟨0, _⟩ => fun st =>
      let g := roundMessage i (a st.1.1.ctx) st.2 st.1.1.challenges
      pure (g, (st, g))
    | ⟨1, h⟩ => fun _ => nomatch h
  receiveChallenge
    | ⟨0, h⟩ => nomatch h
    | ⟨1, _⟩ => fun st => pure fun c => (st, c)
  output := fun ((((stmt, ost), p), g), c) => pure ((roundNext i stmt g c, ost), p)

/-- Send the final table evaluation and retain the same packed table and oracles. -/
def terminalProver :
    OracleProver []ₒ (Statement Context C (Fin.last m)) OStmt ((Fin m → Fin 2) → C)
      (Context × ((Fin m → C) × C)) OStmt ((Fin m → Fin 2) → C) (Terminal.pSpec C) where
  PrvState
    | ⟨0, _⟩ =>
        (Statement Context C (Fin.last m) × (∀ j, OStmt j)) × ((Fin m → Fin 2) → C)
    | ⟨1, _⟩ =>
        ((Statement Context C (Fin.last m) × (∀ j, OStmt j)) × ((Fin m → Fin 2) → C)) × C
  input := id
  sendMessage
    | ⟨0, _⟩ => fun st =>
      let v := terminalMessage st.2 st.1.1
      pure (v, (st, v))
  receiveChallenge
    | ⟨0, h⟩ => nomatch h
  output := fun (((stmt, ost), p), v) => pure ((Terminal.nextStatement stmt v, ost), p)

instance [BEq C] [LawfulBEq C] (i : Fin m) (a : Context → (Fin m → Fin 2) → C) :
    (roundProver OStmt i a).OutputIsPure where
  output_is_pure := ⟨fun ((((stmt, ost), p), g), c) => ((roundNext i stmt g c, ost), p),
    fun _ => rfl⟩

instance : (terminalProver (C := C) (Context := Context) (m := m) OStmt).OutputIsPure where
  output_is_pure := ⟨fun (((stmt, ost), p), v) => ((Terminal.nextStatement stmt v, ost), p),
    fun _ => rfl⟩

variable [∀ j, OracleInterface (OStmt j)] [BEq C]

/-- Check the received quadratic before extending the prefix; pass the original oracles through. -/
def roundVerifier (i : Fin m) :
    OracleVerifier []ₒ (Statement Context C i.castSucc) OStmt
      (Statement Context C i.succ) OStmt (roundPSpec C) :=
  scalarRoundOracleVerifier (fun stmt g => roundCheck i stmt g = true) (roundNext i)

/-- Run one product-sumcheck round, forwarding the original oracle family and packed table. -/
def roundReduction [LawfulBEq C] (i : Fin m) (a : Context → (Fin m → Fin 2) → C) :
    OracleReduction []ₒ (Statement Context C i.castSucc) OStmt ((Fin m → Fin 2) → C)
      (Statement Context C i.succ) OStmt ((Fin m → Fin 2) → C) (roundPSpec C) :=
  ⟨roundProver OStmt i a, roundVerifier OStmt i⟩

/-- Check the terminal product before delivering the evaluation claim on the same oracles. -/
def terminalVerifier (evaluateMultiplier : Context → (Fin m → C) → C) :
    OracleVerifier []ₒ (Statement Context C (Fin.last m)) OStmt
      (Context × ((Fin m → C) × C)) OStmt (Terminal.pSpec C) :=
  messageRoundOracleVerifier (fun stmt v => terminalCheck evaluateMultiplier stmt v = true)
    Terminal.nextStatement

/-- Run the terminal check and forward the original oracle family and packed table. -/
def terminalReduction (evaluateMultiplier : Context → (Fin m → C) → C) :
    OracleReduction []ₒ (Statement Context C (Fin.last m)) OStmt ((Fin m → Fin 2) → C)
      (Context × ((Fin m → C) × C)) OStmt ((Fin m → Fin 2) → C) (Terminal.pSpec C) :=
  ⟨terminalProver OStmt, terminalVerifier OStmt evaluateMultiplier⟩

/-- The materialized round verifier makes the same decision as the explicit-message API. -/
theorem roundVerifier_verify (i : Fin m) (stmt : Statement Context C i.castSucc)
    (ost : ∀ j, OStmt j) (g : Sumcheck.Impl.Representation.Message C 2) (c : C) :
    (roundVerifier OStmt i).toVerifier.verify (stmt, ost) (FullTranscript.mk2 g c) =
      match verifyRound i stmt g c with
      | some out => pure (out, ost)
      | none => failure := by
  have h := (scalarRoundOracleVerifierGuardedForm (oSpec := []ₒ) (OStmt := OStmt)
    (fun s q => roundCheck i s q = true) (roundNext i)).verify_eq
      (stmt, ost) (FullTranscript.mk2 g c)
  rw [scalarRoundOracleVerifierGuardedForm_check, scalarRoundOracleVerifierGuardedForm_out] at h
  rw [roundVerifier]
  convert h using 1
  by_cases hc : roundCheck i stmt g = true <;> simp [verifyRound, hc]

/-- The materialized terminal verifier checks the sent evaluation and forwards the same oracles. -/
theorem terminalVerifier_verify (evaluateMultiplier : Context → (Fin m → C) → C)
    (stmt : Statement Context C (Fin.last m)) (ost : ∀ j, OStmt j) (v : C) :
    (terminalVerifier OStmt evaluateMultiplier).toVerifier.verify (stmt, ost)
        (Terminal.transcript v) =
      match verifyTerminal evaluateMultiplier stmt v with
      | some out => pure (out, ost)
      | none => failure := by
  have h := (messageRoundOracleVerifierGuardedForm (oSpec := []ₒ) (OStmt := OStmt)
    (fun s v => terminalCheck evaluateMultiplier s v = true) Terminal.nextStatement).verify_eq
      (stmt, ost) (Terminal.transcript v)
  erw [messageRoundOracleVerifierGuardedForm_check, messageRoundOracleVerifierGuardedForm_out] at h
  rw [terminalVerifier]
  convert h using 1
  · rfl
  · by_cases hc : terminalCheck evaluateMultiplier stmt v = true <;>
      simp [verifyTerminal, Terminal.transcript, FullTranscript.messages, hc]

end OracleRounds

/-! ## Sequential tail -/

/-- The dependent sequence of quadratic arrays and scalar challenges. -/
abbrev tailLoopPSpec (C : Type) [CommRing C] (m : ℕ) :
    ProtocolSpec (Fin.vsum (fun _ : Fin m => 2)) :=
  ProtocolSpec.seqCompose (fun _ : Fin m => roundPSpec C)

/-- The scalar rounds followed by the final packed evaluation. -/
abbrev tailPSpec (C : Type) [CommRing C] (m : ℕ) :
    ProtocolSpec (Fin.vsum (fun _ : Fin m => 2) + 1) := tailLoopPSpec C m ++ₚ Terminal.pSpec C

section Tail
variable {ι : Type} (OStmt : ι → Type) [∀ j, OracleInterface (OStmt j)] [BEq C] [LawfulBEq C]
  (a : Context → (Fin m → Fin 2) → C) (evaluateMultiplier : Context → (Fin m → C) → C)

/-- The executable scalar rounds, preserving the packed table and its oracles. -/
def tailLoopReduction :
    OracleReduction []ₒ (Statement Context C (0 : Fin (m + 1))) OStmt ((Fin m → Fin 2) → C)
      (Statement Context C (Fin.last m)) OStmt ((Fin m → Fin 2) → C) (tailLoopPSpec C m) :=
  OracleReduction.seqCompose (Statement Context C) (fun _ => OStmt)
    (fun _ => (Fin m → Fin 2) → C) (fun i => roundReduction OStmt i a)

/-- Compose the executable rounds and terminal check, including the zero-round case. -/
def tailReduction :
    OracleReduction []ₒ (Statement Context C (0 : Fin (m + 1))) OStmt ((Fin m → Fin 2) → C)
      (Context × ((Fin m → C) × C)) OStmt ((Fin m → Fin 2) → C) (tailPSpec C m) :=
  (tailLoopReduction OStmt a).append (terminalReduction OStmt evaluateMultiplier)

instance : (tailLoopReduction OStmt a).prover.OutputIsPure :=
  Prover.OutputIsPure.seqCompose
    (fun i => Statement Context C i × (∀ j, OStmt j))
    (fun _ => (Fin m → Fin 2) → C) (roundProver OStmt · a) (fun _ => inferInstance)

instance : (tailReduction OStmt a evaluateMultiplier).prover.OutputIsPure :=
  Prover.OutputIsPure.append _ _
    (show (tailLoopReduction OStmt a).prover.OutputIsPure from inferInstance)
    (show (terminalProver OStmt).OutputIsPure from inferInstance)

/-- The scalar rounds and terminal verifier return the unchanged commitment oracle family. -/
theorem tailReduction_materializeOutput (challenges : (tailPSpec C m).Challenges)
    (ost : ∀ j, OStmt j) (messages : (tailPSpec C m).Messages) :
    (tailReduction OStmt a evaluateMultiplier).verifier.materializeOutput challenges ost messages =
      ost := by
  change ((tailLoopReduction OStmt a).verifier.append
    (terminalVerifier OStmt evaluateMultiplier)).materializeOutput challenges ost messages = ost
  rw [OracleVerifier.append_materializeOutput]
  change (tailLoopReduction OStmt a).verifier.materializeOutput
    challenges.fst ost messages.fst = ost
  exact OracleVerifier.seqCompose_materializeOutput (Statement Context C) OStmt
    (roundVerifier OStmt) (fun _ _ _ _ => rfl) _ _ _

end Tail

/-! ## Verifier correspondence -/

section Correspondence
variable [BEq C] [LawfulBEq C]

/-- Interpret a quadratic coefficient array on the legacy wire, leaving the challenge intact. -/
def decodeRoundTranscript (tr : (roundPSpec C).FullTranscript) :
    (Round.pSpec C).FullTranscript :=
  FullTranscript.mk2 (Sumcheck.Impl.Representation.toMessage C 2 (tr 0)) (tr 1)

/-- The challenge at the second entry is unchanged by round decoding. -/
theorem decodeRoundTranscript_challenge
    (tr : (roundPSpec C).FullTranscript) : (decodeRoundTranscript tr) 1 = tr 1 := rfl

/-- Decode each scalar-round message and keep the original sequence of challenges. -/
def decodeLoopTranscript (tr : (tailLoopPSpec C m).FullTranscript) :
    (ProductSumcheck.loopSpec C m).FullTranscript :=
  FullTranscript.seqCompose (pSpec := fun _ : Fin m => Round.pSpec C)
    fun i => decodeRoundTranscript
      (FullTranscript.component (pSpec := fun _ : Fin m => roundPSpec C) tr i)

/-- The loop transports each component independently, with no reordering. -/
theorem decodeLoopTranscript_component (tr : (tailLoopPSpec C m).FullTranscript) (i : Fin m) :
    FullTranscript.component (pSpec := fun _ : Fin m => Round.pSpec C)
      (decodeLoopTranscript tr) i =
      decodeRoundTranscript
        (FullTranscript.component (pSpec := fun _ : Fin m => roundPSpec C) tr i) := by
  funext j
  simp only [FullTranscript.component, decodeLoopTranscript, FullTranscript.seqCompose_embedSum,
    cast_cast, cast_eq]

/-- Decode the scalar-round messages, keeping the final packed evaluation unchanged. -/
def decodeTailTranscript (tr : (tailPSpec C m).FullTranscript) :
    (ProductSumcheck.pSpec C m).FullTranscript :=
  decodeLoopTranscript tr.fst ++ₜ tr.snd

/-- Decoding preserves the terminal transcript verbatim. -/
theorem decodeTailTranscript_snd (tr : (tailPSpec C m).FullTranscript) :
    (decodeTailTranscript tr).snd = tr.snd :=
  FullTranscript.append_snd (decodeLoopTranscript tr.fst) tr.snd

private theorem seqCompose_verify_eq {k : ℕ} (S : Fin (k + 1) → Type)
    {n : Fin k → ℕ} {ps qs : ∀ i, ProtocolSpec (n i)}
    (V : (i : Fin k) → Verifier []ₒ (S i.castSucc) (S i.succ) (ps i))
    (W : (i : Fin k) → Verifier []ₒ (S i.castSucc) (S i.succ) (qs i))
    (ts : ∀ i, (ps i).FullTranscript) (us : ∀ i, (qs i).FullTranscript)
    (h : ∀ i s, (V i).verify s (ts i) = (W i).verify s (us i))
    (s : S 0) :
    (Verifier.seqCompose S V).verify s (FullTranscript.seqCompose ts) =
      (Verifier.seqCompose S W).verify s (FullTranscript.seqCompose us) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [Verifier.seqCompose_succ, FullTranscript.seqCompose_succ_eq_append,
      Verifier.append, FullTranscript.append_fst, FullTranscript.append_snd]
    erw [h 0]
    congr 1
    funext s
    exact ih (S ∘ Fin.succ) (fun i => V i.succ) (fun i => W i.succ)
      (fun i => ts i.succ) (fun i => us i.succ) (fun i => h i.succ) s

variable {P : Type} [CommRing P] [Algebra P C] (pc : PackedCommitment P m)

omit [Algebra P C] in
private theorem roundVerifier_compare (i : Fin m) (stmt : Statement Context C i.castSucc)
    (ost : ∀ j, pc.OStmt j) (tr : (roundPSpec C).FullTranscript) :
    (roundVerifier pc.OStmt i).toVerifier.verify (stmt, ost) tr =
      (Round.verifier pc i).toVerifier.verify (stmt, ost) (decodeRoundTranscript tr) := by
  classical
  have htr : FullTranscript.mk2 (pSpec := roundPSpec C) (tr 0) (tr 1) = tr := by
    funext j
    fin_cases j <;> rfl
  conv_lhs => rw [← htr]
  rw [roundVerifier_verify, verifyRound_eq, Round.verifier_verify]
  change (match (if Round.check i stmt (Sumcheck.Impl.Representation.toMessage C 2 (tr 0))
    then some (Round.nextStatement i stmt (Sumcheck.Impl.Representation.toMessage C 2 (tr 0))
      (tr 1)) else none) with
    | some out => pure (out, ost)
    | none => failure) =
    if Round.check i stmt (Sumcheck.Impl.Representation.toMessage C 2 (tr 0)) then
      pure (Round.nextStatement i stmt (Sumcheck.Impl.Representation.toMessage C 2 (tr 0))
        (tr 1), ost) else failure
  by_cases hc : Round.check i stmt (Sumcheck.Impl.Representation.toMessage C 2 (tr 0)) <;>
    simp [hc]

omit [Algebra P C] in
private theorem terminalVerifier_compare
    (evaluateMultiplier : Context → (Fin m → C) → C)
    (multiplier : Sumcheck.Structured.Multiplier Context C m)
    (hEvaluate : ∀ ctx r, evaluateMultiplier ctx r = multiplier.evaluate ctx r)
    (stmt : Statement Context C (Fin.last m)) (ost : ∀ j, pc.OStmt j)
    (tr : (Terminal.pSpec C).FullTranscript) :
    (terminalVerifier pc.OStmt evaluateMultiplier).toVerifier.verify (stmt, ost) tr =
      (Terminal.verifier multiplier pc).toVerifier.verify (stmt, ost) tr := by
  classical
  have htr : Terminal.transcript (C := C) (tr 0) = tr := by
    funext j
    fin_cases j
    rfl
  rw [← htr]
  erw [terminalVerifier_verify, verifyTerminal_eq _ multiplier hEvaluate,
    Terminal.verifier_verify]
  change (match (if Terminal.check multiplier stmt (tr 0)
    then some (Terminal.nextStatement stmt (tr 0)) else none) with
    | some out => pure (out, ost)
    | none => failure) =
    if Terminal.check multiplier stmt (tr 0) then pure (Terminal.nextStatement stmt (tr 0), ost)
    else failure
  by_cases hc : Terminal.check multiplier stmt (tr 0) <;> simp [hc]

omit [Algebra P C] in
private theorem tailLoopReduction_verify_eq (a : Context → (Fin m → Fin 2) → C)
    (stmt : Statement Context C (0 : Fin (m + 1))) (ost : ∀ j, pc.OStmt j)
    (tr : (tailLoopPSpec C m).FullTranscript) :
    (tailLoopReduction pc.OStmt a).verifier.toVerifier.verify (stmt, ost) tr =
      (ProductSumcheck.loopVerifier pc).toVerifier.verify (stmt, ost)
        (decodeLoopTranscript tr) := by
  rw [tailLoopReduction, OracleReduction.seqCompose, OracleVerifier.seqCompose_toVerifier,
    ProductSumcheck.loopVerifier_toVerifier]
  have h := seqCompose_verify_eq (fun i => Statement Context C i × (∀ j, pc.OStmt j))
    (fun i => (roundVerifier pc.OStmt i).toVerifier) (fun i => (Round.verifier pc i).toVerifier)
    (FullTranscript.component (pSpec := fun _ : Fin m => roundPSpec C) tr)
    (fun i => decodeRoundTranscript
      (FullTranscript.component (pSpec := fun _ : Fin m => roundPSpec C) tr i))
    (fun i s => roundVerifier_compare pc i s.1 s.2 _) (stmt, ost)
  simpa only [FullTranscript.seqCompose_component, roundReduction, decodeLoopTranscript] using h

omit [Algebra P C] in
/-- The decoded transcript gives exactly the same verdict, including rejection and oracle output. -/
theorem tailReduction_verify_eq (a : Context → (Fin m → Fin 2) → C)
    (evaluateMultiplier : Context → (Fin m → C) → C)
    (multiplier : Sumcheck.Structured.Multiplier Context C m)
    (hEvaluate : ∀ ctx r, evaluateMultiplier ctx r = multiplier.evaluate ctx r)
    (stmt : Statement Context C (0 : Fin (m + 1))) (ost : ∀ j, pc.OStmt j)
    (tr : (tailPSpec C m).FullTranscript) :
    (tailReduction pc.OStmt a evaluateMultiplier).verifier.toVerifier.verify (stmt, ost) tr =
      (ProductSumcheck.verifier multiplier pc).toVerifier.verify (stmt, ost)
        (decodeTailTranscript tr) := by
  change ((tailLoopReduction pc.OStmt a).verifier.append
    (terminalVerifier pc.OStmt evaluateMultiplier)).toVerifier.verify (stmt, ost) tr = _
  rw [OracleVerifier.append_toVerifier, ProductSumcheck.verifier_toVerifier]
  simp only [Verifier.append, decodeTailTranscript, FullTranscript.append_fst,
    FullTranscript.append_snd]
  rw [tailLoopReduction_verify_eq pc]
  congr 1
  funext s
  exact terminalVerifier_compare pc evaluateMultiplier multiplier hEvaluate s.1 s.2 _

end Correspondence

/-! ## Local prover correspondence -/

section ProverCorrespondence
variable {P : Type} [CommRing P] [Algebra P C] (pc : PackedCommitment P m)
  (multiplier : Sumcheck.Structured.Multiplier Context C m)

section ProverRound
variable [BEq C] [LawfulBEq C] (i : Fin m) (a : Context → (Fin m → Fin 2) → C)
  (stmt : Statement Context C i.castSucc) (ost : ∀ j, pc.OStmt j)
  (p : (Fin m → Fin 2) → C) (Q : P⦃≤ 1⦄[X Fin m])
  (ha : ∀ b, a stmt.ctx b = (multiplier stmt.ctx).val.eval (b : Fin m → C))
  (hp : ∀ b, p b = aeval (b : Fin m → C) Q.val)

include ha hp

/-- The actual round prover sends the specified polynomial after decoding its coefficient array. -/
theorem roundProver_send_eq :
    let native := roundProver pc.OStmt i a
    let legacy := Round.prover multiplier pc i
    (fun sent => Sumcheck.Impl.Representation.toMessage C 2 sent.1) <$>
      native.sendMessage ⟨0, rfl⟩ (native.input ((stmt, ost), p)) =
      Prod.fst <$> legacy.sendMessage ⟨0, rfl⟩ (legacy.input ((stmt, ost), Q)) := by
  simp only [roundProver, Round.prover, Round.proverForOracles, id_eq, map_pure]
  exact congrArg pure
    (roundMessage_toMessage i (a stmt.ctx) p stmt.challenges (multiplier stmt.ctx) Q ha hp)

/-- After sending and receiving a challenge, both provers return the same claim and oracles.
Reading the returned legacy witness on the Boolean cube gives the same returned table. -/
theorem roundProver_finish_eq (c : C) :
    let native := roundProver pc.OStmt i a
    let legacy := Round.prover multiplier pc i
    (do
      let sent ← native.sendMessage ⟨0, rfl⟩ (native.input ((stmt, ost), p))
      let receive ← native.receiveChallenge ⟨1, rfl⟩ sent.2
      native.output (receive c)) =
      (fun out => (out.1, fun b : Fin m → Fin 2 => aeval (b : Fin m → C) out.2.val)) <$> (do
        let sent ← legacy.sendMessage ⟨0, rfl⟩ (legacy.input ((stmt, ost), Q))
        let receive ← legacy.receiveChallenge ⟨1, rfl⟩ sent.2
        legacy.output (receive c)) := by
  have hTable : (fun b : Fin m → Fin 2 => aeval (b : Fin m → C) Q.val) = p :=
    (funext hp).symm
  have hNext : roundNext i stmt (roundMessage i (a stmt.ctx) p stmt.challenges) c =
      Round.nextStatement i stmt (Round.honestMessage multiplier i stmt Q) c := by
    simp only [roundNext, Round.nextStatement, Sumcheck.Impl.Representation.evaluate_eq]
    rw [roundMessage_toMessage i (a stmt.ctx) p stmt.challenges (multiplier stmt.ctx) Q ha hp]
    rfl
  change (pure ((roundNext i stmt (roundMessage i (a stmt.ctx) p stmt.challenges) c, ost), p) :
    OracleComp []ₒ _) =
      pure ((Round.nextStatement i stmt (Round.honestMessage multiplier i stmt Q) c, ost),
        fun b : Fin m → Fin 2 => aeval (b : Fin m → C) Q.val)
  rw [hNext, hTable]

end ProverRound

section ProverTerminal
variable (stmt : Statement Context C (Fin.last m)) (ost : ∀ j, pc.OStmt j)
  (p : (Fin m → Fin 2) → C) (Q : P⦃≤ 1⦄[X Fin m])
  (hp : ∀ b, p b = aeval (b : Fin m → C) Q.val)

include hp

/-- The actual terminal provers send the same packed evaluation. -/
theorem terminalProver_send_eq :
    let native := terminalProver pc.OStmt
    let legacy := Terminal.prover (C := C) (Context := Context) pc
    Prod.fst <$> native.sendMessage ⟨0, rfl⟩ (native.input ((stmt, ost), p)) =
      Prod.fst <$> legacy.sendMessage ⟨0, rfl⟩ (legacy.input ((stmt, ost), Q)) := by
  simp only [terminalProver, Terminal.prover, Terminal.proverForOracles, id_eq, map_pure,
    terminalMessage_eq p Q hp stmt]

/-- The terminal provers return the same evaluation claim and original oracles, and the returned
table represents the returned legacy polynomial. -/
theorem terminalProver_finish_eq :
    let native := terminalProver pc.OStmt
    let legacy := Terminal.prover (C := C) (Context := Context) pc
    (do
      let sent ← native.sendMessage ⟨0, rfl⟩ (native.input ((stmt, ost), p))
      native.output sent.2) =
      (fun out => (out.1, fun b : Fin m → Fin 2 => aeval (b : Fin m → C) out.2.val)) <$> (do
        let sent ← legacy.sendMessage ⟨0, rfl⟩ (legacy.input ((stmt, ost), Q))
        legacy.output sent.2) := by
  have hTable : (fun b : Fin m → Fin 2 => aeval (b : Fin m → C) Q.val) = p :=
    (funext hp).symm
  simp only [terminalProver, Terminal.prover, Terminal.proverForOracles, id_eq, pure_bind,
    map_pure, terminalMessage_eq p Q hp stmt, hTable]

end ProverTerminal
end ProverCorrespondence

end RingSwitching.Packing.ProductSumcheck.Computable

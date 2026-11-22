/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
module

public import ArkLib.ProofSystem.RingSwitching.Packing.ProductSumcheck.Basic
public import ArkLib.ProofSystem.RingSwitching.RoundVerifiers
public import ArkLib.OracleReduction.Security.GuardedRoundByRound
public import ArkLib.OracleReduction.Composition.Sequential.GuardedCompleteness

/-!
# A generic product-sumcheck round

The prover sends a clear degree-two polynomial. The verifier checks its Boolean sum, then
extends the fixed challenge prefix and retains the same commitment oracles. The honest message
is computed from the C-valued product of the public multiplier and transported witness.
-/

@[expose] public section

noncomputable section
namespace RingSwitching.Packing.ProductSumcheck.Round
open OracleSpec OracleComp ProtocolSpec Polynomial MvPolynomial
open CoordinateWise.ScalarRound ProbabilityTheory
variable {P C Context : Type} [CommRing P] [CommRing C] [Algebra P C] {m : ℕ}
  (multiplier : Multiplier Context C m) (pc : PackedCommitment P m) (i : Fin m)

/-- One clear degree-two polynomial followed by a scalar challenge over C. -/
def pSpec (C : Type) [CommRing C] : ProtocolSpec 2 := pSpecScalar C⦃≤ 2⦄[X] C

instance : ∀ j, OracleInterface ((pSpec C).Message j) :=
  letI : OracleInterface C⦃≤ 2⦄[X] := OracleInterface.instDefault
  inferInstanceAs (∀ j, OracleInterface ((pSpecScalar C⦃≤ 2⦄[X] C).Message j))

instance [SampleableType C] : ∀ j, SampleableType ((pSpec C).Challenge j)
  | ⟨0, h⟩ => nomatch h
  | ⟨1, _⟩ => inferInstanceAs (SampleableType C)

/-- The honest message is the exact remaining product sum as a polynomial in the next variable. -/
def honestMessage (stmt : Statement Context C i.castSucc) (p : P⦃≤ 1⦄[X Fin m]) :
    C⦃≤ 2⦄[X] := roundMessage i (productPoly (multiplier stmt.ctx) p) stmt.challenges

/-- The local sumcheck equation. -/
def check (stmt : Statement Context C i.castSucc) (g : C⦃≤ 2⦄[X]) : Prop :=
  g.val.eval 0 + g.val.eval 1 = stmt.target

/-- Append the sampled scalar and set the next target to the received polynomial's evaluation. -/
def nextStatement (stmt : Statement Context C i.castSucc) (g : C⦃≤ 2⦄[X]) (c : C) :
    Statement Context C i.succ := ⟨stmt.ctx, Fin.snoc stmt.challenges c, g.val.eval c⟩

/-- The first two states keep the original input and polynomial; the last also records c. -/
def OracleState {ι : Type} (OStmt : ι → Type) : Fin 3 → Type
  | ⟨0, _⟩ => (Statement Context C i.castSucc × (∀ j, OStmt j)) × P⦃≤ 1⦄[X Fin m]
  | ⟨1, _⟩ => (Statement Context C i.castSucc × (∀ j, OStmt j)) × P⦃≤ 1⦄[X Fin m]
  | ⟨2, _⟩ => ((Statement Context C i.castSucc × (∀ j, OStmt j)) ×
      P⦃≤ 1⦄[X Fin m]) × C

/-- The honest round algorithm depends only on the oracle family, independently of compatibility. -/
def proverForOracles {ι : Type} (OStmt : ι → Type) :
    OracleProver []ₒ (Statement Context C i.castSucc) OStmt P⦃≤ 1⦄[X Fin m]
    (Statement Context C i.succ) OStmt P⦃≤ 1⦄[X Fin m] (pSpec C) where
  PrvState := OracleState (P := P) (C := C) (Context := Context) i OStmt
  input := id
  sendMessage
    | ⟨0, _⟩ => fun st => pure (honestMessage multiplier i st.1.1 st.2, st)
    | ⟨1, h⟩ => fun _ => nomatch h
  receiveChallenge
    | ⟨0, h⟩ => nomatch h
    | ⟨1, _⟩ => fun st => pure fun c => (st, c)
  output := fun (((stmt, ost), p), c) =>
    pure ((nextStatement i stmt (honestMessage multiplier i stmt p) c, ost), p)

/-- The honest state family at a fixed commitment oracle interface. -/
abbrev ProverState := OracleState (P := P) (C := C) (Context := Context) i pc.OStmt

/-- Send the exact product-sum polynomial while retaining the packed witness and oracles. -/
def prover := proverForOracles (P := P) multiplier i pc.OStmt

open scoped Classical in
/-- A failed Boolean sum check aborts; acceptance extends the original challenge prefix. -/
def verifier : OracleVerifier []ₒ (Statement Context C i.castSucc) pc.OStmt
    (Statement Context C i.succ) pc.OStmt (pSpec C) :=
  scalarRoundOracleVerifier (check i) (nextStatement i)

/-- The scalar-round reduction preserving the commitment oracle. -/
def reduction : OracleReduction []ₒ (Statement Context C i.castSucc) pc.OStmt P⦃≤ 1⦄[X Fin m]
    (Statement Context C i.succ) pc.OStmt P⦃≤ 1⦄[X Fin m] (pSpec C) :=
  ⟨prover multiplier pc i, verifier (C := C) (Context := Context) pc i⟩

open scoped Classical in
/-- The round's exact guarded form supports state-aware composition. -/
def guardedForm : (verifier (C := C) (Context := Context) pc i).toVerifier.GuardedForm :=
  scalarRoundOracleVerifierGuardedForm (check i) (nextStatement i)

omit [Algebra P C] in
open scoped Classical in
/-- The sumcheck guarded form checks the Boolean sum of the clear message. -/
theorem guardedForm_check (stmt : Statement Context C i.castSucc × (∀ j, pc.OStmt j))
    (tr : FullTranscript (pSpec C)) :
    (guardedForm (C := C) (Context := Context) pc i).check stmt tr =
      decide (check i stmt.1 (tr.messages ⟨0, rfl⟩)) := rfl

omit [Algebra P C] in
/-- The sumcheck guarded form retains the input oracles and appends the scalar challenge. -/
theorem guardedForm_out (stmt : Statement Context C i.castSucc × (∀ j, pc.OStmt j))
    (tr : FullTranscript (pSpec C)) :
    (guardedForm (C := C) (Context := Context) pc i).out stmt tr =
      (nextStatement i stmt.1 (tr.messages ⟨0, rfl⟩) (tr.challenges ⟨1, rfl⟩), stmt.2) := rfl


open scoped Classical in
omit [Algebra P C] in
/-- Round verification with a clear polynomial message and preserved input oracles. -/
theorem verifier_verify (stmt : Statement Context C i.castSucc) (ost : ∀ j, pc.OStmt j)
    (tr : FullTranscript (pSpec C)) :
    (verifier pc i).toVerifier.verify (stmt, ost) tr =
      (if check i stmt (tr.messages ⟨0, rfl⟩) then
        pure (nextStatement i stmt (tr.messages ⟨0, rfl⟩) (tr.challenges ⟨1, rfl⟩), ost)
      else failure) := by
  have h := (guardedForm pc i).verify_eq (stmt, ost) tr
  rw [guardedForm_check, guardedForm_out] at h
  simpa only [decide_eq_true_eq] using h

instance : (prover multiplier pc i).OutputIsPure where
  output_is_pure := ⟨fun (((stmt, ost), p), c) =>
    ((nextStatement i stmt (honestMessage multiplier i stmt p) c, ost), p), fun _ => rfl⟩

/-- The honest polynomial's Boolean sum is the input target. -/
theorem check_honestMessage_of_mem_rel {stmt : Statement Context C i.castSucc} {ost : ∀ j,
    pc.OStmt j}
    {p : P⦃≤ 1⦄[X Fin m]} (h : ((stmt, ost), p) ∈ rel multiplier pc i.castSucc) :
    check i stmt (honestMessage multiplier i stmt p) :=
  (roundMessage_sum i (productPoly (multiplier stmt.ctx) p) stmt.challenges).trans h.1.symm

/-- Every challenge gives the correct next product sum and the original commitment witness. -/
theorem nextStatement_mem_rel {stmt : Statement Context C i.castSucc} {ost : ∀ j, pc.OStmt j}
    {p : P⦃≤ 1⦄[X Fin m]} (h : ((stmt, ost), p) ∈ rel multiplier pc i.castSucc) (c : C) :
    ((nextStatement i stmt (honestMessage multiplier i stmt p) c, ost), p) ∈
      rel multiplier pc i.succ :=
  ⟨roundMessage_eval i (productPoly (multiplier stmt.ctx) p) stmt.challenges c, h.2⟩

end RingSwitching.Packing.ProductSumcheck.Round

/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

import ArkLib.ProofSystem.RingSwitching.Packing.ScalarHead.Layout
import ArkLib.ProofSystem.RingSwitching.Packing.FullFamily.Phase
import ArkLib.ProofSystem.RingSwitching.Packing.CheckedObservation

/-!
# Checked scalar-to-family claim head

The prover sends partial evaluations. The verifier checks their weighted reconstruction against
the original scalar claim and passes the family to the full-family relation on the same packed
commitment. This is one message with no verifier challenge. The later full-family batching is a
separate wire stage; its extra checked-slice message is redundant for the paper's scalar head.
-/

noncomputable section

namespace RingSwitching.Packing.ScalarHead

open OracleSpec OracleComp ProtocolSpec MvPolynomial

variable {B : Type} [CommRing B] (data : PackingData B) (m : ℕ)
  (layout : ClaimLayout data m) (pc : PackedCommitment data.P m)

abbrev Input := layout.Query × data.E

/-- One clear message containing the partial evaluations, with no challenge. -/
def pSpec : ProtocolSpec 1 := pSpecMessage (data.ιP → data.E)

instance : ∀ i, OracleInterface ((pSpec data).Message i) :=
  inferInstanceAs (∀ i, OracleInterface ((pSpecMessage (data.ιP → data.E)).Message i))

instance : ∀ i, SampleableType ((pSpec data).Challenge i)
  | ⟨0, h⟩ => nomatch h

/-- Honest partial evaluations at the retained point. -/
def partials (q : layout.Query) (ps : data.ιP → B⦃≤ 1⦄[X Fin m]) : data.ιP → data.E :=
  fun i => aeval (layout.point q) (ps i).val

/-- Weighted partial evaluations reconstruct the source evaluation. -/
def observation : CheckedObservation layout.Query layout.Source
    (data.ιP → B⦃≤ 1⦄[X Fin m]) (data.ιP → data.E) data.E where
  witnessEquiv := layout.components
  honestMsg := partials data m layout
  scalarEval := layout.eval
  observe q α := ∑ i, layout.weight q i * α i
  eval_eq_observe := layout.reconstruct

/-- The scalar check uses the layout's concrete weight vector. -/
def check (stmt : Input data m layout) (α : data.ιP → data.E) : Prop :=
  stmt.2 = ∑ i, layout.weight stmt.1 i * α i

/-- The output is the full partial-evaluation family at the retained point. -/
def nextStatement (stmt : Input data m layout) (α : data.ιP → data.E) :
    FullFamily.Input data m := (α, layout.point stmt.1)

/-- The head starts from the original scalar claim and the same packed commitment. -/
def relIn : Set (((Input data m layout) × (∀ j, pc.OStmt j)) × layout.Source) :=
  { sw | sw.1.1.2 = layout.eval sw.1.1.1 sw.2 ∧
    pc.commitsTo sw.1.2 (data.packedMLE (layout.components sw.2)) }

/-- Every source and query has a satisfying claim with its honest packed commitment. -/
theorem relIn_honest (q : layout.Query) (p : layout.Source) :
    (((q, layout.eval q p), pc.commit (data.packedMLE (layout.components p))), p) ∈
      relIn data m layout pc := ⟨rfl, pc.commitsTo_commit _⟩

/-- The output relation is exactly the input relation of full-family packing. -/
abbrev relOut := FullFamily.relIn data m pc

/-- The original scalar relation retains the same commitment in observation coordinates. -/
theorem relIn_iff_observation (stmt : Input data m layout) (ost : ∀ j, pc.OStmt j)
    (p : layout.Source) :
    ((stmt, ost), p) ∈ relIn data m layout pc ↔
      pc.commitsTo ost (data.packedMLE (layout.components p)) ∧
        stmt.2 = (observation data m layout).scalarEval stmt.1 p :=
  and_comm

/-- The existing scalar check is precisely equality with the concrete observation. -/
theorem check_iff_observation (stmt : Input data m layout) (α : data.ιP → data.E) :
    check data m layout stmt α ↔ stmt.2 = (observation data m layout).observe stmt.1 α :=
  Iff.rfl

/--
At the verifier output, family validity fixes the message and preserves the commitment oracle.
-/
theorem relOut_iff_observation (stmt : Input data m layout) (ost : ∀ j, pc.OStmt j)
    (α : data.ιP → data.E) (ps : data.ιP → B⦃≤ 1⦄[X Fin m]) :
    ((nextStatement data m layout stmt α, ost), ps) ∈ relOut data m pc ↔
      pc.commitsTo ost (data.packedMLE ps) ∧
        α = (observation data m layout).honestMsg stmt.1 ps := by
  constructor
  · intro h
    exact ⟨h.2, funext h.1⟩
  · rintro ⟨hc, hα⟩
    exact ⟨fun i => congrFun hα i, hc⟩

/-- Before sending the family, retain the source; afterwards retain its components. -/
def ProverState : Fin 2 → Type
  | ⟨0, _⟩ => (Input data m layout × (∀ j, pc.OStmt j)) × layout.Source
  | ⟨1, _⟩ => (Input data m layout × (∀ j, pc.OStmt j)) ×
      (data.ιP → B⦃≤ 1⦄[X Fin m])

/-- The honest prover sends the partial-evaluation family. -/
def prover : OracleProver []ₒ (Input data m layout) pc.OStmt layout.Source
    (FullFamily.Input data m) pc.OStmt (data.ιP → B⦃≤ 1⦄[X Fin m]) (pSpec data) where
  PrvState := ProverState data m layout pc
  input := id
  sendMessage
    | ⟨0, _⟩ => fun ((stmt, ost), p) => pure
      (partials data m layout stmt.1 (layout.components p), ((stmt, ost), layout.components p))
  receiveChallenge
    | ⟨0, h⟩ => nomatch h
  output st := pure
    ((nextStatement data m layout st.1.1 (partials data m layout st.1.1.1 st.2), st.1.2), st.2)

open scoped Classical in
/-- Reject a failed scalar reconstruction, preserving the oracle only on acceptance. -/
def verifier : OracleVerifier []ₒ (Input data m layout) pc.OStmt
    (FullFamily.Input data m) pc.OStmt (pSpec data) :=
  guardedMessageRoundOracleVerifier (check data m layout) (nextStatement data m layout)

/-- The scalar claim reduction. -/
def reduction : OracleReduction []ₒ (Input data m layout) pc.OStmt layout.Source
    (FullFamily.Input data m) pc.OStmt (data.ιP → B⦃≤ 1⦄[X Fin m]) (pSpec data) :=
  ⟨prover data m layout pc, verifier data m layout pc⟩

open scoped Classical in
/-- Exact execution after materializing message and input oracles. -/
theorem verifier_verify (stmt : Input data m layout) (ost : ∀ j, pc.OStmt j)
    (tr : FullTranscript (pSpec data)) :
    (verifier data m layout pc).toVerifier.verify (stmt, ost) tr =
      (if check data m layout stmt (tr.messages ⟨0, rfl⟩) then
        pure (nextStatement data m layout stmt (tr.messages ⟨0, rfl⟩), ost) else failure) := by
  apply guardedMessageRoundOracleVerifier_verify

open scoped Classical in
/-- The scalar verifier as a deterministic guarded form. -/
def guardedForm : (verifier data m layout pc).toVerifier.GuardedForm where
  check stmt tr := decide (check data m layout stmt.1 (tr.messages ⟨0, rfl⟩))
  out stmt tr := (nextStatement data m layout stmt.1 (tr.messages ⟨0, rfl⟩), stmt.2)
  verify_eq stmt tr := by rw [verifier_verify]; simp

/-- The prover output has no oracle queries and can be sequenced statefully. -/
instance : (prover data m layout pc).OutputIsPure where
  output_is_pure := ⟨fun st =>
    ((nextStatement data m layout st.1.1 (partials data m layout st.1.1.1 st.2), st.1.2), st.2),
    fun _ => rfl⟩

/-- The honest scalar check is precisely the concrete layout reconstruction theorem. -/
theorem honest_check {stmt : Input data m layout} {ost : ∀ j, pc.OStmt j} {p : layout.Source}
    (h : ((stmt, ost), p) ∈ relIn data m layout pc) :
    check data m layout stmt (partials data m layout stmt.1 (layout.components p)) := by
  apply (check_iff_observation data m layout _ _).2
  exact (observation data m layout).honest_check
    ((relIn_iff_observation data m layout pc stmt ost p).1 h).2

/-- The honest output preserves the commitment oracle and satisfies the full-family relation. -/
theorem honest_relOut {stmt : Input data m layout} {ost : ∀ j, pc.OStmt j} {p : layout.Source}
    (h : ((stmt, ost), p) ∈ relIn data m layout pc) :
    ((nextStatement data m layout stmt (partials data m layout stmt.1 (layout.components p)),
      ost), layout.components p) ∈ relOut data m pc := ⟨fun _ => rfl, h.2⟩

/-- A checked, correct family reads back the original scalar claim without any random loss. -/
theorem readback (stmt : Input data m layout) (ost : ∀ j, pc.OStmt j)
    (α : data.ιP → data.E) (ps : data.ιP → B⦃≤ 1⦄[X Fin m])
    (hc : check data m layout stmt α)
    (ho : ((nextStatement data m layout stmt α, ost), ps) ∈ relOut data m pc) :
    ((stmt, ost), layout.components.symm ps) ∈ relIn data m layout pc := by
  apply (relIn_iff_observation data m layout pc stmt ost _).2
  exact (observation data m layout).readback_keep
    (fun _ ps => pc.commitsTo ost (data.packedMLE ps))
    ((check_iff_observation data m layout stmt α).1 hc)
    ((relOut_iff_observation data m layout pc stmt ost α ps).1 ho)

end RingSwitching.Packing.ScalarHead

end

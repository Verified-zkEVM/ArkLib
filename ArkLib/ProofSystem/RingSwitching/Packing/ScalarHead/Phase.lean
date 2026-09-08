/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

import ArkLib.ProofSystem.RingSwitching.Packing.ScalarHead.Layout
import ArkLib.ProofSystem.RingSwitching.Packing.FullFamily.Phase

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

/-- Every original source and query has a satisfying claim with its actual packed commitment. -/
theorem relIn_honest (q : layout.Query) (p : layout.Source) :
    (((q, layout.eval q p), pc.commit (data.packedMLE (layout.components p))), p) ∈
      relIn data m layout pc := ⟨rfl, pc.commitsTo_commit _⟩

/-- The output relation is exactly the input relation of full-family packing. -/
abbrev relOut := FullFamily.relIn data m pc

/-- Before sending the family, retain the source; afterwards retain its components. -/
def ProverState : Fin 2 → Type
  | ⟨0, _⟩ => (Input data m layout × (∀ j, pc.OStmt j)) × layout.Source
  | ⟨1, _⟩ => (Input data m layout × (∀ j, pc.OStmt j)) ×
      (data.ιP → B⦃≤ 1⦄[X Fin m])

/-- The honest prover supplies the actual partial-evaluation family. -/
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

/-- The actual scalar claim reduction. -/
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
/-- The deterministic guarded form used for actual execution and state-aware composition. -/
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
    check data m layout stmt (partials data m layout stmt.1 (layout.components p)) :=
  h.1.trans (layout.reconstruct stmt.1 p)

/-- Honest output retains the same oracle and satisfies the full-family relation. -/
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
  refine ⟨?_, ?_⟩
  · rw [layout.reconstruct, layout.components.apply_symm_apply]
    exact hc.trans (Finset.sum_congr rfl fun i _ => congrArg _ (ho.1 i))
  · simpa only [layout.components.apply_symm_apply] using ho.2

end RingSwitching.Packing.ScalarHead

end

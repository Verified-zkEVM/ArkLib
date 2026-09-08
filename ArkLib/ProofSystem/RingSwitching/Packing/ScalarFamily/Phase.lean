/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ProofSystem.RingSwitching.Packing.ScalarHead.Security
import ArkLib.ProofSystem.RingSwitching.Packing.FullFamily.Knowledge
import ArkLib.ProofSystem.RingSwitching.Packing.FullFamily.Completeness
import ArkLib.OracleReduction.Composition.Sequential.Append.Knowledge

/-!
# Scalar claim to a batched packed-polynomial claim

This oracle reduction appends the checked scalar head and the checked full-family phase.
It sends a partial-evaluation family, sends its coordinate slices, then samples a batching
challenge. Both messages are checked, and the same packed-polynomial commitment oracle survives.
The slice message is redundant relative to the literal paper protocol and is retained here as
part of the explicitly checked-message variant.
-/

noncomputable section

namespace RingSwitching.Packing.ScalarFamily

open MvPolynomial OracleSpec OracleComp ProtocolSpec

variable {B : Type} [CommRing B] (data : PackingData B) (m : ℕ)
  (layout : ScalarHead.ClaimLayout data m)
  {C : Type} [CommRing C] [Algebra B C] [Algebra data.P C] [IsScalarTower B data.P C]
  (bat : BatchingStrategy C data.ιE) (pc : PackedCommitment data.P m)

/-- Two prover messages followed by the full-family batching challenge. -/
abbrev pSpec : ProtocolSpec 3 := ScalarHead.pSpec data ++ₚ FullFamily.pSpec data bat

/-- The original scalar relation with its packed commitment. -/
abbrev relIn := ScalarHead.relIn data m layout pc

/-- The challenge-algebra sumcheck claim on the same packed polynomial and commitment oracle. -/
abbrev relOut := FullFamily.relOut data m bat pc

/-- The composed scalar and full-family oracle verifier. -/
def verifier : OracleVerifier []ₒ (ScalarHead.Input data m layout) pc.OStmt
    (FullFamily.Output data m bat) pc.OStmt (pSpec data bat) :=
  (ScalarHead.verifier data m layout pc).append (FullFamily.verifier data m bat pc)

/-- The composed scalar and full-family oracle reduction. -/
def reduction : OracleReduction []ₒ (ScalarHead.Input data m layout) pc.OStmt layout.Source
    (FullFamily.Output data m bat) pc.OStmt (data.P⦃≤ 1⦄[X Fin m]) (pSpec data bat) :=
  (ScalarHead.reduction data m layout pc).append (FullFamily.reduction data m bat pc)

omit [Algebra B C] [IsScalarTower B data.P C] in
/-- The reduction's verifier is exactly the separately named composed verifier. -/
@[simp] theorem reduction_verifier : (reduction data m layout bat pc).verifier =
    verifier data m layout bat pc := rfl

omit [Algebra B C] [IsScalarTower B data.P C] in
/-- Oracle materialization commutes with verifier append. -/
theorem verifier_toVerifier : (verifier data m layout bat pc).toVerifier =
    (ScalarHead.verifier data m layout pc).toVerifier.append
      (FullFamily.verifier data m bat pc).toVerifier :=
  OracleVerifier.append_toVerifier _ _

omit [Algebra B C] [IsScalarTower B data.P C] in
/-- Oracle materialization commutes with reduction append. -/
theorem reduction_toReduction : (reduction data m layout bat pc).toReduction =
    (ScalarHead.reduction data m layout pc).toReduction.append
      (FullFamily.reduction data m bat pc).toReduction :=
  OracleReduction.append_toReduction _ _

/-- Both runtime checks are retained in the composed guarded form. -/
def guardedForm : (verifier data m layout bat pc).toVerifier.GuardedForm := by
  let G := (ScalarHead.guardedForm data m layout pc).append (FullFamily.guardedForm data m bat pc)
  exact {
    check := G.check
    out := G.out
    verify_eq := fun stmt tr => by
      rw [verifier_toVerifier]
      exact G.verify_eq stmt tr }

omit [Algebra B C] [IsScalarTower B data.P C] in
open scoped Classical in
/--
Verification checks the scalar and slice readback, then returns the batched target with the
original commitment oracle.
-/
theorem verifier_run (stmt : ScalarHead.Input data m layout) (ost : ∀ j, pc.OStmt j)
    (tr : FullTranscript (pSpec data bat)) :
    (verifier data m layout bat pc).toVerifier.run (stmt, ost) tr =
      if ScalarHead.check data m layout stmt (tr.fst.messages ⟨0, rfl⟩) then
        if data.claimConsistent (tr.fst.messages ⟨0, rfl⟩) (tr.snd.messages ⟨0, rfl⟩) then
          pure (FullFamily.nextStatement data m bat
            (ScalarHead.nextStatement data m layout stmt (tr.fst.messages ⟨0, rfl⟩))
            (tr.snd.messages ⟨0, rfl⟩) (tr.snd.challenges ⟨1, rfl⟩), ost)
        else failure
      else failure := by
  rw [verifier_toVerifier]
  change (do
    let next ← (ScalarHead.verifier data m layout pc).toVerifier.run (stmt, ost) tr.fst
    (FullFamily.verifier data m bat pc).toVerifier.run next tr.snd) = _
  simp only [Verifier.run, ScalarHead.verifier_verify]
  by_cases hc : ScalarHead.check data m layout stmt (tr.fst.messages ⟨0, rfl⟩)
  · rw [if_pos hc, pure_bind, FullFamily.verifier_verify, if_pos hc]
    rfl
  · simp [hc]

end RingSwitching.Packing.ScalarFamily

end

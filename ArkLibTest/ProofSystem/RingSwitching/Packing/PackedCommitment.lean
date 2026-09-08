/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLibTest.ProofSystem.RingSwitching.Packing.ScalarFamily

/-!
# Nonfunctional finite-list commitment clients

An oracle stores a finite set of candidate polynomials. Honest coverage uses a singleton,
while other oracles can contain two distinct witnesses. The scalar head, including
its exact extractor, zero-challenge knowledge and completeness, accepts this base interface.
No list-decoding probability bound is asserted.
-/

noncomputable section

namespace RingSwitching.Packing.Tests.NonfunctionalCommitment

open MvPolynomial Module OracleSpec OracleComp ProtocolSpec

/-- A concrete finite candidate set, with the same membership relation at all protocol seams. -/
def finiteList (P : Type) [CommRing P] (m : ℕ) : PackedCommitment P m where
  ιC := Unit
  OStmt _ := Finset P⦃≤ 1⦄[X Fin m]
  Oᵢ _ := OracleInterface.instDefault
  commitsTo c p := p ∈ c ()
  commit p _ := {p}
  commitsTo_commit p := Finset.mem_singleton_self p

/-- A constant polynomial as a genuine multilinear witness. -/
def constant {P : Type} [CommRing P] (m : ℕ) (v : P) : P⦃≤ 1⦄[X Fin m] :=
  ⟨C v, by simp [mem_restrictDegree_iff_degreeOf_le]⟩

/-- Two different polynomials can be compatible with one finite-list oracle. -/
theorem finiteList_not_functional (P : Type) [CommRing P] [Nontrivial P] (m : ℕ) :
    ¬ (finiteList P m).Functional := by
  classical
  intro h
  have h01 : (0 : P⦃≤ 1⦄[X Fin m]) = constant m (1 : P) :=
    h (c := fun _ => ({0, constant m (1 : P)} : Finset P⦃≤ 1⦄[X Fin m]))
      (by simp [finiteList]) (by simp [finiteList])
  have hp : (0 : MvPolynomial (Fin m) P) = 1 := by
    simpa [constant] using congrArg Subtype.val h01
  exact zero_ne_one hp

open RingSwitching.Packing.Tests.ScalarFamily in
/-- The original nonconstant scalar source has honest finite-list commitment coverage. -/
theorem scalar_source_related :
    ((stmt, (finiteList data.P 1).commit (data.packedMLE (layout.components source))), source) ∈
      ScalarHead.relIn data 1 layout (finiteList data.P 1) :=
  ScalarHead.relIn_honest data 1 layout (finiteList data.P 1) query source

open RingSwitching.Packing.Tests.ScalarFamily in
/-- The scalar verifier accepts and retains the precise finite-list oracle. -/
theorem scalar_accept :
    (ScalarHead.verifier data 1 layout (finiteList data.P 1)).toVerifier.verify
      (stmt, (finiteList data.P 1).commit (data.packedMLE (layout.components source)))
      (ScalarHead.transcript data α) =
      pure (ScalarHead.nextStatement data 1 layout stmt α,
        (finiteList data.P 1).commit (data.packedMLE (layout.components source))) := by
  rw [ScalarHead.verifier_verify]
  exact if_pos (ScalarHead.honest_check data 1 layout (finiteList data.P 1) scalar_source_related)

open RingSwitching.Packing.Tests.ScalarFamily in
/-- Scalar-head worst-case knowledge uses no commitment functionality. -/
theorem scalar_worst_case {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    Verifier.rbrKnowledgeSoundnessWorstCaseWith init impl
      (ScalarHead.relIn data 1 layout (finiteList data.P 1))
      (FullFamily.relIn data 1 (finiteList data.P 1))
      (ScalarHead.verifier data 1 layout (finiteList data.P 1)).toVerifier
      (ScalarHead.WitMid data 1 layout) (ScalarHead.extractor data 1 layout (finiteList data.P 1))
      (ScalarHead.knowledgeStateFunction data 1 layout (finiteList data.P 1) init impl)
      (fun _ => 0) :=
  ScalarHead.rbrKnowledgeSoundnessWorstCaseWith data 1 layout (finiteList data.P 1) init impl

open RingSwitching.Packing.Tests.ScalarFamily in
/-- Scalar completeness remains uniform over oracle states for the list-valued relation. -/
theorem scalar_complete {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    (ScalarHead.reduction data 1 layout (finiteList data.P 1)).perfectCompleteness init impl
      (ScalarHead.relIn data 1 layout (finiteList data.P 1))
      (FullFamily.relIn data 1 (finiteList data.P 1)) :=
  ScalarHead.perfectCompleteness data 1 layout (finiteList data.P 1) init impl

open scoped Classical in
open RingSwitching.Packing.Tests.ScalarFamily in
/-- One concrete oracle with the honest polynomial and a distinct offset candidate. -/
def twoCandidateOracle : ∀ j, (finiteList data.P 1).OStmt j := fun _ =>
  ({data.packedMLE (layout.components source),
    data.packedMLE (layout.components source) + constant 1 1} : Finset data.P⦃≤ 1⦄[X Fin 1])

open RingSwitching.Packing.Tests.ScalarFamily in
/-- The oracle used by the production verifier contains two different candidates. -/
theorem twoCandidateOracle_card : (twoCandidateOracle ()).card = 2 := by
  classical
  have hne : data.packedMLE (layout.components source) ≠
      data.packedMLE (layout.components source) + constant 1 1 := by
    intro h
    have hz : constant 1 (1 : data.P) = 0 := add_left_cancel (h.symm.trans (add_zero _).symm)
    have he := congrArg (fun p : data.P⦃≤ 1⦄[X Fin 1] => eval (fun _ => 0) p.val) hz
    exact (by decide : (1 : ZMod 5) ≠ 0) (by simpa [constant] using he)
  simp [twoCandidateOracle, hne]

open RingSwitching.Packing.Tests.ScalarFamily in
/-- The scalar source is valid against this two-candidate oracle. -/
theorem twoCandidate_source_related :
    ((stmt, twoCandidateOracle), source) ∈ ScalarHead.relIn data 1 layout (finiteList data.P 1) :=
  ⟨rfl, by simp [finiteList, twoCandidateOracle]⟩

open RingSwitching.Packing.Tests.ScalarFamily in
/-- Both phases accept the nonfunctional relation with the same finite-list oracle. -/
theorem scalarFamily_accept (c : ZMod 5) :
    (RingSwitching.Packing.ScalarFamily.verifier
      data 1 layout bat (finiteList data.P 1)).toVerifier.run
      (stmt, twoCandidateOracle)
      (tr c) = pure (FullFamily.nextStatement data 1 bat
        (ScalarHead.nextStatement data 1 layout stmt α) slices c,
        twoCandidateOracle) := by
  rw [RingSwitching.Packing.ScalarFamily.verifier_run]
  exact if_pos (ScalarHead.honest_check data 1 layout (finiteList data.P 1)
    twoCandidate_source_related)
    |>.trans (if_pos (FullFamily.honest_check data 1 (finiteList data.P 1)
      (ScalarHead.honest_relOut data 1 layout (finiteList data.P 1) twoCandidate_source_related)))

open RingSwitching.Packing.Tests.ScalarFamily in
/-- The randomized composition's completeness also needs no commitment functionality. -/
theorem scalarFamily_complete {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    (RingSwitching.Packing.ScalarFamily.reduction
      data 1 layout bat (finiteList data.P 1)).perfectCompleteness init impl
      (ScalarHead.relIn data 1 layout (finiteList data.P 1))
      (FullFamily.relOut data 1 bat (finiteList data.P 1)) :=
  RingSwitching.Packing.ScalarFamily.perfectCompleteness data 1 layout bat
    (finiteList data.P 1) init impl

end RingSwitching.Packing.Tests.NonfunctionalCommitment

end

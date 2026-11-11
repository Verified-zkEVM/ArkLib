/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.ProofSystem.RingSwitching.Packing.Head
import ArkLib.ProofSystem.RingSwitching.Packing.Batching.CoordinateSample
import Mathlib.Algebra.Algebra.Pi
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.Algebra.Field.ZMod

/-!
# A protocol consumer over a ring with zero divisors and unequal ranks

The packing algebra has rank two and the opening algebra rank three over `ZMod 4`.
A scalar query sums the two component evaluations; batching samples one of the three opening
coordinates, with certified error `2/3`. The generic protocol and its completeness and
round-by-round knowledge theorem are instantiated, including an exact functional
commitment,
nonconstant source, nonzero honest message and rejecting transcript.
-/

noncomputable section

namespace RingSwitching.Packing.Tests.Head

open Module MvPolynomial OracleSpec OracleComp ProtocolSpec ProbabilityTheory
open scoped NNReal ENNReal

abbrev data : PackingData (ZMod 4) where
  P := Fin 2 → ZMod 4
  E := Fin 3 → ZMod 4
  ιP := Fin 2
  ιE := Fin 3
  packBasis := Pi.basisFun _ _
  openBasis := Pi.basisFun _ _

/-- Summed component evaluations are an ordinary scalar claim with identity source layout. -/
def layout : ClaimLayout data 1 where
  Source := Fin 2 → (ZMod 4)⦃≤ 1⦄[X Fin 1]
  Query := Fin 1 → data.E
  components := Equiv.refl _
  point := id
  weight _ _ := 1
  eval q p := ∑ i, aeval q (p i).val
  reconstruct _ _ := by simp

/-- A clear packed-polynomial oracle makes coverage and binding explicit. -/
def pc : PackedCommitment data.P 1 where
  ιC := Unit
  OStmt _ := data.P⦃≤ 1⦄[X Fin 1]
  Oᵢ _ := OracleInterface.instDefault
  commitsTo ost p := ost () = p

def honest : pc.Honest where
  commit p _ := p
  commitsTo_commit _ := rfl

abbrev codec : (data.ιP → data.E) ≃ (data.ιP → data.E) := Equiv.refl _

theorem pc_functional : pc.Functional := fun h h' => h.symm.trans h'

abbrev bat := BatchingStrategy.coordinateSample data.P data.ιE

example : bat.error = (2 : ℝ≥0) / 3 := rfl

/-- This is a complete protocol instantiation, not only a relation or batching-law example. -/
example {σ : Type} (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    (Head.reduction data 1 layout codec bat.toBatchingRule pc).perfectCompleteness init impl
      (Head.relIn data 1 layout pc) (Head.relOut data 1 layout bat.toBatchingRule pc) :=
  Head.perfectCompleteness data 1 layout codec bat.toBatchingRule pc init impl

/-- The concrete extractor has round-by-round error `2/3` without a domain assumption. -/
example {σ : Type} (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    Verifier.rbrKnowledgeSoundnessWith init impl
      (Head.relIn data 1 layout pc) (Head.relOut data 1 layout bat.toBatchingRule pc)
      (Head.verifier data 1 layout codec bat.toBatchingRule pc).toVerifier
      (Head.WitMid data 1 layout)
      (Head.extractor (M := data.ιP → data.E) data 1 layout bat.toBatchingRule pc)
      (Head.knowledgeStateFunction data 1 layout codec bat.toBatchingRule pc init impl)
      (Head.rbrError (M := data.ιP → data.E) data bat) :=
  Head.rbrKnowledgeSoundnessWith data 1 layout codec bat pc
    pc_functional (fun _ _ h => h) init impl

/-- Both components are the nonconstant polynomial `X`. -/
def source : Fin 2 → (ZMod 4)⦃≤ 1⦄[X Fin 1] := fun _ =>
  ⟨MLE (fun y => (y 0 : ZMod 4)), MLE_mem_restrictDegree _⟩

def point : layout.Query := fun _ => 1

/-- The source is nonconstant on the Boolean cube. -/
example : (source 0).val.eval (fun _ => 0) ≠ (source 0).val.eval (fun _ => 1) := by
  change (source 0).val.eval ((fun _ => 0 : Fin 1 → Fin 2) : Fin 1 → ZMod 4) ≠
    (source 0).val.eval ((fun _ => 1 : Fin 1 → Fin 2) : Fin 1 → ZMod 4)
  simp only [source, MLE_eval_zeroOne]
  decide

/-- The message is nonzero. -/
example : Head.partials data 1 layout point source ≠ 0 := by
  intro h
  have h0 := congrFun (congrFun h 0) 0
  have hone : aeval point (source 0).val = (1 : data.E) := by
    have hpoint : point = algebraMap (ZMod 4) data.E ∘ (fun _ : Fin 1 => 1) := by
      change (fun _ : Fin 1 => (1 : data.E)) = _
      funext i
      simp
    rw [hpoint, aeval_algebraMap_apply]
    change algebraMap (ZMod 4) data.E
      ((source 0).val.eval ((fun _ => 1 : Fin 1 → Fin 2) : Fin 1 → ZMod 4)) = 1
    simp only [source, MLE_eval_zeroOne]
    norm_num
  change aeval point (source 0).val 0 = 0 at h0
  rw [hone] at h0
  exact (by decide : (1 : ZMod 4) ≠ 0) h0

/-- The nonconstant source inhabits the commitment-anchored input relation. -/
example : (((point, layout.eval point source),
    honest.commit (data.packedMLE (layout.components source))), source) ∈
      Head.relIn data 1 layout pc :=
  Head.mem_relIn_commit data 1 layout pc honest point source

/-- A transcript claiming zero against the all-one family fails the verifier guard. -/
theorem rejecting_guard : (Head.guardedForm data 1 layout codec bat.toBatchingRule pc).check
    ((point, 0), honest.commit (data.packedMLE (layout.components source)))
    (FullTranscript.mk2 (fun _ => 1) (0 : Fin 3)) = false := by
  classical
  rw [Head.guardedForm_check]
  rw [decide_eq_false_iff_not]
  change ¬ ((0 : data.E) = ∑ _i : Fin 2, (1 : data.E) * 1)
  simp only [Fin.sum_univ_two, one_mul]
  intro h
  have h0 := congrFun h 0
  change (0 : ZMod 4) = 1 + 1 at h0
  exact (by decide : (0 : ZMod 4) ≠ 1 + 1) h0

/-- Rejection by the materialized verifier produces no output statement. -/
example : (Head.verifier data 1 layout codec bat.toBatchingRule pc).toVerifier.verify
    ((point, 0), honest.commit (data.packedMLE (layout.components source)))
    (FullTranscript.mk2 (fun _ => 1) (0 : Fin 3)) = failure := by
  rw [(Head.guardedForm data 1 layout codec bat.toBatchingRule pc).verify_eq, rejecting_guard]
  rfl

/-- A source coordinate polynomial with its explicit multilinearity proof. -/
def coordinatePoly : (ZMod 4)⦃≤ 1⦄[X Fin 1] :=
  ⟨X 0, by
    rw [mem_restrictDegree_iff_degreeOf_le]
    intro i
    exact degreeOf_X_le i 0⟩

/-- The constant polynomial one in the multilinear submodule. -/
def constantOne : (ZMod 4)⦃≤ 1⦄[X Fin 1] :=
  ⟨C 1, by rw [mem_restrictDegree_iff_degreeOf_le]; intro i; simp⟩

/-- Two different nonconstant components: `X` and `1 + 2X`. -/
def distinctSource : Fin 2 → (ZMod 4)⦃≤ 1⦄[X Fin 1] :=
  ![coordinatePoly, constantOne + (2 : ZMod 4) • coordinatePoly]

/-- Each opening coordinate queries a different point. -/
def nonuniformPoint : Fin 1 → data.E := fun _ => ![1, 2, 3]

/-- The honest message uses both packing coordinates and all three different opening coordinates. -/
theorem distinct_partials :
    Head.partials data 1 layout nonuniformPoint distinctSource =
      ![![1, 2, 3], ![3, 1, 3]] := by
  change (fun i => aeval nonuniformPoint (distinctSource i).val) = _
  ext i u
  fin_cases i <;> fin_cases u <;>
    norm_num [data, distinctSource, nonuniformPoint, coordinatePoly, constantOne,
      MvPolynomial.aeval_def, MvPolynomial.smul_eq_C_mul]
  all_goals
    change (1 + (2 : ZMod 4) * _) = _
    decide

/-- A challenge selecting the middle opening coordinate produces its two packing coordinates. -/
example : data.derivedTarget
    (Head.partials data 1 layout nonuniformPoint distinctSource) (bat.weight (1 : Fin 3)) =
      ![2, 1] := by
  rw [distinct_partials]
  change (∑ u : Fin 3, (if u = (1 : Fin 3) then (1 : data.P) else 0) *
    data.transpose ![![1, 2, 3], ![3, 1, 3]] u) = ![2, 1]
  simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq',
    Finset.mem_univ, ↓reduceIte]
  rw [data.transpose_apply]
  change (∑ i : Fin 2, (Pi.basisFun (ZMod 4) (Fin 3)).repr
    (![![1, 2, 3], ![3, 1, 3]] i) (1 : Fin 3) • (Pi.basisFun (ZMod 4) (Fin 2)) i) = ![2, 1]
  simp only [Pi.basisFun_repr, Fin.sum_univ_two]
  ext i
  fin_cases i <;> norm_num [Pi.basisFun_apply]

/-- Only the component evaluations at zero are fixed; the packed polynomial is not unique. -/
def pointBound : PackedCommitment data.P 1 where
  ιC := Unit
  OStmt _ := Unit
  Oᵢ _ := OracleInterface.instDefault
  commitsTo _ p := ∀ i, aeval (0 : Fin 1 → data.E) (data.unpack p i).val = 0

/-- Two different compatible packed polynomials rule out polynomial functionality. -/
example : ¬ pointBound.Functional := by
  intro h
  have hzero : pointBound.commitsTo (fun _ => ()) (data.packedMLE (fun _ => 0)) := by
    change ∀ i, aeval (0 : Fin 1 → data.E) (data.unpack (data.packedMLE (fun _ => 0)) i).val = 0
    rw [data.unpack_packedMLE]
    intro i
    simp
  have hcoord : pointBound.commitsTo (fun _ => ())
      (data.packedMLE (fun _ => coordinatePoly)) := by
    change ∀ i, aeval (0 : Fin 1 → data.E)
      (data.unpack (data.packedMLE (fun _ => coordinatePoly)) i).val = 0
    rw [data.unpack_packedMLE]
    intro i
    simp [coordinatePoly]
  have heq := congrArg
    (fun p => (data.unpack p 0).val.eval (fun _ => (1 : ZMod 4))) (h hzero hcoord)
  rw [data.unpack_packedMLE, data.unpack_packedMLE] at heq
  norm_num [coordinatePoly] at heq
  exact (by decide : (0 : ZMod 4) ≠ 1) heq

/-- Point-local binding alone gives the unguarded collision bound, despite nonfunctionality. -/
example (α : data.ιP → data.E) :
    Pr{let c ← $ᵗ bat.Challenge}[∃ p,
      pointBound.commitsTo (fun _ => ()) p ∧ ((α, (0 : Fin 1 → data.E)), data.unpack p) ∉
        data.openingClaimRel 1 ∧
      (data.derivedTarget α (bat.weight c), p) ∈
        data.sumcheckClaimRel 1 (0 : Fin 1 → data.E) (bat.weight c)] ≤
      (bat.error : ℝ≥0∞) :=
  Head.pr_exists_derivedTarget_le_of_partials_eq data 1 layout bat pointBound
    (fun _ _ h => h) (0 : Fin 1 → data.E) (fun _ => ()) α
    (fun _ _ hp hp' i => (hp i).trans (hp' i).symm)

/-- A fixed zero query isolates evaluation binding from polynomial binding. -/
def pointLayout : ClaimLayout data 1 where
  Source := layout.Source
  Query := Unit
  components := Equiv.refl _
  point _ := 0
  weight _ _ := 1
  eval _ p := ∑ i, aeval (0 : Fin 1 → data.E) (p i).val
  reconstruct _ _ := by
    simp only [one_mul]
    rfl

/-- The nonconstant coordinate source inhabits this head's zero-query input relation. -/
example : ((((), (0 : data.E)), (fun _ => ())), (fun _ => coordinatePoly)) ∈
    Head.relIn data 1 pointLayout pointBound := by
  constructor
  · change (0 : data.E) = ∑ _i : Fin 2, aeval (0 : Fin 1 → data.E) coordinatePoly.val
    simp [coordinatePoly]
  · change ∀ i, aeval (0 : Fin 1 → data.E)
      (data.unpack (data.packedMLE (fun _ => coordinatePoly)) i).val = 0
    rw [data.unpack_packedMLE]
    intro i
    simp [coordinatePoly]

/-- The head has certified round-by-round error `2/3` with this nonfunctional commitment. -/
example {σ : Type} (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    Verifier.rbrKnowledgeSoundnessWith init impl
      (Head.relIn data 1 pointLayout pointBound)
      (Head.relOut data 1 pointLayout bat.toBatchingRule pointBound)
      (Head.verifier data 1 pointLayout codec bat.toBatchingRule pointBound).toVerifier
      (Head.WitMid data 1 pointLayout)
      (Head.extractor (M := data.ιP → data.E) data 1 pointLayout bat.toBatchingRule pointBound)
      (Head.knowledgeStateFunction data 1 pointLayout codec bat.toBatchingRule pointBound init impl)
      (Head.rbrError (M := data.ιP → data.E) data bat) :=
  Head.rbrKnowledgeSoundnessWith_of_partials_eq data 1 pointLayout codec bat pointBound
    (fun _ _ _ _ hp hp' i => (hp i).trans (hp' i).symm) (fun _ _ h => h) init impl

/-- info: 'RingSwitching.Packing.Head.pr_exists_derivedTarget_le_of_partials_eq' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Head.pr_exists_derivedTarget_le_of_partials_eq

/-- info: 'RingSwitching.Packing.Head.rbrKnowledgeSoundnessWith_of_partials_eq'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Head.rbrKnowledgeSoundnessWith_of_partials_eq

end RingSwitching.Packing.Tests.Head

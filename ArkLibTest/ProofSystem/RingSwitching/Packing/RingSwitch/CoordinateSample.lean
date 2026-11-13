/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.ProofSystem.RingSwitching.Packing.RingSwitch
import ArkLib.ProofSystem.RingSwitching.Packing.Batching.CoordinateSample
import Mathlib.Algebra.Algebra.Pi
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.Algebra.Field.ZMod

/-!
# Complete scalar-to-opening acceptance over unequal ranks

The packing algebra has rank one and the opening algebra rank two over `ZMod 7`.
A nonconstant source and exact functional commitment instantiate full completeness and
RBR security. The fixture checks the derived target and same-source terminal relation,
rejection of a changed opening value, and absorbing rejection of a false head message
for every continuation transcript.
-/

noncomputable section
namespace RingSwitching.Packing.Tests.CoordinateSampleOpening
open Module MvPolynomial OracleSpec OracleComp ProtocolSpec
open scoped NNReal ENNReal

instance : Fact (Nat.Prime 7) := ⟨by decide⟩

abbrev data : PackingData (ZMod 7) where
  P := ZMod 7
  E := Fin 2 → ZMod 7
  ιP := Fin 1
  ιE := Fin 2
  packBasis := Basis.singleton _ _
  openBasis := Pi.basisFun _ _

def layout : ClaimLayout data 1 where
  Source := Fin 1 → (ZMod 7)⦃≤ 1⦄[X Fin 1]
  Query := Fin 1 → data.E
  components := Equiv.refl _
  point := id
  weight _ _ := 1
  eval q p := ∑ i, aeval q (p i).val
  reconstruct _ _ := by simp

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

abbrev bat := BatchingStrategy.coordinateSample (ZMod 7) (Fin 2)
abbrev multiplier := Head.multiplier data 1 layout bat.toBatchingRule

example {σ : Type} (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    (RingSwitch.reduction data 1 layout codec bat.toBatchingRule pc).perfectCompleteness init impl
      (Head.relIn data 1 layout pc) (pc.evalRelWithContext (layout.Query × bat.Challenge)) :=
  RingSwitch.perfectCompleteness data 1 layout codec bat.toBatchingRule pc init impl

example {σ : Type} (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    (RingSwitch.verifier data 1 layout codec bat.toBatchingRule
      pc).toVerifier.rbrKnowledgeSoundness
      init impl (Head.relIn data 1 layout pc) (pc.evalRelWithContext (layout.Query × bat.Challenge))
      (RingSwitch.rbrError (M := data.ιP → data.E) data 1 bat) :=
  RingSwitch.rbrKnowledgeSoundness data 1 layout codec bat pc
    pc_functional (fun _ _ h => h) init impl

def source : Fin 1 → (ZMod 7)⦃≤ 1⦄[X Fin 1] := fun _ =>
  ⟨X 0, by
    rw [mem_restrictDegree_iff_degreeOf_le]
    intro i
    exact degreeOf_X_le i 0⟩

def point : Fin 1 → data.E := fun _ => ![1, 3]

def packed : data.P⦃≤ 1⦄[X Fin 1] := data.packedMLE (layout.components source)

example : bat.error = (1 : ℝ≥0) / 2 := by
  norm_num [bat, BatchingStrategy.coordinateSample]

example (i : (RingSwitch.pSpec (M := data.ιP → data.E) data 1 bat.toBatchingRule).ChallengeIdx)
    (j : (ProductSumcheck.pSpec (ZMod 7) 1).ChallengeIdx)
    (h : i = ChallengeIdx.sumEquiv (.inr j)) :
    RingSwitch.rbrError (M := data.ιP → data.E) data 1 bat i = 2 / 7 := by
  subst i
  exact RingSwitch.rbrError_tail data 1 bat j

/-- The nonconstant source is queried at two distinct opening coordinates. -/
theorem partials_eq : Head.partials data 1 layout point source = ![![1, 3]] := by
  change (fun i => aeval point (source i).val) = _
  ext i u
  fin_cases i
  fin_cases u <;> norm_num [data, source, point]

/-- The displayed scalar claim is an honest input on the original packed commitment. -/
theorem honest_input : (((point, ![1, 3]), honest.commit packed), source) ∈
    Head.relIn data 1 layout pc := by
  constructor
  · change (![1, 3] : data.E) = ∑ i : Fin 1, Head.partials data 1 layout point source i
    rw [Fin.sum_univ_one]
    exact (congrFun partials_eq 0).symm
  · rfl

/-- Choosing the second coordinate changes the derived target to three. -/
theorem derived_target_eq :
    data.derivedTarget (Head.partials data 1 layout point source)
      (bat.weight (1 : Fin 2)) = (3 : ZMod 7) := by
  rw [partials_eq]
  change (∑ u : Fin 2, (if u = (1 : Fin 2) then (1 : ZMod 7) else 0) *
    data.transpose ![![1, 3]] u) = 3
  simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  rw [data.transpose_apply]
  change (∑ i : Fin 1, (Pi.basisFun (ZMod 7) (Fin 2)).repr
    (![![1, 3]] i) (1 : Fin 2) • (Basis.singleton (Fin 1) (ZMod 7)) i) = 3
  simp

/-- The terminal statement uses that same public point and batching coordinate. -/
def lastStatement :
    ProductSumcheck.Statement (layout.Query × bat.Challenge) (ZMod 7) (Fin.last 1) :=
  ⟨(point, (1 : Fin 2)), fun _ => 1, 3⟩

theorem multiplier_at_one :
    (multiplier lastStatement.ctx).val.eval lastStatement.challenges =
      (3 : ZMod 7) := by
  change (data.multiplier point (bat.weight (1 : Fin 2))).val.eval
    ((fun _ => (1 : Fin 2)) : Fin 1 → ZMod 7) = 3
  rw [data.multiplier_eval_zeroOne]
  change (∑ u : Fin 2, data.eqCoord point (fun _ => 1) u *
    (if u = (1 : Fin 2) then (1 : ZMod 7) else 0)) = 3
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  change (Pi.basisFun (ZMod 7) (Fin 2)).repr
    (eqTilde point ((fun _ => (1 : Fin 2)) : Fin 1 → data.E)) (1 : Fin 2) = 3
  rw [Pi.basisFun_repr]
  simp [MvPolynomial.eqTilde_eq_prod, point]

/-- The same packed source opens to one at the terminal point. -/
theorem packed_at_one : aeval lastStatement.challenges packed.val = (1 : ZMod 7) := by
  change packed.val.eval lastStatement.challenges = 1
  rw [packed, data.packedMLE_eval]
  change (∑ i : Fin 1, (Basis.singleton (Fin 1) (ZMod 7)) i *
    aeval lastStatement.challenges (source i).val) = 1
  simp only [Basis.singleton_apply, one_mul, Fin.sum_univ_one]
  change aeval (fun _ : Fin 1 => (1 : ZMod 7)) (X 0 : MvPolynomial (Fin 1) (ZMod 7)) = 1
  simp

/-- The true terminal relation retains the original commitment and polynomial. -/
example : ((lastStatement, honest.commit packed), packed) ∈
    ProductSumcheck.rel multiplier pc (Fin.last 1) := by
  apply (ProductSumcheck.rel_last _ _ _ _ _).mpr
  exact ⟨by rw [multiplier_at_one, packed_at_one]; change (3 : ZMod 7) = 3 * 1; norm_num, rfl⟩

/-- A changed final value really aborts the materialized verifier. -/
example : (ProductSumcheck.Terminal.verifier multiplier pc).toVerifier.verify
    (lastStatement, honest.commit packed)
    (ProductSumcheck.Terminal.transcript (0 : ZMod 7)) = failure := by
  classical
  have hc : ¬ ProductSumcheck.Terminal.check multiplier lastStatement 0 := by
    change ¬ (3 : ZMod 7) = _ * 0
    simpa only [mul_zero] using (show (3 : ZMod 7) ≠ 0 by decide)
  calc
    _ = (if ProductSumcheck.Terminal.check multiplier lastStatement 0 then
      pure (ProductSumcheck.Terminal.nextStatement lastStatement 0, honest.commit packed)
      else failure) :=
        ProductSumcheck.Terminal.verifier_verify multiplier pc lastStatement
          (honest.commit packed) (ProductSumcheck.Terminal.transcript 0)
    _ = failure := ite_eq_right hc

/-- A changed component family used to test the full protocol. -/
def badHeadTranscript :
    FullTranscript (Head.pSpec (M := data.ιP → data.E) data bat.toBatchingRule) :=
  FullTranscript.mk2 (0 : data.ιP → data.E) (1 : Fin 2)

/-- A false component message aborts the complete protocol for every continuation transcript. -/
example (tailTr : FullTranscript (ProductSumcheck.pSpec (ZMod 7) 1)) :
    (RingSwitch.verifier data 1 layout codec bat.toBatchingRule pc).toVerifier.verify
      ((point, ![1, 3]), honest.commit packed)
      (badHeadTranscript ++ₜ tailTr) = failure := by
  classical
  have hc : ¬ Head.check data 1 layout (point, ![1, 3]) 0 := by
    change ¬ (![1, 3] : Fin 2 → ZMod 7) = ∑ _i : Fin 1, 1 * 0
    simp only [mul_zero, Fin.sum_univ_one]
    intro h
    have h0 := congrFun h 0
    norm_num at h0
  have hfalse : (Head.guardedForm data 1 layout codec bat.toBatchingRule pc).check
      ((point, ![1, 3]), honest.commit packed) badHeadTranscript = false := by
    rw [Head.guardedForm_check]
    change decide (Head.check data 1 layout (point, ![1, 3]) 0) = false
    exact decide_eq_false hc
  calc
    _ = _ := (RingSwitch.guardedForm data 1 layout codec bat.toBatchingRule pc).verify_eq _ _
    _ = failure := by
      simp only [RingSwitch.guardedForm, Verifier.GuardedForm.append,
        FullTranscript.append_fst, hfalse, Bool.false_and, Bool.false_eq_true, ↓reduceIte]

example : Fintype.card
    (RingSwitch.pSpec (M := data.ιP → data.E) data 1 bat.toBatchingRule).MessageIdx = 3 := by decide
example : Fintype.card
    (RingSwitch.pSpec (M := data.ιP → data.E) data 1 bat.toBatchingRule).ChallengeIdx = 2 := by
  decide

end RingSwitching.Packing.Tests.CoordinateSampleOpening

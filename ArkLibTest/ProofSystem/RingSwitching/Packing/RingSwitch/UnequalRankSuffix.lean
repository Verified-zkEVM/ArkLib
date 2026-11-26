/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ProofSystem.RingSwitching.Packing.RingSwitch
import Mathlib.FieldTheory.Finite.GaloisField

/-!
# Suffix ring switching with unequal nontrivial ranks

The base is F₂, packing algebra F₁₆, opening algebra F₈ and challenge algebra F₁₆. Two suffix
bits are packed; one leading variable is retained. The nonconstant source is `X₀ + X₁X₂`.
The oracle exposes the entire packed polynomial, so this is a protocol specification fixture,
not a succinct commitment scheme. Its total challenge error is `1/4`.
-/
noncomputable section
namespace RingSwitching.Packing.Tests.UnequalRankSuffix
open Module MvPolynomial OracleSpec OracleComp ProtocolSpec
open scoped NNReal

abbrev F2 := ZMod 2
abbrev F16 := GaloisField 2 4
abbrev F8 := GaloisField 2 3
instance : Fintype F16 := Fintype.ofFinite _
instance : Fintype F8 := Fintype.ofFinite _
instance : SampleableType F16 := SampleableType.ofFintype F16

def bP : Basis (Fin 2 → Fin 2) F2 F16 :=
  (Module.finBasisOfFinrankEq F2 F16 (GaloisField.finrank 2 (by norm_num))).reindex
    (Fintype.equivFinOfCardEq (by simp)).symm

def bE : Basis (Fin 3) F2 F8 :=
  Module.finBasisOfFinrankEq F2 F8 (GaloisField.finrank 2 (by norm_num))

abbrev data : PackingData F2 where
  P := F16
  E := F8
  ιP := Fin 2 → Fin 2
  ιE := Fin 3
  packBasis := bP
  openBasis := bE

abbrev layout : ClaimLayout data 1 :=
  ClaimLayout.packedSuffixLayout data 1 2 (Equiv.refl _)
abbrev codec : (data.ιP → data.E) ≃ (data.ιP → data.E) := Equiv.refl _
abbrev bat : BatchingStrategy F16 data.ιE := BatchingStrategy.gammaPowers F16 3

def pc : PackedCommitment data.P 1 where
  ιC := Unit
  OStmt _ := data.P⦃≤ 1⦄[X Fin 1]
  Oᵢ _ := OracleInterface.instDefault
  commitsTo ost p := ost () = p

def honest : pc.Honest where
  commit p _ := p
  commitsTo_commit _ := rfl

theorem functional : pc.Functional := fun h h' => h.symm.trans h'

def source : layout.Source := ⟨X 0 + X 1 * X 2, by
  rw [mem_restrictDegree_iff_degreeOf_le]
  intro i
  apply (degreeOf_add_le i _ _).trans
  apply max_le (degreeOf_X_le i 0)
  apply (degreeOf_mul_le i _ _).trans
  fin_cases i <;> norm_num [degreeOf_X]⟩

def query : layout.Query := (fun _ => 1, ![0, 1])
abbrev packed := data.packedMLE (layout.components source)

/-- A retained-variable change alters the source evaluation. -/
example : aeval (fun _ : Fin 3 => (0 : F8)) source.val = 0 ∧
    aeval (![1, 0, 1] : Fin 3 → F8) source.val = 1 := by
  simp [source]

/-- Completeness has a concrete honest premise on the original packed polynomial. -/
theorem honest_input : (((query, layout.eval query source), honest.commit packed), source) ∈
    Head.relIn data 1 layout pc := Head.mem_relIn_commit data 1 layout pc honest _ _

example {σ : Type} (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    (RingSwitch.reduction data 1 layout codec bat.toBatchingRule pc).perfectCompleteness
      init impl (Head.relIn data 1 layout pc)
      (pc.evalRelWithContext (layout.Query × bat.Challenge)) :=
  RingSwitch.perfectCompleteness data 1 layout codec bat.toBatchingRule pc init impl

example {σ : Type} (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    (RingSwitch.verifier data 1 layout codec bat.toBatchingRule
      pc).toVerifier.rbrKnowledgeSoundness
      init impl (Head.relIn data 1 layout pc)
      (pc.evalRelWithContext (layout.Query × bat.Challenge)) (RingSwitch.rbrError (M := data.ιP →
        data.E) data 1 bat) :=
  RingSwitch.rbrKnowledgeSoundness data 1 layout codec bat pc functional
    (fun _ _ h => h) init impl

/-- This is the sum over the full protocol's challenge indices. -/
example : (∑ i, RingSwitch.rbrError (M := data.ιP → data.E) data 1 bat i) = 1 / 4 := by
  rw [RingSwitch.rbrError_sum]
  have hc : Fintype.card F16 = 16 := by
    rw [Fintype.card_eq_nat_card, GaloisField.card 2 4 (by norm_num)]
    norm_num
  norm_num [bat, BatchingStrategy.gammaPowers, hc]

example : (1 / 4 : ℝ≥0) < 1 := by norm_num

/-- Changing the scalar claim makes the honest carrier fail the full verifier,
for every continuation transcript. -/
example (c : bat.Challenge) (tailTr : FullTranscript (ProductSumcheck.pSpec F16 1)) :
    (RingSwitch.verifier data 1 layout codec bat.toBatchingRule pc).toVerifier.verify
      ((query, layout.eval query source + 1), honest.commit packed)
      ((FullTranscript.mk2 (Head.partials data 1 layout query source) c) ++ₜ tailTr) =
        failure := by
  classical
  have hc : ¬ Head.check data 1 layout
      (query, layout.eval query source + 1) (Head.partials data 1 layout query source) := by
    change ¬ layout.eval query source + 1 =
      ∑ i, layout.weight query i * Head.partials data 1 layout query source i
    change ¬ layout.eval query source + 1 = ∑ i, layout.weight query i *
      aeval (layout.point query) (layout.components source i).val
    rw [← layout.reconstruct query source]
    exact fun h => one_ne_zero (add_left_cancel (h.trans (add_zero _).symm))
  have hfalse : (Head.guardedForm data 1 layout codec bat.toBatchingRule pc).check
      ((query, layout.eval query source + 1), honest.commit packed)
      (FullTranscript.mk2 (Head.partials data 1 layout query source) c) = false := by
    rw [Head.guardedForm_check]
    change decide (Head.check data 1 layout (query, layout.eval query source + 1)
      (Head.partials data 1 layout query source)) = false
    exact decide_eq_false hc
  calc
    _ = _ := (RingSwitch.guardedForm data 1 layout codec bat.toBatchingRule pc).verify_eq _ _
    _ = failure := by
      simp only [RingSwitch.guardedForm, Verifier.GuardedForm.append,
        FullTranscript.append_fst, hfalse, Bool.false_and, Bool.false_eq_true, ↓reduceIte]

/-- Both complete protocol parameters are nontrivial and independent. -/
example : Fintype.card data.ιP = 4 ∧ Fintype.card data.ιE = 3 := by decide
example : Fintype.card (RingSwitch.pSpec (M := data.ιP → data.E) data 1
  bat.toBatchingRule).MessageIdx = 3 := by decide
example : Fintype.card (RingSwitch.pSpec (M := data.ιP → data.E) data 1
  bat.toBatchingRule).ChallengeIdx = 2 := by decide
abbrev multiplier := Head.multiplier data 1 layout bat.toBatchingRule
abbrev headStmt (c : bat.Challenge) :
    ProductSumcheck.Statement (layout.Query × bat.Challenge) F16 (0 : Fin 2) :=
  Head.nextStatement data 1 layout bat.toBatchingRule
  (query, layout.eval query source) (Head.partials data 1 layout query source) c
abbrev roundPoly (c : bat.Challenge) :=
  ProductSumcheck.Round.honestMessage multiplier 0 (headStmt c) packed
abbrev lastStmt (c : bat.Challenge) (z : F16) :
    ProductSumcheck.Statement (layout.Query × bat.Challenge) F16 (Fin.last 1) :=
  ProductSumcheck.Round.nextStatement (m := 1) (0 : Fin 1) (headStmt c) (roundPoly c) z
abbrev finalValue (c : bat.Challenge) (z : F16) := aeval (lastStmt c z).challenges packed.val

/-- The single honest sumcheck round transcript. -/
def componentTr (c : bat.Challenge) (z : F16) :
    FullTranscript (ProductSumcheck.Round.pSpec F16) :=
  FullTranscript.mk2 (roundPoly c) z

def loopState (c : bat.Challenge) (z : F16) (i : Fin 2) :
    ProductSumcheck.Statement (layout.Query × bat.Challenge) F16 i × (∀ j, pc.OStmt j) :=
  match i with
  | ⟨0, _⟩ => (headStmt c, honest.commit packed)
  | ⟨1, _⟩ => (lastStmt c z, honest.commit packed)

theorem loop_accepts (c : bat.Challenge) (z : F16) :
    (ProductSumcheck.loopVerifier (C := F16)
      (Context := layout.Query × bat.Challenge) pc).toVerifier.run
      (headStmt c, honest.commit packed)
      (FullTranscript.seqCompose (fun _ : Fin 1 => componentTr c z)) =
      pure (lastStmt c z, honest.commit packed) := by
  classical
  rw [ProductSumcheck.loopVerifier_toVerifier]
  apply Verifier.seqCompose_run_eq_pure _ _ _ (loopState c z)
  intro i
  fin_cases i
  change (ProductSumcheck.Round.verifier pc 0).toVerifier.verify
    (headStmt c, honest.commit packed) (FullTranscript.mk2 (roundPoly c) z) = _
  rw [ProductSumcheck.Round.verifier_verify]
  change (if ProductSumcheck.Round.check 0 (headStmt c) (roundPoly c) then
    pure (lastStmt c z, honest.commit packed) else failure) = _
  rw [ite_eq_left (ProductSumcheck.Round.check_honestMessage_of_mem_rel multiplier pc 0
    (Head.nextStatement_mem_relOut data 1 layout bat.toBatchingRule pc honest_input c))]
  rfl

def fullTranscript (c : bat.Challenge) (z : F16) :
    FullTranscript (RingSwitch.pSpec (M := data.ιP → data.E) data 1 bat.toBatchingRule) :=
  FullTranscript.mk2 (Head.partials data 1 layout query source) c ++ₜ
    (FullTranscript.seqCompose (fun _ : Fin 1 => componentTr c z) ++ₜ
      ProductSumcheck.Terminal.transcript (finalValue c z))

/-- Full verification preserves the original suffix query and commitment. -/
theorem full_accepts (c : bat.Challenge) (z : F16) :
    (RingSwitch.verifier data 1 layout codec bat.toBatchingRule pc).toVerifier.run
      ((query, layout.eval query source), honest.commit packed) (fullTranscript c z) =
      pure (((query, c), ((lastStmt c z).challenges, finalValue c z)), honest.commit packed) := by
  classical
  have hhead : (Head.verifier data 1 layout codec bat.toBatchingRule pc).toVerifier.run
      ((query, layout.eval query source), honest.commit packed)
      (FullTranscript.mk2 (Head.partials data 1 layout query source) c) =
        pure (headStmt c, honest.commit packed) := by
    change (Head.verifier data 1 layout codec bat.toBatchingRule pc).toVerifier.verify _ _ = _
    rw [(Head.guardedForm data 1 layout codec bat.toBatchingRule pc).verify_eq]
    change (if decide (Head.check data 1 layout (query, layout.eval query source)
      (Head.partials data 1 layout query source)) then _ else _) = _
    rw [decide_eq_true (Head.check_partials_of_mem_relIn data 1 layout pc honest_input)]
    rfl
  have hterminal : (ProductSumcheck.Terminal.verifier multiplier pc).toVerifier.run
      (lastStmt c z, honest.commit packed) (ProductSumcheck.Terminal.transcript (finalValue c z)) =
        pure (((query, c), ((lastStmt c z).challenges, finalValue c z)), honest.commit packed) := by
    change (ProductSumcheck.Terminal.verifier multiplier pc).toVerifier.verify _ _ = _
    rw [ProductSumcheck.Terminal.verifier_verify]
    change (if ProductSumcheck.Terminal.check multiplier (lastStmt c z) (finalValue c z) then
      _ else _) = _
    rw [ite_eq_left (ProductSumcheck.Terminal.check_aeval_of_mem_rel multiplier pc
      (ProductSumcheck.Round.nextStatement_mem_rel multiplier pc 0
        (Head.nextStatement_mem_relOut data 1 layout bat.toBatchingRule pc honest_input c) z))]
    rfl
  rw [RingSwitch.verifier_toVerifier]
  erw [Verifier.append_run]
  erw [fullTranscript, FullTranscript.append_fst, FullTranscript.append_snd]
  rw [hhead, pure_bind, ProductSumcheck.verifier_toVerifier]
  erw [Verifier.append_run, FullTranscript.append_fst, FullTranscript.append_snd,
    loop_accepts, pure_bind, hterminal]

end RingSwitching.Packing.Tests.UnequalRankSuffix

/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLibTest.ProofSystem.RingSwitching.Packing.RingSwitch.UnequalRankSuffix
import ArkLib.ProofSystem.RingSwitching.Packing.ClaimLayout.Quirky

/-!
# Quirky ring switching with independent nontrivial ranks

The packing and challenge fields are F₁₆ and the opening field is F₈ over F₂. Packing indexes
`(skipped bit, extra bit)`, while the source table indexes `(retained bit, extra bit, skipped bit)`.
The interpolation-node query uses the quirky layout through the same complete protocol.
The transparent polynomial oracle is a specification fixture, not a succinct commitment scheme.
-/
noncomputable section
namespace RingSwitching.Packing.Tests.QuirkyRingSwitch
open Module MvPolynomial OracleSpec OracleComp ProtocolSpec
open scoped NNReal

abbrev F2 := UnequalRankSuffix.F2
abbrev F16 := UnequalRankSuffix.F16
abbrev F8 := UnequalRankSuffix.F8
abbrev Idx := (Fin 1 → Fin 2) × Fin 2

def bP : Basis Idx F2 F16 :=
  (Module.finBasisOfFinrankEq F2 F16 (GaloisField.finrank 2 (by norm_num))).reindex
    (Fintype.equivFinOfCardEq (by simp)).symm

def bE : Basis (Fin 3) F2 F8 :=
  Module.finBasisOfFinrankEq F2 F8 (GaloisField.finrank 2 (by norm_num))

abbrev data : PackingData F2 where
  P := F16
  E := F8
  ιP := Idx
  ιE := Fin 3
  packBasis := bP
  openBasis := bE

instance : Fact (IsField data.E) := ⟨Field.toIsField F8⟩

def nodes : (Fin 1 → Fin 2) ↪ data.E :=
  (Function.Embedding.nonempty_of_card_le (by
    rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin, Fintype.card_eq_nat_card,
      GaloisField.card 2 3 (by norm_num)]
    norm_num)).some

abbrev layout : ClaimLayout data 1 :=
  ClaimLayout.quirkyLayout data 1 1 nodes (Equiv.refl _)
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

def source : layout.Source := fun yb σ =>
  (yb.1 0 : F2) + (yb.2 : F2) * (σ 0 : F2)

def query : layout.Query := (fun _ => 1, 1, nodes (fun _ => 0))
abbrev packed := data.packedMLE (layout.components source)

/-- The source table varies in the retained coordinate. -/
example : source ((fun _ => 0), 0) (fun _ => 0) = 0 ∧
    source ((fun _ => 1), 0) (fun _ => 0) = 1 := by
  constructor <;> rfl

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
end RingSwitching.Packing.Tests.QuirkyRingSwitch

/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/
module

public import ArkLib.ProofSystem.Fri.Spec.KnowledgeSoundness
public import ArkLib.ProofSystem.Fri.Spec.Extraction.ClosedCost
public import ArkLib.OracleReduction.Security.Resources

/-!
# Knowledge soundness of FRI with measured extraction

The named FRI extractor executes the instruction program `Extractor.extractProgram` on the
retained commitment history and folding challenges. Its knowledge-soundness error is the existing
`soundnessError`, and every execution path of that program stays within the operation-count
vector `Extractor.extractorProfileBound`, on every history, including rejected ones.

The counts cover field additions, subtractions, multiplications, inversions and equality tests,
reads of retained words, domain points, folding challenges and the final polynomial, coefficient
and cache reads, and designated metadata ticks. They exclude:

* reconstructing the retained history and challenges from the input statement and transcript,
  which is the measured program's uncharged view;
* evaluating any instruction handler, such as a retained word, a domain point, the final
  polynomial, a field operation or a polynomial degree, beyond its unit charge;
* Lean code between instructions, including index arithmetic, list and array traversal, and
  allocation;
* the bit complexity of field elements.

The bounds are therefore operation counts for the stated instruction set, not running time.
Closed forms for the field-operation coordinates are in `Extraction/ClosedCost.lean`.
-/

@[expose] public section

namespace Fri.Spec
open Domain OracleComp OracleSpec ProtocolSpec CompPoly
open scoped NNReal
variable {F : Type} [NonBinaryField F] [Fintype F] [DecidableEq F]
variable {n k : ℕ} {ω : SmoothCosetFftDomain n F}
variable (s : Fin (k + 1) → ℕ+) (d : ℕ+) (l : ℕ)

namespace Extractor

/-- A profile is the run of the certified handlers with VCVio's additive cost instrumentation. -/
theorem profile_eq_runAdd {A : Type} (o : ∀ j, FinalOracleStatement s ω j)
    (α : FinalStatement F k) (program : OracleComp (InstructionSpec s o α) A) :
    profile s o α program =
      (simulateQ (QueryImpl.withAddCost (instructionAnswer s o α) (instructionCost s))
        program).runAdd :=
  rfl

/-- The measured program of `extract`. Its view is the retained commitment history and folding
challenges of the pre-query transcript prefix; computing that view is not charged. -/
def measuredProgram (hs : (∑ j, (s j).val) ≤ n) :
    _root_.Extractor.Straightline.MeasuredProgram []ₒ
      (Statement F (0 : Fin (k + 1)) × ∀ j, OracleStatement s ω 0 j)
      (Witness F s d 0) (Witness F s d (Fin.last (k + 1))) (pSpec k (ω := ω) s l) Cost where
  View := (∀ j, FinalOracleStatement s ω j) × FinalStatement F k
  view := fun ⟨stmt, _, tr, _, _⟩ ↦ (queryHistory s l (initialOracle s stmt) (queryPrefix s l tr),
    queryFoldChallenges s l (queryPrefix s l tr))
  Op := ArithmeticOp F ⊕ AccessOp s ω
  spec v := InstructionSpec s v.1 v.2
  program v := extractProgram s d hs v.1 v.2
  answer v := instructionAnswer s v.1 v.2
  cost := instructionCost s

/-- The named extractor is the execution of its measured program. -/
theorem measuredProgram_realizesExtractor (hs : (∑ j, (s j).val) ≤ n) :
    (measuredProgram (ω := ω) s d l hs).RealizesExtractor (extract s d hs l) := by
  intro stmt wit tr proveQueryLog verifyQueryLog
  rw [extract_run, extractHistory_eq_profile, profile_fst]
  rfl

/-- Every execution path of the measured program stays within `extractorProfileBound`. -/
theorem measuredProgram_costAtMost (hs : (∑ j, (s j).val) ≤ n) :
    (measuredProgram (ω := ω) s d l hs).CostAtMost (extractorProfileBound n s d) :=
  OracleComp.MeasuredProgram.costAtMost_of_forall_eq_answer _ _
    (fun v ↦ eq_instructionAnswer s v.1 v.2)
    (fun v ↦ by
      change (simulateQ (QueryImpl.withAddCost (instructionAnswer s v.1 v.2) (instructionCost s))
        (extractProgram s d hs v.1 v.2)).runAdd.2 ≤ _
      rw [← profile_eq_runAdd]
      exact profile_extractProgram_apply_le s v.1 v.2 d hs)

end Extractor

variable [SampleableType F]

/-- The named extractor satisfies the knowledge-soundness game with error `soundnessError`, and
its measured program stays within the operation-count vector `extractorProfileBound` on every
retained history. The counts exclude reconstructing that history, evaluating any instruction
handler beyond its unit charge, Lean code between instructions, and the bit complexity of field
elements. -/
theorem knowledgeSoundnessWithResources_extract
    (hdom : 2 ^ (∑ j, (s j).val) * d.val ≤ 2 ^ n)
    (θ : ℝ) (δ : ℝ≥0)
    (hrate : min θ δ ≤ 1 - (2 ^ (∑ j, (s j).val) * d.val : ℕ) / (2 ^ n : ℝ))
    [∀ j, SampleableType ((pSpec k (ω := ω) s l).Challenge j)]
    {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl (emptySpec.{0, 0}) (StateT σ ProbComp)) :
    (reduction k (ω := ω) s d hdom l).verifier.knowledgeSoundnessWithResources init impl
      (inputRelation k s d hdom δ) (outputRelation k s d hdom δ)
      (Extractor.extract s d (round_bound hdom) l)
      (soundnessError (ω := ω) s d l θ δ)
      (Extractor.measuredProgram s d l (round_bound hdom))
      (Extractor.extractorProfileBound n s d) :=
  ⟨knowledge_soundness_with s d l hdom θ δ hrate init impl,
    Extractor.measuredProgram_realizesExtractor s d l (round_bound hdom),
    Extractor.measuredProgram_costAtMost s d l (round_bound hdom)⟩

end Fri.Spec

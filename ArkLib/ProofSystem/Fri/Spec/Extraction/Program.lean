/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/
module

public import ArkLib.ProofSystem.Fri.Spec.Extraction.Check
public import ArkLib.ProofSystem.Fri.Spec.Extraction.Scan
public import ArkLib.ProofSystem.Fri.Spec.VerifierExecution
public import ArkLib.ToCompPoly.Univariate.Size

/-!
# A measured straightline FRI extractor

The extractor rejects an oversized final polynomial, scans the actual retained history in domain
order, and interpolates the first sufficiently many accepting positions. Its named executable
result is the erasure of its measured instruction program. The full-transcript wrapper reads only
the prefix preceding query sampling.
-/

@[expose] public section

namespace Fri.Spec.Extractor
open Domain OracleComp OracleSpec CompPoly
variable {F : Type} [NonBinaryField F] [Fintype F] [DecidableEq F]
variable {n k : ℕ} {ω : SmoothCosetFftDomain n F}
variable (s : Fin (k + 1) → ℕ+) (d : ℕ+)

/-- Interpolate the cached selected positions when their count reaches the required degree bound. -/
def interpolateSelection (o : ∀ j, FinalOracleStatement s ω j) (α : FinalStatement F k)
    (state : Selection s o (foldingDegree s d 0)) :
    OracleComp (InstructionSpec s o α) (Option (Witness F s d 0)) := do
  if _ : foldingDegree s d 0 ≤ state.count then
    let p ← liftComp
      (Arithmetic.interpolate state.nodes state.values (foldingDegree s d 0)) _
    let degree ← readDegree s o α p.val
    if hd : degree.val < foldingDegree s d 0 then
      have hdegree : p.val.natDegree < foldingDegree s d 0 := by
        simpa [degree.property] using hd
      have hsize := CPolynomial.size_le_of_natDegree_lt p.val hdegree
      have hw : p.val ∈ CPolynomial.degreeLT (foldingDegree s d 0) :=
        CPolynomial.mem_degreeLT_iff_size_le.mpr hsize
      pure (some ⟨p.val, hw⟩)
    else
      pure none
  else
    pure none

/-- The complete extraction algorithm over the charged immutable-input backend. -/
def extractProgram (hs : (∑ j, (s j).val) ≤ n)
    (o : ∀ j, FinalOracleStatement s ω j) (α : FinalStatement F k) :
    OracleComp (InstructionSpec s o α) (Option (Witness F s d 0)) := do
  let input? ← prepareInputs s o α d
  match input? with
  | none => pure none
  | some input =>
    let state ← scan s o α hs input.generator (checkPosition s o α hs input)
      (foldingDegree s d 0)
    interpolateSelection s d o α state.val

/-- Erase the measured execution of the retained-history extractor. -/
def extractHistory (hs : (∑ j, (s j).val) ≤ n)
    (o : ∀ j, FinalOracleStatement s ω j) (α : FinalStatement F k) :
    Option (Witness F s d 0) :=
  (profile s o α (extractProgram s d hs o α)).1

/-- Extract from the retained prefix of a full transcript. -/
def extract (hs : (∑ j, (s j).val) ≤ n) (l : ℕ) :
    Extractor.Straightline []ₒ
      (Statement F (0 : Fin (k + 1)) × ∀ j, OracleStatement s ω 0 j)
      (Witness F s d 0) (Witness F s d (Fin.last (k + 1))) (pSpec k (ω := ω) s l) :=
  fun stmt _ tr _ _ ↦ OptionT.mk (pure (extractHistory s d hs
    (queryHistory s l (initialOracle s stmt) (queryPrefix s l tr))
    (queryFoldChallenges s l (queryPrefix s l tr))))

/-- Retained-history extraction is exactly the result of its measured instruction program. -/
theorem extractHistory_eq_profile (hs : (∑ j, (s j).val) ≤ n)
    (o : ∀ j, FinalOracleStatement s ω j) (α : FinalStatement F k) :
    extractHistory s d hs o α = (profile s o α (extractProgram s d hs o α)).1 :=
  rfl

/-- The full extractor runs the retained-history algorithm on precisely the pre-query prefix. -/
theorem extract_run (hs : (∑ j, (s j).val) ≤ n) (l : ℕ)
    (stmt : Statement F (0 : Fin (k + 1)) × ∀ j, OracleStatement s ω 0 j)
    (wit : Witness F s d (Fin.last (k + 1)))
    (tr : (pSpec k (ω := ω) s l).FullTranscript)
    (proveLog verifyLog : QueryLog []ₒ) :
    (extract s d hs l stmt wit tr proveLog verifyLog).run =
      pure (extractHistory s d hs
        (queryHistory s l (initialOracle s stmt) (queryPrefix s l tr))
        (queryFoldChallenges s l (queryPrefix s l tr))) :=
  rfl

/-- Extraction is unchanged by later query challenges, output witnesses, or query logs. -/
theorem extract_eq_of_queryPrefix_eq (hs : (∑ j, (s j).val) ≤ n) (l : ℕ)
    (stmt : Statement F (0 : Fin (k + 1)) × ∀ j, OracleStatement s ω 0 j)
    (wit₁ wit₂ : Witness F s d (Fin.last (k + 1)))
    (tr₁ tr₂ : (pSpec k (ω := ω) s l).FullTranscript)
    (proveLog₁ verifyLog₁ proveLog₂ verifyLog₂ : QueryLog []ₒ)
    (h : queryPrefix s l tr₁ = queryPrefix s l tr₂) :
    extract s d hs l stmt wit₁ tr₁ proveLog₁ verifyLog₁ =
      extract s d hs l stmt wit₂ tr₂ proveLog₂ verifyLog₂ := by
  unfold extract
  rw [h]

end Fri.Spec.Extractor

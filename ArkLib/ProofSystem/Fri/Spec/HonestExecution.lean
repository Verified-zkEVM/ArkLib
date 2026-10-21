/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
module

public import ArkLib.ProofSystem.Fri.Spec.FoldExecution

/-!
# Honest FRI commitment histories

The honest polynomial chain folds the supplied computational witness at every stage.
The retained history keeps the original input word, including any errors, and commits exact
polynomial evaluations at every later stage. The final entry is the folded polynomial itself.
-/

@[expose] public section

namespace Fri.Spec

open Domain OracleComp OracleSpec ProtocolSpec Finset
open scoped NNReal

variable {F : Type} [NonBinaryField F] [DecidableEq F]
variable {n k : ℕ} {ω : SmoothCosetFftDomain n F}
variable (s : Fin (k + 1) → ℕ+) (d : ℕ+)

/-- The degree-bounded witness after the first `i` folding challenges. -/
def honestPolynomial (p₀ : Witness F s d 0) (α : Fin (k + 1) → F)
    (i : Fin (k + 2)) : Witness F s d i :=
  Fin.induction p₀ (fun j p ↦
    ⟨CompPoly.CPolynomial.FoldingPolynomial.cpolyFold p.1 (2 ^ (s j).val) (α j),
      witness_lift p.2⟩) i

@[simp]
theorem honestPolynomial_zero (p₀ : Witness F s d 0) (α : Fin (k + 1) → F) :
    honestPolynomial s d p₀ α 0 = p₀ := rfl

@[simp]
theorem honestPolynomial_succ (p₀ : Witness F s d 0) (α : Fin (k + 1) → F)
    (i : Fin (k + 1)) :
    (honestPolynomial s d p₀ α i.succ).val =
      CompPoly.CPolynomial.FoldingPolynomial.cpolyFold
        (honestPolynomial s d p₀ α i.castSucc).val (2 ^ (s i).val) (α i) := by
  unfold honestPolynomial
  rw [Fin.induction_succ]


/-- Only challenges preceding a stage affect its honest polynomial. -/
theorem honestPolynomial_congr (p₀ : Witness F s d 0) {α β : Fin (k + 1) → F}
    (i : Fin (k + 2)) (h : ∀ j, j.val < i.val → α j = β j) :
    honestPolynomial s d p₀ α i = honestPolynomial s d p₀ β i := by
  induction i using Fin.induction with
  | zero => rfl
  | succ i ih =>
    apply Subtype.ext
    rw [honestPolynomial_succ, honestPolynomial_succ,
      ih (fun j hj ↦ h j (by simpa using Nat.lt_succ_of_lt hj)), h i (by simp)]


variable [Fintype F]

/-- The retained non-final words: the supplied input followed by exact folded evaluations. -/
def honestWords (f : OracleStatement s ω (0 : Fin (k + 1)) 0)
    (p₀ : Witness F s d 0) (α : Fin (k + 1) → F) :
    ∀ j, OracleStatement s ω (Fin.last k) j :=
  Fin.cases f (fun i x ↦ (honestPolynomial s d p₀ α i.succ.castSucc).val.eval x.val)

@[simp]
theorem honestWords_zero (f : OracleStatement s ω (0 : Fin (k + 1)) 0)
    (p₀ : Witness F s d 0) (α : Fin (k + 1) → F) :
    honestWords s d f p₀ α 0 = f := rfl

@[simp]
theorem honestWords_succ (f : OracleStatement s ω (0 : Fin (k + 1)) 0)
    (p₀ : Witness F s d 0) (α : Fin (k + 1) → F) (i : Fin k)
    (x : (ω.subdomain (∑ j ∈ finRangeTo (k + 1) (i.val + 1), (s j).val)).toFinset) :
    honestWords s d f p₀ α i.succ x =
      (honestPolynomial s d p₀ α i.succ.castSucc).val.eval x.val := by
  rfl

/-- A retained word depends only on challenges strictly before its commitment. -/
theorem honestWords_congr (f : OracleStatement s ω (0 : Fin (k + 1)) 0)
    (p₀ : Witness F s d 0) {α β : Fin (k + 1) → F} (i : Fin (k + 1))
    (h : ∀ j, j.val < i.val → α j = β j) :
    honestWords s d f p₀ α i = honestWords s d f p₀ β i := by
  refine Fin.cases ?_ (fun i h ↦ ?_) i h
  · intro _
    rfl
  · funext x
    rw [honestWords_succ, honestWords_succ, honestPolynomial_congr s d p₀ _ h]

/-- The final honest folding challenge and the polynomial transmitted in response. -/
def honestFinalTranscript (p₀ : Witness F s d 0) (α : Fin (k + 1) → F) :
    (FinalFoldPhase.pSpec F).FullTranscript :=
  !h[α (Fin.last k), (honestPolynomial s d p₀ α (Fin.last (k + 1))).val]

/-- The actual final verifier's materialization of all honest commitments. -/
def honestHistory (f : OracleStatement s ω (0 : Fin (k + 1)) 0)
    (p₀ : Witness F s d 0) (α : Fin (k + 1) → F) :
    ∀ j, FinalOracleStatement s ω j :=
  (FinalFoldPhase.finalFoldVerifier s d).materializeOutput
    (honestFinalTranscript s d p₀ α).challenges (honestWords s d f p₀ α)
    (honestFinalTranscript s d p₀ α).messages

@[simp]
theorem committedWord_honestHistory (f : OracleStatement s ω (0 : Fin (k + 1)) 0)
    (p₀ : Witness F s d 0) (α : Fin (k + 1) → F) (i : Fin (k + 1)) :
    committedWord s (honestHistory s d f p₀ α) i = honestWords s d f p₀ α i :=
  FinalFoldPhase.committedWord_materialize s d _ _ i

@[simp]
theorem finalPolynomial_honestHistory (f : OracleStatement s ω (0 : Fin (k + 1)) 0)
    (p₀ : Witness F s d 0) (α : Fin (k + 1) → F) :
    finalPolynomial s (honestHistory s d f p₀ α) =
      (honestPolynomial s d p₀ α (Fin.last (k + 1))).val :=
  FinalFoldPhase.finalPolynomial_materialize s d _ _

/-- Histories generated from an initial word and a nearby polynomial witness. -/
def foldCompletenessRelation (δ : ℝ≥0) :
    Set ((FinalStatement F k × ∀ j, FinalOracleStatement s ω j) ×
      Witness F s d (Fin.last (k + 1))) :=
  {sw | ∃ f p₀ α,
    (Code.relHammingDist f (fun x ↦ p₀.val.eval x.val) : ℝ≥0) ≤ δ ∧
    sw = ((α, honestHistory s d f p₀ α), honestPolynomial s d p₀ α (Fin.last (k + 1)))}

omit [Fintype F] in
/-- Every polynomial witness satisfies its executable natural-degree bound. -/
theorem witness_natDegree_lt (i : Fin (k + 2)) (p : Witness F s d i) :
    p.val.natDegree < foldingDegree s d i := by
  rw [CompPoly.CPolynomial.natDegree_toPoly]
  by_cases hp : p.val.toPoly = 0
  · simpa [hp] using foldingDegree_pos s d i
  · apply (Polynomial.natDegree_lt_iff_degree_lt hp).mpr
    exact (Polynomial.mem_degreeLT.mp (CompPoly.CPolynomial.degreeLT_toPoly.mp p.property))

omit [Fintype F] in
/-- The final honest polynomial satisfies the final verifier's degree guard. -/
theorem honestPolynomial_last_natDegree_lt (p₀ : Witness F s d 0)
    (α : Fin (k + 1) → F) :
    (honestPolynomial s d p₀ α (Fin.last (k + 1))).val.natDegree < d.val := by
  simpa using witness_natDegree_lt s d _ (honestPolynomial s d p₀ α (Fin.last (k + 1)))

/-- The transmitted final polynomial and honest output witness satisfy radius-zero output. -/
theorem honestHistory_mem_outputRelation
    (hdom : (2 ^ (∑ i, (s i).val)) * d ≤ 2 ^ n)
    (f : OracleStatement s ω (0 : Fin (k + 1)) 0)
    (p₀ : Witness F s d 0) (α : Fin (k + 1) → F) :
    ((α, honestHistory s d f p₀ α), honestPolynomial s d p₀ α (Fin.last (k + 1))) ∈
      outputRelation k s d hdom 0 := by
  simp only [outputRelation, QueryRound.outputRelation, FinalFoldPhase.outputRelation,
    Set.mem_ofPred_eq]
  change (Code.relHammingDist
    (fun x : (ω.subdomain (∑ j, (s j).val)).toFinset ↦
      (finalPolynomial s (honestHistory s d f p₀ α)).eval x.val)
    (fun x ↦ (honestPolynomial s d p₀ α (Fin.last (k + 1))).val.eval x.val) : ℝ≥0) ≤ 0
  rw [finalPolynomial_honestHistory]
  simp [Code.relHammingDist]


/-- The exact statement, retained words, and witness at a non-final folding boundary. -/
def honestFoldState (f : OracleStatement s ω (0 : Fin (k + 1)) 0)
    (p₀ : Witness F s d 0) (α : Fin (k + 1) → F) (i : Fin (k + 1)) :
    (Statement F i × (∀ j, OracleStatement s ω i j)) × Witness F s d i.castSucc :=
  (foldState s (fun j ↦ α j.castSucc) (honestWords s d f p₀ α) i,
    honestPolynomial s d p₀ α i.castSucc)

/-- The initial honest boundary is exactly the supplied statement and computational witness. -/
theorem honestFoldState_zero_eq
    (stmt : Statement F (0 : Fin (k + 1)) × ∀ j, OracleStatement s ω 0 j)
    (p₀ : Witness F s d 0) (α : Fin (k + 1) → F) :
    honestFoldState s d (stmt.2 0) p₀ α 0 = (stmt, p₀) := by
  apply Prod.ext
  · apply Prod.ext
    · funext j
      exact j.elim0
    · funext j
      fin_cases j
      rfl
  · rfl

/-- A folding boundary depends only on previously received challenges. -/
theorem honestFoldState_congr (f : OracleStatement s ω (0 : Fin (k + 1)) 0)
    (p₀ : Witness F s d 0) {α β : Fin (k + 1) → F} (i : Fin (k + 1))
    (h : ∀ j, j.val < i.val → α j = β j) :
    honestFoldState s d f p₀ α i = honestFoldState s d f p₀ β i := by
  apply Prod.ext
  · apply Prod.ext
    · funext j
      exact h _ j.isLt
    · funext j
      exact honestWords_congr s d f p₀
        ⟨j.val, Nat.lt_of_lt_of_le j.isLt (Nat.succ_le_succ i.is_le)⟩
        (fun t ht ↦ h t (by
          change t.val < j.val at ht
          have hj : j.val < i.val + 1 := j.isLt
          exact lt_of_lt_of_le ht (by omega)))
  · exact honestPolynomial_congr s d p₀ i.castSucc h

/-- Changing a stage's challenge preserves the state entering that stage. -/
theorem honestFoldState_update
    (f : OracleStatement s ω (0 : Fin (k + 1)) 0) (p₀ : Witness F s d 0)
    (α : Fin (k + 1) → F) (i : Fin (k + 1)) (a : F) :
    honestFoldState s d f p₀ (Function.update α i a) i =
      honestFoldState s d f p₀ α i := by
  apply honestFoldState_congr
  intro j hj
  rw [Function.update_of_ne (by
    intro hij
    have hv := congrArg Fin.val hij
    omega)]

/-- Appending the next folded evaluation gives the next honest folding boundary. -/
theorem honestFoldState_succ (f : OracleStatement s ω (0 : Fin (k + 1)) 0)
    (p₀ : Witness F s d 0) (α : Fin (k + 1) → F) (i : Fin k) :
    (Fin.append (honestFoldState s d f p₀ α i.castSucc).1.1
      (fun _ : Fin 1 ↦ α i.castSucc),
      FoldPhase.appendFoldOracle s i (honestFoldState s d f p₀ α i.castSucc).1.2
        (honestPolynomial s d p₀ α i.succ.castSucc).val) =
      (honestFoldState s d f p₀ α i.succ).1 := by
  apply Prod.ext
  · funext j
    refine Fin.lastCases ?_ (fun j ↦ ?_) j
    · simp only [Fin.append_right_eq_snoc, Fin.snoc_last]
      rfl
    · simp only [Fin.append_right_eq_snoc, Fin.snoc_castSucc]
      rfl
  · change FoldPhase.appendFoldOracle s i _ _ = _
    funext j
    refine Fin.lastCases ?_ (fun j ↦ ?_) j
    · simp only [Fin.val_succ]
      rw [FoldPhase.appendFoldOracle_last]
      change _ = honestWords s d f p₀ α i.succ
      funext x
      exact (honestWords_succ s d f p₀ α i x).symm
    · rw [FoldPhase.appendFoldOracle_castSucc]
      rfl

/-- The non-final boundaries generated from a fixed initial word and witness. -/
def honestFoldRelation (f : OracleStatement s ω (0 : Fin (k + 1)) 0)
    (p₀ : Witness F s d 0) (i : Fin (k + 1)) :
    Set ((Statement F i × ∀ j, OracleStatement s ω i j) × Witness F s d i.castSucc) :=
  {sw | ∃ α, sw = honestFoldState s d f p₀ α i}

/-- The completed histories generated from a fixed initial word and witness. -/
def honestOutputRelation (f : OracleStatement s ω (0 : Fin (k + 1)) 0)
    (p₀ : Witness F s d 0) :
    Set ((FinalStatement F k × ∀ j, FinalOracleStatement s ω j) ×
      Witness F s d (Fin.last (k + 1))) :=
  {sw | ∃ α,
    sw = ((α, honestHistory s d f p₀ α), honestPolynomial s d p₀ α (Fin.last (k + 1)))}

/-- The honest transcript of all non-final folds and the final polynomial transmission. -/
def honestFoldTranscript (f : OracleStatement s ω (0 : Fin (k + 1)) 0)
    (p₀ : Witness F s d 0) (α : Fin (k + 1) → F) :
    (pSpecFold k (ω := ω) s ++ₚ FinalFoldPhase.pSpec F).FullTranscript :=
  FullTranscript.seqCompose (foldTranscript s (fun i ↦ α i.castSucc)
    (honestWords s d f p₀ α)) ++ₜ honestFinalTranscript s d p₀ α

end Fri.Spec

/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
module

public import ArkLib.ProofSystem.Fri.Spec.Extraction.Cost

/-!
# Retained-word access counts

Only explicit word instructions contribute to these profiles. Arithmetic, cached-array reads, and
metadata instructions contribute zero in the word-read coordinate.
-/

@[expose] public section

namespace Fri.Spec.Extractor
open Domain OracleComp OracleSpec CompPoly
variable {F : Type} [NonBinaryField F] [Fintype F] [DecidableEq F]
variable {n k : ℕ} {ω : SmoothCosetFftDomain n F}
variable (s : Fin (k + 1) → ℕ+) (o : ∀ j, FinalOracleStatement s ω j)
variable (α : FinalStatement F k)

/-- Generating an initial-domain query performs no retained-word reads. -/
@[simp]
theorem profile_generateInitialQuery_word (gen : Generator ω) (z : Fin (2 ^ n)) :
    (profile s o α (generateInitialQuery s o α gen z)).2 (.inr .wordRead) = 0 := by
  simp [generateInitialQuery, initialPoint, profile_bind, embedArithmeticCost]

/-- Generating a folding block performs no retained-word reads. -/
@[simp]
theorem profile_blockNodes_word (hs : (∑ j, (s j).val) ≤ n) (gen : Generator ω)
    (i : Fin (k + 1)) (roundGen : RoundGenerator s gen i)
    (x : (ω.subdomain 0).toFinset)
    (projected : {a : F // a = (QueryRound.queryPoint s hs i x).val}) :
    (profile s o α (blockNodes s o α hs gen i roundGen x projected)).2 (.inr .wordRead) = 0 := by
  simp [blockNodes, profile_arrayProgram_apply, generateBlockNode, profile_bind,
    embedArithmeticCost]

/-- Reading a block accesses its retained word exactly once at each block node. -/
@[simp]
theorem profile_blockValues_word (hs : (∑ j, (s j).val) ≤ n) (i : Fin (k + 1))
    (x : (ω.subdomain 0).toFinset)
    (nodes : {a : Array F // a = Array.ofFn (fun j : Fin (2 ^ (s i).val) ↦
      (blockNode s hs i x j).val)}) :
    (profile s o α (blockValues s o α hs i x nodes)).2 (.inr .wordRead) = 2 ^ (s i).val := by
  simp [blockValues, profile_arrayProgram_apply, profile_bind, embedArithmeticCost,
    instructionCost, AccessOp.costKind]

/-- A non-final folded value uses one word read; the final folded value uses cached coefficients. -/
@[simp]
theorem profile_nextValue_word (hs : (∑ j, (s j).val) ≤ n) {d : ℕ+}
    (input : PreparedInput s o α d) (i : Fin (k + 1))
    (x : (ω.subdomain 0).toFinset)
    (projected : {a : F // a = (QueryRound.queryPoint s hs i x).val}) :
    (profile s o α (nextValue s o α hs input i x projected)).2 (.inr .wordRead) =
      if i.val < k then 1 else 0 := by
  by_cases hi : i.val < k <;>
    simp [nextValue, hi, profile_bind, embedArithmeticCost, instructionCost, AccessOp.costKind]

/-- A complete local check reads its block and the next word only at non-final rounds. -/
@[simp]
theorem profile_checkRoundProgram_word (hs : (∑ j, (s j).val) ≤ n) {d : ℕ+}
    (input : PreparedInput s o α d) (i : Fin (k + 1))
    (x : (ω.subdomain 0).toFinset) :
    (profile s o α (checkRoundProgram s o α hs input i x)).2 (.inr .wordRead) =
      2 ^ (s i).val + if i.val < k then 1 else 0 := by
  simp [checkRoundProgram, profile_bind, readRoundGenerator, readCachedChallenge,
    projectedPoint, embedArithmeticCost]

/-- Caching one selected value performs exactly one initial-word read. -/
@[simp]
theorem profile_readSample_word (z : Fin (2 ^ n))
    (x : {q : (ω.subdomain 0).toFinset // q = initialQuery z}) :
    (profile s o α (readSample s o α z x)).2 (.inr .wordRead) = 1 := by
  unfold readSample
  dsimp only
  erw [profile_bind]
  simp only [profile_pure, add_zero]
  erw [profile_readWord]
  rfl

/-- A selected sample's extra word read equals the increase in the cache length. -/
theorem profile_selectSample_word_potential {D : ℕ} (state : Selection s o D)
    (z : Fin (2 ^ n)) (x : {q : (ω.subdomain 0).toFinset // q = initialQuery z}) :
    (profile s o α (selectSample s o α state z x)).2 (.inr .wordRead) + state.selected.length =
      (profile s o α (selectSample s o α state z x)).1.val.selected.length := by
  by_cases hcap : state.selected.length < D <;>
    simp [selectSample, hcap, profile_bind, embedArithmeticCost, Nat.add_comm]

end Fri.Spec.Extractor

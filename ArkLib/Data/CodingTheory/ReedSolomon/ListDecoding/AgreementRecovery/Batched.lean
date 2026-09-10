/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.AgreementRecovery.Machine
public import ArkLib.Data.Polynomial.BatchRemainder

/-!
# Batch refinement of shared agreement recovery

For one received position, every live factor of a representation tests the same residual `e`.
`advanceBatch` builds a product tree from those factors and obtains all remainders together.
Replacing `e` by `e mod h` preserves both the monic gcd and its complementary factor, so the
resulting children are exactly those of the depth-first specification in `Machine`.

`runMany_eq` proves equality of complete ordered output lists, including the recorded agreement
positions. Existing interpolation, completeness and cardinality proofs can therefore be reused
without assuming that parameter roots lie in the base field.

Stopped blocks retain their output position but contribute the unit modulus to later trees.
Thus their parameter degree is no longer charged to a live product. Empty factors are discarded.
The total wrapper falls back to the specification for nonmonic input; every well-formed finite
representation uses the batch branch. Backend correctness is explicit, while whole-decoder
arithmetic complexity remains a separate obligation.
-/

@[expose] public section

namespace ReedSolomon.ListDecoding.AgreementRecovery.Batched
open CompPoly CompPoly.CPolynomial
variable {E index : Type*} [Field E] [BEq E] [LawfulBEq E]

/-- Test one equation, retaining a stopped block or creating its agreeing and rejecting
children. -/
def advance (k : ℕ) (i : index) (e : CPolynomial E) (block : Block E index) :
    List (Block E index) :=
  if block.factor.natDegree = 0 then []
  else if k ≤ block.positions.length then [block]
  else [⟨gcdFactor block.factor e, i :: block.positions⟩,
    ⟨gcdComplement block.factor e, block.positions⟩]

/-- Stopped or empty blocks contribute no degree to the next live-factor product tree. -/
def activeModulus (k : ℕ) (block : Block E index) : CPolynomial E :=
  if block.factor.natDegree = 0 ∨ k ≤ block.positions.length then 1 else block.factor

/-- Reduce one common residual against the active factors, then split each block by its
remainder. -/
def advanceBatch (M : MulContext E) (D : ModContext E)
    (k : ℕ) (i : index) (e : CPolynomial E) (blocks : List (Block E index)) :
    List (Block E index) :=
  let residues := BatchRemainder.remainders M D e (blocks.map (activeModulus k))
  (List.zipWith (fun block residue => advance k i residue block) blocks residues).flatten

/-- Both gcd children are unchanged by reducing the equation modulo the active factor. -/
theorem advance_mod (k : ℕ) (i : index) (e : CPolynomial E) (block : Block E index)
    (hb : block.factor.monic) :
    advance k i (e.modByMonic (activeModulus k block)) block = advance k i e block := by
  by_cases hz : block.factor.natDegree = 0
  · simp [advance, hz]
  by_cases hs : k ≤ block.positions.length
  · simp [advance, hz, hs]
  simp [advance, activeModulus, hz, hs, gcdFactor_modByMonic _ _ hb,
    gcdComplement_modByMonic _ _ hb]

/-- A monic factor has monic gcd children, so the next batch again has valid divisors. -/
theorem advance_monic (k : ℕ) (i : index) (e : CPolynomial E) (block : Block E index)
    (hb : block.factor.monic) : ∀ out ∈ advance k i e block, out.factor.monic := by
  have hn : block.factor ≠ 0 :=
    (toPoly_eq_zero_iff _).not.mp ((monic_toPoly_iff _).mp hb).ne_zero
  intro out hout
  simp only [advance] at hout
  split_ifs at hout with hz hs
  · simp at hout
  · simpa using (List.mem_singleton.mp hout) ▸ hb
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hout
    rcases hout with rfl | rfl
    · exact gcdFactor_monic hn
    · exact gcdComplement_monic hb

/-- The batch pass preserves the exact block list produced by separate equation tests. -/
theorem advanceBatch_eq (M : MulContext E) (D : ModContext E)
    (k : ℕ) (i : index) (e : CPolynomial E) (blocks : List (Block E index))
    (hb : ∀ block ∈ blocks, block.factor.monic) :
    advanceBatch M D k i e blocks = blocks.flatMap (advance k i e) := by
  -- Unit placeholders align metadata with the remainders, without retaining stopped degree.
  have hm : ∀ h ∈ blocks.map (activeModulus k), h.monic := by
    intro h hh
    rcases List.mem_map.mp hh with ⟨b, hmem, rfl⟩
    unfold activeModulus
    split_ifs
    · rw [monic_toPoly_iff, toPoly_one]
      exact Polynomial.monic_one
    · exact hb b hmem
  -- The tree returns one remainder per input in order, so zipping loses no block.
  rw [advanceBatch, BatchRemainder.remainders_eq M D e _ hm, List.map_map]
  clear hm
  induction blocks with
  | nil => rfl
  | cons b bs ih =>
      simp only [List.map_cons, List.zipWith_cons_cons, List.flatten_cons, List.flatMap_cons,
        Function.comp_apply]
      rw [advance_mod k i e b (hb b (by simp))]
      congr 1
      exact ih (fun x hx => hb x (by simp [hx]))

/-- Every surviving block can be used in the next product/remainder tree. -/
theorem advanceBatch_monic (M : MulContext E) (D : ModContext E)
    (k : ℕ) (i : index) (e : CPolynomial E) (blocks : List (Block E index))
    (hb : ∀ block ∈ blocks, block.factor.monic) :
    ∀ out ∈ advanceBatch M D k i e blocks, out.factor.monic := by
  rw [advanceBatch_eq M D k i e blocks hb]
  intro out hout
  rcases List.mem_flatMap.mp hout with ⟨b, hmem, hout⟩
  exact advance_monic k i e b (hb b hmem) out hout

/-- One depth-first step can be reassociated into a row pass followed by the remaining equations. -/
theorem split_cons_eq (k : ℕ) (i : index) (e : CPolynomial E)
    (rest : List (index × CPolynomial E)) (block : Block E index) :
    split k ((i, e) :: rest) block = (advance k i e block).flatMap (split k rest) := by
  by_cases hz : block.factor.natDegree = 0
  · simp [split, advance, hz]
  by_cases hs : k ≤ block.positions.length
  · cases rest <;> simp [split, advance, hz, hs]
  simp only [split, advance, hz, hs, if_false, List.flatMap_cons, List.flatMap_nil,
    List.append_nil]

/-- Process received positions in order, batching each residual across all current blocks. -/
def runMany (M : MulContext E) (D : ModContext E) (k : ℕ) :
    List (index × CPolynomial E) → List (Block E index) → List (Block E index)
  | [], blocks => blocks.flatMap (split k [])
  | (i, e) :: rest, blocks => runMany M D k rest (advanceBatch M D k i e blocks)

/-- Row-wise batching refines the depth-first specification, including output order and samples. -/
theorem runMany_eq (M : MulContext E) (D : ModContext E) (k : ℕ)
    (equations : List (index × CPolynomial E)) (blocks : List (Block E index))
    (hb : ∀ block ∈ blocks, block.factor.monic) :
    runMany M D k equations blocks = blocks.flatMap (split k equations) := by
  induction equations generalizing blocks with
  | nil => rfl
  | cons row rest ih =>
      rcases row with ⟨i, e⟩
      rw [runMany, ih _ (advanceBatch_monic M D k i e blocks hb),
        advanceBatch_eq M D k i e blocks hb, List.flatMap_assoc]
      apply List.flatMap_congr
      intro block _
      exact (split_cons_eq k i e rest block).symm

/-- Use batch recovery on monic input and preserve the total specification on malformed input. -/
def run (M : MulContext E) (D : ModContext E) (k : ℕ)
    (equations : List (index × CPolynomial E)) (modulus : CPolynomial E) :
    List (Block E index) :=
  if modulus.monic then runMany M D k equations [⟨modulus, []⟩]
  else AgreementRecovery.run k equations modulus

/-- The public batch wrapper preserves the original total function on every input. -/
@[simp]
theorem run_eq (M : MulContext E) (D : ModContext E) (k : ℕ)
    (equations : List (index × CPolynomial E)) (modulus : CPolynomial E) :
    run M D k equations modulus = AgreementRecovery.run k equations modulus := by
  by_cases hm : modulus.monic
  · rw [run, if_pos hm, runMany_eq M D k equations _ (by simpa)]
    simp [AgreementRecovery.run]
  · simp [run, hm]

end ReedSolomon.ListDecoding.AgreementRecovery.Batched

/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Quang Dao
-/

import ArkLib.Data.Misc.Basic
import CompPoly.Univariate.ToPoly
import ArkLib.ProofSystem.Binius.BinaryBasefold.Spec

/-!
## Binary Basefold Soundness Query Phase Preliminaries

Shared helper definitions and alignment lemmas for the query phase of Binary Basefold soundness.
This file packages:
1. challenge-suffix extraction and transport lemmas
2. monadic query-phase helper functions for oracle access and folding checks
3. logical counterparts used later in the final query-phase soundness proof

## References

* [Diamond, B.E. and Posen, J., *Polylogarithmic proofs for multilinears over binary towers*][DP24]
  Statement numbering below follows the archived revision of [DP24].
-/

namespace Binius.BinaryBasefold

open OracleSpec OracleComp ProtocolSpec Finset AdditiveNTT Polynomial MvPolynomial
  Binius.BinaryBasefold
open scoped NNReal
open ReedSolomon Code BerlekampWelch Function
open Finset AdditiveNTT Polynomial MvPolynomial Nat Matrix
open ProbabilityTheory

variable {r : ℕ} [NeZero r]
variable {L : Type} [Field L] [Fintype L] [DecidableEq L] [CharP L 2]
variable (𝔽q : Type) [Field 𝔽q] [Fintype 𝔽q] [DecidableEq 𝔽q]
  [h_Fq_char_prime : Fact (Nat.Prime (ringChar 𝔽q))] [hF₂ : Fact (Fintype.card 𝔽q = 2)]
variable [Algebra 𝔽q L]
variable (β : Fin r → L) [hβ_lin_indep : Fact (LinearIndependent 𝔽q β)]
  [h_β₀_eq_1 : Fact (β 0 = 1)]
variable {ℓ 𝓡 ϑ : ℕ} (γ_repetitions : ℕ) [NeZero ℓ] [NeZero 𝓡] [NeZero ϑ] -- Should we allow ℓ = 0?
variable {h_ℓ_add_R_rate : ℓ + 𝓡 < r} -- ℓ ∈ {1, ..., r-1}
variable {𝓑 : Fin 2 ↪ L}
noncomputable section
variable [SampleableType L]
variable [hdiv : Fact (ϑ ∣ ℓ)]

open scoped NNReal ProbabilityTheory

namespace QueryPhase

/-!
## Common Proximity Check Helpers

These functions extract the shared logic between the canonical-search query verifier
and the migrated computable query verifier (`queryOracleVerifier`)
and `queryKnowledgeStateFunction` for proximity testing, allowing code reuse
and ensuring both implementations follow the same logic.
-/

/-- Number of oracle blocks at the end of the protocol. -/
abbrev nBlocks : ℕ := toOutCodewordsCount ℓ ϑ (Fin.last ℓ)

/-- Extract suffix starting at position `destIdx` from a full challenge. -/
def extractSuffixFromChallenge (v : AdditiveNTT.Comp.sDomain (𝔽q := 𝔽q) (β := β) (ℓ := ℓ)
    (R_rate := 𝓡) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨0, by omega⟩)
    (destIdx : Fin r) (h_destIdx_le : destIdx ≤ ℓ) :
    AdditiveNTT.Comp.sDomain (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (R_rate := 𝓡)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) destIdx :=
  let suffixCanonical :=
    iteratedQuotientMap 𝔽q β h_ℓ_add_R_rate (i := ⟨0, by omega⟩) (k := destIdx.val)
      (h_destIdx := by simp only [zero_add])
      (h_destIdx_le := h_destIdx_le)
      (x := AdditiveNTT.Comp.toCanonicalSDomain
        (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (R_rate := 𝓡)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := 0) v)
  ⟨suffixCanonical.1,
    AdditiveNTT.Comp.mem_compSDomain_of_mem_canonicalSDomain
      (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (R_rate := 𝓡)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) suffixCanonical.2⟩

/-- **Congruence Lemma for Challenge Suffixes**:
Allows proving equality between two suffix extractions when the destination indices
are proven equal (`destIdx = destIdx'`), handling the necessary type casting. -/
lemma extractSuffixFromChallenge_congr_destIdx
    (v : AdditiveNTT.Comp.sDomain (𝔽q := 𝔽q) (β := β) (ℓ := ℓ)
      (R_rate := 𝓡) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨0, by omega⟩)
    {destIdx destIdx' : Fin r}
    (h_idx_eq : destIdx = destIdx')
    (h_le : destIdx ≤ ℓ)
    (h_le' : destIdx' ≤ ℓ) :
    extractSuffixFromChallenge 𝔽q β v destIdx h_le =
    cast (by rw [h_idx_eq]) (extractSuffixFromChallenge 𝔽q β v destIdx' h_le') := by
  subst h_idx_eq; rfl

/-- **First Oracle Equals Polynomial Oracle Function**:
When `strictOracleFoldingConsistencyProp` holds, the first oracle (`getFirstOracle`) equals
the polynomial oracle function `f₀` derived from the multilinear polynomial `t`.
This follows from the consistency property for `j = 0`, where `iterated_fold` with 0 steps
is the identity function. -/
lemma polyToOracleFunc_eq_getFirstOracle
    (t : MultilinearPoly L ℓ)
    (i : Fin (ℓ + 1))
    (challenges : Fin i → L)
    (oStmt : ∀ j, OracleStatement 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i j)
    (h_consistency : strictOracleFoldingConsistencyProp 𝔽q β (t := t) (i := i)
      (challenges := challenges) (oStmt := oStmt)) :
    let P₀ : CompPoly.CPolynomial L :=
      ⟨CompPoly.CPolynomial.Raw.trim (Array.ofFn (fun i : Fin (2 ^ ℓ) =>
          AdditiveNTT.novelToMonomialCoeffs 𝔽q β ℓ (by omega)
            (fun ω => t.val.eval (bitsOfIndex ω)) i)), by
        exact CompPoly.CPolynomial.Raw.Trim.trim_twice _⟩
    let f₀ := polyToOracleFunc 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (domainIdx := 0)
      (P := CompPoly.CPolynomial.toPoly P₀)
    f₀ = getFirstOracle 𝔽q β oStmt := by
  sorry

/-- Decompose challenge v at position i into (fiberIndex, suffix).
    This is the inverse of `Nat.joinBits` in some sense.
    Uses loose indexing with `Fin r`. -/
def decomposeChallenge (v : AdditiveNTT.Comp.sDomain (𝔽q := 𝔽q) (β := β) (ℓ := ℓ)
    (R_rate := 𝓡) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨0, by omega⟩)
    (i : Fin r) {destIdx : Fin r} (steps : ℕ)
    (h_destIdx_le : destIdx ≤ ℓ) :
    Fin (2^steps) × AdditiveNTT.Comp.sDomain (𝔽q := 𝔽q) (β := β) (ℓ := ℓ)
      (R_rate := 𝓡) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) destIdx :=
  (extractMiddleFinMask 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (v := v)
      (i := i) (steps := steps),
    extractSuffixFromChallenge 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (v:=v)
      (destIdx:=destIdx) (h_destIdx_le:=h_destIdx_le))

-- TODO: KEY LEMMA for connecting fiber queries to challenge decomposition
-- TODO: Lemma connecting queryFiberPoints to extractMiddleFinMask

def queryRbrKnowledgeError_singleRepetition := ((1/2 : ℝ≥0) + (1 : ℝ≥0) / (2 * 2^𝓡))

/-- RBR knowledge error for the query phase.
Proximity testing error rate: `(1/2 + 1/(2 * 2^𝓡))^γ` -/
def queryRbrKnowledgeError := fun _ : (pSpecQuery 𝔽q β γ_repetitions
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).ChallengeIdx =>
  (queryRbrKnowledgeError_singleRepetition (𝓡 := 𝓡))^γ_repetitions

/-- Oracle query helper: query a committed codeword at a given domain point.
    Restricted to codeword indices where the oracle range is L. -/
def queryCodeword (j : Fin (toOutCodewordsCount ℓ ϑ (Fin.last ℓ)))
  (point : AdditiveNTT.Comp.sDomain (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (R_rate := 𝓡)
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨oraclePositionToDomainIndex ℓ ϑ j, by omega⟩) :
  OptionT (OracleComp ([]ₒ +
    ([OracleStatement 𝔽q β (ϑ:=ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ( Fin.last ℓ)]ₒ +
    [(pSpecQuery 𝔽q β γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).Message]ₒ))) L :=
    query (spec := [OracleStatement 𝔽q β (ϑ:=ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ)]ₒ)
      ⟨⟨j, by omega⟩, point⟩

section FinalQueryRoundIOR

/-!
### IOR Implementation for the Final Query Round
-/
def getChallengeSuffix (k : Fin (ℓ / ϑ))
    (v : AdditiveNTT.Comp.sDomain (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (R_rate := 𝓡)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) 0) :
    let i := k.val * ϑ
    have h_i_add_ϑ_le_ℓ : i + ϑ ≤ ℓ := k_succ_mul_ϑ_le_ℓ_₂ (k := k)
    let destIdx : Fin r := ⟨i + ϑ, by omega⟩
    AdditiveNTT.Comp.sDomain (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (R_rate := 𝓡)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) destIdx :=
  have h_i_add_ϑ_le_ℓ := k_succ_mul_ϑ_le_ℓ_₂ (k := k)
  extractSuffixFromChallenge 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (v:=v) (destIdx := ⟨k.val * ϑ + ϑ, by omega⟩) (h_destIdx_le:=by omega)

def challengeSuffixToFin (k : Fin (ℓ / ϑ))
  (suffix : AdditiveNTT.Comp.sDomain (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (R_rate := 𝓡)
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨k.val * ϑ + ϑ, by
    have := k_succ_mul_ϑ_le_ℓ_₂ (k := k); omega⟩) : Fin (2 ^ (ℓ + 𝓡 - (k.val * ϑ + ϑ))) :=
  let i := k.val * ϑ
  have h_i_add_ϑ_le_ℓ : i + ϑ ≤ ℓ := k_succ_mul_ϑ_le_ℓ_₂ (k := k)
  let destIdx : Fin r := ⟨i + ϑ, by omega⟩
  AdditiveNTT.Comp.compSDomainToFinViaCanonical (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (R_rate := 𝓡)
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := ⟨k.val * ϑ + ϑ, by omega⟩) (h_i := by
      simp only [k_succ_mul_ϑ_le_ℓ_₂, Nat.lt_add_of_pos_right_of_le]) suffix

/-- Return the point `f^(i)(u_0, ..., u_{ϑ-1}, v_{i+ϑ}, ..., v_{ℓ+R-1})`
for a fiber index `u ∈ B_ϑ`. -/
noncomputable def getFiberPoint
    (k : Fin (ℓ / ϑ))
    (v : AdditiveNTT.Comp.sDomain (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (R_rate := 𝓡)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) 0) (u : Fin (2 ^ ϑ)) :
    AdditiveNTT.Comp.sDomain (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (R_rate := 𝓡)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := ⟨oraclePositionToDomainIndex ℓ ϑ (i := Fin.last ℓ)
      (positionIdx := ⟨k, by simp only [toOutCodewordsCount_last, Fin.is_lt]⟩),
        lt_r_of_lt_ℓ (x := k.val * ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (h := k_mul_ϑ_lt_ℓ)⟩) := by
  exact
    qMap_total_fiber 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := ⟨k.val * ϑ,
        lt_r_of_lt_ℓ (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (x := k.val * ϑ)
          (h := k_mul_ϑ_lt_ℓ (k := k))⟩)
      (steps := ϑ)
      (h_destIdx := by rfl)
      (h_destIdx_le := by
        exact k_succ_mul_ϑ_le_ℓ_₂ (k := k))
      (y := getChallengeSuffix 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (k := k) (v := v))
      u

section MonadicOracleVerification
/-!
### Helper Functions for Verifier Logic

These functions break down the verifier's proximity checking logic into composable blocks,
making it easier to prove properties about each component separately.
-/

/-- Query all fiber points for a given folding step.
    Returns a list of evaluations `f^(i)(u_0, ..., u_{ϑ-1}, v_{i+ϑ}, ..., v_{ℓ+R-1})`
    for all `u ∈ B_ϑ`.
    Note: `oStmtIn` is accessed via oracle queries in the OracleComp context. -/
noncomputable def queryFiberPoints
    (k : Fin (ℓ / ϑ))
    (v : AdditiveNTT.Comp.sDomain (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (R_rate := 𝓡)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) 0) :
  OptionT
        (OracleComp
          ([]ₒ + ([OracleStatement 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ)]ₒ +
            [(pSpecQuery 𝔽q β γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).Message]ₒ)))
        (Vector L (2^ϑ)) := do
  let k_th_oracleIdx : Fin (toOutCodewordsCount ℓ ϑ (Fin.last ℓ)) :=
    ⟨k, by simp only [toOutCodewordsCount, Fin.val_last, lt_self_iff_false, ↓reduceIte, add_zero,
      Fin.is_lt]⟩
  -- 2. Map over the Vector monadically
  let results : Vector L (2^ϑ) ← (⟨Array.finRange (2^ϑ), by simp only [Array.size_finRange]⟩
    : Vector (Fin (2^ϑ)) (2^ϑ)).mapM (fun (u : Fin (2^ϑ)) => do
    queryCodeword 𝔽q β (γ_repetitions := γ_repetitions) (ϑ:=ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (j := k_th_oracleIdx) (point :=
        getFiberPoint 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (k := k) (v := v) (u := u))
  )
  pure results

/-- Check a single folding step: query fiber points, verify consistency, and compute next value.
    Returns `(c_next, all_checks_passed)` where `c_next` is the computed folded value
    and `all_checks_passed` indicates if all consistency checks passed.
    Note: `oStmtIn` is accessed via oracle queries in the OracleComp context. -/
noncomputable def checkSingleFoldingStep
    (k_val : Fin (ℓ / ϑ)) (c_cur : L)
    (v : AdditiveNTT.Comp.sDomain (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (R_rate := 𝓡)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨0, by omega⟩)
    (stmt : FinalSumcheckStatementOut (L := L) (ℓ := ℓ)) :
    OptionT (OracleComp ([]ₒ + ([OracleStatement 𝔽q β (ϑ:=ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ)]ₒ + [(pSpecQuery 𝔽q β
      γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).Message]ₒ))) L := do
  let i := k_val.val * ϑ
  have h_k: k_val ≤ (ℓ / ϑ - 1) := by omega
  have h_i_add_ϑ_le_ℓ : i + ϑ ≤ ℓ := by
    calc
      i + ϑ = k_val * ϑ + ϑ := by omega
      _ ≤ (ℓ / ϑ - 1) * ϑ + ϑ := by
        apply Nat.add_le_add_right
        apply Nat.mul_le_mul_right
        omega
      _ = ℓ / ϑ * ϑ := by
        rw [Nat.sub_mul, one_mul, Nat.sub_add_cancel]
        conv_lhs => rw [← one_mul ϑ]
        apply Nat.mul_le_mul_right
        omega
      _ ≤ ℓ := by
        apply Nat.div_mul_le_self
  have h_i_lt_ℓ : i < ℓ := by
    calc
      i ≤ ℓ - ϑ := by omega
      _ < ℓ := by
        apply Nat.sub_lt
        exact Nat.pos_of_neZero ℓ
        exact Nat.pos_of_neZero ϑ
  let f_i_on_fiber ← queryFiberPoints 𝔽q β (γ_repetitions := γ_repetitions) (ϑ := ϑ)
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate) k_val v
  if h_i_pos : i > 0 then
    let oracle_point_idx := extractMiddleFinMask 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (v := v) (i := ⟨i, by omega⟩) (steps := ϑ)
    let f_i_val := f_i_on_fiber.get oracle_point_idx
    guard (c_cur = f_i_val)
  let destIdx : Fin r := ⟨i + ϑ, by omega⟩
  let next_suffix_of_v :
      AdditiveNTT.Comp.sDomain (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (R_rate := 𝓡)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) destIdx :=
    getChallengeSuffix (k := k_val) (v := v)
  let cur_challenge_batch : Fin ϑ → L := fun j =>
    stmt.challenges ⟨i + j.val, by simp only [Fin.val_last]; omega⟩
  let c_next : L := single_point_localized_fold_matrix_form 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (i := ⟨i, by omega⟩) (steps := ϑ) (destIdx := destIdx) (h_destIdx := by dsimp only [destIdx])
    (h_destIdx_le := by omega) (r_challenges := cur_challenge_batch) (y := next_suffix_of_v)
    (fiber_eval_mapping := f_i_on_fiber.get)
  return c_next

/-- Check a single repetition: iterate through all folding steps and verify final consistency.
    Returns `true` if all checks pass, `false` otherwise.
    Note: `oStmtIn` is accessed via oracle queries in the OracleComp context.
    Uses `mut` + `for` loop for true early termination (stops immediately on first failure).
    For proofs, we'll need to reason about the loop invariant that `c_cur` maintains the
    correct accumulated value through iterations. -/
noncomputable def checkSingleRepetition
    (v : AdditiveNTT.Comp.sDomain (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (R_rate := 𝓡)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨0, by omega⟩)
    (stmt : FinalSumcheckStatementOut (L := L) (ℓ := ℓ)) (final_constant : L) :
    OptionT (OracleComp ([]ₒ + ([OracleStatement 𝔽q β (ϑ:=ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ)]ₒ + [(pSpecQuery 𝔽q β
      γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).Message]ₒ))) Unit := do
  let mut c_cur : L := 0 -- Will be initialized in first iteration
  -- Iterate through the `ℓ/ϑ` adjacent pairs of oracles & validate local folding consistency
  -- Early termination: stops immediately on first failure via `return false`
  for k_val in List.finRange (ℓ / ϑ) do
    let c_next ← checkSingleFoldingStep 𝔽q β (ϑ:=ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (γ_repetitions := γ_repetitions)
        ⟨k_val, by omega⟩ c_cur v stmt
    c_cur := c_next
  -- Final check: c_ℓ ?= final_constant
  guard (c_cur = final_constant)

end MonadicOracleVerification

section LogicalOracleVerification

/-!
### Proximity check spec: logical defs (mirror monadic verifier exactly)

Logical (non-monadic) versions that capture 100% of the monadic definitions.

Key property from docstring:
  if `i > 0` then `V` requires `c_i ?= f^(i)(v_i, ..., v_{ℓ+R-1})`.
  `V` defines `c_{i+ϑ} := fold(f^(i), r'_i, ..., r'_{i+ϑ-1})(v_{i+ϑ}, ..., v_{ℓ+R-1})`.
  `V` requires `c_ℓ ?= c`.

The logical definitions mirror this exactly:
- `logical_queryFiberPoints` → Queries all `u` for a given step `k` (where `i = k·ϑ`)
- `logical_computeFoldedValue` → Computes `c_{i+ϑ}` via folding
- `logical_checkSingleFoldingStep` → Performs the guard check when `i > 0`
- `logical_checkSingleRepetition` → Enforces all guard checks and the final equality
- `logical_proximityChecksSpec` → Lifts to all `γ` repetitions

### Correspondence with Monadic Implementation

Each monadic function has a logical counterpart:
- `queryFiberPoints` ↔ `logical_queryFiberPoints`
- `checkSingleFoldingStep` ↔ `logical_checkSingleFoldingStep` + `logical_computeFoldedValue`
- `checkSingleRepetition` ↔ `logical_checkSingleRepetition`
-/

/-- Fiber evals for all u (logical; same as monadic `queryFiberPoints`). -/
def logical_queryFiberPoints
    (oStmt : ∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ) j)
    (k : Fin (ℓ / ϑ))
    (v : AdditiveNTT.Comp.sDomain (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (R_rate := 𝓡)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) 0) : Fin (2 ^ ϑ) → L :=
  let k_th_oracleIdx : Fin (toOutCodewordsCount ℓ ϑ (Fin.last ℓ)) :=
    ⟨k.val, by simp only [toOutCodewordsCount, Fin.val_last, lt_self_iff_false, ↓reduceIte,
      add_zero, Fin.is_lt]⟩
  fun u => oStmt k_th_oracleIdx (getFiberPoint 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) k v u)

/-- Compute folded value at step `k` (same as `c_next` in monadic `checkSingleFoldingStep`).
This takes `f_i_on_fiber` - the list of `2^ϑ` fiber evaluations on oracle domain
`k*ϑ`, folds them into a single oracle evaluation on oracle domain `(k+1)*ϑ`, i.e. `c_{i+ϑ}`. -/
def logical_computeFoldedValue
    (k : Fin (ℓ / ϑ))
    (v : AdditiveNTT.Comp.sDomain (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (R_rate := 𝓡)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) 0)
    (stmt : FinalSumcheckStatementOut (L := L) (ℓ := ℓ))
    (f_i_on_fiber : Fin (2 ^ ϑ) → L) : L :=
  let i := k.val * ϑ
  have h_i_add_ϑ_le_ℓ : i + ϑ ≤ ℓ := k_succ_mul_ϑ_le_ℓ_₂ (k := k)
  let destIdx : Fin r := ⟨i + ϑ, by omega⟩
  let next_suffix_of_v :
      AdditiveNTT.Comp.sDomain (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (R_rate := 𝓡)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) destIdx :=
    getChallengeSuffix (k := k) (v := v)
  let cur_challenge_batch : Fin ϑ → L := fun j =>
    stmt.challenges ⟨i + j.val, by simp only [Fin.val_last]; omega⟩
  single_point_localized_fold_matrix_form 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (i := ⟨i, by omega⟩) (steps := ϑ) (destIdx := destIdx) (h_destIdx := by dsimp only [destIdx])
    (h_destIdx_le := by omega) (r_challenges := cur_challenge_batch) (y := next_suffix_of_v)
    (fiber_eval_mapping := f_i_on_fiber)

/-- Check a single folding step at k (logical; mirrors monadic `checkSingleFoldingStep`).

    Captures the guard check from docstring:
      if `i > 0` then `V` requires `c_i ?= f^(i)(v_i, ..., v_{ℓ+R-1})`
    Where c_i is the fold value from step k-1, and f^(i)(v_i,...) is the oracle
    at position k evaluated at the "overlap" point.
    Note: h_i_pos implies k > 0, so k-1 is valid. -/
def logical_checkSingleFoldingStep
    (oStmt : ∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ) j)
    (k : Fin (ℓ / ϑ))
    (v : AdditiveNTT.Comp.sDomain (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (R_rate := 𝓡)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) 0)
    (stmt : FinalSumcheckStatementOut (L := L) (ℓ := ℓ)) : Prop :=
  let i := k.val * ϑ
  have h_i_add_ϑ_le_ℓ : i + ϑ ≤ ℓ := k_succ_mul_ϑ_le_ℓ_₂ (k := k)
  let f_i_on_fiber := logical_queryFiberPoints 𝔽q β oStmt k v
  if h_i_pos : i > 0 then
    have h_k_pos : k.val > 0 := Nat.pos_of_mul_pos_right h_i_pos
    let k_prev : Fin (ℓ / ϑ) := ⟨k.val - 1, by omega⟩
    let f_prev_on_fiber := logical_queryFiberPoints 𝔽q β oStmt k_prev v
    let c_cur := logical_computeFoldedValue 𝔽q β k_prev v stmt f_prev_on_fiber
    let oracle_point_idx := extractMiddleFinMask 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (v := v) (i := ⟨i, by omega⟩) (steps := ϑ)
    let f_i_val := f_i_on_fiber oracle_point_idx
    c_cur = f_i_val
  else
    True

/-- Logical check specific to step k.
    If k is an intermediate index, it is the consistency of the folding step.
    If k is the terminal index, it is the constant check. -/
def logical_stepCondition (oStmt : ∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ) j)
    (k : Fin (ℓ / ϑ + 1))
    (v : AdditiveNTT.Comp.sDomain (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (R_rate := 𝓡)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) 0)
    (stmt : FinalSumcheckStatementOut (L := L) (ℓ := ℓ)) (final_constant : L) : Prop :=
  if h_k_lt : k.val < (ℓ / ϑ) then
    -- Condition for `k ∈ {0, 1, ..., ℓ/ϑ-1}`
    logical_checkSingleFoldingStep 𝔽q β oStmt ⟨k.val, h_k_lt⟩ v stmt
  else
    -- Condition for the final state k = `ℓ/ϑ`
    have h_div_pos : ℓ / ϑ > 0 :=
      Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_neZero ℓ) hdiv.out) (Nat.pos_of_neZero ϑ)
    let k_last : Fin (ℓ / ϑ) := ⟨ℓ / ϑ - 1, by omega⟩
    let f_last_on_fiber := logical_queryFiberPoints 𝔽q β oStmt k_last v
    logical_computeFoldedValue 𝔽q β k_last v stmt f_last_on_fiber = final_constant

/-- Check a single repetition (logical; mirrors monadic `checkSingleRepetition`).
    Captures:
    1. All guard checks pass: ∀ k, logical_checkSingleFoldingStep
    2. Final check: c_ℓ = final_constant (fold at last step equals final constant) -/
def logical_checkSingleRepetition
    (oStmt : ∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ) j)
    (v : AdditiveNTT.Comp.sDomain (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (R_rate := 𝓡)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) 0)
    (stmt : FinalSumcheckStatementOut (L := L) (ℓ := ℓ)) (final_constant : L) : Prop :=
  ∀ k : Fin (ℓ / ϑ + 1),
    logical_stepCondition 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (oStmt := oStmt) (k := k) (v := v) (stmt := stmt) (final_constant := final_constant)

/-- Proximity checks spec: for all γ repetitions, `logical_checkSingleRepetition` holds. -/
def logical_proximityChecksSpec
    (γ_challenges : Fin γ_repetitions → AdditiveNTT.Comp.sDomain (𝔽q := 𝔽q) (β := β)
      (ℓ := ℓ) (R_rate := 𝓡) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) 0)
    (oStmt : ∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ) j)
    (stmt : FinalSumcheckStatementOut (L := L) (ℓ := ℓ)) (final_constant : L) : Prop :=
  ∀ rep : Fin γ_repetitions,
    logical_checkSingleRepetition 𝔽q β oStmt (γ_challenges rep) stmt final_constant

lemma getFiberPoint_eq_qMap_total_fiber
    (k : Fin (ℓ / ϑ))
    (v : AdditiveNTT.Comp.sDomain (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (R_rate := 𝓡)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨0, by omega⟩)
    (u : Fin (2 ^ ϑ)) :
    getFiberPoint 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) k v u =
      qMap_total_fiber 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (i := ⟨k.val * ϑ,
          lt_r_of_lt_ℓ (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (x := k.val * ϑ)
            (h := k_mul_ϑ_lt_ℓ (k := k))⟩)
        (destIdx := ⟨k.val * ϑ + ϑ, by
          exact
            lt_r_of_le_ℓ (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
              (oracle_index_add_steps_le_ℓ (ℓ := ℓ) (ϑ := ϑ)
                (i := Fin.last ℓ) (j := ⟨k.val, by
                  rw [toOutCodewordsCount_last]
                  exact k.isLt⟩))⟩)
        (steps := ϑ) (h_destIdx := by rfl)
        (h_destIdx_le := by exact k_succ_mul_ϑ_le_ℓ_₂ (k := k))
        (y := getChallengeSuffix 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (k := k) (v := v)) u := by
  sorry

set_option maxHeartbeats 200000 in
lemma logical_queryFiberPoints_eq_fiberEvaluations
    (oStmt : ∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ) j)
    (k : Fin (ℓ / ϑ))
    (v : AdditiveNTT.Comp.sDomain (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (R_rate := 𝓡)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) 0) :
    let destDomainIdx : Fin r := ⟨k.val * ϑ + ϑ, by
      exact
        lt_r_of_le_ℓ (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          (oracle_index_add_steps_le_ℓ (ℓ := ℓ) (ϑ := ϑ)
            (i := Fin.last ℓ) (j := ⟨k.val, by
              rw [toOutCodewordsCount_last]
              exact k.isLt⟩))⟩
    let oracleAtK : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        ⟨oraclePositionToDomainIndex ℓ ϑ (i := Fin.last ℓ) ⟨k.val, by
          rw [toOutCodewordsCount_last]
          exact k.isLt⟩, by
          exact lt_r_of_lt_ℓ (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
            (h := by
              change k.val * ϑ < ℓ
              exact k_mul_ϑ_lt_ℓ (k := k))⟩ := by
        exact oStmt ⟨k.val, by
          rw [toOutCodewordsCount_last]
          exact k.isLt⟩
    logical_queryFiberPoints 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) oStmt k v =
      fiberEvaluations 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (i := ⟨oraclePositionToDomainIndex ℓ ϑ (i := Fin.last ℓ) ⟨k.val, by
          rw [toOutCodewordsCount_last]
          exact k.isLt⟩, by
          exact lt_r_of_lt_ℓ (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
            (h := by
              change k.val * ϑ < ℓ
              exact k_mul_ϑ_lt_ℓ (k := k))⟩)
        (destIdx := destDomainIdx)
        (steps := ϑ) (h_destIdx := by rfl) (h_destIdx_le := by
          exact k_succ_mul_ϑ_le_ℓ_₂ (k := k))
        (f := oracleAtK)
        (y := getChallengeSuffix 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (k := k) (v := v)) := by
  sorry

set_option maxHeartbeats 200000 in
lemma logical_computeFoldedValue_eq_iterated_fold
    (oStmt : ∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ) j)
    (k : Fin (ℓ / ϑ))
    (v : AdditiveNTT.Comp.sDomain (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (R_rate := 𝓡)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) 0)
    (stmt : FinalSumcheckStatementOut (L := L) (ℓ := ℓ)) :
    let destDomainIdx : Fin r := ⟨k.val * ϑ + ϑ, by
      exact
        lt_r_of_le_ℓ (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          (oracle_index_add_steps_le_ℓ (ℓ := ℓ) (ϑ := ϑ)
            (i := Fin.last ℓ) (j := ⟨k.val, by
              rw [toOutCodewordsCount_last]
              exact k.isLt⟩))⟩
    let oracleAtK : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        ⟨oraclePositionToDomainIndex ℓ ϑ (i := Fin.last ℓ) ⟨k.val, by
          rw [toOutCodewordsCount_last]
          exact k.isLt⟩, by
          exact lt_r_of_lt_ℓ (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
            (h := by
              change k.val * ϑ < ℓ
              exact k_mul_ϑ_lt_ℓ (k := k))⟩ := by
        exact oStmt ⟨k.val, by
          rw [toOutCodewordsCount_last]
          exact k.isLt⟩
    logical_computeFoldedValue 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) k v stmt
      (logical_queryFiberPoints 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) oStmt k v)
      =
    iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := ⟨oraclePositionToDomainIndex ℓ ϑ (i := Fin.last ℓ) ⟨k.val, by
        rw [toOutCodewordsCount_last]
        exact k.isLt⟩, by
        exact lt_r_of_lt_ℓ (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          (h := by
            change k.val * ϑ < ℓ
            exact k_mul_ϑ_lt_ℓ (k := k))⟩)
      (destIdx := destDomainIdx)
      (steps := ϑ) (h_destIdx := by rfl) (h_destIdx_le := by
          exact k_succ_mul_ϑ_le_ℓ_₂ (k := k))
      (f := oracleAtK)
      (r_challenges := fun j =>
        stmt.challenges ⟨k.val * ϑ + j.val, by
          have h_le : k.val * ϑ + ϑ ≤ ℓ := k_succ_mul_ϑ_le_ℓ_₂ (k := k)
          have h_lt : k.val * ϑ + j.val < k.val * ϑ + ϑ := by
            exact Nat.add_lt_add_left j.isLt (k.val * ϑ)
          exact lt_of_lt_of_le h_lt h_le⟩)
      (getChallengeSuffix 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (k := k) (v := v)) := by
  sorry

end LogicalOracleVerification

end FinalQueryRoundIOR

end QueryPhase

section QueryPhaseHelperLemmas

open QueryPhase

set_option maxHeartbeats 10000 in
lemma iteratedQuotientMap_eq_qMap_total_fiber_extractMiddleFinMask
    (i : Fin r) (steps : ℕ) {destIdx : Fin r}
    (h_destIdx : destIdx.val = i.val + steps)
    (h_destIdx_le : destIdx.val ≤ ℓ)
    (v : AdditiveNTT.Comp.sDomain (𝔽q := 𝔽q) (β := β) (ℓ := ℓ)
      (R_rate := 𝓡) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨0, by omega⟩) :
    extractSuffixFromChallenge 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (v := v)
      (destIdx := i) (h_destIdx_le := by
        have h_i_le : i.val ≤ ℓ := by
          omega
        exact h_i_le) =
    qMap_total_fiber 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := i) (steps := steps) (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le)
      (y := extractSuffixFromChallenge 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (v := v)
        (destIdx := destIdx) (h_destIdx_le := h_destIdx_le))
      (extractMiddleFinMask 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (v := v) (i := i)
        (steps := steps)) := by
  sorry

open Classical in
lemma previousSuffix_eq_getFiberPoint_extractMiddleFinMask
    (j : Fin (ℓ / ϑ))
    (v : AdditiveNTT.Comp.sDomain (𝔽q := 𝔽q) (β := β) (ℓ := ℓ)
      (R_rate := 𝓡) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) 0) :
    extractSuffixFromChallenge 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (v := v)
      (destIdx := ⟨j.val * ϑ, by
        exact lt_r_of_lt_ℓ (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          (h := k_mul_ϑ_lt_ℓ (k := j))⟩)
      (h_destIdx_le := Nat.le_of_lt (k_mul_ϑ_lt_ℓ (k := j))) =
      getFiberPoint 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) j v
        (extractMiddleFinMask 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          (v := v)
          (i := ⟨j.val * ϑ, by
            exact lt_r_of_lt_ℓ (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
              (h := k_mul_ϑ_lt_ℓ (k := j))⟩)
          (steps := ϑ)) := by
  sorry

set_option maxHeartbeats 200000 in
-- The dependent index alignment in `getNextOracle` can take substantial elaboration.
lemma getNextOracle_eq_oracleStatement
    (oStmt : ∀ j, OracleStatement 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ) j)
    (j : Fin (nBlocks (ℓ := ℓ) (ϑ := ϑ)))
    (hj : j.val + 1 < nBlocks (ℓ := ℓ) (ϑ := ϑ)) :
    getNextOracle 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ϑ := ϑ)
      (i := Fin.last ℓ) (oStmt := oStmt) (j := j) (hj := hj)
      (destDomainIdx := ⟨j.val * ϑ + ϑ, by
        exact
          lt_r_of_le_ℓ (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
            (oracle_index_add_steps_le_ℓ (ℓ := ℓ) (ϑ := ϑ)
              (i := Fin.last ℓ) (j := j))⟩)
      (h_destDomainIdx := by rfl) =
    fun y =>
      (oStmt ⟨j.val + 1, hj⟩)
        (cast (by
          apply congrArg (fun i =>
            ↥(AdditiveNTT.Comp.sDomain (𝔽q := 𝔽q) (β := β) (ℓ := ℓ)
              (R_rate := 𝓡) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i))
          apply Fin.eq_of_val_eq
          simp only [oraclePositionToDomainIndex, toOutCodewordsCount_last]
          ring) y) := by
  funext y
  unfold getNextOracle
  simp only [cast_eq]

lemma logical_checkSingleRepetition_guard_eq
    (stmtIn : FinalSumcheckStatementOut (L := L) (ℓ := ℓ))
    (oStmtIn : ∀ j, OracleStatement 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ) j)
    (v : AdditiveNTT.Comp.sDomain (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (R_rate := 𝓡)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) 0)
    (h_accept : logical_checkSingleRepetition 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      oStmtIn v stmtIn stmtIn.final_constant)
    (j : Fin (nBlocks (ℓ := ℓ) (ϑ := ϑ)))
    (h_pos : 0 < j.val) :
    let j_idx : Fin (ℓ / ϑ) := ⟨j.val, by
      have h_lt := j.isLt
      simp only [nBlocks, toOutCodewordsCount_last] at h_lt
      exact h_lt⟩
    let j_prev_idx : Fin (ℓ / ϑ) := ⟨j.val - 1, by
      have h_lt := j.isLt
      simp only [nBlocks, toOutCodewordsCount_last] at h_lt
      omega⟩
    let destIdx : Fin r := ⟨j.val * ϑ, by
      exact
        lt_r_of_lt_ℓ (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          (h := by
            have h_lt := j.isLt
            simp only [nBlocks, toOutCodewordsCount_last] at h_lt
            exact k_mul_ϑ_lt_ℓ (k := ⟨j.val, h_lt⟩))⟩
    have h_destIdx_le : destIdx ≤ ℓ := by
      have h_lt := j.isLt
      simp only [nBlocks, toOutCodewordsCount_last] at h_lt
      exact Nat.le_of_lt (k_mul_ϑ_lt_ℓ (k := ⟨j.val, h_lt⟩))
    let suffix := extractSuffixFromChallenge 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (v := v) (destIdx := destIdx) (h_destIdx_le := h_destIdx_le)
    logical_computeFoldedValue 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      j_prev_idx v stmtIn
      (logical_queryFiberPoints 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        oStmtIn j_prev_idx v) =
    (oStmtIn j) suffix := by
  sorry

abbrev queryBlockIdx (j : Fin (nBlocks (ℓ := ℓ) (ϑ := ϑ))) : Fin (ℓ / ϑ) := ⟨j.val, by
  have h_lt := j.isLt
  simp only [nBlocks, toOutCodewordsCount_last] at h_lt
  exact h_lt⟩

abbrev queryBlockSourceIdx (j : Fin (nBlocks (ℓ := ℓ) (ϑ := ϑ))) : Fin r := ⟨j.val * ϑ, by
  exact lt_r_of_le_ℓ (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (oracle_index_le_ℓ (ℓ := ℓ) (ϑ := ϑ) (i := Fin.last ℓ) (j := j))⟩

abbrev queryBlockDestIdx (j : Fin (nBlocks (ℓ := ℓ) (ϑ := ϑ))) : Fin r :=
  ⟨j.val * ϑ + ϑ, by
    exact lt_r_of_le_ℓ (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (oracle_index_add_steps_le_ℓ (ℓ := ℓ) (ϑ := ϑ)
        (i := Fin.last ℓ) (j := j))⟩

lemma queryBlockSourceIdx_le
    (j : Fin (nBlocks (ℓ := ℓ) (ϑ := ϑ))) :
    (queryBlockSourceIdx (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) j).val ≤ ℓ := by
  exact oracle_index_le_ℓ (ℓ := ℓ) (ϑ := ϑ) (i := Fin.last ℓ) (j := j)

lemma queryBlockDestIdx_le
    (j : Fin (nBlocks (ℓ := ℓ) (ϑ := ϑ))) :
    (queryBlockDestIdx (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) j).val ≤ ℓ := by
  exact oracle_index_add_steps_le_ℓ (ℓ := ℓ) (ϑ := ϑ)
    (i := Fin.last ℓ) (j := j)

abbrev queryBlockSourceSuffix
    (j : Fin (nBlocks (ℓ := ℓ) (ϑ := ϑ)))
    (v : AdditiveNTT.Comp.sDomain (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (R_rate := 𝓡)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) 0) :
    AdditiveNTT.Comp.sDomain (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (R_rate := 𝓡)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (queryBlockSourceIdx (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) j) :=
  extractSuffixFromChallenge 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (v := v)
      (destIdx := queryBlockSourceIdx (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) j)
      (h_destIdx_le := queryBlockSourceIdx_le
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) j)

abbrev queryBlockDestSuffix
    (j : Fin (nBlocks (ℓ := ℓ) (ϑ := ϑ)))
    (v : AdditiveNTT.Comp.sDomain (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (R_rate := 𝓡)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) 0) :
    AdditiveNTT.Comp.sDomain (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (R_rate := 𝓡)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (queryBlockDestIdx (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) j) :=
  extractSuffixFromChallenge 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (v := v)
      (destIdx := queryBlockDestIdx (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) j)
      (h_destIdx_le := queryBlockDestIdx_le
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) j)

lemma queryBlockDestIdx_eq_queryBlockSourceIdx_succ
    (j : Fin (nBlocks (ℓ := ℓ) (ϑ := ϑ)))
    (hj : j.val + 1 < nBlocks (ℓ := ℓ) (ϑ := ϑ)) :
    queryBlockDestIdx (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) j =
      queryBlockSourceIdx (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ)
        ⟨j.val + 1, hj⟩ := by
  apply Fin.eq_of_val_eq
  simp only [queryBlockDestIdx, queryBlockSourceIdx]
  ring

lemma queryBlockDestSuffix_eq_queryBlockSourceSuffix_succ
    (j : Fin (nBlocks (ℓ := ℓ) (ϑ := ϑ)))
    (hj : j.val + 1 < nBlocks (ℓ := ℓ) (ϑ := ϑ))
    (v : AdditiveNTT.Comp.sDomain (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (R_rate := 𝓡)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) 0) :
    queryBlockDestSuffix (𝔽q := 𝔽q) (β := β)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) j v =
      cast (by
        rw [queryBlockDestIdx_eq_queryBlockSourceIdx_succ
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) (j := j) (hj := hj)])
        (queryBlockSourceSuffix (𝔽q := 𝔽q) (β := β)
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) ⟨j.val + 1, hj⟩ v) := by
  sorry

lemma queryBlockSourceSuffix_maps_to_destSuffix
    (j : Fin (nBlocks (ℓ := ℓ) (ϑ := ϑ)))
    (v : AdditiveNTT.Comp.sDomain (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (R_rate := 𝓡)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) 0) :
    iteratedQuotientMap 𝔽q β h_ℓ_add_R_rate
      (i := queryBlockSourceIdx
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) j)
      (destIdx := queryBlockDestIdx
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) j)
      (k := ϑ) (h_destIdx := by rfl)
      (h_destIdx_le := queryBlockDestIdx_le
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) j)
      (x := AdditiveNTT.Comp.toCanonicalSDomain (𝔽q := 𝔽q) (β := β) (ℓ := ℓ)
        (R_rate := 𝓡) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (i := queryBlockSourceIdx (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) j)
        (queryBlockSourceSuffix (𝔽q := 𝔽q) (β := β)
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) j v)) =
    AdditiveNTT.Comp.toCanonicalSDomain (𝔽q := 𝔽q) (β := β) (ℓ := ℓ)
      (R_rate := 𝓡) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := queryBlockDestIdx (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) j)
      (queryBlockDestSuffix (𝔽q := 𝔽q) (β := β)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) j v) := by
  sorry

set_option maxHeartbeats 10000 in
lemma UDRCodeword_eval_eq_of_fin_eq
    {i j : Fin r} (hij : i = j)
    {hi : i ≤ ℓ} {hj : j ≤ ℓ}
    {f : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i}
    {g : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) j}
    (hfg : HEq f g)
    (hf_close : UDRClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i hi f)
    (y : AdditiveNTT.Comp.sDomain (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (R_rate := 𝓡)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) j) :
    let hg_close :=
      UDRClose_of_fin_eq (𝔽q := 𝔽q) (β := β)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        hij hfg hf_close
    UDRCodeword 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      i hi f hf_close
      (cast (by rw [hij]) y) =
    UDRCodeword 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      j hj g hg_close
      y := by
  sorry

set_option maxHeartbeats 10000 in
lemma successor_codeword_eval_eq
    (oStmtIn : ∀ j, OracleStatement 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ) j)
    (j : Fin (nBlocks (ℓ := ℓ) (ϑ := ϑ)))
    (hj : j.val + 1 < nBlocks (ℓ := ℓ) (ϑ := ϑ))
    (v : AdditiveNTT.Comp.sDomain (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (R_rate := 𝓡)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) 0)
    (h_next_close_stmt :
      let j_next : Fin (nBlocks (ℓ := ℓ) (ϑ := ϑ)) := ⟨j.val + 1, hj⟩
      UDRClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (queryBlockDestIdx
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) j)
        (queryBlockDestIdx_le
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) j)
        (fun y => (oStmtIn j_next)
          (cast (by
          rw [queryBlockDestIdx_eq_queryBlockSourceIdx_succ
            (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) (j := j) (hj := hj)]) y)))
    (h_next_close :
      let j_next : Fin (nBlocks (ℓ := ℓ) (ϑ := ϑ)) := ⟨j.val + 1, hj⟩
      UDRClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (queryBlockSourceIdx
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) j_next)
        (queryBlockSourceIdx_le
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) j_next)
        (oStmtIn j_next)) :
    let j_next : Fin (nBlocks (ℓ := ℓ) (ϑ := ϑ)) := ⟨j.val + 1, hj⟩
    UDRCodeword 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (queryBlockDestIdx
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) j)
      (queryBlockDestIdx_le
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) j)
      (f := fun y => (oStmtIn j_next)
        (cast (by
        rw [queryBlockDestIdx_eq_queryBlockSourceIdx_succ
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) (j := j) (hj := hj)]) y))
      (h_within_radius := h_next_close_stmt)
      (cast (by
      rw [queryBlockDestIdx_eq_queryBlockSourceIdx_succ
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) (j := j) (hj := hj)])
      (queryBlockSourceSuffix (𝔽q := 𝔽q) (β := β)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) j_next v)) =
    UDRCodeword 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (queryBlockSourceIdx
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) j_next)
      (queryBlockSourceIdx_le
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) j_next)
      (f := oStmtIn j_next)
      (h_within_radius := h_next_close)
      (queryBlockSourceSuffix (𝔽q := 𝔽q) (β := β)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) j_next v) := by
  sorry

end QueryPhaseHelperLemmas

end

end Binius.BinaryBasefold

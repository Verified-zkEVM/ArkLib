/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Quang Dao
-/
module

public import ArkLib.ProofSystem.Binius.BinaryBasefold.Spec

/-!
# Binary Basefold: the query-phase check

One repetition of the Binary Basefold query phase takes a point `v ∈ S⁽⁰⁾` and walks the oracles
block by block. At block `k` (domain index `i = k·ϑ`) it reads the oracle at position `k` on the
fiber of `S⁽ⁱ⁾` over the suffix of `v` at domain index `i + ϑ`; for `i > 0` it requires the value
carried from the previous block to equal the oracle's value at the suffix of `v` at `i`; and it
carries the fold of the fiber values to the next block. Finally it requires the carried value to
equal the final constant.

This file states that check twice: as an oracle computation, which the query-phase verifier runs,
and as a proposition over the oracle statements, which the soundness analysis uses. It also
provides the index and suffix bookkeeping that relates consecutive blocks.

## Main definitions

* `QueryPhase.extractSuffixFromChallenge`: the image of `v` in `S⁽ʲ⁾` under the iterated quotient
  map, i.e. the suffix of `v` at domain index `j`.
* `QueryPhase.queryFiberPoints`, `QueryPhase.checkSingleFoldingStep`,
  `QueryPhase.checkSingleRepetition`: the check as an oracle computation.
* `QueryPhase.logicalQueryFiberPoints`, `QueryPhase.logicalComputeFoldedValue`,
  `QueryPhase.LogicalCheckSingleFoldingStep`, `QueryPhase.LogicalStepCondition`,
  `QueryPhase.LogicalCheckSingleRepetition`, `QueryPhase.LogicalProximityChecksSpec`: the check
  as a proposition, for one repetition and for all `γ` repetitions.
* `QueryPhase.queryRbrKnowledgeError`: the round-by-round knowledge error of the query phase,
  `(1/2 + 1/(2 · 2^𝓡))^γ`.
* `queryBlockSourceIdx`, `queryBlockDestIdx`, `queryBlockSourceSuffix`, `queryBlockDestSuffix`:
  the domain indices `j·ϑ` and `j·ϑ + ϑ` of block `j`, and the suffixes of `v` there.

## Main statements

* `QueryPhase.logicalComputeFoldedValue_eq_iteratedFold`: the value a block carries forward is
  the fold of the block's oracle at the suffix of `v`.
* `logicalComputeFoldedValue_eq_of_logicalCheckSingleRepetition`: in an accepting repetition,
  the value carried into block `j > 0` is the oracle's value at the suffix of `v` at `j·ϑ`.
* `iteratedQuotientMap_queryBlockSourceSuffix`: the iterated quotient map sends the source suffix
  of a block to its destination suffix.
* `uniqueDecodingCodeword_queryBlockDestIdx_eq_queryBlockSourceIdx_succ`: the decoded codeword
of the next
  oracle, read at the destination index of block `j`, is the decoded codeword of oracle `j + 1`.

## References

* [Diamond, B.E. and Posen, J., *Polylogarithmic proofs for multilinears over binary towers*][DP24]
  Numbering follows the archived revision of [DP24]. The check is step 4 of the evaluation IOP of
  Construction 4.12 (lines 1–7).
-/

@[expose] public section

variable {ι : Type} {oSpec : OracleSpec ι}

namespace Binius.BinaryBasefold

open OracleSpec OracleComp ProtocolSpec Finset AdditiveNTT Polynomial MvPolynomial
  Binius.BinaryBasefold
open scoped NNReal
open ReedSolomon Code BerlekampWelch Function
open Finset AdditiveNTT Polynomial MvPolynomial Nat Matrix
open ProbabilityTheory

variable {r : ℕ} [NeZero r]
variable {L : Type} [Field L] [Fintype L] [DecidableEq L]
variable (𝔽q : Type) [Field 𝔽q]
local instance [Finite 𝔽q] : Fact (Nat.Prime (ringChar 𝔽q)) :=
  ⟨CharP.prime_ringChar 𝔽q⟩
variable [Fintype 𝔽q] [DecidableEq 𝔽q]
  [hF₂ : Fact (Fintype.card 𝔽q = 2)]
variable [Algebra 𝔽q L]
variable (β : Fin r → L) [hβ_lin_indep : Fact (LinearIndependent 𝔽q β)]
  [h_β₀_eq_1 : Fact (β 0 = 1)]
variable {ℓ 𝓡 ϑ : ℕ} (γ_repetitions : ℕ) [NeZero ℓ] [NeZero 𝓡] [NeZero ϑ]
variable {h_ℓ_add_R_rate : ℓ + 𝓡 < r}
noncomputable section
variable [hdiv : Fact (ϑ ∣ ℓ)]

open scoped NNReal ProbabilityTheory

namespace QueryPhase

/-! ### Blocks, suffixes and the error -/

/-- The number of oracles, i.e. of blocks of `ϑ` folds, at the end of the protocol. -/
abbrev nBlocks : ℕ := toOutCodewordsCount ℓ ϑ (Fin.last ℓ)

/-- The suffix of the query point `v ∈ S⁽⁰⁾` at domain index `destIdx`: its image in
`S⁽ᵈᵉˢᵗᴵᵈˣ⁾` under the iterated quotient map. -/
def extractSuffixFromChallenge (v : sDomain 𝔽q β h_ℓ_add_R_rate ⟨0, by omega⟩)
    (destIdx : Fin r) (h_destIdx_le : destIdx ≤ ℓ) :
    sDomain 𝔽q β h_ℓ_add_R_rate destIdx :=
  iteratedQuotientMap 𝔽q β h_ℓ_add_R_rate (i := ⟨0, by omega⟩) (k := destIdx.val)
    (h_destIdx := by simp only [zero_add]) (h_destIdx_le := h_destIdx_le) (x := v)

omit [DecidableEq 𝔽q] hF₂ [NeZero 𝓡] [NeZero ℓ] in
/-- Suffix extraction along an equality of destination indices, up to the cast between the
two domains. -/
lemma extractSuffixFromChallenge_congr_destIdx
    (v : sDomain 𝔽q β h_ℓ_add_R_rate ⟨0, by omega⟩)
    {destIdx destIdx' : Fin r}
    (h_idx_eq : destIdx = destIdx')
    (h_le : destIdx ≤ ℓ)
    (h_le' : destIdx' ≤ ℓ) :
    extractSuffixFromChallenge 𝔽q β v destIdx h_le =
    cast (by rw [h_idx_eq]) (extractSuffixFromChallenge 𝔽q β v destIdx' h_le') := by
  subst h_idx_eq; rfl

omit [DecidableEq 𝔽q] h_β₀_eq_1 in
/-- Under `StrictOracleFoldingConsistent`, the first oracle is the evaluation over `S⁽⁰⁾`
of the univariate polynomial whose novel-basis coefficients are the values of `t` on the
hypercube. This is the consistency property at position `0`, where the fold has `0` steps. -/
lemma polyToOracleFunc_eq_getFirstOracle
    (t : MultilinearPoly L ℓ)
    (i : Fin (ℓ + 1))
    (challenges : Fin i → L)
    (oStmt : ∀ j, OracleStatement 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i j)
    (h_consistency : StrictOracleFoldingConsistent 𝔽q β (t := t) (i := i)
      (challenges := challenges) (oStmt := oStmt)) :
    let P₀ : L[X]_(2 ^ ℓ) :=
      polynomialFromNovelCoeffsF₂ 𝔽q β ℓ (by omega) (fun ω => t.val.eval (bitsOfIndex ω))
    let f₀ := polyToOracleFunc 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (domainIdx := 0) (P := P₀)
    f₀ = getFirstOracle 𝔽q β oStmt := by
  intro P₀ f₀
  -- Use StrictOracleFoldingConsistent for j = 0
  have h_pos : 0 < toOutCodewordsCount ℓ ϑ i := by
    exact (instNeZeroNatToOutCodewordsCount ℓ ϑ i).pos
  have h_first_oracle := h_consistency ⟨0, by omega⟩
  dsimp only [StrictOracleFoldingConsistent] at h_first_oracle
  dsimp only [f₀, P₀, getFirstOracle] at h_first_oracle ⊢
  rw [h_first_oracle]
  funext y
  conv_rhs =>
    rw [iteratedFold_congr_steps_index 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (steps' := 0)
      (h_destIdx := by simp only [Nat.zero_mod, zero_mul, Fin.coe_ofNat_eq_mod, add_zero])
      (h_destIdx_le := by simp only [zero_mul, zero_le])
      (h_steps_eq_steps' := by simp only [zero_mul])]
    rw [iteratedFold_zero_steps 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := 0)
      (h_destIdx := by simp only [Nat.zero_mod, zero_mul, Fin.coe_ofNat_eq_mod])]
  congr 1
  exact eq_of_heq ((cast_heq _ _).trans (cast_heq _ _)).symm

/-- The acceptance probability bound of one query repetition against a noncompliant oracle:
`1/2 + 1/(2 · 2^𝓡)`. -/
def queryRbrKnowledgeErrorSingleRepetition : ℝ≥0 := ((1/2 : ℝ≥0) + (1 : ℝ≥0) / (2 * 2^𝓡))

/-- The round-by-round knowledge error of the query phase, `(1/2 + 1/(2 · 2^𝓡))^γ`, at its one
challenge. -/
def queryRbrKnowledgeError :
    (pSpecQuery 𝔽q β γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).ChallengeIdx → ℝ≥0 :=
  fun _ =>
  (queryRbrKnowledgeErrorSingleRepetition (𝓡 := 𝓡))^γ_repetitions

/-- The oracle computation that queries the committed oracle at position `j` at a point of its
domain. -/
def queryCodeword (j : Fin (toOutCodewordsCount ℓ ϑ (Fin.last ℓ)))
    (point : (sDomain 𝔽q β h_ℓ_add_R_rate) ⟨oraclePositionToDomainIndex ℓ ϑ j, by omega⟩) :
    OptionT (OracleComp (oSpec +
      ([OracleStatement 𝔽q β (ϑ:=ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ( Fin.last ℓ)]ₒ +
      [(pSpecQuery 𝔽q β γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).Message]ₒ))) L :=
    query (spec := [OracleStatement 𝔽q β (ϑ:=ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ)]ₒ)
      ⟨⟨j, by omega⟩, point⟩

section FinalQueryRoundIOR

/-! ### Fiber points -/

/-- The suffix of `v` at the destination index `k·ϑ + ϑ` of block `k`. -/
def getChallengeSuffix (k : Fin (ℓ / ϑ)) (v : sDomain 𝔽q β h_ℓ_add_R_rate ⟨0, by omega⟩) :
    let i := k.val * ϑ
    have h_i_add_ϑ_le_ℓ : i + ϑ ≤ ℓ := k_succ_mul_ϑ_le_ℓ_₂ (k := k)
    let destIdx : Fin r := ⟨i + ϑ, by omega⟩
    sDomain 𝔽q β h_ℓ_add_R_rate destIdx :=
  have h_i_add_ϑ_le_ℓ := k_succ_mul_ϑ_le_ℓ_₂ (k := k)
  extractSuffixFromChallenge 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (v:=v) (destIdx := ⟨k.val * ϑ + ϑ, by omega⟩) (h_destIdx_le:=by omega)

/-- The point `(u₀, …, u_{ϑ-1}, v_{i+ϑ}, …, v_{ℓ+𝓡-1})` of `S⁽ⁱ⁾`, `i = k·ϑ`, for a fiber index
`u ∈ B_ϑ`: the `u`-th point of the fiber over the suffix of `v` at `i + ϑ`. -/
noncomputable def getFiberPoint
    (k : Fin (ℓ / ϑ)) (v : sDomain 𝔽q β h_ℓ_add_R_rate ⟨0, by omega⟩) (u : Fin (2 ^ ϑ)) :
    (sDomain 𝔽q β h_ℓ_add_R_rate) (i := ⟨oraclePositionToDomainIndex ℓ ϑ (i := Fin.last ℓ)
      (positionIdx := ⟨k, by simp only [toOutCodewordsCount_last, Fin.is_lt]⟩),
        lt_r_of_lt_ℓ (x := k.val * ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (h := k_mul_ϑ_lt_ℓ)⟩) := by
    exact
      quotientFiber 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
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

/-! ### The check as an oracle computation -/

/-- The oracle computation that reads the oracle of block `k` on the whole fiber: the vector of
its values at `getFiberPoint k v u` for `u ∈ B_ϑ`. -/
noncomputable def queryFiberPoints
    (k : Fin (ℓ / ϑ))
    (v : sDomain 𝔽q β h_ℓ_add_R_rate ⟨0, by omega⟩) :
  OptionT
        (OracleComp
          (oSpec + ([OracleStatement 𝔽q β (ϑ := ϑ)
            (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ)]ₒ +
            [(pSpecQuery 𝔽q β γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).Message]ₒ)))
        (Vector L (2^ϑ)) := do
  let k_th_oracleIdx : Fin (toOutCodewordsCount ℓ ϑ (Fin.last ℓ)) :=
    ⟨k, by simp only [toOutCodewordsCount, Fin.val_last, lt_self_iff_false, ↓reduceIte, add_zero,
      Fin.is_lt]⟩
  let results : Vector L (2^ϑ) ← (⟨Array.finRange (2^ϑ), by simp only [Array.size_finRange]⟩ :
    Vector (Fin (2^ϑ)) (2^ϑ)).mapM (fun (u : Fin (2^ϑ)) => do
    queryCodeword 𝔽q β (γ_repetitions := γ_repetitions) (ϑ:=ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (j := k_th_oracleIdx) (point :=
        getFiberPoint 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (k := k) (v := v) (u := u))
  )
  pure results

/-- One block of the check as an oracle computation: read the fiber of block `k_val`; if its
domain index `i = k_val·ϑ` is positive, fail unless `c_cur` equals the oracle's value at the
suffix of `v` at `i`; return the fold of the fiber values by the block's challenges. -/
noncomputable def checkSingleFoldingStep
    (k_val : Fin (ℓ / ϑ)) (c_cur : L) (v : sDomain 𝔽q β h_ℓ_add_R_rate ⟨0, by omega⟩)
    (stmt : FinalSumcheckStatementOut (L := L) (ℓ := ℓ)) :
    OptionT (OracleComp (oSpec + ([OracleStatement 𝔽q β (ϑ:=ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ)]ₒ + [(pSpecQuery 𝔽q β
      γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).Message]ₒ))) L := do
  let i := k_val.val * ϑ
  have h_k: k_val ≤ (ℓ/ϑ - 1) := by omega
  have h_i_add_ϑ_le_ℓ : i + ϑ ≤ ℓ := by
    calc i + ϑ = k_val * ϑ + ϑ := by omega
      _ ≤ (ℓ/ϑ - 1) * ϑ + ϑ := by
        apply Nat.add_le_add_right; apply Nat.mul_le_mul_right; omega
      _ = ℓ/ϑ * ϑ := by
        rw [Nat.sub_mul, one_mul, Nat.sub_add_cancel];
        conv_lhs => rw [←one_mul ϑ]
        apply Nat.mul_le_mul_right; omega
      _ ≤ ℓ := by apply Nat.div_mul_le_self;
  have h_i_lt_ℓ : i < ℓ := by
    calc i ≤ ℓ - ϑ := by omega
      _ < ℓ := by
        apply Nat.sub_lt (by exact Nat.pos_of_neZero ℓ) (by exact Nat.pos_of_neZero ϑ)
  let f_i_on_fiber ← queryFiberPoints 𝔽q β (γ_repetitions := γ_repetitions) (ϑ := ϑ)
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate) k_val v
  -- Check consistency if i > 0
  if h_i_pos : i > 0 then
    let oracle_point_idx := extractMiddleFinMask 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (v:=v) (i:=⟨i, by omega⟩) (steps:=ϑ)
    let f_i_val := f_i_on_fiber.get oracle_point_idx
    guard (c_cur = f_i_val)
  -- Compute next folded value
  let destIdx : Fin r := ⟨i + ϑ, by omega⟩
  let next_suffix_of_v : sDomain 𝔽q β h_ℓ_add_R_rate destIdx :=
    getChallengeSuffix (k := k_val) (v := v)
  let cur_challenge_batch : Fin ϑ → L := fun j =>
    stmt.challenges ⟨i + j.val, by simp only [Fin.val_last]; omega⟩
  -- c_next = folded value at step k (logical counterpart: `logicalComputeFoldedValue`)
  let c_next : L := pointFoldMatrixForm 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (i:=⟨i, by omega⟩) (steps:=ϑ) (destIdx:=destIdx) (h_destIdx:=by dsimp only [destIdx])
    (h_destIdx_le:=by omega) (r_challenges:=cur_challenge_batch) (y:=next_suffix_of_v)
    (fiber_eval_mapping := f_i_on_fiber.get)
  return c_next

/-- One repetition of the check as an oracle computation: run `checkSingleFoldingStep` on the
blocks `0, …, ℓ/ϑ - 1` in order, threading the carried value, and fail unless the final carried
value equals `finalConstant`. A failed step fails the whole computation. -/
noncomputable def checkSingleRepetition
    (v : sDomain 𝔽q β h_ℓ_add_R_rate ⟨0, by omega⟩)
    (stmt : FinalSumcheckStatementOut (L := L) (ℓ := ℓ)) (finalConstant : L) :
    OptionT (OracleComp (oSpec + ([OracleStatement 𝔽q β (ϑ:=ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ)]ₒ + [(pSpecQuery 𝔽q β
      γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).Message]ₒ))) Unit := do
  let mut c_cur : L := 0 -- Will be initialized in first iteration
  -- Blocks `0, …, ℓ/ϑ - 1`; a failed guard fails the whole computation.
  for k_val in List.finRange (ℓ / ϑ) do
    let c_next ← checkSingleFoldingStep 𝔽q β (ϑ:=ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (γ_repetitions := γ_repetitions)
        ⟨k_val, by omega⟩ c_cur v stmt
    c_cur := c_next
  -- Final check: c_ℓ ?= finalConstant
  guard (c_cur = finalConstant)

end MonadicOracleVerification

section LogicalOracleVerification

/-! ### The check as a proposition

Each oracle computation above has a propositional counterpart over the oracle statements:
`queryFiberPoints` is `logicalQueryFiberPoints`, `checkSingleFoldingStep` is
`LogicalCheckSingleFoldingStep` (the guard) together with `logicalComputeFoldedValue` (the
returned value), and `checkSingleRepetition` is `LogicalCheckSingleRepetition`. Instead of
threading the carried value, the propositional form recomputes it at block `k` from block
`k - 1`. -/

/-- The values of the oracle of block `k` on the fiber over the suffix of `v` at `k·ϑ + ϑ`. -/
def logicalQueryFiberPoints
    (oStmt : ∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ) j)
    (k : Fin (ℓ / ϑ)) (v : sDomain 𝔽q β h_ℓ_add_R_rate ⟨0, by omega⟩) : Fin (2 ^ ϑ) → L :=
  let k_th_oracleIdx : Fin (toOutCodewordsCount ℓ ϑ (Fin.last ℓ)) :=
    ⟨k.val, by simp only [toOutCodewordsCount, Fin.val_last, lt_self_iff_false, ↓reduceIte,
      add_zero, Fin.is_lt]⟩
  fun u => oStmt k_th_oracleIdx (getFiberPoint 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) k v u)

/-- The value block `k` carries forward: the fold, by the block's `ϑ` challenges, of the fiber
values `f_i_on_fiber` over the suffix of `v` at `k·ϑ + ϑ`. -/
def logicalComputeFoldedValue
    (k : Fin (ℓ / ϑ)) (v : sDomain 𝔽q β h_ℓ_add_R_rate ⟨0, by omega⟩)
    (stmt : FinalSumcheckStatementOut (L := L) (ℓ := ℓ))
    (f_i_on_fiber : Fin (2 ^ ϑ) → L) : L :=
  let i := k.val * ϑ
  have h_i_add_ϑ_le_ℓ : i + ϑ ≤ ℓ := k_succ_mul_ϑ_le_ℓ_₂ (k := k)
  let destIdx : Fin r := ⟨i + ϑ, by omega⟩
  let next_suffix_of_v : sDomain 𝔽q β h_ℓ_add_R_rate destIdx :=
    getChallengeSuffix (k := k) (v := v)
  let cur_challenge_batch : Fin ϑ → L := fun j =>
    stmt.challenges ⟨i + j.val, by simp only [Fin.val_last]; omega⟩
  pointFoldMatrixForm 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (i := ⟨i, by omega⟩) (steps := ϑ) (destIdx := destIdx) (h_destIdx := by dsimp only [destIdx])
    (h_destIdx_le := by omega) (r_challenges := cur_challenge_batch) (y := next_suffix_of_v)
    (fiber_eval_mapping := f_i_on_fiber)

/-- The guard of block `k`: if its domain index `i = k·ϑ` is positive, the value carried from
block `k - 1` equals the value of the oracle of block `k` at the suffix of `v` at `i`;
otherwise `True`. -/
def LogicalCheckSingleFoldingStep
    (oStmt : ∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ) j)
    (k : Fin (ℓ / ϑ)) (v : sDomain 𝔽q β h_ℓ_add_R_rate ⟨0, by omega⟩)
    (stmt : FinalSumcheckStatementOut (L := L) (ℓ := ℓ)) : Prop :=
  -- `k ∈ {0, 1, ..., ℓ/ϑ-1}`, `i ∈ {0, ϑ, 2ϑ, ..., ℓ-ϑ}`
  let i := k.val * ϑ
  have h_i_add_ϑ_le_ℓ : i + ϑ ≤ ℓ := k_succ_mul_ϑ_le_ℓ_₂ (k := k)
  let f_i_on_fiber := logicalQueryFiberPoints 𝔽q β oStmt k v
  -- The guard reads one point of the fiber, as `guard (c_cur = f_i_val)` does.
  if h_i_pos : i > 0 then
    -- h_i_pos implies k > 0 (since i = k * ϑ and ϑ > 0)
    have h_k_pos : k.val > 0 := Nat.pos_of_mul_pos_right h_i_pos
    let k_prev : Fin (ℓ / ϑ) := ⟨k.val - 1, by omega⟩
    -- c_cur = fold value from step k-1
    let f_prev_on_fiber := logicalQueryFiberPoints 𝔽q β oStmt k_prev v
    -- Recomputed from block `k - 1`; the oracle computation threads it instead.
    let c_cur := logicalComputeFoldedValue 𝔽q β k_prev v stmt f_prev_on_fiber
    -- f_i_val = oracle value at overlap point
    let oracle_point_idx := extractMiddleFinMask 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (v := v) (i := ⟨i, by omega⟩) (steps := ϑ)
    let f_i_val := f_i_on_fiber oracle_point_idx
    c_cur = f_i_val
  else True

/-- The condition at step `k ∈ {0, …, ℓ/ϑ}`: the guard of block `k` for `k < ℓ/ϑ`, and for
`k = ℓ/ϑ` the equality of the value carried from the last block with `finalConstant`. -/
def LogicalStepCondition
    (oStmt : ∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ) j)
    (k : Fin (ℓ / ϑ + 1)) (v : sDomain 𝔽q β h_ℓ_add_R_rate ⟨0, by omega⟩)
    (stmt : FinalSumcheckStatementOut (L := L) (ℓ := ℓ)) (finalConstant : L) : Prop :=
  if h_k_lt : k.val < (ℓ / ϑ) then
    -- Condition for `k ∈ {0, 1, ..., ℓ/ϑ-1}`
    LogicalCheckSingleFoldingStep 𝔽q β oStmt ⟨k.val, h_k_lt⟩ v stmt
  else
    -- Condition for the final state k = `ℓ/ϑ`
    have h_div_pos : ℓ / ϑ > 0 :=
      Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_neZero ℓ) hdiv.out) (Nat.pos_of_neZero ϑ)
    let k_last : Fin (ℓ / ϑ) := ⟨ℓ / ϑ - 1, by omega⟩
    let f_last_on_fiber := logicalQueryFiberPoints 𝔽q β oStmt k_last v
    logicalComputeFoldedValue 𝔽q β k_last v stmt f_last_on_fiber = finalConstant

/-- One repetition of the check accepts at `v`: every step condition holds, i.e. every block's
guard and the final equality with `finalConstant`. -/
def LogicalCheckSingleRepetition
    (oStmt : ∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ) j)
    (v : sDomain 𝔽q β h_ℓ_add_R_rate ⟨0, by omega⟩)
    (stmt : FinalSumcheckStatementOut (L := L) (ℓ := ℓ)) (finalConstant : L) : Prop :=
  ∀ k : Fin (ℓ / ϑ + 1),
    LogicalStepCondition 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (oStmt := oStmt) (k := k) (v := v) (stmt := stmt) (finalConstant := finalConstant)

/-- All `γ` repetitions accept, at their query points `γ_challenges`. -/
def LogicalProximityChecksSpec
    (γ_challenges : Fin γ_repetitions → sDomain 𝔽q β h_ℓ_add_R_rate ⟨0, by omega⟩)
    (oStmt : ∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ) j)
    (stmt : FinalSumcheckStatementOut (L := L) (ℓ := ℓ)) (finalConstant : L) : Prop :=
  ∀ rep : Fin γ_repetitions,
    LogicalCheckSingleRepetition 𝔽q β oStmt (γ_challenges rep) stmt finalConstant

omit [DecidableEq 𝔽q] hF₂  in
/-- `getFiberPoint` is the fiber map `quotientFiber` of block `k` over the suffix of `v`. -/
lemma getFiberPoint_eq_quotientFiber
    (k : Fin (ℓ / ϑ)) (v : sDomain 𝔽q β h_ℓ_add_R_rate ⟨0, by omega⟩)
    (u : Fin (2 ^ ϑ)) :
    getFiberPoint 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) k v u =
      quotientFiber 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (i := ⟨k.val * ϑ,
          lt_r_of_lt_ℓ (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (x := k.val * ϑ)
            (h := k_mul_ϑ_lt_ℓ (k := k))⟩)
        (steps := ϑ) (h_destIdx := by rfl)
        (h_destIdx_le := by exact k_succ_mul_ϑ_le_ℓ_₂ (k := k))
        (y := getChallengeSuffix 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (k := k) (v := v)) u := by
  unfold getFiberPoint
  simp only [oraclePositionToDomainIndex]

omit [DecidableEq 𝔽q] hF₂  in
/-- The fiber values of block `k` are the oracle's `fiberEvaluations` over the suffix of `v`. -/
lemma logicalQueryFiberPoints_eq_fiberEvaluations
    (oStmt : ∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ) j)
    (k : Fin (ℓ / ϑ)) (v : sDomain 𝔽q β h_ℓ_add_R_rate ⟨0, by omega⟩) :
    logicalQueryFiberPoints 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) oStmt k v =
      fiberEvaluations 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (i := ⟨k.val * ϑ,
          lt_r_of_lt_ℓ (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (x := k.val * ϑ)
            (h := k_mul_ϑ_lt_ℓ (k := k))⟩) (steps := ϑ)
        (h_destIdx := by rfl) (h_destIdx_le := by
          exact k_succ_mul_ϑ_le_ℓ_₂ (k := k))
        (f := oStmt ⟨k.val, by
          simp only [toOutCodewordsCount, Fin.val_last, lt_self_iff_false, ↓reduceIte, add_zero,
            Fin.is_lt]⟩)
        (y := getChallengeSuffix 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (k := k) (v := v)) := by
  funext u
  simp only [logicalQueryFiberPoints, fiberEvaluations]
  rw [getFiberPoint_eq_quotientFiber 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) k v u]

omit [DecidableEq 𝔽q] hF₂  in
/-- The value block `k` carries forward is the `ϑ`-step fold of the block's oracle, by the
block's challenges, evaluated at the suffix of `v` at `k·ϑ + ϑ`. -/
lemma logicalComputeFoldedValue_eq_iteratedFold
    (oStmt : ∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ) j)
    (k : Fin (ℓ / ϑ)) (v : sDomain 𝔽q β h_ℓ_add_R_rate ⟨0, by omega⟩)
    (stmt : FinalSumcheckStatementOut (L := L) (ℓ := ℓ)) :
    logicalComputeFoldedValue 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) k v stmt
      (logicalQueryFiberPoints 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) oStmt k v)
      =
    iteratedFold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := ⟨k.val * ϑ,
        lt_r_of_lt_ℓ (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (x := k.val * ϑ)
          (h := k_mul_ϑ_lt_ℓ (k := k))⟩) (steps := ϑ)
      (h_destIdx := by rfl) (h_destIdx_le := by
        exact k_succ_mul_ϑ_le_ℓ_₂ (k := k))
      (f := oStmt ⟨k.val, by
        simp only [toOutCodewordsCount, Fin.val_last, lt_self_iff_false, ↓reduceIte, add_zero,
          Fin.is_lt]⟩)
      (r_challenges := fun j =>
        stmt.challenges ⟨k.val * ϑ + j.val, by
          have h_le : k.val * ϑ + ϑ ≤ ℓ := k_succ_mul_ϑ_le_ℓ_₂ (k := k)
          have h_lt : k.val * ϑ + j.val < k.val * ϑ + ϑ := by
            exact Nat.add_lt_add_left j.isLt (k.val * ϑ)
          exact lt_of_lt_of_le h_lt h_le⟩)
      (y := getChallengeSuffix 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (k := k) (v := v)) := by
  simp only [logicalComputeFoldedValue]
  rw [iteratedFold_eq_matrix_form 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (i := ⟨k.val * ϑ,
      lt_r_of_lt_ℓ (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (x := k.val * ϑ)
        (h := k_mul_ϑ_lt_ℓ (k := k))⟩) (steps := ϑ)
    (h_destIdx := by rfl) (h_destIdx_le := by exact k_succ_mul_ϑ_le_ℓ_₂ (k := k))
    (f := oStmt ⟨k.val, by
      simp only [toOutCodewordsCount, Fin.val_last, lt_self_iff_false, ↓reduceIte, add_zero,
        Fin.is_lt]⟩)
    (r_challenges := fun j =>
      stmt.challenges ⟨k.val * ϑ + j.val, by
        have h_le : k.val * ϑ + ϑ ≤ ℓ := k_succ_mul_ϑ_le_ℓ_₂ (k := k)
        have h_lt : k.val * ϑ + j.val < k.val * ϑ + ϑ := by
          exact Nat.add_lt_add_left j.isLt (k.val * ϑ)
        exact lt_of_lt_of_le h_lt h_le⟩)]
  simp [iteratedFoldMatrixForm, pointFoldMatrixForm,
    logicalQueryFiberPoints_eq_fiberEvaluations 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      oStmt k v]

end LogicalOracleVerification

end FinalQueryRoundIOR

end QueryPhase

section QueryPhaseHelperLemmas

open QueryPhase

/-! ### Suffixes and fibers across blocks -/

/-- The suffix of `v` at `i` is the point of the fiber over its suffix at `i + steps` whose fiber
index is the middle bit mask of `v` between `i` and `i + steps`. -/
lemma iteratedQuotientMap_eq_quotientFiber_extractMiddleFinMask
    (i : Fin r) (steps : ℕ) {destIdx : Fin r}
    (h_destIdx : destIdx.val = i.val + steps)
    (h_destIdx_le : destIdx.val ≤ ℓ)
    (v : sDomain 𝔽q β h_ℓ_add_R_rate ⟨0, by omega⟩) :
    iteratedQuotientMap 𝔽q β h_ℓ_add_R_rate (i := ⟨0, by omega⟩) (k := i.val)
      (h_destIdx := by simp only [zero_add])
      (h_destIdx_le := by omega) v =
    quotientFiber 𝔽q β i steps h_destIdx h_destIdx_le
      (iteratedQuotientMap 𝔽q β h_ℓ_add_R_rate (i := ⟨0, by omega⟩) (k := destIdx.val)
        (h_destIdx := by simp only [zero_add])
        (h_destIdx_le := h_destIdx_le) v)
      (extractMiddleFinMask 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) v i steps) := by
  have h_R_pos : 0 < 𝓡 := NeZero.pos 𝓡
  have h_i_le : i.val ≤ ℓ := by omega
  have h_i : i.val < ℓ + 𝓡 := Nat.lt_of_le_of_lt h_i_le (Nat.lt_add_of_pos_right h_R_pos)
  have h_zero : (0 : Fin r).val < ℓ + 𝓡 := by
    change 0 < ℓ + 𝓡
    exact Nat.lt_of_lt_of_le (NeZero.pos ℓ) (Nat.le_add_right ℓ 𝓡)
  apply LinearEquiv.injective (sDomain_basis 𝔽q β h_ℓ_add_R_rate i h_i).repr
  ext j
  rw [getSDomainBasisCoeff_of_iteratedQuotientMap]
  set y : sDomain 𝔽q β h_ℓ_add_R_rate destIdx :=
    iteratedQuotientMap 𝔽q β h_ℓ_add_R_rate (i := ⟨0, by omega⟩) (k := destIdx.val)
      (h_destIdx := by simp only [zero_add]) (h_destIdx_le := h_destIdx_le) v
  have h_repr_fiber := quotientFiber_repr_coeff 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (i := i) (steps := steps) h_destIdx h_destIdx_le (y := y)
    (k := extractMiddleFinMask 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) v i steps) (j := j)
  simp only [y] at h_repr_fiber
  rw [h_repr_fiber]
  by_cases h_j : j.val < steps
  · unfold fiberCoeff
    rw [dite_eq_left h_j]
    set pointFinIdx :=
      sDomainToFin 𝔽q β h_ℓ_add_R_rate ⟨0, by omega⟩ h_zero v
    have h_j_shift : j.val + i.val < ℓ + 𝓡 := by
      omega
    have h_coeff_v := finToBinaryCoeffs_sDomainToFin 𝔽q β h_ℓ_add_R_rate
      ⟨0, by omega⟩ h_zero v
    simp only at h_coeff_v
    have h_coeff_vj := congrFun h_coeff_v ⟨j.val + i.val, h_j_shift⟩
    simp only [finToBinaryCoeffs] at h_coeff_vj
    rw [← h_coeff_vj]
    have h_middle_bit :
        Nat.getBit (k := j) (n := extractMiddleFinMask 𝔽q β
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) v i steps) =
          Nat.getBit (k := j.val + i.val) (n := pointFinIdx) := by
      dsimp [extractMiddleFinMask, pointFinIdx]
      rw [Nat.getBit_of_middleBits]
      simp only [h_j, ↓reduceIte]
      congr 1
    rw [← h_middle_bit]
    by_cases h_bit :
        Nat.getBit (k := j) (n := extractMiddleFinMask 𝔽q β
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) v i steps) = 0
    · simp [h_bit]
    · have h_bit_one :
          Nat.getBit (k := j) (n := extractMiddleFinMask 𝔽q β
            (h_ℓ_add_R_rate := h_ℓ_add_R_rate) v i steps) = 1 := by
        have h := Nat.getBit_eq_zero_or_one
          (k := j) (n := extractMiddleFinMask 𝔽q β
            (h_ℓ_add_R_rate := h_ℓ_add_R_rate) v i steps)
        simp only [h_bit, false_or] at h
        exact h
      simp [h_bit_one]
  · unfold fiberCoeff
    rw [dite_eq_right h_j]
    have h_res := getSDomainBasisCoeff_of_iteratedQuotientMap 𝔽q β h_ℓ_add_R_rate
      ⟨0, by omega⟩ (k := destIdx.val) (h_destIdx := by simp only [zero_add])
      (h_destIdx_le := h_destIdx_le) (x := v) (j := ⟨j.val - steps, by omega⟩)
    simp only at h_res
    have h_idx :
        (⟨j.val + i.val, by omega⟩ : Fin (ℓ + 𝓡)) =
          ⟨j.val - steps + destIdx.val, by omega⟩ := by
      apply Fin.eq_of_val_eq
      simp only
      rw [h_destIdx]
      omega
    rw [h_idx]
    exact h_res.symm

open Classical in
/-- The suffix of `v` at the source index `j·ϑ` of block `j` is the fiber point of block `j`
indexed by the middle bit mask of `v`. -/
lemma extractSuffixFromChallenge_eq_getFiberPoint_extractMiddleFinMask
    (j : Fin (ℓ / ϑ))
    (v : sDomain 𝔽q β h_ℓ_add_R_rate 0) :
    extractSuffixFromChallenge 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (v := v)
      (destIdx := ⟨j.val * ϑ, by
        exact lt_r_of_lt_ℓ (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          (h := k_mul_ϑ_lt_ℓ (k := j))⟩)
      (h_destIdx_le := Nat.le_of_lt (k_mul_ϑ_lt_ℓ (k := j))) =
      getFiberPoint 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) j v
        (extractMiddleFinMask 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (v := v)
          (i := ⟨j.val * ϑ, by
            exact lt_r_of_lt_ℓ (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
              (h := k_mul_ϑ_lt_ℓ (k := j))⟩)
          (steps := ϑ)) := by
  dsimp only [getFiberPoint, extractSuffixFromChallenge, getChallengeSuffix]
  exact
    iteratedQuotientMap_eq_quotientFiber_extractMiddleFinMask
      (𝔽q := 𝔽q) (β := β) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := ⟨j.val * ϑ, by
        exact lt_r_of_lt_ℓ (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          (h := k_mul_ϑ_lt_ℓ (k := j))⟩)
      (steps := ϑ)
      (destIdx := ⟨j.val * ϑ + ϑ, by
        exact lt_r_of_le_ℓ (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          (k_succ_mul_ϑ_le_ℓ_₂ (k := j))⟩)
      (h_destIdx := by rfl)
      (h_destIdx_le := k_succ_mul_ϑ_le_ℓ_₂ (k := j))
      (v := v)

omit [DecidableEq 𝔽q] hF₂ h_β₀_eq_1 [NeZero 𝓡]  in
/-- At the last statement index, the oracle after position `j` is oracle `j + 1`, read through
the cast between the two equal domains. -/
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
          apply congrArg (fun i => ↥(sDomain 𝔽q β h_ℓ_add_R_rate i))
          apply Fin.eq_of_val_eq
          simp only
          ring) y) := by
  funext y
  unfold getNextOracle
  simp only

/-- In an accepting repetition, the value carried into block `j > 0` (the fold of block `j - 1`)
equals the value of oracle `j` at the suffix of `v` at `j·ϑ`. -/
lemma logicalComputeFoldedValue_eq_of_logicalCheckSingleRepetition
    (stmtIn : FinalSumcheckStatementOut (L := L) (ℓ := ℓ))
    (oStmtIn : ∀ j, OracleStatement 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ) j)
    (v : sDomain 𝔽q β h_ℓ_add_R_rate 0)
    (h_accept : LogicalCheckSingleRepetition 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      oStmtIn v stmtIn stmtIn.finalConstant)
    (j : Fin (nBlocks (ℓ := ℓ) (ϑ := ϑ)))
    (h_pos : 0 < j.val) :
    let _j_idx : Fin (ℓ / ϑ) := ⟨j.val, by
      have h_lt := j.isLt
      simp only [nBlocks, toOutCodewordsCount_last] at h_lt
      exact h_lt⟩
    let j_prev_idx : Fin (ℓ / ϑ) := ⟨j.val - 1, by
      have h_lt := j.isLt
      simp only [nBlocks, toOutCodewordsCount_last] at h_lt
      omega⟩
    logicalComputeFoldedValue 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      j_prev_idx v stmtIn
      (logicalQueryFiberPoints 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        oStmtIn j_prev_idx v) =
    (oStmtIn j)
      (extractSuffixFromChallenge 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (v := v)
        (destIdx := ⟨j.val * ϑ, by
          exact
            lt_r_of_lt_ℓ (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
              (h := by
                have h_lt := j.isLt
                simp only [nBlocks, toOutCodewordsCount_last] at h_lt
                exact k_mul_ϑ_lt_ℓ (k := ⟨j.val, h_lt⟩))⟩)
        (h_destIdx_le := Nat.le_of_lt (by
          have h_lt := j.isLt
          simp only [nBlocks, toOutCodewordsCount_last] at h_lt
          exact k_mul_ϑ_lt_ℓ (k := ⟨j.val, h_lt⟩)))) := by
  let j_idx : Fin (ℓ / ϑ) := ⟨j.val, by
    have h_lt := j.isLt
    simp only [nBlocks, toOutCodewordsCount_last] at h_lt
    exact h_lt⟩
  let j_prev_idx : Fin (ℓ / ϑ) := ⟨j.val - 1, by
    have h_lt := j.isLt
    simp only [nBlocks, toOutCodewordsCount_last] at h_lt
    omega⟩
  have h_step := h_accept (⟨j.val, by
    have h_lt := j.isLt
    simp only [nBlocks, toOutCodewordsCount_last] at h_lt
    omega⟩ : Fin (ℓ / ϑ + 1))
  unfold LogicalStepCondition at h_step
  have h_lt_div :
      (⟨j.val, by
        have h_lt := j.isLt
        simp only [nBlocks, toOutCodewordsCount_last] at h_lt
        omega⟩ : Fin (ℓ / ϑ + 1)).val < ℓ / ϑ := by
    have h_lt := j.isLt
    simp only [nBlocks, toOutCodewordsCount_last] at h_lt
    exact h_lt
  rw [dite_eq_left h_lt_div] at h_step
  unfold LogicalCheckSingleFoldingStep at h_step
  have h_i_pos : j.val * ϑ > 0 := by
    exact Nat.mul_pos h_pos (Nat.pos_of_neZero ϑ)
  rw [dite_eq_left h_i_pos] at h_step
  dsimp only [j_idx, j_prev_idx, logicalQueryFiberPoints] at h_step
  change
    logicalComputeFoldedValue 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      j_prev_idx v stmtIn
      (logicalQueryFiberPoints 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        oStmtIn j_prev_idx v) =
    (oStmtIn j)
      (getFiberPoint 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) j_idx v
        (extractMiddleFinMask 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          (v := v)
          (i := ⟨j_idx.val * ϑ, by
            exact
              lt_r_of_lt_ℓ (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
                (h := k_mul_ϑ_lt_ℓ (k := j_idx))⟩)
          (steps := ϑ))) at h_step
  rw [← extractSuffixFromChallenge_eq_getFiberPoint_extractMiddleFinMask
    (𝔽q := 𝔽q) (β := β) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (j := j_idx) (v := v)] at h_step
  exact h_step

/-- Block `j`, as an index into the `ℓ / ϑ` blocks. -/
abbrev queryBlockIdx (j : Fin (nBlocks (ℓ := ℓ) (ϑ := ϑ))) : Fin (ℓ / ϑ) := ⟨j.val, by
  have h_lt := j.isLt
  simp only [nBlocks, toOutCodewordsCount_last] at h_lt
  exact h_lt⟩

/-- The source domain index `j·ϑ` of block `j`. -/
abbrev queryBlockSourceIdx (j : Fin (nBlocks (ℓ := ℓ) (ϑ := ϑ))) : Fin r := ⟨j.val * ϑ, by
  exact
    lt_r_of_lt_ℓ (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (h := k_mul_ϑ_lt_ℓ (k := queryBlockIdx (ℓ := ℓ) (ϑ := ϑ) j))⟩

/-- The destination domain index `j·ϑ + ϑ` of block `j`. -/
abbrev queryBlockDestIdx (j : Fin (nBlocks (ℓ := ℓ) (ϑ := ϑ))) : Fin r :=
  ⟨j.val * ϑ + ϑ, by
    exact
      lt_r_of_le_ℓ (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (oracle_index_add_steps_le_ℓ (ℓ := ℓ) (ϑ := ϑ)
          (i := Fin.last ℓ) (j := j))⟩

omit [NeZero r] [NeZero ℓ] [NeZero 𝓡] in
/-- The source index of a block is at most `ℓ`. -/
lemma queryBlockSourceIdx_le
    (j : Fin (nBlocks (ℓ := ℓ) (ϑ := ϑ))) :
    (queryBlockSourceIdx (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) j).val ≤ ℓ := by
  exact (Nat.le_add_right _ _).trans
    (oracle_index_add_steps_le_ℓ (ℓ := ℓ) (ϑ := ϑ)
      (i := Fin.last ℓ) (j := j))

omit [NeZero r] [NeZero ℓ] [NeZero 𝓡] [NeZero ϑ] in
/-- The destination index of a block is at most `ℓ`. -/
lemma queryBlockDestIdx_le
    (j : Fin (nBlocks (ℓ := ℓ) (ϑ := ϑ))) :
    (queryBlockDestIdx (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) j).val ≤ ℓ := by
  exact oracle_index_add_steps_le_ℓ (ℓ := ℓ) (ϑ := ϑ)
    (i := Fin.last ℓ) (j := j)

/-- The suffix of `v` at the source index of block `j`. -/
abbrev queryBlockSourceSuffix
    (j : Fin (nBlocks (ℓ := ℓ) (ϑ := ϑ)))
    (v : sDomain 𝔽q β h_ℓ_add_R_rate 0) :
    sDomain 𝔽q β h_ℓ_add_R_rate
      (queryBlockSourceIdx (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) j) :=
  extractSuffixFromChallenge 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (v := v)
    (destIdx := queryBlockSourceIdx (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) j)
    (h_destIdx_le := queryBlockSourceIdx_le
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) j)

/-- The suffix of `v` at the destination index of block `j`. -/
abbrev queryBlockDestSuffix
    (j : Fin (nBlocks (ℓ := ℓ) (ϑ := ϑ)))
    (v : sDomain 𝔽q β h_ℓ_add_R_rate 0) :
    sDomain 𝔽q β h_ℓ_add_R_rate
      (queryBlockDestIdx (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) j) :=
  extractSuffixFromChallenge 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (v := v)
    (destIdx := queryBlockDestIdx (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) j)
    (h_destIdx_le := queryBlockDestIdx_le
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) j)

omit [NeZero r] [NeZero ℓ] [NeZero 𝓡] in
/-- The destination index of block `j` is the source index of block `j + 1`. -/
lemma queryBlockDestIdx_eq_queryBlockSourceIdx_succ
    (j : Fin (nBlocks (ℓ := ℓ) (ϑ := ϑ)))
    (hj : j.val + 1 < nBlocks (ℓ := ℓ) (ϑ := ϑ)) :
    queryBlockDestIdx (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) j =
      queryBlockSourceIdx (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ)
        ⟨j.val + 1, hj⟩ := by
  apply Fin.eq_of_val_eq
  simp only
  ring

omit [DecidableEq 𝔽q] hF₂  [NeZero ℓ] [NeZero 𝓡] in
/-- The destination suffix of block `j` is the source suffix of block `j + 1`, up to the cast
between the two equal domains. -/
lemma queryBlockDestSuffix_eq_queryBlockSourceSuffix_succ
    (j : Fin (nBlocks (ℓ := ℓ) (ϑ := ϑ)))
    (hj : j.val + 1 < nBlocks (ℓ := ℓ) (ϑ := ϑ))
    (v : sDomain 𝔽q β h_ℓ_add_R_rate 0) :
    queryBlockDestSuffix (𝔽q := 𝔽q) (β := β)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) j v =
      cast (by
        rw [queryBlockDestIdx_eq_queryBlockSourceIdx_succ
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) (j := j) (hj := hj)])
        (queryBlockSourceSuffix (𝔽q := 𝔽q) (β := β)
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) ⟨j.val + 1, hj⟩ v) := by
  dsimp only [queryBlockDestSuffix, queryBlockSourceSuffix]
  exact
    extractSuffixFromChallenge_congr_destIdx
      (𝔽q := 𝔽q) (β := β) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (v := v)
      (destIdx := queryBlockDestIdx
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) j)
      (destIdx' := queryBlockSourceIdx
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) ⟨j.val + 1, hj⟩)
      (h_idx_eq := queryBlockDestIdx_eq_queryBlockSourceIdx_succ
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) (j := j) (hj := hj))
      (h_le := queryBlockDestIdx_le
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) j)
      (h_le' := queryBlockSourceIdx_le
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) ⟨j.val + 1, hj⟩)

omit [DecidableEq 𝔽q] in
/-- The `ϑ`-step iterated quotient map sends the source suffix of block `j` to its destination
suffix. -/
lemma iteratedQuotientMap_queryBlockSourceSuffix
    (j : Fin (nBlocks (ℓ := ℓ) (ϑ := ϑ)))
    (v : sDomain 𝔽q β h_ℓ_add_R_rate 0) :
    iteratedQuotientMap 𝔽q β h_ℓ_add_R_rate
      (i := queryBlockSourceIdx
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) j)
      (destIdx := queryBlockDestIdx
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) j)
      (k := ϑ) (h_destIdx := by rfl)
      (h_destIdx_le := queryBlockDestIdx_le
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) j)
      (x := queryBlockSourceSuffix (𝔽q := 𝔽q) (β := β)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) j v) =
    queryBlockDestSuffix (𝔽q := 𝔽q) (β := β)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) j v := by
  classical
  have h_source_suffix_eq :
      queryBlockSourceSuffix (𝔽q := 𝔽q) (β := β)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) j v =
      getFiberPoint 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (queryBlockIdx (ℓ := ℓ) (ϑ := ϑ) j) v
        (extractMiddleFinMask 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          (v := v)
          (i := queryBlockSourceIdx
            (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) j)
          (steps := ϑ)) := by
    exact
      extractSuffixFromChallenge_eq_getFiberPoint_extractMiddleFinMask
        (𝔽q := 𝔽q) (β := β) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (j := queryBlockIdx (ℓ := ℓ) (ϑ := ϑ) j) (v := v)
  rw [h_source_suffix_eq]
  have h_generates :
      getChallengeSuffix 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (k := queryBlockIdx (ℓ := ℓ) (ϑ := ϑ) j) (v := v) =
      iteratedQuotientMap 𝔽q β h_ℓ_add_R_rate
        (i := queryBlockSourceIdx
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) j)
        (destIdx := queryBlockDestIdx
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) j)
        (k := ϑ) (h_destIdx := by rfl)
        (h_destIdx_le := queryBlockDestIdx_le
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) j)
        (x := getFiberPoint 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          (queryBlockIdx (ℓ := ℓ) (ϑ := ϑ) j) v
          (extractMiddleFinMask 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
            (v := v)
            (i := queryBlockSourceIdx
              (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) j)
            (steps := ϑ))) := by
    apply eq_iteratedQuotientMap_of_mem_quotientFiber_range
      (𝔽q := 𝔽q) (β := β) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := queryBlockSourceIdx
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) j)
      (steps := ϑ)
      (h_destIdx := by rfl)
      (h_destIdx_le := queryBlockDestIdx_le
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) j)
      (x := getFiberPoint 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (queryBlockIdx (ℓ := ℓ) (ϑ := ϑ) j) v
        (extractMiddleFinMask 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          (v := v)
          (i := queryBlockSourceIdx
            (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) j)
          (steps := ϑ)))
      (y := getChallengeSuffix 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (k := queryBlockIdx (ℓ := ℓ) (ϑ := ϑ) j) (v := v))
    refine ⟨extractMiddleFinMask 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (v := v)
      (i := queryBlockSourceIdx
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) j)
      (steps := ϑ), ?_⟩
    exact getFiberPoint_eq_quotientFiber 𝔽q β _ v _
  exact h_generates.symm

omit [DecidableEq 𝔽q] h_β₀_eq_1 [NeZero ℓ]  in
/-- Decoded codewords at equal indices `i = j` of heterogeneously equal oracles agree pointwise,
up to the cast between the two domains. -/
lemma uniqueDecodingCodeword_eval_eq_of_fin_eq
    {i j : Fin r} (hij : i = j)
    {hi : i ≤ ℓ} {hj : j ≤ ℓ}
    {f : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i}
    {g : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) j}
    (hfg : HEq f g)
    (hf_close : UniqueDecodingClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i f)
    (y : sDomain 𝔽q β h_ℓ_add_R_rate j) :
    let hg_close :=
      uniqueDecodingClose_congr (𝔽q := 𝔽q) (β := β)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        hij hfg hf_close
    uniqueDecodingCodeword 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      i hi f hf_close
      (cast (by rw [hij]) y) =
    uniqueDecodingCodeword 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      j hj g hg_close y := by
  dsimp
  cases hij
  cases hfg
  rfl

omit [DecidableEq 𝔽q] in
/-- The decoded codeword of oracle `j + 1`, read at the destination index of block `j` through
the cast between the two equal domains, agrees with its decoded codeword at the source index of
block `j + 1`, at the source suffix of block `j + 1`. -/
lemma uniqueDecodingCodeword_queryBlockDestIdx_eq_queryBlockSourceIdx_succ
    (oStmtIn : ∀ j, OracleStatement 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ) j)
    (j : Fin (nBlocks (ℓ := ℓ) (ϑ := ϑ)))
    (hj : j.val + 1 < nBlocks (ℓ := ℓ) (ϑ := ϑ))
    (v : sDomain 𝔽q β h_ℓ_add_R_rate 0)
    (h_next_close_stmt :
      let j_next : Fin (nBlocks (ℓ := ℓ) (ϑ := ϑ)) := ⟨j.val + 1, hj⟩
      UniqueDecodingClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (queryBlockDestIdx
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) j)
        (fun y => (oStmtIn j_next) (cast (by
          rw [queryBlockDestIdx_eq_queryBlockSourceIdx_succ
            (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) (j := j) (hj := hj)]) y)))
    (h_next_close :
      let j_next : Fin (nBlocks (ℓ := ℓ) (ϑ := ϑ)) := ⟨j.val + 1, hj⟩
      UniqueDecodingClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (queryBlockSourceIdx
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) j_next)
        (oStmtIn j_next)) :
    let j_next : Fin (nBlocks (ℓ := ℓ) (ϑ := ϑ)) := ⟨j.val + 1, hj⟩
    uniqueDecodingCodeword 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (queryBlockDestIdx
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) j)
      (queryBlockDestIdx_le
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) j)
      (f := fun y => (oStmtIn j_next) (cast (by
        rw [queryBlockDestIdx_eq_queryBlockSourceIdx_succ
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) (j := j) (hj := hj)]) y))
      (h_within_radius := h_next_close_stmt)
      (cast (by
        rw [queryBlockDestIdx_eq_queryBlockSourceIdx_succ
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) (j := j) (hj := hj)])
        (queryBlockSourceSuffix (𝔽q := 𝔽q) (β := β)
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) j_next v)) =
    uniqueDecodingCodeword 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (queryBlockSourceIdx
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) j_next)
      (queryBlockSourceIdx_le
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) j_next)
      (f := oStmtIn j_next)
      (h_within_radius := h_next_close)
      (queryBlockSourceSuffix (𝔽q := 𝔽q) (β := β)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) j_next v) := by
  classical
  let j_next : Fin (nBlocks (ℓ := ℓ) (ϑ := ϑ)) := ⟨j.val + 1, hj⟩
  dsimp only [j_next] at h_next_close_stmt h_next_close ⊢
  have h_idx_eq :=
    queryBlockDestIdx_eq_queryBlockSourceIdx_succ
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) (j := j) (hj := hj)
  let f_next_cast :
      OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (queryBlockDestIdx
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) j) :=
    fun y => (oStmtIn j_next) (cast (by rw [h_idx_eq]) y)
  have h_dom :
      ↥(sDomain 𝔽q β h_ℓ_add_R_rate
        (queryBlockDestIdx
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) j)) =
      ↥(sDomain 𝔽q β h_ℓ_add_R_rate
        (queryBlockSourceIdx
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) j_next)) := by
    exact
      congrArg
        (fun i => ↥(sDomain 𝔽q β h_ℓ_add_R_rate i))
        h_idx_eq
  have h_next_heq :
      HEq f_next_cast (oStmtIn j_next) := by
    exact
      funext_heq h_dom (fun _ => rfl) (by
        intro y
        apply heq_of_eq
        rfl)
  have h_next_close_cast :
      UniqueDecodingClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (queryBlockDestIdx
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) j)
        f_next_cast := by
    change
      UniqueDecodingClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (queryBlockDestIdx
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) j)
        (fun y => (oStmtIn j_next) (cast (by rw [h_idx_eq]) y))
    exact h_next_close_stmt
  have h_next_close_transport :
      UniqueDecodingClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (queryBlockSourceIdx
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) j_next)
        (oStmtIn j_next) := by
    exact
      uniqueDecodingClose_congr (𝔽q := 𝔽q) (β := β)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        h_idx_eq h_next_heq h_next_close_cast
  have h_codeword_eq :
      uniqueDecodingCodeword 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (queryBlockSourceIdx
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) j_next)
        (queryBlockSourceIdx_le
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) j_next)
        (f := oStmtIn j_next)
        (h_within_radius := h_next_close_transport)
        (queryBlockSourceSuffix (𝔽q := 𝔽q) (β := β)
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) j_next v) =
      uniqueDecodingCodeword 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (queryBlockSourceIdx
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) j_next)
        (queryBlockSourceIdx_le
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) j_next)
        (f := oStmtIn j_next)
        (h_within_radius := h_next_close)
        (queryBlockSourceSuffix (𝔽q := 𝔽q) (β := β)
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) j_next v) := by
    rfl
  have h_codeword_transport :
      uniqueDecodingCodeword 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (queryBlockDestIdx
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) j)
        (queryBlockDestIdx_le
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) j)
        (f := f_next_cast)
        (h_within_radius := h_next_close_cast)
        (cast (by rw [h_idx_eq]) (queryBlockSourceSuffix (𝔽q := 𝔽q) (β := β)
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) j_next v)) =
      uniqueDecodingCodeword 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (queryBlockSourceIdx
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) j_next)
        (queryBlockSourceIdx_le
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) j_next)
        (f := oStmtIn j_next)
        (h_within_radius := h_next_close_transport)
        (queryBlockSourceSuffix (𝔽q := 𝔽q) (β := β)
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) j_next v) := by
    exact
      uniqueDecodingCodeword_eval_eq_of_fin_eq (𝔽q := 𝔽q) (β := β)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (i := queryBlockDestIdx
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) j)
        (j := queryBlockSourceIdx
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) j_next)
        h_idx_eq
        (hi := queryBlockDestIdx_le
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) j)
        (hj := queryBlockSourceIdx_le
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) j_next)
        h_next_heq h_next_close_cast
        (queryBlockSourceSuffix (𝔽q := 𝔽q) (β := β)
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) j_next v)
  exact h_codeword_transport.trans h_codeword_eq

end QueryPhaseHelperLemmas

end

end Binius.BinaryBasefold

import ArkLib.ProofSystem.Binius.BinaryBasefold.Spec
import ArkLib.ProofSystem.Binius.BinaryBasefold.Code
import ArkLib.Data.Misc.Basic
import ArkLib.Data.Probability.Instances
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.Nondegenerate

namespace Binius.BinaryBasefold

/-! **Soundness foundational Lemmas (Lemmas 4.20 - 4.25)**
- Probability reasoning: using lemmas in `DG25.lean`
- Foundational definitions and lemmas: `ArkLib.Data.FieldTheory.AdditiveNTT.AdditiveNTT.lean`
  and `ArkLib.ProofSystem.Binius.BinaryBasefold.Prelude`
- Raw proof specs: `ArkLib/ProofSystem/Binius/BinaryBasefold/SoundnessFoundationsSpec.md`
-/

set_option maxHeartbeats 400000  -- Increase if needed
set_option profiler true
set_option profiler.threshold 20  -- Show anything taking over 10ms

open OracleSpec OracleComp ProtocolSpec Finset AdditiveNTT Polynomial MvPolynomial
  Binius.BinaryBasefold Classical
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
variable [SelectableType L]
variable [hdiv : Fact (ϑ ∣ ℓ)]

section IndexBounds

omit [NeZero ℓ] in
@[simp]
lemma k_mul_ϑ_lt_ℓ {k : Fin (ℓ / ϑ)} :
  ↑k * ϑ < ℓ := by
  have h_mul_eq : (ℓ/ϑ) * ϑ = ℓ := Nat.div_mul_cancel hdiv.out
  calc ↑k * ϑ < (ℓ / ϑ) * ϑ := Nat.mul_lt_mul_of_pos_right k.isLt (NeZero.pos ϑ)
    _ = ℓ := h_mul_eq

omit [NeZero ℓ] [NeZero ϑ] in
@[simp]
lemma k_succ_mul_ϑ_le_ℓ {k : Fin (ℓ / ϑ)} : (k.val + 1) * ϑ ≤ ℓ := by
  have h_mul_eq : (ℓ/ϑ) * ϑ = ℓ := Nat.div_mul_cancel hdiv.out
  calc (k.val + 1) * ϑ ≤ (ℓ / ϑ) * ϑ := Nat.mul_le_mul_right (k := ϑ) (h := by omega)
    _ = ℓ := h_mul_eq

omit [NeZero ℓ] [NeZero ϑ] in
@[simp]
lemma k_succ_mul_ϑ_le_ℓ_₂ {k : Fin (ℓ / ϑ)} : (k.val * ϑ + ϑ) ≤ ℓ := by
  conv_lhs => enter [2]; rw [←Nat.one_mul ϑ]
  rw [←Nat.add_mul];
  exact k_succ_mul_ϑ_le_ℓ;

omit [NeZero r] [NeZero ℓ] [NeZero 𝓡] in
@[simp]
lemma lt_r_of_le_ℓ {h_ℓ_add_R_rate : ℓ + 𝓡 < r} {x : ℕ} (h : x ≤ ℓ)
  : x < r := by omega

omit [NeZero r] [NeZero ℓ] [NeZero 𝓡] in
@[simp]
lemma lt_r_of_lt_ℓ {h_ℓ_add_R_rate : ℓ + 𝓡 < r} {x : ℕ} (h : x < ℓ)
  : x < r := by omega

end IndexBounds

open scoped NNReal ProbabilityTheory

omit [CharP L 2] [SelectableType L] in
/-- **Probability bound for the bad sumcheck event** (Schwartz-Zippel).
When the verifier challenge `r_i'` is uniform over `L`, the probability that two distinct
degree-≤2 round polynomials agree at `r_i'` is at most `2 / |L|`. -/
lemma probability_bound_badSumcheckEventProp (h_i h_star : L⦃≤ 2⦄[X]) :
    Pr_{ let r_i' ← $ᵖ L }[ badSumcheckEventProp r_i' h_i h_star ] ≤
      (2 : ℝ≥0) / Fintype.card L := by
  unfold badSumcheckEventProp
  by_cases h_ne : h_i ≠ h_star
  · simp only [ne_eq, h_ne, not_false_eq_true, true_and, ENNReal.coe_ofNat]
    exact prob_poly_agreement_degree_two (p := h_i) (q := h_star) (h_ne := h_ne)
  · simp only [h_ne, false_and, ENNReal.coe_ofNat]
    -- lhs is `Pr_{ let r_i' ← $ᵖ ... }[ False ]`
    simp only [PMF.monad_pure_eq_pure, PMF.monad_bind_eq_bind, PMF.bind_const, PMF.pure_apply,
      eq_iff_iff, iff_false, not_true_eq_false, ↓reduceIte, _root_.zero_le]

namespace QueryPhase

/-!
## Common Proximity Check Helpers

These functions extract the shared logic between `queryOracleVerifier`
and `queryKnowledgeStateFunction` for proximity testing, allowing code reuse
and ensuring both implementations follow the same logic.
-/

/-- Extract suffix starting at position `destIdx` from a full challenge. -/
def extractSuffixFromChallenge (v : sDomain 𝔽q β h_ℓ_add_R_rate ⟨0, by omega⟩)
    (destIdx : Fin r) (h_destIdx_le : destIdx ≤ ℓ) :
    sDomain 𝔽q β h_ℓ_add_R_rate destIdx :=
  iteratedQuotientMap 𝔽q β h_ℓ_add_R_rate (i := ⟨0, by omega⟩) (k := destIdx.val)
    (h_destIdx := by simp only [zero_add]) (h_destIdx_le := h_destIdx_le) (x := v)

omit [CharP L 2] [SelectableType L] [DecidableEq 𝔽q] hF₂ [NeZero 𝓡] in
/-- **Congruence Lemma for Challenge Suffixes**:
Allows proving equality between two suffix extractions when the destination indices
are proven equal (`destIdx = destIdx'`), handling the necessary type casting. -/
lemma extractSuffixFromChallenge_congr_destIdx
    (v : sDomain 𝔽q β h_ℓ_add_R_rate ⟨0, by omega⟩)
    {destIdx destIdx' : Fin r}
    (h_idx_eq : destIdx = destIdx')
    (h_le : destIdx ≤ ℓ)
    (h_le' : destIdx' ≤ ℓ) :
    extractSuffixFromChallenge 𝔽q β v destIdx h_le =
    cast (by rw [h_idx_eq]) (extractSuffixFromChallenge 𝔽q β v destIdx' h_le') := by
  subst h_idx_eq; rfl

omit [CharP L 2] [SelectableType L] [DecidableEq 𝔽q] h_β₀_eq_1 in
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
    let P₀ : L[X]_(2 ^ ℓ) :=
      polynomialFromNovelCoeffsF₂ 𝔽q β ℓ (by omega) (fun ω => t.val.eval (bitsOfIndex ω))
    let f₀ := polyToOracleFunc 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (domainIdx := 0) (P := P₀)
    f₀ = getFirstOracle 𝔽q β oStmt := by
  intro P₀ f₀
  -- Use strictOracleFoldingConsistencyProp for j = 0
  have h_pos : 0 < toOutCodewordsCount ℓ ϑ i := by
    exact (instNeZeroNatToOutCodewordsCount ℓ ϑ i).pos
  have h_first_oracle := h_consistency ⟨0, by omega⟩
  dsimp only [strictOracleFoldingConsistencyProp] at h_first_oracle
  dsimp only [f₀, P₀, getFirstOracle] at h_first_oracle ⊢
  rw [h_first_oracle]
  funext y
  conv_rhs =>
    rw [iterated_fold_congr_steps_index 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (steps' := 0)
      (h_destIdx := by simp only [Nat.zero_mod, zero_mul, Fin.coe_ofNat_eq_mod, add_zero])
      (h_destIdx_le := by simp only [zero_mul, zero_le])
      (h_steps_eq_steps' := by simp only [zero_mul])]
    rw [iterated_fold_zero_steps 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := 0)
      (h_destIdx := by simp only [Nat.zero_mod, zero_mul, Fin.coe_ofNat_eq_mod])]
  conv_rhs => simp only [cast_cast, cast_eq]; simp only [←fun_eta_expansion]

/-- Decompose challenge v at position i into (fiberIndex, suffix).
    This is the inverse of `Nat.joinBits` in some sense.
    Uses loose indexing with `Fin r`. -/
def decomposeChallenge (v : sDomain 𝔽q β h_ℓ_add_R_rate ⟨0, by omega⟩)
    (i : Fin r) {destIdx : Fin r} (steps : ℕ)
    (h_destIdx_le : destIdx ≤ ℓ) :
    Fin (2^steps) × sDomain 𝔽q β h_ℓ_add_R_rate destIdx :=
  (extractMiddleFinMask 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (v:=v) (i:=i) (steps:=steps),
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
    (point : (sDomain 𝔽q β h_ℓ_add_R_rate) ⟨oraclePositionToDomainIndex ℓ ϑ j, by omega⟩) :
  OracleComp ([OracleStatement 𝔽q β (ϑ:=ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (
  Fin.last ℓ)]ₒ) L :=
    OracleSpec.query
      (spec := [OracleStatement 𝔽q β (ϑ:=ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ)]ₒ)
      ⟨j, by omega⟩ point

section FinalQueryRoundIOR

/-!
### IOR Implementation for the Final Query Round
-/
def getChallengeSuffix (k : Fin (ℓ / ϑ)) (v : sDomain 𝔽q β h_ℓ_add_R_rate ⟨0, by omega⟩) :
    let i := k.val * ϑ
    have h_i_add_ϑ_le_ℓ : i + ϑ ≤ ℓ := k_succ_mul_ϑ_le_ℓ_₂ (k := k)
    let destIdx : Fin r := ⟨i + ϑ, by omega⟩
    sDomain 𝔽q β h_ℓ_add_R_rate destIdx :=
  have h_i_add_ϑ_le_ℓ := k_succ_mul_ϑ_le_ℓ_₂ (k := k)
  extractSuffixFromChallenge 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (v:=v) (destIdx := ⟨k.val * ϑ + ϑ, by omega⟩) (h_destIdx_le:=by omega)

def challengeSuffixToFin (k : Fin (ℓ / ϑ))
  (suffix : sDomain 𝔽q β h_ℓ_add_R_rate ⟨k.val * ϑ + ϑ, by
    have := k_succ_mul_ϑ_le_ℓ_₂ (k := k); omega⟩) : Fin (2 ^ (ℓ + 𝓡 - (k.val * ϑ + ϑ))) :=
  let i := k.val * ϑ
  have h_i_add_ϑ_le_ℓ : i + ϑ ≤ ℓ := k_succ_mul_ϑ_le_ℓ_₂ (k := k)
  let destIdx : Fin r := ⟨i + ϑ, by omega⟩
  sDomainToFin 𝔽q β h_ℓ_add_R_rate (i := ⟨k.val * ϑ + ϑ, by omega⟩) (h_i := by
    simp only [k_succ_mul_ϑ_le_ℓ_₂, Nat.lt_add_of_pos_right_of_le]) suffix

/-- Return the point `f^(i)(u_0, ..., u_{ϑ-1}, v_{i+ϑ}, ..., v_{ℓ+R-1})`
for a fiber index `u ∈ B_ϑ`. -/
noncomputable def getFiberPoint
    (k : Fin (ℓ / ϑ)) (v : sDomain 𝔽q β h_ℓ_add_R_rate ⟨0, by omega⟩) (u : Fin (2 ^ ϑ)) :
    (sDomain 𝔽q β h_ℓ_add_R_rate) (i := ⟨oraclePositionToDomainIndex ℓ ϑ (i := Fin.last ℓ)
      (positionIdx := ⟨k, by simp only [toOutCodewordsCount_last, Fin.is_lt]⟩),
        lt_r_of_lt_ℓ (x := k.val * ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (h := k_mul_ϑ_lt_ℓ)⟩) :=
  let i := k.val * ϑ
  have h_i_add_ϑ_le_ℓ : i + ϑ ≤ ℓ := k_succ_mul_ϑ_le_ℓ_₂ (k := k)

  -- TODO: should we make next_suffix_of_v_fin a separate def?
  let destIdx : Fin r := ⟨i + ϑ, by omega⟩

  let next_suffix_of_v_fin : Fin (2 ^ (ℓ + 𝓡 - (i + ϑ))) :=
    challengeSuffixToFin (k := k) (suffix := getChallengeSuffix (k := k) (v := v))

  let fiber_point_num_repr := Nat.joinBits (low := u) (high := next_suffix_of_v_fin)
  have h : 2 ^ (ℓ + 𝓡 - (i + ϑ) + ϑ) = 2 ^ (ℓ + 𝓡 - i) := by
    simp only [Nat.ofNat_pos, ne_eq, OfNat.ofNat_ne_one, not_false_eq_true, pow_right_inj₀]
    omega
  let x : Fin (2 ^ (ℓ + 𝓡 - i)) := ⟨fiber_point_num_repr.val, by omega⟩
  let k_th_oracleIdx : Fin (toOutCodewordsCount ℓ ϑ (Fin.last ℓ)) :=
    ⟨k, by simp only [toOutCodewordsCount, Fin.val_last, lt_self_iff_false, ↓reduceIte, add_zero,
      Fin.is_lt]⟩
  finToSDomain 𝔽q β h_ℓ_add_R_rate (i:=⟨i, by omega⟩)
    (h_i:=by apply Nat.lt_add_of_pos_right_of_le; simp only; omega) (idx:=x)

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
    (v : sDomain 𝔽q β h_ℓ_add_R_rate ⟨0, by omega⟩) :
    OracleComp ([OracleStatement 𝔽q β (ϑ:=ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ)]ₒ)
      (Vector L (2^ϑ)) := do

  let k_th_oracleIdx : Fin (toOutCodewordsCount ℓ ϑ (Fin.last ℓ)) :=
    ⟨k, by simp only [toOutCodewordsCount, Fin.val_last, lt_self_iff_false, ↓reduceIte, add_zero,
      Fin.is_lt]⟩

  -- 2. Map over the Vector monadically
  let results : Vector L (2^ϑ) ← (⟨Array.finRange (2^ϑ), by simp only [Array.size_finRange]⟩
    : Vector (Fin (2^ϑ)) (2^ϑ)).mapM (fun (u : Fin (2^ϑ)) => do
    queryCodeword 𝔽q β (ϑ:=ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (j := k_th_oracleIdx) (point :=
        getFiberPoint 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (k := k) (v := v) (u := u))
  )

  pure results

/-- Check a single folding step: query fiber points, verify consistency, and compute next value.
    Returns `(c_next, all_checks_passed)` where `c_next` is the computed folded value
    and `all_checks_passed` indicates if all consistency checks passed.
    Note: `oStmtIn` is accessed via oracle queries in the OracleComp context. -/
noncomputable def checkSingleFoldingStep
    (k_val : Fin (ℓ / ϑ)) (c_cur : L) (v : sDomain 𝔽q β h_ℓ_add_R_rate ⟨0, by omega⟩)
    (stmt : FinalSumcheckStatementOut (L := L) (ℓ := ℓ)) :
    OracleComp ([OracleStatement 𝔽q β (ϑ:=ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (Fin.last ℓ)]ₒ) (L) := do
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

  let f_i_on_fiber ← queryFiberPoints 𝔽q β (ϑ:=ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) k_val v

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

  -- c_next = folded value at step k (logical counterpart: `logical_computeFoldedValue`)
  let c_next : L := single_point_localized_fold_matrix_form 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (i:=⟨i, by omega⟩) (steps:=ϑ) (destIdx:=destIdx) (h_destIdx:=by dsimp only [destIdx])
    (h_destIdx_le:=by omega) (r_challenges:=cur_challenge_batch) (y:=next_suffix_of_v)
    (fiber_eval_mapping := f_i_on_fiber.get)

  return c_next

/-- Check a single repetition: iterate through all folding steps and verify final consistency.
    Returns `true` if all checks pass, `false` otherwise.
    Note: `oStmtIn` is accessed via oracle queries in the OracleComp context.

    Uses `mut` + `for` loop for true early termination (stops immediately on first failure).
    For proofs, we'll need to reason about the loop invariant that `c_cur` maintains the
    correct accumulated value through iterations. -/
noncomputable def checkSingleRepetition
    (v : sDomain 𝔽q β h_ℓ_add_R_rate ⟨0, by omega⟩)
    (stmt : FinalSumcheckStatementOut (L := L) (ℓ := ℓ)) (final_constant : L) :
    OracleComp ([OracleStatement 𝔽q β (ϑ:=ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ)]ₒ) Unit := do
  let mut c_cur : L := 0 -- Will be initialized in first iteration

  -- Iterate through the `ℓ/ϑ` adjacent pairs of oracles & validate local folding consistency
  -- Early termination: stops immediately on first failure via `return false`
  for k_val in List.finRange (ℓ / ϑ) do
    let c_next ← checkSingleFoldingStep 𝔽q β (ϑ:=ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨k_val, by omega⟩ c_cur v stmt
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
    (k : Fin (ℓ / ϑ)) (v : sDomain 𝔽q β h_ℓ_add_R_rate ⟨0, by omega⟩) : Fin (2 ^ ϑ) → L :=
  let k_th_oracleIdx : Fin (toOutCodewordsCount ℓ ϑ (Fin.last ℓ)) :=
    ⟨k.val, by simp only [toOutCodewordsCount, Fin.val_last, lt_self_iff_false, ↓reduceIte,
      add_zero, Fin.is_lt]⟩
  fun u => oStmt k_th_oracleIdx (getFiberPoint 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) k v u)

/-- Compute folded value at step `k` (same as `c_next` in monadic `checkSingleFoldingStep`).
This takes `f_i_on_fiber` - the list of `2^ϑ` fiber evaluations on oracle domain
`k*ϑ`, folds them into a single oracle evaluation on oracle domain `(k+1)*ϑ`, i.e. `c_{i+ϑ}`. -/
def logical_computeFoldedValue
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
    (k : Fin (ℓ / ϑ)) (v : sDomain 𝔽q β h_ℓ_add_R_rate ⟨0, by omega⟩)
    (stmt : FinalSumcheckStatementOut (L := L) (ℓ := ℓ)) : Prop :=
  -- Index k represents
  let i := k.val * ϑ
  -- `k ∈ {0, 1, ..., ℓ/ϑ-1}`, `i ∈ {0, ϑ, 2ϑ, ..., ℓ-ϑ}`
  -- **NOTE**: this definition is the
    -- `c_i ?= f^(i)(v_i, ..., v_{ℓ+R-1})` check at inner repetition `k`
  have h_i_add_ϑ_le_ℓ : i + ϑ ≤ ℓ := k_succ_mul_ϑ_le_ℓ_₂ (k := k)
  let f_i_on_fiber := logical_queryFiberPoints 𝔽q β oStmt k v
  -- Actually we only need value of one point of `f_i_on_fiber` for this check
  -- This matches monadic: `guard (c_cur = f_i_val)`
  if h_i_pos : i > 0 then
    -- h_i_pos implies k > 0 (since i = k * ϑ and ϑ > 0)
    have h_k_pos : k.val > 0 := Nat.pos_of_mul_pos_right h_i_pos
    let k_prev : Fin (ℓ / ϑ) := ⟨k.val - 1, by omega⟩
    -- c_cur = fold value from step k-1
    let f_prev_on_fiber := logical_queryFiberPoints 𝔽q β oStmt k_prev v
    -- In logical specification, we look backwards at oracle domain `(k-1)*ϑ` to query
    -- the fiber evaluations `f_prev_on_fiber`, fold them to create `c_cur`.
    -- In the monadic `checkSingleFoldingStep`, `c_cur` is automatically available.
    let c_cur := logical_computeFoldedValue 𝔽q β k_prev v stmt f_prev_on_fiber
    -- f_i_val = oracle value at overlap point
    let oracle_point_idx := extractMiddleFinMask 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (v := v) (i := ⟨i, by omega⟩) (steps := ϑ)
    let f_i_val := f_i_on_fiber oracle_point_idx
    c_cur = f_i_val
  else True

/-- Logical check specific to step k.
    If k is an intermediate index, it is the consistency of the folding step.
    If k is the terminal index, it is the constant check. -/
def logical_stepCondition (oStmt : ∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ) j)
    (k : Fin (ℓ / ϑ + 1)) (v : sDomain 𝔽q β h_ℓ_add_R_rate ⟨0, by omega⟩)
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
    (v : sDomain 𝔽q β h_ℓ_add_R_rate ⟨0, by omega⟩)
    (stmt : FinalSumcheckStatementOut (L := L) (ℓ := ℓ)) (final_constant : L) : Prop :=
  ∀ k : Fin (ℓ / ϑ + 1),
    logical_stepCondition 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (oStmt := oStmt) (k := k) (v := v) (stmt := stmt) (final_constant := final_constant)

/-- Proximity checks spec: for all γ repetitions, `logical_checkSingleRepetition` holds. -/
def logical_proximityChecksSpec
    (γ_challenges : Fin γ_repetitions → sDomain 𝔽q β h_ℓ_add_R_rate ⟨0, by omega⟩)
    (oStmt : ∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ) j)
    (stmt : FinalSumcheckStatementOut (L := L) (ℓ := ℓ)) (final_constant : L) : Prop :=
  ∀ rep : Fin γ_repetitions,
    logical_checkSingleRepetition 𝔽q β oStmt (γ_challenges rep) stmt final_constant

end LogicalOracleVerification

end FinalQueryRoundIOR

end QueryPhase


omit [Fintype L] [DecidableEq L] [CharP L 2] in
lemma multilinearWeight_bitsOfIndex_eq_indicator {n : ℕ} (j k : Fin (2 ^ n)) :
  multilinearWeight (F := L) (r := bitsOfIndex k) (i := j) = if j = k then 1 else 0 := by
  set r_k := bitsOfIndex (L := L) k with h_r_k
  unfold multilinearWeight
  -- NOTE: maybe we can generalize this into a lemma?
  -- ⊢ (∏ j_1, if (↑j).testBit ↑j_1 = true then r_k j_1 else 1 - r_k j_1) = if j = k then 1 else 0
  dsimp only [bitsOfIndex, r_k]
  simp_rw [Nat.testBit_eq_getBit]
  by_cases h_eq : j = k
  · simp only [h_eq, ↓reduceIte]
    have h_eq: ∀ (x : Fin n),
      ((if (x.val).getBit ↑k = 1 then if (x.val).getBit ↑k = 1 then (1 : L) else (0 : L) else 1 - if (x.val).getBit ↑k = 1 then (1 : L) else (0 : L))) = (1 : L) := by
        intro x
        by_cases h_eq : (x.val).getBit ↑k = 1
        · simp only [h_eq, ↓reduceIte]
        · simp only [h_eq, ↓reduceIte, sub_zero]
    simp_rw [h_eq]
    simp only [prod_const_one]
  · simp only [h_eq, ↓reduceIte]
    -- ⊢ (∏ x, if (↑x).getBit ↑j = 1 then if (↑x).getBit ↑k = 1 then 1 else 0 else 1 - if (↑x).getBit ↑k = 1 then 1 else 0) = 0
    rw [Finset.prod_eq_zero_iff]
    --         ⊢ ∃ a ∈ univ,
    -- (if (↑a).getBit ↑j = 1 then if (↑a).getBit ↑k = 1 then 1 else 0 else 1 - if (↑a).getBit ↑k = 1 then 1 else 0) = 0
    let exists_bit_diff_idx := Nat.exist_bit_diff_if_diff (a := j) (b := k) (h_a_ne_b := h_eq)
    rcases exists_bit_diff_idx with ⟨bit_diff_idx, h_bit_diff_idx⟩
    have h_getBit_of_j_lt_2 : Nat.getBit (k := bit_diff_idx.val) (n := j) < 2 := by
      exact Nat.getBit_lt_2 (k := bit_diff_idx.val) (n := j)
    have h_getBit_of_k_lt_2 : Nat.getBit (k := bit_diff_idx.val) (n := k) < 2 := by
      exact Nat.getBit_lt_2 (k := bit_diff_idx.val) (n := k)
    use bit_diff_idx
    constructor
    · simp only [mem_univ]
    · by_cases h_bit_diff_of_j_eq_0 : Nat.getBit (k := bit_diff_idx.val) (n := j) = 0
      · simp only [h_bit_diff_of_j_eq_0, zero_ne_one, ↓reduceIte]
        -- ⊢ (1 - if (↑bit_diff_idx).getBit ↑k = 1 then 1 else 0) = 0
        have h_bit_diff_of_k_eq_1 : Nat.getBit (k := bit_diff_idx.val) (n := k) = 1 := by
          omega
        simp only [h_bit_diff_of_k_eq_1, ↓reduceIte, sub_self]
      · have h_bit_diff_of_j_eq_1 :
          Nat.getBit (k := bit_diff_idx.val) (n := j) = 1 := by
          omega
        have h_bit_diff_of_k_eq_0 : Nat.getBit (k := bit_diff_idx.val) (n := k) = 0 := by
          omega
        simp only [h_bit_diff_of_j_eq_1, ↓reduceIte, h_bit_diff_of_k_eq_0, zero_ne_one]

omit [Fintype L] [DecidableEq L] [CharP L 2] in
/-- **Key Property of Tensor Expansion with Binary Challenges**:
When `r = bitsOfIndex k`, the tensor expansion `challengeTensorExpansion n r`
is the indicator vector for index `k` (i.e., 1 at position `k`, 0 elsewhere).
This is a fundamental property used in both Proposition 4.20 and Lemma 4.21. -/
lemma challengeTensorExpansion_bitsOfIndex_is_eq_indicator {n : ℕ} (k : Fin (2 ^ n)) :
    -- Key Property: Tensor(r_k) is the indicator vector for k.
    -- Tensor(r_k)[j] = 1 if j=k, 0 if j≠k.
    challengeTensorExpansion n (r := bitsOfIndex (L := L) k) = fun j => if j = k then 1 else 0 := by
  -- Let r_k be the bit-vector corresponding to index k
  funext j
  unfold challengeTensorExpansion
  -- ⊢ multilinearWeight r_k j = if j = k then 1 else 0
  apply multilinearWeight_bitsOfIndex_eq_indicator

section Lift_PreTensorCombine

/-! **Interleaved Word Construction (Supporting definition for Lemma 4.21)**
Constructs the rows `f_j^{(i+steps)}` of the interleaved word.
For a fixed row index `j` and a domain point `y ∈ S^{i+steps}`,
the value is the `j`-th entry of the vector `M_y * fiber_vals`.
-- NOTE: the way we define `ι` as `sDomain 𝔽q β h_ℓ_add_R_rate ⟨i + steps, by omega⟩` instead of
`Fin` requires using the generic versions of code/proximity gap lemmas.
We don't have a unified mat-mul formula for this, because the `M_y` matrix varies over `y` -/
def preTensorCombine_WordStack (i : Fin ℓ) (steps : ℕ) {destIdx : Fin r}
    (h_destIdx : destIdx.val = i.val + steps) (h_destIdx_le : destIdx ≤ ℓ)
    (f_i : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩) :
    WordStack (A := L) (κ := Fin (2 ^ steps))
      (ι := sDomain 𝔽q β h_ℓ_add_R_rate destIdx) := fun j y =>
    -- 1. Calculate the folding matrix M_y
    let M_y : Matrix (Fin (2 ^ steps)) (Fin (2 ^ steps)) L :=
      foldMatrix 𝔽q β (i := ⟨i, by omega⟩) (steps := steps)
        (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le) (y := y)
    -- 2. Get the evaluation of f on the fiber of y
    let fiber_vals : Fin (2 ^ steps) → L :=
      fiberEvaluations 𝔽q β (i := ⟨i, by omega⟩) (steps := steps)
        (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le) (f := f_i) (y := y)
    -- 3. The result is the j-th component of the matrix-vector product
    (M_y *ᵥ fiber_vals) j

omit [CharP L 2] [DecidableEq 𝔽q] hF₂ h_β₀_eq_1 [NeZero ℓ] in
/-- **Folding with Binary Challenges selects a Matrix Row**
This lemma establishes the geometric link:
The `j`-th row of the `preTensorCombine` matrix product is exactly equal to
folding the function `f` using the bits of `j` as challenges.
This holds for ANY function `f`, not just codewords.
-/
lemma preTensorCombine_row_eq_fold_with_binary_row_challenges
    (i : Fin ℓ) (steps : ℕ) {destIdx : Fin r}
    (h_destIdx : destIdx.val = i.val + steps) (h_destIdx_le : destIdx ≤ ℓ)
    (f : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩)
    (rowIdx : Fin (2 ^ steps)) :
    ∀ y : sDomain 𝔽q β h_ℓ_add_R_rate destIdx,
      (preTensorCombine_WordStack 𝔽q β i steps h_destIdx h_destIdx_le f) rowIdx y =
      iterated_fold 𝔽q β ⟨i, by omega⟩ steps
        (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le) (f := f)
          (r_challenges := bitsOfIndex (L := L) (n := steps) rowIdx) (y := y) := by
  intro y
  -- 1. Expand the definition of preTensorCombine (The LHS)
  -- LHS = (M_y * f_vals)[rowIdx]
  dsimp [preTensorCombine_WordStack]
  -- 2. Expand the matrix form of iterated_fold (The RHS)
  -- RHS = Tensor(r) • (M_y * f_vals)
  rw [iterated_fold_eq_matrix_form 𝔽q β (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le)]
  unfold localized_fold_matrix_form single_point_localized_fold_matrix_form
  -- 3. Use the Tensor Property
  -- Tensor(bits(rowIdx)) is the indicator vector for rowIdx
  let tensor := challengeTensorExpansion (L := L) steps (bitsOfIndex rowIdx)
  have h_indicator : tensor = fun k => if k = rowIdx then 1 else 0 :=
    challengeTensorExpansion_bitsOfIndex_is_eq_indicator (L := L) rowIdx
  simp only
  -- 4. Simplify the Dot Product
  -- (Indicator • Vector) is exactly Vector[rowIdx]
  dsimp only [tensor] at h_indicator
  rw [h_indicator]
  rw [dotProduct]
  simp only [boole_mul]
  rw [Finset.sum_eq_single rowIdx]
  · -- The term at rowIdx is (1 * val)
    simp only [if_true]
  · -- All other terms are 0
    intro b _ hb_ne
    simp [hb_ne]
  · -- rowIdx is in the domain
    intro h_notin
    exact (h_notin (Finset.mem_univ rowIdx)).elim

omit [CharP L 2] in
lemma preTensorCombine_is_interleavedCodeword_of_codeword (i : Fin ℓ) (steps : ℕ) {destIdx : Fin r}
    (h_destIdx : destIdx.val = i.val + steps) (h_destIdx_le : destIdx ≤ ℓ)
    (f : BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩) :
    (⋈|(preTensorCombine_WordStack 𝔽q β i steps h_destIdx h_destIdx_le f)) ∈
      (BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) destIdx ^⋈ (Fin (2 ^ steps))) := by
  -- 1. Interleaved Code Definition: "A word is in the interleaved code iff every row is in the base code"
  set S_next := sDomain 𝔽q β h_ℓ_add_R_rate destIdx with h_S_next
  set u := (⋈|(preTensorCombine_WordStack 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i steps h_destIdx h_destIdx_le f)) with h_u
  set C_next := BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := destIdx)
  simp only [InterleavedWord, InterleavedSymbol, ModuleCode,
    instCodeInterleavableModuleCodeInterleavedSymbol, ModuleCode.moduleInterleavedCode,
    interleavedCodeSet, SetLike.mem_coe, Submodule.mem_mk, AddSubmonoid.mem_mk,
    AddSubsemigroup.mem_mk, Set.mem_setOf_eq]
  -- ⊢ ∀ (k : Fin (2 ^ steps)), uᵀ k ∈ C_next
  intro rowIdx
  -- 2. Setup: Define the specific challenge 'r' corresponding to row index 'rowIdx'
  let r_binary : Fin steps → L := bitsOfIndex rowIdx
  -- 3. Geometric Equivalence:
  -- Show that the `rowIdx`-th row of preTensorCombine is exactly `iterated_fold` of u with challenge r
  -- We rely on Lemma 4.9 (Matrix Form) which states: M_y * vals = iterated_fold(u, r, y)
  let preTensorCombine_Row: S_next → L := preTensorCombine_WordStack 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i steps
    h_destIdx h_destIdx_le (f_i := f) rowIdx
  let rowIdx_binary_folded_Row: S_next → L := iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩ steps (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le) (f := f) (r_challenges := r_binary)
  have h_row_eq_fold : preTensorCombine_Row = rowIdx_binary_folded_Row := by
    funext y
    exact preTensorCombine_row_eq_fold_with_binary_row_challenges 𝔽q β i
      steps h_destIdx h_destIdx_le f rowIdx y
  have h_row_of_u_eq: (uᵀ rowIdx) = preTensorCombine_Row := by rfl
  rw [←h_row_of_u_eq] at h_row_eq_fold
  rw [h_row_eq_fold]
  -- ⊢ rowIdx_binary_folded_Row ∈ C_next (i.e. lhs is of `fold(f, binary_rowIdx_challenges)` form)
  unfold rowIdx_binary_folded_Row
  exact iterated_fold_preserves_BBF_Code_membership 𝔽q β (i := ⟨i, by omega⟩) (steps := steps) (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le) (f := f) (r_challenges := r_binary)

/-!
--------------------------------------------------------------------------------
   SECTION: THE LIFT INFRASTRUCTURE
   Constructing the inverse map from Interleaved Codewords back to Domain CodeWords
--------------------------------------------------------------------------------
-/


open Code.InterleavedCode in
def getRowPoly (i : Fin ℓ) (steps : ℕ) {destIdx : Fin r}
    (h_destIdx : destIdx.val = i.val + steps) (h_destIdx_le : destIdx ≤ ℓ)
    (V_codeword : ((BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) destIdx)
      ^⋈(Fin (2 ^ steps)))) : Fin (2 ^ steps) → L⦃<2^(ℓ-destIdx.val)⦄[X] := fun j => by
  -- 1. Extract polynomials P_j from V_codeword components
  set S_next := sDomain 𝔽q β h_ℓ_add_R_rate destIdx with h_S_next
  set C_next := BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) destIdx with h_C_next
  let curRow := getRow (show InterleavedCodeword (A := L) (κ := Fin (2 ^ steps)) (ι := S_next) (C := C_next) from V_codeword) j
  have h_V_in_C_next : curRow.val ∈ (C_next) := by
    have h_V_mem := V_codeword.property
    let res := Code.InterleavedCode.getRowOfInterleavedCodeword_mem_code (C := (C_next : Set (S_next → L)))
      (κ := Fin (2 ^ steps)) (ι := S_next) (u := V_codeword) (rowIdx := j)
    exact res
  -- For each j, there exists a polynomial P_j of degree < 2^(ℓ - (i+steps))
  exact getBBF_Codeword_poly 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := destIdx) curRow

def getLiftCoeffs (i : Fin ℓ) (steps : ℕ) {destIdx : Fin r}
    (h_destIdx : destIdx.val = i.val + steps) (h_destIdx_le : destIdx ≤ ℓ)
    (V_codeword : ((BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) destIdx)
      ^⋈(Fin (2 ^ steps)))) : Fin (2^(ℓ - i)) → L := fun coeff_idx =>
    -- intertwining novel coeffs of the rows of V_codeword
    -- decompose `coeff_idx = colIdx * 2 ^ steps + rowIdx` as in paper,
      -- i.e. traverse column by column
    let colIdx : Fin (2 ^ (ℓ - destIdx.val)) := ⟨coeff_idx.val / (2 ^ steps), by
      apply Nat.div_lt_of_lt_mul;
      rw [← Nat.pow_add];
      convert coeff_idx.isLt using 2; omega
    ⟩
    let rowIdx : Fin (2 ^ steps) := ⟨coeff_idx.val % (2 ^ steps), by
      have h_coeff_idx_lt_two_pow_ℓ_i : coeff_idx.val < 2 ^ (ℓ - i) := by
        exact coeff_idx.isLt
      have h_coeff_idx_mod_two_pow_steps : coeff_idx.val % (2 ^ steps) < 2 ^ steps := by
        apply Nat.mod_lt; simp only [gt_iff_lt, ofNat_pos, pow_pos]
      exact h_coeff_idx_mod_two_pow_steps
    ⟩
    let coeff := getINovelCoeffs 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := destIdx) (h_i := h_destIdx_le) (P := (getRowPoly 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        i steps h_destIdx h_destIdx_le V_codeword) rowIdx) colIdx
    coeff

/-- Given an interleaved codeword `V ∈ C ⋈^ (2^steps)`, this method converts `2^steps` row polys
of `V` into a poly `P ∈ L[X]_(2^(ℓ-i))` that generates the fiber evaluator `g : S⁽ⁱ⁾ → L`
(this `g` produces the RHS vector in equality of **Lemma 4.9**). If we fold this function `g` using
**binary challenges** corresponding to each of the `2^steps` rows of `V`, let's say `j`,
we also folds `P` into the corresponding row polynomial `P_j` of the `j`-th row of `V`
(via **Lemma 4.13, aka iterated_fold_advances_evaluation_poly**). This works as a core engine for
proof of **Lemma 4.21**. -/
def getLiftPoly (i : Fin ℓ) (steps : ℕ) {destIdx : Fin r}
    (h_destIdx : destIdx.val = i.val + steps) (h_destIdx_le : destIdx ≤ ℓ)
    (V_codeword : ((BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) destIdx)
      ^⋈(Fin (2 ^ steps)))) : L⦃<2^(ℓ-i)⦄[X] := by
  have h_ℓ_lt_r : ℓ < r := by
    have h_pos : 0 < 𝓡 := Nat.pos_of_neZero (n := 𝓡)
    exact lt_trans (Nat.lt_add_of_pos_right (n := ℓ) (k := 𝓡) h_pos) h_ℓ_add_R_rate
  have h_i_lt_r : (i : Nat) < r := lt_trans i.isLt h_ℓ_lt_r
  let iR : Fin r := ⟨i, h_i_lt_r⟩
  refine ⟨intermediateEvaluationPoly 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := iR) (h_i := by
        exact Nat.le_of_lt i.isLt)
      (coeffs := getLiftCoeffs 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        i steps h_destIdx h_destIdx_le V_codeword), ?_⟩
  apply Polynomial.mem_degreeLT.mpr
  exact degree_intermediateEvaluationPoly_lt (𝔽q := 𝔽q) (β := β)
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := iR) (h_i := by
      exact Nat.le_of_lt i.isLt)
    (coeffs := getLiftCoeffs 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      i steps h_destIdx h_destIdx_le V_codeword)

/-- **Lift Function (Inverse Folding)**
Constructs a function `f` on the domain `S^{(i)}` from an interleaved word `W` on `S^{(i+steps)}`.
For any point `x` in the larger domain, we identify its quotient `y` and its index in the fiber.
We recover the fiber values by applying `M_y⁻¹` to the column `W(y)`.
-/
noncomputable def lift_interleavedCodeword (i : Fin ℓ) (steps : ℕ) {destIdx : Fin r}
    (h_destIdx : destIdx.val = i.val + steps) (h_destIdx_le : destIdx ≤ ℓ)
    (V_codeword : ((BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) destIdx)
      ^⋈(Fin (2 ^ steps)))) :
    BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩ := by
  let P : L[X]_(2 ^ (ℓ - ↑i)) := getLiftPoly 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i steps
    h_destIdx h_destIdx_le V_codeword
  -- 3. Define g as evaluation of P
  let g := getBBF_Codeword_of_poly 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (i := ⟨i, by omega⟩) (h_i := by
      exact Nat.le_of_lt i.isLt) P
  exact g

omit [CharP L 2] in
/-- **Lemma 4.21 Helper**: Folding the "Lifted" polynomial `g` with binary challenges corresponding
to row index `j ∈ Fin(2^steps)`, results exactly in the `j`-th row polynomial `P_j`.
**Key insight**: **Binary folding** is a **(Row) Selector**
Proof strategy: applying `iterated_fold_advances_evaluation_poly` and
`intermediateEvaluationPoly_from_inovel_coeffs_eq_self`, then arithemetic equality for novel coeffs
computations in both sides. -/
lemma folded_lifted_IC_eq_IC_row_polyToOracleFunc (i : Fin ℓ) (steps : ℕ) {destIdx : Fin r}
    (h_destIdx : destIdx.val = i.val + steps) (h_destIdx_le : destIdx ≤ ℓ)
    (V_codeword : ((BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) destIdx)^⋈(Fin (2 ^ steps))))
    (j : Fin (2 ^ steps)) :
    let g := lift_interleavedCodeword 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      i steps h_destIdx h_destIdx_le V_codeword
    let P_j := (getRowPoly 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i steps h_destIdx h_destIdx_le
      V_codeword) j
    iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩ steps
      (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le) g (bitsOfIndex j) =
    polyToOracleFunc 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (domainIdx := destIdx) P_j := by
  -- 1. Unfold definitions to expose the underlying polynomials
  -- dsimp only [lift_interleavedCodeword, getLiftPoly]
  simp only
  set g := lift_interleavedCodeword 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i steps
    h_destIdx h_destIdx_le V_codeword with h_g
  set P_j := (getRowPoly 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i steps h_destIdx h_destIdx_le V_codeword) j
  set P_G := getLiftPoly 𝔽q β i steps h_destIdx h_destIdx_le V_codeword with h_P_G -- due to def of `g`
  have h_g : g = polyToOracleFunc 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (domainIdx := ⟨i, by omega⟩) P_G := by rfl
  -- unfold getLiftPoly at h_P_G
  let novelCoeffs := getLiftCoeffs 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i steps
    h_destIdx h_destIdx_le V_codeword
  -- have h_P_G_eq: P_G = intermediateEvaluationPoly 𝔽q β h_ℓ_add_R_rate
    -- (i := ⟨i, by omega⟩) novelCoeffs := by rfl
  let h_fold_g_advances_P_G := iterated_fold_advances_evaluation_poly 𝔽q β
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := ⟨i, by omega⟩) (steps := steps)
    (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le) (r_challenges := bitsOfIndex j) (coeffs := novelCoeffs)
  simp only at h_fold_g_advances_P_G
  conv_lhs at h_fold_g_advances_P_G => -- make it matches the lhs goal
    change iterated_fold 𝔽q β (i := ⟨i, by omega⟩) (steps := steps) (h_destIdx := h_destIdx)
      (h_destIdx_le := h_destIdx_le) (f := g) (bitsOfIndex j)
  conv_lhs => rw [h_fold_g_advances_P_G]
  -- ⊢ polyToOracleFunc 𝔽q β ⟨↑i + steps, ⋯⟩
  --   (intermediateEvaluationPoly 𝔽q β h_ℓ_add_R_rate ⟨↑i + steps, ⋯⟩ fun j_1 ↦
  --     ∑ x, multilinearWeight (bitsOfIndex j) x * novelCoeffs ⟨↑j_1 * 2 ^ steps + ↑x, ⋯⟩) =
  -- polyToOracleFunc 𝔽q β ⟨↑i + steps, ⋯⟩ ↑P_j
  have h_P_j_novel_form := intermediateEvaluationPoly_from_inovel_coeffs_eq_self 𝔽q β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := destIdx) (h_i := h_destIdx_le) (P := P_j) (hP_deg := by
        have h_mem := P_j.property
        rw [Polynomial.mem_degreeLT] at h_mem
        exact h_mem )
  conv_rhs => rw [←h_P_j_novel_form]
  -- polyToOracleFunc(intermediateEvaluationPoly(FOLDED novelCoeffs of P))) (via Lemma 4.13)
    -- = polyToOracleFunc(intermediateEvaluationPoly(inovelCoeffs of P_j))
  unfold polyToOracleFunc intermediateEvaluationPoly novelCoeffs
  simp only [map_sum, map_mul]
  funext y
  congr 1
  apply Finset.sum_congr rfl
  intro x hx_mem_univ
  rw [mul_eq_mul_right_iff]; left
  -- **Arithemetic reasoning**:
  -- ⊢ ∑ x_1, Polynomial.C (multilinearWeight (bitsOfIndex j) x_1) *
          --  Polynomial.C (getLiftCoeffs 𝔽q β i steps ⟨↑x * 2 ^ steps + ↑x_1, ⋯⟩) =
  -- Polynomial.C (getINovelCoeffs 𝔽q β h_ℓ_add_R_rate ⟨↑i + steps, ⋯⟩ (↑P_j) x)
  -- 1. Combine the Ring Homomorphisms to pull C outside the sum
  --    ∑ C(w) * C(v) -> C(∑ w * v)
  simp_rw [←Polynomial.C_mul]
  unfold getINovelCoeffs getLiftCoeffs
  simp only [mul_add_mod_self_right, map_mul]
  -- , ←Polynomial.C_sum]
  -- 2. Use the Indicator Property of multilinearWeight with binary challenges
  --    This logic should ideally be its own lemma: `weight_bits_eq_indicator`
  have h_indicator : ∀ m : Fin (2^steps), multilinearWeight (F := L) (r := bitsOfIndex j)
    (i := m) = if m = j then 1 else 0 := fun m => by
    apply multilinearWeight_bitsOfIndex_eq_indicator (j := m) (k := j)

  simp_rw [h_indicator]
  -- 3. Collapse the Sum using Finset.sum_eq_single
  rw [Finset.sum_eq_single j]
  · -- Case: The Match (x_1 = j)
    simp only [↓reduceIte, map_one, one_mul, Polynomial.C_inj]
    unfold getINovelCoeffs
    have h_idx_decomp : (x.val * 2 ^ steps + j.val) / 2^steps = x.val := by
      have h_j_div_2_pow_steps : j.val / 2^steps = 0 := by
        apply Nat.div_eq_of_lt; omega
      rw [mul_comm]
      have h_res := Nat.mul_add_div (m := 2 ^ steps) (x := x.val) (y := j.val) (m_pos := by
        simp only [gt_iff_lt, ofNat_pos, pow_pos])
      simp only [h_j_div_2_pow_steps, add_zero] at h_res
      exact h_res
    congr 1
    · funext k
      congr
      · apply Nat.mod_eq_of_lt; omega
    · simp_rw [h_idx_decomp]
  · -- Case: The Mismatch (x_1 ≠ j)
    intro m _ h_neq
    simp only [h_neq, ↓reduceIte, map_zero, zero_mul]
  · -- Case: Domain (Empty implies false, but we are in Fin (2^steps))
    intro h_absurd
    exfalso; exact h_absurd (Finset.mem_univ j)

omit [CharP L 2] in
open Code.InterleavedCode in
lemma preTensorCombine_of_lift_interleavedCodeword_eq_self (i : Fin ℓ) (steps : ℕ) {destIdx : Fin r}
    (h_destIdx : destIdx.val = i.val + steps) (h_destIdx_le : destIdx ≤ ℓ)
    (V_codeword : ((BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) destIdx)
      ^⋈(Fin (2 ^ steps)))) :
    let g := lift_interleavedCodeword 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      i steps h_destIdx h_destIdx_le V_codeword
    (⋈|(preTensorCombine_WordStack 𝔽q β i steps h_destIdx h_destIdx_le g)) = V_codeword.val := by
  let S_next := sDomain 𝔽q β h_ℓ_add_R_rate destIdx
  let C_next := BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) destIdx
  set g := lift_interleavedCodeword 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i)
    (steps := steps) (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le) (V_codeword := V_codeword)

  -- **FIRST**,
    -- `∀ j : Fin (2^ϑ), (V_codeword j)` and `fold(g, bitsOfIndex j)` agree identically
        -- over `S^{(i+ϑ)}`
    -- the dotproduct between `M_y's j'th ROW` and `G = g's restriction to the fiber of y`
        -- is actually the result of `fold(G, bitsOfIndex j)`

  have h_agree_with_fold := preTensorCombine_row_eq_fold_with_binary_row_challenges 𝔽q β
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i steps h_destIdx h_destIdx_le g

  let eq_iff_all_rows_eq := (instInterleavedStructureInterleavedWord (A := L) (κ := Fin (2 ^ steps))
    (ι := S_next)).eq_iff_all_rows_eq (u := ⋈|preTensorCombine_WordStack 𝔽q β (i := i)
      (steps := steps) (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le) (↑g)) (v := V_codeword.val)
  simp only
  rw [eq_iff_all_rows_eq]
  intro j
  funext (y : S_next) -- compare the cells at (j, y)
  set G := fiberEvaluations 𝔽q β (i := ⟨i, by omega⟩) (steps := steps)
    (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le) (f := g) (y := y)
  simp only [InterleavedWord, Word, InterleavedSymbol, instInterleavedStructureInterleavedWord,
    InterleavedWord.getRowWord, InterleavedWord.getSymbol, transpose_apply, WordStack,
    instInterleavableWordStackInterleavedWord, interleave_wordStack_eq, ModuleCode,
    instCodeInterleavableModuleCodeInterleavedSymbol.eq_1, ModuleCode.moduleInterleavedCode.eq_1,
    interleavedCodeSet.eq_1]
  -- ⊢ preTensorCombine_WordStack 𝔽q β i steps h_destIdx h_destIdx_le (↑g) j = (↑V_codeword)ᵀ j
  unfold preTensorCombine_WordStack
  simp only
  set M_y := foldMatrix 𝔽q β (i := ⟨i, by omega⟩) (steps := steps)
    (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le) y
  -- ⊢ (foldMatrix 𝔽q β ⟨↑i, ⋯⟩ steps ⋯ y *ᵥ fiberEvaluations 𝔽q β ⟨↑i, ⋯⟩ steps ⋯ (↑g) y) j
    -- = ↑V_codeword y j
  change (M_y *ᵥ G) j = V_codeword.val y j
  let lhs_eq_fold := h_agree_with_fold j y
  unfold preTensorCombine_WordStack at lhs_eq_fold
  simp at lhs_eq_fold
  rw [lhs_eq_fold]
  -- ⊢ iterated_fold 𝔽q β ⟨↑i, ⋯⟩ steps ⋯ (↑g) (bitsOfIndex j) y = ↑V_codeword y j

  -- **SECOND**, we prove that **the same row polynomial `P_j(X)` is used to generates** bot
    -- `fold(g, bitsOfIndex j)` and `j'th row of V_codeword`

  let curRow := getRow (show InterleavedCodeword (A := L) (κ := Fin (2 ^ steps))
    (ι := S_next) (C := C_next) from V_codeword) j

  let P_j := getRowPoly 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i steps h_destIdx h_destIdx_le V_codeword j
  let lhs := iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩ (steps := steps)
    (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le) (f := g)
    (r_challenges := bitsOfIndex j)
  let rhs := curRow.val
  let generatedRow : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) destIdx :=
    polyToOracleFunc 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (domainIdx := destIdx) (P := P_j)

  have h_left_eq_P_j_gen: lhs = generatedRow := by
    unfold lhs generatedRow -- ⊢ iterated_fold 𝔽q β ⟨↑i, ⋯⟩ steps ⋯ (↑g) (bitsOfIndex j)
      -- = polyToOracleFunc 𝔽q β ⟨↑i + steps, ⋯⟩ ↑P_j
    apply folded_lifted_IC_eq_IC_row_polyToOracleFunc

  have h_right_eq_P_j_eval: rhs = generatedRow := by
    unfold rhs generatedRow
    rw [getBBF_Codeword_poly_spec 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := destIdx) (u := curRow)]; rfl

  conv_lhs => change lhs y
  conv_rhs => change rhs y
  rw [h_left_eq_P_j_gen, h_right_eq_P_j_eval]

/-- TODO: **Lifting Equivalence Lemma**: `lift(preTensorCombine(f)) = f`. -/

def fiberDiff (i : Fin ℓ) (steps : ℕ) {destIdx : Fin r}
    (h_destIdx : destIdx.val = i.val + steps) (h_destIdx_le : destIdx ≤ ℓ)
    (f g : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩)
    (y : sDomain 𝔽q β h_ℓ_add_R_rate destIdx) : Prop :=
  ∃ x,
    iteratedQuotientMap 𝔽q β h_ℓ_add_R_rate (i := ⟨i, by omega⟩) (destIdx := destIdx)
      (k := steps) (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le) x = y ∧
    f x ≠ g x

/-- **Distance Isomorphism Lemma**
The crucial logic for Lemma 4.21:
Two functions `f, g` differ on a specific fiber `y` IF AND ONLY IF
their tensor-combinations `U, V` differ at the column `y`.
This holds because `M_y` is a bijection. -/
lemma fiberwise_disagreement_isomorphism (i : Fin ℓ) (steps : ℕ) {destIdx : Fin r}
    (h_destIdx : destIdx.val = i.val + steps) (h_destIdx_le : destIdx ≤ ℓ)
    (f g : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩)
    (y : sDomain 𝔽q β h_ℓ_add_R_rate destIdx) :
    fiberDiff 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i steps h_destIdx h_destIdx_le f g y ↔
    WordStack.getSymbol (preTensorCombine_WordStack 𝔽q β i steps h_destIdx h_destIdx_le f) y ≠
    WordStack.getSymbol (preTensorCombine_WordStack 𝔽q β i steps h_destIdx h_destIdx_le g) y := by
  -- U_y = M_y * f_vals, V_y = M_y * g_vals
  let M_y := foldMatrix 𝔽q β (i := ⟨i, by omega⟩) (steps := steps)
    (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le) y
  let f_vals := fiberEvaluations 𝔽q β (i := ⟨i, by omega⟩) (steps := steps)
    (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le) f y
  let g_vals := fiberEvaluations 𝔽q β (i := ⟨i, by omega⟩) (steps := steps)
    (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le) g y

  have h_det : M_y.det ≠ 0 := foldMatrix_det_ne_zero 𝔽q β (i := ⟨i, by omega⟩) (steps := steps)
    (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le) (y := y)
  constructor
  · -- Forward: Fiber different => Columns different
    intro h_diff
    -- If fiber is different, then vectors f_vals ≠ g_vals
    have h_vec_diff : f_vals ≠ g_vals := by
      rcases h_diff with ⟨x, h_gen_y, h_val_ne⟩ -- h_val_ne : f x ≠ g x
      intro h_eq
      let x_is_fiber_of_y := is_fiber_iff_generates_quotient_point 𝔽q β
        (i := ⟨i, by omega⟩) (steps := steps) (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le)
        (x := x) (y := y).mp (by exact id (Eq.symm h_gen_y))
      let x_fiberIdx : Fin (2 ^ steps) :=
        pointToIterateQuotientIndex 𝔽q β (i := ⟨i, by omega⟩) (steps := steps)
        (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le) (x := x)
      have h_left_eval : f_vals x_fiberIdx = f x := by
        unfold f_vals fiberEvaluations
        rw [x_is_fiber_of_y]
      have h_right_eval : g_vals x_fiberIdx = g x := by
        unfold g_vals fiberEvaluations
        rw [x_is_fiber_of_y]
      let h_eval_eq := congrFun h_eq x_fiberIdx
      rw [h_left_eval, h_right_eval] at h_eval_eq -- f x = g x
      exact h_val_ne h_eval_eq
    -- M_y is invertible, so M_y * u = M_y * v => u = v. Contrapositive: u ≠ v => M_y * u ≠ M_y * v
    intro h_col_eq
    apply h_vec_diff
    -- ⊢ f_vals = g_vals
    -- h_col_eq: WordStack.getSymbol (preTensorCombine_WordStack ... f) y = WordStack.getSymbol (preTensorCombine_WordStack ... g) y
    -- This means: M_y *ᵥ f_vals = M_y *ᵥ g_vals
    -- Rewrite as: M_y *ᵥ (f_vals - g_vals) = 0
    have h_mulVec_sub_eq_zero : M_y *ᵥ (f_vals - g_vals) = 0 := by
      -- From h_col_eq and the definition of preTensorCombine_WordStack:
      -- WordStack.getSymbol (preTensorCombine_WordStack ... f) y = M_y *ᵥ f_vals
      -- WordStack.getSymbol (preTensorCombine_WordStack ... g) y = M_y *ᵥ g_vals
      have h_f_col : WordStack.getSymbol (preTensorCombine_WordStack 𝔽q β i steps h_destIdx h_destIdx_le f) y = M_y *ᵥ f_vals := by
        ext j
        simp only [WordStack.getSymbol, Matrix.transpose_apply]
        rfl
      have h_g_col : WordStack.getSymbol (preTensorCombine_WordStack 𝔽q β i steps h_destIdx h_destIdx_le g) y = M_y *ᵥ g_vals := by
        ext j
        simp only [WordStack.getSymbol, Matrix.transpose_apply]
        rfl
      -- ⊢ M_y *ᵥ (f_vals - g_vals) = 0
      rw [h_f_col, h_g_col] at h_col_eq
      -- Now h_col_eq: M_y *ᵥ f_vals = M_y *ᵥ g_vals
      rw [Matrix.mulVec_sub]
      -- Goal: M_y *ᵥ f_vals - M_y *ᵥ g_vals = 0
      rw [← h_col_eq]
      -- Goal: M_y *ᵥ f_vals - M_y *ᵥ f_vals = 0
      rw [sub_self]
    -- Apply eq_zero_of_mulVec_eq_zero to get f_vals - g_vals = 0
    have h_sub_eq_zero : f_vals - g_vals = 0 :=
      Matrix.eq_zero_of_mulVec_eq_zero h_det h_mulVec_sub_eq_zero -- `usage of M_y's nonsingularity`
    -- Convert to f_vals = g_vals
    exact sub_eq_zero.mp h_sub_eq_zero
  · -- Backward: Columns different => Fiber different
    intro h_col_diff
    by_contra h_fiber_eq
    -- h_fiber_eq: ¬fiberDiff, i.e., ∀ x, iteratedQuotientMap ... x = y → f x = g x
    -- If f and g agree on all points in the fiber of y, then f_vals = g_vals
    have h_vals_eq : f_vals = g_vals := by
      ext idx
      -- f_vals idx = f evaluated at the idx-th point in the fiber of y
      -- g_vals idx = g evaluated at the idx-th point in the fiber of y
      -- We need to show they're equal
      unfold f_vals g_vals fiberEvaluations
      -- fiberEvaluations f y idx = f (qMap_total_fiber ... y idx)
      -- fiberEvaluations g y idx = g (qMap_total_fiber ... y idx)
      let x := qMap_total_fiber 𝔽q β (i := ⟨i, by omega⟩) (steps := steps)
        (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le) (y := y) idx
      -- x is in the fiber of y, so iteratedQuotientMap ... x = y
      have h_x_in_fiber :
          iteratedQuotientMap 𝔽q β h_ℓ_add_R_rate (i := ⟨i, by omega⟩) (destIdx := destIdx)
            (k := steps) (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le) x = y := by
        -- This follows from generates_quotient_point_if_is_fiber_of_y
        have h := generates_quotient_point_if_is_fiber_of_y 𝔽q β (i := ⟨i, by omega⟩) (steps := steps)
          (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le) (x := x) (y := y) (hx_is_fiber := by use idx)
        exact h.symm
      -- Since h_fiber_eq says no point in the fiber has f x ≠ g x,
      -- we have f x = g x for all x in the fiber
      have h_fx_eq_gx : f x = g x := by
        -- h_fiber_eq: ¬fiberDiff, which is ¬(∃ x, iteratedQuotientMap ... x = y ∧ f x ≠ g x)
        -- By De Morgan: ∀ x, ¬(iteratedQuotientMap ... x = y ∧ f x ≠ g x)
        -- Which means: ∀ x, iteratedQuotientMap ... x = y → f x = g x
        push_neg at h_fiber_eq
        -- h_fiber_eq is now: ∀ x, iteratedQuotientMap ... x = y → f x = g x
        unfold fiberDiff at h_fiber_eq
        simp only [ne_eq, Subtype.exists, not_exists, not_and, Decidable.not_not] at h_fiber_eq
        let res := h_fiber_eq x (by simp only [SetLike.coe_mem]) h_x_in_fiber
        exact res
      -- Now f_vals idx = f x = g x = g_vals idx
      exact h_fx_eq_gx
    -- If f_vals = g_vals, then M_y *ᵥ f_vals = M_y *ᵥ g_vals
    have h_col_eq : WordStack.getSymbol (preTensorCombine_WordStack 𝔽q β i steps h_destIdx h_destIdx_le f) y =
                    WordStack.getSymbol (preTensorCombine_WordStack 𝔽q β i steps h_destIdx h_destIdx_le g) y := by
      -- From the forward direction, we know:
      -- WordStack.getSymbol (preTensorCombine_WordStack ... f) y = M_y *ᵥ f_vals
      -- WordStack.getSymbol (preTensorCombine_WordStack ... g) y = M_y *ᵥ g_vals
      have h_f_col : WordStack.getSymbol (preTensorCombine_WordStack 𝔽q β i steps h_destIdx h_destIdx_le f) y = M_y *ᵥ f_vals := by
        ext j
        simp only [WordStack.getSymbol, Matrix.transpose_apply]
        rfl
      have h_g_col : WordStack.getSymbol (preTensorCombine_WordStack 𝔽q β i steps h_destIdx h_destIdx_le g) y = M_y *ᵥ g_vals := by
        ext j
        simp only [WordStack.getSymbol, Matrix.transpose_apply]
        rfl
      rw [h_f_col, h_g_col]
      -- Goal: M_y *ᵥ f_vals = M_y *ᵥ g_vals
      rw [h_vals_eq]
    -- This contradicts h_col_diff
    exact h_col_diff h_col_eq

end Lift_PreTensorCombine

open Classical in
/-- **Proposition 4.20 (Case 1)**:
If f⁽ⁱ⁾ is fiber-wise close to the code, the probability of the bad event is bounded.
The bad event here is: `Δ⁽ⁱ⁾(f⁽ⁱ⁾, f̄⁽ⁱ⁾) ⊄ Δ(fold(f⁽ⁱ⁾), fold(f̄⁽ⁱ⁾))`.
-/
lemma prop_4_20_case_1_fiberwise_close (i : Fin ℓ) (steps : ℕ) [NeZero steps]
    {destIdx : Fin r} (h_destIdx : destIdx.val = i.val + steps) (h_destIdx_le : destIdx ≤ ℓ)
    (f_i : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩)
    (h_close : fiberwiseClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := ⟨i, by omega⟩) (steps := steps) (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le) (f := f_i)) :
    let S_next := sDomain 𝔽q β h_ℓ_add_R_rate destIdx
    let domain_size := Fintype.card S_next
    Pr_{ let r_challenges ←$ᵖ (Fin steps → L) }[
        -- The definition of foldingBadEvent under the "then" branch of h_close
        let f_bar_i := UDRCodeword 𝔽q β (i := ⟨i, by omega⟩) (h_i := by
          exact Nat.le_of_lt i.isLt) f_i
          (UDRClose_of_fiberwiseClose 𝔽q β ⟨i, by omega⟩ steps h_destIdx h_destIdx_le f_i h_close)
        let folded_f_i := iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩
          steps h_destIdx h_destIdx_le f_i r_challenges
        let folded_f_bar_i := iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩
          steps h_destIdx h_destIdx_le f_bar_i r_challenges
        ¬ (fiberwiseDisagreementSet 𝔽q β (i := ⟨i, by omega⟩) steps h_destIdx h_destIdx_le f_i f_bar_i ⊆
           disagreementSet 𝔽q β destIdx (h_i := h_destIdx_le) folded_f_i folded_f_bar_i)
    ] ≤ ((steps * domain_size) / Fintype.card L) := by
  let S_next := sDomain 𝔽q β h_ℓ_add_R_rate destIdx
  let L_card := Fintype.card L
  -- 1. Setup Definitions
  let f_bar_i : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩ :=
    UDRCodeword 𝔽q β (i := ⟨i, by omega⟩) (h_i := by
      exact Nat.le_of_lt i.isLt)
      (f := f_i) (h_within_radius := UDRClose_of_fiberwiseClose 𝔽q β ⟨i, by omega⟩ steps h_destIdx h_destIdx_le f_i h_close)
  let Δ_fiber : Set (sDomain 𝔽q β h_ℓ_add_R_rate destIdx) :=
    fiberwiseDisagreementSet 𝔽q β (i := ⟨i, by omega⟩) steps h_destIdx h_destIdx_le f_i f_bar_i
  -- We apply the Union Bound over `y ∈ Δ_fiber`
    -- `Pr[ ∃ y ∈ Δ_fiber, y ∉ Disagreement(folded) ] ≤ ∑ Pr[ y ∉ Disagreement(folded) ]`
  have h_union_bound :
    Pr_{ let r ←$ᵖ (Fin steps → L) }[
      ¬(Δ_fiber ⊆ disagreementSet 𝔽q β destIdx (h_i := h_destIdx_le)
        (iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩ steps h_destIdx h_destIdx_le f_i r)
        (iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩ steps h_destIdx h_destIdx_le f_bar_i r))
    ] ≤ ∑ y ∈ Δ_fiber.toFinset,
        Pr_{ let r ←$ᵖ (Fin steps → L) }[
            -- The condition y ∉ Disagreement(folded) implies folded values are equal at y
            (iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩ steps h_destIdx h_destIdx_le f_i r) y =
            (iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩ steps h_destIdx h_destIdx_le f_bar_i r) y
        ] := by
      -- Standard probability union bound logic
      -- Convert probability to cardinality ratio for the Union Bound
      rw [prob_uniform_eq_card_filter_div_card]
      simp_rw [prob_uniform_eq_card_filter_div_card]
      simp only [ENNReal.coe_natCast, Fintype.card_pi, prod_const, Finset.card_univ,
        Fintype.card_fin, cast_pow, ENNReal.coe_pow]
      set left_set : Finset (Fin steps → L) :=
        Finset.univ.filter fun r =>
          ¬(Δ_fiber ⊆
            disagreementSet 𝔽q β destIdx (h_i := h_destIdx_le) (iterated_fold 𝔽q β ⟨i, by omega⟩ steps
              h_destIdx h_destIdx_le f_i r)
              (iterated_fold 𝔽q β ⟨↑i, by omega⟩ steps
              h_destIdx h_destIdx_le f_bar_i r))

      set right_set :
          (x : sDomain 𝔽q β h_ℓ_add_R_rate destIdx) →
            Finset (Fin steps → L) :=
        fun x =>
          (Finset.univ.filter fun r =>
            iterated_fold 𝔽q β ⟨↑i, by omega⟩ steps
                h_destIdx h_destIdx_le
                f_i r x =
              iterated_fold 𝔽q β ⟨↑i, by omega⟩ steps
                h_destIdx h_destIdx_le
                f_bar_i r x)
      conv_lhs =>
        change _ * ((Fintype.card L : ENNReal) ^ steps)⁻¹
        rw [mul_comm]
      conv_rhs =>
        change
          ∑ y ∈ Δ_fiber.toFinset,
            ((#(right_set y) : ENNReal) * ((Fintype.card L : ENNReal) ^ steps)⁻¹)
      conv_rhs =>
        simp only [mul_comm]
        rw [←Finset.mul_sum]
      -- ⊢ (↑(Fintype.card L) ^ steps)⁻¹ * ↑(#left_set) ≤ (↑(Fintype.card L) ^ steps)⁻¹ * ∑ i ∈ Δ_fiber.toFinset, ↑(#(right_set i))
      let left_le_right_if := (ENNReal.mul_le_mul_left (a := ((Fintype.card L : ENNReal) ^ steps)⁻¹) (b := (#left_set)) (c := ∑ i ∈ Δ_fiber.toFinset, (#(right_set i))) (h0 := by simp only [ne_eq,
        ENNReal.inv_eq_zero, ENNReal.pow_eq_top_iff, ENNReal.natCast_ne_top, false_and,
        not_false_eq_true]) (hinf := by simp only [ne_eq, ENNReal.inv_eq_top, pow_eq_zero_iff',
          cast_eq_zero, Fintype.card_ne_zero, false_and, not_false_eq_true])).mpr
      apply left_le_right_if

      -- ⊢ ↑(#left_set) ≤ ∑ i ∈ Δ_fiber.toFinset, ↑(#(right_set i))

      -- 1. Prove the subset relation: left_set ⊆ ⋃_{y ∈ Δ} right_set y
      -- This formally connects the failure condition (∃ y, agree) to the union of agreement sets.
      have h_subset : left_set ⊆ Δ_fiber.toFinset.biUnion right_set := by
        intro r hr
        -- Unpack membership in left_set: r is bad if Δ_fiber ⊈ disagreementSet
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, left_set] at hr
        rw [Set.not_subset] at hr
        rcases hr with ⟨y, hy_mem, hy_not_dis⟩
        -- We found a y ∈ Δ_fiber where they do NOT disagree (i.e., they agree)
        rw [Finset.mem_biUnion]
        use y
        constructor
        · exact Set.mem_toFinset.mpr hy_mem
        · -- Show r ∈ right_set y (which is defined as the set of r where they agree at y)
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, right_set]
          -- hy_not_dis is ¬(folded_f_i y ≠ folded_f_bar_i y) ↔ folded_f_i y = folded_f_bar_i y
          simp only [disagreementSet, ne_eq, coe_filter, mem_univ, true_and, Set.mem_setOf_eq,
            Decidable.not_not] at hy_not_dis
          exact hy_not_dis

      -- 2. Apply cardinality bounds (Union Bound)
      calc
        (left_set.card : ENNReal)
        _ ≤ (Δ_fiber.toFinset.biUnion right_set).card := by
          -- Monotonicity of measure/cardinality: A ⊆ B → |A| ≤ |B|
          gcongr
        _ ≤ ∑ i ∈ Δ_fiber.toFinset, (right_set i).card := by
          -- Union Bound: |⋃ S_i| ≤ ∑ |S_i|
          -- push_cast moves the ENNReal coercion inside the sum
          push_cast
          let h_le_in_Nat := Finset.card_biUnion_le (s := Δ_fiber.toFinset) (t := right_set)
          norm_cast
        _ = _ := by push_cast; rfl
  apply le_trans h_union_bound
  -- Now bound the individual probabilities using Schwartz-Zippel
  have h_prob_y : ∀ y ∈ Δ_fiber,
    Pr_{ let r ←$ᵖ (Fin steps → L) }[
        (iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩ steps h_destIdx h_destIdx_le f_i r) y =
        (iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩ steps h_destIdx h_destIdx_le f_bar_i r) y
    ] ≤ (steps) / L_card := by
    intro y hy
    -- 1. Apply Lemma 4.9 (iterated_fold_eq_matrix_form) to express the equality as a matrix eq.
    --    Equality holds iff Tensor(r) * M_y * (f - f_bar)|_fiber = 0.
    -- 2. Define the polynomial P(r) = Tensor(r) * w, where w = M_y * (vals_f - vals_f_bar).
    -- 3. Show w ≠ 0:
    --      a. vals_f - vals_f_bar ≠ 0 because y ∈ Δ_fiber (definitions).
    --      b. M_y is nonsingular (Lemma 4.9 / Butterfly structure).
    -- 4. Apply prob_schwartz_zippel_mv_polynomial to P(r).
    --      degree(P) = steps.
    -- 1. Apply Lemma 4.9 to express folding as Matrix Form
    -- Equality holds iff [Tensor(r)] * [M_y] * [f - f_bar] = 0
    let vals_f : Fin (2 ^ steps) → L := fiberEvaluations 𝔽q β (i := ⟨i, by omega⟩) (steps := steps)
      (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le) f_i y
    let vals_f_bar : Fin (2 ^ steps) → L := fiberEvaluations 𝔽q β (i := ⟨i, by omega⟩) (steps := steps)
      (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le) f_bar_i y
    let v_diff : Fin (2 ^ steps) → L := vals_f - vals_f_bar

    -- 2. Show `v_diff ≠ 0` because `y ∈ Δ_fiber`, this is actually by definition of `Δ_fiber`.
    have hv_ne_zero : v_diff ≠ 0 := by
      unfold v_diff
      have h_exists_diff_point: ∃ x: Fin (2 ^ steps), vals_f x ≠ vals_f_bar x := by
        dsimp only [fiberwiseDisagreementSet, ne_eq, Δ_fiber] at hy
        -- ∃ x, iteratedQuotientMap 𝔽q β h_ℓ_add_R_rate ⟨i, by omega⟩ (k := steps) h_destIdx h_destIdx_le x = y ∧ f_i x ≠ f_bar_i x
        simp only [Subtype.exists, coe_filter, mem_univ, true_and, Set.mem_setOf_eq] at hy
        -- rcases hy with ⟨xL, h_quot, h_ne⟩
        rcases hy with ⟨xL, h_prop_xL⟩
        rcases h_prop_xL with ⟨xL_mem_sDomain, h_quot, h_ne⟩
        set xSDomain : sDomain 𝔽q β h_ℓ_add_R_rate (i := ⟨i, by omega⟩) := ⟨xL, xL_mem_sDomain⟩
        let x_is_fiber_of_y :=
          is_fiber_iff_generates_quotient_point 𝔽q β (i := ⟨i, by omega⟩) (steps := steps)
            (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le)
          (x := xSDomain) (y := y).mp (by exact id (Eq.symm h_quot))
        let x_fiberIdx : Fin (2 ^ steps) := pointToIterateQuotientIndex 𝔽q β (i := ⟨i, by omega⟩) (steps := steps)
          (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le) (x := xSDomain)
        use x_fiberIdx
        have h_left_eval : vals_f x_fiberIdx = f_i xSDomain := by
          unfold vals_f fiberEvaluations
          rw [x_is_fiber_of_y]
        have h_right_eval : vals_f_bar x_fiberIdx = f_bar_i xSDomain := by
          unfold vals_f_bar fiberEvaluations
          rw [x_is_fiber_of_y]
        rw [h_left_eval, h_right_eval]
        exact h_ne
      by_contra h_eq_zero
      rw [funext_iff] at h_eq_zero
      rcases h_exists_diff_point with ⟨x, h_ne⟩
      have h_eq: vals_f x = vals_f_bar x := by
        have res := h_eq_zero x
        simp only [Pi.sub_apply, Pi.zero_apply] at res
        rw [sub_eq_zero] at res
        exact res
      exact h_ne h_eq

    -- 3. M_y is nonsingular (from Lemma 4.9 context/properties of AdditiveNTT)
    let M_y := foldMatrix 𝔽q β (i := ⟨i, by omega⟩) (steps := steps)
      (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le) y
    have hMy_det_ne_zero : M_y.det ≠ 0 := by
      apply foldMatrix_det_ne_zero 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := ⟨i, by omega⟩) (steps := steps)
        (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le) (y := y)

    -- 4. w = M_y * v_diff is non-zero
    let w := M_y *ᵥ v_diff
    have hw_ne_zero : w ≠ 0 := by
      intro h
      exact hv_ne_zero (by exact Matrix.eq_zero_of_mulVec_eq_zero hMy_det_ne_zero h)

    -- 5. Construct the polynomial P(r) = Tensor(r) ⬝ w
    -- This is a multilinear polynomial of degree `steps`
    -- Tensor(r)_k corresponds to the Lagrange basis polynomial evaluated at r
    let P : MvPolynomial (Fin steps) L :=
        ∑ k : Fin (2^steps), (MvPolynomial.C (w k)) * (MvPolynomial.eqPolynomial (r := bitsOfIndex k))

    have hP_eval : ∀ r, P.eval r = (challengeTensorExpansion steps r) ⬝ᵥ w := by
      intro r
      simp only [P, MvPolynomial.eval_sum, MvPolynomial.eval_mul, MvPolynomial.eval_C]
      rw [dotProduct]
      apply Finset.sum_congr rfl
      intro k hk_univ
      conv_lhs => rw [mul_comm]
      congr 1
      -- evaluation of Lagrange basis matches tensor expansion
      -- ⊢ (MvPolynomial.eval r) (eqPolynomial (bitsOfIndex k)) = challengeTensorExpansion steps r k

      -- Unfold definitions to expose the product structure
      unfold eqPolynomial singleEqPolynomial bitsOfIndex challengeTensorExpansion multilinearWeight
      rw [MvPolynomial.eval_prod] -- prod structure of `eqPolynomial`
      -- Now both sides have form `∏ (j : Fin steps), ...`
      apply Finset.prod_congr rfl
      intro j _
      -- Simplify polynomial evaluation
      simp only [MonoidWithZeroHom.map_ite_one_zero, ite_mul, one_mul, zero_mul,
        MvPolynomial.eval_add, MvPolynomial.eval_mul, MvPolynomial.eval_sub, map_one,
        MvPolynomial.eval_X]
      split_ifs with h_bit
      · -- Case: Bit is 1
        simp only [sub_self, zero_mul, MvPolynomial.eval_X, zero_add]
      · -- Case: Bit is 0
        simp only [sub_zero, one_mul, map_zero, add_zero]

    have hP_nonzero : P ≠ 0 := by
      -- Assume P = 0 for contradiction
      intro h_P_zero
      -- Since w ≠ 0, there exists some index k such that w k ≠ 0
      rcases Function.ne_iff.mp hw_ne_zero with ⟨k, hk_ne_zero⟩

      -- Let r_k be the bit-vector corresponding to index k
      let r_k := bitsOfIndex (L := L) k

      -- If P = 0, then P(r_k) must be 0
      have h_eval_zero : MvPolynomial.eval r_k P = 0 := by
        rw [h_P_zero]; simp only [map_zero]

      -- On the other hand, we proved P(r) = Tensor(r) ⬝ w
      rw [hP_eval r_k] at h_eval_zero

      -- Key Property: Tensor(r_k) is the indicator vector for k.
      -- Tensor(r_k)[j] = 1 if j=k, 0 if j≠k.
      have h_tensor_k : ∀ j, (challengeTensorExpansion steps r_k) j = if j = k then 1 else 0 := by
        intro j
        rw [challengeTensorExpansion_bitsOfIndex_is_eq_indicator (L := L) (n := steps) (k := k)]

      -- Thus the dot product is exactly w[k]
      rw [dotProduct, Finset.sum_eq_single k] at h_eval_zero
      · simp only [h_tensor_k, if_true, one_mul] at h_eval_zero
        exact hk_ne_zero h_eval_zero
      · -- Other terms are zero
        intro j _ h_ne
        simp [h_tensor_k, h_ne]
      · simp only [mem_univ, not_true_eq_false, _root_.mul_eq_zero, IsEmpty.forall_iff] -- Case where index k is not in univ (impossible for Fin n)

    have hP_deg : P.totalDegree ≤ steps := by
      -- Use the correct lemma from the list: sum degree ≤ d if all terms degree ≤ d
      apply MvPolynomial.totalDegree_finsetSum_le
      intro k _
      -- Bound degree of each term: deg(C * eqPoly) ≤ deg(C) + deg(eqPoly) = 0 + deg(eqPoly)
      apply le_trans (MvPolynomial.totalDegree_mul _ _)
      simp only [MvPolynomial.totalDegree_C, zero_add]

      -- Bound degree of eqPolynomial (product of linear terms)
      unfold eqPolynomial
      -- deg(∏ f) ≤ ∑ deg(f)
      apply le_trans (MvPolynomial.totalDegree_finset_prod _ _)

      -- The sum of `steps` terms, each of degree ≤ 1
      trans ∑ (i : Fin steps), 1
      · apply Finset.sum_le_sum
        intro i _
        -- Check degree of singleEqPolynomial: r*X + (1-r)*(1-X)
        unfold singleEqPolynomial
        -- deg(A + B) ≤ max(deg A, deg B)
        apply (MvPolynomial.totalDegree_add _ _).trans
        rw [max_le_iff]
        constructor
        · -- deg(C * X) ≤ 1
          apply (MvPolynomial.totalDegree_mul _ _).trans
          -- simp [MvPolynomial.totalDegree_C, MvPolynomial.totalDegree_X]
          -- ⊢ (1 - MvPolynomial.C (bitsOfIndex k i)).totalDegree + (1 - MvPolynomial.X i).totalDegree ≤ 1
          calc
            _ ≤ ((1 : L[X Fin steps]) - MvPolynomial.X i).totalDegree := by
              have h_left_le := MvPolynomial.totalDegree_sub_C_le (p := (1 : L[X Fin steps])) (r := bitsOfIndex k i)
              simp only [totalDegree_one] at h_left_le -- (1 - C (bitsOfIndex k i)).totalDegree ≤ 0
              omega
            _ ≤ max ((1 : L[X Fin steps]).totalDegree) ((MvPolynomial.X (R := L) i).totalDegree) := by
              apply MvPolynomial.totalDegree_sub
            _ = _ := by
              simp only [totalDegree_one, totalDegree_X, _root_.zero_le, sup_of_le_right]
        · -- deg(C * (X)) ≤ 1
          apply (MvPolynomial.totalDegree_mul _ _).trans
          simp only [MvPolynomial.totalDegree_C, zero_add]
          -- ⊢ (MvPolynomial.X i).totalDegree ≤ 1
          simp only [totalDegree_X, le_refl]
      · simp only [sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one, le_refl]
    -- 6. Apply Schwartz-Zippel using Pr_congr to switch the event
    rw [Pr_congr (Q := fun r => MvPolynomial.eval r P = 0)]
    · apply prob_schwartz_zippel_mv_polynomial P hP_nonzero hP_deg
    · intro r
      -- Show that (Folding Eq) ↔ (P(r) = 0)
      rw [iterated_fold_eq_matrix_form 𝔽q β (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le), iterated_fold_eq_matrix_form 𝔽q β (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le)]
      -- Expand the dot product logic:
      unfold localized_fold_matrix_form single_point_localized_fold_matrix_form
      rw [hP_eval]
      rw [Matrix.dotProduct_mulVec]
      simp only
      -- ⊢ challengeTensorExpansion steps r ᵥ* foldMatrix 𝔽q β ⟨↑i, ⋯⟩ steps ⋯ y ⬝ᵥ fiberEvaluations 𝔽q β ⟨↑i, ⋯⟩ steps ⋯ f_i y =
      --     challengeTensorExpansion steps r ⬝ᵥ
      --       foldMatrix 𝔽q β ⟨↑i, ⋯⟩ steps ⋯ y *ᵥ fiberEvaluations 𝔽q β ⟨↑i, ⋯⟩ steps ⋯ f_bar_i y ↔
      --   challengeTensorExpansion steps r ⬝ᵥ w = 0
      rw [←sub_eq_zero]
      -- Transform LHS: u ⬝ (M * a) - u ⬝ (M * b) = u ⬝ (M * a - M * b)
      rw [←Matrix.dotProduct_mulVec]
      rw [←dotProduct_sub]
      -- Transform inner vector: M * a - M * b = M * (a - b)
      rw [←Matrix.mulVec_sub]
      -- Substitute definition of w: w = M * (vals_f - vals_f_bar)
      -- Note: v_diff was defined as vals_f - vals_f_bar
      -- And w was defined as M_y *ᵥ v_diff

  -- Sum the bounds: |Δ_fiber| * (steps / |L|)
  -- Since |Δ_fiber| ≤ |S_next|, this is bounded by |S_next| * steps / |L|
  have h_card_fiber : Δ_fiber.toFinset.card ≤ Fintype.card S_next :=
    Finset.card_le_univ Δ_fiber.toFinset

  calc
    _ ≤ ∑ y ∈ Δ_fiber.toFinset, (steps : ENNReal)  / L_card := by
        apply Finset.sum_le_sum
        intro y hy -- hy : y ∈ Δ_fiber.toFinset
        let res := h_prob_y y (by exact Set.mem_toFinset.mp hy)
        exact res
    _ = (Δ_fiber.toFinset.card) * (steps / L_card) := by
        simp only [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (Fintype.card S_next) * (steps / L_card) := by
        gcongr
    _ = (steps * Fintype.card S_next) / L_card := by
      ring_nf
      conv_rhs => rw [mul_div_assoc]

open Code.InterleavedCode in
/-- **Lemma 4.21** (Interleaved Distance Preservation):
If `d⁽ⁱ⁾(f⁽ⁱ⁾, C⁽ⁱ⁾) ≥ d_{i+ϑ} / 2` (`f` is fiber-wise far wrt UDR),
then `d^{2^ϑ}( (f_j⁽ⁱ⁺ϑ⁾)_{j=0}^{2^ϑ - 1}, C^{(i+ϑ)^{2^ϑ}} ) ≥ d_{i+ϑ} / 2`
  (i.e. interleaved distance ≥ UDR distance).
* **Main Idea of Proof:** For an ARBITRARY interleaved codeword `(g_j⁽ⁱ⁺ϑ⁾)`,
a "lift" `g⁽ⁱ⁾ ∈ C⁽ⁱ⁾` is constructed. It's shown that `g⁽ⁱ⁾` relates to `(g_j⁽ⁱ⁺ϑ⁾)` (via
folding with basis vectors as challenges) similarly to how `f⁽ⁱ⁾` relates to `(f_j⁽ⁱ⁺ϑ⁾)` (via
Lemma 4.9 and matrix `M_y`). Since `f⁽ⁱ⁾` is far from `g⁽ⁱ⁾` on many fibers (by hypothesis), and
`M_y` is invertible, the columns `(f_j⁽ⁱ⁺ϑ⁾(y))` and `(g_j⁽ⁱ⁺ϑ⁾(y))` must differ for these `y`,
establishing the distance for the interleaved words. -/
lemma lemma_4_21_interleaved_word_UDR_far (i : Fin ℓ) (steps : ℕ) [NeZero steps]
    {destIdx : Fin r} (h_destIdx : destIdx.val = i.val + steps) (h_destIdx_le : destIdx ≤ ℓ)
    (f_i : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩)
    (h_far : ¬fiberwiseClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := ⟨i, by omega⟩) (steps := steps)
      (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le) (f := f_i)) :
    let U := preTensorCombine_WordStack 𝔽q β i steps h_destIdx h_destIdx_le f_i
    let C_next : Set (sDomain 𝔽q β h_ℓ_add_R_rate destIdx → L) :=
      BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) destIdx
    ¬(jointProximityNat (C := C_next) (u := U) (e := Code.uniqueDecodingRadius (C := C_next))) := by

  -- 1. Setup variables and definitions
  let m := 2^steps
  let S_next := sDomain 𝔽q β h_ℓ_add_R_rate destIdx
  let C : Set (sDomain 𝔽q β h_ℓ_add_R_rate ⟨i, by omega⟩ → L) :=
      (BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩)
  let C_next := BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) destIdx
  let C_int := C_next ^⋈ (Fin m)
  let U_wordStack := preTensorCombine_WordStack 𝔽q β i steps h_destIdx h_destIdx_le f_i
  let U_interleaved : InterleavedWord L (Fin m) S_next := ⋈|U_wordStack
  let d_next := BBF_CodeDistance 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (i := destIdx)
  let e_udr := Code.uniqueDecodingRadius (C := (C_next : Set (S_next → L)))

  -- 2. Analyze the "Far" hypothesis
  -- h_far : ¬(2 * fiberwiseDistance < d_next) ↔ 2 * fiberwiseDistance ≥ d_next
  -- This means for ANY g ∈ C^(i), the number of fiber disagreements is ≥ d_next/2.
  have h_fiber_dist_ge : ∀ g : BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩,
      2 * (fiberwiseDisagreementSet 𝔽q β ⟨i, by omega⟩ steps h_destIdx h_destIdx_le f_i g).card ≥ d_next := by
    -- Expand negation of fiberwiseClose definition
    intro g
    -- 1. Unwrap the "Far" hypothesis
    -- "Not Close" means 2 * min_dist ≥ d_next
    unfold fiberwiseClose at h_far
    rw [not_lt] at h_far

    -- 2. Set up the set of all distances
    let dist_set := (fun (g' : C) =>
      (fiberwiseDisagreementSet 𝔽q β (i := ⟨i, by omega⟩) steps h_destIdx h_destIdx_le f_i g').card) '' Set.univ

    -- 3. Show that the specific g's distance is >= the minimum distance
    -- We use `csInf_le` which says inf(S) ≤ x for any x ∈ S (provided S is bounded below)
    have h_min_le_g : fiberwiseDistance 𝔽q β (i := ⟨i, by omega⟩) steps h_destIdx h_destIdx_le f_i ≤
        (fiberwiseDisagreementSet 𝔽q β (i := ⟨i, by omega⟩) steps h_destIdx h_destIdx_le f_i g).card := by
      apply csInf_le
      -- S must be bounded below (0 is a lower bound for Nat)
      · use 0
        rintro _ ⟨_, _, rfl⟩
        simp only [_root_.zero_le]
      -- S must be nonempty (g exists)
      · use g
        simp only [Set.mem_univ, true_and]
        rfl

    -- 4. Transitivity: d_next ≤ 2 * min ≤ 2 * specific
    calc
      d_next ≤ 2 * fiberwiseDistance 𝔽q β (i := ⟨i, by omega⟩) steps h_destIdx h_destIdx_le f_i := by
        norm_cast at h_far
      _ ≤ 2 * (fiberwiseDisagreementSet 𝔽q β (i := ⟨i, by omega⟩) steps h_destIdx h_destIdx_le f_i g).card := by
        let res := Nat.mul_le_mul_left (k := (2 : ℕ)) (h := (h_min_le_g))
        exact res

  -- 3. Proof by Contradiction
  -- Assume U is close to C_int (distance ≤ e_udr).
  simp only
  intro h_U_close -- Proof by Contradiction: Assume U is UDR-close to C_int.

  -- By definition of jointProximityNat, this means U is e_udr-close to C_int.
  -- Since C_int is nonempty, there exists a closest codeword V ∈ C_int.
  obtain ⟨V_codeword, h_dist_U_V⟩ := jointProximityNat_iff_closeToInterleavedCodeword
    (u := U_wordStack) (e := e_udr) (C := C_next) |>.mp h_U_close

  -- 4. Construct the "Lifted" Codeword g
  -- We claim there exists a g ∈ C^(i) such that applying `preTensorCombine_WordStack` to g yields V.
  -- This essentially inverses the folding operation. M_y is invertible, so we can recover
  -- the fiber evaluations of g from the columns of V.
  -- The algebraic properties of Binius ensure this reconstructed g is a valid codeword in C^(i).
  let g := lift_interleavedCodeword 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i steps h_destIdx h_destIdx_le V_codeword
  have h_g_is_lift_of_V : (⋈|preTensorCombine_WordStack 𝔽q β i steps h_destIdx h_destIdx_le ↑g)
    = V_codeword.val := by
    apply preTensorCombine_of_lift_interleavedCodeword_eq_self 𝔽q β

  -- 5. Equivalence of Disagreements via Non-Singular M_y
  -- We show that U and V differ at column y iff f_i and g differ on the CORRESPONDING fiber of y.
  -- This relies on U_y = M_y * f_fiber and V_y = M_y * g_fiber.
  have h_disagreement_equiv : ∀ y : S_next,
      (∃ x,
        iteratedQuotientMap 𝔽q β h_ℓ_add_R_rate (i := ⟨i, by omega⟩) (destIdx := destIdx)
          (k := steps) (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le) x = y ∧
        f_i x ≠ g.val x) ↔
      getSymbol U_interleaved y ≠ getSymbol V_codeword y := by
    intro y
    let res := fiberwise_disagreement_isomorphism 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i) (steps := steps)
      (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le) (f := f_i) (g := g.val) (y := y)
    unfold fiberDiff at res
    rw [res]
    have h_col_U_y_eq : (preTensorCombine_WordStack 𝔽q β i steps h_destIdx h_destIdx_le f_i).getSymbol y
      = getSymbol U_interleaved y := by rfl
    have h_col_V_y_eq : (preTensorCombine_WordStack 𝔽q β i steps h_destIdx h_destIdx_le g.val).getSymbol y
      = getSymbol V_codeword y := by
      have h_get_symbol_eq : (preTensorCombine_WordStack 𝔽q β i steps h_destIdx h_destIdx_le
        (g.val)).getSymbol y = getSymbol (⋈|preTensorCombine_WordStack 𝔽q β i steps h_destIdx h_destIdx_le ↑g) y := by rfl
      rw [h_get_symbol_eq]
      rw [h_g_is_lift_of_V]
      -- ⊢ getSymbol (↑V_codeword) y = getSymbol V_codeword y (lhs is I(nterleaved) word, rhs is IC)
      rfl
    rw [h_col_U_y_eq, h_col_V_y_eq]

  -- 6. Connect Distances
  -- The Hamming distance Δ₀(U, V) is exactly the number of columns where they differ.
  -- By the equivalence above, this is exactly the size of `fiberwiseDisagreementSet f_i g`.
  have h_dist_eq : Δ₀(U_interleaved, V_codeword.val) ≥
      (fiberwiseDisagreementSet 𝔽q β (i := ⟨i, by omega⟩) steps h_destIdx h_destIdx_le f_i g).card := by
    -- Use h_disagreement_equiv and definition of Hamming distance / fiberwiseDisagreementSet
    -- We prove equality, which implies ≥
    apply le_of_eq
    -- Definition of Hamming distance is count of {y | U y ≠ V y}
    unfold hammingDist
    -- Definition of fiberwiseDisagreementSet is {y | ∃ x ∈ Fiber(y), f x ≠ g x}
    unfold fiberwiseDisagreementSet
    -- We want to show card {y | U y ≠ V y} = card {y | fiber_diff }
    -- It suffices to show the sets are equal.
    congr 1
    ext y
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    -- Apply the equivalence we proved in step 5
    rw [h_disagreement_equiv]
    -- The LHS of h_disagreement_equiv matches the RHS of our goal here.
    -- The RHS of h_disagreement_equiv matches the LHS of our goal here.
    -- Just need to handle the `InterleavedWord` wrapper
    rfl

  -- 7. Contradiction Algebra
  -- We have:
  -- (1) 2 * dist(U, V) ≤ 2 * e_udr (by assumption h_U_close)
  -- (2) 2 * e_udr < d_next (by definition of UDR)
  -- (3) 2 * card(disagreement f g) ≥ d_next (by h_far hypothesis applied to g)
  -- (4) dist(U, V) = card(disagreement f g) (by h_dist_eq)
  -- Combining (3) and (4): 2 * dist(U, V) ≥ d_next
  -- Combining (1) and (2): 2 * dist(U, V) < d_next
  -- Contradiction.

  have h_ineq_1 : ¬(2 * (fiberwiseDisagreementSet 𝔽q β (i := ⟨i, by omega⟩) steps
        h_destIdx h_destIdx_le f_i g).card < d_next) := by
    simp only [not_lt, h_fiber_dist_ge (g := ⟨g, by simp only [SetLike.coe_mem]⟩)]

  have h_ineq_2 :
      2 * (fiberwiseDisagreementSet 𝔽q β (i := ⟨i, by omega⟩) steps
        h_destIdx h_destIdx_le f_i g).card < d_next := by
    calc
      2 * (fiberwiseDisagreementSet 𝔽q β (i := ⟨i, by omega⟩) steps
        h_destIdx h_destIdx_le f_i g).card
      _ ≤ 2 * Δ₀(U_interleaved, V_codeword.val) := by
        omega
      _ ≤ 2 * e_udr := by
      -- {n m : Nat} (k : Nat) (h : n ≤ m) : n * k ≤ m * k :=
        let res := Nat.mul_le_mul_left (k := 2) (h := h_dist_U_V)
        exact res
      _ < d_next := by
        -- ⊢ 2 * e_udr < d_next
        letI : NeZero (‖(C_next : Set (S_next → L))‖₀) := NeZero.of_pos (by
          have h_pos : 0 <
              BBF_CodeDistance 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) destIdx := by
            -- ⊢ 0 < 2 ^ (ℓ + 𝓡 - destIdx.val) - 2 ^ (ℓ - destIdx.val) + 1
            simp [BBF_CodeDistance_eq (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
              (i := destIdx) (h_i := h_destIdx_le)]
          simpa [C_next, BBF_CodeDistance] using h_pos
        )
        let res := Code.UDRClose_iff_two_mul_proximity_lt_d_UDR
          (C := (C_next : Set (S_next → L))) (e := e_udr).mp (by omega)
        exact res

  exact h_ineq_1 h_ineq_2

lemma prop_4_20_case_2_fiberwise_far (i : Fin ℓ) (steps : ℕ) [NeZero steps]
    {destIdx : Fin r} (h_destIdx : destIdx.val = i.val + steps) (h_destIdx_le : destIdx ≤ ℓ)
    (f_i : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩)
    (h_far : ¬fiberwiseClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := ⟨i, by omega⟩) (steps := steps)
      (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le) (f := f_i)) :
    let next_domain_size := Fintype.card (sDomain 𝔽q β h_ℓ_add_R_rate destIdx)
    Pr_{ let r ←$ᵖ (Fin steps → L) }[
      let f_next := iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩ steps
        h_destIdx h_destIdx_le f_i r
      UDRClose 𝔽q β destIdx h_destIdx_le f_next
    ] ≤ ((steps * next_domain_size) / Fintype.card L) := by
    -- This requires mapping the fiberwise distance to the interleaved code distance
    -- and applying the tensor product proximity gap results from DG25.lean.
  let S_next := sDomain 𝔽q β h_ℓ_add_R_rate destIdx
  let L_card := Fintype.card L
  -- 1. Construct the interleaved word U from f_i
  -- U is a matrix of size m x |S_next|, where row j corresponds to the j-th fiber index.
  let U :=
    preTensorCombine_WordStack 𝔽q β i steps (destIdx := destIdx) h_destIdx h_destIdx_le f_i
  -- 2. Translate Fiber-wise Distance to Interleaved Distance
  -- The fiberwise distance is exactly the minimum Hamming distance between
  -- the columns of U (viewed as vectors in L^m) and the code C^m (interleaved).
  -- Actually, based on Def 4.15/4.16, fiberwiseDistance is the distance of f_i to C_i
  -- but viewed through the fibers. This corresponds to the distance of U to C_next^m.
  let C_next := BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) destIdx
  let C_interleaved := C_next ^⋈ (Fin (2^steps))
  let d_next := BBF_CodeDistance 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (i := destIdx)
  -- 3. Apply Tensor Gap Theorem (Contrapositive)
  -- Theorem 3.6 / Corollary 3.7 states:
  -- If Pr[ multilinearCombine(U, r) is close ] > ε/|L|, then U is close to C_int.
  -- Contrapositive: If U is FAR from C_int, then Pr[ multilinearCombine(U, r) is close ] ≤ ε/|L|.
  -- We identify "close" as distance ≤ e, where e = floor((d_next - 1) / 2).
  let e_prox := (d_next - 1) / 2
  -- Check that "far" hypothesis implies "not close"
  -- h_U_far says 2*dist ≥ d_next.
  -- "Close" means dist ≤ e_prox = (d_next - 1)/2 < d_next/2.
  -- So U is strictly greater than e_prox distance away.
  have h_U_not_UDR_close : ¬ (jointProximityNat (u := U) (e := e_prox) (C := (C_next : Set _))) := by
    apply lemma_4_21_interleaved_word_UDR_far 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i)
      (steps := steps) (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le) (f_i := f_i) (h_far := h_far)

  -- The epsilon for RS codes / Tensor Gaps is typically |S_next| * steps (or similar).
  -- In DG25 Cor 3.7, ε = |S_next|. The bound is ϑ * ε / |L|.
  let ε_gap := Fintype.card S_next

  -- Apply the Tensor Gap Theorem (Corollary 3.7 for RS codes or Theorem 3.6 generic)
  have h_prob_bound :
    Pr_{ let r ←$ᵖ (Fin steps → L) }[ Δ₀(multilinearCombine U r, C_next) ≤ e_prox ]
    ≤ (steps * ε_gap) / L_card := by
    -- Apply contrapositive of h_tensor_gap applied to U
    by_contra h_prob_gt_bound
    let α := Embedding.subtype fun (x : L) ↦ x ∈ S_next
    let C_i_plus_steps := BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) destIdx
    let RS_i_plus_steps := ReedSolomon.code α (2^(ℓ - destIdx.val))

    letI : Nontrivial (RS_i_plus_steps) := by infer_instance

    let h_tensor_gap := reedSolomon_multilinearCorrelatedAgreement_Nat (A := L) (ι := sDomain 𝔽q β h_ℓ_add_R_rate destIdx)
      (α := α)
      (k := 2^(ℓ - destIdx.val))
      (hk := by
        rw [sDomain_card 𝔽q β h_ℓ_add_R_rate (i := destIdx) (h_i := Sdomain_bound (by
          exact h_destIdx_le)), hF₂.out]
        have h_exp : ℓ - destIdx.val ≤ ℓ + 𝓡 - destIdx.val := by
          omega
        exact Nat.pow_le_pow_right (hx := by omega) h_exp
      )
      (e := e_prox) (he := by exact Nat.le_refl _)
      (ϑ := steps) (hϑ_gt_0 := by exact Nat.pos_of_neZero steps)
    -- 3. Apply the theorem to our specific word U
    -- This concludes "U is close" (jointProximityNat)
    let h_U_UDR_close : jointProximityNat (C := C_i_plus_steps) U e_prox :=
      h_tensor_gap U (by
      rw [ENNReal.coe_natCast]
      rw [not_le] at h_prob_gt_bound
      exact h_prob_gt_bound
    )
    exact h_U_not_UDR_close h_U_UDR_close
  -- 4. Connect Folding to Multilinear Combination
  -- Show that `iterated_fold` is exactly `multilinearCombine` of `U`
  -- Lemma 4.9 (iterated_fold_eq_matrix_form) essentially establishes this connection
  -- multilinearCombine U r = Tensor(r) ⬝ U = iterated_fold f r
  have h_fold_eq_combine : ∀ r,
    (iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩ (steps := steps)
      (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le) f_i r) =
    multilinearCombine U r := by
    intro r
    ext y
    rw [iterated_fold_eq_matrix_form 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := ⟨i, by omega⟩) (steps := steps)
      (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le) (f := f_i) (r_challenges := r)]
    unfold localized_fold_matrix_form single_point_localized_fold_matrix_form multilinearCombine
    simp only [dotProduct, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro (rowIdx : Fin (2^steps)) h_rowIdx_univ
    rfl
  -- 5. Conclusion
  -- The event inside the probability is: 2 * dist(folded, C_next) < d_next
  -- This is equivalent to dist(folded, C_next) ≤ (d_next - 1) / 2 = e_prox
  rw [Pr_congr (Q := fun r => Δ₀(multilinearCombine U r, C_next) ≤ e_prox)]
  · exact h_prob_bound
  · intro r
    rw [←h_fold_eq_combine]
    rw [UDRClose_iff_within_UDR_radius]
    have h_e_prox_def : e_prox = Code.uniqueDecodingRadius
      (C := (C_next : Set (sDomain 𝔽q β h_ℓ_add_R_rate destIdx → L))) := by rfl
    rw [h_e_prox_def]

/-!
### Soundness Lemmas (4.20 - 4.25)
-/

open Classical in
/-- **Proposition 4.20** (Bound on Bad Folding Event):
The probability (over random challenges `r`) of the bad folding event is bounded.
Bound: `μ(Eᵢ) ≤ ϑ ⋅ |S⁽ⁱ⁺ϑ⁾| / |L|` (where `μ(R) = Pr_{ let r ←$ᵖ (Fin steps → L) }[ R ]`)
**Case 1: Fiber-wise close** =>
  `μ(Δ⁽ⁱ⁾(f⁽ⁱ⁾, f̄⁽ⁱ⁾) ⊄ Δ_folded_disagreement) ≤ steps · |S⁽ⁱ⁺steps⁾| / |L|`
Proof strategy:
- Show that `∀ y ∈ Δ_fiber, μ(y ∉ Δ_folded_disagreement) ≤ steps / |L|`
- Apply the Union Bound over `y ∈ Δ_fiber`
**Case 2: Fiber-wise far** =>
  μ(`d(fold(f⁽ⁱ⁾, rᵢ', ..., rᵢ₊steps₋₁'), C⁽ⁱ⁺steps⁾) < dᵢ₊steps / 2`) ≤ steps · |S⁽ⁱ⁺steps⁾| / |L|
-/
lemma prop_4_20_bad_event_probability (i : Fin ℓ) (steps : ℕ) [NeZero steps]
    {destIdx : Fin r} (h_destIdx : destIdx.val = i.val + steps) (h_destIdx_le : destIdx ≤ ℓ)
    (f_i : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩) :
    let domain_size := Fintype.card (sDomain 𝔽q β h_ℓ_add_R_rate destIdx)
    Pr_{ let r_challenges ←$ᵖ (Fin steps → L) }[
        foldingBadEvent 𝔽q β (i := ⟨i, by omega⟩) steps h_destIdx h_destIdx_le f_i r_challenges ] ≤
    ((steps * domain_size) / Fintype.card L) := by
  let S_next := sDomain 𝔽q β h_ℓ_add_R_rate destIdx
  let L_card := Fintype.card L

  -- Unfold the event definition to split into the two cases
  unfold foldingBadEvent
  by_cases h_close : fiberwiseClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (i := ⟨i, by omega⟩) (steps := steps) (h_destIdx := h_destIdx)
      (h_destIdx_le := h_destIdx_le) (f := f_i)
  · -- CASE 1: Fiber-wise Close (The main focus of the provided text)
    simp only [h_close, ↓reduceDIte]
    let res := prop_4_20_case_1_fiberwise_close 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i)
      (steps := steps) (h_destIdx := h_destIdx)
      (h_destIdx_le := h_destIdx_le) (f_i := f_i) (h_close := h_close)
    exact res
  · -- CASE 2: Fiber-wise Far
    -- The bad event is that the folded function becomes UDRClose.
    simp only [h_close, ↓reduceDIte]
    -- If fiberwise distance is "far" (≥ d_next / 2),
    -- then the probability of becoming "close" (< d_next / 2) is bounded.
    apply prop_4_20_case_2_fiberwise_far 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (steps := steps)
      (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le) (h_far := h_close)

open Classical in
/-- **Proposition 4.20.2 (Case 1: FiberwiseClose)**.
Incremental bad-event bound for a fixed block start and fixed consumed prefix, under the
block-level close branch.

The fresh event at step `k` is
`¬ E(i, k) ∧ E(i, k+1)` where `E := incrementalFoldingBadEvent`.
-/
lemma prop_4_20_2_case_1_fiberwise_close_incremental
    (block_start_idx : Fin r) {destIdx : Fin r} (k : ℕ) (h_k_lt : k < ϑ)
    (h_destIdx : destIdx = block_start_idx + ϑ) (h_destIdx_le : destIdx ≤ ℓ)
    (f_block_start : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) block_start_idx)
    (r_prefix : Fin k → L)
    (h_block_close : fiberwiseClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := block_start_idx) (steps := ϑ) (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le)
      (f := f_block_start)) :
    let domain_size := Fintype.card (sDomain 𝔽q β h_ℓ_add_R_rate destIdx)
    Pr_{ let r_new ← $ᵖ L }[
      ¬ incrementalFoldingBadEvent 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          (block_start_idx := block_start_idx) (destIdx := destIdx) (k := k)
          (h_k_le := Nat.le_of_lt h_k_lt) (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le)
          (f_block_start := f_block_start) (r_challenges := r_prefix)
      ∧
      incrementalFoldingBadEvent 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (block_start_idx := block_start_idx) (destIdx := destIdx) (k := k + 1)
        (h_k_le := Nat.succ_le_of_lt h_k_lt) (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le)
        (f_block_start := f_block_start)
        (r_challenges := Fin.snoc r_prefix r_new)
    ] ≤
    (domain_size / Fintype.card L) := by
  -- Proof plan:
  -- 1) Expand `incrementalFoldingBadEvent` at `k` and `k+1`.
  -- 2) Use `h_block_close` to fix the close branch in both expansions.
  -- 3) Reduce the fresh event to one-step disagreement vanishing at fixed destination.
  -- 4) Apply Schwartz-Zippel (degree-1 in `r_new`) and union bound over destination points.
  sorry

open Classical in
/-- **Proposition 4.20.2 (Case 2: FiberwiseFar)**.
Incremental bad-event bound for a fixed block start and fixed consumed prefix, under the
block-level far branch.

The fresh event at step `k` is
`¬ E(i, k) ∧ E(i, k+1)` where `E := incrementalFoldingBadEvent`.
-/
lemma prop_4_20_2_case_2_fiberwise_far_incremental
    (block_start_idx : Fin r) {destIdx : Fin r} (k : ℕ) (h_k_lt : k < ϑ)
    (h_destIdx : destIdx = block_start_idx + ϑ) (h_destIdx_le : destIdx ≤ ℓ)
    (f_block_start : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) block_start_idx)
    (r_prefix : Fin k → L)
    (h_block_far : ¬ fiberwiseClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := block_start_idx) (steps := ϑ) (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le)
      (f := f_block_start)) :
    let domain_size := Fintype.card (sDomain 𝔽q β h_ℓ_add_R_rate destIdx)
    Pr_{ let r_new ← $ᵖ L }[
      ¬ incrementalFoldingBadEvent 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          (block_start_idx := block_start_idx) (destIdx := destIdx) (k := k)
          (h_k_le := Nat.le_of_lt h_k_lt) (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le)
          (f_block_start := f_block_start) (r_challenges := r_prefix)
      ∧
      incrementalFoldingBadEvent 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (block_start_idx := block_start_idx) (destIdx := destIdx) (k := k + 1)
        (h_k_le := Nat.succ_le_of_lt h_k_lt) (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le)
        (f_block_start := f_block_start)
        (r_challenges := Fin.snoc r_prefix r_new)
    ] ≤
    (domain_size / Fintype.card L) := by
  -- Proof plan:
  -- 1) Expand `incrementalFoldingBadEvent` at `k` and `k+1`.
  -- 2) Use `h_block_far` to fix the far branch in both expansions.
  -- 3) Rewrite the one-step update as an affine-line fold in interleaved space.
  -- 4) Apply DG25 affine-line proximity gap (ε = |S^{i+ϑ}|), yielding `≤ ε / |L|`.
  sorry

open Classical in
/-- **Proposition 4.20.2 (RBR incremental doom-preservation Probability Bound)**.
For each block and each step `k < ϑ`, with fixed prior challenges in that block, the
probability over the fresh challenge that the incremental bad event flips from false to true is
at most `|S^(i+ϑ)| / |L|`.
-/
lemma prop_4_20_2_incremental_bad_event_probability
    (block_start_idx : Fin r) {destIdx : Fin r} (k : ℕ) (h_k_lt : k < ϑ)
    (h_destIdx : destIdx = block_start_idx + ϑ) (h_destIdx_le : destIdx ≤ ℓ)
    (f_block_start : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) block_start_idx)
    (r_prefix : Fin k → L) :
    let domain_size := Fintype.card (sDomain 𝔽q β h_ℓ_add_R_rate destIdx)
    Pr_{ let r_new ← $ᵖ L }[
      ¬ incrementalFoldingBadEvent 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          (block_start_idx := block_start_idx) (destIdx := destIdx) (k := k)
          (h_k_le := Nat.le_of_lt h_k_lt) (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le)
          (f_block_start := f_block_start) (r_challenges := r_prefix)
      ∧
      incrementalFoldingBadEvent 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (block_start_idx := block_start_idx) (destIdx := destIdx) (k := k + 1)
        (h_k_le := Nat.succ_le_of_lt h_k_lt) (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le)
        (f_block_start := f_block_start)
        (r_challenges := Fin.snoc r_prefix r_new)
    ] ≤
    (domain_size / Fintype.card L) := by
  by_cases h_block_close : fiberwiseClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (i := block_start_idx) (steps := ϑ) (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le)
    (f := f_block_start)
  · exact prop_4_20_2_case_1_fiberwise_close_incremental 𝔽q β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (block_start_idx := block_start_idx)
      (destIdx := destIdx) (k := k) (h_k_lt := h_k_lt) (h_destIdx := h_destIdx)
      (h_destIdx_le := h_destIdx_le) (f_block_start := f_block_start)
      (r_prefix := r_prefix) (h_block_close := h_block_close)
  · exact prop_4_20_2_case_2_fiberwise_far_incremental 𝔽q β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (block_start_idx := block_start_idx)
      (destIdx := destIdx) (k := k) (h_k_lt := h_k_lt) (h_destIdx := h_destIdx)
      (h_destIdx_le := h_destIdx_le) (f_block_start := f_block_start)
      (r_prefix := r_prefix) (h_block_far := h_block_close)

/-!
### Remaining Soundness Statements (Spec.md)
-/

/-! **Proposition 4.22** (Bad events union bound).
The probability that any among the bad events `E₀, E_ϑ, …, E_{ℓ-ϑ}` occurs is bounded by
`2^(ℓ + 𝓡) / |L|`. But this proposition is not used since we do RBR KS analysis -/

open Classical in
omit [CharP L 2] [DecidableEq 𝔽q] hF₂ in
/-- Helper: If `f` and `g` agree on the fiber of `y`, their folds agree at `y`.
NOTE: this might not be needed -/
lemma fold_agreement_of_fiber_agreement (i : Fin ℓ) (steps : ℕ)
    {destIdx : Fin r} (h_destIdx : destIdx.val = i.val + steps) (h_destIdx_le : destIdx ≤ ℓ)
    (f g : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩)
    (r_challenges : Fin steps → L) (y : sDomain 𝔽q β h_ℓ_add_R_rate destIdx) :
    (∀ x,
      iteratedQuotientMap 𝔽q β h_ℓ_add_R_rate (i := ⟨i, by omega⟩) (destIdx := destIdx)
        (k := steps) (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le) x = y →
      f x = g x) →
    (iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩ steps h_destIdx h_destIdx_le f (r_challenges := r_challenges) y =
    (iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩ steps h_destIdx h_destIdx_le g (r_challenges := r_challenges) (y := y))) := by
  intro h_fiber_agree
  -- Expand to matrix form: fold(y) = Tensor(r) * M_y * fiber_vals
  rw [iterated_fold_eq_matrix_form 𝔽q β (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le)]
  rw [iterated_fold_eq_matrix_form 𝔽q β (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le)]
  -- ⊢ localized_fold_matrix_form 𝔽q β i steps h_destIdx h_destIdx_le f r y =
  -- localized_fold_matrix_form 𝔽q β i steps h_destIdx h_destIdx_le g r y
  unfold localized_fold_matrix_form single_point_localized_fold_matrix_form
  simp only
  congr 2
  let left := fiberEvaluations 𝔽q β (i := ⟨i, by omega⟩) (steps := steps) (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le) f y
  let right := fiberEvaluations 𝔽q β (i := ⟨i, by omega⟩) (steps := steps) (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le) g y
  have h_fiber_eval_eq : left = right := by
    unfold left right fiberEvaluations
    ext idx
    let x := qMap_total_fiber 𝔽q β (i := ⟨i, by omega⟩) (steps := steps) (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le) y idx
    have h_x_folds_to_y := generates_quotient_point_if_is_fiber_of_y 𝔽q β (i := ⟨i, by omega⟩) (steps := steps)
          (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le) (x := x) (y := y) (hx_is_fiber := by use idx)
    exact h_fiber_agree x h_x_folds_to_y.symm
  unfold left right at h_fiber_eval_eq
  rw [h_fiber_eval_eq]

omit [CharP L 2] [DecidableEq 𝔽q] hF₂ in
/-- Helper: The disagreement set of the folded functions is a subset of the fiberwise disagreement set. -/
lemma disagreement_fold_subset_fiberwiseDisagreement (i : Fin ℓ) (steps : ℕ)
    {destIdx : Fin r} (h_destIdx : destIdx.val = i.val + steps) (h_destIdx_le : destIdx ≤ ℓ)
    (f g : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩)
    (r_challenges : Fin steps → L) :
    let folded_f := iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩ steps h_destIdx h_destIdx_le f (r_challenges := r_challenges)
    let folded_g := iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩ steps h_destIdx h_destIdx_le g (r_challenges := r_challenges)
    disagreementSet 𝔽q β destIdx (h_i := h_destIdx_le) folded_f folded_g ⊆
    fiberwiseDisagreementSet 𝔽q β (i := ⟨i, by omega⟩) steps h_destIdx h_destIdx_le f g := by
  simp only
  intro y hy_mem
  simp only [disagreementSet, ne_eq, mem_filter, mem_univ, true_and] at hy_mem
  simp only [fiberwiseDisagreementSet, ne_eq, Subtype.exists, mem_filter, mem_univ, true_and]
  -- Contrapositive: If y is NOT in fiberwise disagreement, then f and g agree on fiber.
  -- Then folds must agree (lemma above). Then y is NOT in disagreement set.
  by_contra h_not_in_fiber_diff
  have h_agree_on_fiber : ∀ x,
      iteratedQuotientMap 𝔽q β h_ℓ_add_R_rate (i := ⟨i, by omega⟩) (destIdx := destIdx)
        (k := steps) (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le) x = y →
      f x = g x := by
    intro x hx
    by_contra h_neq
    exact h_not_in_fiber_diff ⟨x, (by simp only [SetLike.coe_mem]), (by simp only [Subtype.coe_eta]; constructor; exact hx; exact h_neq)⟩
  have h_fold_eq := fold_agreement_of_fiber_agreement 𝔽q β i steps h_destIdx h_destIdx_le f g (r_challenges := r_challenges) (y := y) h_agree_on_fiber
  exact hy_mem h_fold_eq

/-- **Lemma 4.24**
For `i*` where `f^(i)` is non-compliant, `f^(i+ϑ)` is UDR-close, and the bad event `E_{i*}`
doesn't occur, the folded function of `f^(i)` is not UDR-close to the UDR-decoded codeword
of `f^(i+ϑ)`. -/
lemma lemma_4_24_dist_folded_ge_of_last_noncompliant (i_star : Fin ℓ) (steps : ℕ) [NeZero steps]
    {destIdx : Fin r} (h_destIdx : destIdx.val = i_star.val + steps) (h_destIdx_le : destIdx ≤ ℓ)
    (f_star : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i_star, by omega⟩)
    (f_next : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) destIdx)
    (r_challenges : Fin steps → L)
    -- 1. f_next is the actual folded function
    -- 2. i* is non-compliant
    (h_not_compliant : ¬ isCompliant 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i_star, by omega⟩ steps h_destIdx h_destIdx_le
       f_star f_next (challenges := r_challenges))
    -- 3. No bad event occurred at i*
    (h_no_bad_event : ¬ foldingBadEvent 𝔽q β (i := ⟨i_star, by omega⟩) steps h_destIdx h_destIdx_le f_star r_challenges)
    -- 4. The next function `f_next` IS close enough to have a unique codeword `f_bar_next`
    (h_next_close : UDRClose 𝔽q β destIdx h_destIdx_le f_next) :
      let f_i_star_folded := iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
       ⟨i_star, by omega⟩ steps h_destIdx h_destIdx_le f_star r_challenges
    -- **CONCLUSION**: 2 * d(f_next, f_bar_next) ≥ d_{i* + steps}
    let f_bar_next := UDRCodeword 𝔽q β destIdx h_destIdx_le (f := f_next) (h_within_radius := h_next_close)
    ¬ pair_UDRClose 𝔽q β destIdx h_destIdx_le f_i_star_folded f_bar_next := by

  -- Definitions for clarity
  let d_next := BBF_CodeDistance 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) destIdx
  let S_next := sDomain 𝔽q β h_ℓ_add_R_rate destIdx
  let C_cur := BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i_star, by omega⟩
  let C_next := BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) destIdx
  let f_bar_next := UDRCodeword 𝔽q β destIdx h_destIdx_le
      (f := f_next) (h_within_radius := h_next_close)
  let f_i_star_folded := iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
       ⟨i_star, by omega⟩ steps h_destIdx h_destIdx_le f_star r_challenges

  have h_f_bar_next_mem_C_next : f_bar_next ∈ C_next := by -- due to definition
    unfold f_bar_next UDRCodeword
    apply UDRCodeword_mem_BBF_Code (i := destIdx) (h_i := h_destIdx_le) (f := f_next) (h_within_radius := h_next_close)

  have h_d_next_ne_0 : d_next ≠ 0 := by
    unfold d_next
    simp [BBF_CodeDistance_eq (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := destIdx) (h_i := h_destIdx_le)]
  let d_fw := fiberwiseDistance 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := ⟨i_star, by omega⟩)
    steps h_destIdx h_destIdx_le (f := f_star)

  -- Split into Case 1 (Close) and Case 2 (Far)
  by_cases h_fw_close : fiberwiseClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (i := ⟨i_star, by omega⟩) (steps := steps) (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le) (f := f_star)
  -- Case 1: Fiberwise Close (d < d_next / 2)
  · let h_fw_dist_lt := h_fw_close -- This gives 2 * fiber_dist < d_next
    -- Define f_bar_star (the unique decoded codeword for f_star) to be the **fiberwise**-close codeword to f_star
    obtain ⟨f_bar_star, ⟨h_f_bar_star_mem, h_f_bar_star_min_card, h_f_bar_star_eq_UDRCodeword⟩, h_unique⟩ := exists_unique_fiberwiseClosestCodeword_within_UDR 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := ⟨i_star, by omega⟩) (steps := steps) (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le) (f := f_star) (h_fw_close := h_fw_close)

    have h_fw_dist_f_g_eq : #(fiberwiseDisagreementSet 𝔽q β ⟨i_star, by omega⟩ steps h_destIdx h_destIdx_le f_star f_bar_star) = d_fw := by
      unfold d_fw
      rw [h_f_bar_star_min_card]; rfl

    let folded_f_bar_star := iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i_star, by omega⟩
       steps h_destIdx h_destIdx_le f_bar_star (r_challenges := r_challenges)

    have h_folded_f_bar_star_mem_C_next : folded_f_bar_star ∈ C_next := by
      unfold folded_f_bar_star
      apply iterated_fold_preserves_BBF_Code_membership 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (i := ⟨i_star, by omega⟩) (steps := steps) (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le) (f := ⟨f_bar_star, h_f_bar_star_mem⟩) (r_challenges := r_challenges)
    -- We prove two inequalities (1) and (2) as per the proof sketch.
    -- **Step (1): Distance between the two codewords in C_next**
    -- First, show that `folded_f_bar_star` ≠ `f_bar_next`.
    -- This follows because `f_star` is NON-COMPLIANT.
    have h_codewords_neq : f_bar_next ≠ folded_f_bar_star := by
      by_contra h_eq
      -- If they were equal, `isCompliant` would be true (satisfying all 3 conditions).
      apply h_not_compliant
      use h_fw_dist_lt -- Condition 1: f_star is close
      use h_next_close -- Condition 2: f_next is close
      -- Condition 3: folded decoding equals next decoding
      simp only
      rw [←h_f_bar_star_eq_UDRCodeword]
      -- ⊢ iterated_fold ⟨i*, ⋯⟩ steps ⋯ f_bar_star r_challenges = UDRCodeword 𝔽q β ⟨i* + steps, ⋯⟩ f_next h_next_close
      exact id (Eq.symm h_eq)

    -- Since they are distinct codewords, their distance is at least `d_next`.
    have h_ineq_1 : Δ₀(f_bar_next, folded_f_bar_star) ≥ d_next := by
      apply Code.pairDist_ge_code_mindist_of_ne (C := (C_next : Set _))
        (u := f_bar_next) (v := folded_f_bar_star)
      · exact h_f_bar_next_mem_C_next
      · exact h_folded_f_bar_star_mem_C_next
      · exact h_codewords_neq

    -- **Step (2): Distance between folded functions**
    -- We know |Δ_fiber(f*, f_bar*)| < d_next / 2 (from fiberwise close hypothesis).
    have h_fiber_dist_lt_half :
        2 * (fiberwiseDisagreementSet 𝔽q β (i := ⟨i_star, by omega⟩) steps h_destIdx h_destIdx_le f_star f_bar_star).card < d_next := by
      rw [Nat.two_mul_lt_iff_le_half_of_sub_one (h_b_pos := by omega)]
      -- ⊢ #(fiberwiseDisagreementSet 𝔽q β i_star steps h_destIdx h_destIdx_le f_star f_bar_star) ≤ (d_next - 1) / 2
      rw [h_fw_dist_f_g_eq]
      rw [←Nat.two_mul_lt_iff_le_half_of_sub_one (h_b_pos := by omega)]
      unfold d_fw
      unfold fiberwiseClose at h_fw_close
      norm_cast at h_fw_close

    -- Lemma 4.18 (Geometric): d(fold(f), fold(g)) ≤ |Δ_fiber(f, g)|
    have h_ineq_2 : 2 * Δ₀(f_i_star_folded, folded_f_bar_star) < d_next := by
      calc
        2 * Δ₀(iterated_fold 𝔽q β ⟨i_star, by omega⟩ steps h_destIdx h_destIdx_le f_star (r_challenges := r_challenges), folded_f_bar_star)
        _ ≤ 2 * (fiberwiseDisagreementSet 𝔽q β (i := ⟨i_star, by omega⟩) steps h_destIdx h_destIdx_le f_star f_bar_star).card := by
          -- Hamming distance is card(disagreementSet)
          -- disagreementSet ⊆ fiberwiseDisagreementSet (Lemma 4.18 Helper)
          apply Nat.mul_le_mul_left
          let res := disagreement_fold_subset_fiberwiseDisagreement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i_star) (steps := steps) (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le) (f := f_star) (g := f_bar_star) (r_challenges := r_challenges)
          simp only at res
          apply Finset.card_le_card
          exact res
        _ < d_next := h_fiber_dist_lt_half

    -- **Final Step: Reverse Triangle Inequality**
    -- d(A, C) ≥ d(B, C) - d(A, B)
    -- We want 2 * d(f_next, f_bar_next) ≥ d_next
    have h_triangle : Δ₀(f_bar_next, folded_f_bar_star) ≤ Δ₀(f_bar_next, f_i_star_folded) + Δ₀(f_i_star_folded, folded_f_bar_star) :=
      hammingDist_triangle f_bar_next f_i_star_folded folded_f_bar_star
    have h_final_bound : 2 * d_next ≤ 2 * Δ₀(f_bar_next, f_i_star_folded) + 2 * Δ₀(f_i_star_folded, folded_f_bar_star) := by
      have h_trans : d_next ≤ Δ₀(f_bar_next, folded_f_bar_star) := h_ineq_1
      have h_mul : 2 * d_next ≤ 2 * Δ₀(f_bar_next, folded_f_bar_star) := Nat.mul_le_mul_left 2 h_trans
      linarith [h_triangle, h_mul]
    -- We have 2*d_next ≤ 2*d(Target) + (something < d_next)
    -- This implies 2*d(Target) > d_next
    -- Or in integer arithmetic: 2*d(Target) ≥ d_next
    rw [hammingDist_comm] at h_final_bound -- align directions
    unfold pair_UDRClose
    simp only [not_lt, ge_iff_le]
    apply le_of_not_gt
    intro h_contra
    -- If 2 * d(target) < d_next:
    -- Sum < d_next + d_next = 2*d_next. Contradiction.
    linarith [h_ineq_2, h_final_bound, h_contra]
  -- **Case 2: Fiberwise Far (d ≥ d_next / 2)**
  · -- In this case, the definition of `foldingBadEvent` (Case 2 branch) simplifies.
    -- The bad event is defined as: UDRClose(f_next).
    unfold foldingBadEvent at h_no_bad_event
    simp only [h_fw_close, ↓reduceDIte] at h_no_bad_event
    -- h_no_bad_event : ¬ UDRClose ...
    -- This means f_next is NOT close to the code C_next.

    -- Definition of not UDRClose: 2 * dist(f_next, C_next) ≥ d_next
    unfold UDRClose at h_no_bad_event
    simp only [not_lt] at h_no_bad_event
    -- ↑(BBF_CodeDistance 𝔽q β destIdx)
    have h_no_bad_event_alt : (d_next : ℕ∞) ≤ 2 * Δ₀(f_i_star_folded, f_bar_next):= by
      calc
        d_next ≤ 2 * Δ₀(f_i_star_folded, (C_next : Set (S_next → L))) := by
          exact h_no_bad_event
        _ ≤ 2 * Δ₀(f_i_star_folded, f_bar_next) := by
          rw [ENat.mul_le_mul_left_iff]
          · simp only [Code.distFromCode_le_dist_to_mem (C := (C_next : Set (S_next → L))) (u :=
              f_i_star_folded) (v := f_bar_next) (hv := h_f_bar_next_mem_C_next)]
          · simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true]
          · simp only [ne_eq, ENat.ofNat_ne_top, not_false_eq_true]

    unfold pair_UDRClose
    simp only [not_lt, ge_iff_le]
    norm_cast at h_no_bad_event_alt

section QueryPhaseSoundnessStatements

variable [hdiv : Fact (ϑ ∣ ℓ)]
variable [SelectableType L]
open QueryPhase

/-- Number of oracle blocks at the end of the protocol. -/
abbrev nBlocks : ℕ := toOutCodewordsCount ℓ ϑ (Fin.last ℓ)

/-- A block index is *bad* if the corresponding folding-compliance check fails. -/
def badBlockProp
    (stmtIn : FinalSumcheckStatementOut (L := L) (ℓ := ℓ))
    (oStmtIn : ∀ j, OracleStatement 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ) j) :
    Fin (nBlocks (ϑ := ϑ) (ℓ := ℓ)) → Prop := fun j =>
  have h_ϑ_le_ℓ : ϑ ≤ ℓ := by apply Nat.le_of_dvd (by exact Nat.pos_of_neZero ℓ) (hdiv.out)
  if hj : j.val + 1 < nBlocks then
    let curDomainIdx : Fin r := ⟨j.val * ϑ, by
      apply lt_r_of_le_ℓ (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (x := j.val * ϑ)
      have h := oracle_index_add_steps_le_ℓ (ℓ := ℓ) (ϑ := ϑ) (i := Fin.last ℓ) (j := j)
      exact (Nat.le_add_right _ _).trans h⟩
    let destIdx : Fin r := ⟨j.val * ϑ + ϑ, by
      apply lt_r_of_le_ℓ (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (x := j.val * ϑ + ϑ)
      exact oracle_index_add_steps_le_ℓ (ℓ := ℓ) (ϑ := ϑ) (i := Fin.last ℓ) (j := j)⟩
    ¬ isCompliant 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (i := curDomainIdx) (steps := ϑ) (destIdx := destIdx)
        (h_destIdx := by rfl) (h_destIdx_le := by
          exact oracle_index_add_steps_le_ℓ (ℓ := ℓ) (ϑ := ϑ) (i := Fin.last ℓ) (j := j))
        (f_i := oStmtIn j)
        (f_i_plus_steps :=
          getNextOracle 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ϑ := ϑ)
            (i := Fin.last ℓ) (oStmt := oStmtIn) (j := j) (hj := by
              simp only [nBlocks] at hj ⊢
              exact hj) (destDomainIdx := destIdx) (h_destDomainIdx := by rfl))
        (challenges :=
          getFoldingChallenges (r := r) (𝓡 := 𝓡) (ϑ := ϑ) (i := Fin.last ℓ)
            stmtIn.challenges (k := j.val * ϑ) (h := by
              exact oracle_index_add_steps_le_ℓ (ℓ := ℓ) (ϑ := ϑ) (i := Fin.last ℓ) (j := j)))
  else
    let j_last := getLastOraclePositionIndex ℓ ϑ (Fin.last ℓ)
    let k := j_last.val * ϑ
    have h_k : k = ℓ - ϑ := by
      dsimp [j_last, k]
      simp only [getLastOraclePositionIndex_last, Nat.sub_mul, Nat.div_mul_cancel (hdiv.out),
        one_mul]
    have hk_add : k + ϑ = ℓ := by
      simp only [h_k] at h_k ⊢
      exact Nat.sub_add_cancel (by omega)
    have hk_le : k ≤ ℓ := by omega
    ¬ isCompliant 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (i := ⟨k, by
          apply lt_r_of_le_ℓ (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (x := k); omega
          ⟩) (steps := ϑ) (destIdx := ⟨k + ϑ, by
          apply lt_r_of_le_ℓ (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (x := k + ϑ); omega
          ⟩)
        (h_destIdx := by rfl)
        (h_destIdx_le := by
          -- k + ϑ = ℓ, so the bound holds
          simp only [hk_add, le_refl])
        (f_i := oStmtIn j_last)
        (f_i_plus_steps := fun _ => stmtIn.final_constant)
        (challenges :=
          getFoldingChallenges (r := r) (𝓡 := 𝓡) (ϑ := ϑ) (i := Fin.last ℓ)
            stmtIn.challenges (k := k) (h := by
              simp only [hk_add, Fin.val_last, le_refl]))

/-- Finset of bad blocks. -/
def badBlockSet
    (stmtIn : FinalSumcheckStatementOut (L := L) (ℓ := ℓ))
    (oStmtIn : ∀ j, OracleStatement 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ) j) :
    Finset (Fin (nBlocks (ℓ := ℓ) (ϑ := ϑ))) :=
  Finset.filter (badBlockProp 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (stmtIn := stmtIn) (oStmtIn := oStmtIn)) Finset.univ

noncomputable def highestBadBlock
    (stmtIn : FinalSumcheckStatementOut (L := L) (ℓ := ℓ))
    (oStmtIn : ∀ j, OracleStatement 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ) j)
    (h_exists : ∃ j : Fin (nBlocks (ℓ := ℓ) (ϑ := ϑ)),
      badBlockProp 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (stmtIn := stmtIn) (oStmtIn := oStmtIn) j) :
    Fin (nBlocks (ℓ := ℓ) (ϑ := ϑ)) :=
  (badBlockSet 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (stmtIn := stmtIn) (oStmtIn := oStmtIn)).max' (by
      rcases h_exists with ⟨j, hj⟩
      refine ⟨j, ?_⟩
      exact (Finset.mem_filter.mpr ⟨by simp, hj⟩))

lemma highestBadBlock_is_bad
    (stmtIn : FinalSumcheckStatementOut (L := L) (ℓ := ℓ))
    (oStmtIn : ∀ j, OracleStatement 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ) j)
    (h_exists : ∃ j : Fin (nBlocks (ℓ := ℓ) (ϑ := ϑ)),
      badBlockProp 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (stmtIn := stmtIn) (oStmtIn := oStmtIn) j) :
    badBlockProp 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (stmtIn := stmtIn) (oStmtIn := oStmtIn)
      (highestBadBlock 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (stmtIn := stmtIn) (oStmtIn := oStmtIn) h_exists) := by
  classical
  have hmem :
      highestBadBlock 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (stmtIn := stmtIn) (oStmtIn := oStmtIn) h_exists
        ∈ badBlockSet 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
            (stmtIn := stmtIn) (oStmtIn := oStmtIn) := by
    -- max' is always a member of the set
    simpa [highestBadBlock] using
      (Finset.max'_mem
        (badBlockSet 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          (stmtIn := stmtIn) (oStmtIn := oStmtIn))
        (by
          rcases h_exists with ⟨j, hj⟩
          refine ⟨j, ?_⟩
          exact (Finset.mem_filter.mpr ⟨by simp, hj⟩)))
  have hmem' := Finset.mem_filter.mp hmem
  exact hmem'.2

lemma not_badBlock_of_lt_highest
    (stmtIn : FinalSumcheckStatementOut (L := L) (ℓ := ℓ))
    (oStmtIn : ∀ j, OracleStatement 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ) j)
    (h_exists : ∃ j : Fin (nBlocks (ℓ := ℓ) (ϑ := ϑ)),
      badBlockProp 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (stmtIn := stmtIn) (oStmtIn := oStmtIn) j)
    {j : Fin (nBlocks (ℓ := ℓ) (ϑ := ϑ))}
    (hlt : highestBadBlock 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (stmtIn := stmtIn) (oStmtIn := oStmtIn) h_exists < j) :
    ¬ badBlockProp 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (stmtIn := stmtIn) (oStmtIn := oStmtIn) j := by
  intro hj_bad
  have hj_mem :
      j ∈ badBlockSet 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (stmtIn := stmtIn) (oStmtIn := oStmtIn) := by
    exact (Finset.mem_filter.mpr ⟨by simp, hj_bad⟩)
  have h_nonempty :
      (badBlockSet 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (stmtIn := stmtIn) (oStmtIn := oStmtIn)).Nonempty := by
    rcases h_exists with ⟨j', hj'⟩
    refine ⟨j', ?_⟩
    exact (Finset.mem_filter.mpr ⟨by simp, hj'⟩)
  have hle : j ≤ highestBadBlock 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (stmtIn := stmtIn) (oStmtIn := oStmtIn) h_exists :=
    by
      -- le_max' takes the membership proof; Nonempty is inferred from max'
      simpa [highestBadBlock] using
        (Finset.le_max' (badBlockSet 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          (stmtIn := stmtIn) (oStmtIn := oStmtIn)) j hj_mem)
  exact not_lt_of_ge hle hlt

/-- Congruence lemma for `UDRClose`: transport along a `Fin r` equality.
Given two `Fin r` indices with the same value and `HEq` functions, `UDRClose` transfers. -/
lemma UDRClose_of_fin_eq {i j : Fin r} (hij : i = j)
    {hi : ↑i ≤ ℓ} {hj : ↑j ≤ ℓ}
    {f : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i}
    {g : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) j}
    (hfg : HEq f g) (h : UDRClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i hi f) :
    UDRClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) j hj g := by
  subst hij; exact eq_of_heq hfg ▸ h

/-- If block `j` is not bad (i.e. it is compliant), then the oracle `oStmtIn j` is UDR-close
at its domain position `j.val * ϑ`. This extracts `fiberwiseClose` from `isCompliant`
(the negation of `badBlockProp`) and converts it to `UDRClose` via `UDRClose_of_fiberwiseClose`. -/
lemma goodBlock_implies_UDRClose
    (stmtIn : FinalSumcheckStatementOut (L := L) (ℓ := ℓ))
    (oStmtIn : ∀ j, OracleStatement 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ) j)
    (j : Fin (nBlocks (ℓ := ℓ) (ϑ := ϑ)))
    (h_good : ¬ badBlockProp 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) stmtIn oStmtIn j)
    {destIdx : Fin r}
    (h_idx : (⟨j.val * ϑ, lt_r_of_le_ℓ (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      ((Nat.le_add_right _ _).trans
        (oracle_index_add_steps_le_ℓ (ℓ := ℓ) (ϑ := ϑ)
          (i := Fin.last ℓ) (j := j)))⟩ : Fin r) = destIdx)
    (h_le : destIdx.val ≤ ℓ) :
    UDRClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      destIdx h_le (fun y => (oStmtIn j) (cast (by rw [h_idx]) y)) := by
  subst h_idx; simp only [cast_eq]
  -- Unfold badBlockProp: it's `¬isCompliant` in both branches.
  simp only [badBlockProp] at h_good
  by_cases h_last : j.val + 1 < nBlocks (ℓ := ℓ) (ϑ := ϑ)
  · -- Intermediate block: badBlockProp = ¬isCompliant
    simp only [h_last, ↓reduceDIte, not_not] at h_good
    obtain ⟨h_fw, _, _⟩ := h_good
    exact UDRClose_of_fiberwiseClose 𝔽q β _ ϑ (by rfl)
      (oracle_index_add_steps_le_ℓ (ℓ := ℓ) (ϑ := ϑ) (i := Fin.last ℓ) (j := j))
      (oStmtIn j) h_fw
  · -- Final block: need getLastOraclePositionIndex = j
    simp only [h_last, ↓reduceDIte, not_not] at h_good
    have h_j_eq : getLastOraclePositionIndex ℓ ϑ (Fin.last ℓ) = j := by
      apply Fin.ext
      simp only [getLastOraclePositionIndex, toOutCodewordsCount_last]
      have h_ge : nBlocks (ℓ := ℓ) (ϑ := ϑ) ≤ j.val + 1 := Nat.le_of_not_gt h_last
      simp only [nBlocks, toOutCodewordsCount_last] at h_ge
      have h_lt : j.val < nBlocks (ℓ := ℓ) (ϑ := ϑ) := j.isLt
      simp only [nBlocks, toOutCodewordsCount_last] at h_lt
      omega
    subst h_j_eq
    obtain ⟨h_fw, _, _⟩ := h_good
    exact UDRClose_of_fiberwiseClose 𝔽q β _ ϑ (by rfl)
      (oracle_index_add_steps_le_ℓ (ℓ := ℓ) (ϑ := ϑ)
        (i := Fin.last ℓ) (j := getLastOraclePositionIndex ℓ ϑ (Fin.last ℓ)))
      (oStmtIn (getLastOraclePositionIndex ℓ ϑ (Fin.last ℓ))) h_fw

open Classical in
lemma prob_uniform_suffix_mem
    (destIdx : Fin r) (h_destIdx_le : destIdx ≤ ℓ)
    (D : Finset (sDomain 𝔽q β h_ℓ_add_R_rate destIdx)) :
    Pr_{ let v ←$ᵖ (sDomain 𝔽q β h_ℓ_add_R_rate 0) }[
      extractSuffixFromChallenge 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (v := v) (destIdx := destIdx) (h_destIdx_le := h_destIdx_le) ∈ D
    ] = (D.card : ENNReal) /
        Fintype.card (sDomain 𝔽q β h_ℓ_add_R_rate destIdx) := by
  classical
  -- Setup
  let S0 := sDomain 𝔽q β h_ℓ_add_R_rate 0
  let Sdest := sDomain 𝔽q β h_ℓ_add_R_rate destIdx
  let steps : ℕ := destIdx.val
  have h_destIdx : destIdx.val = (0 : Fin r).val + steps := by simp [steps]
  let suffix : S0 → Sdest :=
    extractSuffixFromChallenge 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (destIdx := destIdx) (h_destIdx_le := h_destIdx_le)

  -- Express probability via cardinalities
  rw [prob_uniform_eq_card_filter_div_card]
  -- Define the preimage set
  let preimage : Finset S0 := Finset.univ.filter (fun v => suffix v ∈ D)

  -- Each fiber over y has size 2^steps
  let fiberSet : Sdest → Finset S0 := fun y =>
    (Set.image (qMap_total_fiber 𝔽q β (i := (0 : Fin r)) (steps := steps)
      h_destIdx h_destIdx_le (y := y)) (Set.univ : Set (Fin (2 ^ steps)))).toFinset

  have h_fiber_card : ∀ y : Sdest, (fiberSet y).card = 2 ^ steps := by
    intro y
    have h :=
      card_qMap_total_fiber 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (i := (0 : Fin r)) (steps := steps) (h_destIdx := h_destIdx)
        (h_destIdx_le := h_destIdx_le) (y := y)
    -- Convert Fintype.card of the set to Finset.card
    have h_card :
        (fiberSet y).card =
          Fintype.card
            (Set.image (qMap_total_fiber 𝔽q β (i := (0 : Fin r)) (steps := steps)
              h_destIdx h_destIdx_le (y := y)) (Set.univ : Set (Fin (2 ^ steps)))) := by
      classical
      simpa [fiberSet] using
        (Set.toFinset_card
          (s := Set.image (qMap_total_fiber 𝔽q β (i := (0 : Fin r)) (steps := steps)
            h_destIdx h_destIdx_le (y := y)) (Set.univ : Set (Fin (2 ^ steps)))))
    calc
      (fiberSet y).card =
          Fintype.card
            (Set.image (qMap_total_fiber 𝔽q β (i := (0 : Fin r)) (steps := steps)
              h_destIdx h_destIdx_le (y := y)) (Set.univ : Set (Fin (2 ^ steps)))) := h_card
      _ = 2 ^ steps := h

  -- Preimage equals union of fibers over D
  have h_preimage_eq :
      preimage = D.biUnion fiberSet := by
    ext v
    constructor
    · intro hv
      have hv' : suffix v ∈ D := by
        simp only [preimage] at hv ⊢
        exact (Finset.mem_filter.mp hv).2
      -- v is in the fiber of its suffix
      have hv_fiber : v ∈ fiberSet (suffix v) := by
        -- Use the fiber index corresponding to v
        let k :=
          pointToIterateQuotientIndex 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
            (i := (0 : Fin r)) (steps := steps) h_destIdx h_destIdx_le (x := v)
        have hk :
            qMap_total_fiber 𝔽q β (i := (0 : Fin r)) (steps := steps)
              h_destIdx h_destIdx_le (y := suffix v) k = v := by
          -- suffix v is exactly the iterated quotient of v
          have h_eq :
              suffix v =
                iteratedQuotientMap 𝔽q β h_ℓ_add_R_rate (i := (0 : Fin r))
                  (destIdx := destIdx) (k := steps) (h_destIdx := h_destIdx)
                  (h_destIdx_le := h_destIdx_le) (x := v) := by
            simp [suffix, extractSuffixFromChallenge, steps]
          -- Use the characterization of fibers
          exact (is_fiber_iff_generates_quotient_point 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
            (i := (0 : Fin r)) (steps := steps) (h_destIdx := h_destIdx)
            (h_destIdx_le := h_destIdx_le) (x := v) (y := suffix v)).1 h_eq
        -- Show membership in the fiber set
        have : v ∈ Set.image (qMap_total_fiber 𝔽q β (i := (0 : Fin r)) (steps := steps)
              h_destIdx h_destIdx_le (y := suffix v)) (Set.univ : Set (Fin (2 ^ steps))) := by
          refine ⟨k, by simp, hk⟩
        simpa [fiberSet] using this
      -- Put together
      refine Finset.mem_biUnion.mpr ?_
      exact ⟨suffix v, hv', hv_fiber⟩
    · intro hv
      rcases Finset.mem_biUnion.mp hv with ⟨y, hyD, hv_fiber⟩
      -- From v ∈ fiberSet y, deduce suffix v = y
      have hv_fiber' :
          v ∈ Set.image (qMap_total_fiber 𝔽q β (i := (0 : Fin r)) (steps := steps)
            h_destIdx h_destIdx_le (y := y)) (Set.univ : Set (Fin (2 ^ steps))) := by
        simpa [fiberSet] using hv_fiber
      rcases hv_fiber' with ⟨k, hk_mem, hk_eq⟩
      have h_eq :
          y =
            iteratedQuotientMap 𝔽q β h_ℓ_add_R_rate (i := (0 : Fin r))
              (destIdx := destIdx) (k := steps) (h_destIdx := h_destIdx)
              (h_destIdx_le := h_destIdx_le) (x := v) := by
        -- v is in the fiber of y, so y is the iterated quotient of v
        apply generates_quotient_point_if_is_fiber_of_y 𝔽q β
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := (0 : Fin r)) (steps := steps)
          (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le)
          (x := v) (y := y)
        refine ⟨k, ?_⟩
        exact hk_eq.symm
      have : suffix v = y := by
        -- Rewrite suffix v as iteratedQuotientMap
        simpa [suffix, extractSuffixFromChallenge, steps] using h_eq.symm
      -- Conclude v ∈ preimage
      apply Finset.mem_filter.mpr
      constructor
      · simp only [mem_univ]
      · -- suffix v ∈ D
        simpa [this] using hyD

  -- Cardinality of the preimage
  have h_preimage_card : preimage.card = D.card * 2 ^ steps := by
    -- Use disjoint union of fibers
    have h_disjoint :
        ∀ y₁ ∈ D, ∀ y₂ ∈ D, y₁ ≠ y₂ →
          Disjoint (fiberSet y₁) (fiberSet y₂) := by
      intro y₁ hy₁ y₂ hy₂ hy_ne
      -- Apply fiber disjointness lemma
      have h :=
        qMap_total_fiber_disjoint 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          (i := (0 : Fin r)) (steps := steps) (h_destIdx := h_destIdx)
          (h_destIdx_le := h_destIdx_le) (y₁ := y₁) (y₂ := y₂) hy_ne
      simp only [fiberSet] at h ⊢
      exact h
    -- Now compute the card via biUnion
    calc
      preimage.card
          = (D.biUnion fiberSet).card := by simp only [h_preimage_eq]
      _ = ∑ y ∈ D, (fiberSet y).card := by
          exact Finset.card_biUnion (s := D) (t := fiberSet) (h := h_disjoint)
      _ = ∑ y ∈ D, 2 ^ steps := by
          refine Finset.sum_congr rfl ?_
          intro y hy
          simp only [h_fiber_card]
      _ = D.card * 2 ^ steps := by
          simp only [sum_const, smul_eq_mul]

  -- Cardinality of the source domain
  have h_card_S0 : Fintype.card S0 = Fintype.card Sdest * 2 ^ steps := by
    -- Use sDomain_card and the fact |𝔽q| = 2
    have h0 :
        Fintype.card S0 = (Fintype.card 𝔽q) ^ (ℓ + 𝓡 - (0 : Fin r)) := by
      simpa using (sDomain_card 𝔽q β h_ℓ_add_R_rate (i := (0 : Fin r))
        (h_i := Sdomain_bound (by omega)))
    have hdest :
        Fintype.card Sdest = (Fintype.card 𝔽q) ^ (ℓ + 𝓡 - destIdx) := by
      simpa using (sDomain_card 𝔽q β h_ℓ_add_R_rate (i := destIdx)
        (h_i := Sdomain_bound (by omega)))
    -- Rewrite and use pow_add
    have h_add : (ℓ + 𝓡) = (ℓ + 𝓡 - destIdx.val) + destIdx.val := by
      have h_le : destIdx.val ≤ ℓ + 𝓡 := by omega
      exact (Nat.sub_add_cancel h_le).symm
    -- Convert to the desired form
    -- We use hF₂.out to rewrite |𝔽q| = 2
    have hFq : Fintype.card 𝔽q = 2 := hF₂.out
    calc
      Fintype.card S0
          = (Fintype.card 𝔽q) ^ (ℓ + 𝓡) := by
              simpa using h0
      _ = (Fintype.card 𝔽q) ^ ((ℓ + 𝓡 - destIdx.val) + destIdx.val) := by
        exact congrArg (HPow.hPow (Fintype.card 𝔽q)) h_add
      _ = (Fintype.card 𝔽q) ^ (ℓ + 𝓡 - destIdx.val) *
          (Fintype.card 𝔽q) ^ destIdx.val := by
              simp [pow_add]
      _ = Fintype.card Sdest * 2 ^ steps := by
              -- rewrite with hdest and |𝔽q| = 2
          simp only [hFq, hdest, steps]

  -- Finish the probability computation
  have h_card_pos : (2 ^ steps : ENNReal) ≠ 0 := by
    exact_mod_cast (pow_ne_zero steps (by decide : (2 : ℕ) ≠ 0))
  have h_card_fin : (2 ^ steps : ENNReal) ≠ ⊤ := by
    simp
  -- Rewrite in terms of cards
  have h_prob :
      (preimage.card : ENNReal) / Fintype.card S0
        = (D.card : ENNReal) / Fintype.card Sdest := by
    calc
      (preimage.card : ENNReal) / Fintype.card S0
          = ((D.card * 2 ^ steps : ℕ) : ENNReal) /
              (Fintype.card Sdest * 2 ^ steps : ℕ) := by
            simp [h_preimage_card, h_card_S0, preimage, S0, Sdest]
      _ = (D.card : ENNReal) / Fintype.card Sdest := by
            -- Cancel the factor 2^steps
            -- (a*b)/(c*b) = a/c
            simpa [mul_comm, mul_left_comm, mul_assoc] using
              (ENNReal.mul_div_mul_left (a := (D.card : ENNReal))
                (b := (Fintype.card Sdest : ENNReal)) (c := (2 ^ steps : ENNReal))
                h_card_pos h_card_fin)
  simpa [preimage] using h_prob

open Classical in
/-- **Lemma 4.25** (Query rejection from disagreement suffix).

If the verifier's query point `v` has its suffix in the disagreement set between
`fold(f^{(j*\cdot\vartheta)})` and `\bar f^{(j*\cdot\vartheta+\vartheta)}`, then the
single-repetition logical check rejects.

**Hypotheses (following BinaryBasefold.md, Lemma 4.25):**
- `h_no_bad_event`: The bad event at block `j*` didn't occur.
- `h_good_after`: All blocks after `j*` are compliant (maximality of `j*`).
- `h_no_bad_global`: No bad events occur at any block (for the inductive step).

**Proof sketch (per spec):**
- **Base case (i = j*\cdot\vartheta):** `V` computes the fold inline.
  Since the suffix is in the disagreement set, the folded value differs from the codeword.
- **Inductive step (i > j*\cdot\vartheta):** Disagreement propagates using no-bad-events
  and compliance of subsequent blocks.
- **Final step:** The final check fails. -/
theorem lemma_4_25_reject_if_suffix_in_disagreement
    (stmtIn : FinalSumcheckStatementOut (L := L) (ℓ := ℓ))
    (oStmtIn : ∀ j, OracleStatement 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ) j)
    -- Block index j* ∈ {0, ..., ℓ/ϑ - 1} (the highest non-compliant block)
    (j_star : Fin (nBlocks (ℓ := ℓ) (ϑ := ϑ)))
    {destIdx : Fin r} (h_destIdx : destIdx.val = j_star.val * ϑ + ϑ) (h_destIdx_le : destIdx ≤ ℓ)
    (f_next : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) destIdx)
    (r_challenges : Fin ϑ → L)
    (h_no_bad_event : ¬ foldingBadEvent 𝔽q β (i := ⟨j_star.val * ϑ, by omega⟩) ϑ
      h_destIdx h_destIdx_le (oStmtIn j_star) r_challenges)
    (h_next_close : UDRClose 𝔽q β destIdx h_destIdx_le f_next)
    -- All blocks after j* are compliant (consequence of maximality of j*)
    (h_good_after : ∀ j : Fin (nBlocks (ℓ := ℓ) (ϑ := ϑ)), j_star < j →
      ¬ badBlockProp 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) stmtIn oStmtIn j)
    -- No bad events globally (for the inductive step at subsequent blocks)
    (h_no_bad_global : ¬ blockBadEventExistsProp 𝔽q β (stmtIdx := Fin.last ℓ)
      (oracleIdx := OracleFrontierIndex.mkFromStmtIdx (Fin.last ℓ))
      (oStmt := oStmtIn) (challenges := stmtIn.challenges))
    (v : sDomain 𝔽q β h_ℓ_add_R_rate 0) :
    let f_star := oStmtIn j_star
    let folded_f := iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      ⟨j_star.val * ϑ, by omega⟩ ϑ h_destIdx h_destIdx_le f_star (r_challenges := r_challenges)
    let f_bar_next := UDRCodeword 𝔽q β destIdx h_destIdx_le
      (f := f_next) (h_within_radius := h_next_close)
    let v_suffix :=
      iteratedQuotientMap 𝔽q β h_ℓ_add_R_rate (i := (0 : Fin r)) (destIdx := destIdx)
        (k := destIdx.val) (h_destIdx := by simp) (h_destIdx_le := h_destIdx_le) (x := v)
    v_suffix ∈ disagreementSet 𝔽q β destIdx (h_i := h_destIdx_le) folded_f f_bar_next →
    ¬ logical_checkSingleRepetition 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        oStmtIn v stmtIn stmtIn.final_constant := by
  -- Proof per BinaryBasefold.md, Lemma 4.25.
  -- We show: assuming all step conditions pass, the fold value at the last step
  -- disagrees with `final_constant`, contradicting the final step condition.
  -- Introduce the let bindings and hypotheses
  intro f_star folded_f f_bar_next v_suffix h_disagree h_accept

  -- Step 1: Extract the final step condition from h_accept.
  -- At k = ℓ/ϑ (the terminal index), the step condition says:
  --   fold(oStmt(ℓ/ϑ-1), ...)(v_ℓ) = final_constant
  have h_div_pos : ℓ / ϑ > 0 :=
    Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_neZero ℓ) hdiv.out) (Nat.pos_of_neZero ϑ)
  have h_final := h_accept (⟨ℓ / ϑ, by omega⟩ : Fin (ℓ / ϑ + 1))
  unfold logical_stepCondition at h_final
  split_ifs at h_final with h_absurd
  · exact absurd h_absurd (lt_irrefl _)

  -- Step 2: Key inductive invariant — disagreement propagates from j* to the final step.
  -- For each block k from j_star to ℓ/ϑ - 1 (inclusive), conditioned on all guard checks
  -- in h_accept passing, the fold value computed by the verifier at step k disagrees with
  -- the closest codeword at the next level.
  --
  -- At k = ℓ/ϑ - 1 (the last block), this gives:
  --   fold(oStmt(ℓ/ϑ-1), ...)(v_ℓ) ≠ final_constant
  --
  -- The induction proceeds as follows (per the spec):
  -- Base case (k = j*): The fold value = iterated_fold(oStmt(j*), ...)(v_suffix).
  --   Since v_suffix ∈ Δ(fold(oStmt(j*)), f̄), the fold value ≠ f̄(v_suffix).
  -- Inductive step (k > j*): The guard check c_{k*ϑ} = oStmt(k)(v_{k*ϑ}) passes (from h_accept).
  --   Combined with c_{k*ϑ} ≠ f̄^{(k)}(v_{k*ϑ}), we get oStmt(k) ≠ f̄^{(k)} at v_{k*ϑ}.
  --   By ¬E_k (from h_no_bad_global), disagreement propagates through folding.
  --   By compliance (from h_good_after), fold(f̄^{(k)}) = f̄^{(k+1)}.
  --   So fold(oStmt(k))(v_{(k+1)*ϑ}) ≠ f̄^{(k+1)}(v_{(k+1)*ϑ}).
  have h_fold_ne_const :
      logical_computeFoldedValue 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        ⟨ℓ / ϑ - 1, by omega⟩ v stmtIn
        (logical_queryFiberPoints 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          oStmtIn ⟨ℓ / ϑ - 1, by omega⟩ v) ≠
      stmtIn.final_constant := by
    sorry

  -- Step 3: Contradiction.
  exact h_fold_ne_const h_final

open Classical in
/-- **Proposition 4.23** (Query-phase soundness, assuming no bad events).

If any oracle is non-compliant and no bad folding event occurs, then a single
repetition of the proximity check accepts with probability at most
`(1/2) + 1/(2 * 2^𝓡)`. -/
theorem prop_4_23_singleRepetition_proximityCheck_bound
    {h_le : ϑ ≤ ℓ}
    (stmtIn : FinalSumcheckStatementOut (L := L) (ℓ := ℓ))
    (oStmtIn : ∀ j, OracleStatement 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ) j)
    (h_not_consistent : ¬ finalSumcheckStepOracleConsistencyProp 𝔽q β
      (h_le := h_le) (stmtOut := stmtIn) (oStmtOut := oStmtIn))
    (h_no_bad : ¬ blockBadEventExistsProp 𝔽q β (stmtIdx := Fin.last ℓ)
      (oracleIdx := OracleFrontierIndex.mkFromStmtIdx (Fin.last ℓ))
      (oStmt := oStmtIn) (challenges := stmtIn.challenges)) :
    Pr_{ let v ←$ᵖ (sDomain 𝔽q β h_ℓ_add_R_rate 0) }[
      logical_checkSingleRepetition 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        oStmtIn v stmtIn stmtIn.final_constant
    ] ≤ ((1/2 : ℝ≥0) + (1 : ℝ≥0) / (2 * 2^𝓡)) := by
  classical
  -- Extract a concrete bad block from `h_not_consistent`.
  have h_exists_badBlock :
      ∃ j : Fin (nBlocks (ℓ := ℓ) (ϑ := ϑ)),
        badBlockProp 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          (stmtIn := stmtIn) (oStmtIn := oStmtIn) j := by
    -- Define final-step compliance as in `badBlockProp`'s last branch.
    let j_last := getLastOraclePositionIndex ℓ ϑ (Fin.last ℓ)
    let k := j_last.val * ϑ
    have h_k : k = ℓ - ϑ := by
      dsimp [j_last, k]
      simp [getLastOraclePositionIndex_last, Nat.sub_mul, Nat.one_mul, Nat.div_mul_cancel (hdiv.out)]
    have hk_add : k + ϑ = ℓ := by
      simpa [h_k] using (Nat.sub_add_cancel (by omega))
    let final_compliance : Prop :=
      isCompliant 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (i := ⟨k, by
          apply lt_r_of_le_ℓ (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (x := k); omega⟩)
        (steps := ϑ) (destIdx := ⟨k + ϑ, by
          apply lt_r_of_le_ℓ (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (x := k + ϑ); omega⟩)
        (h_destIdx := by rfl) (h_destIdx_le := by simp only [hk_add, le_refl])
        (f_i := oStmtIn j_last)
        (f_i_plus_steps := fun _ => stmtIn.final_constant)
        (challenges :=
          getFoldingChallenges (r := r) (𝓡 := 𝓡) (ϑ := ϑ) (i := Fin.last ℓ)
            stmtIn.challenges (k := k) (h := by simp only [hk_add, Fin.val_last, le_refl]))
    have h_not_and :
        ¬ (oracleFoldingConsistencyProp 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
              (i := Fin.last ℓ) (challenges := stmtIn.challenges) (oStmt := oStmtIn) ∧
            final_compliance) := by
      simpa [finalSumcheckStepOracleConsistencyProp, final_compliance] using h_not_consistent
    by_cases h_final_ok : final_compliance
    · -- Final block compliant: then oracleFoldingConsistencyProp must fail.
      have h_oracle_bad :
          ¬ oracleFoldingConsistencyProp 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
              (i := Fin.last ℓ) (challenges := stmtIn.challenges) (oStmt := oStmtIn) := by
        intro h_oracle_ok
        exact h_not_and ⟨h_oracle_ok, h_final_ok⟩
      have h_oracle_bad' :
          ∃ (j : Fin (nBlocks (ℓ := ℓ) (ϑ := ϑ)))
            (hj : j.val + 1 < nBlocks (ℓ := ℓ) (ϑ := ϑ)),
            ¬ isCompliant 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
              (i := ⟨j.val * ϑ, by
                apply lt_r_of_le_ℓ (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
                exact (Nat.le_add_right _ _).trans
                  (oracle_index_add_steps_le_ℓ (ℓ := ℓ) (ϑ := ϑ)
                    (i := Fin.last ℓ) (j := j))
              ⟩)
              (steps := ϑ)
              (destIdx := ⟨j.val * ϑ + ϑ, by
                apply lt_r_of_le_ℓ (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
                exact oracle_index_add_steps_le_ℓ (ℓ := ℓ) (ϑ := ϑ)
                  (i := Fin.last ℓ) (j := j)
              ⟩)
              (h_destIdx := by rfl)
              (h_destIdx_le := by
                exact oracle_index_add_steps_le_ℓ (ℓ := ℓ) (ϑ := ϑ)
                  (i := Fin.last ℓ) (j := j))
              (f_i := oStmtIn j)
              (f_i_plus_steps :=
                getNextOracle 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ϑ := ϑ)
                  (i := Fin.last ℓ) (oStmt := oStmtIn) (j := j) (hj := by
                    simpa [nBlocks] using hj)
                  (destDomainIdx := ⟨j.val * ϑ + ϑ, by
                    apply lt_r_of_le_ℓ (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
                    exact oracle_index_add_steps_le_ℓ (ℓ := ℓ) (ϑ := ϑ)
                      (i := Fin.last ℓ) (j := j)⟩)
                  (h_destDomainIdx := by rfl))
              (challenges :=
                getFoldingChallenges (r := r) (𝓡 := 𝓡) (ϑ := ϑ) (i := Fin.last ℓ)
                  stmtIn.challenges (k := j.val * ϑ) (h := by
                    exact oracle_index_add_steps_le_ℓ (ℓ := ℓ) (ϑ := ϑ)
                      (i := Fin.last ℓ) (j := j))) := by
        -- Unfold oracleFoldingConsistencyProp and push the negation inside.
        have h_not_forall :
            ¬ (∀ (j : Fin (nBlocks (ℓ := ℓ) (ϑ := ϑ)))
                (hj : j.val + 1 < nBlocks (ℓ := ℓ) (ϑ := ϑ)),
              isCompliant 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
                (i := ⟨j.val * ϑ, by
                  apply lt_r_of_le_ℓ (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
                  exact (Nat.le_add_right _ _).trans
                    (oracle_index_add_steps_le_ℓ (ℓ := ℓ) (ϑ := ϑ)
                      (i := Fin.last ℓ) (j := j))
                ⟩)
                (steps := ϑ)
                (destIdx := ⟨j.val * ϑ + ϑ, by
                  apply lt_r_of_le_ℓ (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
                  exact oracle_index_add_steps_le_ℓ (ℓ := ℓ) (ϑ := ϑ)
                    (i := Fin.last ℓ) (j := j)
                ⟩)
                (h_destIdx := by rfl)
                (h_destIdx_le := by
                  exact oracle_index_add_steps_le_ℓ (ℓ := ℓ) (ϑ := ϑ)
                    (i := Fin.last ℓ) (j := j))
                (f_i := oStmtIn j)
                (f_i_plus_steps :=
                  getNextOracle 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ϑ := ϑ)
                    (i := Fin.last ℓ) (oStmt := oStmtIn) (j := j) (hj := by
                      simpa [nBlocks] using hj)
                    (destDomainIdx := ⟨j.val * ϑ + ϑ, by
                      apply lt_r_of_le_ℓ (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
                      exact oracle_index_add_steps_le_ℓ (ℓ := ℓ) (ϑ := ϑ)
                        (i := Fin.last ℓ) (j := j)⟩)
                    (h_destDomainIdx := by rfl))
                (challenges :=
                  getFoldingChallenges (r := r) (𝓡 := 𝓡) (ϑ := ϑ) (i := Fin.last ℓ)
                    stmtIn.challenges (k := j.val * ϑ) (h := by
                      exact oracle_index_add_steps_le_ℓ (ℓ := ℓ) (ϑ := ϑ)
                        (i := Fin.last ℓ) (j := j)))) := by
          simpa [oracleFoldingConsistencyProp, nBlocks] using h_oracle_bad
        classical
        push_neg at h_not_forall
        exact h_not_forall
      rcases h_oracle_bad' with ⟨j, hj, hbad⟩
      refine ⟨j, ?_⟩
      have hj' : j.val + 1 < ℓ / ϑ := by
        simpa [nBlocks, toOutCodewordsCount_last] using hj
      simpa [badBlockProp, hj', nBlocks, toOutCodewordsCount_last] using hbad
    · -- Final block non-compliant: take the last block.
      refine ⟨j_last, ?_⟩
      have h_no_succ :
          ¬ j_last.val + 1 < nBlocks (ℓ := ℓ) (ϑ := ϑ) := by
        have h_div_pos : 0 < ℓ / ϑ :=
          Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_neZero ℓ) hdiv.out) (Nat.pos_of_neZero ϑ)
        have h_div_pos' : 1 ≤ ℓ / ϑ := Nat.succ_le_iff.mpr h_div_pos
        have h_eq : j_last.val + 1 = nBlocks (ℓ := ℓ) (ϑ := ϑ) := by
          simp [j_last, nBlocks, getLastOraclePositionIndex_last,
            toOutCodewordsCount_last, Nat.sub_add_cancel h_div_pos']
        exact not_lt_of_ge (by simp only [toOutCodewordsCount_last, h_eq, le_refl])
      have h_no_succ' : ¬ j_last.val + 1 < ℓ / ϑ := by
        simpa [nBlocks, toOutCodewordsCount_last] using h_no_succ
      simpa [badBlockProp, h_no_succ', final_compliance, nBlocks, toOutCodewordsCount_last]
        using h_final_ok

  -- Pick the highest bad block.
  let j_star :=
    highestBadBlock 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (stmtIn := stmtIn) (oStmtIn := oStmtIn) h_exists_badBlock
  have h_j_star_bad :
      badBlockProp 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (stmtIn := stmtIn) (oStmtIn := oStmtIn) j_star := by
    simpa using
      (highestBadBlock_is_bad 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (stmtIn := stmtIn) (oStmtIn := oStmtIn) h_exists_badBlock)
  have h_good_of_lt {j : Fin (nBlocks (ℓ := ℓ) (ϑ := ϑ))} (hlt : j_star < j) :
      ¬ badBlockProp 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          (stmtIn := stmtIn) (oStmtIn := oStmtIn) j :=
    not_badBlock_of_lt_highest 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (stmtIn := stmtIn) (oStmtIn := oStmtIn) h_exists_badBlock hlt

  -- Indices for the chosen bad block.
  set i_star : Fin ℓ := ⟨j_star.val * ϑ, by
    simp only [(oracle_block_k_bound (ℓ := ℓ) (ϑ := ϑ) (i := Fin.last ℓ) (j := j_star))]⟩
  set destIdx : Fin r := ⟨j_star.val * ϑ + ϑ, by
    apply lt_r_of_le_ℓ (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    simp only [(oracle_index_add_steps_le_ℓ (ℓ := ℓ) (ϑ := ϑ) (i := Fin.last ℓ) (j := j_star))]⟩
  have h_destIdx : destIdx.val = i_star.val + ϑ := by
    simp [i_star, destIdx]
  have h_destIdx_le : destIdx ≤ ℓ := by
    simpa [destIdx] using
      (oracle_index_add_steps_le_ℓ (ℓ := ℓ) (ϑ := ϑ) (i := Fin.last ℓ) (j := j_star))
  let f_star := oStmtIn j_star
  let r_challenges : Fin ϑ → L :=
    getFoldingChallenges (r := r) (𝓡 := 𝓡) (ϑ := ϑ) (i := Fin.last ℓ)
      stmtIn.challenges (k := j_star.val * ϑ)
      (h := by
        exact oracle_index_add_steps_le_ℓ (ℓ := ℓ) (ϑ := ϑ) (i := Fin.last ℓ) (j := j_star))

  -- No bad event at the chosen block.
  have h_no_bad_event :
      ¬ foldingBadEvent 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (i := ⟨i_star, by omega⟩) ϑ (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le)
        (f_i := f_star) (r_challenges := r_challenges) := by
    intro h_bad
    apply h_no_bad
    refine ⟨j_star, ?_⟩
    have h_branch :
        (oraclePositionToDomainIndex (positionIdx := j_star)).val + ϑ ≤ (Fin.last ℓ).val := by
      simpa using
        (oracle_index_add_steps_le_ℓ (ℓ := ℓ) (ϑ := ϑ) (i := Fin.last ℓ) (j := j_star))
    simpa [foldingBadEventAtBlock, h_branch, r_challenges, i_star, destIdx] using h_bad

  -- Choose `f_next` and extract compliance/UDR-close facts.
  have h_choose :
      ∃ f_next : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) destIdx,
        (¬ isCompliant 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          (i := ⟨i_star, by omega⟩) ϑ (destIdx := destIdx)
          (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le)
          (f_i := f_star) (f_i_plus_steps := f_next) (challenges := r_challenges)) ∧
        UDRClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          destIdx h_destIdx_le f_next := by
    by_cases h_last : j_star.val + 1 < nBlocks (ℓ := ℓ) (ϑ := ϑ)
    · -- Intermediate bad block.
      let f_next :
          OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) destIdx :=
        getNextOracle 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ϑ := ϑ)
          (i := Fin.last ℓ) (oStmt := oStmtIn) (j := j_star) (hj := by
            simpa [nBlocks] using h_last)
          (destDomainIdx := destIdx) (h_destDomainIdx := by rfl)
      have h_not_compliant :
          ¬ isCompliant 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
            (i := ⟨i_star, by omega⟩) ϑ (destIdx := destIdx)
            (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le)
            (f_i := f_star) (f_i_plus_steps := f_next) (challenges := r_challenges) := by
        have h_last' : j_star.val + 1 < ℓ / ϑ := by
          simpa [nBlocks, toOutCodewordsCount_last] using h_last
        simpa [badBlockProp, h_last', nBlocks, toOutCodewordsCount_last, i_star, destIdx]
          using h_j_star_bad
      let j_next : Fin (nBlocks (ℓ := ℓ) (ϑ := ϑ)) := ⟨j_star.val + 1, h_last⟩
      have h_next_good :
          ¬ badBlockProp 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
              (stmtIn := stmtIn) (oStmtIn := oStmtIn) j_next := by
        have hlt : j_star < j_next := by
          exact Fin.lt_iff_val_lt_val.mpr (by simp [j_next])
        exact h_good_of_lt (j := j_next) hlt
      have h_next_close :
          UDRClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
            destIdx h_destIdx_le f_next := by
        have h_j_next_mul_lt_r : ↑j_next * ϑ < r := by
          have : ↑j_next * ϑ = destIdx.val := by simp only [j_next, destIdx]; ring
          omega
        have h_idx : (⟨↑j_next * ϑ, h_j_next_mul_lt_r⟩ : Fin r) = destIdx := by
          apply Fin.ext; simp only [j_next, destIdx]; ring
        have h_udr := goodBlock_implies_UDRClose 𝔽q β stmtIn oStmtIn j_next h_next_good
          (h_idx := h_idx) (h_le := h_destIdx_le)
        exact h_udr
      exact ⟨f_next, h_not_compliant, h_next_close⟩
    · -- Final bad block: `f_next` is the constant oracle.
      let f_next :
          OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) destIdx :=
        fun _ => stmtIn.final_constant
      have h_not_compliant :
          ¬ isCompliant 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
            (i := ⟨i_star, by omega⟩) ϑ (destIdx := destIdx)
            (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le)
            (f_i := f_star) (f_i_plus_steps := f_next) (challenges := r_challenges) := by
        -- Reduce `badBlockProp` to its final-block branch, then rewrite `j_last` to `j_star`.
        have h_j_star_last : j_star = getLastOraclePositionIndex ℓ ϑ (Fin.last ℓ) := by
          apply Fin.ext
          have h_val : j_star.val = (nBlocks (ℓ := ℓ) (ϑ := ϑ)) - 1 := by
            have h_lt : j_star.val < (nBlocks (ℓ := ℓ) (ϑ := ϑ)) := j_star.isLt
            have h_ge : (nBlocks (ℓ := ℓ) (ϑ := ϑ)) ≤ j_star.val + 1 := by
              exact Nat.le_of_not_gt h_last
            omega
          simp [getLastOraclePositionIndex, nBlocks, h_val]
        have h_no_succ' : ¬ j_star.val + 1 < ℓ / ϑ := by
          simp only [nBlocks, toOutCodewordsCount_last] at h_last
          exact h_last
        let j_last : Fin (nBlocks (ℓ := ℓ) (ϑ := ϑ)) :=
          getLastOraclePositionIndex ℓ ϑ (Fin.last ℓ)
        have h_j_star_bad' :
            ¬ isCompliant 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
              (i := ⟨j_last.val * ϑ, by
                apply lt_r_of_le_ℓ (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
                exact (Nat.le_add_right _ _).trans
                  (oracle_index_add_steps_le_ℓ (ℓ := ℓ) (ϑ := ϑ)
                    (i := Fin.last ℓ) (j := j_last))⟩)
              (steps := ϑ)
              (destIdx := ⟨j_last.val * ϑ + ϑ, by
                apply lt_r_of_le_ℓ (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
                exact oracle_index_add_steps_le_ℓ (ℓ := ℓ) (ϑ := ϑ)
                  (i := Fin.last ℓ) (j := j_last)⟩)
              (h_destIdx := by rfl)
              (h_destIdx_le := by
                exact oracle_index_add_steps_le_ℓ (ℓ := ℓ) (ϑ := ϑ)
                  (i := Fin.last ℓ) (j := j_last))
              (f_i := oStmtIn j_last)
              (f_i_plus_steps := fun _ => stmtIn.final_constant)
              (challenges :=
                getFoldingChallenges (r := r) (𝓡 := 𝓡) (ϑ := ϑ) (i := Fin.last ℓ)
                  stmtIn.challenges
                  (k := j_last.val * ϑ) (h := by
                    exact oracle_index_add_steps_le_ℓ (ℓ := ℓ) (ϑ := ϑ)
                      (i := Fin.last ℓ) (j := j_last))) := by
          simp only [badBlockProp, h_no_succ', nBlocks, toOutCodewordsCount_last] at h_j_star_bad
          exact h_j_star_bad
        have h_j_last_to_star : j_last = j_star := by
          simp only [j_last] at h_j_star_last ⊢
          exact h_j_star_last.symm
        have h_j_star_bad'' : ¬ isCompliant 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
            (i := ⟨j_star.val * ϑ, by
              apply lt_r_of_le_ℓ (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
              exact (Nat.le_add_right _ _).trans
                (oracle_index_add_steps_le_ℓ (ℓ := ℓ) (ϑ := ϑ)
                  (i := Fin.last ℓ) (j := j_star))⟩)
            (steps := ϑ)
            (destIdx := ⟨j_star.val * ϑ + ϑ, by
              apply lt_r_of_le_ℓ (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
              exact oracle_index_add_steps_le_ℓ (ℓ := ℓ) (ϑ := ϑ)
                (i := Fin.last ℓ) (j := j_star)⟩)
            (h_destIdx := by rfl)
            (h_destIdx_le := by
              exact oracle_index_add_steps_le_ℓ (ℓ := ℓ) (ϑ := ϑ)
                (i := Fin.last ℓ) (j := j_star))
            (f_i := oStmtIn j_star)
            (f_i_plus_steps := fun _ => stmtIn.final_constant)
            (challenges :=
              getFoldingChallenges (r := r) (𝓡 := 𝓡) (ϑ := ϑ) (i := Fin.last ℓ)
                stmtIn.challenges (k := j_star.val * ϑ) (h := by
                  exact oracle_index_add_steps_le_ℓ (ℓ := ℓ) (ϑ := ϑ)
                    (i := Fin.last ℓ) (j := j_star))) := by
          have h := h_j_star_bad'
          rw [h_j_last_to_star] at h
          exact h
        simp only [i_star, destIdx, f_star, f_next, r_challenges] at h_j_star_bad'' ⊢
        exact h_j_star_bad''
      have h_next_close :
          UDRClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
            destIdx h_destIdx_le f_next := by
        exact
          (constFunc_UDRClose (𝔽q := 𝔽q) (β := β)
            (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := destIdx)
            (h_i := h_destIdx_le) (c := stmtIn.final_constant))
      exact ⟨f_next, h_not_compliant, h_next_close⟩

  rcases h_choose with ⟨f_next, h_not_compliant, h_next_close⟩

  -- Apply Lemma 4.24: folded function is far from the decoded next codeword.
  have h_not_pair :
      let f_i_star_folded :=
        iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          ⟨i_star, by omega⟩ ϑ h_destIdx h_destIdx_le f_star (r_challenges := r_challenges)
      let f_bar_next := UDRCodeword 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        destIdx h_destIdx_le (f := f_next) (h_within_radius := h_next_close)
      ¬ pair_UDRClose 𝔽q β destIdx h_destIdx_le f_i_star_folded f_bar_next := by
    exact
      lemma_4_24_dist_folded_ge_of_last_noncompliant (𝔽q := 𝔽q) (β := β)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i_star := i_star) (steps := ϑ)
        (destIdx := destIdx) (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le)
        (f_star := f_star) (f_next := f_next) (r_challenges := r_challenges)
        h_not_compliant h_no_bad_event h_next_close

  -- Disagreement set between folded oracle and decoded next codeword.
  let folded_f := iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    ⟨i_star, by omega⟩ ϑ h_destIdx h_destIdx_le f_star (r_challenges := r_challenges)
  let f_bar_next := UDRCodeword 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    destIdx h_destIdx_le (f := f_next) (h_within_radius := h_next_close)
  let D :=
    disagreementSet 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      destIdx (h_i := h_destIdx_le) folded_f f_bar_next

  -- From `¬ pair_UDRClose`, derive a lower bound on |D|.
  have h_dist_ge :
      BBF_CodeDistance 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) destIdx ≤
        2 * D.card := by
    have h' :
        BBF_CodeDistance 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) destIdx ≤
          2 * Δ₀(folded_f, f_bar_next) := by
      have h'' := not_lt.mp h_not_pair
        -- f_bar_next = UDRCodeword ... = Classical.choose ..., so types should match
      exact h''
    simp only [D, disagreementSet, hammingDist] at h' ⊢
    exact h'

  -- Acceptance implies the suffix is NOT in the disagreement set.
  have h_accept_subset :
      ∀ v : sDomain 𝔽q β h_ℓ_add_R_rate 0,
        logical_checkSingleRepetition 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          oStmtIn v stmtIn stmtIn.final_constant →
        extractSuffixFromChallenge 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          (v := v) (destIdx := destIdx) (h_destIdx_le := h_destIdx_le) ∉ D := by
    intro v h_accept h_mem
    have h_reject :=
      lemma_4_25_reject_if_suffix_in_disagreement (𝔽q := 𝔽q) (β := β)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (stmtIn := stmtIn) (oStmtIn := oStmtIn)
        (j_star := j_star) (destIdx := destIdx) (h_destIdx := by simp [destIdx])
        (h_destIdx_le := h_destIdx_le) (f_next := f_next)
        (r_challenges := r_challenges) (h_no_bad_event := by
          simp only [i_star, destIdx] at h_no_bad_event; exact h_no_bad_event)
        (h_next_close := h_next_close)
        (h_good_after := fun j hlt => h_good_of_lt hlt)
        (h_no_bad_global := h_no_bad) (v := v)
    exact h_reject (by
      simp only [UDRCodeword, SetLike.mem_coe, uniqueDecodingRadius_eq_floor_div_2, and_imp, D,
        folded_f, f_bar_next] at h_mem ⊢
      exact h_mem) h_accept

  -- Probability bound via monotonicity.
  have h_prob_accept_le :
      Pr_{ let v ←$ᵖ (sDomain 𝔽q β h_ℓ_add_R_rate 0) }[
        logical_checkSingleRepetition 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          oStmtIn v stmtIn stmtIn.final_constant
      ] ≤
      Pr_{ let v ←$ᵖ (sDomain 𝔽q β h_ℓ_add_R_rate 0) }[
        extractSuffixFromChallenge 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          (v := v) (destIdx := destIdx) (h_destIdx_le := h_destIdx_le) ∉ D
      ] := by
    apply prob_mono
    exact h_accept_subset

  -- Evaluate the suffix probability for the complement set.
  have h_prob_suffix_not :
      Pr_{ let v ←$ᵖ (sDomain 𝔽q β h_ℓ_add_R_rate 0) }[
        extractSuffixFromChallenge 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          (v := v) (destIdx := destIdx) (h_destIdx_le := h_destIdx_le) ∉ D
      ] =
      ((Dᶜ).card : ENNReal) /
        Fintype.card (sDomain 𝔽q β h_ℓ_add_R_rate destIdx) := by
    have h :=
      prob_uniform_suffix_mem (𝔽q := 𝔽q) (β := β) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (destIdx := destIdx) (h_destIdx_le := h_destIdx_le) (D := Dᶜ)
    simp only [Finset.mem_compl, D] at h ⊢
    exact h

  -- Bound the complement probability using the distance bound.
  have h_prob_bound :
      ((Dᶜ).card : ENNReal) /
        Fintype.card (sDomain 𝔽q β h_ℓ_add_R_rate destIdx)
        ≤ ((1/2 : ℝ≥0) + (1 : ℝ≥0) / (2 * 2^𝓡)) := by
    -- Set up notation.
    let Sdest := sDomain 𝔽q β h_ℓ_add_R_rate destIdx
    let n : ℕ := Fintype.card Sdest
    have h_card_Sdest :
        n = 2 ^ (ℓ + 𝓡 - destIdx.val) := by
      have h := (sDomain_card 𝔽q β h_ℓ_add_R_rate (i := destIdx)
          (h_i := Sdomain_bound (by omega)))
      simp only [n, hF₂.out] at h ⊢
      exact h
    have h_exp :
        ℓ + 𝓡 - destIdx.val = 𝓡 + (ℓ - destIdx.val) := by
      have h_le : destIdx.val ≤ ℓ := by exact h_destIdx_le
      calc
        ℓ + 𝓡 - destIdx.val = 𝓡 + ℓ - destIdx.val := by omega
        _ = 𝓡 + (ℓ - destIdx.val) := by
          exact Nat.add_sub_assoc h_destIdx_le 𝓡
    have h_n_div :
        n / 2 ^ 𝓡 = 2 ^ (ℓ - destIdx.val) := by
      have h_pos : 0 < 2 ^ 𝓡 := by
        exact pow_pos (by decide : 0 < (2 : ℕ)) _
      calc
        n / 2 ^ 𝓡
            = (2 ^ (ℓ + 𝓡 - destIdx.val)) / 2 ^ 𝓡 := by simp [h_card_Sdest]
        _ = (2 ^ (𝓡 + (ℓ - destIdx.val))) / 2 ^ 𝓡 := by
              simp [h_exp]
        _ = (2 ^ 𝓡 * 2 ^ (ℓ - destIdx.val)) / 2 ^ 𝓡 := by
              simp only [pow_add, ne_eq, Nat.pow_eq_zero, OfNat.ofNat_ne_zero, false_and,
                not_false_eq_true, mul_div_cancel_left₀]
        _ = 2 ^ (ℓ - destIdx.val) := by
          have h := Nat.mul_div_left (2 ^ (ℓ - destIdx.val)) h_pos
          simp only [Nat.mul_comm] at h ⊢
          exact h
    have h_d_next :
        BBF_CodeDistance 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) destIdx =
          n - n / 2 ^ 𝓡 + 1 := by
      have h_d :=
        BBF_CodeDistance_eq (𝔽q := 𝔽q) (β := β)
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := destIdx) (h_i := h_destIdx_le)
      rw [h_n_div, h_card_Sdest]
      exact h_d
    have h_Dcomp_nat :
        2 * (Dᶜ).card ≤ n + n / 2 ^ 𝓡 := by
      have h_card_compl :
          (Dᶜ).card = n - D.card := by
        have h := Finset.card_compl (s := D)
        simp only [Sdest, n] at h ⊢
        exact h
      have h1 :
          2 * (Dᶜ).card = 2 * n - 2 * D.card := by
        simp only [h_card_compl, Nat.mul_sub_left_distrib]
      have h2 :
          2 * n - 2 * D.card ≤ 2 * n -
            BBF_CodeDistance 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) destIdx := by
        exact Nat.sub_le_sub_left h_dist_ge _
      have h3 :
          2 * n -
            BBF_CodeDistance 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) destIdx ≤
            n + n / 2 ^ 𝓡 := by
        simp [h_d_next]; omega
      exact le_trans (by
      simp only [h1] at h2 ⊢
      exact h2) h3

    have h_n_pos : (n : ENNReal) ≠ 0 := by
      -- exact_mod_cast (pow_ne_zero (ℓ + 𝓡 - destIdx.val) (by decide : (2 : ℕ) ≠ 0))
      simp [h_card_Sdest]
    have h_n_fin : (n : ENNReal) ≠ ⊤ := by simp
    have h_Dcomp_ennreal :
        (2 * (Dᶜ).card : ENNReal) ≤
          (n : ENNReal) + ((n / 2 ^ 𝓡 : ℕ) : ENNReal) := by
      exact_mod_cast h_Dcomp_nat
    have h_div_cast :
        ((n / 2 ^ 𝓡 : ℕ) : ENNReal) =
          (n : ENNReal) / (2 ^ 𝓡 : ENNReal) := by
      have h_dvd : (2 ^ 𝓡) ∣ n := by
        refine ⟨2 ^ (ℓ - destIdx.val), ?_⟩
        calc
          n = 2 ^ (ℓ + 𝓡 - destIdx.val) := h_card_Sdest
          _ = 2 ^ (𝓡 + (ℓ - destIdx.val)) := by simp [h_exp]
          _ = 2 ^ 𝓡 * 2 ^ (ℓ - destIdx.val) := by
                simp [pow_add, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
      have h_pos : (2 ^ 𝓡 : ENNReal) ≠ 0 := by
        exact_mod_cast (pow_ne_zero 𝓡 (by decide : (2 : ℕ) ≠ 0))
      have h_pos_nn : (2 ^ 𝓡 : NNReal) ≠ 0 := by
        exact_mod_cast (pow_ne_zero 𝓡 (by decide : (2 : ℕ) ≠ 0))
      have h_div_nn : ((n / 2 ^ 𝓡 : ℕ) : NNReal) = (n : NNReal) / (2 ^ 𝓡 : NNReal) := by
        have h := Nat.cast_div (K := NNReal) h_dvd (by
          simp only [cast_pow, cast_ofNat, ne_eq, h_pos_nn, not_false_eq_true])
        simp only [cast_pow, cast_ofNat] at h
        exact h
      simpa [ENNReal.coe_div h_pos_nn] using (congr_arg (ENNReal.ofNNReal) h_div_nn)

    have h_Dcomp_ennreal' :
        (2 * (Dᶜ).card : ENNReal) ≤
          (n : ENNReal) + (n : ENNReal) / (2 ^ 𝓡 : ENNReal) := by
      simpa [h_div_cast] using h_Dcomp_ennreal

    have h_step :
        ((Dᶜ).card : ENNReal) ≤
          ((2 : ENNReal)⁻¹ * ((n : ENNReal) + (n : ENNReal) / (2 ^ 𝓡 : ENNReal))) := by
      rw [← ENNReal.mul_le_iff_le_inv (by simp) (by simp)]
      simpa [mul_comm] using h_Dcomp_ennreal'

    apply (ENNReal.div_le_iff h_n_pos h_n_fin).2
    have h_rhs :
        ((2 : ENNReal)⁻¹ * ((n : ENNReal) + (n : ENNReal) / (2 ^ 𝓡 : ENNReal))) =
          ((1/2 : ℝ≥0) + (1 : ℝ≥0) / (2 * 2 ^ 𝓡)) * (n : ENNReal) := by
      have h_inv : (2 * 2 ^ 𝓡 : ENNReal)⁻¹ = 2⁻¹ * (2 ^ 𝓡 : ENNReal)⁻¹ := by
        apply ENNReal.mul_inv (Or.inl (by simp)) (Or.inl (by simp))
      simp [mul_add, add_mul, h_inv, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
    simpa [h_rhs] using h_step

  have h_prob_suffix_not' :
      Pr_{ let v ←$ᵖ (sDomain 𝔽q β h_ℓ_add_R_rate 0) }[
        extractSuffixFromChallenge 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          (v := v) (destIdx := destIdx) (h_destIdx_le := h_destIdx_le) ∉ D
      ] ≤ ((1/2 : ℝ≥0) + (1 : ℝ≥0) / (2 * 2^𝓡)) := by
    rw [h_prob_suffix_not]
    exact h_prob_bound

  exact le_trans h_prob_accept_le h_prob_suffix_not'

end QueryPhaseSoundnessStatements

end
end Binius.BinaryBasefold

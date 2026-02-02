/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Quang Dao
-/
import ArkLib.ProofSystem.Binius.BinaryBasefold.Spec

namespace Binius.BinaryBasefold.QueryPhase

/-!
## Query Phase (Final Query Round)
The final verification phase (proximity testing) as an oracle reduction.
(Note that here `B_k` means the boolean hypercube of dimension `k`)

- `V` executes the following querying procedure:
  for `γ` repetitions do
    `V` samples a challenge `v ← B_{ℓ+R}` randomly and sends it to P.
    for `i in {0, ϑ, ..., ℓ-ϑ}` (i.e., taking `ϑ`-sized steps) do
      for each `u` in `B_v`, => gather data for `c_{i+ϑ}`
        `V` sends (query, [f^(i)], (u_0, ..., u_{ϑ-1}, v_{i+ϑ}, ..., v_{ℓ+R-1})) to the oracle.
      if `i > 0` then `V` requires `c_i ?= f^(i)(v_i, ..., v_{ℓ+R-1})`.
      `V` defines `c_{i+ϑ} := fold(f^(i), r'_i, ..., r'_{i+ϑ-1})(v_{i+ϑ}, ..., v_{ℓ+R-1})`.
    `V` requires `c_ℓ ?= c`.
-/
noncomputable section
open OracleSpec OracleComp
open AdditiveNTT Polynomial MvPolynomial

variable {r : ℕ} [NeZero r]
variable {L : Type} [Field L] [Fintype L] [DecidableEq L] [CharP L 2]
  [SampleableType L]
variable (𝔽q : Type) [Field 𝔽q] [Fintype 𝔽q] [DecidableEq 𝔽q]
  [h_Fq_char_prime : Fact (Nat.Prime (ringChar 𝔽q))] [hF₂ : Fact (Fintype.card 𝔽q = 2)]
variable [Algebra 𝔽q L]
variable (β : Fin r → L) [hβ_lin_indep : Fact (LinearIndependent 𝔽q β)]
  [h_β₀_eq_1 : Fact (β 0 = 1)]
variable {ℓ 𝓡 ϑ : ℕ} (γ_repetitions : ℕ) [NeZero ℓ] [NeZero 𝓡] [NeZero ϑ] -- Should we allow ℓ = 0?
variable {h_ℓ_add_R_rate : ℓ + 𝓡 < r} -- ℓ ∈ {1, ..., r-1}
variable {𝓑 : Fin 2 ↪ L}
variable [hdiv : Fact (ϑ ∣ ℓ)]

open scoped NNReal

/-!
## Common Proximity Check Helpers

These functions extract the shared logic between `queryOracleVerifier`
and `queryKnowledgeStateFunction` for proximity testing, allowing code reuse
and ensuring both implementations follow the same logic.
-/

/-- Extract suffix (v_{i+ϑ}, ..., v_{ℓ+R-1}) from challenge v for proximity testing -/
def extractNextSuffixFromChallenge (v : sDomain 𝔽q β h_ℓ_add_R_rate ⟨0, by omega⟩)
    (i : ℕ) (h_i_add_ϑ_le_ℓ : i + ϑ ≤ ℓ) :
    (sDomain 𝔽q β h_ℓ_add_R_rate) ⟨i + ϑ, by omega⟩ := by
  let val := iteratedQuotientMap 𝔽q β h_ℓ_add_R_rate (i:=0) (k:=i + ϑ) (h_bound:=by
      simp only [Fin.coe_ofNat_eq_mod, Nat.zero_mod, zero_add]; exact h_i_add_ϑ_le_ℓ) (x:=v)
  simp only [Fin.val_zero, zero_add] at val
  exact val

/-- This proposition declaratively captures the iterative logic of the verifier. For each repetition
and each folding step, it asserts that the folded value of the function from level `i` must equal
the value of the function from the oracle of the next level `i+ϑ`.
-/
def proximityChecksSpec (γ_challenges :
    Fin γ_repetitions → sDomain 𝔽q β h_ℓ_add_R_rate ⟨0, by omega⟩)
    (oStmt : ∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ) j)
    (fold_challenges : Fin ℓ → L) (final_constant : L) : Prop :=
  ∀ rep : Fin γ_repetitions,
    let v := γ_challenges rep
    -- For all folding levels k = 0, ..., ℓ/ϑ - 1, we track c_cur through the iterations
    ∀ k_val : Fin (ℓ / ϑ),
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
      let k_th_oracleIdx: Fin (toOutCodewordsCount ℓ ϑ (Fin.last ℓ)) :=
        ⟨k_val, by simp only [toOutCodewordsCount, Fin.val_last,
          lt_self_iff_false, ↓reduceIte, add_zero, Fin.is_lt];⟩
      have h: k_th_oracleIdx.val * ϑ = i := by rw [show k_th_oracleIdx.val = k_val.val by rfl]
      have h_i_lt_ℓ: i < ℓ := by
        calc i ≤ ℓ - ϑ := by omega
          _ < ℓ := by
            apply Nat.sub_lt (by exact Nat.pos_of_neZero ℓ) (by exact Nat.pos_of_neZero ϑ)
      -- Create the suffix `(v_{i+ϑ}, ..., v_{ℓ+R-1})` as an element of `S^(i+ϑ)`
      let next_suffix_of_v := extractNextSuffixFromChallenge 𝔽q β (ϑ:=ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) v i h_i_add_ϑ_le_ℓ

      let next_suffix_of_v_fin : Fin (2 ^ (ℓ + 𝓡 - (i + ϑ))) :=
        by simpa [Fin.val_mk] using
          sDomainToFin 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i + ϑ, by omega⟩ (by
              apply Nat.lt_add_of_pos_right_of_le; simp only; omega) next_suffix_of_v

      -- Create the fiber evaluation mapping by querying oracle f^(i) at all fiber points
      let f_i_on_fiber : Fin (2^ϑ) → L := fun u =>
        let x: Fin (2 ^ (ℓ + 𝓡 - i)) := by
          let fiber_point_num_repr := Nat.joinBits (low := u) (high := next_suffix_of_v_fin)
          simp at fiber_point_num_repr
          have h: 2 ^ (ℓ + 𝓡 - (i + ϑ) + ϑ) = 2 ^ (ℓ + 𝓡 - i) := by
            simp only [Nat.ofNat_pos, ne_eq, OfNat.ofNat_ne_one, not_false_eq_true,
              pow_right_inj₀]
            omega
          rw [h] at fiber_point_num_repr
          exact fiber_point_num_repr
        let x_point := finToSDomain 𝔽q β h_ℓ_add_R_rate ⟨i, by omega⟩ (by
            apply Nat.lt_add_of_pos_right_of_le; simp only; omega) x
        oStmt k_th_oracleIdx x_point

      -- Compute the next value using localized fold matrix form
      let cur_challenge_batch : Fin ϑ → L := fun j => fold_challenges ⟨i + j.val, by omega⟩

      let c_next := localized_fold_matrix_form 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (i:=⟨i, by omega⟩) (steps:=ϑ) (h_i_add_steps:=by simp only; omega)
        (r_challenges:=cur_challenge_batch) (y:=next_suffix_of_v) (fiber_eval_mapping:=f_i_on_fiber)

      -- NOTE: at i, we do the consistency check FOR THE NEXT LEVEL (`i + ϑ`):
      -- `c_next ?= f^(i + ϑ)(v_{i + ϑ}, ..., v_{ℓ+R-1})`, the final check is also covered
      let consistency_check : Prop :=
        let oracle_point_idx := extractMiddleFinMask 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          (v:=v) (i:=⟨i, by exact h_i_lt_ℓ⟩) (steps:=ϑ)
        let f_i_next_val :=
          if hk: k_val < ℓ / ϑ - 1 then
            let x_next: sDomain 𝔽q β h_ℓ_add_R_rate ⟨i + ϑ, by
              dsimp only [i]
              let kfin: Fin (ℓ / ϑ - 1) := ⟨k_val, hk⟩
              change kfin * ϑ + ϑ < r
              calc _ ≤ ℓ - ϑ := bIdx_mul_ϑ_add_x_lt_ℓ_sub_ϑ (bIdx:=kfin) (x:=ϑ) (hx:=Nat.le_refl ϑ)
                _ < ℓ := rounds_sub_steps_lt
                _ < r := ℓ_lt_r (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
            ⟩ := next_suffix_of_v
            oStmt ⟨k_val + 1, by rw [toOutCodewordsCount_last ℓ ϑ]; omega⟩ ⟨x_next, by
              simp only
              have h_index: (k_val + 1) * ϑ = i + ϑ := by
                dsimp only [i]; rw [Nat.add_mul, Nat.one_mul]
              rw! [h_index]
              exact Submodule.coe_mem x_next
            ⟩
          else final_constant
        c_next = f_i_next_val
      consistency_check

/-- RBR knowledge error for the query phase.
Proximity testing error rate: `(1/2 + 1/(2 * 2^𝓡))^γ` -/
def queryRbrKnowledgeError := fun _ : (pSpecQuery 𝔽q β γ_repetitions
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).ChallengeIdx =>
  ((1/2 : ℝ≥0) + (1 : ℝ≥0) / (2 * 2^𝓡))^γ_repetitions

/-- Oracle query helper: query a committed codeword at a given domain point.
    Restricted to codeword indices where the oracle range is L. -/
def queryCodeword (j : Fin (toOutCodewordsCount ℓ ϑ (Fin.last ℓ)))
    (point : (sDomain 𝔽q β h_ℓ_add_R_rate) ⟨j.val * ϑ,
      by calc
          j.val * ϑ < ℓ := by exact toCodewordsCount_mul_ϑ_lt_ℓ ℓ ϑ (Fin.last ℓ) j
          _ < r := by omega⟩) :
  OracleComp ([OracleStatement 𝔽q β (ϑ:=ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (
  Fin.last ℓ)]ₒ) L :=
      OracleComp.lift <| by
        simpa using
          OracleSpec.query
            (spec := [OracleStatement 𝔽q β (ϑ:=ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ)]ₒ)
            ⟨j, by omega⟩
            (by exact point)

section FinalQueryRoundIOR

/-!
### IOR Implementation for the Final Query Round
-/

/-- The oracle prover for the final query phase (equivalent to regular prover). -/
noncomputable def queryOracleProver :
  OracleProver
    (oSpec := []ₒ)
    (StmtIn := FinalSumcheckStatementOut (L:=L) (ℓ:=ℓ))
    (OStmtIn := OracleStatement 𝔽q β (ϑ:=ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (
    Fin.last ℓ))
    (WitIn := Unit)
    (StmtOut := Bool)
    (OStmtOut := fun _ : Empty => Unit)
    (WitOut := Unit)
    (pSpec := pSpecQuery 𝔽q β γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate)) where
  PrvState := fun
    | 0 => Unit
    | 1 => Unit
  input := fun _ => ()

  sendMessage
  | ⟨0, h⟩ => nomatch h

  receiveChallenge
  | ⟨0, _⟩ => fun _ => do
    -- V sends all γ challenges v₁, ..., v_γ
    pure (fun _challenges => ())

  output := fun _ => do -- The prover always returns true since it's honest
    pure (⟨true, fun _ => ()⟩, ())

noncomputable def queryOracleVerifier :
  OracleVerifier
    (oSpec := []ₒ)
    (StmtIn := FinalSumcheckStatementOut (L:=L) (ℓ:=ℓ))
    (OStmtIn := OracleStatement 𝔽q β (ϑ:=ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (
    Fin.last ℓ))
    (StmtOut := Bool)
    (OStmtOut := fun _ : Empty => Unit)
    (pSpec := pSpecQuery 𝔽q β γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate)) where
  verify := fun (stmt: FinalSumcheckStatementOut (L:=L) (ℓ:=ℓ))
    (challenges: (pSpecQuery 𝔽q β γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).Challenges) => do
    -- Get all γ challenges from the second message (final sumcheck already checked earlier).
    let c := stmt.final_constant
    let fold_challenges : Fin γ_repetitions → sDomain 𝔽q β h_ℓ_add_R_rate 0 :=
      challenges ⟨0, by rfl⟩

    -- 4. Proximity testing for all γ repetitions.
    -- This implements the specification defined in proximityChecksSpec
    for rep in (List.finRange γ_repetitions) do
      let mut c_cur : L := 0 -- Placeholder, will be initialized in the first iteration.
      let v := fold_challenges rep

      for k_val in List.finRange (ℓ / ϑ) do
        let i := k_val * ϑ
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
        let k_th_oracleIdx: Fin (toOutCodewordsCount ℓ ϑ (Fin.last ℓ)) :=
          ⟨k_val, by simp only [toOutCodewordsCount, Fin.val_last,
            lt_self_iff_false, ↓reduceIte, add_zero, Fin.is_lt];⟩
        have h: k_th_oracleIdx.val * ϑ = i := by rw [show k_th_oracleIdx.val = k_val by rfl]
        have h_i: i = k_val * ϑ := by omega
        have h_i_lt_ℓ: i < ℓ := by
          calc i ≤ ℓ - ϑ := by omega
            _ < ℓ := by
              apply Nat.sub_lt (by exact Nat.pos_of_neZero ℓ) (by exact Nat.pos_of_neZero ϑ)
        have h_i_plus_ϑ: i + ϑ = (k_val + 1) * ϑ := by
          rw [h_i]
          conv_lhs => enter [2]; rw [←one_mul ϑ]
          rw [add_mul]

        -- Create the suffix `(v_{i+ϑ}, ..., v_{ℓ+R-1})` as an element of `S^(i+ϑ)`
        let next_suffix_of_v := extractNextSuffixFromChallenge 𝔽q β (ϑ:=ϑ)
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) v i h_i_add_ϑ_le_ℓ

        let next_suffix_of_v_fin : Fin (2 ^ (ℓ + 𝓡 - (i + ϑ))) :=
          by simpa [Fin.val_mk] using
            sDomainToFin 𝔽q β h_ℓ_add_R_rate ⟨i + ϑ, by omega⟩ (by
                apply Nat.lt_add_of_pos_right_of_le; simp only; omega) next_suffix_of_v

        /- Create the list of fiber points of `next_suffix_of_v` in `S^(i)`, which have the
        form `(u_0, ..., u_{ϑ-1}, v_{i+v}, ..., v_{ℓ+R-1})`, which are actually result of the
        fiber mapping: `(q^(i+ϑ-1) ∘ ... ∘ q^(i))⁻¹({(v_{i+ϑ}, ..., v_{ℓ+R-1})})`,
        by querying the oracle `f^(i)` on all fiber points using queryCodeword helper. -/
        let f_i_on_fiber ← (List.finRange (2^ϑ)).mapM (fun (u : Fin (2^ϑ)) => do
          let x: Fin (2 ^ (ℓ + 𝓡 - i)) := by
            let fiber_point_num_repr := Nat.joinBits (low := u) (high := next_suffix_of_v_fin)
            simp at fiber_point_num_repr
            have h: 2 ^ (ℓ + 𝓡 - (i + ϑ) + ϑ) = 2 ^ (ℓ + 𝓡 - i) := by
              simp only [Nat.ofNat_pos, ne_eq, OfNat.ofNat_ne_one, not_false_eq_true,
                pow_right_inj₀]
              omega
            rw [h] at fiber_point_num_repr
            exact fiber_point_num_repr
          let x_point := finToSDomain 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩ (by
              apply Nat.lt_add_of_pos_right_of_le; simp only; omega) x
          queryCodeword 𝔽q β (ϑ:=ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
            (j := k_th_oracleIdx) (point := x_point)
        )

        have h_f_i_on_fiber_length: f_i_on_fiber.length = 2 ^ ϑ := by
          sorry

        if i > 0 then
          -- cᵢ ?= f^(i)(vᵢ, ..., v_{ℓ+R-1})
          let oracle_point_idx := extractMiddleFinMask 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
            (v:=v) (i:=⟨i, by exact h_i_lt_ℓ⟩) (steps:=ϑ)

          let f_i_val := f_i_on_fiber.get ⟨oracle_point_idx.val, by
            rw [h_f_i_on_fiber_length]; exact oracle_point_idx.isLt⟩
          unless c_cur = f_i_val do
            return false

        let cur_challenge_batch : Fin ϑ → L := fun j => stmt.challenges ⟨i +
        j.val, by rw [Fin.val_last]; omega⟩

        let c_next := localized_fold_matrix_form 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          (i:=⟨i, by omega⟩) (steps:=ϑ) (h_i_add_steps:=by simp only; omega)
          (r_challenges:=cur_challenge_batch) (y:=next_suffix_of_v)
          (fiber_eval_mapping:=fun idx => f_i_on_fiber.get ⟨idx, by
            rw [h_f_i_on_fiber_length]; omega⟩)

        -- Update c_prev_iter for the next loop iteration's check.
        c_cur := c_next

      -- Final check after all folding: `c_ℓ ?= c`.
      unless c_cur = c do
        return false

  -- If all repetitions and all checks pass, the verifier accepts.
    return true
  embed := ⟨Empty.elim, fun a b => Empty.elim a⟩
  hEq := fun i => Empty.elim i

/-- The oracle reduction for the final query phase. -/
noncomputable def queryOracleReduction :
  OracleReduction
    (oSpec := []ₒ)
    (StmtIn := FinalSumcheckStatementOut (L:=L) (ℓ:=ℓ))
    (OStmtIn := OracleStatement 𝔽q β (ϑ:=ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (
    Fin.last ℓ))
    (WitIn := Unit)
    (StmtOut := Bool)
    (OStmtOut := fun _ : Empty => Unit)
    (WitOut := Unit)
    (pSpec := pSpecQuery 𝔽q β γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate)) where
  prover := queryOracleProver 𝔽q β (ϑ:=ϑ) γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
  verifier := queryOracleVerifier 𝔽q β (ϑ:=ϑ) γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate)

/-- The final query round as an `OracleProof` (since it outputs Bool and no oracle statements). -/
noncomputable def queryOracleProof : OracleProof
    (oSpec := []ₒ)
    (Statement := FinalSumcheckStatementOut (L:=L) (ℓ:=ℓ))
    (OStatement := OracleStatement 𝔽q β (ϑ:=ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (
    Fin.last ℓ))
    (Witness := Unit)
    (pSpec := pSpecQuery 𝔽q β γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate)) :=
  queryOracleReduction 𝔽q β (ϑ:=ϑ) γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate)

/-- Perfect completeness for the final query round (using the oracle queryProof). -/
theorem queryOracleProof_perfectCompleteness {σ : Type}
  (init : ProbComp σ)
  (impl : QueryImpl []ₒ (StateT σ ProbComp))
  (hInit : init.neverFails) :
  OracleProof.perfectCompleteness
    (pSpec := pSpecQuery 𝔽q β γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
    (relation := finalSumcheckRelOut 𝔽q β (ϑ:=ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
    (oracleProof := queryOracleProof 𝔽q β (ϑ:=ϑ) γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
    (init := init)
    (impl := impl) := by
  unfold OracleProof.perfectCompleteness
  intro stmtIn witIn h_relIn
  sorry

open scoped NNReal

/-- The round-by-round extractor for the query phase.
Since f^(0) is always available, we can invoke the extractMLP function directly. -/
noncomputable def queryRbrExtractor :
  Extractor.RoundByRound []ₒ
    (StmtIn := (FinalSumcheckStatementOut (L:=L) (ℓ:=ℓ))
      × (∀ j, OracleStatement 𝔽q β (ϑ:=ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ) j))
    (WitIn := Unit)
    Unit
    (pSpec := pSpecQuery 𝔽q β γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
    (fun _ => Unit) where
  eqIn := rfl
  extractMid := fun _ _ _ witMidSucc => witMidSucc
  extractOut := fun _ _ _ => ()

def queryKStateProp {m : Fin (1 + 1)}
  (tr : ProtocolSpec.Transcript m
    (pSpecQuery 𝔽q β γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate)))
  (stmt : FinalSumcheckStatementOut (L := L) (ℓ := ℓ))
  (witMid : Unit)
  (oStmt : ∀ j, OracleStatement 𝔽q β (ϑ := ϑ)
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ) j) : Prop :=
if h0 : m.val = 0 then
  -- Same as last Kstate of finalSumcheck reduction
  Binius.BinaryBasefold.finalSumcheckRelOutProp 𝔽q β (input:=⟨⟨stmt, oStmt⟩, witMid⟩)
else
    let r := stmt.ctx.t_eval_point
    let s := stmt.ctx.original_claim
    let challenges : Fin ℓ → L := stmt.challenges
    let tr_so_far := (pSpecQuery 𝔽q β γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).take m m.is_le
    let chalIdx : tr_so_far.ChallengeIdx := ⟨⟨0,
      Nat.lt_of_succ_le (by omega)⟩, by simp only [Nat.reduceAdd]; rfl⟩
    let γ_challenges : Fin γ_repetitions → sDomain 𝔽q
      β h_ℓ_add_R_rate ⟨0, by omega⟩ := ((ProtocolSpec.Transcript.equivMessagesChallenges (k:=m)
        (pSpec:=pSpecQuery 𝔽q β γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
        tr).2 chalIdx)
    let fold_challenges := stmt.challenges
    -- Checks available after message 1 (V -> P: γ challenges)
    let proximityTestsCheck : Prop :=
      proximityChecksSpec 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (ϑ:=ϑ) γ_repetitions γ_challenges oStmt fold_challenges stmt.final_constant
    proximityTestsCheck

/-- The knowledge state function for the query phase -/
noncomputable def queryKnowledgeStateFunction {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
  (queryOracleVerifier 𝔽q β (ϑ:=ϑ) γ_repetitions).KnowledgeStateFunction init impl
  (relIn := finalSumcheckRelOut 𝔽q β (ϑ:=ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
  (relOut := acceptRejectOracleRel)
  (extractor := queryRbrExtractor 𝔽q β (ϑ:=ϑ) γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate)) where
  toFun := fun m ⟨stmt, oStmt⟩ tr witMid =>
    queryKStateProp 𝔽q β (ϑ:=ϑ) (γ_repetitions:=γ_repetitions)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (m:=m) (tr:=tr) (stmt:=stmt) (witMid:=witMid) (oStmt:=oStmt)
  toFun_empty := fun stmt witMid => by simp only; rfl
  toFun_next := fun m hDir stmt tr msg witMid h => by
    sorry
  toFun_full := fun stmt tr witOut h => by
    sorry

/-- Round-by-round knowledge soundness for the oracle verifier (query phase) -/
theorem queryOracleVerifier_rbrKnowledgeSoundness [Fintype L] {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    (queryOracleVerifier 𝔽q β (ϑ:=ϑ) γ_repetitions).rbrKnowledgeSoundness init impl
    (relIn := finalSumcheckRelOut 𝔽q β (ϑ:=ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
    (relOut := acceptRejectOracleRel)
    (rbrKnowledgeError := queryRbrKnowledgeError 𝔽q β γ_repetitions
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate)) := by
  use fun _ => Unit
  use queryRbrExtractor 𝔽q β (ϑ:=ϑ) γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
  use queryKnowledgeStateFunction 𝔽q β (ϑ:=ϑ) γ_repetitions init impl
  intro stmtIn witIn prover j
  sorry

end FinalQueryRoundIOR
end
end Binius.BinaryBasefold.QueryPhase

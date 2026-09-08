/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.OracleReduction.Security.Basic
import ArkLib.OracleReduction.Security.Implications
import ArkLib.OracleReduction.Composition.Sequential.Append
import ArkLib.Data.MvPolynomial.SchwartzZippelCounting
import ArkLib.ProofSystem.Logup.Algebra
import ArkLib.ProofSystem.Logup.Security.Common
import ArkLib.ToVCVio.OracleComp.Coercions.SubSpec

/-!
# LogUp Soundness Bounds

Error budgets and reusable probability bounds used by the LogUp soundness proof.
-/

open scoped NNReal BigOperators

namespace Logup

section Soundness

variable {ι : Type} (oSpec : OracleSpec ι)
variable (F : Type) [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
variable (n M : ℕ)
variable (params : ProtocolParams M)
variable {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))

/-- Soundness error of the outer LogUp reduction.

The reduction samples the challenge `x` that turns the rational lookup identity into a polynomial
identity of degree at most `|H| * (M + 1) - 1`, the Lagrange-kernel point `z` that must not hide a
nonzero multilinear domain identity, and the batching scalar that combines the `K + 1` zero-sum
claims into one.

The first two terms are an unconditional union bound over denominator poles and roots of the
cleared lookup identity. The `params.numGroups * n / |F|` term bounds the chance that the sampled
Lagrange-kernel point hides one of the nonzero domain identities. This is the same bad event that
appears as the `ε₂` term in the paper, but it is charged to the outer phase here because this phase
samples the point. -/
noncomputable def logupOuterSoundnessError (F : Type) [Fintype F] (n M : ℕ)
    (params : ProtocolParams M) : ℝ≥0 :=
  ((((M + 1) * Fintype.card (Fin n → Fin 2) : ℕ) : ℝ≥0) /
      (Fintype.card F : ℝ≥0)) +
    ((((M + 1) * Fintype.card (Fin n → Fin 2) - 1 : ℕ) : ℝ≥0) /
      (Fintype.card F : ℝ≥0)) +
    (((params.numGroups * n : ℕ) : ℝ≥0) / (Fintype.card F : ℝ≥0)) +
    ((1 : ℕ) : ℝ≥0) / (Fintype.card F : ℝ≥0)

/-- Error budget for the final LogUp point-check phase.

The final verifier has no fresh challenges: once the sumcheck final claim and retained oracles are
fixed, it either accepts or rejects deterministically. Its phase error is therefore `0`. The
Lagrange-kernel bad event is already proved in `logupOuterSoundnessError`, where that random point
is sampled. -/
noncomputable def logupFinalCheckSoundnessError : ℝ≥0 :=
  0

/-- Full LogUp soundness error: the sum of the outer, embedded-sumcheck, and final-check errors.

The outer contribution includes the probability that the sampled Lagrange-kernel point hides a
nonzero domain identity. The final-check contribution is `0`, because that phase has no fresh
random challenges. -/
noncomputable def logupSoundnessError (F : Type) [Fintype F] (n M : ℕ) (params : ProtocolParams M)
    (sumcheckSoundnessError : ℝ≥0) : ℝ≥0 :=
  logupOuterSoundnessError F n M params + sumcheckSoundnessError +
    logupFinalCheckSoundnessError

/-- The generic Sumcheck soundness error used by LogUp's embedded sumcheck phase. -/
noncomputable def logupSumcheckSoundnessError (F : Type) [CommSemiring F] [Fintype F] (n M : ℕ)
    (params : ProtocolParams M) : ℝ≥0 :=
  ∑ _ : (Sumcheck.Spec.pSpec F (logupSumcheckDegree M params) n).ChallengeIdx,
    ((logupSumcheckDegree M params : ℕ) : ℝ≥0) / (Fintype.card F : ℝ≥0)

omit [SampleableType F] in
/-- A false input supplies a missing lookup value whose lookup count is positive and nonzero in
the field, while its table count is zero. -/
theorem exists_missing_column_with_nonzero_lookup_count
    (stmt : StmtIn F n M) (oStmt : ∀ i, OStmtIn F n M i)
    (hnotInput : ((stmt, oStmt), ()) ∉ inputRelation F n M) :
    ∃ i : Fin M, ∃ u : Fin n → Fin 2,
      (∀ v : Fin n → Fin 2,
        MvPolynomial.toEvalsZeroOne (oStmt (.column i)).1 u ≠
          MvPolynomial.toEvalsZeroOne (oStmt .table).1 v) ∧
      0 < lookupMultiplicityCount
          (fun j => MvPolynomial.toEvalsZeroOne (oStmt (.column j)).1)
          (MvPolynomial.toEvalsZeroOne (oStmt (.column i)).1 u) ∧
      (lookupMultiplicityCount
          (fun j => MvPolynomial.toEvalsZeroOne (oStmt (.column j)).1)
          (MvPolynomial.toEvalsZeroOne (oStmt (.column i)).1 u) : F) ≠ 0 ∧
      tableMultiplicityCount (MvPolynomial.toEvalsZeroOne (oStmt .table).1)
          (MvPolynomial.toEvalsZeroOne (oStmt (.column i)).1 u) = 0 := by
  have hmissing_exists :
      ∃ i : Fin M, ∃ u : Fin n → Fin 2, ∀ v : Fin n → Fin 2,
        MvPolynomial.toEvalsZeroOne (oStmt (.column i)).1 u ≠
          MvPolynomial.toEvalsZeroOne (oStmt .table).1 v := by
    unfold inputRelation at hnotInput
    simpa [not_forall, not_exists] using hnotInput
  obtain ⟨i, u, hmissing⟩ :=
    hmissing_exists
  let table := MvPolynomial.toEvalsZeroOne (oStmt .table).1
  let columns : Fin M → (Fin n → Fin 2) → F :=
    fun j => MvPolynomial.toEvalsZeroOne (oStmt (.column j)).1
  let a := columns i u
  have hpos : 0 < lookupMultiplicityCount columns a :=
    lookupMultiplicityCount_pos_of_column_value (F := F) (n := n) (M := M) columns i u
  have hcast : (lookupMultiplicityCount columns a : F) ≠ 0 :=
    lookupMultiplicityCount_cast_ne_zero_of_pos (F := F) (n := n) (M := M)
      stmt.charLarge columns hpos
  have htable :
    tableMultiplicityCount table a = 0 :=
    tableMultiplicityCount_eq_zero_of_missing (F := F) (n := n) table
      (a := a) hmissing
  exact ⟨i, u, hmissing, hpos, hcast, htable⟩

set_option linter.unusedDecidableInType false in
omit [SampleableType F] in
/-- Contrapositive of LogUp's set-inclusion lemma for an arbitrary malicious multiplicity oracle:
if the lookup input is false, the cleared rational identity is not the zero polynomial. -/
theorem clearedLookupIdentity_ne_zero_of_not_input
    (stmt : StmtIn F n M) (oStmt : ∀ i, OStmtIn F n M i)
    (multiplicity : (Fin n → Fin 2) → F)
    (hnotInput : ((stmt, oStmt), ()) ∉ inputRelation F n M) :
    clearedLookupIdentity
        (MvPolynomial.toEvalsZeroOne (oStmt .table).1)
        (fun i => MvPolynomial.toEvalsZeroOne (oStmt (.column i)).1)
        multiplicity ≠ 0 := by
  classical
  let table := MvPolynomial.toEvalsZeroOne (oStmt .table).1
  let columns : Fin M → (Fin n → Fin 2) → F :=
    fun i => MvPolynomial.toEvalsZeroOne (oStmt (.column i)).1
  obtain ⟨i, u, hmissing, hpos, hcast, _htable⟩ :=
    exists_missing_column_with_nonzero_lookup_count (F := F) (n := n) (M := M)
      stmt oStmt hnotInput
  let z := columns i u
  have hfiber : 0 < (Finset.univ.filter fun a : LookupOccur n M =>
      lookupOccurValue table columns a = z).card := by
    rw [Finset.card_pos]
    exact ⟨LookupOccur.column i u, by simp [lookupOccurValue, z, columns]⟩
  have hsum :
      (∑ a ∈ (Finset.univ.filter fun a : LookupOccur n M =>
        lookupOccurValue table columns a = z),
          lookupOccurNumerator multiplicity a) ≠ 0 := by
    have hsum_eq :
        (∑ a ∈ (Finset.univ.filter fun a : LookupOccur n M =>
          lookupOccurValue table columns a = z),
            lookupOccurNumerator multiplicity a) =
          - (lookupMultiplicityCount columns z : F) := by
      refine lookupOccurNumerator_fiber_sum_of_table_missing
        (F := F) (n := n) (M := M) table columns multiplicity ?_
      intro v
      simpa [table, columns, z] using hmissing v
    rw [hsum_eq]
    exact neg_ne_zero.mpr hcast
  change
    clearedOccurrences (F := F)
      (lookupOccurValue table columns)
      (lookupOccurNumerator multiplicity) ≠ 0
  exact clearedOccurrences_ne_zero_of_fiber_sum_ne_zero
    (F := F) (value := lookupOccurValue table columns)
    (coeff := lookupOccurNumerator multiplicity) hfiber hsum

set_option linter.unusedDecidableInType false in
/-- Uniform `x` bound for the division-safe bad event: either `x` is a denominator pole for some
occurrence, or it is a root of the nonzero cleared lookup identity. -/
theorem clearedLookupIdentity_bad_x_prob_le
    (table : (Fin n → Fin 2) → F) (columns : Fin M → (Fin n → Fin 2) → F)
    (multiplicity : (Fin n → Fin 2) → F)
    (hpoly : clearedLookupIdentity table columns multiplicity ≠ 0) :
    Pr[fun x : F =>
        (∃ a : LookupOccur n M, x + lookupOccurValue table columns a = 0) ∨
          Polynomial.eval x (clearedLookupIdentity table columns multiplicity) = 0 | $ᵗ F] ≤
      (((M + 1) * Fintype.card (Fin n → Fin 2) : ℕ) : ENNReal) /
          (Fintype.card F : ENNReal) +
        (((M + 1) * Fintype.card (Fin n → Fin 2) - 1 : ℕ) : ENNReal) /
          (Fintype.card F : ENNReal) := by
  classical
  refine le_trans (probEvent_or_le ($ᵗ F)
    (fun x : F => ∃ a : LookupOccur n M, x + lookupOccurValue table columns a = 0)
    (fun x : F => Polynomial.eval x (clearedLookupIdentity table columns multiplicity) = 0)) ?_
  rw [probEvent_uniformSample, probEvent_uniformSample]
  exact add_le_add
    (ENNReal.div_le_div_right
      (Nat.cast_le.mpr (lookupOccur_pole_card_le (F := F) (n := n) (M := M) table columns))
      (Fintype.card F : ENNReal))
    (ENNReal.div_le_div_right
      (Nat.cast_le.mpr
        (clearedLookupIdentity_root_card_le (F := F) (n := n) (M := M)
          table columns multiplicity hpoly))
      (Fintype.card F : ENNReal))

set_option linter.unusedDecidableInType false in
/-- Schwartz-Zippel for the verifier's uniform `z : F`i`n n → F` sampling, phrased in the
`ProbComp` notation used by the protocol proofs. -/
theorem mvPolynomial_uniform_eval_zero_prob_le_div
    (p : MvPolynomial (Fin n) F) (hp : p ≠ 0) (d : ℕ) (hd : p.totalDegree ≤ d) :
    Pr[fun z : Fin n → F => MvPolynomial.eval z p = 0 | $ᵗ (Fin n → F)] ≤
      (d : ENNReal) / (Fintype.card F : ENNReal) := by
  classical
  rw [probEvent_uniformSample]
  have hFpos : 0 < Fintype.card F := Fintype.card_pos_iff.mpr ⟨0⟩
  have hcount :=
    schwartz_zippel_counting (F := F) p hp
      (fun _ : Fin n => (Finset.univ : Finset F)) d (Fintype.card F) hd hFpos
      (fun _ => le_rfl)
  have hpi :
      Fintype.piFinset (fun _ : Fin n => (Finset.univ : Finset F)) =
        (Finset.univ : Finset (Fin n → F)) := by
    ext z
    simp
  have hprod :
      (∏ _i : Fin n, (Finset.univ : Finset F).card) =
        Fintype.card (Fin n → F) := by
    simp [Fintype.card_pi]
  have hcount' :
      (Finset.univ.filter fun z : Fin n → F => MvPolynomial.eval z p = 0).card *
          Fintype.card F ≤ d * Fintype.card (Fin n → F) := by
    rw [hpi] at hcount
    simpa [hprod] using hcount
  exact ENNReal.div_le_div_of_mul_le hFpos Fintype.card_pos hcount'

omit [Field F] [DecidableEq F] [SampleableType F] in
/-- Splitting a function table at one coordinate gives that coordinate and all remaining
coordinates. This is the cardinality form used by the batching-root count. -/
theorem finFunction_card_eq_card_mul_rest (K : ℕ) (k₀ : Fin K) :
    Fintype.card (Fin K → F) =
      Fintype.card F * Fintype.card ({k : Fin K // k ≠ k₀} → F) := by
  classical
  let Rest := {k : Fin K // k ≠ k₀} → F
  let split : (Fin K → F) ≃ F × Rest :=
    { toFun := fun lam => (lam k₀, fun k => lam k.1)
      invFun := fun p k => if h : k = k₀ then p.1 else p.2 ⟨k, h⟩
      left_inv := by
        intro lam
        funext k
        by_cases h : k = k₀ <;> simp [h]
      right_inv := by
        intro p
        rcases p with ⟨x, rest⟩
        apply Prod.ext
        · simp
        · funext k
          simp [k.2] }
  calc
    Fintype.card (Fin K → F) = Fintype.card (F × Rest) := Fintype.card_congr split
    _ = Fintype.card F * Fintype.card Rest := Fintype.card_prod F Rest

omit [SampleableType F] in
/-- If one batching coefficient is nonzero, the bad batching scalars are determined by all
coordinates except that coefficient's coordinate. -/
theorem random_linear_batch_bad_card_le_of_coeff_ne_zero (K : ℕ)
    (c₀ : F) (c : Fin K → F) (k₀ : Fin K) (hk₀ : c k₀ ≠ 0) :
    (Finset.univ.filter fun lam : Fin K → F => c₀ + ∑ k : Fin K, lam k * c k = 0).card ≤
      Fintype.card ({k : Fin K // k ≠ k₀} → F) := by
  classical
  let bad : Finset (Fin K → F) :=
    Finset.univ.filter fun lam : Fin K → F => c₀ + ∑ k : Fin K, lam k * c k = 0
  let Rest := {k : Fin K // k ≠ k₀} → F
  let drop : (Fin K → F) → Rest := fun lam k => lam k.1
  have hdrop_inj : Set.InjOn drop (bad : Set (Fin K → F)) := by
    intro lam hlam mu hmu hdrop
    have hlam_eq : c₀ + ∑ k : Fin K, lam k * c k = 0 := by
      simpa [bad] using (Finset.mem_filter.mp hlam).2
    have hmu_eq : c₀ + ∑ k : Fin K, mu k * c k = 0 := by
      simpa [bad] using (Finset.mem_filter.mp hmu).2
    have hrest : ∀ k : Fin K, k ≠ k₀ → lam k = mu k := by
      intro k hk
      exact congrFun hdrop ⟨k, hk⟩
    have hsum_rest :
        (∑ k ∈ (Finset.univ.erase k₀), lam k * c k) =
          ∑ k ∈ (Finset.univ.erase k₀), mu k * c k := by
      refine Finset.sum_congr rfl ?_
      intro k hk
      rw [hrest k (Finset.mem_erase.mp hk).1]
    rw [← Finset.add_sum_erase (Finset.univ : Finset (Fin K))
        (fun k => lam k * c k) (Finset.mem_univ k₀)] at hlam_eq
    rw [← Finset.add_sum_erase (Finset.univ : Finset (Fin K))
        (fun k => mu k * c k) (Finset.mem_univ k₀)] at hmu_eq
    have hmu_eq' :
        c₀ + (mu k₀ * c k₀ + ∑ k ∈ (Finset.univ.erase k₀), lam k * c k) = 0 := by
      simpa [hsum_rest] using hmu_eq
    have hmain :
        c₀ + (lam k₀ * c k₀ + ∑ k ∈ (Finset.univ.erase k₀), lam k * c k) =
          c₀ + (mu k₀ * c k₀ + ∑ k ∈ (Finset.univ.erase k₀), lam k * c k) := by
      rw [hlam_eq, hmu_eq']
    have hmul_add :
        lam k₀ * c k₀ + ∑ k ∈ (Finset.univ.erase k₀), lam k * c k =
          mu k₀ * c k₀ + ∑ k ∈ (Finset.univ.erase k₀), lam k * c k :=
      add_left_cancel hmain
    have hmul : lam k₀ * c k₀ = mu k₀ * c k₀ := add_right_cancel hmul_add
    funext k
    by_cases hk : k = k₀
    · subst hk
      exact mul_right_cancel₀ hk₀ hmul
    · exact hrest k hk
  calc
    (Finset.univ.filter fun lam : Fin K → F =>
        c₀ + ∑ k : Fin K, lam k * c k = 0).card = bad.card := rfl
    _ ≤ (Finset.univ : Finset Rest).card :=
        Finset.card_le_card_of_injOn drop (fun _ _ => Finset.mem_univ _) hdrop_inj
    _ = Fintype.card Rest := Finset.card_univ

set_option linter.unusedDecidableInType false in
/-- The batched outer sumcheck claim is a random linear combination of the helper-sum claim and
the `K` domain-identity claims, so if one unbatched claim is nonzero the random batching scalar
hits zero with probability at most `1 / |F|`. -/
theorem random_linear_batch_zero_prob_le (K : ℕ)
    (c₀ : F) (c : Fin K → F) (hNonzero : c₀ ≠ 0 ∨ ∃ k, c k ≠ 0) :
    Pr[fun lam : Fin K → F => c₀ + ∑ k : Fin K, lam k * c k = 0 | $ᵗ (Fin K → F)] ≤
      ((1 : ℕ) : ENNReal) / (Fintype.card F : ENNReal) := by
  classical
  by_cases hCoeff : ∃ k, c k ≠ 0
  · obtain ⟨k₀, hk₀⟩ := hCoeff
    rw [probEvent_uniformSample]
    let Rest := {k : Fin K // k ≠ k₀} → F
    have hbad_card :
        (Finset.univ.filter fun lam : Fin K → F =>
          c₀ + ∑ k : Fin K, lam k * c k = 0).card ≤ Fintype.card Rest := by
      simpa [Rest] using
        random_linear_batch_bad_card_le_of_coeff_ne_zero (F := F) K c₀ c k₀ hk₀
    have hcard_domain :
        Fintype.card (Fin K → F) = Fintype.card F * Fintype.card Rest := by
      simpa [Rest] using finFunction_card_eq_card_mul_rest (F := F) K k₀
    have hRest_ne_zero : (Fintype.card Rest : ENNReal) ≠ 0 := by
      exact Nat.cast_ne_zero.mpr Fintype.card_ne_zero
    have hRest_ne_top : (Fintype.card Rest : ENNReal) ≠ ⊤ :=
      ENNReal.natCast_ne_top (Fintype.card Rest)
    calc
      ((Finset.univ.filter fun lam : Fin K → F =>
          c₀ + ∑ k : Fin K, lam k * c k = 0).card : ENNReal) /
            Fintype.card (Fin K → F)
          ≤ (Fintype.card Rest : ENNReal) / Fintype.card (Fin K → F) := by
            exact ENNReal.div_le_div_right (Nat.cast_le.mpr hbad_card)
              (Fintype.card (Fin K → F) : ENNReal)
      _ = (Fintype.card Rest : ENNReal) /
            (Fintype.card F * Fintype.card Rest : ℕ) := by
            rw [hcard_domain]
      _ = ((1 : ℕ) : ENNReal) / (Fintype.card F : ENNReal) := by
            rw [Nat.cast_mul]
            simpa [one_mul, mul_comm, mul_left_comm, mul_assoc] using
              (ENNReal.mul_div_mul_right (a := (1 : ENNReal))
                (b := (Fintype.card F : ENNReal))
                (c := (Fintype.card Rest : ENNReal)) hRest_ne_zero hRest_ne_top)
  · have hc₀ : c₀ ≠ 0 := by
      rcases hNonzero with hc₀ | hcoeff
      · exact hc₀
      · exact False.elim (hCoeff hcoeff)
    have hzero_coeff : ∀ k : Fin K, c k = 0 := by
      intro k
      by_contra hk
      exact hCoeff ⟨k, hk⟩
    rw [probEvent_uniformSample]
    have hempty :
        (Finset.univ.filter fun lam : Fin K → F =>
          c₀ + ∑ k : Fin K, lam k * c k = 0) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro lam _ hbad
      have hsum_zero : (∑ k : Fin K, lam k * c k) = 0 := by
        simp [hzero_coeff]
      exact hc₀ (by simpa [hsum_zero] using hbad)
    rw [hempty]
    simp

end Soundness

end Logup

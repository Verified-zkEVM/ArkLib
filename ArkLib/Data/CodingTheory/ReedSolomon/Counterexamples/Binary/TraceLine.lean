/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.Polynomial.BinaryTraceWitness
public import ArkLib.Data.CodingTheory.ReedSolomon.ReciprocalWord

/-!
# An affine line with binary trace agreement witnesses

`rationalLine_agreement_witness` is the entry point: over a field of size `q = 2^m`, `m ≥ 3`,
every word on the displayed affine line has an explicit polynomial of degree strictly below
`q/4` agreeing at exactly `q/2` coordinates. The hypotheses are a field-cardinality equality
and a parameter `τ` of absolute trace one; `Polynomial.exists_binaryTrace_eq_one` supplies
such a parameter.

The line is `rationalPowerWord m + z * reciprocalWord τ`. Away from zero these words are
`x^(q/2 - 1)` and `1/x`; at zero their values are prescribed as `1` and `τ`. These pole values
are part of the construction, not removable conventions.

## Proof structure

At `z = 0`, use the quotient with parameter `s = 1`. Its `q/2 - 1` nonzero trace-zero
agreements are supplemented by the repaired origin. At `z ≠ 0`, use `s = z⁻¹` and the
trace-one fiber, which already has `q/2` nonzero points. The origin cannot add another
agreement: that would force `τ z² + z + 1 = 0`, contradicting `Tr(τ) = 1`.

This module supplies the exact witnesses and their strict degree bounds. It does not assert
that both source words are far from Reed–Solomon, nor does it prove the paper's native-rate,
full-field, or mutual-correlated-agreement counterexamples. Those require additional hypotheses
and arguments beyond this foundational construction.
-/

@[expose] public section

open scoped BigOperators

namespace ReedSolomon

namespace Binary

open Polynomial

section Definitions

/-- The power word, repaired to have value one at the origin. -/
def rationalPowerWord {F : Type*} [Field F] [DecidableEq F] (m : ℕ) (x : F) : F :=
  if x = 0 then 1 else x ^ (binaryTraceTopDegree m - 1)

end Definitions

section FiniteBinaryField

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [CharP F 2]

omit [Fintype F] [CharP F 2] in
private lemma rationalLineWord_zero (m : ℕ) (τ z : F) :
    rationalPowerWord m 0 + z * reciprocalWord τ 0 = 1 + z * τ := by
  simp [rationalPowerWord, reciprocalWord]

omit [Fintype F] [CharP F 2] in
private lemma rationalLineWord_ne_zero (m : ℕ) (τ z : F) {x : F} (hx : x ≠ 0) :
    rationalPowerWord m x + z * reciprocalWord τ x =
      x ^ (binaryTraceTopDegree m - 1) + z * x⁻¹ := by
  simp [rationalPowerWord, reciprocalWord, hx]

/-- Every word on the trace line has an explicit polynomial below the quarter-field degree
threshold agreeing at exactly half the field. -/
theorem rationalLine_agreement_witness {m : ℕ} (hm : 3 ≤ m)
    (hcard : Fintype.card F = 2 ^ m) {τ : F} (hτ : binaryTrace m τ = 1) (z : F) :
    ∃ p : F[X], p.natDegree < binaryTraceQuarterDegree m ∧
      Code.agree (fun x : F ↦ rationalPowerWord m x + z * reciprocalWord τ x)
        (fun x ↦ p.eval x) =
        binaryTraceTopDegree m := by
  classical
  by_cases hz : z = 0
  · -- The repaired origin completes the nonzero trace-zero fiber.
    subst z
    refine ⟨binaryTraceQuotient m 1, binaryTraceQuotient_natDegree_lt hm 1, ?_⟩
    let nonzeroAgreements := Finset.univ.filter fun x : F ↦ x ≠ 0 ∧
      (binaryTraceQuotient m 1).eval x = x ^ (binaryTraceTopDegree m - 1)
    have hnonzero : nonzeroAgreements.card = Fintype.card F / 2 - 1 := by
      simpa [nonzeroAgreements] using
        binaryTraceQuotient_one_nonzero_agreement_card (F := F) hm hcard
    have hsets :
        Finset.univ.filter (fun x : F ↦
          rationalPowerWord m x + 0 * reciprocalWord τ x =
            (binaryTraceQuotient m 1).eval x) =
          insert 0 nonzeroAgreements := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
      by_cases hx : x = 0
      · subst x
        rw [binaryTraceQuotient_eval_zero (by omega)]
        simp [rationalPowerWord, reciprocalWord]
      · simp only [hx, false_or, nonzeroAgreements]
        rw [rationalLineWord_ne_zero m τ 0 hx]
        simp [hx, eq_comm]
    change (Finset.univ.filter fun x : F ↦
      rationalPowerWord m x + 0 * reciprocalWord τ x =
        (binaryTraceQuotient m 1).eval x).card = binaryTraceTopDegree m
    rw [hsets, Finset.card_insert_of_notMem]
    · rw [hnonzero, binaryTraceTopDegree_eq_card_div_two (F := F) (by omega) hcard]
      have hhalf_pos : 0 < Fintype.card F / 2 := by
        rw [← binaryTraceTopDegree_eq_card_div_two (F := F) (by omega) hcard]
        simp only [binaryTraceTopDegree]
        exact pow_pos Nat.zero_lt_two _
      omega
    · simp [nonzeroAgreements]
  · -- Invert the line parameter to obtain the normalized trace-one witness.
    let s : F := z⁻¹
    have hs : s ≠ 0 := inv_ne_zero hz
    refine ⟨binaryTraceQuotient m s, binaryTraceQuotient_natDegree_lt hm s, ?_⟩
    --
    -- Trace one rules out an accidental extra agreement at the pole.
    have horigin :
        ¬rationalPowerWord m 0 + z * reciprocalWord τ 0 =
          (binaryTraceQuotient m s).eval 0 := by
      rw [binaryTraceQuotient_eval_zero (by omega) s, rationalLineWord_zero]
      intro heq
      have hscaled := congrArg (fun w : F ↦ z * w) heq.symm
      have hzs : z * s = 1 := by simp [s, hz]
      rw [hzs, mul_add, mul_one] at hscaled
      apply trace_one_ne_quadratic_zero hcard hτ
      calc
        τ * z ^ 2 + z + 1 = z * (z * τ) + z + 1 := by
          simp only [pow_two]
          ac_rfl
        _ = (z + z * (z * τ)) + 1 := by ac_rfl
        _ = 1 + 1 := by rw [← hscaled]
        _ = 0 := CharTwo.add_self_eq_zero 1
    --
    -- All remaining agreements are precisely the already-counted trace-one fiber.
    have hsets :
        Finset.univ.filter (fun x : F ↦
          rationalPowerWord m x + z * reciprocalWord τ x =
            (binaryTraceQuotient m s).eval x) =
        Finset.univ.filter (fun x : F ↦
          (binaryTraceQuotient m s).eval x =
            x ^ (binaryTraceTopDegree m - 1) + s⁻¹ * x⁻¹) := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      by_cases hx : x = 0
      · subst x
        apply iff_of_false horigin
        rw [binaryTraceQuotient_eval_zero (by omega) s]
        have hpow : binaryTraceTopDegree m - 1 ≠ 0 := by
          simp only [binaryTraceTopDegree]
          have hle : 2 ^ 1 ≤ 2 ^ (m - 1) := Nat.pow_le_pow_right (by omega) (by omega)
          norm_num at hle
          omega
        simp [zero_pow hpow, hs]
      · rw [rationalLineWord_ne_zero m τ z hx]
        simp [s, eq_comm]
    change (Finset.univ.filter fun x : F ↦
      rationalPowerWord m x + z * reciprocalWord τ x =
        (binaryTraceQuotient m s).eval x).card = binaryTraceTopDegree m
    rw [hsets, binaryTraceQuotient_agreement_card hm hcard hs]
    exact (binaryTraceTopDegree_eq_card_div_two (F := F) (by omega) hcard).symm

end FiniteBinaryField

end Binary

end ReedSolomon

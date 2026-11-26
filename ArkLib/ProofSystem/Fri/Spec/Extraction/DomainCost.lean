/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/
module

public import ArkLib.ProofSystem.Fri.Spec.Extraction.FullCost

/-!
# FRI extraction budgets in the initial domain size

This module bounds each coordinate of the FRI extractor's operation profile by a polynomial in
the initial domain cardinality `N = 2 ^ n`. The bound holds for every folding schedule `s` and
terminal degree bound `d` with `2 ^ (∑ j, (s j).val) * d.val ≤ 2 ^ n`. The price function
`instructionCost` charges one unit in the coordinate of each declared instruction.

## Main results

* `extractorDomainPolynomial`: the polynomial for each resource kind.
* `extractorProfileBound_le_domainEnvelope`: the profile is at most the polynomial evaluated
  at `2 ^ n`.
-/

@[expose] public section

namespace Fri.Spec.Extractor

open CompPoly

/-- Positive folding exponents let the product of the block sizes bound their sum, also after
raising each block size to a positive power. -/
private theorem sum_blockPow_le {k n : ℕ} (s : Fin (k + 1) → ℕ+)
    (hs : (∑ i, (s i).val) ≤ n) {p : ℕ} (hp : 0 < p) :
    (∑ i, (2 ^ (s i).val : ℕ) ^ p) ≤ (2 ^ n) ^ p := by
  have h : ∀ t : Finset (Fin (k + 1)),
      (∑ i ∈ t, (2 ^ (s i).val : ℕ) ^ p) ≤ (2 ^ (∑ i ∈ t, (s i).val)) ^ p := by
    intro t
    induction t using Finset.induction_on with
    | empty => simp
    | insert a t ha ih =>
      by_cases ht : t.Nonempty
      · have htpos : 0 < ∑ i ∈ t, (s i).val := by
          obtain ⟨i, hi⟩ := ht
          exact (s i).pos.trans_le (Finset.single_le_sum (fun j _ ↦ Nat.zero_le (s j).val) hi)
        have two_le (a : ℕ) (ha : 0 < a) : 2 ≤ (2 ^ a : ℕ) ^ p :=
          (Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) ha).trans
            (le_self_pow Nat.one_le_two_pow hp.ne')
        rw [Finset.sum_insert ha, Finset.sum_insert ha, pow_add, mul_pow]
        exact (Nat.add_le_add_left ih _).trans (Nat.add_le_mul
          (two_le _ (s a).pos) (two_le _ htpos))
      · simp [Finset.not_nonempty_iff_eq_empty.mp ht]
  exact (h Finset.univ).trans (Nat.pow_le_pow_left (Nat.pow_le_pow_right (by decide) hs) p)

private theorem rounds_le {n k : ℕ} (s : Fin (k + 1) → ℕ+)
    (hs : (∑ i, (s i).val) ≤ n) : k + 1 ≤ n := by
  calc
    k + 1 = ∑ _ : Fin (k + 1), 1 := by simp
    _ ≤ ∑ i, (s i).val := Finset.sum_le_sum fun i _ ↦ (s i).pos
    _ ≤ n := hs

/-- Bounds for interpolation, grouped by the degree of each coordinate. -/
private def interpolationEnvelope (m : ℕ) : ArithmeticCost
  | .add => 9 * m ^ 3
  | .sub => 2 * m ^ 2
  | .mul => 5 * m ^ 3
  | .inv => m ^ 2
  | .eq => 9 * m ^ 2
  | .coefficientRead => 37 * m ^ 3
  | .nodeRead => 2 * m ^ 2
  | .valueRead => m
  | .metadata => 52 * m ^ 3

private theorem interpolationProfileBound_le_envelope {m N : ℕ} (hm : 0 < m) (hN : m ≤ N)
    (kind : ArithmeticCostKind) :
    Arithmetic.interpolationProfileBound m kind ≤ interpolationEnvelope N kind := by
  have hs : m ≤ m ^ 2 := by simpa [pow_two] using Nat.mul_le_mul_right m hm
  have hc : m ^ 2 ≤ m ^ 3 := by
    simpa only [Nat.mul_one, pow_succ m 2] using Nat.mul_le_mul_left (m ^ 2) hm
  have ht : m - 1 ≤ m := Nat.sub_le ..
  have h₁ := Nat.mul_le_mul_left m ht
  have h₂ := Nat.mul_le_mul_left m (Nat.pow_le_pow_left ht 2)
  apply le_trans (b := interpolationEnvelope m kind)
  · cases kind <;> simp only [Arithmetic.interpolationProfileBound, interpolationEnvelope] <;>
      nlinarith only [hm, hs, hc, h₁, h₂]
  · cases kind <;> simp only [interpolationEnvelope] <;> gcongr

private theorem evaluationProfileBound_mono {m N : ℕ} (h : m ≤ N)
    (kind : ArithmeticCostKind) : Arithmetic.evaluationProfileBound m kind ≤
      Arithmetic.evaluationProfileBound N kind := by
  cases kind <;> simp only [Arithmetic.evaluationProfileBound] <;> gcongr

/-- Bounds for one folding block excluding prefix squaring and final-polynomial evaluation. -/
private def blockEnvelope (m : ℕ) : Cost
  | .inl .add => 10 * m ^ 3
  | .inl .sub => 2 * m ^ 2
  | .inl .mul => 10 * m ^ 3
  | .inl .inv => m ^ 2
  | .inl .eq => 10 * m ^ 2
  | .inl .coefficientRead => 38 * m ^ 3
  | .inl .nodeRead => 4 * m ^ 2
  | .inl .valueRead => 2 * m
  | .inl .metadata => 62 * m ^ 3
  | .inr .wordRead => 2 * m
  | _ => 0

private def prefixEnvelope (n : ℕ) (kind : CostKind) : ℕ :=
  if kind = .inl .mul ∨ kind = .inl .metadata then n else 0

private theorem roundProfileBound_le_blockEnvelope {k n d : ℕ} (s : Fin (k + 1) → ℕ+)
    (hs : (∑ i, (s i).val) ≤ n) (i : Fin (k + 1)) (kind : CostKind) :
    roundProfileBound s d i kind ≤
      blockEnvelope (2 ^ (s i).val) kind + prefixEnvelope n kind +
        if i.val < k then 0
        else embedArithmeticCost (Arithmetic.evaluationProfileBound d) kind := by
  have hprefix := (foldingPrefix_le s i.castSucc).trans hs
  unfold roundProfileBound nextValueProfileBound blockNodesProfileBound blockValuesProfileBound
  generalize he : (s i).val = e
  generalize hm : 2 ^ e = m
  have hb : 0 < m := hm ▸ Nat.two_pow_pos e
  have hem : e ≤ m := hm ▸ Nat.lt_two_pow_self.le
  have hs : m ≤ m ^ 2 := by simpa [pow_two] using Nat.mul_le_mul_right m hb
  have hc : m ^ 2 ≤ m ^ 3 := by
    simpa only [Nat.mul_one, pow_succ m 2] using Nat.mul_le_mul_left (m ^ 2) hb
  have hme := Nat.mul_le_mul_left m hem
  have hI : embedArithmeticCost (Arithmetic.interpolationProfileBound m) kind ≤
      embedArithmeticCost (interpolationEnvelope m) kind := by
    cases kind with
    | inl kind => exact interpolationProfileBound_le_envelope hb le_rfl kind
    | inr => rfl
  rcases kind with kind | kind <;> cases kind <;> by_cases hi : i.val < k <;>
    simp [hi, blockEnvelope, prefixEnvelope, embedArithmeticCost, Arithmetic.evaluationProfileBound,
      interpolationEnvelope] at hI ⊢ <;>
    nlinarith only [hprefix, hb, hem, hs, hc, hme, hI]

private theorem sum_blockEnvelope_le {k n : ℕ} (s : Fin (k + 1) → ℕ+)
    (hs : (∑ i, (s i).val) ≤ n) (kind : CostKind) :
    (∑ i, blockEnvelope (2 ^ (s i).val) kind) ≤ blockEnvelope (2 ^ n) kind := by
  have h₁ := sum_blockPow_le s hs (p := 1) (by decide)
  have h₂ := sum_blockPow_le s hs (p := 2) (by decide)
  have h₃ := sum_blockPow_le s hs (p := 3) (by decide)
  rcases kind with kind | kind <;> cases kind <;>
    simp only [blockEnvelope, ← Finset.mul_sum, Finset.sum_const_zero, le_refl] <;> first
    | exact h₂
    | exact Nat.mul_le_mul_left _ h₂
    | exact Nat.mul_le_mul_left _ h₃
    | exact Nat.mul_le_mul_left _ (by simpa only [pow_one] using h₁)

private def positionDomainEnvelope (N : ℕ) (kind : CostKind) : ℕ :=
  blockEnvelope N kind + N * prefixEnvelope N kind +
    embedArithmeticCost (Arithmetic.evaluationProfileBound N) kind +
    if kind = .inl .metadata then N else 0

private theorem positionProfileBound_le_domainEnvelope {n k : ℕ} (s : Fin (k + 1) → ℕ+)
    (d : ℕ+) (hs : (∑ i, (s i).val) ≤ n) (hd : d.val ≤ 2 ^ n) (kind : CostKind) :
    positionProfileBound s d.val kind ≤ positionDomainEnvelope (2 ^ n) kind := by
  have hn : n ≤ 2 ^ n := Nat.lt_two_pow_self.le
  have hk := (rounds_le s hs).trans hn
  have hprefix : (k + 1) * prefixEnvelope n kind ≤ 2 ^ n * prefixEnvelope (2 ^ n) kind := by
    apply Nat.mul_le_mul hk
    unfold prefixEnvelope
    split <;> omega
  have hsumFinal (a : ℕ) : (∑ i : Fin (k + 1), if i.val < k then 0 else a) = a := by
    rw [Fin.sum_univ_castSucc]
    simp
  have heval : embedArithmeticCost (Arithmetic.evaluationProfileBound d.val) kind ≤
      embedArithmeticCost (Arithmetic.evaluationProfileBound (2 ^ n)) kind := by
    cases kind with
    | inl kind => exact evaluationProfileBound_mono hd kind
    | inr => rfl
  unfold positionProfileBound positionDomainEnvelope
  calc
    _ ≤ (∑ i, (blockEnvelope (2 ^ (s i).val) kind + prefixEnvelope n kind +
          if i.val < k then 0 else embedArithmeticCost (Arithmetic.evaluationProfileBound d.val)
            kind)) + (if kind = .inl .metadata then k + 1 else 0) :=
      Nat.add_le_add_right
        (Finset.sum_le_sum fun i _ ↦ roundProfileBound_le_blockEnvelope s hs i kind) _
    _ ≤ _ := by
      simp only [Finset.sum_add_distrib, hsumFinal, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul, Nat.cast_id]
      have hblock := sum_blockEnvelope_le s hs kind
      split <;> omega

private def initializationDomainEnvelope (N : ℕ) : Cost
  | .inl .mul => 1 + N ^ 2
  | .inl .inv => 1
  | .inl .coefficientRead => N
  | .inl .metadata => N + N ^ 2 + 2 * N + 4
  | .inr .domainRead => 2
  | .inr .challengeRead => N
  | .inr .finalPolynomialRead => 1
  | _ => 0

private theorem initializationBound_le_domainEnvelope {n k : ℕ} (s : Fin (k + 1) → ℕ+)
    (d : ℕ+) (hs : (∑ i, (s i).val) ≤ n) (hd : d.val ≤ 2 ^ n) (kind : CostKind) :
    initializationBound n s d.val kind ≤ initializationDomainEnvelope (2 ^ n) kind := by
  have hn : n ≤ 2 ^ n := Nat.lt_two_pow_self.le
  have hk := (rounds_le s hs).trans hn
  have hsum : (∑ i, (n - (s i).val)) ≤ (2 ^ n) ^ 2 := by
    calc
      _ ≤ ∑ _ : Fin (k + 1), 2 ^ n :=
        Finset.sum_le_sum fun i _ ↦ (Nat.sub_le n (s i).val).trans hn
      _ ≤ _ := by
        simpa [Finset.sum_const, nsmul_eq_mul, pow_two] using Nat.mul_le_mul_right (2 ^ n) hk
  rcases kind with kind | kind <;> cases kind <;>
    simp only [initializationBound, initializationDomainEnvelope] <;> omega

/-- Per-kind polynomial in the initial domain cardinality for the FRI extraction program. -/
noncomputable def extractorDomainPolynomial : CostKind → Polynomial ℕ :=
  let x : Polynomial ℕ := Polynomial.X
  fun
  | .inl .add => 10 * x ^ 4 + 9 * x ^ 3 + x ^ 2
  | .inl .sub => 2 * x ^ 3 + 2 * x ^ 2
  | .inl .mul => 10 * x ^ 4 + 7 * x ^ 3 + 3 * x ^ 2 + x + 1
  | .inl .inv => x ^ 3 + x ^ 2 + 1
  | .inl .eq => 10 * x ^ 3 + 9 * x ^ 2
  | .inl .coefficientRead => 38 * x ^ 4 + 37 * x ^ 3 + x ^ 2 + x
  | .inl .nodeRead => 4 * x ^ 3 + 2 * x ^ 2
  | .inl .valueRead => 2 * x ^ 2 + x
  | .inl .metadata => 62 * x ^ 4 + 54 * x ^ 3 + 4 * x ^ 2 + 6 * x + 6
  | .inr .wordRead => 2 * x ^ 2 + x
  | .inr .domainRead => 2
  | .inr .challengeRead => x
  | .inr .finalPolynomialRead => 1

/-- Budget indexed only by the initial domain cardinality and the resource kind. -/
noncomputable def extractorDomainEnvelope (N : ℕ) (kind : CostKind) : ℕ :=
  (extractorDomainPolynomial kind).eval N

private theorem extractorDomainEnvelope_eq (N : ℕ) (kind : CostKind) :
    extractorDomainEnvelope N kind = initializationDomainEnvelope N kind +
      N * scanCellProfileBound N (positionDomainEnvelope N) kind +
      (if kind = .inl .metadata then 2 else 0) +
      embedArithmeticCost (interpolationEnvelope N) kind := by
  rcases kind with kind | kind <;> cases kind <;>
    simp only [extractorDomainEnvelope, extractorDomainPolynomial, initializationDomainEnvelope,
      scanCellProfileBound, initialPointProfileBound, positionDomainEnvelope, prefixEnvelope,
      blockEnvelope, interpolationEnvelope, embedArithmeticCost, Arithmetic.evaluationProfileBound,
      Polynomial.eval_X, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_ofNat, Polynomial.eval_one, Sum.elim_inl, Sum.elim_inr, Sum.inl.injEq,
      Sum.inr.injEq, reduceCtorEq, or_true, or_false, ite_true, ite_false] <;>
    ring

/-- If `2 ^ (∑ j, (s j).val) * d.val ≤ 2 ^ n`, the coordinate `extractorProfileBound n s d kind`
is at most `extractorDomainEnvelope (2 ^ n) kind`. -/
theorem extractorProfileBound_le_domainEnvelope {n k : ℕ} (s : Fin (k + 1) → ℕ+) (d : ℕ+)
    (hdom : 2 ^ (∑ j, (s j).val) * d.val ≤ 2 ^ n) :
    extractorProfileBound n s d ≤ extractorDomainEnvelope (2 ^ n) := by
  have hs := round_bound hdom
  have hd : d.val ≤ 2 ^ n := le_of_mul_le_of_one_le_right hdom Nat.one_le_two_pow
  have hf : foldingDegree s d 0 ≤ 2 ^ n := by simpa [foldingDegree] using hdom
  have hn : n ≤ 2 ^ n := Nat.lt_two_pow_self.le
  intro kind
  have hinit := initializationBound_le_domainEnvelope s d hs hd kind
  have hposition := positionProfileBound_le_domainEnvelope s d hs hd kind
  have hscan : scanCellProfileBound n (positionProfileBound s d.val) kind ≤
      scanCellProfileBound (2 ^ n) (positionDomainEnvelope (2 ^ n)) kind := by
    unfold scanCellProfileBound initialPointProfileBound
    split <;> split <;> omega
  have hrec : embedArithmeticCost (Arithmetic.interpolationProfileBound (foldingDegree s d 0))
      kind ≤ embedArithmeticCost (interpolationEnvelope (2 ^ n)) kind := by
    cases kind with
    | inl kind => exact interpolationProfileBound_le_envelope (foldingDegree_pos s d 0) hf kind
    | inr => rfl
  have hm := Nat.mul_le_mul_left (2 ^ n) hscan
  rw [extractorDomainEnvelope_eq]
  unfold extractorProfileBound finalInterpolationProfileBound
  have hticks : (if kind = .inl .metadata then 1 else 0) +
      (if kind = .inl .metadata then 1 else 0) =
      (if kind = .inl .metadata then 2 else 0) := by
    split <;> rfl
  refine (Nat.add_le_add (Nat.add_le_add_right (Nat.add_le_add hinit hm) _)
    (Nat.add_le_add_right hrec _)).trans_eq ?_
  rw [← hticks]
  ac_rfl

end Fri.Spec.Extractor

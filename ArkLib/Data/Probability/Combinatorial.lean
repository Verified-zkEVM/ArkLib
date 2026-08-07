/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Algebra.Order.Chebyshev
import ArkLib.Data.Probability.Notation

/-!
# Probabilistic combinatorics

Stand-alone probabilistic-combinatorics statements used elsewhere in ArkLib.
Currently this module hosts `exists_large_image_of_pairwise_collision_bound`,
which is Claim B.1 of [ABF26].

## References

* [Arnon, G., Boneh, D., Fenzi, G., *Open Problems in List Decoding and
  Correlated Agreement*][ABF26]
-/

namespace Probability

open Finset NNReal ENNReal ProbabilityTheory

/-! ## Colliding-pair helpers (ABF26 Appendix B counting)

Helper definitions and the central Cauchy-Schwarz-on-fibers lemma used
by `exists_large_image_of_pairwise_collision_bound` (Claim B.1). -/

section CollidingPairs

variable {S T : Type} [Fintype S] [DecidableEq S] [DecidableEq T]

/-- Number of *ordered* pairs `(x, y) : S × S` with `x ≠ y` and `φ x = φ y`.

This equals twice the number of distinct (unordered) colliding pairs;
working ordered avoids needing a `LinearOrder S` to canonicalise unordered
pairs. Paper's `|C_φ|` is `numCollsOrdered φ / 2`. -/
def numCollsOrdered (φ : S → T) : ℕ :=
  (Finset.univ.filter (fun p : S × S ↦ p.1 ≠ p.2 ∧ φ p.1 = φ p.2)).card

/-- Sum of squared fiber-cardinalities = `|S| + numCollsOrdered`.

Each ordered pair `(x, y)` with `φ x = φ y` is counted once on the LHS
(via its common image μ); the `|S|` diagonal pairs `(x, x)` and the
`numCollsOrdered` off-diagonal pairs partition them. -/
lemma sum_fiber_sq_eq (φ : S → T) :
    ∑ μ ∈ Finset.univ.image φ,
        ((Finset.univ.filter (fun x : S ↦ φ x = μ)).card)^2 =
      Fintype.card S + numCollsOrdered φ := by
  classical
  -- Step 1: LHS = #{(x, y) : φ x = φ y}.
  -- Each μ ∈ image contributes |fiber μ|² = |fiber μ × fiber μ| = #{(x,y) : φ x = φ y = μ}.
  have step1 :
      ∑ μ ∈ Finset.univ.image φ,
          ((Finset.univ.filter (fun x : S ↦ φ x = μ)).card)^2 =
        (Finset.univ.filter (fun p : S × S ↦ φ p.1 = φ p.2)).card := by
    -- The matching-pair set D = univ.filter (φ p.1 = φ p.2) partitions by φ p.1 ∈ image.
    set D := Finset.univ.filter (fun p : S × S ↦ φ p.1 = φ p.2)
    -- D maps into image φ via the projection p ↦ φ p.1
    have hMaps : (D : Set (S × S)).MapsTo (fun p : S × S ↦ φ p.1)
                  (Finset.univ.image φ : Finset T) := by
      intros p _
      simp only [Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_range]
      exact ⟨p.1, rfl⟩
    rw [Finset.card_eq_sum_card_fiberwise (f := fun p : S × S ↦ φ p.1)
        (t := Finset.univ.image φ) hMaps]
    apply Finset.sum_congr rfl
    intros μ _
    -- {p ∈ D | φ p.1 = μ} = fiber μ × fiber μ.
    rw [sq, ← Finset.card_product]
    congr 1
    ext ⟨x, y⟩
    simp only [D, Finset.mem_filter, Finset.mem_univ, Finset.mem_product, true_and]
    -- Goal: (φ x = μ ∧ φ y = μ) ↔ φ x = φ y ∧ φ x = μ
    constructor
    · rintro ⟨hx, hy⟩
      exact ⟨hx.trans hy.symm, hx⟩
    · rintro ⟨h_match, hx⟩
      exact ⟨hx, h_match.symm.trans hx⟩
  rw [step1]
  -- Step 2: #{(x, y) : φ x = φ y} = |diag| + |off-diag matching|.
  -- diag = {(x, x)}; off-diag matching = numCollsOrdered's filter set.
  have step2 :
      (Finset.univ.filter (fun p : S × S ↦ φ p.1 = φ p.2)).card =
        (Finset.univ.filter (fun p : S × S ↦ p.1 = p.2)).card +
        (Finset.univ.filter (fun p : S × S ↦ p.1 ≠ p.2 ∧ φ p.1 = φ p.2)).card := by
    rw [← Finset.card_union_of_disjoint]
    · congr 1
      ext ⟨x, y⟩
      simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_univ, true_and]
      by_cases hxy : x = y
      · simp [hxy]
      · constructor
        · intro hφ; right; exact ⟨hxy, hφ⟩
        · rintro (h_eq | ⟨_, hφ⟩) <;> [exact (hxy h_eq).elim; exact hφ]
    · rw [Finset.disjoint_filter]
      intros _ _ h_eq h_ne_and; exact h_ne_and.1 h_eq
  rw [step2]
  -- Step 3: diag count = |S| via the (x : S) ↔ ((x, x) ∈ diag) bijection.
  congr 1
  -- diag = (Finset.univ : Finset S).image (fun x ↦ (x, x))
  rw [show (Finset.univ.filter (fun p : S × S ↦ p.1 = p.2)) =
        (Finset.univ : Finset S).image (fun x ↦ (x, x)) by
    ext ⟨x, y⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image, Prod.mk.injEq]
    constructor
    · intro h_eq; exact ⟨x, ⟨rfl, h_eq⟩⟩
    · rintro ⟨a, ⟨rfl, rfl⟩⟩; rfl]
  rw [Finset.card_image_of_injective _ (fun a b h ↦ (Prod.mk.injEq _ _ _ _).mp h |>.1)]
  rfl

/-- Cauchy-Schwarz applied to fiber cardinalities.

Equivalent to `Finset.sq_sum_le_card_mul_sum_sq` over the image of `φ`,
combined with `sum_fiber_sq_eq` to rewrite the squared-sum side and
with `Finset.card_eq_sum_card_image` to identify
`Σ μ ∈ image, |fiber μ| = |S|`. -/
lemma cauchy_schwarz_fiber (φ : S → T) :
    (Fintype.card S)^2 ≤
      (Finset.univ.image φ).card * (Fintype.card S + numCollsOrdered φ) := by
  classical
  -- Fiber decomposition: Σ μ ∈ image, |fiber μ| = |S|.
  have h_sum_card :
      ∑ μ ∈ Finset.univ.image φ,
          (Finset.univ.filter (fun x : S ↦ φ x = μ)).card = Fintype.card S := by
    have := Finset.card_eq_sum_card_image φ (Finset.univ : Finset S)
    simpa using this.symm
  -- Cast inequality through ℝ since Chebyshev requires LinearOrderedSemifield.
  have h_cs := sq_sum_le_card_mul_sum_sq
    (s := Finset.univ.image φ)
    (f := fun μ ↦ ((Finset.univ.filter (fun x : S ↦ φ x = μ)).card : ℝ))
  -- LHS in ℝ: (Σ μ, |fiber μ|)² = |S|² (via h_sum_card cast).
  have h_lhs :
      (∑ μ ∈ Finset.univ.image φ,
          ((Finset.univ.filter (fun x : S ↦ φ x = μ)).card : ℝ))
        = (Fintype.card S : ℝ) := by
    rw [← Nat.cast_sum, h_sum_card]
  -- RHS sum in ℝ: Σ μ, |fiber μ|² = |S| + numCollsOrdered φ (via sum_fiber_sq_eq cast).
  have h_rhs :
      (∑ μ ∈ Finset.univ.image φ,
          (((Finset.univ.filter (fun x : S ↦ φ x = μ)).card : ℝ))^2)
        = ((Fintype.card S + numCollsOrdered φ : ℕ) : ℝ) := by
    rw [show (∑ μ ∈ Finset.univ.image φ,
          (((Finset.univ.filter (fun x : S ↦ φ x = μ)).card : ℝ))^2)
        = (∑ μ ∈ Finset.univ.image φ,
          (((Finset.univ.filter (fun x : S ↦ φ x = μ)).card)^2 : ℕ) : ℝ) by
      push_cast; rfl]
    rw [← Nat.cast_sum, sum_fiber_sq_eq]
  rw [h_lhs, h_rhs] at h_cs
  -- h_cs : (Fintype.card S : ℝ)² ≤ (#image : ℝ) * (Fintype.card S + numColls : ℝ)
  exact_mod_cast h_cs

end CollidingPairs

/-- **Claim B.1 of [ABF26]** ("Omitted claim for Lemma 6.12").

Suppose `S, T` are finite sets and `Φ` is a distribution on functions `S → T`
such that for any distinct `x, y ∈ S`, the probability that a sample
`φ ← Φ` sends `x` and `y` to the same image is bounded by `ε`:
```
∀ x y ∈ S, x ≠ y → Pr_{φ ← Φ}[φ x = φ y] ≤ ε.
```
Then there exists some `φ` in the support of `Φ` whose image has cardinality
at least `|S| / (1 + (|S| − 1) · ε)`.

## Proof sketch (contradiction-form, avoids Jensen)

Let `N := |S|`, `δ := 1 + (N − 1) · ε`, `K := N / δ`. The proof tracks three
in-line steps; the inelegance-saving idea is to negate the goal and exploit
linearity of expectation instead of integrating a convex function.

**Step A (pointwise Cauchy–Schwarz; [`cauchy_schwarz_fiber`]).** For every
`φ : S → T`, the fiber decomposition `Σ μ ∈ image φ, |φ⁻¹(μ)| = |S|` combined
with `sq_sum_le_card_mul_sum_sq` (Chebyshev for `f = g`) and
[`sum_fiber_sq_eq`] gives `N² ≤ |image φ| · (N + numCollsOrdered φ)`.

**Step B (linearity of expectation).** Each `numCollsOrdered φ` is a sum of
`(φ p.1 = φ p.2)`-indicators over ordered off-diagonal pairs `P`. Swapping
the outer PMF `tsum` with the inner `Finset.sum` via
`Summable.tsum_finsetSum` and using the hypothesis `Pr_{φ ← Φ}[φ x = φ y] ≤ ε`
(unfolded via [`Pr_decide_eq_tsum_indicator`]) gives
`∑' φ, Φ φ · (numCollsOrdered φ : ENNReal) ≤ N · (N − 1) · ε`.

**Step C (contradiction by strict averaging).** Assume for contradiction
`∀ φ ∈ Φ.support, |image φ| < K`. Step A then forces, for each such φ,
`numCollsOrdered φ > N · (N − 1) · ε` (via `mul_lt_of_lt_div` and ENNReal
cross-multiplication: `A · δ < N` combined with `N² ≤ A · (N + C)` together
with the negation `C ≤ N(N−1)ε` produces `N² < N²`). Strict averaging via
`ENNReal.tsum_lt_tsum` at any `φ₀ ∈ Φ.support` lifts the per-φ strict bound
to `N · (N − 1) · ε < ∑' φ, Φ φ · numCollsOrdered φ`, contradicting Step B. -/
theorem exists_large_image_of_pairwise_collision_bound
    {S T : Type} [Fintype S] [DecidableEq T]
    (Φ : PMF (S → T)) (ε : ENNReal)
    (hΦ : ∀ x y : S, x ≠ y →
        Pr_{ let φ ← Φ }[(decide (φ x = φ y) : Prop)] ≤ ε) :
    ∃ φ ∈ Φ.support, ((Finset.univ.image φ).card : ENNReal) ≥
      (Fintype.card S : ENNReal) / (1 + (Fintype.card S - 1) * ε) := by
  classical
  set N : ℕ := Fintype.card S with hN_def
  -- Pairs of distinct elements.
  set P : Finset (S × S) := Finset.univ.filter (fun p : S × S ↦ p.1 ≠ p.2) with hP_def
  -- `|P| = N · (N - 1)` (Finset count of off-diagonal pairs).
  have hP_card : P.card = N * (N - 1) := by
    have h_eq : P = Finset.offDiag (Finset.univ : Finset S) := by
      rw [hP_def]
      ext ⟨x, y⟩
      simp [Finset.mem_offDiag]
    rw [h_eq, Finset.offDiag_card]
    simp [hN_def, Nat.mul_sub_one]
  -- ## Step A — Pointwise Cauchy-Schwarz, in ENNReal.
  -- For every `φ : S → T`,  `N² ≤ |image φ| · (N + numCollsOrdered φ)` in ENNReal.
  have hCS_E : ∀ φ : S → T,
      (N : ENNReal)^2 ≤ ((Finset.univ.image φ).card : ENNReal) *
        ((N : ENNReal) + (numCollsOrdered φ : ENNReal)) := by
    intro φ
    have h := cauchy_schwarz_fiber φ
    -- h : N^2 ≤ #image · (N + numColls) in ℕ; cast to ENNReal.
    exact_mod_cast h
  -- ## Step B — Linearity of expectation.
  -- `∑' φ, Φ φ * (numCollsOrdered φ : ENNReal) ≤ N · (N - 1) · ε`.
  -- numCollsOrdered φ = #{(x, y) ∈ P : φ x = φ y}; unfold as a sum of indicators,
  -- swap with the outer tsum, and apply hΦ pointwise.
  have h_lin : ∑' φ : S → T, Φ φ * (numCollsOrdered φ : ENNReal) ≤
      ((N * (N - 1) : ℕ) : ENNReal) * ε := by
    -- Step B.1: numCollsOrdered φ = ∑ p ∈ P, (if φ p.1 = φ p.2 then 1 else 0).
    have h_numCard : ∀ φ : S → T,
        (numCollsOrdered φ : ENNReal) =
          ∑ p ∈ P, (if φ p.1 = φ p.2 then (1 : ENNReal) else 0) := by
      intro φ
      rw [show numCollsOrdered φ =
          (P.filter (fun p : S × S ↦ φ p.1 = φ p.2)).card by
        unfold numCollsOrdered
        rw [hP_def]
        congr 1
        ext ⟨x, y⟩
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]]
      rw [Finset.card_filter]
      push_cast
      rfl
    -- Step B.2: ∑' φ, Φ φ * (Σ p, indicator) = Σ p, ∑' φ, Φ φ * indicator.
    simp_rw [h_numCard, Finset.mul_sum]
    rw [Summable.tsum_finsetSum (fun _ _ ↦ ENNReal.summable)]
    -- Goal: ∑ p ∈ P, ∑' φ, Φ φ * (if φ p.1 = φ p.2 then 1 else 0) ≤ N(N-1) · ε.
    -- Step B.3: each inner sum is `Pr_{φ←Φ}[φ p.1 = φ p.2] ≤ ε`.
    have h_inner : ∀ p ∈ P,
        ∑' φ : S → T, Φ φ * (if φ p.1 = φ p.2 then (1 : ENNReal) else 0) ≤ ε := by
      intro p hp
      simp only [hP_def, Finset.mem_filter, Finset.mem_univ, true_and] at hp
      have h := hΦ p.1 p.2 hp
      rwa [Pr_decide_eq_tsum_indicator] at h
    -- Step B.4: bound termwise.
    calc ∑ p ∈ P, ∑' φ : S → T, Φ φ * (if φ p.1 = φ p.2 then (1 : ENNReal) else 0)
        ≤ ∑ _p ∈ P, ε := Finset.sum_le_sum h_inner
      _ = (P.card : ENNReal) * ε := by rw [Finset.sum_const, nsmul_eq_mul]
      _ = ((N * (N - 1) : ℕ) : ENNReal) * ε := by rw [hP_card]
  -- ## Step C — Contradiction route.
  -- Assume `∀ φ ∈ supp Φ, |image φ| < K = N / (1 + (N-1) ε)`.
  -- Then for each such φ:  numCollsOrdered φ > N(N-1) ε  (via Cauchy-Schwarz + algebra).
  -- Averaging: `∑' φ, Φ φ * numColls φ > N(N-1) ε`, contradicting h_lin.
  by_contra h_neg
  push Not at h_neg
  -- h_neg : ∀ φ ∈ Φ.support, ((|image φ|) : ENNReal) < K
  -- Derive a strict per-φ lower bound on numCollsOrdered φ for φ ∈ supp.
  have h_pointwise :
      ∀ φ ∈ Φ.support,
        ((N * (N - 1) : ℕ) : ENNReal) * ε <
          (numCollsOrdered φ : ENNReal) := by
    intro φ hφ
    set A : ENNReal := ((Finset.univ.image φ).card : ENNReal) with hA_def
    set C : ENNReal := (numCollsOrdered φ : ENNReal) with hC_def
    set δ : ENNReal := 1 + ((N : ENNReal) - 1) * ε with hδ_def
    -- From `h_neg φ hφ`.
    have hA_lt_K : A < (N : ENNReal) / δ := h_neg φ hφ
    -- A < K = N/δ ⇒ K > 0 ⇒ N ≠ 0 ∧ δ ≠ ⊤.
    have hK_pos : (0 : ENNReal) < (N : ENNReal) / δ :=
      lt_of_le_of_lt (zero_le) hA_lt_K
    obtain ⟨hN_ne, _hδ_ne_top⟩ := ENNReal.div_pos_iff.mp hK_pos
    have hN_ne_top : (N : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top _
    -- A · δ < N (from A < N/δ).
    have hAδ : A * δ < (N : ENNReal) := mul_lt_of_lt_div hA_lt_K
    have hCS : (N : ENNReal) ^ 2 ≤ A * ((N : ENNReal) + C) := hCS_E φ
    rw [sq] at hCS
    -- Helper: ℕ-cast vs ENNReal arithmetic on `N(N-1)`.
    have hN_sub_cast : ((N - 1 : ℕ) : ENNReal) = (N : ENNReal) - 1 := by
      rw [ENNReal.natCast_sub]; simp
    have h_NC_cast : ((N * (N - 1) : ℕ) : ENNReal) =
        (N : ENNReal) * ((N : ENNReal) - 1) := by
      rw [Nat.cast_mul, hN_sub_cast]
    -- By contradiction: assume C ≤ N(N-1)·ε.
    by_contra h_not
    push Not at h_not
    -- h_not : C ≤ ((N * (N - 1) : ℕ) : ENNReal) * ε
    -- Show N + C ≤ N · δ.
    have h_NC_le : (N : ENNReal) + C ≤ (N : ENNReal) * δ := by
      have h_arith : (N : ENNReal) + ((N * (N - 1) : ℕ) : ENNReal) * ε
          = (N : ENNReal) * δ := by
        rw [hδ_def, mul_add, mul_one, h_NC_cast]; ring
      calc (N : ENNReal) + C
          ≤ (N : ENNReal) + ((N * (N - 1) : ℕ) : ENNReal) * ε := by gcongr
        _ = (N : ENNReal) * δ := h_arith
    -- A · (N + C) ≤ A · N · δ = (A · δ) · N.
    have h_step : A * ((N : ENNReal) + C) ≤ A * δ * (N : ENNReal) := by
      calc A * ((N : ENNReal) + C)
          ≤ A * ((N : ENNReal) * δ) := by gcongr
        _ = A * δ * (N : ENNReal) := by ring
    -- (A · δ) · N < N · N = N² (since A · δ < N and N ≠ 0, N ≠ ⊤).
    have h_strict_lt : A * δ * (N : ENNReal) < (N : ENNReal) * (N : ENNReal) :=
      ENNReal.mul_lt_mul_left hN_ne hN_ne_top hAδ
    -- Chain: N² ≤ A·(N+C) ≤ (A·δ)·N < N². Contradiction.
    exact absurd (hCS.trans h_step) (not_le_of_gt h_strict_lt)
  -- Sum to contradict h_lin.
  have h_strict :
      ((N * (N - 1) : ℕ) : ENNReal) * ε <
        ∑' φ : S → T, Φ φ * (numCollsOrdered φ : ENNReal) := by
    obtain ⟨φ₀, hφ₀⟩ := Φ.support_nonempty
    -- We need ∑' g > c where c := N(N-1)ε. Reformulate c as ∑' (Φ * c).
    -- This requires `tsum f ≠ ⊤`, which forces a case-split on `c = ⊤`.
    set c : ENNReal := ((N * (N - 1) : ℕ) : ENNReal) * ε with hc_def
    by_cases h_top : c = ⊤
    · -- c = ⊤: h_pointwise gives ⊤ < numCollsOrdered φ₀, but numCollsOrdered is finite.
      exfalso
      have h_pt := h_pointwise φ₀ hφ₀
      rw [h_top] at h_pt
      exact absurd h_pt (not_lt.mpr le_top)
    -- Express c as ∑' φ, Φ φ * c.
    have h_eq : ∑' φ : S → T, Φ φ * c = c := by
      rw [ENNReal.tsum_mul_right, Φ.tsum_coe, one_mul]
    rw [show c = ∑' φ : S → T, Φ φ * c from h_eq.symm]
    -- Apply tsum_lt_tsum.
    apply ENNReal.tsum_lt_tsum (i := φ₀)
    · rw [h_eq]; exact h_top
    · -- Pointwise: Φ φ * c ≤ Φ φ * numCollsOrdered φ.
      intro φ
      by_cases hφ_supp : φ ∈ Φ.support
      · gcongr
        exact (h_pointwise φ hφ_supp).le
      · -- Outside support, Φ φ = 0.
        have : Φ φ = 0 := by
          rwa [Φ.mem_support_iff, not_not] at hφ_supp
        simp [this]
    · -- Strict at φ₀: Φ φ₀ > 0 and (numCollsOrdered φ₀ > c).
      have hΦ_pos : (0 : ENNReal) < Φ φ₀ := (Φ.apply_pos_iff _).mpr hφ₀
      have hΦ_ne_top : Φ φ₀ ≠ ⊤ := PMF.apply_ne_top Φ φ₀
      exact ENNReal.mul_lt_mul_right (ne_of_gt hΦ_pos) hΦ_ne_top
        (h_pointwise φ₀ hφ₀)
  exact absurd (h_strict.trans_le h_lin) (lt_irrefl _)

end Probability

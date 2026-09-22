/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/
module

public import Mathlib.Algebra.Order.Chebyshev
public import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
public import VCVio.OracleComp.Constructions.SampleableType.NativeMeasure

/-!
# Probabilistic combinatorics

A random function whose pairs collide with small probability has, for some sample, a large
image.

## Main statements

* `Probability.exists_large_image_of_pairwise_collision_bound` — if every pair of distinct
  points of a finite `S` collides with probability at most `ε` under a probability measure on
  functions, then some positive-mass function in its countable carrier has large image.

## References

* [Arnon, G., Boneh, D., Fenzi, G., *Open Problems in List Decoding and
  Correlated Agreement*][ABF26]
-/

@[expose] public section

namespace Probability

open Finset NNReal ENNReal MeasureTheory

/-! ## Colliding-pair helpers

Fiber counting and the Cauchy-Schwarz step feeding
`exists_large_image_of_pairwise_collision_bound`. -/

section CollidingPairs

variable {S T : Type*} [Fintype S] [DecidableEq S] [DecidableEq T]

/-- The number of *ordered* pairs `(x, y)` with `x ≠ y` and `φ x = φ y`, twice the number of
unordered colliding pairs. Counting ordered pairs avoids needing a `LinearOrder S`. -/
private def numCollsOrdered (φ : S → T) : ℕ :=
  (Finset.univ.filter (fun p : S × S ↦ p.1 ≠ p.2 ∧ φ p.1 = φ p.2)).card

/-- The squared fiber cardinalities of `φ` sum to `|S| + numCollsOrdered φ`: each ordered
pair with `φ x = φ y` is counted once, and the `|S|` diagonal pairs together with the
`numCollsOrdered φ` off-diagonal ones exhaust them. -/
private lemma sum_fiber_sq_eq (φ : S → T) :
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

/-- Cauchy-Schwarz on the fiber cardinalities of `φ`:
`|S| ^ 2 ≤ |image φ| * (|S| + numCollsOrdered φ)`.

This is `sq_sum_le_card_mul_sum_sq` over the image of `φ`, with `sum_fiber_sq_eq` rewriting
the sum of squares and `Finset.card_eq_sum_card_image` identifying
`∑ μ ∈ image φ, |fiber μ| = |S|`. -/
private lemma cauchy_schwarz_fiber (φ : S → T) :
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

open Classical in
/-- Let `μ` be a probability measure on functions `S → T`, concentrated on the countable set
`A`. If every pair of distinct points of the finite type `S` collides with probability at most
`ε`, then some positive-mass function in `A` has image of cardinality at least
`|S| / (1 + (|S| - 1) * ε)`.

The explicit countable carrier is the measure-native analogue of the support of a probability mass
function. It preserves the positive-atom conclusion while allowing `S` and `T` in arbitrary
universes.

Writing `N = |S|`, the proof uses linearity of the Lebesgue integral and a strict averaging
argument.

* Pointwise, `cauchy_schwarz_fiber` gives `N ^ 2 ≤ |image φ| * (N + numCollsOrdered φ)`.
* The expected number of ordered collisions is at most `N * (N - 1) * ε`.
* If every positive-mass `φ` in `A` had smaller image, the first item would force its collision
  count strictly above that expectation bound. Since `A` is countable and has full mass, this
  strict inequality holds almost everywhere, a contradiction. -/
theorem exists_large_image_of_pairwise_collision_bound
    {S T : Type*} [Fintype S]
    [MeasurableSpace (S → T)] [DiscreteMeasurableSpace (S → T)]
    (μ : Measure (S → T)) [IsProbabilityMeasure μ]
    (A : Set (S → T)) (hA_countable : A.Countable) (hμA : μ A = 1)
    (ε : ENNReal)
    (hμ : ∀ x y : S, x ≠ y → μ {φ | φ x = φ y} ≤ ε) :
    ∃ φ ∈ A, 0 < μ {φ} ∧
      (Fintype.card S : ENNReal) / (1 + (Fintype.card S - 1) * ε) ≤
        ((@Finset.image S T (Classical.decEq T) φ Finset.univ).card : ENNReal) := by
  classical
  set N : ℕ := Fintype.card S with hN_def
  set P : Finset (S × S) := Finset.univ.filter (fun p : S × S ↦ p.1 ≠ p.2) with hP_def
  have hP_card : P.card = N * (N - 1) := by
    have h_eq : P = Finset.offDiag (Finset.univ : Finset S) := by
      rw [hP_def]
      ext ⟨x, y⟩
      simp [Finset.mem_offDiag]
    rw [h_eq, Finset.offDiag_card]
    simp [hN_def, Nat.mul_sub_one]
  have hCS_E : ∀ φ : S → T,
      (N : ENNReal)^2 ≤ ((Finset.univ.image φ).card : ENNReal) *
        ((N : ENNReal) + (numCollsOrdered φ : ENNReal)) := by
    intro φ
    exact_mod_cast cauchy_schwarz_fiber φ
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
  have h_lin : ∫⁻ φ, (numCollsOrdered φ : ENNReal) ∂μ ≤
      ((N * (N - 1) : ℕ) : ENNReal) * ε := by
    simp_rw [h_numCard]
    rw [lintegral_finsetSum P (fun _ _ ↦ Measurable.of_discrete)]
    have h_inner : ∀ p ∈ P,
        (∫⁻ φ, (if φ p.1 = φ p.2 then (1 : ENNReal) else 0) ∂μ) ≤ ε := by
      intro p hp
      simp only [hP_def, Finset.mem_filter, Finset.mem_univ, true_and] at hp
      calc
        (∫⁻ φ, (if φ p.1 = φ p.2 then (1 : ENNReal) else 0) ∂μ) =
            μ {φ | φ p.1 = φ p.2} := by
              rw [← lintegral_indicator_one MeasurableSet.of_discrete]
              congr 1
        _ ≤ ε := hμ p.1 p.2 hp
    calc
      ∑ p ∈ P, ∫⁻ φ, (if φ p.1 = φ p.2 then (1 : ENNReal) else 0) ∂μ
          ≤ ∑ _p ∈ P, ε := Finset.sum_le_sum h_inner
      _ = (P.card : ENNReal) * ε := by rw [Finset.sum_const, nsmul_eq_mul]
      _ = ((N * (N - 1) : ℕ) : ENNReal) * ε := by rw [hP_card]
  by_contra h_neg
  push Not at h_neg
  have h_pointwise : ∀ φ ∈ A, 0 < μ {φ} →
      ((N * (N - 1) : ℕ) : ENNReal) * ε <
        (numCollsOrdered φ : ENNReal) := by
    intro φ hφA hφ_pos
    set B : ENNReal := ((Finset.univ.image φ).card : ENNReal) with hB_def
    set C : ENNReal := (numCollsOrdered φ : ENNReal) with hC_def
    set δ : ENNReal := 1 + ((N : ENNReal) - 1) * ε with hδ_def
    have hB_lt_K : B < (N : ENNReal) / δ := h_neg φ hφA hφ_pos
    have hK_pos : (0 : ENNReal) < (N : ENNReal) / δ :=
      lt_of_le_of_lt zero_le hB_lt_K
    obtain ⟨hN_ne, _hδ_ne_top⟩ := ENNReal.div_pos_iff.mp hK_pos
    have hN_ne_top : (N : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top _
    have hBδ : B * δ < (N : ENNReal) := mul_lt_of_lt_div hB_lt_K
    have hCS : (N : ENNReal) ^ 2 ≤ B * ((N : ENNReal) + C) := hCS_E φ
    rw [sq] at hCS
    have hN_sub_cast : ((N - 1 : ℕ) : ENNReal) = (N : ENNReal) - 1 := by
      rw [ENNReal.natCast_sub]
      simp
    have h_NC_cast : ((N * (N - 1) : ℕ) : ENNReal) =
        (N : ENNReal) * ((N : ENNReal) - 1) := by
      rw [Nat.cast_mul, hN_sub_cast]
    by_contra h_not
    push Not at h_not
    have h_NC_le : (N : ENNReal) + C ≤ (N : ENNReal) * δ := by
      have h_arith : (N : ENNReal) + ((N * (N - 1) : ℕ) : ENNReal) * ε =
          (N : ENNReal) * δ := by
        rw [hδ_def, mul_add, mul_one, h_NC_cast]
        ring
      calc
        (N : ENNReal) + C
            ≤ (N : ENNReal) + ((N * (N - 1) : ℕ) : ENNReal) * ε := by gcongr
        _ = (N : ENNReal) * δ := h_arith
    have h_step : B * ((N : ENNReal) + C) ≤ B * δ * (N : ENNReal) := by
      calc
        B * ((N : ENNReal) + C) ≤ B * ((N : ENNReal) * δ) := by gcongr
        _ = B * δ * (N : ENNReal) := by ring
    have h_strict_lt : B * δ * (N : ENNReal) < (N : ENNReal) * (N : ENNReal) :=
      ENNReal.mul_lt_mul_left hN_ne hN_ne_top hBδ
    exact absurd (hCS.trans h_step) (not_le_of_gt h_strict_lt)
  let Z : Set (S → T) := {φ | φ ∈ A ∧ μ {φ} = 0}
  have hZ_countable : Z.Countable := hA_countable.mono fun _ hφ ↦ hφ.1
  have hμZ : μ Z = 0 := by
    rw [← Z.biUnion_of_singleton, measure_biUnion_null_iff hZ_countable]
    intro φ hφ
    exact hφ.2
  have h_positive_atom : ∃ φ ∈ A, 0 < μ {φ} := by
    by_contra h
    push Not at h
    have hAZ : A ⊆ Z := by
      intro φ hφA
      exact ⟨hφA, bot_unique (h φ hφA)⟩
    have hA_zero : μ A = 0 := measure_mono_null hAZ hμZ
    rw [hμA] at hA_zero
    simp at hA_zero
  have h_ae_strict : ∀ᵐ φ ∂μ,
      ((N * (N - 1) : ℕ) : ENNReal) * ε < (numCollsOrdered φ : ENNReal) := by
    have h_ae_A : ∀ᵐ φ ∂μ, φ ∈ A :=
      (mem_ae_iff_prob_eq_one hA_countable.measurableSet).2 hμA
    have h_ae_not_Z : ∀ᵐ φ ∂μ, φ ∉ Z := measure_eq_zero_iff_ae_notMem.mp hμZ
    filter_upwards [h_ae_A, h_ae_not_Z] with φ hφA hφZ
    apply h_pointwise φ hφA
    exact pos_iff_ne_zero.mpr fun hzero ↦ hφZ ⟨hφA, hzero⟩
  have h_strict : ((N * (N - 1) : ℕ) : ENNReal) * ε <
      ∫⁻ φ, (numCollsOrdered φ : ENNReal) ∂μ := by
    have h_const_ne_top :
        (∫⁻ _φ : S → T, ((N * (N - 1) : ℕ) : ENNReal) * ε ∂μ) ≠ ⊤ := by
      rw [lintegral_const, measure_univ, mul_one]
      by_cases hε : ε = ⊤
      · obtain ⟨φ, hφA, hφ_pos⟩ := h_positive_atom
        have hzero : N * (N - 1) = 0 := by
          by_contra hNprod
          have hcast : ((N * (N - 1) : ℕ) : ENNReal) ≠ 0 := by exact_mod_cast hNprod
          have htop : ((N * (N - 1) : ℕ) : ENNReal) * ε = ⊤ := by
            rw [hε]
            exact ENNReal.mul_top hcast
          have hbad := h_pointwise φ hφA hφ_pos
          rw [htop] at hbad
          exact (not_lt_of_ge le_top) hbad
        simp [hzero]
      · exact ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) hε
    have hμ_ne_zero : μ ≠ 0 := IsProbabilityMeasure.ne_zero μ
    have hlt := lintegral_strict_mono hμ_ne_zero Measurable.of_discrete.aemeasurable
      h_const_ne_top h_ae_strict
    simpa [lintegral_const, measure_univ] using hlt
  exact (not_lt_of_ge h_lin) h_strict

open Classical in
/-- `exists_large_image_of_pairwise_collision_bound` for a probabilistic computation.  The
positive singleton supplied by the measure theorem is exactly an operationally reachable output
under the uniform oracle semantics of `ProbComp`. -/
theorem exists_large_image_of_pairwise_collision_bound_of_probComp
    {S T : Type} [Fintype S]
    (Φ : ProbComp (S → T)) (ε : ENNReal)
    (hΦ : ∀ x y : S, x ≠ y → Pr{let φ ← Φ}[φ x = φ y] ≤ ε) :
    ∃ φ ∈ MonadAttach.support Φ,
      (Fintype.card S : ENNReal) / (1 + (Fintype.card S - 1) * ε) ≤
        ((@Finset.image S T (Classical.decEq T) φ Finset.univ).card : ENNReal) := by
  let : MeasurableSpace (S → T) := ⊤
  obtain ⟨φ, hφ, _, hcard⟩ := exists_large_image_of_pairwise_collision_bound
    𝒟[Φ] (MonadAttach.support Φ)
      (OracleComp.support_finite (spec := unifSpec) Φ).countable
      (by
        change 𝒟[Φ] {x | x ∈ MonadAttach.support Φ} = 1
        rw [OracleComp.evalDist_apply_setOf_eq_one_iff_forall_mem_support]
        simp)
      ε fun x y hxy => by
      simpa only [prEvent_eq_evalDist_of_discrete] using hΦ x y hxy
  exact ⟨φ, hφ, hcard⟩

end Probability

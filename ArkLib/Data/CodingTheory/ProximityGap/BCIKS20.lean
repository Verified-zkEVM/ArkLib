/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Katerina Hristova, František Silváši, Julian Sutherland,
         Ilia Vlasov, Chung Thai Nguyen
-/

import ArkLib.Data.CodingTheory.ProximityGap.Basic
import ArkLib.Data.Probability.Instances


/-!
  # Definitions and Theorems about Proximity Gaps

  We state the main results from [BCIKS20] about proximity gap properties of Reed-Solomon codes.

  ## References

  * [Ben-Sasson, E., Carmon, D., Ishai, Y., Kopparty, S., and Saraf, S., *Proximity Gaps
      for Reed-Solomon Codes*][BCIKS20]
      * NB we use version 20210703:203025

  ## Main Definitions and Statements

  - statement of Theorem 1.2 (Proximity Gaps for Reed-Solomon codes) in [BCIKS20].
  - statements of all the correlated agreement theorems from [BCIKS20]:
  Theorem 1.4 (Main Theorem — Correlated agreement over affine lines),
  Theorem 4.1 (Correlated agreement over affine lines in the unique decoding regime),
  Theorem 1.5 (Correlated agreement for low-degree parameterised curves)
  Theorem 1.6 (Correlated agreement over affine spaces).

-/

namespace ProximityGap

open NNReal Finset Function
open scoped BigOperators
open NNReal Finset Function ProbabilityTheory Finset
open scoped BigOperators LinearCode
open Code

universe u v w k l


section BCIKS20ProximityGapSection5
variable {F : Type} [Field F] [DecidableEq F] [DecidableEq (RatFunc F)]
variable {n : ℕ}

section

open GuruswamiSudan
open Polynomial.Bivariate
open RatFunc
open scoped Polynomial.Bivariate

/-- The degree bound (a.k.a. `D_X`) for instantiation of Guruswami-Sudan
    in lemma 5.3 of [BCIKS20].
    D_X(m) = (m + 1/2)√rhon.
-/
noncomputable def D_X (rho : ℚ) (n m : ℕ) : ℝ := (m + 1/2) * (Real.sqrt rho) * n

open Classical in
noncomputable def proximity_gap_degree_bound (rho : ℚ) (m n : ℕ) : ℕ :=
  let b := D_X rho m n
  if h : ∃ n : ℕ, b = n
  then h.choose - 1
  else Nat.floor b

/-- The ball radius from lemma 5.3 of [BCIKS20],
    which follows from the Johnson bound.
    δ₀(rho, m) = 1 - √rho - √rho/2m.
-/
noncomputable def proximity_gap_johnson (rho : ℚ) (m : ℕ) : ℝ :=
  (1 : ℝ) - Real.sqrt rho - Real.sqrt rho / (2 * m)


omit [DecidableEq (RatFunc F)] in
/-- The first part of lemma 5.3 from [BCIKS20].
    Given the D_X (`proximity_gap_degree_bound`) and δ₀ (`proximity_gap_johnson`),
    a solution to Guruswami-Sudan system exists.
-/
lemma guruswami_sudan_for_proximity_gap_existence {k m : ℕ}
    {ωs : Fin n ↪ F} {f : Fin n → F} :
  ∃ Q,
    GuruswamiSudan.GSCondition (n := n) (F := F) k m
      (GuruswamiSudan.proximity_gap_degree_bound (n := n) k m) ωs f Q := by
  simpa using
    (GuruswamiSudan.guruswami_sudan_for_proximity_gap_existence (F := F) (n := n)
      (k := k) (m := m) (ωs := ωs) f)

open Polynomial in
omit [DecidableEq (RatFunc F)] in
/-- The second part of lemma 5.3 from [BCIKS20].
    For any solution Q of the Guruswami-Sudan system, and for any
    polynomial P ∈ RS[n, k, rho] such that δᵣ(w, P) ≤ δ₀(rho, m),
    we have that Y - P(X) divides Q(X, Y) in the polynomial ring
    F[X][Y]. Note that in F[X][Y], the term X actually refers to
    the outer variable, Y.
-/
lemma guruswami_sudan_for_proximity_gap_property {k m : ℕ} [NeZero n] [NeZero m]
  (hδ :
    (0 : ℝ) ≤
      (1 : ℝ) - Real.sqrt ((k + 1 : ℚ) / n) - Real.sqrt ((k + 1 : ℚ) / n) / (2 * m))
  {ωs : Fin n ↪ F} {f : Fin n → F} {Q : F[X][Y]}
  (hQ : GuruswamiSudan.GSCondition (n := n) (F := F) k m
    (GuruswamiSudan.proximity_gap_degree_bound (n := n) k m) ωs f Q)
  {p : F[X]} (hpdeg : p.natDegree < k)
  (hdist : Δ₀(f, p.eval ∘ ωs) ≤ GuruswamiSudan.proximity_gap_johnson (n := n) k m) :
  ((Polynomial.X : F[X][Y]) - Polynomial.C p) ∣ Q := by
  simpa using
    (GuruswamiSudan.guruswami_sudan_for_proximity_gap_property (F := F) (n := n)
      (k := k) (m := m) hδ (ωs := ωs) (f := f) hQ hpdeg hdist)

omit [DecidableEq (RatFunc F)] in
lemma proximity_gap_list_size_bound {k m : ℕ} [Fintype F] [NeZero n] [NeZero m] [NeZero k]
    (hk : 2 ≤ k)
    (hδ :
      (0 : ℝ) ≤
        (1 : ℝ) - Real.sqrt ((k + 1 : ℚ) / n) - Real.sqrt ((k + 1 : ℚ) / n) / (2 * m))
    {ωs : Fin n ↪ F} {f : Fin n → F} :
    ((messagePolynomials (F := F) k).filter fun p =>
      Δ₀(f, p.eval ∘ ωs) ≤ GuruswamiSudan.proximity_gap_johnson (n := n) k m).card
      ≤ GuruswamiSudan.proximity_gap_degree_bound (n := n) k m := by
  classical
  rcases (guruswami_sudan_for_proximity_gap_existence (F := F) (n := n) (k := k) (m := m)
    (ωs := ωs) (f := f)) with ⟨Q, hQ⟩
  exact
    GuruswamiSudan.list_size_le_degree_bound_of_GSCondition (F := F) (n := n) (k := k) (m := m)
      hk hδ hQ

end

end BCIKS20ProximityGapSection5

section BCIKS20ProximityGapSection7

variable {F : Type} [Field F] [DecidableEq F] [DecidableEq (RatFunc F)]
variable {n k m : ℕ}

namespace WeightedAgreement

open NNReal Finset Function

open scoped BigOperators

section

variable {n : Type} [Fintype n] [DecidableEq n]

variable {ι : Type} [Fintype ι] [Nonempty ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

variable (C : Submodule F (n → F)) [DecidablePred (· ∈ C)]
         (μ : ι → Set.Icc (0 : ℚ) 1)

/-- Relative μ-agreement between words `u` and `v`. -/
noncomputable def agree (u v : ι → F) : ℝ :=
  1 / (Fintype.card ι) * ∑ i ∈ { i | u i = v i }, (μ i).1

/-- `μ`-agreement between a word and a set `V`. -/
noncomputable def agree_set (u : ι → F) (V : Finset (ι → F)) [Nonempty V] : ℝ :=
  (Finset.image (agree μ u) V).max' (nonempty_coe_sort.1 (by aesop))

/-- Weighted size of a subdomain. -/
noncomputable def mu_set (ι' : Finset ι) : ℝ :=
  1/(Fintype.card ι) * ∑ i ∈ ι', (μ i).1

/-- Uniform weight on `ι` (all coordinates weight `1`). -/
noncomputable def uniformWeight : ι → Set.Icc (0 : ℚ) 1 :=
  fun _ => ⟨1, by constructor <;> norm_num⟩

omit [Nonempty ι] in
/-- `mu_set` for the uniform weight is just normalized cardinality. -/
lemma mu_set_uniform_eq (ι' : Finset ι) :
    mu_set (μ := (uniformWeight (ι := ι))) ι' =
      (ι'.card : ℝ) / (Fintype.card ι : ℝ) := by
  classical
  unfold mu_set uniformWeight
  simp [Finset.sum_const, nsmul_eq_mul, div_eq_mul_inv, mul_comm]

omit [Field F] [Fintype F] in
lemma agree_uniform_ge_one_sub_of_hamming_le
    [DecidableEq ι] {u v : ι → F} {δ : ℝ≥0}
    (h : Δ₀(u, v) ≤ Nat.floor (δ * Fintype.card ι)) :
    agree (μ := uniformWeight (ι := ι)) u v ≥ (1 - δ) := by
  classical
  -- Extract a large agreement set from the Hamming bound.
  have hS :=
    (closeToWord_iff_exists_agreementCols (u := u) (v := v)
      (e := Nat.floor (δ * Fintype.card ι))).1 h
  rcases hS with ⟨S, hS_card, hS_prop⟩
  let eqSet : Finset ι := Finset.filter (fun i => u i = v i) Finset.univ
  have hS_subset : S ⊆ eqSet := by
    intro i hi
    have hEq := (hS_prop i).1 hi
    simp [eqSet, hEq]
  have hcard_le : (S.card : ℝ) ≤ (eqSet.card : ℝ) := by
    exact_mod_cast (Finset.card_le_card hS_subset)
  let n : ℕ := Fintype.card ι
  let e : ℕ := Nat.floor (δ * Fintype.card ι)
  have hcard_ge : (n : ℝ) - (e : ℝ) ≤ (S.card : ℝ) := by
    have hcard_ge' : ((n - e : ℕ) : ℝ) ≤ (S.card : ℝ) :=
      (Nat.cast_le (α := ℝ)).2 hS_card
    have hsub_le :
        (n : ℝ) - (e : ℝ) ≤ ((n - e : ℕ) : ℝ) := by
      by_cases hle : e ≤ n
      · have hcast : ((n - e : ℕ) : ℝ) = (n : ℝ) - (e : ℝ) := by
          simp [Nat.cast_sub hle]
        simp [hcast]
      · have hle' : (n : ℝ) ≤ (e : ℝ) := by
          exact_mod_cast (le_of_not_ge hle)
        have hleft : (n : ℝ) - (e : ℝ) ≤ 0 := by
          exact sub_nonpos.mpr hle'
        have hright : ((n - e : ℕ) : ℝ) = 0 := by
          have : n - e = 0 := Nat.sub_eq_zero_of_le (le_of_not_ge hle)
          simp [this]
        simpa [hright] using hleft
    exact le_trans hsub_le hcard_ge'
  have hagree_eq :
      agree (μ := uniformWeight (ι := ι)) u v =
        (eqSet.card : ℝ) / (Fintype.card ι : ℝ) := by
    classical
    unfold agree uniformWeight eqSet
    simp [Finset.sum_const, div_eq_mul_inv, mul_comm]
  have hn_pos : (0 : ℝ) < (n : ℝ) := by
    dsimp [n]
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card ι)
  have hagree_ge :
      ((n : ℝ) - (e : ℝ)) / (Fintype.card ι : ℝ) ≤
        agree (μ := uniformWeight (ι := ι)) u v := by
    have h1 : ((n : ℝ) - (e : ℝ)) ≤ (eqSet.card : ℝ) :=
      le_trans hcard_ge hcard_le
    have h1' := div_le_div_of_nonneg_right h1 (le_of_lt hn_pos)
    simpa [hagree_eq] using h1'
  have hfloor :
      (e : ℝ) ≤ (δ : ℝ) * (n : ℝ) := by
    exact_mod_cast
      (Nat.floor_le (a := (δ : ℝ) * (n : ℝ)) (by positivity))
  have hnum :
      (n : ℝ) - (δ : ℝ) * (n : ℝ) ≤ (n : ℝ) - (e : ℝ) := by
    linarith
  have hnum' := div_le_div_of_nonneg_right hnum (le_of_lt hn_pos)
  have hn_ne : (n : ℝ) ≠ 0 := ne_of_gt hn_pos
  have hrewrite :
      ((n : ℝ) - (δ : ℝ) * (n : ℝ)) / (Fintype.card ι : ℝ) = (1 - (δ : ℝ)) := by
    calc
      ((n : ℝ) - (δ : ℝ) * (n : ℝ)) / (Fintype.card ι : ℝ) =
          (n : ℝ) / (Fintype.card ι : ℝ) -
            ((δ : ℝ) * (n : ℝ)) / (Fintype.card ι : ℝ) := by
              ring
      _ = (1 : ℝ) - (δ : ℝ) := by
        have hdiv1 :
            (n : ℝ) / (Fintype.card ι : ℝ) = (1 : ℝ) := by
          simp [n, hn_ne]
        have hdiv2 :
            ((δ : ℝ) * (n : ℝ)) / (Fintype.card ι : ℝ) = (δ : ℝ) := by
          simp [n, hn_ne]
        simp [hdiv1, hdiv2]
  have hbound :
      (1 - (δ : ℝ)) ≤ ((n : ℝ) - (e : ℝ)) / (Fintype.card ι : ℝ) := by
    -- `hnum'` gives (n - δn)/n ≤ (n - floor)/n; rewrite the left-hand side.
    calc
      (1 - (δ : ℝ)) =
          ((n : ℝ) - (δ : ℝ) * (n : ℝ)) / (Fintype.card ι : ℝ) := by
        simp [hrewrite]
      _ ≤ ((n : ℝ) - (e : ℝ)) / (Fintype.card ι : ℝ) := hnum'
  exact le_trans hbound hagree_ge

/-- `μ`-weighted correlated agreement. -/
noncomputable def weightedCorrelatedAgreement
  (C : Set (ι → F)) [Nonempty C] {k : ℕ} (U : Fin k → ι → F) : ℝ :=
  sSup {x |
    ∃ D' ⊆ (Finset.univ (α := ι)),
      x = mu_set μ D' ∧
      ∃ v : Fin k → ι → F, ∀ i, v i ∈ C ∧ ∀ j ∈ D', v i j = U i j
  }

open ReedSolomonCode

instance {domain : ι ↪ F} {deg : ℕ} : Nonempty (finCarrier domain deg) := by
  unfold finCarrier
  apply Nonempty.to_subtype
  simp [ReedSolomon.code]
  exact Submodule.nonempty (Polynomial.degreeLT F deg)

omit [Fintype ι] [Fintype F] [DecidableEq F] in
/--
Lemma 7.5 in [BCIKS20].

This is the “list agreement on a curve implies correlated agreement” lemma.

We are given two lists of functions `u, v : Fin (l + 2) → ι → F`, where each `v i` is a
Reed–Solomon codeword of degree `deg` over the evaluation domain `domain`.  From these
lists we form the bivariate “curves”

* `w   x z = ∑ i, z^(i.1) * u i x`,
* `wtilde x z = ∑ i, z^(i.1) * v i x`.

Fix a finite set `S' ⊆ F` with `S'.card > l + 1`, and a (product) measure `μ` on the
evaluation domain `ι`.  Assume that for every `z ∈ S'` the one-dimensional functions
`w · z` and `wtilde · z` have agreement at least `α` with respect to `μ`.  Then the set
of points `x` on which *all* coordinates agree, i.e. `u i x = v i x` for every `i`,
has μ-measure strictly larger than

`α - (l + 1) / (S'.card - (l + 1))`.
-/
lemma list_agreement_on_curve_implies_correlated_agreement_bound
  [DecidableEq ι] [Fintype ι] [DecidableEq F] {k l : ℕ} {u : Fin (l + 2) → ι → F}
  {deg : ℕ} {domain : ι ↪ F}
  {μ : ι → Set.Icc (0 : ℚ) 1}
  {α : ℝ≥0}
  {v : Fin (l + 2) → ι → F}
  (hv : ∀ i, v i ∈ (ReedSolomon.code domain deg))
  {S' : Finset F}
  (hS'_card : S'.card > l + 1) :
  letI w (x : ι) (z : F) : F := ∑ i, z ^ i.1 * u i x
  letI wtilde (x : ι) (z : F) : F := ∑ i, z ^ i.1 * v i x
  (hS'_agree : ∀ z ∈ S', agree μ (w · z) (wtilde · z) ≥ α) →
  mu_set μ {x : ι | ∀ i, u i x = v i x} >
  α - ((l + 1) : ℝ) / (S'.card - (l + 1)) := by
  classical
  have _ := k
  have _ := hv
  intro hS'_agree
  let w (x : ι) (z : F) : F := ∑ i, z ^ i.1 * u i x
  let wtilde (x : ι) (z : F) : F := ∑ i, z ^ i.1 * v i x
  have hS'_agree' : ∀ z ∈ S', agree μ (w · z) (wtilde · z) ≥ α := by
    intro z hz
    simpa [w, wtilde] using hS'_agree z hz
  let μw : ι → ℝ := fun x => (μ x).1
  have hμw_nonneg : ∀ x, 0 ≤ μw x := by
    intro x
    have hx : (0 : ℚ) ≤ (μ x).1 := (μ x).2.1
    exact (Rat.cast_nonneg (K := ℝ)).2 hx
  have hμw_le_one : ∀ x, μw x ≤ 1 := by
    intro x
    have hx : (μ x).1 ≤ 1 := (μ x).2.2
    have : μw x ≤ ((1 : ℚ) : ℝ) := (Rat.cast_le (K := ℝ)).2 hx
    simpa using this

  have mu_set_eq (T : Finset ι) :
      mu_set μ T = 1 / (Fintype.card ι : ℝ) * ∑ x ∈ T, μw x := by
    unfold mu_set
    simp [μw, Rat.cast_sum]
  have mu_set_nonneg (T : Finset ι) : 0 ≤ mu_set μ T := by
    rw [mu_set_eq (T := T)]
    refine mul_nonneg (by positivity) (Finset.sum_nonneg (fun x hx => hμw_nonneg x))
  have mu_set_univ_le_one : mu_set μ (Finset.univ : Finset ι) ≤ 1 := by
    rw [mu_set_eq (T := (Finset.univ : Finset ι))]
    have hsum_le :
        (∑ x ∈ (Finset.univ : Finset ι), μw x) ≤ ∑ x ∈ (Finset.univ : Finset ι), (1 : ℝ) := by
      refine Finset.sum_le_sum ?_
      intro x hx
      exact hμw_le_one x
    have hsum_one :
        (∑ x ∈ (Finset.univ : Finset ι), (1 : ℝ)) = (Fintype.card ι : ℝ) := by
      simp [Finset.sum_const, nsmul_eq_mul]
    have hsum_le_card :
        (∑ x ∈ (Finset.univ : Finset ι), μw x) ≤ (Fintype.card ι : ℝ) := by
      simpa [hsum_one] using hsum_le
    have := mul_le_mul_of_nonneg_left hsum_le_card (by positivity : 0 ≤ (1 / (Fintype.card ι : ℝ)))
    have hcard_ne : (Fintype.card ι : ℝ) ≠ 0 := by
      exact_mod_cast (Fintype.card_ne_zero : Fintype.card ι ≠ 0)
    simpa [div_eq_mul_inv, hcard_ne] using this

  let B : Finset ι := {x : ι | ∀ i, u i x = v i x}
  let p : ι → Polynomial F := fun x =>
    ∑ i : Fin (l + 2), Polynomial.monomial i.1 (u i x - v i x)
  let Zx : ι → Finset F := fun x =>
    S'.filter (fun z => w x z = wtilde x z)

  have eval_sum_monomial (a : Fin (l + 2) → F) (z : F) :
      (∑ i : Fin (l + 2), Polynomial.monomial i.1 (a i)).eval z =
        ∑ i : Fin (l + 2), (a i) * z ^ i.1 := by
    change (Polynomial.evalRingHom z)
        (∑ i : Fin (l + 2), Polynomial.monomial i.1 (a i)) = _
    simp [map_sum, Polynomial.eval_monomial]

  have p_eval (x : ι) (z : F) :
      (p x).eval z = w x z - wtilde x z := by
    have h_eval :
        (p x).eval z = ∑ i : Fin (l + 2), (u i x - v i x) * z ^ i.1 := by
      simpa [p] using eval_sum_monomial (a := fun i => u i x - v i x) z
    calc
      (p x).eval z
          = ∑ i : Fin (l + 2), (u i x - v i x) * z ^ i.1 := h_eval
      _ = ∑ i : Fin (l + 2), (u i x * z ^ i.1 - v i x * z ^ i.1) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            simp [sub_mul]
      _ = (∑ i : Fin (l + 2), u i x * z ^ i.1) - ∑ i : Fin (l + 2), v i x * z ^ i.1 := by
            simp [Finset.sum_sub_distrib]
      _ = (∑ i : Fin (l + 2), z ^ i.1 * u i x) - ∑ i : Fin (l + 2), z ^ i.1 * v i x := by
            simp [mul_comm]
      _ = w x z - wtilde x z := by
            rfl

  have p_natDegree_le (x : ι) : (p x).natDegree ≤ l + 1 := by
    classical
    have h1 :
        (p x).natDegree ≤
          Finset.fold max 0
            (fun i : Fin (l + 2) =>
              (Polynomial.monomial i.1 (u i x - v i x)).natDegree)
            (Finset.univ : Finset (Fin (l + 2))) := by
      simpa [p] using
        (Polynomial.natDegree_sum_le (s := (Finset.univ : Finset (Fin (l + 2))))
          (f := fun i : Fin (l + 2) => Polynomial.monomial i.1 (u i x - v i x)))
    have hfold :
        Finset.fold max 0
            (fun i : Fin (l + 2) =>
              (Polynomial.monomial i.1 (u i x - v i x)).natDegree)
            (Finset.univ : Finset (Fin (l + 2)))
          ≤ l + 1 := by
      classical
      refine Finset.induction (s := (Finset.univ : Finset (Fin (l + 2)))) (by simp) ?_
      intro a s ha hs
      have ha_le : (Polynomial.monomial a.1 (u a x - v a x)).natDegree ≤ l + 1 := by
        have hdeg : (Polynomial.monomial a.1 (u a x - v a x)).natDegree ≤ a.1 :=
          Polynomial.natDegree_monomial_le (a := (u a x - v a x))
        have hval : a.1 ≤ l + 1 := by
          exact Nat.lt_succ_iff.mp a.isLt
        exact le_trans hdeg hval
      simpa [Finset.fold_insert ha] using max_le ha_le hs
    exact le_trans h1 hfold

  have sum_if_val_eq (a : Fin (l + 2) → ι → F) (x : ι) (i : Fin (l + 2)) :
      (∑ j : Fin (l + 2), if j.1 = i.1 then a j x else 0) = a i x := by
    classical
    have h0 :
        ∀ b ∈ (Finset.univ : Finset (Fin (l + 2))),
          b ≠ i → (if b.1 = i.1 then a b x else 0) = 0 := by
      intro b hb hbi
      have : b.1 ≠ i.1 := by
        intro hval
        exact hbi (Fin.ext hval)
      simp [this]
    have h1 :
        i ∉ (Finset.univ : Finset (Fin (l + 2))) →
          (if i.1 = i.1 then a i x else 0) = 0 := by
      intro hi
      exfalso
      exact hi (Finset.mem_univ i)
    have h :=
      Finset.sum_eq_single (s := (Finset.univ : Finset (Fin (l + 2))))
        (f := fun j => if j.1 = i.1 then a j x else 0) i h0 h1
    simp [h]
  have p_coeff (x : ι) (i : Fin (l + 2)) : (p x).coeff i.1 = u i x - v i x := by
    classical
    simp [p, Polynomial.coeff_monomial, sum_if_val_eq]

  have mem_B_of_Zx_large (x : ι) (hx : (Zx x).card > l + 1) : x ∈ B := by
    have hpdeg : (p x).natDegree ≤ l + 1 := p_natDegree_le x
    have heval : ∀ z ∈ Zx x, (p x).eval z = 0 := by
      intro z hz
      have hw' : w x z = wtilde x z := (Finset.mem_filter.1 hz).2
      simp [p_eval x z, hw']
    have hnat : (p x).natDegree < (Zx x).card := lt_of_le_of_lt hpdeg hx
    have hp0 : p x = 0 :=
      Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero' (p x) (Zx x) heval hnat
    have hx_eq : ∀ i, u i x = v i x := by
      intro i
      have hc : (p x).coeff i.1 = 0 := by
        simp [hp0]
      have hci : u i x - v i x = 0 := by
        simpa [p_coeff x i] using hc
      exact sub_eq_zero.mp hci
    simp [B, hx_eq]

  have Zx_card_le (x : ι) (hxB : x ∉ B) : (Zx x).card ≤ l + 1 := by
    by_contra hle
    exact hxB (mem_B_of_Zx_large x (Nat.lt_of_not_ge hle))

  have Zx_eq_S' (x : ι) (hxB : x ∈ B) : Zx x = S' := by
    have hx' : ∀ i, u i x = v i x := by
      simpa [B] using hxB
    have hw' : ∀ z, w x z = wtilde x z := by
      intro z
      refine Finset.sum_congr rfl ?_
      intro i hi
      simp [hx' i]
    ext z
    constructor
    · intro hz
      exact (Finset.mem_filter.1 hz).1
    · intro hzS
      refine Finset.mem_filter.2 ?_
      exact ⟨hzS, hw' z⟩

  let A : F → Finset ι := fun z => {x : ι | w x z = wtilde x z}
  have hterm : ∀ z ∈ S', (α : ℝ) ≤ mu_set μ (A z) := by
    intro z hzS
    simpa [A, agree, mu_set] using (hS'_agree' z hzS)
  have hsum_lower :
      (S'.card : ℝ) * (α : ℝ) ≤ ∑ z ∈ S', mu_set μ (A z) := by
    have h :=
      Finset.sum_le_sum (s := S') (f := fun _ => (α : ℝ)) (g := fun z => mu_set μ (A z)) hterm
    simpa [Finset.sum_const, nsmul_eq_mul] using h

  have hsum_upper :
      (∑ z ∈ S', mu_set μ (A z))
        ≤ (S'.card : ℝ) * mu_set μ B + (l + 1 : ℝ) * mu_set μ Bᶜ := by
    have hLHS :
        (∑ z ∈ S', mu_set μ (A z))
          = (1 / (Fintype.card ι : ℝ)) * (∑ z ∈ S', ∑ x ∈ A z, μw x) := by
      calc
        (∑ z ∈ S', mu_set μ (A z))
            = ∑ z ∈ S', (1 / (Fintype.card ι : ℝ)) * ∑ x ∈ A z, μw x := by
                simp [mu_set_eq, A]
        _ = (1 / (Fintype.card ι : ℝ)) * (∑ z ∈ S', ∑ x ∈ A z, μw x) := by
                simpa using
                  (Finset.mul_sum (s := S') (f := fun z => ∑ x ∈ A z, μw x)
                    (a := (1 / (Fintype.card ι : ℝ)))).symm
    have htotal :
        (∑ z ∈ S', ∑ x ∈ A z, μw x)
          ≤ (S'.card : ℝ) * (∑ x ∈ B, μw x) + (l + 1 : ℝ) * (∑ x ∈ Bᶜ, μw x) := by
      have hswap :
          (∑ z ∈ S', ∑ x ∈ A z, μw x)
            = ∑ x ∈ (Finset.univ : Finset ι), ∑ z ∈ S', if w x z = wtilde x z then μw x else 0 := by
        calc
          (∑ z ∈ S', ∑ x ∈ A z, μw x)
              = ∑ z ∈ S', ∑ x ∈ (Finset.univ : Finset ι),
                  if w x z = wtilde x z then μw x else 0 := by
                    refine Finset.sum_congr rfl ?_
                    intro z hz
                    simpa [A] using
                      (Finset.sum_filter (s := (Finset.univ : Finset ι))
                        (p := fun x => w x z = wtilde x z) (f := μw))
          _ = ∑ x ∈ (Finset.univ : Finset ι), ∑ z ∈ S', if w x z = wtilde x z then μw x else 0 := by
                simpa using
                  (Finset.sum_comm (s := S') (t := (Finset.univ : Finset ι))
                    (f := fun z x => if w x z = wtilde x z then μw x else 0))
      have hsplit :
          (∑ x : ι, ∑ z ∈ S', if w x z = wtilde x z then μw x else 0)
            = (∑ x ∈ B, ∑ z ∈ S', if w x z = wtilde x z then μw x else 0)
              + (∑ x ∈ Bᶜ, ∑ z ∈ S', if w x z = wtilde x z then μw x else 0) := by
        have :=
          (Finset.sum_add_sum_compl (s := B)
            (f := fun x : ι => ∑ z ∈ S', if w x z = wtilde x z then μw x else 0))
        simpa [add_comm, add_left_comm, add_assoc] using this.symm
      have hB :
          (∑ x ∈ B, ∑ z ∈ S', if w x z = wtilde x z then μw x else 0)
            = (S'.card : ℝ) * (∑ x ∈ B, μw x) := by
        have :
            (∑ x ∈ B, ∑ z ∈ S', if w x z = wtilde x z then μw x else 0)
              = ∑ x ∈ B, (S'.card : ℝ) * μw x := by
            refine Finset.sum_congr rfl ?_
            intro x hx
            have hZ : Zx x = S' := Zx_eq_S' x hx
            have :
                (∑ z ∈ S', if w x z = wtilde x z then μw x else 0)
                  = (S'.card : ℝ) * μw x := by
                have :
                    (∑ z ∈ S', if w x z = wtilde x z then μw x else 0)
                      = ((S'.filter (fun z => w x z = wtilde x z)).card : ℝ) * μw x := by
                    have :
                        (∑ z ∈ S', if w x z = wtilde x z then μw x else 0)
                          = (S'.filter (fun z => w x z = wtilde x z)).card • (μw x) := by
                        calc
                          (∑ z ∈ S', if w x z = wtilde x z then μw x else 0)
                              = ∑ z ∈ S' with w x z = wtilde x z, μw x := by
                                  exact
                                    (Finset.sum_filter (s := S')
                                      (p := fun z => w x z = wtilde x z)
                                      (f := fun _ => μw x)).symm
                          _ = (S'.filter (fun z => w x z = wtilde x z)).card • (μw x) := by
                                  exact
                                    (Finset.sum_const
                                      (s := S'.filter (fun z => w x z = wtilde x z))
                                      (μw x))
                    have this' := this
                    simp [nsmul_eq_mul] at this'
                    exact this'
                have this' := this
                simp [Zx, hZ] at this'
                exact this'
            have this' := this
            simp [this']            
        -- turn the pointwise form into a factorised form
        have hfactor :
            (∑ x ∈ B, (S'.card : ℝ) * μw x) = (S'.card : ℝ) * (∑ x ∈ B, μw x) := by
          exact (Finset.mul_sum (s := B) (f := fun x => μw x) (a := (S'.card : ℝ))).symm
        exact this.trans hfactor
      have hBc :
          (∑ x ∈ Bᶜ, ∑ z ∈ S', if w x z = wtilde x z then μw x else 0)
            ≤ (l + 1 : ℝ) * (∑ x ∈ Bᶜ, μw x) := by
        have hpoint :
            ∀ x ∈ Bᶜ,
              (∑ z ∈ S', if w x z = wtilde x z then μw x else 0)
                ≤ (l + 1 : ℝ) * μw x := by
          intro x hx
          have hsum :
              (∑ z ∈ S', if w x z = wtilde x z then μw x else 0)
                = ((Zx x).card : ℝ) * μw x := by
            have :
                (∑ z ∈ S', if w x z = wtilde x z then μw x else 0)
                  = ((S'.filter (fun z => w x z = wtilde x z)).card : ℝ) * μw x := by
              have :
                  (∑ z ∈ S', if w x z = wtilde x z then μw x else 0)
                    = (S'.filter (fun z => w x z = wtilde x z)).card • (μw x) := by
                calc
                  (∑ z ∈ S', if w x z = wtilde x z then μw x else 0)
                      = ∑ z ∈ S' with w x z = wtilde x z, μw x := by
                          exact
                            (Finset.sum_filter (s := S')
                              (p := fun z => w x z = wtilde x z)
                              (f := fun _ => μw x)).symm
                  _ = (S'.filter (fun z => w x z = wtilde x z)).card • (μw x) := by
                          exact
                            (Finset.sum_const
                              (s := S'.filter (fun z => w x z = wtilde x z))
                              (μw x))
              have this' := this
              simp [nsmul_eq_mul] at this'
              exact this'
            have this' := this
            simp at this'
            exact this'
          have hcard : (Zx x).card ≤ l + 1 := Zx_card_le x (by simpa using hx)
          have hcardR : ((Zx x).card : ℝ) ≤ (l + 1 : ℝ) := by exact_mod_cast hcard
          have := mul_le_mul_of_nonneg_right hcardR (hμw_nonneg x)
          simpa [hsum, mul_assoc] using this
        have hsum' :
            (∑ x ∈ Bᶜ, ∑ z ∈ S', if w x z = wtilde x z then μw x else 0)
              ≤ ∑ x ∈ Bᶜ, (l + 1 : ℝ) * μw x := by
          refine Finset.sum_le_sum ?_
          intro x hx
          exact hpoint x hx
        have : ∑ x ∈ Bᶜ, (l + 1 : ℝ) * μw x = (l + 1 : ℝ) * (∑ x ∈ Bᶜ, μw x) := by
          exact (Finset.mul_sum (s := Bᶜ) (f := fun x => μw x) (a := (l + 1 : ℝ))).symm
        have hsum'' : ∑ x ∈ Bᶜ, (l + 1 : ℝ) * μw x = (l + 1 : ℝ) * (∑ x ∈ Bᶜ, μw x) := by
          exact this
        exact le_trans hsum' (le_of_eq hsum'')
      have h_univ :
          (∑ x ∈ (Finset.univ : Finset ι), ∑ z ∈ S', if w x z = wtilde x z then μw x else 0)
            ≤ (S'.card : ℝ) * (∑ x ∈ B, μw x) + (l + 1 : ℝ) * (∑ x ∈ Bᶜ, μw x) := by
        calc
          (∑ x ∈ (Finset.univ : Finset ι), ∑ z ∈ S', if w x z = wtilde x z then μw x else 0)
              = (∑ x ∈ B, ∑ z ∈ S', if w x z = wtilde x z then μw x else 0)
                + (∑ x ∈ Bᶜ, ∑ z ∈ S', if w x z = wtilde x z then μw x else 0) := by
                    exact hsplit
          _ ≤ (S'.card : ℝ) * (∑ x ∈ B, μw x) + (l + 1 : ℝ) * (∑ x ∈ Bᶜ, μw x) := by
                exact add_le_add (le_of_eq hB) hBc
      have h_univ' := h_univ
      simpa [hswap] using h_univ'
    have hmul :
        (1 / (Fintype.card ι : ℝ)) * (∑ z ∈ S', ∑ x ∈ A z, μw x)
          ≤ (1 / (Fintype.card ι : ℝ)) *
              ((S'.card : ℝ) * (∑ x ∈ B, μw x) + (l + 1 : ℝ) * (∑ x ∈ Bᶜ, μw x)) := by
      exact mul_le_mul_of_nonneg_left htotal (by positivity : 0 ≤ (1 / (Fintype.card ι : ℝ)))
    have hR :
        (1 / (Fintype.card ι : ℝ)) *
              ((S'.card : ℝ) * (∑ x ∈ B, μw x) + (l + 1 : ℝ) * (∑ x ∈ Bᶜ, μw x))
          = (S'.card : ℝ) * mu_set μ B + (l + 1 : ℝ) * mu_set μ Bᶜ := by
      simp [mu_set_eq, mul_add, add_mul]
      ring
    rw [hLHS]
    have := le_trans hmul (le_of_eq hR)
    simpa using this

  -- isolate `mu_set μ B`
  have hDpos : (0 : ℝ) < (S'.card : ℝ) - (l + 1 : ℝ) := by
    have hlt : (l + 1 : ℝ) < (S'.card : ℝ) := by exact_mod_cast hS'_card
    exact sub_pos.2 hlt
  have hDne : (S'.card : ℝ) - (l + 1 : ℝ) ≠ 0 := ne_of_gt hDpos
  have hmulU : (l + 1 : ℝ) * mu_set μ (Finset.univ : Finset ι) ≤ (l + 1 : ℝ) := by
    have := mul_le_mul_of_nonneg_left mu_set_univ_le_one (by positivity : 0 ≤ (l + 1 : ℝ))
    simpa using this
  have hsum_main :
      (S'.card : ℝ) * (α : ℝ)
        ≤ ((S'.card : ℝ) - (l + 1 : ℝ)) * mu_set μ B
          + (l + 1 : ℝ) * mu_set μ (Finset.univ : Finset ι) := by
    -- rewrite `Bᶜ` as `univ - B`
    have hBcompl :
        mu_set μ Bᶜ = mu_set μ (Finset.univ : Finset ι) - mu_set μ B := by
      -- from `mu_set B + mu_set Bᶜ = mu_set univ`
      have hsum :
          mu_set μ B + mu_set μ Bᶜ = mu_set μ (Finset.univ : Finset ι) := by
        rw [mu_set_eq (T := B), mu_set_eq (T := Bᶜ), mu_set_eq (T := (Finset.univ : Finset ι))]
        have hsum' : (∑ x ∈ B, μw x) + (∑ x ∈ Bᶜ, μw x) = ∑ x : ι, μw x := by
          simpa using (Finset.sum_add_sum_compl (s := B) (f := μw))
        -- factor out the common scalar and use `Finset.sum_add_sum_compl`
        calc
          (1 / (Fintype.card ι : ℝ)) * (∑ x ∈ B, μw x)
              + (1 / (Fintype.card ι : ℝ)) * (∑ x ∈ Bᶜ, μw x)
              = (1 / (Fintype.card ι : ℝ)) * ((∑ x ∈ B, μw x) + (∑ x ∈ Bᶜ, μw x)) := by
                ring
          _ = (1 / (Fintype.card ι : ℝ)) * ∑ x : ι, μw x := by simp [hsum']
      apply (eq_sub_iff_add_eq).2
      simpa [add_comm, add_left_comm, add_assoc] using hsum
    have hupper' :
        ∑ z ∈ S', mu_set μ (A z)
          ≤ ((S'.card : ℝ) - (l + 1 : ℝ)) * mu_set μ B
            + (l + 1 : ℝ) * mu_set μ (Finset.univ : Finset ι) := by
      have h := hsum_upper
      have :
          (S'.card : ℝ) * mu_set μ B + (l + 1 : ℝ) * mu_set μ Bᶜ
            = ((S'.card : ℝ) - (l + 1 : ℝ)) * mu_set μ B
                + (l + 1 : ℝ) * mu_set μ (Finset.univ : Finset ι) := by
        -- rewrite `μ(Bᶜ)` as `μ(univ) - μ(B)` and rearrange
        simp [hBcompl]
        ring
      simpa [this] using h
    have := le_trans hsum_lower hupper'
    simpa using this

  have hnum_le :
      (S'.card : ℝ) * (α : ℝ) - (l + 1 : ℝ)
        ≤ ((S'.card : ℝ) - (l + 1 : ℝ)) * mu_set μ B := by
    have hsub := sub_le_sub_right hsum_main ((l + 1 : ℝ) * mu_set μ (Finset.univ : Finset ι))
    have hsub' :
        (S'.card : ℝ) * (α : ℝ) - (l + 1 : ℝ) * mu_set μ (Finset.univ : Finset ι)
          ≤ ((S'.card : ℝ) - (l + 1 : ℝ)) * mu_set μ B := by
      simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using hsub
    have hdrop :
        (S'.card : ℝ) * (α : ℝ) - (l + 1 : ℝ)
          ≤ (S'.card : ℝ) * (α : ℝ) - (l + 1 : ℝ) * mu_set μ (Finset.univ : Finset ι) := by
      simpa using (sub_le_sub_left hmulU ((S'.card : ℝ) * (α : ℝ)))
    exact le_trans hdrop hsub'
  have hB_lower :
      ((S'.card : ℝ) * (α : ℝ) - (l + 1 : ℝ)) / ((S'.card : ℝ) - (l + 1 : ℝ))
        ≤ mu_set μ B := by
    have hmul :=
      mul_le_mul_of_nonneg_left hnum_le (by positivity : 0 ≤ (1 / ((S'.card : ℝ) - (l + 1 : ℝ))))
    simpa [div_eq_mul_inv, hDne, mul_assoc, mul_left_comm, mul_comm] using hmul

  -- final strictness
  by_cases hα : α = 0
  · have hRHS_neg :
        (α : ℝ) - (l + 1 : ℝ) / ((S'.card : ℝ) - (l + 1 : ℝ)) < 0 := by
        subst hα
        have hlpos : (0 : ℝ) < (l + 1 : ℝ) := by exact_mod_cast (Nat.succ_pos l)
        have hfracpos : 0 < (l + 1 : ℝ) / ((S'.card : ℝ) - (l + 1 : ℝ)) := div_pos hlpos hDpos
        simpa [sub_eq_add_neg] using (neg_neg_of_pos hfracpos)
    have hB_nonneg : 0 ≤ mu_set μ B := mu_set_nonneg B
    exact lt_of_lt_of_le hRHS_neg hB_nonneg
  · have hαpos : (0 : ℝ) < (α : ℝ) := by
        have : 0 < α :=
          lt_of_le_of_ne (show (0 : ℝ≥0) ≤ α from bot_le) (by simpa [eq_comm] using hα)
        exact (NNReal.coe_pos).2 this
    have hfrac :
        (α : ℝ) - (l + 1 : ℝ) / ((S'.card : ℝ) - (l + 1 : ℝ))
          < ((S'.card : ℝ) * (α : ℝ) - (l + 1 : ℝ)) / ((S'.card : ℝ) - (l + 1 : ℝ)) := by
      have hdiff :
          ((S'.card : ℝ) * (α : ℝ) - (l + 1 : ℝ)) / ((S'.card : ℝ) - (l + 1 : ℝ))
            - ((α : ℝ) - (l + 1 : ℝ) / ((S'.card : ℝ) - (l + 1 : ℝ)))
            = (α : ℝ) * (l + 1 : ℝ) / ((S'.card : ℝ) - (l + 1 : ℝ)) := by
        field_simp [hDne]
        ring
      have hpos :
          0 < (α : ℝ) * (l + 1 : ℝ) / ((S'.card : ℝ) - (l + 1 : ℝ)) := by
        have hlpos : (0 : ℝ) < (l + 1 : ℝ) := by exact_mod_cast (Nat.succ_pos l)
        exact div_pos (mul_pos hαpos hlpos) hDpos
      have : 0 <
          ((S'.card : ℝ) * (α : ℝ) - (l + 1 : ℝ)) / ((S'.card : ℝ) - (l + 1 : ℝ))
            - ((α : ℝ) - (l + 1 : ℝ) / ((S'.card : ℝ) - (l + 1 : ℝ))) := by
        simpa [hdiff] using hpos
      exact sub_pos.1 this
    exact lt_of_lt_of_le hfrac hB_lower

/-
Lemma 7.6 in [BCIKS20].

This is the “integral-weight” strengthening of the list-agreement-on-a-curve ⇒
correlated-agreement bound.

We have two lists of functions `u, v : Fin (l + 2) → ι → F`, where each `v i` is a
Reed–Solomon codeword of degree `deg` over the evaluation domain `domain`.  From
these lists we form the bivariate “curves”
* `w x z     = ∑ i, z^(i.1) * u i x`,
* `wtilde x z = ∑ i, z^(i.1) * v i x`.

The domain `ι` is finite and is equipped with a weighted measure `μ`, where each
weight `μ i` is a rational with common denominator `M`.  Let `S' ⊆ F` be a set of
field points with
* `S'.card > l + 1`, and
* `S'.card ≥ (M * Fintype.card ι + 1) * (l + 1)`.

Assume that for every `z ∈ S'` the µ-weighted agreement between `w · z` and
`wtilde · z` is at least `α`.  Then the µ-measure of the set of points where *all*
coordinates agree, i.e. where `u i x = v i x` for every `i`, is at least `α`:

`mu_set μ {x | ∀ i, u i x = v i x} ≥ α`.
-/
omit n k m C μ [Fintype n] [DecidableEq n] [DecidablePred (· ∈ C)] [Nonempty ι]
  [Fintype ι] [Fintype F] [DecidableEq F] in
lemma sufficiently_large_list_agreement_on_curve_implies_correlated_agreement
  [DecidableEq ι] [Fintype ι] [Nonempty ι] [DecidableEq F] {k l : ℕ} {u : Fin (l + 2) → ι → F}
  {deg : ℕ} {domain : ι ↪ F}
  {μ : ι → Set.Icc (0 : ℚ) 1}
  {α : ℝ≥0}
  {M : ℕ}
  (hμ : ∀ i, ∃ n : ℤ, (μ i).1 = (n : ℚ) / (M : ℚ))
  {v : Fin (l + 2) → ι → F}
  (hv : ∀ i, v i ∈ ReedSolomon.code domain deg)
  {S' : Finset F}
  (hS'_card : S'.card > l + 1)
  (hS'_card₁ : S'.card ≥ (M * Fintype.card ι + 1) * (l + 1)) :
  letI w (x : ι) (z : F) : F := ∑ i, z ^ i.1 * u i x
  letI wtilde (x : ι) (z : F) : F := ∑ i, z ^ i.1 * v i x
  (hS'_agree : ∀ z ∈ S', agree μ (w · z) (wtilde · z) ≥ α) →
  mu_set μ {x : ι | ∀ i, u i x = v i x} ≥ α := by
  classical
  intro hS'_agree
  let w (x : ι) (z : F) : F := ∑ i, z ^ i.1 * u i x
  let wtilde (x : ι) (z : F) : F := ∑ i, z ^ i.1 * v i x
  have hS'_agree' : ∀ z ∈ S', agree μ (w · z) (wtilde · z) ≥ α := by
    simpa [w, wtilde] using hS'_agree

  by_cases hM0 : M = 0
  · subst hM0
    have hμ0 : ∀ i, (μ i).1 = 0 := by
      intro i
      rcases hμ i with ⟨n, hn⟩
      simpa using hn

    have hcard_pos : 0 < S'.card := Nat.lt_trans (Nat.succ_pos l) hS'_card
    have hS'nonempty : S'.Nonempty := Finset.card_pos.mp hcard_pos
    rcases hS'nonempty with ⟨z, hz⟩

    have hagree0 : agree μ (w · z) (wtilde · z) = 0 := by
      unfold agree
      simp [hμ0]

    have hα0 : α = 0 := by
      have hα_le0_real : (α : ℝ) ≤ 0 := by
        have := hS'_agree' z hz
        simpa [hagree0] using this
      have hα_le0 : α ≤ 0 := by
        exact_mod_cast hα_le0_real
      exact le_antisymm hα_le0 (by simp)

    have hmuB0 : mu_set μ {x : ι | ∀ i, u i x = v i x} = 0 := by
      unfold mu_set
      simp [hμ0]

    simp [hα0, hmuB0]

  have hM : M ≠ 0 := hM0
  have hMn : M * Fintype.card ι ≠ 0 := by
    have hMpos : 0 < M := Nat.pos_of_ne_zero hM
    have hcardpos : 0 < Fintype.card ι := Fintype.card_pos
    exact Nat.ne_of_gt (Nat.mul_pos hMpos hcardpos)

  choose nfun hnfun using hμ

  let den : ℝ := (M : ℝ) * (Fintype.card ι : ℝ)
  have hden_pos : 0 < den := by
    have hMpos : 0 < (M : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hM
    have hcardpos : 0 < (Fintype.card ι : ℝ) := by
      exact_mod_cast (Fintype.card_pos : 0 < Fintype.card ι)
    simpa [den] using mul_pos hMpos hcardpos
  have hden_ne : den ≠ 0 := ne_of_gt hden_pos

  have hw : ∀ i, ((μ i).1 : ℝ) = (nfun i : ℝ) / (M : ℝ) := by
    intro i
    have hq := hnfun i
    have : ((μ i).1 : ℝ) = ((nfun i : ℚ) / (M : ℚ) : ℝ) := by
      exact_mod_cast hq
    simpa using this

  have agree_eq_int_div (a b : ι → F) :
      agree μ a b = ((∑ i ∈ {i | a i = b i}, nfun i) : ℝ) / den := by
    classical
    have : agree μ a b = (1 / (Fintype.card ι : ℝ)) * ∑ i ∈ {i | a i = b i}, ((μ i).1 : ℝ) := by
      unfold agree
      simp [Rat.cast_sum]
    calc
      agree μ a b
          = (1 / (Fintype.card ι : ℝ)) * ∑ i ∈ {i | a i = b i}, ((μ i).1 : ℝ) := this
      _ = (1 / (Fintype.card ι : ℝ)) * ∑ i ∈ {i | a i = b i}, (nfun i : ℝ) / (M : ℝ) := by
            refine congrArg (fun s => (1 / (Fintype.card ι : ℝ)) * s) ?_
            refine Finset.sum_congr rfl ?_
            intro i hi
            simp [hw]
      _ = (1 / (Fintype.card ι : ℝ)) * ((∑ i ∈ {i | a i = b i}, (nfun i : ℝ)) / (M : ℝ)) := by
            simp [div_eq_mul_inv]
            simpa using
              (Finset.sum_mul (s := {i | a i = b i}) (f := fun i => (nfun i : ℝ))
                (a := (M : ℝ)⁻¹)).symm
      _ = ((∑ i ∈ {i | a i = b i}, nfun i) : ℝ) / den := by
            simp [den, div_eq_mul_inv]
            ring

  have mu_set_eq_int_div (T : Finset ι) :
      mu_set μ T = ((∑ i ∈ T, nfun i) : ℝ) / den := by
    classical
    have : mu_set μ T = (1 / (Fintype.card ι : ℝ)) * ∑ i ∈ T, ((μ i).1 : ℝ) := by
      unfold mu_set
      simp [Rat.cast_sum]
    calc
      mu_set μ T
          = (1 / (Fintype.card ι : ℝ)) * ∑ i ∈ T, ((μ i).1 : ℝ) := this
      _ = (1 / (Fintype.card ι : ℝ)) * ∑ i ∈ T, (nfun i : ℝ) / (M : ℝ) := by
            refine congrArg (fun s => (1 / (Fintype.card ι : ℝ)) * s) ?_
            refine Finset.sum_congr rfl ?_
            intro i hi
            simp [hw]
      _ = (1 / (Fintype.card ι : ℝ)) * ((∑ i ∈ T, (nfun i : ℝ)) / (M : ℝ)) := by
            simp [div_eq_mul_inv]
            simpa using
              (Finset.sum_mul (s := T) (f := fun i => (nfun i : ℝ)) (a := (M : ℝ)⁻¹)).symm
      _ = ((∑ i ∈ T, nfun i) : ℝ) / den := by
            simp [den, div_eq_mul_inv]
            ring

  let α0_num : ℤ := Int.ceil ((α : ℝ) * den)
  let α0_real : ℝ := (α0_num : ℝ) / den
  have hα_le_α0 : (α : ℝ) ≤ α0_real := by
    have h1 : (α : ℝ) * den ≤ (α0_num : ℝ) := by
      simpa [α0_num] using (Int.le_ceil ((α : ℝ) * den))
    have hdiv := div_le_div_of_nonneg_right h1 (le_of_lt hden_pos)
    simpa [α0_real, den, hden_ne, mul_assoc] using hdiv
  have hα0_nonneg : 0 ≤ α0_real := by
    have hα_nonneg : (0 : ℝ) ≤ (α : ℝ) := by
      exact_mod_cast (show (0 : ℝ≥0) ≤ α from bot_le)
    exact le_trans hα_nonneg hα_le_α0
  let α0 : ℝ≥0 := ⟨α0_real, hα0_nonneg⟩

  have hS'_agree0 : ∀ z ∈ S', agree μ (w · z) (wtilde · z) ≥ α0 := by
    intro z hz
    have hagree_eq := agree_eq_int_div (a := (w · z)) (b := (wtilde · z))
    let numZ : ℤ := ∑ i ∈ {i | (w · z) i = (wtilde · z) i}, nfun i
    have hagree_eq' : agree μ (w · z) (wtilde · z) = (numZ : ℝ) / den := by
      simpa [numZ] using hagree_eq
    have hα_le_agree : (α : ℝ) ≤ agree μ (w · z) (wtilde · z) := by
      simpa using hS'_agree' z hz
    have hαden_le : (α : ℝ) * den ≤ (numZ : ℝ) := by
      have hmul := mul_le_mul_of_nonneg_right hα_le_agree (le_of_lt hden_pos)
      simpa [hagree_eq', div_eq_mul_inv, hden_ne, mul_assoc] using hmul
    have hceil_le : α0_num ≤ numZ := by
      have : Int.ceil ((α : ℝ) * den) ≤ numZ := (Int.ceil_le).2 hαden_le
      simpa [α0_num] using this
    have hceil_le_real : (α0_num : ℝ) ≤ (numZ : ℝ) := by exact_mod_cast hceil_le
    have hdiv := div_le_div_of_nonneg_right hceil_le_real (le_of_lt hden_pos)
    have : (α0_real : ℝ) ≤ agree μ (w · z) (wtilde · z) := by
      simpa [α0_real, hagree_eq', hden_ne] using hdiv
    simpa [α0, α0_real] using this

  have hBound :=
    list_agreement_on_curve_implies_correlated_agreement_bound (k := k) (u := u) (v := v)
      (μ := μ) (α := α0) (deg := deg) (domain := domain) hv hS'_card
      (by simpa [w, wtilde] using hS'_agree0)

  have herr : (l + 1 : ℝ) / (S'.card - (l + 1)) ≤ (1 : ℝ) / den := by
    have hMn_pos : (0 : ℝ) < (M * Fintype.card ι : ℝ) := by
      exact_mod_cast (Nat.pos_of_ne_zero hMn)
    have hs_ge : l + 1 ≤ S'.card := le_of_lt hS'_card
    have hcast_sub : ((S'.card - (l + 1) : ℕ) : ℝ) = (S'.card : ℝ) - (l + 1 : ℝ) := by
      simpa using (Nat.cast_sub hs_ge)

    have hD_lower : (M * Fintype.card ι : ℝ) * (l + 1 : ℝ) ≤ (S'.card : ℝ) - (l + 1 : ℝ) := by
      have h1 : (S'.card : ℝ) ≥ ((M * Fintype.card ι + 1) * (l + 1) : ℝ) := by
        exact_mod_cast hS'_card₁
      calc
        (S'.card : ℝ) - (l + 1 : ℝ)
            ≥ ((M * Fintype.card ι + 1) * (l + 1) : ℝ) - (l + 1 : ℝ) := by linarith
        _ = (M * Fintype.card ι : ℝ) * (l + 1 : ℝ) := by ring

    have hl_pos : (0 : ℝ) < (l + 1 : ℝ) := by exact_mod_cast Nat.succ_pos l
    have hdenom_pos : (0 : ℝ) < (M * Fintype.card ι : ℝ) * (l + 1 : ℝ) := mul_pos hMn_pos hl_pos

    have : (l + 1 : ℝ) / ((S'.card : ℝ) - (l + 1 : ℝ)) ≤ (1 : ℝ) / (M * Fintype.card ι : ℝ) := by
      calc
        (l + 1 : ℝ) / ((S'.card : ℝ) - (l + 1 : ℝ))
            ≤ (l + 1 : ℝ) / ((M * Fintype.card ι : ℝ) * (l + 1 : ℝ)) := by
                  exact div_le_div_of_nonneg_left (le_of_lt hl_pos) hdenom_pos hD_lower
        _ = (1 : ℝ) / (M * Fintype.card ι : ℝ) := by
              field_simp [hMn]
              ring

    have : (l + 1 : ℝ) / (S'.card - (l + 1)) ≤ (1 : ℝ) / (M * Fintype.card ι : ℝ) := by
      simpa [hcast_sub] using this
    simpa [den, Nat.cast_mul] using this

  have hBound' : mu_set μ {x : ι | ∀ i, u i x = v i x} > (α0 : ℝ) - (1 : ℝ) / den := by
    have hsub :
        (α0 : ℝ) - (1 : ℝ) / den ≤ (α0 : ℝ) - (l + 1 : ℝ) / (S'.card - (l + 1)) := by
      have hneg : -((1 : ℝ) / den) ≤ -((l + 1 : ℝ) / (S'.card - (l + 1))) := by
        exact neg_le_neg herr
      have := add_le_add_left hneg (α0 : ℝ)
      simpa [sub_eq_add_neg] using this
    have hBound0 :
        (α0 : ℝ) - (l + 1 : ℝ) / (S'.card - (l + 1))
          < mu_set μ {x : ι | ∀ i, u i x = v i x} := hBound
    exact lt_of_le_of_lt hsub hBound0

  let B : Finset ι := {x : ι | ∀ i, u i x = v i x}
  have hmuB_eq : mu_set μ B = ((∑ i ∈ B, nfun i) : ℝ) / den := mu_set_eq_int_div (T := B)
  let numB : ℤ := ∑ i ∈ B, nfun i
  have hmuB_eq' : mu_set μ B = (numB : ℝ) / den := by
    simpa [B, numB] using hmuB_eq

  have hBound'' : (numB : ℝ) / den > (α0_num : ℝ) / den - (1 : ℝ) / den := by
    have : mu_set μ B > (α0 : ℝ) - (1 : ℝ) / den := by
      simpa [B] using hBound'
    simpa [α0, α0_real, hmuB_eq'] using this

  have hrhs : (α0_num : ℝ) / den - den⁻¹ = ((α0_num - 1 : ℤ) : ℝ) / den := by
    have : (α0_num : ℝ) / den - (1 : ℝ) / den = ((α0_num - 1 : ℤ) : ℝ) / den := by
      field_simp [hden_ne]
    simpa [one_div] using this

  have hBound''' : ((α0_num - 1 : ℤ) : ℝ) / den < (numB : ℝ) / den := by
    have : (α0_num : ℝ) / den - den⁻¹ < (numB : ℝ) / den := by
      simpa [one_div] using hBound''
    simpa [hrhs] using this

  have hmul : ((α0_num - 1 : ℤ) : ℝ) < (numB : ℝ) := by
    have := mul_lt_mul_of_pos_right hBound''' hden_pos
    simpa [div_eq_mul_inv, hden_ne, mul_assoc] using this

  have hmul_int : α0_num - 1 < numB := by
    exact_mod_cast hmul

  have hα0_num_le : α0_num ≤ numB := by
    have h' : α0_num < numB + 1 := by
      have := add_lt_add_right hmul_int 1
      simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using this
    exact (Int.lt_add_one_iff).1 h'

  have hα0_le_muB : (α0_real : ℝ) ≤ mu_set μ B := by
    have hcast : (α0_num : ℝ) ≤ (numB : ℝ) := by exact_mod_cast hα0_num_le
    have hdiv := div_le_div_of_nonneg_right hcast (le_of_lt hden_pos)
    simpa [hmuB_eq', α0_real, hden_ne] using hdiv

  have : (α : ℝ) ≤ mu_set μ B := le_trans hα_le_α0 hα0_le_muB
  simpa [B] using this
end

end WeightedAgreement

end BCIKS20ProximityGapSection7

section CoreResults
variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
         {F : Type} [Field F] [Fintype F] [DecidableEq F]

open WeightedAgreement

noncomputable instance {domain : ι ↪ F} {deg : ℕ} : Fintype (ReedSolomon.code domain deg) :=
  Fintype.ofFinite _

omit [Field F] [DecidableEq F] in
lemma card_filter_gt_floor_of_prob_gt {P : F → Prop} [DecidablePred P] [Nonempty F] {ε : ℝ≥0} :
    Pr_{let z ← $ᵖ F}[P z] > ε →
    (Finset.filter P Finset.univ).card >
      Nat.floor ((ε : ℝ) * (Fintype.card F : ℝ)) := by
  classical
  intro hprob
  have hprob_eq :
      ((P <$> $ᵖ F) True : ENNReal) =
        ((Finset.filter P Finset.univ).card : ENNReal) / (Fintype.card F : ENNReal) := by
    exact (prob_uniform_eq_card_filter_div_card (F := F) (P := P))
  have hprob' :
      ((Finset.filter P Finset.univ).card : ENNReal) / (Fintype.card F : ENNReal) >
        (ε : ENNReal) := by
    simpa [hprob_eq] using hprob
  have hprobR :
      ((Finset.filter P Finset.univ).card : ℝ) / (Fintype.card F : ℝ) >
        (ε : ℝ) := by
    have hne_top :
        ((Finset.filter P Finset.univ).card : ENNReal) / (Fintype.card F : ENNReal) ≠ ⊤ := by
      have hb : (Fintype.card F : ENNReal) ≠ 0 := by
        exact_mod_cast (ne_of_gt (Fintype.card_pos : 0 < Fintype.card F))
      simp [ENNReal.div_eq_top, hb]
    have hε_ne_top : (ε : ENNReal) ≠ ⊤ := by
      exact (ENNReal.coe_ne_top (r := ε))
    have hprob_lt : (ε : ENNReal) <
        ((Finset.filter P Finset.univ).card : ENNReal) / (Fintype.card F : ENNReal) := by
      simpa [gt_iff_lt] using hprob'
    have hprob_toReal :
        (ε : ENNReal).toReal <
          (((Finset.filter P Finset.univ).card : ENNReal) / (Fintype.card F : ENNReal)).toReal := by
      exact (ENNReal.toReal_lt_toReal hε_ne_top hne_top).2 hprob_lt
    have hprob_toReal' :
        (((Finset.filter P Finset.univ).card : ENNReal) / (Fintype.card F : ENNReal)).toReal >
          (ε : ENNReal).toReal := by
      simpa [gt_iff_lt] using hprob_toReal
    simpa using hprob_toReal'
  have hpos : (0 : ℝ) < (Fintype.card F : ℝ) := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card F)
  have hmul := (mul_lt_mul_of_pos_right hprobR hpos)
  have hcardR :
      (ε : ℝ) * (Fintype.card F : ℝ) < (Finset.filter P Finset.univ).card := by
    have hne : (Fintype.card F : ℝ) ≠ 0 := ne_of_gt hpos
    simpa [div_eq_mul_inv, hne, mul_comm, mul_left_comm, mul_assoc] using hmul
  have hfloor_le :
      (Nat.floor ((ε : ℝ) * (Fintype.card F : ℝ)) : ℝ) ≤
        (ε : ℝ) * (Fintype.card F : ℝ) := by
    exact Nat.floor_le (by positivity)
  have hfloor_lt :
      (Nat.floor ((ε : ℝ) * (Fintype.card F : ℝ)) : ℝ) <
        (Finset.filter P Finset.univ).card := by
    exact lt_of_le_of_lt hfloor_le hcardR
  exact (Nat.cast_lt).1 hfloor_lt

omit [Fintype ι] [Nonempty ι] [DecidableEq ι] [Field F] [DecidableEq F] in
lemma exists_finset_of_prob_gt {P : F → Prop} [DecidablePred P] [Nonempty F] {ε : ℝ≥0} :
    Pr_{let z ← $ᵖ F}[P z] > ε →
    ∃ S : Finset F,
      S.card > Nat.floor ((ε : ℝ) * (Fintype.card F : ℝ)) ∧
      ∀ z ∈ S, P z := by
  classical
  intro hprob
  refine ⟨Finset.filter P Finset.univ, ?_, ?_⟩
  · exact card_filter_gt_floor_of_prob_gt (P := P) hprob
  · intro z hz
    have hz' : z ∈ Finset.filter P Finset.univ := hz
    exact (Finset.mem_filter.1 hz').2

lemma card_filter_gt_floor_of_prob_gt' {α : Type} [Fintype α] [DecidableEq α] [Nonempty α]
    {P : α → Prop} [DecidablePred P] {ε : ℝ≥0} :
    Pr_{let x ← $ᵖ α}[P x] > ε →
    (Finset.filter P Finset.univ).card >
      Nat.floor ((ε : ℝ) * (Fintype.card α : ℝ)) := by
  classical
  intro hprob
  have hprob_eq :
      ((P <$> $ᵖ α) True : ENNReal) =
        ((Finset.filter P Finset.univ).card : ENNReal) / (Fintype.card α : ENNReal) := by
    exact (prob_uniform_eq_card_filter_div_card (F := α) (P := P))
  have hprob' :
      ((Finset.filter P Finset.univ).card : ENNReal) / (Fintype.card α : ENNReal) >
        (ε : ENNReal) := by
    simpa [hprob_eq] using hprob
  have hprobR :
      ((Finset.filter P Finset.univ).card : ℝ) / (Fintype.card α : ℝ) >
        (ε : ℝ) := by
    have hne_top :
        ((Finset.filter P Finset.univ).card : ENNReal) / (Fintype.card α : ENNReal) ≠ ⊤ := by
      have hb : (Fintype.card α : ENNReal) ≠ 0 := by
        exact_mod_cast (ne_of_gt (Fintype.card_pos : 0 < Fintype.card α))
      simp [ENNReal.div_eq_top, hb]
    have hε_ne_top : (ε : ENNReal) ≠ ⊤ := by
      exact (ENNReal.coe_ne_top (r := ε))
    have hprob_lt : (ε : ENNReal) <
        ((Finset.filter P Finset.univ).card : ENNReal) / (Fintype.card α : ENNReal) := by
      simpa [gt_iff_lt] using hprob'
    have hprob_toReal :
        (ε : ENNReal).toReal <
          (((Finset.filter P Finset.univ).card : ENNReal) / (Fintype.card α : ENNReal)).toReal := by
      exact (ENNReal.toReal_lt_toReal hε_ne_top hne_top).2 hprob_lt
    have hprob_toReal' :
        (((Finset.filter P Finset.univ).card : ENNReal) / (Fintype.card α : ENNReal)).toReal >
          (ε : ENNReal).toReal := by
      simpa [gt_iff_lt] using hprob_toReal
    simpa using hprob_toReal'
  have hpos : (0 : ℝ) < (Fintype.card α : ℝ) := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card α)
  have hmul := (mul_lt_mul_of_pos_right hprobR hpos)
  have hcardR :
      (ε : ℝ) * (Fintype.card α : ℝ) < (Finset.filter P Finset.univ).card := by
    have hne : (Fintype.card α : ℝ) ≠ 0 := ne_of_gt hpos
    simpa [div_eq_mul_inv, hne, mul_comm, mul_left_comm, mul_assoc] using hmul
  have hfloor_le :
      (Nat.floor ((ε : ℝ) * (Fintype.card α : ℝ)) : ℝ) ≤
        (ε : ℝ) * (Fintype.card α : ℝ) := by
    exact Nat.floor_le (by positivity)
  have hfloor_lt :
      (Nat.floor ((ε : ℝ) * (Fintype.card α : ℝ)) : ℝ) <
        (Finset.filter P Finset.univ).card := by
    exact lt_of_le_of_lt hfloor_le hcardR
  exact (Nat.cast_lt).1 hfloor_lt

lemma exists_finset_of_prob_gt' {α : Type} [Fintype α] [DecidableEq α] [Nonempty α]
    {P : α → Prop} [DecidablePred P] {ε : ℝ≥0} :
    Pr_{let x ← $ᵖ α}[P x] > ε →
    ∃ S : Finset α,
      S.card > Nat.floor ((ε : ℝ) * (Fintype.card α : ℝ)) ∧
      ∀ x ∈ S, P x := by
  classical
  intro hprob
  refine ⟨Finset.filter P Finset.univ, ?_, ?_⟩
  · exact card_filter_gt_floor_of_prob_gt' (P := P) hprob
  · intro x hx
    have hx' : x ∈ Finset.filter P Finset.univ := hx
    exact (Finset.mem_filter.1 hx').2

lemma exists_fiber_card_gt_of_card_gt_mul {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (f : α → β) (m : ℕ) (h : Fintype.card α > m * Fintype.card β) :
    ∃ b : β, Fintype.card {a : α // f a = b} > m := by
  classical
  by_contra hcontra
  have hle : ∀ b : β, Fintype.card {a : α // f a = b} ≤ m := by
    intro b
    by_contra hb
    exact hcontra ⟨b, lt_of_not_ge hb⟩
  have hsum :
      Fintype.card α = ∑ b : β, Fintype.card {a : α // f a = b} := by
    classical
    let e : α ≃ Σ b : β, {a : α // f a = b} :=
      { toFun := fun a => ⟨f a, ⟨a, rfl⟩⟩
        invFun := fun s => s.2.1
        left_inv := by intro a; rfl
        right_inv := by
          rintro ⟨b, ⟨a, ha⟩⟩
          cases ha
          rfl }
    calc
      Fintype.card α = Fintype.card (Σ b : β, {a : α // f a = b}) := by
        exact (Fintype.card_congr e)
      _ = ∑ b : β, Fintype.card {a : α // f a = b} := by
        simp [Fintype.card_sigma]
  have hsum_le : ∑ b : β, Fintype.card {a : α // f a = b} ≤ ∑ _b : β, m := by
    refine Finset.sum_le_sum ?_
    intro b hb
    exact hle b
  have hbound :
      Fintype.card α ≤ m * Fintype.card β := by
    calc
      Fintype.card α
          = ∑ b : β, Fintype.card {a : α // f a = b} := hsum
      _ ≤ ∑ _b : β, m := hsum_le
      _ = m * Fintype.card β := by simp [mul_comm]
  exact (not_lt_of_ge hbound) h

omit [Nonempty ι] [DecidableEq ι] in
lemma exists_pair_with_large_fiber_of_exists_close
    {S : Finset F} {deg : ℕ} {domain : ι ↪ F} {u₀ u₁ : ι → F} {e m : ℕ}
    (hS : S.card > m * (Fintype.card (ReedSolomon.code domain deg)) ^ 2)
    (hclose :
      ∀ z ∈ S, ∃ v₀ ∈ ReedSolomon.code domain deg, ∃ v₁ ∈ ReedSolomon.code domain deg,
        Δ₀(fun i => u₀ i + z * u₁ i, fun i => v₀ i + z * v₁ i) ≤ e) :
    ∃ v₀ ∈ ReedSolomon.code domain deg, ∃ v₁ ∈ ReedSolomon.code domain deg,
      ∃ S' ⊆ S, S'.card > m ∧
        ∀ z ∈ S',
          Δ₀(fun i => u₀ i + z * u₁ i, fun i => v₀ i + z * v₁ i) ≤ e := by
  classical
  let α := {z : F // z ∈ S}
  let β := ReedSolomon.code domain deg
  letI : Fintype α := Fintype.ofFinite α
  letI : Fintype β := Fintype.ofFinite β
  have hclose' :
      ∀ z : α,
        ∃ p : β × β,
          Δ₀(fun i => u₀ i + z.1 * u₁ i, fun i => p.1.1 i + z.1 * p.2.1 i) ≤ e := by
    intro z
    rcases hclose z.1 z.2 with ⟨v₀, hv₀, v₁, hv₁, hdist⟩
    refine ⟨⟨⟨v₀, hv₀⟩, ⟨v₁, hv₁⟩⟩, ?_⟩
    simpa using hdist
  let f : α → β × β := fun z => Classical.choose (hclose' z)
  have hf_spec :
      ∀ z : α,
        Δ₀(fun i => u₀ i + z.1 * u₁ i, fun i => (f z).1.1 i + z.1 * (f z).2.1 i) ≤ e := by
    intro z
    simpa [f] using (Classical.choose_spec (hclose' z))
  have hcard_alpha : Fintype.card α = S.card := by
    classical
    have h :
        Fintype.card α = #{z | z ∈ S} := by
      simp [α]
    simpa [Finset.filter_univ_mem] using h
  have hS' :
      Fintype.card α > m * Fintype.card (β × β) := by
    have hS'' : S.card > m * (Fintype.card β) ^ 2 := hS
    simpa [hcard_alpha, Fintype.card_prod, pow_two, mul_comm, mul_left_comm, mul_assoc] using hS''
  rcases exists_fiber_card_gt_of_card_gt_mul (f := f) (m := m) hS' with ⟨p, hp⟩
  let T : Finset α := Finset.univ.filter (fun z => f z = p)
  have hT_card : T.card > m := by
    have hcard_T :
        Fintype.card {z : α // f z = p} = T.card := by
      classical
      simpa using
        (Fintype.card_subtype (α := α) (p := fun z => f z = p))
    simpa [hcard_T] using hp
  let S' : Finset F := T.image (fun z => z.1)
  have hS'_card : S'.card > m := by
    have h_inj : Function.Injective (fun z : α => z.1) := by
      intro x y hxy
      exact Subtype.ext (by simpa using hxy)
    have hcard : S'.card = T.card := by
      simpa [S'] using (Finset.card_image_of_injective (s := T) (f := fun z : α => z.1) h_inj)
    simpa [hcard] using hT_card
  have hS'_subset : S' ⊆ S := by
    intro z hz
    rcases Finset.mem_image.mp hz with ⟨z', hz', rfl⟩
    exact z'.2
  refine ⟨p.1.1, p.1.2, p.2.1, p.2.2, S', hS'_subset, hS'_card, ?_⟩
  intro z hz
  rcases Finset.mem_image.mp hz with ⟨z', hz', rfl⟩
  have hz' : f z' = p := by
    have hz'' : z' ∈ T := hz'
    simpa [T] using (Finset.mem_filter.mp hz'').2
  have hdist := hf_spec z'
  simpa [hz'] using hdist

/-- The error bound `ε` in the pair of proximity and error parameters `(δ,ε)` for Reed-Solomon codes
  defined up to the Johnson bound. More precisely, let `ρ` be the rate of the Reed-Solomon code.
  Then for `δ ∈ (0, 1 - √ρ)`, we define the relevant error parameter `ε` for the unique decoding
  bound, i.e. `δ ∈ (0, (1-ρ)/2]` and Johnson bound, i.e. `δ ∈ ((1-ρ)/2 , 1 - √ρ)`. Otherwise,
  we set `ε = 0`.
-/
noncomputable def errorBound (δ : ℝ≥0) (deg : ℕ) (domain : ι ↪ F) : ℝ≥0 :=
  letI ρ : ℝ≥0 := ρ (ReedSolomon.code domain deg)
  if δ ∈ Set.Icc 0 ((1 - ρ)/2)
  then Fintype.card ι / Fintype.card F
  else if δ ∈ Set.Ioo ((1 - ρ)/2) (1 - ρ.sqrt)
       then letI m := min (1 - ρ.sqrt - δ) (ρ.sqrt / 20)
            ⟨(deg ^ 2 : ℝ≥0) / ((2 * m) ^ 7 * (Fintype.card F : ℝ)), by positivity⟩
       else 0


omit [Nonempty ι] in
/-- Theorem 1.2 (Proximity Gaps for Reed-Solomon codes) in [BCIKS20].

Let `C` be a collection of affine spaces. Then `C` displays a `(δ, ε)`-proximity gap with respect to
a Reed-Solomon code, where `(δ,ε)` are the proximity and error parameters defined up to the
Johnson bound. -/
theorem proximity_gap_RSCodes_split {k t : ℕ} [NeZero k] [NeZero t] {deg : ℕ} {domain : ι ↪ F}
    (C : Fin t → (Fin k → (ι → F))) {δ : ℝ≥0}
    (hδ : δ ≤ 1 - (ReedSolomonCode.sqrtRate deg domain)) :
    ∀ i : Fin t,
      (∀ coeffs : Fin k → F, ∃ v ∈ ReedSolomon.code domain deg,
        Δ₀(∑ j, coeffs j • C i j, v) ≤ Nat.floor (δ * Fintype.card ι))
      ∨
      (∃ coeffs : Fin k → F, ∀ v ∈ ReedSolomon.code domain deg,
        Δ₀(∑ j, coeffs j • C i j, v) > Nat.floor (δ * Fintype.card ι)) := by
  intro i
  have _ := hδ
  classical
  by_cases hall :
      ∀ coeffs : Fin k → F, ∃ v ∈ ReedSolomon.code domain deg,
        Δ₀(∑ j, coeffs j • C i j, v) ≤ Nat.floor (δ * Fintype.card ι)
  · exact Or.inl hall
  · exact Or.inr (by
      push_neg at hall
      exact hall)

/-
Theorem 4.1. Suppose `δ ≤ (1-ρ) / 2`. Let `u_0, u_1: 𝒟 → 𝔽_q` be functions. Let
`S = {z ∈ 𝔽_q : Δ(u_0 + z u_1, V) ≤ δ}`
and suppose `|S| > n`. Then `S = 𝔽_q`. Furthermore there are `v_0, v_1 ∈ V` such that
for all `z ∈ 𝔽_q`, `Δ(u_0 + z u_1, v_0 + z v_1) ≤ δ`
and in fact `|{x ∈ 𝒟 : (u_0(x), u_1(x)) ≠ (v_0(x), v_1(x))}| ≤ δ|𝒟|.`
-/
omit [Fintype F] in
theorem RS_correlatedAgreement_affineLines_uniqueDecodingRegime
    {deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0} {u₀ u₁ : ι → F}
    (hδ : δ ≤ relativeUniqueDecodingRadius (ι := ι) (F := F) (C := ReedSolomon.code domain deg))
    (hS_large : ∃ S : Finset F, S.card > Fintype.card ι ∧
      ∃ v₀ ∈ ReedSolomon.code domain deg, ∃ v₁ ∈ ReedSolomon.code domain deg,
        ∀ z ∈ S, Δ₀(fun i => u₀ i + z * u₁ i, fun i => v₀ i + z * v₁ i) ≤
          Nat.floor (δ * Fintype.card ι)) :
    ∃ v₀ ∈ ReedSolomon.code domain deg, ∃ v₁ ∈ ReedSolomon.code domain deg,
  ((Finset.filter (fun i => u₀ i = v₀ i ∧ u₁ i = v₁ i) Finset.univ).card : ℝ) ≥
        (1 - δ) * (Fintype.card ι : ℝ) := by
  classical
  have _ := hδ
  rcases hS_large with ⟨S, hS_card, v₀, hv₀, v₁, hv₁, hclose⟩
  refine ⟨v₀, hv₀, v₁, hv₁, ?_⟩
  -- Apply the list-agreement-on-a-curve lemma with uniform weights and `l = 0`.
  let u : Fin 2 → ι → F := fun i => Fin.cases u₀ (fun _ => u₁) i
  let v : Fin 2 → ι → F := fun i => Fin.cases v₀ (fun _ => v₁) i
  have hμ : ∀ i, ∃ n : ℤ, (uniformWeight (ι := ι) i).1 = (n : ℚ) / (1 : ℚ) := by
    intro i
    refine ⟨1, by simp [uniformWeight]⟩
  have hS'_card : S.card > (0 + 1) := by
    have hn_pos : 1 ≤ Fintype.card ι := Nat.succ_le_iff.mpr (Fintype.card_pos)
    exact lt_of_le_of_lt hn_pos hS_card
  have hS'_card₁ : S.card ≥ (1 * Fintype.card ι + 1) * (0 + 1) := by
    have : S.card ≥ Fintype.card ι + 1 := Nat.succ_le_iff.mpr hS_card
    simpa using this
  have hS'_agree :
      ∀ z ∈ S,
        agree (μ := uniformWeight (ι := ι)) (fun i => u₀ i + z * u₁ i)
          (fun i => v₀ i + z * v₁ i) ≥ (1 - δ) := by
    intro z hz
    have hdist := hclose z hz
    exact
      agree_uniform_ge_one_sub_of_hamming_le (u := fun i => u₀ i + z * u₁ i)
        (v := fun i => v₀ i + z * v₁ i) (δ := δ) hdist
  have hagree_nonneg (f g : ι → F) :
      0 ≤ agree (μ := uniformWeight (ι := ι)) f g := by
    classical
    have hEq :
        agree (μ := uniformWeight (ι := ι)) f g =
          ((Finset.filter (fun i => f i = g i) Finset.univ).card : ℝ) /
            (Fintype.card ι : ℝ) := by
      unfold agree uniformWeight
      simp [Finset.sum_const, div_eq_mul_inv, mul_comm]
    have hpos : (0 : ℝ) < (Fintype.card ι : ℝ) := by
      exact_mod_cast (Fintype.card_pos : 0 < Fintype.card ι)
    have hnonneg :
        0 ≤
          ((Finset.filter (fun i => f i = g i) Finset.univ).card : ℝ) /
            (Fintype.card ι : ℝ) := by
      exact div_nonneg (by exact_mod_cast (Nat.zero_le _)) (le_of_lt hpos)
    simpa [hEq] using hnonneg
  let A : Finset ι := {x : ι | ∀ i, u i x = v i x}
  have hmu_set0 : mu_set (μ := uniformWeight (ι := ι)) A ≥ ((1 - δ : ℝ≥0) : ℝ) := by
    have hv' : ∀ i : Fin 2, v i ∈ ReedSolomon.code domain deg := by
      refine Fin.cases ?_ (fun j => ?_)
      · simpa [v] using hv₀
      · refine Fin.cases ?_ (fun j' => (Fin.elim0 j')) j
        · simpa [v] using hv₁
    -- instantiate Lemma 7.6 with `l = 0` and `M = 1`
    dsimp [A]
    refine
      (sufficiently_large_list_agreement_on_curve_implies_correlated_agreement
        (k := 0) (l := 0) (u := u) (v := v) (μ := uniformWeight (ι := ι)) (α := (1 - δ))
        (M := 1) (deg := deg) (domain := domain) hμ
        (hv := hv') (S' := S) hS'_card hS'_card₁ ?_)
    intro z hz
    have hagree := hS'_agree z hz
    by_cases hδ' : δ ≤ 1
    · simp [NNReal.coe_sub hδ', u, v, Fin.sum_univ_two, pow_zero, pow_one] at *; exact hagree
    · have hright : ((1 - δ : ℝ≥0) : ℝ) = 0 := by
        have : (1 : ℝ≥0) ≤ δ := by exact_mod_cast (le_of_not_ge hδ')
        simp [tsub_eq_zero_of_le this]
      have hnonneg :=
        hagree_nonneg (fun i => u₀ i + z * u₁ i) (fun i => v₀ i + z * v₁ i)
      simpa [u, v, Fin.sum_univ_two, pow_zero, pow_one, hright] using hnonneg
  have h_one_sub_le :
      (1 - (δ : ℝ)) ≤ ((1 - δ : ℝ≥0) : ℝ) := by
    by_cases hδ' : δ ≤ 1
    · simp [NNReal.coe_sub hδ']
    · have hδ' : (1 : ℝ) ≤ (δ : ℝ) := by
        exact_mod_cast (le_of_not_ge hδ')
      have hleft : (1 - (δ : ℝ)) ≤ 0 := by linarith
      have hright : ((1 - δ : ℝ≥0) : ℝ) = 0 := by
        have : (1 : ℝ≥0) ≤ δ := by exact_mod_cast hδ'
        simp [tsub_eq_zero_of_le this]
      simpa [hright] using hleft
  have hmu_set : mu_set (μ := uniformWeight (ι := ι)) A ≥ (1 - (δ : ℝ)) := by
    exact le_trans h_one_sub_le hmu_set0
  -- Convert from `mu_set` to a cardinality lower bound.
  have hmu_set' :
      ((A.card : ℝ) / (Fintype.card ι : ℝ)) ≥ (1 - δ) := by
    simpa [A, mu_set_uniform_eq (ι := ι) (ι' := A)] using hmu_set
  have hn_pos : (0 : ℝ) < (Fintype.card ι : ℝ) := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card ι)
  have hmu_set'' : (1 - (δ : ℝ)) ≤ (A.card : ℝ) / (Fintype.card ι : ℝ) := by
    simpa [ge_iff_le] using hmu_set'
  have hcard :
      (1 - (δ : ℝ)) * (Fintype.card ι : ℝ) ≤
        (A.card : ℝ) := by
    have hmul :=
      mul_le_mul_of_nonneg_right hmu_set'' (le_of_lt hn_pos)
    have hn_ne : (Fintype.card ι : ℝ) ≠ 0 := ne_of_gt hn_pos
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc, hn_ne] using hmul
  -- Rewrite the agreement set for `Fin 2`.
  have hset_eq :
      A =
        Finset.filter (fun i => u₀ i = v₀ i ∧ u₁ i = v₁ i) Finset.univ := by
    apply Finset.ext
    intro x
    constructor
    · intro hx
      have hx' : ∀ i, u i x = v i x := by
        simpa [A] using hx
      have hx0 : u₀ x = v₀ x := by
        simpa [u, v] using hx' 0
      have hx1 : u₁ x = v₁ x := by
        simpa [u, v] using hx' 1
      simp [hx0, hx1]
    · intro hx
      have hx' : u₀ x = v₀ x ∧ u₁ x = v₁ x := by
        simpa using hx
      have hforall : ∀ i, u i x = v i x := by
        refine Fin.cases ?_ (fun j => ?_)
        · simpa [u, v] using hx'.1
        · refine Fin.cases ?_ (fun j' => (Fin.elim0 j')) j
          · simpa [u, v] using hx'.2
      simpa [A] using hforall
  simpa [hset_eq] using hcard

theorem RS_correlatedAgreement_affineLines_uniqueDecodingRegime_of_prob
    {deg : ℕ} {domain : ι ↪ F} {δ ε : ℝ≥0} {u₀ u₁ v₀ v₁ : ι → F} [Nonempty F]
    (hδ : δ ≤ relativeUniqueDecodingRadius (ι := ι) (F := F) (C := ReedSolomon.code domain deg))
    (hv₀ : v₀ ∈ ReedSolomon.code domain deg)
    (hv₁ : v₁ ∈ ReedSolomon.code domain deg)
    (hε_large : Nat.floor ((ε : ℝ) * (Fintype.card F : ℝ)) ≥ Fintype.card ι)
    (hprob :
      Pr_{ let z ← $ᵖ F}[Δ₀(fun i => u₀ i + z * u₁ i, fun i => v₀ i + z * v₁ i) ≤
        Nat.floor (δ * Fintype.card ι)] > ε) :
    ∃ v₀ ∈ ReedSolomon.code domain deg, ∃ v₁ ∈ ReedSolomon.code domain deg,
      ((Finset.filter (fun i => u₀ i = v₀ i ∧ u₁ i = v₁ i) Finset.univ).card : ℝ) ≥
        (1 - δ) * (Fintype.card ι : ℝ) := by
  classical
  have hS :=
    exists_finset_of_prob_gt
      (P := fun z =>
        Δ₀(fun i => u₀ i + z * u₁ i, fun i => v₀ i + z * v₁ i) ≤
          Nat.floor (δ * Fintype.card ι)) hprob
  rcases hS with ⟨S, hS_card, hS_prop⟩
  have hS_large : S.card > Fintype.card ι := by
    have hS_floor : S.card > Nat.floor ((ε : ℝ) * (Fintype.card F : ℝ)) := hS_card
    exact lt_of_le_of_lt hε_large hS_floor
  have hS_large' :
      ∃ S : Finset F, S.card > Fintype.card ι ∧
        ∃ v₀ ∈ ReedSolomon.code domain deg, ∃ v₁ ∈ ReedSolomon.code domain deg,
          ∀ z ∈ S,
            Δ₀(fun i => u₀ i + z * u₁ i, fun i => v₀ i + z * v₁ i) ≤
              Nat.floor (δ * Fintype.card ι) := by
    refine ⟨S, hS_large, v₀, hv₀, v₁, hv₁, ?_⟩
    exact hS_prop
  exact
    RS_correlatedAgreement_affineLines_uniqueDecodingRegime
      (deg := deg) (domain := domain) (δ := δ) (u₀ := u₀) (u₁ := u₁) hδ hS_large'

/-- Theorem 1.4 (Main Theorem — Correlated agreement over lines) in [BCIKS20].

Take a Reed-Solomon code of length `ι` and degree `deg`, a proximity-error parameter
pair `(δ, ε)` and two words `u₀` and `u₁`, such that the probability that a random affine
line passing through `u₀` and `u₁` is `δ`-close to Reed-Solomon code is at most `ε`.
Then, the words `u₀` and `u₁` have correlated agreement. -/
theorem RS_correlatedAgreement_affineLines {deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    {u₀ u₁ : ι → F} {ε : ℝ≥0}
    (hδ : δ ≤ 1 - (ReedSolomonCode.sqrtRate deg domain))
    (hε_large :
      Nat.floor ((ε : ℝ) * (Fintype.card F : ℝ)) ≥
        (Fintype.card ι) * (Fintype.card (ReedSolomon.code domain deg)) ^ 2)
    (hprob :
      Pr_{ let z ← $ᵖ F}[∃ v₀ ∈ ReedSolomon.code domain deg, ∃ v₁ ∈ ReedSolomon.code domain deg,
        Δ₀(fun i => u₀ i + z * u₁ i, fun i => v₀ i + z * v₁ i) ≤
        Nat.floor (δ * Fintype.card ι)] > ε) :
    ∃ v₀ ∈ ReedSolomon.code domain deg, ∃ v₁ ∈ ReedSolomon.code domain deg,
      ((Finset.filter (fun i => u₀ i = v₀ i ∧ u₁ i = v₁ i) Finset.univ).card : ℝ) ≥
        (1 - δ) * (Fintype.card ι : ℝ) := by
  classical
  have _ := hδ
  let P : F → Prop := fun z =>
    ∃ v₀ ∈ ReedSolomon.code domain deg, ∃ v₁ ∈ ReedSolomon.code domain deg,
      Δ₀(fun i => u₀ i + z * u₁ i, fun i => v₀ i + z * v₁ i) ≤
        Nat.floor (δ * Fintype.card ι)
  have hS := exists_finset_of_prob_gt (P := P) hprob
  rcases hS with ⟨S, hS_card, hS_prop⟩
  have hS_large :
      S.card > (Fintype.card ι) * (Fintype.card (ReedSolomon.code domain deg)) ^ 2 := by
    have hε_le :
        (Fintype.card ι) * (Fintype.card (ReedSolomon.code domain deg)) ^ 2 ≤
          Nat.floor ((ε : ℝ) * (Fintype.card F : ℝ)) := by
      simpa [ge_iff_le] using hε_large
    have hS_floor :
        Nat.floor ((ε : ℝ) * (Fintype.card F : ℝ)) < S.card := by
      simpa [gt_iff_lt] using hS_card
    exact lt_of_le_of_lt hε_le hS_floor
  rcases
      exists_pair_with_large_fiber_of_exists_close
        (S := S) (deg := deg) (domain := domain) (u₀ := u₀) (u₁ := u₁)
        (e := Nat.floor (δ * Fintype.card ι)) (m := Fintype.card ι)
        hS_large hS_prop
    with ⟨v₀, hv₀, v₁, hv₁, S', hS'_subset, hS'_card, hclose⟩
  have hS_large' : S'.card > Fintype.card ι := hS'_card
  refine ⟨v₀, hv₀, v₁, hv₁, ?_⟩
  -- Reuse the same argument as in the unique-decoding regime:
  -- list agreement ⇒ correlated agreement.
  let u : Fin 2 → ι → F := fun i => Fin.cases u₀ (fun _ => u₁) i
  let v : Fin 2 → ι → F := fun i => Fin.cases v₀ (fun _ => v₁) i
  have hμ : ∀ i, ∃ n : ℤ, (uniformWeight (ι := ι) i).1 = (n : ℚ) / (1 : ℚ) := by
    intro i
    refine ⟨1, by simp [uniformWeight]⟩
  have hS'_card : S'.card > (0 + 1) := by
    have hn_pos : 1 ≤ Fintype.card ι := Nat.succ_le_iff.mpr (Fintype.card_pos)
    exact lt_of_le_of_lt hn_pos hS_large'
  have hS'_card₁ : S'.card ≥ (1 * Fintype.card ι + 1) * (0 + 1) := by
    have : S'.card ≥ Fintype.card ι + 1 := Nat.succ_le_iff.mpr hS_large'
    simpa using this
  have hS'_agree :
      ∀ z ∈ S',
        agree (μ := uniformWeight (ι := ι)) (fun i => u₀ i + z * u₁ i)
          (fun i => v₀ i + z * v₁ i) ≥ (1 - δ) := by
    intro z hz
    have hdist := hclose z hz
    exact
      agree_uniform_ge_one_sub_of_hamming_le (u := fun i => u₀ i + z * u₁ i)
        (v := fun i => v₀ i + z * v₁ i) (δ := δ) hdist
  have hagree_nonneg (f g : ι → F) :
      0 ≤ agree (μ := uniformWeight (ι := ι)) f g := by
    classical
    have hEq :
        agree (μ := uniformWeight (ι := ι)) f g =
          ((Finset.filter (fun i => f i = g i) Finset.univ).card : ℝ) /
            (Fintype.card ι : ℝ) := by
      unfold agree uniformWeight
      simp [Finset.sum_const, div_eq_mul_inv, mul_comm]
    have hpos : (0 : ℝ) < (Fintype.card ι : ℝ) := by
      exact_mod_cast (Fintype.card_pos : 0 < Fintype.card ι)
    have hnonneg :
        0 ≤
          ((Finset.filter (fun i => f i = g i) Finset.univ).card : ℝ) /
            (Fintype.card ι : ℝ) := by
      exact div_nonneg (by exact_mod_cast (Nat.zero_le _)) (le_of_lt hpos)
    simpa [hEq] using hnonneg
  let A : Finset ι := {x : ι | ∀ i, u i x = v i x}
  have hmu_set0 : mu_set (μ := uniformWeight (ι := ι)) A ≥ ((1 - δ : ℝ≥0) : ℝ) := by
    have hv' : ∀ i : Fin 2, v i ∈ ReedSolomon.code domain deg := by
      refine Fin.cases ?_ (fun j => ?_)
      · simpa [v] using hv₀
      · refine Fin.cases ?_ (fun j' => (Fin.elim0 j')) j
        · simpa [v] using hv₁
    dsimp [A]
    refine
      (sufficiently_large_list_agreement_on_curve_implies_correlated_agreement
        (k := 0) (l := 0) (u := u) (v := v) (μ := uniformWeight (ι := ι)) (α := (1 - δ))
        (M := 1) (deg := deg) (domain := domain) hμ
        (hv := hv')
        (S' := S') hS'_card hS'_card₁ ?_)
    intro z hz
    have hagree := hS'_agree z hz
    by_cases hδ' : δ ≤ 1
    · simp [NNReal.coe_sub hδ', u, v, Fin.sum_univ_two, pow_zero, pow_one] at *; exact hagree
    · have hright : ((1 - δ : ℝ≥0) : ℝ) = 0 := by
        have : (1 : ℝ≥0) ≤ δ := by exact_mod_cast (le_of_not_ge hδ')
        simp [tsub_eq_zero_of_le this]
      have hnonneg :=
        hagree_nonneg (fun i => u₀ i + z * u₁ i) (fun i => v₀ i + z * v₁ i)
      simpa [u, v, Fin.sum_univ_two, pow_zero, pow_one, hright] using hnonneg
  have h_one_sub_le :
      (1 - (δ : ℝ)) ≤ ((1 - δ : ℝ≥0) : ℝ) := by
    by_cases hδ' : δ ≤ 1
    · simp [NNReal.coe_sub hδ']
    · have hδ' : (1 : ℝ) ≤ (δ : ℝ) := by
        exact_mod_cast (le_of_not_ge hδ')
      have hleft : (1 - (δ : ℝ)) ≤ 0 := by linarith
      have hright : ((1 - δ : ℝ≥0) : ℝ) = 0 := by
        have : (1 : ℝ≥0) ≤ δ := by exact_mod_cast hδ'
        simp [tsub_eq_zero_of_le this]
      simpa [hright] using hleft
  have hmu_set : mu_set (μ := uniformWeight (ι := ι)) A ≥ (1 - (δ : ℝ)) := by
    exact le_trans h_one_sub_le hmu_set0
  have hmu_set' :
      ((A.card : ℝ) / (Fintype.card ι : ℝ)) ≥ (1 - δ) := by
    simpa [A, mu_set_uniform_eq (ι := ι) (ι' := A)] using hmu_set
  have hn_pos : (0 : ℝ) < (Fintype.card ι : ℝ) := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card ι)
  have hmu_set'' : (1 - (δ : ℝ)) ≤ (A.card : ℝ) / (Fintype.card ι : ℝ) := by
    simpa [ge_iff_le] using hmu_set'
  have hcard :
      (1 - (δ : ℝ)) * (Fintype.card ι : ℝ) ≤
        (A.card : ℝ) := by
    have hmul :=
      mul_le_mul_of_nonneg_right hmu_set'' (le_of_lt hn_pos)
    have hn_ne : (Fintype.card ι : ℝ) ≠ 0 := ne_of_gt hn_pos
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc, hn_ne] using hmul
  have hset_eq :
      A =
        Finset.filter (fun i => u₀ i = v₀ i ∧ u₁ i = v₁ i) Finset.univ := by
    apply Finset.ext
    intro x
    constructor
    · intro hx
      have hx' : ∀ i, u i x = v i x := by
        simpa [A] using hx
      have hx0 : u₀ x = v₀ x := by
        simpa [u, v] using hx' 0
      have hx1 : u₁ x = v₁ x := by
        simpa [u, v] using hx' 1
      simp [hx0, hx1]
    · intro hx
      have hx' : u₀ x = v₀ x ∧ u₁ x = v₁ x := by
        simpa using hx
      have hforall : ∀ i, u i x = v i x := by
        refine Fin.cases ?_ (fun j => ?_)
        · simpa [u, v] using hx'.1
        · refine Fin.cases ?_ (fun j' => (Fin.elim0 j')) j
          · simpa [u, v] using hx'.2
      simpa [A] using hforall
  simpa [hset_eq] using hcard


omit [DecidableEq ι] in
/-- Theorem 1.5 (Correlated agreement for low-degree parameterised curves) in [BCIKS20].

Take a Reed-Solomon code of length `ι` and degree `deg`, a proximity-error parameter
pair `(δ, ε)` and a curve passing through words `u₀, ..., uκ`, such that
the  probability that a random point on the curve is `δ`-close to the Reed-Solomon code
is at most `ε`. Then, the words `u₀, ..., uκ` have correlated agreement. -/
theorem correlatedAgreement_affine_curves [DecidableEq ι] {k : ℕ} {u : Fin k → ι → F}
    {deg : ℕ} {domain : ι ↪ F} {δ ε : ℝ≥0}
    (hδ : δ ≤ 1 - ReedSolomonCode.sqrtRate deg domain)
    (hε_large :
      Nat.floor ((ε : ℝ) * (Fintype.card F : ℝ)) ≥
        ((Fintype.card ι + 1) * (k - 1)) * (Fintype.card (ReedSolomon.code domain deg)) ^ k)
    (hprob :
      Pr_{ let z ← $ᵖ F}[∃ v : Fin k → ι → F,
        (∀ j, v j ∈ ReedSolomon.code domain deg) ∧
        Δ₀(fun i => ∑ j : Fin k, z ^ j.val * u j i,
            fun i => ∑ j : Fin k, z ^ j.val * v j i) ≤ Nat.floor (δ * Fintype.card ι)] > ε) :
    ∃ v : Fin k → ι → F,
  (∀ j, v j ∈ ReedSolomon.code domain deg) ∧
      ((Finset.filter (fun i => ∀ j, u j i = v j i) Finset.univ).card : ℝ) ≥
        (1 - δ) * (Fintype.card ι : ℝ) := by
  classical
  have _ := hδ
  have _ := (inferInstance : DecidableEq ι)
  let P : F → Prop := fun z =>
    ∃ v : Fin k → ι → F,
      (∀ j, v j ∈ ReedSolomon.code domain deg) ∧
      Δ₀(fun i => ∑ j : Fin k, z ^ j.val * u j i,
        fun i => ∑ j : Fin k, z ^ j.val * v j i) ≤ Nat.floor (δ * Fintype.card ι)
  have hS := exists_finset_of_prob_gt (P := P) hprob
  rcases hS with ⟨S, hS_card, hS_prop⟩
  let α := {z : F // z ∈ S}
  let β := (Fin k → ReedSolomon.code domain deg)
  letI : Fintype α := Fintype.ofFinite α
  have hcard_alpha : Fintype.card α = S.card := by
    classical
    have h :
        Fintype.card α = #{z | z ∈ S} := by
      simp [α]
    simpa [Finset.filter_univ_mem] using h
  have hS_large :
      S.card > ((Fintype.card ι + 1) * (k - 1)) * Fintype.card β := by
    have hcard_beta :
        Fintype.card β = (Fintype.card (ReedSolomon.code domain deg)) ^ k := by
      classical
      calc
        Fintype.card β
            = Fintype.card (Fin k → ReedSolomon.code domain deg) := by
                simp [β]
        _ = Fintype.card (ReedSolomon.code domain deg) ^ Fintype.card (Fin k) := by
                exact
                  (Fintype.card_fun (α := Fin k) (β := ReedSolomon.code domain deg))
        _ = (Fintype.card (ReedSolomon.code domain deg)) ^ k := by
                simp
    have hε_le :
        ((Fintype.card ι + 1) * (k - 1)) * Fintype.card β ≤
          Nat.floor ((ε : ℝ) * (Fintype.card F : ℝ)) := by
      simpa [hcard_beta, ge_iff_le] using hε_large
    have hS_floor :
        Nat.floor ((ε : ℝ) * (Fintype.card F : ℝ)) < S.card := by
      simpa [gt_iff_lt] using hS_card
    exact lt_of_le_of_lt hε_le hS_floor
  have hS' :
      Fintype.card α > ((Fintype.card ι + 1) * (k - 1)) * Fintype.card β := by
    simpa [hcard_alpha] using hS_large
  have hclose' : ∀ z : α, ∃ v : β,
      Δ₀(fun i => ∑ j : Fin k, z.1 ^ j.val * u j i,
        fun i => ∑ j : Fin k, z.1 ^ j.val * (v j).1 i) ≤ Nat.floor (δ * Fintype.card ι) := by
    intro z
    rcases hS_prop z.1 z.2 with ⟨v, hv, hdist⟩
    refine ⟨fun j => ⟨v j, hv j⟩, ?_⟩
    simpa using hdist
  let f : α → β := fun z => Classical.choose (hclose' z)
  have hf_spec :
      ∀ z : α,
        Δ₀(fun i => ∑ j : Fin k, z.1 ^ j.val * u j i,
          fun i => ∑ j : Fin k, z.1 ^ j.val * (f z j).1 i) ≤
          Nat.floor (δ * Fintype.card ι) := by
    intro z
    simpa [f] using (Classical.choose_spec (hclose' z))
  rcases exists_fiber_card_gt_of_card_gt_mul (f := f)
      (m := (Fintype.card ι + 1) * (k - 1)) hS' with ⟨v, hv_large⟩
  let T : Finset α := Finset.univ.filter (fun z => f z = v)
  have hT_card : T.card > (Fintype.card ι + 1) * (k - 1) := by
    have hcard_T :
        Fintype.card {z : α // f z = v} = T.card := by
      classical
      simpa using
        (Fintype.card_subtype (α := α) (p := fun z => f z = v))
    simpa [hcard_T] using hv_large
  let S' : Finset F := T.image (fun z => z.1)
  have hS'_card : S'.card > (Fintype.card ι + 1) * (k - 1) := by
    have h_inj : Function.Injective (fun z : α => z.1) := by
      intro x y hxy
      exact Subtype.ext (by simpa using hxy)
    have hcard : S'.card = T.card := by
      simpa [S'] using (Finset.card_image_of_injective (s := T) (f := fun z : α => z.1) h_inj)
    simpa [hcard] using hT_card
  have hclose :
      ∀ z ∈ S',
        Δ₀(fun i => ∑ j : Fin k, z ^ j.val * u j i,
          fun i => ∑ j : Fin k, z ^ j.val * (v j).1 i) ≤
            Nat.floor (δ * Fintype.card ι) := by
    intro z hz
    rcases Finset.mem_image.mp hz with ⟨z', hz', rfl⟩
    have hz' : f z' = v := by
      have hz'' : z' ∈ T := hz'
      simpa [T] using (Finset.mem_filter.mp hz'').2
    have hdist := hf_spec z'
    simpa [hz'] using hdist
  let vfun : Fin k → ι → F := fun j => (v j).1
  have hvfun : ∀ j, vfun j ∈ ReedSolomon.code domain deg := by
    intro j; exact (v j).2
  -- Split on the length of the curve.
  cases k with
  | zero =>
      refine ⟨(fun j => (Fin.elim0 j)), ?_, ?_⟩
      · intro j; exact (Fin.elim0 j)
      · -- The agreement set is all coordinates.
        have hn_pos : (0 : ℝ) ≤ (Fintype.card ι : ℝ) := by exact_mod_cast (Nat.zero_le _)
        have hδ_le : (1 - (δ : ℝ)) ≤ 1 := by
          have hδ_nonneg : (0 : ℝ) ≤ (δ : ℝ) := by exact_mod_cast (show (0 : ℝ≥0) ≤ δ from bot_le)
          linarith
        have hcard_univ :
            ((Finset.univ : Finset ι).card : ℝ) ≥ (1 - δ) * (Fintype.card ι : ℝ) := by
          have hmul := mul_le_mul_of_nonneg_right hδ_le hn_pos
          refine (ge_iff_le).2 ?_
          calc
            (1 - δ) * (Fintype.card ι : ℝ) ≤ (1 : ℝ) * (Fintype.card ι : ℝ) := hmul
            _ = ((Finset.univ : Finset ι).card : ℝ) := by
              simp [Finset.card_univ, one_mul]
        have hfilter_eq :
            Finset.filter (fun i => ∀ j, u j i = vfun j i) Finset.univ = Finset.univ := by
          ext i
          simp
        have hcard :
            ((Finset.filter (fun i => ∀ j, u j i = vfun j i) Finset.univ).card : ℝ) ≥
              (1 - δ) * (Fintype.card ι : ℝ) := by
          rw [hfilter_eq]
          exact hcard_univ
        exact hcard
  | succ k' =>
      cases k' with
      | zero =>
          -- k = 1
          refine ⟨vfun, hvfun, ?_⟩
          have hS_nonempty : S'.Nonempty := by
            have : 0 < S'.card := by simpa using hS'_card
            exact Finset.card_pos.mp this
          rcases hS_nonempty with ⟨z, hz⟩
          have hdist := hclose z hz
          have hagree := agree_uniform_ge_one_sub_of_hamming_le
            (u := fun i => ∑ j : Fin 1, z ^ j.val * u j i)
            (v := fun i => ∑ j : Fin 1, z ^ j.val * vfun j i) (δ := δ) hdist
          -- For `Fin 1`, the sum is just the `0`th term.
          let A : Finset ι := {x : ι | ∀ i, u i x = vfun i x}
          have hagree' :
              agree (μ := uniformWeight (ι := ι)) (fun i => u 0 i) (fun i => vfun 0 i) ≥
                (1 - δ) := by
            simpa [Fin.sum_univ_one, Fin.val_zero, pow_zero, one_mul] using hagree
          have hagree_eq :
              agree (μ := uniformWeight (ι := ι)) (fun i => u 0 i) (fun i => vfun 0 i) =
                (A.card : ℝ) / (Fintype.card ι : ℝ) := by
            classical
            unfold agree uniformWeight
            simp [A, Fin.forall_fin_one, Finset.sum_const, div_eq_mul_inv,
              mul_comm]
          have hmu_set :
              ((A.card : ℝ) / (Fintype.card ι : ℝ)) ≥ (1 - δ) := by
            simpa [hagree_eq] using hagree'
          have hn_pos : (0 : ℝ) < (Fintype.card ι : ℝ) := by
            exact_mod_cast (Fintype.card_pos : 0 < Fintype.card ι)
          have hmu_set'' : (1 - (δ : ℝ)) ≤ (A.card : ℝ) / (Fintype.card ι : ℝ) := by
            simpa [ge_iff_le] using hmu_set
          have hcard :
              (1 - (δ : ℝ)) * (Fintype.card ι : ℝ) ≤
                (A.card : ℝ) := by
            have hmul :=
              mul_le_mul_of_nonneg_right hmu_set'' (le_of_lt hn_pos)
            have hn_ne : (Fintype.card ι : ℝ) ≠ 0 := ne_of_gt hn_pos
            simpa [div_eq_mul_inv, mul_comm, hn_ne] using hmul
          simpa [A, Fin.forall_fin_one] using hcard
      | succ k'' =>
          -- k = k'' + 2
          refine ⟨vfun, hvfun, ?_⟩
          have hμ : ∀ i, ∃ n : ℤ, (uniformWeight (ι := ι) i).1 = (n : ℚ) / (1 : ℚ) := by
            intro i
            refine ⟨1, by simp [uniformWeight]⟩
          have hS'_card' : S'.card > (k'' + 1) := by
            have hk_pos : 0 < k'' + 1 := Nat.succ_pos _
            have hfactor : 1 < Fintype.card ι + 1 := by
              exact (Nat.succ_lt_succ_iff.mpr (Fintype.card_pos : 0 < Fintype.card ι))
            have hmult :
                (k'' + 1) < (Fintype.card ι + 1) * (k'' + 1) := by
              -- `1 < n + 1` and `0 < k'' + 1`
              have hmult' := Nat.mul_lt_mul_of_pos_right hfactor hk_pos
              convert hmult' using 1
              simp [one_mul]
            have hS'_card_big :
                (Fintype.card ι + 1) * (k'' + 1) < S'.card := by
              simpa [gt_iff_lt, Nat.succ_eq_add_one, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
                using hS'_card
            exact lt_trans hmult hS'_card_big
          have hS'_card₁ :
              S'.card ≥ (1 * Fintype.card ι + 1) * (k'' + 1) := by
            have hS'_card_big :
                (Fintype.card ι + 1) * (k'' + 1) < S'.card := by
              simpa [gt_iff_lt, Nat.succ_eq_add_one, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
                using hS'_card
            have hS'_card_big' :
                (1 * Fintype.card ι + 1) * (k'' + 1) < S'.card := by
              simpa using hS'_card_big
            exact Nat.le_of_lt hS'_card_big'
          have hS'_agree :
              ∀ z ∈ S',
                agree (μ := uniformWeight (ι := ι))
                  (fun i => ∑ j : Fin (k'' + 2), z ^ j.val * u j i)
                  (fun i => ∑ j : Fin (k'' + 2), z ^ j.val * vfun j i) ≥ (1 - δ) := by
            intro z hz
            have hdist := hclose z hz
            exact
              agree_uniform_ge_one_sub_of_hamming_le
                (u := fun i => ∑ j : Fin (k'' + 2), z ^ j.val * u j i)
                (v := fun i => ∑ j : Fin (k'' + 2), z ^ j.val * vfun j i)
                (δ := δ) hdist
          let A : Finset ι := {x : ι | ∀ i, u i x = vfun i x}
          have hmu_set0 : mu_set (μ := uniformWeight (ι := ι)) A ≥ ((1 - δ : ℝ≥0) : ℝ) := by
            dsimp [A]
            refine
              (sufficiently_large_list_agreement_on_curve_implies_correlated_agreement
                (k := k'') (l := k'') (u := u) (v := vfun)
                (μ := uniformWeight (ι := ι)) (α := (1 - δ))
                (M := 1) (deg := deg) (domain := domain) hμ hvfun
                (S' := S') hS'_card' hS'_card₁ ?_)
            intro z hz
            have hagree := hS'_agree z hz
            by_cases hδ' : δ ≤ 1
            · simp [NNReal.coe_sub hδ'] at *; exact hagree
            · have hright : ((1 - δ : ℝ≥0) : ℝ) = 0 := by
                have : (1 : ℝ≥0) ≤ δ := by exact_mod_cast (le_of_not_ge hδ')
                simp [tsub_eq_zero_of_le this]
              have hagree_nonneg :
                  0 ≤
                    agree (μ := uniformWeight (ι := ι))
                      (fun i => ∑ j : Fin (k'' + 2), z ^ j.val * u j i)
                      (fun i => ∑ j : Fin (k'' + 2), z ^ j.val * vfun j i) := by
                classical
                -- Convert `agree` to normalized cardinality.
                have hagree_eq :
                    agree (μ := uniformWeight (ι := ι))
                        (fun i => ∑ j : Fin (k'' + 2), z ^ j.val * u j i)
                        (fun i => ∑ j : Fin (k'' + 2), z ^ j.val * vfun j i) =
                      ((Finset.filter
                  (fun i =>
                    (∑ j : Fin (k'' + 2), z ^ j.val * u j i) =
                      ∑ j : Fin (k'' + 2), z ^ j.val * vfun j i)
                  Finset.univ).card : ℝ) / (Fintype.card ι : ℝ) := by
                  unfold agree uniformWeight
                  simp [Finset.sum_const, div_eq_mul_inv, mul_comm]
                have hpos : (0 : ℝ) < (Fintype.card ι : ℝ) := by
                  exact_mod_cast (Fintype.card_pos : 0 < Fintype.card ι)
                have hnonneg :
                    0 ≤
                      ((Finset.filter
                        (fun i =>
                          (∑ j : Fin (k'' + 2), z ^ j.val * u j i) =
                            ∑ j : Fin (k'' + 2), z ^ j.val * vfun j i)
                        Finset.univ).card : ℝ) / (Fintype.card ι : ℝ) := by
                  exact div_nonneg (by exact_mod_cast (Nat.zero_le _)) (le_of_lt hpos)
                simp [hagree_eq] at *
                exact hnonneg
              simpa [hright] using hagree_nonneg
          have h_one_sub_le :
              (1 - (δ : ℝ)) ≤ ((1 - δ : ℝ≥0) : ℝ) := by
            by_cases hδ' : δ ≤ 1
            · simp [NNReal.coe_sub hδ']
            · have hδ' : (1 : ℝ) ≤ (δ : ℝ) := by
                exact_mod_cast (le_of_not_ge hδ')
              have hleft : (1 - (δ : ℝ)) ≤ 0 := by linarith
              have hright : ((1 - δ : ℝ≥0) : ℝ) = 0 := by
                have : (1 : ℝ≥0) ≤ δ := by exact_mod_cast hδ'
                simp [tsub_eq_zero_of_le this]
              simpa [hright] using hleft
          have hmu_set : mu_set (μ := uniformWeight (ι := ι)) A ≥ (1 - (δ : ℝ)) := by
            exact le_trans h_one_sub_le hmu_set0
          have hmu_set' :
              ((A.card : ℝ) / (Fintype.card ι : ℝ)) ≥ (1 - δ) := by
            simpa [A, mu_set_uniform_eq (ι := ι) (ι' := A)] using hmu_set
          have hn_pos : (0 : ℝ) < (Fintype.card ι : ℝ) := by
            exact_mod_cast (Fintype.card_pos : 0 < Fintype.card ι)
          have hmu_set'' : (1 - (δ : ℝ)) ≤ (A.card : ℝ) / (Fintype.card ι : ℝ) := by
            simpa [ge_iff_le] using hmu_set'
          have hcard :
              (1 - (δ : ℝ)) * (Fintype.card ι : ℝ) ≤
                (A.card : ℝ) := by
            have hmul :=
              mul_le_mul_of_nonneg_right hmu_set'' (le_of_lt hn_pos)
            have hn_ne : (Fintype.card ι : ℝ) ≠ 0 := ne_of_gt hn_pos
            simpa [div_eq_mul_inv, mul_comm, hn_ne] using hmul
          simpa [A] using hcard

open Affine in
/-- A point lies in the affine span of `u₀, …, uₖ` iff it lies in the affine subspace
`u₀ + span{uᵢ - u₀}`. -/
lemma mem_affineSpan_range_iff_mem_affineSubspaceAtOrigin
    {k : ℕ} {u : Fin (k + 1) → ι → F} {x : ι → F} :
    x ∈ affineSpan F (Set.range u) ↔
      x ∈ affineSubspaceAtOrigin (F := F) (A := F) (u 0)
        (fun i : Fin k => u (Fin.succ i) - u 0) := by
  classical
  have _ := (inferInstance : Nonempty ι)
  have _ := (inferInstance : DecidableEq ι)
  have _ := (inferInstance : Fintype F)
  constructor
  · intro hx
    rcases
      (eq_affineCombination_of_mem_affineSpan_of_fintype (k := F) (p := u) hx)
      with ⟨w, hw_sum, hw_eq⟩
    have hw_sum' :
        (∑ i ∈ (Finset.univ : Finset (Fin (k + 1))), w i) = (1 : F) := by
      simp [hw_sum]
    have hsum_succ :
        (∑ i, w (Fin.succ i)) = (1 : F) - w 0 := by
      have hsum' : (∑ i, w (Fin.succ i)) + w 0 = (1 : F) := by
        have hsum0 : w 0 + ∑ i, w (Fin.succ i) = (1 : F) := by
          simpa [Fin.sum_univ_succ] using hw_sum
        simpa [add_comm, add_left_comm, add_assoc] using hsum0
      exact eq_sub_of_add_eq hsum'
    have hx' :
        x = u 0 + ∑ i : Fin k, w (Fin.succ i) • (u (Fin.succ i) - u 0) := by
      have hx_lin :
          x = ∑ i, w i • u i := by
        simp [Finset.univ.affineCombination_eq_linear_combination _ _ hw_sum', hw_eq]
      have hx_decomp :
          ∑ i, w i • u i =
            w 0 • u 0 + ∑ i : Fin k, w (Fin.succ i) • u (Fin.succ i) := by
        simp [Fin.sum_univ_succ]
      have hx_aff :
          w 0 • u 0 + ∑ i : Fin k, w (Fin.succ i) • u (Fin.succ i)
            = u 0 + ∑ i : Fin k, w (Fin.succ i) • (u (Fin.succ i) - u 0) := by
        -- Rewrite the RHS using linearity of `•` and the sum.
        have hsum_succ' : (∑ t : Fin k, w (Fin.succ t)) = (1 : F) - w 0 := hsum_succ
        have hsum_sub :
            ∑ i : Fin k, w (Fin.succ i) • (u (Fin.succ i) - u 0)
              = ∑ i : Fin k, w (Fin.succ i) • u (Fin.succ i)
                  - ∑ i : Fin k, w (Fin.succ i) • u 0 := by
          have hsum_sub' :=
            (Finset.sum_sub_distrib (s := (Finset.univ : Finset (Fin k)))
              (f := fun i => w (Fin.succ i) • u (Fin.succ i))
              (g := fun i => w (Fin.succ i) • u 0))
          simp [smul_sub, hsum_sub']
        symm
        calc
              u 0 + ∑ i : Fin k, w (Fin.succ i) • (u (Fin.succ i) - u 0)
                  = u 0 + (∑ i : Fin k, w (Fin.succ i) • u (Fin.succ i))
                    - ∑ i : Fin k, w (Fin.succ i) • u 0 := by
                    rw [hsum_sub]
                    simp [sub_eq_add_neg, add_assoc]
          _ = u 0 + (∑ i : Fin k, w (Fin.succ i) • u (Fin.succ i))
                  - (∑ i : Fin k, w (Fin.succ i)) • u 0 := by
                    simp [Finset.sum_smul]
          _ = u 0 + (∑ i : Fin k, w (Fin.succ i) • u (Fin.succ i))
                  - ((1 - w 0) • u 0) := by
                    simp [hsum_succ']
          _ = w 0 • u 0 + ∑ i : Fin k, w (Fin.succ i) • u (Fin.succ i) := by
                    ext i
                    simp [sub_eq_add_neg]
                    ring
      exact hx_lin.trans (hx_decomp.trans hx_aff)
    -- Conclude membership in the affine subspace.
    have hx_mem :
        x ∈ affineSubspaceAtOrigin (F := F) (A := F) (u 0)
          (fun i : Fin k => u (Fin.succ i) - u 0) := by
      apply (mem_affineSubspaceFrom_iff (origin := u 0)
        (directions := fun i : Fin k => u (Fin.succ i) - u 0) (x := x)).2
      refine ⟨fun i => w (Fin.succ i), ?_⟩
      simp [hx']
    exact hx_mem
  · intro hx
    -- Build affine-combination weights from the direction coefficients.
    rcases
      (mem_affineSubspaceFrom_iff (origin := u 0)
        (directions := fun i : Fin k => u (Fin.succ i) - u 0) (x := x)).1 hx
      with ⟨β, hβ⟩
    let w : Fin (k + 1) → F := fun i =>
      Fin.cases (1 - ∑ j : Fin k, β j) (fun j => β j) i
    have hw_sum : (∑ i, w i) = (1 : F) := by
      simp [w, Fin.sum_univ_succ, add_comm]
    have hx_eq :
        x = ∑ i, w i • u i := by
      -- Expand `x` using `hβ` and rewrite as an affine combination.
      calc
        x = u 0 + ∑ i : Fin k, β i • (u (Fin.succ i) - u 0) := by simpa using hβ
        _ = (1 - ∑ i : Fin k, β i) • u 0 + ∑ i : Fin k, β i • u (Fin.succ i) := by
              ext i
              -- reduce scalar multiplication
              simp [smul_eq_mul]
              have hsum :
                  (∑ x : Fin k, u 0 i * β x) = u 0 i * ∑ x : Fin k, β x := by
                simpa [eq_comm] using
                  (Finset.mul_sum (s := (Finset.univ : Finset (Fin k)))
                    (f := fun x => β x) (a := u 0 i))
              calc
                u 0 i + ∑ x : Fin k, β x * (u x.succ i - u 0 i)
                    = u 0 i + ∑ x : Fin k, (β x * u x.succ i - β x * u 0 i) := by
                      simp [mul_sub]
                _ = u 0 i + (∑ x : Fin k, β x * u x.succ i) - ∑ x : Fin k, u 0 i * β x := by
                      simp [sub_eq_add_neg, Finset.sum_add_distrib,
                        Finset.sum_neg_distrib, add_assoc,
                        mul_comm]
                _ = u 0 i - u 0 i * ∑ x : Fin k, β x + ∑ x : Fin k, β x * u x.succ i := by
                      simp [hsum, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
                _ = (1 - ∑ x : Fin k, β x) * u 0 i + ∑ x : Fin k, β x * u x.succ i := by
                      ring
        _ = ∑ i, w i • u i := by
              simp [w, Fin.sum_univ_succ]
    have hx_mem :
        x ∈ affineSpan F (Set.range u) := by
      have hw_sum' :
          (∑ i ∈ (Finset.univ : Finset (Fin (k + 1))), w i) = (1 : F) := by
        simpa using hw_sum
      have hx_aff :
          (Finset.univ.affineCombination F u w) ∈ affineSpan F (Set.range u) := by
        exact affineCombination_mem_affineSpan (k := F) (s := Finset.univ) hw_sum' u
      simpa [Finset.univ.affineCombination_eq_linear_combination _ _ hw_sum', hx_eq] using hx_aff
    exact hx_mem

/-- Theorem 1.6 (Correlated agreement over affine spaces) in [BCIKS20].

Take a Reed-Solomon code of length `ι` and degree `deg`, a proximity-error parameter
pair `(δ, ε)` and an affine space with origin `u₀` and affine generting set `u₁, ..., uκ`
such that the probability a random point in the affine space is `δ`-close to the Reed-Solomon
code is at most `ε`. Then the words `u₀, ..., uκ` have correlated agreement.

Note that we have `k+2` vectors to form the affine space. This an intricacy needed us to be
able to isolate the affine origin from the affine span and to form a generating set of the
correct size. The reason for taking an extra vector is that after isolating the affine origin,
the affine span is formed as the span of the difference of the rest of the vector set. -/
theorem correlatedAgreement_affine_spaces {k : ℕ} [NeZero k] {u : Fin (k + 1) → ι → F}
    {deg : ℕ} {domain : ι ↪ F} {δ ε : ℝ≥0}
    (hδ : δ ≤ 1 - (ReedSolomonCode.sqrtRate deg domain))
    (hk : k = 1)
    (hε_large :
      Nat.floor ((ε : ℝ) * (Fintype.card F : ℝ)) ≥
        (Fintype.card ι) * (Fintype.card (ReedSolomon.code domain deg)) ^ 2)
    (hprob :
      Pr_{ let z ← $ᵖ F}[∃ v₀ ∈ ReedSolomon.code domain deg, ∃ v₁ ∈ ReedSolomon.code domain deg,
        Δ₀(fun i => u 0 i + z * u 1 i, fun i => v₀ i + z * v₁ i) ≤
        Nat.floor (δ * Fintype.card ι)] > ε) :
    ∃ v : Fin (k + 1) → ι → F,
      (∀ j, v j ∈ ReedSolomon.code domain deg) ∧
      ((Finset.filter (fun i => ∀ j, u j i = v j i) Finset.univ).card : ℝ) ≥
        (1 - δ) * (Fintype.card ι : ℝ) := by
  classical
  -- Reduce to the affine-line case (`k = 1`).
  subst hk
  have hline :=
    RS_correlatedAgreement_affineLines (deg := deg) (domain := domain) (δ := δ)
      (u₀ := u 0) (u₁ := u 1) hδ hε_large hprob
  -- Repackage the witness to match the `k = 1` statement.
  rcases hline with ⟨v₀, hv₀, v₁, hv₁, hcard⟩
  let v' : Fin 2 → ι → F := fun i => Fin.cases v₀ (fun _ => v₁) i
  refine ⟨v', ?_, ?_⟩
  · intro j
    refine Fin.cases ?_ (fun j => ?_) j
    · simpa [v'] using hv₀
    · refine Fin.cases ?_ (fun j' => (Fin.elim0 j')) j
      · simpa [v'] using hv₁
  -- For `Fin 2`, the agreement condition matches `∀ j`.
  simpa [v', Fin.forall_fin_two] using hcard

end CoreResults

section
variable {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

open Affine in
/-- If the generating words have joint agreement with the code, then every point in the
corresponding affine subspace is `δ`-close to the code. -/
lemma all_points_close_of_jointAgreement_affineSubspace
    {k : ℕ} {u : Fin (k + 1) → ι → F} {deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    (hJA :
      jointAgreement (C := ReedSolomon.code domain deg) (δ := δ) (W := u)) :
    ∀ x ∈ affineSubspaceAtOrigin (F := F) (A := F) (u 0)
      (fun i : Fin k => u (Fin.succ i) - u 0),
      δᵣ(x, ReedSolomon.code domain deg) ≤ δ := by
  classical
  have _ := (inferInstance : DecidableEq ι)
  have _ := (inferInstance : Fintype F)
  intro x hx
  -- Extract the agreement set and codewords.
  rcases hJA with ⟨S, hS_card, v, hv⟩
  -- Represent x as an affine combination of the generators.
  rcases
      (mem_affineSubspaceFrom_iff (origin := u 0)
        (directions := fun i : Fin k => u (Fin.succ i) - u 0) (x := x)).1 hx
    with ⟨β, hβ⟩
  -- Build the corresponding affine combination of codewords.
  let w : Fin (k + 1) → F := fun i =>
    Fin.cases (1 - ∑ j : Fin k, β j) (fun j => β j) i
  let v' : ι → F := ∑ j, w j • v j
  have hv'_mem : v' ∈ ReedSolomon.code domain deg := by
    -- Submodule closure under linear combinations.
    have hsum :
        (∑ j, w j • v j) ∈ ReedSolomon.code domain deg := by
      refine (ReedSolomon.code domain deg).sum_mem ?_
      intro j hj
      exact (ReedSolomon.code domain deg).smul_mem (w j) (hv j).1
    simpa [v'] using hsum
  -- Show that x and v' agree on S.
  have hagree : ∀ i, i ∈ S → x i = v' i := by
    intro i hi
    have hSi : ∀ j, u j i = v j i := by
      intro j
      have hsubset := (hv j).2
      have hi' : i ∈ Finset.filter (fun j' => v j j' = u j j') Finset.univ := by
        exact hsubset hi
      have : v j i = u j i := by
        simpa [Finset.mem_filter] using hi'
      simpa using this.symm
    have hx_eq :
        x i = u 0 i + ∑ t : Fin k, β t • (u (Fin.succ t) i - u 0 i) := by
      have hx_eq' := congrArg (fun f => f i) hβ
      simp at hx_eq'
      exact hx_eq'
    have hv_eq :
        v' i = v 0 i + ∑ t : Fin k, β t • (v (Fin.succ t) i - v 0 i) := by
      have hsum :
          (∑ x : Fin k, v 0 i * β x) = v 0 i * ∑ x : Fin k, β x := by
        simpa [eq_comm] using
          (Finset.mul_sum (s := (Finset.univ : Finset (Fin k)))
            (f := fun x => β x) (a := v 0 i))
      calc
        v' i
            = (1 - ∑ t : Fin k, β t) • v 0 i + ∑ t : Fin k, β t • v (Fin.succ t) i := by
                simp [v', w, Fin.sum_univ_succ]
        _ = v 0 i - v 0 i * ∑ t : Fin k, β t + ∑ t : Fin k, β t * v (Fin.succ t) i := by
                simp [smul_eq_mul, sub_eq_add_neg, add_assoc, add_comm]
                ring
        _ = v 0 i + (∑ t : Fin k, β t * v (Fin.succ t) i) - ∑ t : Fin k, v 0 i * β t := by
                simp [hsum, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
        _ = v 0 i + ∑ t : Fin k, β t * (v (Fin.succ t) i - v 0 i) := by
                simp [sub_eq_add_neg, mul_add, mul_neg, Finset.sum_add_distrib,
                  Finset.sum_neg_distrib, add_assoc, mul_comm]
    simp [hx_eq, hv_eq, hSi 0, fun t => hSi (Fin.succ t)]
  -- Convert agreement on S to a distance bound.
  have hS_card_nat :
      (Fintype.card ι) - Nat.floor (δ * Fintype.card ι) ≤ S.card := by
    have hS_card_real :
        (S.card : ℝ) ≥ (1 - (δ : ℝ)) * (Fintype.card ι : ℝ) := by
      by_cases hδ : δ ≤ 1
      · have hS_card' :
            ((S.card : ℝ≥0) : ℝ) ≥ ((1 - δ : ℝ≥0) : ℝ) * (Fintype.card ι : ℝ) := by
          exact_mod_cast hS_card
        simpa [NNReal.coe_sub hδ] using hS_card'
      · have hδ' : (1 - (δ : ℝ)) ≤ 0 := by
          have : (1 : ℝ) ≤ (δ : ℝ) := by exact_mod_cast (le_of_not_ge hδ)
          linarith
        have hnonneg : 0 ≤ (S.card : ℝ) := by exact_mod_cast (Nat.zero_le _)
        have hn : (0 : ℝ) ≤ (Fintype.card ι : ℝ) := by exact_mod_cast (Nat.zero_le _)
        have hneg : (1 - (δ : ℝ)) * (Fintype.card ι : ℝ) ≤ 0 := by nlinarith
        exact le_trans hneg hnonneg
    have hreal :
        ((Fintype.card ι - S.card : ℕ) : ℝ) ≤ (δ : ℝ) * (Fintype.card ι : ℝ) := by
      have hreal' :
          (Fintype.card ι : ℝ) - (S.card : ℝ) ≤ (δ : ℝ) * (Fintype.card ι : ℝ) := by
        nlinarith [hS_card_real]
      have hle : S.card ≤ Fintype.card ι := by
        exact (Finset.card_le_univ (s := S))
      have hcast :
          ((Fintype.card ι - S.card : ℕ) : ℝ) =
            (Fintype.card ι : ℝ) - (S.card : ℝ) := by
        simp [Nat.cast_sub hle]
      simpa [hcast] using hreal'
    have hfloor :
        (Fintype.card ι - S.card) ≤ Nat.floor (δ * Fintype.card ι) := by
      have hreal' : ((Fintype.card ι - S.card : ℕ) : ℝ) ≤ (δ : ℝ) * (Fintype.card ι : ℝ) := hreal
      have hnonneg : (0 : ℝ) ≤ (δ : ℝ) * (Fintype.card ι : ℝ) := by nlinarith
      exact (Nat.le_floor_iff hnonneg).2 hreal'
    have hfloor' : Fintype.card ι ≤ Nat.floor (δ * Fintype.card ι) + S.card :=
      (Nat.sub_le_iff_le_add.mp hfloor)
    exact (Nat.sub_le_iff_le_add.mpr (by simpa [add_comm, add_left_comm, add_assoc] using hfloor'))
  have hrel :
      δᵣ(x, v') ≤ δ := by
    have hS_prop :
        ∀ colIdx : ι,
          (colIdx ∈ S → x colIdx = v' colIdx) ∧ (x colIdx ≠ v' colIdx → colIdx ∉ S) := by
      intro colIdx
      constructor
      · intro hmem
        exact hagree colIdx hmem
      · intro hneq hmem
        exact hneq (hagree colIdx hmem)
    exact (relCloseToWord_iff_exists_agreementCols (u := x) (v := v') (δ := δ)).2
      ⟨S, hS_card_nat, hS_prop⟩
  have hrel' : (δᵣ(x, v') : ENNReal) ≤ (δ : ℝ≥0) := by
    exact_mod_cast hrel
  exact
    (relDistFromCode_le_relDist_to_mem (u := x) (C := ReedSolomon.code domain deg) (v := v')
      hv'_mem).trans hrel'

end

end ProximityGap

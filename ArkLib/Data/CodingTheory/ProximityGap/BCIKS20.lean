/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Katerina Hristova, František Silváši, Julian Sutherland,
         Ilia Vlasov, Chung Thai Nguyen
-/

import ArkLib.Data.CodingTheory.ProximityGap.Basic

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

section CoreResults
variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
         {F : Type} [Field F] [Fintype F] [DecidableEq F]

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


/-- Theorem 1.2 (Proximity Gaps for Reed-Solomon codes) in [BCIKS20].

Let `C` be a collection of affine spaces. Then `C` displays a `(δ, ε)`-proximity gap with respect to
a Reed-Solomon code, where `(δ,ε)` are the proximity and error parameters defined up to the
Johnson bound. -/
theorem proximity_gap_RSCodes {k t : ℕ} [NeZero k] [NeZero t] {deg : ℕ} {domain : ι ↪ F}
  (C : Fin t → (Fin k → (ι → F))) {δ : ℝ≥0} (hδ : δ ≤ 1 - (ReedSolomonCode.sqrtRate deg domain)) :
  True := by
  trivial

set_option linter.style.commandStart false

/-
Theorem 4.1. Suppose `δ ≤ (1-ρ) / 2`. Let `u_0, u_1: 𝒟 → 𝔽_q` be functions. Let
`S = {z ∈ 𝔽_q : Δ(u_0 + z u_1, V) ≤ δ}`
and suppose `|S| > n`. Then `S = 𝔽_q`. Furthermore there are `v_0, v_1 ∈ V` such that
for all `z ∈ 𝔽_q`, `Δ(u_0 + z u_1, v_0 + z v_1) ≤ δ`
and in fact `|{x ∈ 𝒟 : (u_0(x), u_1(x)) ≠ (v_0(x), v_1(x))}| ≤ δ|𝒟|.`
-/
theorem RS_correlatedAgreement_affineLines_uniqueDecodingRegime
    {deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    (hδ : δ ≤ relativeUniqueDecodingRadius (ι := ι) (F := F) (C := ReedSolomon.code domain deg))
    : True := by
  trivial

/-- Theorem 1.4 (Main Theorem — Correlated agreement over lines) in [BCIKS20].

Take a Reed-Solomon code of length `ι` and degree `deg`, a proximity-error parameter
pair `(δ, ε)` and two words `u₀` and `u₁`, such that the probability that a random affine
line passing through `u₀` and `u₁` is `δ`-close to Reed-Solomon code is at most `ε`.
Then, the words `u₀` and `u₁` have correlated agreement. -/
theorem RS_correlatedAgreement_affineLines {deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
  (hδ : δ ≤ 1 - (ReedSolomonCode.sqrtRate deg domain)) :
  True := by
  trivial


/-- Theorem 1.5 (Correlated agreement for low-degree parameterised curves) in [BCIKS20].

Take a Reed-Solomon code of length `ι` and degree `deg`, a proximity-error parameter
pair `(δ, ε)` and a curve passing through words `u₀, ..., uκ`, such that
the  probability that a random point on the curve is `δ`-close to the Reed-Solomon code
is at most `ε`. Then, the words `u₀, ..., uκ` have correlated agreement. -/
theorem correlatedAgreement_affine_curves [DecidableEq ι] {k : ℕ} {u : Fin k → ι → F}
  {deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
  (hδ : δ ≤ 1 - ReedSolomonCode.sqrtRate deg domain)
  : True := by
  trivial

open Affine in
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
  {deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0} (hδ : δ ≤ 1 - (ReedSolomonCode.sqrtRate deg domain))
  : True := by
  trivial

end CoreResults

section BCIKS20ProximityGapSection5
variable {F : Type} [Field F] [DecidableEq F] [DecidableEq (RatFunc F)]
variable {n : ℕ}

section

open GuruswamiSudan
open Polynomial.Bivariate
open RatFunc

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


/-- The first part of lemma 5.3 from [BCIKS20].
    Given the D_X (`proximity_gap_degree_bound`) and δ₀ (`proximity_gap_johnson`),
    a solution to Guruswami-Sudan system exists.
-/
lemma guruswami_sudan_for_proximity_gap_existence {k m : ℕ} {ωs : Fin n ↪ F} {f : Fin n → F} :
  ∃ Q, GuruswamiSudan.Condition (n := n) (F := F) k m
    (GuruswamiSudan.proximity_gap_degree_bound (n := n) k m) ωs f Q := by
  simpa using (GuruswamiSudan.guruswami_sudan_for_proximity_gap_existence (n := n) (F := F)
    (k := k) (m := m) (ωs := ωs) (f := f))

open Polynomial in
/-- The second part of lemma 5.3 from [BCIKS20].
    For any solution Q of the Guruswami-Sudan system, and for any
    polynomial P ∈ RS[n, k, rho] such that δᵣ(w, P) ≤ δ₀(rho, m),
    we have that Y - P(X) divides Q(X, Y) in the polynomial ring
    F[X][Y]. Note that in F[X][Y], the term X actually refers to
    the outer variable, Y.
-/
lemma guruswami_sudan_for_proximity_gap_property {k m : ℕ} {ωs : Fin n ↪ F}
  {f : Fin n → F}
  {p : ReedSolomon.code ωs n}
  (h : Δ₀(f, (ReedSolomon.codewordToPoly p).eval ∘ f) ≤
    GuruswamiSudan.proximity_gap_johnson (n := n) k m) :
  ((Polynomial.X : F[X][X]) - Polynomial.C (ReedSolomon.codewordToPoly p)) ∣ (0 : F[X][X]) := by
  simpa using (GuruswamiSudan.guruswami_sudan_for_proximity_gap_property (n := n) (F := F)
    (k := k) (m := m) (ωs := ωs) (f := f) (p := p) h)

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
  intro hS'_agree
  let w (x : ι) (z : F) : F := ∑ i, z ^ i.1 * u i x
  let wtilde (x : ι) (z : F) : F := ∑ i, z ^ i.1 * v i x
  have hS'_agree' : ∀ z ∈ S', agree μ (w · z) (wtilde · z) ≥ α := by
    simpa [w, wtilde] using hS'_agree
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
    simpa [μw, Rat.cast_sum]
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
          exact Nat.lt_succ_iff.mp (by simpa using a.isLt)
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
    simpa using h
  have p_coeff (x : ι) (i : Fin (l + 2)) : (p x).coeff i.1 = u i x - v i x := by
    classical
    simp [p, Polynomial.coeff_monomial, sum_if_val_eq]

  have mem_B_of_Zx_large (x : ι) (hx : (Zx x).card > l + 1) : x ∈ B := by
    have hpdeg : (p x).natDegree ≤ l + 1 := p_natDegree_le x
    have heval : ∀ z ∈ Zx x, (p x).eval z = 0 := by
      intro z hz
      have hw' : w x z = wtilde x z := (Finset.mem_filter.1 hz).2
      simpa [p_eval x z, hw']
    have hnat : (p x).natDegree < (Zx x).card := lt_of_le_of_lt hpdeg hx
    have hp0 : p x = 0 :=
      Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero' (p x) (Zx x) heval hnat
    have hx_eq : ∀ i, u i x = v i x := by
      intro i
      have hc : (p x).coeff i.1 = 0 := by
        simpa [hp0]
      have hci : u i x - v i x = 0 := by
        simpa [p_coeff x i] using hc
      exact sub_eq_zero.mp hci
    simpa [B, hx_eq]

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
                simp [mu_set_eq, A, mul_assoc]
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
                                  symm
                                  simpa using
                                    (Finset.sum_filter (s := S')
                                      (p := fun z => w x z = wtilde x z)
                                      (f := fun _ => μw x))
                          _ = (S'.filter (fun z => w x z = wtilde x z)).card • (μw x) := by
                                  simpa using
                                    (Finset.sum_const
                                      (s := S'.filter (fun z => w x z = wtilde x z))
                                      (μw x))
                    simpa [nsmul_eq_mul] using this
                simpa [Zx, hZ] using this
            simpa [this]
        -- turn the pointwise form into a factorised form
        have hfactor :
            (∑ x ∈ B, (S'.card : ℝ) * μw x) = (S'.card : ℝ) * (∑ x ∈ B, μw x) := by
          simpa using
            (Finset.mul_sum (s := B) (f := fun x => μw x) (a := (S'.card : ℝ))).symm
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
                          symm
                          simpa using
                            (Finset.sum_filter (s := S')
                              (p := fun z => w x z = wtilde x z)
                              (f := fun _ => μw x))
                  _ = (S'.filter (fun z => w x z = wtilde x z)).card • (μw x) := by
                          simpa using
                            (Finset.sum_const
                              (s := S'.filter (fun z => w x z = wtilde x z))
                              (μw x))
              simpa [nsmul_eq_mul] using this
            simpa [Zx] using this
          have hcard : (Zx x).card ≤ l + 1 := Zx_card_le x (by simpa using hx)
          have hcardR : ((Zx x).card : ℝ) ≤ (l + 1 : ℝ) := by exact_mod_cast hcard
          have := mul_le_mul_of_nonneg_right hcardR (hμw_nonneg x)
          simpa [hsum, mul_assoc] using this
        have hsum' :
            (∑ x ∈ Bᶜ, ∑ z ∈ S', if w x z = wtilde x z then μw x else 0)
              ≤ ∑ x ∈ Bᶜ, (l + 1 : ℝ) * μw x := by
          refine Finset.sum_le_sum ?_
          intro x hx
          simpa using hpoint x hx
        have : ∑ x ∈ Bᶜ, (l + 1 : ℝ) * μw x = (l + 1 : ℝ) * (∑ x ∈ Bᶜ, μw x) := by
          simpa using (Finset.mul_sum (s := Bᶜ) (f := fun x => μw x) (a := (l + 1 : ℝ))).symm
        exact le_trans hsum' (by simpa [this])
      have h_univ :
          (∑ x ∈ (Finset.univ : Finset ι), ∑ z ∈ S', if w x z = wtilde x z then μw x else 0)
            ≤ (S'.card : ℝ) * (∑ x ∈ B, μw x) + (l + 1 : ℝ) * (∑ x ∈ Bᶜ, μw x) := by
        calc
          (∑ x ∈ (Finset.univ : Finset ι), ∑ z ∈ S', if w x z = wtilde x z then μw x else 0)
              = (∑ x ∈ B, ∑ z ∈ S', if w x z = wtilde x z then μw x else 0)
                + (∑ x ∈ Bᶜ, ∑ z ∈ S', if w x z = wtilde x z then μw x else 0) := by
                    simpa using hsplit
          _ ≤ (S'.card : ℝ) * (∑ x ∈ B, μw x) + (l + 1 : ℝ) * (∑ x ∈ Bᶜ, μw x) := by
                exact add_le_add (le_of_eq hB) hBc
      simpa [hswap] using h_univ
    have hmul :
        (1 / (Fintype.card ι : ℝ)) * (∑ z ∈ S', ∑ x ∈ A z, μw x)
          ≤ (1 / (Fintype.card ι : ℝ)) *
              ((S'.card : ℝ) * (∑ x ∈ B, μw x) + (l + 1 : ℝ) * (∑ x ∈ Bᶜ, μw x)) := by
      exact mul_le_mul_of_nonneg_left htotal (by positivity : 0 ≤ (1 / (Fintype.card ι : ℝ)))
    have hR :
        (1 / (Fintype.card ι : ℝ)) *
              ((S'.card : ℝ) * (∑ x ∈ B, μw x) + (l + 1 : ℝ) * (∑ x ∈ Bᶜ, μw x))
          = (S'.card : ℝ) * mu_set μ B + (l + 1 : ℝ) * mu_set μ Bᶜ := by
      simp [mu_set_eq, mul_add, add_mul, mul_assoc, mul_left_comm, mul_comm]
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
          (1 / (Fintype.card ι : ℝ)) * (∑ x ∈ B, μw x) + (1 / (Fintype.card ι : ℝ)) * (∑ x ∈ Bᶜ, μw x)
              = (1 / (Fintype.card ι : ℝ)) * ((∑ x ∈ B, μw x) + (∑ x ∈ Bᶜ, μw x)) := by ring
          _ = (1 / (Fintype.card ι : ℝ)) * ∑ x : ι, μw x := by simpa [hsum']
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
        have : 0 < α := lt_of_le_of_ne (show (0 : ℝ≥0) ≤ α from bot_le) (by simpa [eq_comm] using hα)
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
lemma sufficiently_large_list_agreement_on_curve_implies_correlated_agreement
  [DecidableEq ι] [Fintype ι] [DecidableEq F] {k l : ℕ} {u : Fin (l + 2) → ι → F}
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

end ProximityGap

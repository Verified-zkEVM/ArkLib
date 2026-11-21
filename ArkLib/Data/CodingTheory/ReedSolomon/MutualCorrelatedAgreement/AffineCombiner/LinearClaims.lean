/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Coratger
-/
module

public import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.AffineCombiner.EqualDegree
public import ArkLib.ToMathlib.Finset.AffineZeros

/-!
# Equal-degree combiners with linear claims

A prover claims `⟨coef(F), v⟩ = γ₀` and `⟨coef(G), v⟩ = γ₁` for a public weight vector `v`.
After the challenge `θ`, it sends `c`, meant to be `⟨coef(X(F + θ G)), v⟩`.
The combined claim is `⟨coef(P), v⟩ = γ₁ + α(γ₀ + θ γ₁) + β c`.
Honest claims satisfy it by linearity.

A candidate is exceptional when it satisfies the combined claim but has no good witness pair.
A good pair has correct claims and loses at most `s` agreements.
For one point of loss, the error is at most the affine error plus `2ℓ₀/q`.
Here `ℓ₀ = ⌊n(A - 1 - d)/((A - 1)² - nd)⌋`, `n` is the domain size, and `q` the field size.
The bound assumes `nd < (A - 1)²`.

The equal-degree argument handles all but `ℓ₀` values of `θ`.
Its witness pair lies in the list of pairs of degree below `d` with `A - 1` common agreements.
The Johnson bound limits this list to `ℓ₀` pairs, independently of the challenges.
A pair with a false claim leaves a nonzero affine residual in `(α, β)`.
That residual has at most `q` zeros.
This is the first inequality of (5.5) in Theorem 5.1 of [CWYZ26].
The second inequality is in `Theorem`.
The [paper page](../../../../../../docs/kb/papers/CWYZ26.md) records the correspondence.

The message is a function of `θ`.
Every deterministic prover strategy is such a function; randomized strategies average over them.
The round-saving variant sends `c = c_F + θ c_G` and is one such function.
The paper's list has degrees at most `d`; the count uses only its pairs of degree below `d`.
The combination identity for claims needs no degree bound, so it is stated without one.

The error is a mathematical supremum with classical decidability for polynomial witnesses.
The residual is noncomputable because polynomial multiplication is.
Its counting definition requires no sampler.
The sampling module identifies it with native uniform probabilities.

## Main definitions

* `ReedSolomon.linearClaim`: the claim value `⟨coef(U), v⟩`.
* `ReedSolomon.LinearClaimInstance`: received words, claims, and the prover's message.
* `ReedSolomon.IsLinearClaimExceptional`: an exceptional candidate for three challenges.
* `ReedSolomon.linearClaimMcaError`: the supremum of exceptional-event probabilities.
* `ReedSolomon.HasCorrectLinearClaims`: the three claims of a witness pair hold.
* `ReedSolomon.linearClaimResidual`: the residual of the combined claim for a witness pair.

## Main statements

* `ReedSolomon.linearClaim_add` and `ReedSolomon.linearClaim_C_mul`: the claim is linear.
* `ReedSolomon.linearClaim_add_affineMultiplier_mul`: claims combine by linearity.
* `ReedSolomon.linearClaimMcaError_le_affineMcaError_add`: the reduction with loss `2ℓ₀/q`.
* `ReedSolomon.le_linearClaimMcaError`: one instance bounds the error from below.
* `ReedSolomon.linearClaimMcaError_le_one`: the error is at most one.
* `ReedSolomon.IsLinearClaimExceptional.isEqualDegreeExceptional_or_exists`: the case split.
* `ReedSolomon.card_filter_linearClaimResidual_eq_zero_le`: a false claim's residual zeros.

## References

* [Chiesa, A., Weissenberg, G., Yogev, E., and Zheng, K. Z.,
    *Affine combiners for Reed–Solomon proximity gaps*][CWYZ26]
-/

@[expose] public section

namespace ReedSolomon

open Polynomial Finset

variable {F : Type*} [Field F] [DecidableEq F] {ι : Type*} [Fintype ι]

/-- The claim value `⟨coef(U), v⟩ = ∑_{j ≤ d} [X^j] U · v_j`.

The weight vector `v` has length `d + 1`. -/
def linearClaim {d : ℕ} (v : Fin (d + 1) → F) (U : F[X]) : F :=
  ∑ j : Fin (d + 1), U.coeff j * v j

/-- A linear-claim instance: received words, a weight vector, two claims, and a message.

The weight vector is public.
The prover's message is a function of the first challenge. -/
structure LinearClaimInstance (ι F : Type*) (d : ℕ) where
  /-- The first received word. -/
  f : ι → F
  /-- The second received word. -/
  g : ι → F
  /-- The public weight vector. -/
  v : Fin (d + 1) → F
  /-- The claimed value for the first word. -/
  γ₀ : F
  /-- The claimed value for the second word. -/
  γ₁ : F
  /-- The prover's message after the first challenge. -/
  message : F → F

/-- `P` is exceptional for the linear-claim combiner at `(θ, α, β)` with prover message `c`.

`P` has degree at most `d` and agrees with `g + (α + β x)(f + θ g)` on at least `A` points.
It satisfies the combined claim `⟨coef(P), v⟩ = γ₁ + α(γ₀ + θ γ₁) + β c`.
Consider pairs `F₀, G₀` of degrees below `d` with `P = G₀ + (α + βX)(F₀ + θG₀)`.
Assume `⟨coef(F₀), v⟩ = γ₀`, `⟨coef(G₀), v⟩ = γ₁`, and `⟨coef(X(F₀ + θG₀)), v⟩ = c`.
Every such pair loses more than `s` of these points. -/
def IsLinearClaimExceptional (domain : ι ↪ F) (f g : ι → F) (d A s : ℕ) (v : Fin (d + 1) → F)
    (γ₀ γ₁ c θ α β : F) (P : F[X]) : Prop :=
  P.degree ≤ d ∧
    A ≤ #(polynomialAgreementSet domain (equalDegreeWord domain f g θ α β) P) ∧
    linearClaim v P = γ₁ + α * (γ₀ + θ * γ₁) + β * c ∧
    ∀ F₀ G₀ : F[X], F₀.degree < d → G₀.degree < d →
      P = G₀ + affineMultiplier α β * (F₀ + C θ * G₀) →
      linearClaim v F₀ = γ₀ → linearClaim v G₀ = γ₁ →
      linearClaim v (X * (F₀ + C θ * G₀)) = c →
      s < #{i ∈ polynomialAgreementSet domain (equalDegreeWord domain f g θ α β) P |
        F₀.eval (domain i) ≠ f i ∨ G₀.eval (domain i) ≠ g i}

open Classical in
/-- The supremum over linear-claim instances of an exceptional-event probability.

The event is that some candidate is exceptional for uniform challenges `(θ, α, β)`.
The prover's message is the instance's message at `θ`.
The output degree bound is `d`, and both witness degrees are below `d`.
The agreement threshold is `A`, and the allowed agreement loss is `s`. -/
noncomputable def linearClaimMcaError [Fintype F] (domain : ι ↪ F) (d A s : ℕ) : ENNReal :=
  ⨆ w : LinearClaimInstance ι F d,
    ENNReal.ofReal
      ((#{c : F × F × F | ∃ P, IsLinearClaimExceptional domain w.f w.g d A s w.v w.γ₀ w.γ₁
        (w.message c.1) c.1 c.2.1 c.2.2 P} : ℝ) / (Fintype.card F : ℝ) ^ 3)

open Classical in
/-- One linear-claim instance bounds the error from below. -/
theorem le_linearClaimMcaError [Fintype F] (domain : ι ↪ F) (d A s : ℕ)
    (w : LinearClaimInstance ι F d) :
    ENNReal.ofReal
      ((#{c : F × F × F | ∃ P, IsLinearClaimExceptional domain w.f w.g d A s w.v w.γ₀ w.γ₁
        (w.message c.1) c.1 c.2.1 c.2.2 P} : ℝ) / (Fintype.card F : ℝ) ^ 3) ≤
      linearClaimMcaError domain d A s := by
  unfold linearClaimMcaError
  exact le_iSup_of_le w le_rfl

/-- The linear-claim error is at most one. -/
theorem linearClaimMcaError_le_one [Fintype F] (domain : ι ↪ F) (d A s : ℕ) :
    linearClaimMcaError domain d A s ≤ 1 := by
  classical
  refine iSup_le fun w ↦ ?_
  rw [← ENNReal.ofReal_one]
  apply ENNReal.ofReal_le_ofReal
  rw [div_le_one (by positivity)]
  calc (#{c : F × F × F | ∃ P, IsLinearClaimExceptional domain w.f w.g d A s w.v w.γ₀ w.γ₁
        (w.message c.1) c.1 c.2.1 c.2.2 P} : ℝ)
      ≤ (Finset.univ : Finset (F × F × F)).card := by
        exact_mod_cast Finset.card_filter_le _ _
    _ = (Fintype.card F : ℝ) ^ 3 := by simp [pow_succ, mul_assoc]

omit [DecidableEq F] in
/-- The claim value is additive. -/
@[simp]
theorem linearClaim_add {d : ℕ} (v : Fin (d + 1) → F) (U W : F[X]) :
    linearClaim v (U + W) = linearClaim v U + linearClaim v W := by
  simp [linearClaim, add_mul, Finset.sum_add_distrib]

omit [DecidableEq F] in
/-- The claim value commutes with scalar multiplication. -/
@[simp]
theorem linearClaim_C_mul {d : ℕ} (v : Fin (d + 1) → F) (a : F) (U : F[X]) :
    linearClaim v (C a * U) = a * linearClaim v U := by
  simp [linearClaim, Finset.mul_sum, mul_assoc]

omit [DecidableEq F] in
/-- Claims combine by linearity.

The claim value of `G₀ + (α + βX)(F₀ + θG₀)` is
`⟨coef(G₀), v⟩ + α(⟨coef(F₀), v⟩ + θ⟨coef(G₀), v⟩) + β⟨coef(X(F₀ + θG₀)), v⟩`.
No degree bound is needed, since the claim value is linear in the polynomial. -/
theorem linearClaim_add_affineMultiplier_mul {d : ℕ} (v : Fin (d + 1) → F) (F₀ G₀ : F[X])
    (θ α β : F) :
    linearClaim v (G₀ + affineMultiplier α β * (F₀ + C θ * G₀)) =
      linearClaim v G₀ + α * (linearClaim v F₀ + θ * linearClaim v G₀) +
        β * linearClaim v (X * (F₀ + C θ * G₀)) := by
  have : G₀ + affineMultiplier α β * (F₀ + C θ * G₀) =
      G₀ + C α * (F₀ + C θ * G₀) + C β * (X * (F₀ + C θ * G₀)) := by
    unfold affineMultiplier
    ring
  rw [this]
  simp

/-- The three claims of a witness pair `F₀, G₀` hold for the challenge `θ` and message `c`.

They are `⟨coef(F₀), v⟩ = γ₀`, `⟨coef(G₀), v⟩ = γ₁`, and `⟨coef(X(F₀ + θG₀)), v⟩ = c`. -/
def HasCorrectLinearClaims {d : ℕ} (v : Fin (d + 1) → F) (γ₀ γ₁ c θ : F) (F₀ G₀ : F[X]) : Prop :=
  linearClaim v F₀ = γ₀ ∧ linearClaim v G₀ = γ₁ ∧ linearClaim v (X * (F₀ + C θ * G₀)) = c

/-- The residual `ΔG + α(ΔF + θ ΔG) + β ΔX` of the combined claim for a witness pair.

Here `ΔF = ⟨coef(F₀), v⟩ - γ₀` and `ΔG = ⟨coef(G₀), v⟩ - γ₁`.
The last difference is `ΔX = ⟨coef(X(F₀ + θG₀)), v⟩ - c`. -/
noncomputable def linearClaimResidual {d : ℕ} (v : Fin (d + 1) → F) (γ₀ γ₁ c θ : F) (F₀ G₀ : F[X])
    (α β : F) : F :=
  linearClaim v G₀ - γ₁ + α * (linearClaim v F₀ - γ₀ + θ * (linearClaim v G₀ - γ₁)) +
    β * (linearClaim v (X * (F₀ + C θ * G₀)) - c)

/-- If a claim of the pair `F₀, G₀` is false, few challenges make its residual vanish.

At most `q` pairs `(α, β)` do, where `q` is the field size. -/
theorem card_filter_linearClaimResidual_eq_zero_le [Fintype F] {d : ℕ} (v : Fin (d + 1) → F)
    {γ₀ γ₁ c θ : F} {F₀ G₀ : F[X]} (h : ¬ HasCorrectLinearClaims v γ₀ γ₁ c θ F₀ G₀) :
    #{x : F × F | linearClaimResidual v γ₀ γ₁ c θ F₀ G₀ x.1 x.2 = 0} ≤ Fintype.card F := by
  set a := linearClaim v G₀ - γ₁
  set b := linearClaim v F₀ - γ₀ + θ * (linearClaim v G₀ - γ₁)
  set e := linearClaim v (X * (F₀ + C θ * G₀)) - c
  have hne : a ≠ 0 ∨ b ≠ 0 ∨ e ≠ 0 := by
    by_contra hall
    push Not at hall
    obtain ⟨h₁, h₂, h₃⟩ := hall
    exact h ⟨by linear_combination h₂ - θ * h₁, by linear_combination h₁,
      by linear_combination h₃⟩
  refine le_of_eq_of_le ?_ (Finset.card_filter_add_mul_add_mul_eq_zero_le hne)
  simp only [linearClaimResidual, a, b, e, mul_comm]

/-- A linear-claim exceptional candidate is equal-degree exceptional, or has a bad witness pair.

The pair `F₀, G₀` has degrees below `d` and satisfies `P = G₀ + (α + βX)(F₀ + θG₀)`.
It agrees with `(f, g)` on at least `A - s` common points.
One of its claims is false, and its residual vanishes at `(α, β)`. -/
theorem IsLinearClaimExceptional.isEqualDegreeExceptional_or_exists {domain : ι ↪ F}
    {f g : ι → F} {d A s : ℕ} {v : Fin (d + 1) → F} {γ₀ γ₁ c θ α β : F} {P : F[X]}
    (h : IsLinearClaimExceptional domain f g d A s v γ₀ γ₁ c θ α β P) :
    IsEqualDegreeExceptional domain f g d A s θ α β P ∨
      ∃ F₀ G₀ : F[X], F₀.degree < d ∧ G₀.degree < d ∧
        P = G₀ + affineMultiplier α β * (F₀ + C θ * G₀) ∧
        A - s ≤ #(commonPolynomialAgreementSet domain f g F₀ G₀) ∧
        ¬ HasCorrectLinearClaims v γ₀ γ₁ c θ F₀ G₀ ∧
        linearClaimResidual v γ₀ γ₁ c θ F₀ G₀ α β = 0 := by
  obtain ⟨hP, hA, hclaim, hexc⟩ := h
  by_cases heq : IsEqualDegreeExceptional domain f g d A s θ α β P
  · exact Or.inl heq
  right
  obtain ⟨F₀, G₀, hF, hG, hPeq, hloss⟩ : ∃ F₀ G₀ : F[X], F₀.degree < d ∧ G₀.degree < d ∧
      P = G₀ + affineMultiplier α β * (F₀ + C θ * G₀) ∧
      #{i ∈ polynomialAgreementSet domain (equalDegreeWord domain f g θ α β) P |
        F₀.eval (domain i) ≠ f i ∨ G₀.eval (domain i) ≠ g i} ≤ s := by
    by_contra hno
    push Not at hno
    exact heq ⟨hP, hA, hno⟩
  refine ⟨F₀, G₀, hF, hG, hPeq, ?_, fun ⟨h₁, h₂, h₃⟩ ↦ ?_, ?_⟩
  · classical
    refine (Nat.sub_le_sub_left hloss A).trans ((Nat.sub_le_sub_right hA _).trans
      ((Finset.le_card_sdiff _ _).trans (Finset.card_le_card fun i hi ↦ ?_)))
    obtain ⟨hiP, hiL⟩ := Finset.mem_sdiff.mp hi
    simp only [Finset.mem_filter, hiP, true_and, not_or, not_not] at hiL
    exact (mem_commonPolynomialAgreementSet _ _ _ _ _ _).mpr hiL
  · have := hexc F₀ G₀ hF hG hPeq h₁ h₂ h₃
    omega
  · rw [hPeq, linearClaim_add_affineMultiplier_mul] at hclaim
    unfold linearClaimResidual
    linear_combination hclaim

/-- At loss one, the linear-claim error is at most the affine error plus `2ℓ₀/q`.

Here `n = |ι|` is the domain size, and `q = |F|` is the field size.
The rounded-down Johnson bound is `ℓ₀ = ⌊n(A - 1 - d)/((A - 1)² - nd)⌋`.
Assume `nd < (A - 1)²`. -/
theorem linearClaimMcaError_le_affineMcaError_add [Fintype F] (domain : ι ↪ F) {d A : ℕ}
    (hJ : Fintype.card ι * d < (A - 1) ^ 2) :
    linearClaimMcaError domain d A 1 ≤ affineMcaError domain d A 1 +
      ENNReal.ofReal
        (2 * ((⌊(Fintype.card ι : ℝ) * ((A : ℝ) - 1 - d) /
          (((A : ℝ) - 1) ^ 2 - Fintype.card ι * d)⌋₊ : ℕ) : ℝ) / Fintype.card F) := by
  classical
  refine iSup_le fun w ↦ ?_
  obtain ⟨f, g, v, γ₀, γ₁, msg⟩ := w
  set q : ℝ := (Fintype.card F : ℝ)
  set n : ℕ := Fintype.card ι
  set ℓ₀ := ⌊(n : ℝ) * ((A : ℝ) - 1 - d) / (((A : ℝ) - 1) ^ 2 - n * d)⌋₊
  set E := (affineMcaError domain d A 1).toReal
  have hE : affineMcaError domain d A 1 ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top (affineMcaError_le_one domain d A 1)
  have hq : 0 < q := by positivity
  have hA1 : 1 ≤ A := by
    rcases A with _ | A
    · simp at hJ
    · omega
  -- The integer Johnson count at `L = A - 1` gives the floor `ℓ₀`.
  have hfloor : ∀ k : ℕ, k * ((A - 1) * (A - 1) - n * d) ≤ n * (A - 1 - d) → (k : ℝ) ≤ ℓ₀ :=
    fun k hk ↦ by
      have h := le_floor_johnson_of_mul_le hJ hk
      rw [Nat.cast_sub hA1, Nat.cast_one] at h
      exact Nat.cast_le.mpr h
  -- The list of pairs of degree below `d` with `A - 1` common agreements.
  have hfin : {p : F[X] × F[X] | p.1.degree < d ∧ p.2.degree < d ∧
      A - 1 ≤ #(commonPolynomialAgreementSet domain f g p.1 p.2)}.Finite := by
    have hS : {p : F[X] | p.degree < d}.Finite := by
      have : Finite (degreeLT F d) := Finite.of_equiv _ (degreeLTEquiv F d).toEquiv.symm
      exact (Set.finite_range fun p : degreeLT F d ↦ (p : F[X])).subset
        fun p hp ↦ ⟨⟨p, mem_degreeLT.mpr hp⟩, rfl⟩
    exact (hS.prod hS).subset fun p hp ↦ ⟨hp.1, hp.2.1⟩
  set T := hfin.toFinset
  have hT : (#T : ℝ) ≤ ℓ₀ := by
    refine hfloor _ (card_mul_sq_sub_card_mul_le_of_commonPolynomialAgreementSet domain f g T
      (fun p hp ↦ ?_) (fun p hp ↦ (hfin.mem_toFinset.mp hp).2.2))
    obtain ⟨h₁, h₂, -⟩ := hfin.mem_toFinset.mp hp
    exact ⟨h₁.le, h₂.le⟩
  -- The exceptional triples split into three sets.
  set B := badEqualDegreeChallenges domain f g d (A - 1)
  set X₁ : Finset (F × F × F) := {c | ∃ P,
    IsAffineExceptional domain g (fun i ↦ f i + c.1 * g i) d A 1 c.2.1 c.2.2 P}
  set X₂ : Finset (F × F × F) := {c | c.1 ∈ B}
  set X₃ : Finset (F × F × F) := {c | ∃ p ∈ T,
    ¬ HasCorrectLinearClaims v γ₀ γ₁ (msg c.1) c.1 p.1 p.2 ∧
      linearClaimResidual v γ₀ γ₁ (msg c.1) c.1 p.1 p.2 c.2.1 c.2.2 = 0}
  have hsub : ({c | ∃ P, IsLinearClaimExceptional domain f g d A 1 v γ₀ γ₁ (msg c.1)
      c.1 c.2.1 c.2.2 P} : Finset (F × F × F)) ⊆ X₁ ∪ X₂ ∪ X₃ := by
    intro c hc
    obtain ⟨P, hP⟩ := (Finset.mem_filter.mp hc).2
    rcases hP.isEqualDegreeExceptional_or_exists with h | ⟨F₀, G₀, hF, hG, -, hL, hbad, hres⟩
    · rcases h.isAffineExceptional_or_exists_degree_eq with h | h
      · exact Finset.mem_union_left _ (Finset.mem_union_left _
          (Finset.mem_filter.mpr ⟨Finset.mem_univ _, P, h⟩))
      · exact Finset.mem_union_left _ (Finset.mem_union_right _
          (Finset.mem_filter.mpr ⟨Finset.mem_univ _,
            by simpa [B, badEqualDegreeChallenges] using h⟩))
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, (F₀, G₀),
        hfin.mem_toFinset.mpr ⟨hF, hG, hL⟩, hbad, hres⟩)
  have hX₁ : (#X₁ : ℝ) ≤ q ^ 3 * E :=
    card_filter_isAffineExceptional_le_mul_affineMcaError domain d A 1 f g
  have hX₂ : (#X₂ : ℝ) = #B * q ^ 2 := by
    have : X₂ = B ×ˢ (Finset.univ : Finset (F × F)) := by
      ext c
      simp [X₂]
    rw [this, Finset.card_product, Finset.card_univ, Fintype.card_prod]
    push_cast
    ring
  have hX₃ : (#X₃ : ℝ) ≤ #T * q ^ 2 := by
    have hsum : #X₃ = ∑ θ : F, #{x : F × F | ∃ p ∈ T,
        ¬ HasCorrectLinearClaims v γ₀ γ₁ (msg θ) θ p.1 p.2 ∧
          linearClaimResidual v γ₀ γ₁ (msg θ) θ p.1 p.2 x.1 x.2 = 0} := by
      rw [Finset.card_filter, Fintype.sum_prod_type]
      simp only [Finset.card_filter]
    have hθ : ∀ θ : F, #{x : F × F | ∃ p ∈ T,
        ¬ HasCorrectLinearClaims v γ₀ γ₁ (msg θ) θ p.1 p.2 ∧
          linearClaimResidual v γ₀ γ₁ (msg θ) θ p.1 p.2 x.1 x.2 = 0} ≤
        #T * Fintype.card F := fun θ ↦ by
      calc _ ≤ #(T.biUnion fun p ↦ ({x : F × F |
            ¬ HasCorrectLinearClaims v γ₀ γ₁ (msg θ) θ p.1 p.2 ∧
              linearClaimResidual v γ₀ γ₁ (msg θ) θ p.1 p.2 x.1 x.2 = 0} : Finset (F × F))) := by
            refine Finset.card_le_card fun x hx ↦ ?_
            obtain ⟨p, hp, hx⟩ := (Finset.mem_filter.mp hx).2
            exact Finset.mem_biUnion.mpr ⟨p, hp, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩⟩
        _ ≤ ∑ p ∈ T, #({x : F × F |
            ¬ HasCorrectLinearClaims v γ₀ γ₁ (msg θ) θ p.1 p.2 ∧
              linearClaimResidual v γ₀ γ₁ (msg θ) θ p.1 p.2 x.1 x.2 = 0} : Finset (F × F)) :=
            Finset.card_biUnion_le
        _ ≤ ∑ _p ∈ T, Fintype.card F := Finset.sum_le_sum fun p _ ↦ by
            by_cases hp : HasCorrectLinearClaims v γ₀ γ₁ (msg θ) θ p.1 p.2
            · simp [hp]
            · refine (Finset.card_le_card fun x hx ↦ ?_).trans
                (card_filter_linearClaimResidual_eq_zero_le v hp)
              exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hx).2.2⟩
        _ = #T * Fintype.card F := by rw [Finset.sum_const, smul_eq_mul]
    have h : #X₃ ≤ #T * Fintype.card F * Fintype.card F := by
      rw [hsum]
      calc _ ≤ ∑ _θ : F, #T * Fintype.card F := Finset.sum_le_sum fun θ _ ↦ hθ θ
        _ = _ := by rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_comm]
    calc (#X₃ : ℝ) ≤ ((#T * Fintype.card F * Fintype.card F : ℕ) : ℝ) := by exact_mod_cast h
      _ = _ := by push_cast; ring
  have hBfloor : (#B : ℝ) ≤ (ℓ₀ : ℝ) :=
    hfloor _ (card_badEqualDegreeChallenges_mul_le domain f g d (A - 1))
  have hcount : (#{c : F × F × F | ∃ P, IsLinearClaimExceptional domain f g d A 1 v γ₀ γ₁
      (msg c.1) c.1 c.2.1 c.2.2 P} : ℝ) / q ^ 3 ≤ E + 2 * (ℓ₀ : ℝ) / q := by
    rw [div_le_iff₀ (by positivity)]
    calc (#{c : F × F × F | ∃ P, IsLinearClaimExceptional domain f g d A 1 v γ₀ γ₁
          (msg c.1) c.1 c.2.1 c.2.2 P} : ℝ)
        ≤ #(X₁ ∪ X₂ ∪ X₃) := by exact_mod_cast Finset.card_le_card hsub
      _ ≤ #X₁ + #X₂ + #X₃ := by
          exact_mod_cast (Finset.card_union_le _ _).trans
            (Nat.add_le_add_right (Finset.card_union_le _ _) _)
      _ ≤ q ^ 3 * E + (ℓ₀ : ℝ) * q ^ 2 + (ℓ₀ : ℝ) * q ^ 2 := by
          rw [hX₂]
          gcongr
          exact hX₃.trans (by gcongr)
      _ = (E + 2 * (ℓ₀ : ℝ) / q) * q ^ 3 := by
          field_simp
          ring
  calc _ ≤ ENNReal.ofReal (E + 2 * (ℓ₀ : ℝ) / q) :=
        ENNReal.ofReal_le_ofReal hcount
    _ = _ := by
      rw [ENNReal.ofReal_add ENNReal.toReal_nonneg (by positivity), ENNReal.ofReal_toReal hE]

end ReedSolomon

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

For a public weight vector `v`, the prover claims `linearClaim v F = γ₀` and
`linearClaim v G = γ₁`. After seeing `θ`, it sends `c` as the claim for `X(F + θG)`.
The claim for the combined polynomial is `γ₁ + α (γ₀ + θγ₁) + βc`.
A candidate is exceptional if it agrees, satisfies this claim, and has no witness pair
with correct claims that loses at most the allowed number of agreements.

At loss one, the Johnson bound limits the list of witness pairs of degree below `d`
with `A - 1` common agreements. Except for the first challenges excluded by the
equal-degree argument, each false pair needs a nonzero affine residual in `(α, β)`
to vanish. This gives the first inequality of (5.5) in Theorem 5.1 of [CWYZ26].
Each excluded challenge also gives a pair of degree at most `d` whose second polynomial has
degree exactly `d`. So the excluded challenges and the list fit one Johnson list, and the
additive term `2ℓ₀/q` of (5.5) improves to `ℓ₀/q`.
See the [paper page](../../../../../../docs/kb/papers/CWYZ26.md) for the correspondence.

## Main definitions and statements

* `ReedSolomon.LinearClaimInstance`: words, public weights, claims, and the prover's
  message as a function of the first challenge.
* `ReedSolomon.HasCorrectLinearClaims`: the three claims of a witness pair are correct.
* `ReedSolomon.linearClaim_add_affineMultiplier_mul`: the combination identity for
  honest claims, valid at any degree.
* `ReedSolomon.linearClaimMcaError`: the worst-case exceptional-event probability.
  Its exact rational evaluator is in the sibling `LinearClaimsExact` module.
* `ReedSolomon.linearClaimMcaError_le_affineMcaError_add_johnson`: the error is at most the
  affine error plus `ℓ₀/q`, where `ℓ₀` is the Johnson list bound.
* `ReedSolomon.linearClaimMcaError_le_affineMcaError_add`: the weaker bound with `2ℓ₀/q`.

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

namespace LinearClaimInstance

/-- The instance fields as a product that can be enumerated over finite `ι` and `F`. -/
def equivProd (ι F : Type*) (d : ℕ) :
    LinearClaimInstance ι F d ≃
      (ι → F) × (ι → F) × (Fin (d + 1) → F) × F × F × (F → F) where
  toFun w := (w.f, w.g, w.v, w.γ₀, w.γ₁, w.message)
  invFun := fun ⟨f, g, v, γ₀, γ₁, message⟩ ↦ ⟨f, g, v, γ₀, γ₁, message⟩
  left_inv := by intro w; cases w; rfl
  right_inv := by rintro ⟨f, g, v, γ₀, γ₁, message⟩; rfl

instance [DecidableEq ι] [Fintype F] (d : ℕ) : Fintype (LinearClaimInstance ι F d) :=
  Fintype.ofEquiv _ (equivProd ι F d).symm

end LinearClaimInstance

/-- The three claims of a witness pair `F₀, G₀` hold for the challenge `θ` and message `c`.

They are `⟨coef(F₀), v⟩ = γ₀`, `⟨coef(G₀), v⟩ = γ₁`, and `⟨coef(X(F₀ + θG₀)), v⟩ = c`. -/
def HasCorrectLinearClaims {d : ℕ} (v : Fin (d + 1) → F) (γ₀ γ₁ c θ : F) (F₀ G₀ : F[X]) : Prop :=
  linearClaim v F₀ = γ₀ ∧ linearClaim v G₀ = γ₁ ∧ linearClaim v (X * (F₀ + C θ * G₀)) = c

/-- `P` is exceptional for the linear-claim combiner at `(θ, α, β)` with prover message `c`.

`P` has degree at most `d` and agrees with `g + (α + β x)(f + θ g)` on at least `A` points.
It satisfies the combined claim `⟨coef(P), v⟩ = γ₁ + α(γ₀ + θ γ₁) + β c`.
Consider pairs `F₀, G₀` of degrees below `d` with `P = G₀ + (α + βX)(F₀ + θG₀)`.
Assume their claims are correct: `⟨coef(F₀), v⟩ = γ₀`, `⟨coef(G₀), v⟩ = γ₁`,
and `⟨coef(X(F₀ + θG₀)), v⟩ = c`.
Every such pair loses more than `s` of these points. -/
def IsLinearClaimExceptional (domain : ι ↪ F) (f g : ι → F) (d A s : ℕ) (v : Fin (d + 1) → F)
    (γ₀ γ₁ c θ α β : F) (P : F[X]) : Prop :=
  P.degree ≤ d ∧
    A ≤ #(polynomialAgreementSet domain (equalDegreeWord domain f g θ α β) P) ∧
    linearClaim v P = γ₁ + α * (γ₀ + θ * γ₁) + β * c ∧
    ∀ F₀ G₀ : F[X], F₀.degree < d → G₀.degree < d →
      P = G₀ + affineMultiplier α β * (F₀ + C θ * G₀) →
      HasCorrectLinearClaims v γ₀ γ₁ c θ F₀ G₀ →
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
  refine ⟨F₀, G₀, hF, hG, hPeq, ?_, fun hcorr ↦ ?_, ?_⟩
  · classical
    refine (Nat.sub_le_sub_left hloss A).trans ((Nat.sub_le_sub_right hA _).trans
      ((Finset.le_card_sdiff _ _).trans (Finset.card_le_card fun i hi ↦ ?_)))
    obtain ⟨hiP, hiL⟩ := Finset.mem_sdiff.mp hi
    simp only [Finset.mem_filter, hiP, true_and, not_or, not_not] at hiL
    exact (mem_commonPolynomialAgreementSet _ _ _ _ _ _).mpr hiL
  · have := hexc F₀ G₀ hF hG hPeq hcorr
    omega
  · rw [hPeq, linearClaim_add_affineMultiplier_mul] at hclaim
    unfold linearClaimResidual
    linear_combination hclaim

/-- At loss one, the linear-claim error is at most the affine error plus `ℓ₀/q`.

Here `n = |ι|` is the domain size, and `q = |F|` is the field size.
The rounded-down Johnson bound is `ℓ₀ = ⌊n(A - 1 - d)/((A - 1)² - nd)⌋`.
Assume `nd < (A - 1)²`.

Each bad first challenge gives a pair of degree at most `d` whose second polynomial has
degree exactly `d`, and distinct challenges give distinct pairs.
The listed pairs with a false claim have both degrees below `d`.
Both kinds have `A - 1` common agreements, so one Johnson list bounds them together. -/
theorem linearClaimMcaError_le_affineMcaError_add_johnson [Fintype F] (domain : ι ↪ F) {d A : ℕ}
    (hJ : Fintype.card ι * d < (A - 1) ^ 2) :
    linearClaimMcaError domain d A 1 ≤ affineMcaError domain d A 1 +
      ENNReal.ofReal
        (((⌊(Fintype.card ι : ℝ) * ((A : ℝ) - 1 - d) /
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
  set B := badEqualDegreeChallenges domain f g d (A - 1)
  have hB : ∀ θ ∈ B, ∃ U V : F[X], U.degree ≤ d ∧ V.degree = d ∧
      U.coeff d + θ * V.coeff d = 0 ∧
      A - 1 ≤ #(commonPolynomialAgreementSet domain f g U V) := fun θ hθ ↦ by
    simpa [B, badEqualDegreeChallenges] using hθ
  choose! U V hU hV hlead hUV using hB
  let bPair (θ : F) := (U θ, V θ)
  have hinj : Set.InjOn bPair B := by
    intro θ hθ θ' hθ' heq
    obtain ⟨h₁, h₂⟩ := Prod.mk.inj heq
    have hcoeff : (V θ).coeff d ≠ 0 := by
      rw [← natDegree_eq_of_degree_eq_some (hV θ hθ)]
      exact leadingCoeff_ne_zero.mpr fun hzero ↦ by simpa [hzero] using hV θ hθ
    have h := (hlead θ hθ).trans (hlead θ' hθ').symm
    rw [h₁, h₂] at h
    exact mul_right_cancel₀ (h₂ ▸ hcoeff) (add_left_cancel h)
  have hdisjoint : Disjoint (B.image bPair) T := by
    refine Finset.disjoint_left.mpr fun p hp hpT ↦ ?_
    obtain ⟨θ, hθ, rfl⟩ := Finset.mem_image.mp hp
    have hlt := (hfin.mem_toFinset.mp hpT).2.1
    change (V θ).degree < d at hlt
    exact (ne_of_lt hlt) (hV θ hθ)
  have hsum : (((#T + #B : ℕ) : ℝ)) ≤ ℓ₀ := by
    have hj := card_mul_sq_sub_card_mul_le_of_commonPolynomialAgreementSet domain f g
      (d := d) (L := A - 1) (B.image bPair ∪ T) (fun p hp ↦ ?_) (fun p hp ↦ ?_)
    · rw [Finset.card_union_of_disjoint hdisjoint, Finset.card_image_of_injOn hinj, add_comm] at hj
      exact hfloor _ hj
    · rcases Finset.mem_union.mp hp with h | h
      · obtain ⟨θ, hθ, rfl⟩ := Finset.mem_image.mp h
        exact ⟨hU θ hθ, (hV θ hθ).le⟩
      · obtain ⟨h₁, h₂, -⟩ := hfin.mem_toFinset.mp h
        exact ⟨h₁.le, h₂.le⟩
    · rcases Finset.mem_union.mp hp with h | h
      · obtain ⟨θ, hθ, rfl⟩ := Finset.mem_image.mp h
        exact hUV θ hθ
      · exact (hfin.mem_toFinset.mp h).2.2
  set X₃ : Finset (F × F × F) := {c | ∃ p ∈ T,
    ¬ HasCorrectLinearClaims v γ₀ γ₁ (msg c.1) c.1 p.1 p.2 ∧
      linearClaimResidual v γ₀ γ₁ (msg c.1) c.1 p.1 p.2 c.2.1 c.2.2 = 0}
  have hp (c : F × F × F) (hc : ∃ P, IsLinearClaimExceptional domain f g d A 1 v γ₀ γ₁
      (msg c.1) c.1 c.2.1 c.2.2 P) :
      ((∃ P, IsAffineExceptional domain g (fun i ↦ f i + c.1 * g i) d A 1 c.2.1 c.2.2 P) ∨
        c ∈ X₃) ∨ c.1 ∈ B := by
    obtain ⟨P, hP⟩ := hc
    rcases hP.isEqualDegreeExceptional_or_exists with h | ⟨F₀, G₀, hF, hG, -, hL, hbad, hres⟩
    · rcases h.isAffineExceptional_or_exists_degree_eq with h | h
      · exact Or.inl (Or.inl ⟨P, h⟩)
      · exact Or.inr (by simpa [B, badEqualDegreeChallenges] using h)
    · exact Or.inl (Or.inr (Finset.mem_filter.mpr ⟨Finset.mem_univ _, (F₀, G₀),
        hfin.mem_toFinset.mpr ⟨hF, hG, hL⟩, hbad, hres⟩))
  -- For each `θ`, each listed pair with a false claim adds at most `q` pairs `(α, β)`.
  have hX₃ (θ : F) : #{x : F × F | (θ, x.1, x.2) ∈ X₃} ≤ #T * Fintype.card F := by
    calc _ ≤ #(T.biUnion fun p ↦ ({x : F × F |
          ¬ HasCorrectLinearClaims v γ₀ γ₁ (msg θ) θ p.1 p.2 ∧
            linearClaimResidual v γ₀ γ₁ (msg θ) θ p.1 p.2 x.1 x.2 = 0} : Finset (F × F))) := by
          refine Finset.card_le_card fun x hx ↦ ?_
          obtain ⟨p, hp, hx⟩ := (Finset.mem_filter.mp (Finset.mem_filter.mp hx).2).2
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
  -- For each `θ`, at most `q² (E + #T / q)` pairs are affine exceptional or in `X₃`.
  have ha (θ : F) : (#{x : F × F |
      (∃ P, IsAffineExceptional domain g (fun i ↦ f i + θ * g i) d A 1 x.1 x.2 P) ∨
        (θ, x.1, x.2) ∈ X₃} : ℝ) ≤ q ^ 2 * (E + #T / q) := by
    rw [Finset.filter_or]
    calc _ ≤ (#({x : F × F | ∃ P, IsAffineExceptional domain g (fun i ↦ f i + θ * g i) d A 1
          x.1 x.2 P} : Finset (F × F)) : ℝ) + #({x : F × F | (θ, x.1, x.2) ∈ X₃} :
            Finset (F × F)) := by exact_mod_cast Finset.card_union_le _ _
      _ ≤ q ^ 2 * E + #T * q := by
          gcongr
          · exact card_filter_isAffineExceptional_le_mul_affineMcaError domain d A 1 g _
          · have h : ((#{x : F × F | (θ, x.1, x.2) ∈ X₃} : ℕ) : ℝ) ≤
                ((#T * Fintype.card F : ℕ) : ℝ) := by exact_mod_cast hX₃ θ
            rw [Nat.cast_mul] at h
            exact h
      _ = q ^ 2 * (E + #T / q) := by field_simp
  have hcount : (#{c : F × F × F | ∃ P, IsLinearClaimExceptional domain f g d A 1 v γ₀ γ₁
      (msg c.1) c.1 c.2.1 c.2.2 P} : ℝ) / q ^ 3 ≤ E + (ℓ₀ : ℝ) / q := by
    have key := Finset.card_filter_triples_le_of_imp_or B hp ha
    rw [div_le_iff₀ (by positivity)]
    calc _ ≤ q ^ 3 * (E + #T / q) + #B * q ^ 2 := key
      _ = q ^ 3 * E + #T * q ^ 2 + #B * q ^ 2 := by field_simp
      _ = q ^ 3 * E + (((#T + #B : ℕ) : ℝ)) * q ^ 2 := by push_cast; ring
      _ ≤ q ^ 3 * E + (ℓ₀ : ℝ) * q ^ 2 := by gcongr
      _ = (E + (ℓ₀ : ℝ) / q) * q ^ 3 := by
          field_simp
  calc _ ≤ ENNReal.ofReal (E + (ℓ₀ : ℝ) / q) :=
        ENNReal.ofReal_le_ofReal hcount
    _ = _ := by
      rw [ENNReal.ofReal_add ENNReal.toReal_nonneg (by positivity), ENNReal.ofReal_toReal hE]

/-- At loss one, the linear-claim error is at most the affine error plus `2ℓ₀/q`.

Here `n = |ι|` is the domain size, and `q = |F|` is the field size.
The rounded-down Johnson bound is `ℓ₀ = ⌊n(A - 1 - d)/((A - 1)² - nd)⌋`.
Assume `nd < (A - 1)²`.
This follows from `linearClaimMcaError_le_affineMcaError_add_johnson`, since `ℓ₀ ≤ 2ℓ₀`. -/
theorem linearClaimMcaError_le_affineMcaError_add [Fintype F] (domain : ι ↪ F) {d A : ℕ}
    (hJ : Fintype.card ι * d < (A - 1) ^ 2) :
    linearClaimMcaError domain d A 1 ≤ affineMcaError domain d A 1 +
      ENNReal.ofReal
        (2 * ((⌊(Fintype.card ι : ℝ) * ((A : ℝ) - 1 - d) /
          (((A : ℝ) - 1) ^ 2 - Fintype.card ι * d)⌋₊ : ℕ) : ℝ) / Fintype.card F) := by
  refine (linearClaimMcaError_le_affineMcaError_add_johnson domain hJ).trans ?_
  gcongr
  exact le_mul_of_one_le_left (by positivity) one_le_two

end ReedSolomon

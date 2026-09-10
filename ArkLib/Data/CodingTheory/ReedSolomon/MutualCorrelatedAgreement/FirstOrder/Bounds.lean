/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.FirstOrder.AutomaticHybridProbability
public import ArkLib.Data.CodingTheory.ReedSolomon.ListDecodability.FirstOrder.Bounds
/-!
# Exact first-order correlated agreement along a received line

Above the first-order rate curve, one automatic numerical recipe supplies both the complete-list
bound and exact mutual correlated agreement (MCA) along every received line. Its parameters are
fixed from the physical rate `ρ` and agreement fraction `a` before choosing a field or received
words.

For `D = k - 1`, put `θ = (n - D) / (A - D)` and
`T = ∑_{r=1}^M r(2(μ-M)+r)`. The paper-facing exception count is `E = E₀ + E₁ + E₂`, where

* `E₀ = (2μ-1)h + θ(h+μ+4Dμh) + (n-D-1)μ` handles the ordinary tail,
* `E₁ = (24D²h+8D)θ²T` handles joint regular-stage families, and
* `E₂ = 4D(n-D-1)θT` handles generic regular fibers.

One exceptional set works simultaneously for every qualifying polynomial. The recovered pair may
depend on the challenge and polynomial, and its conclusion identifies the entire agreement set.
The field is arbitrary here; finite-field probability is derived in `FirstOrder.RateBounds`.
-/

@[expose] public section

namespace ReedSolomon
open Polynomial HiddenDerivative

open Classical in
/-- The optimized finite bounds and closed `Λ` and `E` from one automatic first-order recipe.

The outer quantifiers make the uniformity explicit: numerical and code parameters precede the
field; the list conclusion then holds for every received word, while one exceptional set is chosen
for each received line before either the challenge or candidate polynomial. -/
theorem automaticFirstOrder_list_and_lineMCA
    (rho a : ℝ) (n k A : ℕ)
    (hrho : 0 < rho) (hrhoOne : rho < 1)
    (ha : automaticFirstOrderThreshold rho < a) (haOne : a < 1)
    /-

    The dimension and integer agreement threshold enforce the fixed physical rate
    and the requested agreement fraction.
    -/
    (hn : 0 < n) (hk : 2 ≤ k) (hkRate : (k : ℝ) ≤ rho * n)
    (hA : a * n ≤ A) (hAn : A ≤ n)
    /-

    Distinct evaluation points turn agreement into a count of distinct polynomial roots.
    -/
    {F : Type*} [Field F] (domain : Fin n ↪ F)
    (hchar : ringChar F = 0 ∨
      max (k - 1) (automaticDerivativeCap rho a) < ringChar F) :
    -- D is the largest candidate degree. The incidence ratio is
    -- theta = (n-D)/(A-D), with 1 ≤ theta ≤ 1/(a-rho).
    let D := k - 1
    let theta := hybridTheta n D A
    /-

    h bounds challenge degree, mu total jet degree, and M hidden-derivative degree.
    -/
    let h := automaticChallengeHeight rho a
    let mu := automaticJetDegree rho a
    let M := automaticDerivativeCap rho a
    /-

    Finiteness and the cardinality bound concern the complete list, even over infinite fields.
    -/
    (∀ received : Fin n → F,
      (closePolynomialSet domain received k A).Finite ∧
        ((closePolynomialSet domain received k A).ncard : ℝ) ≤
          hybridListOptimizedRaw theta D mu M ∧
        (closePolynomialSet domain received k A).ncard ≤
          hybridListOptimizedCeil theta D mu M ∧
        ((closePolynomialSet domain received k A).ncard : ℝ) ≤
          hybridLambdaClosed theta D mu M) ∧
      ∀ f g : Fin n → F, ∃ exceptional : Finset F,
        (exceptional.card : ℝ) ≤ hybridEOptimizedRaw theta n D A h mu M ∧
        exceptional.card ≤ hybridEOptimizedCeil theta n D A h mu M ∧
        (exceptional.card : ℝ) ≤ hybridEClosed theta n D h mu M ∧
        ∀ z ∉ exceptional, ∀ P : F[X], P.degree < k →
          A ≤ (polynomialAgreementSet domain (fun i ↦ f i + z * g i) P).card →
          HasExactCorrelatedPair domain f g (RingHom.id F) k z P := by
  dsimp only
  constructor
  · intro received
    exact automaticFirstOrder_closePolynomialSet_finite_and_card_le
      hrho hrhoOne ha haOne hn rfl hk hkRate hA hAn domain received hchar
  · intro f g
    obtain ⟨Q, hQ, hweight, hdegree, hheight, hsound, exceptional,
        hraw, hceil, hclosed, hgood⟩ :=
      exists_automaticFirstOrder_hybridEquation_base
        hrho hrhoOne ha haOne hn rfl hk hkRate hA hAn hchar domain f g
    refine ⟨exceptional, hraw, hceil, hclosed, ?_⟩
    intro z hz P hP hagree
    have hdegreeCast : P.degree < ((k - 1 : ℕ) : WithBot ℕ) + 1 := by
      have heq : ((k : WithBot ℕ)) = ((k - 1 : ℕ) : WithBot ℕ) + 1 :=
        congrArg (fun x : ℕ ↦ (x : WithBot ℕ))
          (Nat.sub_add_cancel (by omega : 1 ≤ k)).symm
      rwa [← heq]
    simpa only [show k - 1 + 1 = k by omega, Matrix.cons_val_zero,
      Matrix.cons_val_one] using
      (exactCorrelatedPair_of_powerAgreement_one domain ![f, g] (RingHom.id F) z P
        (hgood z hz P hdegreeCast (by
          have hword : powerBatchedWord ![f, g] z = (fun i ↦ f i + z * g i) := by
            funext i
            simp [powerBatchedWord, Fin.sum_univ_two]
          rwa [hword])))

open Classical in
/-- **One exceptional set gives exact correlated agreement along a received line.**

Fix a physical rate upper bound `ρ` and an agreement fraction `a` above the first-order
threshold. The automatic recipe determines `M`, `μ`, and `h` from these two real numbers.
No interpolation certificate or surplus inequality is required from the caller.

For any received words `f` and `g`, there is a set of at most `E` exceptional challenges.
Outside this set, every polynomial `P` of degree `< k` with at least `A` agreements with
`f + z * g` has a representation `P = P₀ + z * P₁`, where both degrees are `< k` and

`Agr(f + z * g, P) = Agr(f, P₀) ∩ Agr(g, P₁)`.

The exceptional set is uniform over all candidate polynomials. The recovered pair may
depend on the challenge and candidate. The field need not be finite. In characteristic zero
the characteristic guard is automatic; in positive characteristic it requires `p > D` and
`p > M`, while the ordinary tail needs no `p > μ` hypothesis.
-/
theorem automatic_first_order_line_agreement
    /-

    Choose the physical rate and agreement fraction before the code data.
    -/
    (ρ a : ℝ)
    (hρ : 0 < ρ)
    (hρone : ρ < 1)
    (ha : automaticFirstOrderThreshold ρ < a)
    (haone : a < 1)
    /-

    Dimension k means degree strictly below k; A counts agreeing positions.
    -/
    (n k A : ℕ)
    (hn : 0 < n)
    (hk : 2 ≤ k)
    (hrate : (k : ℝ) ≤ ρ * n)
    (hagree : a * n ≤ A)
    (hAn : A ≤ n)
    /-

    Distinct evaluation points over an arbitrary field.
    -/
    {F : Type*} [Field F]
    (domain : Fin n ↪ F)
    -- Taylor recovery through degree D divides by 1,...,D; separant descent
    -- differentiates at most M times in Y₁. These require p > D and p > M
    -- in positive characteristic. The ordinary tail is characteristic-free,
    -- so no p > μ assumption is needed.
    (hchar : ringChar F = 0 ∨
      max (k - 1) (automaticDerivativeCap ρ a) < ringChar F)
    (f g : Fin n → F) :
    /-

    D = k - 1 is the largest allowed candidate degree.
    The hypotheses give D < A ≤ n, so the differences below are positive.
    -/
    let D := k - 1
    /-

    θ = (n - D) / (A - D) is the direct agreement-incidence ratio.
    It converts the degree of a fixed-word solution family into a candidate count.
    Here 1 ≤ θ ≤ 1 / (a - ρ); the ratio grows as agreement approaches the rate.
    -/
    let θ := hybridTheta n D A
    /-

    The recipe uses a₀ = min(a, (1 + a₁(ρ))/2), β = 3(1-a₀)/(2(2-ρ)),
    and m = ceil(4/S), where S > 0 is the normalized interpolation surplus.
    Then mS ≥ 4 pays for the finite rounding loss 3m², leaving positive surplus.
    M = floor(βm) caps the exponent of the hidden derivative variable Y₁.
    Lean normalizes this cap by min with μ; the recipe proves M ≤ μ.
    -/
    let M := automaticDerivativeCap ρ a
    /-

    μ = ceil(m a₀ / ρ) bounds total degree in the jet variables (Y₀,Y₁).
    This is distinct from the Y₁-degree cap M and the candidate degree D.
    -/
    let μ := automaticJetDegree ρ a
    /-

    h = max(1, floor(r(m,M) μ / (N₀ - r(m,M)))) bounds the degree
    in the challenge variable of the symbolic interpolant.
    N₀ is the normalized source count; r(m,M) is a certified upper bound on the
    local constraint rank.
    The finite-surplus proof gives N₀ - r(m,M) > 0; choosing h this way
    leaves enough challenge-coefficient slots for a nonzero polynomial kernel vector.
    -/
    let h := automaticChallengeHeight ρ a
    /-

    The regular-stage degree sum is
    T = sum_{r=1}^M r(2(μ-M)+r)
      = (μ-M)M(M+1) + M(M+1)(2M+1)/6.
    Retaining M at every separant stage gives this sum instead of a μ-only bound.
    -/
    let T := hybridT μ M
    /-

    The closed exception count is E = E₀ + E₁ + E₂, where
    E₀ = (2μ-1)h + θ(h+μ+4Dμh) + (n-D-1)μ is the ordinary-tail budget.
    Its first term covers exceptional content/resultant specializations;
    its second applies incidence to the factorwise rational images;
    its third allows accidental agreements on at most μ persistent graph lines.

    For the regular stages, the joint-family degree satisfies
    J₁ ≤ (12D²h+4D)T and the generic-fiber degree satisfies B₁ ≤ 2DT.
    Keeping L = D + ceil((A-D)/2) common agreements costs at most
    2θ²J₁ + 2(n-D-1)θB₁ exceptions. Thus the two remaining terms are
    E₁ = (24D²h+8D)θ²T and E₂ = 4D(n-D-1)θT.
    E counts challenges; only min(1,E/|F|) is a finite-field probability.
    -/
    let E₀ := hybridOrdinaryRaw θ n D h μ
    let E : ℝ := E₀ + (24 * D ^ 2 * h + 8 * D) * θ ^ 2 * T +
      4 * D * (n - D - 1 : ℕ) * θ * T
    /-

    Choose one exceptional set before the challenge or candidate polynomial.
    -/
    ∃ exceptional : Finset F,
      (exceptional.card : ℝ) ≤ E ∧
      /-

      Every qualifying candidate outside the fixed exceptional set admits exact recovery.
      -/
      ∀ z ∉ exceptional,
        ∀ P : F[X],
          P.degree < k →
          A ≤ (polynomialAgreementSet domain (fun i ↦ f i + z * g i) P).card →
          /-

          Exact recovery includes equality of the entire agreement set.
          -/
          HasExactCorrelatedPair domain f g (RingHom.id F) k z P := by
  dsimp only
  obtain ⟨exceptional, _hraw, _hceil, hclosed, hgood⟩ :=
    (automaticFirstOrder_list_and_lineMCA ρ a n k A hρ hρone ha haone
      hn hk hrate hagree hAn domain hchar).2 f g
  exact ⟨exceptional, hclosed, hgood⟩

open Classical in
/-- Paper-facing positive-slack form of `automatic_first_order_line_agreement`.

The equation `a = a₁(ρ) + η₁` makes strict separation from the rate curve explicit. The
rate-only consequence bounds `E` by `O_ρ(n² / η₁⁵)`; this theorem retains the exact finite
formula and arbitrary-field quantifiers. -/
theorem automatic_first_order_line_agreement_of_slack
    (ρ η₁ : ℝ)
    (hρ : 0 < ρ)
    (hρone : ρ < 1)
    (hη₁ : 0 < η₁)
    (haone : automaticFirstOrderThreshold ρ + η₁ < 1)
    /-

    Dimension k means degree < k; A is the integer agreement threshold.
    -/
    (n k A : ℕ)
    (hn : 0 < n)
    (hk : 2 ≤ k)
    (hrate : (k : ℝ) ≤ ρ * n)
    (hagree : (automaticFirstOrderThreshold ρ + η₁) * n ≤ A)
    (hAn : A ≤ n)
    /-

    Distinct evaluation points turn agreement into a count of distinct polynomial roots.
    -/
    {F : Type*} [Field F]
    (domain : Fin n ↪ F)
    (hchar : ringChar F = 0 ∨
      max (k - 1)
        (automaticDerivativeCap ρ (automaticFirstOrderThreshold ρ + η₁)) < ringChar F)
    (f g : Fin n → F) :
    /-

    Positive slack fixes a strictly above a₁(ρ); the recipe below is evaluated at this a.
    -/
    let a := automaticFirstOrderThreshold ρ + η₁
    let D := k - 1
    let θ := hybridTheta n D A
    let M := automaticDerivativeCap ρ a
    let μ := automaticJetDegree ρ a
    let h := automaticChallengeHeight ρ a
    let T := hybridT μ M
    let E₀ := hybridOrdinaryRaw θ n D h μ
    let E : ℝ := E₀ + (24 * D ^ 2 * h + 8 * D) * θ ^ 2 * T +
      4 * D * (n - D - 1 : ℕ) * θ * T
    /-

    One exceptional set must work for all challenges and candidates quantified below.
    -/
    ∃ exceptional : Finset F,
      (exceptional.card : ℝ) ≤ E ∧
      ∀ z ∉ exceptional,
        ∀ P : F[X],
          P.degree < k →
          A ≤ (polynomialAgreementSet domain (fun i ↦ f i + z * g i) P).card →
          HasExactCorrelatedPair domain f g (RingHom.id F) k z P := by
  dsimp only
  exact automatic_first_order_line_agreement ρ (automaticFirstOrderThreshold ρ + η₁)
    hρ hρone (lt_add_of_pos_right _ hη₁) haone n k A hn hk hrate hagree hAn
    domain hchar f g
end ReedSolomon

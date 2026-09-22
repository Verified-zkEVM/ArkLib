/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.Agreement
public import ArkLib.ToMathlib.Finset.LineAgreement
public import ArkLib.ToMathlib.LinearAlgebra.LagrangeLine

/-!
# Recognizing graph lines from a common agreement sample

Fix an evaluation domain `domain : ι ↪ F` and two received words `f g : ι → F`. For a field
homomorphism `φ : F →+* E`, the affine received word at a challenge `z : E` is
`i ↦ φ (f i) + z * φ (g i)`, evaluated on the domain `domain.trans ⟨φ, φ.injective⟩`.

A sample of `k` coordinates determines two polynomials `F₀ G₀` over `F` of degree below `k`,
the interpolants of `f` and `g`. Over every field extension and at every challenge, a polynomial of
degree below `k` agreeing with the affine word on the sample is `F₀.map φ + C z * G₀.map φ`.
For a fixed pair `F₀ G₀`, the agreement set of this polynomial with the affine word is the common
agreement set of `F₀` with `f` and `G₀` with `g`, except for at most one challenge per coordinate
where `G₀` disagrees with `g`.

In characteristic `p`, a Frobenius pullback of degree below `p ^ e * k` with sparse Taylor
coefficients is recognized from the same `k` coordinates, evaluated at `p ^ e`-th roots of the
domain points, with the challenge `w ^ p ^ e`.

## Main statements

* `ReedSolomon.exists_graphLine_polynomials_of_sample`: recognition over every extension.
* `ReedSolomon.exists_exceptional_graphLine_challenges_le_disagreement`: at most
  `Fintype.card ι - #(polynomialAgreementSet domain g G₀)` challenges create agreement beyond the
  common agreement set.
* `ReedSolomon.exists_exceptional_graphLine_challenges`,
  `ReedSolomon.exists_exceptional_graphLine_challenges_of_sample`: the same with the bounds
  `Fintype.card ι - #(commonPolynomialAgreementSet domain f g F₀ G₀)` and `Fintype.card ι - k`.
* `ReedSolomon.exists_graphLine_polynomials_and_exceptional_challenges`: both conclusions for
  one pair.
* `ReedSolomon.exists_frobeniusGraphLine_polynomials_of_sample`: recognition of a sparse
  Frobenius pullback.

## References

Ported from ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`, from
`Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/GraphLine.lean` and
`Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/Ordinary/Frobenius/PointRecognition.lean`.
The two source files are merged because a module for the second at its source path would exceed
the module-name length limit, and both recognize a graph line from one sample. Throughout, the
coordinate type `Fin n` is generalized to any type `ι` (finite where agreement sets appear), and
the source's `mappedDomain domain iota` is written out as `domain.trans ⟨φ, φ.injective⟩`, as in
`ArkLib.Data.CodingTheory.ReedSolomon.PowerAgreement`.

* `exists_graphLine_polynomials_of_sample` has the source statement. Its proof is
  `Lagrange.eq_map_interpolate_add_C_mul_of_eval_eq`.
* `exists_exceptional_graphLine_challenges` has the source statement. It is derived from the new
  `exists_exceptional_graphLine_challenges_le_disagreement`, whose bound counts only coordinates
  where `G₀` disagrees with `g`. Its proof is
  `Finset.exists_card_le_forall_add_mul_eq_add_mul_iff` instead of the source's product of linear
  polynomials.
* `exists_graphLine_polynomials_and_exceptional_challenges` bounds the exceptional set by
  `Fintype.card ι - k` instead of the source's `n`.
* `exists_frobeniusGraphLine_polynomials_of_sample` needs the root condition only on the sample
  instead of on every coordinate. Its proof is
  `Lagrange.eq_expand_map_interpolate_add_C_mul_of_eval_eq`.
* `exists_exceptional_graphLine_challenges_of_sample` has the source statement.

The source's private `accidentalFactor` and `accidentalPolynomial` are not ported. Consumers of
these statements in the source's `Ordinary/Frobenius/`, `TaylorChart/`, `Pairs/` and
`PolynomialCurve/` directories are not ported here.
-/

@[expose] public section

namespace ReedSolomon

open Polynomial

/-- **Graph-line recognition.** A sample of `k` coordinates determines polynomials `F₀ G₀` over
`F` of degree below `k` that agree with `f` and `g` on the sample, such that, over every field
extension `φ : F →+* E` and at every challenge `z : E`, a polynomial `P` of degree below `k` that
agrees with the affine word `φ ∘ f + z • φ ∘ g` on the sample is `F₀.map φ + C z * G₀.map φ`.

The pair is chosen before `E`, `φ`, `z` and `P`. The degree bound `k` is the sample size: with a
larger bound, `P` is not determined by the sample. -/
theorem exists_graphLine_polynomials_of_sample {F ι : Type*} [Field F] {k : ℕ}
    (domain : ι ↪ F) (f g : ι → F) (sample : Finset ι) (hsample : sample.card = k) :
    ∃ F₀ G₀ : F[X], F₀.degree < k ∧ G₀.degree < k ∧
      (∀ i ∈ sample, F₀.eval (domain i) = f i ∧ G₀.eval (domain i) = g i) ∧
      ∀ {E : Type*} [Field E] (φ : F →+* E) (z : E) (P : E[X]), P.degree < k →
        (∀ i ∈ sample,
          P.eval (domain.trans ⟨φ, φ.injective⟩ i) = φ (f i) + z * φ (g i)) →
        P = F₀.map φ + C z * G₀.map φ := by
  classical
  subst hsample
  have hinj : Set.InjOn domain sample := domain.injective.injOn
  refine ⟨Lagrange.interpolate sample domain f, Lagrange.interpolate sample domain g,
    Lagrange.degree_interpolate_lt f hinj, Lagrange.degree_interpolate_lt g hinj,
    fun i hi ↦ ⟨Lagrange.eval_interpolate_at_node f hinj hi,
      Lagrange.eval_interpolate_at_node g hinj hi⟩, ?_⟩
  intro E _ φ z P hP heval
  exact Lagrange.eq_map_interpolate_add_C_mul_of_eval_eq φ hinj f g z hP heval

/-- **Exceptional challenges, counted by the disagreements of `G₀`.** For fixed `F₀ G₀` over
`F` and any extension `φ : F →+* E`, outside a set of at most
`Fintype.card ι - #(polynomialAgreementSet domain g G₀)` challenges `z`, the agreement set of
`F₀.map φ + C z * G₀.map φ` with the affine word `φ ∘ f + z • φ ∘ g` is exactly the common
agreement set of `F₀` with `f` and `G₀` with `g`.

Each coordinate where `G₀` disagrees with `g` contributes at most one exceptional challenge;
coordinates where `G₀` agrees with `g` contribute none. No degree bound on `F₀` or `G₀` is
needed. -/
theorem exists_exceptional_graphLine_challenges_le_disagreement
    {F E ι : Type*} [Field F] [Field E] [DecidableEq F] [DecidableEq E] [Fintype ι]
    (domain : ι ↪ F) (f g : ι → F) (F₀ G₀ : F[X]) (φ : F →+* E) :
    ∃ exceptional : Finset E,
      exceptional.card ≤ Fintype.card ι - (polynomialAgreementSet domain g G₀).card ∧
      ∀ z ∉ exceptional,
        polynomialAgreementSet (domain.trans ⟨φ, φ.injective⟩)
            (fun i ↦ φ (f i) + z * φ (g i)) (F₀.map φ + C z * G₀.map φ) =
          commonPolynomialAgreementSet domain f g F₀ G₀ := by
  classical
  obtain ⟨exceptional, hcard, hiff⟩ :=
    Finset.exists_card_le_forall_add_mul_eq_add_mul_iff Finset.univ
      (fun i ↦ φ (F₀.eval (domain i))) (fun i ↦ φ (G₀.eval (domain i)))
      (fun i ↦ φ (f i)) (fun i ↦ φ (g i))
  refine ⟨exceptional, hcard.trans_eq ?_, fun z hz ↦ ?_⟩
  · rw [← Finset.card_compl]
    congr 1
    ext i
    simp [φ.injective.eq_iff]
  · ext i
    have h := hiff z hz i (Finset.mem_univ i)
    simp only [φ.injective.eq_iff] at h
    simp [eval_map, Polynomial.eval₂_at_apply, h]

/-- **Exceptional challenges.** The count of
`exists_exceptional_graphLine_challenges_le_disagreement`, weakened to
`Fintype.card ι - #(commonPolynomialAgreementSet domain f g F₀ G₀)`: the common agreement set is
contained in the agreement set of `G₀` with `g`. -/
theorem exists_exceptional_graphLine_challenges
    {F E ι : Type*} [Field F] [Field E] [DecidableEq F] [DecidableEq E] [Fintype ι]
    (domain : ι ↪ F) (f g : ι → F) (F₀ G₀ : F[X]) (φ : F →+* E) :
    ∃ exceptional : Finset E,
      exceptional.card ≤
          Fintype.card ι - (commonPolynomialAgreementSet domain f g F₀ G₀).card ∧
      ∀ z ∉ exceptional,
        polynomialAgreementSet (domain.trans ⟨φ, φ.injective⟩)
            (fun i ↦ φ (f i) + z * φ (g i)) (F₀.map φ + C z * G₀.map φ) =
          commonPolynomialAgreementSet domain f g F₀ G₀ := by
  obtain ⟨exceptional, hcard, hagree⟩ :=
    exists_exceptional_graphLine_challenges_le_disagreement domain f g F₀ G₀ φ
  refine ⟨exceptional, hcard.trans (Nat.sub_le_sub_left (Finset.card_le_card ?_) _), hagree⟩
  intro i hi
  simp only [mem_commonPolynomialAgreementSet] at hi
  simpa using hi.2

/-- **Exceptional challenges from a sample.** If `F₀` and `G₀` agree with `f` and `g` on a sample
of `k` coordinates, at most `Fintype.card ι - k` challenges create agreement beyond the common
agreement set. The sample is contained in that set. -/
theorem exists_exceptional_graphLine_challenges_of_sample
    {F E ι : Type*} [Field F] [Field E] [DecidableEq F] [DecidableEq E] [Fintype ι] {k : ℕ}
    (domain : ι ↪ F) (f g : ι → F) (sample : Finset ι) (hsample : sample.card = k)
    (F₀ G₀ : F[X])
    (hfg : ∀ i ∈ sample, F₀.eval (domain i) = f i ∧ G₀.eval (domain i) = g i)
    (φ : F →+* E) :
    ∃ exceptional : Finset E, exceptional.card ≤ Fintype.card ι - k ∧
      ∀ z ∉ exceptional,
        polynomialAgreementSet (domain.trans ⟨φ, φ.injective⟩)
            (fun i ↦ φ (f i) + z * φ (g i)) (F₀.map φ + C z * G₀.map φ) =
          commonPolynomialAgreementSet domain f g F₀ G₀ := by
  obtain ⟨exceptional, hcard, hagree⟩ :=
    exists_exceptional_graphLine_challenges domain f g F₀ G₀ φ
  have hk : k ≤ (commonPolynomialAgreementSet domain f g F₀ G₀).card := by
    rw [← hsample]
    exact Finset.card_le_card fun i hi ↦ (mem_commonPolynomialAgreementSet ..).mpr (hfg i hi)
  exact ⟨exceptional, hcard.trans (Nat.sub_le_sub_left hk _), hagree⟩

/-- **Recognition and exceptional challenges for one pair.** The pair `F₀ G₀` of
`exists_graphLine_polynomials_of_sample` also satisfies the conclusion of
`exists_exceptional_graphLine_challenges_of_sample` over every extension. -/
theorem exists_graphLine_polynomials_and_exceptional_challenges
    {F ι : Type*} [Field F] [DecidableEq F] [Fintype ι] {k : ℕ} (domain : ι ↪ F)
    (f g : ι → F) (sample : Finset ι) (hsample : sample.card = k) :
    ∃ F₀ G₀ : F[X], F₀.degree < k ∧ G₀.degree < k ∧
      (∀ i ∈ sample, F₀.eval (domain i) = f i ∧ G₀.eval (domain i) = g i) ∧
      (∀ {E : Type*} [Field E] (φ : F →+* E) (z : E) (P : E[X]), P.degree < k →
        (∀ i ∈ sample,
          P.eval (domain.trans ⟨φ, φ.injective⟩ i) = φ (f i) + z * φ (g i)) →
        P = F₀.map φ + C z * G₀.map φ) ∧
      ∀ {E : Type*} [Field E] [DecidableEq E] (φ : F →+* E),
        ∃ exceptional : Finset E, exceptional.card ≤ Fintype.card ι - k ∧
          ∀ z ∉ exceptional,
            polynomialAgreementSet (domain.trans ⟨φ, φ.injective⟩)
                (fun i ↦ φ (f i) + z * φ (g i)) (F₀.map φ + C z * G₀.map φ) =
              commonPolynomialAgreementSet domain f g F₀ G₀ := by
  obtain ⟨F₀, G₀, hF₀, hG₀, hfg, hrecognize⟩ :=
    exists_graphLine_polynomials_of_sample domain f g sample hsample
  exact ⟨F₀, G₀, hF₀, hG₀, hfg, hrecognize, fun φ ↦
    exists_exceptional_graphLine_challenges_of_sample domain f g sample hsample F₀ G₀ hfg φ⟩

/-- **Frobenius graph-line recognition.** A sample of `k` coordinates determines `F₀ G₀` over `F`
of degree below `k` such that the following holds over every field `E` of exponential
characteristic `p`. Let `P` have degree below `p ^ e * k`, with Taylor coefficients at `center`
vanishing outside the multiples of `p ^ e`, and let `P` take the value
`φ (f i) + w ^ p ^ e * φ (g i)` at a `p ^ e`-th root `roots i` of `φ (domain i)` for every `i` in
the sample. Then `P` is `expand E (p ^ e)` of `F₀.map φ + C (w ^ p ^ e) * G₀.map φ`, and its
value at `center` is the graph-line value at `center ^ p ^ e`.

Only `k` coordinates are used, although `P` can have degree up to `p ^ e * k - 1`. The sparsity
hypothesis is needed, since without it `P` need not be a pullback. -/
theorem exists_frobeniusGraphLine_polynomials_of_sample {F ι : Type*} [Field F] {k : ℕ}
    (domain : ι ↪ F) (f g : ι → F) (sample : Finset ι) (hsample : sample.card = k) :
    ∃ F₀ G₀ : F[X], F₀.degree < k ∧ G₀.degree < k ∧
      (∀ i ∈ sample, F₀.eval (domain i) = f i ∧ G₀.eval (domain i) = g i) ∧
      ∀ {E : Type*} [Field E] (φ : F →+* E) (p e : ℕ) [ExpChar E p]
        (roots : ι → E) (center w : E) (P : E[X]),
        (∀ i ∈ sample, roots i ^ p ^ e = φ (domain i)) →
        P.degree < ↑(p ^ e * k) →
        (∀ j : ℕ, ¬p ^ e ∣ j → (taylor center P).coeff j = 0) →
        (∀ i ∈ sample, P.eval (roots i) = φ (f i) + w ^ p ^ e * φ (g i)) →
        P = expand E (p ^ e) (F₀.map φ + C (w ^ p ^ e) * G₀.map φ) ∧
          P.eval center = (F₀.map φ).eval (center ^ p ^ e) +
            w ^ p ^ e * (G₀.map φ).eval (center ^ p ^ e) := by
  classical
  subst hsample
  have hinj : Set.InjOn domain sample := domain.injective.injOn
  refine ⟨Lagrange.interpolate sample domain f, Lagrange.interpolate sample domain g,
    Lagrange.degree_interpolate_lt f hinj, Lagrange.degree_interpolate_lt g hinj,
    fun i hi ↦ ⟨Lagrange.eval_interpolate_at_node f hinj hi,
      Lagrange.eval_interpolate_at_node g hinj hi⟩, ?_⟩
  intro E _ φ p e _ roots center w P hroots hP hsparse heval
  have hPeq := Lagrange.eq_expand_map_interpolate_add_C_mul_of_eval_eq φ hinj f g (w ^ p ^ e)
    p e roots hroots center hP hsparse heval
  refine ⟨hPeq, ?_⟩
  rw [hPeq, expand_eval, eval_add, eval_mul, eval_C]

end ReedSolomon

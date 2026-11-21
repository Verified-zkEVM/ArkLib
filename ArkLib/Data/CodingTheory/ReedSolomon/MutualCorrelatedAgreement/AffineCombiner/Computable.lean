/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Coratger, Alexander Hicks
-/
module

public import ArkLib.Data.Probability.MaxEventProbability
public import CompPoly.Univariate.ToPoly.Degree
public import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.AffineCombiner.EqualDegree

/-!
# Computable combiner errors

The affine, scalar, and equal-degree combiner errors are suprema of counting probabilities in
`ENNReal`. This module computes each of them as an exact nonnegative rational. The evaluators
`ReedSolomon.affineMcaErrorRat`, `ReedSolomon.scalarMcaErrorRat`, and
`ReedSolomon.equalDegreeMcaErrorRat` enumerate the received word pairs and the challenges, and
take the largest fraction of exceptional challenges with `Probability.maxEventProbability`.

For a fixed candidate, the predicates in `ReedSolomon.Computable` have `Decidable` instances that
search the witnesses, and the evaluators search the candidates. Candidates and witnesses are
CompPoly polynomials in the finite subtypes `↥(CompPoly.CPolynomial.degreeLT k)`, whose enumeration
is `CompPoly.CPolynomial.instFintypeDegreeLT`. A degree bound `deg P ≤ d` corresponds to the
subtype `degreeLT (d + 1)`. In the affine and scalar combiners, the candidate `P` and the second
witness `G₀` determine the first witness `F₀ = P - L G₀`, where `L` is the affine or scalar
multiplier. Their searches therefore run over `G₀` only. The equal-degree search runs over both
witnesses.

The theorems `ReedSolomon.ofReal_affineMcaErrorRat`, `ReedSolomon.ofReal_scalarMcaErrorRat`, and
`ReedSolomon.ofReal_equalDegreeMcaErrorRat` prove that `ENNReal.ofReal` of the real cast of each
rational value is the semantic error.

Five executable definitions in `ReedSolomon.Computable` reuse the names of their semantic
counterparts in `ReedSolomon`: `affineMultiplier`, `combinedWord`, `IsAffineExceptional`,
`IsScalarExceptional`, and `IsEqualDegreeExceptional`. When both namespaces are open, refer to
them with the namespace prefix.

The semantic affine error follows Section 1.1 of [CWYZ26]. The semantic scalar error follows the
definition of `ε_sc` at the start of Section 6. The semantic equal-degree error uses the combiner
and witness conditions in (5.1) and (5.2). Theorem 5.1 bounds the error of that combiner.
The [paper page](../../../../../../docs/kb/papers/CWYZ26.md) records the correspondence.

## Computability

The definitions use no classical decision procedure and no sampler. Execution requires executable
field operations, a decidable equality on `F`, and `Fintype` instances that enumerate `F` and `ι`.
The evaluators obtain `DecidableEq ι` from `domain.injective.decidableEq` to enumerate words
`ι → F`. When unfolding an evaluator in a proof, use that equality instance or compare the
resulting word enumeration with the one built from the equality instance used in the proof.

## Cost

Let `q` be the field size, `n` the domain size, `d` the output degree bound, and `A` the agreement
threshold. Each evaluator visits all `q^(2n)` received word pairs. The affine and scalar
evaluators examine up to `q^(2n+2d+3)` combinations of a word pair, a challenge, a candidate, and
a witness. The equal-degree evaluator examines up to `q^(2n+3d+4)` combinations of a word pair, a
challenge, a candidate, and a witness pair. Charge one unit for each field operation, equality
test, natural-number operation, and evaluation of `domain`, as well as for each other primitive
step, such as an array access, a list-cell allocation, or a closure call. Suppose the `Fintype`
instances of `F` and `ι` list their elements in `O(q)` and `O(n)` steps, as those of `ZMod q`
and `Fin n` do. In this model, the running time is at most the corresponding number of
combinations times a factor that is polynomial in `n` and `d`.

Each search over candidates or witnesses stops at the first element that decides it, but it builds
its whole enumeration before the first test. Each evaluator skips the witness search for a
candidate with fewer than `A` agreements and rebuilds the witness enumeration for each candidate
that meets the threshold. In the equal-degree search, it also builds the enumeration of the
second witness again for each first witness.

## Main definitions

* `ReedSolomon.Computable.IsAffineExceptional`, `ReedSolomon.Computable.IsScalarExceptional`,
  and `ReedSolomon.Computable.IsEqualDegreeExceptional`: exceptional candidates with finite
  witness searches.
* `ReedSolomon.affineMcaErrorRat`, `ReedSolomon.scalarMcaErrorRat`, and
  `ReedSolomon.equalDegreeMcaErrorRat`: the exact errors in `ℚ≥0`.

## Main statements

* `ReedSolomon.Computable.exists_isAffineExceptional_iff`,
  `ReedSolomon.Computable.exists_isScalarExceptional_iff`, and
  `ReedSolomon.Computable.exists_isEqualDegreeExceptional_iff`: the finite searches detect
  exactly the semantic exceptional challenges.
* `ReedSolomon.ofReal_affineMcaErrorRat`, `ReedSolomon.ofReal_scalarMcaErrorRat`, and
  `ReedSolomon.ofReal_equalDegreeMcaErrorRat`: `ENNReal.ofReal` of the real cast of each rational
  value is its semantic error.

## References

* [Chiesa, A., Weissenberg, G., Yogev, E., and Zheng, K. Z.,
    *Affine combiners for Reed–Solomon proximity gaps*][CWYZ26]
-/

@[expose] public section

namespace ReedSolomon.Computable

open CompPoly Finset

variable {F ι : Type*} [Field F] [DecidableEq F] [Fintype ι]

/-! ### Words and lost positions -/

/-- The affine multiplier `α + β X` as a computable polynomial. -/
def affineMultiplier (α β : F) : CPolynomial F :=
  CPolynomial.C α + CPolynomial.C β * CPolynomial.X

/-- The word `i ↦ f i + L(domain i) g i` for a computable multiplier `L`. -/
def combinedWord (domain : ι ↪ F) (f g : ι → F) (L : CPolynomial F) : ι → F :=
  fun i ↦ f i + L.eval (domain i) * g i

/-- The agreement points of `P` with `word` at which at least one witness disagrees with its
received word: `F₀ ≠ f` or `G₀ ≠ g`. -/
def lostPositions (domain : ι ↪ F) (f g word : ι → F) (P F₀ G₀ : CPolynomial F) : Finset ι :=
  {i : ι | P.eval (domain i) = word i ∧
    (F₀.eval (domain i) ≠ f i ∨ G₀.eval (domain i) ≠ g i)}

/-- The computable affine multiplier converts to `ReedSolomon.affineMultiplier`. -/
@[simp]
theorem toPoly_affineMultiplier (α β : F) :
    (affineMultiplier α β).toPoly = ReedSolomon.affineMultiplier α β := by
  simp [affineMultiplier, ReedSolomon.affineMultiplier]

omit [DecidableEq F] [Fintype ι] in
/-- The computable combined word is the combined word of the converted multiplier. -/
theorem combinedWord_eq_combinedWord_toPoly (domain : ι ↪ F) (f g : ι → F) (L : CPolynomial F) :
    combinedWord domain f g L = ReedSolomon.combinedWord domain f g L.toPoly := by
  classical
  funext i
  simp [combinedWord, ReedSolomon.combinedWord, CPolynomial.eval_toPoly]

/-- The number of agreements of `P` with `word` is the size of the agreement set of the converted
polynomial. -/
theorem card_eval_eq_card_polynomialAgreementSet (domain : ι ↪ F) (word : ι → F)
    (P : CPolynomial F) :
    #{i : ι | P.eval (domain i) = word i} = (polynomialAgreementSet domain word P.toPoly).card := by
  simp [polynomialAgreementSet, CPolynomial.eval_toPoly]

/-- The lost positions are the agreement points of the converted candidate at which at least one
converted witness disagrees with its received word. -/
theorem lostPositions_eq_filter (domain : ι ↪ F) (f g word : ι → F)
    (P F₀ G₀ : CPolynomial F) :
    lostPositions domain f g word P F₀ G₀ =
      {i ∈ polynomialAgreementSet domain word P.toPoly |
        F₀.toPoly.eval (domain i) ≠ f i ∨ G₀.toPoly.eval (domain i) ≠ g i} := by
  ext i
  simp [lostPositions, polynomialAgreementSet, CPolynomial.eval_toPoly]

/-- The lost positions against the word `f + L g` are the agreement loss of the converted
polynomials. -/
theorem lostPositions_combinedWord (domain : ι ↪ F) (f g : ι → F) (L P F₀ G₀ : CPolynomial F) :
    lostPositions domain f g (combinedWord domain f g L) P F₀ G₀ =
      agreementLoss domain f g L.toPoly P.toPoly F₀.toPoly G₀.toPoly := by
  rw [lostPositions_eq_filter, combinedWord_eq_combinedWord_toPoly, agreementLoss]

omit [DecidableEq F] [Fintype ι] in
/-- A candidate in `degreeLT (d + 1)` converts to a polynomial of degree at most `d`. -/
private theorem degree_toPoly_le [BEq F] [LawfulBEq F] {d : ℕ}
    (P : ↥(CPolynomial.degreeLT (R := F) (d + 1))) :
    P.val.toPoly.degree ≤ d :=
  Polynomial.degree_lt_succ_iff.mp <|
    Polynomial.mem_degreeLT.mp (CPolynomial.degreeLT_toPoly.mp P.property)

omit [DecidableEq F] [Fintype ι] in
/-- Suppose that every polynomial that satisfies `Q` has degree at most `d`. Then some candidate in
`degreeLT (d + 1)` satisfies `Q` after conversion exactly when some polynomial satisfies `Q`. -/
private theorem exists_degreeLT_succ_toPoly_iff_of_degree_le [BEq F] [LawfulBEq F] (d : ℕ)
    (Q : Polynomial F → Prop) (hQ : ∀ p, Q p → p.degree ≤ d) :
    (∃ p : ↥(CPolynomial.degreeLT (R := F) (d + 1)), Q p.val.toPoly) ↔ ∃ p, Q p :=
  CPolynomial.exists_degreeLT_toPoly_iff_of_degree_lt (d + 1) Q fun p hp ↦
    Polynomial.degree_lt_succ_iff.mpr (hQ p hp)

/-- Suppose that `P` has degree at most `d`, and that `L G₀` has degree at most `d` for every `G₀`
that satisfies `S`. Then two statements are equivalent. The first says that no witness pair
`(F₀, G₀)` with `deg F₀ ≤ d` and `S G₀` is a loss witness for `P`. The second says that every
`G₀` that satisfies `S` loses more than `s` agreements together with `F₀ = P - L G₀`. -/
private theorem forall_not_isLossWitness_iff {domain : ι ↪ F} {f g : ι → F} {s d : ℕ}
    {L P : Polynomial F} {S : Polynomial F → Prop} (hP : P.degree ≤ d)
    (hL : ∀ G₀, S G₀ → (L * G₀).degree ≤ d) :
    (∀ F₀ G₀ : Polynomial F, F₀.degree ≤ d → S G₀ →
      ¬ ReedSolomon.IsLossWitness domain f g s L P F₀ G₀) ↔
      ∀ G₀, S G₀ → s < (agreementLoss domain f g L P (P - L * G₀) G₀).card := by
  constructor
  · intro h G₀ hG₀
    by_contra hs
    exact h (P - L * G₀) G₀ ((Polynomial.degree_sub_le _ _).trans (max_le hP (hL G₀ hG₀))) hG₀
      ⟨by ring, not_lt.mp hs⟩
  · rintro h F₀ G₀ - hG₀ ⟨hPeq, hs⟩
    have hF₀ : P - L * G₀ = F₀ := by rw [hPeq]; ring
    exact absurd hs (not_le.mpr (hF₀ ▸ h G₀ hG₀))

/-! ### Affine and scalar combiners -/

/-- `P` is exceptional for the affine challenge `(α, β)` at threshold `A` and loss `s`.

The subtype `degreeLT (d + 1)` gives `P` degree at most `d`. `P` agrees with `f + (α + β x) g`
on at least `A` points. For every `G₀ ∈ degreeLT d`, the witness pair `(P - (α + β X) G₀, G₀)`
loses more than `s` of these points. These pairs are exactly the decompositions
`P = F₀ + (α + β X) G₀` with `deg F₀ ≤ d` and `deg G₀ < d`.
`isAffineExceptional_iff` identifies this predicate with `ReedSolomon.IsAffineExceptional`. -/
def IsAffineExceptional (domain : ι ↪ F) (f g : ι → F) (d A s : ℕ) (α β : F)
    (P : ↥(CPolynomial.degreeLT (R := F) (d + 1))) : Prop :=
  A ≤ #{i : ι | P.val.eval (domain i) = combinedWord domain f g (affineMultiplier α β) i} ∧
    ∀ G₀ : ↥(CPolynomial.degreeLT (R := F) d),
      s < (lostPositions domain f g (combinedWord domain f g (affineMultiplier α β)) P.val
        (P.val - affineMultiplier α β * G₀.val) G₀.val).card

instance [Fintype F] (domain : ι ↪ F) (f g : ι → F) (d A s : ℕ) (α β : F)
    (P : ↥(CPolynomial.degreeLT (R := F) (d + 1))) :
    Decidable (IsAffineExceptional domain f g d A s α β P) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- The computable affine predicate holds exactly when `ReedSolomon.IsAffineExceptional` holds
for the converted candidate. -/
theorem isAffineExceptional_iff (domain : ι ↪ F) (f g : ι → F) (d A s : ℕ) (α β : F)
    (P : ↥(CPolynomial.degreeLT (R := F) (d + 1))) :
    IsAffineExceptional domain f g d A s α β P ↔
      ReedSolomon.IsAffineExceptional domain f g d A s α β P.val.toPoly := by
  rw [IsAffineExceptional, ReedSolomon.IsAffineExceptional,
    forall_not_isLossWitness_iff (degree_toPoly_le P) fun G₀ hG₀ ↦
      (Polynomial.degree_mul_le _ _).trans <|
        (add_le_add_left (degree_affineMultiplier_le α β) _).trans <|
          (add_comm (1 : WithBot ℕ) _).trans_le (Nat.WithBot.add_one_le_of_lt hG₀)]
  simp only [lostPositions_combinedWord, CPolynomial.toPoly_sub, CPolynomial.toPoly_mul,
    toPoly_affineMultiplier]
  simp only [card_eval_eq_card_polynomialAgreementSet, combinedWord_eq_combinedWord_toPoly,
    toPoly_affineMultiplier, degree_toPoly_le P, true_and]
  exact and_congr_right fun _ ↦ CPolynomial.forall_degreeLT_toPoly_iff d fun G₀ ↦
    s < (agreementLoss domain f g (ReedSolomon.affineMultiplier α β) P.val.toPoly
      (P.val.toPoly - ReedSolomon.affineMultiplier α β * G₀) G₀).card

/-- `P` is exceptional for the scalar challenge `α` at threshold `A` and loss `s`.

The subtype `degreeLT (d + 1)` gives `P` degree at most `d`. `P` agrees with `f + α g` on at
least `A` points. For every `G₀ ∈ degreeLT (d + 1)`, the witness pair `(P - α G₀, G₀)` loses
more than `s` of these points. These pairs are exactly the decompositions `P = F₀ + α G₀` with
both witness degrees at most `d`.
`isScalarExceptional_iff` identifies this predicate with `ReedSolomon.IsScalarExceptional`. -/
def IsScalarExceptional (domain : ι ↪ F) (f g : ι → F) (d A s : ℕ) (α : F)
    (P : ↥(CPolynomial.degreeLT (R := F) (d + 1))) : Prop :=
  A ≤ #{i : ι | P.val.eval (domain i) = combinedWord domain f g (CPolynomial.C α) i} ∧
    ∀ G₀ : ↥(CPolynomial.degreeLT (R := F) (d + 1)),
      s < (lostPositions domain f g (combinedWord domain f g (CPolynomial.C α)) P.val
        (P.val - CPolynomial.C α * G₀.val) G₀.val).card

instance [Fintype F] (domain : ι ↪ F) (f g : ι → F) (d A s : ℕ) (α : F)
    (P : ↥(CPolynomial.degreeLT (R := F) (d + 1))) :
    Decidable (IsScalarExceptional domain f g d A s α P) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- The computable scalar predicate holds exactly when `ReedSolomon.IsScalarExceptional` holds
for the converted candidate. -/
theorem isScalarExceptional_iff (domain : ι ↪ F) (f g : ι → F) (d A s : ℕ) (α : F)
    (P : ↥(CPolynomial.degreeLT (R := F) (d + 1))) :
    IsScalarExceptional domain f g d A s α P ↔
      ReedSolomon.IsScalarExceptional domain f g d A s α P.val.toPoly := by
  rw [IsScalarExceptional, ReedSolomon.IsScalarExceptional,
    forall_not_isLossWitness_iff (degree_toPoly_le P) fun G₀ hG₀ ↦ by
      rw [← Polynomial.smul_eq_C_mul]
      exact (Polynomial.degree_smul_le α G₀).trans hG₀]
  simp only [lostPositions_combinedWord, CPolynomial.toPoly_sub, CPolynomial.toPoly_mul,
    CPolynomial.C_toPoly]
  simp only [card_eval_eq_card_polynomialAgreementSet, combinedWord_eq_combinedWord_toPoly,
    CPolynomial.C_toPoly, degree_toPoly_le P, true_and]
  refine and_congr_right fun _ ↦ ?_
  simpa only [Polynomial.degree_lt_succ_iff] using
    CPolynomial.forall_degreeLT_toPoly_iff (d + 1) fun G₀ ↦
      s < (agreementLoss domain f g (Polynomial.C α) P.val.toPoly
        (P.val.toPoly - Polynomial.C α * G₀) G₀).card

/-- Some candidate of degree at most `d` satisfies the computable affine predicate exactly when
some polynomial satisfies `ReedSolomon.IsAffineExceptional`. -/
theorem exists_isAffineExceptional_iff (domain : ι ↪ F) (f g : ι → F) (d A s : ℕ) (α β : F) :
    (∃ P : ↥(CPolynomial.degreeLT (R := F) (d + 1)),
      IsAffineExceptional domain f g d A s α β P) ↔
      ∃ P, ReedSolomon.IsAffineExceptional domain f g d A s α β P := by
  simp_rw [isAffineExceptional_iff]
  exact exists_degreeLT_succ_toPoly_iff_of_degree_le d _ fun _ hP ↦ hP.1

/-- Some candidate of degree at most `d` satisfies the computable scalar predicate exactly when
some polynomial satisfies `ReedSolomon.IsScalarExceptional`. -/
theorem exists_isScalarExceptional_iff (domain : ι ↪ F) (f g : ι → F) (d A s : ℕ) (α : F) :
    (∃ P : ↥(CPolynomial.degreeLT (R := F) (d + 1)),
      IsScalarExceptional domain f g d A s α P) ↔
      ∃ P, ReedSolomon.IsScalarExceptional domain f g d A s α P := by
  simp_rw [isScalarExceptional_iff]
  exact exists_degreeLT_succ_toPoly_iff_of_degree_le d _ fun _ hP ↦ hP.1

/-! ### Equal-degree combiner -/

/-- `P` is exceptional for the equal-degree challenge `(θ, α, β)` at threshold `A` and loss `s`.

The subtype `degreeLT (d + 1)` gives `P` degree at most `d`. `P` agrees with
`g + (α + β x)(f + θ g)` on at least `A` points. No pair `F₀, G₀` in `degreeLT d` satisfies
`P = G₀ + (α + β X)(F₀ + θ G₀)` while losing at most `s` of these points.
`isEqualDegreeExceptional_iff` identifies this predicate with
`ReedSolomon.IsEqualDegreeExceptional`. -/
def IsEqualDegreeExceptional (domain : ι ↪ F) (f g : ι → F) (d A s : ℕ) (θ α β : F)
    (P : ↥(CPolynomial.degreeLT (R := F) (d + 1))) : Prop :=
  A ≤ #{i : ι | P.val.eval (domain i) = equalDegreeWord domain f g θ α β i} ∧
    ∀ F₀ G₀ : ↥(CPolynomial.degreeLT (R := F) d),
      P.val = G₀.val + affineMultiplier α β * (F₀.val + CPolynomial.C θ * G₀.val) →
        s < (lostPositions domain f g (equalDegreeWord domain f g θ α β)
          P.val F₀.val G₀.val).card

instance [Fintype F] (domain : ι ↪ F) (f g : ι → F) (d A s : ℕ) (θ α β : F)
    (P : ↥(CPolynomial.degreeLT (R := F) (d + 1))) :
    Decidable (IsEqualDegreeExceptional domain f g d A s θ α β P) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- The computable equal-degree predicate holds exactly when
`ReedSolomon.IsEqualDegreeExceptional` holds for the converted candidate. -/
theorem isEqualDegreeExceptional_iff (domain : ι ↪ F) (f g : ι → F) (d A s : ℕ) (θ α β : F)
    (P : ↥(CPolynomial.degreeLT (R := F) (d + 1))) :
    IsEqualDegreeExceptional domain f g d A s θ α β P ↔
      ReedSolomon.IsEqualDegreeExceptional domain f g d A s θ α β P.val.toPoly := by
  rw [IsEqualDegreeExceptional, ReedSolomon.IsEqualDegreeExceptional,
    card_eval_eq_card_polynomialAgreementSet]
  simp only [degree_toPoly_le P, true_and]
  have heq (F₀ G₀ : CPolynomial F) :
      (P.val = G₀ + affineMultiplier α β * (F₀ + CPolynomial.C θ * G₀)) ↔
      P.val.toPoly = G₀.toPoly + ReedSolomon.affineMultiplier α β *
        (F₀.toPoly + Polynomial.C θ * G₀.toPoly) := by
    simpa only [CPolynomial.toPoly_add, CPolynomial.toPoly_mul, toPoly_affineMultiplier,
      CPolynomial.C_toPoly] using
        (CPolynomial.toPoly_inj (p := P.val)
          (q := G₀ + affineMultiplier α β * (F₀ + CPolynomial.C θ * G₀))).symm
  simp_rw [heq, lostPositions_eq_filter]
  refine and_congr_right fun _ ↦ ?_
  exact CPolynomial.forall₂_degreeLT_toPoly_iff d d
    (fun F₀ G₀ ↦ P.val.toPoly = G₀ + ReedSolomon.affineMultiplier α β *
      (F₀ + Polynomial.C θ * G₀) →
        s < #{i ∈ polynomialAgreementSet domain (equalDegreeWord domain f g θ α β) P.val.toPoly |
          F₀.eval (domain i) ≠ f i ∨ G₀.eval (domain i) ≠ g i})

/-- Some candidate of degree at most `d` satisfies the computable equal-degree predicate exactly
when some polynomial satisfies `ReedSolomon.IsEqualDegreeExceptional`. -/
theorem exists_isEqualDegreeExceptional_iff (domain : ι ↪ F) (f g : ι → F) (d A s : ℕ)
    (θ α β : F) :
    (∃ P : ↥(CPolynomial.degreeLT (R := F) (d + 1)),
      IsEqualDegreeExceptional domain f g d A s θ α β P) ↔
      ∃ P, ReedSolomon.IsEqualDegreeExceptional domain f g d A s θ α β P := by
  simp_rw [isEqualDegreeExceptional_iff]
  exact exists_degreeLT_succ_toPoly_iff_of_degree_le d _ fun _ hP ↦ hP.1

end ReedSolomon.Computable

namespace ReedSolomon

open CompPoly Finset

variable {F ι : Type*} [Field F] [DecidableEq F] [Fintype F] [Fintype ι]

/-! ### Exact errors -/

/-- The exact affine-combiner error as a nonnegative rational: the largest fraction, over received
word pairs, of affine challenges `(α, β)` with an exceptional candidate.

The output degree bound is `d`, the agreement threshold is `A`, and the allowed loss is `s`. Witness
degrees are at most `d` and below `d`. `ofReal_affineMcaErrorRat` proves that `ENNReal.ofReal` of
the real cast of the value is `affineMcaError`. The module docstring explains how the evaluator
enumerates received words and gives the search cost. -/
def affineMcaErrorRat (domain : ι ↪ F) (d A s : ℕ) : ℚ≥0 :=
  letI : DecidableEq ι := domain.injective.decidableEq
  Probability.maxEventProbability fun (w : (ι → F) × (ι → F)) (c : F × F) ↦
    decide (∃ P : ↥(CPolynomial.degreeLT (R := F) (d + 1)),
      Computable.IsAffineExceptional domain w.1 w.2 d A s c.1 c.2 P)

/-- The exact scalar-combiner error as a nonnegative rational: the largest fraction, over received
word pairs, of scalar challenges `α` with an exceptional candidate.

The output and witness degree bound is `d`, the agreement threshold is `A`, and the allowed loss is
`s`. `ofReal_scalarMcaErrorRat` proves that `ENNReal.ofReal` of the real cast of the value is
`scalarMcaError`. The module docstring explains how the evaluator enumerates received words
and gives the search cost. -/
def scalarMcaErrorRat (domain : ι ↪ F) (d A s : ℕ) : ℚ≥0 :=
  letI : DecidableEq ι := domain.injective.decidableEq
  Probability.maxEventProbability fun (w : (ι → F) × (ι → F)) (α : F) ↦
    decide (∃ P : ↥(CPolynomial.degreeLT (R := F) (d + 1)),
      Computable.IsScalarExceptional domain w.1 w.2 d A s α P)

/-- The exact equal-degree combiner error as a nonnegative rational: the largest fraction, over
received word pairs, of challenges `(θ, α, β)` with an exceptional candidate.

The output degree bound is `d`, both witness degrees are below `d`, the agreement threshold is `A`,
and the allowed loss is `s`. `ofReal_equalDegreeMcaErrorRat` proves that `ENNReal.ofReal` of the
real cast of the value is `equalDegreeMcaError`. The module docstring explains how the evaluator
enumerates received words and gives the search cost. -/
def equalDegreeMcaErrorRat (domain : ι ↪ F) (d A s : ℕ) : ℚ≥0 :=
  letI : DecidableEq ι := domain.injective.decidableEq
  Probability.maxEventProbability fun (w : (ι → F) × (ι → F)) (c : F × F × F) ↦
    decide (∃ P : ↥(CPolynomial.degreeLT (R := F) (d + 1)),
      Computable.IsEqualDegreeExceptional domain w.1 w.2 d A s c.1 c.2.1 c.2.2 P)

/-- `ENNReal.ofReal` of the real cast of the computed affine error is the semantic error
`affineMcaError`. -/
theorem ofReal_affineMcaErrorRat (domain : ι ↪ F) (d A s : ℕ) :
    ENNReal.ofReal (affineMcaErrorRat domain d A s : ℝ) = affineMcaError domain d A s := by
  classical
  let : DecidableEq ι := domain.injective.decidableEq
  rw [affineMcaErrorRat, Probability.ofReal_maxEventProbability_eq_iSup_of_iff _
    (fun w c ↦ ∃ P, IsAffineExceptional domain w.1 w.2 d A s c.1 c.2 P) fun w c ↦
      decide_eq_true_iff.trans
        (Computable.exists_isAffineExceptional_iff domain w.1 w.2 d A s c.1 c.2)]
  simp only [affineMcaError, Fintype.card_prod, Nat.cast_mul, sq]

/-- `ENNReal.ofReal` of the real cast of the computed scalar error is the semantic error
`scalarMcaError`. -/
theorem ofReal_scalarMcaErrorRat (domain : ι ↪ F) (d A s : ℕ) :
    ENNReal.ofReal (scalarMcaErrorRat domain d A s : ℝ) = scalarMcaError domain d A s := by
  classical
  let : DecidableEq ι := domain.injective.decidableEq
  rw [scalarMcaErrorRat, Probability.ofReal_maxEventProbability_eq_iSup_of_iff _
    (fun w α ↦ ∃ P, IsScalarExceptional domain w.1 w.2 d A s α P) fun w α ↦
      decide_eq_true_iff.trans (Computable.exists_isScalarExceptional_iff domain w.1 w.2 d A s α)]
  rw [scalarMcaError]

/-- `ENNReal.ofReal` of the real cast of the computed equal-degree error is the semantic error
`equalDegreeMcaError`. -/
theorem ofReal_equalDegreeMcaErrorRat (domain : ι ↪ F) (d A s : ℕ) :
    ENNReal.ofReal (equalDegreeMcaErrorRat domain d A s : ℝ) =
      equalDegreeMcaError domain d A s := by
  classical
  let : DecidableEq ι := domain.injective.decidableEq
  rw [equalDegreeMcaErrorRat, Probability.ofReal_maxEventProbability_eq_iSup_of_iff _
    (fun w c ↦ ∃ P, IsEqualDegreeExceptional domain w.1 w.2 d A s c.1 c.2.1 c.2.2 P) fun w c ↦
      decide_eq_true_iff.trans
        (Computable.exists_isEqualDegreeExceptional_iff domain w.1 w.2 d A s c.1 c.2.1 c.2.2)]
  simp only [equalDegreeMcaError, Fintype.card_prod, Nat.cast_mul, pow_succ, pow_zero, one_mul,
    mul_assoc]

end ReedSolomon

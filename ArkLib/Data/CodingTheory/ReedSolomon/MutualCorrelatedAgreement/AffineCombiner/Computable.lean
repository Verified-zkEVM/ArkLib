/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Coratger, Alexander Hicks
-/
module

public import ArkLib.Data.Probability.MaxEventProbability
public import ArkLib.ToCompPoly.Univariate.DegreeLT
public import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.AffineCombiner.EqualDegree
public import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.AffineCombiner.Probability

/-!
# Computable combiner errors

The affine, scalar, and equal-degree combiner errors are suprema of counting probabilities in
`ENNReal`. This module computes each of them as an exact nonnegative rational. The evaluators
`ReedSolomon.affineMcaErrorRat`, `ReedSolomon.scalarMcaErrorRat`, and
`ReedSolomon.equalDegreeMcaErrorRat` enumerate the received word pairs and the challenges, and
take the largest fraction of exceptional challenges with `Probability.maxEventProbability`.

The evaluator enumerates candidates of degree at most `d` in `degreeLT (d + 1)`.
Finite polynomial searches use `CompPoly.CPolynomial.instFintypeDegreeLT` to enumerate
`degreeLT k` at the required bound `k`. The affine search enumerates the second witness `G₀`
in `degreeLT d`, and the scalar search enumerates it in `degreeLT (d + 1)`.
Both recover `F₀ = P - L G₀` from the candidate `P` and multiplier `L`.

An equal-degree witness pair satisfies `P = G₀ + L W`, where `L` is the affine multiplier and
`W = F₀ + θ G₀`. The search enumerates `W` of degree below `d` and computes `G₀ = P - L W`.
It tests the agreement loss of `(W - θ G₀, G₀)` only when `G₀` also has degree below `d`.

The theorems `ReedSolomon.ofReal_affineMcaErrorRat`, `ReedSolomon.ofReal_scalarMcaErrorRat`, and
`ReedSolomon.ofReal_equalDegreeMcaErrorRat` prove that `ENNReal.ofReal` of the real cast of each
rational value is the semantic error.
`ReedSolomon.mcaError_affineLine_eq_ofReal_scalarMcaErrorRat` computes the affine-line
`CoreDefinitions.mcaError` of `code domain (d + 1)` from the scalar error at loss zero.

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
evaluators examine up to `q^(2n+2d+3)` tuples of a word pair, a challenge, a candidate, and a
second witness. The equal-degree evaluator examines up to `q^(2n+2d+4)` tuples with `W` in place
of the second witness. Charge one unit for each field operation, equality test, natural-number
operation, and evaluation of `domain`. Also charge one unit for each other primitive step, such
as an array access, a list-cell allocation, or a closure call. Suppose the `Fintype`
instances of `F` and `ι` list their elements in `O(q)` and `O(n)` steps, as those of `ZMod q`
and `Fin n` do. In this model, the running time is at most the corresponding number of
tuples times a factor that is polynomial in `n` and `d`.

Each finite search builds its enumeration before it tests any element and stops at the first
element that decides it. Each evaluator skips the inner search for candidates with fewer than
`A` agreements. For each candidate that meets the threshold, it builds the enumeration of
second witnesses or of `W`.

## Main definitions

* `ReedSolomon.Computable.IsAffineExceptional`, `ReedSolomon.Computable.IsScalarExceptional`,
  and `ReedSolomon.Computable.IsEqualDegreeExceptional`: exceptional candidates with finite
  witness searches.
* `ReedSolomon.affineMcaErrorRat`, `ReedSolomon.scalarMcaErrorRat`, and
  `ReedSolomon.equalDegreeMcaErrorRat`: the exact errors in `ℚ≥0`.

## Main statements

* `ReedSolomon.Computable.forall_eq_equalDegreePolynomial_iff`: the correspondence between
  bounded witness pairs and the combinations used in the equal-degree search.
* `ReedSolomon.Computable.exists_isAffineExceptional_iff`,
  `ReedSolomon.Computable.exists_isScalarExceptional_iff`, and
  `ReedSolomon.Computable.exists_isEqualDegreeExceptional_iff`: the finite searches detect
  exactly the semantic exceptional challenges.
* `ReedSolomon.ofReal_affineMcaErrorRat`, `ReedSolomon.ofReal_scalarMcaErrorRat`, and
  `ReedSolomon.ofReal_equalDegreeMcaErrorRat`: `ENNReal.ofReal` of the real cast of each rational
  value is its semantic error.
* `ReedSolomon.mcaError_affineLine_eq_ofReal_scalarMcaErrorRat`: the affine-line MCA error at
  radius `δ` is the computed scalar error at loss zero and threshold `⌈n(1 - δ)⌉₊`.

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
    forall_not_isLossWitness_iff (CPolynomial.degree_toPoly_le P) fun G₀ hG₀ ↦
      (Polynomial.degree_mul_le _ _).trans <|
        (add_le_add_left (degree_affineMultiplier_le α β) _).trans <|
          (add_comm (1 : WithBot ℕ) _).trans_le (Nat.WithBot.add_one_le_of_lt hG₀)]
  simp only [lostPositions_combinedWord, CPolynomial.toPoly_sub, CPolynomial.toPoly_mul,
    toPoly_affineMultiplier]
  simp only [card_eval_eq_card_polynomialAgreementSet, combinedWord_eq_combinedWord_toPoly,
    toPoly_affineMultiplier, CPolynomial.degree_toPoly_le P, true_and]
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
    forall_not_isLossWitness_iff (CPolynomial.degree_toPoly_le P) fun G₀ hG₀ ↦ by
      rw [← Polynomial.smul_eq_C_mul]
      exact (Polynomial.degree_smul_le α G₀).trans hG₀]
  simp only [lostPositions_combinedWord, CPolynomial.toPoly_sub, CPolynomial.toPoly_mul,
    CPolynomial.C_toPoly]
  simp only [card_eval_eq_card_polynomialAgreementSet, combinedWord_eq_combinedWord_toPoly,
    CPolynomial.C_toPoly, CPolynomial.degree_toPoly_le P, true_and]
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
  exact CPolynomial.exists_degreeLT_succ_toPoly_iff_of_degree_le d _ fun _ hP ↦ hP.1

/-- Some candidate of degree at most `d` satisfies the computable scalar predicate exactly when
some polynomial satisfies `ReedSolomon.IsScalarExceptional`. -/
theorem exists_isScalarExceptional_iff (domain : ι ↪ F) (f g : ι → F) (d A s : ℕ) (α : F) :
    (∃ P : ↥(CPolynomial.degreeLT (R := F) (d + 1)),
      IsScalarExceptional domain f g d A s α P) ↔
      ∃ P, ReedSolomon.IsScalarExceptional domain f g d A s α P := by
  simp_rw [isScalarExceptional_iff]
  exact CPolynomial.exists_degreeLT_succ_toPoly_iff_of_degree_le d _ fun _ hP ↦ hP.1

/-! ### Equal-degree combiner -/

/-- Combine two polynomials at the equal-degree challenge `(θ, α, β)`. -/
def equalDegreePolynomial (θ α β : F) (U V : CPolynomial F) : CPolynomial F :=
  V + affineMultiplier α β * (U + CPolynomial.C θ * V)

/-- Conversion preserves the equal-degree combination. -/
@[simp]
theorem toPoly_equalDegreePolynomial (θ α β : F) (U V : CPolynomial F) :
    (equalDegreePolynomial θ α β U V).toPoly =
      V.toPoly + ReedSolomon.affineMultiplier α β * (U.toPoly + Polynomial.C θ * V.toPoly) := by
  simp [equalDegreePolynomial, CPolynomial.toPoly_add, CPolynomial.toPoly_mul]

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
      P.val = equalDegreePolynomial θ α β F₀.val G₀.val →
        s < (lostPositions domain f g (equalDegreeWord domain f g θ α β)
          P.val F₀.val G₀.val).card

/-- Let `Q` be a predicate on pairs of polynomials. Consider the pairs `(F₀, G₀)` in `degreeLT d`
that satisfy `P = G₀ + (α + β X)(F₀ + θ G₀)`. All these pairs satisfy `Q` exactly when
`Q (W - θ V) V` holds for every `W ∈ degreeLT d` with `V = P - (α + β X) W` of degree below `d`.

The pairs and these `W` correspond through `(F₀, G₀) ↦ F₀ + θ G₀`. -/
theorem forall_eq_equalDegreePolynomial_iff (P : CPolynomial F) (θ α β : F) (d : ℕ)
    (Q : CPolynomial F → CPolynomial F → Prop) :
    (∀ F₀ G₀ : ↥(CPolynomial.degreeLT (R := F) d),
      P = equalDegreePolynomial θ α β F₀.val G₀.val → Q F₀.val G₀.val) ↔
      ∀ W : ↥(CPolynomial.degreeLT (R := F) d),
        (P - affineMultiplier α β * W.val).degree < d →
          Q (W.val - CPolynomial.C θ * (P - affineMultiplier α β * W.val))
            (P - affineMultiplier α β * W.val) := by
  have hC (G : CPolynomial F) : (CPolynomial.C θ * G).degree ≤ G.degree :=
    (CPolynomial.degree_mul_le _ _).trans <|
      (add_le_add_left (CPolynomial.degree_C_le θ) G.degree).trans_eq (zero_add _)
  simp only [equalDegreePolynomial]
  constructor
  · intro h W hG
    refine h ⟨_, CPolynomial.mem_degreeLT.mpr <| (CPolynomial.degree_sub_le _ _).trans_lt
      (max_lt (CPolynomial.mem_degreeLT.mp W.property) ((hC _).trans_lt hG))⟩
      ⟨_, CPolynomial.mem_degreeLT.mpr hG⟩ (by ring)
  · intro h F₀ G₀ hP
    let W := F₀.val + CPolynomial.C θ * G₀.val
    have hW : W ∈ CPolynomial.degreeLT d :=
      CPolynomial.mem_degreeLT.mpr <| (CPolynomial.degree_add_le _ _).trans_lt
        (max_lt (CPolynomial.mem_degreeLT.mp F₀.property)
          ((hC G₀.val).trans_lt (CPolynomial.mem_degreeLT.mp G₀.property)))
    have hG : P - affineMultiplier α β * W = G₀.val := by rw [hP]; ring
    simpa only [hG, W, add_sub_cancel_right] using
      h ⟨W, hW⟩ (hG ▸ CPolynomial.mem_degreeLT.mp G₀.property)

/-- The decision procedure searches the combinations `W = F₀ + θ G₀ ∈ degreeLT d`. Each
`W` determines the witnesses `G₀ = P - (α + β X) W` and `F₀ = W - θ G₀`. The search skips `W` if
`G₀` has degree at least `d`. -/
instance [Fintype F] (domain : ι ↪ F) (f g : ι → F) (d A s : ℕ) (θ α β : F)
    (P : ↥(CPolynomial.degreeLT (R := F) (d + 1))) :
    Decidable (IsEqualDegreeExceptional domain f g d A s θ α β P) :=
  let word := equalDegreeWord domain f g θ α β
  decidable_of_iff
    (A ≤ #{i : ι | P.val.eval (domain i) = word i} ∧
      ∀ W : ↥(CPolynomial.degreeLT (R := F) d),
        let G₀ := P.val - affineMultiplier α β * W.val
        G₀.degree < d → s < (lostPositions domain f g word P.val
          (W.val - CPolynomial.C θ * G₀) G₀).card)
    (and_congr_right fun _ ↦ (forall_eq_equalDegreePolynomial_iff P.val θ α β d
      fun F₀ G₀ ↦ s < (lostPositions domain f g word P.val F₀ G₀).card).symm)

/-- The computable equal-degree predicate holds exactly when
`ReedSolomon.IsEqualDegreeExceptional` holds for the converted candidate. -/
theorem isEqualDegreeExceptional_iff (domain : ι ↪ F) (f g : ι → F) (d A s : ℕ) (θ α β : F)
    (P : ↥(CPolynomial.degreeLT (R := F) (d + 1))) :
    IsEqualDegreeExceptional domain f g d A s θ α β P ↔
      ReedSolomon.IsEqualDegreeExceptional domain f g d A s θ α β P.val.toPoly := by
  rw [IsEqualDegreeExceptional, ReedSolomon.IsEqualDegreeExceptional,
    card_eval_eq_card_polynomialAgreementSet]
  simp only [CPolynomial.degree_toPoly_le P, true_and]
  simp_rw [← CPolynomial.toPoly_inj (p := P.val), toPoly_equalDegreePolynomial,
    lostPositions_eq_filter]
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
  exact CPolynomial.exists_degreeLT_succ_toPoly_iff_of_degree_le d _ fun _ hP ↦ hP.1

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

/-- The affine-line MCA error of `code domain (d + 1)` at radius `δ` is `ENNReal.ofReal` of the
real cast of the computed scalar error at loss zero and threshold `A = ⌈n(1 - δ)⌉₊`,
where `n = |ι|`. -/
theorem mcaError_affineLine_eq_ofReal_scalarMcaErrorRat {F ι : Type} [Field F] [DecidableEq F]
    [Fintype F] [Fintype ι] [SampleableType F] (domain : ι ↪ F) (d A : ℕ) (δ : ℝ)
    (hδ : ⌈(Fintype.card ι : ℝ) * (1 - δ)⌉₊ = A) :
    CoreDefinitions.mcaError (CoreDefinitions.AffineLineGenerator F) (code domain (d + 1)) δ =
      ENNReal.ofReal (scalarMcaErrorRat domain d A 0 : ℝ) := by
  rw [ofReal_scalarMcaErrorRat, scalarMcaError_zero_eq_mcaError domain d A δ hδ]

end ReedSolomon

/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Coratger, Alexander Hicks
-/

import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.AffineCombiner.Computable
import Mathlib.Algebra.Field.ZMod

/-! # Acceptance tests for the exact combiner errors -/

open ReedSolomon

private def emptyDomain : Fin 0 ↪ ZMod 2 := ⟨Fin.elim0, fun a ↦ Fin.elim0 a⟩

private def binaryDomain : ZMod 2 ↪ ZMod 2 := (Equiv.refl _).toEmbedding

private def ternaryTwo : Fin 2 ↪ ZMod 3 := ⟨fun i ↦ (i.val : ZMod 3), by decide⟩

private def ternaryDomain : ZMod 3 ↪ ZMod 3 := (Equiv.refl _).toEmbedding

/-! ### Affine combiner -/

-- With loss zero, take `g` nonconstant. The interpolant of the combined word meets `A = 2`, and
-- no constant second witness agrees with `g` at both points. Every challenge is exceptional.
/-- info: true -/
#guard_msgs in
#eval affineMcaErrorRat binaryDomain 1 2 0 == 1

-- With one point of allowed loss, take `G₀ = C (g 0)` and `F₀ = P - (α + β X) G₀`. They agree
-- with their received words at the domain point `0`, so the loss is at most one.
/-- info: true -/
#guard_msgs in
#eval affineMcaErrorRat binaryDomain 1 2 1 == 0

-- An agreement threshold above the domain size excludes every candidate.
/-- info: true -/
#guard_msgs in
#eval affineMcaErrorRat binaryDomain 0 3 0 == 0

-- With `d = 0` the second witness `G₀` is zero. For `f = 0` and `g = 1`, the constant candidate
-- `C α` agrees with the combined word at the domain point `0`. Its witnesses are `F₀ = C α` and
-- `G₀ = 0`, and `G₀` differs from `g` at that point, so the point is lost. Hence every challenge is
-- exceptional.
/-- info: true -/
#guard_msgs in
#eval affineMcaErrorRat binaryDomain 0 0 0 == 1

-- With `d = 0` a challenge is exceptional when the combined word is constant, but `f` is not
-- constant or `g` is not zero. For `g ≠ 0` one linear equation in `(α, β)` defines these
-- challenges, so three of the nine challenges over `ZMod 3` are exceptional.
/-- info: true -/
#guard_msgs in
#eval affineMcaErrorRat ternaryTwo 0 2 0 == 1 / 3

-- On the empty domain every decomposition has loss zero, and `F₀ = P` with `G₀ = 0` decomposes
-- every candidate. Hence no challenge is exceptional.
/-- info: true -/
#guard_msgs in
#eval affineMcaErrorRat emptyDomain 1 0 0 == 0

/-! ### Scalar combiner -/

-- With `d = 0` a challenge `α` is exceptional when `f + α g` is constant, but `f` or `g` is not
-- constant. A nonconstant `g` admits exactly one such challenge.
/-- info: true -/
#guard_msgs in
#eval scalarMcaErrorRat binaryDomain 0 2 0 == 1 / 2

-- Over `ZMod 3`, the same argument gives one of the three challenges.
/-- info: true -/
#guard_msgs in
#eval scalarMcaErrorRat ternaryTwo 0 2 0 == 1 / 3

-- With one point of allowed loss, take both constant witnesses from the received words at the
-- point `0`. Their scalar combination is the constant candidate, so the loss is at most one.
/-- info: true -/
#guard_msgs in
#eval scalarMcaErrorRat ternaryTwo 0 2 1 == 0

-- With `d = 0` and `A = 3` on the three points of `ZMod 3`, a candidate that meets the threshold
-- is the constant value of `f + α g`, so `f + α g` is constant. If two challenges `α ≠ α'` make it
-- constant, then `(α - α') g` is constant, so both words are constant. Their constant
-- interpolants decompose the candidate with loss zero. Hence at most one of the three challenges is
-- exceptional. For `f = -x`, `g = x`, and `α = 1`, the candidate is zero. Every decomposition has
-- a constant `G₀`, which differs from `g` at two points. Its loss is at least two, above `s = 1`.
/-- info: true -/
#guard_msgs in
#eval scalarMcaErrorRat ternaryDomain 0 3 1 == 1 / 3

-- On the empty domain every decomposition has loss zero, and `F₀ = P` with `G₀ = 0` decomposes
-- every candidate. Hence no challenge is exceptional.
/-- info: true -/
#guard_msgs in
#eval scalarMcaErrorRat emptyDomain 0 0 0 == 0

-- With `d = 1` on two points, the interpolants `F₀` of `f` and `G₀` of `g` have degree at most one.
-- Every candidate that agrees with `f + α g` at both points equals `F₀ + α G₀`, with loss zero.
-- Hence no challenge is exceptional.
/-- info: true -/
#guard_msgs in
#eval scalarMcaErrorRat ternaryTwo 1 2 0 == 0

-- With `A = 3` above the domain size `n = 2`, no candidate has `A` agreements. Hence no challenge
-- is exceptional.
/-- info: true -/
#guard_msgs in
#eval scalarMcaErrorRat binaryDomain 0 3 0 == 0

/-! ### Equal-degree combiner -/

-- With loss `s = 2` on two points, every decomposition has small enough loss, so only the
-- polynomial identity can fail. A candidate that meets `A = 2` is the interpolant `P₀ + P₁ X` of
-- the word, and both witnesses are constants. Put `W = F₀ + θ G₀`. For `β ≠ 0`, the witnesses
-- with `W = P₁ / β`, `G₀ = P₀ - α W`, and `F₀ = W - θ G₀` decompose the candidate. For `β = 0`,
-- `G₀ + α W` is constant, and `G₀ = c` with `F₀ = -θ c` gives every constant `c`. So the identity
-- fails exactly when the word takes two values.
-- At `β = 0` the word is `(1 + α θ) g + α f`, that is `g`, `g`, `f + g`, and `f` for the pairs
-- `(θ, α) = (0, 0), (1, 0), (0, 1), (1, 1)`. Over `ZMod 2` on two points, `f`, `g`, and `f + g`
-- cannot all be nonconstant, so at most three of these four words are nonconstant. The pair
-- `f = g = x` makes three of them nonconstant, which gives three of the eight challenges.
/-- info: true -/
#guard_msgs in
#eval equalDegreeMcaErrorRat binaryDomain 1 2 2 == 3 / 8

-- Over `ZMod 3`, the argument of the previous case shows that a challenge is exceptional exactly
-- when `β = 0` and the word takes two values. At `β = 0` the word is `(1 + α θ) g + α f`. For
-- `α = 0` it is `g` for each of the three values of `θ`. For `α ≠ 0` it is `α (f + c g)` with
-- `c = θ + α⁻¹`, and `c` runs over `ZMod 3` with `θ`. If `g` is nonconstant, exactly one `c` makes
-- `f + c g` constant, so seven of the nine words are nonconstant. If `g` is constant, at most six
-- are. This gives seven of the 27 challenges.
/-- info: true -/
#guard_msgs in
#eval equalDegreeMcaErrorRat ternaryTwo 1 2 2 == 7 / 27

/-- The equal-degree decision by pair enumeration at `d = 1` with `f = 0`, `g = x`, and
`A = s = 0` on the two-point ternary domain. -/
private def equalDegreePairSearch (θ α β : ZMod 3)
    (P : ↥(CompPoly.CPolynomial.degreeLT (R := ZMod 3) 2)) : Bool :=
  @decide (Computable.IsEqualDegreeExceptional ternaryTwo 0 ![0, 1] 1 0 0 θ α β P)
    (by unfold Computable.IsEqualDegreeExceptional; infer_instance)

-- With `f = 0` and `g = x` on the two-point domain, check that both compiled searches agree
-- for every challenge and candidate of degree at most one. The threshold and loss are both zero.
/-- info: true -/
#guard_msgs in
#eval decide (∀ c : ZMod 3 × ZMod 3 × ZMod 3,
    ∀ P : ↥(CompPoly.CPolynomial.degreeLT (R := ZMod 3) 2),
      decide (Computable.IsEqualDegreeExceptional ternaryTwo 0 ![0, 1] 1 0 0 c.1 c.2.1 c.2.2 P) =
        equalDegreePairSearch c.1 c.2.1 c.2.2 P)

-- Adding `X² + X` to the linear interpolant gives a quadratic candidate for every combined
-- word. For `β = 0`, witnesses of degree at most one cannot produce that candidate.
-- For `β ≠ 0` and any candidate `P` meeting `A = 2`, choose a linear polynomial `W` with
-- constant term `f 0 + θ * g 0` and linear coefficient equal to the quadratic coefficient of
-- `P` divided by `β`. Then `G₀ = P - (α + β X) W`
-- and `F₀ = W - θ G₀` have degree at most one and agree with their words at `0`. Exactly half
-- the challenges have `β = 0`, so the error is `1 / 2`.
/-- info: true -/
#guard_msgs in
#eval equalDegreeMcaErrorRat binaryDomain 2 2 1 == 1 / 2

-- The argument of the previous case applies at `d = 5`. Adding `X⁵ + X` to the linear interpolant
-- gives a candidate of degree five for every combined word. For `β = 0`, witnesses of degree at
-- most four cannot produce that candidate. For `β ≠ 0` and any candidate `P` meeting `A = 2`,
-- choose `W` of degree at most four with constant term `f 0 + θ * g 0`. Set its `X⁴`
-- coefficient to the `X⁵` coefficient of `P`
-- divided by `β`. The witnesses `G₀ = P - (α + β X) W` and `F₀ = W - θ G₀` have degree at most
-- four and agree with their words at `0`. Exactly the challenges with `β = 0` have exceptional
-- candidates, so the error is `1 / 2`.
/-- info: true -/
#guard_msgs in
#eval equalDegreeMcaErrorRat binaryDomain 5 2 1 == 1 / 2

-- On the empty domain, only the polynomial identity can fail. It fails exactly when `β = 0`,
-- because a constant multiplier cannot produce the candidate `X`.
/-- info: true -/
#guard_msgs in
#eval equalDegreeMcaErrorRat emptyDomain 1 0 0 == 1 / 2

-- With `A = 0` every candidate meets the threshold. With `d = 0` both witnesses have degree below
-- zero, so they are zero and decompose only the zero candidate. Every nonzero constant candidate
-- is exceptional for every challenge.
/-- info: true -/
#guard_msgs in
#eval equalDegreeMcaErrorRat binaryDomain 0 0 0 == 1

-- At `d = 0` both witnesses are zero. For `f = 0` and `g = 1`, the combined word is
-- constant exactly when `θ * β = 0`. All six constant cases are exceptional at loss zero.
-- For any nonzero word pair there is a `θ` for which some challenge gives a nonconstant word.
-- At that `θ`, the difference between the two values is affine in `(α, β)`, so at most two
-- pairs give a constant word. The zero word pair has no exceptional challenges.
/-- info: true -/
#guard_msgs in
#eval equalDegreeMcaErrorRat binaryDomain 0 2 0 == 3 / 4

-- An agreement threshold above the domain size excludes every candidate.
/-- info: true -/
#guard_msgs in
#eval equalDegreeMcaErrorRat binaryDomain 1 3 0 == 0

/-! ### Bridges to the semantic errors -/

/-- info: 'ReedSolomon.ofReal_affineMcaErrorRat' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReedSolomon.ofReal_affineMcaErrorRat

/-- info: 'ReedSolomon.ofReal_scalarMcaErrorRat' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReedSolomon.ofReal_scalarMcaErrorRat

/-- info: 'ReedSolomon.ofReal_equalDegreeMcaErrorRat' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReedSolomon.ofReal_equalDegreeMcaErrorRat

/-- info: 'ReedSolomon.mcaError_affineLine_eq_ofReal_scalarMcaErrorRat' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReedSolomon.mcaError_affineLine_eq_ofReal_scalarMcaErrorRat

/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.Ordinary.FactorBudget
public import ArkLib.ToMathlib.MvPolynomial.RadicalSplit

/-!
# Combining ordinary factor exceptional sets

The ordinary mutual correlated agreement argument splits the interpolating polynomial `Q` into
its content radical, which does not involve the root variable `X i`, and its distinct irreducible
factors of positive degree in `X i` (`ArkLib.ToMathlib.MvPolynomial.RadicalSplit`). Each factor
has a set of exceptional challenges bounded by its per-factor charge, and the content radical
vanishes on a set bounded by its height. This file unions these sets and charges the union to the
budget of the whole polynomial, for both per-factor charges of
`ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.Ordinary.FactorBudget`.

Both theorems are `MvPolynomial.exists_exceptional_of_factor_exceptional` followed by a summation
bound: the root degrees of the factors add up to at most the root degree of `Q`
(`MvPolynomial.sum_degreeOf_positiveDegreeFactorClasses_le`), and the heights are assumed to add up
to at most `H`.

## Main statements

* `ReedSolomon.exists_exceptional_ordinaryFactorAssembly`: the combination for the coarse charge
  `ordinaryFactorRaw`.
* `ReedSolomon.exists_exceptional_ordinaryUnifiedPowerFactorAssembly`: the combination for the
  free-retention charge `ordinaryUnifiedPowerFactorRawAt`.

## References

`exists_exceptional_ordinaryFactorAssembly` is ported from
`Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/Ordinary/Factors/FactorAssembly.lean` at
ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`, under the same name. The source
assumed a coefficient field `F`, polynomials in `MvPolynomial (Option σ) F` with root variable
`none`, and ring homomorphisms into a domain. Here the coefficients form any unique factorization
domain, the root variable is any `i : σ`, and the evaluations are
monoid-with-zero homomorphisms into any commutative monoid with zero without zero divisors. The
source's `ordinaryContent`, `ordinaryRootFactorClasses` and `ordinaryFactorRepresentative` are
`MvPolynomial.radicalContent i`, `MvPolynomial.positiveDegreeFactorClasses i` and
`Associates.rep`. The source proof is split into the budget-independent
`MvPolynomial.exists_exceptional_of_factor_exceptional` and `ordinaryFactorRaw_sum_le`.

`exists_exceptional_ordinaryUnifiedPowerFactorAssembly` is new. The source repeated the same
union argument inline for the free-retention charge in
`Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/Ordinary/UnifiedCurve.lean`; that file is
not ported yet.
-/

@[expose] public section

open scoped BigOperators
open MvPolynomial

namespace ReedSolomon

variable {R σ W V K Fn : Type*} [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R]
  [CommMonoidWithZero K] [NoZeroDivisors K] [FunLike Fn (MvPolynomial σ R) K]
  [MonoidWithZeroHomClass Fn (MvPolynomial σ R) K]

/-- Combine the content exception with the exceptions of the distinct positive-root-degree
factors, charging the coarse per-factor charge `ordinaryFactorRaw`. If the content radical
vanishes only for challenges in a set of size at most its height, and each factor `c` has a set of
size at most `ordinaryFactorRaw theta n D (degreeOf i c.rep) (height c.rep)` outside which its
zeros are good, then the zeros of `Q` are good outside a set of size at most
`ordinaryFactorRaw theta n D mu H`.

The hypothesis `Q ≠ 0` is needed as in `MvPolynomial.exists_exceptional_of_factor_exceptional`.
The hypotheses `0 ≤ theta` and `1 ≤ mu` are needed as in `ordinaryFactorRaw_sum_le`. -/
theorem exists_exceptional_ordinaryFactorAssembly
    (i : σ) (Q : MvPolynomial σ R) (hQ : Q ≠ 0)
    (ev : W → V → Fn) (Good : W → V → Prop) (height : MvPolynomial σ R → ℕ)
    (theta : ℚ) (n D mu H : ℕ) (htheta : 0 ≤ theta) (hmu : 1 ≤ mu)
    (hroot : degreeOf i Q ≤ mu)
    (hheight : height (radicalContent i Q) +
      ∑ c ∈ positiveDegreeFactorClasses i Q, height c.rep ≤ H)
    (hcontent : ∃ ex : Finset W, ex.card ≤ height (radicalContent i Q) ∧
      ∀ w ∉ ex, ∀ v, ev w v (radicalContent i Q) ≠ 0)
    (hfactors : ∀ c ∈ positiveDegreeFactorClasses i Q, ∃ ex : Finset W,
      (ex.card : ℚ) ≤ ordinaryFactorRaw theta n D (degreeOf i c.rep) (height c.rep) ∧
      ∀ w ∉ ex, ∀ v, ev w v c.rep = 0 → Good w v) :
    ∃ ex : Finset W, (ex.card : ℚ) ≤ ordinaryFactorRaw theta n D mu H ∧
      ∀ w ∉ ex, ∀ v, ev w v Q = 0 → Good w v := by
  obtain ⟨contentEx, hcCard, hc⟩ := hcontent
  have hsum := ordinaryFactorRaw_sum_le (positiveDegreeFactorClasses i Q)
    (fun c ↦ degreeOf i c.rep) (fun c ↦ height c.rep) theta n D mu H
    (height (radicalContent i Q)) htheta hmu
    ((sum_degreeOf_positiveDegreeFactorClasses_le i Q).trans hroot) hheight
  obtain ⟨ex, hcard, hgood⟩ := exists_exceptional_of_factor_exceptional (α := ℚ) i hQ ev Good
    (height (radicalContent i Q))
    (fun c ↦ ordinaryFactorRaw theta n D (degreeOf i c.rep) (height c.rep))
    ⟨contentEx, Nat.cast_le.mpr hcCard, hc⟩ hfactors
  exact ⟨ex, hcard.trans hsum, hgood⟩

/-- Combine the content exception with the exceptions of the distinct positive-root-degree
factors, charging the free-retention charge `ordinaryUnifiedPowerFactorRawAt` with `ell` rows and
retention threshold `L`. The conclusion bounds the exceptional set by the free-retention charge of
the whole polynomial, with root-degree budget `B` and height budget `H`.

The hypothesis `Q ≠ 0` is needed as in `MvPolynomial.exists_exceptional_of_factor_exceptional`.
The hypotheses `0 ≤ theta` and `1 ≤ B` are needed as in
`ordinaryUnifiedPowerFactorRawAt_sum_le`. -/
theorem exists_exceptional_ordinaryUnifiedPowerFactorAssembly
    (i : σ) (Q : MvPolynomial σ R) (hQ : Q ≠ 0)
    (ev : W → V → Fn) (Good : W → V → Prop) (height : MvPolynomial σ R → ℕ)
    (theta : ℚ) (n D ell B H L : ℕ) (htheta : 0 ≤ theta) (hB : 1 ≤ B)
    (hroot : degreeOf i Q ≤ B)
    (hheight : height (radicalContent i Q) +
      ∑ c ∈ positiveDegreeFactorClasses i Q, height c.rep ≤ H)
    (hcontent : ∃ ex : Finset W, ex.card ≤ height (radicalContent i Q) ∧
      ∀ w ∉ ex, ∀ v, ev w v (radicalContent i Q) ≠ 0)
    (hfactors : ∀ c ∈ positiveDegreeFactorClasses i Q, ∃ ex : Finset W,
      (ex.card : ℚ) ≤
        ordinaryUnifiedPowerFactorRawAt theta n D ell (degreeOf i c.rep) (height c.rep) L ∧
      ∀ w ∉ ex, ∀ v, ev w v c.rep = 0 → Good w v) :
    ∃ ex : Finset W, (ex.card : ℚ) ≤ ordinaryUnifiedPowerFactorRawAt theta n D ell B H L ∧
      ∀ w ∉ ex, ∀ v, ev w v Q = 0 → Good w v := by
  obtain ⟨contentEx, hcCard, hc⟩ := hcontent
  have hsum := ordinaryUnifiedPowerFactorRawAt_sum_le (positiveDegreeFactorClasses i Q)
    (fun c ↦ degreeOf i c.rep) (fun c ↦ height c.rep) theta n D ell B H L
    (height (radicalContent i Q)) htheta hB
    ((sum_degreeOf_positiveDegreeFactorClasses_le i Q).trans hroot) hheight
  obtain ⟨ex, hcard, hgood⟩ := exists_exceptional_of_factor_exceptional (α := ℚ) i hQ ev Good
    (height (radicalContent i Q))
    (fun c ↦ ordinaryUnifiedPowerFactorRawAt theta n D ell (degreeOf i c.rep) (height c.rep) L)
    ⟨contentEx, Nat.cast_le.mpr hcCard, hc⟩ hfactors
  exact ⟨ex, hcard.trans hsum, hgood⟩

end ReedSolomon

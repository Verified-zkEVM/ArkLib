/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.Ordinary.FactorAssembly

/-!
# Acceptance tests for ordinary factor assembly

The source statement of `exists_exceptional_ordinaryFactorAssembly`, over a field with root
variable `none` and ring homomorphisms into a domain, is derived from the general one. The
fixed-split form of the free-retention assembly, which the source's unified curve theorem uses,
is derived through `ordinaryUnifiedPowerFactorRaw_eq_rawAt`. A two-point instance with no
positive-degree factor checks that the content exception alone is charged.
-/

open MvPolynomial

namespace ReedSolomon.FactorAssemblyTest

variable {F τ W V D : Type*} [Field F] [CommRing D] [IsDomain D]

/-- The source statement, with `ordinaryContent`, `ordinaryRootFactorClasses` and
`ordinaryFactorRepresentative` spelled `radicalContent none`, `positiveDegreeFactorClasses none`
and `Associates.rep`. -/
example (Q : MvPolynomial (Option τ) F) (hQ : Q ≠ 0)
    (ev : W → V → MvPolynomial (Option τ) F →+* D)
    (Good : W → V → Prop) (height : MvPolynomial (Option τ) F → ℕ)
    (theta : ℚ) (n D' mu H : ℕ) (htheta : 0 ≤ theta) (hmu : 1 ≤ mu)
    (hroot : Q.degreeOf none ≤ mu)
    (hheight : height (radicalContent none Q) +
      ∑ a ∈ positiveDegreeFactorClasses none Q, height a.rep ≤ H)
    (hcontent : ∃ ex : Finset W, ex.card ≤ height (radicalContent none Q) ∧
      ∀ w ∉ ex, ∀ v, ev w v (radicalContent none Q) ≠ 0)
    (hfactors : ∀ a ∈ positiveDegreeFactorClasses none Q, ∃ ex : Finset W,
      (ex.card : ℚ) ≤ ordinaryFactorRaw theta n D' (degreeOf none a.rep) (height a.rep) ∧
      ∀ w ∉ ex, ∀ v, ev w v a.rep = 0 → Good w v) :
    ∃ ex : Finset W, (ex.card : ℚ) ≤ ordinaryFactorRaw theta n D' mu H ∧
      ∀ w ∉ ex, ∀ v, ev w v Q = 0 → Good w v :=
  exists_exceptional_ordinaryFactorAssembly none Q hQ ev Good height theta n D' mu H htheta hmu
    hroot hheight hcontent hfactors

/-- The fixed-split form of the free-retention assembly. -/
example (Q : MvPolynomial (Option τ) F) (hQ : Q ≠ 0)
    (ev : W → V → MvPolynomial (Option τ) F →+* D)
    (Good : W → V → Prop) (height : MvPolynomial (Option τ) F → ℕ)
    (theta : ℚ) (n D' ell B H : ℕ) (htheta : 0 ≤ theta) (hB : 1 ≤ B)
    (hroot : Q.degreeOf none ≤ B)
    (hheight : height (radicalContent none Q) +
      ∑ a ∈ positiveDegreeFactorClasses none Q, height a.rep ≤ H)
    (hcontent : ∃ ex : Finset W, ex.card ≤ height (radicalContent none Q) ∧
      ∀ w ∉ ex, ∀ v, ev w v (radicalContent none Q) ≠ 0)
    (hfactors : ∀ a ∈ positiveDegreeFactorClasses none Q, ∃ ex : Finset W,
      (ex.card : ℚ) ≤
        ordinaryUnifiedPowerFactorRaw theta n D' ell (degreeOf none a.rep) (height a.rep) ∧
      ∀ w ∉ ex, ∀ v, ev w v a.rep = 0 → Good w v) :
    ∃ ex : Finset W, (ex.card : ℚ) ≤ ordinaryUnifiedPowerFactorRaw theta n D' ell B H ∧
      ∀ w ∉ ex, ∀ v, ev w v Q = 0 → Good w v := by
  simp only [ordinaryUnifiedPowerFactorRaw_eq_rawAt] at hfactors ⊢
  exact exists_exceptional_ordinaryUnifiedPowerFactorAssembly none Q hQ ev Good height theta n D'
    ell B H (D' + 1) htheta hB hroot hheight hcontent hfactors

end ReedSolomon.FactorAssemblyTest

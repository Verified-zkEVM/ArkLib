/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.Polynomial.GCDSplit
public import ArkLib.Data.Polynomial.ModularInverse

/-!
# Zero-unit splitting for quotient coefficients

The D5 Euclidean recursion branches on whether one coefficient is zero or invertible at each root
of its current squarefree modulus.  This file implements that single coefficient split.  It takes
the gcd of the modulus with the coefficient, divides out the gcd, and computes one modular inverse
on the complementary child.

The result partitions geometric roots exactly after every coefficient-field extension.  This is
only the base-modulus operation used by the recursion; it does not construct the full decoder or
make a runtime-complexity claim.
-/

@[expose] public section

namespace ReedSolomon.ListDecoding.FirstOrderNormDecoder.D5

open CompPoly Polynomial

variable {F : Type*} [Field F] [BEq F] [LawfulBEq F]

/-- Executable data returned by splitting one quotient coefficient into its zero and unit loci. -/
structure CoefficientSplit where
  zeroModulus : CPolynomial F
  unitModulus : CPolynomial F
  unitInverse : CPolynomial F

/-- Split `g` by the vanishing of `a`, then compute an inverse of `a` modulo the nonvanishing
child.  Failure is possible for arbitrary inputs; a nonzero squarefree modulus always succeeds. -/
def coefficientSplit? (g a : CPolynomial F) : Option (CoefficientSplit (F := F)) :=
  let g0 := CPolynomial.gcdFactor g a
  let g1 := CPolynomial.gcdComplement g a
  match CPolynomial.inverseMod? a g1 with
  | none => none
  | some inverse => some ⟨g0, g1, inverse⟩

/-- A returned split exposes the computed gcd, complementary factor, and modular inverse exactly. -/
theorem coefficientSplit?_eq_some_iff
    {g a : CPolynomial F} {output : CoefficientSplit (F := F)} :
    coefficientSplit? g a = some output ↔
      ∃ inverse, CPolynomial.inverseMod? a (CPolynomial.gcdComplement g a) = some inverse ∧
        output = ⟨CPolynomial.gcdFactor g a, CPolynomial.gcdComplement g a, inverse⟩ := by
  dsimp only [coefficientSplit?]
  split
  · rename_i hinverse
    simp [hinverse]
  · rename_i inverse hinverse
    simp only [Option.some.injEq]
    constructor
    · intro houtput
      exact ⟨inverse, hinverse, houtput.symm⟩
    · rintro ⟨candidate, hcandidate, rfl⟩
      exact congrArg
        (CoefficientSplit.mk (CPolynomial.gcdFactor g a)
          (CPolynomial.gcdComplement g a))
        (Option.some.inj (hinverse.symm.trans hcandidate))

/-- The inverse guard succeeds for a nonzero squarefree modulus. -/
theorem exists_coefficientSplit (g a : CPolynomial F) (hg : g ≠ 0)
    (hgfree : Squarefree g.toPoly) :
    ∃ output, coefficientSplit? g a = some output := by
  have hcoprime : IsCoprime a.toPoly (CPolynomial.gcdComplement g a).toPoly :=
    (CPolynomial.gcdComplement_isCoprime_right hg hgfree).symm
  obtain ⟨inverse, hinverse⟩ :=
    (CPolynomial.inverseMod_exists_iff_coprime a (CPolynomial.gcdComplement g a)).2 hcoprime
  refine ⟨⟨CPolynomial.gcdFactor g a, CPolynomial.gcdComplement g a, inverse⟩, ?_⟩
  simp [coefficientSplit?, hinverse]

/-- A successful split factors the original modulus exactly. -/
theorem coefficientSplit_factorization
    {g a : CPolynomial F} {output : CoefficientSplit (F := F)}
    (houtput : coefficientSplit? g a = some output) (hg : g ≠ 0) :
    output.zeroModulus * output.unitModulus = g := by
  obtain ⟨_, _, rfl⟩ := coefficientSplit?_eq_some_iff.mp houtput
  exact CPolynomial.gcdFactor_mul_gcdComplement hg

/-- Splitting preserves the complete degree budget, including constant children. -/
theorem coefficientSplit_natDegree_add
    {g a : CPolynomial F} {output : CoefficientSplit (F := F)}
    (houtput : coefficientSplit? g a = some output) (hg : g ≠ 0) :
    output.zeroModulus.natDegree + output.unitModulus.natDegree = g.natDegree := by
  obtain ⟨_, _, rfl⟩ := coefficientSplit?_eq_some_iff.mp houtput
  simpa only [CPolynomial.natDegree_toPoly] using
    CPolynomial.natDegree_gcdFactor_add_gcdComplement (h := g) (e := a) hg

/-- A monic parent produces two monic children. -/
theorem coefficientSplit_monic
    {g a : CPolynomial F} {output : CoefficientSplit (F := F)}
    (houtput : coefficientSplit? g a = some output) (hg : g ≠ 0) (hgmonic : g.monic) :
    output.zeroModulus.monic ∧ output.unitModulus.monic := by
  obtain ⟨_, _, rfl⟩ := coefficientSplit?_eq_some_iff.mp houtput
  exact ⟨CPolynomial.gcdFactor_monic hg, CPolynomial.gcdComplement_monic hgmonic⟩

/-- A squarefree parent produces two squarefree children. -/
theorem coefficientSplit_squarefree
    {g a : CPolynomial F} {output : CoefficientSplit (F := F)}
    (houtput : coefficientSplit? g a = some output) (hg : g ≠ 0)
    (hgfree : Squarefree g.toPoly) :
    Squarefree output.zeroModulus.toPoly ∧ Squarefree output.unitModulus.toPoly := by
  obtain ⟨_, _, rfl⟩ := coefficientSplit?_eq_some_iff.mp houtput
  exact ⟨CPolynomial.gcdFactor_squarefree hgfree,
    CPolynomial.gcdComplement_squarefree hg hgfree⟩

/-- Over every field extension, the zero child consists exactly of roots where the coefficient
vanishes. -/
theorem eval₂_zeroModulus_eq_zero_iff
    {g a : CPolynomial F} {output : CoefficientSplit (F := F)}
    (houtput : coefficientSplit? g a = some output)
    {K : Type*} [Field K] (phi : F →+* K) (x : K) :
    output.zeroModulus.toPoly.eval₂ phi x = 0 ↔
      g.toPoly.eval₂ phi x = 0 ∧ a.toPoly.eval₂ phi x = 0 := by
  obtain ⟨_, _, rfl⟩ := coefficientSplit?_eq_some_iff.mp houtput
  exact CPolynomial.eval₂_gcdFactor_eq_zero_iff_left_right phi x g a

/-- Over every field extension, the unit child consists exactly of roots where the coefficient
does not vanish. -/
theorem eval₂_unitModulus_eq_zero_iff
    {g a : CPolynomial F} {output : CoefficientSplit (F := F)}
    (houtput : coefficientSplit? g a = some output) (hg : g ≠ 0)
    (hgfree : Squarefree g.toPoly)
    {K : Type*} [Field K] (phi : F →+* K) (x : K) :
    output.unitModulus.toPoly.eval₂ phi x = 0 ↔
      g.toPoly.eval₂ phi x = 0 ∧ a.toPoly.eval₂ phi x ≠ 0 := by
  obtain ⟨_, _, rfl⟩ := coefficientSplit?_eq_some_iff.mp houtput
  exact CPolynomial.eval₂_gcdComplement_eq_zero_iff_left_and_right_ne_zero
    phi x hg hgfree

/-- The returned Bézout coefficient is an executable inverse modulo the unit child. -/
theorem coefficientSplit_inverse_mod
    {g a : CPolynomial F} {output : CoefficientSplit (F := F)}
    (houtput : coefficientSplit? g a = some output) (hgmonic : g.monic) :
    (a * output.unitInverse).modByMonic output.unitModulus =
      (1 : CPolynomial F).modByMonic output.unitModulus := by
  obtain ⟨_, hinverse, rfl⟩ := coefficientSplit?_eq_some_iff.mp houtput
  have hunitMonic : (CPolynomial.gcdComplement g a).monic :=
    CPolynomial.gcdComplement_monic hgmonic
  exact CPolynomial.inverseMod?_mul_modByMonic hunitMonic hinverse

/-- At every geometric root of the unit child, the returned inverse specializes to a scalar
inverse of the coefficient. -/
theorem eval₂_mul_unitInverse_eq_one
    {g a : CPolynomial F} {output : CoefficientSplit (F := F)}
    (houtput : coefficientSplit? g a = some output)
    {K : Type*} [Field K] (phi : F →+* K) (x : K)
    (hroot : output.unitModulus.toPoly.eval₂ phi x = 0) :
    a.toPoly.eval₂ phi x * output.unitInverse.toPoly.eval₂ phi x = 1 := by
  obtain ⟨_, hinverse, rfl⟩ := coefficientSplit?_eq_some_iff.mp houtput
  exact CPolynomial.eval₂_mul_inverseMod_eq_one phi x hroot
    hinverse

end ReedSolomon.ListDecoding.FirstOrderNormDecoder.D5

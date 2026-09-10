/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.ToCompPoly.Univariate.Basic
public import CompPoly.Univariate.EuclideanAlgorithm
public import Mathlib.Algebra.Polynomial.FieldDivision
public import Mathlib.Algebra.Squarefree.Basic

/-!
# Executable gcd splitting for computable polynomials

This file packages `CompPoly.CPolynomial.gcdMonic` and `divByMonic` as the
factor split used by symbolic decoding.  The executable definitions stay in
`CPolynomial`; their specifications are stated through `toPoly`, so downstream
proofs can use Mathlib's polynomial API directly.
-/

@[expose] public section

namespace CompPoly.CPolynomial

variable {F : Type*} [Field F] [BEq F] [LawfulBEq F]

/-- The monic common factor selected when splitting `h` by an equation `e`. -/
def gcdFactor (h e : CPolynomial F) : CPolynomial F :=
  gcdMonic h e

/-- The exact complementary factor of `h` selected by `gcdFactor`. -/
def gcdComplement (h e : CPolynomial F) : CPolynomial F :=
  h.divByMonic (gcdFactor h e)

/-- Executable split of `h` into its gcd with `e` and the complementary factor. -/
def gcdSplit (h e : CPolynomial F) : CPolynomial F × CPolynomial F :=
  (gcdFactor h e, gcdComplement h e)

@[simp] theorem gcdSplit_fst (h e : CPolynomial F) :
    (gcdSplit h e).1 = gcdFactor h e := rfl

@[simp] theorem gcdSplit_snd (h e : CPolynomial F) :
    (gcdSplit h e).2 = gcdComplement h e := rfl

theorem gcdFactor_toPoly [DecidableEq F] (h e : CPolynomial F) :
    (gcdFactor h e).toPoly =
      normalize (EuclideanDomain.gcd h.toPoly e.toPoly) := by
  exact gcdMonic_toPoly_eq_normalize_gcd h e

theorem gcdFactor_monic {h e : CPolynomial F} (hh : h ≠ 0) :
    (gcdFactor h e).monic := by
  let : DecidableEq F := instDecidableEqOfLawfulBEq
  rw [monic_toPoly_iff, gcdFactor_toPoly]
  apply Polynomial.monic_normalize
  intro hgcd
  have hhpoly : h.toPoly = 0 := (EuclideanDomain.gcd_eq_zero_iff.mp hgcd).1
  exact hh ((toPoly_eq_zero_iff h).mp hhpoly)

theorem gcdFactor_dvd_left (h e : CPolynomial F) :
    (gcdFactor h e).toPoly ∣ h.toPoly := by
  let : DecidableEq F := instDecidableEqOfLawfulBEq
  rw [gcdFactor_toPoly]
  exact (normalize_associated (EuclideanDomain.gcd h.toPoly e.toPoly)).dvd.trans
    (EuclideanDomain.gcd_dvd_left h.toPoly e.toPoly)

theorem gcdFactor_dvd_right (h e : CPolynomial F) :
    (gcdFactor h e).toPoly ∣ e.toPoly := by
  let : DecidableEq F := instDecidableEqOfLawfulBEq
  rw [gcdFactor_toPoly]
  exact (normalize_associated (EuclideanDomain.gcd h.toPoly e.toPoly)).dvd.trans
    (EuclideanDomain.gcd_dvd_right h.toPoly e.toPoly)

/-- The gcd child contains exactly the common roots, after any field extension. -/
theorem eval₂_gcdFactor_eq_zero_iff_left_right
    {K : Type*} [Field K] (phi : F →+* K) (x : K) (h e : CPolynomial F) :
    (gcdFactor h e).toPoly.eval₂ phi x = 0 ↔
      h.toPoly.eval₂ phi x = 0 ∧ e.toPoly.eval₂ phi x = 0 := by
  let : DecidableEq F := instDecidableEqOfLawfulBEq
  rw [gcdFactor_toPoly]
  let g := EuclideanDomain.gcd h.toPoly e.toPoly
  have hnormalize : (normalize g).eval₂ phi x = 0 ↔ g.eval₂ phi x = 0 := by
    by_cases hg : g = 0
    · simp [hg]
    · have hunit :
          IsUnit (Polynomial.eval₂ phi x ((normUnit g : Polynomial F))) :=
        (normUnit g).isUnit.map (Polynomial.eval₂RingHom phi x)
      rw [normalize_apply, Polynomial.eval₂_mul, mul_eq_zero, or_iff_left hunit.ne_zero]
  rw [hnormalize]
  exact Polynomial.root_gcd_iff_root_left_right

theorem gcdComplement_toPoly {h e : CPolynomial F} (hh : h ≠ 0) :
    (gcdComplement h e).toPoly =
      h.toPoly /ₘ (gcdFactor h e).toPoly := by
  exact divByMonic_toPoly_eq_divByMonic h (gcdFactor h e) (gcdFactor_monic hh)

/-- The executable split is exact, rather than merely a division with remainder. -/
theorem gcdFactor_mul_gcdComplement {h e : CPolynomial F} (hh : h ≠ 0) :
    gcdFactor h e * gcdComplement h e = h := by
  have hdivision := modByMonic_add_mul_divByMonic h (gcdFactor h e) (gcdFactor_monic hh)
  have hmod : h.modByMonic (gcdFactor h e) = 0 := by
    apply toPoly_injective
    rw [modByMonic_toPoly_eq_modByMonic h (gcdFactor h e) (gcdFactor_monic hh),
      toPoly_zero]
    exact Polynomial.modByMonic_eq_zero_iff_dvd
      ((monic_toPoly_iff (gcdFactor h e)).mp (gcdFactor_monic hh)) |>.2
        (gcdFactor_dvd_left h e)
  simpa [gcdComplement, hmod] using hdivision

/-- Root partition induced by `gcdSplit`, valid after mapping coefficients to any field. -/
theorem eval₂_gcdFactor_eq_zero_or_gcdComplement_eq_zero
    {K : Type*} [Field K] (phi : F →+* K) (x : K)
    {h e : CPolynomial F} (hh : h ≠ 0) :
    h.toPoly.eval₂ phi x = 0 ↔
      (gcdFactor h e).toPoly.eval₂ phi x = 0 ∨
        (gcdComplement h e).toPoly.eval₂ phi x = 0 := by
  have hfac := congrArg (CPolynomial.toPoly (R := F))
    (gcdFactor_mul_gcdComplement (h := h) (e := e) hh)
  rw [toPoly_mul] at hfac
  rw [← hfac, Polynomial.eval₂_mul, mul_eq_zero]

theorem gcdFactor_squarefree {h e : CPolynomial F}
    (hhfree : Squarefree h.toPoly) : Squarefree (gcdFactor h e).toPoly :=
  hhfree.squarefree_of_dvd (gcdFactor_dvd_left h e)

theorem gcdComplement_squarefree {h e : CPolynomial F} (hh : h ≠ 0)
    (hhfree : Squarefree h.toPoly) : Squarefree (gcdComplement h e).toPoly := by
  apply hhfree.squarefree_of_dvd
  refine ⟨(gcdFactor h e).toPoly, ?_⟩
  have hfac := congrArg (CPolynomial.toPoly (R := F))
    (gcdFactor_mul_gcdComplement (h := h) (e := e) hh)
  rw [toPoly_mul] at hfac
  simpa [mul_comm] using hfac.symm

/-- A monic parent splits into two monic children. -/
theorem gcdComplement_monic {h e : CPolynomial F} (hhmonic : h.monic) :
    (gcdComplement h e).monic := by
  have hhpolyMonic : h.toPoly.Monic := (monic_toPoly_iff h).mp hhmonic
  have hh : h ≠ 0 := (toPoly_eq_zero_iff h).not.mp hhpolyMonic.ne_zero
  rw [monic_toPoly_iff]
  apply ((monic_toPoly_iff (gcdFactor h e)).mp (gcdFactor_monic hh)).of_mul_monic_left
  have hfac := congrArg (CPolynomial.toPoly (R := F))
    (gcdFactor_mul_gcdComplement (h := h) (e := e) hh)
  rw [toPoly_mul] at hfac
  exact hfac.symm ▸ hhpolyMonic

theorem gcdFactor_isRelPrime_gcdComplement {h e : CPolynomial F} (hh : h ≠ 0)
    (hhfree : Squarefree h.toPoly) :
    IsRelPrime (gcdFactor h e).toPoly (gcdComplement h e).toPoly := by
  have hfac := congrArg (CPolynomial.toPoly (R := F))
    (gcdFactor_mul_gcdComplement (h := h) (e := e) hh)
  rw [toPoly_mul] at hfac
  exact IsRelPrime.of_squarefree_mul (hfac.symm ▸ hhfree)

/-- Squarefreeness makes the two children root-disjoint over every field extension. -/
theorem eval₂_gcdFactor_ne_zero_or_gcdComplement_ne_zero
    {K : Type*} [Field K] (phi : F →+* K) (x : K)
    {h e : CPolynomial F} (hh : h ≠ 0) (hhfree : Squarefree h.toPoly) :
    (gcdFactor h e).toPoly.eval₂ phi x ≠ 0 ∨
      (gcdComplement h e).toPoly.eval₂ phi x ≠ 0 := by
  have hcoprime :=
    (gcdFactor_isRelPrime_gcdComplement (e := e) hh hhfree).isCoprime
  rcases hcoprime with ⟨a, b, hab⟩
  by_contra! hz
  have heval := congrArg (Polynomial.eval₂ phi x) hab
  simp [hz.1, hz.2] at heval

/-- Under a squarefree modulus, the complementary child contains precisely the roots
of `h` rejected by the equation `e`. -/
theorem eval₂_gcdComplement_eq_zero_iff_left_and_right_ne_zero
    {K : Type*} [Field K] (phi : F →+* K) (x : K)
    {h e : CPolynomial F} (hh : h ≠ 0) (hhfree : Squarefree h.toPoly) :
    (gcdComplement h e).toPoly.eval₂ phi x = 0 ↔
      h.toPoly.eval₂ phi x = 0 ∧ e.toPoly.eval₂ phi x ≠ 0 := by
  constructor
  · intro hq
    have hhroot : h.toPoly.eval₂ phi x = 0 :=
      (eval₂_gcdFactor_eq_zero_or_gcdComplement_eq_zero phi x hh).2 (Or.inr hq)
    refine ⟨hhroot, ?_⟩
    intro heroot
    have hgroot := (eval₂_gcdFactor_eq_zero_iff_left_right phi x h e).2
      ⟨hhroot, heroot⟩
    exact (eval₂_gcdFactor_ne_zero_or_gcdComplement_ne_zero phi x hh hhfree).elim
      (fun hg ↦ hg hgroot) (fun hqn ↦ hqn hq)
  · rintro ⟨hhroot, heroot⟩
    rcases (eval₂_gcdFactor_eq_zero_or_gcdComplement_eq_zero phi x hh).1 hhroot with
      hgroot | hqroot
    · exact False.elim (heroot
        ((eval₂_gcdFactor_eq_zero_iff_left_right phi x h e).1 hgroot).2)
    · exact hqroot

theorem natDegree_gcdFactor_add_gcdComplement {h e : CPolynomial F} (hh : h ≠ 0) :
    (gcdFactor h e).toPoly.natDegree + (gcdComplement h e).toPoly.natDegree =
      h.toPoly.natDegree := by
  have hfac := congrArg (CPolynomial.toPoly (R := F))
    (gcdFactor_mul_gcdComplement (h := h) (e := e) hh)
  rw [toPoly_mul] at hfac
  have hg : (gcdFactor h e).toPoly ≠ 0 :=
    ((monic_toPoly_iff (gcdFactor h e)).mp (gcdFactor_monic hh)).ne_zero
  have hhpoly : h.toPoly ≠ 0 := (toPoly_eq_zero_iff h).not.mpr hh
  have hq : (gcdComplement h e).toPoly ≠ 0 := by
    intro hq
    apply hhpoly
    simpa [hq] using hfac.symm
  rw [← hfac, Polynomial.natDegree_mul hg hq]

/-- Removing the gcd from a squarefree modulus leaves a factor coprime to the entire tested
polynomial. This is the guard needed to invert a denominator on the surviving root set. -/
theorem gcdComplement_isCoprime_right {h e : CPolynomial F}
    (hh : h ≠ 0) (hfree : Squarefree h.toPoly) :
    IsCoprime (gcdComplement h e).toPoly e.toPoly := by
  let : DecidableEq F := instDecidableEqOfLawfulBEq
  apply IsRelPrime.isCoprime
  intro d hdleft hdright
  have hdg : d ∣ (gcdFactor h e).toPoly := by
    rw [gcdFactor_toPoly, dvd_normalize_iff]
    apply EuclideanDomain.dvd_gcd
    · exact hdleft.trans (by
        have heq := congrArg CPolynomial.toPoly
          (gcdFactor_mul_gcdComplement (h := h) (e := e) hh)
        rw [toPoly_mul] at heq
        exact ⟨(gcdFactor h e).toPoly, by rw [← heq]; ring⟩)
    · exact hdright
  exact (gcdFactor_isRelPrime_gcdComplement (e := e) hh hfree) hdg hdleft

/-- Replacing a residual by its remainder preserves the normalized agreement factor. -/
theorem gcdFactor_modByMonic (h e : CPolynomial F) (hh : h.monic) :
    gcdFactor h (e.modByMonic h) = gcdFactor h e := by
  let : DecidableEq F := instDecidableEqOfLawfulBEq
  have hn : h ≠ 0 := (toPoly_eq_zero_iff h).not.mp ((monic_toPoly_iff h).mp hh).ne_zero
  apply toPoly_injective
  apply Polynomial.eq_of_monic_of_associated
    ((monic_toPoly_iff _).mp (gcdFactor_monic hn))
    ((monic_toPoly_iff _).mp (gcdFactor_monic hn))
  apply associated_of_dvd_dvd
  · rw [gcdFactor_toPoly h e, dvd_normalize_iff]
    apply EuclideanDomain.dvd_gcd
    · exact gcdFactor_dvd_left _ _
    · have hd := gcdFactor_dvd_right h (e.modByMonic h)
      rw [modByMonic_toPoly_eq_modByMonic _ _ hh] at hd
      rw [← Polynomial.modByMonic_add_div e.toPoly h.toPoly]
      exact dvd_add hd (dvd_mul_of_dvd_left (gcdFactor_dvd_left _ _) _)
  · rw [gcdFactor_toPoly h (e.modByMonic h), dvd_normalize_iff]
    apply EuclideanDomain.dvd_gcd
    · exact gcdFactor_dvd_left _ _
    · rw [modByMonic_toPoly_eq_modByMonic _ _ hh, Polynomial.modByMonic_eq_sub_mul_div]
      exact dvd_sub (gcdFactor_dvd_right _ _)
        (dvd_mul_of_dvd_left (gcdFactor_dvd_left _ _) _)

/-- The complementary branch is also unchanged after reducing the tested equation. -/
theorem gcdComplement_modByMonic (h e : CPolynomial F) (hh : h.monic) :
    gcdComplement h (e.modByMonic h) = gcdComplement h e := by
  simp only [gcdComplement, gcdFactor_modByMonic h e hh]

end CompPoly.CPolynomial

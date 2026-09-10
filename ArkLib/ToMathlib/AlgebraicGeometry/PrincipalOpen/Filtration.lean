/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import ArkLib.ToMathlib.AlgebraicGeometry.Hilbert.Function
public import Mathlib.RingTheory.Localization.Away.Basic

/-!
# Degree growth in a principal localization

The actual finite filtration consists of bounded-degree numerators divided by
bounded powers of the localized element. Clearing denominators gives a controlled
numerator and bounds its dimension between two original Hilbert-function values.
-/

@[expose] public section

noncomputable section

open MvPolynomial
open scoped BigOperators

namespace AffineHilbert

variable {F σ : Type*} [Field F] [Finite σ]

abbrev CoordinateRing (I : Ideal (MvPolynomial σ F)) :=
  MvPolynomial σ F ⧸ I

abbrev AwayRing (I : Ideal (MvPolynomial σ F)) (s : MvPolynomial σ F) :=
  Localization.Away (Ideal.Quotient.mk I s)

/-- Numerators of degree at most `N`, embedded in the principal localization. -/
def awayNumeratorDegreeLE (I : Ideal (MvPolynomial σ F)) (s : MvPolynomial σ F) (N : ℕ) :
    Submodule F (AwayRing I s) :=
  (quotientDegreeLE I N).map
    (IsScalarTower.toAlgHom F (CoordinateRing I) (AwayRing I s)).toLinearMap

/-- A numerator of degree at most `N`, multiplied by the `e`th power of the distinguished
inverse in the principal localization. -/
def awayTermMap (I : Ideal (MvPolynomial σ F)) (s : MvPolynomial σ F) (N e : ℕ) :
    quotientDegreeLE I N →ₗ[F] AwayRing I s where
  toFun q := IsScalarTower.toAlgHom F (CoordinateRing I) (AwayRing I s) q.1 *
    IsLocalization.Away.invSelf (Ideal.Quotient.mk I s) ^ e
  map_add' x y := by simp [add_mul]
  map_smul' c x := by simp

/-- The concrete bounded numerator-and-denominator filtration on a principal localization. -/
def awayDegreeLE (I : Ideal (MvPolynomial σ F)) (s : MvPolynomial σ F) (N : ℕ) :
    Submodule F (AwayRing I s) :=
  ⨆ e : Fin (N + 1), LinearMap.range (awayTermMap I s N e)

/-- The original quotient filtration embeds as the denominator-exponent-zero part. -/
def quotientDegreeLEToAwayDegreeLE (I : Ideal (MvPolynomial σ F))
    (s : MvPolynomial σ F) (N : ℕ) :
    quotientDegreeLE I N →ₗ[F] awayDegreeLE I s N :=
  (awayTermMap I s N 0).codRestrict _ fun q ↦
    Submodule.mem_iSup_of_mem (0 : Fin (N + 1)) ⟨q, rfl⟩

omit [Finite σ] in
theorem quotientDegreeLEToAwayDegreeLE_injective
    {I : Ideal (MvPolynomial σ F)} (hI : I.IsPrime)
    {s : MvPolynomial σ F} (hs : s ∉ I) (N : ℕ) :
    Function.Injective (quotientDegreeLEToAwayDegreeLE I s N) := by
  let _ : I.IsPrime := hI
  have hsbar : Ideal.Quotient.mk I s ≠ 0 := fun h ↦
    hs (Ideal.Quotient.eq_zero_iff_mem.mp h)
  have hinj : Function.Injective
      (algebraMap (CoordinateRing I) (AwayRing I s)) := by
    exact IsLocalization.injective (AwayRing I s)
      (Submonoid.powers_le.mpr (mem_nonZeroDivisors_iff_ne_zero.mpr hsbar))
  intro x y hxy
  apply Subtype.ext
  apply hinj
  simpa [quotientDegreeLEToAwayDegreeLE, awayTermMap] using congrArg Subtype.val hxy

/-- Multiplication by the common denominator used to clear all inverse powers up to `N`. -/
def awayClearMap (I : Ideal (MvPolynomial σ F)) (s : MvPolynomial σ F) (N : ℕ) :
    AwayRing I s →ₗ[F] AwayRing I s :=
  LinearMap.mulLeft F
    (algebraMap (CoordinateRing I) (AwayRing I s) (Ideal.Quotient.mk I s) ^ N)

omit [Finite σ] in
theorem awayDegreeLE_le_comap_clear
    (I : Ideal (MvPolynomial σ F)) (s : MvPolynomial σ F) (N : ℕ) :
    awayDegreeLE I s N ≤
      (awayNumeratorDegreeLE I s (N + N * s.totalDegree)).comap
        (awayClearMap I s N) := by
  rw [awayDegreeLE]
  apply iSup_le
  intro e
  rintro _ ⟨q, rfl⟩
  rw [Submodule.mem_comap]
  obtain ⟨p, hp, hpq⟩ := q.property
  have hpdeg : p.totalDegree ≤ N := (mem_restrictTotalDegree σ N p).mp hp
  have he : e.val ≤ N := by omega
  have hproddeg : (s ^ (N - e.val) * p).totalDegree ≤ N + N * s.totalDegree := by
    calc
      (s ^ (N - e.val) * p).totalDegree ≤
          (N - e.val) * s.totalDegree + p.totalDegree :=
        (totalDegree_mul _ _).trans (Nat.add_le_add_right (totalDegree_pow _ _) _)
      _ ≤ N * s.totalDegree + N :=
        Nat.add_le_add (Nat.mul_le_mul_right _ (Nat.sub_le N e.val)) hpdeg
      _ = N + N * s.totalDegree := Nat.add_comm _ _
  let q' : quotientDegreeLE I (N + N * s.totalDegree) :=
    ⟨Ideal.Quotient.mk I (s ^ (N - e.val) * p),
      ⟨s ^ (N - e.val) * p,
        (mem_restrictTotalDegree σ (N + N * s.totalDegree) _).mpr hproddeg, rfl⟩⟩
  rw [awayNumeratorDegreeLE, Submodule.mem_map]
  refine ⟨q', q'.property, ?_⟩
  have hpow :
      algebraMap (CoordinateRing I) (AwayRing I s) (Ideal.Quotient.mk I s) ^ N =
        algebraMap (CoordinateRing I) (AwayRing I s) (Ideal.Quotient.mk I s) ^ (N - e.val) *
          algebraMap (CoordinateRing I) (AwayRing I s) (Ideal.Quotient.mk I s) ^ e.val := by
    rw [← pow_add, Nat.sub_add_cancel he]
  have hinv := IsLocalization.Away.mul_invSelf
    (S := AwayRing I s) (Ideal.Quotient.mk I s)
  symm
  change algebraMap (CoordinateRing I) (AwayRing I s) (Ideal.Quotient.mk I s) ^ N *
      (IsScalarTower.toAlgHom F (CoordinateRing I) (AwayRing I s) q.1 *
        IsLocalization.Away.invSelf (Ideal.Quotient.mk I s) ^ e.val) =
    IsScalarTower.toAlgHom F (CoordinateRing I) (AwayRing I s) q'.1
  rw [hpow]
  have hpq' : q.1 = Ideal.Quotient.mk I p := hpq.symm
  rw [hpq']
  change _ = algebraMap (CoordinateRing I) (AwayRing I s)
    (Ideal.Quotient.mk I (s ^ (N - e.val) * p))
  rw [map_mul, map_pow]
  rw [map_mul, map_pow]
  have hcancel :
      algebraMap (CoordinateRing I) (AwayRing I s) (Ideal.Quotient.mk I s) ^ e.val *
        IsLocalization.Away.invSelf (Ideal.Quotient.mk I s) ^ e.val = 1 := by
    rw [← mul_pow, hinv, one_pow]
  calc
    _ = algebraMap (CoordinateRing I) (AwayRing I s) (Ideal.Quotient.mk I s) ^
          (N - e.val) *
        IsScalarTower.toAlgHom F (CoordinateRing I) (AwayRing I s)
          (Ideal.Quotient.mk I p) *
        (algebraMap (CoordinateRing I) (AwayRing I s) (Ideal.Quotient.mk I s) ^ e.val *
          IsLocalization.Away.invSelf (Ideal.Quotient.mk I s) ^ e.val) := by ring
    _ = _ := by rw [hcancel, mul_one, IsScalarTower.toAlgHom_apply]

/-- The localization filtration has dimension between the original degree-`N` quotient piece
and the original degree-`N(1+deg s)` piece.  This is the concrete growth comparison obtained by
embedding at denominator exponent zero and clearing all denominators by `s^N`. -/
theorem hilbertFunction_le_finrank_awayDegreeLE_le
    {I : Ideal (MvPolynomial σ F)} (hI : I.IsPrime)
    {s : MvPolynomial σ F} (hs : s ∉ I) (N : ℕ) :
    hilbertFunction I N ≤ Module.finrank F (awayDegreeLE I s N) ∧
      Module.finrank F (awayDegreeLE I s N) ≤
        hilbertFunction I (N + N * s.totalDegree) := by
  let _ : I.IsPrime := hI
  let numeratorMap : quotientDegreeLE I (N + N * s.totalDegree) →ₗ[F]
      awayNumeratorDegreeLE I s (N + N * s.totalDegree) :=
    ((IsScalarTower.toAlgHom F (CoordinateRing I) (AwayRing I s)).toLinearMap.domRestrict
      (quotientDegreeLE I (N + N * s.totalDegree))).codRestrict _ fun q ↦ by
        rw [awayNumeratorDegreeLE, Submodule.mem_map]
        exact ⟨q, q.property, rfl⟩
  have hnumerator : Function.Surjective numeratorMap := by
    intro y
    have hy := y.property
    change y.1 ∈ (quotientDegreeLE I (N + N * s.totalDegree)).map
      (IsScalarTower.toAlgHom F (CoordinateRing I) (AwayRing I s)).toLinearMap at hy
    rw [Submodule.mem_map] at hy
    obtain ⟨q, hq, hqy⟩ := hy
    refine ⟨⟨q, hq⟩, Subtype.ext ?_⟩
    exact hqy
  let _ : Module.Finite F
      (awayNumeratorDegreeLE I s (N + N * s.totalDegree)) :=
    Module.Finite.of_surjective numeratorMap hnumerator
  let clear : awayDegreeLE I s N →ₗ[F]
      awayNumeratorDegreeLE I s (N + N * s.totalDegree) :=
    ((awayClearMap I s N).domRestrict (awayDegreeLE I s N)).codRestrict _
      (fun x ↦ awayDegreeLE_le_comap_clear I s N x.property)
  have hclear : Function.Injective clear := by
    intro x y hxy
    apply Subtype.ext
    have hunit : IsUnit
        (algebraMap (CoordinateRing I) (AwayRing I s) (Ideal.Quotient.mk I s) ^ N) :=
      (IsLocalization.Away.algebraMap_isUnit (S := AwayRing I s)
        (Ideal.Quotient.mk I s)).pow N
    apply hunit.mul_left_cancel
    simpa only [clear, awayClearMap, LinearMap.codRestrict_apply,
      LinearMap.domRestrict_apply, LinearMap.mulLeft_apply] using congrArg Subtype.val hxy
  let _ : Module.Finite F (awayDegreeLE I s N) :=
    Module.Finite.of_injective clear hclear
  constructor
  · unfold hilbertFunction
    exact LinearMap.finrank_le_finrank_of_injective
      (quotientDegreeLEToAwayDegreeLE_injective hI hs N)
  · exact (LinearMap.finrank_le_finrank_of_injective hclear).trans
      (by
        unfold hilbertFunction
        exact LinearMap.finrank_le_finrank_of_surjective hnumerator)

end AffineHilbert

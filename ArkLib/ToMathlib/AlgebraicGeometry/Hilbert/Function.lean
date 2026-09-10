/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.RingTheory.Ideal.Quotient.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.RingTheory.Polynomial.Basic

/-!
# Filtered Hilbert functions of affine quotients

The degree filtration is the image of the actual bounded-total-degree polynomial space
in an ideal quotient. Multiplication by an equation outside a prime ideal is injective;
together with the quotient map this gives the principal-cut Hilbert-function inequality.
This is finite-dimensional filtered algebra, without assuming a geometric degree theory.
-/

@[expose] public section

noncomputable section

open MvPolynomial

namespace AffineHilbert

variable {F σ : Type*} [Field F] [Finite σ]

/-- The image in an affine quotient of the polynomials of total degree at most `N`. -/
def quotientDegreeLE (I : Ideal (MvPolynomial σ F)) (N : ℕ) :
    Submodule F (MvPolynomial σ F ⧸ I) :=
  (restrictTotalDegree σ F N).map (Ideal.Quotient.mkₐ F I).toLinearMap

instance quotientDegreeLE_moduleFinite (I : Ideal (MvPolynomial σ F)) (N : ℕ) :
    Module.Finite F (quotientDegreeLE I N) := by
  unfold quotientDegreeLE
  infer_instance

/-- The affine Hilbert function, defined from the actual total-degree filtration on the
polynomial quotient. -/
def hilbertFunction (I : Ideal (MvPolynomial σ F)) (N : ℕ) : ℕ :=
  Module.finrank F (quotientDegreeLE I N)

/-- Every ideal in a finite-variable polynomial ring has a finite generating set with a uniform
total-degree bound. -/
theorem exists_finset_generators_totalDegree_le (I : Ideal (MvPolynomial σ F)) :
    ∃ (s : Finset (MvPolynomial σ F)) (b : ℕ),
      Ideal.span (s : Set (MvPolynomial σ F)) = I ∧ ∀ f ∈ s, f.totalDegree ≤ b := by
  obtain ⟨S, hS_finite, hS_span⟩ :=
    Submodule.fg_def.mp (Ideal.fg_of_isNoetherianRing I)
  rw [Ideal.submodule_span_eq] at hS_span
  have hfinset : ∃ s : Finset (MvPolynomial σ F),
      Ideal.span (s : Set (MvPolynomial σ F)) = I :=
    (Set.exists_finite_iff_finset
      (p := fun T : Set (MvPolynomial σ F) ↦ Ideal.span T = I)).mp
        ⟨S, hS_finite, hS_span⟩
  obtain ⟨s, hs⟩ := hfinset
  refine ⟨s, s.sup totalDegree, hs, fun f hf ↦ ?_⟩
  exact Finset.le_sup hf

private def filteredFactor {I J : Ideal (MvPolynomial σ F)} (hIJ : I ≤ J) (N : ℕ) :
    quotientDegreeLE I N →ₗ[F] quotientDegreeLE J N :=
  ((Ideal.Quotient.factorₐ F hIJ).toLinearMap.domRestrict (quotientDegreeLE I N)).codRestrict
    (quotientDegreeLE J N) (fun x ↦ by
      obtain ⟨p, hp, hpx⟩ := x.property
      refine ⟨p, hp, ?_⟩
      change Ideal.Quotient.mkₐ F J p = Ideal.Quotient.factorₐ F hIJ x
      rw [← hpx]
      rfl)

omit [Finite σ] in
private theorem filteredFactor_surjective {I J : Ideal (MvPolynomial σ F)} (hIJ : I ≤ J)
    (N : ℕ) : Function.Surjective (filteredFactor hIJ N) := by
  intro y
  obtain ⟨p, hp, hpy⟩ := y.property
  let x : quotientDegreeLE I N := ⟨Ideal.Quotient.mkₐ F I p, ⟨p, hp, rfl⟩⟩
  refine ⟨x, Subtype.ext ?_⟩
  change Ideal.Quotient.factorₐ F hIJ (Ideal.Quotient.mkₐ F I p) = y
  rw [← hpy]
  rfl

private def filteredMul {I : Ideal (MvPolynomial σ F)} {f : MvPolynomial σ F} {b N : ℕ}
    (hfdeg : f.totalDegree ≤ b) (hbN : b ≤ N) :
    quotientDegreeLE I (N - b) →ₗ[F] quotientDegreeLE I N :=
  ((LinearMap.mulLeft F (Ideal.Quotient.mkₐ F I f)).domRestrict
      (quotientDegreeLE I (N - b))).codRestrict (quotientDegreeLE I N) (fun x ↦ by
        obtain ⟨p, hp, hpx⟩ := x.property
        refine ⟨f * p, ?_, ?_⟩
        · apply (mem_restrictTotalDegree σ N (f * p)).mpr
          apply (totalDegree_mul f p).trans
          calc
            f.totalDegree + p.totalDegree ≤ b + (N - b) :=
              Nat.add_le_add hfdeg ((mem_restrictTotalDegree σ (N - b) p).mp hp)
            _ = N := Nat.add_sub_of_le hbN
        · change Ideal.Quotient.mkₐ F I (f * p) =
            Ideal.Quotient.mkₐ F I f * x
          rw [map_mul]
          exact congrArg (fun q ↦ Ideal.Quotient.mkₐ F I f * q) hpx)

omit [Finite σ] in
private theorem filteredMul_injective {I : Ideal (MvPolynomial σ F)} (hI : I.IsPrime)
    {f : MvPolynomial σ F} (hfI : f ∉ I) {b N : ℕ}
    (hfdeg : f.totalDegree ≤ b) (hbN : b ≤ N) :
    Function.Injective (filteredMul (I := I) hfdeg hbN) := by
  let _ : I.IsPrime := hI
  intro x y hxy
  apply Subtype.ext
  have hqf : Ideal.Quotient.mk I f ≠ 0 := by
    intro hzero
    exact hfI (Ideal.Quotient.eq_zero_iff_mem.mp hzero)
  apply mul_left_cancel₀ hqf
  have hxy_values := congrArg Subtype.val hxy
  simpa [filteredMul] using hxy_values

omit [Finite σ] in
private theorem filteredFactor_filteredMul_eq_zero {I : Ideal (MvPolynomial σ F)}
    {f : MvPolynomial σ F} {b N : ℕ} (hfdeg : f.totalDegree ≤ b) (hbN : b ≤ N)
    (x : quotientDegreeLE I (N - b)) :
    filteredFactor (show I ≤ I ⊔ Ideal.span {f} from le_sup_left) N
      (filteredMul (I := I) hfdeg hbN x) = 0 := by
  apply Subtype.ext
  simp only [filteredFactor, filteredMul, LinearMap.codRestrict_apply,
    LinearMap.domRestrict_apply, LinearMap.mulLeft_apply]
  have hfzero : Ideal.Quotient.mk (I ⊔ Ideal.span {f}) f = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr
      ((show Ideal.span {f} ≤ I ⊔ Ideal.span {f} from le_sup_right)
        (Ideal.subset_span (Set.mem_singleton f)))
  change Ideal.Quotient.factorₐ F
      (show I ≤ I ⊔ Ideal.span {f} from le_sup_left)
        (Ideal.Quotient.mkₐ F I f * x) = 0
  rw [map_mul]
  change Ideal.Quotient.mk (I ⊔ Ideal.span {f}) f * _ = 0
  rw [hfzero, zero_mul]

/-- Cutting a prime affine quotient by a nonzero polynomial decreases its Hilbert function by
at least the shifted Hilbert function. -/
theorem principalCut_hilbertFunction_add_le {I : Ideal (MvPolynomial σ F)} (hI : I.IsPrime)
    {f : MvPolynomial σ F} (hfI : f ∉ I) {b N : ℕ}
    (hfdeg : f.totalDegree ≤ b) (hbN : b ≤ N) :
    hilbertFunction (I ⊔ Ideal.span {f}) N + hilbertFunction I (N - b) ≤
      hilbertFunction I N := by
  let cut := filteredFactor (show I ≤ I ⊔ Ideal.span {f} from le_sup_left) N
  let mulToKer : quotientDegreeLE I (N - b) →ₗ[F] LinearMap.ker cut :=
    (filteredMul (I := I) hfdeg hbN).codRestrict (LinearMap.ker cut) fun x ↦ by
      exact filteredFactor_filteredMul_eq_zero hfdeg hbN x
  have hmul_injective : Function.Injective mulToKer := by
    intro x y hxy
    apply filteredMul_injective hI hfI hfdeg hbN
    exact congrArg Subtype.val hxy
  have hsmall_le_ker :
      Module.finrank F (quotientDegreeLE I (N - b)) ≤ Module.finrank F (LinearMap.ker cut) :=
    LinearMap.finrank_le_finrank_of_injective hmul_injective
  have hcut_surjective : Function.Surjective cut :=
    filteredFactor_surjective (show I ≤ I ⊔ Ideal.span {f} from le_sup_left) N
  have hrank := cut.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hcut_surjective, finrank_top] at hrank
  unfold hilbertFunction
  omega

end AffineHilbert

/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import ArkLib.ToMathlib.AlgebraicGeometry.PrincipalOpen.Filtration
public import Mathlib.Data.Finsupp.Option

/-!
# A finite-type presentation of a principal localization

The extra variable in `MvPolynomial (Option σ) F` maps to the inverse of the localized
element.  Its ordinary total-degree filtration is compared in both directions with the concrete
bounded numerator-and-denominator filtration.  Passing through the kernel quotient identifies
this presentation filtration with an actual affine Hilbert function.
-/

@[expose] public section

noncomputable section

open MvPolynomial
open scoped BigOperators

namespace AffineHilbert

variable {F σ : Type*} [Field F] [Finite σ]

private abbrev PresentationCoordinateRing (I : Ideal (MvPolynomial σ F)) :=
  MvPolynomial σ F ⧸ I

private abbrev PresentationAwayRing (I : Ideal (MvPolynomial σ F))
    (s : MvPolynomial σ F) :=
  Localization.Away (Ideal.Quotient.mk I s)

/-- The explicit affine presentation of the principal localization: the new `none` variable is
sent to `s⁻¹`, and the old `some i` variables are sent to their quotient classes. -/
def awayPresentationHom (I : Ideal (MvPolynomial σ F)) (s : MvPolynomial σ F) :
    MvPolynomial (Option σ) F →ₐ[F] Localization.Away (Ideal.Quotient.mk I s) :=
  MvPolynomial.eval₂AlgHom F fun
    | none => IsLocalization.Away.invSelf (Ideal.Quotient.mk I s)
    | some i => algebraMap ((MvPolynomial σ F ⧸ I)) (Localization.Away (Ideal.Quotient.mk I s))
        (Ideal.Quotient.mk I (MvPolynomial.X i))

/-- The total-degree filtration from the explicit finite-type presentation of the localization. -/
def awayPresentationDegreeLE (I : Ideal (MvPolynomial σ F))
    (s : MvPolynomial σ F) (N : ℕ) : Submodule F (Localization.Away (Ideal.Quotient.mk I s)) :=
  (restrictTotalDegree (Option σ) F N).map (awayPresentationHom I s).toLinearMap

instance awayPresentationDegreeLE_moduleFinite (I : Ideal (MvPolynomial σ F))
    (s : MvPolynomial σ F) (N : ℕ) : Module.Finite F (awayPresentationDegreeLE I s N) := by
  unfold awayPresentationDegreeLE
  infer_instance

omit [Finite σ] in
/-- Renaming the original variables into the presentation evaluates to the quotient numerator. -/
theorem awayPresentationHom_rename_some (I : Ideal (MvPolynomial σ F))
    (s : MvPolynomial σ F) (p : MvPolynomial σ F) :
    awayPresentationHom I s (MvPolynomial.rename some p) =
      algebraMap ((MvPolynomial σ F ⧸ I)) (Localization.Away (Ideal.Quotient.mk I s))
        (Ideal.Quotient.mk I p) := by
  have heq : (awayPresentationHom I s).comp (MvPolynomial.rename some) =
      (IsScalarTower.toAlgHom F (MvPolynomial σ F ⧸ I)
        (Localization.Away (Ideal.Quotient.mk I s))).comp
        (Ideal.Quotient.mkₐ F I) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp [awayPresentationHom]
  exact DFunLike.congr_fun heq p

omit [Finite σ] in
/-- Evaluation of one term in the bounded numerator-and-denominator filtration. -/
theorem awayTermMap_apply (I : Ideal (MvPolynomial σ F)) (s : MvPolynomial σ F)
    (N e : ℕ) (q : quotientDegreeLE I N) :
    awayTermMap I s N e q =
      algebraMap (MvPolynomial σ F ⧸ I) (Localization.Away (Ideal.Quotient.mk I s)) q.1 *
        IsLocalization.Away.invSelf (Ideal.Quotient.mk I s) ^ e := by
  rfl

omit [Finite σ] in
/-- Split an option-indexed monomial into its original-variable part and inverse-variable power. -/
lemma monomial_option_factor (u : Option σ →₀ ℕ) (c : F) :
    MvPolynomial.monomial u c =
      MvPolynomial.rename some (MvPolynomial.monomial u.some c) *
        MvPolynomial.X none ^ u none := by
  have hu : Finsupp.mapDomain some u.some + Finsupp.single none (u none) = u := by
    ext x
    cases x with
    | none =>
        simp only [Finsupp.add_apply]
        rw [Finsupp.mapDomain_of_notMem_range]
        · simp
        · simp
    | some x =>
        simp only [Finsupp.add_apply]
        rw [Finsupp.mapDomain_apply (@Option.some_injective σ)]
        simp
  calc
    MvPolynomial.monomial u c =
        MvPolynomial.monomial
          (Finsupp.mapDomain some u.some + Finsupp.single none (u none)) c := by
      rw [hu]
    _ = MvPolynomial.monomial (Finsupp.mapDomain some u.some) c *
          MvPolynomial.X none ^ u none := MvPolynomial.monomial_add_single
    _ = MvPolynomial.rename some (MvPolynomial.monomial u.some c) *
          MvPolynomial.X none ^ u none := by
      rw [MvPolynomial.rename_monomial]

omit [Finite σ] in
/-- A presentation monomial of total degree at most `N` belongs to the degree-`N` box. -/
lemma awayPresentationHom_monomial_mem_awayDegreeLE
    (I : Ideal (MvPolynomial σ F)) (s : MvPolynomial σ F) (N : ℕ)
    (u : Option σ →₀ ℕ) (c : F)
    (hu : u.sum (fun _ e ↦ e) ≤ N) :
    awayPresentationHom I s (MvPolynomial.monomial u c) ∈ awayDegreeLE I s N := by
  have husum : u none + u.some.sum (fun _ e ↦ e) = u.sum (fun _ e ↦ e) := by
    symm
    simpa using u.sum_option_index (fun _ e ↦ e) (by simp) (by simp)
  have hunone : u none ≤ N := by omega
  have husome : u.some.sum (fun _ e ↦ e) ≤ N := by omega
  have hpdeg : (MvPolynomial.monomial u.some c).totalDegree ≤ N :=
    (MvPolynomial.totalDegree_monomial_le _ _).trans husome
  let q : quotientDegreeLE I N := ⟨Ideal.Quotient.mk I (MvPolynomial.monomial u.some c),
    ⟨MvPolynomial.monomial u.some c,
      (mem_restrictTotalDegree σ N _).mpr hpdeg, rfl⟩⟩
  refine Submodule.mem_iSup_of_mem ⟨u none, by omega⟩ ?_
  refine ⟨q, ?_⟩
  rw [awayTermMap_apply, monomial_option_factor, map_mul, map_pow,
    awayPresentationHom_rename_some]
  simp only [awayPresentationHom, MvPolynomial.eval₂AlgHom_X]
  rfl

omit [Finite σ] in
/-- Presentation total degree at most `N` is contained in the box filtration at the same bound. -/
theorem awayPresentationDegreeLE_le_awayDegreeLE
    (I : Ideal (MvPolynomial σ F)) (s : MvPolynomial σ F) (N : ℕ) :
    awayPresentationDegreeLE I s N ≤ awayDegreeLE I s N := by
  rintro _ ⟨p, hp, rfl⟩
  have hpdeg : p.totalDegree ≤ N := (mem_restrictTotalDegree (Option σ) N p).mp hp
  rw [p.as_sum, map_sum]
  refine Submodule.sum_mem _ fun u hu ↦ ?_
  exact awayPresentationHom_monomial_mem_awayDegreeLE I s N u (p.coeff u)
    ((MvPolynomial.le_totalDegree hu).trans hpdeg)

omit [Finite σ] in
/-- The explicit polynomial presentation maps onto the principal localization. -/
theorem awayPresentationHom_surjective (I : Ideal (MvPolynomial σ F))
    (s : MvPolynomial σ F) : Function.Surjective (awayPresentationHom I s) := by
  intro z
  obtain ⟨n, a, hz⟩ := IsLocalization.Away.surj (Ideal.Quotient.mk I s) z
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
  refine ⟨MvPolynomial.rename some p * MvPolynomial.X none ^ n, ?_⟩
  rw [map_mul, map_pow, awayPresentationHom_rename_some]
  simp only [awayPresentationHom, MvPolynomial.eval₂AlgHom_X]
  have hz' := congrArg
    (fun w : Localization.Away (Ideal.Quotient.mk I s) ↦
      w * IsLocalization.Away.invSelf (Ideal.Quotient.mk I s) ^ n) hz
  simpa [← mul_pow, IsLocalization.Away.mul_invSelf, mul_assoc] using hz'.symm

/-- The defining ideal of the explicit affine presentation of the localization. -/
def awayPresentationIdeal (I : Ideal (MvPolynomial σ F)) (s : MvPolynomial σ F) :
    Ideal (MvPolynomial (Option σ) F) :=
  RingHom.ker (awayPresentationHom I s).toRingHom

/-- The quotient by the defining ideal is the principal localization. -/
def awayPresentationEquiv (I : Ideal (MvPolynomial σ F)) (s : MvPolynomial σ F) :
    (MvPolynomial (Option σ) F ⧸ awayPresentationIdeal I s) ≃ₐ[F]
      Localization.Away (Ideal.Quotient.mk I s) :=
  Ideal.quotientKerAlgEquivOfSurjective (awayPresentationHom_surjective I s)

omit [Finite σ] in
/-- The presentation filtration is the image of the kernel quotient's degree filtration. -/
theorem awayPresentationDegreeLE_eq_map_quotientDegreeLE
    (I : Ideal (MvPolynomial σ F)) (s : MvPolynomial σ F) (N : ℕ) :
    awayPresentationDegreeLE I s N =
      (quotientDegreeLE (awayPresentationIdeal I s) N).map
        (awayPresentationEquiv I s).toLinearMap := by
  have hcomp :
      (awayPresentationEquiv I s).toLinearMap.comp
          (Ideal.Quotient.mkₐ F (awayPresentationIdeal I s)).toLinearMap =
        (awayPresentationHom I s).toLinearMap := by
    apply LinearMap.ext
    intro p
    exact Ideal.quotientKerAlgEquivOfSurjective_mk
      (awayPresentationHom_surjective I s) p
  rw [awayPresentationDegreeLE, quotientDegreeLE, ← Submodule.map_comp]
  rw [hcomp]

omit [Finite σ] in
/-- Every box-filtered fraction has presentation total degree at most `2N`. -/
theorem awayDegreeLE_le_awayPresentationDegreeLE_two_mul
    (I : Ideal (MvPolynomial σ F)) (s : MvPolynomial σ F) (N : ℕ) :
    awayDegreeLE I s N ≤ awayPresentationDegreeLE I s (2 * N) := by
  rw [awayDegreeLE]
  apply iSup_le
  intro e
  rintro _ ⟨q, rfl⟩
  obtain ⟨p, hp, hpq⟩ := q.property
  have hpdeg : p.totalDegree ≤ N := (mem_restrictTotalDegree σ N p).mp hp
  let t : MvPolynomial (Option σ) F :=
    MvPolynomial.rename some p * MvPolynomial.X none ^ e.val
  have htdeg : t.totalDegree ≤ 2 * N := by
    dsimp only [t]
    refine (totalDegree_mul _ _).trans ?_
    rw [totalDegree_X_pow]
    calc
      (MvPolynomial.rename some p).totalDegree + e.val ≤ N + N :=
        Nat.add_le_add ((totalDegree_rename_le some p).trans hpdeg) (by omega)
      _ = 2 * N := by omega
  rw [awayPresentationDegreeLE, Submodule.mem_map]
  refine ⟨t, (mem_restrictTotalDegree (Option σ) (2 * N) t).mpr htdeg, ?_⟩
  change awayPresentationHom I s t = awayTermMap I s N e.val q
  dsimp only [t]
  rw [map_mul, map_pow, awayPresentationHom_rename_some]
  rw [awayTermMap_apply]
  simp only [awayPresentationHom, MvPolynomial.eval₂AlgHom_X]
  exact congrArg
    (fun x : MvPolynomial σ F ⧸ I ↦
      algebraMap (MvPolynomial σ F ⧸ I) (Localization.Away (Ideal.Quotient.mk I s)) x *
        IsLocalization.Away.invSelf (Ideal.Quotient.mk I s) ^ e.val) hpq

omit [Finite σ] in
/-- The presentation filtration has exactly the Hilbert function of its kernel ideal. -/
theorem finrank_awayPresentationDegreeLE_eq_hilbertFunction
    (I : Ideal (MvPolynomial σ F)) (s : MvPolynomial σ F) (N : ℕ) :
    Module.finrank F (awayPresentationDegreeLE I s N) =
      hilbertFunction (awayPresentationIdeal I s) N := by
  rw [awayPresentationDegreeLE_eq_map_quotientDegreeLE, hilbertFunction]
  exact (awayPresentationEquiv I s).toLinearEquiv.finrank_map_eq _

/-- The Hilbert function of the original prime quotient is bounded by the localization
presentation Hilbert function after doubling the degree. -/
theorem hilbertFunction_le_awayPresentation_hilbertFunction_two_mul
    {I : Ideal (MvPolynomial σ F)} (hI : I.IsPrime) {s : MvPolynomial σ F} (hs : s ∉ I)
    (N : ℕ) :
    hilbertFunction I N ≤ hilbertFunction (awayPresentationIdeal I s) (2 * N) := by
  calc
    hilbertFunction I N ≤ Module.finrank F (awayDegreeLE I s N) :=
      (hilbertFunction_le_finrank_awayDegreeLE_le hI hs N).1
    _ ≤ Module.finrank F (awayPresentationDegreeLE I s (2 * N)) :=
      Submodule.finrank_mono (awayDegreeLE_le_awayPresentationDegreeLE_two_mul I s N)
    _ = hilbertFunction (awayPresentationIdeal I s) (2 * N) :=
      finrank_awayPresentationDegreeLE_eq_hilbertFunction I s (2 * N)

/-- The localization presentation Hilbert function is bounded by the original quotient Hilbert
function after the explicit linear rescaling `N ↦ N + N·deg(s)`. -/
theorem awayPresentation_hilbertFunction_le_hilbertFunction_rescaled
    {I : Ideal (MvPolynomial σ F)} (hI : I.IsPrime) {s : MvPolynomial σ F} (hs : s ∉ I)
    (N : ℕ) :
    hilbertFunction (awayPresentationIdeal I s) N ≤
      hilbertFunction I (N + N * s.totalDegree) := by
  let inclusion : awayDegreeLE I s N →ₗ[F] awayPresentationDegreeLE I s (2 * N) :=
    Submodule.inclusion (awayDegreeLE_le_awayPresentationDegreeLE_two_mul I s N)
  let _ : Module.Finite F (awayDegreeLE I s N) :=
    Module.Finite.of_injective inclusion (Submodule.inclusion_injective _)
  calc
    hilbertFunction (awayPresentationIdeal I s) N =
        Module.finrank F (awayPresentationDegreeLE I s N) :=
      (finrank_awayPresentationDegreeLE_eq_hilbertFunction I s N).symm
    _ ≤ Module.finrank F (awayDegreeLE I s N) :=
      Submodule.finrank_mono (awayPresentationDegreeLE_le_awayDegreeLE I s N)
    _ ≤ hilbertFunction I (N + N * s.totalDegree) :=
      (hilbertFunction_le_finrank_awayDegreeLE_le hI hs N).2

end AffineHilbert

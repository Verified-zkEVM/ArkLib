/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.ToCompPoly.Multivariate.PartialDerivative
public import ArkLib.ToCompPoly.Multivariate.Substitution
public import Mathlib.Algebra.MvPolynomial.Monad

/-!
# Affine cover by simultaneous scalar translations

For `s` variables, any explicit list of more than `s` distinct scalars covers
every affine point: one scalar differs from all `s` coordinates.  Translating
all coordinates by that scalar moves the point into the torus.  This is the
unconditional affine-chart cover used before a toric eliminant construction.

The list of shifts is runtime input.  A caller over a small base field may
construct it in a sufficiently large explicit extension; this module does not
enumerate a field or assume an oracle producing distinct elements.
-/

@[expose] public section

namespace ArkLib.Rojas.AffineCover

open CPoly CPoly.CMvPolynomial

variable {F : Type*} [Field F] [BEq F] [LawfulBEq F]
variable {s : ℕ}

/-- Translate a point from original coordinates to the chart centered at `c`. -/
def translatePoint (c : F) (x : Fin s → F) : Fin s → F := fun i ↦ x i - c

/-- Return from the chart centered at `c` to original coordinates. -/
def inverseTranslatePoint (c : F) (y : Fin s → F) : Fin s → F := fun i ↦ y i + c

omit [BEq F] [LawfulBEq F] in
@[simp]
theorem inverseTranslatePoint_translatePoint (c : F) (x : Fin s → F) :
    inverseTranslatePoint c (translatePoint c x) = x := by
  funext i
  simp [inverseTranslatePoint, translatePoint]

omit [BEq F] [LawfulBEq F] in
@[simp]
theorem translatePoint_inverseTranslatePoint (c : F) (y : Fin s → F) :
    translatePoint c (inverseTranslatePoint c y) = y := by
  funext i
  simp [inverseTranslatePoint, translatePoint]

/-- Substitute `xᵢ = yᵢ + c` in a computable multivariate polynomial. -/
def translatePolynomial (c : F) (polynomial : CMvPolynomial s F) : CMvPolynomial s F :=
  bind₁ (fun i ↦ X i + C c) polynomial

/-- Translate every equation of a polynomial system by the same scalar. -/
def translateSystem (c : F) (system : List (CMvPolynomial s F)) :
    List (CMvPolynomial s F) :=
  system.map (translatePolynomial c)

/-- Produce all translated charts associated with an explicit shift list. -/
def cover (shifts : List F) (system : List (CMvPolynomial s F)) :
    List (F × List (CMvPolynomial s F)) :=
  shifts.map fun c ↦ (c, translateSystem c system)

/-- All equations in a computable system vanish at a point. -/
def VanishesAt {K : Type*} [Field K] (ι : F →+* K) (x : Fin s → K)
    (system : List (CMvPolynomial s F)) : Prop :=
  ∀ polynomial ∈ system, polynomial.eval₂ ι x = 0

/-- A point has no zero coordinates. -/
def InTorus {K : Type*} [Field K] (x : Fin s → K) : Prop := ∀ i, x i ≠ 0

/-- The evaluated Jacobian, represented as one gradient row per equation. -/
def jacobianAt {K : Type*} [Field K] (ι : F →+* K) (x : Fin s → K)
    (system : List (CMvPolynomial s F)) : List (Fin s → K) :=
  system.map fun polynomial j ↦ (partialDerivative j polynomial).eval₂ ι x

/-- Algebraic interpretation of executable affine translation. -/
theorem fromCMvPolynomial_translatePolynomial (c : F)
    (polynomial : CMvPolynomial s F) :
    fromCMvPolynomial (translatePolynomial c polynomial) =
      MvPolynomial.bind₁ (fun i ↦ MvPolynomial.X i + MvPolynomial.C c)
        (fromCMvPolynomial polynomial) := by
  simp [translatePolynomial, fromCMvPolynomial_bind₁, MvPolynomial.aeval_eq_bind₁,
    CPoly.map_add, fromCMvPolynomial_X, fromCMvPolynomial_C]

/-- Evaluation after symbolic translation equals evaluation at the
inverse-translated point. -/
theorem eval₂_translatePolynomial
    {K : Type*} [Field K] (ι : F →+* K) (y : Fin s → K)
    (c : F) (polynomial : CMvPolynomial s F) :
    (translatePolynomial c polynomial).eval₂ ι y =
      polynomial.eval₂ ι (inverseTranslatePoint (ι c) y) := by
  rw [CPoly.eval₂_equiv, CPoly.eval₂_equiv, translatePolynomial,
    fromCMvPolynomial_bind₁, MvPolynomial.aeval_eq_bind₁]
  change MvPolynomial.eval₂Hom ι y
      (MvPolynomial.bind₁
        (fun i ↦ fromCMvPolynomial (X i + C c)) (fromCMvPolynomial polynomial)) =
    MvPolynomial.eval₂Hom ι (inverseTranslatePoint (ι c) y)
      (fromCMvPolynomial polynomial)
  rw [MvPolynomial.eval₂Hom_bind₁]
  congr 1
  apply MvPolynomial.ringHom_ext
  · intro r
    simp
  · intro i
    simp [CPoly.map_add, fromCMvPolynomial_X, fromCMvPolynomial_C,
      inverseTranslatePoint]

/-- A translated equation vanishes at the translated original point exactly
when the original equation vanishes. -/
theorem eval₂_translatePolynomial_at_translatePoint
    {K : Type*} [Field K] (ι : F →+* K) (x : Fin s → K)
    (c : F) (polynomial : CMvPolynomial s F) :
    (translatePolynomial c polynomial).eval₂ ι (translatePoint (ι c) x) =
      polynomial.eval₂ ι x := by
  rw [eval₂_translatePolynomial]
  simp

/-- Simultaneous translation preserves the root predicate in both
directions. -/
theorem vanishesAt_translateSystem_iff
    {K : Type*} [Field K] (ι : F →+* K) (y : Fin s → K)
    (c : F) (system : List (CMvPolynomial s F)) :
    VanishesAt ι y (translateSystem c system) ↔
      VanishesAt ι (inverseTranslatePoint (ι c) y) system := by
  constructor
  · intro hroot polynomial hpolynomial
    have htranslated := hroot (translatePolynomial c polynomial) <| by
      exact List.mem_map.mpr ⟨polynomial, hpolynomial, rfl⟩
    rw [eval₂_translatePolynomial] at htranslated
    exact htranslated
  · intro hroot translated htranslated
    obtain ⟨polynomial, hpolynomial, rfl⟩ := List.mem_map.mp htranslated
    rw [eval₂_translatePolynomial]
    exact hroot polynomial hpolynomial

/-- Root equivalence at corresponding original and translated points. -/
theorem vanishesAt_translateSystem_at_translatePoint_iff
    {K : Type*} [Field K] (ι : F →+* K) (x : Fin s → K)
    (c : F) (system : List (CMvPolynomial s F)) :
    VanishesAt ι (translatePoint (ι c) x) (translateSystem c system) ↔
      VanishesAt ι x system := by
  rw [vanishesAt_translateSystem_iff]
  simp

omit [BEq F] [LawfulBEq F] in
/-- Partial differentiation commutes with simultaneous scalar translation. -/
theorem pderiv_affine_bind (c : F) (j : Fin s)
    (polynomial : MvPolynomial (Fin s) F) :
    MvPolynomial.pderiv j
        (MvPolynomial.bind₁ (fun i ↦ MvPolynomial.X i + MvPolynomial.C c) polynomial) =
      MvPolynomial.bind₁ (fun i ↦ MvPolynomial.X i + MvPolynomial.C c)
        (MvPolynomial.pderiv j polynomial) := by
  classical
  induction polynomial using MvPolynomial.induction_on with
  | C coefficient => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp =>
      by_cases hij : i = j
      · subst i
        simp [hp]
      · simp [MvPolynomial.pderiv_X_of_ne hij, hp]

/-- Executable partial differentiation commutes with executable affine
translation. -/
theorem partialDerivative_translatePolynomial (c : F) (j : Fin s)
    (polynomial : CMvPolynomial s F) :
    partialDerivative j (translatePolynomial c polynomial) =
      translatePolynomial c (partialDerivative j polynomial) := by
  apply fromCMvPolynomial_injective
  rw [fromCMvPolynomial_partialDerivative,
    fromCMvPolynomial_translatePolynomial, pderiv_affine_bind,
    fromCMvPolynomial_translatePolynomial,
    fromCMvPolynomial_partialDerivative]

/-- The computable Jacobian entry of a translated polynomial evaluates to the
original Jacobian entry at the inverse-translated point. -/
theorem eval₂_partialDerivative_translatePolynomial
    {K : Type*} [Field K] (ι : F →+* K) (y : Fin s → K)
    (c : F) (j : Fin s) (polynomial : CMvPolynomial s F) :
    (partialDerivative j (translatePolynomial c polynomial)).eval₂ ι y =
      (partialDerivative j polynomial).eval₂ ι
        (inverseTranslatePoint (ι c) y) := by
  rw [partialDerivative_translatePolynomial, eval₂_translatePolynomial]

/-- Simultaneous translation preserves every evaluated Jacobian entry. -/
theorem jacobianAt_translateSystem
    {K : Type*} [Field K] (ι : F →+* K) (y : Fin s → K)
    (c : F) (system : List (CMvPolynomial s F)) :
    jacobianAt ι y (translateSystem c system) =
      jacobianAt ι (inverseTranslatePoint (ι c) y) system := by
  simp [jacobianAt, translateSystem,
    eval₂_partialDerivative_translatePolynomial]

/-- Jacobian equality at corresponding original and translated points. -/
theorem jacobianAt_translateSystem_at_translatePoint
    {K : Type*} [Field K] (ι : F →+* K) (x : Fin s → K)
    (c : F) (system : List (CMvPolynomial s F)) :
    jacobianAt ι (translatePoint (ι c) x) (translateSystem c system) =
      jacobianAt ι x system := by
  rw [jacobianAt_translateSystem]
  simp

omit [BEq F] [LawfulBEq F] in
/-- More than `s` distinct scalars contain one which differs from all `s`
coordinates of a given point. -/
theorem exists_shift_avoiding_coordinates
    (shifts : List F) (hnodup : shifts.Nodup) (hlength : s < shifts.length)
    (x : Fin s → F) :
    ∃ c ∈ shifts, ∀ i, x i - c ≠ 0 := by
  classical
  by_contra hcontra
  simp only [not_exists, not_and, not_forall, not_not] at hcontra
  have hsubset : shifts.toFinset ⊆ Finset.univ.image x := by
    intro c hc
    have hmem : c ∈ shifts := by simpa using hc
    obtain ⟨i, hi⟩ := hcontra c hmem
    have hxi : x i = c := sub_eq_zero.mp hi
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, hxi⟩
  have hcard : shifts.length ≤ s := by
    rw [← List.toFinset_card_of_nodup hnodup]
    exact (Finset.card_le_card hsubset).trans <| by
      simpa using Finset.card_image_le (s := Finset.univ) (f := x)
  omega

omit [BEq F] [LawfulBEq F] in
/-- The same pigeonhole cover holds for points over any coefficient-field
extension, because a field homomorphism is injective. -/
theorem exists_shift_avoiding_coordinates_extension
    (shifts : List F) (hnodup : shifts.Nodup) (hlength : s < shifts.length)
    {K : Type*} [Field K] (ι : F →+* K) (x : Fin s → K) :
    ∃ c ∈ shifts, InTorus (translatePoint (ι c) x) := by
  have hmapped : (shifts.map ι).Nodup := hnodup.map ι.injective
  obtain ⟨d, hd, havoid⟩ := exists_shift_avoiding_coordinates
    (shifts.map ι) hmapped (by simpa using hlength) x
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hd
  exact ⟨c, hc, havoid⟩

/-- Every affine root is represented by at least one translated torus chart,
and the corresponding Jacobian is unchanged after inverse translation. -/
theorem exists_torus_chart_of_vanishesAt
    (shifts : List F) (hnodup : shifts.Nodup) (hlength : s < shifts.length)
    {K : Type*} [Field K] (ι : F →+* K) (x : Fin s → K)
    (system : List (CMvPolynomial s F)) (hroot : VanishesAt ι x system) :
    ∃ c ∈ shifts,
      (c, translateSystem c system) ∈ cover shifts system ∧
      InTorus (translatePoint (ι c) x) ∧
      VanishesAt ι (translatePoint (ι c) x) (translateSystem c system) ∧
      jacobianAt ι (translatePoint (ι c) x) (translateSystem c system) =
        jacobianAt ι x system := by
  obtain ⟨c, hc, htorus⟩ :=
    exists_shift_avoiding_coordinates_extension shifts hnodup hlength ι x
  refine ⟨c, hc, ?_, htorus, ?_, ?_⟩
  · exact List.mem_map.mpr ⟨c, hc, rfl⟩
  · rw [vanishesAt_translateSystem_iff]
    simpa using hroot
  · rw [jacobianAt_translateSystem]
    simp

end ArkLib.Rojas.AffineCover

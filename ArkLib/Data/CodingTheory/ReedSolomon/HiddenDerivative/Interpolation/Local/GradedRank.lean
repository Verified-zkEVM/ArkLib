/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.SourceMonomial
public import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.Local.Translation
public import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

/-!
# The graded image of the local constraint map

At the origin, the hidden-derivative substitution preserves total jet degree when both the
visible local jets and the remainder variable `E` have degree one and the displacement `T` has
degree zero. Consequently, a source monomial of jet degree `t` can contribute only to local
rows of the same degree. This is the grading that supplies the row profile for shifted symbolic
interpolation.

Translation in the global `X` and `Y₀` coordinates is triangular for this grading: it can lower
total jet degree but cannot raise it. The final theorem exposes that support fact independently
of the older asymmetric-band predicates.
-/

@[expose] public section

open PolynomialDifferential

namespace ReedSolomon.HiddenDerivative

noncomputable section

open MvPolynomial
open scoped BigOperators

variable {R : Type*} [CommRing R] {d m : ℕ}

/-- Weight one on every global jet variable and zero on the ordinary variable `X`. -/
def sourceJetDegreeWeight : JetVariable d → ℕ
  | none => 0
  | some _ => 1

/-- Weight one on the local remainder and visible jets and zero on the displacement `T`. -/
def localJetDegreeWeight : LocalVariable d → ℕ
  | none => 0
  | some _ => 1

/-- Total local jet degree, counting the remainder `E` as one jet variable. -/
def localJetDegree (e : LocalVariable d →₀ ℕ) : ℕ :=
  Finsupp.weight (localJetDegreeWeight (d := d)) e

/-- The weight formulation of source jet degree agrees with `totalJetDegree`. -/
theorem sourceJetDegreeWeight_eq_totalJetDegree (u : JetVariable d →₀ ℕ) :
    Finsupp.weight (sourceJetDegreeWeight (d := d)) u = totalJetDegree u := by
  simp [sourceJetDegreeWeight, totalJetDegree, Finsupp.weight_eq_sum,
    Finsupp.degree_eq_sum, Fintype.sum_option]

/-- Every monomial of the local correction has local jet degree one. -/
theorem localCorrection_isWeightedHomogeneous (d : ℕ) :
    (localCorrection (R := R) d).IsWeightedHomogeneous
      (localJetDegreeWeight (d := d)) 1 := by
  rw [← mem_weightedHomogeneousSubmodule]
  apply Submodule.sum_mem
  intro j _
  rw [mem_weightedHomogeneousSubmodule]
  have hC := isWeightedHomogeneous_C
    (localJetDegreeWeight (d := d)) ((-1 : R) ^ j.val)
  have hT := isWeightedHomogeneous_X
    (R := R) (localJetDegreeWeight (d := d)) (localT d)
  have hY := isWeightedHomogeneous_X
    (R := R) (localJetDegreeWeight (d := d)) (localY j)
  simpa [localCorrection, localJetDegreeWeight, localT, localY, zero_add] using
    (hC.mul (hT.pow (j.val + 1))).mul hY

/-- At the origin, the image of `Y₀` is homogeneous of local jet degree one. -/
theorem unscaledLocalSubstitution_zero_Y_zero_isWeightedHomogeneous (d : ℕ) :
    (unscaledLocalSubstitution (R := R) d 0 0 (X (some 0))).IsWeightedHomogeneous
      (localJetDegreeWeight (d := d)) 1 := by
  rw [unscaledLocalSubstitution_Y_zero]
  have hcorrection := localCorrection_isWeightedHomogeneous (R := R) d
  have hT := isWeightedHomogeneous_X
    (R := R) (localJetDegreeWeight (d := d)) (localT d)
  have hE := isWeightedHomogeneous_X
    (R := R) (localJetDegreeWeight (d := d)) (localE d)
  simpa [localJetDegreeWeight] using
    (isWeightedHomogeneous_zero R (localJetDegreeWeight (d := d)) 1).add
      hcorrection |>.add (hT.mul hE)

/-- The complete origin image of a source monomial is homogeneous of its total jet degree. -/
theorem unscaledLocalSubstitution_zero_sourceMonomial_isWeightedHomogeneous
    (x b : ℕ) (higher : Fin d → ℕ) :
    (unscaledLocalSubstitution (R := R) d 0 0
      (sourceMonomial x b higher)).IsWeightedHomogeneous
        (localJetDegreeWeight (d := d)) (b + ∑ j, higher j) := by
  have hX := isWeightedHomogeneous_X
    (R := R) (localJetDegreeWeight (d := d)) (localT d)
  have hY₀ := unscaledLocalSubstitution_zero_Y_zero_isWeightedHomogeneous (R := R) d
  have hhigher : (∏ j, X (localY j) ^ higher j : LocalPolynomial R d).IsWeightedHomogeneous
      (localJetDegreeWeight (d := d)) (∑ j, higher j) := by
    apply MvPolynomial.IsWeightedHomogeneous.prod
    intro j _
    simpa [localJetDegreeWeight, localY] using
      (isWeightedHomogeneous_X
        (R := R) (localJetDegreeWeight (d := d)) (localY j)).pow (higher j)
  simp only [sourceMonomial, map_mul, map_pow, map_prod,
    unscaledLocalSubstitution_X, unscaledLocalSubstitution_Y_zero,
    unscaledLocalSubstitution_Y_succ]
  simpa [localJetDegreeWeight, localT, zero_nsmul, zero_add, add_assoc] using
    ((hX.pow x).mul (hY₀.pow b)).mul hhigher

/-- The projected origin constraint remains homogeneous of the source monomial's jet degree. -/
theorem localConstraintAt_zero_sourceMonomial_isWeightedHomogeneous
    (x b : ℕ) (higher : Fin d → ℕ) :
    (localConstraintAt (R := R) (d := d) m 0 0
      (sourceMonomial x b higher)).IsWeightedHomogeneous
        (localJetDegreeWeight (d := d)) (b + ∑ j, higher j) := by
  intro e he
  apply unscaledLocalSubstitution_zero_sourceMonomial_isWeightedHomogeneous
    (R := R) x b higher
  rw [localConstraintAt, LinearMap.comp_apply, AlgHom.toLinearMap_apply,
    projectLowContact, coeff_filterLocalMonomials] at he
  split at he
  · exact he
  · simp at he

/-- The origin substitution sends each global generator to the local block of the same jet
degree. -/
theorem unscaledLocalSubstitution_zero_X_isWeightedHomogeneous (v : JetVariable d) :
    (unscaledLocalSubstitution (R := R) d 0 0 (X v)).IsWeightedHomogeneous
      (localJetDegreeWeight (d := d)) (sourceJetDegreeWeight v) := by
  rcases v with _ | j
  · simpa [sourceJetDegreeWeight, localJetDegreeWeight, localT] using
      (isWeightedHomogeneous_X
        (R := R) (localJetDegreeWeight (d := d)) (localT d))
  · induction j using Fin.cases with
    | zero =>
        simpa [sourceJetDegreeWeight] using
          unscaledLocalSubstitution_zero_Y_zero_isWeightedHomogeneous (R := R) d
    | succ j =>
        simpa [sourceJetDegreeWeight, localJetDegreeWeight, localY] using
          (isWeightedHomogeneous_X
            (R := R) (localJetDegreeWeight (d := d)) (localY j))

/-- The origin image of an arbitrary global monomial is homogeneous of its source jet weight. -/
theorem unscaledLocalSubstitution_zero_monomial_isWeightedHomogeneous
    (u : JetVariable d →₀ ℕ) (a : R) :
    (unscaledLocalSubstitution (R := R) d 0 0 (monomial u a)).IsWeightedHomogeneous
      (localJetDegreeWeight (d := d))
      (Finsupp.weight (sourceJetDegreeWeight (d := d)) u) := by
  rw [unscaledLocalSubstitution, MvPolynomial.bind₁_monomial]
  have hprod : (∏ i ∈ u.support, unscaledLocalImage d 0 0 i ^ u i :
      LocalPolynomial R d).IsWeightedHomogeneous (localJetDegreeWeight (d := d))
        (∑ i ∈ u.support, u i • sourceJetDegreeWeight i) := by
    apply MvPolynomial.IsWeightedHomogeneous.prod
    intro i _
    simpa [unscaledLocalSubstitution] using
      (unscaledLocalSubstitution_zero_X_isWeightedHomogeneous
        (R := R) i).pow (u i)
  simpa only [zero_add, Finsupp.weight_apply, Finsupp.sum] using
    (isWeightedHomogeneous_C (localJetDegreeWeight (d := d)) a).mul hprod

/-- The origin local constraint sends every homogeneous polynomial to the matching local block. -/
theorem localConstraintAt_zero_isWeightedHomogeneous {Q : DifferentialPolynomial R d} {t : ℕ}
    (hQ : Q.IsWeightedHomogeneous (sourceJetDegreeWeight (d := d)) t) :
    (localConstraintAt (R := R) (d := d) m 0 0 Q).IsWeightedHomogeneous
      (localJetDegreeWeight (d := d)) t := by
  induction hQ using MvPolynomial.IsWeightedHomogeneous.induction_on with
  | zero => simp [isWeightedHomogeneous_zero]
  | add P Q hP hQ ihP ihQ =>
      simpa using ihP.add ihQ
  | monomial u a hu =>
      intro e he
      have hsubstitution := unscaledLocalSubstitution_zero_monomial_isWeightedHomogeneous
        (R := R) u a
      rw [localConstraintAt, LinearMap.comp_apply, AlgHom.toLinearMap_apply,
        projectLowContact, coeff_filterLocalMonomials] at he
      split at he
      · simpa [hu] using hsubstitution he
      · simp at he

/-- The source block of total jet degree `t`. -/
def sourceJetGrade (R : Type*) [CommRing R] (d t : ℕ) :
    Submodule R (DifferentialPolynomial R d) :=
  weightedHomogeneousSubmodule R (sourceJetDegreeWeight (d := d)) t

/-- The local block of total jet degree `t`, with `E` counted as degree one. -/
def localJetGrade (R : Type*) [CommRing R] (d t : ℕ) :
    Submodule R (LocalPolynomial R d) :=
  weightedHomogeneousSubmodule R (localJetDegreeWeight (d := d)) t

/-- The local constraint at the origin restricted to one homogeneous source and target block. -/
def gradedLocalConstraintAtZero (m t : ℕ) :
    sourceJetGrade R d t →ₗ[R] localJetGrade R d t where
  toFun Q := ⟨localConstraintAt (d := d) m 0 0 Q.1,
    localConstraintAt_zero_isWeightedHomogeneous (m := m) Q.2⟩
  map_add' P Q := by ext; simp
  map_smul' a Q := by ext; simp

section ImageCoordinates

variable {F V W : Type*} [Field F] [AddCommGroup V] [Module F V]
  [AddCommGroup W] [Module F W]

/-- Coordinates on the actual image of a finite-rank linear map, chosen over its base field. -/
def gradedImageCoordinateEquiv (f : V →ₗ[F] W) [Module.Finite F f.range] :
    f.range ≃ₗ[F] (Fin (Module.finrank F f.range) → F) :=
  (Module.finBasis F f.range).repr.trans
    (Finsupp.linearEquivFunOnFinite F F (Fin (Module.finrank F f.range)))

/-- The coordinate map on a graded source block. It has exactly the rank of the actual image. -/
def gradedImageCoordinateMap (f : V →ₗ[F] W) [Module.Finite F f.range] :
    V →ₗ[F] (Fin (Module.finrank F f.range) → F) :=
  (gradedImageCoordinateEquiv f).toLinearMap.comp
    (f.codRestrict f.range fun v ↦ ⟨v, rfl⟩)

/-- Passing to base-field image coordinates loses no equation from the original block. -/
theorem gradedImageCoordinateMap_eq_zero_iff
    (f : V →ₗ[F] W) [Module.Finite F f.range] (v : V) :
    gradedImageCoordinateMap f v = 0 ↔ f v = 0 := by
  constructor
  · intro h
    have h' : (f.codRestrict f.range fun x ↦ ⟨x, rfl⟩) v = 0 :=
      (gradedImageCoordinateEquiv f).injective (by simpa [gradedImageCoordinateMap] using h)
    exact congrArg Subtype.val h'
  · intro h
    change (gradedImageCoordinateEquiv f) ⟨f v, _⟩ = 0
    have hz : (⟨f v, by exact ⟨v, rfl⟩⟩ : f.range) = 0 := Subtype.ext h
    simp [hz]

end ImageCoordinates

/-- An origin constraint coefficient vanishes unless source and target jet degrees agree. -/
theorem coeff_localConstraintAt_zero_sourceMonomial_eq_zero
    (x b : ℕ) (higher : Fin d → ℕ) (e : LocalVariable d →₀ ℕ)
    (hgrade : localJetDegree e ≠ b + ∑ j, higher j) :
    MvPolynomial.coeff e (localConstraintAt (R := R) (d := d) m 0 0
      (sourceMonomial x b higher)) = 0 := by
  exact (localConstraintAt_zero_sourceMonomial_isWeightedHomogeneous
    (R := R) (m := m) x b higher).coeff_eq_zero e hgrade

/-- Translation by a received point cannot raise the total jet degree of any support monomial. -/
theorem totalJetDegree_le_of_mem_globalPointTranslation_support
    (center received : R) {Q : DifferentialPolynomial R d} {t : ℕ}
    (hQ : ∀ u ∈ Q.support, totalJetDegree u ≤ t)
    {e : JetVariable d →₀ ℕ} (he : e ∈ (globalPointTranslation center received Q).support) :
    totalJetDegree e ≤ t := by
  rw [← sourceJetDegreeWeight_eq_totalJetDegree]
  apply globalPointTranslation_support_weight_le sourceJetDegreeWeight
    (by simp [sourceJetDegreeWeight]) (by simp [sourceJetDegreeWeight])
    center received (a := t) _ he
  intro u hu
  rw [sourceJetDegreeWeight_eq_totalJetDegree]
  exact hQ u hu

end

end ReedSolomon.HiddenDerivative

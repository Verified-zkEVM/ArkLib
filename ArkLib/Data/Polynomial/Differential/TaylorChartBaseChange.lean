/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.Polynomial.Differential.BaseChange
public import ArkLib.Data.Polynomial.Differential.TaylorChartGeometry

/-!
# Common regular centers after coefficient extension

An injective coefficient map preserves nonzero separant specializations over the target domain.
If that domain is infinite, the mapped family has a common center where all these separants
remain nonzero.

## Main statements

* `exists_forall_jetEvaluation_ne_zero_map`: a common regular center for a finite family after
  mapping coefficients into an infinite domain.

## References

* [DKT26]
-/

@[expose] public section

namespace PolynomialDifferential

open Classical in
/-- A finite family with nonzero separant specialization has a common regular center after an
injective coefficient map into an infinite domain. The jet coordinate may be any `j`. -/
theorem exists_forall_jetEvaluation_ne_zero_map {F E : Type*} [CommSemiring F] [CommRing E]
    [IsDomain E] [Infinite E] {r : ℕ} (f : F →+* E) (hf : Function.Injective f)
    (Q : DifferentialPolynomial F r) (S : Finset (Polynomial F)) (j : Fin (r + 1))
    (hregular : ∀ P ∈ S, differentialSpecialization (separant Q j) P ≠ 0) :
    ∃ center : E, ∀ P ∈ S,
      jetEvaluation (separant (MvPolynomial.map f Q) j) center
        (polynomialJet center (P.map f)) ≠ 0 := by
  classical
  have hregularMap : ∀ P ∈ S.image (Polynomial.map f),
      differentialSpecialization (separant (MvPolynomial.map f Q) j) P ≠ 0 := by
    intro P hP
    obtain ⟨P, hPS, rfl⟩ := Finset.mem_image.mp hP
    rw [← map_separant]
    exact (map_differentialSpecialization_ne_zero_iff hf (separant Q j) P).2
      (hregular P hPS)
  obtain ⟨center, hc⟩ :=
    exists_forall_jetEvaluation_ne_zero (separant (MvPolynomial.map f Q) j)
      (S.image (Polynomial.map f)) hregularMap
  exact ⟨center, fun P hP ↦ hc _ (Finset.mem_image.mpr ⟨P, hP, rfl⟩)⟩

end PolynomialDifferential

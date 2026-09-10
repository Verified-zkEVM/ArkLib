/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.WeightedSupport.LocalRank


/-!
# A nonzero interpolant from the weighted support surplus

The product of the actual local maps has rank at most the sum of their coordinate budgets.
A strict surplus of supported monomials therefore gives a nonzero kernel vector. The domain
is the no-band weighted support itself, so the resulting polynomial retains all its
specialization and total-jet bounds.

The numerical dimension inequality is supplied by weighted simplex counting. No rank or
independence premise is hidden in the local budget: its bound is proved from reachable
coordinates over every field.
-/

@[expose] public section

open PolynomialDifferential


noncomputable section

open scoped BigOperators

namespace ReedSolomon.HiddenDerivative

variable {F : Type*} [Field F] {ι : Type*} [Fintype ι]
variable {D d m W : ℕ} {L : ℝ}

/-- Product of the actual local maps on the common weighted-support domain. -/
def weightedSupportGlobalConstraint (hD : 0 < D) (centers received : ι → F) :
    weightedSupportSpace F D d W L hD →ₗ[F] (ι → LocalPolynomial F d) :=
  LinearMap.pi fun i ↦ weightedSupportLocalConstraint m hD (centers i) (received i)

/-- The product map has rank at most the number of received positions times the proved
pointwise coordinate budget. The ambient polynomial codomain need not be finite-dimensional. -/
theorem finrank_weightedSupportGlobalConstraint_le (hd : 0 < d) (hD : 0 < D)
    (centers received : ι → F) :
    Module.finrank F (weightedSupportGlobalConstraint (d := d) (m := m) (W := W)
      (L := L) hD centers received).range ≤
        Fintype.card ι * localResidualCoordinateBudget d m W (L / D) := by
  let V := weightedSupportSpace F D d W L hD
  let : Module.Finite F V := Module.Finite.of_basis (weightedSupportBasis hD)
  let φ := fun i ↦ weightedSupportLocalConstraint (d := d) (W := W)
    (L := L) m hD (centers i) (received i)
  let Φ := weightedSupportGlobalConstraint (d := d) (m := m) (W := W)
    (L := L) hD centers received
  let includeRange : Φ.range →ₗ[F] (∀ i, (φ i).range) := {
    toFun y i := ⟨y.1 i, by
      rcases y.2 with ⟨v, hv⟩
      exact ⟨v, congrFun hv i⟩⟩
    map_add' x y := by ext i; rfl
    map_smul' a x := by ext i; rfl
  }
  have hinj : Function.Injective includeRange := by
    intro x y hxy
    apply Subtype.ext
    funext i
    exact congrArg Subtype.val (congrFun hxy i)
  calc
    Module.finrank F Φ.range ≤ Module.finrank F (∀ i, (φ i).range) :=
      LinearMap.finrank_le_finrank_of_injective hinj
    _ = ∑ i, Module.finrank F (φ i).range := Module.finrank_pi_fintype F
    _ ≤ ∑ _i : ι, localResidualCoordinateBudget d m W (L / D) :=
      Finset.sum_le_sum fun i _ ↦
        finrank_weightedSupportLocalConstraint_le (d := d) (m := m) (W := W)
          (L := L) hd hD (centers i) (received i)
    _ = _ := by simp

/-- The strict finite dimension surplus yields a genuine nonzero interpolant with every local
constraint, over any field and any indexed collection of received positions. -/
theorem exists_nonzero_weightedSupport_interpolant (hd : 0 < d) (hD : 0 < D)
    (centers received : ι → F)
    (hdim : Fintype.card ι * localResidualCoordinateBudget d m W (L / D) <
      (weightedSupportExponents D d W L hD).card) :
    ∃ Q : DifferentialPolynomial F d, Q ≠ 0 ∧
      Q ∈ weightedSupportSpace F D d W L hD ∧
        ∀ i, SatisfiesLocalConstraints m (centers i) (received i) Q := by
  let V := weightedSupportSpace F D d W L hD
  let : Module.Finite F V := Module.Finite.of_basis (weightedSupportBasis hD)
  let Φ := weightedSupportGlobalConstraint (d := d) (m := m) (W := W)
    (L := L) hD centers received
  have hrank : Module.finrank F Φ.range < Module.finrank F V := by
    rw [finrank_weightedSupportSpace_eq_card hD]
    exact (finrank_weightedSupportGlobalConstraint_le hd hD centers received).trans_lt hdim
  have hnull := LinearMap.finrank_range_add_finrank_ker Φ
  change Module.finrank F Φ.range + Module.finrank F Φ.ker = Module.finrank F V at hnull
  have hpos : 0 < Module.finrank F Φ.ker := by omega
  have hker : Φ.ker ≠ ⊥ := by
    intro h
    rw [h] at hpos
    simp at hpos
  obtain ⟨v, hvker, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  refine ⟨v.1, ?_, v.2, ?_⟩
  · intro hv
    exact hv0 (Subtype.ext hv)
  · intro i
    have hi := congrFun (LinearMap.mem_ker.mp hvker) i
    exact hi

/-- The weighted-support interpolant lies in the existing exact search space when the total
cutoff supplies its first-derivative cap. Nonzeroness and every local constraint are preserved. -/
theorem exists_nonzero_exact_interpolant_of_weightedSupport_surplus {A M : ℕ}
    (hd : 0 < d) (hD : 0 < D) (hdD : d < D) (centers received : ι → F)
    (hL : L ≤ (m * A : ℕ)) (hcap : L ≤ (D : ℝ) * M)
    (hdim : Fintype.card ι * localResidualCoordinateBudget d m W (L / D) <
      (weightedSupportExponents D d W L hD).card) :
    ∃ Q : DifferentialPolynomial F d, Q ≠ 0 ∧
      Q ∈ exactInterpolationSpace F D A d m M W hdD ∧
        ∀ i, SatisfiesLocalConstraints m (centers i) (received i) Q := by
  obtain ⟨Q, hQ0, hQsupport, hQlocal⟩ :=
    exists_nonzero_weightedSupport_interpolant hd hD centers received hdim
  exact ⟨Q, hQ0,
    weightedSupportSpace_le_exactInterpolationSpace hD hdD hL hcap hQsupport, hQlocal⟩

end ReedSolomon.HiddenDerivative

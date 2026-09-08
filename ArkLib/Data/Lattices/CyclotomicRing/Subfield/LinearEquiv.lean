/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.Lattices.CyclotomicRing.Subfield.Bijectivity

/-!
# Fixed-subring linear coordinates for Hachi packing

The Hachi packing map is linear over the fixed subring and is a linear equivalence
under the hypotheses of `psi_bijective`. Neither this equivalence nor cancellation of the
trace scale needs a field structure on the fixed subring.

## References

* [Nguyen, N. K., O'Rourke, G., and Zhang, J., *Hachi: Efficient Lattice-Based Multilinear
  Polynomial Commitments over Extension Fields*][NOZ26]
-/

namespace ArkLib.Lattices.CyclotomicModulus

section Linear

variable {R : Type*} [Field R] [BEq R] [LawfulBEq R] [DecidableEq R]

/-- Hachi's packing map respects multiplication by fixed-subring scalars. -/
theorem psi_smul (α k : ℕ) (c : fixedSubring (R := R) α k)
    (a : Fin (2 ^ α / k) → fixedSubring (R := R) α k) :
    psi α k (c • a) = c • psi α k a := by
  simp only [psi, Pi.smul_apply, smul_eq_mul, MulMemClass.coe_mul, Subring.smul_def,
    Finset.mul_sum]
  exact Finset.sum_congr rfl (fun _ _ => mul_assoc _ _ _)

/-- The fixed-subring linear map underlying `psi`. -/
def psiLinearMap (α k : ℕ) :
    (Fin (2 ^ α / k) → fixedSubring (R := R) α k) →ₗ[fixedSubring (R := R) α k]
      Rq (powTwoCyclotomic (R := R) α) where
  toFun := psi α k
  map_add' := psi_add α k
  map_smul' := psi_smul α k

omit [DecidableEq R] in
/-- The trace scale is a unit in the ambient quotient ring: it is a power of the unit `2`.
This uses the coefficient field, without asserting that the fixed subring is a field. -/
theorem isUnit_traceScale (α κ : ℕ) (h2 : (2 : R) ≠ 0)
    (hk : 2 * 2 ^ κ ∣ 2 ^ α) :
    IsUnit ((2 ^ α / 2 ^ κ : ℕ) : Rq (powTwoCyclotomic (R := R) α)) := by
  have hκ : κ ≤ α := Nat.le_of_succ_le (succ_le_of_two_mul_two_pow_dvd hk)
  rw [Nat.pow_div hκ (by norm_num), Nat.cast_pow, Nat.cast_ofNat]
  exact (isUnit_two (powTwoCyclotomic α) h2).pow _

/-- Cancelling the genuine (unnormalized) trace scale recovers the scalar inner product. -/
theorem traceH_psi_mul_conj_eq_iff (α κ : ℕ) (h2 : (2 : R) ≠ 0)
    (hk : 2 * 2 ^ κ ∣ 2 ^ α)
    (a b : Fin (2 ^ α / 2 ^ κ) → fixedSubring (R := R) α (2 ^ κ))
    (z : fixedSubring (R := R) α (2 ^ κ)) :
    traceH α (2 ^ κ) (psi α (2 ^ κ) a * conjAut α (psi α (2 ^ κ) b)) =
        (2 ^ α / 2 ^ κ) • (z : Rq (powTwoCyclotomic α)) ↔
      ∑ i, a i * b i = z := by
  rw [traceH_psi_mul_conj α (2 ^ κ) h2 ⟨κ, rfl⟩ hk, nsmul_eq_mul, nsmul_eq_mul]
  constructor
  · intro h
    exact Subtype.coe_injective ((isUnit_traceScale α κ h2 hk).mul_left_cancel h)
  · intro h
    rw [h]

end Linear

section Equivalence

variable (q : ℕ) [Fact (Nat.Prime q)] [NeZero q] [BEq (ZMod q)] [LawfulBEq (ZMod q)]

/-- Fixed-subring linear coordinates of the packing map. -/
noncomputable def psiLinearEquiv (α κ : ℕ) (h2 : (2 : ZMod q) ≠ 0)
    (hk : 2 * 2 ^ κ ∣ 2 ^ α) :
    (Fin (2 ^ α / 2 ^ κ) → fixedSubring (R := ZMod q) α (2 ^ κ)) ≃ₗ[
        fixedSubring (R := ZMod q) α (2 ^ κ)]
      Rq (powTwoCyclotomic (R := ZMod q) α) :=
  LinearEquiv.ofBijective (psiLinearMap α (2 ^ κ)) (psi_bijective q α κ h2 hk)

/-- The linear equivalence computes exactly the paper's `psi`. -/
@[simp] theorem psiLinearEquiv_apply (α κ : ℕ) (h2 : (2 : ZMod q) ≠ 0)
    (hk : 2 * 2 ^ κ ∣ 2 ^ α)
    (a : Fin (2 ^ α / 2 ^ κ) → fixedSubring (R := ZMod q) α (2 ^ κ)) :
    psiLinearEquiv q α κ h2 hk a = psi α (2 ^ κ) a := rfl

/-- Hachi's packing basis over the fixed subring, obtained from the explicit coordinate map. -/
noncomputable def psiBasis (α κ : ℕ) (h2 : (2 : ZMod q) ≠ 0)
    (hk : 2 * 2 ^ κ ∣ 2 ^ α) :
    Module.Basis (Fin (2 ^ α / 2 ^ κ)) (fixedSubring (R := ZMod q) α (2 ^ κ))
      (Rq (powTwoCyclotomic (R := ZMod q) α)) :=
  (Pi.basisFun _ _).map (psiLinearEquiv q α κ h2 hk)

end Equivalence

end ArkLib.Lattices.CyclotomicModulus

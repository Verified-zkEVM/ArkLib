/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/
module

public import ArkLib.Data.Lattices.CyclotomicRing.Subfield.Bijectivity
public import ArkLib.Commitments.Functional.Hachi.TraceHead.Coefficients

/-!
# Coefficient-packing coordinates

`coefficientEquiv` is `ψ` reindexed by the `2^(α−κ)` binary monomial indices of
`CMlPolynomial`'s coefficients. In these coordinates the scaled trace check is a coefficient
inner product (`traceH_coefficientEquiv_eq_iff`) and, at a packed polynomial, the evaluation of the
decoded scalar polynomial (`traceH_eval_eq_iff`).

## References

* [Nguyen, N. K., O'Rourke, G., and Zhang, J., *Hachi: Efficient Lattice-Based Multilinear
  Polynomial Commitments over Extension Fields*][NOZ26]
-/

@[expose] public section

open CompPoly
open ArkLib.Lattices.CyclotomicModulus

namespace ArkLib.Lattices.Hachi.TraceHead

variable (q : ℕ) [Fact (Nat.Prime q)] [NeZero q] [BEq (ZMod q)] [LawfulBEq (ZMod q)]
variable (α κ : ℕ) (h2 : (2 : ZMod q) ≠ 0) (hk : 2 * 2 ^ κ ∣ 2 ^ α)

include hk in
/-- Binary monomial indices have exactly the cardinality of the packing vector. -/
theorem packingRank_eq : 2 ^ α / 2 ^ κ = 2 ^ (α - κ) :=
  Nat.pow_div (Nat.le_of_succ_le (succ_le_of_two_mul_two_pow_dvd hk)) (by norm_num)

/-- The `psi` map indexed by `Fin (2^(α-κ))`. -/
noncomputable def coefficientEquiv :
    (Fin (2 ^ (α - κ)) → fixedSubring (R := ZMod q) α (2 ^ κ)) ≃ₗ[
      fixedSubring (R := ZMod q) α (2 ^ κ)] Rq (powTwoCyclotomic (R := ZMod q) α) :=
  (LinearEquiv.funCongrLeft _ _ (finCongr (packingRank_eq α κ hk))).trans
    (psiLinearEquiv q α κ h2 hk)

/-- The index transport preserves each numeric monomial index. -/
@[simp] theorem coefficientEquiv_apply
    (a : Fin (2 ^ (α - κ)) → fixedSubring (R := ZMod q) α (2 ^ κ)) :
    coefficientEquiv q α κ h2 hk a =
      psi α (2 ^ κ) (fun j => a (finCongr (packingRank_eq α κ hk) j)) := rfl

/-- The trace equality is exactly an inner product in the binary-indexed coordinates. -/
theorem traceH_coefficientEquiv_eq_iff
    (a b : Fin (2 ^ (α - κ)) → fixedSubring (R := ZMod q) α (2 ^ κ))
    (z : fixedSubring (R := ZMod q) α (2 ^ κ)) :
    traceH α (2 ^ κ) (coefficientEquiv q α κ h2 hk a *
        conjAut α (coefficientEquiv q α κ h2 hk b)) =
      (2 ^ α / 2 ^ κ) • (z : Rq (powTwoCyclotomic α)) ↔ ∑ i, a i * b i = z := by
  rw [coefficientEquiv_apply, coefficientEquiv_apply,
    traceH_psi_mul_conj_eq_iff α κ h2 hk]
  rw [Equiv.sum_comp (finCongr (packingRank_eq α κ hk)) (fun i => a i * b i)]

/--
The scaled trace check equals evaluation of the decoded polynomial. Retained point coordinates
lie in the fixed subring and are embedded into `Rq`.
-/
theorem traceH_eval_eq_iff {n : ℕ}
    (F : CMlPolynomial (Rq (powTwoCyclotomic (R := ZMod q) α)) n)
    (x : Vector (fixedSubring (R := ZMod q) α (2 ^ κ)) n)
    (xp : Vector (fixedSubring (R := ZMod q) α (2 ^ κ)) (α - κ))
    (z : fixedSubring (R := ZMod q) α (2 ^ κ)) :
    traceH α (2 ^ κ) (F.eval (x.map (algebraMap _ _)) *
        conjAut α (coefficientEquiv q α κ h2 hk (CMlPolynomial.monomialBasis xp).get)) =
      (2 ^ α / 2 ^ κ) • (z : Rq (powTwoCyclotomic α)) ↔
      (unpackCoefficients (coefficientEquiv q α κ h2 hk) F).eval (x ++ xp) = z := by
  rw [unpackCoefficients_eval, ← traceH_coefficientEquiv_eq_iff q α κ h2 hk,
    LinearEquiv.apply_symm_apply]

end ArkLib.Lattices.Hachi.TraceHead

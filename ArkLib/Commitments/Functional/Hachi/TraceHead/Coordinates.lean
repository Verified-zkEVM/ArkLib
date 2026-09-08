/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.Lattices.CyclotomicRing.Subfield.LinearEquiv
import ArkLib.Commitments.Functional.Hachi.TraceHead.Coefficients
import ArkLib.ProofSystem.RingSwitching.Packing.Coordinates

/-!
# Hachi's actual coefficient-packing coordinates

The generic algebra instance has packing algebra `Rq` and opening algebra the fixed subring.
Its opening rank is one. The trace head uses this same packing basis, with the binary index
transport required by `CMlPolynomial`'s monomial coefficients.
-/

open CompPoly
open ArkLib.Lattices.CyclotomicModulus

namespace ArkLib.Lattices.Hachi.TraceHead

variable (q : ℕ) [Fact (Nat.Prime q)] [NeZero q] [BEq (ZMod q)] [LawfulBEq (ZMod q)]
variable (α κ : ℕ) (h2 : (2 : ZMod q) ≠ 0) (hk : 2 * 2 ^ κ ∣ 2 ^ α)

include hk in
/-- Binary monomial indices have exactly the cardinality of Hachi's packing vector. -/
theorem packingRank_eq : 2 ^ α / 2 ^ κ = 2 ^ (α - κ) :=
  Nat.pow_div (Nat.le_of_succ_le (succ_le_of_two_mul_two_pow_dvd hk)) (by norm_num)

/-- The actual `psi` map with the monomial index type `Fin (2^(α-κ))`. -/
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

/-- Hachi instantiates the general finite-free algebra model with `P = Rq`, `E = B`.
This assertion uses only the actual fixed subring's ring structure. -/
noncomputable def packingData :
    RingSwitching.Packing.PackingData (fixedSubring (R := ZMod q) α (2 ^ κ)) where
  P := Rq (powTwoCyclotomic (R := ZMod q) α)
  E := fixedSubring (R := ZMod q) α (2 ^ κ)
  ιP := Fin (2 ^ α / 2 ^ κ)
  ιE := Unit
  packBasis := psiBasis q α κ h2 hk
  openBasis := Module.Basis.singleton Unit _

/-- The trace equality is exactly an inner product in the binary-indexed coordinates. -/
theorem trace_coefficientEquiv_eq_iff
    (a b : Fin (2 ^ (α - κ)) → fixedSubring (R := ZMod q) α (2 ^ κ))
    (z : fixedSubring (R := ZMod q) α (2 ^ κ)) :
    traceH α (2 ^ κ) (coefficientEquiv q α κ h2 hk a *
        conjAut α (coefficientEquiv q α κ h2 hk b)) =
      (2 ^ α / 2 ^ κ) • (z : Rq (powTwoCyclotomic α)) ↔ ∑ i, a i * b i = z := by
  rw [coefficientEquiv_apply, coefficientEquiv_apply,
    traceH_psi_mul_conj_eq_iff α κ h2 hk]
  rw [Equiv.sum_comp (finCongr (packingRank_eq α κ hk)) (fun i => a i * b i)]

/-- The actual scaled trace check is precisely the decoded polynomial's scalar evaluation.
All retained point coordinates lie in the fixed subring; `Rq` points are their embeddings. -/
theorem trace_eval_eq_iff {n : ℕ}
    (F : CMlPolynomial (Rq (powTwoCyclotomic (R := ZMod q) α)) n)
    (x : Vector (fixedSubring (R := ZMod q) α (2 ^ κ)) n)
    (xp : Vector (fixedSubring (R := ZMod q) α (2 ^ κ)) (α - κ))
    (z : fixedSubring (R := ZMod q) α (2 ^ κ)) :
    traceH α (2 ^ κ) (F.eval (x.map (algebraMap _ _)) *
        conjAut α (coefficientEquiv q α κ h2 hk (CMlPolynomial.monomialBasis xp).get)) =
      (2 ^ α / 2 ^ κ) • (z : Rq (powTwoCyclotomic α)) ↔
      (unpackCoefficients (coefficientEquiv q α κ h2 hk) F).eval (x ++ xp) = z := by
  rw [unpackCoefficients_eval]
  conv_lhs =>
    arg 1
    arg 3
    arg 1
    rw [← (coefficientEquiv q α κ h2 hk).apply_symm_apply
      (F.eval (x.map (algebraMap _ _)))]
  exact trace_coefficientEquiv_eq_iff q α κ h2 hk _ _ z

end ArkLib.Lattices.Hachi.TraceHead

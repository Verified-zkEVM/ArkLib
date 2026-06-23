/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tobias Rothmann
-/
import ArkLib.CommitmentScheme.Ajtai.Gadget
import ArkLib.Data.Lattices.CyclotomicRing.NormBounds

/-!
# Centered Norm Bounds for the Gadget Decomposition `G⁻¹`

Centered `ℓ₂²` and `ℓ∞` shortness of the Hachi gadget inverse `gadgetDecompose` over `ZMod q`,
when instantiated with the genuine base-`b` digit decomposition `zmodDigitDecomposition`. These
are the honest-case norm bounds the inner-outer Ajtai commitment needs for perfect correctness
(`InnerOuter.Correctness.perfectlyCorrect`).

The single analytic input is `zmodDigit_natAbs_le`: each base-`b` digit, as a centered residue,
has absolute value `≤ b - 1` (under `b - 1 ≤ q/2`, so the residue does not wrap). Everything else
is bookkeeping over the gadget's coefficient layout (`Rq.ofFinCoeff_coeff`).

This file bridges the gadget algebra (`CommitmentScheme.Ajtai.Gadget`) and the centered norms
(`Data.Lattices.CyclotomicRing.NormBounds`).

## References

* [Nguyen, N. K., and Seiler, G., *Greyhound: Fast Polynomial Commitments from Lattices*][NS24]
* [Nguyen, N. K., O'Rourke, G., and Zhang, J., *Hachi: Efficient Lattice-Based Multilinear
    Polynomial Commitments over Extension Fields*][NOZ26]
-/

open CompPoly ArkLib.Lattices ArkLib.Lattices.CyclotomicModulus

namespace ArkLib.Lattices.Ajtai

section ZModGadgetNorms

variable {q : ℕ} [NeZero q] [Fact (Nat.Prime q)] [BEq (ZMod q)] [LawfulBEq (ZMod q)]
  (Φ : CyclotomicModulus (ZMod q)) [IsCyclotomic Φ]

omit [NeZero q] [IsCyclotomic Φ] in
/-- The degree bound needed to read off gadget coefficients: `deg φ` does not exceed the degree
of the modulus polynomial. -/
theorem natDegree_le_degree_toPoly (h : 1 ≤ Φ.φ.natDegree) :
    (Φ.φ.natDegree : WithBot ℕ) ≤ Φ.φ.toPoly.degree := by
  have hnd : 1 ≤ Φ.φ.toPoly.natDegree := by
    rw [← CompPoly.CPolynomial.natDegree_toPoly]; exact h
  have hne : Φ.φ.toPoly ≠ 0 := fun h0 => by simp [h0] at hnd
  rw [Polynomial.degree_eq_natDegree hne, ← CompPoly.CPolynomial.natDegree_toPoly]

omit [Fact (Nat.Prime q)] [BEq (ZMod q)] [LawfulBEq (ZMod q)] in
/-- **Core digit bound.** Each base-`b` digit of `zmodDigitDecomposition`, viewed as a centered
residue, has absolute value at most `b - 1` — provided `b - 1 ≤ q/2`, so the digit (a natural
number `< b`) does not wrap to a negative centered representative. -/
theorem zmodDigit_natAbs_le {b digits : ℕ} (hb : 1 < b) (hq : q ≤ b ^ digits)
    (hbq : b - 1 ≤ q / 2) (c : ZMod q) (e : Fin digits) :
    ((zmodDigitDecomposition b digits hb hq).digit c e).valMinAbs.natAbs ≤ b - 1 := by
  simp only [zmodDigitDecomposition]
  set d := (Nat.digits b c.val).getD (e : ℕ) 0 with hd
  have hdb : d < b := by
    rcases lt_or_ge (e : ℕ) (Nat.digits b c.val).length with hlt | hge
    · rw [hd, List.getD_eq_getElem _ _ hlt]
      exact Nat.digits_lt_base hb (List.getElem_mem _)
    · rw [hd, List.getD_eq_default _ _ hge]; omega
  rw [ZMod.valMinAbs_natCast_of_le_half (by omega : d ≤ q / 2)]
  simp only [Int.natAbs_natCast]
  omega

omit [NeZero q] in
/-- The `k`-th coefficient (`k < deg φ`) of a gadget-decomposition block is exactly the
corresponding digit of the corresponding input coefficient. -/
theorem gadgetDecompose_coeff {base : ZMod q} {rows digits : ℕ}
    (dd : DigitDecomposition base digits) (h : 1 ≤ Φ.φ.natDegree)
    (x : PolyVec (Rq Φ) rows) (j : Fin (rows * digits)) {k : ℕ} (hk : k < Φ.φ.natDegree) :
    (gadgetDecompose Φ dd x j).1.coeff k =
      dd.digit ((x (finProdFinEquiv.symm j).1).1.coeff k) (finProdFinEquiv.symm j).2 := by
  rw [show gadgetDecompose Φ dd x j =
      Rq.ofFinCoeff Φ Φ.φ.natDegree (fun k =>
        dd.digit ((x (finProdFinEquiv.symm j).1).1.coeff k) (finProdFinEquiv.symm j).2) from rfl,
    Rq.ofFinCoeff_coeff Φ _ (natDegree_le_degree_toPoly Φ h) k, if_pos hk]

/-! ## `ℓ∞` bound -/

/-- Each gadget-decomposition block is `ℓ∞`-short: its centered `ℓ∞` norm is `≤ b - 1`. -/
theorem gadgetDecompose_zmod_lInftyNorm_le {b digits rows : ℕ} (hb : 1 < b) (hq : q ≤ b ^ digits)
    (hbq : b - 1 ≤ q / 2) (h : 1 ≤ Φ.φ.natDegree) (x : PolyVec (Rq Φ) rows)
    (j : Fin (rows * digits)) :
    Rq.lInftyNorm Φ (gadgetDecompose Φ (zmodDigitDecomposition b digits hb hq) x j) ≤ b - 1 := by
  unfold Rq.lInftyNorm
  refine Finset.sup_le (fun k hk => ?_)
  rw [gadgetDecompose_coeff Φ _ h x j (Finset.mem_range.mp hk)]
  exact zmodDigit_natAbs_le hb hq hbq _ _

/-- **`ℓ∞` shortness of `G⁻¹`.** The full gadget decomposition has centered `ℓ∞` norm `≤ b - 1`. -/
theorem gadgetDecompose_zmod_vecLInftyNorm_le {b digits rows : ℕ} (hb : 1 < b) (hq : q ≤ b ^ digits)
    (hbq : b - 1 ≤ q / 2) (h : 1 ≤ Φ.φ.natDegree) (x : PolyVec (Rq Φ) rows) :
    vecLInftyNorm Φ (gadgetDecompose Φ (zmodDigitDecomposition b digits hb hq) x) ≤ b - 1 := by
  unfold vecLInftyNorm
  exact Finset.sup_le (fun j _ => gadgetDecompose_zmod_lInftyNorm_le Φ hb hq hbq h x j)

/-! ## `ℓ₂²` bound -/

/-- Each gadget-decomposition block is `ℓ₂²`-short: its centered squared-`ℓ₂` norm is at most
`(deg φ)·(b-1)²` (each of the `deg φ` coefficients contributes at most `(b-1)²`). -/
theorem gadgetDecompose_zmod_l2NormSq_le {b digits rows : ℕ} (hb : 1 < b) (hq : q ≤ b ^ digits)
    (hbq : b - 1 ≤ q / 2) (h : 1 ≤ Φ.φ.natDegree) (x : PolyVec (Rq Φ) rows)
    (j : Fin (rows * digits)) :
    ‖gadgetDecompose Φ (zmodDigitDecomposition b digits hb hq) x j‖₂² ≤
      Φ.φ.natDegree * (b - 1) ^ 2 := by
  unfold Rq.l2NormSq
  calc ∑ k ∈ Finset.range Φ.φ.natDegree,
        ((gadgetDecompose Φ (zmodDigitDecomposition b digits hb hq) x j).1.coeff k).valMinAbs.natAbs
          ^ 2
      ≤ ∑ _k ∈ Finset.range Φ.φ.natDegree, (b - 1) ^ 2 := by
        refine Finset.sum_le_sum (fun k hk => ?_)
        rw [gadgetDecompose_coeff Φ _ h x j (Finset.mem_range.mp hk)]
        exact Nat.pow_le_pow_left (zmodDigit_natAbs_le hb hq hbq _ _) 2
    _ = Φ.φ.natDegree * (b - 1) ^ 2 := by
        rw [Finset.sum_const, Finset.card_range, smul_eq_mul]

/-- **`ℓ₂²` shortness of `G⁻¹`.** The full gadget decomposition has centered squared-`ℓ₂` norm at
most `(rows·digits)·(deg φ)·(b-1)²`. -/
theorem gadgetDecompose_zmod_vecL2NormSq_le {b digits rows : ℕ} (hb : 1 < b) (hq : q ≤ b ^ digits)
    (hbq : b - 1 ≤ q / 2) (h : 1 ≤ Φ.φ.natDegree) (x : PolyVec (Rq Φ) rows) :
    ‖gadgetDecompose Φ (zmodDigitDecomposition b digits hb hq) x‖₂² ≤
      rows * digits * (Φ.φ.natDegree * (b - 1) ^ 2) := by
  unfold vecL2NormSq
  calc ∑ i : Fin (rows * digits),
        Rq.l2NormSq Φ (gadgetDecompose Φ (zmodDigitDecomposition b digits hb hq) x i)
      ≤ ∑ _i : Fin (rows * digits), Φ.φ.natDegree * (b - 1) ^ 2 :=
        Finset.sum_le_sum (fun i _ => gadgetDecompose_zmod_l2NormSq_le Φ hb hq hbq h x i)
    _ = rows * digits * (Φ.φ.natDegree * (b - 1) ^ 2) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]

end ZModGadgetNorms

end ArkLib.Lattices.Ajtai

/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tobias Rothmann
-/
import ArkLib.Data.Lattices.ModuleSIS
import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.ZMod

/-!
# Ajtai Gadget Matrices

The base-`b` gadget matrix `G = I_rows ⊗ [1, b, b², …, b^(digits-1)]` over the cyclotomic
ring `Rq Φ`, mapping `rows * digits` ring elements to `rows` ring elements, used by the
inner-outer (Greyhound [NS24] / Hachi [NOZ26]) commitment. Gadget entries are *ring
constants* `C(bᵉ)` embedded into `Rq Φ`. `IsLawfulGadgetDecomposition` records when a
decomposition is inverted by gadget multiplication (`G · G⁻¹(x) = x`).

The norm-reducing inverse `G⁻¹` is the genuine **base-`b` digit decomposition** of the
Hachi paper [NOZ26]: each coefficient of a ring element is written in base `b`, and digit `e` of
each coefficient is placed in the `bᵉ`-slot of its block. This is captured abstractly by
`DigitDecomposition` (a per-coefficient digit map satisfying the base-`b` reconstruction
law) and realized concretely over `ZMod q` by `zmodDigitDecomposition`. The associated
`gadgetDecompose` is then lawful (`gadgetDecompose_lawful`), replacing the earlier
units-place placeholder.

## References

* [Nguyen, N. K., and Seiler, G., *Greyhound: Fast Polynomial Commitments from Lattices*][NS24]
* [Nguyen, N. K., O'Rourke, G., and Zhang, J., *Hachi: Efficient Lattice-Based Multilinear
    Polynomial Commitments over Extension Fields*][NOZ26]
-/

open CompPoly ArkLib.Lattices ArkLib.Lattices.CyclotomicModulus

namespace ArkLib.Lattices.Ajtai

/-! ## Base-`b` reconstruction of `Nat.ofDigits` as a finite sum -/

/-- `Nat.ofDigits` as the finite sum of digit-weighted powers over the length of the list. -/
private theorem ofDigits_eq_sum_range {α : Type*} [CommSemiring α] (β : α) (L : List ℕ) :
    Nat.ofDigits β L = ∑ i ∈ Finset.range L.length, (L.getD i 0 : α) * β ^ i := by
  induction L with
  | nil => simp [Nat.ofDigits]
  | cons h t ih =>
    rw [show Nat.ofDigits β (h :: t) = (h : α) + β * Nat.ofDigits β t from rfl, ih,
        List.length_cons, Finset.sum_range_succ', Finset.mul_sum]
    simp only [List.getD_cons_succ, List.getD_cons_zero, pow_zero, mul_one, pow_succ]
    rw [add_comm]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    ring

/-- `Nat.ofDigits` as a finite sum over any range `D` at least the list length (the extra
high-order digits are zero). -/
private theorem ofDigits_eq_sum_range_of_len_le {α : Type*} [CommSemiring α] (β : α) (L : List ℕ)
    {D : ℕ} (hLD : L.length ≤ D) :
    Nat.ofDigits β L = ∑ i ∈ Finset.range D, (L.getD i 0 : α) * β ^ i := by
  rw [ofDigits_eq_sum_range β L]
  apply Finset.sum_subset (fun x hx =>
    Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hx) hLD))
  intro i _ hi
  rw [Finset.mem_range, not_lt] at hi
  rw [List.getD_eq_default _ _ hi, Nat.cast_zero, zero_mul]

/-! ## Abstract digit decompositions of the coefficient ring -/

section Digit

variable {R : Type*} [CommSemiring R]

/-- A base-`base` digit decomposition of the coefficient ring `R`: for each coefficient `c`,
`digit c e` is the `e`-th base-`base` digit, and the `digits` digits reconstruct `c` via
`∑ₑ baseᵉ · digit c e = c`. This is the per-coefficient data behind the Hachi gadget inverse
`G⁻¹`. -/
structure DigitDecomposition (base : R) (digits : Nat) where
  /-- The `e`-th base-`base` digit of a coefficient. -/
  digit : R → Fin digits → R
  /-- The digits reconstruct the coefficient: `∑ₑ baseᵉ · digit c e = c`. -/
  reconstruct : ∀ c : R, ∑ e : Fin digits, base ^ (e : ℕ) * digit c e = c

end Digit

/-! ## The concrete base-`b` digit decomposition over `ZMod q` -/

section ZModDigit

variable {q : ℕ} [NeZero q]

/-- The genuine base-`b` (binary, for `b = 2`) digit decomposition over `ZMod q`: digit `e`
of a coefficient `c` is the `e`-th base-`b` digit of its canonical representative `c.val`.
Reconstruction holds whenever `1 < b` and `q ≤ b ^ digits` (so every residue fits in
`digits` base-`b` digits). This is the coefficient-level Hachi `G⁻¹`. -/
def zmodDigitDecomposition (b digits : ℕ) (hb : 1 < b) (hq : q ≤ b ^ digits) :
    DigitDecomposition (R := ZMod q) (b : ZMod q) digits where
  digit c e := ((Nat.digits b c.val).getD (e : ℕ) 0 : ZMod q)
  reconstruct c := by
    set L := Nat.digits b c.val with hL
    have hlen : L.length ≤ digits :=
      (Nat.digits_length_le_iff hb c.val).mpr (lt_of_lt_of_le (ZMod.val_lt c) hq)
    calc ∑ e : Fin digits, (b : ZMod q) ^ (e : ℕ) * ((L.getD (e : ℕ) 0 : ZMod q))
        = ∑ e : Fin digits, ((L.getD (e : ℕ) 0 : ZMod q)) * (b : ZMod q) ^ (e : ℕ) := by
          apply Finset.sum_congr rfl; intro e _; ring
      _ = ∑ i ∈ Finset.range digits, ((L.getD i 0 : ZMod q)) * (b : ZMod q) ^ i :=
          Fin.sum_univ_eq_sum_range (fun i => (L.getD i 0 : ZMod q) * (b : ZMod q) ^ i) digits
      _ = Nat.ofDigits (b : ZMod q) L := (ofDigits_eq_sum_range_of_len_le (b : ZMod q) L hlen).symm
      _ = ((Nat.ofDigits b L : ℕ) : ZMod q) := (Nat.coe_ofDigits (ZMod q) b L).symm
      _ = ((c.val : ℕ) : ZMod q) := by rw [hL, Nat.ofDigits_digits]
      _ = c := ZMod.natCast_zmod_val c

end ZModDigit

/-! ## The gadget matrix over `Rq Φ` -/

variable {R : Type} [Field R] [BEq R] [LawfulBEq R] [DecidableEq R]
  (Φ : CyclotomicModulus R) [IsCyclotomic Φ]

/-- Entry of the base-`base` gadget matrix `I_rows ⊗ [1, base, …, base^(digits-1)]`:
column `j` of row `i` is `base^(j % digits)` when `j / digits = i`, else `0`. -/
def gadgetEntry (base : R) {rows digits : Nat} (i : Fin rows) (j : Fin (rows * digits)) : Rq Φ :=
  if j.val / digits = i.val then Rq.constRq Φ (base ^ (j.val % digits)) else 0

/-- The base-`base` gadget matrix `I_rows ⊗ [1, base, …, base^(digits-1)]`. -/
def gadgetMatrix (base : R) (rows digits : Nat) : PolyMatrix (Rq Φ) rows (rows * digits) :=
  fun i j => gadgetEntry Φ base i j

/-- Apply the gadget matrix to a decomposed vector. -/
def gadgetMul (base : R) {rows digits : Nat} (v : PolyVec (Rq Φ) (rows * digits)) :
    PolyVec (Rq Φ) rows :=
  gadgetMatrix Φ base rows digits *ᵥ v

/-- A gadget decomposition is lawful when gadget multiplication reconstructs its input. -/
def IsLawfulGadgetDecomposition (base : R) {rows digits : Nat}
    (decompose : PolyVec (Rq Φ) rows → PolyVec (Rq Φ) (rows * digits)) : Prop :=
  ∀ x, gadgetMul Φ base (decompose x) = x

/-! ## The gadget product as a block digit-sum -/

omit [DecidableEq R] in
/-- The gadget entry at the flattened index `finProdFinEquiv (i', e)` is `constRq (base^e)`
on the diagonal block and `0` elsewhere. -/
theorem gadgetEntry_finProdFinEquiv (base : R) {rows digits : Nat} (hd : 0 < digits)
    (i i' : Fin rows) (e : Fin digits) :
    gadgetEntry Φ base i (finProdFinEquiv (i', e))
      = if i' = i then Rq.constRq Φ (base ^ (e : ℕ)) else 0 := by
  unfold gadgetEntry
  have hval : (finProdFinEquiv (i', e)).val = e.val + digits * i'.val := rfl
  have hdiv : (finProdFinEquiv (i', e)).val / digits = i'.val := by
    rw [hval, Nat.add_mul_div_left _ _ hd, Nat.div_eq_of_lt e.isLt, zero_add]
  have hmod : (finProdFinEquiv (i', e)).val % digits = e.val := by
    rw [hval, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt e.isLt]
  rw [hdiv, hmod]
  simp only [Fin.ext_iff]

omit [DecidableEq R] in
/-- The gadget product, evaluated at row `i`, is the base-weighted sum of the `digits`
slots of block `i`. -/
theorem gadgetMul_apply (base : R) {rows digits : Nat} (hd : 0 < digits)
    (v : PolyVec (Rq Φ) (rows * digits)) (i : Fin rows) :
    gadgetMul Φ base v i
      = ∑ e : Fin digits, Rq.constRq Φ (base ^ (e : ℕ)) * v (finProdFinEquiv (i, e)) := by
  rw [gadgetMul, matVecMul_apply, dot_eq_sum]
  simp only [gadgetMatrix]
  rw [← Equiv.sum_comp finProdFinEquiv (fun j => gadgetEntry Φ base i j * v j),
      Fintype.sum_prod_type]
  rw [Finset.sum_eq_single i]
  · apply Finset.sum_congr rfl
    intro e _
    rw [gadgetEntry_finProdFinEquiv Φ base hd i i e, if_pos rfl]
  · intro i' _ hne
    apply Finset.sum_eq_zero
    intro e _
    rw [gadgetEntry_finProdFinEquiv Φ base hd i i' e, if_neg hne, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ i) h

/-! ## The base-`b` gadget decomposition and its lawfulness

`gadgetDecompose dd` is the Hachi gadget inverse `G⁻¹` built from a `DigitDecomposition dd`:
block `i`'s slot `e` is the ring element whose `k`-th coefficient is the `e`-th base-`b`
digit of the `k`-th coefficient of `x i`. By the reconstruction law of `dd`, gadget
multiplication recovers `x` (`gadgetDecompose_lawful`), so the inner-outer correctness
theorem instantiates with this genuine binary decomposition. -/

variable {base : R}

/-- The base-`b` gadget decomposition (Hachi `G⁻¹`) induced by a `DigitDecomposition`. -/
def gadgetDecompose {rows digits : Nat} (dd : DigitDecomposition base digits)
    (x : PolyVec (Rq Φ) rows) : PolyVec (Rq Φ) (rows * digits) :=
  fun j => Rq.ofFinCoeff Φ Φ.φ.natDegree
    (fun k => dd.digit ((x (finProdFinEquiv.symm j).1).1.coeff k) (finProdFinEquiv.symm j).2)

/-- Value of `gadgetDecompose` at the flattened index `finProdFinEquiv (i, e)`. -/
theorem gadgetDecompose_apply {rows digits : Nat} (dd : DigitDecomposition base digits)
    (x : PolyVec (Rq Φ) rows) (i : Fin rows) (e : Fin digits) :
    gadgetDecompose Φ dd x (finProdFinEquiv (i, e))
      = Rq.ofFinCoeff Φ Φ.φ.natDegree (fun k => dd.digit ((x i).1.coeff k) e) := by
  unfold gadgetDecompose
  simp only [Equiv.symm_apply_apply]

/-- The base-`b` gadget decomposition is a lawful gadget decomposition. -/
theorem gadgetDecompose_lawful {rows digits : Nat} (hd : 0 < digits) (h1 : 1 ≤ Φ.φ.natDegree)
    (dd : DigitDecomposition base digits) :
    IsLawfulGadgetDecomposition Φ base (gadgetDecompose Φ dd (rows := rows)) := by
  intro x
  funext i
  rw [gadgetMul_apply Φ base hd]
  simp_rw [gadgetDecompose_apply Φ dd x i]
  apply Subtype.ext
  rw [CompPoly.CPolynomial.eq_iff_coeff]
  intro k
  have hsum : (∑ e : Fin digits,
        Rq.constRq Φ (base ^ (e : ℕ)) * Rq.ofFinCoeff Φ Φ.φ.natDegree
          (fun k' => dd.digit ((x i).1.coeff k') e)).1.coeff k
      = ∑ e : Fin digits,
        (Rq.constRq Φ (base ^ (e : ℕ)) * Rq.ofFinCoeff Φ Φ.φ.natDegree
          (fun k' => dd.digit ((x i).1.coeff k') e)).1.coeff k := by
    rw [← Rq.coeffHom_apply Φ k, map_sum]
    simp only [Rq.coeffHom_apply]
  have hterm : ∀ e : Fin digits,
      (Rq.constRq Φ (base ^ (e : ℕ)) * Rq.ofFinCoeff Φ Φ.φ.natDegree
          (fun k' => dd.digit ((x i).1.coeff k') e)).1.coeff k
        = base ^ (e : ℕ) * (if k < Φ.φ.natDegree then dd.digit ((x i).1.coeff k) e else 0) := by
    intro e
    rw [Rq.constRq_mul_coeff Φ h1, Rq.ofFinCoeff_coeff Φ _ (Rq.phi_natDegree_le_degree Φ)]
  rw [hsum]
  simp_rw [hterm]
  by_cases hk : k < Φ.φ.natDegree
  · simp only [if_pos hk]
    exact dd.reconstruct ((x i).1.coeff k)
  · simp only [if_neg hk, mul_zero, Finset.sum_const_zero]
    exact (Rq.coeff_eq_zero_of_natDegree_le Φ (x i) (not_lt.mp hk)).symm

end ArkLib.Lattices.Ajtai

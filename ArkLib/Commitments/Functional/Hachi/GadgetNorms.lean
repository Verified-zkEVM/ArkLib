/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tobias Rothmann
-/
import ArkLib.Commitments.Functional.Hachi.Gadget
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

/-! # Part II — the recomposition direction `G·ẑ` -/

section ZModGadgetRecomposeNorms

variable {q : ℕ} [NeZero q] [Fact (Nat.Prime q)] [BEq (ZMod q)] [LawfulBEq (ZMod q)]
  (Φ : CyclotomicModulus (ZMod q)) [IsCyclotomic Φ]

/-- **Core recomposition coefficient bound.** Each centered coefficient of an entry of the
gadget product `G_{b,rows} ·ᵥ v` is at most `(∑_{u<digits} bᵘ) · γ` whenever `‖v‖∞ ≤ γ`.

The wraparound of the `ZMod q` powers `bᵘ` is immaterial: the integer
`∑ₑ bᵉ·valMinAbs(vₑ.coeff k)` is an explicit representative of the output coefficient, and
the centered representative is minimal among all representatives (`valMinAbs_natAbs_le`).
Holds for **any** range-bounded `v` (in particular an adversarial `ẑ`), not just honest
digit decompositions. -/
theorem gadgetMul_zmod_coeff_natAbs_le {b rows digits : ℕ} (hd : 0 < digits)
    (h1 : 1 ≤ Φ.φ.natDegree) {γ : ℕ} (v : PolyVec (Rq Φ) (rows * digits))
    (hv : vecLInftyNorm Φ v ≤ γ) (i : Fin rows) {k : ℕ} (hk : k < Φ.φ.natDegree) :
    ((gadgetMul Φ (b : ZMod q) v i).1.coeff k).valMinAbs.natAbs
      ≤ (∑ u ∈ Finset.range digits, b ^ u) * γ := by
  -- the coefficient of the gadget product is the digit-weighted sum of block coefficients
  have hcoeff : (gadgetMul Φ (b : ZMod q) v i).1.coeff k
      = ∑ e : Fin digits, (b : ZMod q) ^ (e : ℕ) * (v (finProdFinEquiv (i, e))).1.coeff k := by
    rw [gadgetMul_apply Φ (b : ZMod q) hd v i, ← Rq.coeffHom_apply Φ k, map_sum]
    simp only [Rq.coeffHom_apply]
    exact Finset.sum_congr rfl fun e _ => constRq_mul_coeff Φ h1 _ _ k
  -- the explicit integer representative of that coefficient
  have hrep : ((∑ e : Fin digits,
        (b : ℤ) ^ (e : ℕ) * ((v (finProdFinEquiv (i, e))).1.coeff k).valMinAbs : ℤ) : ZMod q)
      = (gadgetMul Φ (b : ZMod q) v i).1.coeff k := by
    rw [hcoeff, Int.cast_sum]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [Int.cast_mul, Int.cast_pow, Int.cast_natCast, ZMod.coe_valMinAbs]
  -- entrywise range bound from the ℓ∞ hypothesis
  have hentry : ∀ e : Fin digits,
      ((v (finProdFinEquiv (i, e))).1.coeff k).valMinAbs.natAbs ≤ γ := fun e =>
    calc ((v (finProdFinEquiv (i, e))).1.coeff k).valMinAbs.natAbs
        ≤ Rq.lInftyNorm Φ (v (finProdFinEquiv (i, e))) :=
          Finset.le_sup (f := fun k => ((v (finProdFinEquiv (i, e))).1.coeff k).valMinAbs.natAbs)
            (Finset.mem_range.mpr hk)
      _ ≤ vecLInftyNorm Φ v :=
          Finset.le_sup (f := fun j => Rq.lInftyNorm Φ (v j)) (Finset.mem_univ _)
      _ ≤ γ := hv
  -- minimality of the centered representative + triangle over the integer representative
  calc ((gadgetMul Φ (b : ZMod q) v i).1.coeff k).valMinAbs.natAbs
      ≤ (∑ e : Fin digits,
          (b : ℤ) ^ (e : ℕ) * ((v (finProdFinEquiv (i, e))).1.coeff k).valMinAbs).natAbs :=
        valMinAbs_natAbs_le _ hrep
    _ ≤ ∑ e : Fin digits,
          ((b : ℤ) ^ (e : ℕ) * ((v (finProdFinEquiv (i, e))).1.coeff k).valMinAbs).natAbs :=
        Int.natAbs_sum_le _ _
    _ = ∑ e : Fin digits,
          b ^ (e : ℕ) * ((v (finProdFinEquiv (i, e))).1.coeff k).valMinAbs.natAbs := by
        refine Finset.sum_congr rfl fun e _ => ?_
        rw [Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_natCast]
    _ ≤ ∑ e : Fin digits, b ^ (e : ℕ) * γ :=
        Finset.sum_le_sum fun e _ => Nat.mul_le_mul_left _ (hentry e)
    _ = (∑ u ∈ Finset.range digits, b ^ u) * γ := by
        rw [← Finset.sum_mul, Fin.sum_univ_eq_sum_range (fun u => b ^ u) digits]

/-- Entrywise `ℓ∞` growth of the gadget recomposition: `‖(G·ᵥv)ᵢ‖∞ ≤ (∑_{u<digits} bᵘ)·γ`. -/
theorem gadgetMul_zmod_lInftyNorm_le {b rows digits : ℕ} (hd : 0 < digits)
    (h1 : 1 ≤ Φ.φ.natDegree) {γ : ℕ} (v : PolyVec (Rq Φ) (rows * digits))
    (hv : vecLInftyNorm Φ v ≤ γ) (i : Fin rows) :
    Rq.lInftyNorm Φ (gadgetMul Φ (b : ZMod q) v i)
      ≤ (∑ u ∈ Finset.range digits, b ^ u) * γ := by
  unfold Rq.lInftyNorm
  exact Finset.sup_le fun k hkmem =>
    gadgetMul_zmod_coeff_natAbs_le Φ hd h1 v hv i (Finset.mem_range.mp hkmem)

/-- **`ℓ∞` growth of the gadget recomposition.**
`‖G_{b,rows} ·ᵥ v‖∞ ≤ (∑_{u<digits} bᵘ) · γ` whenever `‖v‖∞ ≤ γ` — for **any**
range-bounded `v` (adversarial `ẑ` included). -/
theorem gadgetMul_zmod_vecLInftyNorm_le {b rows digits : ℕ} (hd : 0 < digits)
    (h1 : 1 ≤ Φ.φ.natDegree) {γ : ℕ} (v : PolyVec (Rq Φ) (rows * digits))
    (hv : vecLInftyNorm Φ v ≤ γ) :
    vecLInftyNorm Φ (gadgetMul Φ (b : ZMod q) v)
      ≤ (∑ u ∈ Finset.range digits, b ^ u) * γ := by
  unfold vecLInftyNorm
  exact Finset.sup_le fun i _ => gadgetMul_zmod_lInftyNorm_le Φ hd h1 v hv i

/-- **The `J`-recomposition `ℓ₂²` chain.** From the range check `‖ẑ‖∞ ≤ γ`
(Eq. (20)'s `ẑ ∈ S_b`, symmetric model), the recomposed `z = J·ẑ` satisfies
`‖z‖₂² ≤ zRecomposeL2SqBound γ b τ (deg φ) rows` — no primitive `‖z‖₂²` verifier check
is needed. -/
theorem gadgetMul_zmod_vecL2NormSq_le {b rows digits : ℕ} (hd : 0 < digits)
    (h1 : 1 ≤ Φ.φ.natDegree) {γ : ℕ} (v : PolyVec (Rq Φ) (rows * digits))
    (hv : vecLInftyNorm Φ v ≤ γ) :
    ‖gadgetMul Φ (b : ZMod q) v‖₂²
      ≤ zRecomposeL2SqBound γ b digits Φ.φ.natDegree rows := by
  calc vecL2NormSq Φ (gadgetMul Φ (b : ZMod q) v)
      ≤ rows * (Φ.φ.natDegree * (vecLInftyNorm Φ (gadgetMul Φ (b : ZMod q) v)) ^ 2) :=
        vecL2NormSq_le_card_mul_lInftyNorm_sq Φ _
    _ ≤ rows * (Φ.φ.natDegree * ((∑ u ∈ Finset.range digits, b ^ u) * γ) ^ 2) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left
          (gadgetMul_zmod_vecLInftyNorm_le Φ hd h1 v hv) 2))
    _ = zRecomposeL2SqBound γ b digits Φ.φ.natDegree rows := rfl

/-- End-to-end subtraction chain: two range-checked decompositions recompose to vectors whose
difference is `ℓ₂²`-bounded by `subL2NormSqBound (zRecomposeL2SqBound …) = 4·B_z` — exactly the
`βSq` needed for `VerifiedBlock.scaled_short` (`‖c̄ⱼ •ᵥ sⱼ‖₂² = ‖z_sib − z_cent‖₂² ≤ 4·B_z`). -/
theorem gadgetMul_zmod_sub_l2NormSq_le {b rows digits : ℕ} (hd : 0 < digits)
    (h1 : 1 ≤ Φ.φ.natDegree) {γ : ℕ} (v w : PolyVec (Rq Φ) (rows * digits))
    (hv : vecLInftyNorm Φ v ≤ γ) (hw : vecLInftyNorm Φ w ≤ γ) :
    ‖gadgetMul Φ (b : ZMod q) v - gadgetMul Φ (b : ZMod q) w‖₂²
      ≤ subL2NormSqBound (zRecomposeL2SqBound γ b digits Φ.φ.natDegree rows) :=
  sub_l2NormSq_le Φ _ _ (gadgetMul_zmod_vecL2NormSq_le Φ hd h1 v hv)
    (gadgetMul_zmod_vecL2NormSq_le Φ hd h1 w hw)

/-! ## The constants of Hachi's polynomial-evaluation reduction (`B_z`, `βSq`) -/

/-- **The reduction's derived `B_z`** (Hachi Lemma 8) — the `ℓ₂²` bound on `z = J_{2^m}·ẑ` that
follows from
Eq. (20)'s range check on `ẑ` alone (no extra verifier check): `z` has `2^m·δ` entries
(`cols = 2^m·δ`, `d = deg φ`, `τ = ⌈log_b β⌉` digits of the `J` gadget), so
`B_z = 2^m·δ · (d · ((∑_{u<τ} bᵘ)·γ)²)`.

**Honest values (paper footnote):** `γ` plays the paper's `b` — Eq. (20) checks
`ẑ ∈ S_b` (centered coefficients in `[⌈-b/2⌉, ⌈b/2⌉-1]`, magnitude `≤ b`), which the
symmetric model relaxes to `‖ẑ‖∞ ≤ γ` with `γ := b`. Then the entrywise `ℓ∞` bound
`(∑_{u<τ} bᵘ)·b = b·(b^τ-1)/(b-1) ≤ 2·b^τ` recovers (up to the constant 2) the paper's
derived `‖z⁽ʲ⁾‖∞ ≤ b^τ` (Lemma 8's `β̄ = 2b^τ` slack), and
`B_z ≈ 2^m·δ·d·b^{2τ}` up to small constants. -/
def quadEvalZL2SqBound (γ b τ d m δ : ℕ) : ℕ := zRecomposeL2SqBound γ b τ d (2 ^ m * δ)

/-- **The reduction's `βSq`** (Hachi Lemma 8) := `subL2NormSqBound B_z = 4·B_z` — the `ℓ₂²` bound
on the extracted `c̄ⱼ •ᵥ sⱼ = z_sib − z_central` fed to `VerifiedBlock.scaled_short`. -/
def quadEvalBetaSq (γ b τ d m δ : ℕ) : ℕ := subL2NormSqBound (quadEvalZL2SqBound γ b τ d m δ)

end ZModGadgetRecomposeNorms

end ArkLib.Lattices.Ajtai

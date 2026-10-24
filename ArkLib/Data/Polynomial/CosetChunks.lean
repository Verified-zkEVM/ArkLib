/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Coratger
-/
module

public import Mathlib.LinearAlgebra.Lagrange
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

/-!
# Splitting a polynomial over cosets and recombining it

Let `c, m > 0`, let `w` be a primitive root of order `c m`, and let `s ≠ 0`.

The coset `s ⟨w⟩` splits into the `c` chunks `D_i = { s w^(i + c t) : t < m }`, for `i < c`.

Write `Z_i(X) = (X / s_i)^m - 1` for `s_i = s w^i`, which vanishes exactly on `D_i`.

The Lagrange factor of chunk `i` is `L_i = ∏_(j ≠ i) Z_j / Z_j(s_i)`.

It is `1` on `D_i` and `0` on the other chunks.

## Results

* A polynomial of degree below `c m` is `∑_i L_i q_i`, for `q_i` its interpolant on `D_i`.
* Masks `Z_i t_i` leave the sum unchanged when the last mask cancels the others.

STARK provers commit to a quotient through such chunks.

Verifiers recombine the openings with the factors `L_i(ζ)`.

`chunkWeight` computes its scalar coefficient directly using field arithmetic. Its agreement
with the polynomial normalization is `chunkWeight_eq_prod_inv_eval`.
The polynomial-valued `chunkZ`, `chunkL`, `chunkInterp`, and `mask` are mathematical views:
Mathlib's formal-polynomial arithmetic and Lagrange interpolation have no executable code here.

The STARK context follows [EthStark21] and [FRI1216]. The recombination and mask cancellation
specialize the Lagrange decomposition of [HK24], Section 4.2, to a regular cyclic-coset partition.
These are algebraic identities; this module does not define a protocol or prove zero-knowledge.
See `docs/kb/papers/HK24.md` for the statement correspondence and remaining protocol obligations.

## References

* [Ben-Sasson, E., *ethSTARK Documentation*][EthStark21]
* [Haböck, U., *A summary on the FRI low degree test*][FRI1216]
* [Haböck, U., and Al Kindi, *A note on adding zero-knowledge to STARKs*][HK24]
-/

@[expose] public section

open Polynomial Finset

namespace Polynomial.CosetChunks

variable {K : Type*} [Field K] {s w : K} {c m : ℕ}

/-- Point `t` of chunk `i`: `s w^(i + c t)`. -/
def point (s w : K) (c : ℕ) (i t : ℕ) : K := s * w ^ (i + c * t)

/-- The normalized chunk polynomial `(X / (s * w ^ i)) ^ m - 1`. -/
noncomputable def chunkZ (s w : K) (m i : ℕ) : K[X] := (C (s * w ^ i)⁻¹ * X) ^ m - 1

/-- The factor for chunk `i`: multiply `chunkZ s w m j` over the other chunks `j < c`,
normalizing each factor by its value at `s * w ^ i`. -/
noncomputable def chunkL (s w : K) (c m i : ℕ) : K[X] :=
  ∏ j ∈ (range c).erase i, C ((chunkZ s w m j).eval (s * w ^ i))⁻¹ * chunkZ s w m j

/-- The interpolant of `Q` on chunk `i`. -/
noncomputable def chunkInterp (s w : K) (c m : ℕ) (Q : K[X]) (i : ℕ) : K[X] :=
  Lagrange.interpolate univ (fun t : Fin m => point s w c i t) fun t => Q.eval (point s w c i t)

/-- The computable weight of chunk `i`: the product of the inverse values of the other chunk
polynomials at `s * w ^ i`. See `chunkWeight_eq_prod_inv_eval` for the polynomial view. -/
def chunkWeight (s w : K) (c m i : ℕ) : K :=
  ∏ j ∈ (range c).erase i, (((s * w ^ j)⁻¹ * (s * w ^ i)) ^ m - 1)⁻¹

/-- The masks: `t_i` on every chunk but the last.

The last mask is minus the weighted sum of the others, so that they cancel. -/
noncomputable def mask (s w : K) (c m : ℕ) (t : ℕ → K[X]) (i : ℕ) : K[X] :=
  if i < c - 1 then t i
  else -∑ j ∈ range (c - 1), C (chunkWeight s w c m j / chunkWeight s w c m (c - 1)) * t j

/-- Evaluating the normalized chunk polynomial gives its defining field expression. -/
theorem eval_chunkZ (j : ℕ) (x : K) :
    (chunkZ s w m j).eval x = ((s * w ^ j)⁻¹ * x) ^ m - 1 := by
  simp [chunkZ]

/-- The scalar weight agrees with the inverse-evaluation product of the chunk polynomials. -/
theorem chunkWeight_eq_prod_inv_eval (i : ℕ) :
    chunkWeight s w c m i =
      ∏ j ∈ (range c).erase i, ((chunkZ s w m j).eval (s * w ^ i))⁻¹ := by
  simp only [chunkWeight, eval_chunkZ]

/-- A normalized chunk polynomial has natural degree at most `m`. -/
theorem natDegree_chunkZ_le (j : ℕ) : (chunkZ s w m j).natDegree ≤ m := by
  refine (natDegree_sub_le _ _).trans (max_le ?_ (by simp))
  refine natDegree_pow_le.trans ?_
  calc _ ≤ m * 1 := Nat.mul_le_mul_left _ ((natDegree_C_mul_le _ _).trans natDegree_X_le)
    _ = m := mul_one m

/-- A chunk factor has natural degree at most `(c - 1) * m`. -/
theorem natDegree_chunkL_le {i : ℕ} (hi : i < c) :
    (chunkL s w c m i).natDegree ≤ (c - 1) * m := by
  refine (natDegree_prod_le _ _).trans ?_
  calc _ ≤ ((range c).erase i).card • m := sum_le_card_nsmul _ _ _ fun j _ =>
        (natDegree_C_mul_le _ _).trans (natDegree_chunkZ_le (s := s) (w := w) (m := m) j)
    _ = (c - 1) * m := by rw [card_erase_of_mem (mem_range.mpr hi), card_range, smul_eq_mul]

/-- Valid chunk and point indices give an exponent below the full domain size. -/
theorem point_lt {i t : ℕ} (hi : i < c) (ht : t < m) : i + c * t < c * m := by
  nlinarith

variable (hw : IsPrimitiveRoot w (c * m)) (hs : s ≠ 0) (hc : 0 < c) (hm : 0 < m)
include hw hs hc hm

omit hm in
/-- The `m` points within a valid chunk are distinct. -/
theorem point_injective {i : ℕ} (hi : i < c) :
    Function.Injective fun t : Fin m => point s w c i t := by
  intro a b h
  have := hw.pow_inj (point_lt hi a.2) (point_lt hi b.2)
    (mul_left_cancel₀ hs h)
  exact Fin.ext (Nat.eq_of_mul_eq_mul_left hc (by omega))

omit hs hc hm in
/-- `Z_j` takes one value on each chunk: its value at the chunk's first point. -/
theorem eval_chunkZ_point (i j t : ℕ) :
    (chunkZ s w m j).eval (point s w c i t) = (chunkZ s w m j).eval (s * w ^ i) := by
  have h1 : (w ^ (c * t)) ^ m = 1 := by
    rw [← pow_mul, show c * t * m = c * m * t by ring, pow_mul, hw.pow_eq_one, one_pow]
  rw [eval_chunkZ, eval_chunkZ, point, pow_add,
    show (s * w ^ j)⁻¹ * (s * (w ^ i * w ^ (c * t))) =
        (s * w ^ j)⁻¹ * (s * w ^ i) * w ^ (c * t)
      by ring, mul_pow, h1, mul_one]

/-- `Z_j` vanishes at the first point of chunk `i` exactly when `i = j`. -/
theorem eval_chunkZ_first {i j : ℕ} (hi : i < c) (hj : j < c) :
    (chunkZ s w m j).eval (s * w ^ i) = 0 ↔ i = j := by
  have hw0 : w ≠ 0 := hw.ne_zero (Nat.mul_pos hc hm).ne'
  have e : (s * w ^ j)⁻¹ * (s * w ^ i) = w ^ i / w ^ j := by field_simp
  have hlt : ∀ a < c, a * m < c * m := fun a ha => Nat.mul_lt_mul_of_pos_right ha hm
  rw [eval_chunkZ, e, sub_eq_zero, div_pow, div_eq_one_iff_eq (pow_ne_zero _ (pow_ne_zero _ hw0)),
    ← pow_mul, ← pow_mul]
  exact ⟨fun h => Nat.eq_of_mul_eq_mul_right hm (hw.pow_inj (hlt i hi) (hlt j hj) h),
    fun h => h ▸ rfl⟩

/-- A chunk factor evaluates to the indicator of its own chunk. -/
theorem eval_chunkL_point {i i' : ℕ} (hi : i < c) (hi' : i' < c) (t : ℕ) :
    (chunkL s w c m i').eval (point s w c i t) = if i' = i then 1 else 0 := by
  simp only [chunkL, eval_prod, eval_mul, eval_C, eval_chunkZ_point hw]
  split_ifs with h
  · subst h
    refine prod_eq_one fun j hj => inv_mul_cancel₀ ?_
    obtain ⟨hne, hj⟩ := mem_erase.mp hj
    exact fun h0 => hne ((eval_chunkZ_first hw hs hc hm hi' (mem_range.mp hj)).mp h0).symm
  · exact prod_eq_zero (mem_erase.mpr ⟨fun e => h e.symm, mem_range.mpr hi⟩)
      (by rw [(eval_chunkZ_first hw hs hc hm hi hi).mpr rfl, mul_zero])

/-- A chunk interpolant has natural degree at most `m - 1`. -/
theorem natDegree_chunkInterp_le (Q : K[X]) {i : ℕ} (hi : i < c) :
    (chunkInterp s w c m Q i).natDegree ≤ m - 1 := by
  classical
  have hd := Lagrange.degree_interpolate_lt (s := (univ : Finset (Fin m)))
    (r := fun t => Q.eval (point s w c i t)) (point_injective hw hs hc hi).injOn
  rw [card_univ, Fintype.card_fin] at hd
  by_cases h0 : chunkInterp s w c m Q i = 0
  · simp [h0]
  · have := (natDegree_lt_iff_degree_lt h0).mpr hd
    omega

/-- A polynomial of degree below `c m` is recovered from its chunk interpolants. -/
theorem sum_chunkL_mul_chunkInterp (Q : K[X]) (hQ : Q.degree < (c * m : ℕ)) :
    ∑ i ∈ range c, chunkL s w c m i * chunkInterp s w c m Q i = Q := by
  classical
  have hinj : Set.InjOn (fun n => s * w ^ n) (range (c * m)) :=
    fun a ha b hb h => hw.pow_inj (mem_range.mp ha) (mem_range.mp hb) (mul_left_cancel₀ hs h)
  refine eq_of_degree_sub_lt_of_eval_finset_eq ((range (c * m)).image fun n => s * w ^ n) ?_ ?_
  · rw [card_image_of_injOn hinj, card_range]
    refine (degree_sub_le _ _).trans_lt (max_lt ?_ hQ)
    refine degree_le_natDegree.trans_lt (Nat.cast_lt.mpr ?_)
    refine lt_of_le_of_lt (natDegree_sum_le_of_forall_le _ _ (n := c * m - 1)
      fun i hi => (natDegree_mul_le).trans ?_) (by have := Nat.mul_pos hc hm; omega)
    have h1 := natDegree_chunkL_le (s := s) (w := w) (m := m) (mem_range.mp hi)
    have h2 := natDegree_chunkInterp_le hw hs hc hm Q (mem_range.mp hi)
    have : (c - 1) * m + m = c * m := by
      rw [← Nat.succ_mul, Nat.succ_eq_add_one, Nat.sub_add_cancel hc]
    omega
  · intro x hx
    obtain ⟨n, hn, rfl⟩ := mem_image.mp hx
    have hn' := mem_range.mp hn
    have hi : n % c < c := Nat.mod_lt _ hc
    have ht : n / c < m := by rw [Nat.div_lt_iff_lt_mul hc, mul_comm]; exact hn'
    have hpt : s * w ^ n = point s w c (n % c) (n / c) := by rw [point, Nat.mod_add_div]
    rw [hpt, eval_finsetSum, sum_eq_single (n % c)]
    · simp only [eval_mul, eval_chunkL_point hw hs hc hm hi hi, ↓reduceIte, one_mul, chunkInterp]
      exact Lagrange.eval_interpolate_at_node (i := ⟨n / c, ht⟩) _
        (point_injective hw hs hc hi).injOn (mem_univ _)
    · intro i' hi' hne
      simp only [eval_mul, eval_chunkL_point hw hs hc hm hi (mem_range.mp hi'), hne, ↓reduceIte,
        zero_mul]
    · exact fun h => absurd (mem_range.mpr hi) h

/-! ## Masked chunks -/

omit hw hs hc hm in
/-- `L_i Z_i` is the weight of chunk `i` times the product of all the `Z_j`. -/
theorem chunkL_mul_chunkZ {i : ℕ} (hi : i < c) :
    chunkL s w c m i * chunkZ s w m i =
      C (chunkWeight s w c m i) * ∏ j ∈ range c, chunkZ s w m j := by
  rw [chunkL, prod_mul_distrib, ← map_prod, chunkWeight_eq_prod_inv_eval, mul_assoc,
    prod_erase_mul _ _ (mem_range.mpr hi)]

/-- A valid chunk has nonzero normalization weight. -/
theorem chunkWeight_ne_zero {i : ℕ} (hi : i < c) : chunkWeight s w c m i ≠ 0 := by
  rw [chunkWeight_eq_prod_inv_eval]
  exact prod_ne_zero_iff.mpr fun _ hj => inv_ne_zero fun h =>
    (mem_erase.mp hj).1
      ((eval_chunkZ_first hw hs hc hm hi (mem_range.mp (mem_erase.mp hj).2)).mp h).symm

/-- Masking each interpolant by `Z_i` times its mask leaves the recombination unchanged. -/
theorem sum_chunkL_mul_masked (q t : ℕ → K[X]) :
    ∑ i ∈ range c, chunkL s w c m i * (q i + chunkZ s w m i * mask s w c m t i) =
      ∑ i ∈ range c, chunkL s w c m i * q i := by
  have hw' := chunkWeight_ne_zero hw hs hc hm (i := c - 1) (by omega)
  simp only [mul_add, sum_add_distrib, add_eq_left]
  have : ∀ i ∈ range c, chunkL s w c m i * (chunkZ s w m i * mask s w c m t i) =
      (∏ j ∈ range c, chunkZ s w m j) * (C (chunkWeight s w c m i) * mask s w c m t i) :=
    fun i hi => by rw [← mul_assoc, chunkL_mul_chunkZ (mem_range.mp hi)]; ring
  rw [sum_congr rfl this, ← mul_sum, mul_eq_zero]
  right
  obtain ⟨d, rfl⟩ : ∃ d, c = d + 1 := ⟨c - 1, by omega⟩
  rw [sum_range_succ]
  simp only [mask, Nat.add_sub_cancel, lt_irrefl, ↓reduceIte] at hw' ⊢
  rw [sum_congr rfl (g := fun i => C (chunkWeight s w (d + 1) m i) * t i) fun i hi => by
    simp only [mem_range.mp hi, ↓reduceIte], mul_neg, mul_sum]
  simp only [← mul_assoc, ← C_mul, mul_div_cancel₀ _ hw']
  exact add_neg_cancel _

end Polynomial.CosetChunks

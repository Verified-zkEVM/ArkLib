/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

import ArkLib.Data.CodingTheory.ListDecodability
import ArkLib.Data.CodingTheory.ListDecodability.Bounds.KKH26SumSet
import ArkLib.Data.CodingTheory.ProximityGap.Errors

/-!
# Additive-set lower bounds for Reed--Solomon codes

This module develops the useful-family and sum-set templates underlying the KKH26
Reed--Solomon lower bounds.

## Main declarations

- `sumSet` — the sum-set `Λ_𝒮 = {∑_{α ∈ S} α : S ∈ 𝒮}`.
- `IsUsefulFamily` / `IsUsefulFamilyWith` — the
  `(H, k̂, c)`-useful families (fixed elementary symmetric sums `e_i(S) = λ_i`, `i ∈ [c]`).
- `prod_X_sub_C_eq_leadingPart_add_remainder` and
  `IsUsefulFamilyWith.vanishing_decomposition` — the Vieta decomposition
  `V_S(Y) = ∑_{i=0}^{c} (-1)^i λ_i Y^{k̂-i} + p_S(Y)` with `deg p_S ≤ k̂ - c - 1` (Vieta).
- `sumSet_card_div_le_epsCa` — the CA lower-bound template
  `ε_ca(RS[F, L, k], 1 - k̂/h) ≥ |Λ_𝒮| / |F|`.
- `two_pow_mul_choose_le_card_sumSet` — over a prime field
  `𝔽_q` with `q > h^{h/2}`, the family of all `k̂`-subsets of a power-of-two-order
  subgroup `H` has `|Λ_𝒮| ≥ 2^k̂ · C(h/2, k̂)` [KKH26, Lemma 1]; proved in
  `KKH26SumSet.lean`.
- `usefulFamily_list_lower_bound` — a useful family yields a nearby-word list of size `|𝒮|`.
- `choose_le_Lambda_rs_vanilla` — the all-subsets specialization
  `|List(C, δ_min(C) - (k̂d - k + 1)/n)| ≥ C(h, k̂)`.
- `choose_le_Lambda_rs_antipodal_even` / `choose_le_Lambda_rs_antipodal_odd` — via antipodal
  pairs, list size at the same
  radius is `≥ C(h/2, k̂/2)` (`k̂` even) resp. `≥ C(h/2 - 1, (k̂-1)/2)` (`k̂` odd).

## Formulation

- A smooth domain of size `n = d·h` is represented by an explicit power-map projection
  `π : x ↦ x^d` onto a set `H` of size `h`, with fibers of size `d`. The lemma
  `Smooth.exists_pow_projection_structure` bridges from ArkLib's `ReedSolomon.Smooth`
  class (coset-of-a-2-group domains) to this package — including, for even `h`, the
  negation-closure of `H` used by the antipodal corollary — and the `*_of_smooth`
  wrappers restate the corollaries over `[Smooth domain]` exactly as in the paper.
- The codeword witness is `w_S := f - V_S(x^d) = -p_S(x^d)`, so its agreement set is
  `{x : π(x) ∈ S}`. This is the sign-consistent form of the displayed construction.
- `IsUsefulFamilyWith` includes `i = 0`; this records the conventional `λ₀ = 1` directly.
- The template uses `closeCodewordsRel` for its explicit center and `Code.Lambda` for maximized
  list size.

## References

- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*.
  2026.
- [KKH26] Krachun, Kazanin, Haböck. *Failure of proximity gaps close to capacity*.
  ePrint 2026/782.
-/

-- The statements deliberately carry `[Fintype F]` / `[DecidableEq _]` (finite-field codes,
-- decidable filters) even where a statement's *type* does not mention them; matching the
-- idiom of `ProximityGap/Errors.lean`.
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

open Polynomial Finset Code ProximityGap
open scoped NNReal BigOperators

namespace CodingTheory.AdditiveSetListDecoding

/-! ## Sum sets and useful families -/

section Defs

variable {F : Type*} [CommRing F]

/-- A family is `(H, k̂, c)`-useful with symmetric-function values `lam` when every
`S ∈ 𝒮` is a `k̂`-subset of `H` whose
elementary symmetric sums `e_i(S) = ∑_{A ⊆ S, |A| = i} ∏_{α ∈ A} α` equal `lam i` for
all `i ≤ c`. Including `i = 0` records `lam 0 = 1` for nonempty families. -/
def IsUsefulFamilyWith (H : Finset F) (khat c : ℕ) (𝒮 : Finset (Finset F))
    (lam : ℕ → F) : Prop :=
  ∀ S ∈ 𝒮, S ⊆ H ∧ S.card = khat ∧ ∀ i ≤ c, S.1.esymm i = lam i

/-- A family is `(H, k̂, c)`-useful if its members share the first `c` elementary symmetric
sums. -/
def IsUsefulFamily (H : Finset F) (khat c : ℕ) (𝒮 : Finset (Finset F)) : Prop :=
  ∃ lam : ℕ → F, IsUsefulFamilyWith H khat c 𝒮 lam

/-- The leading part `∑_{i=0}^{c} (-1)^i · λ_i · Y^{k̂-i}` of the vanishing polynomial of
a member of a useful family. -/
noncomputable def leadingPart (khat c : ℕ) (lam : ℕ → F) : F[X] :=
  ∑ i ∈ Finset.range (c + 1), C ((-1) ^ i * lam i) * X ^ (khat - i)

/-- If `|S| = k̂` and the elementary symmetric sums `e_i(S)` for `i ≤ c ≤ k̂` are given by
`lam`, then the
vanishing polynomial `V_S(Y) = ∏_{α ∈ S} (Y - α)` decomposes as
`V_S = ∑_{i=0}^{c} (-1)^i λ_i Y^{k̂-i} + p_S` with `deg p_S ≤ k̂ - c - 1`.
Mathlib's `Multiset.prod_X_sub_X_eq_sum_esymm` (Vieta) provides the full expansion. -/
theorem prod_X_sub_C_eq_leadingPart_add_remainder {S : Finset F} {khat c : ℕ} {lam : ℕ → F}
    (hcard : S.card = khat) (hck : c ≤ khat) (hesymm : ∀ i ≤ c, S.1.esymm i = lam i) :
    ∃ p : F[X], p.degree ≤ ((khat - c - 1 : ℕ) : WithBot ℕ) ∧
      ∏ α ∈ S, (X - C α) = leadingPart khat c lam + p := by
  classical
  subst hcard
  -- Full Vieta expansion of the vanishing polynomial, with each summand in
  -- `C _ * X ^ _` normal form.
  have hV : ∏ α ∈ S, (X - C α)
      = ∑ j ∈ Finset.range (S.card + 1), C ((-1) ^ j * S.1.esymm j) * X ^ (S.card - j) := by
    rw [Finset.prod_eq_multiset_prod, Multiset.prod_X_sub_X_eq_sum_esymm]
    exact Finset.sum_congr rfl fun j _ => by
      rw [map_mul, map_pow, map_neg, map_one, mul_assoc]; exact rfl
  -- Split the range at `c + 1`.
  have hsplit : ∑ j ∈ Finset.range (S.card + 1), C ((-1) ^ j * S.1.esymm j) * X ^ (S.card - j)
      = (∑ j ∈ Finset.range (c + 1), C ((-1) ^ j * S.1.esymm j) * X ^ (S.card - j))
        + ∑ j ∈ Finset.Ico (c + 1) (S.card + 1),
            C ((-1) ^ j * S.1.esymm j) * X ^ (S.card - j) := by
    rw [Finset.range_eq_Ico, Finset.range_eq_Ico,
      ← Finset.sum_Ico_consecutive _ (Nat.zero_le (c + 1)) (by omega)]
  refine ⟨∑ j ∈ Finset.Ico (c + 1) (S.card + 1),
      C ((-1) ^ j * S.1.esymm j) * X ^ (S.card - j), ?_, ?_⟩
  · refine (Polynomial.degree_sum_le _ _).trans (Finset.sup_le fun j hj => ?_)
    refine (Polynomial.degree_C_mul_X_pow_le _ _).trans ?_
    have hj' := Finset.mem_Ico.mp hj
    have hle : S.card - j ≤ S.card - c - 1 := by omega
    exact_mod_cast hle
  · rw [hV, hsplit, leadingPart]
    congr 1
    exact Finset.sum_congr rfl fun i hi => by
      rw [hesymm i (by simpa using Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))]

/-- For a `(H, k̂, c)`-useful family with values `lam`, `c < k̂`, and `S ∈ 𝒮`, the
vanishing polynomial decomposes as
`V_S(Y) = ∑_{i=0}^{c} (-1)^i λ_i Y^{k̂-i} + p_S(Y)` with `deg p_S ≤ k̂ - c - 1`. -/
theorem IsUsefulFamilyWith.vanishing_decomposition {H : Finset F} {khat c : ℕ}
    {𝒮 : Finset (Finset F)} {lam : ℕ → F} (hU : IsUsefulFamilyWith H khat c 𝒮 lam)
    (hck : c < khat) {S : Finset F} (hS : S ∈ 𝒮) :
    ∃ p : F[X], p.degree ≤ ((khat - c - 1 : ℕ) : WithBot ℕ) ∧
      ∏ α ∈ S, (X - C α) = leadingPart khat c lam + p :=
  prod_X_sub_C_eq_leadingPart_add_remainder (hU S hS).2.1 hck.le (hU S hS).2.2

end Defs

/-! ## Counting helpers: fibers of `x ↦ x^d` and root counting -/

section Counting

variable {ι : Type*} [Fintype ι] {F : Type*} [Field F] [DecidableEq F]

/-- If every `y ∈ H` has exactly `d` preimages in the domain under `x ↦ x^d`, then a
subset `S ⊆ H` pulls back to exactly `|S| · d` domain points. -/
lemma card_filter_pow_mem (domain : ι ↪ F) {d : ℕ} {H S : Finset F} (hSH : S ⊆ H)
    (hfib : ∀ y ∈ H, (Finset.univ.filter fun i => domain i ^ d = y).card = d) :
    (Finset.univ.filter fun i => domain i ^ d ∈ S).card = S.card * d := by
  classical
  have hsplit : (Finset.univ.filter fun i => domain i ^ d ∈ S)
      = S.biUnion fun y => Finset.univ.filter fun i => domain i ^ d = y := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion]
    exact ⟨fun hmem => ⟨_, hmem, rfl⟩, fun ⟨y, hy, hxy⟩ => hxy ▸ hy⟩
  rw [hsplit, Finset.card_biUnion (fun y _ z _ hyz => ?_)]
  · rw [Finset.sum_congr rfl fun y hy => hfib y (hSH hy), Finset.sum_const, smul_eq_mul]
  · simp only [Function.onFun, Finset.disjoint_left]
    intro i hi hj
    exact hyz ((Finset.mem_filter.mp hi).2.symm.trans (Finset.mem_filter.mp hj).2)

/-- A nonzero polynomial `Q` vanishes on at most `natDegree Q` points of an (injectively
embedded) evaluation domain. -/
lemma card_filter_eval_eq_zero_le_natDegree (domain : ι ↪ F) {Q : F[X]} (hQ : Q ≠ 0) :
    (Finset.univ.filter fun i => Q.eval (domain i) = 0).card ≤ Q.natDegree := by
  classical
  refine le_trans ?_ (le_trans (Multiset.toFinset_card_le Q.roots) (Polynomial.card_roots' Q))
  refine Finset.card_le_card_of_injOn domain (fun i hi => ?_)
    (fun i _ j _ hij => domain.injective hij)
  simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hi
  simp only [Finset.mem_coe, Multiset.mem_toFinset, Polynomial.mem_roots hQ]
  exact hi

end Counting

/-! ## Useful-family and sum-set templates -/

section Templates

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

omit [Fintype ι] [Nonempty ι] [DecidableEq ι] [Fintype F] [DecidableEq F] in
/-- Unfolding lemma for `ReedSolomon.evalOnPoints` applications (avoids whnf-heavy
`rfl`s through `set`-bound local definitions in the proofs below). -/
private lemma evalOnPoints_apply (domain : ι ↪ F) (p : F[X]) (i : ι) :
    ReedSolomon.evalOnPoints domain p i = p.eval (domain i) := rfl

omit [DecidableEq ι] [Fintype F] in
/-- Shared distance computation: if `u - w` is, pointwise on the domain, the evaluation of
the vanishing polynomial `V_S(x^d)` of a `k̂`-subset `S ⊆ H` (with `d`-regular fibers),
then `δᵣ(u, w) ≤ 1 - k̂/h` (as a real number; `n = d·h`). -/
lemma relHammingDist_le_of_sub_eq_vanishing (domain : ι ↪ F) {d h : ℕ}
    (hn : Fintype.card ι = d * h) (hh : 0 < h)
    {H S : Finset F} (hSH : S ⊆ H) {khat : ℕ} (hScard : S.card = khat)
    (hfib : ∀ y ∈ H, (Finset.univ.filter fun i => domain i ^ d = y).card = d)
    {u w : ι → F} (huw : ∀ i, u i - w i = (∏ α ∈ S, (X - C α)).eval (domain i ^ d)) :
    ((Code.relHammingDist u w : ℚ≥0) : ℝ) ≤ 1 - (khat : ℝ) / (h : ℝ) := by
  classical
  have hnpos : 0 < Fintype.card ι := Fintype.card_pos
  have hd0 : 0 < d := by
    rcases Nat.eq_zero_or_pos d with hd | hd
    · rw [hd, Nat.zero_mul] at hn; omega
    · exact hd
  -- `u` and `w` agree (at least) on the `k̂·d` points with `x^d ∈ S`.
  have hagree : (Finset.univ.filter fun i => domain i ^ d ∈ S).card = khat * d := by
    rw [card_filter_pow_mem domain hSH hfib, hScard]
  have hagree_le : khat * d ≤ Fintype.card ι := by
    rw [← hagree]
    exact (Finset.card_filter_le _ _).trans (le_of_eq Finset.card_univ)
  have hsub : (Finset.univ.filter fun i => u i ≠ w i)
      ⊆ Finset.univ.filter fun i => domain i ^ d ∉ S := by
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    intro hmem
    refine hi (sub_eq_zero.mp ?_)
    rw [huw i, Polynomial.eval_prod]
    exact Finset.prod_eq_zero hmem (by simp)
  have hcount : (Finset.univ.filter fun i => u i ≠ w i).card
      ≤ Fintype.card ι - khat * d := by
    have hsplit := Finset.card_filter_add_card_filter_not
      (s := Finset.univ) (p := fun i => domain i ^ d ∈ S)
    have hle := Finset.card_le_card hsub
    rw [Finset.card_univ] at hsplit
    omega
  have hdist : hammingDist u w ≤ Fintype.card ι - khat * d := by
    simpa [hammingDist] using hcount
  -- Cast to ℝ and conclude by arithmetic (`n = d·h`).
  have hrel : ((Code.relHammingDist u w : ℚ≥0) : ℝ)
      = (hammingDist u w : ℝ) / (Fintype.card ι : ℝ) := by
    rw [Code.relHammingDist, NNRat.cast_div, NNRat.cast_natCast, NNRat.cast_natCast]
  rw [hrel]
  have hcast : (hammingDist u w : ℝ) ≤ (Fintype.card ι : ℝ) - (khat : ℝ) * d := by
    calc (hammingDist u w : ℝ) ≤ ((Fintype.card ι - khat * d : ℕ) : ℝ) := by
          exact_mod_cast hdist
      _ = (Fintype.card ι : ℝ) - (khat : ℝ) * d := by rw [Nat.cast_sub hagree_le, Nat.cast_mul]
  calc (hammingDist u w : ℝ) / (Fintype.card ι : ℝ)
      ≤ ((Fintype.card ι : ℝ) - (khat : ℝ) * d) / (Fintype.card ι : ℝ) := by
        gcongr
    _ = 1 - (khat : ℝ) / (h : ℝ) := by
        rw [hn]
        have hd' : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hd0.ne'
        have hh' : (h : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hh.ne'
        push_cast
        field_simp

omit [DecidableEq ι] in
set_option linter.unusedVariables false in
/-- Let the evaluation domain have size `n = d·h`, let `H : Finset F` with `|H| = h` be
`d`-regularly covered by `x ↦ x^d`, let `𝒮` be a `(H, k̂, c)`-useful family with `c < k̂`, and let
`(k̂ - c - 1)·d < k ≤ k̂·d`. Then there is a word `f` with
`|List(RS[F, L, k], 1 - k̂/h, f)| ≥ |𝒮|`.

The witness is `f(x) = ∑_{i=0}^{c} (-1)^i λ_i x^{(k̂-i)d}`; each `S ∈ 𝒮` contributes the
codeword `w_S := f - V_S(x^d) = -p_S(x^d)`, which agrees with `f` on the `k̂·d` points
`{x : x^d ∈ S}`. -/
theorem usefulFamily_list_lower_bound (domain : ι ↪ F) {d h khat c k : ℕ}
    (hn : Fintype.card ι = d * h)
    {H : Finset F} (hHcard : H.card = h)
    (hfib : ∀ y ∈ H, (Finset.univ.filter fun i => domain i ^ d = y).card = d)
    {𝒮 : Finset (Finset F)} (hU : IsUsefulFamily H khat c 𝒮) (hck : c < khat)
    (hk1 : (khat - c - 1) * d < k) (hk2 : k ≤ khat * d) :
    ∃ f : ι → F, 𝒮.card ≤
      (closeCodewordsRel (↑(ReedSolomon.code domain k) : Set (ι → F)) f
        (1 - (khat : ℝ) / (h : ℝ))).ncard := by
  classical
  obtain ⟨lam, hUW⟩ := hU
  rcases 𝒮.eq_empty_or_nonempty with rfl | h𝒮ne
  · exact ⟨fun _ => 0, by simp⟩
  have hnpos : 0 < Fintype.card ι := Fintype.card_pos
  have hd0 : 0 < d := by
    rcases Nat.eq_zero_or_pos d with hd | hd
    · rw [hd, Nat.zero_mul] at hn; omega
    · exact hd
  have hh0 : 0 < h := by
    rcases Nat.eq_zero_or_pos h with hh | hh
    · rw [hh, Nat.mul_zero] at hn; omega
    · exact hh
  -- The word `f(x) = ∑_{i=0}^{c} (-1)^i λ_i x^{(k̂-i)d}` and the per-`S` codewords
  -- `w_S = f - V_S(x^d)`.
  set f : ι → F := ReedSolomon.evalOnPoints domain ((leadingPart khat c lam).comp (X ^ d))
    with hf
  set Φ : Finset F → (ι → F) := fun S =>
    ReedSolomon.evalOnPoints domain
      ((leadingPart khat c lam - ∏ α ∈ S, (X - C α)).comp (X ^ d)) with hΦ
  refine ⟨f, ?_⟩
  -- Each `w_S` lies in the list around `f` at radius `1 - k̂/h`.
  have hmem : ∀ S ∈ 𝒮, Φ S ∈ closeCodewordsRel
      (↑(ReedSolomon.code domain k) : Set (ι → F)) f (1 - (khat : ℝ) / (h : ℝ)) := by
    intro S hS
    obtain ⟨hSH, hScard, hesymm⟩ := hUW S hS
    obtain ⟨p, hpdeg, hpeq⟩ :=
      prod_X_sub_C_eq_leadingPart_add_remainder hScard hck.le hesymm
    have hlp : leadingPart khat c lam - ∏ α ∈ S, (X - C α) = -p := by rw [hpeq]; ring
    rw [Code.mem_closeCodewordsRel_iff]
    refine ⟨?_, ?_⟩
    · -- `w_S ∈ RS[F, L, k]`: it evaluates `-p_S(x^d)` of degree `≤ (k̂-c-1)d < k`.
      have hnd : ((leadingPart khat c lam - ∏ α ∈ S, (X - C α)).comp (X ^ d)).natDegree
          < k := by
        calc ((leadingPart khat c lam - ∏ α ∈ S, (X - C α)).comp (X ^ d)).natDegree
            ≤ (leadingPart khat c lam - ∏ α ∈ S, (X - C α)).natDegree
                * (X ^ d : F[X]).natDegree := Polynomial.natDegree_comp_le
          _ ≤ (khat - c - 1) * d := by
              rw [Polynomial.natDegree_X_pow, hlp, Polynomial.natDegree_neg]
              exact Nat.mul_le_mul_right d (Polynomial.natDegree_le_iff_degree_le.mpr hpdeg)
          _ < k := hk1
      simp only [hΦ]
      exact ReedSolomon.mem_code_of_polynomial_of_degree_lt_of_eval _
        (lt_of_le_of_lt Polynomial.degree_le_natDegree (by exact_mod_cast hnd))
        (fun i => evalOnPoints_apply domain _ i)
    · -- `δᵣ(f, w_S) ≤ 1 - k̂/h`: `f - w_S = V_S(x^d)` vanishes on the `k̂·d` points
      -- with `x^d ∈ S`.
      have hsub_eq : ∀ i, f i - Φ S i = (∏ α ∈ S, (X - C α)).eval (domain i ^ d) := by
        intro i
        simp only [hf, hΦ, evalOnPoints_apply, Polynomial.eval_comp, Polynomial.eval_pow,
          Polynomial.eval_X, Polynomial.eval_sub]
        ring
      have hball := relHammingDist_le_of_sub_eq_vanishing domain hn hh0 hSH hScard hfib hsub_eq
      simpa using hball
  -- Distinct `S` give distinct codewords `w_S`.
  have hinj : Set.InjOn Φ ↑𝒮 := by
    intro S hS T hT hST
    obtain ⟨hSH, hScard, -⟩ := hUW S (Finset.mem_coe.mp hS)
    obtain ⟨hTH, hTcard, -⟩ := hUW T (Finset.mem_coe.mp hT)
    by_contra hne
    -- The vanishing polynomials differ (roots recover the set), ...
    have hprod_ne : (∏ α ∈ S, (X - C α)) ≠ ∏ α ∈ T, (X - C α) := by
      intro heq
      refine hne (Finset.val_inj.mp ?_)
      have := congrArg Polynomial.roots heq
      rwa [Polynomial.roots_prod_X_sub_C, Polynomial.roots_prod_X_sub_C] at this
    set P : F[X] := (∏ α ∈ S, (X - C α)) - ∏ α ∈ T, (X - C α) with hP
    have hPne : P ≠ 0 := sub_ne_zero.mpr hprod_ne
    -- ... their difference has degree `< k̂` (both are monic of degree `k̂`), ...
    have hdegS : (∏ α ∈ S, (X - C α)).degree = (khat : WithBot ℕ) := by
      rw [Polynomial.degree_prod]
      simp [Polynomial.degree_X_sub_C, hScard]
    have hdegT : (∏ α ∈ T, (X - C α)).degree = (khat : WithBot ℕ) := by
      rw [Polynomial.degree_prod]
      simp [Polynomial.degree_X_sub_C, hTcard]
    have hPdeg : P.natDegree < khat := by
      rw [Polynomial.natDegree_lt_iff_degree_lt hPne]
      refine lt_of_lt_of_eq (Polynomial.degree_sub_lt_left (hdegS.trans hdegT.symm) ?_ ?_) hdegS
      · exact (Polynomial.monic_prod_of_monic _ _
          fun α _ => Polynomial.monic_X_sub_C α).ne_zero
      · rw [(Polynomial.monic_prod_of_monic _ _ fun α _ =>
              Polynomial.monic_X_sub_C α).leadingCoeff,
          (Polynomial.monic_prod_of_monic _ _ fun α _ => Polynomial.monic_X_sub_C α).leadingCoeff]
    -- ... yet `P(x^d)` vanishes on all `n` domain points: contradiction with `k̂ ≤ h`.
    have hQzero : ∀ i, (P.comp (X ^ d)).eval (domain i) = 0 := by
      intro i
      have h1 := congrFun hST i
      simp only [hΦ, evalOnPoints_apply, Polynomial.eval_comp, Polynomial.eval_pow,
        Polynomial.eval_X, Polynomial.eval_sub] at h1
      simp only [hP, Polynomial.eval_comp, Polynomial.eval_pow, Polynomial.eval_X,
        Polynomial.eval_sub]
      linear_combination -h1
    have hQne : P.comp (X ^ d) ≠ 0 := by
      intro hzero
      rcases (Polynomial.comp_eq_zero_iff).mp hzero with hP0 | ⟨-, hXd⟩
      · exact hPne hP0
      · have := congrArg Polynomial.natDegree hXd
        rw [Polynomial.natDegree_X_pow, Polynomial.natDegree_C] at this
        omega
    have hcard := card_filter_eval_eq_zero_le_natDegree domain hQne
    have hfull : (Finset.univ.filter fun i => (P.comp (X ^ d)).eval (domain i) = 0)
        = Finset.univ := Finset.filter_true_of_mem fun i _ => hQzero i
    rw [hfull, Finset.card_univ] at hcard
    have hkh : khat ≤ h := by
      rw [← hScard, ← hHcard]
      exact Finset.card_le_card hSH
    have hnd : (P.comp (X ^ d)).natDegree ≤ (khat - 1) * d := by
      calc (P.comp (X ^ d)).natDegree
          ≤ P.natDegree * (X ^ d : F[X]).natDegree := Polynomial.natDegree_comp_le
        _ ≤ (khat - 1) * d := by
            rw [Polynomial.natDegree_X_pow]
            exact Nat.mul_le_mul_right d (by omega)
    have h1 : (khat - 1) * d < khat * d := (Nat.mul_lt_mul_right hd0).mpr (by omega)
    have h2 : khat * d ≤ d * h := by
      calc khat * d ≤ h * d := Nat.mul_le_mul_right d hkh
        _ = d * h := Nat.mul_comm h d
    omega
  -- Count: the image of `𝒮` is a `|𝒮|`-element subset of the list.
  calc 𝒮.card = (𝒮.image Φ).card := (Finset.card_image_of_injOn hinj).symm
    _ = ((𝒮.image Φ : Finset (ι → F)) : Set (ι → F)).ncard :=
        (Set.ncard_coe_finset _).symm
    _ ≤ (closeCodewordsRel (↑(ReedSolomon.code domain k) : Set (ι → F)) f
          (1 - (khat : ℝ) / (h : ℝ))).ncard := by
        refine Set.ncard_le_ncard (fun x hx => ?_) (Set.toFinite _)
        simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at hx
        obtain ⟨S, hS, rfl⟩ := hx
        exact hmem S hS

omit [Fintype ι] [Nonempty ι] [DecidableEq ι] [Fintype F] [DecidableEq F] in
/-- The first elementary symmetric sum of a finite set is its sum:
`e₁(S) = ∑_{α ∈ S} α`. -/
private lemma esymm_one_eq_sum (S : Finset F) : S.1.esymm 1 = ∑ α ∈ S, α := by
  classical
  rw [Multiset.esymm, Multiset.powersetCard_one, Multiset.map_map]
  simp only [Function.comp_apply, Multiset.prod_singleton]
  rw [← Finset.sum_eq_multiset_sum]

omit [DecidableEq ι] in
/-- Let the evaluation domain have
size `n = d·h`, let `H : Finset F` with `|H| = h` be `d`-regularly covered by `x ↦ x^d`,
let `𝒮` be a family of `k̂`-subsets of `H`, and let `(k̂-2)·d < k ≤ (k̂-1)·d`. Then for
`C := RS[F, L, k]`, the correlated agreement error at radius `1 - k̂/h` is at least
`|Λ_𝒮| / |F|`.

The witness pair is `(f₀, -f₁) = (x^{k̂d}, -x^{(k̂-1)d})`: the second row is `> δ`-far
from `C`, while for every `γ = ∑_{α ∈ S} α ∈ Λ_𝒮` the fold `f₀ - γ·f₁` agrees with the
codeword `-p_S(x^d)` on the `k̂·d` points `{x : x^d ∈ S}`. -/
theorem sumSet_card_div_le_epsCa (domain : ι ↪ F) {d h khat k : ℕ}
    (hn : Fintype.card ι = d * h)
    {H : Finset F} (hHcard : H.card = h)
    (hfib : ∀ y ∈ H, (Finset.univ.filter fun i => domain i ^ d = y).card = d)
    {𝒮 : Finset (Finset F)} (h𝒮 : ∀ S ∈ 𝒮, S ⊆ H ∧ S.card = khat)
    (hk1 : (khat - 2) * d < k) (hk2 : k ≤ (khat - 1) * d) :
    ((sumSet 𝒮).card : ENNReal) / (Fintype.card F : ENNReal) ≤
      epsCa (F := F) (A := F) (↑(ReedSolomon.code domain k) : Set (ι → F))
        (1 - (khat : ℝ) / (h : ℝ)).toNNReal (1 - (khat : ℝ) / (h : ℝ)).toNNReal := by
  classical
  set Cset : Set (ι → F) := (↑(ReedSolomon.code domain k) : Set (ι → F)) with hC
  set δ : ℝ≥0 := (1 - (khat : ℝ) / (h : ℝ)).toNNReal with hδdef
  -- Step 0: dispose of `𝒮 = ∅`.
  rcases 𝒮.eq_empty_or_nonempty with rfl | h𝒮ne
  · simp [sumSet]
  obtain ⟨S₀, hS₀mem⟩ := h𝒮ne
  obtain ⟨hS₀H, hS₀card⟩ := h𝒮 S₀ hS₀mem
  -- Basic positivity facts.
  have hnpos : 0 < Fintype.card ι := Fintype.card_pos
  have hd0 : 0 < d := by
    rcases Nat.eq_zero_or_pos d with hd | hd
    · rw [hd, Nat.zero_mul] at hn; omega
    · exact hd
  have hh0 : 0 < h := by
    rcases Nat.eq_zero_or_pos h with hh | hh
    · rw [hh, Nat.mul_zero] at hn; omega
    · exact hh
  have hkh : khat ≤ h := by rw [← hS₀card, ← hHcard]; exact Finset.card_le_card hS₀H
  have hkhat2 : 2 ≤ khat := by
    -- `(khat - 2) * d < k ≤ (khat - 1) * d`, and `d > 0`, forces `khat ≥ 2`.
    by_contra hlt
    push Not at hlt
    interval_cases khat <;> omega
  have hk1' : 1 ≤ khat := by omega
  have hh' : (h : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hh0.ne'
  have hd' : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hd0.ne'
  -- Step 1: reals for `δ`.
  have hkhle : (khat : ℝ) / (h : ℝ) ≤ 1 := by
    rw [div_le_one (by positivity)]; exact_mod_cast hkh
  have hδnn : (0 : ℝ) ≤ 1 - (khat : ℝ) / (h : ℝ) := by linarith
  have hδcoe : (δ : ℝ) = 1 - (khat : ℝ) / (h : ℝ) := by
    rw [hδdef, Real.coe_toNNReal _ hδnn]
  have hδle1 : δ ≤ 1 := by
    rw [← NNReal.coe_le_coe, hδcoe]
    have : (0 : ℝ) ≤ (khat : ℝ) / (h : ℝ) := by positivity
    push_cast; linarith
  have h1subδ : ((1 - δ : ℝ≥0) : ℝ) = (khat : ℝ) / (h : ℝ) := by
    rw [NNReal.coe_sub hδle1, hδcoe]; simp
  -- Step 2: the witness stack `u = (x^{k̂d}, -x^{(k̂-1)d})`.
  set u : Code.WordStack F (Fin 2) ι :=
    ![ReedSolomon.evalOnPoints domain (X ^ (khat * d)),
      -(ReedSolomon.evalOnPoints domain (X ^ ((khat - 1) * d)))] with hu
  have hu0 : u 0 = ReedSolomon.evalOnPoints domain (X ^ (khat * d)) := by
    rw [hu]; simp [Matrix.cons_val_zero]
  have hu1 : u 1 = -(ReedSolomon.evalOnPoints domain (X ^ ((khat - 1) * d))) := by
    rw [hu]; simp [Matrix.cons_val_one]
  -- Step 3: reduce `epsCa` to its `u`-summand, with the `if_neg` branch.
  rw [epsCa]
  refine le_iSup_of_le u ?_
  -- Step 4: the pair `u` is NOT jointly `δ`-close, so we take the `Pr` branch.
  have hnj : ¬ Code.jointProximity Cset (u := u) δ := by
    rw [← Code.jointAgreement_iff_jointProximity]
    rintro ⟨T, hT, v, hv⟩
    -- `hT : (T.card : ℝ) ≥ (1 - δ) * card ι` and `(hv 1)` : `v 1 ∈ C`,
    -- `T ⊆ agree(v 1, u 1)`.
    obtain ⟨hv1mem, hv1sub⟩ := hv 1
    -- `T.card ≥ khat * d`.
    have hTge : khat * d ≤ T.card := by
      have hcardι : (Fintype.card ι : ℝ) = (d : ℝ) * (h : ℝ) := by rw [hn]; push_cast; ring
      have : (khat * d : ℝ) ≤ (T.card : ℝ) := by
        calc (khat * d : ℝ) = ((khat : ℝ) / (h : ℝ)) * ((d : ℝ) * (h : ℝ)) := by
              field_simp
          _ = ((1 - δ : ℝ≥0) : ℝ) * (Fintype.card ι : ℝ) := by rw [h1subδ, hcardι]
          _ ≤ (T.card : ℝ) := by
              have := hT
              rw [ge_iff_le, ← NNReal.coe_le_coe] at this
              push_cast at this ⊢
              convert this using 2
      exact_mod_cast this
    -- `v 1 ∈ C`: obtain its polynomial `q`, `deg q < k`.
    rw [hC, SetLike.mem_coe, ReedSolomon.mem_code_iff_exists_polynomial] at hv1mem
    obtain ⟨q, hqdeg, hqeq⟩ := hv1mem
    -- `Q := q + X^{(khat-1)d}` is nonzero and vanishes on the domain points of `T`.
    set Q : F[X] := q + X ^ ((khat - 1) * d) with hQ
    have hqnd : q.natDegree < k := by
      rcases eq_or_ne q 0 with hq0 | hq0
      · rw [hq0]; simp; omega
      · rw [Polynomial.natDegree_lt_iff_degree_lt hq0]; exact hqdeg
    have hkle : k ≤ (khat - 1) * d := hk2
    have hQne : Q ≠ 0 := by
      intro h0
      have : q = -(X ^ ((khat - 1) * d)) := by rw [hQ] at h0; linear_combination h0
      have hqd : q.degree = ((khat - 1) * d : ℕ) := by
        rw [this, Polynomial.degree_neg, Polynomial.degree_X_pow]
      have : ((khat - 1) * d : ℕ) < (k : ℕ) := by
        rw [hqd] at hqdeg; exact_mod_cast hqdeg
      omega
    have hQzero : T ⊆ Finset.univ.filter (fun j => Q.eval (domain j) = 0) := by
      intro j hj
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ j, ?_⟩
      have hjsub := Finset.subset_iff.mp hv1sub hj
      rw [Finset.mem_filter] at hjsub
      have hvj : v 1 j = u 1 j := hjsub.2
      rw [hu1, Pi.neg_apply, evalOnPoints_apply, Polynomial.eval_pow, Polynomial.eval_X] at hvj
      have hqj : q.eval (domain j) = v 1 j := by
        rw [hqeq, evalOnPoints_apply]
      rw [hQ, Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X, hqj, hvj]
      ring
    have hcard := card_filter_eval_eq_zero_le_natDegree domain hQne
    -- `natDegree Q ≤ (khat - 1) * d`.
    have hQnd : Q.natDegree ≤ (khat - 1) * d := by
      rw [hQ]
      refine (Polynomial.natDegree_add_le _ _).trans ?_
      rw [Polynomial.natDegree_X_pow]
      exact max_le (by omega) le_rfl
    have hTle : T.card ≤ Q.natDegree :=
      (Finset.card_le_card hQzero).trans hcard
    -- Contradiction: `khat * d ≤ T.card ≤ natDegree Q ≤ (khat - 1) * d < khat * d`.
    have hlt : (khat - 1) * d < khat * d := (Nat.mul_lt_mul_right hd0).mpr (by omega)
    omega
  rw [if_neg hnj]
  have : DecidablePred (fun γ : F => δᵣ(u 0 + γ • u 1, Cset) ≤ (δ : ℝ≥0)) :=
    Classical.decPred _
  -- Step 6: every `γ ∈ Λ_𝒮` makes the fold `u 0 + γ • u 1` `δ`-close to `C`.
  have hsubset : sumSet 𝒮 ⊆
      Finset.univ.filter (fun γ : F => δᵣ(u 0 + γ • u 1, Cset) ≤ (δ : ℝ≥0)) := by
    intro γ hγ
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ γ, ?_⟩
    -- `γ = ∑_{α ∈ S} α` for some `S ∈ 𝒮`.
    rw [sumSet, Finset.mem_image] at hγ
    obtain ⟨S, hSmem, rfl⟩ := hγ
    obtain ⟨hSH, hScard⟩ := h𝒮 S hSmem
    -- The `(H, k̂, 1)`-useful structure of `{S}` with `λ = (1, γ)`.
    set lam : ℕ → F := fun i => if i = 0 then 1 else ∑ α ∈ S, α with hlam
    have hesymm : ∀ i ≤ 1, S.1.esymm i = lam i := by
      intro i hi
      interval_cases i
      · simp [Multiset.esymm, hlam]
      · rw [esymm_one_eq_sum]; simp [hlam]
    obtain ⟨p, hpdeg, hpeq⟩ :=
      prod_X_sub_C_eq_leadingPart_add_remainder hScard (by omega : (1 : ℕ) ≤ khat) hesymm
    -- The codeword `w := -p_S(x^d) = (leadingPart - V_S)(x^d)`.
    set w : ι → F := ReedSolomon.evalOnPoints domain
      ((leadingPart khat 1 lam - ∏ α ∈ S, (X - C α)).comp (X ^ d)) with hw
    have hlp : leadingPart khat 1 lam - ∏ α ∈ S, (X - C α) = -p := by rw [hpeq]; ring
    -- `w ∈ C`: its polynomial has degree `≤ (k̂-2)·d < k`.
    have hwmem : w ∈ Cset := by
      rw [hC]
      have hnd :
          ((leadingPart khat 1 lam - ∏ α ∈ S, (X - C α)).comp (X ^ d)).natDegree < k := by
        calc ((leadingPart khat 1 lam - ∏ α ∈ S, (X - C α)).comp (X ^ d)).natDegree
            ≤ (leadingPart khat 1 lam - ∏ α ∈ S, (X - C α)).natDegree
                * (X ^ d : F[X]).natDegree := Polynomial.natDegree_comp_le
          _ ≤ (khat - 2) * d := by
              rw [Polynomial.natDegree_X_pow, hlp, Polynomial.natDegree_neg]
              refine Nat.mul_le_mul_right d ?_
              have : p.natDegree ≤ khat - 1 - 1 :=
                Polynomial.natDegree_le_iff_degree_le.mpr hpdeg
              omega
          _ < k := hk1
      exact ReedSolomon.mem_code_of_polynomial_of_degree_lt_of_eval _
        (lt_of_le_of_lt Polynomial.degree_le_natDegree (by exact_mod_cast hnd))
        (fun i => evalOnPoints_apply domain _ i)
    -- Pointwise: `(u 0 + γ • u 1) i = (leadingPart)(x^d)` at `domain i`, so subtracting `w`
    -- (which is `(leadingPart - V_S)(x^d)`) leaves exactly `V_S(x^d)`.
    have hfold : ∀ i, (u 0 + (∑ α ∈ S, α) • u 1) i
        = ((leadingPart khat 1 lam).comp (X ^ d)).eval (domain i) := by
      intro i
      rw [hu0, hu1]
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.neg_apply, evalOnPoints_apply,
        Polynomial.eval_pow, Polynomial.eval_X]
      -- Unfold `leadingPart khat 1 lam` (sum over `range 2`).
      simp only [leadingPart, Finset.sum_range_succ, Finset.sum_range_zero, zero_add, hlam,
        pow_zero, pow_one, Nat.sub_zero, Polynomial.eval_comp, Polynomial.eval_add,
        Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C,
        if_true, if_neg (by norm_num : (1 : ℕ) ≠ 0)]
      rw [← pow_mul, ← pow_mul, Nat.mul_comm d khat, Nat.mul_comm d (khat - 1)]
      ring
    have hsub_eq : ∀ i, (u 0 + (∑ α ∈ S, α) • u 1) i - w i
        = (∏ α ∈ S, (X - C α)).eval (domain i ^ d) := by
      intro i
      rw [hfold i, hw, evalOnPoints_apply]
      simp only [Polynomial.eval_comp, Polynomial.eval_pow, Polynomial.eval_X,
        Polynomial.eval_sub]
      ring
    -- Distance bound: `δᵣ(u 0 + γ•u 1, C) ≤ δᵣ(·, w) ≤ 1 - k̂/h = δ`.
    have hball := relHammingDist_le_of_sub_eq_vanishing domain hn hh0 hSH hScard hfib hsub_eq
    have hle : δᵣ(u 0 + (∑ α ∈ S, α) • u 1, Cset)
        ≤ (Code.relHammingDist (u 0 + (∑ α ∈ S, α) • u 1) w : ENNReal) :=
      Code.relDistFromCode_le_relDist_to_mem _ w hwmem
    refine hle.trans ?_
    -- `(relHammingDist · w : ℝ≥0) ≤ δ` in `ℝ≥0`, then lift to `ENNReal`.
    have hrnn : ((Code.relHammingDist (u 0 + (∑ α ∈ S, α) • u 1) w : ℚ≥0) : ℝ≥0)
        ≤ δ := by
      rw [← NNReal.coe_le_coe, hδcoe]
      exact_mod_cast hball
    -- Reconcile `((q : ℚ≥0) : ENNReal)` with `((((q : ℚ≥0) : ℝ≥0)) : ENNReal)`.
    calc (Code.relHammingDist (u 0 + (∑ α ∈ S, α) • u 1) w : ENNReal)
        = (((Code.relHammingDist (u 0 + (∑ α ∈ S, α) • u 1) w : ℚ≥0) : ℝ≥0) :
            ENNReal) := by
          norm_cast
      _ ≤ ((δ : ℝ≥0) : ENNReal) := by exact_mod_cast hrnn
  -- Step 5: rewrite the probability as a cardinality fraction and compare.
  rw [Probability.prob_uniform_eq_card_filter_div_card
    (P := fun γ : F => δᵣ(u 0 + γ • u 1, Cset) ≤ (δ : ℝ≥0))]
  rw [show ((Fintype.card F : ℝ≥0) : ENNReal) = (Fintype.card F : ENNReal) from by
        rw [ENNReal.coe_natCast],
    show (((Finset.univ.filter
        (fun γ : F => δᵣ(u 0 + γ • u 1, Cset) ≤ (δ : ℝ≥0))).card : ℝ≥0) : ENNReal)
        = ((Finset.univ.filter
          (fun γ : F => δᵣ(u 0 + γ • u 1, Cset) ≤ (δ : ℝ≥0))).card : ENNReal) from by
        rw [ENNReal.coe_natCast]]
  refine ENNReal.div_le_div_right ?_ _
  exact_mod_cast Finset.card_le_card hsubset

end Templates

/-! ## Instantiations: the two corollaries -/

section Corollaries

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

omit [DecidableEq ι] [Fintype F] in
/-- Radius bookkeeping for the corollaries: for `RS[F, L, k]` with `n = d·h` and
`k ≤ k̂·d ≤ n`, the radius `δ_min(C) - (k̂d - k + 1)/n` equals `1 - k̂/h`
(via `ReedSolomon.minDist_eq'`: `minDist = n - k + 1`). -/
lemma minRelDist_sub_eq (domain : ι ↪ F) {d h khat k : ℕ}
    (hn : Fintype.card ι = d * h) (hk0 : 0 < k) (hkh : khat ≤ h)
    (hk2 : k ≤ khat * d) :
    ((δᵣ (↑(ReedSolomon.code domain k) : Set (ι → F)) : ℚ≥0) : ℝ)
        - ((khat * d - k + 1 : ℕ) : ℝ) / (Fintype.card ι : ℝ)
      = 1 - (khat : ℝ) / (h : ℝ) := by
  classical
  have hnpos : 0 < Fintype.card ι := Fintype.card_pos
  have hd0 : 0 < d := by
    rcases Nat.eq_zero_or_pos d with hd | hd
    · rw [hd, Nat.zero_mul] at hn; omega
    · exact hd
  have hh0 : 0 < h := by
    rcases Nat.eq_zero_or_pos h with hh | hh
    · rw [hh, Nat.mul_zero] at hn; omega
    · exact hh
  have : NeZero k := ⟨hk0.ne'⟩
  have hkn : k ≤ Fintype.card ι := by
    calc k ≤ khat * d := hk2
      _ ≤ h * d := Nat.mul_le_mul_right d hkh
      _ = Fintype.card ι := by rw [hn, Nat.mul_comm]
  -- `δ_min(C) = (n - k + 1)/n` via `minDist_eq'` and the ℚ-valued bridge.
  have hmd : Code.minDist (↑(ReedSolomon.code domain k) : Set (ι → F))
      = Fintype.card ι - k + 1 := ReedSolomon.minDist_of_le hkn
  have hbridge := Code.minDist_div_card_eq_minRelHammingDistCode
    (↑(ReedSolomon.code domain k) : Set (ι → F))
  have hq : ((δᵣ (↑(ReedSolomon.code domain k) : Set (ι → F)) : ℚ≥0) : ℝ)
      = ((Fintype.card ι - k + 1 : ℕ) : ℝ) / (Fintype.card ι : ℝ) := by
    have h2 : ((Code.minDist (↑(ReedSolomon.code domain k) : Set (ι → F)) : ℝ))
        / (Fintype.card ι : ℝ)
        = ((δᵣ (↑(ReedSolomon.code domain k) : Set (ι → F)) : ℚ≥0) : ℝ) := by
      have := congrArg (fun q : ℚ => (q : ℝ)) hbridge
      simpa [Rat.cast_nnratCast] using this
    rw [← h2, hmd]
  rw [hq, hn]
  have hkdh : k ≤ d * h := by rw [← hn]; exact hkn
  have hd' : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hd0.ne'
  have hh' : (h : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hh0.ne'
  have h1 : ((d * h - k + 1 : ℕ) : ℝ) = (d : ℝ) * h - k + 1 := by
    push_cast [Nat.cast_sub hkdh]; ring
  have h2 : ((khat * d - k + 1 : ℕ) : ℝ) = (khat : ℝ) * d - k + 1 := by
    push_cast [Nat.cast_sub hk2]; ring
  rw [h1, h2]
  push_cast
  field_simp
  ring

omit [DecidableEq ι] in
/-- For a Reed--Solomon code over a domain of size
`n = d·h` projecting `d`-regularly onto `H` (`|H| = h`), with `1 ≤ k̂ < h` and
`(k̂-1)·d < k ≤ k̂·d`:
`|List(C, δ_min(C) - (k̂d - k + 1)/n)| ≥ C(h, k̂)`.

This instantiates the useful-family template with the `(H, k̂, 0)`-useful family of all
`k̂`-subsets of `H`. -/
theorem choose_le_Lambda_rs_vanilla (domain : ι ↪ F) {d h khat k : ℕ}
    (hn : Fintype.card ι = d * h)
    {H : Finset F} (hHcard : H.card = h)
    (hfib : ∀ y ∈ H, (Finset.univ.filter fun i => domain i ^ d = y).card = d)
    (hkhat : 1 ≤ khat) (hkh : khat < h)
    (hk1 : (khat - 1) * d < k) (hk2 : k ≤ khat * d) :
    (h.choose khat : ℕ∞) ≤
      Lambda (↑(ReedSolomon.code domain k) : Set (ι → F))
        (((δᵣ (↑(ReedSolomon.code domain k) : Set (ι → F)) : ℚ≥0) : ℝ)
          - ((khat * d - k + 1 : ℕ) : ℝ) / (Fintype.card ι : ℝ)) := by
  classical
  have hk0 : 0 < k := Nat.pos_of_ne_zero fun hk => by omega
  rw [minRelDist_sub_eq domain hn hk0 hkh.le hk2]
  -- The `(H, k̂, 0)`-useful family of all `k̂`-subsets of `H`.
  have hU : IsUsefulFamily H khat 0 (H.powersetCard khat) := by
    refine ⟨fun _ => 1, fun S hS => ?_⟩
    obtain ⟨hsub, hcard⟩ := Finset.mem_powersetCard.mp hS
    refine ⟨hsub, hcard, fun i hi => ?_⟩
    obtain rfl : i = 0 := Nat.le_zero.mp hi
    simp [Multiset.esymm]
  obtain ⟨f, hf⟩ := usefulFamily_list_lower_bound domain hn hHcard hfib hU hkhat
    (by simpa using hk1) hk2
  refine le_iSup_of_le f ?_
  have hcard𝒮 : (H.powersetCard khat).card = h.choose khat := by
    rw [Finset.card_powersetCard, hHcard]
  rw [← hcard𝒮]
  rw [← (Set.toFinite _).cast_ncard_eq]
  exact_mod_cast hf

omit [Fintype F] in
/-- Any finite set closed under negation and without `-`-fixed points splits into
antipodal pairs: there is a transversal `P` picking exactly one of `{y, -y}` for each
pair, so `2·|P| = |H|`. -/
lemma exists_neg_transversal {H : Finset F} (hneg : ∀ y ∈ H, -y ∈ H)
    (hnf : ∀ y ∈ H, -y ≠ y) :
    ∃ P : Finset F, P ⊆ H ∧ 2 * P.card = H.card ∧ ∀ y ∈ H, (y ∈ P ↔ -y ∉ P) := by
  classical
  obtain ⟨n, hn⟩ : ∃ n, H.card = n := ⟨_, rfl⟩
  induction n using Nat.strong_induction_on generalizing H with
  | _ n IH =>
    rcases H.eq_empty_or_nonempty with rfl | ⟨a, ha⟩
    · exact ⟨∅, by simp, by simp, by simp⟩
    · have hna : -a ∈ H := hneg a ha
      have hane : -a ≠ a := hnf a ha
      set H' : Finset F := H \ {a, -a} with hH'
      -- `H'` is closed under negation and free of `-`-fixed points.
      have hneg' : ∀ y ∈ H', -y ∈ H' := by
        intro y hy
        rw [hH', Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton] at hy ⊢
        obtain ⟨hyH, hy2⟩ := hy
        refine ⟨hneg y hyH, ?_⟩
        rintro (h | h)
        · exact hy2 (Or.inr (neg_eq_iff_eq_neg.mp h))
        · exact hy2 (Or.inl (neg_inj.mp h))
      have hnf' : ∀ y ∈ H', -y ≠ y := fun y hy =>
        hnf y (Finset.mem_sdiff.mp hy).1
      -- The pair `{a, -a}` has two elements, so `|H'| = |H| - 2`.
      have hpair : ({a, -a} : Finset F).card = 2 := by
        rw [Finset.card_insert_of_notMem
            (by simp only [Finset.mem_singleton]; exact fun h => hane h.symm),
          Finset.card_singleton]
      have hpairsub : ({a, -a} : Finset F) ⊆ H := by
        intro x hx
        rw [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl
        · exact ha
        · exact hna
      have hcard' : H'.card = n - 2 := by
        rw [hH', Finset.card_sdiff_of_subset hpairsub, hpair, hn]
      have hlt : n - 2 < n := by
        have : 2 ≤ n := by
          rw [← hn]; exact hpair ▸ Finset.card_le_card hpairsub
        omega
      obtain ⟨P', hP'sub, hP'card, hP'iff⟩ := IH (n - 2) hlt hneg' hnf' hcard'
      refine ⟨insert a P', ?_, ?_, ?_⟩
      · intro x hx
        rw [Finset.mem_insert] at hx
        rcases hx with rfl | hx
        · exact ha
        · exact (Finset.mem_sdiff.mp (hP'sub hx)).1
      · -- `a ∉ P'` since `P' ⊆ H'` and `a ∉ H'`.
        have haP' : a ∉ P' := fun h => by
          have := (Finset.mem_sdiff.mp (hP'sub h)).2
          exact this (by simp)
        have h2 : 2 ≤ n := by
          rw [← hn]; exact hpair ▸ Finset.card_le_card hpairsub
        rw [Finset.card_insert_of_notMem haP', hn]
        omega
      · -- `a ∉ P'` and `-a ∉ P'` since `P' ⊆ H'` and neither is in `H'`.
        have haP' : a ∉ P' := fun h => by
          have := (Finset.mem_sdiff.mp (hP'sub h)).2; exact this (by simp)
        have hnaP' : -a ∉ P' := fun h => by
          have := (Finset.mem_sdiff.mp (hP'sub h)).2; exact this (by simp)
        intro y hyH
        by_cases hya : y = a
        · subst hya
          -- `y = a ∈ insert a P'`; need `-a ∉ insert a P'`.
          simp only [Finset.mem_insert, true_or, true_iff, not_or]
          exact ⟨hane, hnaP'⟩
        · by_cases hyna : y = -a
          · subst hyna
            -- `y = -a`; `-y = a ∈ insert a P'`, and `-a ∉ insert a P'`.
            have hnyeq : -(-a) = a := neg_neg a
            simp only [Finset.mem_insert, hnyeq, true_or, not_true_eq_false, iff_false, not_or]
            exact ⟨hane, hnaP'⟩
          · -- `y ∈ H'`, use `hP'iff`.
            have hyH' : y ∈ H' := by
              rw [hH', Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
              exact ⟨hyH, fun h => h.elim hya hyna⟩
            have hnyne_a : ¬ (-y = a) := by
              intro h; exact hyna (by rw [← neg_neg y, h])
            rw [Finset.mem_insert, Finset.mem_insert]
            simp only [hya, hnyne_a, false_or]
            exact hP'iff y hyH'

omit [Fintype F] [DecidableEq F] in
/-- The degree-`0` elementary symmetric function is `1`. -/
private lemma esymm_zero_eq_one (S : Finset F) : S.1.esymm 0 = 1 := by
  simp [Multiset.esymm]

omit [DecidableEq ι] in
/-- If additionally `H = -H` with no
`-`-fixed points (supplied for smooth domains by `Smooth.exists_pow_projection_structure`
when `h` is even) and `k̂` is even, `(k̂-2)·d < k ≤ k̂·d`, then
`|List(C, δ_min(C) - (k̂d - k + 1)/n)| ≥ C(h/2, k̂/2)`.

This instantiates the useful-family template with the `(H, k̂, 1)`-useful family of unions of
`k̂/2` antipodal pairs (common sum `0`). -/
theorem choose_le_Lambda_rs_antipodal_even (domain : ι ↪ F) {d h khat k : ℕ}
    (hn : Fintype.card ι = d * h)
    {H : Finset F} (hHcard : H.card = h)
    (hfib : ∀ y ∈ H, (Finset.univ.filter fun i => domain i ^ d = y).card = d)
    (hneg : ∀ y ∈ H, -y ∈ H) (hnf : ∀ y ∈ H, -y ≠ y)
    (hkhat : 1 ≤ khat) (hkh : khat < h) (hkeven : Even khat)
    (hk1 : (khat - 2) * d < k) (hk2 : k ≤ khat * d) :
    ((h / 2).choose (khat / 2) : ℕ∞) ≤
      Lambda (↑(ReedSolomon.code domain k) : Set (ι → F))
        (((δᵣ (↑(ReedSolomon.code domain k) : Set (ι → F)) : ℚ≥0) : ℝ)
          - ((khat * d - k + 1 : ℕ) : ℝ) / (Fintype.card ι : ℝ)) := by
  classical
  have hk0 : 0 < k := by
    have := hk1; nlinarith [Nat.zero_le ((khat - 2) * d)]
  rw [minRelDist_sub_eq domain hn hk0 hkh.le hk2]
  -- `k̂ = t + t` from evenness; `1 < k̂`.
  obtain ⟨t, ht⟩ := hkeven
  have h1lt : 1 < khat := by omega
  -- Antipodal transversal `P` with `|P| = h/2`.
  obtain ⟨P, hPsub, hPcard, hPiff⟩ := exists_neg_transversal hneg hnf
  have hPcard2 : P.card = h / 2 := by rw [← hHcard]; omega
  -- The family: unions of `t` antipodal pairs.
  set Ψ : Finset F → Finset F := fun T => T ∪ T.image (fun y => -y) with hΨ
  set 𝒮 : Finset (Finset F) := (P.powersetCard t).image Ψ with h𝒮def
  -- For `T` a `t`-subset of `P`: `T` and `-T` are disjoint.
  have hdisj : ∀ T, T ⊆ P → Disjoint T (T.image (fun y => -y)) := by
    intro T hTP
    rw [Finset.disjoint_left]
    intro y hyT hyneg
    rw [Finset.mem_image] at hyneg
    obtain ⟨z, hzT, hzy⟩ := hyneg
    -- `y ∈ P` and `y = -z` with `z ∈ P`, i.e. `-y = z ∈ P`, contradicting the transversal.
    have hyP : y ∈ P := hTP hyT
    have hzP : z ∈ P := hTP hzT
    have hyH : y ∈ H := hPsub hyP
    have hnyP : -y ∈ P := by rw [← hzy, neg_neg]; exact hzP
    exact (hPiff y hyH).mp hyP hnyP
  -- Membership facts about `T ∈ P.powersetCard t`.
  have hmemT : ∀ T ∈ P.powersetCard t, T ⊆ P ∧ T.card = t :=
    fun T hT => Finset.mem_powersetCard.mp hT
  -- `Ψ T` has card `k̂`, sits in `H`, and sums to `0`.
  have hΨcard : ∀ T ∈ P.powersetCard t, (Ψ T).card = khat := by
    intro T hT
    obtain ⟨hTP, hTc⟩ := hmemT T hT
    rw [hΨ, Finset.card_union_of_disjoint (hdisj T hTP),
      Finset.card_image_of_injective _ neg_injective, hTc, ht]
  have hΨsub : ∀ T ∈ P.powersetCard t, Ψ T ⊆ H := by
    intro T hT
    obtain ⟨hTP, -⟩ := hmemT T hT
    rw [hΨ]
    intro y hy
    rw [Finset.mem_union] at hy
    rcases hy with hy | hy
    · exact hPsub (hTP hy)
    · rw [Finset.mem_image] at hy
      obtain ⟨z, hzT, rfl⟩ := hy
      exact hneg _ (hPsub (hTP hzT))
  have hΨsum : ∀ T ∈ P.powersetCard t, ∑ y ∈ Ψ T, y = 0 := by
    intro T hT
    obtain ⟨hTP, -⟩ := hmemT T hT
    rw [hΨ, Finset.sum_union (hdisj T hTP),
      Finset.sum_image (fun x _ y _ h => neg_injective h), Finset.sum_neg_distrib]
    ring
  -- Injectivity of `Ψ` on `↑(P.powersetCard t)`: recover `T = Ψ T ∩ P`.
  have hΨinj : Set.InjOn Ψ ↑(P.powersetCard t) := by
    intro T hT T' hT' heq
    rw [Finset.mem_coe] at hT hT'
    obtain ⟨hTP, -⟩ := hmemT T hT
    obtain ⟨hT'P, -⟩ := hmemT T' hT'
    -- `T = Ψ T ∩ P`: elements of `T.image neg` are not in `P`.
    have key : ∀ (U : Finset F), U ⊆ P → Ψ U ∩ P = U := by
      intro U hUP
      ext y
      rw [Finset.mem_inter, hΨ, Finset.mem_union]
      constructor
      · rintro ⟨hy | hy, hyP⟩
        · exact hy
        · rw [Finset.mem_image] at hy
          obtain ⟨z, hzU, rfl⟩ := hy
          have hzP : z ∈ P := hUP hzU
          have hnzP : -z ∈ P := hyP
          exact absurd hnzP ((hPiff z (hPsub hzP)).mp hzP)
      · intro hy
        exact ⟨Or.inl hy, hUP hy⟩
    have := (key T hTP).symm.trans ((congrArg (· ∩ P) heq).trans (key T' hT'P))
    exact this
  -- `(H, k̂, 1)`-useful family with `λ 0 = 1`, `λ 1 = 0`.
  have hU : IsUsefulFamily H khat 1 𝒮 := by
    refine ⟨fun i => if i = 0 then 1 else 0, fun S hS => ?_⟩
    rw [h𝒮def, Finset.mem_image] at hS
    obtain ⟨T, hT, rfl⟩ := hS
    refine ⟨hΨsub T hT, hΨcard T hT, fun i hi => ?_⟩
    interval_cases i
    · simp [esymm_zero_eq_one]
    · simp only [Nat.one_ne_zero, if_false]
      rw [esymm_one_eq_sum, hΨsum T hT]
  -- Apply the general template.
  obtain ⟨f, hf⟩ := usefulFamily_list_lower_bound domain hn hHcard hfib hU h1lt
    (show (khat - 1 - 1) * d < k by rw [Nat.sub_sub]; exact hk1) hk2
  refine le_iSup_of_le f ?_
  -- Count: `|𝒮| = C(h/2, k̂/2)`.
  have hcard𝒮 : 𝒮.card = (h / 2).choose (khat / 2) := by
    rw [h𝒮def, Finset.card_image_of_injOn hΨinj, Finset.card_powersetCard, hPcard2]
    congr 1
    omega
  rw [← hcard𝒮]
  rw [← (Set.toFinite _).cast_ncard_eq]
  exact_mod_cast hf

omit [DecidableEq ι] in
/-- The odd-cardinality version of `choose_le_Lambda_rs_antipodal_even`:
`|List(C, δ_min(C) - (k̂d - k + 1)/n)| ≥ C(h/2 - 1, (k̂-1)/2)`.

This instantiates the useful-family template with the `(H, k̂, 1)`-useful family
`{α₀} ∪ (k̂-1)/2` antipodal pairs avoiding `±α₀` (common sum `α₀`). -/
theorem choose_le_Lambda_rs_antipodal_odd (domain : ι ↪ F) {d h khat k : ℕ}
    (hn : Fintype.card ι = d * h)
    {H : Finset F} (hHcard : H.card = h)
    (hfib : ∀ y ∈ H, (Finset.univ.filter fun i => domain i ^ d = y).card = d)
    (hneg : ∀ y ∈ H, -y ∈ H) (hnf : ∀ y ∈ H, -y ≠ y)
    (hkhat : 1 ≤ khat) (hkh : khat < h) (hkodd : Odd khat)
    (hk1 : (khat - 2) * d < k) (hk2 : k ≤ khat * d) :
    ((h / 2 - 1).choose ((khat - 1) / 2) : ℕ∞) ≤
      Lambda (↑(ReedSolomon.code domain k) : Set (ι → F))
        (((δᵣ (↑(ReedSolomon.code domain k) : Set (ι → F)) : ℚ≥0) : ℝ)
          - ((khat * d - k + 1 : ℕ) : ℝ) / (Fintype.card ι : ℝ)) := by
  classical
  have hk0 : 0 < k := by
    have := hk1; nlinarith [Nat.zero_le ((khat - 2) * d)]
  rw [minRelDist_sub_eq domain hn hk0 hkh.le hk2]
  -- `H` is nonempty; pick `a₀ ∈ H`.
  have hHpos : 0 < H.card := by rw [hHcard]; omega
  obtain ⟨a₀, ha₀⟩ := Finset.card_pos.mp hHpos
  rcases eq_or_lt_of_le hkhat with hk1eq | h1lt
  · -- Special case `k̂ = 1` (so `t = 0`): the singleton family `{{a₀}}`.
    subst hk1eq
    set 𝒮 : Finset (Finset F) := {({a₀} : Finset F)} with h𝒮def
    have hU : IsUsefulFamily H 1 0 𝒮 := by
      refine ⟨fun _ => 1, fun S hS => ?_⟩
      rw [h𝒮def, Finset.mem_singleton] at hS
      subst hS
      refine ⟨by simpa using ha₀, by simp, fun i hi => ?_⟩
      obtain rfl : i = 0 := Nat.le_zero.mp hi
      exact esymm_zero_eq_one _
    obtain ⟨f, hf⟩ := usefulFamily_list_lower_bound domain hn hHcard hfib hU
      (by norm_num) (by simpa using hk0) hk2
    refine le_iSup_of_le f ?_
    have hcard𝒮 : 𝒮.card = (h / 2 - 1).choose ((1 - 1) / 2) := by
      rw [h𝒮def, Finset.card_singleton]; simp
    rw [← hcard𝒮]
    rw [← (Set.toFinite _).cast_ncard_eq]
    exact_mod_cast hf
  · -- General odd case `k̂ ≥ 3`: `k̂ = 2t + 1` with `t ≥ 1`.
    obtain ⟨t, ht⟩ := hkodd
    have ht1 : 1 ≤ t := by omega
    -- Antipodal transversal `P`, `|P| = h/2`.
    obtain ⟨P, hPsub, hPcard, hPiff⟩ := exists_neg_transversal hneg hnf
    have hPcard2 : P.card = h / 2 := by rw [← hHcard]; omega
    -- `b₀ ∈ P` representing the pair `{a₀, -a₀}`.
    have hna₀ : -a₀ ∈ H := hneg a₀ ha₀
    set b₀ : F := if a₀ ∈ P then a₀ else -a₀ with hb₀
    have hb₀P : b₀ ∈ P := by
      rw [hb₀]
      by_cases h : a₀ ∈ P
      · rwa [if_pos h]
      · rw [if_neg h]
        have := (hPiff (-a₀) hna₀).mpr (by rwa [neg_neg])
        exact this
    -- `a₀ ∉ P.erase b₀`.
    set P' : Finset F := P.erase b₀ with hP'def
    have hPcard' : P'.card = h / 2 - 1 := by
      rw [hP'def, Finset.card_erase_of_mem hb₀P, hPcard2]
    have ha₀nP' : a₀ ∉ P' := by
      rw [hP'def, Finset.mem_erase]
      rintro ⟨hne, ha₀P⟩
      -- If `a₀ ∈ P`, then `b₀ = a₀`, contradicting `a₀ ≠ b₀`.
      rw [hb₀, if_pos ha₀P] at hne
      exact hne rfl
    -- The family: `insert a₀ (T ∪ -T)` for `t`-subsets `T` of `P'`.
    set Ψ : Finset F → Finset F := fun T => insert a₀ (T ∪ T.image (fun y => -y)) with hΨ
    set 𝒮 : Finset (Finset F) := (P'.powersetCard t).image Ψ with h𝒮def
    have hmemT : ∀ T ∈ P'.powersetCard t, T ⊆ P' ∧ T.card = t :=
      fun T hT => Finset.mem_powersetCard.mp hT
    have hP'subP : P' ⊆ P := Finset.erase_subset _ _
    -- `T` and `-T` are disjoint (as in the even case).
    have hdisj : ∀ T, T ⊆ P' → Disjoint T (T.image (fun y => -y)) := by
      intro T hTP'
      rw [Finset.disjoint_left]
      intro y hyT hyneg
      rw [Finset.mem_image] at hyneg
      obtain ⟨z, hzT, hzy⟩ := hyneg
      have hyP : y ∈ P := hP'subP (hTP' hyT)
      have hzP : z ∈ P := hP'subP (hTP' hzT)
      have hyH : y ∈ H := hPsub hyP
      have hnyP : -y ∈ P := by rw [← hzy, neg_neg]; exact hzP
      exact (hPiff y hyH).mp hyP hnyP
    -- `a₀ ∉ T ∪ -T` for `T ⊆ P'`.
    have ha₀nunion : ∀ T, T ⊆ P' → a₀ ∉ T ∪ T.image (fun y => -y) := by
      intro T hTP' hmem
      rw [Finset.mem_union] at hmem
      rcases hmem with hmem | hmem
      · -- `a₀ ∈ T ⊆ P'` contradicts `a₀ ∉ P'`.
        exact ha₀nP' (hTP' hmem)
      · -- `a₀ = -z`, `z ∈ T ⊆ P'`, so `z = -a₀ ∈ P` forces `a₀ ∉ P`, i.e.
        -- `b₀ = -a₀ = z`,
        -- but `z ∈ P.erase b₀` — contradiction.
        rw [Finset.mem_image] at hmem
        obtain ⟨z, hzT, hza₀⟩ := hmem
        have hzeq : z = -a₀ := by rw [← hza₀, neg_neg]
        have hzP' : z ∈ P' := hTP' hzT
        have hzP : z ∈ P := hP'subP hzP'
        -- `-a₀ ∈ P` (that is `z`), so by the transversal `a₀ ∉ P`, hence
        -- `b₀ = -a₀ = z`.
        have hnzP : z ∈ P := hzP
        have ha₀nP : a₀ ∉ P := by
          intro ha₀P
          have : -a₀ ∉ P := (hPiff a₀ ha₀).mp ha₀P
          rw [← hzeq] at this
          exact this hzP
        have hb₀eq : b₀ = z := by rw [hb₀, if_neg ha₀nP, hzeq]
        rw [hP'def, Finset.mem_erase] at hzP'
        exact hzP'.1 hb₀eq.symm
    -- `Ψ T` has card `k̂`, sits in `H`, sums to `a₀`.
    have hΨcard : ∀ T ∈ P'.powersetCard t, (Ψ T).card = khat := by
      intro T hT
      obtain ⟨hTP', hTc⟩ := hmemT T hT
      rw [hΨ, Finset.card_insert_of_notMem (ha₀nunion T hTP'),
        Finset.card_union_of_disjoint (hdisj T hTP'),
        Finset.card_image_of_injective _ neg_injective, hTc, ht]
      omega
    have hΨsub : ∀ T ∈ P'.powersetCard t, Ψ T ⊆ H := by
      intro T hT
      obtain ⟨hTP', -⟩ := hmemT T hT
      rw [hΨ]
      intro y hy
      rw [Finset.mem_insert, Finset.mem_union] at hy
      rcases hy with rfl | hy | hy
      · exact ha₀
      · exact hPsub (hP'subP (hTP' hy))
      · rw [Finset.mem_image] at hy
        obtain ⟨z, hzT, rfl⟩ := hy
        exact hneg _ (hPsub (hP'subP (hTP' hzT)))
    have hΨsum : ∀ T ∈ P'.powersetCard t, ∑ y ∈ Ψ T, y = a₀ := by
      intro T hT
      obtain ⟨hTP', -⟩ := hmemT T hT
      rw [hΨ, Finset.sum_insert (ha₀nunion T hTP'), Finset.sum_union (hdisj T hTP'),
        Finset.sum_image (fun x _ y _ h => neg_injective h), Finset.sum_neg_distrib]
      ring
    -- Injectivity of `Ψ`: recover `T = Ψ T ∩ P'` (`a₀ ∉ P'`, `-z ∉ P'`).
    have hΨinj : Set.InjOn Ψ ↑(P'.powersetCard t) := by
      intro T hT T' hT' heq
      rw [Finset.mem_coe] at hT hT'
      obtain ⟨hTP', -⟩ := hmemT T hT
      obtain ⟨hT'P', -⟩ := hmemT T' hT'
      have key : ∀ (U : Finset F), U ⊆ P' → Ψ U ∩ P' = U := by
        intro U hUP'
        ext y
        rw [Finset.mem_inter, hΨ, Finset.mem_insert, Finset.mem_union]
        constructor
        · rintro ⟨hy | hy | hy, hyP'⟩
          · exact absurd (hy ▸ hyP') ha₀nP'
          · exact hy
          · -- `y = -z`, `z ∈ U ⊆ P'`; `-z ∈ P'` contradicts the transversal.
            rw [Finset.mem_image] at hy
            obtain ⟨z, hzU, rfl⟩ := hy
            have hzP : z ∈ P := hP'subP (hUP' hzU)
            have hnzP : -z ∈ P := hP'subP hyP'
            exact absurd hnzP ((hPiff z (hPsub hzP)).mp hzP)
        · intro hy
          exact ⟨Or.inr (Or.inl hy), hUP' hy⟩
      have := (key T hTP').symm.trans ((congrArg (· ∩ P') heq).trans (key T' hT'P'))
      exact this
    -- `(H, k̂, 1)`-useful with `λ 0 = 1`, `λ 1 = a₀`.
    have hU : IsUsefulFamily H khat 1 𝒮 := by
      refine ⟨fun i => if i = 0 then 1 else a₀, fun S hS => ?_⟩
      rw [h𝒮def, Finset.mem_image] at hS
      obtain ⟨T, hT, rfl⟩ := hS
      refine ⟨hΨsub T hT, hΨcard T hT, fun i hi => ?_⟩
      interval_cases i
      · simp [esymm_zero_eq_one]
      · simp only [Nat.one_ne_zero, if_false]
        rw [esymm_one_eq_sum, hΨsum T hT]
    obtain ⟨f, hf⟩ := usefulFamily_list_lower_bound domain hn hHcard hfib hU h1lt
      (show (khat - 1 - 1) * d < k by rw [Nat.sub_sub]; exact hk1) hk2
    refine le_iSup_of_le f ?_
    have hcard𝒮 : 𝒮.card = (h / 2 - 1).choose ((khat - 1) / 2) := by
      rw [h𝒮def, Finset.card_image_of_injOn hΨinj, Finset.card_powersetCard, hPcard']
      congr 1
      omega
    rw [← hcard𝒮]
    rw [← (Set.toFinite _).cast_ncard_eq]
    exact_mod_cast hf

end Corollaries

/-! ## Bridge from `ReedSolomon.Smooth` domains -/

section SmoothBridge

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

omit [DecidableEq ι] [Fintype F] in
/-- Group-theoretic core of the smooth-domain projection: on a smooth coset `a·H₀`, every
element `u` of the subgroup `H₀` satisfies `u^n = 1` (as an element of `F`), where
`n = |ι|`.  This is Lagrange (`pow_card_eq_one'`) once `Nat.card ↥H₀ = n`, which follows
from the coset equation `image domain = a · H₀`. -/
private lemma smooth_pow_card_eq_one (domain : ι ↪ F) (H0 : Subgroup (Units F)) (a : Units F)
    (h_coset : (↑(Finset.image domain Finset.univ) : Set F)
        = (fun h : Units F => (a : F) * (h : F)) '' (H0 : Set (Units F)))
    (u : Units F) (hu : u ∈ H0) : (u : F) ^ (Fintype.card ι) = 1 := by
  classical
  set n := Fintype.card ι with hn_def
  have hginj : Function.Injective (fun u : Units F => (a : F) * (u : F)) := by
    intro x y hxy
    simp only at hxy
    exact Units.ext (mul_left_cancel₀ (Units.ne_zero a) hxy)
  have hcard_set : (H0 : Set (Units F)).ncard = n := by
    have h1 : ((fun u : Units F => (a : F) * (u : F)) '' (H0 : Set (Units F))).ncard
        = (H0 : Set (Units F)).ncard := Set.ncard_image_of_injective _ hginj
    rw [← h_coset, Set.ncard_coe_finset,
      Finset.card_image_of_injective _ domain.injective, Finset.card_univ] at h1
    exact h1.symm
  have hfin : (H0 : Set (Units F)).Finite :=
    Set.finite_of_ncard_ne_zero (by rw [hcard_set]; exact (Fintype.card_pos (α := ι)).ne')
  have hfin' : Finite ↥H0 := hfin.to_subtype
  have hnatcard : Nat.card ↥H0 = n := by
    have h := Nat.card_coe_set_eq (H0 : Set (Units F))
    rw [hcard_set] at h; exact h
  have hpow : (⟨u, hu⟩ : ↥H0) ^ n = 1 := by rw [← hnatcard]; exact pow_card_eq_one'
  have h3 : (u : Units F) ^ n = 1 := by
    have h2 : ((⟨u, hu⟩ : ↥H0) : Units F) ^ n = 1 := by
      rw [← Subgroup.coe_pow, hpow, Subgroup.coe_one]
    exact h2
  calc (u : F) ^ n = ((u ^ n : Units F) : F) := by rw [Units.val_pow_eq_pow_val]
    _ = ((1 : Units F) : F) := by rw [h3]
    _ = 1 := Units.val_one

omit [DecidableEq ι] [Fintype F] in
/-- **Smooth-domain projection structure.** A smooth evaluation domain (a coset `a·H₀` of
a 2-group `H₀ ≤ Fˣ`) of size `n = d·h` projects under `x ↦ x^d` onto a set `H` of exactly
`h` values, `d`-to-`1`; when `h` is even, `H` is moreover closed under negation with no
`-`-fixed points. The smooth-domain corollaries below consume this package.

Proof route (elementary, field-theoretic): every fiber of `x ↦ x^d` has at most `d`
elements (roots of `X^d - y`); every projected value lies among the `≤ h` roots of
`X^h - a^n` (since `u^{|H₀|} = 1` on `H₀`); fibers partition the `n = d·h` domain points,
forcing exactly `h` values with fibers of size exactly `d`. For even `h`, `H` is then the
full root set of `X^h - a^n`, which is negation-closed; a `-`-fixed point would force
characteristic 2, where `X^h - a^n` (h even) cannot have `h` distinct roots. -/
theorem Smooth.exists_pow_projection_structure (domain : ι ↪ F)
    [ReedSolomon.Smooth domain] {d h : ℕ} (hn : Fintype.card ι = d * h) :
    ∃ H : Finset F, H.card = h ∧ (∀ i, domain i ^ d ∈ H) ∧
      (∀ y ∈ H, (Finset.univ.filter fun i => domain i ^ d = y).card = d) ∧
      (Even h → (∀ y ∈ H, -y ∈ H) ∧ ∀ y ∈ H, -y ≠ y) := by
  classical
  set n := Fintype.card ι with hn_def
  have hnpos : 0 < n := Fintype.card_pos
  have hd0 : 0 < d := by
    rcases Nat.eq_zero_or_pos d with hd | hd
    · rw [hd, Nat.zero_mul] at hn; omega
    · exact hd
  have hh0 : 0 < h := by
    rcases Nat.eq_zero_or_pos h with hh | hh
    · rw [hh, Nat.mul_zero] at hn; omega
    · exact hh
  set H0 := ReedSolomon.Smooth.H domain with hH0
  set a := ReedSolomon.Smooth.a domain with ha
  have h_coset : (↑(Finset.image domain Finset.univ) : Set F)
      = (fun h : Units F => (a : F) * (h : F)) '' (H0 : Set (Units F)) :=
    ReedSolomon.Smooth.h_coset
  -- The projected value set `HF = {domain i ^ d}`.
  set HF : Finset F := Finset.image (fun i => domain i ^ d) Finset.univ with hHF
  have hmemHF : ∀ i, domain i ^ d ∈ HF := fun i =>
    Finset.mem_image_of_mem _ (Finset.mem_univ i)
  -- Coset structure: every domain point is `a * u` with `u ∈ H₀`.
  have hpt : ∀ i, ∃ u : Units F, u ∈ H0 ∧ (domain i : F) = (a : F) * (u : F) := by
    intro i
    have hmem : (domain i : F) ∈ (↑(Finset.image domain Finset.univ) : Set F) := by
      simp
    rw [h_coset] at hmem
    obtain ⟨u, hu, hval⟩ := hmem
    exact ⟨u, hu, hval.symm⟩
  -- Every projected value is an `h`-th root of `a^n`.
  have han : ((a : F) ^ n) ≠ 0 := pow_ne_zero _ (Units.ne_zero a)
  have hroot : ∀ y ∈ HF, y ^ h = (a : F) ^ n := by
    intro y hy
    rw [hHF, Finset.mem_image] at hy
    obtain ⟨i, -, rfl⟩ := hy
    obtain ⟨u, hu, hval⟩ := hpt i
    have hun : (u : F) ^ n = 1 := smooth_pow_card_eq_one domain H0 a h_coset u hu
    calc (domain i ^ d) ^ h = domain i ^ (d * h) := by rw [← pow_mul]
      _ = domain i ^ n := by rw [← hn]
      _ = ((a : F) * (u : F)) ^ n := by rw [hval]
      _ = (a : F) ^ n * (u : F) ^ n := by rw [mul_pow]
      _ = (a : F) ^ n := by rw [hun, mul_one]
  have hsubroots : HF ⊆ Polynomial.nthRootsFinset h ((a : F) ^ n) := by
    intro y hy
    rw [Polynomial.mem_nthRootsFinset hh0]
    exact hroot y hy
  have hHFle : HF.card ≤ h := by
    refine le_trans (Finset.card_le_card hsubroots) ?_
    rw [Polynomial.nthRootsFinset_def]
    exact le_trans (Multiset.toFinset_card_le _) (Polynomial.card_nthRoots h ((a : F) ^ n))
  -- Each fiber of `x ↦ x^d` has at most `d` domain points (roots of `X^d - y`).
  have hfible : ∀ y : F, (Finset.univ.filter fun i => domain i ^ d = y).card ≤ d := by
    intro y
    set Q : F[X] := X ^ d - C y with hQ
    have hQne : Q ≠ 0 := Polynomial.X_pow_sub_C_ne_zero hd0 y
    have hQdeg : Q.natDegree = d := Polynomial.natDegree_X_pow_sub_C
    have heq : (Finset.univ.filter fun i => domain i ^ d = y)
        = (Finset.univ.filter fun i => Q.eval (domain i) = 0) := by
      apply Finset.filter_congr
      intro i _
      simp only [hQ, eval_sub, eval_pow, eval_X, eval_C, sub_eq_zero]
    rw [heq]
    have hcard := card_filter_eval_eq_zero_le_natDegree domain hQne
    rw [hQdeg] at hcard
    exact hcard
  -- Double counting: the `n = d·h` domain points partition into `HF`-fibers.
  have hmaps : Set.MapsTo (fun i => domain i ^ d) (↑(Finset.univ : Finset ι) : Set ι) HF :=
    fun i _ => hmemHF i
  have hsum : n = ∑ y ∈ HF, (Finset.univ.filter fun i => domain i ^ d = y).card := by
    rw [hn_def]
    have hcf := Finset.card_eq_sum_card_fiberwise (f := fun i => domain i ^ d)
      (s := (Finset.univ : Finset ι)) (t := HF) hmaps
    rw [Finset.card_univ] at hcf
    convert hcf using 2
  have hle : n ≤ HF.card * d := by
    rw [hsum]
    calc ∑ y ∈ HF, (Finset.univ.filter fun i => domain i ^ d = y).card
        ≤ HF.card • d := Finset.sum_le_card_nsmul HF _ d (fun y _ => hfible y)
      _ = HF.card * d := by rw [smul_eq_mul]
  have hHFcard : HF.card = h := by
    have h1 : h * d ≤ HF.card * d := by rw [mul_comm h d, ← hn]; exact hle
    have h2 : h ≤ HF.card := Nat.le_of_mul_le_mul_right h1 hd0
    exact le_antisymm hHFle h2
  -- Since fibers sum to `n = HF.card · d` and each is `≤ d`, each equals `d`.
  have hfibeq : ∀ y ∈ HF, (Finset.univ.filter fun i => domain i ^ d = y).card = d := by
    intro y0 hy0
    by_contra hne
    have hlt : (Finset.univ.filter fun i => domain i ^ d = y0).card < d :=
      lt_of_le_of_ne (hfible y0) hne
    have hstrict : ∑ y ∈ HF, (Finset.univ.filter fun i => domain i ^ d = y).card
        < ∑ _y ∈ HF, d := by
      apply Finset.sum_lt_sum
      · intro y _; exact hfible y
      · exact ⟨y0, hy0, hlt⟩
    rw [Finset.sum_const, smul_eq_mul, hHFcard, ← hsum, hn, mul_comm] at hstrict
    exact lt_irrefl _ hstrict
  refine ⟨HF, hHFcard, hmemHF, hfibeq, ?_⟩
  -- Even `h`: `HF` is the full root set of `X^h - a^n`, hence negation-closed and
  -- without `-`-fixed points (the latter would force characteristic 2).
  intro hheven
  have hcardroots : (Polynomial.nthRootsFinset h ((a : F) ^ n)).card ≤ h := by
    rw [Polynomial.nthRootsFinset_def]
    exact le_trans (Multiset.toFinset_card_le _) (Polynomial.card_nthRoots h ((a : F) ^ n))
  have hHFeq : HF = Polynomial.nthRootsFinset h ((a : F) ^ n) :=
    Finset.eq_of_subset_of_card_le hsubroots (by rw [hHFcard]; exact hcardroots)
  refine ⟨?_, ?_⟩
  · intro y hy
    rw [hHFeq, Polynomial.mem_nthRootsFinset hh0] at hy ⊢
    rw [hheven.neg_pow, hy]
  · intro y hy hfix
    have hyne : y ≠ 0 := by
      intro hy0
      have hr := hroot y hy
      rw [hy0, zero_pow hh0.ne'] at hr
      exact han hr.symm
    have h2y : (2 : F) * y = 0 := by linear_combination -hfix
    have hchar2 : (2 : F) = 0 := by
      rcases mul_eq_zero.mp h2y with hc | hc
      · exact hc
      · exact absurd hc hyne
    obtain ⟨m, hm⟩ := hheven
    have hmpos : 0 < m := by omega
    have hsqinj : ∀ x z : F, x ^ 2 = z ^ 2 → x = z := by
      intro x z hxz
      have hsq0 : (x - z) ^ 2 = 0 := by linear_combination hxz + (z ^ 2 - x * z) * hchar2
      have hz := (pow_eq_zero_iff (n := 2) (by norm_num)).mp hsq0
      exact sub_eq_zero.mp hz
    have hmm : h = m * 2 := by omega
    have hallm : ∀ y1 ∈ HF, ∀ y2 ∈ HF, y1 ^ m = y2 ^ m := by
      intro y1 hy1 y2 hy2
      apply hsqinj
      rw [← pow_mul, ← pow_mul, ← hmm, hroot y1 hy1, hroot y2 hy2]
    obtain ⟨y0, hy0⟩ := Finset.card_pos.mp (by rw [hHFcard]; exact hh0)
    set s := y0 ^ m with hs
    have hsub2 : HF ⊆ Polynomial.nthRootsFinset m s := by
      intro y1 hy1
      rw [Polynomial.mem_nthRootsFinset hmpos, hs]
      exact hallm y1 hy1 y0 hy0
    have hcards : (Polynomial.nthRootsFinset m s).card ≤ m := by
      rw [Polynomial.nthRootsFinset_def]
      exact le_trans (Multiset.toFinset_card_le _) (Polynomial.card_nthRoots m s)
    have hhm : h ≤ m := by
      rw [← hHFcard]; exact le_trans (Finset.card_le_card hsub2) hcards
    omega

omit [DecidableEq ι] in
/-- `choose_le_Lambda_rs_vanilla` specialized to a smooth evaluation domain. -/
theorem choose_le_Lambda_rs_vanilla_of_smooth (domain : ι ↪ F)
    [ReedSolomon.Smooth domain] {d h khat k : ℕ}
    (hn : Fintype.card ι = d * h) (hkhat : 1 ≤ khat) (hkh : khat < h)
    (hk1 : (khat - 1) * d < k) (hk2 : k ≤ khat * d) :
    (h.choose khat : ℕ∞) ≤
      Lambda (↑(ReedSolomon.code domain k) : Set (ι → F))
        (((δᵣ (↑(ReedSolomon.code domain k) : Set (ι → F)) : ℚ≥0) : ℝ)
          - ((khat * d - k + 1 : ℕ) : ℝ) / (Fintype.card ι : ℝ)) := by
  obtain ⟨H, hHcard, -, hfib, -⟩ := Smooth.exists_pow_projection_structure domain hn
  exact choose_le_Lambda_rs_vanilla domain hn hHcard hfib hkhat hkh hk1 hk2

omit [DecidableEq ι] in
/-- `choose_le_Lambda_rs_antipodal_even` specialized to a smooth domain with even `h`. -/
theorem choose_le_Lambda_rs_antipodal_even_of_smooth (domain : ι ↪ F)
    [ReedSolomon.Smooth domain] {d h khat k : ℕ}
    (hn : Fintype.card ι = d * h) (hheven : Even h)
    (hkhat : 1 ≤ khat) (hkh : khat < h) (hkeven : Even khat)
    (hk1 : (khat - 2) * d < k) (hk2 : k ≤ khat * d) :
    ((h / 2).choose (khat / 2) : ℕ∞) ≤
      Lambda (↑(ReedSolomon.code domain k) : Set (ι → F))
        (((δᵣ (↑(ReedSolomon.code domain k) : Set (ι → F)) : ℚ≥0) : ℝ)
          - ((khat * d - k + 1 : ℕ) : ℝ) / (Fintype.card ι : ℝ)) := by
  obtain ⟨H, hHcard, -, hfib, hanti⟩ := Smooth.exists_pow_projection_structure domain hn
  exact choose_le_Lambda_rs_antipodal_even domain hn hHcard hfib (hanti hheven).1
    (hanti hheven).2 hkhat hkh hkeven hk1 hk2

omit [DecidableEq ι] in
/-- `choose_le_Lambda_rs_antipodal_odd` specialized to a smooth domain with even `h`. -/
theorem choose_le_Lambda_rs_antipodal_odd_of_smooth (domain : ι ↪ F)
    [ReedSolomon.Smooth domain] {d h khat k : ℕ}
    (hn : Fintype.card ι = d * h) (hheven : Even h)
    (hkhat : 1 ≤ khat) (hkh : khat < h) (hkodd : Odd khat)
    (hk1 : (khat - 2) * d < k) (hk2 : k ≤ khat * d) :
    ((h / 2 - 1).choose ((khat - 1) / 2) : ℕ∞) ≤
      Lambda (↑(ReedSolomon.code domain k) : Set (ι → F))
        (((δᵣ (↑(ReedSolomon.code domain k) : Set (ι → F)) : ℚ≥0) : ℝ)
          - ((khat * d - k + 1 : ℕ) : ℝ) / (Fintype.card ι : ℝ)) := by
  obtain ⟨H, hHcard, -, hfib, hanti⟩ := Smooth.exists_pow_projection_structure domain hn
  exact choose_le_Lambda_rs_antipodal_odd domain hn hHcard hfib (hanti hheven).1
    (hanti hheven).2 hkhat hkh hkodd hk1 hk2

end SmoothBridge

end CodingTheory.AdditiveSetListDecoding

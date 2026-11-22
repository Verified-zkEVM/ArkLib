/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, XC0R
-/
module

public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.Algebra.MvPolynomial.SchwartzZippel
public import Mathlib.Algebra.Order.Ring.NNRat
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Data.Fintype.CardEmbedding

/-!
# The Schwartz–Zippel bound as a zero count

Mathlib's `MvPolynomial.schwartz_zippel_totalDegree` bounds the proportion of zeros of a nonzero
polynomial in `n` variables over a domain on a grid `Sⁿ` by `totalDegree / #S`, in `ℚ≥0`. For
`n + 1` variables this is equivalent to the division-free count

  `#{x ∈ Sⁿ⁺¹ | p(x) = 0} ≤ totalDegree p * #S ^ n`,

which is `card_filter_eval_eq_zero_le`. The empty grid needs no special hypothesis: it has no
points.

Among the `(#S).descFactorial n` points of `Sⁿ` with pairwise-distinct coordinates, a nonzero
polynomial `p` in `n` variables over a domain vanishes at `N` of them, where

  `N * (#S - n + 1) ≤ p.totalDegree * (#S).descFactorial n`,

which is `card_filter_injective_eval_eq_zero_le`. So a tuple of `n` elements of `S` drawn without
replacement is a zero of `p` with probability at most `p.totalDegree / (#S - n + 1)`.

The proof follows `MvPolynomial.schwartz_zippel_sup_sum`. Write `p` as a polynomial in `X 0` with
leading coefficient `pₖ` in the other variables. Given pairwise-distinct values of the other
`n - 1` coordinates, the first coordinate ranges over the `#S - n + 1` elements of `S` they miss;
at most `k` of them are zeros unless `pₖ` vanishes there, which the induction hypothesis counts.
-/

@[expose] public section

namespace MvPolynomial

open Finset

variable {R : Type*} [CommRing R] [IsDomain R] [DecidableEq R]

/-- **Schwartz–Zippel, division-free.** A nonzero polynomial `p` in `n + 1` variables over a domain
has at most `p.totalDegree * #S ^ n` zeros on the grid `Sⁿ⁺¹`. -/
theorem card_filter_eval_eq_zero_le {n : ℕ} {p : MvPolynomial (Fin (n + 1)) R} (hp : p ≠ 0)
    (S : Finset R) :
    #{x ∈ Fintype.piFinset fun _ ↦ S | eval x p = 0} ≤ p.totalDegree * #S ^ n := by
  obtain rfl | hS := S.eq_empty_or_nonempty
  · simp
  have h := schwartz_zippel_totalDegree hp S
  have hpos : (0 : ℚ≥0) < #S := by exact_mod_cast hS.card_pos
  rw [div_le_div_iff₀ (pow_pos hpos _) hpos, pow_succ, ← mul_assoc] at h
  exact_mod_cast le_of_mul_le_mul_right h hpos

omit [CommRing R] [IsDomain R] in
/-- There are `(#S).descFactorial n` points of `Sⁿ` with pairwise-distinct coordinates. -/
private theorem card_filter_piFinset_injective (S : Finset R) (n : ℕ) :
    #{x ∈ Fintype.piFinset fun _ : Fin n ↦ S | Function.Injective x} = (#S).descFactorial n := by
  have h := Fintype.card_embedding_eq (α := Fin n) (β := S)
  rw [Fintype.card_fin, Fintype.card_coe] at h
  rw [← h, ← card_univ]
  refine card_bij' (fun x hx ↦ ⟨fun i ↦ ⟨x i, Fintype.mem_piFinset.mp (mem_filter.mp hx).1 i⟩,
      fun i j hij ↦ (mem_filter.mp hx).2 (congrArg Subtype.val hij)⟩)
    (fun e _ i ↦ (e i : R)) (fun _ _ ↦ mem_univ _) (fun e _ ↦ ?_) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)
  exact mem_filter.mpr ⟨Fintype.mem_piFinset.mpr fun i ↦ (e i).2,
    fun i j hij ↦ e.injective (Subtype.ext hij)⟩

/-- **Schwartz–Zippel over pairwise-distinct points, division-free.** A nonzero polynomial `p` in
`n` variables over a domain vanishes at `N` points of `Sⁿ` with pairwise-distinct coordinates,
where `N * (#S - n + 1) ≤ p.totalDegree * (#S).descFactorial n`. -/
theorem card_filter_injective_eval_eq_zero_le {n : ℕ} {p : MvPolynomial (Fin n) R} (hp : p ≠ 0)
    (S : Finset R) :
    #{x ∈ Fintype.piFinset fun _ ↦ S | Function.Injective x ∧ eval x p = 0} * (#S - n + 1) ≤
      p.totalDegree * (#S).descFactorial n := by
  induction n with
  | zero =>
    rw [p.eq_C_of_isEmpty] at hp ⊢
    simp [C_ne_zero.mp hp]
  | succ n ih =>
    set p' := finSuccEquiv R n p
    set k := p'.natDegree
    set pₖ := p'.leadingCoeff
    have hpₖ : pₖ ≠ 0 := Polynomial.leadingCoeff_ne_zero.2 (EmbeddingLike.map_ne_zero_iff.2 hp)
    set T := {t ∈ Fintype.piFinset fun _ : Fin n ↦ S | Function.Injective t}
    set Z := {x ∈ Fintype.piFinset fun _ : Fin (n + 1) ↦ S | Function.Injective x ∧ eval x p = 0}
    rcases lt_or_ge n #S with hn | hn
    swap
    · have hZ : #Z ≤ (#S).descFactorial (n + 1) := by
        rw [← card_filter_piFinset_injective]
        exact card_le_card fun x hx ↦ mem_filter.mpr ⟨(mem_filter.mp hx).1, (mem_filter.mp hx).2.1⟩
      rw [Nat.descFactorial_eq_zero_iff_lt.mpr (by omega), Nat.le_zero] at hZ
      simp [hZ]
    have hfib : ∀ t ∈ T, #{x ∈ Z | Fin.tail x = t} ≤ if eval t pₖ = 0 then #S - n else k := by
      intro t ht
      have hinj : Set.InjOn (fun x : Fin (n + 1) → R ↦ x 0)
          ({x ∈ Z | Fin.tail x = t} : Finset _) := by
        intro x hx y hy hxy
        rw [← Fin.cons_self_tail x, ← Fin.cons_self_tail y, (mem_filter.mp (mem_coe.mp hx)).2,
          (mem_filter.mp (mem_coe.mp hy)).2]
        simp only at hxy
        rw [hxy]
      split_ifs with h0
      · have hsub : univ.image t ⊆ S := fun _ hy ↦ by
          obtain ⟨i, -, rfl⟩ := mem_image.mp hy
          exact Fintype.mem_piFinset.mp (mem_filter.mp ht).1 i
        have hcard : #(S \ univ.image t) = #S - n := by
          rw [card_sdiff_of_subset hsub, card_image_of_injective _ (mem_filter.mp ht).2, card_univ,
            Fintype.card_fin]
        rw [← hcard]
        refine card_le_card_of_injOn _ (fun x hx ↦ ?_) hinj
        obtain ⟨hxZ, rfl⟩ := mem_filter.mp hx
        obtain ⟨hxS, hxinj, -⟩ := mem_filter.mp hxZ
        refine mem_sdiff.mpr ⟨Fintype.mem_piFinset.mp hxS 0, fun hx0 ↦ ?_⟩
        obtain ⟨i, -, hi⟩ := mem_image.mp hx0
        exact Fin.succ_ne_zero i (hxinj hi)
      · have hq : p'.map (eval t) ≠ 0 := fun hq ↦ h0 <| by
          have h := congrArg (fun q ↦ q.coeff k) hq
          rwa [Polynomial.coeff_map, Polynomial.coeff_zero] at h
        calc #{x ∈ Z | Fin.tail x = t}
            ≤ #(p'.map (eval t)).roots.toFinset := by
              refine card_le_card_of_injOn _ (fun x hx ↦ ?_) hinj
              obtain ⟨hxZ, rfl⟩ := mem_filter.mp hx
              rw [mem_coe, Multiset.mem_toFinset, Polynomial.mem_roots hq, Polynomial.IsRoot.def,
                ← eval_eq_eval_mv_eval', Fin.cons_self_tail]
              exact (mem_filter.mp hxZ).2.2
          _ ≤ Multiset.card (p'.map (eval t)).roots := Multiset.toFinset_card_le _
          _ ≤ (p'.map (eval t)).natDegree := Polynomial.card_roots' _
          _ ≤ k := Polynomial.natDegree_map_le
    have hZ : #Z ≤ #{t ∈ Fintype.piFinset fun _ : Fin n ↦ S |
        Function.Injective t ∧ eval t pₖ = 0} * (#S - n) + k * #T := by
      rw [card_eq_sum_card_fiberwise (f := Fin.tail) (t := T) fun x hx ↦ ?_]
      · refine (sum_le_sum hfib).trans ?_
        rw [sum_ite, sum_const, sum_const, smul_eq_mul, smul_eq_mul, filter_filter, mul_comm _ k]
        exact Nat.add_le_add_left (Nat.mul_le_mul_left k (card_filter_le _ _)) _
      · obtain ⟨hxS, hxinj, -⟩ := mem_filter.mp hx
        exact mem_filter.mpr ⟨Fintype.mem_piFinset.mpr fun i ↦ Fintype.mem_piFinset.mp hxS i.succ,
          hxinj.comp (Fin.succ_injective _)⟩
    rw [card_filter_piFinset_injective] at hZ
    rw [Nat.descFactorial_succ, show #S - (n + 1) + 1 = #S - n by omega]
    calc #Z * (#S - n)
        ≤ (#{t ∈ Fintype.piFinset fun _ : Fin n ↦ S | Function.Injective t ∧ eval t pₖ = 0} *
            (#S - n + 1) + k * (#S).descFactorial n) * (#S - n) := by
          gcongr
          exact hZ.trans (by gcongr; omega)
      _ ≤ (pₖ.totalDegree + k) * (#S).descFactorial n * (#S - n) := by
          rw [add_mul pₖ.totalDegree]
          exact Nat.mul_le_mul_right _ (Nat.add_le_add_right (ih hpₖ) _)
      _ ≤ p.totalDegree * ((#S - n) * (#S).descFactorial n) := by
          rw [mul_comm (#S - n), ← mul_assoc]
          gcongr
          exact totalDegree_coeff_finSuccEquiv_add_le p k hpₖ

end MvPolynomial

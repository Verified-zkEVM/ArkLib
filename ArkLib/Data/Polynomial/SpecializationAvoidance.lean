/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import Mathlib.Algebra.Polynomial.Roots

/-!
# Specialization points that avoid a polynomial's roots

A nonzero polynomial over a domain has at most `natDegree` roots. This file turns that bound into
existence statements for specialization points: from a finite candidate set that is larger than a
forbidden set plus the degree of a polynomial `c`, some candidate is neither forbidden nor a root
of `c`. Taking `c` to be the leading coefficient of `A : R[X][X]` gives a specialization
`A.map (evalRingHom t)` of the coefficient variable that keeps the outer degree of `A`.

## Main statements

* `card_le_natDegree_of_injOn_of_eval_eq_zero`: if a nonzero `p` vanishes at `x w` for every
  `w ∈ s`, and `x` is injective on `s`, then `s.card ≤ p.natDegree`.
* `exists_forall_eval_ne_zero`: finitely many nonzero polynomials have a common nonvanishing
  evaluation over an infinite domain.
* `exists_mem_eval_ne_zero_of_card_add_natDegree_lt_card`: if
  `forbidden.card + c.natDegree < T.card`, some `t ∈ T` is not forbidden and `c.eval t ≠ 0`.
* `exists_mem_map_evalRingHom_ne_zero_of_card_add_natDegree_lt_card`: the degree-preserving
  specialization of the coefficient variable of `A : R[X][X]`, chosen from a finite candidate set.
* `exists_map_evalRingHom_ne_zero_avoiding` and `exists_map_evalRingHom_ne_zero`: the same over an
  infinite domain, with no candidate set.
* `exists_card_le_forall_eval_eq_zero_iff`: a family of polynomials of degree at most `d`, all
  zero outside an index set `s`, has an exceptional set of at most `d * s.card` points outside
  which each member vanishes only if it is the zero polynomial.

The finite candidate forms apply over finite fields, where the infinite forms do not.

## Proof outline

The counting statement maps `s` injectively into the roots of `p` and applies Mathlib's
`card_le_degree_of_subset_roots`. For the avoidance statement, if every non-forbidden candidate
were a root of `c`, the set `T \ forbidden`, of size at least `T.card - forbidden.card`, would
exceed `c.natDegree`. For `A : R[X][X]`, a point `t` with `A.leadingCoeff.eval t ≠ 0` keeps the
leading coefficient under `evalRingHom t`, so `natDegree_map_of_leadingCoeff_ne_zero` applies.
Over an infinite domain, `Infinite.exists_subset_card_eq` supplies a candidate set of any size.

Mathlib's `eq_zero_of_natDegree_lt_card_of_eval_eq_zero` is the contrapositive of the counting
statement for a map that is injective on a whole `Fintype` index. The counting statement here
takes a finset, a map injective on that finset, and concludes a cardinality bound; the avoidance
statements below use it in that form.
-/

@[expose] public section

namespace Polynomial

variable {R α : Type*} [CommRing R] [IsDomain R]

/-- In an infinite domain, finitely many nonzero polynomials have a common nonvanishing point. -/
theorem exists_forall_eval_ne_zero {ι : Type*} [Infinite R] (T : Finset ι)
    (P : ι → Polynomial R) (hT : ∀ i ∈ T, P i ≠ 0) :
    ∃ center : R, ∀ i ∈ T, (P i).eval center ≠ 0 := by
  classical
  have hprod : ∏ i ∈ T, P i ≠ 0 := Finset.prod_ne_zero_iff.mpr hT
  obtain ⟨center, hc⟩ :
      ∃ center : R, (∏ i ∈ T, P i).eval center ≠ 0 := by
    by_contra! h
    exact hprod (Polynomial.funext (by simpa using h))
  refine ⟨center, fun P hP ↦ ?_⟩
  rw [Polynomial.eval_prod, Finset.prod_ne_zero_iff] at hc
  exact hc P hP

/-- A nonzero polynomial `p` over a domain vanishes at no more than `p.natDegree` of the points
`x w`, `w ∈ s`, when `x` is injective on `s`.

`hp` is necessary because the zero polynomial vanishes everywhere. `hx` is necessary because a
root hit by several `w` is counted once among the roots. The domain assumption is necessary:
over `ZMod 8`, the polynomial `X ^ 2 - 1` of degree `2` has the four roots `1, 3, 5, 7`. With
`x := id` this is Mathlib's `card_le_degree_of_subset_roots`; with `R := F[X]` and `x := C` it
bounds the number of constants `w` with `p.eval (C w) = 0`. -/
theorem card_le_natDegree_of_injOn_of_eval_eq_zero {p : R[X]} (hp : p ≠ 0) {x : α → R}
    {s : Finset α} (hx : Set.InjOn x s) (hroot : ∀ w ∈ s, p.eval (x w) = 0) :
    s.card ≤ p.natDegree := by
  classical
  rw [← Finset.card_image_of_injOn hx]
  refine card_le_degree_of_subset_roots fun r hr ↦ ?_
  obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hr
  exact (mem_roots hp).mpr (hroot w hw)

/-- If a finite candidate set `T` has more than `forbidden.card + c.natDegree` elements, then
some candidate `t ∈ T` is not in `forbidden` and is not a root of the nonzero polynomial `c`.

`hc` is necessary because every point is a root of `0`. The bound is sharp: if
`T.card = forbidden.card + c.natDegree`, the forbidden points and the roots of `c` can cover `T`.
`forbidden` need not be a subset of `T`, and only its size matters. The statement is written as
`t ∈ T` and `t ∉ forbidden` rather than `t ∈ T \ forbidden` so that it needs no decidable
equality on `R`. -/
theorem exists_mem_eval_ne_zero_of_card_add_natDegree_lt_card {c : R[X]} (hc : c ≠ 0)
    {T forbidden : Finset R} (hcard : forbidden.card + c.natDegree < T.card) :
    ∃ t ∈ T, t ∉ forbidden ∧ c.eval t ≠ 0 := by
  classical
  by_contra! hroot
  have hle := card_le_natDegree_of_injOn_of_eval_eq_zero hc (x := id) (s := T \ forbidden)
    (Set.injOn_id _) fun t ht ↦ hroot t (Finset.mem_sdiff.mp ht).1 (Finset.mem_sdiff.mp ht).2
  have hsdiff := Finset.le_card_sdiff forbidden T
  omega

/-- A nonzero `A : R[X][X]` has a specialization `t` of its coefficient variable, chosen from a
finite candidate set `T` and outside `forbidden`, at which `A.map (evalRingHom t)` is nonzero
and has the same degree as `A`.

The candidate set must have more than `forbidden.card + A.leadingCoeff.natDegree` elements,
because the points `t` at which the conclusion fails are exactly the roots of
`A.leadingCoeff`. For a finite field `F` and `R := F`, take `T := Finset.univ`. `hA` is necessary
because `0` has no nonzero specialization. -/
theorem exists_mem_map_evalRingHom_ne_zero_of_card_add_natDegree_lt_card {A : R[X][X]}
    (hA : A ≠ 0) {T forbidden : Finset R}
    (hcard : forbidden.card + A.leadingCoeff.natDegree < T.card) :
    ∃ t ∈ T, t ∉ forbidden ∧ A.map (evalRingHom t) ≠ 0 ∧
      (A.map (evalRingHom t)).natDegree = A.natDegree := by
  obtain ⟨t, htT, htforbidden, heval⟩ :=
    exists_mem_eval_ne_zero_of_card_add_natDegree_lt_card (leadingCoeff_ne_zero.mpr hA) hcard
  have hleading : evalRingHom t A.leadingCoeff ≠ 0 := heval
  refine ⟨t, htT, htforbidden, fun hzero ↦ hleading ?_,
    natDegree_map_of_leadingCoeff_ne_zero _ hleading⟩
  rw [leadingCoeff, ← coeff_map, hzero, coeff_zero]

/-- Over an infinite domain, a nonzero `A : R[X][X]` has a specialization `t` of its coefficient
variable outside any finite set `forbidden` at which `A.map (evalRingHom t)` is nonzero and has
the same degree as `A`.

It follows from
`exists_mem_map_evalRingHom_ne_zero_of_card_add_natDegree_lt_card` with a candidate set of size
`forbidden.card + A.leadingCoeff.natDegree + 1`. Over a finite field use that finite form. -/
theorem exists_map_evalRingHom_ne_zero_avoiding [Infinite R] (A : R[X][X]) (hA : A ≠ 0)
    (forbidden : Finset R) :
    ∃ t : R, t ∉ forbidden ∧ A.map (evalRingHom t) ≠ 0 ∧
      (A.map (evalRingHom t)).natDegree = A.natDegree := by
  obtain ⟨T, hT⟩ :=
    Infinite.exists_subset_card_eq R (forbidden.card + A.leadingCoeff.natDegree + 1)
  obtain ⟨t, -, ht⟩ :=
    exists_mem_map_evalRingHom_ne_zero_of_card_add_natDegree_lt_card hA (T := T)
      (forbidden := forbidden) (by omega)
  exact ⟨t, ht⟩

/-- Over an infinite domain, a nonzero `A : R[X][X]` has a specialization of its coefficient
variable at which `A.map (evalRingHom t)` is nonzero and has the same degree as `A`. This is the
case `forbidden = ∅` of `exists_map_evalRingHom_ne_zero_avoiding`. -/
theorem exists_map_evalRingHom_ne_zero [Infinite R] (A : R[X][X]) (hA : A ≠ 0) :
    ∃ t : R, A.map (evalRingHom t) ≠ 0 ∧
      (A.map (evalRingHom t)).natDegree = A.natDegree := by
  obtain ⟨t, -, ht⟩ := exists_map_evalRingHom_ne_zero_avoiding A hA ∅
  exact ⟨t, ht⟩

/-- **Simultaneous non-vanishing of a family.** Let `p i` be polynomials over a domain, with
`(p i).natDegree ≤ d` for `i ∈ s` and `p i = 0` for `i ∉ s`. Some set of at most `d * s.card`
points, the union of the roots of the nonzero `p i`, contains every `z` at which a nonzero member
vanishes: outside it, `(p i).eval z = 0` holds exactly when `p i = 0`.

The index type need not be finite; only the members indexed by `s` can be nonzero. -/
theorem exists_card_le_forall_eval_eq_zero_iff {ι : Type*} (p : ι → R[X]) {d : ℕ}
    (s : Finset ι) (hp : ∀ i ∈ s, (p i).natDegree ≤ d) (hs : ∀ i ∉ s, p i = 0) :
    ∃ exceptional : Finset R, exceptional.card ≤ d * s.card ∧
      ∀ z ∉ exceptional, ∀ i, (p i).eval z = 0 ↔ p i = 0 := by
  classical
  refine ⟨s.biUnion fun i ↦ (p i).roots.toFinset, ?_, fun z hz i ↦ ?_⟩
  · rw [mul_comm]
    refine Finset.card_biUnion_le_card_mul _ _ _ fun i hi ↦ ?_
    exact ((Multiset.toFinset_card_le _).trans (card_roots' _)).trans (hp i hi)
  · refine ⟨fun heval ↦ ?_, fun h ↦ by simp [h]⟩
    by_contra hne
    exact hz (Finset.mem_biUnion.mpr ⟨i, by_contra fun hi ↦ hne (hs i hi),
      Multiset.mem_toFinset.mpr ((mem_roots hne).mpr heval)⟩)

end Polynomial

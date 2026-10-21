/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import Mathlib.Algebra.Polynomial.Roots

/-!
# Collisions of polynomial tuples at sampled points

Let `S` be a finite family of tuples `f : κ → R[X]` of polynomials over a domain `R`, each
coordinate of natural degree at most `d`, and let `x : ι → R` be a tuple of `|ι|` points.
Evaluating every coordinate of `f` at every point gives `evalTuple x f : ι → κ → R`. The points
*separate* `S` when `evalTuple x` is injective on `S`.

Two distinct tuples `f ≠ g` differ in some coordinate `j`, and `f j - g j` is a nonzero polynomial
of natural degree at most `d`, so it has at most `d` roots. If `evalTuple x f = evalTuple x g`,
every point `x i` is such a root. Hence at most `d ^ |ι|` point tuples make `f` and `g` collide,
and a union bound over the `choose |S| 2` unordered pairs shows that at most
`choose |S| 2 * d ^ |ι|` point tuples fail to separate `S`. Dividing by the size of a sample space
gives the probability form, which is in
`ArkLib.Data.Polynomial.PointCollisionProbability`.

## Main definitions

* `Polynomial.evalTuple`: the evaluations of a polynomial tuple at a point tuple.

## Main statements

* `Polynomial.card_le_of_evalTuple_eq`: two distinct tuples collide on at most `d ^ |ι|` point
  tuples.
* `Polynomial.card_le_of_not_injOn_evalTuple`: at most `choose |S| 2 * d ^ |ι|` point tuples fail
  to separate a finite family `S`.
* `Polynomial.exists_option_eq_some_iff_of_injOn_evalTuple`: separating points select at most
  one tuple for each claimed value array.
* `Polynomial.evalTuple_mul_add_of_eval_eq_zero`: reconstruction `D * q + I` from a divisor `D`
  vanishing at the points has the same point evaluations as `I`.
-/

@[expose] public section

namespace Polynomial

section Semiring

variable {R ι κ : Type*} [CommSemiring R]

/-- The evaluations of every coordinate of `f : κ → R[X]` at every point of `x : ι → R`. With
`x` a Reed–Solomon evaluation domain this is the interleaved codeword of the message tuple `f`;
with `x` a tuple of sampled anchors it is the tuple of anchor values. -/
def evalTuple (x : ι → R) (f : κ → R[X]) : ι → κ → R :=
  fun i j ↦ (f j).eval (x i)

/-- Entry `(i, j)` of `evalTuple x f` is `f j` evaluated at `x i`. -/
@[simp] theorem evalTuple_apply (x : ι → R) (f : κ → R[X]) (i : ι) (j : κ) :
    evalTuple x f i j = (f j).eval (x i) := rfl

/-- **Point values of a reconstruction.** If the divisor `D` vanishes at every point `x i`, then
the coordinatewise reconstruction `D * q j + I j` has the same point values as `I`, whatever the
quotients `q`. This is `eval_mul_add_of_eval_eq_zero` in every coordinate. -/
theorem evalTuple_mul_add_of_eval_eq_zero {D : R[X]} {x : ι → R} (hx : ∀ i, D.eval (x i) = 0)
    (q I : κ → R[X]) : evalTuple x (fun j ↦ D * q j + I j) = evalTuple x I := by
  funext i j
  simp [hx i]

/-- **Selection by separating points.** If the points `x` separate a set `S` of polynomial
tuples, then for each claimed value array `c` there is an option that is `some f` exactly for the
tuple `f ∈ S` whose point values are `c`, and `none` if there is no such tuple.

The option depends only on `x`, `S` and `c`. A statement that quantifies over data chosen later
can therefore compare that data with a candidate fixed in advance. -/
theorem exists_option_eq_some_iff_of_injOn_evalTuple {x : ι → R} {S : Set (κ → R[X])}
    (hS : Set.InjOn (evalTuple x) S) (c : ι → κ → R) :
    ∃ o : Option (κ → R[X]), ∀ f, o = some f ↔ f ∈ S ∧ evalTuple x f = c := by
  classical
  by_cases h : ∃ f ∈ S, evalTuple x f = c
  · obtain ⟨f, hf, hfc⟩ := h
    refine ⟨some f, fun g ↦ ⟨?_, fun hg ↦ ?_⟩⟩
    · rintro ⟨⟩
      exact ⟨hf, hfc⟩
    · exact congrArg some (hS hf hg.1 (hfc.trans hg.2.symm))
  · refine ⟨none, fun g ↦ ⟨fun h ↦ (Option.some_ne_none _ h.symm).elim, fun hg ↦ ?_⟩⟩
    exact (h ⟨g, hg⟩).elim

end Semiring

section Domain

variable {R ι κ : Type*} [CommRing R] [IsDomain R] [Fintype ι]

/-- **Collisions of one pair.** Two distinct polynomial tuples whose coordinates have natural
degree at most `d` have equal evaluations on at most `d ^ |ι|` point tuples `x : ι → R`.

Some coordinate `f j - g j` is nonzero of natural degree at most `d`, and every point of a
colliding tuple is one of its at most `d` roots. `f ≠ g` is needed: a tuple collides with itself
at every point. The domain assumption is needed: over `ZMod 8` the tuples `X ^ 2 - 1` and `0` of
degree `2` collide at the four points `1, 3, 5, 7`. -/
theorem card_le_of_evalTuple_eq {f g : κ → R[X]} (hne : f ≠ g) {d : ℕ}
    (hf : ∀ j, (f j).natDegree ≤ d) (hg : ∀ j, (g j).natDegree ≤ d) (T : Finset (ι → R))
    (hT : ∀ x ∈ T, evalTuple x f = evalTuple x g) : T.card ≤ d ^ Fintype.card ι := by
  classical
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hne
  have hp : f j - g j ≠ 0 := sub_ne_zero.mpr hj
  have hroots : (f j - g j).roots.toFinset.card ≤ d :=
    (Multiset.toFinset_card_le _).trans <| (card_roots' _).trans <|
      (natDegree_sub_le _ _).trans (max_le (hf j) (hg j))
  calc T.card ≤ (Fintype.piFinset fun _ : ι ↦ (f j - g j).roots.toFinset).card := by
        refine Finset.card_le_card fun x hx ↦ Fintype.mem_piFinset.mpr fun i ↦ ?_
        have hxi := congrFun (congrFun (hT x hx) i) j
        simp only [evalTuple_apply] at hxi
        simp [Multiset.mem_toFinset, mem_roots hp, hxi]
    _ = (f j - g j).roots.toFinset.card ^ Fintype.card ι := by simp [Fintype.card_piFinset]
    _ ≤ d ^ Fintype.card ι := Nat.pow_le_pow_left hroots _

/-- **Collisions of a finite family.** If every coordinate of every tuple in `S` has natural
degree at most `d`, then any finite set `T` of point tuples, none of which separates `S`, has at
most `choose |S| 2 * d ^ |ι|` elements.

Each non-separating point tuple makes some unordered pair `{f, g} ⊆ S` collide, and each pair
collides on at most `d ^ |ι|` point tuples by `card_le_of_evalTuple_eq`. For `|S| ≤ 1` the bound
is `0`: every point tuple separates a family with at most one element. -/
theorem card_le_of_not_injOn_evalTuple (S : Finset (κ → R[X])) {d : ℕ}
    (hdeg : ∀ f ∈ S, ∀ j, (f j).natDegree ≤ d) (T : Finset (ι → R))
    (hT : ∀ x ∈ T, ¬ Set.InjOn (evalTuple x) (S : Set (κ → R[X]))) :
    T.card ≤ S.card.choose 2 * d ^ Fintype.card ι := by
  classical
  let collide : Finset (κ → R[X]) → Finset (ι → R) := fun t ↦
    T.filter fun x ↦ ∀ f ∈ t, ∀ g ∈ t, evalTuple x f = evalTuple x g
  have hsub : T ⊆ (S.powersetCard 2).biUnion collide := by
    intro x hx
    have hx' := hT x hx
    simp only [Set.InjOn, not_forall, exists_prop] at hx'
    obtain ⟨f, hf, g, hg, hfg, hne⟩ := hx'
    refine Finset.mem_biUnion.mpr ⟨{f, g}, Finset.mem_powersetCard.mpr
      ⟨Finset.insert_subset_iff.mpr ⟨hf, Finset.singleton_subset_iff.mpr hg⟩,
        Finset.card_pair hne⟩, Finset.mem_filter.mpr ⟨hx, ?_⟩⟩
    simp only [Finset.mem_insert, Finset.mem_singleton]
    rintro f' (rfl | rfl) g' (rfl | rfl) <;> simp [hfg]
  have hpair : ∀ t ∈ S.powersetCard 2, (collide t).card ≤ d ^ Fintype.card ι := by
    intro t ht
    obtain ⟨htS, htcard⟩ := Finset.mem_powersetCard.mp ht
    obtain ⟨f, g, hne, rfl⟩ := Finset.card_eq_two.mp htcard
    refine card_le_of_evalTuple_eq hne (hdeg f (htS (by simp))) (hdeg g (htS (by simp))) _ ?_
    intro x hx
    exact (Finset.mem_filter.mp hx).2 f (by simp) g (by simp)
  calc T.card ≤ ((S.powersetCard 2).biUnion collide).card := Finset.card_le_card hsub
    _ ≤ ∑ t ∈ S.powersetCard 2, (collide t).card := Finset.card_biUnion_le
    _ ≤ ∑ _t ∈ S.powersetCard 2, d ^ Fintype.card ι := Finset.sum_le_sum hpair
    _ = S.card.choose 2 * d ^ Fintype.card ι := by
      rw [Finset.sum_const, Finset.card_powersetCard, smul_eq_mul]

end Domain

end Polynomial

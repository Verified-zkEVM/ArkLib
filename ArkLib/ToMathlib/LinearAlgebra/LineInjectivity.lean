/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import Mathlib.Algebra.Module.Torsion.Free
public import Mathlib.Data.Set.Finite.Lattice
public import Mathlib.Tactic.Abel

/-!
# Specializing a finite family of lines injectively

Let `V` be a torsion-free module over a domain `K`. A pair `(a, b)` of vectors
defines the line `z ↦ a + z • b`. Two distinct pairs define lines that meet in at most one
parameter: if `a + x • b = c + x • d` and `a + y • b = c + y • d` with `x ≠ y`, then
`(x - y) • (b - d) = 0`, so `b = d` and then `a = c`.

Consequently, for a finite family of distinct pairs, only finitely many parameters `z` make two
members of the family meet, and when `K` is infinite some `z` outside any prescribed finite set
separates the whole family.

## Main statements

* `eq_and_eq_of_add_smul_eq_add_smul_of_ne`: two parameters determine the pair.
* `subsingleton_setOf_add_smul_eq_add_smul`: distinct pairs meet at most once.
* `Set.Finite.finite_setOf_not_injOn_add_smul`: finitely many parameters fail to separate a finite
  family.
* `Set.Finite.exists_notMem_injOn_add_smul`: over an infinite domain, a separating parameter
  avoids any finite set.
-/

@[expose] public section

variable {K V : Type*} [Ring K] [IsDomain K] [AddCommGroup V] [Module K V]
  [Module.IsTorsionFree K V]

/-- **Two parameters determine a line.** If the lines `z ↦ a + z • b` and `z ↦ c + z • d` agree
at two distinct parameters `x ≠ y`, then `a = c` and `b = d`.

The hypothesis `Module.IsTorsionFree K V` is needed: the difference of the two equations is
`(x - y) • (b - d) = 0`, and without it `b - d` can be a nonzero torsion vector. For example, in
the `ℤ`-module `ZMod 2` the lines `z ↦ 0 + z • 1` and `z ↦ 0 + z • 0` agree at `z = 0` and
`z = 2`. -/
theorem eq_and_eq_of_add_smul_eq_add_smul_of_ne {a b c d : V} {x y : K} (hxy : x ≠ y)
    (hx : a + x • b = c + x • d) (hy : a + y • b = c + y • d) : a = c ∧ b = d := by
  have hbd : (x - y) • (b - d) = 0 := by
    have h : (x - y) • (b - d) = (a + x • b - (c + x • d)) - (a + y • b - (c + y • d)) := by
      simp only [sub_smul, smul_sub]
      abel
    rw [h, hx, hy, sub_self, sub_self, sub_zero]
  have hbd' : b = d := sub_eq_zero.mp ((smul_eq_zero_iff_right (sub_ne_zero.mpr hxy)).mp hbd)
  subst hbd'
  exact ⟨add_right_cancel hx, rfl⟩

/-- **Distinct lines meet at most once.** If `(a, b) ≠ (c, d)`, at most one parameter `z`
satisfies `a + z • b = c + z • d`. -/
theorem subsingleton_setOf_add_smul_eq_add_smul {a b c d : V} (hne : (a, b) ≠ (c, d)) :
    {z : K | a + z • b = c + z • d}.Subsingleton := by
  intro x hx y hy
  by_contra hxy
  obtain ⟨rfl, rfl⟩ := eq_and_eq_of_add_smul_eq_add_smul_of_ne hxy hx hy
  exact hne rfl

namespace Set.Finite

variable {α : Type*} {s : Set α}

/-- **Finitely many parameters fail to separate a finite family.** Let `s` be finite and let the
pairs `(a p, b p)` be distinct for distinct `p ∈ s`. Then the parameters `z` at which
`p ↦ a p + z • b p` is not injective on `s` form a finite set: each of the finitely many
unordered pairs of members of `s` contributes at most one such parameter.

The injectivity hypothesis `hab` is needed: if two members of `s` give the same pair, every
parameter fails. -/
theorem finite_setOf_not_injOn_add_smul (hs : s.Finite) (a b : α → V)
    (hab : Set.InjOn (fun p ↦ (a p, b p)) s) :
    {z : K | ¬ Set.InjOn (fun p ↦ a p + z • b p) s}.Finite := by
  have hfin : (⋃ p ∈ s, ⋃ q ∈ s,
      {z : K | p ≠ q ∧ a p + z • b p = a q + z • b q}).Finite := by
    refine hs.biUnion fun p hp ↦ hs.biUnion fun q hq ↦ ?_
    by_cases hpq : p = q
    · simp [hpq]
    · exact (subsingleton_setOf_add_smul_eq_add_smul fun h ↦ hpq (hab hp hq h)).finite.subset
        fun _ hz ↦ hz.2
  refine hfin.subset fun z hz ↦ ?_
  simp only [Set.InjOn, not_forall] at hz
  obtain ⟨p, hp, q, hq, heq, hne⟩ := hz
  simp only [Set.mem_iUnion]
  exact ⟨p, hp, q, hq, hne, heq⟩

/-- **A separating parameter avoiding a finite set.** Over an infinite domain `K`, for a finite
family `s` whose pairs `(a p, b p)` are distinct, some parameter `z ∉ avoid` makes
`p ↦ a p + z • b p` injective on `s`, for any finite set `avoid`.

`Infinite K` is needed: over a finite field the separating parameters can all be excluded, for
example by `avoid = Set.univ`. -/
theorem exists_notMem_injOn_add_smul [Infinite K] (hs : s.Finite) (a b : α → V)
    (hab : Set.InjOn (fun p ↦ (a p, b p)) s) {avoid : Set K} (havoid : avoid.Finite) :
    ∃ z ∉ avoid, Set.InjOn (fun p ↦ a p + z • b p) s := by
  obtain ⟨z, hz⟩ := ((hs.finite_setOf_not_injOn_add_smul a b hab).union havoid).exists_notMem
  simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_not] at hz
  exact ⟨z, hz.2, hz.1⟩

end Set.Finite

/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XC0R
-/
module

public import Mathlib.Algebra.CharP.Two
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-!
# Additive subgroups of a finite binary field

A finite field with `2 ^ m` elements has at least `2 ^ (v * (m - v))` additive subgroups of size
`2 ^ v`, namely the graphs of `𝔽₂`-linear maps `𝔽₂ ^ v → 𝔽₂ ^ (m - v)`.

## Main statements

* `FiniteField.two_pow_le_card_addSubgroup`
-/

@[expose] public section

namespace FiniteField

section Counting

variable {F : Type*} [Field F] [Fintype F]

/-- A field of characteristic `2` with `2 ^ m` elements is additively
`(ZMod 2) ^ v × (ZMod 2) ^ (m - v)`. -/
private theorem nonempty_addEquiv_prod [CharP F 2] {m v : ℕ} (hF : Fintype.card F = 2 ^ m)
    (hv : v ≤ m) : Nonempty (F ≃+ (Fin v → ZMod 2) × (Fin (m - v) → ZMod 2)) := by
  let : Module (ZMod 2) F := AddCommGroup.zmodModule (n := 2) (fun x => by
    rw [two_nsmul]; exact CharTwo.add_self_eq_zero x)
  have h1 : Fintype.card F = Fintype.card (ZMod 2) ^ Module.finrank (ZMod 2) F :=
    Module.card_eq_pow_finrank
  rw [ZMod.card, hF] at h1
  have h2 : Module.finrank (ZMod 2) F = m := (Nat.pow_right_injective (le_refl 2) h1).symm
  have h3 : Module.finrank (ZMod 2) F =
      Module.finrank (ZMod 2) ((Fin v → ZMod 2) × (Fin (m - v) → ZMod 2)) := by
    rw [h2, Module.finrank_prod, Module.finrank_fin_fun, Module.finrank_fin_fun]
    omega
  exact ⟨(LinearEquiv.ofFinrankEq _ _ h3).toAddEquiv⟩

private theorem linearMap_graph_injective {v k : ℕ} :
    Function.Injective fun g : (Fin v → ZMod 2) →ₗ[ZMod 2] (Fin k → ZMod 2) => g.graph := by
  intro g h hgh
  refine LinearMap.ext fun x => ?_
  have hx : (x, g x) ∈ h.graph := by
    rw [← show g.graph = h.graph from hgh]
    exact (LinearMap.mem_graph_iff g (x, g x)).2 rfl
  exact (LinearMap.mem_graph_iff h (x, g x)).1 hx

private theorem card_linearMap_graph {v k : ℕ}
    (g : (Fin v → ZMod 2) →ₗ[ZMod 2] (Fin k → ZMod 2)) :
    Nat.card g.graph = 2 ^ v := by
  rw [LinearMap.graph_eq_range_prod]
  have hinj : Function.Injective (LinearMap.id.prod g) := fun x y h => congrArg Prod.fst h
  rw [← Nat.card_congr (LinearEquiv.ofInjective _ hinj).toEquiv]
  simp [Nat.card_eq_fintype_card, ZMod.card]

/-- A finite field of characteristic `2` with `2 ^ m` elements has at least `2 ^ (v * (m - v))`
additive subgroups of size `2 ^ v`: the graphs of the `𝔽₂`-linear maps `𝔽₂ ^ v → 𝔽₂ ^ (m - v)`. -/
theorem two_pow_le_card_addSubgroup [CharP F 2] {m v : ℕ} (hF : Fintype.card F = 2 ^ m)
    (hv : v ≤ m) : 2 ^ (v * (m - v)) ≤ Nat.card {V : AddSubgroup F // Nat.card V = 2 ^ v} := by
  obtain ⟨e⟩ := nonempty_addEquiv_prod hF hv
  let f : ((Fin v → ZMod 2) →ₗ[ZMod 2] (Fin (m - v) → ZMod 2)) →
      {V : AddSubgroup F // Nat.card V = 2 ^ v} := fun g =>
    ⟨g.graph.toAddSubgroup.map e.symm.toAddMonoidHom, by
      rw [← card_linearMap_graph g]
      exact (Nat.card_congr (AddSubgroup.equivMapOfInjective g.graph.toAddSubgroup
        e.symm.toAddMonoidHom e.symm.injective).toEquiv).symm⟩
  have hf : Function.Injective f := fun g h hgh =>
    linearMap_graph_injective (Submodule.toAddSubgroup_injective
      (AddSubgroup.map_injective e.symm.injective (congrArg Subtype.val hgh)))
  have hcard : Nat.card ((Fin v → ZMod 2) →ₗ[ZMod 2] (Fin (m - v) → ZMod 2)) =
      2 ^ (v * (m - v)) := by
    rw [Nat.card_congr (LinearMap.toMatrix' (R := ZMod 2)).toEquiv]
    simp [Nat.card_eq_fintype_card, Matrix, ZMod.card, ← pow_mul]
  rw [← hcard]
  exact Nat.card_le_card_of_injective f hf

end Counting

end FiniteField

/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.AGM.Basic

/-! # Prime-order group representations with one scalar per basis index -/

namespace AGM.GroupRepresentationTest

variable {G : Type*} [Group G] {p : ℕ} [Fact (Nat.Prime p)] [PrimeOrderWith G p]

local instance : Fact (1 < p) := ⟨(Fact.out : Nat.Prime p).one_lt⟩

/-- The identity representation assigns zero to every coordinate rather than omitting them. -/
def zeroRepresentation {ι : Type*} [Fintype ι] (basis : ι → G) :
    GroupRepresentation (p := p) basis 1 :=
  ⟨fun _ => 0, by simp⟩

example {ι : Type*} [Fintype ι] (basis : ι → G) (i : ι) :
    (zeroRepresentation (p := p) basis).exponents i = 0 := rfl

/-- A singleton basis represents its actual element, including nonidentity elements. -/
def singletonRepresentation (g : G) :
    GroupRepresentation (p := p) (fun _ : Unit => g) g :=
  ⟨fun _ => 1, by simp [ZMod.val_one]⟩

/-- Two coordinates remain present even when the first coefficient is zero. -/
def secondRepresentation (g : G) :
    GroupRepresentation (p := p) (fun i : Fin 2 => if i = 0 then 1 else g) g :=
  ⟨fun i => if i = 0 then 0 else 1, by simp [Fin.prod_univ_two, ZMod.val_one]⟩

example (g : G) (hg : g ≠ 1) :
    ∃ representation : GroupRepresentation (p := p)
        (fun i : Fin 2 => if i = 0 then 1 else g) g,
      representation.exponents 0 = 0 ∧ representation.exponents 1 = 1 ∧ g ≠ 1 :=
  ⟨secondRepresentation (p := p) g,
    by simp [secondRepresentation], by simp [secondRepresentation], hg⟩

example (g : G) : g ^ ((-1 : ZMod p) + 1).val = g ^ (-1 : ZMod p).val * g := by
  simpa [ZMod.val_one] using GroupRepresentation.pow_val_add g (-1) 1

example (g : G) : 0 < p :=
  GroupRepresentation.modulus_pos (singletonRepresentation (p := p) g)

end AGM.GroupRepresentationTest

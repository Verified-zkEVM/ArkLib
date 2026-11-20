/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.OracleReduction.Security.CoordinateWiseSpecialSoundness.Heterogeneous

/-!
# Heterogeneous coordinate-wise special soundness: concrete tests

A challenge with two coordinates, the first over `ZMod 5` and the second over `ZMod 3`, with
parameters `(3, 2)`. A star has `1 + 2 + 1 = 4` members. The tests check a star, a family that is
injective but not a star, the agreement with the homogeneous notion, and the computed tree size
and error bound (`2/5 + 1/3 = 11/15`, below one).
-/

open CoordinateWise ProtocolSpec

namespace CoordinateWiseHeterogeneousTest

/-- The alphabet of coordinate `0` is `ZMod 5`, that of coordinate `1` is `ZMod 3`. -/
def alph : Fin 2 → Type
  | 0 => ZMod 5
  | 1 => ZMod 3

instance : ∀ u, DecidableEq (alph u)
  | 0 => inferInstanceAs (DecidableEq (ZMod 5))
  | 1 => inferInstanceAs (DecidableEq (ZMod 3))

instance : ∀ u, Fintype (alph u)
  | 0 => inferInstanceAs (Fintype (ZMod 5))
  | 1 => inferInstanceAs (Fintype (ZMod 3))

/-- The coordinate vector with the given entries. -/
def vec (a : ZMod 5) (b : ZMod 3) : (u : Fin 2) → alph u
  | 0 => a
  | 1 => b

/-- Parameters `(3, 2)`. -/
def k : Fin 2 → ℕ := ![3, 2]

/-- A star: centre `(0, 0)`, two siblings in coordinate `0` and one in coordinate `1`. -/
def star : Fin 4 → ((u : Fin 2) → alph u) := ![vec 0 0, vec 1 0, vec 2 0, vec 0 1]

example : IsHeteroSpecialSoundFamily k star := by decide

/-- The star is as small as a star can be: `∑ u, (k u - 1) + 1 = 4`. -/
example : ∑ u, (k u - 1) + 1 = 4 := by decide

example : ∑ u, (k u - 1) + 1 ≤ 4 := (show IsHeteroSpecialSoundFamily k star by decide).card_ge

/-- Distinct vectors do not make a star: no two of them differ in one coordinate only. -/
def diagonal : Fin 3 → ((u : Fin 2) → alph u) := ![vec 0 0, vec 1 1, vec 2 2]

example : Function.Injective diagonal ∧ ¬ IsHeteroSpecialSoundFamily ![2, 2] diagonal := by
  decide

/-- A family with a sibling in coordinate `1` but a repeated vector is not a star either. -/
example : ¬ IsHeteroSpecialSoundFamily k ![vec 0 0, vec 1 0, vec 1 0, vec 0 1] := by decide

/-- Over one alphabet and one parameter the notion is `IsSpecialSoundFamily`. -/
example : IsSpecialSoundFamily 2 3
    (![![0, 0], ![1, 0], ![2, 0], ![0, 1], ![0, 2]] : Fin 5 → (Fin 2 → ZMod 5)) :=
  (isSpecialSoundFamily_iff_isHeteroSpecialSoundFamily _).2 (by decide)

/-- A one-round protocol whose challenge is a vector over the alphabets `alph`. -/
abbrev pSpec : ProtocolSpec 1 := ⟨!v[.V_to_P], fun _ => (u : Fin 2) → alph u⟩

instance : Unique pSpec.ChallengeIdx where
  default := ⟨0, rfl⟩
  uniq _ := Subtype.ext (Subsingleton.elim _ _)

/-- The structure with parameters `k`. -/
abbrev D : HeteroCWSSStructure pSpec where
  coordIndex := fun _ => 2
  alphabet := fun _ => alph
  decompose := fun _ => Equiv.refl ((u : Fin 2) → alph u)
  soundnessParam := fun _ => k
  arity := fun _ => 4
  arity_eq := by
    funext i
    decide

example : D.treeSize = 4 := by decide

example : D.toShape.arity = fun _ => 4 := rfl

#eval D.errorBound

example : D.errorBound = 11 / 15 := by
  have h5 : Fintype.card (alph 0) = 5 := by decide
  have h3 : Fintype.card (alph 1) = 3 := by decide
  simp only [HeteroCWSSStructure.errorBound, Fintype.sum_unique, Fin.sum_univ_two]
  simp only [k, h5, h3]
  norm_num

/-- Plain `3`-special soundness of a one-round protocol with a `Bool` challenge, seen as a
heterogeneous structure, has the same shape and the same tree size. -/
abbrev boolSpec : ProtocolSpec 1 := ⟨!v[.V_to_P], !v[Bool]⟩

example (hk : ∀ i : boolSpec.ChallengeIdx, 2 ≤ (fun _ => 3) i) :
    (CWSSStructure.ofSpecialSound (fun _ => 3) hk).toHetero.toShape =
      (CWSSStructure.ofSpecialSound (fun _ => 3) hk).toShape :=
  CWSSStructure.toHetero_toShape _

example (hk : ∀ i : boolSpec.ChallengeIdx, 2 ≤ (fun _ => 3) i) :
    (CWSSStructure.ofSpecialSound (fun _ => 3) hk).toHetero.treeSize = 3 := by
  rw [CWSSStructure.toHetero_treeSize, Fintype.prod_unique]
  rfl

end CoordinateWiseHeterogeneousTest

/--
info: 'CoordinateWise.IsHeteroSpecialSoundFamily.card_ge' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CoordinateWise.IsHeteroSpecialSoundFamily.card_ge

/--
info: 'CoordinateWise.isHeteroSpecialSoundFamily_comp_equiv_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CoordinateWise.isHeteroSpecialSoundFamily_comp_equiv_iff

/--
info: 'CWSSStructure.toHetero_toShape' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CWSSStructure.toHetero_toShape

/--
info: 'CWSSStructure.toHetero_errorBound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CWSSStructure.toHetero_errorBound

/--
info: 'Verifier.treeSpecialSound_toHetero_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Verifier.treeSpecialSound_toHetero_iff

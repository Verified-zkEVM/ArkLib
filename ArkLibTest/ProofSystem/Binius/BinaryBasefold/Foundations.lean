/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Quang Dao
-/
import ArkLib.ProofSystem.Binius.BinaryBasefold.Relations
import Mathlib.Data.ZMod.Basic

/-! # Minimal assumptions and zero-step folding interfaces -/

open Binius.BinaryBasefold AdditiveNTT

-- Characteristic transport does not require a finite or integral-domain target.
example : CharP (Polynomial (ZMod 2)) 2 := by
  let : Fact (Fintype.card (ZMod 2) = 2) := ⟨by simp⟩
  exact charP_two_of_card_eq_two (ZMod 2) (Polynomial (ZMod 2))

-- The characteristic transport only asks for the semiring algebra interface.
example (A : Type*) [Semiring A] [Nontrivial A] [Algebra (ZMod 2) A] : CharP A 2 := by
  let : Fact (Fintype.card (ZMod 2) = 2) := ⟨by simp⟩
  exact charP_two_of_card_eq_two (ZMod 2) A

-- The matrix constructors themselves are defined over rings with zero divisors.
example : butterflyMatrix (L := ZMod 4) 0 0 1 = !![1, 0; -1, 1] := by
  simp [butterflyMatrix_zero_apply]

section Closeness

variable {r : ℕ} [NeZero r]
variable {L : Type} [Field L] [Fintype L] [DecidableEq L]
variable (K : Type) [Field K] [Fintype K] [DecidableEq K]
  [Fact (Nat.Prime (ringChar K))] [Fact (Fintype.card K = 2)] [Algebra K L]
variable (β : Fin r → L) [Fact (LinearIndependent K β)] [Fact (β 0 = 1)]
variable {ℓ R : ℕ} [NeZero R] {hrate : ℓ + R < r}

-- No proof that i ≤ ℓ is needed to state code closeness.
example (i : Fin r) (f : OracleFunction K β (h_ℓ_add_R_rate := hrate) i) :
    UniqueDecodingClose K β (h_ℓ_add_R_rate := hrate) i f ↔
      2 * Code.distFromCode f (code K β (h_ℓ_add_R_rate := hrate) i) <
        codeDistance K β (h_ℓ_add_R_rate := hrate) i := Iff.rfl

-- Positive distance also holds at rate zero and without an active-round bound.
omit [NeZero R] in
example (i : Fin r) :
    0 < codeDistance K β (h_ℓ_add_R_rate := hrate) i :=
  codeDistance_pos K β i

-- Zero steps need no contradictory NeZero 0 instance.
example (i : Fin r) (hi : i ≤ ℓ)
    (f : OracleFunction K β (h_ℓ_add_R_rate := hrate) i) :
    FiberwiseClose K β (h_ℓ_add_R_rate := hrate) i 0 (by simp) hi f ↔
      UniqueDecodingClose K β (h_ℓ_add_R_rate := hrate) i f := by
  exact fiberwiseClose_steps_zero_iff_uniqueDecodingClose K β i i (by simp) hi f

end Closeness

/--
info: 'Binius.BinaryBasefold.uniqueDecodingCodeword_spec' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms uniqueDecodingCodeword_spec

/--
info: 'Binius.BinaryBasefold.uniqueDecodingCodeword_eq_of_extractMlp_eq_some' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms uniqueDecodingCodeword_eq_of_extractMlp_eq_some

/--
info: 'Binius.BinaryBasefold.foldingBadEventAtBlock_iff_incrementalBadEvent_last' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms foldingBadEventAtBlock_iff_incrementalBadEvent_last

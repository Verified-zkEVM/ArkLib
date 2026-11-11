/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.ProofSystem.Sumcheck.Message.Basic
public import ArkLib.ProofSystem.Sumcheck.Impl.Representation

/-!
# Computable coefficient-array messages

The runtime operations use Horner evaluation and a finite domain sum. The model reuses the
representation layer's degree-preserving `toPoly` interpretation and evaluation theorem.
-/

@[expose] public section

namespace Sumcheck

variable {R : Type} [CommRing R] {d : ℕ}

/-- Executable operations for bounded CompPoly coefficient arrays. -/
def compOps [DecidableEq R] (D : Finset R) :
    MessageOps R (Impl.Representation.Message R d) :=
  plainOps D (Impl.Representation.evaluate R d)

/-- Proof-only meaning of the executable coefficient-array operations. -/
noncomputable def compModel [DecidableEq R] [BEq R] [LawfulBEq R] (D : Finset R) :
    MessageModel D (compOps (d := d) D) d where
  interpret _ := Impl.Representation.toMessage R d
  evaluate_eq _ := Impl.Representation.evaluate_eq R d
  accept_iff _ _ := by
    simp [compOps, plainOps, Impl.Representation.evaluate_eq]

end Sumcheck

/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tobias Rothmann
-/
import ArkLib.Commitments.Ordinary.Ajtai.Simple.Scheme

/-!
# Correctness of the Simple Ajtai Commitment

An honest commitment to a message accepted by `isShort` always verifies. The shortness
side condition is intrinsic to the scheme's `verify`, so unconditional `PerfectlyCorrect`
does not hold once `isShort` rejects some messages.
-/

open OracleComp CommitmentScheme CompPoly ArkLib.Lattices ArkLib.Lattices.CyclotomicModulus

namespace ArkLib.Lattices.Ajtai.Simple

variable {R : Type} [Field R] [BEq R] [LawfulBEq R] (Φ : CyclotomicModulus R) [IsCyclotomic Φ]

@[simp] theorem verify_commit {rows cols : Nat} [DecidableEq (Commitment Φ rows)]
    (A : PublicParams Φ rows cols) (s : Message Φ cols) :
    verify Φ A s (commit Φ A s) () = true := by simp [verify]

@[simp] theorem verify_eq_true_iff {rows cols : Nat} [DecidableEq (Commitment Φ rows)]
    (A : PublicParams Φ rows cols) (s : Message Φ cols)
    (c : Commitment Φ rows) (opening : Opening) :
    verify Φ A s c opening = true ↔ commit Φ A s = c := by simp [verify]

/-- Simple Ajtai commitments are correct on short messages: an honest commitment to a
message accepted by `isShort` always verifies. -/
theorem perfectlyCorrect (rows cols : Nat) (isShort : Message Φ cols → Bool)
    [SampleableType (PublicParams Φ rows cols)] [DecidableEq (Commitment Φ rows)]
    (A : PublicParams Φ rows cols) (s : Message Φ cols) (hs : isShort s = true)
    (cd : Commitment Φ rows × Opening)
    (hmem : cd ∈ support ((commitmentScheme Φ rows cols isShort).commit A s)) :
    (commitmentScheme Φ rows cols isShort).verify A s cd.1 cd.2 = true := by
  simp only [commitmentScheme, support_pure, Set.mem_singleton_iff] at hmem
  rcases hmem with rfl
  change (isShort s && verify Φ A s (commit Φ A s) ()) = true
  simp [hs]

end ArkLib.Lattices.Ajtai.Simple

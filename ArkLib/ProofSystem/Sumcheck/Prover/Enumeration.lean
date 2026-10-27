/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.ProofSystem.Sumcheck.Prover.Basic
public import ArkLib.ProofSystem.Sumcheck.Message.CompPoly
public import ArkLib.ProofSystem.Sumcheck.Impl.Projection

/-!
# Enumeration prover adapter

The state retains the original computational polynomial and its challenge prefix. Message
construction reuses the existing finite enumeration prover; folding appends a challenge.
The correspondence theorems expose its existing mathematical meaning through the new contracts.
-/

@[expose] public section

namespace Sumcheck

variable {R : Type} [CommRing R] {d : ℕ}

/-- Original computational polynomial and the prefix fixed before the remaining rounds. -/
structure EnumerationState (R : Type) [CommRing R] (N d remaining : ℕ) where
  start : ℕ
  finish : start + remaining = N
  poly : CPoly.CMvPolynomial N R
  degree : ∀ j, poly.degreeOf j ≤ d
  challenges : Fin start → R

/-- Construct each message by enumerating all suffixes, then extend the challenge prefix. -/
def enumerationOps [BEq R] [LawfulBEq R] [Nontrivial R] {N m : ℕ}
    (D : Fin m ↪ R) : ProverOps R (Impl.Representation.Message R d)
      (EnumerationState R N d) where
  message s := Impl.Computable.projectedMessage D
    ⟨s.start, by have := s.finish; omega⟩ s.challenges s.poly s.degree
  fold s r := ⟨s.start + 1, by have := s.finish; omega,
    s.poly, s.degree, Fin.snoc s.challenges r⟩

variable [DecidableEq R] [BEq R] [LawfulBEq R] [Nontrivial R] {N m n : ℕ}

/-- The enumeration message decodes to the existing projected round polynomial. -/
theorem enumeration_message_interpret (D : Fin m ↪ R)
    (s : EnumerationState R N d (n + 1)) (c : R) :
    (compModel (d := d) (Finset.univ.map D)).interpret c ((enumerationOps D).message s) =
      Spec.SingleRound.projectedRoundPolynomial R N d D
        ⟨s.start, by have := s.finish; omega⟩ s.challenges
        (Impl.Computable.toOracleStatement s.poly s.degree) := by
  exact Impl.Computable.projectedMessage_toMessage D
    ⟨s.start, by have := s.finish; omega⟩ s.challenges s.poly s.degree

/-- Runtime evaluation of an enumeration message agrees with the existing round semantics. -/
theorem enumeration_message_evaluate (D : Fin m ↪ R)
    (s : EnumerationState R N d (n + 1)) (c r : R) :
    (compOps (d := d) (Finset.univ.map D)).evaluate c ((enumerationOps D).message s) r =
      (Spec.SingleRound.projectedRoundPolynomial R N d D
        ⟨s.start, by have := s.finish; omega⟩ s.challenges
        (Impl.Computable.toOracleStatement s.poly s.degree)).val.eval r := by
  exact Impl.Computable.projectedMessage_evaluate D
    ⟨s.start, by have := s.finish; omega⟩ s.challenges s.poly s.degree r

end Sumcheck

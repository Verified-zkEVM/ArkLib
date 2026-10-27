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

namespace EnumerationState

open MvPolynomial

/-- The original polynomial with the challenge prefix fixed, in the remaining variables. -/
noncomputable def polynomial (s : EnumerationState R N d n) : R⦃≤ d⦄[X Fin n] :=
  (by have := s.finish; omega : N - s.start = n) ▸
    MvPolynomial.fixPrefix N ⟨s.start, by have := s.finish; omega⟩
      (Impl.Computable.toOracleStatement s.poly s.degree) s.challenges

omit [DecidableEq R] [BEq R] [LawfulBEq R] [Nontrivial R] in
/-- Residual evaluation appends the remaining point to the fixed challenge prefix. -/
theorem polynomial_eval (s : EnumerationState R N d n) (x : Fin n → R) :
    (s.polynomial).val.eval x =
      (Impl.Computable.toOracleStatement s.poly s.degree).val.eval
        (Fin.append s.challenges x ∘ Fin.cast s.finish.symm) := by
  rcases s with ⟨k, h, p, hd, c⟩
  have hn : N - k = n := by omega
  subst n
  simpa only [polynomial, MvPolynomial.fixPrefix] using
    MvPolynomial.eval_fixFirstVariablesOfMQP_append
      (⟨k, by omega⟩ : Fin (N + 1))
      (Impl.Computable.toOracleStatement p hd).val c x

omit [DecidableEq R] in
/-- Appending a challenge fixes the first remaining coordinate. -/
theorem polynomial_fold_eval (D : Fin m ↪ R)
    (s : EnumerationState R N d (n + 1)) (r : R) (x : Fin n → R) :
    (((enumerationOps D).fold s r).polynomial).val.eval x =
      s.polynomial.val.eval (Fin.cons r x) := by
  rw [polynomial_eval, polynomial_eval]
  dsimp [enumerationOps]
  congr 2
  rw [Fin.append_left_snoc]
  funext j
  apply congrArg (Fin.append s.challenges (Fin.cons r x))
  exact Fin.ext rfl

end EnumerationState

/-- An enumeration message evaluates to the cube sum after extending the challenge prefix. -/
theorem enumeration_message_sum (D : Fin m ↪ R)
    (s : EnumerationState R N d (n + 1)) (c r : R) :
    (compOps (d := d) (Finset.univ.map D)).evaluate c ((enumerationOps D).message s) r =
      ∑ x ∈ Fintype.piFinset (fun _ : Fin n => Finset.univ.map D),
        (((enumerationOps D).fold s r).polynomial).val.eval x := by
  rw [enumeration_message_evaluate]
  simp only [Spec.SingleRound.projectedRoundPolynomial, Polynomial.eval_finsetSum]
  rcases s with ⟨k, h, p, hd, cs⟩
  cases N with
  | zero => omega
  | succ N =>
    simp only [Spec.SingleRound.roundSuffix]
    simp_rw [MvPolynomial.eval_evalExcept_append]
    have hn : n = N - k := by omega
    subst n
    apply Finset.sum_congr rfl
    intro x _
    rw [EnumerationState.polynomial_eval]
    rfl

/-- The enumeration prover models the original polynomial with its challenge prefix fixed;
its claim sums the residual polynomial over the remaining product of the domain. -/
noncomputable def enumerationModel (D : Fin m ↪ R) :
    ProverModel (compOps (d := d) (Finset.univ.map D)) (EnumerationState R N d)
      (enumerationOps D) (fun n ↦ Fintype.piFinset fun _ : Fin n ↦ Finset.univ.map D) d where
  polynomial := EnumerationState.polynomial
  claim s := ∑ x ∈ Fintype.piFinset (fun _ => Finset.univ.map D), s.polynomial.val.eval x
  claim_eq _ := rfl
  fold_eq := EnumerationState.polynomial_fold_eval D
  message_eq s r := enumeration_message_sum D s _ r
  message_accept s := by
    apply ((compModel (d := d) (Finset.univ.map D)).accept_iff _ _).mpr
    simp_rw [← (compModel (d := d) (Finset.univ.map D)).evaluate_eq,
      enumeration_message_sum, EnumerationState.polynomial_fold_eval]
    exact (Fin.sum_piFinset_cons (fun _ => Finset.univ.map D)
      (fun x => s.polynomial.val.eval x)).symm

/-- An honest enumeration step accepts and returns the folded residual cube sum. -/
theorem enumeration_honest_step (D : Fin m ↪ R)
    (s : EnumerationState R N d (n + 1)) (r : R) :
    step (compOps (d := d) (Finset.univ.map D)) ((enumerationModel D).claim s)
      ((enumerationOps D).message s) r =
      some ((enumerationModel D).claim ((enumerationOps D).fold s r)) :=
  honest_step _ _ _ _ (enumerationModel D) s r

end Sumcheck

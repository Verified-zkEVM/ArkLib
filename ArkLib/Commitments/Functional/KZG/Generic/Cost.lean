/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Commitments.Functional.KZG.Generic.Program

/-!
# Operation budget for generic KZG recovery

The reduction uses at most `q + n + 1` group operations: the adversary's `q` operations and
at most `n + 1` candidate scalings. Scalar root finding, metadata, and equality tests are free.

References: [KZG10TR]; Shoup, EUROCRYPT 1997; Maurer, IMA 2005;
Fuchsbauer–Kiltz–Loss, *The Algebraic Group Model and its Applications*, CRYPTO 2018.
-/

@[expose] public section

open CompPoly OracleComp OracleSpec GroupModel GroupModel.Interaction

namespace KZG.Generic

attribute [local implicit_reducible] spec handleSpec isGroupOp

variable {F D : Type} [Field F] [DecidableEq F]

omit [DecidableEq F] in
/-- Each root test uses one scaling and a free equality query. -/
theorem isQueryBoundP_testRoots (rs : List F) :
    IsQueryBoundP (testRoots rs) (fun i => isGroupOp i = true) rs.length := by
  induction rs with
  | nil => simp [testRoots]
  | cons r rs ih =>
      simp only [testRoots]
      simp only [isGroupOp, Sum.elim_inl, GroupModel.Query.isOp_smul,
        GroupModel.Query.isOp_eq, Bool.false_eq_true, ↓reduceIte, not_false_eq_true,
        true_or, add_apply_inl, List.length_cons, isQueryBoundP_query_bind_iff,
        lt_add_iff_pos_left, Order.lt_add_one_iff, zero_le, or_true,
        add_tsub_cancel_right, true_and]
      intro h ok
      split
      · simp
      · exact ih

/-- Forwarding the handle program adds only the final bounded candidate search. -/
theorem isQueryBoundP_reductionProgram (n : ℕ) (roots : CPolynomial F → List F)
    (claims : D → List (F × F))
    (p : OracleComp (adversarySpec F) (Message D (fun _ : PSort => Handle))) (q : ℕ)
    (hq : IsQueryBoundP p (fun i => isGroupOp i = true) q)
    (st : Pairing.Tracked F (fun _ : Bool => F) F) :
    IsQueryBoundP (reductionProgram n roots claims p st)
      (fun i => isGroupOp i = true) (q + (n + 1)) := by
  induction p using OracleComp.inductionOn generalizing q st with
  | pure msg =>
      exact (isQueryBoundP_testRoots _).mono
        ((AGM.length_candidatesFirstData_le roots _ _).trans (by omega))
  | query_bind t next ih =>
      rcases t with t | t | k | t
      · change IsQueryBoundP (do
          let a ← (liftM ((genSpec F pairingSig).query (.inl t)) :
            OracleComp (genSpec F pairingSig) _)
          reductionProgram n roots claims (next a) (Pairing.step 0 t st).2) _ _
        simp only [isQueryBoundP_query_bind_iff] at hq ⊢
        cases ht : t.isOp <;>
          simp only [isGroupOp, Sum.elim_inl, ht, Bool.false_eq_true,
            ↓reduceIte, not_false_eq_true, true_or, not_true_eq_false, false_or,
            add_pos_iff, Order.lt_add_one_iff, zero_le, or_true, add_apply_inl,
            Nat.add_succ_sub_one, true_and] at hq ⊢
        · exact fun a => ih a q (hq a) _
        · intro a
          exact (ih a (q - 1) (hq.2 a) _).mono (by omega)
      · change IsQueryBoundP (reductionProgram n roots claims (next ()) st) _ _
        simp only [isQueryBoundP_query_bind_iff, isGroupOp, Sum.elim_inr,
          Bool.false_eq_true, not_false_eq_true, true_or, ↓reduceIte, true_and] at hq
        exact ih () q (hq ()) st
      · change IsQueryBoundP (do
          let a ← (liftM ((genSpec F pairingSig).query (.inr k)) :
            OracleComp (genSpec F pairingSig) _)
          reductionProgram n roots claims (next a) st) _ _
        simp only [isQueryBoundP_query_bind_iff, isGroupOp, Sum.elim_inr,
          Bool.false_eq_true, not_false_eq_true, true_or, ↓reduceIte, true_and] at hq ⊢
        exact fun a => ih a q (hq a) st
      · exact t.data.elim

/-- The complete recovery program costs at most `q + n + 1`, independently of claim count. -/
theorem isQueryBoundP_program (n : ℕ) (roots : CPolynomial F → List F)
    (claims : D → List (F × F)) (A : Adversary F D) (q : ℕ)
    (hq : IsQueryBoundP (A (input n)) (fun i => isGroupOp i = true) q) :
    IsQueryBoundP (program n roots claims A) (fun i => isGroupOp i = true) (q + n + 1) := by
  simpa only [program, Nat.add_assoc] using
    isQueryBoundP_reductionProgram n roots claims (A (input n)) q hq (initialMetadata n)

end KZG.Generic

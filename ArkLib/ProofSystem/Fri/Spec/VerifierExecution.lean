/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

public import ArkLib.ProofSystem.Fri.Spec.FoldExecution
public import ArkLib.ProofSystem.Fri.Spec.AdaptiveSoundness

/-!
# The composed FRI verifier and its transcript history

This module identifies the history retained by the composed verifier with the history
read from the chronological transcript in the bad-event argument.
-/

@[expose] public section

namespace Fri.Spec

open Domain OracleComp OracleSpec ProtocolSpec Finset

variable {F : Type} [NonBinaryField F] [Fintype F] [DecidableEq F]
variable {n k : ℕ} {ω : SmoothCosetFftDomain n F}
variable (s : Fin (k + 1) → ℕ+) (l : ℕ)

/-- The fixed transcript immediately before the query vector is sampled. -/
def queryPrefix (tr : (pSpec k (ω := ω) s l).FullTranscript) :
    (pSpec k (ω := ω) s l).Transcript (queryChallenge (ω := ω) s l).val.castSucc :=
  Transcript.restrict (b := Fin.last _) (by
    simp only [Fin.val_castSucc, Fin.val_last]; omega) tr

omit [Fintype F] in
private theorem component_full_heq (tr : (pSpec k (ω := ω) s l).FullTranscript)
    (i : Fin k) (j : Fin 2) :
    HEq (FullTranscript.component tr.fst.fst i j)
      (tr (Fin.castAdd 1 (Fin.castAdd 2 (Fin.embedSum i j)))) :=
  (FullTranscript.component_apply_heq tr.fst.fst i j).trans
    ((FullTranscript.fst_apply_heq tr.fst _).trans (FullTranscript.fst_apply_heq tr _))

omit [Fintype F] in
/-- The final polynomial read at the query boundary is the transmitted polynomial. -/
theorem readFinalPolynomial_queryPrefix (tr : (pSpec k (ω := ω) s l).FullTranscript) :
    readFinalPolynomial s l (queryPrefix s l tr) (by simp) = tr.fst.snd 1 := by
  apply eq_of_heq
  unfold readFinalPolynomial
  refine (cast_heq _ _).trans ?_
  exact ((FullTranscript.snd_apply_heq tr.fst (1 : Fin 2)).trans
    (FullTranscript.fst_apply_heq tr _)).symm

omit [Fintype F] in
/-- The non-final challenge read from the prefix is the challenge used by its verifier. -/
theorem readFoldChallenge_queryPrefix_castSucc
    (tr : (pSpec k (ω := ω) s l).FullTranscript) (i : Fin k) :
    readFoldChallenge s l (queryPrefix s l tr) i.castSucc
      (by simp only [Fin.val_castSucc, queryChallenge_val]; omega) =
        foldChallenges s tr.fst.fst i := by
  apply eq_of_heq
  unfold readFoldChallenge
  refine (cast_heq _ _).trans ?_
  have hi : foldChallenge (ω := ω) s l i.castSucc = nonfinalChallenge s l i :=
    dite_eq_left i.isLt
  exact (congr_arg_heq tr (congrArg Subtype.val hi)).trans
    (component_full_heq s l tr i 0).symm

omit [Fintype F] in
/-- The final folding challenge read from the prefix is the one used by the final verifier. -/
theorem readFoldChallenge_queryPrefix_last
    (tr : (pSpec k (ω := ω) s l).FullTranscript) :
    readFoldChallenge s l (queryPrefix s l tr) (Fin.last k)
      (by simp only [Fin.val_last, Fin.val_castSucc, queryChallenge_val]; omega) =
        tr.fst.snd 0 := by
  apply eq_of_heq
  unfold readFoldChallenge
  refine (cast_heq _ _).trans ?_
  have hi : foldChallenge (ω := ω) s l (Fin.last k) = finalChallenge s l :=
    dite_eq_right (Nat.lt_irrefl k)
  exact (congr_arg_heq tr (congrArg Subtype.val hi)).trans
    ((FullTranscript.snd_apply_heq tr.fst (0 : Fin 2)).trans
      (FullTranscript.fst_apply_heq tr _)).symm

omit [Fintype F] in
/-- The challenge vectors from chronological reading and verifier composition coincide. -/
theorem queryFoldChallenges_eq (tr : (pSpec k (ω := ω) s l).FullTranscript) :
    queryFoldChallenges s l (queryPrefix s l tr) = foldPhaseChallenges s tr.fst := by
  funext i
  refine Fin.lastCases ?_ (fun i ↦ ?_) i
  · change _ = Fin.append _ _ (Fin.natAdd k (0 : Fin 1))
    rw [Fin.append_right]
    exact readFoldChallenge_queryPrefix_last s l tr
  · change _ = Fin.append _ _ (Fin.castAdd 1 i)
    rw [Fin.append_left]
    exact readFoldChallenge_queryPrefix_castSucc s l tr i

/-- Word chronology agrees with the arbitrary words retained by the folding verifiers. -/
theorem readWord_queryPrefix
    (stmt : Statement F (0 : Fin (k + 1)) × ∀ j, OracleStatement s ω 0 j)
    (tr : (pSpec k (ω := ω) s l).FullTranscript) (i : Fin (k + 1)) :
    readWord s l (initialOracle s stmt) (queryPrefix s l tr) i
      (by simp only [Fin.val_castSucc, queryChallenge_val]; omega) =
        foldWords s (stmt.2 0) tr.fst.fst i := by
  refine Fin.cases ?_ (fun j ↦ ?_) i
  · apply eq_of_heq
    unfold readWord
    simp only [Fin.val_zero, ↓reduceDIte]
    exact (cast_heq _ _).trans (cast_heq _ _)
  · apply eq_of_heq
    unfold readWord
    simp only [Fin.val_succ, Nat.add_one_ne_zero, ↓reduceDIte]
    exact (cast_heq _ _).trans ((cast_heq _ _).trans
      (component_full_heq s l tr j 1).symm)

/-- The query phase sees exactly the same retained commitments as the bad-event proof. -/
theorem queryHistory_eq (d : ℕ+)
    (stmt : Statement F (0 : Fin (k + 1)) × ∀ j, OracleStatement s ω 0 j)
    (tr : (pSpec k (ω := ω) s l).FullTranscript) :
    queryHistory s l (initialOracle s stmt) (queryPrefix s l tr) =
      foldPhaseHistory s d stmt tr.fst := by
  apply oracleHistory_ext s
  · intro i
    rw [committedWord_queryHistory, readWord_queryPrefix]
    exact (FinalFoldPhase.committedWord_materialize s d _ _ i).symm
  · rw [finalPolynomial_queryHistory, readFinalPolynomial_queryPrefix]
    exact (FinalFoldPhase.finalPolynomial_materialize s d _ _).symm

omit [Fintype F] in
/-- The last transcript entry is exactly the vector consumed by the query verifier. -/
theorem queryVector_eq (tr : (pSpec k (ω := ω) s l).FullTranscript) :
    cast (queryChallenge_type (ω := ω) s l) (tr (queryChallenge s l).val) = tr.snd 0 := by
  apply eq_of_heq
  exact (cast_heq _ _).trans (FullTranscript.snd_apply_heq tr (0 : Fin 1)).symm

/-- The terminal bad event describes precisely the degree guard and query checks on the
history retained by verifier composition. -/
theorem queryBad_full_iff (d : ℕ+) (hs : (∑ j, (s j).val) ≤ n)
    (stmt : Statement F (0 : Fin (k + 1)) × ∀ j, OracleStatement s ω 0 j)
    (tr : (pSpec k (ω := ω) s l).FullTranscript) :
    queryBad s d l hs (initialOracle s stmt)
      (Transcript.restrict (b := Fin.last _)
        (by simp only [Fin.val_succ, Fin.val_last]; omega) tr) ↔
      (tr.fst.snd 1).natDegree < d.val ∧ ∀ j i,
        (simulateQ (OracleInterface.simOracle0 (FinalOracleStatement s ω)
          (foldPhaseHistory s d stmt tr.fst))
          (QueryRound.checkRound s hs (tr.fst.snd 1) (foldPhaseChallenges s tr.fst i)
            i (tr.snd 0 j))).run = true := by
  classical
  unfold queryBad
  change (finalPolynomial s
      (queryHistory s l (initialOracle s stmt) (queryPrefix s l tr))).natDegree < d.val ∧
    (simulateQ (OracleInterface.simOracle0 (FinalOracleStatement s ω)
      (queryHistory s l (initialOracle s stmt) (queryPrefix s l tr)))
      (QueryRound.verifyQueries s hs l (queryFoldChallenges s l (queryPrefix s l tr))
        (cast (queryChallenge_type (ω := ω) s l) (tr (queryChallenge s l).val))).run).run ≠
        none ↔ _
  rw [queryHistory_eq s l d, queryFoldChallenges_eq, queryVector_eq,
    QueryRound.eval_verifyQueries]
  have hp : finalPolynomial s (foldPhaseHistory s d stmt tr.fst) = tr.fst.snd 1 :=
    FinalFoldPhase.finalPolynomial_materialize s d _ _
  rw [hp]
  simp

open Classical in
set_option backward.isDefEq.respectTransparency false in
/-- Exact rejection semantics of the existing complete FRI reduction. -/
theorem reduction_run (d : ℕ+)
    (hdom : 2 ^ (∑ j, (s j).val) * d.val ≤ 2 ^ n)
    (stmt : Statement F (0 : Fin (k + 1)) × ∀ j, OracleStatement s ω 0 j)
    (tr : (pSpec k (ω := ω) s l).FullTranscript) :
    ((reduction k s d hdom l).verifier.toVerifier.run stmt tr).run =
      pure (if queryBad s d l (round_bound hdom) (initialOracle s stmt)
        (Transcript.restrict (b := Fin.last _)
          (by simp only [Fin.val_succ, Fin.val_last]; omega) tr) then
        some (foldPhaseChallenges s tr.fst, foldPhaseHistory s d stmt tr.fst) else none) := by
  classical
  change ((OracleVerifier.append (reductionFold k s d).verifier
    (QueryRound.queryVerifier s (round_bound hdom) l)).toVerifier.run stmt tr).run = _
  rw [OracleVerifier.append_toVerifier, Verifier.append_run]
  simp only [OptionT.run_bind, Option.elimM, reductionFold_run, pure_bind]
  by_cases hd : (tr.fst.snd 1).natDegree < d.val
  · simp only [hd, ↓reduceIte, Option.elim_some]
    rw [QueryRound.queryVerifier_toVerifier_verify]
    have hp : finalPolynomial s (foldPhaseHistory s d stmt tr.fst) = tr.fst.snd 1 :=
      FinalFoldPhase.finalPolynomial_materialize s d _ _
    simp only [hp, queryBad_full_iff, hd, true_and]
  · simp only [hd, ↓reduceIte, Option.elim_none, queryBad_full_iff, false_and]

end Fri.Spec

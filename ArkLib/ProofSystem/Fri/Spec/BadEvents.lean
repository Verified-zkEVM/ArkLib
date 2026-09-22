/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

module

public import ArkLib.ProofSystem.Fri.Spec.RoundSoundness

/-!
# The last bad event in FRI

Once all folding challenges are safe, an accepting query vector is the only remaining bad
event. The final polynomial degree check is included, just as in the composed verifier.
-/

@[expose] public section

namespace Fri.Spec

open Domain OracleComp OracleSpec ProtocolSpec ReedSolomon Finset
open scoped ProbabilityTheory NNReal

variable {F : Type} [NonBinaryField F] [Fintype F] [DecidableEq F]
variable {n k : ℕ} {ω : SmoothCosetFftDomain n F}
variable (s : Fin (k + 1) → ℕ+) (d : ℕ+) (l : ℕ)

/-- Acceptance after the final query challenge, including the final degree check. -/
def queryBad (hs : (∑ j, (s j).val) ≤ n) (f : (ω.subdomain 0).toFinset → F)
    (tr : (pSpec k (ω := ω) s l).Transcript (queryChallenge (ω := ω) s l).val.succ) : Prop :=
  let pretr := tr.restrict (by simp only [Fin.val_castSucc, Fin.val_succ]; omega)
  let o := queryHistory s l f pretr
  let α := queryFoldChallenges s l pretr
  let xs := cast (queryChallenge_type (ω := ω) s l)
    (tr.read (queryChallenge s l).val (by simp))
  (finalPolynomial s o).natDegree < d.val ∧
    (simulateQ (OracleInterface.simOracle0 (FinalOracleStatement s ω) o)
      (QueryRound.verifyQueries s hs l α xs).run).run ≠ none

/-- The commitment history is fixed when the query vector is appended. -/
theorem queryBad_concat_iff (hs : (∑ j, (s j).val) ≤ n)
    (f : (ω.subdomain 0).toFinset → F)
    (tr : (pSpec k (ω := ω) s l).Transcript (queryChallenge (ω := ω) s l).val.castSucc)
    (xs : (pSpec k (ω := ω) s l).Challenge (queryChallenge s l)) :
    queryBad s d l hs f (tr.concat xs) ↔
      (finalPolynomial s (queryHistory s l f tr)).natDegree < d.val ∧
      (simulateQ (OracleInterface.simOracle0 (FinalOracleStatement s ω) (queryHistory s l f tr))
        (QueryRound.verifyQueries s hs l (queryFoldChallenges s l tr)
          (cast (queryChallenge_type (ω := ω) s l) xs)).run).run ≠ none := by
  unfold queryBad
  simp only [Transcript.restrict_concat
    (a := (queryChallenge (ω := ω) s l).val.castSucc) (b := (queryChallenge s l).val)
    le_rfl, Transcript.restrict_refl,
    Transcript.read_concat_last]

/-- Conditional on the preceding folding challenges being safe, the final bad event has
the query error from the updated analysis. -/
theorem queryBad_prob_le (hs : (∑ j, (s j).val) ≤ n)
    (f : (ω.subdomain 0).toFinset → F) (θ δ : ℝ)
    [SampleableType ((pSpec k (ω := ω) s l).Challenge (queryChallenge s l))]
    (tr : (pSpec k (ω := ω) s l).Transcript (queryChallenge (ω := ω) s l).val.castSucc)
    (hsafe : ∀ i : Fin (k + 1), ¬ foldingBad s d l f θ i
      (tr.restrict (by simp only [Fin.val_succ, Fin.val_castSucc,
        foldChallenge_val, queryChallenge_val]; omega)))
    (hdist : ∀ u ∈ code ω (2 ^ (∑ j, (s j).val) * d.val),
      δ ≤ (Code.relHammingDist (fun z ↦ f (initialQuery z)) u : ℝ)) :
    Pr{let xs ← $ᵗ ((pSpec k (ω := ω) s l).Challenge (queryChallenge s l))}[
      queryBad s d l hs f (tr.concat xs)] ≤
      ENNReal.ofReal (1 - min θ δ) ^ l := by
  classical
  simp only [queryBad_concat_iff]
  by_cases hd : (finalPolynomial s (queryHistory s l f tr)).natDegree < d.val
  · simp only [hd, true_and]
    refine (SampleableType.prEvent_uniformSample_equiv
      (Equiv.cast (queryChallenge_type (ω := ω) s l))
      (fun xs ↦ (simulateQ
        (OracleInterface.simOracle0 (FinalOracleStatement s ω) (queryHistory s l f tr))
        (QueryRound.verifyQueries s hs l (queryFoldChallenges s l tr) xs).run).run ≠ none)
      ).le.trans ?_
    apply QueryRound.verifyQueries_soundness s d hs _ _ θ δ
      (safeHistory_queryHistory s d l f θ tr hsafe) hd
    simpa only [show initialWord s (queryHistory s l f tr) = (fun z ↦ f (initialQuery z)) from
      funext (initialWord_queryHistory s l f tr)] using hdist
  · simp only [hd, false_and]
    simp

/-- Bad events indexed by challenges of the existing composed protocol. The equalities
only transport prefixes; no alternative protocol or extra randomness is introduced. -/
def badEvent (hs : (∑ j, (s j).val) ≤ n) (θ : ℝ)
    (j : (pSpec k (ω := ω) s l).ChallengeIdx) (f : (ω.subdomain 0).toFinset → F)
    (tr : (pSpec k (ω := ω) s l).Transcript j.val.succ) : Prop :=
  (∃ i, ∃ h : j = foldChallenge s l i, foldingBad s d l f θ i (h ▸ tr)) ∨
    ∃ h : j = queryChallenge s l, queryBad s d l hs f (h ▸ tr)

@[simp]
theorem badEvent_fold (hs : (∑ j, (s j).val) ≤ n) (θ : ℝ)
    (i : Fin (k + 1)) (f : (ω.subdomain 0).toFinset → F)
    (tr : (pSpec k (ω := ω) s l).Transcript (foldChallenge (ω := ω) s l i).val.succ) :
    badEvent s d l hs θ (foldChallenge s l i) f tr ↔ foldingBad s d l f θ i tr := by
  constructor
  · rintro (⟨j, h, hb⟩ | ⟨h, _⟩)
    · have hij := foldChallenge_injective s l h
      subst j
      exact hb
    · exact (foldChallenge_ne_query s l i h).elim
  · intro hb
    exact Or.inl ⟨i, rfl, hb⟩

@[simp]
theorem badEvent_query (hs : (∑ j, (s j).val) ≤ n) (θ : ℝ)
    (f : (ω.subdomain 0).toFinset → F)
    (tr : (pSpec k (ω := ω) s l).Transcript (queryChallenge (ω := ω) s l).val.succ) :
    badEvent s d l hs θ (queryChallenge s l) f tr ↔ queryBad s d l hs f tr := by
  constructor
  · rintro (⟨i, h, _⟩ | ⟨h, hb⟩)
    · exact (foldChallenge_ne_query s l i h.symm).elim
    · exact hb
  · intro hb
    exact Or.inr ⟨rfl, hb⟩

/-- Each folding challenge contributes its MCA error; the last challenge contributes
the independent-query error from the updated analysis. -/
noncomputable def challengeError [SampleableType F] (θ δ : ℝ)
    (j : (pSpec k (ω := ω) s l).ChallengeIdx) : ℝ≥0 :=
  (∑ i, if j = foldChallenge s l i then foldingError (ω := ω) s d θ i else 0) +
    if j = queryChallenge s l then Real.toNNReal (1 - min θ δ) ^ l else 0

@[simp]
theorem challengeError_fold [SampleableType F] (θ δ : ℝ) (i : Fin (k + 1)) :
    challengeError (ω := ω) s d l θ δ (foldChallenge s l i) =
      foldingError (ω := ω) s d θ i := by
  classical
  simp only [challengeError, foldChallenge_ne_query, ↓reduceIte, add_zero,
    (foldChallenge_injective (ω := ω) s l).eq_iff]
  simp

@[simp]
theorem challengeError_query [SampleableType F] (θ δ : ℝ) :
    challengeError (ω := ω) s d l θ δ (queryChallenge s l) =
      Real.toNNReal (1 - min θ δ) ^ l := by
  classical
  have hne (i : Fin (k + 1)) : queryChallenge (ω := ω) s l ≠ foldChallenge s l i :=
    (foldChallenge_ne_query s l i).symm
  unfold challengeError
  rw [ite_eq_left rfl]
  have hz : (∑ i, if queryChallenge (ω := ω) s l = foldChallenge s l i then
      foldingError (ω := ω) s d θ i else 0) = 0 :=
    Finset.sum_eq_zero (fun i _ ↦ ite_eq_right (hne i))
  rw [hz, zero_add]

/-- Summing over the actual protocol challenges counts every folding error exactly once,
followed by the single query-vector error. -/
theorem sum_challengeError [SampleableType F] (θ δ : ℝ) :
    ∑ j, challengeError (ω := ω) s d l θ δ j =
      (∑ i, foldingError (ω := ω) s d θ i) + Real.toNNReal (1 - min θ δ) ^ l := by
  classical
  simp only [challengeError, Finset.sum_add_distrib]
  rw [Finset.sum_comm]
  congr 1
  · apply Finset.sum_congr rfl
    intro i _
    exact Fintype.sum_ite_eq' (foldChallenge (ω := ω) s l i)
      (fun _ ↦ foldingError (ω := ω) s d θ i)
  · exact Fintype.sum_ite_eq' (queryChallenge (ω := ω) s l)
      (fun _ ↦ Real.toNNReal (1 - min θ δ) ^ l)

/-- Proximity language using the existing Reed–Solomon code and relative distance. -/
def proximityLanguage (δ : ℝ) : Set ((ω.subdomain 0).toFinset → F) :=
  {f | ∃ u ∈ code ω (2 ^ (∑ j, (s j).val) * d.val),
    (Code.relHammingDist (fun z ↦ f (initialQuery z)) u : ℝ) < δ}

/-- Every fresh bad event obeys its bound, conditional on no earlier bad event. -/
theorem badEvent_prob_le [SampleableType F] (hs : (∑ j, (s j).val) ≤ n) (θ δ : ℝ)
    [∀ j, SampleableType ((pSpec k (ω := ω) s l).Challenge j)]
    (f : (ω.subdomain 0).toFinset → F) (hf : f ∉ proximityLanguage s d δ)
    (j : (pSpec k (ω := ω) s l).ChallengeIdx)
    (tr : (pSpec k (ω := ω) s l).Transcript j.val.castSucc)
    (hbefore : ¬ Verifier.badEventState (proximityLanguage s d δ)
      (badEvent s d l hs θ) j.val.castSucc f tr) :
    Pr{let c ← $ᵗ ((pSpec k (ω := ω) s l).Challenge j)}[badEvent s d l hs θ j f (tr.concat c)] ≤
        (challengeError (ω := ω) s d l θ δ j : ENNReal) := by
  rcases challenge_cases s l j with ⟨i, rfl⟩ | rfl
  · simpa only [badEvent_fold, challengeError_fold] using
      foldingBad_prob_le s d l f θ i tr
  · simp only [badEvent_query, challengeError_query, ENNReal.coe_pow]
    apply queryBad_prob_le s d l hs f θ δ tr
    · intro i hb
      apply hbefore
      refine Or.inr ⟨foldChallenge s l i, ?_, ?_⟩
      · simp only [foldChallenge_val, Fin.val_castSucc, queryChallenge_val]
        omega
      · exact (badEvent_fold s d l hs θ i f _).mpr hb
    · intro u hu
      exact le_of_not_gt (fun h ↦ hf ⟨u, hu, h⟩)

end Fri.Spec

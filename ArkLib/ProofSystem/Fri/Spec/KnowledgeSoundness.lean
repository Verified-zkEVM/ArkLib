/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/
module

public import ArkLib.ProofSystem.Fri.Spec.ExtractionCorrectness
public import ArkLib.ProofSystem.Fri.Spec.Soundness
public import ArkLib.OracleReduction.Security.Acceptance

/-!
# Knowledge soundness of the measured FRI extractor

The named extractor recovers from the retained commitment history on every input statement.
An absent or invalid extracted witness counts as extraction failure. The actual logged
knowledge game is bounded by the folding errors and the existing repeated-query error.
Writing `D = 2 ^ (∑ i, (s i).val) * d.val` and `N = 2 ^ n`, the threshold
`min θ δ ≤ 1-D/N` is inclusive. All query counts are allowed; zero queries and negative
thresholds give a vacuous error of at least one.

The deterministic recovery step follows Corollary 5.6 of the March 27, 2026 revision of
[GMW25]. Here it is combined with round-by-round bad-event bounds to establish the logged
knowledge game for arbitrary inputs and malicious provers.

## References

* [Garreta, A., Mohnblatt, N., Wagner, B., *A Simplified Round-by-round Soundness Proof
  of FRI*][GMW25]
-/

@[expose] public section

namespace Fri.Spec
open Domain OracleComp OracleSpec ProtocolSpec ReedSolomon Finset
open scoped ProbabilityTheory NNReal
variable {F : Type} [NonBinaryField F] [Fintype F] [DecidableEq F]
variable {n k : ℕ} {ω : SmoothCosetFftDomain n F}
variable (s : Fin (k + 1) → ℕ+) (d : ℕ+) (l : ℕ)


private theorem verifyQueries_probability_eq
    (hs : (∑ j, (s j).val) ≤ n)
    (o : ∀ j, FinalOracleStatement s ω j) (α : FinalStatement F k) :
    Pr{let xs ←$ᵗ (Fin l → (ω.subdomain 0).toFinset)}[
      (simulateQ (OracleInterface.simOracle0 (FinalOracleStatement s ω) o)
        (QueryRound.verifyQueries s hs l α xs).run).run ≠ none] =
      ((acceptingQueries s hs o α).card / (2 ^ n : ENNReal)) ^ l := by
  classical
  let e : (Fin l → Fin (2 ^ n)) ≃ (Fin l → (ω.subdomain 0).toFinset) :=
    Equiv.arrowCongr (Equiv.refl _) (ω.subdomain 0).equivToFinset
  rw [← SampleableType.prEvent_uniformSample_equiv e]
  have he (zs : Fin l → Fin (2 ^ n)) (j : Fin l) : e zs j = initialQuery (zs j) := by
    apply Subtype.ext
    simp [e, initialQuery, CosetFftDomain.subdomain_zero_eq_self]
  have hpoint (zs : Fin l → Fin (2 ^ n)) :
      ((simulateQ (OracleInterface.simOracle0 (FinalOracleStatement s ω) o)
        (QueryRound.verifyQueries s hs l α (e zs)).run).run ≠ none) ↔
      ∀ j, zs j ∈ acceptingQueries s hs o α := by
    rw [QueryRound.eval_verifyQueries]
    simp [acceptingQueries, he]
    rfl
  simp only [hpoint]
  simpa using Probability.prob_uniform_pi_mem_finset_eq (acceptingQueries s hs o α) l

private theorem verifyQueries_probability_le_of_density
    (hs : (∑ j, (s j).val) ≤ n)
    (o : ∀ j, FinalOracleStatement s ω j) (α : FinalStatement F k) (τ : ℝ)
    (hdensity : ((acceptingQueries s hs o α).card : ℝ) / 2 ^ n ≤ 1 - τ) :
    Pr{let xs ←$ᵗ (Fin l → (ω.subdomain 0).toFinset)}[
      (simulateQ (OracleInterface.simOracle0 (FinalOracleStatement s ω) o)
        (QueryRound.verifyQueries s hs l α xs).run).run ≠ none] ≤
      ENNReal.ofReal (1 - τ) ^ l := by
  rw [verifyQueries_probability_eq]
  apply pow_le_pow_left' _ l
  have h := ENNReal.ofReal_le_ofReal hdensity
  simpa [ENNReal.ofReal_div_of_pos, show (0 : ℝ) < 2 ^ n by positivity] using h

private def extractionQueryBad (hs : (∑ j, (s j).val) ≤ n)
    (fails : (f : (ω.subdomain 0).toFinset → F) →
      (pSpec k (ω := ω) s l).Transcript (queryChallenge (ω := ω) s l).val.castSucc → Prop)
    (f : (ω.subdomain 0).toFinset → F)
    (tr : (pSpec k (ω := ω) s l).Transcript (queryChallenge (ω := ω) s l).val.succ) : Prop :=
  queryBad s d l hs f tr ∧
    fails f (tr.restrict (by simp only [Fin.val_castSucc, Fin.val_succ]; omega))

private theorem extractionQueryBad_concat_iff (hs : (∑ j, (s j).val) ≤ n)
    (fails : (f : (ω.subdomain 0).toFinset → F) →
      (pSpec k (ω := ω) s l).Transcript (queryChallenge (ω := ω) s l).val.castSucc → Prop)
    (f : (ω.subdomain 0).toFinset → F)
    (tr : (pSpec k (ω := ω) s l).Transcript (queryChallenge (ω := ω) s l).val.castSucc)
    (xs : (pSpec k (ω := ω) s l).Challenge (queryChallenge s l)) :
    extractionQueryBad s d l hs fails f (tr.concat xs) ↔
      queryBad s d l hs f (tr.concat xs) ∧ fails f tr := by
  unfold extractionQueryBad
  simp only [Transcript.restrict_concat
    (a := (queryChallenge (ω := ω) s l).val.castSucc) (b := (queryChallenge s l).val)
    le_rfl, Transcript.restrict_refl]

private theorem extractionQueryBad_prob_le (hs : (∑ j, (s j).val) ≤ n)
    (fails : (f : (ω.subdomain 0).toFinset → F) →
      (pSpec k (ω := ω) s l).Transcript (queryChallenge (ω := ω) s l).val.castSucc → Prop)
    (f : (ω.subdomain 0).toFinset → F) (θ δ : ℝ)
    [SampleableType ((pSpec k (ω := ω) s l).Challenge (queryChallenge s l))]
    (tr : (pSpec k (ω := ω) s l).Transcript (queryChallenge (ω := ω) s l).val.castSucc)
    (hsafe : ∀ i : Fin (k + 1), ¬ foldingBad s d l f θ i
      (tr.restrict (by simp only [Fin.val_succ, Fin.val_castSucc,
        foldChallenge_val, queryChallenge_val]; omega)))
    (hrecover : SafeHistory s d (queryHistory s l f tr) (queryFoldChallenges s l tr) θ →
      (finalPolynomial s (queryHistory s l f tr)).natDegree < d.val →
      (2 ^ n : ℝ) * (1 - min θ δ) ≤
        (acceptingQueries s hs (queryHistory s l f tr) (queryFoldChallenges s l tr)).card →
      ¬ fails f tr) :
    Pr{let xs ←$ᵗ ((pSpec k (ω := ω) s l).Challenge (queryChallenge s l))}[
      extractionQueryBad s d l hs fails f (tr.concat xs)] ≤
      ENNReal.ofReal (1 - min θ δ) ^ l := by
  classical
  simp only [extractionQueryBad_concat_iff, queryBad_concat_iff]
  by_cases hf : fails f tr
  · simp only [hf, and_true]
    by_cases hd : (finalPolynomial s (queryHistory s l f tr)).natDegree < d.val
    · simp only [hd, true_and]
      refine (SampleableType.prEvent_uniformSample_equiv
        (Equiv.cast (queryChallenge_type (ω := ω) s l))
        (fun xs ↦ (simulateQ
          (OracleInterface.simOracle0 (FinalOracleStatement s ω) (queryHistory s l f tr))
          (QueryRound.verifyQueries s hs l (queryFoldChallenges s l tr) xs).run).run ≠ none)
        ).le.trans ?_
      apply verifyQueries_probability_le_of_density
      apply le_of_lt
      apply (div_lt_iff₀ (show (0 : ℝ) < 2 ^ n by positivity)).mpr
      have hn := mt (hrecover (safeHistory_queryHistory s d l f θ tr hsafe) hd) (not_not.mpr hf)
      exact lt_of_not_ge (by simpa [mul_comm] using hn)
    · simp only [hd, false_and]
      simp
  · simp only [hf, and_false]
    simp

private def extractionBadEvent (hs : (∑ j, (s j).val) ≤ n) (θ : ℝ)
    (fails : (f : (ω.subdomain 0).toFinset → F) →
      (pSpec k (ω := ω) s l).Transcript (queryChallenge (ω := ω) s l).val.castSucc → Prop)
    (j : (pSpec k (ω := ω) s l).ChallengeIdx) (f : (ω.subdomain 0).toFinset → F)
    (tr : (pSpec k (ω := ω) s l).Transcript j.val.succ) : Prop :=
  (∃ i, ∃ h : j = foldChallenge s l i, foldingBad s d l f θ i (h ▸ tr)) ∨
    ∃ h : j = queryChallenge s l, extractionQueryBad s d l hs fails f (h ▸ tr)

private theorem extractionBadEvent_fold (hs : (∑ j, (s j).val) ≤ n) (θ : ℝ)
    (fails : (f : (ω.subdomain 0).toFinset → F) →
      (pSpec k (ω := ω) s l).Transcript (queryChallenge (ω := ω) s l).val.castSucc → Prop)
    (i : Fin (k + 1)) (f : (ω.subdomain 0).toFinset → F)
    (tr : (pSpec k (ω := ω) s l).Transcript (foldChallenge (ω := ω) s l i).val.succ) :
    extractionBadEvent s d l hs θ fails (foldChallenge s l i) f tr ↔
      foldingBad s d l f θ i tr := by
  constructor
  · rintro (⟨j, h, hb⟩ | ⟨h, _⟩)
    · have hij := foldChallenge_injective s l h
      subst j
      exact hb
    · exact (foldChallenge_ne_query s l i h).elim
  · intro hb
    exact Or.inl ⟨i, rfl, hb⟩

private theorem extractionBadEvent_query (hs : (∑ j, (s j).val) ≤ n) (θ : ℝ)
    (fails : (f : (ω.subdomain 0).toFinset → F) →
      (pSpec k (ω := ω) s l).Transcript (queryChallenge (ω := ω) s l).val.castSucc → Prop)
    (f : (ω.subdomain 0).toFinset → F)
    (tr : (pSpec k (ω := ω) s l).Transcript (queryChallenge (ω := ω) s l).val.succ) :
    extractionBadEvent s d l hs θ fails (queryChallenge s l) f tr ↔
      extractionQueryBad s d l hs fails f tr := by
  constructor
  · rintro (⟨i, h, _⟩ | ⟨h, hb⟩)
    · exact (foldChallenge_ne_query s l i h.symm).elim
    · exact hb
  · intro hb
    exact Or.inr ⟨rfl, hb⟩

private theorem extractionBadEvent_prob_le [SampleableType F]
    (hs : (∑ j, (s j).val) ≤ n) (θ δ : ℝ)
    [∀ j, SampleableType ((pSpec k (ω := ω) s l).Challenge j)]
    (fails : (f : (ω.subdomain 0).toFinset → F) →
      (pSpec k (ω := ω) s l).Transcript (queryChallenge (ω := ω) s l).val.castSucc → Prop)
    (hrecover : ∀ f tr,
      SafeHistory s d (queryHistory s l f tr) (queryFoldChallenges s l tr) θ →
      (finalPolynomial s (queryHistory s l f tr)).natDegree < d.val →
      (2 ^ n : ℝ) * (1 - min θ δ) ≤
        (acceptingQueries s hs (queryHistory s l f tr) (queryFoldChallenges s l tr)).card →
      ¬ fails f tr)
    (f : (ω.subdomain 0).toFinset → F)
    (j : (pSpec k (ω := ω) s l).ChallengeIdx)
    (tr : (pSpec k (ω := ω) s l).Transcript j.val.castSucc)
    (hbefore : ¬ Verifier.badEventState ∅
      (fun j f tr ↦ extractionBadEvent s d l hs θ fails j f tr)
      j.val.castSucc f tr) :
    Pr{let c ← $ᵗ ((pSpec k (ω := ω) s l).Challenge j)}[
      extractionBadEvent s d l hs θ fails j f (tr.concat c)] ≤
        (challengeError (ω := ω) s d l θ δ j : ENNReal) := by
  rcases challenge_cases s l j with ⟨i, rfl⟩ | rfl
  · simpa only [extractionBadEvent_fold, challengeError_fold] using
      foldingBad_prob_le s d l f θ i tr
  · simp only [extractionBadEvent_query, challengeError_query, ENNReal.coe_pow]
    apply extractionQueryBad_prob_le s d l hs fails f θ δ tr
    · intro i hb
      apply hbefore
      refine Or.inr ⟨foldChallenge s l i, ?_, ?_⟩
      · simp only [foldChallenge_val, Fin.val_castSucc, queryChallenge_val]
        omega
      · exact (extractionBadEvent_fold s d l hs θ fails i f _).mpr hb
    · exact hrecover f tr

private theorem extractionTerminalEvent_prob_le [SampleableType F]
    (hs : (∑ j, (s j).val) ≤ n) (θ δ : ℝ)
    [∀ j, SampleableType ((pSpec k (ω := ω) s l).Challenge j)]
    (fails : (f : (ω.subdomain 0).toFinset → F) →
      (pSpec k (ω := ω) s l).Transcript (queryChallenge (ω := ω) s l).val.castSucc → Prop)
    (hrecover : ∀ f tr,
      SafeHistory s d (queryHistory s l f tr) (queryFoldChallenges s l tr) θ →
      (finalPolynomial s (queryHistory s l f tr)).natDegree < d.val →
      (2 ^ n : ℝ) * (1 - min θ δ) ≤
        (acceptingQueries s hs (queryHistory s l f tr) (queryFoldChallenges s l tr)).card →
      ¬ fails f tr)
    {σ WitIn WitOut StmtOut : Type}
    (impl : QueryImpl (emptySpec.{0, 0}) (StateT σ ProbComp))
    (prover : Prover []ₒ
      (Statement F (0 : Fin (k + 1)) × ∀ j, OracleStatement s ω 0 j)
      WitIn StmtOut WitOut (pSpec k (ω := ω) s l))
    (stmt : Statement F (0 : Fin (k + 1)) × ∀ j, OracleStatement s ω 0 j)
    (wit : WitIn)
    (E : (pSpec k (ω := ω) s l).FullTranscript → Prop)
    (hterminal : ∀ tr, E tr → extractionQueryBad s d l hs fails (initialOracle s stmt)
      (Transcript.restrict (b := Fin.last _)
        (by simp only [Fin.val_succ, Fin.val_last]; omega) tr))
    (os : σ) :
    Pr{let x ← (simulateQ (impl.addLift challengeQueryImpl : QueryImpl _ (StateT σ ProbComp))
        (prover.run stmt wit)).run os}[E x.1.1] ≤
      (soundnessError (ω := ω) s d l θ δ : ENNReal) := by
  let bad := fun j st tr ↦ extractionBadEvent (ω := ω) s d l hs θ fails j
    (initialOracle s st) tr
  have hb : ∀ st ∉ (∅ : Set (Statement F (0 : Fin (k + 1)) ×
      ∀ j, OracleStatement s ω 0 j)), ∀ j, ∀ tr,
      ¬ Verifier.badEventState ∅ bad j.val.castSucc st tr →
      Pr{let c ← $ᵗ ((pSpec k (ω := ω) s l).Challenge j)}[bad j st (tr.concat c)] ≤
        (challengeError (ω := ω) s d l θ δ j : ENNReal) := by
    intro st _ j tr hbefore
    apply extractionBadEvent_prob_le s d l hs θ δ fails hrecover
    intro hbad
    apply hbefore
    rcases hbad with hbad | ⟨i, hi, hbad⟩
    · exact hbad.elim
    · exact Or.inr ⟨i, hi, hbad⟩
  have h := Verifier.prob_terminal_event_le_of_badEvents impl ∅ bad
    (fun j ↦ (challengeError (ω := ω) s d l θ δ j : ENNReal)) hb
    prover stmt (Set.notMem_empty _) wit E (fun tr he ↦ ?_) os
  · simpa only [← ENNReal.ofNNReal_finsetSum, sum_challengeError, soundnessError,
      ENNReal.coe_add, ENNReal.coe_pow, ENNReal.ofReal] using h
  · exact Or.inr ⟨queryChallenge s l, (queryChallenge s l).val.isLt,
      (extractionBadEvent_query s d l hs θ fails (initialOracle s stmt) _).mpr
        (hterminal tr he)⟩

end Fri.Spec

namespace Fri.Spec
open Domain OracleComp OracleSpec ProtocolSpec ReedSolomon Finset
open scoped NNReal
variable {F : Type} [NonBinaryField F] [Fintype F] [SampleableType F] [DecidableEq F]
variable {n k : ℕ} {ω : SmoothCosetFftDomain n F}
variable (s : Fin (k + 1) → ℕ+) (d : ℕ+) (l : ℕ)

private theorem knowledge_soundness_with_of_history_extractor
    (hdom : 2 ^ (∑ j, (s j).val) * d.val ≤ 2 ^ n)
    (θ : ℝ) (δ : ℝ≥0)
    [∀ j, SampleableType ((pSpec k (ω := ω) s l).Challenge j)]
    (e : (f : (ω.subdomain 0).toFinset → F) →
      (pSpec k (ω := ω) s l).Transcript (queryChallenge (ω := ω) s l).val.castSucc →
        Option (Witness F s d (0 : Fin (k + 2))))
    (hrecover : ∀ f tr,
      SafeHistory s d (queryHistory s l f tr) (queryFoldChallenges s l tr) θ →
      (finalPolynomial s (queryHistory s l f tr)).natDegree < d.val →
      (2 ^ n : ℝ) * (1 - min θ δ) ≤
        (acceptingQueries s (round_bound hdom) (queryHistory s l f tr)
          (queryFoldChallenges s l tr)).card →
      ∃ p ∈ e f tr, (Code.relHammingDist (fun z ↦ f (initialQuery z))
        (fun z ↦ p.1.eval (ω z)) : ℝ) ≤ δ)
    {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl (emptySpec.{0, 0}) (StateT σ ProbComp)) :
    (reduction k (ω := ω) s d hdom l).verifier.toVerifier.knowledgeSoundnessWith init impl
      (inputRelation k s d hdom δ) (outputRelation k s d hdom δ)
      (Extractor.Straightline.ofTranscript
        (fun stmt tr ↦ e (initialOracle s stmt) (queryPrefix s l tr)))
      (soundnessError (ω := ω) s d l θ δ) := by
  let fails := fun (f : (ω.subdomain 0).toFinset → F)
      (tr : (pSpec k (ω := ω) s l).Transcript
        (queryChallenge (ω := ω) s l).val.castSucc) ↦
    ∀ p ∈ e f tr, ¬ (Code.relHammingDist (fun z ↦ f (initialQuery z))
      (fun z ↦ p.1.eval (ω z)) : ℝ) ≤ δ
  let E := fun (stmt : Statement F (0 : Fin (k + 1)) ×
      ∀ j, OracleStatement s ω 0 j) (tr : (pSpec k (ω := ω) s l).FullTranscript) ↦
    queryBad s d l (round_bound hdom) (initialOracle s stmt)
      (Transcript.restrict (b := Fin.last _)
        (by simp only [Fin.val_succ, Fin.val_last]; omega) tr) ∧
      fails (initialOracle s stmt) (queryPrefix s l tr)
  apply Verifier.knowledgeSoundnessWith_of_transcript_event init impl _ _ _ _ _ E
  · intro stmt tr hfail hE
    rw [reduction_run]
    apply congrArg pure
    apply ite_eq_right
    intro hbad
    apply hE
    refine ⟨hbad, ?_⟩
    intro p hp hdist
    exact hfail p hp (mem_inputRelation_of_relHammingDist_le s d hdom δ stmt p hdist)
  · intro Aux stmt wit prover os
    have hrec : ∀ f tr,
        SafeHistory s d (queryHistory s l f tr) (queryFoldChallenges s l tr) θ →
        (finalPolynomial s (queryHistory s l f tr)).natDegree < d.val →
        (2 ^ n : ℝ) * (1 - min θ δ) ≤
          (acceptingQueries s (round_bound hdom) (queryHistory s l f tr)
            (queryFoldChallenges s l tr)).card → ¬ fails f tr := by
      intro f tr hsafe hdegree hlarge
      obtain ⟨p, hp, hdist⟩ := hrecover f tr hsafe hdegree hlarge
      exact fun hf ↦ hf p hp hdist
    exact extractionTerminalEvent_prob_le s d l (round_bound hdom) θ δ fails hrec
      impl prover stmt wit (E stmt) (fun _ hE ↦ hE) os


/-- The named extractor fails to produce a valid input witness on a valid accepted output
with probability at most `soundnessError`, for every input statement. -/
theorem knowledge_soundness_with
    (hdom : 2 ^ (∑ j, (s j).val) * d.val ≤ 2 ^ n)
    (θ : ℝ) (δ : ℝ≥0)
    (hrate : min θ δ ≤ 1 - (2 ^ (∑ j, (s j).val) * d.val : ℕ) / (2 ^ n : ℝ))
    [∀ j, SampleableType ((pSpec k (ω := ω) s l).Challenge j)]
    {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl (emptySpec.{0, 0}) (StateT σ ProbComp)) :
    (reduction k (ω := ω) s d hdom l).verifier.knowledgeSoundnessWith init impl
      (inputRelation k s d hdom δ) (outputRelation k s d hdom δ)
      (Extractor.extract s d (round_bound hdom) l)
      (soundnessError (ω := ω) s d l θ δ) := by
  apply knowledge_soundness_with_of_history_extractor s d l hdom θ δ
    (fun f tr ↦ Extractor.extractHistory s d (round_bound hdom)
      (queryHistory s l f tr) (queryFoldChallenges s l tr))
  intro f tr hsafe hdegree hlarge
  obtain ⟨p, hp, hdist⟩ := Extractor.extractHistory_eq_some_of_density s d
    (round_bound hdom) (queryHistory s l f tr) (queryFoldChallenges s l tr)
    θ (min θ δ) hsafe hdegree (min_le_left _ _) hrate hlarge
  refine ⟨p, hp, ?_⟩
  have hf : initialWord s (queryHistory s l f tr) = (fun z ↦ f (initialQuery z)) :=
    funext (initialWord_queryHistory s l f tr)
  simpa only [hf] using hdist.trans (min_le_right θ (δ : ℝ))

/-- The measured prefix extractor witnesses straightline knowledge soundness. -/
theorem knowledge_soundness
    (hdom : 2 ^ (∑ j, (s j).val) * d.val ≤ 2 ^ n)
    (θ : ℝ) (δ : ℝ≥0)
    (hrate : min θ δ ≤ 1 - (2 ^ (∑ j, (s j).val) * d.val : ℕ) / (2 ^ n : ℝ))
    [∀ j, SampleableType ((pSpec k (ω := ω) s l).Challenge j)]
    {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl (emptySpec.{0, 0}) (StateT σ ProbComp)) :
    (reduction k (ω := ω) s d hdom l).verifier.knowledgeSoundness init impl
      (inputRelation k s d hdom δ) (outputRelation k s d hdom δ)
      (soundnessError (ω := ω) s d l θ δ) :=
  OracleVerifier.knowledgeSoundness_of_with init impl
    (knowledge_soundness_with s d l hdom θ δ hrate init impl)

end Fri.Spec

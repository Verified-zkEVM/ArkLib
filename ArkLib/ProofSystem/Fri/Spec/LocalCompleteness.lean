/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

public import ArkLib.ProofSystem.Fri.Spec.HonestExecution
public import ArkLib.ProofSystem.Fri.Spec.QueryExecution
public import ArkLib.ProofSystem.Fri.Spec.QueryCompleteness
public import ArkLib.ToMathlib.InformationTheory.Hamming

/-!
# Completeness of polynomial FRI query checks

The executable local check accepts polynomial evaluations on its queried block when the next
answer is the corresponding polynomial fold. No degree bound is needed for this identity.
-/

@[expose] public section

namespace Fri.Spec.QueryRound

open Domain OracleSpec OracleComp ProtocolSpec Finset
open scoped NNReal ENNReal ProbabilityTheory

variable {F : Type} [NonBinaryField F] [Fintype F] [DecidableEq F]
variable {n k : ℕ} {ω : SmoothCosetFftDomain n F}
variable (s : Fin (k + 1) → ℕ+)

/-- Polynomial answers on a queried block pass the local check against their folded value. -/
theorem eval_checkRound_eq_true_of_polynomial (hs : (∑ j, (s j).val) ≤ n)
    (o : ∀ j, FinalOracleStatement s ω j) (p q : CompPoly.CPolynomial F)
    (α : F) (i : Fin (k + 1)) (x : (ω.subdomain 0).toFinset)
    (hword : ∀ y ∈ queryBlock s hs i x, committedWord s o i y = q.eval y.val)
    (hnext : simulateQ (OracleInterface.simOracle0 (FinalOracleStatement s ω) o)
      (queryNext s hs p i x) =
        (CompPoly.CPolynomial.FoldingPolynomial.cpolyFold q (2 ^ (s i).val) α).eval
          ((queryPoint s hs i x).val ^ (2 ^ (s i).val))) :
    simulateQ (OracleInterface.simOracle0 (FinalOracleStatement s ω) o)
      (checkRound s hs p α i x) = true := by
  rw [eval_checkRound, hnext]
  erw [RoundConsistency.roundConsistencyCheck_map_get]
  let qs := queryBlock s hs i x
  let a := (queryPoint s hs i x).val
  have hlen : qs.length = 2 ^ (s i).val := queryBlock_length s hs i x
  have : NeZero qs.length := ⟨by rw [hlen]; positivity⟩
  let points : Fin qs.length ↪ F :=
    ⟨fun j ↦ (qs.get j).val, Subtype.val_injective.comp
      (List.nodup_iff_injective_get.mp (queryBlock_nodup s hs i x))⟩
  have hpow (j : Fin qs.length) : points j ^ qs.length = a ^ qs.length := by
    change (qs.get j).val ^ qs.length = a ^ qs.length
    simpa only [hlen] using queryBlock_pow s hs i x (qs.get j) (List.get_mem _ _)
  have h := RoundConsistency.roundConsistencyCheck_eq_true_of_pow_eq points q a α hpow
  have hword' (j : Fin qs.length) :
      committedWord s o i (qs.get j) = q.eval (qs.get j).val :=
    hword _ (List.get_mem _ _)
  have hpoints (j : Fin qs.length) : points j = (qs.get j).val := rfl
  change RoundConsistency.roundConsistencyCheck α
    (fun j : Fin qs.length ↦ ((qs.get j).val, committedWord s o i (qs.get j)))
    ((CompPoly.CPolynomial.FoldingPolynomial.cpolyFold q (2 ^ (s i).val) α).eval
      (a ^ (2 ^ (s i).val))) = true
  simpa only [hword', hpoints, hlen] using h

/-- Every retained word after the initial word is an exact honest polynomial evaluation. -/
theorem committedWord_honestHistory_of_ne_zero (d : ℕ+)
    (f : (ω.subdomain 0).toFinset → F) (p₀ : Witness F s d 0)
    (α : Fin (k + 1) → F) (i : Fin (k + 1)) (hi : i ≠ 0)
    (x : (ω.subdomain (foldingPrefix s i.castSucc)).toFinset) :
    committedWord s (honestHistory s d f p₀ α) i x =
      (honestPolynomial s d p₀ α i.castSucc).val.eval x.val := by
  erw [committedWord_honestHistory]
  obtain ⟨j, rfl⟩ := Fin.eq_succ_of_ne_zero hi
  rfl

/-- The next honest commitment, including the final polynomial, evaluates the next witness. -/
theorem committedFunction_honestHistory_succ (d : ℕ+)
    (f : (ω.subdomain 0).toFinset → F) (p₀ : Witness F s d 0)
    (α : Fin (k + 1) → F) (i : Fin (k + 1))
    (x : (ω.subdomain (foldingPrefix s i.succ)).toFinset) :
    committedFunction s (honestHistory s d f p₀ α) i.succ x.val =
      (honestPolynomial s d p₀ α i.succ).val.eval x.val := by
  revert x
  refine Fin.lastCases ?_ (fun j ↦ ?_) i
  · intro x
    simp only [Fin.succ_last, committedFunction_last]
    erw [finalPolynomial_honestHistory]
  · intro x
    change committedFunction s (honestHistory s d f p₀ α) j.succ.castSucc x.val =
      (honestPolynomial s d p₀ α j.succ.castSucc).val.eval x.val
    rw [committedFunction_castSucc]
    exact committedWord_honestHistory_of_ne_zero s d f p₀ α j.succ (Fin.succ_ne_zero j) x

/-- The answer following an honest block equals evaluation of its folded polynomial. -/
theorem eval_queryNext_honestHistory (d : ℕ+) (hs : (∑ j, (s j).val) ≤ n)
    (f : (ω.subdomain 0).toFinset → F) (p₀ : Witness F s d 0)
    (α : Fin (k + 1) → F) (i : Fin (k + 1)) (x : (ω.subdomain 0).toFinset) :
    simulateQ (OracleInterface.simOracle0 (FinalOracleStatement s ω)
      (honestHistory s d f p₀ α))
      (queryNext s hs (finalPolynomial s (honestHistory s d f p₀ α)) i x) =
        (CompPoly.CPolynomial.FoldingPolynomial.cpolyFold
          (honestPolynomial s d p₀ α i.castSucc).val (2 ^ (s i).val) (α i)).eval
          ((queryPoint s hs i x).val ^ (2 ^ (s i).val)) := by
  rw [eval_queryNext]
  have hx : x.val ^ (2 ^ foldingPrefix s i.succ) ∈
      (ω.subdomain (foldingPrefix s i.succ)).toFinset :=
    CosetFftDomainClass.pow_mem_subdomain_of_mem_subdomain_0_toFinset
      ((foldingPrefix_le s i.succ).trans hs) x.property
  rw [committedFunction_honestHistory_succ s d f p₀ α i ⟨_, hx⟩,
    honestPolynomial_succ]
  congr 1
  change x.val ^ (2 ^ foldingPrefix s i.succ) =
    (queryPoint s hs i x).val ^ (2 ^ (s i).val)
  rw [foldingPrefix_succ, pow_add, pow_mul]
  rfl

/-- Every noninitial local check accepts the honest retained history, even for noisy input. -/
theorem eval_checkRound_honestHistory_of_ne_zero (d : ℕ+)
    (hs : (∑ j, (s j).val) ≤ n)
    (f : (ω.subdomain 0).toFinset → F) (p₀ : Witness F s d 0)
    (α : Fin (k + 1) → F) (i : Fin (k + 1)) (hi : i ≠ 0)
    (x : (ω.subdomain 0).toFinset) :
    simulateQ (OracleInterface.simOracle0 (FinalOracleStatement s ω)
      (honestHistory s d f p₀ α))
      (checkRound s hs (finalPolynomial s (honestHistory s d f p₀ α)) (α i) i x) = true := by
  apply eval_checkRound_eq_true_of_polynomial s hs _ _
    (honestPolynomial s d p₀ α i.castSucc).val
  · intro y _
    exact committedWord_honestHistory_of_ne_zero s d f p₀ α i hi y
  · exact eval_queryNext_honestHistory s d hs f p₀ α i x

/-- Exact input evaluations pass every honest local check for arbitrary folding challenges. -/
theorem eval_checkRound_honestHistory (d : ℕ+) (hs : (∑ j, (s j).val) ≤ n)
    (p₀ : Witness F s d 0) (α : Fin (k + 1) → F)
    (i : Fin (k + 1)) (x : (ω.subdomain 0).toFinset) :
    simulateQ (OracleInterface.simOracle0 (FinalOracleStatement s ω)
      (honestHistory s d (fun y : (ω.subdomain 0).toFinset ↦ p₀.val.eval y.val) p₀ α))
      (checkRound s hs (finalPolynomial s
        (honestHistory s d (fun y : (ω.subdomain 0).toFinset ↦ p₀.val.eval y.val) p₀ α))
        (α i) i x) = true := by
  by_cases hi : i = 0
  · subst i
    apply eval_checkRound_eq_true_of_polynomial s hs _ _ p₀.val
    · intro y _
      erw [committedWord_honestHistory, honestWords_zero]
    · simpa only [Fin.castSucc_zero, honestPolynomial_zero] using
        eval_queryNext_honestHistory s d hs
          (fun y : (ω.subdomain 0).toFinset ↦ p₀.val.eval y.val) p₀ α 0 x
  · exact eval_checkRound_honestHistory_of_ne_zero s d hs _ p₀ α i hi x

/-- Every query vector accepts the honest history of an exact input polynomial. -/
theorem eval_verifyQueries_honestHistory (d : ℕ+) (hs : (∑ j, (s j).val) ≤ n)
    (p₀ : Witness F s d 0) (α : Fin (k + 1) → F) {l : ℕ}
    (xs : Fin l → (ω.subdomain 0).toFinset) :
    (simulateQ (OracleInterface.simOracle0 (FinalOracleStatement s ω)
      (honestHistory s d (fun y : (ω.subdomain 0).toFinset ↦ p₀.val.eval y.val) p₀ α))
      (verifyQueries s hs l α xs).run).run = some α := by
  rw [eval_verifyQueries]
  exact ite_eq_left fun j i ↦ eval_checkRound_honestHistory s d hs p₀ α i (xs j)

/-- A query whose first block has no input errors passes every honest local check. -/
theorem cleanFirstQueries_subset_acceptingQueries (d : ℕ+)
    (hs : (∑ j, (s j).val) ≤ n)
    (f : (ω.subdomain 0).toFinset → F) (p₀ : Witness F s d 0)
    (α : Fin (k + 1) → F) :
    cleanFirstQueries ω (s 0).val (fun z ↦ f (initialQuery z))
      (fun z ↦ p₀.val.eval (ω z)) ⊆
      acceptingQueries s hs (honestHistory s d f p₀ α) α := by
  classical
  intro z hz
  rw [acceptingQueries, mem_filter]
  refine ⟨mem_univ _, fun i ↦ ?_⟩
  by_cases hi : i = 0
  · subst i
    apply eval_checkRound_eq_true_of_polynomial s hs _ _ p₀.val
    · intro y hy
      erw [committedWord_honestHistory, honestWords_zero]
      have hy_mem : y.val ∈ ω.toFinset := by
        have hy₀ : y.val ∈ (ω.subdomain 0).toFinset := y.property
        rwa [CosetFftDomain.subdomain_zero_eq_self] at hy₀
      let j := ω.equivToFinset.symm ⟨y.val, hy_mem⟩
      have hj : ω j = y.val := ω.equivToFinset_symm_apply ⟨y.val, hy_mem⟩
      have hquery : initialQuery j = y := Subtype.ext hj
      have hpow := queryBlock_pow s hs 0 (initialQuery z) y hy
      have hpow' : ω j ^ 2 ^ (s 0).val = ω z ^ 2 ^ (s 0).val := by
        simpa [queryPoint, initialQuery, hj] using hpow
      have hclean := (mem_cleanFirstQueries ω (s 0).val _ _ z).mp hz j hpow'
      simpa only [hquery, hj] using hclean
    · simpa only [Fin.castSucc_zero, honestPolynomial_zero] using
        eval_queryNext_honestHistory s d hs f p₀ α 0 (initialQuery z)
  · exact eval_checkRound_honestHistory_of_ne_zero s d hs f p₀ α i hi (initialQuery z)

private theorem prob_verifyQueries_eq (hs : (∑ j, (s j).val) ≤ n)
    (o : ∀ j, FinalOracleStatement s ω j) (α : Fin (k + 1) → F) (l : ℕ) :
    Pr{let xs ←$ᵗ (Fin l → (ω.subdomain 0).toFinset)}[
      (simulateQ (OracleInterface.simOracle0 (FinalOracleStatement s ω) o)
        (verifyQueries s hs l α xs).run).run ≠ none] =
      Pr{let zs ←$ᵗ (Fin l → Fin (2 ^ n))}[
        ∀ j, zs j ∈ acceptingQueries s hs o α] := by
  classical
  let e : (Fin l → Fin (2 ^ n)) ≃ (Fin l → (ω.subdomain 0).toFinset) :=
    Equiv.arrowCongr (Equiv.refl _) (ω.subdomain 0).equivToFinset
  rw [← SampleableType.prEvent_uniformSample_equiv e]
  have he (zs : Fin l → Fin (2 ^ n)) (j : Fin l) : e zs j = initialQuery (zs j) := by
    apply Subtype.ext
    simp [e, initialQuery, CosetFftDomain.subdomain_zero_eq_self]
  have hpoint (zs : Fin l → Fin (2 ^ n)) :
      ((simulateQ (OracleInterface.simOracle0 (FinalOracleStatement s ω)
          o) (verifyQueries s hs l α (e zs)).run).run ≠ none) ↔
        ∀ j, zs j ∈ acceptingQueries s hs o α := by
    rw [eval_verifyQueries]
    simp [acceptingQueries, he]
    rfl
  simp only [hpoint]

/-- Independent uniform queries accept an honest history with the clean first-block bound. -/
theorem verifyQueries_completeness_blocks (d : ℕ+) (hs : (∑ j, (s j).val) ≤ n)
    (f : (ω.subdomain 0).toFinset → F) (p₀ : Witness F s d 0)
    (α : Fin (k + 1) → F) (l : ℕ) :
    (((cleanFirstQueries ω (s 0).val (fun z ↦ f (initialQuery z))
      (fun z ↦ p₀.val.eval (ω z))).card : ℝ≥0∞) / 2 ^ n) ^ l ≤
      Pr{let xs ←$ᵗ (Fin l → (ω.subdomain 0).toFinset)}[
        (simulateQ (OracleInterface.simOracle0 (FinalOracleStatement s ω)
          (honestHistory s d f p₀ α)) (verifyQueries s hs l α xs).run).run ≠ none] := by
  rw [prob_verifyQueries_eq]
  exact cleanFirstQueries_pow_le_prob_uniform_queries ω (s 0).val
    (fun z ↦ f (initialQuery z)) (fun z ↦ p₀.val.eval (ω z))
    (acceptingQueries s hs (honestHistory s d f p₀ α) α)
    (cleanFirstQueries_subset_acceptingQueries s d hs f p₀ α) l

/-- Independent uniform queries accept an honest folded history with the clipped radius bound. -/
theorem verifyQueries_completeness (d : ℕ+) (hs : (∑ j, (s j).val) ≤ n)
    (f : (ω.subdomain 0).toFinset → F) (p₀ : Witness F s d 0)
    (α : Fin (k + 1) → F) (δ : ℝ≥0) (l : ℕ)
    (hdist : (Code.relHammingDist f (fun x ↦ p₀.val.eval x.val) : ℝ≥0) ≤ δ) :
    1 - (completenessError s δ l : ℝ≥0∞) ≤
      Pr{let xs ←$ᵗ (Fin l → (ω.subdomain 0).toFinset)}[
        (simulateQ (OracleInterface.simOracle0 (FinalOracleStatement s ω)
          (honestHistory s d f p₀ α)) (verifyQueries s hs l α xs).run).run ≠ none] := by
  rw [prob_verifyQueries_eq]
  have hdist' : (Code.relHammingDist (fun z ↦ f (initialQuery z))
      (fun z ↦ p₀.val.eval (ω z)) : ℝ≥0) ≤ δ := by
    let e₀ := (ω.subdomain 0).equivToFinset
    have he₀ (z : Fin (2 ^ n)) : e₀ z = initialQuery z := by
      apply Subtype.ext
      simp [e₀, initialQuery, CosetFftDomain.subdomain_zero_eq_self]
    have hdist_eq : Code.relHammingDist (f ∘ e₀)
        ((fun x ↦ p₀.val.eval x.val) ∘ e₀) =
        Code.relHammingDist f (fun x ↦ p₀.val.eval x.val) := by
      unfold Code.relHammingDist
      rw [hammingDist_comp_equiv, Fintype.card_congr e₀]
    rw [← hdist_eq] at hdist
    simpa [Function.comp_def, he₀, initialQuery] using hdist
  exact one_sub_completenessError_le_prob_uniform_queries ω s
    ((Finset.single_le_sum (f := fun j ↦ (s j).val) (by simp) (by simp)).trans hs)
    (fun z ↦ f (initialQuery z)) (fun z ↦ p₀.val.eval (ω z)) δ hdist'
    (acceptingQueries s hs (honestHistory s d f p₀ α) α)
    (cleanFirstQueries_subset_acceptingQueries s d hs f p₀ α) l

end Fri.Spec.QueryRound

/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.ProofSystem.BatchedFri.Spec.General
public import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.AffineCoefficients
public import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.GeneratorBounds
public import ArkLib.Data.CodingTheory.ProximityGenerator.Multilinear
public import ArkLib.OracleReduction.Composition.Sequential.GuardedCompleteness
public import ArkLib.OracleReduction.Security.GuardedSoundness

/-!
# Security of the batching round

A seed selects coefficients through a proximity generator. The honest combination preserves
the common agreement set for every radius; soundness is bounded by the generator's `caError`.
The input relation and the FRI output relation do not depend on the generator.

The family corollaries use independent affine coefficients with `errorBound`, powers with
`m * errorBound` (both in the open Johnson regime), and `t`-variable tensor monomials with
`t * n / |F|` in the unique-decoding regime, where `n` is the code length.
`soundness_multilinear_johnson` also supplies `t` times the proved 1.5-Johnson MCA error.

## References

* [Ben-Sasson, E., Carmon, D., Ishai, Y., Kopparty, S., Saraf, S.,
  *Proximity Gaps for Reed–Solomon Codes*][BCIKS20]
-/

@[expose] public section

namespace BatchedFri.Spec.BatchingRound

open Domain OracleSpec OracleComp ProtocolSpec Finset
open scoped NNReal ENNReal ProbabilityTheory

variable {F : Type} [NonBinaryField F] [Fintype F] [DecidableEq F]
variable {n k : ℕ} {ω : SmoothCosetFftDomain n F}
variable (s : Fin (k + 1) → ℕ+) (d : ℕ+) (m : ℕ)
variable {S : Type}
variable (G : CoreDefinitions.Generator S (Fin (m + 1)) F)

/-- Indexed view of the batched input words on the initial evaluation domain. -/
def inputWords (os : ∀ j, OracleStatement m ω j) : Fin (m + 1) → Fin (2 ^ n) → F :=
  fun i z ↦ os i ⟨ω z, CosetFftDomain.mem_toFinset_self⟩

/-- The virtual word is the generated combination on the original evaluation domain. -/
theorem initialOracle_combinedOracle (cs : S)
    (os : ∀ j, OracleStatement m ω j) (z : Fin (2 ^ n)) :
    Fri.Spec.initialOracle s (Fin.elim0, combinedOracle s m G cs os) (Fri.Spec.initialQuery z) =
      ∑ i, G cs i * inputWords m os i z := by
  change combinedOracle s m G cs os 0 (Fri.Spec.initialQuery z) = _
  simp only [combinedOracle, inputWords, ← List.ofFn_eq_map, List.sum_ofFn]
  rfl

omit [Fintype F] in
/-- Evaluation commutes with the honest polynomial combination. -/
theorem eval_combinedWitness (cs : S) (ps : Witness F s d m) (x : F) :
    (combinedWitness s d m G cs ps).1.eval x =
      ∑ i, G cs i * (ps i).1.eval x := by
  simp [combinedWitness]

/-- Every challenge preserves the radius and the common agreement set, with the exact
combined polynomial as the output witness. -/
theorem combined_mem_outputRelation
    (hdom : 2 ^ (∑ i, (s i).1) * d ≤ 2 ^ n) (δ : ℝ≥0)
    (stmt : Unit × ∀ j, OracleStatement m ω j) (ps : Witness F s d m)
    (hin : (stmt, ps) ∈ inputRelation s d m δ) (cs : S) :
    ((Fin.elim0, combinedOracle s m G cs stmt.2), combinedWitness s d m G cs ps) ∈
      outputRelation s d hdom δ := by
  obtain ⟨S, hS, hagree⟩ := hin
  change ∀ i, ∀ z ∈ S,
    stmt.2 i ⟨ω z, CosetFftDomain.mem_toFinset_self⟩ = (ps i).1.eval (ω z) at hagree
  apply Fri.Spec.mem_inputRelation_of_relHammingDist_le
  have hclose : Code.relHammingDist
      (fun z ↦ Fri.Spec.initialOracle s (Fin.elim0, combinedOracle s m G cs stmt.2)
        (Fri.Spec.initialQuery z))
      (fun z ↦ (combinedWitness s d m G cs ps).1.eval (ω z)) ≤ δ := by
    apply (Code.relCloseToWord_iff_exists_agreementCols _ _ δ).2
    refine ⟨S, (Code.relDist_floor_bound_iff_complement_bound _ _ δ).2 hS, ?_⟩
    intro z
    have hz : z ∈ S →
        Fri.Spec.initialOracle s (Fin.elim0, combinedOracle s m G cs stmt.2)
          (Fri.Spec.initialQuery z) = (combinedWitness s d m G cs ps).1.eval (ω z) :=
      fun hz ↦ by
      rw [initialOracle_combinedOracle, eval_combinedWitness]
      simp only [inputWords]
      apply Finset.sum_congr rfl
      intro i _
      rw [hagree i z hz]
    exact ⟨hz, fun hne hzS ↦ hne (hz hzS)⟩
  exact_mod_cast hclose

/-- The batching verifier is pure, including materialization of its virtual output oracle. -/
def batchPureForm : (batchVerifier (ω := ω) s m G).toVerifier.PureForm where
  verify := fun stmt tr ↦
    (Fin.elim0, combinedOracle s m G (tr.challenges ⟨0, by simp⟩) stmt.2)
  verify_eq := by
    intro stmt tr
    rfl

instance : (batchVerifier (ω := ω) s m G).toVerifier.IsPure :=
  (batchPureForm s m G).isPure

omit [Fintype F] in
/-- Correlated agreement supplies all of the polynomial witnesses in the input language. -/
theorem mem_inputLanguage_of_jointAgreement (δ : ℝ≥0)
    (stmt : Unit × ∀ j, OracleStatement m ω j)
    (h : Code.jointAgreement
      ((ReedSolomon.code (ω : Fin (2 ^ n) ↪ F) (2 ^ (∑ i, (s i).1) * d)).carrier) δ
      (inputWords m stmt.2)) :
    stmt ∈ (inputRelation (ω := ω) s d m δ).language := by
  classical
  obtain ⟨S, hS, v, hv⟩ := h
  have hp (i) := ReedSolomon.mem_code_iff_exists_polynomial.mp (hv i).1
  choose p hpdeg hpeval using hp
  let pc (i) : CompPoly.CPolynomial F :=
    ⟨(p i).toImpl, CompPoly.CPolynomial.Raw.isCanonical_toImpl (p i)⟩
  have hpc (i) : (pc i).toPoly = p i := CompPoly.CPolynomial.toPoly_mk_toImpl (p i)
  let ps : Witness F s d m := fun i ↦ ⟨pc i, by
    rw [CompPoly.CPolynomial.degreeLT_toPoly, Polynomial.mem_degreeLT, hpc]
    exact hpdeg i⟩
  rw [Set.mem_language_iff]
  refine ⟨ps, S, hS, ?_⟩
  intro i z hz
  have heq := (Finset.mem_filter.mp ((hv i).2 hz)).2
  rw [hpeval i] at heq
  change stmt.2 i (ω.equivToFinset z) = (pc i).eval (ω z)
  rw [CompPoly.CPolynomial.eval_toPoly (ω z) (pc i), hpc]
  exact heq.symm

/-- Membership in the FRI output language implies closed-ball proximity of the generated word
on the original evaluation domain, with the actual initial degree bound. -/
theorem close_of_mem_outputLanguage
    (hdom : 2 ^ (∑ i, (s i).1) * d ≤ 2 ^ n) (δ : ℝ≥0)
    (os : ∀ j, OracleStatement m ω j) (cs : S)
    (h : (Fin.elim0, combinedOracle s m G cs os) ∈
      (outputRelation (ω := ω) s d hdom δ).language) :
    Code.relDistFromCode (∑ i, G cs i • inputWords m os i)
      ((ReedSolomon.code (ω : Fin (2 ^ n) ↪ F)
        (2 ^ (∑ i, (s i).1) * d)).carrier) ≤ δ := by
  obtain ⟨p, hp⟩ := (Set.mem_language_iff _ _).mp h
  have hprox := Fri.Spec.relHammingDist_le_of_mem_inputRelation s d hdom δ
    (Fin.elim0, combinedOracle s m G cs os) p hp
  have heval : (fun z ↦ p.1.eval (ω z)) ∈
      ReedSolomon.code (ω : Fin (2 ^ n) ↪ F) (2 ^ (∑ i, (s i).1) * d) := by
    apply ReedSolomon.mem_code_iff_eval.mpr
    refine ⟨p.1.toPoly, ?_, ?_⟩
    · have hd := (CompPoly.CPolynomial.degreeLT_toPoly.mp p.2)
      simpa [Fri.Spec.Witness, Polynomial.mem_degreeLT, finRangeTo] using hd
    · intro z
      exact (CompPoly.CPolynomial.eval_toPoly (ω z) p.1).symm
  apply (Code.relCloseToCode_iff_relCloseToCodeword_of_minDist _ δ).2
  refine ⟨_, heval, ?_⟩
  have hf : (fun z ↦ Fri.Spec.initialOracle s (Fin.elim0, combinedOracle s m G cs os)
      (Fri.Spec.initialQuery z)) = ∑ i, G cs i • inputWords m os i := by
    funext z
    rw [initialOracle_combinedOracle]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [hf] at hprox
  exact_mod_cast hprox

variable [SampleableType S]

/-- The sole challenge samples the generator seed uniformly. -/
noncomputable instance instSampleableTypeChallenge :
    ∀ j, SampleableType ((batchSpec S).Challenge j) := by
  rintro ⟨j, hj⟩
  have hzero : j = 0 := Fin.eq_zero j
  subst j
  change SampleableType S
  infer_instance

omit [SampleableType S] in
/-- The honest prover receives the seed and returns the combined polynomial. -/
theorem batchProver_run (stmt : Unit × ∀ j, OracleStatement m ω j)
    (ps : Witness F s d m) :
    (batchProver s d m G).run stmt ps = (do
      let cs ← (batchSpec S).getChallenge ⟨0, rfl⟩
      pure (((default : (batchSpec S).Transcript 0).concat
        (m := (0 : Fin 1)) cs),
        (Fin.elim0, combinedOracle s m G cs stmt.2), combinedWitness s d m G cs ps)) := by
  unfold Prover.run
  erw [Prover.runToRound_succ (0 : Fin 1)]
  erw [Prover.processRound_of_dir_eq_V_to_P (0 : Fin 1) rfl]
  simp [Prover.runToRound_zero_of_prover_first, batchProver]

/-- The honest execution preserves the relation with probability one for every radius. -/
theorem perfect_completeness
    (hdom : 2 ^ (∑ i, (s i).1) * d ≤ 2 ^ n) (δ : ℝ≥0)
    {σ : Type} (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    (batchOracleReduction (ω := ω) s d m G).perfectCompleteness init impl
      (inputRelation s d m δ) (outputRelation s d hdom δ) := by
  change (batchOracleReduction (ω := ω) s d m G).toReduction.completeness _ _ _ _ 0
  rw [Reduction.completeness_iff_of_guarded_verifier _
    (batchPureForm s m G).toGuardedForm]
  intro stmt ps hin
  have hrun := batchProver_run s d m G stmt ps
  have hget := simulateQ_addLift_challengeQueryImpl_getChallenge
    (pSpec := batchSpec S) impl ⟨0, rfl⟩
  change _ ≤ Pr{let q ← (do
    (simulateQ (impl.addLift challengeQueryImpl : QueryImpl _ (StateT σ ProbComp))
      ((batchProver s d m G).run stmt ps)).run (← init))}[_]
  rw [hrun]
  simp only [simulateQ_bind, simulateQ_pure]
  erw [hget]
  simp only [ENNReal.coe_zero, tsub_zero, Fin.coe_ofNat_eq_mod, Nat.zero_mod,
    Nat.reduceAdd, Fin.vcons_of_one, Fin.isValue, Challenge, bind_pure_comp,
    StateT.run_map, StateT.run_monadLift, monadLift_self, Functor.map_map,
    map_bind, _root_.prEvent_bind_const, prEvent_true_eq_one, one_mul,
    batchPureForm, Verifier.PureForm.toGuardedForm, FullTranscript.challenges,
    Transcript.concat_zero, true_and, and_true]
  apply le_of_eq
  symm
  rw [SampleableType.prEvent_uniformSample_eq_one_iff]
  intro cs
  exact combined_mem_outputRelation s d m G hdom δ stmt ps hin cs

/-- A generator's correlated-agreement error bounds the probability that an invalid
batch reaches the FRI input language, at every radius. -/
theorem batching_error
    (hdom : 2 ^ (∑ i, (s i).1) * d ≤ 2 ^ n) (δ ε : ℝ≥0)
    (hε : ProximityGap.caError G
      (ReedSolomon.code (ω : Fin (2 ^ n) ↪ F) (2 ^ (∑ i, (s i).1) * d)).carrier δ δ ≤ ε)
    (stmt : Unit × ∀ j, OracleStatement m ω j)
    (hnot : stmt ∉ (inputRelation (ω := ω) s d m δ).language) :
    Pr{let cs ← $ᵗ S}[
      (Fin.elim0, combinedOracle s m G cs stmt.2) ∈
        (outputRelation (ω := ω) s d hdom δ).language] ≤ ε := by
  apply le_trans (prEvent_mono _ _ _ (fun cs h ↦
    close_of_mem_outputLanguage s d m G hdom δ stmt.2 cs h))
  apply le_trans (ProximityGap.prob_le_caError G _ (inputWords m stmt.2) δ δ ?_) hε
  intro h
  exact hnot (mem_inputLanguage_of_jointAgreement s d m δ stmt
    ((Code.jointAgreement_iff_jointProximity _ _ _).mpr h))

/-- Before the sole challenge the certificate is input-language membership; afterward it
is membership of the verifier's deterministic output in the output language. -/
def batchStateFunction
    (hdom : 2 ^ (∑ i, (s i).1) * d ≤ 2 ^ n) (δ : ℝ≥0)
    {σ : Type} (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    (batchVerifier (ω := ω) s m G).toVerifier.StateFunction init impl
      (inputRelation s d m δ).language (outputRelation s d hdom δ).language where
  toFun
    | 0, stmt, _ => stmt ∈ (inputRelation s d m δ).language
    | 1, stmt, tr => (batchPureForm s m G).verify stmt tr ∈
        (outputRelation s d hdom δ).language
  toFun_empty := fun _ h ↦ h
  toFun_next := by
    intro i hi
    have hz : i = 0 := Fin.eq_zero i
    subst i
    contradiction
  toFun_full := by
    intro stmt tr hnot
    apply le_antisymm _ zero_le
    apply le_of_not_gt
    intro hpos
    have hp := ((batchPureForm s m G).toGuardedForm.prEvent_pos_iff
      stmt tr (fun out ↦ out ∈ (outputRelation s d hdom δ).language)).mp hpos
    exact hnot hp.2

/-- Round-by-round soundness for the batching verifier. There are no prover
messages; the only transition is the uniformly sampled seed. -/
theorem round_soundness
    (hdom : 2 ^ (∑ i, (s i).1) * d ≤ 2 ^ n) (δ ε : ℝ≥0)
    (hε : ProximityGap.caError G
      (ReedSolomon.code (ω : Fin (2 ^ n) ↪ F) (2 ^ (∑ i, (s i).1) * d)).carrier δ δ ≤ ε)
    {σ : Type} (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    (batchVerifier (ω := ω) s m G).toVerifier.rbrSoundness init impl
      (inputRelation s d m δ).language (outputRelation s d hdom δ).language
      (fun _ ↦ ε) := by
  classical
  refine ⟨batchStateFunction s d m G hdom δ init impl, ?_⟩
  intro stmt hnot ⟨i, hi⟩ tr
  have hz : i = 0 := Fin.eq_zero i
  subst i
  let : SampleableType ((batchSpec S).Challenge ⟨0, hi⟩) :=
    instSampleableTypeChallenge (S := S) ⟨0, hi⟩
  change Pr{let cs ← $ᵗ ((batchSpec S).Challenge ⟨0, hi⟩)}[
    ¬ stmt ∈ (inputRelation s d m δ).language ∧
      (Fin.elim0, combinedOracle s m G cs stmt.2) ∈
        (outputRelation s d hdom δ).language] ≤ _
  simp only [hnot, not_false_eq_true, true_and]
  have heq := @SampleableType.prEvent_uniformSample_equiv
    ((batchSpec S).Challenge ⟨0, hi⟩) S
    (instSampleableTypeChallenge (S := S) ⟨0, hi⟩) inferInstance (Equiv.refl _)
    (fun cs ↦ (Fin.elim0, combinedOracle s m G cs stmt.2) ∈
      (outputRelation s d hdom δ).language)
  exact heq.trans_le (batching_error s d m G hdom δ ε hε stmt hnot)

/-- Ordinary soundness against any prover, with any bound on the generator-indexed CA error. -/
theorem soundness
    (hdom : 2 ^ (∑ i, (s i).1) * d ≤ 2 ^ n) (δ ε : ℝ≥0)
    (hε : ProximityGap.caError G
      (ReedSolomon.code (ω : Fin (2 ^ n) ↪ F) (2 ^ (∑ i, (s i).1) * d)).carrier δ δ ≤ ε)
    {σ : Type} (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    (batchVerifier (ω := ω) s m G).soundness init impl
      (inputRelation s d m δ).language (outputRelation s d hdom δ).language
      (ε) := by
  let : Unique (batchSpec S).ChallengeIdx :=
    { default := ⟨0, rfl⟩
      uniq := fun j ↦ Subtype.ext (Fin.eq_zero j.1) }
  have h := (batchPureForm (ω := ω) s m G).toGuardedForm.soundness_of_rbrSoundness
    (round_soundness s d m G hdom δ ε hε init impl)
  simpa only [OracleVerifier.soundness, Finset.sum_const, Finset.card_univ,
    Fintype.card_unique, one_nsmul] using h


omit [SampleableType S] in
/-- affineSpace specialization of `batching_error`, with the BCIKS20 error. -/
theorem batching_error_affineSpace [SampleableType F]
    (hdom : 2 ^ (∑ i, (s i).1) * d ≤ 2 ^ n) (δ : ℝ≥0)
    (hδ_pos : 0 < δ)
    (hδ : δ < 1 - ReedSolomon.sqrtRate (2 ^ (∑ i, (s i).1) * d)
      (ω : Fin (2 ^ n) ↪ F))
    (stmt : Unit × ∀ j, OracleStatement m ω j)
    (hnot : stmt ∉ (inputRelation (ω := ω) s d m δ).language) :
    Pr{let cs ← $ᵗ (Fin m → F)}[
      (Fin.elim0, combinedOracle s m (CoreDefinitions.AffineSpaceGenerator F m) cs stmt.2) ∈
        (outputRelation (ω := ω) s d hdom δ).language] ≤
      (ProximityGap.errorBound δ (2 ^ (∑ i, (s i).1) * d)
        (ω : Fin (2 ^ n) ↪ F) : ℝ≥0) := by
  exact batching_error s d m (CoreDefinitions.AffineSpaceGenerator F m) hdom δ _
    (ProximityGap.caError_affineSpace_le m (by positivity) hδ_pos hδ) stmt hnot
omit [SampleableType S] in
/-- affineSpace specialization of `round_soundness`, with the BCIKS20 error. -/
theorem round_soundness_affineSpace [SampleableType F]
    (hdom : 2 ^ (∑ i, (s i).1) * d ≤ 2 ^ n) (δ : ℝ≥0)
    (hδ_pos : 0 < δ)
    (hδ : δ < 1 - ReedSolomon.sqrtRate (2 ^ (∑ i, (s i).1) * d)
      (ω : Fin (2 ^ n) ↪ F))
    {σ : Type} (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    (batchVerifier (ω := ω) s m
      (CoreDefinitions.AffineSpaceGenerator F m)).toVerifier.rbrSoundness
      init impl
      (inputRelation s d m δ).language (outputRelation s d hdom δ).language
      (fun _ ↦ ProximityGap.errorBound δ (2 ^ (∑ i, (s i).1) * d) (ω : Fin (2 ^ n) ↪ F)) := by
  exact round_soundness s d m (CoreDefinitions.AffineSpaceGenerator F m) hdom δ _
    (ProximityGap.caError_affineSpace_le m (by positivity) hδ_pos hδ) init impl
omit [SampleableType S] in
/-- affineSpace specialization of `soundness`, with the BCIKS20 error. -/
theorem soundness_affineSpace [SampleableType F]
    (hdom : 2 ^ (∑ i, (s i).1) * d ≤ 2 ^ n) (δ : ℝ≥0)
    (hδ_pos : 0 < δ)
    (hδ : δ < 1 - ReedSolomon.sqrtRate (2 ^ (∑ i, (s i).1) * d)
      (ω : Fin (2 ^ n) ↪ F))
    {σ : Type} (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    (batchVerifier (ω := ω) s m (CoreDefinitions.AffineSpaceGenerator F m)).soundness init impl
      (inputRelation s d m δ).language (outputRelation s d hdom δ).language
      (ProximityGap.errorBound δ (2 ^ (∑ i, (s i).1) * d) (ω : Fin (2 ^ n) ↪ F)) := by
  exact soundness s d m (CoreDefinitions.AffineSpaceGenerator F m) hdom δ _
    (ProximityGap.caError_affineSpace_le m (by positivity) hδ_pos hδ) init impl
omit [SampleableType S] in
/-- powers specialization of `batching_error`, with the BCIKS20 error. -/
theorem batching_error_powers [SampleableType F]
    (hdom : 2 ^ (∑ i, (s i).1) * d ≤ 2 ^ n) (δ : ℝ≥0)
    (hδ_pos : 0 < δ)
    (hδ : δ < 1 - ReedSolomon.sqrtRate (2 ^ (∑ i, (s i).1) * d)
      (ω : Fin (2 ^ n) ↪ F))
    (stmt : Unit × ∀ j, OracleStatement m ω j)
    (hnot : stmt ∉ (inputRelation (ω := ω) s d m δ).language) :
    Pr{let cs ← $ᵗ F}[
      (Fin.elim0, combinedOracle s m (CoreDefinitions.univariatePowersGenerator F m) cs stmt.2) ∈
        (outputRelation (ω := ω) s d hdom δ).language] ≤
      (m * ProximityGap.errorBound δ (2 ^ (∑ i, (s i).1) * d)
        (ω : Fin (2 ^ n) ↪ F) : ℝ≥0) := by
  exact batching_error s d m (CoreDefinitions.univariatePowersGenerator F m) hdom δ _
    (ProximityGap.caError_powers_le m (by positivity) hδ_pos hδ) stmt hnot
omit [SampleableType S] in
/-- powers specialization of `round_soundness`, with the BCIKS20 error. -/
theorem round_soundness_powers [SampleableType F]
    (hdom : 2 ^ (∑ i, (s i).1) * d ≤ 2 ^ n) (δ : ℝ≥0)
    (hδ_pos : 0 < δ)
    (hδ : δ < 1 - ReedSolomon.sqrtRate (2 ^ (∑ i, (s i).1) * d)
      (ω : Fin (2 ^ n) ↪ F))
    {σ : Type} (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    (batchVerifier (ω := ω) s m
      (CoreDefinitions.univariatePowersGenerator F m)).toVerifier.rbrSoundness
      init impl
      (inputRelation s d m δ).language (outputRelation s d hdom δ).language
      (fun _ ↦ m * ProximityGap.errorBound δ (2 ^ (∑ i, (s i).1) * d) (ω : Fin (2 ^ n) ↪ F)) := by
  exact round_soundness s d m (CoreDefinitions.univariatePowersGenerator F m) hdom δ _
    (ProximityGap.caError_powers_le m (by positivity) hδ_pos hδ) init impl
omit [SampleableType S] in
/-- powers specialization of `soundness`, with the BCIKS20 error. -/
theorem soundness_powers [SampleableType F]
    (hdom : 2 ^ (∑ i, (s i).1) * d ≤ 2 ^ n) (δ : ℝ≥0)
    (hδ_pos : 0 < δ)
    (hδ : δ < 1 - ReedSolomon.sqrtRate (2 ^ (∑ i, (s i).1) * d)
      (ω : Fin (2 ^ n) ↪ F))
    {σ : Type} (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    (batchVerifier (ω := ω) s m (CoreDefinitions.univariatePowersGenerator F m)).soundness init impl
      (inputRelation s d m δ).language (outputRelation s d hdom δ).language
      (m * ProximityGap.errorBound δ (2 ^ (∑ i, (s i).1) * d) (ω : Fin (2 ^ n) ↪ F)) := by
  exact soundness s d m (CoreDefinitions.univariatePowersGenerator F m) hdom δ _
    (ProximityGap.caError_powers_le m (by positivity) hδ_pos hδ) init impl



omit [SampleableType S] in
/-- Multilinear batching has error `t * n / |F|` in the unique-decoding regime,
using the proved affine-line MCA bound and additive tensor composition. -/
theorem round_soundness_multilinear [SampleableType F] (t : ℕ)
    (hdom : 2 ^ (∑ i, (s i).1) * d ≤ 2 ^ n) (δ : ℝ≥0)
    (hδ_pos : 0 < δ)
    (hδ : δ ≤ Code.relativeUniqueDecodingRadius
      (ReedSolomon.code (ω : Fin (2 ^ n) ↪ F) (2 ^ (∑ i, (s i).1) * d)).carrier)
    {σ : Type} (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    (batchVerifier (ω := ω) s (2 ^ t - 1)
      (CoreDefinitions.multilinearBatchGenerator F t)).toVerifier.rbrSoundness
      init impl
      (inputRelation s d (2 ^ t - 1) δ).language (outputRelation s d hdom δ).language
      (fun _ ↦ t * (2 ^ n / Fintype.card F)) := by
  exact round_soundness s d (2 ^ t - 1) (CoreDefinitions.multilinearBatchGenerator F t)
    hdom δ _ (by simpa using ProximityGap.caError_multilinearBatch_le t hδ_pos hδ) init impl

omit [SampleableType S] in
/-- Multilinear batching has error `t * n / |F|` in the unique-decoding regime,
using the proved affine-line MCA bound and additive tensor composition. -/
theorem soundness_multilinear [SampleableType F] (t : ℕ)
    (hdom : 2 ^ (∑ i, (s i).1) * d ≤ 2 ^ n) (δ : ℝ≥0)
    (hδ_pos : 0 < δ)
    (hδ : δ ≤ Code.relativeUniqueDecodingRadius
      (ReedSolomon.code (ω : Fin (2 ^ n) ↪ F) (2 ^ (∑ i, (s i).1) * d)).carrier)
    {σ : Type} (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    (batchVerifier (ω := ω) s (2 ^ t - 1)
      (CoreDefinitions.multilinearBatchGenerator F t)).soundness init impl
      (inputRelation s d (2 ^ t - 1) δ).language (outputRelation s d hdom δ).language
      (t * (2 ^ n / Fintype.card F)) := by
  exact soundness s d (2 ^ t - 1) (CoreDefinitions.multilinearBatchGenerator F t)
    hdom δ _ (by simpa using ProximityGap.caError_multilinearBatch_le t hδ_pos hδ) init impl



omit [SampleableType S] in
/-- Multilinear batching using the proved 1.5-Johnson MCA bound. -/
theorem soundness_multilinear_johnson [SampleableType F] (t : ℕ)
    (hdom : 2 ^ (∑ i, (s i).val) * d ≤ 2 ^ n)
    (δ_min η δ : ℝ≥0)
    (hdist : (δ_min : ℝ) = (Code.minDist
      (ReedSolomon.code (ω : Fin (2 ^ n) ↪ F)
        (2 ^ (∑ i, (s i).val) * d)).carrier : ℝ) / Fintype.card (Fin (2 ^ n)))
    (hη : 0 < η) (hη_lt : η < δ_min) (hδ_pos : 0 < δ)
    (hδ : (δ : ℝ) ≤ 1 - (1 - (δ_min : ℝ) + (η : ℝ)) ^ ((1 : ℝ) / 3))
    {σ : Type} (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    (batchVerifier (ω := ω) s (2 ^ t - 1)
      (CoreDefinitions.multilinearBatchGenerator F t)).soundness init impl
      (inputRelation s d (2 ^ t - 1) δ).language (outputRelation s d hdom δ).language
      (t * ProximityGap.affineLineMcaJohnsonError (2 ^ n) (Fintype.card F) δ_min η) := by
  exact soundness s d (2 ^ t - 1) (CoreDefinitions.multilinearBatchGenerator F t)
    hdom δ _ (by
      simpa only [Fintype.card_fin, PNat.val] using
        ProximityGap.caError_multilinearBatch_le_johnson t
          (ReedSolomon.code (ω : Fin (2 ^ n) ↪ F) (2 ^ (∑ i, (s i).val) * d))
          δ_min η δ hdist hη hη_lt hδ_pos hδ) init impl

end BatchedFri.Spec.BatchingRound

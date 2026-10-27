/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.ProofSystem.BatchedFri.Spec.General
public import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.AffineSpaces
public import ArkLib.OracleReduction.Composition.Sequential.GuardedCompleteness
public import ArkLib.OracleReduction.Security.GuardedSoundness

/-!
# Security of the batching round

The honest linear combination preserves the common agreement set. Soundness uses the
correlated-agreement bound for affine spaces from [BCIKS20] at the initial FRI degree bound.
The virtual output word is determined entirely by the input words and verifier coefficients.

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

/-- Indexed view of the batched input words on the initial evaluation domain. -/
def inputWords (os : ∀ j, OracleStatement m ω j) : Fin (m + 1) → Fin (2 ^ n) → F :=
  fun i z ↦ os i ⟨ω z, CosetFftDomain.mem_toFinset_self⟩

/-- The virtual word is the affine combination on the original evaluation domain. -/
theorem initialOracle_combinedOracle (cs : Fin m → F)
    (os : ∀ j, OracleStatement m ω j) (z : Fin (2 ^ n)) :
    Fri.Spec.initialOracle s (Fin.elim0, combinedOracle s m cs os) (Fri.Spec.initialQuery z) =
      inputWords m os 0 z + ∑ i, cs i * inputWords m os i.succ z := by
  change combinedOracle s m cs os 0 (Fri.Spec.initialQuery z) = _
  simp only [combinedOracle, inputWords, ← List.ofFn_eq_map, List.sum_ofFn]
  rfl

omit [Fintype F] in
/-- Evaluation commutes with the honest polynomial combination. -/
theorem eval_combinedWitness (cs : Fin m → F) (ps : Witness F s d m) (x : F) :
    (combinedWitness s d m cs ps).1.eval x =
      (ps 0).1.eval x + ∑ i, cs i * (ps i.succ).1.eval x := by
  simp [combinedWitness]

/-- Every challenge preserves the radius and the common agreement set, with the exact
combined polynomial as the output witness. -/
theorem combined_mem_outputRelation
    (hdom : 2 ^ (∑ i, (s i).1) * d ≤ 2 ^ n) (δ : ℝ≥0)
    (stmt : Unit × ∀ j, OracleStatement m ω j) (ps : Witness F s d m)
    (hin : (stmt, ps) ∈ inputRelation s d m δ) (cs : Fin m → F) :
    ((Fin.elim0, combinedOracle s m cs stmt.2), combinedWitness s d m cs ps) ∈
      outputRelation s d hdom δ := by
  obtain ⟨S, hS, hagree⟩ := hin
  change ∀ i, ∀ z ∈ S,
    stmt.2 i ⟨ω z, CosetFftDomain.mem_toFinset_self⟩ = (ps i).1.eval (ω z) at hagree
  apply Fri.Spec.mem_inputRelation_of_relHammingDist_le
  have hclose : Code.relHammingDist
      (fun z ↦ Fri.Spec.initialOracle s (Fin.elim0, combinedOracle s m cs stmt.2)
        (Fri.Spec.initialQuery z))
      (fun z ↦ (combinedWitness s d m cs ps).1.eval (ω z)) ≤ δ := by
    apply (Code.relCloseToWord_iff_exists_agreementCols _ _ δ).2
    refine ⟨S, (Code.relDist_floor_bound_iff_complement_bound _ _ δ).2 hS, ?_⟩
    intro z
    have hz : z ∈ S →
        Fri.Spec.initialOracle s (Fin.elim0, combinedOracle s m cs stmt.2)
          (Fri.Spec.initialQuery z) = (combinedWitness s d m cs ps).1.eval (ω z) :=
      fun hz ↦ by
      rw [initialOracle_combinedOracle, eval_combinedWitness]
      simp only [inputWords]
      rw [hagree 0 z hz]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      rw [hagree i.succ z hz]
    exact ⟨hz, fun hne hzS ↦ hne (hz hzS)⟩
  exact_mod_cast hclose

/-- The batching verifier is pure, including materialization of its virtual output oracle. -/
def batchPureForm : (batchVerifier (ω := ω) s m).toVerifier.PureForm where
  verify := fun stmt tr ↦
    (Fin.elim0, combinedOracle s m (tr.challenges ⟨0, by simp⟩) stmt.2)
  verify_eq := by
    intro stmt tr
    rfl

instance : (batchVerifier (ω := ω) s m).toVerifier.IsPure :=
  (batchPureForm s m).isPure

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

/-- Membership in the FRI output language implies closed-ball proximity of the affine word
on the original evaluation domain, with the actual initial degree bound. -/
theorem close_of_mem_outputLanguage
    (hdom : 2 ^ (∑ i, (s i).1) * d ≤ 2 ^ n) (δ : ℝ≥0)
    (os : ∀ j, OracleStatement m ω j) (cs : Fin m → F)
    (h : (Fin.elim0, combinedOracle s m cs os) ∈
      (outputRelation (ω := ω) s d hdom δ).language) :
    Code.relDistFromCode (inputWords m os 0 + ∑ i, cs i • inputWords m os i.succ)
      ((ReedSolomon.code (ω : Fin (2 ^ n) ↪ F)
        (2 ^ (∑ i, (s i).1) * d)).carrier) ≤ δ := by
  obtain ⟨p, hp⟩ := (Set.mem_language_iff _ _).mp h
  have hprox : Code.relHammingDist
      (Fri.Spec.initialOracle s (Fin.elim0, combinedOracle s m cs os))
      (fun x ↦ p.1.eval x.1) ≤ δ := by
    cases k <;> exact hp
  let e := (ω.subdomain 0).equivToFinset
  have he (z : Fin (2 ^ n)) : e z = Fri.Spec.initialQuery z := by
    apply Subtype.ext
    simp [e, Fri.Spec.initialQuery, CosetFftDomain.subdomain_zero_eq_self]
  have hdist : Code.relHammingDist
      ((Fri.Spec.initialOracle s (Fin.elim0, combinedOracle s m cs os)) ∘ e)
      ((fun x : (ω.subdomain 0).toFinset ↦ p.1.eval x.val) ∘ e) =
      Code.relHammingDist
        (Fri.Spec.initialOracle s (Fin.elim0, combinedOracle s m cs os))
        (fun x ↦ p.1.eval x.val) := by
    unfold Code.relHammingDist
    rw [hammingDist_comp_equiv, Fintype.card_congr e]
  rw [← hdist] at hprox
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
  have hf : (Fri.Spec.initialOracle s (Fin.elim0, combinedOracle s m cs os)) ∘ e =
      inputWords m os 0 + ∑ i, cs i • inputWords m os i.succ := by
    funext z
    rw [Function.comp_apply, he, initialOracle_combinedOracle]
    simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  have hp' : (fun x : (ω.subdomain 0).toFinset ↦ p.1.eval x.val) ∘ e =
      (fun z ↦ p.1.eval (ω z)) := by
    funext z
    rw [Function.comp_apply, he]
    rfl
  rwa [hf, hp'] at hprox

variable [SampleableType F]

/-- The sole challenge samples all batching coefficients uniformly. -/
noncomputable instance instSampleableTypeChallenge :
    ∀ j, SampleableType ((batchSpec F m).Challenge j) := by
  rintro ⟨j, hj⟩
  have hzero : j = 0 := Fin.eq_zero j
  subst j
  change SampleableType (Fin m → F)
  infer_instance

omit [SampleableType F] in
/-- The honest prover receives the coefficients and returns the combined polynomial. -/
theorem batchProver_run (stmt : Unit × ∀ j, OracleStatement m ω j)
    (ps : Witness F s d m) :
    (batchProver s d m).run stmt ps = (do
      let cs ← (batchSpec F m).getChallenge ⟨0, rfl⟩
      pure (((default : (batchSpec F m).Transcript 0).concat
        (m := (0 : Fin 1)) cs),
        (Fin.elim0, combinedOracle s m cs stmt.2), combinedWitness s d m cs ps)) := by
  unfold Prover.run
  erw [Prover.runToRound_succ (0 : Fin 1)]
  erw [Prover.processRound_of_dir_eq_V_to_P (0 : Fin 1) rfl]
  simp [Prover.runToRound_zero_of_prover_first, batchProver]

/-- The honest execution preserves the relation with probability one for every radius. -/
theorem perfect_completeness
    (hdom : 2 ^ (∑ i, (s i).1) * d ≤ 2 ^ n) (δ : ℝ≥0)
    {σ : Type} (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    (batchOracleReduction (ω := ω) s d m).perfectCompleteness init impl
      (inputRelation s d m δ) (outputRelation s d hdom δ) := by
  change (batchOracleReduction (ω := ω) s d m).toReduction.completeness _ _ _ _ 0
  rw [Reduction.completeness_iff_of_guarded_verifier _
    (batchPureForm s m).toGuardedForm]
  intro stmt ps hin
  have hrun := batchProver_run s d m stmt ps
  have hget := simulateQ_addLift_challengeQueryImpl_getChallenge
    (pSpec := batchSpec F m) impl ⟨0, rfl⟩
  change _ ≤ Pr{let q ← (do
    (simulateQ (impl.addLift challengeQueryImpl : QueryImpl _ (StateT σ ProbComp))
      ((batchProver s d m).run stmt ps)).run (← init))}[_]
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
  exact combined_mem_outputRelation s d m hdom δ stmt ps hin cs

/-- Uniform coefficients induce the uniform distribution on their affine image, including
linearly dependent and zero directions. The fibers are translates of the kernel. -/
theorem uniform_affine_combination {ι : Type} [Fintype ι] [DecidableEq ι]
    (u : Fin (m + 1) → ι → F) (P : (ι → F) → Prop) :
    Pr{let cs ← $ᵗ (Fin m → F)}[P (u 0 + ∑ i, cs i • u i.succ)] =
    Pr{let y ← $ᵗ ↥(Affine.affineSubspaceAtOrigin (F := F) (u 0) (Fin.tail u))}[
      P y.1] := by
  classical
  let L : (Fin m → F) →ₗ[F] (ι → F) :=
    { toFun := fun c ↦ ∑ i, c i • u i.succ
      map_add' := by intro a b; simp [add_smul, sum_add_distrib]
      map_smul' := by intro a b; simp [Finset.smul_sum, smul_smul] }
  let U := ↥(Affine.affineSubspaceAtOrigin (F := F) (u 0) (Fin.tail u))
  have lift_exists (y : U) : ∃ c, y.1 = u 0 + L c :=
    (Affine.mem_affineSubspaceFrom_iff _ _ _).mp y.2
  let t : U → (Fin m → F) := fun y ↦ (lift_exists y).choose
  have ht (y : U) : y.1 = u 0 + L (t y) := (lift_exists y).choose_spec
  let f : (Fin m → F) → U := fun c ↦
    ⟨u 0 + L c, (Affine.mem_affineSubspaceFrom_iff _ _ _).mpr ⟨c, rfl⟩⟩
  let e : (Fin m → F) ≃ U × L.ker :=
    { toFun := fun c ↦ (f c, ⟨c - t (f c), by
        change L (c - t (f c)) = 0
        rw [map_sub, sub_eq_zero]
        exact add_left_cancel (ht (f c))⟩)
      invFun := fun y ↦ t y.1 + y.2.1
      left_inv := by intro c; dsimp; abel
      right_inv := by
        rintro ⟨y, z⟩
        have hf : f (t y + z.1) = y := by
          apply Subtype.ext
          change u 0 + L (t y + z.1) = y.1
          rw [map_add, z.2, add_zero, ← ht]
        apply Prod.ext
        · exact hf
        · apply Subtype.ext
          change t y + z.1 - t (f (t y + z.1)) = z.1
          rw [hf]; abel }
  have h := SampleableType.prEvent_uniformSample_equiv e (fun y ↦ P y.1.1)
  change Pr{let c ← $ᵗ (Fin m → F)}[P (u 0 + L c)] = _
  change Pr{let c ← $ᵗ (Fin m → F)}[P (e c).1.1] = _
  rw [h, SampleableType.prEvent_uniformSample_prod]
  simp only [prEvent_norm]
  conv_rhs => rw [← bind_pure_comp]
  apply OracleComp.prEvent_bind_congr_of_support
  intro x _
  simpa only [bind_pure_comp] using
    OracleComp.prEvent_bind_const ($ᵗ L.ker : ProbComp _) (pure (P x.val))

omit [SampleableType F] in
/-- With no directions, an output witness already establishes the unbatched input language. -/
theorem mem_inputLanguage_of_output_zero
    (hdom : 2 ^ (∑ i, (s i).1) * d ≤ 2 ^ n) (δ : ℝ≥0)
    (stmt : Unit × ∀ j, OracleStatement 0 ω j) (cs : Fin 0 → F)
    (hout : (Fin.elim0, combinedOracle s 0 cs stmt.2) ∈
      (outputRelation (ω := ω) s d hdom δ).language) :
    stmt ∈ (inputRelation (ω := ω) s d 0 δ).language := by
  have hclose := close_of_mem_outputLanguage s d 0 hdom δ stmt.2 cs hout
  simp only [Fin.sum_univ_zero, add_zero] at hclose
  obtain ⟨v, hv, hdist⟩ :=
    (Code.relCloseToCode_iff_relCloseToCodeword_of_minDist _ δ).mp hclose
  obtain ⟨S, hS, hagree⟩ := (Code.relCloseToWord_iff_exists_agreementCols _ _ δ).mp hdist
  apply mem_inputLanguage_of_jointAgreement s d 0 δ stmt
  refine ⟨S, (Code.relDist_floor_bound_iff_complement_bound _ _ δ).mp hS,
    (fun _ ↦ v), ?_⟩
  intro i
  refine ⟨hv, ?_⟩
  intro z hz
  have hi : i = 0 := Fin.eq_zero i
  subst i
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ((hagree z).1 hz).symm⟩

/-- If the input words lack correlated agreement, a uniformly sampled combined word lands
in the FRI input language with probability at most the affine-space proximity error.
The radius is positive and below the Johnson bound; the degree is the initial FRI bound,
strictly below the domain size, and the stated error must be less than one. -/
theorem batching_error
    (hdom : 2 ^ (∑ i, (s i).1) * d ≤ 2 ^ n) (δ : ℝ≥0)
    (hδ_pos : 0 < δ)
    (hδ : δ < 1 - ReedSolomon.sqrtRate (2 ^ (∑ i, (s i).1) * d) (ω : Fin (2 ^ n) ↪ F))
    (hRS : 2 ^ (∑ i, (s i).1) * d + 1 ≤ Fintype.card (Fin (2 ^ n)))
    (hε : ProximityGap.errorBound δ (2 ^ (∑ i, (s i).1) * d) (ω : Fin (2 ^ n) ↪ F) < 1)
    (stmt : Unit × ∀ j, OracleStatement m ω j)
    (hnot : stmt ∉ (inputRelation (ω := ω) s d m δ).language) :
    Pr{let cs ← $ᵗ (Fin m → F)}[
      (Fin.elim0, combinedOracle s m cs stmt.2) ∈
        (outputRelation (ω := ω) s d hdom δ).language] ≤
      ProximityGap.errorBound δ (2 ^ (∑ i, (s i).1) * d) (ω : Fin (2 ^ n) ↪ F) := by
  by_cases hm : m = 0
  · subst m
    have hz : Pr{let cs ← $ᵗ (Fin 0 → F)}[
        (Fin.elim0, combinedOracle s 0 cs stmt.2) ∈
          (outputRelation (ω := ω) s d hdom δ).language] = 0 := by
      apply prEvent_eq_zero_of_forall_mem_support
      intro cs _ hout
      exact hnot (mem_inputLanguage_of_output_zero s d hdom δ stmt cs hout)
    rw [hz]
    exact zero_le
  let : NeZero m := ⟨hm⟩
  apply le_trans (prEvent_mono _ _ _ (fun cs h ↦
    close_of_mem_outputLanguage s d m hdom δ stmt.2 cs h))
  apply le_of_not_gt
  intro hprob
  have heq := uniform_affine_combination m (inputWords m stmt.2)
    (fun f ↦ Code.relDistFromCode f
      (ReedSolomon.code (ω : Fin (2 ^ n) ↪ F) (2 ^ (∑ i, (s i).1) * d)).carrier ≤ δ)
  have hprob' := lt_of_lt_of_eq hprob heq
  apply hnot
  apply mem_inputLanguage_of_jointAgreement s d m δ stmt
  exact ProximityGap.correlatedAgreement_affine_spaces
    (by positivity) hδ_pos hδ hRS hε (inputWords m stmt.2) hprob'

/-- Before the sole challenge the certificate is input-language membership; afterward it
is membership of the verifier's deterministic output in the output language. -/
def batchStateFunction
    (hdom : 2 ^ (∑ i, (s i).1) * d ≤ 2 ^ n) (δ : ℝ≥0)
    {σ : Type} (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    (batchVerifier (ω := ω) s m).toVerifier.StateFunction init impl
      (inputRelation s d m δ).language (outputRelation s d hdom δ).language where
  toFun
    | 0, stmt, _ => stmt ∈ (inputRelation s d m δ).language
    | 1, stmt, tr => (batchPureForm s m).verify stmt tr ∈
        (outputRelation s d hdom δ).language
  toFun_empty := fun _ ↦ Iff.rfl
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
    have hp := ((batchPureForm s m).toGuardedForm.prEvent_pos_iff
      stmt tr (fun out ↦ out ∈ (outputRelation s d hdom δ).language)).mp hpos
    exact hnot hp.2

/-- Worst-case round-by-round soundness for the batching verifier. There are no prover
messages; the only transition is the uniformly sampled coefficient vector. -/
theorem round_soundness
    (hdom : 2 ^ (∑ i, (s i).1) * d ≤ 2 ^ n) (δ : ℝ≥0)
    (hδ_pos : 0 < δ)
    (hδ : δ < 1 - ReedSolomon.sqrtRate (2 ^ (∑ i, (s i).1) * d)
      (ω : Fin (2 ^ n) ↪ F))
    (hRS : 2 ^ (∑ i, (s i).1) * d + 1 ≤ Fintype.card (Fin (2 ^ n)))
    (hε : ProximityGap.errorBound δ (2 ^ (∑ i, (s i).1) * d)
      (ω : Fin (2 ^ n) ↪ F) < 1)
    {σ : Type} (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    (batchVerifier (ω := ω) s m).toVerifier.rbrSoundnessWorstCase init impl
      (inputRelation s d m δ).language (outputRelation s d hdom δ).language
      (fun _ ↦ ProximityGap.errorBound δ (2 ^ (∑ i, (s i).1) * d)
        (ω : Fin (2 ^ n) ↪ F)) := by
  classical
  refine ⟨batchStateFunction s d m hdom δ init impl, ?_⟩
  intro stmt hnot ⟨i, hi⟩ tr
  have hz : i = 0 := Fin.eq_zero i
  subst i
  let : SampleableType ((batchSpec F m).Challenge ⟨0, hi⟩) :=
    instSampleableTypeChallenge (F := F) m ⟨0, hi⟩
  change Pr{let cs ← $ᵗ ((batchSpec F m).Challenge ⟨0, hi⟩)}[
    ¬ stmt ∈ (inputRelation s d m δ).language ∧
      (Fin.elim0, combinedOracle s m cs stmt.2) ∈
        (outputRelation s d hdom δ).language] ≤ _
  simp only [hnot, not_false_eq_true, true_and]
  have heq := @SampleableType.prEvent_uniformSample_equiv
    ((batchSpec F m).Challenge ⟨0, hi⟩) (Fin m → F)
    (instSampleableTypeChallenge m ⟨0, hi⟩) inferInstance (Equiv.refl _)
    (fun cs ↦ (Fin.elim0, combinedOracle s m cs stmt.2) ∈
      (outputRelation s d hdom δ).language)
  exact heq.trans_le (batching_error s d m hdom δ hδ_pos hδ hRS hε stmt hnot)

/-- Ordinary soundness against any prover, with the affine-space error at the actual FRI rate. -/
theorem soundness
    (hdom : 2 ^ (∑ i, (s i).1) * d ≤ 2 ^ n) (δ : ℝ≥0)
    (hδ_pos : 0 < δ)
    (hδ : δ < 1 - ReedSolomon.sqrtRate (2 ^ (∑ i, (s i).1) * d)
      (ω : Fin (2 ^ n) ↪ F))
    (hRS : 2 ^ (∑ i, (s i).1) * d + 1 ≤ Fintype.card (Fin (2 ^ n)))
    (hε : ProximityGap.errorBound δ (2 ^ (∑ i, (s i).1) * d)
      (ω : Fin (2 ^ n) ↪ F) < 1)
    {σ : Type} (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    (batchVerifier (ω := ω) s m).soundness init impl
      (inputRelation s d m δ).language (outputRelation s d hdom δ).language
      (ProximityGap.errorBound δ (2 ^ (∑ i, (s i).1) * d)
        (ω : Fin (2 ^ n) ↪ F)) := by
  let : Unique (batchSpec F m).ChallengeIdx :=
    { default := ⟨0, rfl⟩
      uniq := fun j ↦ Subtype.ext (Fin.eq_zero j.1) }
  have h := (batchPureForm (ω := ω) s m).toGuardedForm.soundness_of_rbrSoundnessWorstCase
    (round_soundness s d m hdom δ hδ_pos hδ hRS hε init impl)
  simpa only [OracleVerifier.soundness, Finset.sum_const, Finset.card_univ,
    Fintype.card_unique, one_nsmul] using h

end BatchedFri.Spec.BatchingRound

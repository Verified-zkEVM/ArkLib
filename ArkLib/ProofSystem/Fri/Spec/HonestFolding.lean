/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/
module

public import ArkLib.ProofSystem.Fri.Spec.HonestFinalFolding
public import ArkLib.OracleReduction.Security.Acceptance
public import ArkLib.OracleReduction.Composition.Sequential.NoAmbient
public import ArkLib.OracleReduction.Composition.Sequential.OracleCompleteness

/-!
# Execution of the honest FRI folding prover

The actual folding prover preserves the supplied input word and computational witness through
the indexed polynomial chain. Every folding verifier agrees with the honest prover's full
statement and retained oracle history, including the final polynomial message.
-/

@[expose] public section

namespace Fri.Spec

open Domain OracleComp OracleSpec ProtocolSpec Finset
open scoped NNReal

variable {F : Type} [NonBinaryField F] [Fintype F] [DecidableEq F]
variable {n k : ℕ} {ω : SmoothCosetFftDomain n F}
variable (s : Fin (k + 1) → ℕ+) (d : ℕ+)

/-- The folding verifier accepts the canonical transcript and retains its complete history. -/
theorem reductionFold_run_honest
    (f : OracleStatement s ω (0 : Fin (k + 1)) 0)
    (p₀ : Witness F s d 0) (α : Fin (k + 1) → F) :
    ((reductionFold k s d).verifier.toVerifier.run (honestFoldState s d f p₀ α 0).1
      (honestFoldTranscript s d f p₀ α)).run = pure (some (α, honestHistory s d f p₀ α)) := by
  change ((OracleVerifier.append
    (OracleVerifier.seqCompose (Statement F) (OracleStatement s ω)
      (fun i ↦ FoldPhase.foldVerifier s i))
    (FinalFoldPhase.finalFoldVerifier s d)).toVerifier.run
      (foldState s (fun i ↦ α i.castSucc) (honestWords s d f p₀ α) 0)
      (honestFoldTranscript s d f p₀ α)).run = _
  rw [OracleVerifier.append_toVerifier, Verifier.append_run]
  simp only [honestFoldTranscript, FullTranscript.append_fst, FullTranscript.append_snd]
  rw [foldVerifiers_run, pure_bind]
  exact FinalFoldPhase.finalFoldVerifier_run_honest s d f p₀ α

namespace FoldPhase

/-- Uniform sampling of the field challenge of a non-final fold. -/
noncomputable instance instSampleableTypeChallenge (i : Fin k) :
    ∀ j, SampleableType ((pSpec (ω := ω) s i).Challenge j) :=
  fun _ ↦ SampleableType.ofFintype _

set_option backward.isDefEq.respectTransparency false in
/-- A non-final honest prover samples a challenge, folds the witness, and appends evaluations. -/
theorem foldProver_run (i : Fin k) (c : Statement F i.castSucc)
    (o : ∀ j, OracleStatement s ω i.castSucc j)
    (p : Witness F s d i.castSucc.castSucc) :
    (foldProver s d i).run (c, o) p = (do
      let α ← (pSpec (ω := ω) s i).getChallenge ⟨0, rfl⟩
      let p' : Witness F s d i.succ.castSucc :=
        ⟨CompPoly.CPolynomial.FoldingPolynomial.cpolyFold p.val (2 ^ (s i.castSucc).val) α,
          witness_lift (i := i.castSucc) p.property⟩
      pure (FullTranscript.mk2 α (fun x ↦ p'.val.eval x.val),
        (Fin.append c (fun _ : Fin 1 ↦ α), appendFoldOracle s i o p'.val), p')) := by
  have step2 : (foldProver s d i).runToRound (Fin.last 2) (c, o) p =
      (foldProver s d i).processRound (1 : Fin 2)
        ((foldProver s d i).runToRound (1 : Fin 2).castSucc (c, o) p) :=
    Prover.runToRound_succ (1 : Fin 2) (c, o) p _
  have step1 : (foldProver s d i).runToRound (1 : Fin 2).castSucc (c, o) p =
      (foldProver s d i).processRound (0 : Fin 2)
        ((foldProver s d i).runToRound (0 : Fin 2).castSucc (c, o) p) :=
    Prover.runToRound_succ (0 : Fin 2) (c, o) p _
  have step0 : (foldProver s d i).runToRound (0 : Fin 2).castSucc (c, o) p =
      pure ((fun j ↦ j.elim0), ((c, o), p)) := rfl
  unfold Prover.run
  rw [step2, step1, step0,
    Prover.processRound_of_dir_eq_P_to_V (1 : Fin 2) rfl,
    Prover.processRound_of_dir_eq_V_to_P (0 : Fin 2) rfl]
  simp only [foldProver, liftM, monadLift,
    MonadLift.monadLift, OracleComp.liftComp_pure, monad_norm,
    FullTranscript.mk2_eq_snoc_snoc]
  rfl

/-- The honest non-final prover extends the supplied input's canonical polynomial chain. -/
theorem foldProver_run_honest
    (f : OracleStatement s ω (0 : Fin (k + 1)) 0) (p₀ : Witness F s d 0)
    (α : Fin (k + 1) → F) (i : Fin k) :
    (foldProver s d i).run (honestFoldState s d f p₀ α i.castSucc).1
      (honestFoldState s d f p₀ α i.castSucc).2 = (do
        let a ← (pSpec (ω := ω) s i).getChallenge ⟨0, rfl⟩
        let β := Function.update α i.castSucc a
        pure (foldTranscript s (fun j ↦ β j.castSucc) (honestWords s d f p₀ β) i,
          (honestFoldState s d f p₀ β i.succ).1,
          (honestFoldState s d f p₀ β i.succ).2)) := by
  rw [foldProver_run]
  apply bind_congr
  intro a
  let β := Function.update α i.castSucc a
  have hcur : honestFoldState s d f p₀ α i.castSucc =
      honestFoldState s d f p₀ β i.castSucc :=
    (honestFoldState_update s d f p₀ α i.castSucc a).symm
  have hp : (⟨CompPoly.CPolynomial.FoldingPolynomial.cpolyFold
      (honestFoldState s d f p₀ α i.castSucc).2.val (2 ^ (s i.castSucc).val) a,
        witness_lift (i := i.castSucc) (honestFoldState s d f p₀ α i.castSucc).2.property⟩ :
        Witness F s d i.succ.castSucc) = honestPolynomial s d p₀ β i.succ.castSucc := by
    apply Subtype.ext
    change CompPoly.CPolynomial.FoldingPolynomial.cpolyFold
      (honestFoldState s d f p₀ α i.castSucc).2.val (2 ^ (s i.castSucc).val) a = _
    rw [congrArg (fun st ↦ st.2.val) hcur]
    change CompPoly.CPolynomial.FoldingPolynomial.cpolyFold
      (honestPolynomial s d p₀ β i.castSucc.castSucc).val (2 ^ (s i.castSucc).val) a =
      (honestPolynomial s d p₀ β i.castSucc.succ).val
    rw [honestPolynomial_succ]
    simp [β]
  have hpval := congrArg Subtype.val hp
  simp only at hpval
  simp only
  rw [hp, hpval]
  apply congrArg pure
  apply Prod.ext
  · funext j
    fin_cases j
    · simp [foldTranscript, β]
    · funext x
      exact (honestWords_succ s d f p₀ β i x).symm
  · apply Prod.ext
    · change (Fin.append (honestFoldState s d f p₀ α i.castSucc).1.1
        (fun _ : Fin 1 ↦ a), appendFoldOracle s i
          (honestFoldState s d f p₀ α i.castSucc).1.2
          (honestPolynomial s d p₀ β i.succ.castSucc).val) = _
      rw [congrArg Prod.fst hcur]
      have ha : β i.castSucc = a := by simp [β]
      calc
        _ = (Fin.append (honestFoldState s d f p₀ β i.castSucc).1.1
          (fun _ : Fin 1 ↦ β i.castSucc), appendFoldOracle s i
            (honestFoldState s d f p₀ β i.castSucc).1.2
            (honestPolynomial s d p₀ β i.succ.castSucc).val) := by rw [ha]
        _ = (honestFoldState s d f p₀ β i.succ).1 := honestFoldState_succ s d f p₀ β i
    · rfl

/-- Every honest non-final run extends the supplied initial word's polynomial history. -/
theorem foldOracleReduction_run_support_honest
    (f : OracleStatement s ω (0 : Fin (k + 1)) 0) (p₀ : Witness F s d 0)
    (α : Fin (k + 1) → F) (i : Fin k)
    (x : Option (((pSpec (ω := ω) s i).FullTranscript ×
      (Statement F i.succ × ∀ j, OracleStatement s ω i.succ j) ×
      Witness F s d i.succ.castSucc) ×
      (Statement F i.succ × ∀ j, OracleStatement s ω i.succ j)))
    (hx : x ∈ support (((foldOracleReduction s d i).toReduction.run
      (honestFoldState s d f p₀ α i.castSucc).1
      (honestFoldState s d f p₀ α i.castSucc).2).run)) :
    ∃ β, x = some ((foldTranscript s (fun j ↦ β j.castSucc)
        (honestWords s d f p₀ β) i,
        (honestFoldState s d f p₀ β i.succ).1,
        (honestFoldState s d f p₀ β i.succ).2),
        (honestFoldState s d f p₀ β i.succ).1) := by
  rw [Reduction.run_run_eq_bind] at hx
  change x ∈ support (do
    let pr ← (foldProver s d i).run (honestFoldState s d f p₀ α i.castSucc).1
      (honestFoldState s d f p₀ α i.castSucc).2
    let out ← liftComp ((foldVerifier s i).toVerifier.run
      (honestFoldState s d f p₀ α i.castSucc).1 pr.1).run _
    pure (out.map (fun v ↦ (pr, v)))) at hx
  rw [foldProver_run_honest, mem_support_bind_iff] at hx
  obtain ⟨pr, hpr, hx⟩ := hx
  rw [mem_support_bind_iff] at hpr
  obtain ⟨a, -, hpr⟩ := hpr
  rw [mem_support_pure_iff] at hpr
  subst pr
  let β := Function.update α i.castSucc a
  have hcur : honestFoldState s d f p₀ α i.castSucc =
      honestFoldState s d f p₀ β i.castSucc :=
    (honestFoldState_update s d f p₀ α i.castSucc a).symm
  have hverify : (foldVerifier s i).toVerifier.run
      (honestFoldState s d f p₀ α i.castSucc).1
      (foldTranscript s (fun j ↦ β j.castSucc) (honestWords s d f p₀ β) i) =
      pure (honestFoldState s d f p₀ β i.succ).1 := by
    rw [congrArg Prod.fst hcur]
    exact foldVerifier_run s (fun j ↦ β j.castSucc) (honestWords s d f p₀ β) i
  change x ∈ support (do
    let out ← liftComp ((foldVerifier s i).toVerifier.run
      (honestFoldState s d f p₀ α i.castSucc).1
      (foldTranscript s (fun j ↦ β j.castSucc) (honestWords s d f p₀ β) i)).run _
    pure (out.map (fun v ↦
      ((foldTranscript s (fun j ↦ β j.castSucc) (honestWords s d f p₀ β) i,
        (honestFoldState s d f p₀ β i.succ).1,
        (honestFoldState s d f p₀ β i.succ).2), v)))) at hx
  rw [hverify] at hx
  simp only [OptionT.run_pure, liftComp_pure, pure_bind, Option.map_some,
    mem_support_pure_iff] at hx
  exact ⟨β, hx⟩

/-- Each non-final fold preserves histories generated from a fixed word and witness. -/
theorem foldOracleReduction_perfectCompleteness_honest
    (f : OracleStatement s ω (0 : Fin (k + 1)) 0) (p₀ : Witness F s d 0) (i : Fin k)
    {σ : Type} (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    (foldOracleReduction s d i).perfectCompleteness init impl
      (honestFoldRelation s d f p₀ i.castSucc) (honestFoldRelation s d f p₀ i.succ) := by
  apply Reduction.perfectCompleteness_of_run_support
  intro stmt p h x hx
  obtain ⟨α, hα⟩ := h
  cases hα
  obtain ⟨β, hx⟩ := foldOracleReduction_run_support_honest s d f p₀ α i x hx
  refine ⟨_, hx, ⟨β, rfl⟩, rfl⟩

end FoldPhase

/-- Uniform challenge sampling for the sequence of non-final folds. -/
noncomputable instance instSampleableTypeChallengePSpecFold :
    ∀ j, SampleableType ((pSpecFold k (ω := ω) s).Challenge j) :=
  ProtocolSpec.instSampleableTypeChallengeSeqCompose

/-- Uniform challenge sampling for all polynomial-folding commitments. -/
noncomputable instance instSampleableTypeChallengeFold :
    ∀ j, SampleableType ((pSpecFold k (ω := ω) s ++ₚ FinalFoldPhase.pSpec F).Challenge j) :=
  ProtocolSpec.instSampleableTypeChallengeAppend

/-- The non-final folding chain preserves a fixed input's exact honest history. -/
theorem nonfinal_perfectCompleteness_honest
    (f : OracleStatement s ω (0 : Fin (k + 1)) 0) (p₀ : Witness F s d 0)
    {σ : Type} (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    (OracleReduction.seqCompose (Statement F) (OracleStatement s ω)
      (fun i : Fin (k + 1) ↦ Witness F s d i.castSucc)
      (FoldPhase.foldOracleReduction s (ω := ω) d)).perfectCompleteness init impl
        (honestFoldRelation s d f p₀ 0) (honestFoldRelation s d f p₀ (Fin.last k)) := by
  exact OracleReduction.seqCompose_perfectCompleteness_of_guarded_verifiers
    (Statement F) (OracleStatement s ω) (fun i ↦ Witness F s d i.castSucc)
    init impl (honestFoldRelation s d f p₀) (FoldPhase.foldOracleReduction s (ω := ω) d)
    (fun _ ↦ inferInstance)
    (fun _ ↦ Verifier.GuardedForm.ofEmpty _ (fun _ ↦ (fun _ ↦ 0, fun _ _ ↦ 0)))
    (fun i st ↦ FoldPhase.foldOracleReduction_perfectCompleteness_honest
      s d f p₀ i (pure st) impl)

/-- Every folding stage preserves the history generated from the supplied word and witness. -/
theorem reductionFold_perfectCompleteness_honest
    (f : OracleStatement s ω (0 : Fin (k + 1)) 0) (p₀ : Witness F s d 0)
    {σ : Type} (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    (reductionFold k s d).perfectCompleteness init impl
      (honestFoldRelation s d f p₀ 0) (honestOutputRelation s d f p₀) := by
  exact OracleReduction.append_perfectCompleteness_of_guarded_verifiers
    _ _
    (Verifier.GuardedForm.ofEmpty _ (fun _ ↦ (fun _ ↦ 0, fun _ _ ↦ 0)))
    (FinalFoldPhase.finalFoldGuardedForm s d)
    (fun _ ↦ Or.inl inferInstance)
    (nonfinal_perfectCompleteness_honest s d f p₀ init impl)
    (fun st ↦ FinalFoldPhase.finalFoldOracleReduction_perfectCompleteness
      s d (pure st) impl f p₀)

/-- The folding phase preserves proximity to the supplied initial polynomial witness. -/
theorem reductionFold_perfectCompleteness
    (hdom : 2 ^ (∑ j, (s j).val) * d.val ≤ 2 ^ n) (δ : ℝ≥0)
    {σ : Type} (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    (reductionFold k s d).perfectCompleteness init impl
      (inputRelation k s d hdom δ) (foldCompletenessRelation s d (ω := ω) δ) := by
  intro stmt p hIn
  have hdist : (Code.relHammingDist (stmt.2 0) (fun x ↦ p.val.eval x.val) : ℝ≥0) ≤ δ := by
    cases k <;> exact hIn
  have hout : honestOutputRelation s d (stmt.2 0) p ⊆ foldCompletenessRelation s d δ := by
    rintro sw ⟨α, rfl⟩
    exact ⟨stmt.2 0, p, α, hdist, rfl⟩
  have hcomplete := Reduction.completeness_relOut_mono init impl hout
    (reductionFold_perfectCompleteness_honest s d (stmt.2 0) p init impl)
  apply hcomplete stmt p
  exact ⟨fun _ ↦ 0, (honestFoldState_zero_eq s d stmt p (fun _ ↦ 0)).symm⟩

end Fri.Spec

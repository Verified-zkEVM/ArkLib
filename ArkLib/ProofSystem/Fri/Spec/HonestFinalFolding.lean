/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/
module

public import ArkLib.ProofSystem.Fri.Spec.HonestExecution
public import ArkLib.OracleReduction.Security.CoordinateWiseSpecialSoundness.Guarded
public import ArkLib.OracleReduction.Security.Acceptance

/-!
# Honest execution of the final FRI fold

The final folding prover transmits its folded witness and preserves every preceding oracle
word. Its output agrees with the verifier's entire materialized history, and its witness
satisfies the final degree guard even for the zero polynomial.
-/

@[expose] public section

namespace Fri.Spec.FinalFoldPhase

open Domain OracleComp OracleSpec ProtocolSpec Finset
open scoped NNReal

variable {F : Type} [NonBinaryField F] [Fintype F] [DecidableEq F]
variable {n k : ℕ} {ω : SmoothCosetFftDomain n F}
variable (s : Fin (k + 1) → ℕ+) (d : ℕ+)

/-- Uniform sampling of the field challenge of the final fold. -/
noncomputable instance instSampleableTypeChallenge :
    ∀ j, SampleableType ((pSpec F).Challenge j) :=
  fun _ ↦ SampleableType.ofFintype _

/-- The final verifier checks the polynomial degree and materializes the full output history. -/
def finalFoldGuardedForm :
    (finalFoldOracleReduction (ω := ω) s d).toReduction.verifier.GuardedForm where
  check := fun _ tr ↦ decide ((tr 1).natDegree < d.val)
  out := fun stmt tr ↦ (Fin.append stmt.1 (fun _ : Fin 1 ↦ tr 0),
    (finalFoldVerifier s d).materializeOutput tr.challenges stmt.2 tr.messages)
  verify_eq := by
    intro ⟨c, o⟩ tr
    apply OptionT.ext
    change ((finalFoldVerifier s d).toVerifier.run (c, o) tr).run = _
    rw [toVerifier_run]
    by_cases h : (tr 1).natDegree < d.val <;> simp [h]

set_option backward.isDefEq.respectTransparency false in
/-- The final prover folds its witness, transmits that polynomial, and retains all earlier words. -/
theorem finalFoldProver_run (c : Statement F (Fin.last k))
    (o : ∀ j, OracleStatement s ω (Fin.last k) j)
    (p : Witness F s d (Fin.last k).castSucc) :
    (finalFoldProver s d).run (c, o) p = (do
      let a ← (pSpec F).getChallenge ⟨0, rfl⟩
      let p' : Witness F s d (Fin.last (k + 1)) :=
        ⟨CompPoly.CPolynomial.FoldingPolynomial.cpolyFold
          p.val (2 ^ (s (Fin.last k)).val) a, witness_lift (i := Fin.last k) p.property⟩
      let tr : (pSpec F).FullTranscript := FullTranscript.mk2 a p'.val
      pure (tr, (Fin.append c (fun _ : Fin 1 ↦ a),
        (finalFoldVerifier s d).materializeOutput tr.challenges o tr.messages), p')) := by
  have step2 : (finalFoldProver s d).runToRound (Fin.last 2) (c, o) p =
      (finalFoldProver s d).processRound (1 : Fin 2)
        ((finalFoldProver s d).runToRound (1 : Fin 2).castSucc (c, o) p) :=
    Prover.runToRound_succ (1 : Fin 2) (c, o) p _
  have step1 : (finalFoldProver s d).runToRound (1 : Fin 2).castSucc (c, o) p =
      (finalFoldProver s d).processRound (0 : Fin 2)
        ((finalFoldProver s d).runToRound (0 : Fin 2).castSucc (c, o) p) :=
    Prover.runToRound_succ (0 : Fin 2) (c, o) p _
  have step0 : (finalFoldProver s d).runToRound (0 : Fin 2).castSucc (c, o) p =
      pure ((fun j ↦ j.elim0), ((c, o), p)) := rfl
  unfold Prover.run
  rw [step2, step1, step0,
    Prover.processRound_of_dir_eq_P_to_V (1 : Fin 2) rfl,
    Prover.processRound_of_dir_eq_V_to_P (0 : Fin 2) rfl]
  simp only [finalFoldProver, liftM, monadLift,
    MonadLift.monadLift, OracleComp.liftComp_pure, monad_norm,
    FullTranscript.mk2_eq_snoc_snoc]
  apply bind_congr
  intro a
  apply congrArg pure
  apply Prod.ext
  · rfl
  · apply Prod.ext
    · apply Prod.ext
      · change Fin.vappend c !v[a] = Fin.append c (fun _ : Fin 1 ↦ a)
        simp only [Fin.vappend_eq_append]
        congr 1
        funext i
        fin_cases i
        rfl
      · apply oracleHistory_ext s
        · intro i
          rw [committedWord_materialize]
          simp [committedWord, show i.val ≠ k + 1 by omega]
        · rw [finalPolynomial_materialize]
          simp only [finalPolynomial, Fin.val_last, ↓reduceDIte, finRangeTo, eq_mpr_eq_cast,
            id_eq, cast_cast, cast_eq, Fin.isValue]
          exact (Transcript.concat_last (pSpec := pSpec F) (m := (1 : Fin 2)) _ _).symm
    · rfl

/-- The final prover extends the fixed initial witness's honest polynomial chain. -/
theorem finalFoldProver_run_honest
    (f : OracleStatement s ω (0 : Fin (k + 1)) 0) (p₀ : Witness F s d 0)
    (α : Fin (k + 1) → F) :
    (finalFoldProver s d).run (honestFoldState s d f p₀ α (Fin.last k)).1
      (honestFoldState s d f p₀ α (Fin.last k)).2 = (do
        let a ← (pSpec F).getChallenge ⟨0, rfl⟩
        let β := Function.update α (Fin.last k) a
        pure (honestFinalTranscript s d p₀ β,
          (β, honestHistory s d f p₀ β),
          honestPolynomial s d p₀ β (Fin.last (k + 1)))) := by
  rw [finalFoldProver_run]
  apply bind_congr
  intro a
  let β := Function.update α (Fin.last k) a
  have hcur : honestFoldState s d f p₀ α (Fin.last k) =
      honestFoldState s d f p₀ β (Fin.last k) :=
    (honestFoldState_update s d f p₀ α (Fin.last k) a).symm
  have hp : (⟨CompPoly.CPolynomial.FoldingPolynomial.cpolyFold
      (honestFoldState s d f p₀ α (Fin.last k)).2.val
        (2 ^ (s (Fin.last k)).val) a,
        witness_lift (i := Fin.last k)
          (honestFoldState s d f p₀ α (Fin.last k)).2.property⟩ :
        Witness F s d (Fin.last (k + 1))) =
      honestPolynomial s d p₀ β (Fin.last (k + 1)) := by
    apply Subtype.ext
    change CompPoly.CPolynomial.FoldingPolynomial.cpolyFold
      (honestFoldState s d f p₀ α (Fin.last k)).2.val
        (2 ^ (s (Fin.last k)).val) a = _
    rw [congrArg (fun st ↦ st.2.val) hcur]
    change CompPoly.CPolynomial.FoldingPolynomial.cpolyFold
      (honestPolynomial s d p₀ β (Fin.last k).castSucc).val
        (2 ^ (s (Fin.last k)).val) a =
      (honestPolynomial s d p₀ β (Fin.last k).succ).val
    rw [honestPolynomial_succ]
    simp [β]
  have hpval := congrArg Subtype.val hp
  simp only at hpval
  simp only
  rw [hp, hpval]
  apply congrArg pure
  have htr : FullTranscript.mk2 a
      (honestPolynomial s d p₀ β (Fin.last (k + 1))).val =
      honestFinalTranscript s d p₀ β := by
    funext j
    fin_cases j <;> simp [honestFinalTranscript, FullTranscript.mk2, β]
  rw [htr]
  apply Prod.ext
  · rfl
  · apply Prod.ext
    · apply Prod.ext
      · funext j
        refine Fin.lastCases ?_ (fun j ↦ ?_) j
        · simp [Fin.append_right_eq_snoc]
        · simp [Fin.append_right_eq_snoc, honestFoldState, foldState]
      · rw [congrArg (fun st ↦ st.1.2) hcur]
        rfl
    · rfl

/-- The final verifier accepts the honest polynomial and agrees on the entire output history. -/
theorem finalFoldVerifier_run_honest
    (f : OracleStatement s ω (0 : Fin (k + 1)) 0) (p₀ : Witness F s d 0)
    (α : Fin (k + 1) → F) :
    ((finalFoldVerifier s d).toVerifier.run
      (honestFoldState s d f p₀ α (Fin.last k)).1
      (honestFinalTranscript s d p₀ α)).run =
        pure (some (α, honestHistory s d f p₀ α)) := by
  change ((finalFoldVerifier s d).toVerifier.run
    ((honestFoldState s d f p₀ α (Fin.last k)).1.1,
      (honestFoldState s d f p₀ α (Fin.last k)).1.2)
    (honestFinalTranscript s d p₀ α)).run = _
  rw [toVerifier_run]
  change pure (if (honestPolynomial s d p₀ α (Fin.last (k + 1))).val.natDegree < d.val
    then some (Fin.append (honestFoldState s d f p₀ α (Fin.last k)).1.1
      (fun _ : Fin 1 ↦ α (Fin.last k)), honestHistory s d f p₀ α) else none) = _
  rw [ite_eq_left (honestPolynomial_last_natDegree_lt s d p₀ α)]
  congr 3
  funext j
  refine Fin.lastCases ?_ (fun j ↦ ?_) j
  · simp [Fin.append_right_eq_snoc]
  · simp [Fin.append_right_eq_snoc, honestFoldState, foldState]

/-- Every final honest run transmits the honest witness and agrees on the entire history. -/
theorem finalFoldOracleReduction_run_support_honest
    (f : OracleStatement s ω (0 : Fin (k + 1)) 0) (p₀ : Witness F s d 0)
    (α : Fin (k + 1) → F)
    (x : Option (((pSpec F).FullTranscript ×
      (FinalStatement F k × ∀ j, FinalOracleStatement s ω j) ×
      Witness F s d (Fin.last (k + 1))) ×
      (FinalStatement F k × ∀ j, FinalOracleStatement s ω j)))
    (hx : x ∈ support (((finalFoldOracleReduction s d).toReduction.run
      (honestFoldState s d f p₀ α (Fin.last k)).1
      (honestFoldState s d f p₀ α (Fin.last k)).2).run)) :
    ∃ β, x = some ((honestFinalTranscript s d p₀ β,
      (β, honestHistory s d f p₀ β), honestPolynomial s d p₀ β (Fin.last (k + 1))),
      (β, honestHistory s d f p₀ β)) := by
  rw [Reduction.run_run_eq_bind] at hx
  change x ∈ support (do
    let pr ← (finalFoldProver s d).run (honestFoldState s d f p₀ α (Fin.last k)).1
      (honestFoldState s d f p₀ α (Fin.last k)).2
    let out ← liftComp ((finalFoldVerifier s d).toVerifier.run
      (honestFoldState s d f p₀ α (Fin.last k)).1 pr.1).run _
    pure (out.map (fun v ↦ (pr, v)))) at hx
  rw [finalFoldProver_run_honest, mem_support_bind_iff] at hx
  obtain ⟨pr, hpr, hx⟩ := hx
  rw [mem_support_bind_iff] at hpr
  obtain ⟨a, -, hpr⟩ := hpr
  rw [mem_support_pure_iff] at hpr
  subst pr
  let β := Function.update α (Fin.last k) a
  have hcur : honestFoldState s d f p₀ α (Fin.last k) =
      honestFoldState s d f p₀ β (Fin.last k) :=
    (honestFoldState_update s d f p₀ α (Fin.last k) a).symm
  have hverify := finalFoldVerifier_run_honest s d f p₀ β
  rw [← congrArg Prod.fst hcur] at hverify
  change x ∈ support (do
    let out ← liftComp ((finalFoldVerifier s d).toVerifier.run
      (honestFoldState s d f p₀ α (Fin.last k)).1
      (honestFinalTranscript s d p₀ β)).run _
    pure (out.map (fun v ↦
      ((honestFinalTranscript s d p₀ β, (β, honestHistory s d f p₀ β),
        honestPolynomial s d p₀ β (Fin.last (k + 1))), v)))) at hx
  rw [hverify] at hx
  simp only [liftComp_pure, pure_bind, Option.map_some, mem_support_pure_iff] at hx
  exact ⟨β, hx⟩

variable {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl []ₒ (StateT σ ProbComp))

/-- The final fold is perfectly complete for every honest history, including noisy input. -/
theorem finalFoldOracleReduction_perfectCompleteness
    (f : OracleStatement s ω (0 : Fin (k + 1)) 0) (p₀ : Witness F s d 0) :
    (finalFoldOracleReduction s d).perfectCompleteness init impl
      (honestFoldRelation s d f p₀ (Fin.last k)) (honestOutputRelation s d f p₀) := by
  apply Reduction.perfectCompleteness_of_run_support
  intro stmt p h x hx
  obtain ⟨α, hα⟩ := h
  cases hα
  obtain ⟨β, hx⟩ := finalFoldOracleReduction_run_support_honest s d f p₀ α x hx
  exact ⟨_, hx, ⟨β, rfl⟩, rfl⟩

end Fri.Spec.FinalFoldPhase

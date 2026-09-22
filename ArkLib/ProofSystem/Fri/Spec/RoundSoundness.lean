/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

module

public import ArkLib.ProofSystem.Fri.Spec.Transcript
public import ArkLib.ProofSystem.Fri.Spec.QueryExecution

/-!
# Bad folding challenges in the actual FRI execution

The challenge is sampled after its input word is fixed. The resulting MCA bound is therefore
uniform over all partial transcripts, without imposing honesty on the prover's commitments.
-/

@[expose] public section

namespace Fri.Spec

open Domain OracleComp OracleSpec ProtocolSpec ProximityGap ReedSolomon CoreDefinitions
open scoped ProbabilityTheory NNReal

variable {F : Type} [NonBinaryField F] [Fintype F] [DecidableEq F]
variable {n k : ℕ} {ω : SmoothCosetFftDomain n F}
variable (s : Fin (k + 1) → ℕ+) (d : ℕ+) (l : ℕ)

/-- The folding bad event at its actual position in the composed FRI protocol. -/
def foldingBad (f : (ω.subdomain 0).toFinset → F) (θ : ℝ) (i : Fin (k + 1))
    (tr : (pSpec k (ω := ω) s l).Transcript (foldChallenge (ω := ω) s l i).val.succ) : Prop :=
  FoldingAgreementFailure (ω.subdomain (foldingPrefix s i.castSucc))
    (fun z ↦ readWord s l f tr i (by simp)
      ⟨ω.subdomain (foldingPrefix s i.castSucc) z, CosetFftDomain.mem_toFinset_self⟩)
    (s i).val (foldingDegree s d i.succ) θ (readFoldChallenge s l tr i (by simp))

/-- The existing powers-generator MCA error for this folding round. -/
noncomputable def foldingError [SampleableType F] (θ : ℝ) (i : Fin (k + 1)) : ℝ≥0 :=
  (mcaError (univariatePowersGenerator F (2 ^ (s i).val - 1))
    (code (((ω.subdomain (foldingPrefix s i.castSucc)).subdomain (s i).val) :
      Fin (2 ^ (n - foldingPrefix s i.castSucc - (s i).val)) ↪ F)
      (foldingDegree s d i.succ)) θ).toNNReal

omit [Fintype F] in
/-- Appending the challenge changes its value, but does not change its input word. -/
theorem foldingBad_concat_iff (f : (ω.subdomain 0).toFinset → F) (θ : ℝ)
    (i : Fin (k + 1))
    (tr : (pSpec k (ω := ω) s l).Transcript (foldChallenge (ω := ω) s l i).val.castSucc)
    (α : (pSpec k (ω := ω) s l).Challenge (foldChallenge s l i)) :
    foldingBad s d l f θ i (tr.concat α) ↔
      FoldingAgreementFailure (ω.subdomain (foldingPrefix s i.castSucc))
        (fun z ↦ readWord s l f tr i (by simp)
          ⟨ω.subdomain (foldingPrefix s i.castSucc) z, CosetFftDomain.mem_toFinset_self⟩)
        (s i).val (foldingDegree s d i.succ) θ (cast (foldChallenge_type s l i) α) := by
  unfold foldingBad
  rw [readFoldChallenge_concat, readWord_concat]

/-- A fresh folding challenge has at most the existing MCA error, for every fixed
adversarial transcript prefix. -/
theorem foldingBad_prob_le [SampleableType F] (f : (ω.subdomain 0).toFinset → F) (θ : ℝ)
    (i : Fin (k + 1))
    [SampleableType ((pSpec k (ω := ω) s l).Challenge (foldChallenge s l i))]
    (tr : (pSpec k (ω := ω) s l).Transcript (foldChallenge (ω := ω) s l i).val.castSucc) :
    Pr{let α ← $ᵗ ((pSpec k (ω := ω) s l).Challenge (foldChallenge s l i))}[
      foldingBad s d l f θ i (tr.concat α)] ≤
      (foldingError (ω := ω) s d θ i : ENNReal) := by
  classical
  simp only [foldingBad_concat_iff]
  let w := fun z ↦ readWord s l f tr i (by simp)
    ⟨ω.subdomain (foldingPrefix s i.castSucc) z, CosetFftDomain.mem_toFinset_self⟩
  refine (SampleableType.prEvent_uniformSample_equiv
    (Equiv.cast (foldChallenge_type (ω := ω) s l i))
    (FoldingAgreementFailure (ω.subdomain (foldingPrefix s i.castSucc)) w
      (s i).val (foldingDegree s d i.succ) θ)).le.trans ?_
  unfold foldingError
  rw [ENNReal.coe_toNNReal (mcaError_ne_top _ _ _)]
  exact foldingAgreementFailure_prob_le_powers _ _ (foldingDegree_pos s d i.succ) θ

@[simp]
theorem initialWord_queryHistory (f : (ω.subdomain 0).toFinset → F)
    (tr : (pSpec k (ω := ω) s l).Transcript (queryChallenge (ω := ω) s l).val.castSucc)
    (z : Fin (2 ^ n)) :
    initialWord s (queryHistory s l f tr) z = f (initialQuery z) := by
  unfold initialWord
  have hx : ω z ∈ (ω.subdomain (foldingPrefix s (0 : Fin (k + 2)))).toFinset := by
    rw [foldingPrefix_zero, CosetFftDomain.subdomain_zero_eq_self]
    exact CosetFftDomain.mem_toFinset_self
  change committedFunction s (queryHistory s l f tr) (0 : Fin (k + 1)).castSucc (ω z) = _
  rw [committedFunction_castSucc s _ 0 ⟨ω z, hx⟩, committedWord_queryHistory]
  rfl

/-- Absence of bad folding events in the actual prefix implies the query history's
algebraic safety condition. -/
theorem safeHistory_queryHistory (f : (ω.subdomain 0).toFinset → F) (θ : ℝ)
    (tr : (pSpec k (ω := ω) s l).Transcript (queryChallenge (ω := ω) s l).val.castSucc)
    (hsafe : ∀ i : Fin (k + 1), ¬ foldingBad s d l f θ i
      (tr.restrict (by simp only [Fin.val_succ, Fin.val_castSucc,
        foldChallenge_val, queryChallenge_val]; omega))) :
    SafeHistory s d (queryHistory s l f tr) (queryFoldChallenges s l tr) θ := by
  intro i hbad
  apply hsafe i
  unfold foldingBad
  simp only [readWord_restrict, readFoldChallenge_restrict]
  have hw :
      (fun z ↦ committedFunction s (queryHistory s l f tr) i.castSucc
        (ω.subdomain (foldingPrefix s i.castSucc) z)) =
      (fun z ↦ readWord s l f tr i (by
        simp only [Fin.val_castSucc, queryChallenge_val]; omega)
        ⟨ω.subdomain (foldingPrefix s i.castSucc) z, CosetFftDomain.mem_toFinset_self⟩) := by
    funext z
    rw [← committedWord_queryHistory s l f tr i]
    exact committedFunction_castSucc s _ i ⟨_, CosetFftDomain.mem_toFinset_self⟩
  change FoldingAgreementFailure _ _ _ _ _ _ at hbad
  rw [hw] at hbad
  exact hbad

end Fri.Spec

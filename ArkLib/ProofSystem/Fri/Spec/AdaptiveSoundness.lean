/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.ProofSystem.Fri.Spec.BadEvents
import ArkLib.OracleReduction.Security.Accumulation

/-!
# Adaptive FRI transcript bounds

The probability bound is on ArkLib's actual `Prover.run`, with the existing FRI schedule
and input statement. No independence is assumed between successive prover commitments.
-/

namespace Fri.Spec

open Domain OracleComp OracleSpec ProtocolSpec ReedSolomon Finset
open scoped NNReal

variable {F : Type} [NonBinaryField F] [Fintype F] [DecidableEq F]
variable {n k : ℕ} {ω : SmoothCosetFftDomain n F}
variable (s : Fin (k + 1) → ℕ+) (d : ℕ+) (l : ℕ)

/-- The input word, expressed on the initial domain rather than the singleton history. -/
def initialOracle
    (stmt : Statement F (0 : Fin (k + 1)) × ∀ j, OracleStatement s ω 0 j) :
    (ω.subdomain 0).toFinset → F :=
  cast (by simp [OracleStatement, finRangeTo]; rfl) (stmt.2 0)

/-- Every terminal event implying acceptance of the committed query history has the
sum of the per-round MCA errors and the updated query error. The terminal implication
is separated from the probabilistic argument so verifier execution can be audited on its own. -/
theorem terminalEvent_prob_le (hs : (∑ j, (s j).val) ≤ n) (θ δ : ℝ)
    [∀ j, SampleableType ((pSpec k (ω := ω) s l).Challenge j)]
    {σ WitIn WitOut StmtOut : Type}
    (impl : QueryImpl (emptySpec.{0, 0}) (StateT σ ProbComp))
    (prover : Prover []ₒ
      (Statement F (0 : Fin (k + 1)) × ∀ j, OracleStatement s ω 0 j)
      WitIn StmtOut WitOut (pSpec k (ω := ω) s l))
    (stmt : Statement F (0 : Fin (k + 1)) × ∀ j, OracleStatement s ω 0 j)
    (hstmt : initialOracle s stmt ∉ proximityLanguage s d δ) (wit : WitIn)
    (E : (pSpec k (ω := ω) s l).FullTranscript → Prop)
    (hterminal : ∀ tr, E tr → queryBad s d l hs (initialOracle s stmt)
      (Transcript.restrict (b := Fin.last _)
        (by simp only [Fin.val_succ, Fin.val_last]; omega) tr))
    (os : σ) :
    Pr[ fun x ↦ E x.1.1 |
      (simulateQ (impl.addLift challengeQueryImpl : QueryImpl _ (StateT σ ProbComp))
        (prover.run stmt wit)).run os] ≤
      (∑ i, (foldingError (ω := ω) s d θ i : ENNReal)) +
        ENNReal.ofReal (1 - min θ δ) ^ l := by
  let lang := (initialOracle (ω := ω) s) ⁻¹' proximityLanguage s d δ
  let bad := fun j st tr ↦ badEvent (ω := ω) s d l hs θ j (initialOracle s st) tr
  have hb : ∀ st ∉ lang, ∀ j, ∀ tr,
      ¬ Verifier.badEventState lang bad j.val.castSucc st tr →
      Pr[ fun c ↦ bad j st (tr.concat c) |
        $ᵗ ((pSpec k (ω := ω) s l).Challenge j)] ≤
        (challengeError (ω := ω) s d l θ δ j : ENNReal) := by
    intro st hst j tr hbefore
    exact badEvent_prob_le s d l hs θ δ (initialOracle s st) hst j tr hbefore
  have h := Verifier.prob_terminal_event_le_of_badEvents impl lang bad
    (fun j ↦ (challengeError (ω := ω) s d l θ δ j : ENNReal)) hb
    prover stmt hstmt wit E (fun tr he ↦ ?_) os
  · simpa only [← ENNReal.ofNNReal_finsetSum, sum_challengeError, ENNReal.coe_add,
      ENNReal.coe_pow, ENNReal.ofReal] using h
  · exact Or.inr ⟨queryChallenge s l, (queryChallenge s l).val.isLt,
      (badEvent_query s d l hs θ (initialOracle s stmt) _).mpr (hterminal tr he)⟩

end Fri.Spec

/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.ProofSystem.Sumcheck.Interaction.MultivariateSoundness
public import ArkLib.ProofSystem.Sumcheck.Interaction.Protocol
public import VCVio.EvalDist.ProbabilityBounds

/-!
# Soundness against native Sumcheck prover strategies

The soundness bound concerns the actual full protocol executor and quantifies over its native
prover strategy. The prover may retain arbitrary continuation memory and perform effects after
each public challenge. The proof follows execution order and reuses the single-round projection
bound: a false-to-true transition costs at most `deg / |F|`, while false successors are handled
by induction on the remaining protocol rounds.
-/

@[expose] public section

namespace Sumcheck.Interaction.MultivariateRound

open OracleComp OracleSpec
open _root_.Interaction.Oracle
open SingleRound
open scoped ENNReal

noncomputable section

variable (n deg : ℕ) (F : Type) [Field F] [Fintype F] [DecidableEq F] [SampleableType F]

omit [DecidableEq F] in
/-- When the sent sum passes, the true-successor event of the fresh challenge is bounded by
the existing actual single-round soundness theorem. -/
theorem uniform_successor_soundness {m : ℕ} (D : Fin m ↪ F) (i : Fin n)
    (stmt : Spec.StatementRound F n i.castSucc) (p : Spec.OracleStatement F n deg ())
    (q : Message F deg)
    (hfalse : ¬ closedRelation F n deg D i.castSucc
      ⟨stmt, (polynomialFamily F n deg).behaviorOfRealizations (fun _ => p)⟩)
    (hcheck : ((Finset.univ.map D).toList.map (fun x => q.val.eval x)).sum = stmt.target) :
    Pr{let r ← ($ᵗ F)}[closedRelation F n deg D i.succ
      ⟨⟨q.val.eval r, Fin.snoc stmt.challenges r⟩,
        (polynomialFamily F n deg).behaviorOfRealizations (fun _ => p)⟩] ≤
      (deg : ENNReal) / Fintype.card F := by
  classical
  have h := executeCore_sampled_soundness n deg F D i stmt p
    ((polynomialFamily F n deg).behaviorOfRealizations (fun _ => p)) q rfl hfalse
  rw [executeCore_sampled_closed_eq, prEvent_map] at h
  simpa only [hcheck, ↓reduceIte, Option.map_some, Option.some.injEq, eq_iff_iff,
    iff_true] using h

end
end Sumcheck.Interaction.MultivariateRound

namespace Sumcheck.Interaction.Native

open OracleComp OracleSpec
open _root_.Interaction.Oracle
open SingleRound MultivariateRound
open scoped ENNReal

noncomputable section

variable (n deg : ℕ) (F : Type) [Field F] [Fintype F] [DecidableEq F] [SampleableType F]

set_option backward.isDefEq.respectTransparency false in
/-- Full native Sumcheck is sound against every ordinary prover strategy. From a false initial
claim over a polynomial-realized original oracle, the probability that the actual closed output
satisfies its original-oracle evaluation relation is at most `count * deg / |F|`.

The prover's response to each challenge is an arbitrary effectful native continuation. Its
effects execute after that challenge; no external private-state or message-kernel representation
is assumed. All accumulated source slots remain available, while `root` identifies the original
oracle view. The final relation is a predicate on the actual output behavior and does not add a
verifier query. -/
theorem execute_soundness {m : ℕ} (D : Fin m ↪ F)
    (count start : ℕ) (finish : start + count = n) (A : PFunctor)
    (root : VirtualOracle (OracleSpec.ofPFunctor A) (family F n deg))
    (stmt : Spec.StatementRound F n ⟨start, by omega⟩)
    (impl : QueryImpl (OracleSpec.ofPFunctor A) Id)
    (prover : Prover F deg unifSpec count) (p : Spec.OracleStatement F n deg ())
    (hroot : root.eval impl = (family F n deg).behaviorOfRealizations (fun _ => p))
    (hfalse : ¬ closedRelation F n deg D ⟨start, by omega⟩ ⟨stmt, root.eval impl⟩) :
    Pr{let result ← (execute F n deg unifSpec ($ᵗ F) (Finset.univ.map D).toList
      count start finish A root stmt impl prover)}[
        result.map (outputRelation F n deg) = some True] ≤
      (count : ENNReal) * deg / Fintype.card F := by
  induction count generalizing start A with
  | zero =>
    subst n
    rw [execute_zero]
    simpa [outputRelation] using
      (fun h => hfalse ((closedRelation_last_iff F start deg D
        ⟨stmt, root.eval impl⟩).mpr h))
  | succ count ih =>
    rw [execute_succ]
    refine prEvent_bind_le_of_forall_le _ _ _ ?_
    rintro ⟨q, respond⟩
    by_cases hcheck : ((Finset.univ.map D).toList.map (fun x => q.val.eval x)).sum =
        stmt.target
    · rw [ite_eq_left hcheck]
      let i : Fin n := ⟨start, by omega⟩
      let good : F → Prop := fun r => closedRelation F n deg D i.succ
        ⟨⟨q.val.eval r, Fin.snoc stmt.challenges r⟩,
          (family F n deg).behaviorOfRealizations (fun _ => p)⟩
      have hbad : Pr{let r ← ($ᵗ F)}[good r] ≤ (deg : ENNReal) / Fintype.card F :=
        uniform_successor_soundness n deg F D i stmt p q (by
          change ¬ closedRelation F n deg D ⟨start, by omega⟩
            ⟨stmt, (family F n deg).behaviorOfRealizations (fun _ => p)⟩
          rw [← hroot]
          exact hfalse) hcheck
      have hbound := prEvent_bind_le_prEvent_add ($ᵗ F)
        (fun r => do
          let next ← respond (some r)
          execute F n deg unifSpec ($ᵗ F) (Finset.univ.map D).toList count (start + 1)
            (by omega) (Access.extend A (polynomialInterface F deg))
            (extendRoot F n deg A root) ⟨q.val.eval r, Fin.snoc stmt.challenges r⟩
            (Access.extendImpl A (polynomialInterface F deg) impl q) next)
        good (fun result => result.map (outputRelation F n deg) = some True)
        (ε := (count : ENNReal) * deg / Fintype.card F) (fun r hr => by
          refine prEvent_bind_le_of_forall_le _ _ _ ?_
          intro next
          apply ih (start + 1) (by omega) (Access.extend A (polynomialInterface F deg))
            (extendRoot F n deg A root) ⟨q.val.eval r, Fin.snoc stmt.challenges r⟩
            (Access.extendImpl A (polynomialInterface F deg) impl q) next
          · rw [extendRoot_eval]
            exact hroot
          · rw [extendRoot_eval, hroot]
            exact hr)
      refine hbound.trans ?_
      calc
        _ ≤ (deg : ENNReal) / Fintype.card F +
            (count : ENNReal) * deg / Fintype.card F := add_le_add hbad le_rfl
        _ = _ := by simp [Nat.cast_succ, div_eq_mul_inv, add_mul, add_comm]
    · rw [ite_eq_right hcheck]
      refine prEvent_bind_le_of_forall_le _ _ _ ?_
      intro ignored
      simp

end
end Sumcheck.Interaction.Native

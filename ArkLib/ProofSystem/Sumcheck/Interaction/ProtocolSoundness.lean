/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.ProofSystem.Sumcheck.Interaction.MultivariateSoundness
public import ArkLib.ProofSystem.Sumcheck.Interaction.Protocol
public import ArkLib.ProofSystem.Sumcheck.Interaction.Composition
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

open Interaction.Oracle

namespace Sumcheck.Interaction.MultivariateRound

open OracleComp OracleSpec
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
open SingleRound MultivariateRound
open scoped ENNReal

noncomputable section

variable (n deg : ℕ) (F : Type) [Field F] [Fintype F] [DecidableEq F] [SampleableType F]

/-- A successful midpoint has the existing next-round relation; public abort is never true. -/
def midpointRelation {m : ℕ} (D : Fin m ↪ F) (count start : ℕ)
    (finish : start + (count + 1) = n)
    (path : (firstRoundProtocol F deg).tree.BranchPath) :
    ClosedClaim (midpointStatement F n deg count start finish path)
      (polynomialFamily F n deg) → Prop :=
  match path with
  | ⟨_, none, _⟩ => fun _ => False
  | ⟨_, some _, _⟩ => closedRelation F n deg D ⟨start + 1, by omega⟩

/-- Admissibility requires the actual closed export to retain the realized original polynomial. -/
def midpointOracleRealized (count start : ℕ) (finish : start + (count + 1) = n)
    (p : Spec.OracleStatement F n deg ())
    (path : (firstRoundProtocol F deg).tree.BranchPath)
    (claim : ClosedClaim (midpointStatement F n deg count start finish path)
      (polynomialFamily F n deg)) : Prop :=
  claim.oracles = (polynomialFamily F n deg).behaviorOfRealizations (fun _ => p)

/-- The actual prefix can turn a false claim true with probability at most one round's error. -/
theorem exportedPrefixRun_soundness {m : ℕ} (D : Fin m ↪ F)
    (count start : ℕ) (finish : start + (count + 1) = n) (A : PFunctor)
    (originalOracle : VirtualOracle (ofPFunctor A) (polynomialFamily F n deg))
    (stmt : Spec.StatementRound F n ⟨start, by omega⟩) (impl : QueryImpl (ofPFunctor A) Id)
    (prover : Prover.Strategy unifSpec (protocol F deg (count + 1)).tree
      (protocol F deg (count + 1)).roles (fun _ => Unit)) (p : Spec.OracleStatement F n deg ())
    (horiginal : originalOracle.eval impl =
      (polynomialFamily F n deg).behaviorOfRealizations (fun _ => p))
    (hfalse : ¬ closedRelation F n deg D ⟨start, by omega⟩ ⟨stmt, originalOracle.eval impl⟩) :
    Pr{let b ← (exportedPrefixRun unifSpec (firstRoundProtocol F deg).tree
      (fun path => (remainingProtocol F deg count path).tree) (firstRoundProtocol F deg).roles
      (fun path => (remainingProtocol F deg count path).roles) (firstRoundProtocol F deg).oracles
      A impl (midpointStatement F n deg count start finish)
      (fun _ => Spec.OracleStatement F n deg) (fun _ => polynomialFamily F n deg)
      (fun _ => Unit) prover
      (firstRoundFragment F n deg unifSpec ($ᵗ F) (Finset.univ.map D).toList count start finish
        A originalOracle stmt))}[
      midpointRelation n deg F D count start finish
        (TypeTree.ExecutionPath.ofTypeTreePath b.1).toBranchPath
        (b.2.2.closeWith ((TypeTree.ExecutionPath.ofTypeTreePath b.1).closingImpl
          (firstRoundProtocol F deg).oracles A impl))] ≤
      (deg : ENNReal) / Fintype.card F := by
  rw [exportedPrefixRun_firstRound]
  refine prEvent_bind_le_of_forall_le _ _ _ ?_
  rintro ⟨q, respond⟩
  change SingleRound.Message F deg at q
  by_cases hcheck : ((Finset.univ.map D).toList.map (fun x => q.val.eval x)).sum = stmt.target
  · simp only [hcheck, ↓reduceIte, bind_assoc, pure_bind]
    let i : Fin n := ⟨start, by omega⟩
    let good : F → Prop := fun r => closedRelation F n deg D i.succ
      ⟨⟨q.val.eval r, Fin.snoc stmt.challenges r⟩,
        (polynomialFamily F n deg).behaviorOfRealizations (fun _ => p)⟩
    have hgood := uniform_successor_soundness n deg F D i stmt p q (by
      change ¬ closedRelation F n deg D ⟨start, by omega⟩
        ⟨stmt, (polynomialFamily F n deg).behaviorOfRealizations (fun _ => p)⟩
      rw [← horiginal]
      exact hfalse) hcheck
    change Pr{let r ← ($ᵗ F); let _next ← respond (some r)}[
      closedRelation F n deg D i.succ
        ⟨⟨q.val.eval r, Fin.snoc stmt.challenges r⟩,
          (originalOracle.sumWeaken (polynomialInterface F deg).spec).eval
            (Access.extendImpl A (polynomialInterface F deg) impl q)⟩] ≤ _
    rw [VirtualOracle.eval_sumWeaken_extendImpl, horiginal]
    have hbound := prEvent_bind_le_prEvent_of_forall_eq_zero ($ᵗ F)
      (fun r => do
        let _next ← respond (some r)
        return good r) good (fun truth => truth) (by
          intro r hr
          simp only [hr, bind_assoc, pure_bind, prEvent_false])
    simpa only [bind_assoc, pure_bind] using hbound.trans hgood
  · simp only [hcheck, ↓reduceIte, bind_assoc, pure_bind]
    change Pr{let _next ← respond none}[False] ≤ _
    simp only [prEvent_false, zero_le]

omit [Fintype F] in
/-- The actual prefix preserves the realized original oracle on every returned branch. -/
theorem exportedPrefixRun_admissibility {m : ℕ} (D : Fin m ↪ F)
    (count start : ℕ) (finish : start + (count + 1) = n) (A : PFunctor)
    (originalOracle : VirtualOracle (ofPFunctor A) (polynomialFamily F n deg))
    (stmt : Spec.StatementRound F n ⟨start, by omega⟩) (impl : QueryImpl (ofPFunctor A) Id)
    (prover : Prover.Strategy unifSpec (protocol F deg (count + 1)).tree
      (protocol F deg (count + 1)).roles (fun _ => Unit)) (p : Spec.OracleStatement F n deg ())
    (horiginal : originalOracle.eval impl =
      (polynomialFamily F n deg).behaviorOfRealizations (fun _ => p)) :
    Pr{let b ← (exportedPrefixRun unifSpec (firstRoundProtocol F deg).tree
      (fun path => (remainingProtocol F deg count path).tree) (firstRoundProtocol F deg).roles
      (fun path => (remainingProtocol F deg count path).roles) (firstRoundProtocol F deg).oracles
      A impl (midpointStatement F n deg count start finish)
      (fun _ => Spec.OracleStatement F n deg) (fun _ => polynomialFamily F n deg)
      (fun _ => Unit) prover
      (firstRoundFragment F n deg unifSpec ($ᵗ F) (Finset.univ.map D).toList count start finish
        A originalOracle stmt))}[
      ¬ midpointOracleRealized n deg F count start finish p
        (TypeTree.ExecutionPath.ofTypeTreePath b.1).toBranchPath
        (b.2.2.closeWith ((TypeTree.ExecutionPath.ofTypeTreePath b.1).closingImpl
          (firstRoundProtocol F deg).oracles A impl))] ≤
      0 := by
  rw [exportedPrefixRun_firstRound]
  refine prEvent_bind_le_of_forall_le _ _ _ ?_
  rintro ⟨q, respond⟩
  change SingleRound.Message F deg at q
  by_cases hcheck : ((Finset.univ.map D).toList.map (fun x => q.val.eval x)).sum = stmt.target
  · simp only [hcheck, ↓reduceIte, bind_assoc, pure_bind]
    change Pr{let r ← ($ᵗ F); let _next ← respond (some r)}[
      ¬ (originalOracle.sumWeaken (polynomialInterface F deg).spec).eval
        (Access.extendImpl A (polynomialInterface F deg) impl q) =
          (polynomialFamily F n deg).behaviorOfRealizations (fun _ => p)] ≤ 0
    rw [VirtualOracle.eval_sumWeaken_extendImpl, horiginal]
    simp only [not_true_eq_false]
    have hzero := prEvent_false (do
      let r ← ($ᵗ F)
      let _next ← respond (some r)
      return ())
    simpa only [bind_assoc, pure_bind] using hzero.le
  · simp only [hcheck, ↓reduceIte, bind_assoc, pure_bind]
    change Pr{let _next ← respond none}[
      ¬ (originalOracle.sumWeaken (polynomialInterface F deg).spec).eval
        (Access.extendImpl A (polynomialInterface F deg) impl q) =
          (polynomialFamily F n deg).behaviorOfRealizations (fun _ => p)] ≤ 0
    rw [VirtualOracle.eval_sumWeaken_extendImpl, horiginal]
    simp only [not_true_eq_false, prEvent_false, le_refl]

set_option backward.isDefEq.respectTransparency false in
/-- Full native Sumcheck is sound against every ordinary prover strategy. From a false initial
claim over a polynomial-realized original oracle, the probability that the actual closed output
satisfies its original-oracle evaluation relation is at most `count * deg / |F|`.

The prover's response to each challenge is an arbitrary effectful native continuation. Its
effects execute after that challenge; no external private-state or message-kernel representation
is assumed. All accumulated source slots remain available, while `originalOracle` identifies the
original oracle view. The final relation is a predicate on the actual output behavior and does not
add a verifier query. -/
theorem execute_soundness {m : ℕ} (D : Fin m ↪ F)
    (count start : ℕ) (finish : start + count = n) (A : PFunctor)
    (originalOracle : VirtualOracle (OracleSpec.ofPFunctor A) (polynomialFamily F n deg))
    (stmt : Spec.StatementRound F n ⟨start, by omega⟩)
    (impl : QueryImpl (OracleSpec.ofPFunctor A) Id)
    (prover : Prover.Strategy unifSpec (protocol F deg count).tree
      (protocol F deg count).roles (fun _ => Unit)) (p : Spec.OracleStatement F n deg ())
    (horiginal : originalOracle.eval impl =
      (polynomialFamily F n deg).behaviorOfRealizations (fun _ => p))
    (hfalse : ¬ closedRelation F n deg D ⟨start, by omega⟩ ⟨stmt, originalOracle.eval impl⟩) :
    Pr{let result ← (execute F n deg unifSpec ($ᵗ F) (Finset.univ.map D).toList
      count start finish A originalOracle stmt impl prover)}[
        result.map (outputRelation F n deg) = some True] ≤
      (count : ENNReal) * deg / Fintype.card F := by
  induction count generalizing start A with
  | zero =>
    subst n
    rw [execute_zero]
    simpa [outputRelation, Core.outputRelation] using
      (fun h => hfalse ((closedRelation_last_iff F start deg D
        ⟨stmt, originalOracle.eval impl⟩).mpr h))
  | succ count ih =>
    let tree := (firstRoundProtocol F deg).tree
    let suffix := fun path => (remainingProtocol F deg count path).tree
    let secondRoles := fun path => (remainingProtocol F deg count path).roles
    let firstOracles := (firstRoundProtocol F deg).oracles
    let middle := midpointStatement F n deg count start finish
    let exportFamily := fun _ : tree.BranchPath => polynomialFamily F n deg
    let prefixProgram := exportedPrefixRun unifSpec tree suffix (firstRoundProtocol F deg).roles
      secondRoles firstOracles A impl middle (fun _ => Spec.OracleStatement F n deg) exportFamily
      (fun _ => Unit) prover
      (firstRoundFragment F n deg unifSpec ($ᵗ F) (Finset.univ.map D).toList count start finish
        A originalOracle stmt)
    let trueMid := fun b : ExportedBoundary unifSpec tree suffix secondRoles firstOracles A
      middle (fun _ => Spec.OracleStatement F n deg) exportFamily (fun _ => Unit) =>
        midpointRelation n deg F D count start finish
          (TypeTree.ExecutionPath.ofTypeTreePath b.1).toBranchPath
          (b.2.2.closeWith ((TypeTree.ExecutionPath.ofTypeTreePath b.1).closingImpl
            firstOracles A impl))
    let admissible := fun b : ExportedBoundary unifSpec tree suffix secondRoles firstOracles A
      middle (fun _ => Spec.OracleStatement F n deg) exportFamily (fun _ => Unit) =>
        midpointOracleRealized n deg F count start finish p
          (TypeTree.ExecutionPath.ofTypeTreePath b.1).toBranchPath
          (b.2.2.closeWith ((TypeTree.ExecutionPath.ofTypeTreePath b.1).closingImpl
            firstOracles A impl))
    have htruth : Pr{let b ← prefixProgram}[trueMid b] ≤
        (deg : ENNReal) / Fintype.card F :=
      exportedPrefixRun_soundness n deg F D count start finish A originalOracle stmt impl
        prover p horiginal hfalse
    have hinvalid : Pr{let b ← prefixProgram}[¬ trueMid b ∧ ¬ admissible b] ≤ 0 :=
      (prEvent_and_le_right prefixProgram (fun b => ¬ trueMid b) (fun b => ¬ admissible b)).trans
        (exportedPrefixRun_admissibility n deg F D count start finish A originalOracle stmt impl
          prover p horiginal)
    have assembled := executeStrategies_appendExported_soundness_ae unifSpec tree suffix
      (firstRoundProtocol F deg).roles secondRoles firstOracles
      (fun path => (remainingProtocol F deg count path).oracles) A impl middle
      (fun _ => Spec.OracleStatement F n deg) exportFamily (fun _ => FinalStatement F n)
      (fun _ => Spec.OracleStatement F n deg) (fun _ => polynomialFamily F n deg) (fun _ => Unit)
      prover
      (firstRoundFragment F n deg unifSpec ($ᵗ F) (Finset.univ.map D).toList count start finish
        A originalOracle stmt)
      (remainingVerifier F n deg unifSpec ($ᵗ F) (Finset.univ.map D).toList count start finish)
      (midpointRelation n deg F D count start finish)
      (midpointOracleRealized n deg F count start finish p) (fun _ => outputRelation F n deg)
      ((deg : ENNReal) / Fintype.card F) 0 ((count : ENNReal) * deg / Fintype.card F)
      htruth hinvalid
    have hsuffix : let : MeasurableSpace (ExportedBoundary unifSpec tree suffix secondRoles
        firstOracles A middle (fun _ => Spec.OracleStatement F n deg) exportFamily
          (fun _ => Unit)) := ⊤
        ∀ᵐ b ∂𝒟[prefixProgram], ¬ trueMid b → admissible b →
        Pr{let result ← (exportedSuffixRun unifSpec tree suffix secondRoles firstOracles
          (fun path => (remainingProtocol F deg count path).oracles) A impl middle
          (fun _ => Spec.OracleStatement F n deg) exportFamily (fun _ => FinalStatement F n)
          (fun _ => Spec.OracleStatement F n deg) (fun _ => polynomialFamily F n deg)
          (fun _ => Unit)
          (remainingVerifier F n deg unifSpec ($ᵗ F) (Finset.univ.map D).toList count start finish)
          b)}[result.2.map (outputRelation F n deg) = some True] ≤
          (count : ENNReal) * deg / Fintype.card F := by
      apply Filter.Eventually.of_forall
      rintro ⟨⟨q, ⟨choice, last⟩⟩, next, mid⟩ hfalseMid hgood
      cases last
      cases choice with
      | none =>
        have hrun := exportedSuffixRun_none F n deg unifSpec ($ᵗ F)
          (Finset.univ.map D).toList count start finish A impl q next mid
        have hzero : Pr{let result ← (pure none : ProbComp
            (Option (ClosedClaim (FinalStatement F n) (polynomialFamily F n deg))))}[
            result.map (outputRelation F n deg) = some True] = 0 := by simp
        rw [← hrun, prEvent_map] at hzero
        exact hzero.le.trans zero_le
      | some r =>
        change ¬ closedRelation F n deg D ⟨start + 1, by omega⟩
          ⟨mid.stmt, mid.oracles.eval
            (Access.extendImpl A (polynomialInterface F deg) impl q)⟩ at hfalseMid
        change mid.oracles.eval (Access.extendImpl A (polynomialInterface F deg) impl q) =
          (polynomialFamily F n deg).behaviorOfRealizations (fun _ => p) at hgood
        have hnext := ih (start + 1) (by omega) (polynomialFamily F n deg).spec.toPFunctor
          (VirtualOracle.id (polynomialFamily F n deg)) mid.stmt
          (mid.oracles.eval (Access.extendImpl A (polynomialInterface F deg) impl q)) next
          (by simpa only [VirtualOracle.eval_id] using hgood)
          (by simpa only [VirtualOracle.eval_id] using hfalseMid)
        have hrun := exportedSuffixRun_some F n deg unifSpec ($ᵗ F)
          (Finset.univ.map D).toList count start finish A impl q r next mid
        rw [← hrun, prEvent_map] at hnext
        exact hnext
    have bound := assembled hsuffix
    rw [execute_eq_appendExported, prEvent_map]
    simp only [Option.map_map]
    refine bound.trans ?_
    simp only [add_zero]
    simp [Nat.cast_succ, div_eq_mul_inv, add_mul, add_comm]


end
end Sumcheck.Interaction.Native

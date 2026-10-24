/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ProofSystem.Sumcheck.Interaction.ComputableSoundness
import ArkLib.ProofSystem.Sumcheck.Interaction.ComputableCompleteness
import ArkLib.Interaction.Oracle.LoggedExecution
import ArkLib.Interaction.Oracle.SourceRouting
import Mathlib.Algebra.Field.ZMod
import Lean.Compiler.IR

/-!
# Actual terminal authentication through native Sumcheck and exported composition

The verifier accepts the honest coefficient message and rejects a forged final value, including
with zero rounds. Ordered source observations distinguish the retained prefix helper from an
unused input with the same honest value. Private prover state and effects survive success and
public abort. Mathematical polynomial views occur only in realization proofs.
-/

open Interaction.Oracle OracleComp OracleSpec
open Sumcheck.Interaction

namespace Sumcheck.Interaction.TerminalCheckTest

abbrev F := ZMod 17
instance : Fact (Nat.Prime 17) := ⟨by decide⟩

abbrev ambientSpec : OracleSpec (Fin 3) := Fin 3 →ₒ F
abbrev inputSpec : OracleSpec (Fin 2 × F) := (Fin 2 × F) →ₒ F

def event (i : Fin 3) : OracleComp ambientSpec F := liftM (ambientSpec.query i)

/-- The two retained inputs compute `2*x` and `-1`, respectively. -/
def inputImpl : QueryImpl inputSpec Id := fun ⟨i, x⟩ => (show F from if i = 0 then 2*x else -1)

/-- The virtual polynomial computes its answer by two actual input-source queries. -/
def originalView : VirtualOracle (ofPFunctor inputSpec.toPFunctor)
    (MultivariateRound.polynomialFamily F 1 1) := ⟨fun q => do
  let a ← liftM ((ofPFunctor inputSpec.toPFunctor).query ((0 : Fin 2), q.2 0))
  let b ← liftM ((ofPFunctor inputSpec.toPFunctor).query ((1 : Fin 2), q.2 0))
  return a+b⟩

/-- Proof-only mathematical view using Mathlib's noncomputable sparse-polynomial arithmetic.
The verifier never constructs or evaluates this representation. -/
noncomputable def mathematicalQ (helper : F) : Sumcheck.Spec.OracleStatement F 1 1 () :=
  ⟨MvPolynomial.C 2 * MvPolynomial.X 0 + MvPolynomial.C helper, by
    rw [MvPolynomial.mem_restrictDegree_iff_degreeOf_le]
    intro i
    apply le_trans (MvPolynomial.degreeOf_add_le _ _ _)
    apply max_le
    · apply le_trans (MvPolynomial.degreeOf_mul_le _ _ _)
      simp only [MvPolynomial.degreeOf_C, MvPolynomial.degreeOf_X, zero_add]
      split <;> omega
    · simp⟩

/-- The actual virtual query program realizes a degree-bounded original polynomial. -/
theorem originalView_realizes : originalView.eval inputImpl =
    (MultivariateRound.polynomialFamily F 1 1).behaviorOfRealizations
      (fun _ => mathematicalQ (-1)) := by
  funext q
  change 2 * q.2 0 + (-1) =
    MvPolynomial.eval q.2 (MvPolynomial.C 2 * MvPolynomial.X 0 + MvPolynomial.C (-1))
  simp only [map_add, map_mul,
    MvPolynomial.eval_C (f := (show Fin 1 → F from q.2)),
    MvPolynomial.eval_X (f := (show Fin 1 → F from q.2))]

def affine (a b : F) : Sumcheck.Impl.Representation.Message F 1 :=
  ⟨CompPoly.CPolynomial.ofArray #[b, a], by
    have hsize := CompPoly.CPolynomial.Raw.Trim.size_le_size (#[b, a] : Array F)
    change (CompPoly.CPolynomial.ofArray #[b, a]).val.size ≤ 2 at hsize
    generalize h : (CompPoly.CPolynomial.ofArray #[b, a]).val.size = size at *
    cases size with
    | zero => simp [CompPoly.CPolynomial.degree, h]
    | succ size =>
      simp only [CompPoly.CPolynomial.degree, h]
      exact_mod_cast (show size ≤ 1 by omega)⟩

def prover (q : Sumcheck.Impl.Representation.Message F 1) :
    Prover.Strategy ambientSpec (Computable.protocol F 1 1).tree
      (Computable.protocol F 1 1).roles (fun _ => F) := do
  let secret ← event 0
  return ⟨q, fun choice =>
    match choice with
    | none => do
      let trailing ← event 2
      return secret + trailing
    | some r => do
      let trailing ← event 2
      return secret + r + trailing⟩

def initial : Sumcheck.Spec.StatementRound F 1 0 := ⟨0, Fin.elim0⟩

def logger : QueryImpl ambientSpec (StateM (List Nat)) := fun i => do
  modify (· ++ [i.val])
  return ![7,3,5] i

abbrev Result := LoggedResult (Computable.protocol F 1 1).tree
  (Computable.protocol F 1 1).oracles inputSpec.toPFunctor (fun _ => F) (fun _ => Bool)

def run (q : Sumcheck.Impl.Representation.Message F 1) : OracleComp ambientSpec Result :=
  executeStrategiesLogged ambientSpec (Computable.protocol F 1 1).tree
    (Computable.protocol F 1 1).roles (Computable.protocol F 1 1).oracles
    inputSpec.toPFunctor inputImpl (prover q)
    (Computable.verifierWithFinalCheck F 1 1 ambientSpec (event 1) [0,1] 1 0 rfl
      inputSpec.toPFunctor originalView initial)

def observed (q : Sumcheck.Impl.Representation.Message F 1) : Result × List Nat :=
  (simulateQ logger (run q)).run []

/-- Project an already completed run without unfolding its execution during elaboration. -/
def summarize {tree : _root_.Interaction.Oracle.TypeTree} {oracles : tree.OracleDecoration}
    {A : PFunctor}
    (result : LoggedResult tree oracles A (fun _ => F) (fun _ => Bool) × List Nat) :
    Bool × F × Nat × List Nat :=
  (result.1.verifierOut, result.1.proverOut, result.1.sourceLog.length, result.2)

abbrev oneRoundAccess := Access.extend inputSpec.toPFunctor
  (Native.Core.messageInterface F (Sumcheck.Impl.Representation.Message F 1)
    (Sumcheck.Impl.Representation.evaluate F 1))

def encodeEntry (entry : (query : oneRoundAccess.A) × oneRoundAccess.B query) : String × F :=
  match entry with
  | ⟨.inl ⟨i, x⟩, answer⟩ => (s!"input[{i.val}]({reprStr (show F from x)})", answer)
  | ⟨.inr x, answer⟩ => (s!"message({reprStr (show F from x)})", answer)

def encodeSource (path : (Computable.protocol F 1 1).tree.ExecutionPath) :
    QueryLog (ofPFunctor (TypeTree.accessAfter (Computable.protocol F 1 1).tree
      (Computable.protocol F 1 1).oracles inputSpec.toPFunctor path.toBranchPath)) →
      List (String × F) := by
  rcases path with ⟨message, choice, stop⟩
  cases choice with
  | none => exact fun log => log.map encodeEntry
  | some r => exact fun log => log.map encodeEntry

def observations (q : Sumcheck.Impl.Representation.Message F 1) : List (String × F) :=
  let result := (observed q).1
  encodeSource result.path result.sourceLog

def summary (q : Sumcheck.Impl.Representation.Message F 1) : Bool × F × Nat × List Nat :=
  summarize (observed q)

/-- A zero-round native protocol still executes final authentication at its retained prefix. -/
abbrev FinalResult := LoggedResult (Computable.protocol F 1 0).tree
  (Computable.protocol F 1 0).oracles inputSpec.toPFunctor (fun _ => F) (fun _ => Bool)

def runFinal (target : F) : OracleComp ambientSpec FinalResult :=
  executeStrategiesLogged ambientSpec (Computable.protocol F 1 0).tree
    (Computable.protocol F 1 0).roles (Computable.protocol F 1 0).oracles
    inputSpec.toPFunctor inputImpl (OutP := fun _ => F) (9 : F)
    (Computable.verifierWithFinalCheck F 1 1 ambientSpec (event 1) [0, 1] 0 1 rfl
      inputSpec.toPFunctor originalView ⟨target, fun _ => 3⟩)

def summaryFinal (target : F) : Bool × F × Nat × List Nat :=
  summarize ((simulateQ logger (runFinal target)).run [])

namespace Composed

open PFunctor.FreeM.Displayed (Decoration)

@[reducible]
def helperInterface : OracleInterface F where
  Query := Unit
  toOC.spec := Unit →ₒ F
  toOC.impl _ := read

local notation "family" => MultivariateRound.polynomialFamily F 1 1
abbrev firstProtocol : _root_.Interaction.Oracle.Protocol :=
  .oracleWith F helperInterface .done
abbrev secondProtocol : _root_.Interaction.Oracle.Protocol := Computable.protocol F 1 1
abbrev combined : _root_.Interaction.Oracle.Protocol :=
  ⟨PFunctor.FreeM.append firstProtocol.tree (fun _ => secondProtocol.tree),
    Decoration.append firstProtocol.roles (fun _ => secondProtocol.roles),
    Decoration.append firstProtocol.oracles (fun _ => secondProtocol.oracles)⟩
abbrev prefixAccess := Access.extend inputSpec.toPFunctor helperInterface

/-- The exported polynomial retains a fixed input and the actual prefix message. -/
def exportView : VirtualOracle (ofPFunctor prefixAccess) family := ⟨fun q => do
  let input : F ← liftM ((ofPFunctor prefixAccess).query (.inl ((0 : Fin 2), q.2 0)))
  let helper : F ← liftM ((ofPFunctor prefixAccess).query (.inr ()))
  return input + helper⟩

/-- Realization holds for every helper, including a malicious prefix message. -/
theorem exportView_realizes (helper : F) :
    exportView.eval (Access.extendImpl inputSpec.toPFunctor helperInterface inputImpl helper) =
      (family).behaviorOfRealizations (fun _ => mathematicalQ helper) := by
  funext q
  change 2 * q.2 0 + helper =
    MvPolynomial.eval q.2 (MvPolynomial.C 2 * MvPolynomial.X 0 + MvPolynomial.C helper)
  simp only [map_add, map_mul,
    MvPolynomial.eval_C (f := (show Fin 1 → F from q.2)),
    MvPolynomial.eval_X (f := (show Fin 1 → F from q.2))]

def firstVerifier : Verifier.Fragment ambientSpec firstProtocol.tree firstProtocol.roles
    firstProtocol.oracles inputSpec.toPFunctor (fun p =>
      OpenClaim (ofPFunctor (TypeTree.accessAfter firstProtocol.tree firstProtocol.oracles
        inputSpec.toPFunctor p)) (Sumcheck.Spec.StatementRound F 1 0) family) :=
  pure ⟨initial, exportView⟩

/-- The suffix is authored over Q alone, with no access to its raw input or helper sources. -/
def secondVerifier (_ : firstProtocol.tree.BranchPath)
    (stmt : Sumcheck.Spec.StatementRound F 1 0) :
    Verifier.Strategy ambientSpec secondProtocol.tree secondProtocol.roles secondProtocol.oracles
      (family).spec.toPFunctor (TerminalClaim secondProtocol (family).spec.toPFunctor
        (fun _ => Computable.FinalStatement F 1) (fun _ => family)) :=
  Computable.verifier F 1 1 ambientSpec (event 1) [0, 1] 1 0 rfl (family).spec.toPFunctor
    (VirtualOracle.id family) stmt

/-- Exported composition routes the native final claim back to actual retained sources. -/
def reductionVerifier : Verifier.Strategy ambientSpec combined.tree combined.roles combined.oracles
    inputSpec.toPFunctor (TerminalClaim combined inputSpec.toPFunctor
      (fun _ => Computable.FinalStatement F 1) (fun _ => family)) :=
  Verifier.appendExported ambientSpec firstProtocol.tree (fun _ => secondProtocol.tree)
    firstProtocol.roles (fun _ => secondProtocol.roles)
    firstProtocol.oracles (fun _ => secondProtocol.oracles) inputSpec.toPFunctor
    (fun _ => Sumcheck.Spec.StatementRound F 1 0)
    (fun _ => Sumcheck.Spec.OracleStatement F 1 1) (fun _ => family)
    (fun _ => Computable.FinalStatement F 1)
    (fun _ => Sumcheck.Spec.OracleStatement F 1 1) (fun _ => family)
    firstVerifier secondVerifier

/-- A complete native argument executes the routed final query action. -/
def verifier : Verifier.Strategy ambientSpec combined.tree combined.roles combined.oracles
    inputSpec.toPFunctor (fun _ => Bool) :=
  Verifier.Fragment.mapOutput ambientSpec (fun path action =>
    Native.Core.checkFinalResult F 1 1 ambientSpec
      (TypeTree.accessAfter combined.tree combined.oracles inputSpec.toPFunctor path) action)
    reductionVerifier

/-- Ordinary native continuations cross both fragments with their private state intact. -/
def prover (helper : F) (q : Sumcheck.Impl.Representation.Message F 1) :
    Prover.Strategy ambientSpec combined.tree combined.roles (fun _ => F) := do
  let secret ← event 0
  return ⟨helper, do
    return ⟨q, fun choice =>
      match choice with
      | none => do
        let trailing ← event 2
        return secret + trailing
      | some r => do
        let trailing ← event 2
        return secret + r + trailing⟩⟩

abbrev Result := LoggedResult combined.tree combined.oracles inputSpec.toPFunctor
  (fun _ => F) (fun _ => Bool)

def run (helper : F) (q : Sumcheck.Impl.Representation.Message F 1) :
    OracleComp ambientSpec Result :=
  executeStrategiesLogged ambientSpec combined.tree combined.roles combined.oracles
    inputSpec.toPFunctor inputImpl (prover helper q) verifier

def observed (helper : F) (q : Sumcheck.Impl.Representation.Message F 1) : Result × List Nat :=
  (simulateQ logger (run helper q)).run []

abbrev finalAccess := Access.extend prefixAccess
  (Native.Core.messageInterface F (Sumcheck.Impl.Representation.Message F 1)
    (Sumcheck.Impl.Representation.evaluate F 1))

def encodeEntry (entry : (query : finalAccess.A) × finalAccess.B query) : String × F :=
  match entry with
  | ⟨.inl (.inl ⟨i, x⟩), answer⟩ => (s!"input[{i.val}]({reprStr (show F from x)})", answer)
  | ⟨.inl (.inr ()), answer⟩ => ("helper", answer)
  | ⟨.inr x, answer⟩ => (s!"message({reprStr (show F from x)})", answer)

def encodeSource (path : combined.tree.ExecutionPath) :
    QueryLog (ofPFunctor (TypeTree.accessAfter combined.tree combined.oracles
      inputSpec.toPFunctor path.toBranchPath)) → List (String × F) := by
  rcases path with ⟨helper, message, choice, stop⟩
  cases choice with
  | none => exact fun log => log.map encodeEntry
  | some r => exact fun log => log.map encodeEntry

def observations (helper : F) (q : Sumcheck.Impl.Representation.Message F 1) :
    List (String × F) :=
  let result := (observed helper q).1
  encodeSource result.path result.sourceLog

def summary (helper : F) (q : Sumcheck.Impl.Representation.Message F 1) :
    Bool × F × Nat × List Nat :=
  summarize (observed helper q)

end Composed

/-- The named complete endpoint executes the same verifier with arbitrary private prover output. -/
def endpointSummary (q : Sumcheck.Impl.Representation.Message F 1) : Bool × List Nat :=
  (simulateQ logger (Computable.executeWithFinalCheck F 1 1 ambientSpec (event 1) [0,1]
    1 0 rfl inputSpec.toPFunctor originalView initial inputImpl (prover q))).run []

/-- Change only the final private return type of the actual native prover. -/
def erasedProver (q : Sumcheck.Impl.Representation.Message F 1) :
    Prover.Strategy ambientSpec (Computable.protocol F 1 1).tree
      (Computable.protocol F 1 1).roles (fun _ => Unit) :=
  Interaction.StrategyOver.TwoParty.Focal.mapOutput (fun _ _ => (() : Unit)) (prover q)

/-- Erasing the private return retains the same transcript and ambient effect order. -/
def erasedEndpointSummary (q : Sumcheck.Impl.Representation.Message F 1) : Bool × List Nat :=
  (simulateQ logger (Computable.executeWithFinalCheck F 1 1 ambientSpec (event 1) [0,1]
    1 0 rfl inputSpec.toPFunctor originalView initial inputImpl
    (erasedProver q))).run []

namespace FalseInput

open scoped BigOperators ProbabilityTheory ENNReal
open Finset

def domain : Fin 2 ↪ F := ⟨fun i => i.val, by decide⟩
theorem domain_perm : ([0, 1] : List F).Perm (Finset.univ.map domain).toList := by
  apply List.perm_of_nodup_nodup_toFinset_eq (by decide) (Finset.nodup_toList _)
  rw [Finset.toList_toFinset]
  decide

abbrev inputSpec : OracleSpec Unit := Unit →ₒ F
def inputImpl : QueryImpl inputSpec Id := fun _ => 0
def zeroView : VirtualOracle (ofPFunctor inputSpec.toPFunctor)
    (MultivariateRound.polynomialFamily F 1 1) := ⟨fun _ => pure (0 : F)⟩
theorem zeroView_realizes : zeroView.eval inputImpl =
    (MultivariateRound.polynomialFamily F 1 1).behaviorOfRealizations
      (fun _ => (0 : Sumcheck.Spec.OracleStatement F 1 1 ())) := by
  funext q
  change (0 : F) = MvPolynomial.eval q.2 (0 : MvPolynomial (Fin 1) F)
  simp only [map_zero]
def falseInitial : Sumcheck.Spec.StatementRound F 1 0 := ⟨1, Fin.elim0⟩
theorem falseInitial_false : ¬ MultivariateRound.closedRelation F 1 1 domain 0
    ⟨falseInitial, zeroView.eval inputImpl⟩ := by
  intro h
  change (∑ x ∈ (Finset.univ.map domain) ^ᶠ (1 - 0), (0 : F)) = 1 at h
  simp at h

/-- This private-output prover passes the local sum and wins only at the root of X. -/
def falseClaimProver : Prover.Strategy unifSpec (Computable.protocol F 1 1).tree
    (Computable.protocol F 1 1).roles (fun _ => F) := by
  refine pure ⟨affine 1 0, ?_⟩
  intro choice
  cases choice <;> exact pure (7 : F)

def falseClaimExecution : ProbComp Bool :=
  Computable.executeWithFinalCheck F 1 1 unifSpec ($ᵗ F) [0, 1] 1 0 rfl
    inputSpec.toPFunctor zeroView falseInitial inputImpl falseClaimProver

theorem falseClaim_bound :
    Pr{let accepted ← falseClaimExecution}[accepted = true] ≤ (1 : ENNReal) / 17 := by
  simpa only [falseClaimExecution, Nat.cast_one, one_mul, ZMod.card, Nat.cast_ofNat] using
    Computable.executeWithFinalCheck_soundness 1 1 F domain [0, 1] domain_perm 1 0 rfl
      inputSpec.toPFunctor zeroView falseInitial inputImpl falseClaimProver 0 zeroView_realizes
      falseInitial_false

example : (1 : ENNReal) / 17 < 1 := by norm_num
example : #{r : F | r = 0} = 1 := by decide

theorem zero_degree : ∀ j : Fin 1, (0 : CPoly.CMvPolynomial 1 F).degreeOf j ≤ 1 := by
  intro j
  rw [congrFun (CPoly.degreeOf_equiv (S := F) (p := (0 : CPoly.CMvPolynomial 1 F))) j]
  simp

theorem zero_computational_realizes : zeroView.eval inputImpl =
    (MultivariateRound.polynomialFamily F 1 1).behaviorOfRealizations
      (fun _ => Sumcheck.Impl.Computable.toOracleStatement 0 zero_degree) := by
  funext q
  change (0 : F) = MvPolynomial.eval q.2
    (CPoly.fromCMvPolynomial (0 : CPoly.CMvPolynomial 1 F))
  simp

theorem zero_current : MultivariateRound.closedRelation F 1 1 domain 0
    ⟨initial, zeroView.eval inputImpl⟩ := by
  change (∑ x ∈ (Finset.univ.map domain) ^ᶠ (1 - 0), (0 : F)) = 0
  simp

/-- Both verifier enumeration and honest computational projection execute on concrete data. -/
def honestExecution : OracleComp ambientSpec Bool :=
  Computable.executeWithFinalCheck F 1 1 ambientSpec (event 1) [0, 1] 1 0 rfl
    inputSpec.toPFunctor zeroView initial inputImpl
    (Computable.honestProver F 1 1 domain ambientSpec 1 0 rfl initial 0 zero_degree)

theorem honest_support : ∀ accepted ∈ support honestExecution, accepted = true :=
  Computable.executeWithFinalCheck_support_completeness F 1 1 domain ambientSpec (event 1)
    [0, 1] domain_perm 1 0 rfl inputSpec.toPFunctor zeroView initial inputImpl 0 zero_degree
    zero_computational_realizes zero_current

def honestSummary : Bool × List Nat := (simulateQ logger honestExecution).run []

end FalseInput

-- These checks evaluate genuine native programs through an ordinary external caller.
open Lean Elab Command

run_cmd do
  unless FalseInput.honestSummary == (true, [1]) do
    throwError "complete verifier rejected the computational honest strategy"
  unless summaryFinal 5 == (true, 9, 2, []) do
    throwError "zero-round honest source authentication failed"
  unless summaryFinal 0 == (false, 9, 2, []) do
    throwError "zero-round forged source claim was accepted"
  unless summary (affine 2 (-1)) == (true, 15, 5, [0, 1, 2]) do
    throwError "honest native execution lost its private output or effects"
  unless summary (affine 0 0) == (false, 15, 5, [0, 1, 2]) do
    throwError "native execution accepted a forged final value"
  unless summary (affine 0 1) == (false, 12, 2, [0, 2]) do
    throwError "public abort lost its native prover continuation"
  unless (observations (affine 2 (-1))).map Prod.snd == [16, 1, 5, 6, 16] do
    throwError "honest execution changed its ordered source queries"
  unless (observations (affine 0 0)).map Prod.snd == [0, 0, 0, 6, 16] do
    throwError "forged execution skipped retained original source queries"
  unless (observations (affine 0 1)).map Prod.snd == [1, 1] do
    throwError "public abort made unexpected source queries"
  unless Composed.summary (-1) (affine 2 (-1)) == (true, 15, 5, [0, 1, 2]) do
    throwError "exported composition rejected the honest retained helper"
  unless Composed.summary (-1) (affine 0 0) == (false, 15, 5, [0, 1, 2]) do
    throwError "exported composition accepted a forged final value"
  unless Composed.summary 0 (affine 2 (-1)) == (false, 15, 5, [0, 1, 2]) do
    throwError "exported composition ignored the actual retained helper"
  unless Composed.summary (-1) (affine 0 1) == (false, 12, 2, [0, 2]) do
    throwError "exported composition lost the abort continuation"
  unless (Composed.observations (-1) (affine 2 (-1))).map Prod.snd == [16, 1, 5, 6, 16] do
    throwError "exported honest source-query order changed"
  unless (Composed.observations 0 (affine 2 (-1))).map Prod.snd == [16, 1, 5, 6, 0] do
    throwError "exported composition substituted an earlier input for the actual helper"
  unless erasedEndpointSummary (affine 2 (-1)) == (true, [0, 1, 2]) &&
      erasedEndpointSummary (affine 0 0) == (false, [0, 1, 2]) &&
      erasedEndpointSummary (affine 0 1) == (false, [0, 2]) do
    throwError "private-output erasure changed native acceptance or effects"
  unless endpointSummary (affine 2 (-1)) == (true, [0, 1, 2]) do
    throwError "complete endpoint rejected the honest native prover"
  unless endpointSummary (affine 0 0) == (false, [0, 1, 2]) do
    throwError "complete endpoint accepted a forged native final claim"
  unless endpointSummary (affine 0 1) == (false, [0, 2]) do
    throwError "complete endpoint lost abort-response effects"

run_cmd do
  for name in #[``Native.Core.checkFinalClaim, ``Native.Core.checkFinalResult,
      ``Native.Core.accepts, ``Native.Core.verifierWithFinalCheck,
      ``Native.Core.executeWithFinalCheck, ``FalseInput.falseClaimExecution,
      ``FalseInput.honestExecution, ``FalseInput.honestSummary, ``originalView, ``prover,
      ``run, ``summary,
      ``runFinal, ``summaryFinal, ``endpointSummary, ``erasedEndpointSummary, ``Composed.exportView,
      ``Composed.firstVerifier, ``Composed.secondVerifier, ``Composed.reductionVerifier,
      ``Composed.verifier, ``Composed.prover, ``Composed.run, ``Composed.summary] do
    unless (Lean.IR.findEnvDecl (← getEnv) name).isSome do
      throwError "expected compiler IR for `{name}`"

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``Native.Core.simulate_checkFinalClaim, ``Native.Core.simulate_checkFinalResult,
      ``Native.Core.accepts_eq_true_iff, ``Native.Core.executeStrategies_verifierWithFinalCheck,
      ``Native.Core.executeWithFinalCheck_eq_execute,
      ``Native.Core.executeWithFinalCheck_eq_execute_eraseOutput,
      ``Native.Core.execute_eq_of_domain_perm,
      ``Native.Core.executeWithFinalCheck_eq_of_domain_perm,
      ``Computable.executeWithFinalCheck_soundness,
      ``Computable.executeWithFinalCheck_support_completeness, ``originalView_realizes,
      ``Composed.exportView_realizes, ``FalseInput.zeroView_realizes,
      ``FalseInput.falseInitial_false, ``FalseInput.falseClaim_bound,
      ``FalseInput.domain_perm, ``FalseInput.zero_computational_realizes,
      ``FalseInput.honest_support] do
    let axioms ← collectAxioms name
    unless axioms.all allowed.contains do
      throwError "`{name}` depends on unexpected axioms: {axioms}"

end Sumcheck.Interaction.TerminalCheckTest

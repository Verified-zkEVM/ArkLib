/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.ProofSystem.Sumcheck.Interaction.ComputableCompleteness
import ArkLib.Interaction.Oracle.LoggedExecution
import ArkLib.Interaction.Oracle.SourceRouting
import Mathlib.Algebra.Field.ZMod

/-!
# Compiled native Sumcheck checks

The sent polynomials are CompPoly coefficient arrays. These checks run ordinary native strategies
through the shared executor and observe continuation effects, rejection, and the retained original
oracle. The fixed challenge handler is a deterministic test fixture, not a randomness generator.
-/

namespace SumcheckRuntime

open OracleComp OracleSpec Interaction.Oracle
open Sumcheck.Interaction

abbrev F := ZMod 17

instance : Fact (Nat.Prime 17) := ⟨by decide⟩

/-- Construct a two-coefficient array, trimming a zero leading coefficient. -/
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

abbrev events : OracleSpec (Fin 4) := Fin 4 →ₒ F

def event (i : Fin 4) : OracleComp events F := liftM (events.query i)

/-- The second message depends on both private samples and the first public challenge. -/
def lastProver (a b r : F) : Prover.Strategy events (Computable.protocol F 1 1).tree
    (Computable.protocol F 1 1).roles (fun _ => Unit) := by
  refine pure ⟨affine (b + a) (a * r + 1), ?_⟩
  intro choice
  cases choice <;> exact do
    let _ ← event 3
    return ()

/-- Private memory is captured in the native continuation, with effects on either public branch. -/
def adaptive : Prover.Strategy events (Computable.protocol F 1 2).tree
    (Computable.protocol F 1 2).roles (fun _ => Unit) := by
  refine do
    let a ← event 0
    return ⟨affine a 1, ?_⟩
  intro choice
  cases choice with
  | none => exact do
      let _ ← event 2
      return ()
  | some r => exact do
      let b ← event 2
      return lastProver a b r

def original : (MultivariateRound.polynomialFamily F 2 1).Behavior := fun _ => (0 : F)

def initial : Sumcheck.Spec.StatementRound F 2 0 := ⟨1, Fin.elim0⟩

def record : QueryImpl events (StateM (List (Fin 4))) := fun i => do
  modify (fun seen => seen ++ [i])
  return ![7, 3, 5, 11] i

def run (domain : List F) :=
  Computable.execute F 2 1 events (event 1) domain 2 0 (by decide)
    (MultivariateRound.polynomialFamily F 2 1).spec.toPFunctor
    (VirtualOracle.id (MultivariateRound.polynomialFamily F 2 1))
    initial original adaptive

/-- Observe the scalar output and the original oracle separately from verifier acceptance. -/
def observe (domain : List F) : Option (F × F × F × F) × List (Fin 4) :=
  (simulateQ record ((fun result => result.map fun claim =>
    (claim.stmt.target, claim.stmt.challenges ⟨0, by decide⟩,
      claim.stmt.challenges ⟨1, by decide⟩,
      claim.oracles ⟨(), claim.stmt.challenges⟩)) <$> run domain)).run []

def check (label : String) (ok : Unit → Bool) : IO Unit := do
  unless ok () do throw (IO.userError s!"Sumcheck runtime check failed: {label}")
  IO.println s!"ok: {label}"

def runChecks : IO Unit := do
  check "Horner evaluation, including trimmed zero leading coefficient" fun _ =>
    Sumcheck.Impl.Representation.evaluate F 1 (affine 7 1) 3 == 5 &&
    Sumcheck.Impl.Representation.evaluate F 1 (affine 0 4) 9 == 4
  check "two rounds preserve private memory and effect order" fun _ =>
    observe [0] == (some (7, 3, 3, 0), [0, 1, 2, 1, 3])
  check "public abort runs the prover response and stops before the challenge" fun _ =>
    observe [] == (none, [0, 2])


/-- A directly constructed polynomial `x² + 3xy + 2y² + 5`. -/
def quadratic : CPoly.CMvPolynomial 2 F :=
  let x := CPoly.CMvPolynomial.X (0 : Fin 2)
  let y := CPoly.CMvPolynomial.X (1 : Fin 2)
  x ^ 2 + CPoly.CMvPolynomial.C 3 * x * y + CPoly.CMvPolynomial.C 2 * y ^ 2 +
    CPoly.CMvPolynomial.C 5

theorem quadratic_degree : ∀ j, quadratic.degreeOf j ≤ 2 := by
  intro j
  rw [congrFun (CPoly.degreeOf_equiv (S := F) (p := quadratic)) j]
  change (CPoly.polyRingEquiv (n := 2) (R := F) quadratic).degreeOf j ≤ 2
  simp only [quadratic, map_add, map_mul, map_pow, CPoly.coe_polyRingEquiv,
    CPoly.CMvPolynomial.fromCMvPolynomial_X, CPoly.CMvPolynomial.fromCMvPolynomial_C]
  have hx : (MvPolynomial.X (0 : Fin 2) : MvPolynomial (Fin 2) F).degreeOf j ≤ 1 := by
    simp only [MvPolynomial.degreeOf_X]
    split <;> omega
  have hy : (MvPolynomial.X (1 : Fin 2) : MvPolynomial (Fin 2) F).degreeOf j ≤ 1 := by
    simp only [MvPolynomial.degreeOf_X]
    split <;> omega
  refine (MvPolynomial.degreeOf_add_le j _ _).trans (max_le ?_ ?_)
  · refine (MvPolynomial.degreeOf_add_le j _ _).trans (max_le ?_ ?_)
    · refine (MvPolynomial.degreeOf_add_le j _ _).trans (max_le ?_ ?_)
      · exact (MvPolynomial.degreeOf_pow_le j _ 2).trans (by omega)
      · refine (MvPolynomial.degreeOf_mul_le j _ _).trans ?_
        have hcx := (MvPolynomial.degreeOf_C_mul_le _ j (3 : F)).trans hx
        omega
    · exact (MvPolynomial.degreeOf_C_mul_le _ j (2 : F)).trans
        ((MvPolynomial.degreeOf_pow_le j _ 2).trans (by omega))
  · simp

def three : Fin 3 ↪ F := ⟨fun i => (i.val : F), by decide⟩

def quadraticOriginal : (MultivariateRound.polynomialFamily F 2 2).Behavior :=
  Sumcheck.Impl.Computable.inputImpl quadratic 2

def quadraticInitial : Sumcheck.Spec.StatementRound F 2 0 := ⟨15, Fin.elim0⟩

/-- Fixed challenge `4`; the log counts its actual native sampling queries. -/
def quadraticRecord : QueryImpl events (StateM (List (Fin 4))) := fun i => do
  modify (fun seen => seen ++ [i])
  return 4

def quadraticRun :=
  Computable.execute F 2 2 events (event 1) [0, 1, 2] 2 0 (by decide)
    (MultivariateRound.polynomialFamily F 2 2).spec.toPFunctor
    (VirtualOracle.id (MultivariateRound.polynomialFamily F 2 2))
    quadraticInitial quadraticOriginal
    (Computable.honestProver F 2 2 three events 2 0 (by decide) quadraticInitial
      quadratic quadratic_degree)

def quadraticObserve : Option (F × F × F × F) × List (Fin 4) :=
  (simulateQ quadraticRecord ((fun result => result.map fun claim =>
    (claim.stmt.target, claim.stmt.challenges ⟨0, by decide⟩,
      claim.stmt.challenges ⟨1, by decide⟩,
      claim.oracles ⟨(), claim.stmt.challenges⟩)) <$> quadraticRun)).run []

/-- The complete endpoint also runs actual indexed-domain honest message generation. -/
def quadraticAuthenticatedRun :=
  Computable.executeWithFinalCheck F 2 2 events (event 1) [0, 1, 2] 2 0 (by decide)
    (MultivariateRound.polynomialFamily F 2 2).spec.toPFunctor
    (VirtualOracle.id (MultivariateRound.polynomialFamily F 2 2))
    quadraticInitial quadraticOriginal
    (Computable.honestProver F 2 2 three events 2 0 (by decide) quadraticInitial
      quadratic quadratic_degree)

def quadraticAuthenticatedObserve (_ : Unit) : Bool × List (Fin 4) :=
  (simulateQ quadraticRecord quadraticAuthenticatedRun).run []

def quadraticFinal : Sumcheck.Spec.StatementRound F 2 (Fin.last 2) := ⟨16, ![4, 4]⟩

def quadraticZeroRun :=
  Computable.execute F 2 2 events (event 1) [] 0 2 (by decide)
    (MultivariateRound.polynomialFamily F 2 2).spec.toPFunctor
    (VirtualOracle.id (MultivariateRound.polynomialFamily F 2 2))
    quadraticFinal quadraticOriginal
    (Computable.honestProver F 2 2 three events 0 2 (by decide) quadraticFinal
      quadratic quadratic_degree)

def quadraticZeroObserve : Option (F × F × F × F) × List (Fin 4) :=
  (simulateQ quadraticRecord ((fun result => result.map fun claim =>
    (claim.stmt.target, claim.stmt.challenges ⟨0, by decide⟩,
      claim.stmt.challenges ⟨1, by decide⟩,
      claim.oracles ⟨(), claim.stmt.challenges⟩)) <$> quadraticZeroRun)).run []

/-- The total sum `117`, first-round value `109`, and final value `101`, reduced modulo `17`,
are calculated independently of the projection implementation. -/
def quadraticChecks : IO Unit := do
  check "direct multivariate quadratic and cross term" fun _ =>
    (([0, 1, 2] : List F).map fun x =>
      (([0, 1, 2] : List F).map fun y => quadratic.eval ![x, y]).sum).sum == 15 &&
    quadratic.eval ![4, 4] == 16 &&
    (Sumcheck.Impl.Computable.projectedMessage three (0 : Fin 2) Fin.elim0 quadratic
      quadratic_degree).val.evalHorner 4 == 7
  check "honest native two rounds and retained computational original" fun _ =>
    quadraticObserve == (some (16, 4, 4, 16), [1, 1])
  check "complete verifier accepts actual computational honest messages" fun _ =>
    quadraticAuthenticatedObserve () == (true, [1, 1])
  check "zero rounds retain computational original without sampling" fun _ =>
    quadraticZeroObserve == (some (16, 4, 4, 16), [])

end SumcheckRuntime

open OracleComp OracleSpec Interaction.Oracle
open Sumcheck.Interaction

namespace SumcheckRuntime.TerminalAuthentication

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

/-- Independently calculated outcomes exercise the complete executable native endpoint. -/
def runChecks : IO Unit := do
  check "zero rounds still authenticate the retained original source" fun _ =>
    summaryFinal 5 == (true, 9, 2, []) && summaryFinal 0 == (false, 9, 2, [])
  check "final source check accepts the honest round message" fun _ =>
    summary (affine 2 (-1)) == (true, 15, 5, [0, 1, 2]) &&
    (observations (affine 2 (-1))).map Prod.snd == [16, 1, 5, 6, 16]
  check "round-sum success cannot hide a forged final value" fun _ =>
    summary (affine 0 0) == (false, 15, 5, [0, 1, 2]) &&
    (observations (affine 0 0)).map Prod.snd == [0, 0, 0, 6, 16]
  check "terminal authentication preserves public-abort response effects" fun _ =>
    summary (affine 0 1) == (false, 12, 2, [0, 2]) &&
    (observations (affine 0 1)).map Prod.snd == [1, 1]
  check "exported native composition accepts the retained honest helper" fun _ =>
    Composed.summary (-1) (affine 2 (-1)) == (true, 15, 5, [0, 1, 2]) &&
    (Composed.observations (-1) (affine 2 (-1))).map Prod.snd == [16, 1, 5, 6, 16]
  check "exported composition queries the actual helper instead of an earlier input slot" fun _ =>
    Composed.summary 0 (affine 2 (-1)) == (false, 15, 5, [0, 1, 2]) &&
    (Composed.observations 0 (affine 2 (-1))).map Prod.snd == [16, 1, 5, 6, 0]
  check "exported composition rejects a forgery and preserves the abort continuation" fun _ =>
    Composed.summary (-1) (affine 0 0) == (false, 15, 5, [0, 1, 2]) &&
    Composed.summary (-1) (affine 0 1) == (false, 12, 2, [0, 2])
  check "named complete endpoint retains arbitrary private-output prover effects" fun _ =>
    endpointSummary (affine 2 (-1)) == (true, [0, 1, 2]) &&
    endpointSummary (affine 0 0) == (false, [0, 1, 2]) &&
    endpointSummary (affine 0 1) == (false, [0, 2])
  check "private-output erasure preserves native acceptance and ambient effects" fun _ =>
    erasedEndpointSummary (affine 2 (-1)) == (true, [0, 1, 2]) &&
    erasedEndpointSummary (affine 0 0) == (false, [0, 1, 2]) &&
    erasedEndpointSummary (affine 0 1) == (false, [0, 2])

end SumcheckRuntime.TerminalAuthentication

def main : IO Unit := do
  SumcheckRuntime.runChecks
  SumcheckRuntime.quadraticChecks
  SumcheckRuntime.TerminalAuthentication.runChecks

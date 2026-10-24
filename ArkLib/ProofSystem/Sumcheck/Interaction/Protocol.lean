/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.ProofSystem.Sumcheck.Interaction.MultivariateRound
public import ArkLib.Interaction.Oracle.Sequential

/-!
# Native Sumcheck with a public abort branch

The full protocol alternates a degree-bounded oracle message with the verifier's optional field
challenge. `none` publicly aborts the interaction; `some r` continues the native tree. Ordinary
prover continuations retain their own memory and effects. The restricted verifier queries only
the latest sent polynomial, retaining all earlier access slots and exporting the original oracle
through a virtual view. At the final leaf it returns an evaluation claim without querying the
original polynomial. Truth of that claim is a separate relation. The complete verifier binds that
terminal action and queries the retained original source at the returned point before accepting.
Its execution has exactly the base verifier's closed-relation acceptance event.
-/

@[expose] public section

open Interaction Interaction.Oracle

namespace Sumcheck.Interaction.Native.Core

open OracleComp OracleSpec
open SingleRound MultivariateRound


variable (R : Type) [CommSemiring R] (n deg : ℕ) (M : Type) (evaluate : M → R → R)

/-- Evaluation-only access to the actual round message. -/
@[reducible]
def messageInterface : OracleInterface M where
  Query := R
  toOC.spec := R →ₒ R
  toOC.impl x := do return evaluate (← read) x

/-- Each failed sum check takes a terminal public abort branch. -/
def protocol : ℕ → Protocol
  | 0 => .done
  | count + 1 => .oracleWith M (messageInterface R M evaluate)
      (.public .receiver (Option R) fun choice =>
        match choice with
        | none => .done
        | some _ => protocol count)

/-- One oracle polynomial and a public challenge, with `none` announcing rejection. -/
def firstRoundProtocol : Protocol :=
  .oracleWith M (messageInterface R M evaluate)
    (.public .receiver (Option R) fun _ => .done)
/-- Rejection ends the protocol; a successful challenge leaves the remaining rounds. -/
def remainingProtocol (count : ℕ)
    (path : (firstRoundProtocol R M evaluate).tree.BranchPath) : Protocol :=
  match path.2.1 with
  | none => .done
  | some _ => protocol R M evaluate count
omit [CommSemiring R] in
/-- The existing native protocol is the first round followed by the remaining public branch. -/
theorem protocol_succ_eq_append (count : ℕ) : protocol R M evaluate (count + 1) =
    ⟨PFunctor.FreeM.append (firstRoundProtocol R M evaluate).tree
        (fun path => (remainingProtocol R M evaluate count path).tree),
      PFunctor.FreeM.Displayed.Decoration.append (firstRoundProtocol R M evaluate).roles
        (fun path => (remainingProtocol R M evaluate count path).roles),
      PFunctor.FreeM.Displayed.Decoration.append (firstRoundProtocol R M evaluate).oracles
        (fun path => (remainingProtocol R M evaluate count path).oracles)⟩ := by
  unfold protocol firstRoundProtocol remainingProtocol
  simp only [Protocol.oracleWith, Protocol.public, Protocol.done,
    PFunctor.FreeM.append, PFunctor.FreeM.Displayed.Decoration.append]
  congr 3

/-- The final claim has the full challenge vector and the claimed evaluation. -/
abbrev FinalStatement := Spec.StatementRound R n (Fin.last n)

variable {ι : Type} (ambient : OracleSpec ι)

/-- Query the latest message, leaving all earlier source slots available. -/
def latest (A : PFunctor) (x : R) :
    OracleComp
      (ambient + OracleSpec.ofPFunctor (Access.extend A (messageInterface R M evaluate))) R :=
  liftM ((ambient + OracleSpec.ofPFunctor (Access.extend A (messageInterface R M evaluate))).query
    (.inr (.inr x)))

/-- Sum the latest message over the declared domain. -/
def latestSum (A : PFunctor) : List R →
    OracleComp (ambient + OracleSpec.ofPFunctor (Access.extend A (messageInterface R M evaluate))) R
  | [] => pure 0
  | x :: xs => do
      let value ← latest R M evaluate ambient A x
      let rest ← latestSum A xs
      return value + rest

variable [DecidableEq R]

/-- The verifier uses only declared answers. Its original-oracle view is exported, never queried
to decide final acceptance. Aborting still runs the ordinary prover's response to the move. -/
def verifier (challenge : OracleComp ambient R) (domain : List R) :
    (count start : ℕ) → (finish : start + count = n) → (A : PFunctor) →
    VirtualOracle (OracleSpec.ofPFunctor A) (polynomialFamily R n deg) →
    Spec.StatementRound R n ⟨start, by omega⟩ →
    Verifier.Strategy ambient (protocol R M evaluate count).tree (protocol R M evaluate count).roles
      (protocol R M evaluate count).oracles A
      (TerminalClaim (protocol R M evaluate count) A (fun _ => FinalStatement R n)
        (fun _ => polynomialFamily R n deg))
  | 0, start, finish, A, originalOracle, stmt =>
      pure (some ⟨⟨stmt.target, stmt.challenges ∘ Fin.cast (by simp; omega)⟩,
        originalOracle⟩)
  | count + 1, start, finish, A, originalOracle, stmt => do
      let total ← latestSum R M evaluate ambient A domain
      return do
        if total = stmt.target then
          let r ← OracleComp.liftComp challenge
            (ambient + OracleSpec.ofPFunctor (Access.extend A (messageInterface R M evaluate)))
          let value ← latest R M evaluate ambient A r
          return ⟨some r, verifier challenge domain count (start + 1) (by omega)
            (Access.extend A (messageInterface R M evaluate))
            (originalOracle.sumWeaken (messageInterface R M evaluate).spec)
            ⟨value, Fin.snoc stmt.challenges r⟩⟩
        else return ⟨none, pure none⟩

/-- Execute and close the full native interaction, retaining its actual paired source handler. -/
def execute (challenge : OracleComp ambient R) (domain : List R)
    (count start : ℕ) (finish : start + count = n) (A : PFunctor)
    (originalOracle : VirtualOracle (OracleSpec.ofPFunctor A) (polynomialFamily R n deg))
    (stmt : Spec.StatementRound R n ⟨start, by omega⟩)
    (impl : QueryImpl (OracleSpec.ofPFunctor A) Id)
    (prover : Prover.Strategy ambient (protocol R M evaluate count).tree
      (protocol R M evaluate count).roles (fun _ => Unit)) :
    OracleComp ambient (Option (ClosedClaim (FinalStatement R n) (polynomialFamily R n deg))) :=
  (fun run => CoreRun.closed run) <$>
    executeStrategiesCore (protocol := protocol R M evaluate count)
    impl prover
    (verifier R n deg M evaluate ambient challenge domain count start finish A originalOracle stmt)

/-- Truth at the final leaf is evaluation of the retained original behavior at the full prefix. -/
def outputRelation (claim : ClosedClaim (FinalStatement R n) (polynomialFamily R n deg)) : Prop :=
  claim.oracles ⟨(), claim.stmt.challenges⟩ = claim.stmt.target

omit [DecidableEq R] [CommSemiring R] in
/-- Pure resource interpretation of the newest message's evaluation. -/
theorem simulate_latest (A : PFunctor) (impl : QueryImpl (OracleSpec.ofPFunctor A) Id)
    (q : M) (x : R) :
    simulateQ (Verifier.liftAccessImpl ambient (Access.extend A (messageInterface R M evaluate))
      (Access.extendImpl A (messageInterface R M evaluate) impl q))
      (latest R M evaluate ambient A x) =
      pure (evaluate q x) := by
  rfl

omit [DecidableEq R] in
/-- Pure resource interpretation of the entire newest-message sum. -/
theorem simulate_latestSum (A : PFunctor) (impl : QueryImpl (OracleSpec.ofPFunctor A) Id)
    (q : M) (domain : List R) :
    simulateQ (Verifier.liftAccessImpl ambient (Access.extend A (messageInterface R M evaluate))
      (Access.extendImpl A (messageInterface R M evaluate) impl q))
      (latestSum R M evaluate ambient A domain) =
      pure (domain.map (fun x => evaluate q x)).sum := by
  induction domain with
  | nil => rfl
  | cons x xs ih =>
      simp only [latestSum, simulateQ_bind, simulate_latest, pure_bind, ih, simulateQ_pure]
      rfl

/-- With no rounds left, the terminal verifier exports the original view without querying it. -/
theorem execute_zero (challenge : OracleComp ambient R) (domain : List R)
    (start : ℕ) (finish : start + 0 = n) (A : PFunctor)
    (originalOracle : VirtualOracle (OracleSpec.ofPFunctor A) (polynomialFamily R n deg))
    (stmt : Spec.StatementRound R n ⟨start, by omega⟩)
    (impl : QueryImpl (OracleSpec.ofPFunctor A) Id)
    (prover : Prover.Strategy ambient (protocol R M evaluate 0).tree
      (protocol R M evaluate 0).roles (fun _ => Unit)) :
    execute R n deg M evaluate ambient challenge domain 0 start finish A originalOracle stmt impl
      prover =
      pure (some ⟨⟨stmt.target, stmt.challenges ∘ Fin.cast (by simp; omega)⟩,
        originalOracle.eval impl⟩) := by
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Decompose actual native execution for every ordinary prover strategy. The response to a
successful challenge remains effectful; so does the prover's response to public abort. -/
theorem execute_succ (challenge : OracleComp ambient R) (domain : List R)
    (count start : ℕ) (finish : start + (count + 1) = n) (A : PFunctor)
    (originalOracle : VirtualOracle (OracleSpec.ofPFunctor A) (polynomialFamily R n deg))
    (stmt : Spec.StatementRound R n ⟨start, by omega⟩)
    (impl : QueryImpl (OracleSpec.ofPFunctor A) Id)
    (prover : Prover.Strategy ambient (protocol R M evaluate (count + 1)).tree
      (protocol R M evaluate (count + 1)).roles (fun _ => Unit)) :
    execute R n deg M evaluate ambient challenge domain (count + 1) start finish A originalOracle
      stmt impl prover =
      (do
        let chosen ← prover
        if (domain.map (fun x => evaluate chosen.1 x)).sum = stmt.target then
          let r ← challenge
          let next ← chosen.2 (some r)
          execute R n deg M evaluate ambient challenge domain count (start + 1) (by omega)
            (Access.extend A (messageInterface R M evaluate))
            (originalOracle.sumWeaken (messageInterface R M evaluate).spec)
            ⟨evaluate chosen.1 r, Fin.snoc stmt.challenges r⟩
            (Access.extendImpl A (messageInterface R M evaluate) impl chosen.1) next
        else
          let _ ← chosen.2 none
          return none) := by
  simp only [execute, executeStrategiesCore, executeStrategies,
    map_eq_bind_pure_comp, bind_assoc, pure_bind]
  simp only [protocol, verifier, Protocol.oracleWith_tree, Protocol.oracleWith_roles,
    Protocol.oracleWith_oracles, Protocol.public_tree, Protocol.public_roles,
    Protocol.public_oracles, Protocol.done_tree, Protocol.done_roles,
    Verifier.toCounterpart, Verifier.toCounterpartWith,
    TypeTree.toTypeTree_oracle, TypeTree.toTypeTree_public,
    TypeTree.RoleDecoration.toTypeTreeRoles_oracle,
    TypeTree.RoleDecoration.toTypeTreeRoles_public, TypeTree.RoleDecoration.toTypeTreeRoles_done]
  dsimp only [TwoParty.run,
    InteractionOver.runTypeTree,
    InteractionOver.TwoParty.pairedTypeTree,
    InteractionOver.TwoParty.paired,
    TwoParty.participantProfile,
    TwoParty.collectParticipantOutputs]
  simp only [simulateQ_bind, simulateQ_pure, simulate_latestSum, pure_bind, bind_assoc]
  congr 1
  funext chosen
  split
  · simp only [simulateQ_bind, simulateQ_pure]
    rw [QueryImpl.simulateQ_liftComp_left_eq_of_apply _ (QueryImpl.id' ambient)
      (fun _ => rfl), simulateQ_id']
    simp only [simulate_latest, pure_bind, bind_assoc]
    rfl
  · rfl

/-- Permuting domain queries preserves closed execution because message handlers are pure.
The actual prover's private continuations and all ambient effects remain in the same order. -/
theorem execute_eq_of_domain_perm (challenge : OracleComp ambient R)
    (domain₁ domain₂ : List R) (hdomain : domain₁.Perm domain₂)
    (count start : ℕ) (finish : start + count = n) (A : PFunctor)
    (original : VirtualOracle (ofPFunctor A) (polynomialFamily R n deg))
    (stmt : Spec.StatementRound R n ⟨start, by omega⟩)
    (impl : QueryImpl (ofPFunctor A) Id)
    (prover : Prover.Strategy ambient (protocol R M evaluate count).tree
      (protocol R M evaluate count).roles (fun _ => Unit)) :
    execute R n deg M evaluate ambient challenge domain₁ count start finish A original stmt impl
      prover =
      execute R n deg M evaluate ambient challenge domain₂ count start finish A original stmt impl
        prover := by
  induction count generalizing start A with
  | zero => rfl
  | succ count ih =>
    rw [execute_succ, execute_succ]
    apply bind_congr
    rintro ⟨q, respond⟩
    rw [(hdomain.map (fun x => evaluate q x)).sum_eq]
    split
    · apply bind_congr
      intro r
      apply bind_congr
      intro next
      apply ih
    · rfl

/-- Equal original-oracle behavior gives the same native execution and optional closed claim.

Both sides use the same statement, challenge program, and arbitrary whole native prover.
Their source interfaces and total deterministic handlers may differ. The equality preserves
ambient effects, including responses to public abort; it does not compare raw source query logs.
This abbrev observes the optional closed claim, as does `execute`. -/
theorem execute_eq_of_originalOracle_eq (challenge : OracleComp ambient R) (domain : List R)
    (count start : ℕ) (finish : start + count = n) (A B : PFunctor)
    (viewA : VirtualOracle (ofPFunctor A) (polynomialFamily R n deg))
    (viewB : VirtualOracle (ofPFunctor B) (polynomialFamily R n deg))
    (stmt : Spec.StatementRound R n ⟨start, by omega⟩)
    (implA : QueryImpl (ofPFunctor A) Id) (implB : QueryImpl (ofPFunctor B) Id)
    (prover : Prover.Strategy ambient (protocol R M evaluate count).tree
      (protocol R M evaluate count).roles (fun _ => Unit))
    (hview : viewA.eval implA = viewB.eval implB) :
    execute R n deg M evaluate ambient challenge domain count start finish A viewA stmt implA
      prover =
      execute R n deg M evaluate ambient challenge domain count start finish B viewB stmt implB
        prover := by
  induction count generalizing start A B with
  | zero => simp only [execute_zero, hview]
  | succ count ih =>
    rw [execute_succ, execute_succ]
    apply bind_congr
    rintro ⟨q, respond⟩
    change M at q
    by_cases check : (domain.map (fun x => evaluate q x)).sum = stmt.target
    · simp only [check, ↓reduceIte]
      apply bind_congr
      intro r
      apply bind_congr
      intro next
      apply ih
      rw [VirtualOracle.eval_sumWeaken_extendImpl, VirtualOracle.eval_sumWeaken_extendImpl]
      exact hview
    · simp only [check, ↓reduceIte]


variable (N : Type) (evaluateN : N → R → R) (interpret : M → N)

/-- Interpret every sent message of an ordinary native prover. All ambient computations and
all public-branch responses are retained, including the response to public abort. -/
def transportProver : (count : ℕ) →
    Prover.Strategy ambient (protocol R M evaluate count).tree
      (protocol R M evaluate count).roles (fun _ => Unit) →
    Prover.Strategy ambient (protocol R N evaluateN count).tree
      (protocol R N evaluateN count).roles (fun _ => Unit)
  | 0, prover => prover
  | count + 1, prover => do
      let chosen ← prover
      return ⟨interpret chosen.1, fun
        | none => do
            let next ← chosen.2 none
            return next
        | some r => do
            let next ← chosen.2 (some r)
            return transportProver count next⟩

set_option backward.isDefEq.respectTransparency false in
/-- Actual whole native execution commutes with message interpretation. The arbitrary prover's
private continuations and abort effects survive, and the closed original behavior is identical. -/
theorem execute_transport (challenge : OracleComp ambient R) (domain : List R)
    (count start : ℕ) (finish : start + count = n) (A B : PFunctor)
    (viewA : VirtualOracle (ofPFunctor A) (polynomialFamily R n deg))
    (viewB : VirtualOracle (ofPFunctor B) (polynomialFamily R n deg))
    (stmt : Spec.StatementRound R n ⟨start, by omega⟩)
    (implA : QueryImpl (ofPFunctor A) Id) (implB : QueryImpl (ofPFunctor B) Id)
    (prover : Prover.Strategy ambient (protocol R M evaluate count).tree
      (protocol R M evaluate count).roles (fun _ => Unit))
    (hevaluate : ∀ q x, evaluateN (interpret q) x = evaluate q x)
    (hview : viewA.eval implA = viewB.eval implB) :
    execute R n deg M evaluate ambient challenge domain count start finish A viewA stmt implA
      prover =
    execute R n deg N evaluateN ambient challenge domain count start finish B viewB stmt implB
      (transportProver R M evaluate ambient N evaluateN interpret count prover) := by
  induction count generalizing start A B with
  | zero => simp only [execute_zero, hview]
  | succ count ih =>
      rw [execute_succ, execute_succ]
      simp only [transportProver, bind_assoc, pure_bind]
      apply bind_congr
      rintro ⟨q, respond⟩
      simp only [hevaluate]
      by_cases check : (domain.map (fun x => evaluate q x)).sum = stmt.target
      · simp only [check, ↓reduceIte]
        apply bind_congr
        intro r
        apply bind_congr
        intro next
        apply ih
        rw [VirtualOracle.eval_sumWeaken_extendImpl, VirtualOracle.eval_sumWeaken_extendImpl]
        exact hview
      · simp only [check, ↓reduceIte]
        rfl

/-- Query the virtual original oracle in the verifier's actual terminal action. -/
def checkFinalClaim (A : PFunctor)
    (claim : OpenClaim (ofPFunctor A) (FinalStatement R n)
      (MultivariateRound.polynomialFamily R n deg)) :
    OracleComp (ambient + ofPFunctor A) Bool := do
  let answer : R ← liftM (claim.oracles.query ⟨(), claim.stmt.challenges⟩)
  return decide (answer = claim.stmt.target)

/-- Interpreting an arbitrary source-only program adds no ambient effects. -/
private theorem simulate_sourceProgram (A : PFunctor) (impl : QueryImpl (ofPFunctor A) Id)
    {α : Type} (program : OracleComp (ofPFunctor A) α) :
    simulateQ (Verifier.liftAccessImpl ambient A impl)
      (liftM program : OracleComp (ambient + ofPFunctor A) α) =
      pure (simulateQ impl program) := by
  change simulateQ (QueryImpl.add (QueryImpl.id' ambient)
    (impl.liftTarget (OracleComp ambient))) _ = _
  rw [QueryImpl.add_eq_hAdd, QueryImpl.simulateQ_add_liftM_right, simulateQ_liftTarget]
  rfl

/-- The terminal query is interpreted with the same current source handler. -/
theorem simulate_checkFinalClaim (A : PFunctor)
    (impl : QueryImpl (ofPFunctor A) Id)
    (claim : OpenClaim (ofPFunctor A) (FinalStatement R n)
      (MultivariateRound.polynomialFamily R n deg)) :
    simulateQ (Verifier.liftAccessImpl ambient A impl) (checkFinalClaim R n deg ambient A claim) =
      pure (decide ((show R from (claim.closeWith impl).oracles ⟨(), claim.stmt.challenges⟩) =
        claim.stmt.target)) := by
  have query_eq : simulateQ (Verifier.liftAccessImpl ambient A impl)
      (liftM (claim.oracles.query ⟨(), claim.stmt.challenges⟩) :
        OracleComp (ambient + ofPFunctor A) R) =
      pure (show R from (claim.closeWith impl).oracles ⟨(), claim.stmt.challenges⟩) := by
    exact simulate_sourceProgram ambient A impl (claim.oracles.query ⟨(), claim.stmt.challenges⟩)
  simp only [checkFinalClaim, simulateQ_bind, query_eq, simulateQ_pure]
  rfl

/-- Rejection stays rejection; a successful claim is queried once by the terminal checker. -/
def checkFinalResult (A : PFunctor)
    (action : OracleComp (ambient + ofPFunctor A)
      (Option (OpenClaim (ofPFunctor A) (FinalStatement R n)
        (MultivariateRound.polynomialFamily R n deg)))) :
    OracleComp (ambient + ofPFunctor A) Bool := do
  let result ← action
  match result with
  | none => return false
  | some claim => checkFinalClaim R n deg ambient A claim

/-- Boolean form of the final output relation on an optional closed result.
This is the terminal criterion also used by stateless replay clients. -/
def accepts (result : Option (ClosedClaim (FinalStatement R n)
    (MultivariateRound.polynomialFamily R n deg))) : Bool :=
  match result with
  | none => false
  | some claim =>
      decide ((show R from claim.oracles ⟨(), claim.stmt.challenges⟩) = claim.stmt.target)

/-- Bool acceptance is precisely the closed-relation event used by existing native soundness. -/
theorem accepts_eq_true_iff (result : Option (ClosedClaim (FinalStatement R n)
    (MultivariateRound.polynomialFamily R n deg))) :
    accepts R n deg result = true ↔
      result.map (outputRelation R n deg) = some True := by
  cases result <;>
    simp [accepts, outputRelation]
  rfl

/-- The terminal checker realizes the final closed relation using the supplied source behavior. -/
theorem simulate_checkFinalResult (A : PFunctor) (impl : QueryImpl (ofPFunctor A) Id)
    (action : OracleComp (ambient + ofPFunctor A)
      (Option (OpenClaim (ofPFunctor A) (FinalStatement R n)
        (MultivariateRound.polynomialFamily R n deg)))) :
    simulateQ (Verifier.liftAccessImpl ambient A impl)
      (checkFinalResult R n deg ambient A action) =
      (fun result => accepts R n deg (result.map (fun claim => claim.closeWith impl))) <$>
        simulateQ (Verifier.liftAccessImpl ambient A impl) action := by
  simp only [checkFinalResult, simulateQ_bind, map_eq_pure_bind]
  apply bind_congr
  intro result
  cases result with
  | none => rfl
  | some claim => exact simulate_checkFinalClaim R n deg ambient A impl claim

/-- Bind the native Sumcheck terminal action before deciding acceptance. -/
def verifierWithFinalCheck (challenge : OracleComp ambient R) (domain : List R)
    (count start : ℕ) (finish : start + count = n) (A : PFunctor)
    (original : VirtualOracle (ofPFunctor A) (MultivariateRound.polynomialFamily R n deg))
    (stmt : Sumcheck.Spec.StatementRound R n ⟨start, by omega⟩) :
    Verifier.Strategy ambient (protocol R M evaluate count).tree
      (protocol R M evaluate count).roles (protocol R M evaluate count).oracles A
      (fun _ => Bool) :=
  Verifier.Fragment.mapOutput ambient (fun path action =>
    checkFinalResult R n deg ambient
      (TypeTree.accessAfter (protocol R M evaluate count).tree
        (protocol R M evaluate count).oracles A path) action)
    (verifier R n deg M evaluate ambient challenge domain count start finish A original stmt)

/-- Execute the complete native verifier, including its actual final source query action.
The native prover may have arbitrary private output and effectful continuations. -/
def executeWithFinalCheck (challenge : OracleComp ambient R) (domain : List R)
    (count start : ℕ) (finish : start + count = n) (A : PFunctor)
    (original : VirtualOracle (ofPFunctor A) (MultivariateRound.polynomialFamily R n deg))
    (stmt : Sumcheck.Spec.StatementRound R n ⟨start, by omega⟩)
    (impl : QueryImpl (ofPFunctor A) Id)
    {OutP : (protocol R M evaluate count).tree.ExecutionPath → Type}
    (prover : Prover.Strategy ambient (protocol R M evaluate count).tree
      (protocol R M evaluate count).roles OutP) : OracleComp ambient Bool :=
  (fun result => result.2.2) <$>
    executeStrategies ambient (protocol R M evaluate count).tree
      (protocol R M evaluate count).roles (protocol R M evaluate count).oracles A impl prover
      (verifierWithFinalCheck R n deg M evaluate ambient challenge domain count start finish A
        original stmt)

/-- The existing runner supplies the terminal action with exactly this run's accumulated
source handler, for every native prover continuation and private output family. -/
private theorem execute_map_terminal (tree : _root_.Interaction.Oracle.TypeTree)
    (roles : tree.RoleDecoration) (oracles : tree.OracleDecoration) (A : PFunctor)
    (impl : QueryImpl (ofPFunctor A) Id)
    (Leaf Out : tree.BranchPath → Type)
    (OutP : tree.ExecutionPath → Type)
    (prover : Prover.Strategy ambient tree roles OutP)
    (fragment : Verifier.Fragment ambient tree roles oracles A Leaf)
    (finish : (path : tree.BranchPath) → Leaf path →
      OracleComp (ambient + ofPFunctor (TypeTree.accessAfter tree oracles A path)) (Out path)) :
    executeStrategies ambient tree roles oracles A impl prover
      (Verifier.Fragment.mapOutput ambient finish fragment) = (do
      let result ← _root_.Interaction.TwoParty.run tree.toTypeTree
        (TypeTree.RoleDecoration.toTypeTreeRoles tree roles) prover
        (Verifier.toCounterpartValue ambient tree roles oracles A impl Leaf fragment)
      let path := TypeTree.ExecutionPath.ofTypeTreePath result.1
      let out ← simulateQ
        (Verifier.liftAccessImpl ambient (TypeTree.accessAfter tree oracles A path.toBranchPath)
          (path.closingImpl oracles A impl))
        (finish path.toBranchPath result.2.2)
      return ⟨path, result.2.1, out⟩) := by
  unfold executeStrategies Verifier.toCounterpart
  rw [Verifier.toCounterpartWith_mapOutput,
    Verifier.toCounterpartWith_finish_eq_mapOutput, run_counterpart_mapOutput]
  simp only [bind_map_left]

/-- The completed native verifier has exactly the original run's path and private output,
with acceptance given by the original claim closed against that run's retained resources.
This is an equality of open programs and quantifies over arbitrary native prover continuations. -/
theorem executeStrategies_verifierWithFinalCheck (challenge : OracleComp ambient R)
    (domain : List R)
    (count start : ℕ) (finish : start + count = n) (A : PFunctor)
    (original : VirtualOracle (ofPFunctor A) (MultivariateRound.polynomialFamily R n deg))
    (stmt : Sumcheck.Spec.StatementRound R n ⟨start, by omega⟩)
    (impl : QueryImpl (ofPFunctor A) Id)
    (OutP : (protocol R M evaluate count).tree.ExecutionPath → Type)
    (prover : Prover.Strategy ambient (protocol R M evaluate count).tree
      (protocol R M evaluate count).roles OutP) :
    executeStrategies ambient (protocol R M evaluate count).tree
      (protocol R M evaluate count).roles (protocol R M evaluate count).oracles A impl
      prover (verifierWithFinalCheck R n deg M evaluate ambient challenge domain count start finish
        A original stmt) =
    (fun result => ⟨result.1, result.2.1, accepts R n deg
      (result.2.2.map (fun claim => claim.closeWith
        (result.1.closingImpl (protocol R M evaluate count).oracles A impl)))⟩) <$>
      executeStrategies ambient (protocol R M evaluate count).tree
        (protocol R M evaluate count).roles (protocol R M evaluate count).oracles A impl
        prover (verifier R n deg M evaluate ambient challenge domain count start finish A original
          stmt) := by
  unfold verifierWithFinalCheck
  rw [execute_map_terminal]
  simp only [simulate_checkFinalResult, bind_map_left]
  unfold executeStrategies
  rw [Verifier.toCounterpart, Verifier.toCounterpartWith_finish_eq_mapOutput,
    run_counterpart_mapOutput]
  simp only [bind_map_left, map_bind, map_pure]

/-- The executable Bool event is exactly the existing closed native Sumcheck event.
Consequently adding terminal authentication contributes zero additional soundness error. -/
theorem executeWithFinalCheck_eq_execute (challenge : OracleComp ambient R) (domain : List R)
    (count start : ℕ) (finish : start + count = n) (A : PFunctor)
    (original : VirtualOracle (ofPFunctor A) (MultivariateRound.polynomialFamily R n deg))
    (stmt : Sumcheck.Spec.StatementRound R n ⟨start, by omega⟩)
    (impl : QueryImpl (ofPFunctor A) Id)
    (prover : Prover.Strategy ambient (protocol R M evaluate count).tree
      (protocol R M evaluate count).roles (fun _ => Unit)) :
    executeWithFinalCheck R n deg M evaluate ambient challenge domain count start finish A
      original stmt impl prover =
      accepts R n deg <$> execute R n deg M evaluate ambient challenge domain count start finish
        A original stmt impl prover := by
  unfold executeWithFinalCheck
  rw [executeStrategies_verifierWithFinalCheck]
  simp only [execute, executeStrategiesCore, CoreRun.closed,
    map_eq_pure_bind, bind_assoc, pure_bind]

/-- Discarding only the prover's final private return value preserves complete acceptance.
The paired-run output map retains the actual path and every ambient effect, so the existing
Unit-output native soundness theorem applies to arbitrary private-output prover strategies. -/
theorem executeWithFinalCheck_eq_execute_eraseOutput
    (challenge : OracleComp ambient R) (domain : List R)
    (count start : ℕ) (finish : start + count = n) (A : PFunctor)
    (original : VirtualOracle (ofPFunctor A) (MultivariateRound.polynomialFamily R n deg))
    (stmt : Sumcheck.Spec.StatementRound R n ⟨start, by omega⟩)
    (impl : QueryImpl (ofPFunctor A) Id)
    {OutP : (protocol R M evaluate count).tree.ExecutionPath → Type}
    (prover : Prover.Strategy ambient (protocol R M evaluate count).tree
      (protocol R M evaluate count).roles OutP) :
    executeWithFinalCheck R n deg M evaluate ambient challenge domain count start finish A
      original stmt impl prover =
      accepts R n deg <$> execute R n deg M evaluate ambient challenge domain count start finish
        A original stmt impl
        (StrategyOver.TwoParty.Focal.mapOutput (fun _ _ => (() : Unit)) prover) := by
  let counterpart := Verifier.toCounterpart ambient (protocol R M evaluate count).tree
    (protocol R M evaluate count).roles (protocol R M evaluate count).oracles A impl
    (fun _ => Bool)
    (verifierWithFinalCheck R n deg M evaluate ambient challenge domain count start finish A
      original stmt)
  have mapped := TwoParty.run_mapOutput_mapOutput (fun _ _ => (() : Unit))
    (fun _ out => out) prover counterpart
  simp only [StrategyOver.TwoParty.Counterpart.mapOutput_id] at mapped
  rw [← executeWithFinalCheck_eq_execute]
  simp only [executeWithFinalCheck, executeStrategies, map_bind, map_pure]
  rw [mapped]
  simp only [bind_map_left]
  rfl

/-- Complete executable acceptance is independent of the order of a domain enumeration.
Only source-query order changes; the closed Bool program preserves all ambient effects. -/
theorem executeWithFinalCheck_eq_of_domain_perm (challenge : OracleComp ambient R)
    (domain₁ domain₂ : List R) (hdomain : domain₁.Perm domain₂)
    (count start : ℕ) (finish : start + count = n) (A : PFunctor)
    (original : VirtualOracle (ofPFunctor A) (polynomialFamily R n deg))
    (stmt : Spec.StatementRound R n ⟨start, by omega⟩)
    (impl : QueryImpl (ofPFunctor A) Id)
    {OutP : (protocol R M evaluate count).tree.ExecutionPath → Type}
    (prover : Prover.Strategy ambient (protocol R M evaluate count).tree
      (protocol R M evaluate count).roles OutP) :
    executeWithFinalCheck R n deg M evaluate ambient challenge domain₁ count start finish A
      original stmt impl prover =
      executeWithFinalCheck R n deg M evaluate ambient challenge domain₂ count start finish A
        original stmt impl prover := by
  rw [executeWithFinalCheck_eq_execute_eraseOutput,
    executeWithFinalCheck_eq_execute_eraseOutput,
    execute_eq_of_domain_perm R n deg M evaluate ambient challenge domain₁ domain₂ hdomain]


end Sumcheck.Interaction.Native.Core

namespace Sumcheck.Interaction.Native

open OracleSpec SingleRound MultivariateRound

variable (R : Type) [CommSemiring R] (n deg : ℕ)

/-- The mathematical message specialization of the shared native protocol. -/
def protocol := Core.protocol R (Message R deg) (fun q x => q.val.eval x)
/-- The first mathematical round of the shared native protocol. -/
def firstRoundProtocol := Core.firstRoundProtocol R (Message R deg) (fun q x => q.val.eval x)
/-- Remaining rounds after the public choice. -/
def remainingProtocol := Core.remainingProtocol R (Message R deg) (fun q x => q.val.eval x)
/-- Final native Sumcheck statement. -/
abbrev FinalStatement := Core.FinalStatement R n

variable {ι : Type} (ambient : OracleSpec ι)

/-- Latest mathematical message query in the shared verifier. -/
def latest := Core.latest R (Message R deg) (fun q x => q.val.eval x) ambient
/-- Domain sum in the shared verifier. -/
def latestSum := Core.latestSum R (Message R deg) (fun q x => q.val.eval x) ambient
/-- The mathematical specialization of the shared native verifier. -/
def verifier [DecidableEq R] := Core.verifier R n deg (Message R deg)
  (fun q x => q.val.eval x) ambient
/-- Close execution of the mathematical specialization. -/
def execute [DecidableEq R] := Core.execute R n deg (Message R deg)
  (fun q x => q.val.eval x) ambient
/-- Truth of the exported original-oracle evaluation claim. -/
def outputRelation := Core.outputRelation R n deg


/-- Mathematical specialization of the shared native execution law. -/
theorem protocol_succ_eq_append (count : ℕ) : protocol R deg (count + 1) =
    ⟨PFunctor.FreeM.append (firstRoundProtocol R deg).tree
        (fun path => (remainingProtocol R deg count path).tree),
      PFunctor.FreeM.Displayed.Decoration.append (firstRoundProtocol R deg).roles
        (fun path => (remainingProtocol R deg count path).roles),
      PFunctor.FreeM.Displayed.Decoration.append (firstRoundProtocol R deg).oracles
        (fun path => (remainingProtocol R deg count path).oracles)⟩ := by
  exact Core.protocol_succ_eq_append R (Message R deg) (fun q x => q.val.eval x)
    count

/-- Mathematical specialization of the shared native execution law. -/
theorem simulate_latest (A : PFunctor) (impl : QueryImpl (OracleSpec.ofPFunctor A) Id)
    (q : Message R deg) (x : R) :
    simulateQ (Verifier.liftAccessImpl ambient (Access.extend A (polynomialInterface R deg))
      (Access.extendImpl A (polynomialInterface R deg) impl q)) (latest R deg ambient A x) =
      pure (q.val.eval x) := by
  exact Core.simulate_latest R (Message R deg) (fun q x => q.val.eval x) ambient
    A impl q x

/-- Mathematical specialization of the shared native execution law. -/
theorem simulate_latestSum (A : PFunctor) (impl : QueryImpl (OracleSpec.ofPFunctor A) Id)
    (q : Message R deg) (domain : List R) :
    simulateQ (Verifier.liftAccessImpl ambient (Access.extend A (polynomialInterface R deg))
      (Access.extendImpl A (polynomialInterface R deg) impl q))
      (latestSum R deg ambient A domain) = pure (domain.map (fun x => q.val.eval x)).sum := by
  exact Core.simulate_latestSum R (Message R deg) (fun q x => q.val.eval x) ambient
    A impl q domain

/-- Mathematical specialization of the shared native execution law. -/
theorem execute_zero [DecidableEq R] (challenge : OracleComp ambient R) (domain : List R)
    (start : ℕ) (finish : start + 0 = n) (A : PFunctor)
    (originalOracle : VirtualOracle (OracleSpec.ofPFunctor A) (polynomialFamily R n deg))
    (stmt : Spec.StatementRound R n ⟨start, by omega⟩)
    (impl : QueryImpl (OracleSpec.ofPFunctor A) Id)
    (prover : Prover.Strategy ambient (protocol R deg 0).tree
      (protocol R deg 0).roles (fun _ => Unit)) :
    execute R n deg ambient challenge domain 0 start finish A originalOracle stmt impl prover =
      pure (some ⟨⟨stmt.target, stmt.challenges ∘ Fin.cast (by simp; omega)⟩,
        originalOracle.eval impl⟩) := by
  exact Core.execute_zero R n deg (Message R deg) (fun q x => q.val.eval x) ambient
    challenge domain start finish A originalOracle stmt impl prover

/-- Mathematical specialization of the shared native execution law. -/
theorem execute_succ [DecidableEq R] (challenge : OracleComp ambient R) (domain : List R)
    (count start : ℕ) (finish : start + (count + 1) = n) (A : PFunctor)
    (originalOracle : VirtualOracle (OracleSpec.ofPFunctor A) (polynomialFamily R n deg))
    (stmt : Spec.StatementRound R n ⟨start, by omega⟩)
    (impl : QueryImpl (OracleSpec.ofPFunctor A) Id)
    (prover : Prover.Strategy ambient (protocol R deg (count + 1)).tree
      (protocol R deg (count + 1)).roles (fun _ => Unit)) :
    execute R n deg ambient challenge domain (count + 1) start finish A originalOracle
      stmt impl prover =
      (do
        let chosen ← prover
        if (domain.map (fun x => chosen.1.val.eval x)).sum = stmt.target then
          let r ← challenge
          let next ← chosen.2 (some r)
          execute R n deg ambient challenge domain count (start + 1) (by omega)
            (Access.extend A (polynomialInterface R deg))
            (originalOracle.sumWeaken (polynomialInterface R deg).spec)
            ⟨chosen.1.val.eval r, Fin.snoc stmt.challenges r⟩
            (Access.extendImpl A (polynomialInterface R deg) impl chosen.1) next
        else
          let _ ← chosen.2 none
          return none) := by
  exact Core.execute_succ R n deg (Message R deg) (fun q x => q.val.eval x) ambient
    challenge domain count start finish A originalOracle stmt impl prover

/-- Mathematical specialization of the shared native execution law. -/
theorem execute_eq_of_originalOracle_eq [DecidableEq R]
    (challenge : OracleComp ambient R) (domain : List R)
    (count start : ℕ) (finish : start + count = n) (A B : PFunctor)
    (viewA : VirtualOracle (ofPFunctor A) (polynomialFamily R n deg))
    (viewB : VirtualOracle (ofPFunctor B) (polynomialFamily R n deg))
    (stmt : Spec.StatementRound R n ⟨start, by omega⟩)
    (implA : QueryImpl (ofPFunctor A) Id) (implB : QueryImpl (ofPFunctor B) Id)
    (prover : Prover.Strategy ambient (protocol R deg count).tree
      (protocol R deg count).roles (fun _ => Unit))
    (hview : viewA.eval implA = viewB.eval implB) :
    execute R n deg ambient challenge domain count start finish A viewA stmt implA prover =
      execute R n deg ambient challenge domain count start finish B viewB stmt implB prover := by
  exact Core.execute_eq_of_originalOracle_eq R n deg (Message R deg)
    (fun q x => q.val.eval x) ambient
    challenge domain count start finish A B viewA viewB stmt implA implB prover hview

end Sumcheck.Interaction.Native

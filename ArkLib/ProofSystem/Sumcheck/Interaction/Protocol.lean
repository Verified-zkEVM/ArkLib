/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.ProofSystem.Sumcheck.Interaction.MultivariateRound

/-!
# Native Sumcheck with a public abort branch

The full protocol alternates a degree-bounded oracle message with the verifier's optional field
challenge. `none` publicly aborts the interaction; `some r` continues the native tree. Ordinary
prover continuations retain their own memory and effects. The restricted verifier queries only
the latest sent polynomial, retaining all earlier access slots and exporting the original oracle
through a virtual view. At the final leaf it returns an evaluation claim without querying the
original polynomial. Truth of that claim is a separate relation.
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

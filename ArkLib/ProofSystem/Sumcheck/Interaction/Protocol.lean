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

namespace Sumcheck.Interaction.Native

open OracleComp OracleSpec
open SingleRound MultivariateRound

noncomputable section

variable (R : Type) [CommSemiring R] (n deg : ℕ)

/-- Each failed sum check takes a terminal public abort branch. -/
def protocol : ℕ → Protocol
  | 0 => .done
  | count + 1 => .oracleWith (Message R deg) (polynomialInterface R deg)
      (.public .receiver (Option R) fun choice =>
        match choice with
        | none => .done
        | some _ => protocol count)

/-- The final claim has the full challenge vector and the claimed evaluation. -/
abbrev FinalStatement := Spec.StatementRound R n (Fin.last n)

variable {ι : Type} (ambient : OracleSpec ι)

/-- Query the latest message, leaving all earlier source slots available. -/
def latest (A : PFunctor) (x : R) :
    OracleComp (ambient + OracleSpec.ofPFunctor (Access.extend A (polynomialInterface R deg))) R :=
  liftM ((ambient + OracleSpec.ofPFunctor (Access.extend A (polynomialInterface R deg))).query
    (.inr (.inr x)))

/-- Sum the latest message over the declared domain. -/
def latestSum (A : PFunctor) : List R →
    OracleComp (ambient + OracleSpec.ofPFunctor (Access.extend A (polynomialInterface R deg))) R
  | [] => pure 0
  | x :: xs => do
      let value ← latest R deg ambient A x
      let rest ← latestSum A xs
      return value + rest

variable [DecidableEq R]

/-- The verifier uses only declared answers. Its original-oracle view is exported, never queried
to decide final acceptance. Aborting still runs the ordinary prover's response to the move. -/
def verifier (challenge : OracleComp ambient R) (domain : List R) :
    (count start : ℕ) → (finish : start + count = n) → (A : PFunctor) →
    VirtualOracle (OracleSpec.ofPFunctor A) (polynomialFamily R n deg) →
    Spec.StatementRound R n ⟨start, by omega⟩ →
    Verifier.Strategy ambient (protocol R deg count).tree (protocol R deg count).roles
      (protocol R deg count).oracles A
      (TerminalClaim (protocol R deg count) A (fun _ => FinalStatement R n)
        (fun _ => polynomialFamily R n deg))
  | 0, start, finish, A, originalOracle, stmt =>
      pure (some ⟨⟨stmt.target, stmt.challenges ∘ Fin.cast (by simp; omega)⟩, originalOracle⟩)
  | count + 1, start, finish, A, originalOracle, stmt => do
      let total ← latestSum R deg ambient A domain
      return do
        if total = stmt.target then
          let r ← OracleComp.liftComp challenge
            (ambient + OracleSpec.ofPFunctor (Access.extend A (polynomialInterface R deg)))
          let value ← latest R deg ambient A r
          return ⟨some r, verifier challenge domain count (start + 1) (by omega)
            (Access.extend A (polynomialInterface R deg))
            (originalOracle.sumWeaken (polynomialInterface R deg).spec)
            ⟨value, Fin.snoc stmt.challenges r⟩⟩
        else return ⟨none, pure none⟩

/-- Execute and close the full native interaction, retaining its actual paired source handler. -/
def execute (challenge : OracleComp ambient R) (domain : List R)
    (count start : ℕ) (finish : start + count = n) (A : PFunctor)
    (originalOracle : VirtualOracle (OracleSpec.ofPFunctor A) (polynomialFamily R n deg))
    (stmt : Spec.StatementRound R n ⟨start, by omega⟩)
    (impl : QueryImpl (OracleSpec.ofPFunctor A) Id)
    (prover : Prover.Strategy ambient (protocol R deg count).tree
      (protocol R deg count).roles (fun _ => Unit)) :
    OracleComp ambient (Option (ClosedClaim (FinalStatement R n) (polynomialFamily R n deg))) :=
  CoreRun.closed <$> executeStrategiesCore (protocol := protocol R deg count) impl prover
    (verifier R n deg ambient challenge domain count start finish A originalOracle stmt)

/-- Truth at the final leaf is evaluation of the retained original behavior at the full prefix. -/
def outputRelation (claim : ClosedClaim (FinalStatement R n) (polynomialFamily R n deg)) : Prop :=
  claim.oracles ⟨(), claim.stmt.challenges⟩ = claim.stmt.target

omit [DecidableEq R] in
/-- Pure resource interpretation of the newest message's evaluation. -/
theorem simulate_latest (A : PFunctor) (impl : QueryImpl (OracleSpec.ofPFunctor A) Id)
    (q : Message R deg) (x : R) :
    simulateQ (Verifier.liftAccessImpl ambient (Access.extend A (polynomialInterface R deg))
      (Access.extendImpl A (polynomialInterface R deg) impl q)) (latest R deg ambient A x) =
      pure (q.val.eval x) := by
  rfl

omit [DecidableEq R] in
/-- Pure resource interpretation of the entire newest-message sum. -/
theorem simulate_latestSum (A : PFunctor) (impl : QueryImpl (OracleSpec.ofPFunctor A) Id)
    (q : Message R deg) (domain : List R) :
    simulateQ (Verifier.liftAccessImpl ambient (Access.extend A (polynomialInterface R deg))
      (Access.extendImpl A (polynomialInterface R deg) impl q))
      (latestSum R deg ambient A domain) = pure (domain.map (fun x => q.val.eval x)).sum := by
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
    (prover : Prover.Strategy ambient (protocol R deg 0).tree
      (protocol R deg 0).roles (fun _ => Unit)) :
    execute R n deg ambient challenge domain 0 start finish A originalOracle stmt impl prover =
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
  simp only [execute, executeStrategiesCore, executeStrategies,
    map_eq_bind_pure_comp, bind_assoc, pure_bind]
  simp only [protocol, verifier, Protocol.oracleWith_tree, Protocol.oracleWith_roles,
    Protocol.oracleWith_oracles, Protocol.public_tree, Protocol.public_roles,
    Protocol.public_oracles, Protocol.done_tree, Protocol.done_roles,
    Verifier.toCounterpart, TypeTree.toTypeTree_oracle, TypeTree.toTypeTree_public,
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

end
end Sumcheck.Interaction.Native

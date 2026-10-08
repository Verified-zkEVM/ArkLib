/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Interaction.Oracle.Prefix
public import ArkLib.Interaction.Oracle.Execution
public import VCVio.CryptoFoundations.RoundByRound
public import VCVio.EvalDist.ProbabilityBounds

/-!
# Ordinary round-by-round soundness on native prefixes

An ordinary state is false initially on a false input, cannot become true at a prover move,
and is true at every successful terminal path. Local soundness bounds false-to-true transitions
at every authored verifier prefix, including prefixes having zero execution probability.

The challenge model uses VCVio's game family. Its challenge types are small even though the
native prefix carrier stores a dependent residual tree. `FreshVerifier` connects that model to
actual native verifier actions after closing declared access and interpreting ambient effects.
It preserves receive effects and supported private continuations. The ambient interpreter may
lose probability mass, including when the native prover fails to return.
-/

@[expose] public section

open Interaction.Oracle Interaction.TwoParty OracleComp OracleSpec
open Interaction.Oracle.TypeTree
open scoped ENNReal

namespace Interaction.Oracle.Security

universe v

/-- At every authored prefix, a prover move cannot turn a false state true. -/
def ProverPreserves : (tree : TypeTree) → tree.RoleDecoration →
    (ExecutionPrefix tree → Prop) → Prop
  | .done, _, _ => True
  | .public _ rest, roles, state =>
      (roles.1 = .sender → ∀ move,
        state (ExecutionPrefix.prependPublic move (.root (rest move))) → state (.root _)) ∧
      ∀ move, ProverPreserves (rest move) (roles.2 move)
        (fun pfx => state (ExecutionPrefix.prependPublic move pfx))
  | .oracle _ rest, roles, state =>
      (∀ message, state (ExecutionPrefix.prependOracle message (.root (rest PUnit.unit))) →
        state (.root _)) ∧
      ∀ message, ProverPreserves (rest PUnit.unit) (roles.2 PUnit.unit)
        (fun pfx => state (ExecutionPrefix.prependOracle message pfx))

/-- Structural ordinary-security laws for a fixed input and terminal path relation. -/
structure OrdinaryState (protocol : Protocol) (input : Prop)
    (output : protocol.tree.ExecutionPath → Prop) where
  state : ExecutionPrefix protocol.tree → Prop
  initial : ¬ input → ¬ state (.root protocol.tree)
  prover : ProverPreserves protocol.tree protocol.roles state
  terminal : ∀ path, output path → state (.ofExecutionPath path)

/-- Some false-to-true verifier edge occurs on this concrete execution path.
The recursive alternatives follow only the actual path moves and messages. -/
def VerifierEscapeOnPath : (tree : TypeTree) → tree.RoleDecoration →
    (ExecutionPrefix tree → Prop) → tree.ExecutionPath → Prop
  | .done, _, _, _ => False
  | .public _ rest, roles, state, path =>
      (roles.1 = .receiver ∧ ¬ state (.root _) ∧
        state (ExecutionPrefix.prependPublic path.1 (.root (rest path.1)))) ∨
      VerifierEscapeOnPath (rest path.1) (roles.2 path.1)
        (fun pfx => state (ExecutionPrefix.prependPublic path.1 pfx)) path.2
  | .oracle _ rest, roles, state, path =>
      VerifierEscapeOnPath (rest PUnit.unit) (roles.2 PUnit.unit)
        (fun pfx => state (ExecutionPrefix.prependOracle path.1 pfx)) path.2

/-- A path from a false state to a true terminal state contains a verifier escape. -/
theorem ProverPreserves.verifier_escape (tree : TypeTree) (roles : tree.RoleDecoration)
    (state : ExecutionPrefix tree → Prop) (hprover : ProverPreserves tree roles state)
    (path : tree.ExecutionPath) (hfalse : ¬ state (.root _))
    (hterminal : state (.ofExecutionPath path)) :
    VerifierEscapeOnPath tree roles state path := by
  induction tree with
  | done => exact hfalse hterminal
  | «public» Moves rest ih =>
    rcases path with ⟨move, tail⟩
    by_cases hnext : state (ExecutionPrefix.prependPublic move (.root (rest move)))
    · left
      refine ⟨?_, hfalse, hnext⟩
      cases hrole : roles.1 with
      | sender => exact False.elim (hfalse (hprover.1 hrole move hnext))
      | receiver => rfl
    · right
      exact ih move (roles.2 move) (fun pfx => state (ExecutionPrefix.prependPublic move pfx))
        (hprover.2 move) tail hnext hterminal
  | «oracle» Messages rest ih =>
    rcases path with ⟨message, tail⟩
    apply ih (roles.2 PUnit.unit)
      (fun pfx => state (ExecutionPrefix.prependOracle message pfx)) (hprover.2 message) tail
    · exact fun h => hfalse (hprover.1 message h)
    · exact hterminal

/-- Every accepting path from a false input contains a bad verifier challenge.
No probability bound is used; an empty path contradicts the initial and terminal laws. -/
theorem OrdinaryState.exists_verifier_escape {protocol : Protocol} {input : Prop}
    {output : protocol.tree.ExecutionPath → Prop}
    (certificate : OrdinaryState protocol input output)
    (path : protocol.tree.ExecutionPath) (hfalse : ¬ input) (houtput : output path) :
    VerifierEscapeOnPath protocol.tree protocol.roles certificate.state path :=
  certificate.prover.verifier_escape _ _ _ path (certificate.initial hfalse)
    (certificate.terminal path houtput)

/-- All authored branches have at most `count` challenges; only verifier moves increase rank. -/
def ChallengeSchedule : (tree : TypeTree) → tree.RoleDecoration →
    (ExecutionPrefix tree → ℕ) → ℕ → Prop
  | .done, _, rank, count => rank (.root _) ≤ count
  | .public _ rest, roles, rank, count =>
      (match roles.1 with
      | .sender => ∀ move,
          rank (ExecutionPrefix.prependPublic move (.root (rest move))) = rank (.root _)
      | .receiver => rank (.root _) < count ∧ ∀ move,
          rank (ExecutionPrefix.prependPublic move (.root (rest move))) = rank (.root _) + 1) ∧
      ∀ move, ChallengeSchedule (rest move) (roles.2 move)
        (fun pfx => rank (ExecutionPrefix.prependPublic move pfx)) count
  | .oracle _ rest, roles, rank, count =>
      (∀ message,
        rank (ExecutionPrefix.prependOracle message (.root (rest PUnit.unit))) = rank (.root _)) ∧
      ∀ message, ChallengeSchedule (rest PUnit.unit) (roles.2 PUnit.unit)
        (fun pfx => rank (ExecutionPrefix.prependOracle message pfx)) count

/-- The residual root is a public move owned by the verifier. -/
def IsVerifierRoot : (tree : TypeTree) → tree.RoleDecoration → Prop
  | .done, _ => False
  | .public _ _, roles => roles.1 = .receiver
  | .oracle _ _, _ => False

/-- The actual restricted role at this authored prefix is a verifier public move. -/
def IsVerifierPrefix {tree : TypeTree} (roles : tree.RoleDecoration)
    (pfx : ExecutionPrefix tree) : Prop :=
  IsVerifierRoot pfx.cursor.residual (pfx.roles roles)

/-- Fresh local challenge programs and their concrete native prefix extensions. -/
structure ChallengeModel (protocol : Protocol.{0}) where
  Result : ExecutionPrefix protocol.tree → Type
  sample : (pfx : ExecutionPrefix protocol.tree) → ProbComp (Result pfx)
  extend : (pfx : ExecutionPrefix protocol.tree) → Result pfx → ExecutionPrefix protocol.tree

/-- False-to-true escape games indexed by all authored verifier prefixes. -/
def localGames {protocol : Protocol} (model : ChallengeModel protocol)
    (state : ExecutionPrefix protocol.tree → Prop) :
    RoundByRound.GameFamily
      {pfx : ExecutionPrefix protocol.tree // IsVerifierPrefix protocol.roles pfx}
      (fun _ => Unit) where
  Result := fun pfx => model.Result pfx.val
  sample := fun pfx _ => model.sample pfx.val
  event := fun pfx _ result => ¬ state pfx.val ∧ state (model.extend pfx.val result)

/-- Every authored verifier-prefix escape game is bounded by its challenge rank error. -/
def LocalSoundness {protocol : Protocol} (model : ChallengeModel protocol)
    (state : ExecutionPrefix protocol.tree → Prop) (rank : ExecutionPrefix protocol.tree → ℕ)
    (error : ℕ → ℝ≥0∞) : Prop :=
  (localGames model state).IsBounded (fun pfx => error (rank pfx.val))

/-- Actual native verifier actions follow the local challenge model.

At verifier moves, the closed and interpreted action has the specified fresh challenge
event marginals,
and the named observation map gives exactly the concrete prefix extension. Recursion covers
all supported actual verifier continuations; prover messages range over all possible values.
No whole-execution probability bound is assumed. -/
def FreshVerifier {protocol : Protocol} (model : ChallengeModel protocol)
    {ι : Type} (ambient : OracleSpec ι) {m : Type → Type v}
    [Monad m] [EvalDistSemantics m] [MonadAttach m] (handler : QueryImpl ambient m) :
    (tree : TypeTree) → (roles : tree.RoleDecoration) →
    (oracles : tree.OracleDecoration) → (initial : PFunctor) →
    QueryImpl (ofPFunctor initial) Id → (OutV : tree.BranchPath → Type) →
    Verifier.Strategy ambient tree roles oracles initial OutV →
    (ExecutionPrefix tree → ExecutionPrefix protocol.tree) → Prop
  | .done, _, _, _, _, _, _, _ => True
  | .public _ rest, ⟨.sender, roles⟩, oracles, initial, impl, OutV, verifier, embed =>
      ∀ move next, next ∈ support (simulateQ handler
        (simulateQ (Verifier.liftAccessImpl ambient initial impl) (verifier move))) →
        FreshVerifier model ambient handler (rest move) (roles move) (oracles.2 move) initial impl
          (fun path => OutV ⟨move, path⟩) next
          (fun pfx => embed (ExecutionPrefix.prependPublic move pfx))
  | .public _ rest, ⟨.receiver, roles⟩, oracles, initial, impl, OutV, verifier, embed =>
      IsVerifierPrefix protocol.roles (embed (.root _)) ∧
      (∃ encode : _ → model.Result (embed (.root _)),
        (∀ event : model.Result (embed (.root _)) → Prop,
          Pr{let chosen ← (simulateQ handler
            (simulateQ (Verifier.liftAccessImpl ambient initial impl) verifier))}[
              event (encode chosen.1)] =
            Pr{let result ← model.sample (embed (.root _))}[event result]) ∧
        ∀ move, model.extend (embed (.root _)) (encode move) =
          embed (ExecutionPrefix.prependPublic move (.root (rest move)))) ∧
      ∀ chosen ∈ support (simulateQ handler
          (simulateQ (Verifier.liftAccessImpl ambient initial impl) verifier)),
        FreshVerifier model ambient handler (rest chosen.1) (roles chosen.1) (oracles.2 chosen.1)
          initial impl (fun path => OutV ⟨chosen.1, path⟩) chosen.2
          (fun pfx => embed (ExecutionPrefix.prependPublic chosen.1 pfx))
  | .oracle _ rest, roles, oracles, initial, impl, OutV, verifier, embed =>
      ∀ message next, next ∈ support (simulateQ handler (simulateQ
        (Verifier.liftAccessImpl ambient (Access.extend initial oracles.1)
          (Access.extendImpl initial oracles.1 impl message)) verifier)) →
        FreshVerifier model ambient handler (rest PUnit.unit) (roles.2 PUnit.unit)
          (oracles.2 PUnit.unit) (Access.extend initial oracles.1)
          (Access.extendImpl initial oracles.1 impl message)
          (fun path => OutV ⟨PUnit.unit, path⟩) next
          (fun pfx => embed (ExecutionPrefix.prependOracle message pfx))

/-- Transport the same actual native verifier through an all-authored prefix map.

The map preserves verifier roles, fresh event marginals, and concrete challenge extensions.
The native actions and supported private continuations remain unchanged. -/
theorem FreshVerifier.mapPrefixes {source target : Protocol}
    (sourceModel : ChallengeModel source) (targetModel : ChallengeModel target)
    (map : ExecutionPrefix source.tree → ExecutionPrefix target.tree)
    (roles : ∀ pfx, IsVerifierPrefix source.roles pfx → IsVerifierPrefix target.roles (map pfx))
    (resultMap : (pfx : ExecutionPrefix source.tree) →
      sourceModel.Result pfx → targetModel.Result (map pfx))
    (sample : ∀ pfx, IsVerifierPrefix source.roles pfx →
      ∀ event : targetModel.Result (map pfx) → Prop,
      Pr{let result ← sourceModel.sample pfx}[event (resultMap pfx result)] =
        Pr{let result ← targetModel.sample (map pfx)}[event result])
    (extend : ∀ pfx, IsVerifierPrefix source.roles pfx → ∀ result,
      targetModel.extend (map pfx) (resultMap pfx result) =
        map (sourceModel.extend pfx result))
    {ι : Type} (ambient : OracleSpec ι) {m : Type → Type v}
    [Monad m] [EvalDistSemantics m] [MonadAttach m] (handler : QueryImpl ambient m)
    (tree : TypeTree) (nativeRoles : tree.RoleDecoration) (oracles : tree.OracleDecoration)
    (initial : PFunctor) (impl : QueryImpl (ofPFunctor initial) Id)
    (OutV : tree.BranchPath → Type)
    (verifier : Verifier.Strategy ambient tree nativeRoles oracles initial OutV)
    (embed : ExecutionPrefix tree → ExecutionPrefix source.tree)
    (fresh : FreshVerifier sourceModel ambient handler tree nativeRoles oracles initial impl
      OutV verifier embed) :
    FreshVerifier targetModel ambient handler tree nativeRoles oracles initial impl OutV
      verifier (fun pfx => map (embed pfx)) := by
  induction tree generalizing initial with
  | done => trivial
  | «public» Moves rest ih =>
    rcases nativeRoles with ⟨role, nativeRoles⟩
    cases role with
    | sender =>
      intro move next hnext
      exact ih move (nativeRoles move) (oracles.2 move) initial impl
        (fun path => OutV ⟨move, path⟩) next
        (fun pfx => embed (.prependPublic move pfx)) (fresh move next hnext)
    | receiver =>
      obtain ⟨hturn, ⟨encode, heq, hextend⟩, hnext⟩ := fresh
      refine ⟨roles _ hturn, ⟨fun move => resultMap _ (encode move), ?_, ?_⟩, ?_⟩
      · intro event
        rw [heq (fun result => event (resultMap _ result))]
        exact sample _ hturn event
      · intro move
        rw [extend _ hturn, hextend move]
      · intro chosen hchosen
        exact ih chosen.1 (nativeRoles chosen.1) (oracles.2 chosen.1) initial impl
          (fun path => OutV ⟨chosen.1, path⟩) chosen.2
          (fun pfx => embed (.prependPublic chosen.1 pfx)) (hnext chosen hchosen)
  | «oracle» Messages rest ih =>
    intro message next hnext
    exact ih (nativeRoles.2 PUnit.unit) (oracles.2 PUnit.unit)
      (Access.extend initial oracles.1) (Access.extendImpl initial oracles.1 impl message)
      (fun path => OutV ⟨PUnit.unit, path⟩) next
      (fun pfx => embed (.prependOracle message pfx)) (fresh message next hnext)

end Interaction.Oracle.Security

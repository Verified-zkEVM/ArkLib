/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
module

public import ArkLib.ProofSystem.Logup.Interaction.Protocol

/-!
# Exact execution of the weighted LogUp prefix

These open-program equalities expose the actual challenge and prover bind order. Prefix
continuations are extracted from the supplied whole prover by the existing append projection.
Both receiver responses and the helper sender retain their ambient effects. Erasing only the
prover's final private return value preserves the complete executable Boolean endpoint.

The suffix is the existing complete native Sumcheck verifier over the Q behavior exported by
this run's retained source. The equality follows from the proved exported-composition routing
law and actual terminal authentication; no desired execution equality or message kernel is a
premise. Interpreted source handlers are pure, so this law concerns ambient programs rather than
raw query logs across the exported source boundary.
-/

@[expose] public section

open Interaction.Oracle OracleComp OracleSpec
open PFunctor.FreeM.Displayed (Decoration)

namespace Logup.Interaction

variable {E : Type} [CommRing E]

/-- Extract the actual weighted-prefix strategy and its native suffix continuation from a whole
Unit-output prover. This uses the existing append projection, without a new adversary model. -/
def splitPrefixProver (n K ell : Nat) {ι : Type} (ambient : OracleSpec ι)
    (prover : Prover.Strategy ambient (protocol E n K ell).tree
      (protocol E n K ell).roles (fun _ ↦ Unit)) :
    Prover.Strategy ambient (prefixProtocol E n K).tree (prefixProtocol E n K).roles
      (fun _ ↦ Prover.Strategy ambient
        (Sumcheck.Interaction.Computable.protocol E (ell + 2) n).tree
        (Sumcheck.Interaction.Computable.protocol E (ell + 2) n).roles (fun _ ↦ Unit)) :=
  Interaction.StrategyOver.TwoParty.Focal.splitPrefix
    (onAppendedRuntime ambient _root_.Interaction.TwoParty.Participant.focal
      (prefixProtocol E n K).tree
      (fun _ ↦ (Sumcheck.Interaction.Computable.protocol E (ell + 2) n).tree)
      (prefixProtocol E n K).roles
      (fun _ ↦ (Sumcheck.Interaction.Computable.protocol E (ell + 2) n).roles)
      (fun _ ↦ Unit) prover)
end Logup.Interaction

namespace Logup.Interaction

variable {B E : Type} [CommRing B] [CommRing E] [DecidableEq E]
variable (f : B →+* E) (n T ell : Nat) (cfg : Config n T ell)
variable {ι : Type} (ambient : OracleSpec ι)

/-- The actual terminal source action accepts precisely the native closed claim from the same
run, for every dependent private-output family. -/
theorem execute_eq_accepts_closed (alphaDraw : OracleComp ambient E)
    (jointDraw : OracleComp ambient ((Fin n → E) × (Fin (T ⌈/⌉ ell) → E)))
    (roundDraw : OracleComp ambient E) (A : PFunctor.{0, 0})
    (inputView : VirtualOracle (ofPFunctor A) (inputFamily f n T))
    (impl : QueryImpl (ofPFunctor A) Id)
    {OutP : (protocol E n (T ⌈/⌉ ell) ell).tree.ExecutionPath → Type}
    (prover : Prover.Strategy ambient (protocol E n (T ⌈/⌉ ell) ell).tree
      (protocol E n (T ⌈/⌉ ell) ell).roles OutP) :
    execute f n T ell cfg ambient alphaDraw jointDraw roundDraw A inputView impl prover =
      (fun result ↦ Sumcheck.Interaction.Native.Core.accepts E n (ell + 2)
        (result.2.2.map (fun claim ↦ claim.closeWith
          (result.1.closingImpl (protocol E n (T ⌈/⌉ ell) ell).oracles A impl)))) <$>
        executeStrategies ambient (protocol E n (T ⌈/⌉ ell) ell).tree
          (protocol E n (T ⌈/⌉ ell) ell).roles (protocol E n (T ⌈/⌉ ell) ell).oracles A impl
          prover
          (reductionVerifier f n T ell cfg ambient alphaDraw jointDraw roundDraw A inputView) := by
  simp only [execute, verifier, executeStrategies, Verifier.toCounterpart]
  rw [Verifier.toCounterpartWith_mapOutput, Verifier.toCounterpartWith_finish_eq_mapOutput,
    run_counterpart_mapOutput]
  simp only [bind_map_left, Sumcheck.Interaction.Native.Core.simulate_checkFinalResult,
    map_bind, map_pure, bind_assoc, pure_bind]
  rw [Verifier.toCounterpartWith_finish_eq_mapOutput, run_counterpart_mapOutput]
  simp only [bind_map_left]
end Logup.Interaction

namespace Logup.Interaction

variable {B E : Type} [CommRing B] [CommRing E] [DecidableEq E]
variable (f : B →+* E) (n T ell : Nat) (cfg : Config n T ell)
variable {ι : Type} (ambient : OracleSpec ι)

set_option backward.isDefEq.respectTransparency false in
/-- Executing the actual weighted verifier factors through its prefix run and the existing
complete native verifier over the Q behavior exported by that run's retained source. -/
theorem execute_eq_prefix_run (alphaDraw : OracleComp ambient E)
    (jointDraw : OracleComp ambient ((Fin n → E) × (Fin (T ⌈/⌉ ell) → E)))
    (roundDraw : OracleComp ambient E) (A : PFunctor.{0, 0})
    (inputView : VirtualOracle (ofPFunctor A) (inputFamily f n T))
    (impl : QueryImpl (ofPFunctor A) Id)
    (prover : Prover.Strategy ambient (protocol E n (T ⌈/⌉ ell) ell).tree
      (protocol E n (T ⌈/⌉ ell) ell).roles (fun _ ↦ Unit)) :
    execute f n T ell cfg ambient alphaDraw jointDraw roundDraw A inputView impl prover = (do
      let result ← _root_.Interaction.TwoParty.run
        (prefixProtocol E n (T ⌈/⌉ ell)).tree.toTypeTree
        (TypeTree.RoleDecoration.toTypeTreeRoles (prefixProtocol E n (T ⌈/⌉ ell)).tree
          (prefixProtocol E n (T ⌈/⌉ ell)).roles)
        (splitPrefixProver n (T ⌈/⌉ ell) ell ambient prover)
        (Verifier.toCounterpartValue ambient (prefixProtocol E n (T ⌈/⌉ ell)).tree
          (prefixProtocol E n (T ⌈/⌉ ell)).roles
          (prefixProtocol E n (T ⌈/⌉ ell)).oracles A impl _
          (prefixVerifier f n T ell cfg ambient alphaDraw jointDraw A inputView))
      Sumcheck.Interaction.Computable.executeWithFinalCheck E n (ell + 2) ambient roundDraw [0,1]
        n 0 (Nat.zero_add n) (family (E := E) n ell).spec.toPFunctor
        (VirtualOracle.id (family (E := E) n ell)) result.2.2.stmt
        (result.2.2.oracles.eval ((TypeTree.ExecutionPath.ofTypeTreePath result.1).closingImpl
          (prefixProtocol E n (T ⌈/⌉ ell)).oracles A impl))
        (OutP := fun _ ↦ Unit) result.2.1) := by
  have routing := executeStrategies_appendExported_close ambient
    (prefixProtocol E n (T ⌈/⌉ ell)).tree
    (fun _ ↦ (Sumcheck.Interaction.Computable.protocol E (ell + 2) n).tree)
    (prefixProtocol E n (T ⌈/⌉ ell)).roles
    (fun _ ↦ (Sumcheck.Interaction.Computable.protocol E (ell + 2) n).roles)
    (prefixProtocol E n (T ⌈/⌉ ell)).oracles
    (fun _ ↦ (Sumcheck.Interaction.Computable.protocol E (ell + 2) n).oracles) A impl
    (fun _ ↦ Sumcheck.Spec.StatementRound E n 0)
    (fun _ ↦ Sumcheck.Spec.OracleStatement E n (ell + 2)) (fun _ ↦ family (E := E) n ell)
    (fun _ ↦ Sumcheck.Interaction.Computable.FinalStatement E n)
    (fun _ ↦ Sumcheck.Spec.OracleStatement E n (ell + 2)) (fun _ ↦ family (E := E) n ell)
    (fun _ ↦ Unit) prover (prefixVerifier f n T ell cfg ambient alphaDraw jointDraw A inputView)
    (suffixVerifier n T ell ambient roundDraw)
  have accepted := congrArg (fun program ↦
    (fun result ↦ Sumcheck.Interaction.Native.Core.accepts E n (ell + 2) result.2.2) <$> program)
    routing
  rw [execute_eq_accepts_closed]
  simp only [Functor.map_map] at accepted
  convert accepted using 1
  · rfl
  · simp only [splitPrefixProver, suffixVerifier, Verifier.toCounterpartWith_finish_eq_mapOutput,
      run_counterpart_mapOutput, bind_map_left, map_bind, map_pure]
    apply bind_congr
    rintro ⟨path, continuation, mid⟩
    dsimp only
    unfold Sumcheck.Interaction.Computable.executeWithFinalCheck
      Sumcheck.Interaction.Native.Core.executeWithFinalCheck
      Sumcheck.Interaction.Native.Core.verifierWithFinalCheck
    simp only [executeStrategies, Verifier.toCounterpart]
    rw [Verifier.toCounterpartWith_mapOutput,
      Verifier.toCounterpartWith_finish_eq_mapOutput, run_counterpart_mapOutput]
    simp only [bind_map_left, Sumcheck.Interaction.Native.Core.simulate_checkFinalResult,
      map_bind, map_pure, cast_eq]

end Logup.Interaction


namespace Logup.Interaction

variable {B E : Type} [CommRing B] [CommRing E] [DecidableEq E]
variable (f : B →+* E) (n T ell : Nat) (cfg : Config n T ell)
variable {ι : Type} (ambient : OracleSpec ι)

/-- Erasing only the whole prover's private return value preserves the Boolean program,
including all prior and terminal private effects. -/
theorem execute_eq_eraseOutput (alphaDraw : OracleComp ambient E)
    (jointDraw : OracleComp ambient ((Fin n → E) × (Fin (T ⌈/⌉ ell) → E)))
    (roundDraw : OracleComp ambient E) (A : PFunctor.{0, 0})
    (inputView : VirtualOracle (ofPFunctor A) (inputFamily f n T))
    (impl : QueryImpl (ofPFunctor A) Id)
    {OutP : (protocol E n (T ⌈/⌉ ell) ell).tree.ExecutionPath → Type}
    (prover : Prover.Strategy ambient (protocol E n (T ⌈/⌉ ell) ell).tree
      (protocol E n (T ⌈/⌉ ell) ell).roles OutP) :
    execute f n T ell cfg ambient alphaDraw jointDraw roundDraw A inputView impl prover =
      execute f n T ell cfg ambient alphaDraw jointDraw roundDraw A inputView impl
        (OutP := fun _ ↦ Unit)
        (Interaction.StrategyOver.TwoParty.Focal.mapOutput (fun _ _ ↦ (() : Unit)) prover) := by
  let counterpart := Verifier.toCounterpart ambient (protocol E n (T ⌈/⌉ ell) ell).tree
    (protocol E n (T ⌈/⌉ ell) ell).roles (protocol E n (T ⌈/⌉ ell) ell).oracles A impl
    (fun _ ↦ Bool)
    (verifier f n T ell cfg ambient alphaDraw jointDraw roundDraw A inputView)
  have mapped := _root_.Interaction.TwoParty.run_mapOutput_mapOutput (OutputP' := fun _ ↦ Unit)
    (fun _ _ ↦ (() : Unit)) (fun _ out ↦ out) prover counterpart
  simp only [Interaction.StrategyOver.TwoParty.Counterpart.mapOutput_id] at mapped
  simp only [execute, executeStrategies]
  rw [mapped]
  simp only [bind_map_left, bind_assoc, pure_bind]
  rfl
end Logup.Interaction

namespace Logup.Interaction

variable {B E : Type} [CommRing B] [CommRing E] [DecidableEq E]
variable (f : B →+* E) (n T ell : Nat) (cfg : Config n T ell)
variable {ι : Type} (ambient : OracleSpec ι)

set_option backward.isDefEq.respectTransparency false in
private theorem prefix_run_eq_binds (alphaDraw : OracleComp ambient E)
    (jointDraw : OracleComp ambient ((Fin n → E) × (Fin (T ⌈/⌉ ell) → E)))
    (roundDraw : OracleComp ambient E) (A : PFunctor.{0, 0})
    (inputView : VirtualOracle (ofPFunctor A) (inputFamily f n T))
    (impl : QueryImpl (ofPFunctor A) Id)
    (prefixP : Prover.Strategy ambient (prefixProtocol E n (T ⌈/⌉ ell)).tree
      (prefixProtocol E n (T ⌈/⌉ ell)).roles
      (fun _ ↦ Prover.Strategy ambient
        (Sumcheck.Interaction.Computable.protocol E (ell + 2) n).tree
        (Sumcheck.Interaction.Computable.protocol E (ell + 2) n).roles (fun _ ↦ Unit))) :
    (do
      let result ← _root_.Interaction.TwoParty.run
        (prefixProtocol E n (T ⌈/⌉ ell)).tree.toTypeTree
        (TypeTree.RoleDecoration.toTypeTreeRoles (prefixProtocol E n (T ⌈/⌉ ell)).tree
          (prefixProtocol E n (T ⌈/⌉ ell)).roles) prefixP
        (Verifier.toCounterpartValue ambient (prefixProtocol E n (T ⌈/⌉ ell)).tree
          (prefixProtocol E n (T ⌈/⌉ ell)).roles
          (prefixProtocol E n (T ⌈/⌉ ell)).oracles A impl _
          (prefixVerifier f n T ell cfg ambient alphaDraw jointDraw A inputView))
      Sumcheck.Interaction.Computable.executeWithFinalCheck E n (ell + 2) ambient roundDraw [0,1]
        n 0 (Nat.zero_add n) (family (E := E) n ell).spec.toPFunctor
        (VirtualOracle.id (family (E := E) n ell)) result.2.2.stmt
        (result.2.2.oracles.eval ((TypeTree.ExecutionPath.ofTypeTreePath result.1).closingImpl
          (prefixProtocol E n (T ⌈/⌉ ell)).oracles A impl))
        (OutP := fun _ ↦ Unit) result.2.1) = (do
      let alpha ← alphaDraw
      let helperStage ← prefixP alpha
      let sent ← helperStage
      let joint ← jointDraw
      let continuation ← sent.2 joint
      Sumcheck.Interaction.Computable.executeWithFinalCheck E n (ell + 2) ambient roundDraw [0,1]
        n 0 (Nat.zero_add n) (family (E := E) n ell).spec.toPFunctor
        (VirtualOracle.id (family (E := E) n ell)) (zeroStatement E n)
        ((qView f n T (T ⌈/⌉ ell) cfg.groups alpha joint.1 joint.2 ell A inputView).eval
          (Access.extendImpl A (helperInterface (E := E) n (T ⌈/⌉ ell)) impl sent.1))
        (OutP := fun _ ↦ Unit) continuation) := by
  have lift_eq (access : PFunctor) (handler : QueryImpl (ofPFunctor access) Id)
      {X : Type} (program : OracleComp ambient X) :
      simulateQ (Verifier.liftAccessImpl ambient access handler)
        (OracleComp.liftComp program (ambient + ofPFunctor access)) = program := by
    rw [QueryImpl.simulateQ_liftComp_left_eq_of_apply
      (impl₁ := QueryImpl.id' ambient) (h := fun _ ↦ rfl), simulateQ_id']
  simp only [prefixProtocol, Protocol.public, Protocol.oracleWith, Protocol.done,
    Protocol.tree, Protocol.roles, Protocol.oracles, prefixVerifier,
    TypeTree.toTypeTree_public, TypeTree.toTypeTree_oracle, TypeTree.toTypeTree_done,
    TypeTree.RoleDecoration.toTypeTreeRoles,
    Verifier.toCounterpartValue,
    Verifier.toCounterpartWith, simulateQ_bind, simulateQ_pure, lift_eq, pure_bind,
    bind_assoc]
  simp only [PFunctor.FreeM.liftBind_eq, PFunctor.FreeM.bind_eq_bind,
    _root_.Interaction.TypeTree.done,
    _root_.Interaction.TwoParty.run_receiver, _root_.Interaction.TwoParty.run_sender,
    _root_.Interaction.TwoParty.run_done, bind_assoc, pure_bind]
  rfl

end Logup.Interaction

namespace Logup.Interaction

variable {B E : Type} [CommRing B] [CommRing E] [DecidableEq E]
variable (f : B →+* E) (n T ell : Nat) (cfg : Config n T ell)
variable {ι : Type} (ambient : OracleSpec ι)

/-- The complete executable verifier has this exact challenge and prover bind order, against
any whole prover with arbitrary dependent private output. The prefix is projected from that
prover after effect-preserving return-value erasure; it is not an assumed helper kernel. -/
theorem execute_eq_prefix_binds (alphaDraw : OracleComp ambient E)
    (jointDraw : OracleComp ambient ((Fin n → E) × (Fin (T ⌈/⌉ ell) → E)))
    (roundDraw : OracleComp ambient E) (A : PFunctor.{0, 0})
    (inputView : VirtualOracle (ofPFunctor A) (inputFamily f n T))
    (impl : QueryImpl (ofPFunctor A) Id)
    {OutP : (protocol E n (T ⌈/⌉ ell) ell).tree.ExecutionPath → Type}
    (prover : Prover.Strategy ambient (protocol E n (T ⌈/⌉ ell) ell).tree
      (protocol E n (T ⌈/⌉ ell) ell).roles OutP) :
    execute f n T ell cfg ambient alphaDraw jointDraw roundDraw A inputView impl prover = (do
      let prefixP := splitPrefixProver n (T ⌈/⌉ ell) ell ambient
        (Interaction.StrategyOver.TwoParty.Focal.mapOutput (fun _ _ ↦ (() : Unit)) prover)
      let alpha ← alphaDraw
      let helperStage ← prefixP alpha
      let sent ← helperStage
      let joint ← jointDraw
      let continuation ← sent.2 joint
      Sumcheck.Interaction.Computable.executeWithFinalCheck E n (ell + 2) ambient roundDraw [0, 1]
        n 0 (Nat.zero_add n) (family (E := E) n ell).spec.toPFunctor
        (VirtualOracle.id (family (E := E) n ell)) (zeroStatement E n)
        ((qView f n T (T ⌈/⌉ ell) cfg.groups alpha joint.1 joint.2 ell A inputView).eval
          (Access.extendImpl A (helperInterface (E := E) n (T ⌈/⌉ ell)) impl sent.1))
        (OutP := fun _ ↦ Unit) continuation) := by
  rw [execute_eq_eraseOutput, execute_eq_prefix_run, prefix_run_eq_binds]
end Logup.Interaction

/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/
module
public import ArkLib.ProofSystem.Sumcheck.Interaction.Resources
public import ArkLib.Interaction.Oracle.PhasedExecution
import all ArkLib.Interaction.Oracle.PhasedExecution
import all ArkLib.Interaction.Oracle.Execution

/-!
# Verifier-party sampling in actual native phased executions

Count verifier-party queries in the existing boundary-labelled phases of the actual complete
executor. The supplied draw program may make several primitive queries per invocation; its
supported log length is an explicit premise. Original-source handlers are pure, so source reads,
local checks and terminal authentication add no ambient queries. Prover logs and private effects
remain arbitrary, including queries to the same sampler index and responses after public abort.

The equality counts every completed supported run, including final rejection, without assuming
losslessness. It is not a bound on all ambient queries of a malicious prover or on the internal
cost of a primitive sampler. Selected sampler instances supply their own supported-log premise.
-/

@[expose] public section

open Interaction Interaction.Oracle OracleComp OracleSpec CompPoly
namespace Sumcheck.Interaction.Computable.SamplingResources
open Resources
variable {R : Type} [CommSemiring R] [DecidableEq R]

set_option backward.isDefEq.respectTransparency false in
omit [DecidableEq R] in
private theorem logged_latest {deg : Nat} {ι : Type}
    (ambient : OracleSpec ι) (A : PFunctor) (prior : QueryImpl (ofPFunctor A) Id)
    (message : Impl.Representation.Message R deg) (x : R) :
    (simulateQ (Verifier.loggedLiftAccessImpl ambient
      (Access.extend A (Native.Core.messageInterface R
        (Impl.Representation.Message R deg) (Impl.Representation.evaluate R deg)))
      (Access.extendImpl A (Native.Core.messageInterface R
        (Impl.Representation.Message R deg) (Impl.Representation.evaluate R deg)) prior message))
      (Native.Core.latest R (Impl.Representation.Message R deg)
        (Impl.Representation.evaluate R deg) ambient A x)).run =
      pure (Impl.Representation.evaluate R deg message x,
        [⟨.inr x, Impl.Representation.evaluate R deg message x⟩]) := by
  have h := logged_latestSum ambient A prior message [x]
  simpa [Native.Core.latestSum_cons, Native.Core.latestSum_nil, simulateQ_bind,
    simulateQ_pure, WriterT.run_bind', WriterT.run_pure', pure_bind,
    bind_pure_comp, add_zero] using h

set_option backward.isDefEq.respectTransparency false in
private theorem complete_zero (n deg : Nat) {ι : Type}
    (ambient : OracleSpec ι) (challenge : OracleComp ambient R) (start : Nat)
    (finish : start + 0 = n) (A : PFunctor)
    (original : VirtualOracle (ofPFunctor A) (MultivariateRound.polynomialFamily R n deg))
    (stmt : Spec.StatementRound R n ⟨start, by omega⟩) :
    verifierWithFinalCheck R n deg ambient challenge [0, 1] 0 start finish A original stmt =
      Native.Core.checkFinalClaim R n deg ambient A
        ⟨⟨stmt.target, stmt.challenges ∘ Fin.cast (by simp; omega)⟩, original⟩ := by
  rfl

set_option backward.isDefEq.respectTransparency false in
private theorem complete_succ (n deg : Nat) {ι : Type}
    (ambient : OracleSpec ι) (challenge : OracleComp ambient R) (count start : Nat)
    (finish : start + (count + 1) = n) (A : PFunctor)
    (original : VirtualOracle (ofPFunctor A) (MultivariateRound.polynomialFamily R n deg))
    (stmt : Spec.StatementRound R n ⟨start, by omega⟩) :
    verifierWithFinalCheck R n deg ambient challenge [0, 1]
        (count + 1) start finish A original stmt = (do
      let total ← Native.Core.latestSum R (Impl.Representation.Message R deg)
        (Impl.Representation.evaluate R deg) ambient A [0, 1]
      return do
        if total = stmt.target then
          let r ← OracleComp.liftComp challenge
            (ambient + ofPFunctor (Access.extend A (Native.Core.messageInterface R
              (Impl.Representation.Message R deg) (Impl.Representation.evaluate R deg))))
          let value ← Native.Core.latest R (Impl.Representation.Message R deg)
            (Impl.Representation.evaluate R deg) ambient A r
          return ⟨some r, verifierWithFinalCheck R n deg ambient challenge [0, 1]
            count (start + 1) (by omega)
            (Access.extend A (Native.Core.messageInterface R
              (Impl.Representation.Message R deg) (Impl.Representation.evaluate R deg)))
            (original.sumWeaken (Native.Core.messageInterface R
              (Impl.Representation.Message R deg) (Impl.Representation.evaluate R deg)).spec)
            ⟨value, Fin.snoc stmt.challenges r⟩⟩
        else return ⟨none, pure false⟩) := by
  simp only [verifierWithFinalCheck, Native.Core.verifierWithFinalCheck,
    Native.Core.verifier, Verifier.Fragment.mapOutput, ShapeOver.mapOutput,
    Verifier.localShape, Verifier.decorate, Native.Core.protocol,
    Protocol.oracleWith_tree, Protocol.oracleWith_roles, Protocol.oracleWith_oracles,
    Protocol.public_tree, Protocol.public_roles, Protocol.public_oracles,
    Impl.VerifierChecks.equalM, Id.run, decide_eq_true_eq,
    map_bind, map_pure]
  apply bind_congr
  intro total
  split_ifs
  · simp only [map_bind, map_pure]
    apply congrArg pure
    apply bind_congr
    intro r
    apply bind_congr
    intro value
    rfl
  · rfl

set_option backward.isDefEq.respectTransparency false in
/-- Each passed native check invokes the actual verifier draw program once. -/
theorem phased_verifier_queries (n deg : Nat) {ι : Type}
    (ambient : OracleSpec ι) (challenge : OracleComp ambient R) (c : Nat)
    (hchallenge : ∀ sample ∈ support challenge.withQueryLog, sample.2.length = c)
    (count start : Nat) (finish : start + count = n) (A : PFunctor)
    (original : VirtualOracle (ofPFunctor A) (MultivariateRound.polynomialFamily R n deg))
    (stmt : Spec.StatementRound R n ⟨start, by omega⟩) (impl : QueryImpl (ofPFunctor A) Id)
    {OutP : (protocol R deg count).tree.ExecutionPath → Type}
    (prover : Prover.Strategy ambient (protocol R deg count).tree
      (protocol R deg count).roles OutP) :
    ∀ result ∈ support (executeStrategiesPhased ambient (protocol R deg count).tree
      (protocol R deg count).roles (protocol R deg count).oracles A impl prover
      (verifierWithFinalCheck R n deg ambient challenge [0, 1]
        count start finish A original stmt)),
      WorldSegments.queryCount .verifier (protocol R deg count).roles result.world =
        c * (pathUsage deg count result.path).roundSamples := by
  induction count generalizing start A with
  | zero =>
    intro result hresult
    simp only [complete_zero, Computable.protocol, Native.Core.protocol,
      Protocol.done_tree, Protocol.done_roles, Protocol.done_oracles,
      executeStrategiesPhased] at hresult
    erw [logged_checkFinalClaim] at hresult
    simp only [OracleComp.withQueryLog_pure, pure_bind] at hresult
    have heq := OracleComp.eq_of_mem_support_pure _ hresult
    subst result
    simp [pathUsage, Computable.protocol, Native.Core.protocol,
      WorldSegments.queryCount_done]
  | succ count ih =>
    intro result hresult
    simp only [complete_succ, Computable.protocol, Native.Core.protocol,
      Protocol.oracleWith_tree, Protocol.oracleWith_roles, Protocol.oracleWith_oracles,
      Protocol.public_tree, Protocol.public_roles, Protocol.public_oracles,
      executeStrategiesPhased] at hresult
    obtain ⟨chosen, _, hresult⟩ := OracleComp.mem_support_bind_peel _ _ hresult
    simp only [simulateQ_bind, simulateQ_pure, WriterT.run_bind', WriterT.run_pure',
      logged_latestSum, pure_bind, map_pure, Prod.map, id_eq,
      OracleComp.withQueryLog_pure] at hresult
    by_cases check : ([0, 1].map fun x => Impl.Representation.evaluate R deg chosen.1.1 x).sum =
        stmt.target
    · simp only [check, ↓reduceIte, simulateQ_bind, simulateQ_pure,
        WriterT.run_bind', WriterT.run_pure', Verifier.loggedLiftAccessImpl_liftComp,
        logged_latest, pure_bind, bind_map_left, map_pure, List.nil_append,
        OracleComp.withQueryLog_bind, OracleComp.withQueryLog_pure,
        Prod.map, id_eq, List.append_nil, bind_assoc] at hresult
      obtain ⟨sample, hsample, hresult⟩ := OracleComp.mem_support_bind_peel _ _ hresult
      obtain ⟨nextP, _, hresult⟩ := OracleComp.mem_support_bind_peel _ _ hresult
      obtain ⟨tail, htail, hresult⟩ := OracleComp.mem_support_bind_peel _ _ hresult
      have heq := OracleComp.eq_of_mem_support_pure _ hresult
      subst result
      have hc := hchallenge sample hsample
      have ht := ih (start + 1) (by omega) _
        (original.sumWeaken (Native.Core.messageInterface R
          (Impl.Representation.Message R deg) (Impl.Representation.evaluate R deg)).spec)
        ⟨Impl.Representation.evaluate R deg chosen.1.1 sample.1,
          Fin.snoc stmt.challenges sample.1⟩
        (Access.extendImpl A (Native.Core.messageInterface R
          (Impl.Representation.Message R deg) (Impl.Representation.evaluate R deg))
          impl chosen.1.1)
        (OutP := fun path => OutP ⟨chosen.1.1, ⟨some sample.1, path⟩⟩) nextP.1 tail htail
      simp only [Computable.protocol, Native.Core.protocol, Protocol.oracleWith_roles,
        WorldSegments.queryCount_oracle, pathUsage, roundUsage, plus]
      erw [WorldSegments.queryCount_public_receiver]
      simpa [hc, Nat.mul_add] using congrArg (fun count => c + count) ht
    · simp only [check, ↓reduceIte, simulateQ_pure, WriterT.run_pure',
        OracleComp.withQueryLog_pure, pure_bind, Protocol.done_tree, Protocol.done_roles,
        Protocol.done_oracles, executeStrategiesPhased, bind_assoc] at hresult
      obtain ⟨nextP, _, hresult⟩ := OracleComp.mem_support_bind_peel _ _ hresult
      have heq := OracleComp.eq_of_mem_support_pure _ hresult
      subst result
      simp only [Computable.protocol, Native.Core.protocol, Protocol.oracleWith_roles,
        WorldSegments.queryCount_oracle, pathUsage, roundUsage]
      erw [WorldSegments.queryCount_public_receiver]
      simp [WorldSegments.queryCount_done]

end Sumcheck.Interaction.Computable.SamplingResources

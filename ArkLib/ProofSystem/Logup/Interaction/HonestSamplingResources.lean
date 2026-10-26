/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
module
public import ArkLib.ProofSystem.Logup.Lookup.ArithmeticProver
public import ArkLib.ProofSystem.Logup.Lookup.Tuple.ArithmeticProver
public import ArkLib.Interaction.Oracle.PhasedExecution
import all ArkLib.Interaction.Oracle.PhasedExecution

/-!
# Private ambient queries of actual honest LogUp provers

The existing phased executor observes each selected honest sender and receiver action as pure.
Every supported run therefore has zero prover-party ambient queries, including public abort
responses and zero native rounds. Verifier actions, output families and ambient queries remain
arbitrary; source reads still execute under the same actual retained handlers.

Reference statements allow any pure message builder without a correctness or off-pole premise.
Exact ordinary-strategy equalities transfer this observable log fact to the measured weighted,
scalar and eager tuple defaults. They do not transfer arithmetic request profiles, preprocessing,
storage or machine costs. No losslessness, lookup validity or verifier-query bound is asserted.
-/

@[expose] public section

open Interaction Interaction.Oracle OracleComp OracleSpec CompPoly
namespace Logup.Interaction.HonestSamplingResources
open Logup.Prover.Honest

set_option backward.isDefEq.respectTransparency false in
/-- Every actual native honest action has an empty private log, for any restricted verifier. -/
theorem nativeWith_prover_queries_zero {E : Type} [CommRing E] {T K ell : Nat}
    {ι : Type} (ambient : OracleSpec ι)
    (build : (r : Nat) → Logup.Prover.State E T K (r + 1) →
      Sumcheck.Impl.Representation.Message E (ell + 2))
    (count : Nat) (state : Logup.Prover.State E T K count)
    (A : PFunctor) (impl : QueryImpl (ofPFunctor A) Id)
    {OutV : (Sumcheck.Interaction.Computable.protocol E (ell + 2) count).tree.BranchPath → Type}
    (verifier : Verifier.Strategy ambient
      (Sumcheck.Interaction.Computable.protocol E (ell + 2) count).tree
      (Sumcheck.Interaction.Computable.protocol E (ell + 2) count).roles
      (Sumcheck.Interaction.Computable.protocol E (ell + 2) count).oracles A OutV) :
    ∀ result ∈ support (executeStrategiesPhased ambient
      (Sumcheck.Interaction.Computable.protocol E (ell + 2) count).tree
      (Sumcheck.Interaction.Computable.protocol E (ell + 2) count).roles
      (Sumcheck.Interaction.Computable.protocol E (ell + 2) count).oracles A impl
      (nativeWith ambient build count state) verifier),
      WorldSegments.queryCount .prover
        (Sumcheck.Interaction.Computable.protocol E (ell + 2) count).roles result.world = 0 := by
  induction count generalizing A with
  | zero =>
    intro result hresult
    simp only [Sumcheck.Interaction.Computable.protocol, Sumcheck.Interaction.Native.Core.protocol,
      Protocol.done_tree, Protocol.done_roles, Protocol.done_oracles,
      executeStrategiesPhased] at hresult
    obtain ⟨terminal, _, hresult⟩ := OracleComp.mem_support_bind_peel _ _ hresult
    have heq := OracleComp.eq_of_mem_support_pure _ hresult
    subst result
    simp [Sumcheck.Interaction.Computable.protocol, Sumcheck.Interaction.Native.Core.protocol,
      WorldSegments.queryCount_done]
  | succ count ih =>
    intro result hresult
    simp only [nativeWith, Sumcheck.Interaction.Computable.protocol,
      Sumcheck.Interaction.Native.Core.protocol, Protocol.oracleWith_tree,
      Protocol.oracleWith_roles, Protocol.oracleWith_oracles,
      Protocol.public_tree, Protocol.public_roles, Protocol.public_oracles,
      executeStrategiesPhased, OracleComp.withQueryLog_pure, pure_bind, bind_assoc] at hresult
    obtain ⟨received, _, hresult⟩ := OracleComp.mem_support_bind_peel _ _ hresult
    obtain ⟨choice, _, hresult⟩ := OracleComp.mem_support_bind_peel _ _ hresult
    rcases choice with ⟨⟨⟨move, nextV⟩, laterSource⟩, laterWorld⟩
    cases move with
    | none =>
      simp only [OracleComp.withQueryLog_pure, pure_bind, Protocol.done_tree,
        Protocol.done_roles, Protocol.done_oracles, executeStrategiesPhased, bind_assoc]
        at hresult
      obtain ⟨terminal, _, hresult⟩ := OracleComp.mem_support_bind_peel _ _ hresult
      have heq := OracleComp.eq_of_mem_support_pure _ hresult
      subst result
      simp only [Sumcheck.Interaction.Computable.protocol,
        Sumcheck.Interaction.Native.Core.protocol, Protocol.oracleWith_roles,
        WorldSegments.queryCount_oracle]
      erw [WorldSegments.queryCount_public_receiver]
      simp [WorldSegments.queryCount_done]
    | some r =>
      simp only [OracleComp.withQueryLog_pure, pure_bind] at hresult
      obtain ⟨tail, htail, hresult⟩ := OracleComp.mem_support_bind_peel _ _ hresult
      have heq := OracleComp.eq_of_mem_support_pure _ hresult
      subst result
      have ht := ih (Logup.Prover.State.fold state r) _
        (Access.extendImpl A (Sumcheck.Interaction.Native.Core.messageInterface E
          (Sumcheck.Impl.Representation.Message E (ell + 2))
          (Sumcheck.Impl.Representation.evaluate E (ell + 2))) impl (build count state))
        (OutV := fun path => OutV ⟨PUnit.unit, ⟨some r, path⟩⟩) nextV tail htail
      simp only [Sumcheck.Interaction.Computable.protocol,
        Sumcheck.Interaction.Native.Core.protocol, Protocol.oracleWith_roles,
        WorldSegments.queryCount_oracle]
      erw [WorldSegments.queryCount_public_receiver]
      simpa using ht

set_option backward.isDefEq.respectTransparency false in
/-- The alpha/helper/joint prefix and native continuation have no private ambient query. -/
theorem honestWith_prover_queries_zero {B E : Type} [CommRing B] [Field E]
    {n T ell : Nat} (f : B →+* E) (cfg : Config n T ell)
    (data : Fin 2 × Fin T → CMlPolynomialEval B n) {ι : Type} (ambient : OracleSpec ι)
    (build : (r : Nat) → Logup.Prover.State E T (T ⌈/⌉ ell) (r + 1) →
      Sumcheck.Impl.Representation.Message E (ell + 2))
    (A : PFunctor) (impl : QueryImpl (ofPFunctor A) Id)
    {OutV : (protocol E n (T ⌈/⌉ ell) ell).tree.BranchPath → Type}
    (verifier : Verifier.Strategy ambient (protocol E n (T ⌈/⌉ ell) ell).tree
      (protocol E n (T ⌈/⌉ ell) ell).roles (protocol E n (T ⌈/⌉ ell) ell).oracles A OutV) :
    ∀ result ∈ support (executeStrategiesPhased ambient (protocol E n (T ⌈/⌉ ell) ell).tree
      (protocol E n (T ⌈/⌉ ell) ell).roles (protocol E n (T ⌈/⌉ ell) ell).oracles A impl
      (honestWith f cfg data ambient build) verifier),
      WorldSegments.queryCount .prover (protocol E n (T ⌈/⌉ ell) ell).roles result.world = 0 := by
  intro result hresult
  simp only [honestWith, protocol, prefixProtocol, Protocol.public_tree,
    Protocol.public_roles, Protocol.public_oracles, Protocol.oracleWith_tree,
    Protocol.oracleWith_roles, Protocol.oracleWith_oracles, Protocol.done_tree,
    Protocol.done_roles, Protocol.done_oracles, PFunctor.FreeM.append,
    PFunctor.FreeM.Displayed.Decoration.append, executeStrategiesPhased,
    OracleComp.withQueryLog_pure, pure_bind, bind_assoc] at hresult
  obtain ⟨alpha, _, hresult⟩ := OracleComp.mem_support_bind_peel _ _ hresult
  obtain ⟨received, _, hresult⟩ := OracleComp.mem_support_bind_peel _ _ hresult
  obtain ⟨joint, _, hresult⟩ := OracleComp.mem_support_bind_peel _ _ hresult
  obtain ⟨tail, htail, hresult⟩ := OracleComp.mem_support_bind_peel _ _ hresult
  have heq := OracleComp.eq_of_mem_support_pure _ hresult
  subst result
  have ht := nativeWith_prover_queries_zero ambient build n
    (Logup.Prover.State.start (Logup.Prover.State.prepare f alpha.1.1.1 cfg data)
      joint.1.1.1.1 joint.1.1.1.2) _
    (Access.extendImpl A (helperInterface (E := E) n (T ⌈/⌉ ell)) impl
      (Logup.Prover.State.prepare f alpha.1.1.1 cfg data).helper)
    (OutV := fun path => OutV ⟨alpha.1.1.1, ⟨PUnit.unit, ⟨joint.1.1.1, path⟩⟩⟩)
    joint.1.1.2 tail htail
  simp only [protocol, prefixProtocol, Protocol.public_tree, Protocol.public_roles,
    Protocol.public_oracles, Protocol.oracleWith_tree, Protocol.oracleWith_roles,
    Protocol.oracleWith_oracles, Protocol.done_tree, Protocol.done_roles,
    Protocol.done_oracles, PFunctor.FreeM.append, PFunctor.FreeM.Displayed.Decoration.append]
  erw [WorldSegments.queryCount_public_receiver, WorldSegments.queryCount_oracle,
    WorldSegments.queryCount_public_receiver]
  simpa using ht

set_option backward.isDefEq.respectTransparency false in
/-- Actual histogram sending and weighted reference actions preserve the empty private log. -/
theorem scalarWith_prover_queries_zero {B E : Type} [CommRing B] [Field E]
    {n M P ell : Nat} (f : B →+* E) (cfg : Logup.Lookup.Config B n M P ell)
    (data : Logup.Lookup.Data B n M P)
    (indices : Vector (Fin (P * 2 ^ n)) (M * 2 ^ n)) {ι : Type} (ambient : OracleSpec ι)
    (build : (r : Nat) → Logup.Prover.State E (M + P) ((M + P) ⌈/⌉ ell) (r + 1) →
      Sumcheck.Impl.Representation.Message E (ell + 2))
    (A : PFunctor) (impl : QueryImpl (ofPFunctor A) Id)
    {OutV : (Logup.Lookup.protocol f n M P ell).tree.BranchPath → Type}
    (verifier : Verifier.Strategy ambient (Logup.Lookup.protocol f n M P ell).tree
      (Logup.Lookup.protocol f n M P ell).roles
      (Logup.Lookup.protocol f n M P ell).oracles A OutV) :
    ∀ result ∈ support (executeStrategiesPhased ambient (Logup.Lookup.protocol f n M P ell).tree
      (Logup.Lookup.protocol f n M P ell).roles (Logup.Lookup.protocol f n M P ell).oracles A impl
      (Logup.Lookup.Honest.proverWith f cfg data indices ambient build) verifier),
      WorldSegments.queryCount .prover (Logup.Lookup.protocol f n M P ell).roles
        result.world = 0 := by
  intro result hresult
  simp only [Logup.Lookup.Honest.proverWith, Logup.Lookup.protocol, Protocol.oracleWith_tree,
    Protocol.oracleWith_roles, Protocol.oracleWith_oracles, executeStrategiesPhased,
    OracleComp.withQueryLog_pure, pure_bind] at hresult
  obtain ⟨received, _, hresult⟩ := OracleComp.mem_support_bind_peel _ _ hresult
  obtain ⟨tail, htail, hresult⟩ := OracleComp.mem_support_bind_peel _ _ hresult
  have heq := OracleComp.eq_of_mem_support_pure _ hresult
  subst result
  have ht := honestWith_prover_queries_zero f cfg.weighted
    (Logup.Lookup.weightedData data (Logup.Lookup.multiplicities (B := B) indices)) ambient build _
    (Access.extendImpl A (Logup.Lookup.multiplicityInterface f n P) impl
      (Logup.Lookup.multiplicities (B := B) indices))
    (OutV := fun path => OutV ⟨PUnit.unit, path⟩) received.1.1 tail htail
  simpa [Logup.Lookup.protocol, Protocol.oracleWith_roles,
    WorldSegments.queryCount_oracle] using ht

set_option backward.isDefEq.respectTransparency false in
/-- Actual pre-beta histogram sending and the beta response have empty private logs. -/
theorem tupleWith_prover_queries_zero {B E : Type} [CommRing B] [Field E]
    {b W n M P ell : Nat} {schema : TaggedTuple.Schema B b W}
    {layout : Logup.Lookup.Tuple.ProviderLayout b P}
    (f : B →+* E) (cfg : Logup.Lookup.Config B n M P ell)
    (prepared : Logup.Lookup.Tuple.PreparedProvider schema layout n M)
    (indices : Vector (Fin (P * 2 ^ n)) (M * 2 ^ n)) {ι : Type} (ambient : OracleSpec ι)
    (build : (r : Nat) → Logup.Prover.State E (M + P) ((M + P) ⌈/⌉ ell) (r + 1) →
      Sumcheck.Impl.Representation.Message E (ell + 2))
    (A : PFunctor) (impl : QueryImpl (ofPFunctor A) Id)
    {OutV : (Logup.Lookup.Tuple.protocol f n M P ell).tree.BranchPath → Type}
    (verifier : Verifier.Strategy ambient (Logup.Lookup.Tuple.protocol f n M P ell).tree
      (Logup.Lookup.Tuple.protocol f n M P ell).roles
      (Logup.Lookup.Tuple.protocol f n M P ell).oracles A OutV) :
    ∀ result ∈ support (executeStrategiesPhased ambient
      (Logup.Lookup.Tuple.protocol f n M P ell).tree (Logup.Lookup.Tuple.protocol f n M P ell).roles
      (Logup.Lookup.Tuple.protocol f n M P ell).oracles A impl
      (Logup.Lookup.Tuple.Honest.proverWith f cfg prepared indices ambient build) verifier),
      WorldSegments.queryCount .prover (Logup.Lookup.Tuple.protocol f n M P ell).roles
        result.world = 0 := by
  intro result hresult
  simp only [Logup.Lookup.Tuple.Honest.proverWith, Logup.Lookup.Tuple.protocol,
    Protocol.oracleWith_tree, Protocol.oracleWith_roles, Protocol.oracleWith_oracles,
    Protocol.public_tree, Protocol.public_roles, Protocol.public_oracles,
    executeStrategiesPhased, OracleComp.withQueryLog_pure, pure_bind, bind_assoc] at hresult
  obtain ⟨received, _, hresult⟩ := OracleComp.mem_support_bind_peel _ _ hresult
  obtain ⟨beta, _, hresult⟩ := OracleComp.mem_support_bind_peel _ _ hresult
  obtain ⟨tail, htail, hresult⟩ := OracleComp.mem_support_bind_peel _ _ hresult
  have heq := OracleComp.eq_of_mem_support_pure _ hresult
  subst result
  have ht := honestWith_prover_queries_zero (RingHom.id E) cfg.weighted
    (prepared.weightedData f beta.1.1.1 (Logup.Lookup.multiplicities (B := B) indices))
    ambient build _
    (Access.extendImpl A (Logup.Lookup.multiplicityInterface f n P) impl
      (Logup.Lookup.multiplicities (B := B) indices))
    (OutV := fun path => OutV ⟨PUnit.unit, ⟨beta.1.1.1, path⟩⟩) beta.1.1.2 tail htail
  simp only [Logup.Lookup.Tuple.protocol, Protocol.oracleWith_roles,
    WorldSegments.queryCount_oracle]
  erw [WorldSegments.queryCount_public_receiver]
  simpa using ht

/-- Equality of ordinary strategies transfers the ambient-log observation, not arithmetic costs. -/
theorem weighted_prover_queries_zero {B E : Type} [CommRing B] [Field E] [DecidableEq E]
    {n T ell : Nat} (f : B →+* E) (cfg : Config n T ell)
    (data : Fin 2 × Fin T → CMlPolynomialEval B n) {ι : Type} (ambient : OracleSpec ι)
    (A : PFunctor) (impl : QueryImpl (ofPFunctor A) Id)
    {OutV : (protocol E n (T ⌈/⌉ ell) ell).tree.BranchPath → Type}
    (verifier : Verifier.Strategy ambient (protocol E n (T ⌈/⌉ ell) ell).tree
      (protocol E n (T ⌈/⌉ ell) ell).roles (protocol E n (T ⌈/⌉ ell) ell).oracles A OutV) :
    ∀ result ∈ support (executeStrategiesPhased ambient (protocol E n (T ⌈/⌉ ell) ell).tree
      (protocol E n (T ⌈/⌉ ell) ell).roles (protocol E n (T ⌈/⌉ ell) ell).oracles A impl
      (Logup.Prover.Honest.prover f cfg data ambient) verifier),
      WorldSegments.queryCount .prover (protocol E n (T ⌈/⌉ ell) ell).roles result.world = 0 := by
  simpa only [Logup.Prover.Honest.prover_eq_honestWith] using
    honestWith_prover_queries_zero f cfg data ambient
      (pureBuilder cfg.groups cfg.length_group_le) A impl verifier

/-- The actual histogram sender and measured scalar suffix make no private ambient query. -/
theorem scalar_prover_queries_zero {B E : Type} [CommRing B] [Field E] [DecidableEq E]
    {n M P ell : Nat} (f : B →+* E) (cfg : Logup.Lookup.Config B n M P ell)
    (data : Logup.Lookup.Data B n M P)
    (indices : Vector (Fin (P * 2 ^ n)) (M * 2 ^ n)) {ι : Type} (ambient : OracleSpec ι)
    (A : PFunctor) (impl : QueryImpl (ofPFunctor A) Id)
    {OutV : (Logup.Lookup.protocol f n M P ell).tree.BranchPath → Type}
    (verifier : Verifier.Strategy ambient (Logup.Lookup.protocol f n M P ell).tree
      (Logup.Lookup.protocol f n M P ell).roles
      (Logup.Lookup.protocol f n M P ell).oracles A OutV) :
    ∀ result ∈ support (executeStrategiesPhased ambient (Logup.Lookup.protocol f n M P ell).tree
      (Logup.Lookup.protocol f n M P ell).roles (Logup.Lookup.protocol f n M P ell).oracles A impl
      (Logup.Lookup.Honest.prover f cfg data indices ambient) verifier),
      WorldSegments.queryCount .prover (Logup.Lookup.protocol f n M P ell).roles
        result.world = 0 := by
  simpa only [Logup.Lookup.Honest.prover_eq_proverWith] using
    scalarWith_prover_queries_zero f cfg data indices ambient
      (pureBuilder cfg.weighted.groups cfg.weighted.length_group_le) A impl verifier

/-- The actual eager tuple cache and measured suffix preserve the same private ambient log. -/
theorem tuple_prover_queries_zero {B E : Type} [CommRing B] [Field E] [DecidableEq E]
    {b W n M P ell : Nat} {schema : TaggedTuple.Schema B b W}
    {layout : Logup.Lookup.Tuple.ProviderLayout b P}
    (f : B →+* E) (cfg : Logup.Lookup.Config B n M P ell)
    (prepared : Logup.Lookup.Tuple.PreparedProvider schema layout n M)
    (indices : Vector (Fin (P * 2 ^ n)) (M * 2 ^ n)) {ι : Type} (ambient : OracleSpec ι)
    (A : PFunctor) (impl : QueryImpl (ofPFunctor A) Id)
    {OutV : (Logup.Lookup.Tuple.protocol f n M P ell).tree.BranchPath → Type}
    (verifier : Verifier.Strategy ambient (Logup.Lookup.Tuple.protocol f n M P ell).tree
      (Logup.Lookup.Tuple.protocol f n M P ell).roles
      (Logup.Lookup.Tuple.protocol f n M P ell).oracles A OutV) :
    ∀ result ∈ support (executeStrategiesPhased ambient
      (Logup.Lookup.Tuple.protocol f n M P ell).tree (Logup.Lookup.Tuple.protocol f n M P ell).roles
      (Logup.Lookup.Tuple.protocol f n M P ell).oracles A impl
      (Logup.Lookup.Tuple.Honest.prover f cfg prepared indices ambient) verifier),
      WorldSegments.queryCount .prover (Logup.Lookup.Tuple.protocol f n M P ell).roles
        result.world = 0 := by
  simpa only [Logup.Lookup.Tuple.Honest.prover_eq_proverWith] using
    tupleWith_prover_queries_zero f cfg prepared indices ambient
      (pureBuilder cfg.weighted.groups cfg.weighted.length_group_le) A impl verifier

end Logup.Interaction.HonestSamplingResources

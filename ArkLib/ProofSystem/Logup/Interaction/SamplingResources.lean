/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/
module
public import ArkLib.ProofSystem.Logup.Interaction.Resources
public import ArkLib.ProofSystem.Sumcheck.Interaction.SamplingResources
public import ArkLib.Data.Probability.Uniform
public import ArkLib.ProofSystem.Logup.Interaction.HonestSamplingResources
import all ArkLib.Interaction.Oracle.PhasedExecution
/-!
# Actual LogUp verifier phases and honest primitive sampling logs

Every supported complete phased run retains its real sender and receiver effects. The weighted
prefix contributes the alpha and joint draw programs, the scalar multiplicity sender contributes
no verifier query, and the tuple prefix adds beta. The native term uses the actual path's number
of completed draws; final rejection and public round abort remain distinct. A private ambient
abort may prevent a later stage entirely. No completed-result equation asserts losslessness or
bounds arbitrary private queries, including private queries to the verifier's own sampler index.

Selected uniform programs draw the coordinate vectors in their existing order. An explicit
supported primitive-log length c for one E sample gives c*(1+n+K+s) verifier queries, or
c*(2+n+K+s) for tuples. KoalaBear.Field supplies c=1 and its pinned Ext6 sampler supplies c=6;
these count uniform-oracle invocations, not internal RNG work. No generic sampler is assumed to
have either constant. Exact program identities connect the existing phased observation to the
actual Bool endpoints and their complete chronological ambient logs.

For the selected honest defaults, the proved private-empty observation and existing phase
partition convert the verifier count into the whole named uniform endpoint's primitive log
length. Actual output and a supported concrete path survive that comparison. This transfers
observable strategy behavior only, not arithmetic, preprocessing, backend, storage or machine
costs. No protocol, sampler, runner or runtime body is changed here.
-/

@[expose] public section
open Interaction Interaction.Oracle OracleComp OracleSpec CompPoly
open Logup.Interaction
namespace Logup.Interaction.SamplingResources
private theorem joint_uniform_log_length {E : Type} [SampleableType E]
    (n K c : Nat)
    (hsample : ∀ result ∈ support ($ᵗ E).withQueryLog, result.2.length = c)
    (result : ((Fin n → E) × (Fin K → E)) × QueryLog unifSpec)
    (member : result ∈ support ($ᵗ ((Fin n → E) × (Fin K → E))).withQueryLog) :
    result.2.length = (n + K) * c := by
  rw [SampleableType.uniformSample_pi_fin_prod_eq_ofFnM] at member
  simp only [withQueryLog_bind, withQueryLog_pure, map_bind, map_pure] at member
  obtain ⟨z, hz, member⟩ := OracleComp.mem_support_bind_peel _ _ member
  obtain ⟨lambda, hlambda, member⟩ := OracleComp.mem_support_bind_peel _ _ member
  have heq := OracleComp.eq_of_mem_support_pure _ member
  subst result
  simp only [Prod.map, id_eq, List.length_append, List.length_nil, Nat.add_zero]
  rw [withQueryLog_ofFnM_const_length ($ᵗ E) c n hsample z hz,
    withQueryLog_ofFnM_const_length ($ᵗ E) c K hsample lambda hlambda, Nat.add_mul]

set_option backward.isDefEq.respectTransparency false in
private theorem phased_bool_world_eq {ι : Type} (ambient : OracleSpec ι)
    (tree : Oracle.TypeTree) (roles : tree.RoleDecoration) (oracles : tree.OracleDecoration)
    (A : PFunctor) (impl : QueryImpl (ofPFunctor A) Id)
    {OutP : tree.ExecutionPath → Type} (prover : Prover.Strategy ambient tree roles OutP)
    (verifier : Verifier.Strategy ambient tree roles oracles A (fun _ => Bool)) :
    (fun result : PhasedResult ambient tree roles oracles A OutP (fun _ => Bool) =>
      (result.verifierOut, result.world.flatten)) <$>
      executeStrategiesPhased ambient tree roles oracles A impl prover verifier =
      ((fun result : (path : tree.ExecutionPath) × OutP path × Bool => result.2.2) <$>
        executeStrategies ambient tree roles oracles A impl prover verifier).withQueryLog := by
  have paired := executeStrategiesPhased_logView ambient tree roles oracles A impl prover verifier
  have hp := congrArg (fun program =>
    (fun observed : LoggedObservation tree oracles A OutP (fun _ => Bool) × QueryLog ambient =>
      (observed.1.2.2.1, observed.2)) <$> program) paired
  simp only [Functor.map_map, PhasedResult.logView, PhasedResult.observe,
    LoggedResult.observe] at hp
  have erase := executeStrategiesLogged_erase ambient tree roles oracles A impl prover verifier
  have hb := congrArg (fun program =>
    (fun result : (path : tree.ExecutionPath) × OutP path × Bool => result.2.2) <$> program) erase
  simp only [Functor.map_map, LoggedResult.erase] at hb
  rw [← hb, OracleComp.withQueryLog_map]
  exact hp

variable {B E : Type} [CommRing B] [CommRing E] [DecidableEq E]
set_option backward.isDefEq.respectTransparency false in
/-- The actual weighted prefix and native suffix give an exact verifier-party query count. -/
theorem phased_verifier_queries (f : B →+* E) (n T ell : Nat) (cfg : Config n T ell)
    {ι : Type} (ambient : OracleSpec ι)
    (alphaDraw : OracleComp ambient E)
    (jointDraw : OracleComp ambient ((Fin n → E) × (Fin (T ⌈/⌉ ell) → E)))
    (roundDraw : OracleComp ambient E) (ca cj cr : Nat)
    (ha : ∀ a ∈ support alphaDraw.withQueryLog, a.2.length = ca)
    (hj : ∀ j ∈ support jointDraw.withQueryLog, j.2.length = cj)
    (hr : ∀ r ∈ support roundDraw.withQueryLog, r.2.length = cr)
    (A : PFunctor) (inputView : VirtualOracle (ofPFunctor A) (inputFamily f n T))
    (impl : QueryImpl (ofPFunctor A) Id)
    {OutP : (protocol E n (T ⌈/⌉ ell) ell).tree.ExecutionPath → Type}
    (wholeProver : Prover.Strategy ambient (protocol E n (T ⌈/⌉ ell) ell).tree
      (protocol E n (T ⌈/⌉ ell) ell).roles OutP) :
    ∀ result ∈ support (executeStrategiesPhased ambient (protocol E n (T ⌈/⌉ ell) ell).tree
      (protocol E n (T ⌈/⌉ ell) ell).roles (protocol E n (T ⌈/⌉ ell) ell).oracles A impl
      wholeProver (verifier f n T ell cfg ambient alphaDraw jointDraw roundDraw A inputView)),
      WorldSegments.queryCount .verifier (protocol E n (T ⌈/⌉ ell) ell).roles result.world =
        ca + cj + cr * (Sumcheck.Interaction.Computable.Resources.pathUsage (ell + 2) n
          result.path.2.2.2).roundSamples := by
  intro result hresult
  rw [Resources.verifier_eq_prefix] at hresult
  simp only [protocol, prefixProtocol, Protocol.public_tree, Protocol.public_roles,
    Protocol.public_oracles, Protocol.oracleWith_tree, Protocol.oracleWith_roles,
    Protocol.oracleWith_oracles, Protocol.done_tree, Protocol.done_roles,
    Protocol.done_oracles, PFunctor.FreeM.append, PFunctor.FreeM.Displayed.Decoration.append,
    executeStrategiesPhased, simulateQ_bind, simulateQ_pure, WriterT.run_bind',
    WriterT.run_pure', Verifier.loggedLiftAccessImpl_liftComp, bind_map_left, pure_bind,
    map_pure, Prod.map, id_eq, List.nil_append,
    OracleComp.withQueryLog_pure, OracleComp.withQueryLog_bind, bind_assoc] at hresult
  obtain ⟨alpha, halpha, hresult⟩ := OracleComp.mem_support_bind_peel _ _ hresult
  obtain ⟨afterAlpha, _, hresult⟩ := OracleComp.mem_support_bind_peel _ _ hresult
  obtain ⟨sent, _, hresult⟩ := OracleComp.mem_support_bind_peel _ _ hresult
  obtain ⟨joint, hjoint, hresult⟩ := OracleComp.mem_support_bind_peel _ _ hresult
  obtain ⟨suffix, _, hresult⟩ := OracleComp.mem_support_bind_peel _ _ hresult
  obtain ⟨tail, htail, hresult⟩ := OracleComp.mem_support_bind_peel _ _ hresult
  have heq := OracleComp.eq_of_mem_support_pure _ hresult
  subst result
  have ht := Sumcheck.Interaction.Computable.SamplingResources.phased_verifier_queries
    n (ell + 2) ambient roundDraw cr hr n 0 (Nat.zero_add n)
    (Access.extend A (helperInterface (E := E) n (T ⌈/⌉ ell)))
    (qView f n T (T ⌈/⌉ ell) cfg.groups alpha.1 joint.1.1 joint.1.2 ell A inputView)
    (zeroStatement E n)
    (Access.extendImpl A (helperInterface (E := E) n (T ⌈/⌉ ell)) impl sent.1.1)
    (OutP := fun path => OutP ⟨alpha.1, ⟨sent.1.1, ⟨joint.1, path⟩⟩⟩)
    suffix.1 tail htail
  simp only [protocol, prefixProtocol, Protocol.public_tree, Protocol.public_roles,
    Protocol.public_oracles, Protocol.oracleWith_tree, Protocol.oracleWith_roles,
    Protocol.oracleWith_oracles, Protocol.done_tree, Protocol.done_roles,
    Protocol.done_oracles, PFunctor.FreeM.append, PFunctor.FreeM.Displayed.Decoration.append]
  erw [WorldSegments.queryCount_public_receiver, WorldSegments.queryCount_oracle,
    WorldSegments.queryCount_public_receiver]
  simpa [ha alpha halpha, hj joint hjoint, Nat.add_assoc] using congrArg (fun c => ca + cj + c) ht
set_option backward.isDefEq.respectTransparency false in
/-- The retained multiplicity sender adds no verifier query to the weighted phase count. -/
theorem scalar_phased_verifier_queries (f : B →+* E) (n M P ell : Nat)
    (cfg : Logup.Lookup.Config B n M P ell) {ι : Type} (ambient : OracleSpec ι)
    (alphaDraw : OracleComp ambient E)
    (jointDraw : OracleComp ambient ((Fin n → E) × (Fin ((M + P) ⌈/⌉ ell) → E)))
    (roundDraw : OracleComp ambient E) (ca cj cr : Nat)
    (ha : ∀ a ∈ support alphaDraw.withQueryLog, a.2.length = ca)
    (hj : ∀ j ∈ support jointDraw.withQueryLog, j.2.length = cj)
    (hr : ∀ r ∈ support roundDraw.withQueryLog, r.2.length = cr)
    (A : PFunctor) (view : VirtualOracle (ofPFunctor A) (Logup.Lookup.valuesFamily f n M P))
    (impl : QueryImpl (ofPFunctor A) Id)
    {OutP : (Logup.Lookup.protocol f n M P ell).tree.ExecutionPath → Type}
    (wholeProver : Prover.Strategy ambient (Logup.Lookup.protocol f n M P ell).tree
      (Logup.Lookup.protocol f n M P ell).roles OutP) :
    ∀ result ∈ support (executeStrategiesPhased ambient (Logup.Lookup.protocol f n M P ell).tree
      (Logup.Lookup.protocol f n M P ell).roles (Logup.Lookup.protocol f n M P ell).oracles A impl
      wholeProver
      (Logup.Lookup.verifier f n M P ell cfg ambient alphaDraw jointDraw roundDraw A view)),
      WorldSegments.queryCount .verifier (Logup.Lookup.protocol f n M P ell).roles result.world =
        ca + cj + cr * (Sumcheck.Interaction.Computable.Resources.pathUsage (ell + 2) n
          result.path.2.2.2.2).roundSamples := by
  intro result hresult
  simp only [Logup.Lookup.verifier, Logup.Lookup.protocol, Protocol.oracleWith_tree,
    Protocol.oracleWith_roles, Protocol.oracleWith_oracles, executeStrategiesPhased,
    simulateQ_pure, WriterT.run_pure', OracleComp.withQueryLog_pure, pure_bind] at hresult
  obtain ⟨sent, _, hresult⟩ := OracleComp.mem_support_bind_peel _ _ hresult
  obtain ⟨tail, htail, hresult⟩ := OracleComp.mem_support_bind_peel _ _ hresult
  have heq := OracleComp.eq_of_mem_support_pure _ hresult
  subst result
  have ht := phased_verifier_queries f n (M + P) ell cfg.weighted ambient
    alphaDraw jointDraw roundDraw ca cj cr ha hj hr
    (Access.extend A (Logup.Lookup.multiplicityInterface f n P))
    (Logup.Lookup.weightedView f n M P A view)
    (Access.extendImpl A (Logup.Lookup.multiplicityInterface f n P) impl sent.1.1)
    (OutP := fun path => OutP ⟨sent.1.1, path⟩) sent.1.2 tail htail
  simpa [Logup.Lookup.protocol, Protocol.oracleWith_roles,
    WorldSegments.queryCount_oracle] using ht

set_option backward.isDefEq.respectTransparency false in
/-- The actual tuple beta stage adds its supported draw length before the weighted suffix. -/
theorem tuple_phased_verifier_queries (f : B →+* E) (n M P W ell : Nat)
    (cfg : Logup.Lookup.Config B n M P ell) {ι : Type} (ambient : OracleSpec ι)
    (betaDraw alphaDraw : OracleComp ambient E)
    (jointDraw : OracleComp ambient ((Fin n → E) × (Fin ((M + P) ⌈/⌉ ell) → E)))
    (roundDraw : OracleComp ambient E) (cb ca cj cr : Nat)
    (hb : ∀ b ∈ support betaDraw.withQueryLog, b.2.length = cb)
    (ha : ∀ a ∈ support alphaDraw.withQueryLog, a.2.length = ca)
    (hj : ∀ j ∈ support jointDraw.withQueryLog, j.2.length = cj)
    (hr : ∀ r ∈ support roundDraw.withQueryLog, r.2.length = cr)
    (A : PFunctor)
    (view : VirtualOracle (ofPFunctor A) (Logup.Lookup.Tuple.coefficientFamily f n M P W))
    (impl : QueryImpl (ofPFunctor A) Id)
    {OutP : (Logup.Lookup.Tuple.protocol f n M P ell).tree.ExecutionPath → Type}
    (wholeProver : Prover.Strategy ambient (Logup.Lookup.Tuple.protocol f n M P ell).tree
      (Logup.Lookup.Tuple.protocol f n M P ell).roles OutP) :
    ∀ result ∈ support (executeStrategiesPhased ambient
      (Logup.Lookup.Tuple.protocol f n M P ell).tree
      (Logup.Lookup.Tuple.protocol f n M P ell).roles
      (Logup.Lookup.Tuple.protocol f n M P ell).oracles A impl wholeProver
      (Logup.Lookup.Tuple.verifier f n M P W ell cfg ambient betaDraw alphaDraw jointDraw
        roundDraw A view)),
      WorldSegments.queryCount .verifier (Logup.Lookup.Tuple.protocol f n M P ell).roles
        result.world = cb + ca + cj + cr *
          (Sumcheck.Interaction.Computable.Resources.pathUsage (ell + 2) n
            result.path.2.2.2.2.2).roundSamples := by
  intro result hresult
  simp only [Logup.Lookup.Tuple.verifier, Logup.Lookup.Tuple.protocol,
    Protocol.oracleWith_tree, Protocol.oracleWith_roles, Protocol.oracleWith_oracles,
    Protocol.public_tree, Protocol.public_roles, Protocol.public_oracles,
    executeStrategiesPhased, simulateQ_bind, simulateQ_pure, WriterT.run_bind',
    WriterT.run_pure', Verifier.loggedLiftAccessImpl_liftComp, bind_map_left, pure_bind,
    map_pure, Prod.map, id_eq,
    OracleComp.withQueryLog_pure, OracleComp.withQueryLog_bind, bind_assoc] at hresult
  obtain ⟨sent, _, hresult⟩ := OracleComp.mem_support_bind_peel _ _ hresult
  obtain ⟨beta, hbeta, hresult⟩ := OracleComp.mem_support_bind_peel _ _ hresult
  obtain ⟨suffix, _, hresult⟩ := OracleComp.mem_support_bind_peel _ _ hresult
  obtain ⟨tail, htail, hresult⟩ := OracleComp.mem_support_bind_peel _ _ hresult
  have heq := OracleComp.eq_of_mem_support_pure _ hresult
  subst result
  have ht := phased_verifier_queries (RingHom.id E) n (M + P) ell cfg.weighted ambient
    alphaDraw jointDraw roundDraw ca cj cr ha hj hr
    (Access.extend A (Logup.Lookup.multiplicityInterface f n P))
    (Logup.Lookup.Tuple.weightedView f n M P W beta.1 A view)
    (Access.extendImpl A (Logup.Lookup.multiplicityInterface f n P) impl sent.1.1)
    (OutP := fun path => OutP ⟨sent.1.1, ⟨beta.1, path⟩⟩) suffix.1 tail htail
  simp only [Logup.Lookup.Tuple.protocol, Protocol.oracleWith_roles,
    WorldSegments.queryCount_oracle]
  erw [WorldSegments.queryCount_public_receiver]
  simpa [hb beta hbeta, Nat.add_assoc] using congrArg (fun c => cb + c) ht
/-- The selected weighted uniform programs use 1+n+K+s E sample blocks of primitive length c. -/
theorem uniform_phased_verifier_queries [SampleableType E]
    (f : B →+* E) (n T ell : Nat) (cfg : Config n T ell) (c : Nat)
    (hsample : ∀ result ∈ support ($ᵗ E).withQueryLog, result.2.length = c)
    (A : PFunctor) (view : VirtualOracle (ofPFunctor A) (inputFamily f n T))
    (impl : QueryImpl (ofPFunctor A) Id)
    {OutP : (protocol E n (T ⌈/⌉ ell) ell).tree.ExecutionPath → Type}
    (wholeProver : Prover.Strategy unifSpec (protocol E n (T ⌈/⌉ ell) ell).tree
      (protocol E n (T ⌈/⌉ ell) ell).roles OutP) :
    ∀ result ∈ support (executeStrategiesPhased unifSpec (protocol E n (T ⌈/⌉ ell) ell).tree
      (protocol E n (T ⌈/⌉ ell) ell).roles (protocol E n (T ⌈/⌉ ell) ell).oracles A impl
      wholeProver (verifier f n T ell cfg unifSpec ($ᵗ E)
        ($ᵗ ((Fin n → E) × (Fin (T ⌈/⌉ ell) → E))) ($ᵗ E) A view)),
      WorldSegments.queryCount .verifier (protocol E n (T ⌈/⌉ ell) ell).roles result.world =
        c * (1 + n + (T ⌈/⌉ ell) +
          (Sumcheck.Interaction.Computable.Resources.pathUsage (ell + 2) n
            result.path.2.2.2).roundSamples) := by
  intro result hresult
  have h := phased_verifier_queries f n T ell cfg unifSpec ($ᵗ E)
    ($ᵗ ((Fin n → E) × (Fin (T ⌈/⌉ ell) → E))) ($ᵗ E) c ((n + (T ⌈/⌉ ell)) * c) c
    hsample (joint_uniform_log_length n (T ⌈/⌉ ell) c hsample) hsample
    A view impl wholeProver result hresult
  calc
    _ = c + (n + (T ⌈/⌉ ell)) * c + c *
        (Sumcheck.Interaction.Computable.Resources.pathUsage (ell + 2) n
          result.path.2.2.2).roundSamples := h
    _ = _ := by ring

/-- The actual scalar uniform programs use 1+n+K+s E sample blocks of primitive length c. -/
theorem scalar_uniform_phased_verifier_queries [SampleableType E]
    (f : B →+* E) (n M P ell : Nat) (cfg : Logup.Lookup.Config B n M P ell) (c : Nat)
    (hsample : ∀ result ∈ support ($ᵗ E).withQueryLog, result.2.length = c)
    (A : PFunctor) (view : VirtualOracle (ofPFunctor A) (Logup.Lookup.valuesFamily f n M P))
    (impl : QueryImpl (ofPFunctor A) Id)
    {OutP : (Logup.Lookup.protocol f n M P ell).tree.ExecutionPath → Type}
    (wholeProver : Prover.Strategy unifSpec (Logup.Lookup.protocol f n M P ell).tree
      (Logup.Lookup.protocol f n M P ell).roles OutP) :
    ∀ result ∈ support (executeStrategiesPhased unifSpec (Logup.Lookup.protocol f n M P ell).tree
      (Logup.Lookup.protocol f n M P ell).roles (Logup.Lookup.protocol f n M P ell).oracles A impl
      wholeProver (Logup.Lookup.verifier f n M P ell cfg unifSpec ($ᵗ E)
        ($ᵗ ((Fin n → E) × (Fin ((M + P) ⌈/⌉ ell) → E))) ($ᵗ E) A view)),
      WorldSegments.queryCount .verifier (Logup.Lookup.protocol f n M P ell).roles result.world =
        c * (1 + n + ((M + P) ⌈/⌉ ell) +
          (Sumcheck.Interaction.Computable.Resources.pathUsage (ell + 2) n
            result.path.2.2.2.2).roundSamples) := by
  intro result hresult
  have h := scalar_phased_verifier_queries f n M P ell cfg unifSpec ($ᵗ E)
    ($ᵗ ((Fin n → E) × (Fin ((M + P) ⌈/⌉ ell) → E))) ($ᵗ E)
    c ((n + ((M + P) ⌈/⌉ ell)) * c) c
    hsample (joint_uniform_log_length n ((M + P) ⌈/⌉ ell) c hsample) hsample
    A view impl wholeProver result hresult
  calc
    _ = c + (n + ((M + P) ⌈/⌉ ell)) * c + c *
        (Sumcheck.Interaction.Computable.Resources.pathUsage (ell + 2) n
          result.path.2.2.2.2).roundSamples := h
    _ = _ := by ring

/-- The actual tuple uniform programs use 2+n+K+s E sample blocks of primitive length c. -/
theorem tuple_uniform_phased_verifier_queries [SampleableType E]
    (f : B →+* E) (n M P W ell : Nat) (cfg : Logup.Lookup.Config B n M P ell) (c : Nat)
    (hsample : ∀ result ∈ support ($ᵗ E).withQueryLog, result.2.length = c)
    (A : PFunctor)
    (view : VirtualOracle (ofPFunctor A) (Logup.Lookup.Tuple.coefficientFamily f n M P W))
    (impl : QueryImpl (ofPFunctor A) Id)
    {OutP : (Logup.Lookup.Tuple.protocol f n M P ell).tree.ExecutionPath → Type}
    (wholeProver : Prover.Strategy unifSpec (Logup.Lookup.Tuple.protocol f n M P ell).tree
      (Logup.Lookup.Tuple.protocol f n M P ell).roles OutP) :
    ∀ result ∈ support (executeStrategiesPhased unifSpec
      (Logup.Lookup.Tuple.protocol f n M P ell).tree
      (Logup.Lookup.Tuple.protocol f n M P ell).roles
      (Logup.Lookup.Tuple.protocol f n M P ell).oracles A impl wholeProver
      (Logup.Lookup.Tuple.verifier f n M P W ell cfg unifSpec ($ᵗ E) ($ᵗ E)
        ($ᵗ ((Fin n → E) × (Fin ((M + P) ⌈/⌉ ell) → E))) ($ᵗ E) A view)),
      WorldSegments.queryCount .verifier (Logup.Lookup.Tuple.protocol f n M P ell).roles
        result.world = c * (2 + n + ((M + P) ⌈/⌉ ell) +
          (Sumcheck.Interaction.Computable.Resources.pathUsage (ell + 2) n
            result.path.2.2.2.2.2).roundSamples) := by
  intro result hresult
  have h := tuple_phased_verifier_queries f n M P W ell cfg unifSpec ($ᵗ E) ($ᵗ E)
    ($ᵗ ((Fin n → E) × (Fin ((M + P) ⌈/⌉ ell) → E))) ($ᵗ E)
    c c ((n + ((M + P) ⌈/⌉ ell)) * c) c
    hsample hsample (joint_uniform_log_length n ((M + P) ⌈/⌉ ell) c hsample) hsample
    A view impl wholeProver result hresult
  calc
    _ = c + c + (n + ((M + P) ⌈/⌉ ell)) * c + c *
        (Sumcheck.Interaction.Computable.Resources.pathUsage (ell + 2) n
          result.path.2.2.2.2.2).roundSamples := h
    _ = _ := by ring
/-- The actual weighted Bool endpoint has exactly the phased execution's complete ambient log. -/
theorem execute_world_eq (f : B →+* E) (n T ell : Nat) (cfg : Config n T ell)
    {ι : Type} (ambient : OracleSpec ι) (alphaDraw : OracleComp ambient E)
    (jointDraw : OracleComp ambient ((Fin n → E) × (Fin (T ⌈/⌉ ell) → E)))
    (roundDraw : OracleComp ambient E) (A : PFunctor)
    (view : VirtualOracle (ofPFunctor A) (inputFamily f n T))
    (impl : QueryImpl (ofPFunctor A) Id)
    {OutP : (protocol E n (T ⌈/⌉ ell) ell).tree.ExecutionPath → Type}
    (prover : Prover.Strategy ambient (protocol E n (T ⌈/⌉ ell) ell).tree
      (protocol E n (T ⌈/⌉ ell) ell).roles OutP) :
    (fun result : PhasedResult ambient (protocol E n (T ⌈/⌉ ell) ell).tree
        (protocol E n (T ⌈/⌉ ell) ell).roles (protocol E n (T ⌈/⌉ ell) ell).oracles A OutP
        (fun _ => Bool) => (result.verifierOut, result.world.flatten)) <$>
      executeStrategiesPhased ambient (protocol E n (T ⌈/⌉ ell) ell).tree
        (protocol E n (T ⌈/⌉ ell) ell).roles (protocol E n (T ⌈/⌉ ell) ell).oracles A impl
        prover (verifier f n T ell cfg ambient alphaDraw jointDraw roundDraw A view) =
      (execute f n T ell cfg ambient alphaDraw jointDraw roundDraw A view impl
        prover).withQueryLog := by
  simpa only [execute, bind_pure_comp] using phased_bool_world_eq ambient
    (protocol E n (T ⌈/⌉ ell) ell).tree (protocol E n (T ⌈/⌉ ell) ell).roles
    (protocol E n (T ⌈/⌉ ell) ell).oracles A impl prover
    (verifier f n T ell cfg ambient alphaDraw jointDraw roundDraw A view)

/-- The actual scalar Bool endpoint has exactly the phased execution's complete ambient log. -/
theorem scalar_execute_world_eq (f : B →+* E) (n M P ell : Nat)
    (cfg : Logup.Lookup.Config B n M P ell) {ι : Type} (ambient : OracleSpec ι)
    (alphaDraw : OracleComp ambient E)
    (jointDraw : OracleComp ambient ((Fin n → E) × (Fin ((M + P) ⌈/⌉ ell) → E)))
    (roundDraw : OracleComp ambient E) (A : PFunctor)
    (view : VirtualOracle (ofPFunctor A) (Logup.Lookup.valuesFamily f n M P))
    (impl : QueryImpl (ofPFunctor A) Id)
    {OutP : (Logup.Lookup.protocol f n M P ell).tree.ExecutionPath → Type}
    (prover : Prover.Strategy ambient (Logup.Lookup.protocol f n M P ell).tree
      (Logup.Lookup.protocol f n M P ell).roles OutP) :
    (fun result : PhasedResult ambient (Logup.Lookup.protocol f n M P ell).tree
        (Logup.Lookup.protocol f n M P ell).roles (Logup.Lookup.protocol f n M P ell).oracles A
        OutP (fun _ => Bool) => (result.verifierOut, result.world.flatten)) <$>
      executeStrategiesPhased ambient (Logup.Lookup.protocol f n M P ell).tree
        (Logup.Lookup.protocol f n M P ell).roles (Logup.Lookup.protocol f n M P ell).oracles A impl
        prover (Logup.Lookup.verifier f n M P ell cfg ambient alphaDraw jointDraw roundDraw
          A view) =
      (Logup.Lookup.execute f n M P ell cfg ambient alphaDraw jointDraw roundDraw A view impl
        prover).withQueryLog := by
  simpa only [Logup.Lookup.execute, bind_pure_comp] using phased_bool_world_eq ambient
    (Logup.Lookup.protocol f n M P ell).tree (Logup.Lookup.protocol f n M P ell).roles
    (Logup.Lookup.protocol f n M P ell).oracles A impl prover
    (Logup.Lookup.verifier f n M P ell cfg ambient alphaDraw jointDraw roundDraw A view)

/-- The actual tuple Bool endpoint has exactly the phased execution's complete ambient log. -/
theorem tuple_execute_world_eq (f : B →+* E) (n M P W ell : Nat)
    (cfg : Logup.Lookup.Config B n M P ell) {ι : Type} (ambient : OracleSpec ι)
    (betaDraw alphaDraw : OracleComp ambient E)
    (jointDraw : OracleComp ambient ((Fin n → E) × (Fin ((M + P) ⌈/⌉ ell) → E)))
    (roundDraw : OracleComp ambient E) (A : PFunctor)
    (view : VirtualOracle (ofPFunctor A) (Logup.Lookup.Tuple.coefficientFamily f n M P W))
    (impl : QueryImpl (ofPFunctor A) Id)
    {OutP : (Logup.Lookup.Tuple.protocol f n M P ell).tree.ExecutionPath → Type}
    (prover : Prover.Strategy ambient (Logup.Lookup.Tuple.protocol f n M P ell).tree
      (Logup.Lookup.Tuple.protocol f n M P ell).roles OutP) :
    (fun result : PhasedResult ambient (Logup.Lookup.Tuple.protocol f n M P ell).tree
        (Logup.Lookup.Tuple.protocol f n M P ell).roles
        (Logup.Lookup.Tuple.protocol f n M P ell).oracles
        A OutP (fun _ => Bool) => (result.verifierOut, result.world.flatten)) <$>
      executeStrategiesPhased ambient (Logup.Lookup.Tuple.protocol f n M P ell).tree
        (Logup.Lookup.Tuple.protocol f n M P ell).roles
        (Logup.Lookup.Tuple.protocol f n M P ell).oracles
        A impl prover (Logup.Lookup.Tuple.verifier f n M P W ell cfg ambient betaDraw alphaDraw
          jointDraw roundDraw A view) =
      (Logup.Lookup.Tuple.execute f n M P W ell cfg ambient betaDraw alphaDraw jointDraw roundDraw
        A view impl prover).withQueryLog := by
  simpa only [Logup.Lookup.Tuple.execute, bind_pure_comp] using phased_bool_world_eq ambient
    (Logup.Lookup.Tuple.protocol f n M P ell).tree (Logup.Lookup.Tuple.protocol f n M P ell).roles
    (Logup.Lookup.Tuple.protocol f n M P ell).oracles A impl prover
    (Logup.Lookup.Tuple.verifier f n M P W ell cfg ambient betaDraw alphaDraw jointDraw
      roundDraw A view)

/-- Every supported named weighted default output has the stated primitive log length
at a supported actual phase path; the actual Bool and ordered log are retained. -/
theorem uniformExecute_default_queries {F : Type} [Field F] [DecidableEq F] [SampleableType F]
    (f : B →+* F) (n T ell : Nat) (cfg : Config n T ell)
    (data : Fin 2 × Fin T → CMlPolynomialEval B n) (c : Nat)
    (hsample : ∀ result ∈ support ($ᵗ F).withQueryLog, result.2.length = c)
    (A : PFunctor) (view : VirtualOracle (ofPFunctor A) (inputFamily f n T))
    (impl : QueryImpl (ofPFunctor A) Id) :
    ∀ actual ∈ support (uniformExecute f n T ell cfg A view impl
      (Logup.Prover.Honest.prover f cfg data unifSpec)).withQueryLog,
      ∃ result ∈ support (executeStrategiesPhased unifSpec (protocol F n (T ⌈/⌉ ell) ell).tree
        (protocol F n (T ⌈/⌉ ell) ell).roles (protocol F n (T ⌈/⌉ ell) ell).oracles A impl
        (Logup.Prover.Honest.prover f cfg data unifSpec)
        (verifier f n T ell cfg unifSpec ($ᵗ F)
          ($ᵗ ((Fin n → F) × (Fin (T ⌈/⌉ ell) → F))) ($ᵗ F) A view)),
        actual = (result.verifierOut, result.world.flatten) ∧
          actual.2.length = c * (1 + n + (T ⌈/⌉ ell) +
            (Sumcheck.Interaction.Computable.Resources.pathUsage (ell + 2) n
              result.path.2.2.2).roundSamples) := by
  intro actual hactual
  rw [uniformExecute, ← execute_world_eq, support_map] at hactual
  obtain ⟨result, hresult, rfl⟩ := hactual
  refine ⟨result, hresult, rfl, ?_⟩
  have hv := uniform_phased_verifier_queries f n T ell cfg c hsample A view impl
    (Logup.Prover.Honest.prover f cfg data unifSpec) result hresult
  have hp := HonestSamplingResources.weighted_prover_queries_zero f cfg data unifSpec A impl
    (verifier f n T ell cfg unifSpec ($ᵗ F)
      ($ᵗ ((Fin n → F) × (Fin (T ⌈/⌉ ell) → F))) ($ᵗ F) A view) result hresult
  have partition := WorldSegments.queryCount_partition (protocol F n (T ⌈/⌉ ell) ell).roles
    result.world
  change result.world.flatten.length = _
  omega

/-- Every named scalar default output retains an actual supported phase path,
with the stated primitive log length and no caller-supplied private-query assumption. -/
theorem scalar_uniformExecute_default_queries
    {F : Type} [Field F] [DecidableEq F] [SampleableType F]
    (f : B →+* F) (n M P ell : Nat) (cfg : Logup.Lookup.Config B n M P ell)
    (data : Logup.Lookup.Data B n M P)
    (indices : Vector (Fin (P * 2 ^ n)) (M * 2 ^ n)) (c : Nat)
    (hsample : ∀ result ∈ support ($ᵗ F).withQueryLog, result.2.length = c)
    (A : PFunctor) (view : VirtualOracle (ofPFunctor A) (Logup.Lookup.valuesFamily f n M P))
    (impl : QueryImpl (ofPFunctor A) Id) :
    ∀ actual ∈ support (Logup.Lookup.uniformExecute f n M P ell cfg A view impl
      (Logup.Lookup.Honest.prover f cfg data indices unifSpec)).withQueryLog,
      ∃ result ∈ support (executeStrategiesPhased unifSpec
        (Logup.Lookup.protocol f n M P ell).tree (Logup.Lookup.protocol f n M P ell).roles
        (Logup.Lookup.protocol f n M P ell).oracles A impl
        (Logup.Lookup.Honest.prover f cfg data indices unifSpec)
        (Logup.Lookup.verifier f n M P ell cfg unifSpec ($ᵗ F)
          ($ᵗ ((Fin n → F) × (Fin ((M + P) ⌈/⌉ ell) → F))) ($ᵗ F) A view)),
        actual = (result.verifierOut, result.world.flatten) ∧
          actual.2.length = c * (1 + n + ((M + P) ⌈/⌉ ell) +
            (Sumcheck.Interaction.Computable.Resources.pathUsage (ell + 2) n
              result.path.2.2.2.2).roundSamples) := by
  intro actual hactual
  rw [Logup.Lookup.uniformExecute, ← scalar_execute_world_eq, support_map] at hactual
  obtain ⟨result, hresult, rfl⟩ := hactual
  refine ⟨result, hresult, rfl, ?_⟩
  have hv := scalar_uniform_phased_verifier_queries f n M P ell cfg c hsample A view impl
    (Logup.Lookup.Honest.prover f cfg data indices unifSpec) result hresult
  have hp := HonestSamplingResources.scalar_prover_queries_zero f cfg data indices unifSpec A impl
    (Logup.Lookup.verifier f n M P ell cfg unifSpec ($ᵗ F)
      ($ᵗ ((Fin n → F) × (Fin ((M + P) ⌈/⌉ ell) → F))) ($ᵗ F) A view) result hresult
  have partition := WorldSegments.queryCount_partition (Logup.Lookup.protocol f n M P ell).roles
    result.world
  change result.world.flatten.length = _
  omega

/-- Every named eager tuple default output retains an actual supported phase path,
with its exact primitive log length including the beta draw. -/
theorem tuple_uniformExecute_default_queries
    {F : Type} [Field F] [DecidableEq F] [SampleableType F]
    {b W n M P ell : Nat} {schema : TaggedTuple.Schema B b W}
    {layout : Logup.Lookup.Tuple.ProviderLayout b P}
    (f : B →+* F) (cfg : Logup.Lookup.Config B n M P ell)
    (prepared : Logup.Lookup.Tuple.PreparedProvider schema layout n M)
    (indices : Vector (Fin (P * 2 ^ n)) (M * 2 ^ n)) (c : Nat)
    (hsample : ∀ result ∈ support ($ᵗ F).withQueryLog, result.2.length = c)
    (A : PFunctor)
    (view : VirtualOracle (ofPFunctor A) (Logup.Lookup.Tuple.coefficientFamily f n M P W))
    (impl : QueryImpl (ofPFunctor A) Id) :
    ∀ actual ∈ support (Logup.Lookup.Tuple.uniformExecute f n M P W ell cfg A view impl
      (Logup.Lookup.Tuple.Honest.prover f cfg prepared indices unifSpec)).withQueryLog,
      ∃ result ∈ support (executeStrategiesPhased unifSpec
        (Logup.Lookup.Tuple.protocol f n M P ell).tree
        (Logup.Lookup.Tuple.protocol f n M P ell).roles
        (Logup.Lookup.Tuple.protocol f n M P ell).oracles A impl
        (Logup.Lookup.Tuple.Honest.prover f cfg prepared indices unifSpec)
        (Logup.Lookup.Tuple.verifier f n M P W ell cfg unifSpec ($ᵗ F) ($ᵗ F)
          ($ᵗ ((Fin n → F) × (Fin ((M + P) ⌈/⌉ ell) → F))) ($ᵗ F) A view)),
        actual = (result.verifierOut, result.world.flatten) ∧
          actual.2.length = c * (2 + n + ((M + P) ⌈/⌉ ell) +
            (Sumcheck.Interaction.Computable.Resources.pathUsage (ell + 2) n
              result.path.2.2.2.2.2).roundSamples) := by
  intro actual hactual
  rw [Logup.Lookup.Tuple.uniformExecute, ← tuple_execute_world_eq, support_map] at hactual
  obtain ⟨result, hresult, rfl⟩ := hactual
  refine ⟨result, hresult, rfl, ?_⟩
  have hv := tuple_uniform_phased_verifier_queries f n M P W ell cfg c hsample A view impl
    (Logup.Lookup.Tuple.Honest.prover f cfg prepared indices unifSpec) result hresult
  have hp := HonestSamplingResources.tuple_prover_queries_zero f cfg prepared indices unifSpec
    A impl (Logup.Lookup.Tuple.verifier f n M P W ell cfg unifSpec ($ᵗ F) ($ᵗ F)
      ($ᵗ ((Fin n → F) × (Fin ((M + P) ⌈/⌉ ell) → F))) ($ᵗ F) A view) result hresult
  have partition := WorldSegments.queryCount_partition
    (Logup.Lookup.Tuple.protocol f n M P ell).roles
    result.world
  change result.world.flatten.length = _
  omega
end Logup.Interaction.SamplingResources

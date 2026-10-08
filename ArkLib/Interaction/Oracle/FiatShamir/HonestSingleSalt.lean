/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Interaction.Oracle.FiatShamir.SingleSaltSecurity

/-!
# Honest private-coin provers for a single global Fiat–Shamir salt

An honest prover is a native public-protocol strategy with access only to private uniform
sampling. Its continuation may depend on each preceding public challenge. The compiler below
samples a single global salt before running that strategy, and hashes a typed full-prefix key
only after the corresponding public message passes its guard.
-/

@[expose] public section

open Interaction.Oracle OracleComp OracleSpec

namespace Interaction.Oracle.FiatShamir

open Security.StateRestoration

/-- A native honest public-message prover, with only private sampling as an ambient effect. -/
abbrev HonestProver (rounds : List Round) :=
  Prover.Strategy unifSpec (publicProtocol rounds).tree
    (publicProtocol rounds).roles (fun _ => Unit)

/-- The interactive uniform-challenge run of an adaptive honest strategy. A failed prefix guard
stops before sampling the current challenge. The result keeps the messages and the complete
accepted path, so it can be compared with the compiled run at the same observation type. -/
def honestInteractiveRun {Input : Type} : (rounds : List Round) →
    GuardSchedule Input PUnit rounds → Input → HonestProver rounds →
    ProbComp (Option (PublicMessages rounds × (protocol rounds).tree.ExecutionPath))
  | [], _, _, _ => pure (some (PUnit.unit, PUnit.unit))
  | round :: rounds, (guard, next), z, prover => do
      let chosen ← prover
      let message := chosen.1
      if !guard z message PUnit.unit then
        return none
      let challenge ← $ᵗ round.Challenge
      let continuation ← chosen.2 challenge
      let suffix ← honestInteractiveRun rounds (next message PUnit.unit challenge) z continuation
      return suffix.map fun (messages, path) =>
        (⟨message, messages⟩, ⟨message, challenge, path⟩)

/-- Adapt an unguarded private-coin strategy to the actual guarded public tree. A rejected
message has no prover continuation; a passed challenge preserves the private response action. -/
def guardedHonestProver {Input : Type} : (rounds : List Round) →
    (guards : GuardSchedule Input PUnit rounds) → (z : Input) → HonestProver rounds →
    Prover.Strategy unifSpec (guardedPublicProtocol rounds guards z).tree
      (guardedPublicProtocol rounds guards z).roles (fun _ => Unit)
  | [], _, _, _ => ()
  | round :: rounds, (guard, next), z, prover => do
      let chosen ← prover
      let message := chosen.1
      let after : (pass : Bool) → Prover.Strategy unifSpec
          (publicRest round rounds next z message pass).tree
          (publicRest round rounds next z message pass).roles (fun _ => Unit)
        | false => ()
        | true => fun challenge => do
            let continuation ← chosen.2 challenge
            pure (guardedHonestProver rounds (next message PUnit.unit challenge)
              z continuation)
      pure ⟨message, after (guard z message PUnit.unit)⟩

/-- The native interactive verifier samples each reached public challenge uniformly. -/
def honestUniformVerifier {Input : Type} : (rounds : List Round) →
    (guards : GuardSchedule Input PUnit rounds) → (z : Input) →
    Verifier.Strategy unifSpec (guardedPublicProtocol rounds guards z).tree
      (guardedPublicProtocol rounds guards z).roles
      (guardedPublicProtocol rounds guards z).oracles 0 (fun _ => Unit)
  | [], _, _ => pure ()
  | round :: rounds, (guard, next), z => fun message =>
      let after : (pass : Bool) → OracleComp (unifSpec + ofPFunctor 0)
        (Verifier.Strategy unifSpec
          (publicRest round rounds next z message pass).tree
          (publicRest round rounds next z message pass).roles
          (publicRest round rounds next z message pass).oracles 0 (fun _ => Unit))
        | false => pure (pure ())
        | true => pure (do
            let challenge ← liftComp ($ᵗ round.Challenge) (unifSpec + ofPFunctor 0)
            pure ⟨challenge,
              honestUniformVerifier rounds (next message PUnit.unit challenge) z⟩)
      after (guard z message PUnit.unit)

/-- The existing native paired strategy executor for the guarded interactive protocol. -/
def honestNativeInteractiveRun {Input : Type} (rounds : List Round)
    (guards : GuardSchedule Input PUnit rounds) (z : Input)
    (prover : HonestProver rounds) :
    ProbComp (Option (protocol rounds).tree.ExecutionPath) :=
  (fun result => acceptedPath rounds guards z result.1) <$>
    executeStrategies unifSpec (guardedPublicProtocol rounds guards z).tree
      (guardedPublicProtocol rounds guards z).roles
      (guardedPublicProtocol rounds guards z).oracles 0
      (fun q => nomatch q)
      (guardedHonestProver rounds guards z prover)
      (honestUniformVerifier rounds guards z)

private def honestRoundProver {Input : Type} (round : Round) (rounds : List Round)
    (next : round.Message → PUnit → round.Challenge → GuardSchedule Input PUnit rounds)
    (z : Input) (message : round.Message)
    (continuation : round.Challenge → ProbComp (HonestProver rounds)) :
    (pass : Bool) → Prover.Strategy unifSpec
      (publicRest round rounds next z message pass).tree
      (publicRest round rounds next z message pass).roles (fun _ => Unit)
  | false => ()
  | true => fun challenge =>
      guardedHonestProver rounds (next message PUnit.unit challenge) z <$>
        continuation challenge

private def honestRoundVerifier {Input : Type} (round : Round) (rounds : List Round)
    (next : round.Message → PUnit → round.Challenge → GuardSchedule Input PUnit rounds)
    (z : Input) (message : round.Message) :
    (pass : Bool) → OracleComp (unifSpec + ofPFunctor 0)
      (Verifier.Strategy unifSpec
        (publicRest round rounds next z message pass).tree
        (publicRest round rounds next z message pass).roles
        (publicRest round rounds next z message pass).oracles 0 (fun _ => Unit))
  | false => pure (pure ())
  | true => pure (do
      let challenge ← liftComp ($ᵗ round.Challenge) (unifSpec + ofPFunctor 0)
      pure ⟨challenge, honestUniformVerifier rounds
        (next message PUnit.unit challenge) z⟩)

private def honestAfterSend {Input : Type} (round : Round) (rounds : List Round)
    (next : round.Message → PUnit → round.Challenge → GuardSchedule Input PUnit rounds)
    (z : Input) (message : round.Message)
    (continuation : round.Challenge → ProbComp (HonestProver rounds))
    (pass : Bool) : ProbComp (Option (protocol (round :: rounds)).tree.ExecutionPath) :=
  (fun result => decodeAfterGuard round rounds next z message
    (fun challenge suffix => acceptedPath rounds (next message PUnit.unit challenge) z suffix)
    pass result.1) <$>
    (do
      let verifier ← simulateQ (Verifier.liftAccessImpl unifSpec 0 (fun q => nomatch q))
        (honestRoundVerifier round rounds next z message pass)
      executeStrategies unifSpec (publicRest round rounds next z message pass).tree
        (publicRest round rounds next z message pass).roles
        (publicRest round rounds next z message pass).oracles 0 (fun q => nomatch q)
        (honestRoundProver round rounds next z message continuation pass) verifier)

private theorem honestUniformSample (round : Round) :
    simulateQ (Verifier.liftAccessImpl unifSpec 0 (fun q => nomatch q))
      (liftComp ($ᵗ round.Challenge) (unifSpec + ofPFunctor 0)) =
    ($ᵗ round.Challenge : ProbComp round.Challenge) := by
  rw [QueryImpl.simulateQ_liftComp_left_eq_of_apply
    (Verifier.liftAccessImpl unifSpec 0 (fun q => nomatch q))
    (QueryImpl.id' unifSpec) (by intro q; rfl) ($ᵗ round.Challenge)]
  exact simulateQ_id' _

set_option backward.isDefEq.respectTransparency false in
private theorem honestAfterSend_eq {Input : Type} (round : Round) (rounds : List Round)
    (next : round.Message → PUnit → round.Challenge → GuardSchedule Input PUnit rounds)
    (z : Input) (message : round.Message)
    (continuation : round.Challenge → ProbComp (HonestProver rounds))
    (ih : ∀ (guards : GuardSchedule Input PUnit rounds) (prover : HonestProver rounds),
      honestNativeInteractiveRun rounds guards z prover =
        (fun result => result.map Prod.snd) <$>
          honestInteractiveRun rounds guards z prover)
    (pass : Bool) :
    honestAfterSend round rounds next z message continuation pass =
      if pass then (do
        let challenge ← $ᵗ round.Challenge
        let prover ← continuation challenge
        let suffix ← honestInteractiveRun rounds
          (next message PUnit.unit challenge) z prover
        pure (suffix.map fun item => ⟨message, challenge, item.2⟩))
      else pure none := by
  cases pass with
  | false =>
      simp [honestAfterSend, honestRoundVerifier, honestRoundProver,
        publicRest, decodeAfterGuard, executeStrategies_done]
  | true =>
      unfold honestAfterSend
      simp only [honestRoundVerifier, honestRoundProver, publicRest,
        Protocol.public_tree, Protocol.public_roles, Protocol.public_oracles]
      simp only [simulateQ_pure, pure_bind]
      rw [executeStrategies_public_receiver]
      simp only [ite_true, decodeAfterGuard, map_bind, bind_pure_comp]
      rw [simulateQ_map, honestUniformSample]
      simp only [map_eq_pure_bind, bind_assoc, pure_bind]
      apply bind_congr
      intro challenge
      apply bind_congr
      intro prover
      have htail := ih (next message PUnit.unit challenge) prover
      have mapped := congrArg
        (fun run : ProbComp (Option (protocol rounds).tree.ExecutionPath) =>
          Option.map (fun tail =>
            (⟨message, challenge, tail⟩ : (protocol (round :: rounds)).tree.ExecutionPath))
              <$> run) htail
      simpa only [honestNativeInteractiveRun, map_eq_pure_bind, bind_assoc,
        pure_bind, Functor.map_map, Option.map_map, Function.comp_def] using mapped

set_option backward.isDefEq.respectTransparency false in
/-- The direct uniform-challenge interpreter is exactly the accepted-path projection of the
actual native guarded public strategy executor, for arbitrary adaptive private continuations. -/
theorem honestNativeInteractiveRun_eq {Input : Type} :
    (rounds : List Round) → (guards : GuardSchedule Input PUnit rounds) →
    (z : Input) → (prover : HonestProver rounds) →
    honestNativeInteractiveRun rounds guards z prover =
      (fun result => result.map Prod.snd) <$>
        honestInteractiveRun rounds guards z prover
  | [], _, _, prover => by
      simp [honestNativeInteractiveRun, honestInteractiveRun,
        guardedPublicProtocol, guardedHonestProver,
        honestUniformVerifier, acceptedPath, executeStrategies_done]
  | round :: rounds, (guard, next), z, prover => by
      have hstep :
          honestNativeInteractiveRun (round :: rounds) (guard, next) z prover =
            (do
              let chosen ← prover
              honestAfterSend round rounds next z chosen.1 chosen.2
                (guard z chosen.1 PUnit.unit)) := by
        unfold honestNativeInteractiveRun
        simp only [guardedPublicProtocol, Protocol.public_tree,
          Protocol.public_roles, Protocol.public_oracles]
        rw [executeStrategies_public_sender]
        simp only [guardedHonestProver, honestUniformVerifier, acceptedPath,
          map_bind, bind_pure_comp]
        simp only [map_eq_pure_bind, bind_assoc, pure_bind]
        apply bind_congr
        intro chosen
        simp only [honestAfterSend, publicRest, honestRoundProver,
          honestRoundVerifier, decodeAfterGuard, map_bind, bind_pure_comp]
        rfl
      rw [hstep]
      simp only [honestInteractiveRun, map_bind]
      apply bind_congr
      intro chosen
      rw [honestAfterSend_eq round rounds next z chosen.1 chosen.2
        (fun guards continuation => honestNativeInteractiveRun_eq rounds guards z continuation)]
      cases hguard : guard z chosen.1 PUnit.unit with
      | false => simp
      | true =>
          simp only [↓reduceIte, TypeTree.runtimeLens_toFunA_public,
            Protocol.public_tree, PFunctor.FreeM.liftBind_eq,
            PFunctor.selfMonomial_B, PFunctor.FreeM.bind_eq_bind,
            Protocol.public_roles, TypeTree.runtimeLens_toFunA_oracle,
            TypeTree.runtimeLens_toFunB_oracle,
            TypeTree.runtimeLens_toFunB_public, bind_pure_comp,
            Bool.not_true, Bool.false_eq_true, map_bind,
            Functor.map_map, Option.map_map]
          apply bind_congr
          intro challenge
          apply bind_congr
          intro tailProver
          congr 1

/-- Compile the same adaptive strategy to the native lazy challenge oracle. The embedding
remembers the already-sent message prefix when this definition recurses on a suffix. -/
def honestCompiledRun {Input : Type} {allRounds : List Round} :
    (rounds : List Round) → GuardSchedule Input PUnit rounds → Input →
    HonestProver rounds →
    (embed : Key Input PUnit rounds → Key Input PUnit allRounds) →
    (preserve : ∀ key, (embed key).Challenge = key.Challenge) →
    OracleComp (unifSpec + oracleSpec Input PUnit allRounds)
      (Option (PublicMessages rounds × (protocol rounds).tree.ExecutionPath))
  | [], _, _, _, _, _ => pure (some (PUnit.unit, PUnit.unit))
  | round :: rounds, (guard, next), z, prover, embed, preserve => do
      let chosen ← liftM prover
      let message := chosen.1
      if !guard z message PUnit.unit then
        return none
      let response ← liftM ((unifSpec + oracleSpec Input PUnit allRounds).query
        (.inr (embed (Key.here z message PUnit.unit))))
      let challenge : round.Challenge :=
        cast (preserve (Key.here z message PUnit.unit)) response
      let continuation ← liftM (chosen.2 challenge)
      let suffix ← honestCompiledRun rounds (next message PUnit.unit challenge) z
        continuation (fun key => embed (Key.later message PUnit.unit key))
        (fun key => preserve (Key.later message PUnit.unit key))
      return suffix.map fun (messages, path) =>
        (⟨message, messages⟩, ⟨message, challenge, path⟩)

/-- Draw a salt independently, then compile a private-coin strategy to a complete proof. The
selected proof is emitted only if every reached guard passed. -/
def honestSingleSaltAdversary {Statement GlobalSalt Witness : Type}
    [SampleableType GlobalSalt] (rounds : List Round)
    (guards : GuardSchedule (Statement × GlobalSalt) PUnit rounds)
    (statement : Statement) (witness : Witness) (prover : GlobalSalt → HonestProver rounds) :
    SingleSaltAdversary Statement GlobalSalt Witness rounds := do
  let salt ← liftM (($ᵗ GlobalSalt) : ProbComp GlobalSalt)
  let selected ← honestCompiledRun rounds guards (statement, salt) (prover salt) id (fun _ => rfl)
  return selected.map fun (messages, _) => (statement, (salt, messages), witness)

/-- Uniform interactive challenges with the same independent salt and terminal check. This is
the observation compared with the accepted native-verifier output. -/
def honestInteractiveAccepted {Statement GlobalSalt Witness : Type}
    [SampleableType GlobalSalt] (rounds : List Round)
    (guards : GuardSchedule (Statement × GlobalSalt) PUnit rounds)
    (accepts : (Statement × GlobalSalt) → (protocol rounds).tree.ExecutionPath → Bool)
    (statement : Statement) (witness : Witness) (prover : GlobalSalt → HonestProver rounds) :
    ProbComp (Option ((Statement × GlobalSalt) ×
      (protocol rounds).tree.ExecutionPath × Witness)) := do
  let salt ← $ᵗ GlobalSalt
  let result ← honestInteractiveRun rounds guards (statement, salt) (prover salt)
  return (result.map fun (_, path) => ((statement, salt), path, witness)).filter
    (fun selected => accepts selected.1 selected.2.1)

/-- The honest source endpoint uses the actual guarded public strategy executor and a pure
terminal acceptance predicate. The strategy is selected after the independent salt draw. -/
def honestNativeInteractiveAccepted {Statement GlobalSalt Witness : Type}
    [SampleableType GlobalSalt] (rounds : List Round)
    (guards : GuardSchedule (Statement × GlobalSalt) PUnit rounds)
    (accepts : (Statement × GlobalSalt) → (protocol rounds).tree.ExecutionPath → Bool)
    (statement : Statement) (witness : Witness)
    (prover : GlobalSalt → HonestProver rounds) :
    ProbComp (Option ((Statement × GlobalSalt) ×
      (protocol rounds).tree.ExecutionPath × Witness)) := do
  let salt ← $ᵗ GlobalSalt
  let path ← honestNativeInteractiveRun rounds guards (statement, salt) (prover salt)
  return (path.map fun transcript => ((statement, salt), transcript, witness)).filter
    (fun selected => accepts selected.1 selected.2.1)

/-- The direct interactive interpreter and the actual guarded native source have exactly the
same accepted-output distribution for salt-aware adaptive private-coin provers. -/
theorem honestNativeInteractiveAccepted_eq
    {Statement GlobalSalt Witness : Type}
    [SampleableType GlobalSalt] (rounds : List Round)
    (guards : GuardSchedule (Statement × GlobalSalt) PUnit rounds)
    (accepts : (Statement × GlobalSalt) → (protocol rounds).tree.ExecutionPath → Bool)
    (statement : Statement) (witness : Witness)
    (prover : GlobalSalt → HonestProver rounds) :
    honestNativeInteractiveAccepted rounds guards accepts statement witness prover =
      honestInteractiveAccepted rounds guards accepts statement witness prover := by
  unfold honestNativeInteractiveAccepted honestInteractiveAccepted
  apply bind_congr
  intro salt
  rw [honestNativeInteractiveRun_eq]
  simp only [bind_pure_comp, Functor.map_map]
  congr 1
  funext selected
  cases selected with
  | none => rfl
  | some selected =>
      rcases selected with ⟨messages, path⟩
      rfl

/-- The actual accepted native execution of the compiled honest prover. Verification reruns
the guarded public strategy against the same lazy challenge oracle. -/
def honestSingleSaltAccepted {Statement GlobalSalt Witness : Type}
    [SampleableType GlobalSalt] (rounds : List Round)
    (guards : GuardSchedule (Statement × GlobalSalt) PUnit rounds)
    (accepts : (Statement × GlobalSalt) → (protocol rounds).tree.ExecutionPath → Bool)
    (statement : Statement) (witness : Witness) (prover : GlobalSalt → HonestProver rounds) :=
  singleSaltAcceptedExecution rounds guards accepts
    (honestSingleSaltAdversary rounds guards statement witness prover)

/-- No key in the still-unplayed suffix has been queried. -/
def HonestCacheFresh {Input : Type} {rounds allRounds : List Round}
    (cache : (oracleSpec Input PUnit allRounds).QueryCache)
    (embed : Key Input PUnit rounds → Key Input PUnit allRounds) : Prop :=
  ∀ key, cache (embed key) = none

/-- The next key is absent from a cache fresh on the remaining suffix. -/
theorem honestCacheFresh_here {Input : Type} {round : Round} {rounds allRounds : List Round}
    (cache : (oracleSpec Input PUnit allRounds).QueryCache)
    (embed : Key Input PUnit (round :: rounds) → Key Input PUnit allRounds)
    (fresh : HonestCacheFresh cache embed) (z : Input) (message : round.Message) :
    cache (embed (Key.here z message PUnit.unit)) = none :=
  fresh _

/-- Adding the current answer leaves every strictly later key fresh. -/
theorem honestCacheFresh_later {Input : Type} [DecidableEq Input]
    {round : Round} {rounds allRounds : List Round}
    (cache : (oracleSpec Input PUnit allRounds).QueryCache)
    (embed : Key Input PUnit (round :: rounds) → Key Input PUnit allRounds)
    (injective : Function.Injective embed) (fresh : HonestCacheFresh cache embed)
    (z : Input) (message : round.Message)
    (response : (embed (Key.here z message PUnit.unit)).Challenge) :
    HonestCacheFresh (cache.cacheQuery (embed (Key.here z message PUnit.unit)) response)
      (fun key => embed (Key.later message PUnit.unit key)) := by
  intro key
  have hne : embed (Key.later message PUnit.unit key) ≠
      embed (Key.here z message PUnit.unit) := by
    intro h
    have h' := injective h
    cases h'
  rw [QueryCache.cacheQuery_of_ne _ _ hne]
  exact fresh _

/-- Uniform sampling commutes with the answer-type transport of this key embedding. This is
automatic for the concrete identity and prefix constructors used by the compiler. -/
def HonestSamplePreserving {Input : Type} {rounds allRounds : List Round}
    (embed : Key Input PUnit rounds → Key Input PUnit allRounds)
    (preserve : ∀ key, (embed key).Challenge = key.Challenge) : Prop :=
  ∀ key, (cast (preserve key)) <$> ($ᵗ (embed key).Challenge : ProbComp _) =
    ($ᵗ key.Challenge : ProbComp _)

theorem honestSamplePreserving_id {Input : Type} {rounds : List Round} :
    HonestSamplePreserving (Input := Input) (rounds := rounds) id (fun _ => rfl) := by
  intro key
  change (cast (rfl : key.Challenge = key.Challenge)) <$> ($ᵗ key.Challenge) =
    ($ᵗ key.Challenge : ProbComp _)
  have hcast : (cast (rfl : key.Challenge = key.Challenge)) =
      (id : key.Challenge → key.Challenge) := by
    funext x
    exact cast_eq _ x
  rw [hcast, id_map]

private theorem map_run_fst {S A B : Type} (f : A → B)
    (st : StateT S ProbComp A) (s : S) :
    (fun result => f result.1) <$> st.run s = f <$> st.run' s := by
  simp only [StateT.run'_eq, Functor.map_map]

private theorem bind_cast_sample {A B C : Type} (h : A = B)
    (sample : ProbComp A) (continuation : A → ProbComp C) :
    (sample >>= continuation) =
      ((cast h) <$> sample) >>= fun b => continuation (cast h.symm b) := by
  cases h
  have hcast : (cast (rfl : A = A)) = (id : A → A) := by
    funext x
    exact cast_eq _ x
  simp only [hcast, id_map, id_eq]

private theorem cast_symm_cast {A B : Type} (h : A = B) (b : B) :
    cast h (cast h.symm b) = b := by
  cases h
  calc
    cast (rfl : A = A) (cast (rfl : A = A) b) = cast (rfl : A = A) b := by
      exact congrArg (cast (rfl : A = A)) (cast_eq (rfl : A = A) b)
    _ = b := cast_eq _ b

private theorem cast_cast_symm {A B : Type} (h : A = B) (a : A) :
    cast h.symm (cast h a) = a := by
  cases h
  exact (cast_eq _ (cast (rfl : A = A) a)).trans (cast_eq _ a)

set_option backward.isDefEq.respectTransparency false in
/-- A cache that has no remaining suffix key makes each compiled hash answer an independent
uniform challenge. This equality includes all adaptive private continuation sampling. -/
theorem honestCompiledRun_eq_interactive {Input : Type} [DecidableEq Input]
    {allRounds : List Round} (rounds : List Round)
    (guards : GuardSchedule Input PUnit rounds) (z : Input)
    (prover : HonestProver rounds)
    (embed : Key Input PUnit rounds → Key Input PUnit allRounds)
    (preserve : ∀ key, (embed key).Challenge = key.Challenge)
    (injective : Function.Injective embed)
    (sampleLaw : HonestSamplePreserving embed preserve)
    (cache : (oracleSpec Input PUnit allRounds).QueryCache)
    (fresh : HonestCacheFresh cache embed) :
    (simulateQ (oracleSpec Input PUnit allRounds).romImpl
      (honestCompiledRun rounds guards z prover embed preserve)).run' cache =
    honestInteractiveRun rounds guards z prover := by
  induction rounds generalizing allRounds with
  | nil =>
      simp [honestCompiledRun, honestInteractiveRun]
  | cons round rounds ih =>
      rcases guards with ⟨guard, next⟩
      simp only [honestCompiledRun, honestInteractiveRun]
      simp only [simulateQ_bind]
      rw [roSim.run'_liftM_bind
        (hashSpec := oracleSpec Input PUnit allRounds)
        (ro := (oracleSpec Input PUnit allRounds).randomOracle) prover]
      apply bind_congr
      intro chosen
      cases hguard : guard z chosen.1 PUnit.unit with
      | false => simp
      | true =>
          simp only [Bool.not_true, Bool.false_eq_true, ite_false]
          simp only [simulateQ_bind, simulateQ_query, OracleQuery.cont_query,
            OracleQuery.input_query, id_map]
          simp only [simulateQ_pure, StateT.run'_bind', StateT.run'_pure']
          simp only [OracleSpec.romImpl_apply_inr, randomOracle.run_eq,
            fresh (Key.here z chosen.1 PUnit.unit)]
          simp only [bind_assoc, pure_bind]
          simp only [roSim.run_liftM, bind_map_left]
          simp only [bind_pure_comp]
          simp_rw [map_run_fst]
          rw [bind_cast_sample (preserve (Key.here z chosen.1 PUnit.unit))]
          rw [sampleLaw (Key.here z chosen.1 PUnit.unit)]
          simp only [cast_symm_cast]
          apply bind_congr
          intro challenge
          conv_lhs =>
            arg 1
            change chosen.2 (cast (preserve (Key.here z chosen.1 PUnit.unit))
              (cast (preserve (Key.here z chosen.1 PUnit.unit)).symm challenge))
          have harg := cast_symm_cast
            (preserve (Key.here z chosen.1 PUnit.unit)) challenge
          rw [harg]
          apply bind_congr
          intro continuation
          have hinj : Function.Injective
              (fun key => embed (Key.later chosen.1 PUnit.unit key)) := by
            intro x y hxy
            exact congrArg (fun data => data.2.2) (Sum.inr.inj (injective hxy))
          have hsamp : HonestSamplePreserving
              (fun key => embed (Key.later chosen.1 PUnit.unit key))
              (fun key => preserve (Key.later chosen.1 PUnit.unit key)) := by
            intro key
            exact sampleLaw (Key.later chosen.1 PUnit.unit key)
          have hfresh := honestCacheFresh_later cache embed injective fresh
            z chosen.1
            (cast (preserve (Key.here z chosen.1 PUnit.unit)).symm challenge)
          rw [ih (next chosen.1 PUnit.unit challenge) continuation
            (fun key => embed (Key.later chosen.1 PUnit.unit key))
            (fun key => preserve (Key.later chosen.1 PUnit.unit key))
            hinj hsamp _ hfresh]

/-- With an initially empty oracle cache, the compiler's complete path and message sequence
have exactly the interactive uniform-challenge distribution. Ordered hash logs are projected
away; private sampling remains inside the same `ProbComp`. -/
theorem honestCompiledRun_empty_eq_interactive {Input : Type} [DecidableEq Input]
    (rounds : List Round) (guards : GuardSchedule Input PUnit rounds)
    (z : Input) (prover : HonestProver rounds) :
    (fun result => result.1.1) <$>
      randomOracleLoggedRun (honestCompiledRun rounds guards z prover id (fun _ => rfl)) ∅ =
    honestInteractiveRun rounds guards z prover := by
  have hproj := randomOracleLoggedRun_project
    (honestCompiledRun rounds guards z prover id (fun _ => rfl))
    (∅ : (oracleSpec Input PUnit rounds).QueryCache)
  have hresult := congrArg (fun computation => Prod.fst <$> computation) hproj
  simp only [Functor.map_map] at hresult
  have hfresh : HonestCacheFresh
      (∅ : (oracleSpec Input PUnit rounds).QueryCache) id := by
    intro key
    rfl
  simpa only [Function.comp_def] using hresult.trans
    (honestCompiledRun_eq_interactive rounds guards z prover id (fun _ => rfl)
      (fun _ _ h => h) honestSamplePreserving_id ∅ hfresh)

/-- The salt is drawn before any prover action. The compiled proof producer therefore has
the same selected-proof distribution as the uniform interactive run, including aborts. -/
theorem honestSingleSaltAdversary_run'_eq_interactive
    {Statement GlobalSalt Witness : Type}
    [DecidableEq Statement] [DecidableEq GlobalSalt] [SampleableType GlobalSalt]
    (rounds : List Round)
    (guards : GuardSchedule (Statement × GlobalSalt) PUnit rounds)
    (statement : Statement) (witness : Witness) (prover : GlobalSalt → HonestProver rounds) :
    (simulateQ (oracleSpec (Statement × GlobalSalt) PUnit rounds).romImpl
      (honestSingleSaltAdversary rounds guards statement witness prover)).run' ∅ = (do
        let salt ← $ᵗ GlobalSalt
        let result ← honestInteractiveRun rounds guards (statement, salt) (prover salt)
        pure (result.map fun (messages, _) => (statement, (salt, messages), witness))) := by
  unfold honestSingleSaltAdversary
  simp only [simulateQ_bind, simulateQ_pure]
  rw [roSim.run'_liftM_bind
    (hashSpec := oracleSpec (Statement × GlobalSalt) PUnit rounds)
    (ro := (oracleSpec (Statement × GlobalSalt) PUnit rounds).randomOracle)
    (($ᵗ GlobalSalt) : ProbComp GlobalSalt)]
  apply bind_congr
  intro salt
  simp only [bind_pure_comp]
  rw [StateT.run'_map']
  have hfresh : HonestCacheFresh
      (∅ : (oracleSpec (Statement × GlobalSalt) PUnit rounds).QueryCache) id := by
    intro key
    rfl
  rw [honestCompiledRun_eq_interactive rounds guards (statement, salt) (prover salt)
    id (fun _ => rfl) (fun _ _ h => h) honestSamplePreserving_id ∅ hfresh]

/-- The actual logged lazy-oracle run of the honest proof producer has the same visible
selected-proof distribution as the salted interactive source. -/
theorem honestSingleSaltAdversary_logged_eq_interactive
    {Statement GlobalSalt Witness : Type}
    [DecidableEq Statement] [DecidableEq GlobalSalt] [SampleableType GlobalSalt]
    (rounds : List Round)
    (guards : GuardSchedule (Statement × GlobalSalt) PUnit rounds)
    (statement : Statement) (witness : Witness) (prover : GlobalSalt → HonestProver rounds) :
    (fun result => result.1.1) <$> randomOracleLoggedRun
      (honestSingleSaltAdversary rounds guards statement witness prover) ∅ = (do
        let salt ← $ᵗ GlobalSalt
        let result ← honestInteractiveRun rounds guards (statement, salt) (prover salt)
        pure (result.map fun (messages, _) => (statement, (salt, messages), witness))) := by
  have hproj := randomOracleLoggedRun_project
    (honestSingleSaltAdversary rounds guards statement witness prover)
    (∅ : (oracleSpec (Statement × GlobalSalt) PUnit rounds).QueryCache)
  have hresult := congrArg (fun computation => Prod.fst <$> computation) hproj
  simp only [Functor.map_map] at hresult
  simpa only [Function.comp_def] using hresult.trans
    (honestSingleSaltAdversary_run'_eq_interactive rounds guards statement witness prover)

/-- Every lazy random-oracle run extends its initial cache, even when private uniform draws
are interleaved and the program returns a failed result. -/
theorem honestRom_cache_le {Input : Type} [DecidableEq Input]
    {rounds : List Round} {α : Type}
    (program : OracleComp (unifSpec + oracleSpec Input PUnit rounds) α)
    (initial : (oracleSpec Input PUnit rounds).QueryCache)
    (result : α × (oracleSpec Input PUnit rounds).QueryCache)
    (supported : result ∈ support
      ((simulateQ (oracleSpec Input PUnit rounds).romImpl program).run initial)) :
    initial ≤ result.2 := by
  let spec := oracleSpec Input PUnit rounds
  have hprivate : QueryImpl.PreservesInv (unifFwdImpl spec)
      (initial ≤ ·) := by
    intro n cache hle value hvalue
    rw [show (unifFwdImpl spec n).run cache =
      (fun answer => (answer, cache)) <$> (unifSpec.query n : ProbComp (Fin (n + 1)))
      from roSim.run_apply_inl (ro := spec.randomOracle) n cache] at hvalue
    rw [support_map] at hvalue
    obtain ⟨_, _, rfl⟩ := hvalue
    exact hle
  have hhash : QueryImpl.PreservesInv spec.randomOracle (initial ≤ ·) :=
    QueryImpl.PreservesInv.withCaching_le uniformSampleImpl initial
  have himpl : QueryImpl.PreservesInv spec.romImpl (initial ≤ ·) :=
    hprivate.add hhash
  exact OracleComp.simulateQ_run_preservesInv spec.romImpl (initial ≤ ·) himpl
    program initial le_rfl result supported

/-- A successful compiler output records messages and challenges that the final cache can
replay, with every guard on that path satisfied. -/
def HonestCachedPath {Input : Type} {allRounds : List Round} :
    (rounds : List Round) → GuardSchedule Input PUnit rounds → Input →
    (embed : Key Input PUnit rounds → Key Input PUnit allRounds) →
    (preserve : ∀ key, (embed key).Challenge = key.Challenge) →
    PublicMessages rounds → (protocol rounds).tree.ExecutionPath →
    (oracleSpec Input PUnit allRounds).QueryCache → Prop
  | [], _, _, _, _, _, _, _ => True
  | _ :: rounds, (guard, next), z, embed, preserve, messages, path, cache =>
      messages.1 = path.1 ∧ guard z path.1 PUnit.unit = true ∧
        cache (embed (Key.here z path.1 PUnit.unit)) =
          some (cast (preserve (Key.here z path.1 PUnit.unit)).symm path.2.1) ∧
        HonestCachedPath rounds (next path.1 PUnit.unit path.2.1) z
          (fun key => embed (Key.later path.1 PUnit.unit key))
          (fun key => preserve (Key.later path.1 PUnit.unit key))
          messages.2 path.2.2 cache

/-- A cached path remains cached when the oracle cache is extended. -/
theorem honestCachedPath_mono {Input : Type}
    {allRounds : List Round} :
    (rounds : List Round) → (guards : GuardSchedule Input PUnit rounds) → (z : Input) →
    (embed : Key Input PUnit rounds → Key Input PUnit allRounds) →
    (preserve : ∀ key, (embed key).Challenge = key.Challenge) →
    (messages : PublicMessages rounds) → (path : (protocol rounds).tree.ExecutionPath) →
    (cache₁ cache₂ : (oracleSpec Input PUnit allRounds).QueryCache) →
    cache₁ ≤ cache₂ → HonestCachedPath rounds guards z embed preserve messages path cache₁ →
      HonestCachedPath rounds guards z embed preserve messages path cache₂
  | [], _, _, _, _, _, _, _, _, _, _ => True.intro
  | round :: rounds, (guard, next), z, embed, preserve,
      (message, messages), ⟨pathMessage, challenge, tail⟩, cache₁, cache₂,
      hle, ⟨hmessage, hguard, hcache, htail⟩ => by
        change message = pathMessage ∧ guard z pathMessage PUnit.unit = true ∧
          cache₂ (embed (Key.here z pathMessage PUnit.unit)) =
            some (cast (preserve (Key.here z pathMessage PUnit.unit)).symm challenge) ∧
          HonestCachedPath rounds (next pathMessage PUnit.unit challenge) z
            (fun key => embed (Key.later pathMessage PUnit.unit key))
            (fun key => preserve (Key.later pathMessage PUnit.unit key)) messages tail cache₂
        exact ⟨hmessage, hguard, hle hcache,
          honestCachedPath_mono rounds (next pathMessage PUnit.unit challenge) z
            (fun key => embed (Key.later pathMessage PUnit.unit key))
            (fun key => preserve (Key.later pathMessage PUnit.unit key))
            messages tail cache₁ cache₂ hle htail⟩

/-- Replaying a cached accepted path performs no fresh challenge sampling and returns the
same complete path. This is the operational fact used for actual native verification. -/
theorem honestCachedPath_replay {Input : Type} [DecidableEq Input]
    {allRounds : List Round} :
    (rounds : List Round) → (guards : GuardSchedule Input PUnit rounds) → (z : Input) →
    (messages : PublicMessages rounds) →
    (embed : Key Input PUnit rounds → Key Input PUnit allRounds) →
    (preserve : ∀ key, (embed key).Challenge = key.Challenge) →
    (path : (protocol rounds).tree.ExecutionPath) →
    (cache : (oracleSpec Input PUnit allRounds).QueryCache) →
    HonestCachedPath rounds guards z embed preserve messages path cache →
    (simulateQ (oracleSpec Input PUnit allRounds).randomOracle
      (mappedStoppedComplete rounds guards z messages embed preserve)).run cache =
      pure (some path, cache)
  | [], _, _, _, _, _, path, _, _ => by
      cases path
      simp [mappedStoppedComplete, simulateQ_pure]
  | round :: rounds, (guard, next), z, (message, messages), embed, preserve,
      ⟨pathMessage, challenge, tail⟩, cache,
      ⟨hmessage, hguard, hkey, htail⟩ => by
        change message = pathMessage at hmessage
        subst pathMessage
        simp only [mappedStoppedComplete, hguard, Bool.not_true,
          Bool.false_eq_true, ite_false, simulateQ_bind, simulateQ_query,
          OracleQuery.cont_query, OracleQuery.input_query, id_map]
        rw [StateT.run_bind, randomOracle.run_eq, hkey]
        simp only [pure_bind]
        have hroundtrip : ∀ (h : (embed (Key.here z message PUnit.unit)).Challenge =
              round.Challenge),
            cast h (cast (preserve (Key.here z message PUnit.unit)).symm challenge) =
              challenge := by
          intro h
          have heq : h = preserve (Key.here z message PUnit.unit) :=
            Subsingleton.elim _ _
          rw [heq]
          exact cast_symm_cast _ _
        simp only [hroundtrip, simulateQ_pure, StateT.run_bind]
        have htail' : HonestCachedPath rounds (next message PUnit.unit challenge) z
            (fun key => embed (Key.later message PUnit.unit key))
            (fun key => preserve (Key.later message PUnit.unit key))
            messages tail cache := htail
        rw [honestCachedPath_replay rounds (next message PUnit.unit challenge) z
          messages (fun key => embed (Key.later message PUnit.unit key))
          (fun key => preserve (Key.later message PUnit.unit key)) tail cache htail']
        rfl

set_option backward.isDefEq.respectTransparency false in
/-- Whenever the compiled prover returns a complete path, its final cache contains every
challenge on that path; failed branches impose no path condition. -/
theorem honestCompiledRun_cached {Input : Type} [DecidableEq Input]
    {allRounds : List Round} :
    (rounds : List Round) → (guards : GuardSchedule Input PUnit rounds) → (z : Input) →
    (prover : HonestProver rounds) →
    (embed : Key Input PUnit rounds → Key Input PUnit allRounds) →
    (preserve : ∀ key, (embed key).Challenge = key.Challenge) →
    (cache : (oracleSpec Input PUnit allRounds).QueryCache) →
    (result : Option (PublicMessages rounds × (protocol rounds).tree.ExecutionPath) ×
      (oracleSpec Input PUnit allRounds).QueryCache) →
    result ∈ support ((simulateQ (oracleSpec Input PUnit allRounds).romImpl
      (honestCompiledRun rounds guards z prover embed preserve)).run cache) →
    ∀ messages path, result.1 = some (messages, path) →
      HonestCachedPath rounds guards z embed preserve messages path result.2
  | [], _, _, _, _, _, _, result, supported, messages, path, hresult => by
      simp only [honestCompiledRun, simulateQ_pure, StateT.run_pure,
        support_pure, Set.mem_singleton_iff] at supported
      subst result
      exact True.intro
  | round :: rounds, (guard, next), z, prover, embed, preserve,
      cache, result, supported, messages, path, hresult => by
        simp only [honestCompiledRun, simulateQ_bind, StateT.run_bind] at supported
        rw [mem_support_bind_iff] at supported
        obtain ⟨⟨chosen, afterPrivate⟩, hprivate, hrest⟩ := supported
        rw [OracleSpec.simulateQ_romImpl_liftM_run] at hprivate
        rw [support_map] at hprivate
        obtain ⟨selected, _, hp⟩ := hprivate
        cases hp
        cases hguard : guard z chosen.1 PUnit.unit with
        | false =>
            simp only [TypeTree.runtimeLens_toFunA_public, Protocol.public_tree,
              PFunctor.FreeM.liftBind_eq, PFunctor.selfMonomial_B,
              PFunctor.FreeM.bind_eq_bind, Protocol.public_roles, hguard,
              Bool.not_false, ↓reduceIte, simulateQ_pure, StateT.run_pure,
              MonadAttach.support_pure, Set.mem_singleton_iff] at hrest
            cases hrest
            cases hresult
        | true =>
            simp only [hguard, Bool.not_true, Bool.false_eq_true, ite_false,
              simulateQ_bind, simulateQ_query, OracleQuery.cont_query,
              OracleQuery.input_query, id_map, StateT.run_bind] at hrest
            rw [mem_support_bind_iff] at hrest
            obtain ⟨⟨response, afterQuery⟩, hquery, hafterQuery⟩ := hrest
            rw [mem_support_bind_iff] at hafterQuery
            obtain ⟨⟨continuation, afterContinuation⟩,
              hcontinuation, hafterContinuation⟩ := hafterQuery
            rw [OracleSpec.simulateQ_romImpl_liftM_run, support_map] at hcontinuation
            obtain ⟨sampledContinuation, _, hp⟩ := hcontinuation
            cases hp
            rw [mem_support_bind_iff] at hafterContinuation
            obtain ⟨⟨suffix, finalCache⟩, hsuffix, hfinal⟩ := hafterContinuation
            simp only [simulateQ_pure, StateT.run_pure,
              support_pure, Set.mem_singleton_iff] at hfinal
            have hcached : afterQuery
                (embed (Key.here z chosen.1 PUnit.unit)) = some response := by
              exact QueryImpl.withCaching_run_caches uniformSampleImpl
                (embed (Key.here z chosen.1 PUnit.unit)) cache
                (response, afterQuery) hquery
            have hle : afterQuery ≤ finalCache :=
              honestRom_cache_le
                (honestCompiledRun rounds
                  (next chosen.1 PUnit.unit
                    (cast (preserve (Key.here z chosen.1 PUnit.unit)) response)) z
                  continuation (fun key => embed (Key.later chosen.1 PUnit.unit key))
                  (fun key => preserve (Key.later chosen.1 PUnit.unit key)))
                afterQuery (suffix, finalCache) hsuffix
            cases hfinal
            cases suffix with
            | none => simp at hresult
            | some suffixData =>
                rcases suffixData with ⟨suffixMessages, suffixPath⟩
                have hpair :
                    ((chosen.1, suffixMessages),
                      (⟨chosen.1,
                        cast (preserve (Key.here z chosen.1 PUnit.unit)) response,
                        suffixPath⟩ : (protocol (round :: rounds)).tree.ExecutionPath)) =
                    (messages, path) := by
                  exact Option.some.inj hresult
                cases hpair
                have hcurrent : finalCache (embed (Key.here z chosen.1 PUnit.unit)) =
                    some response := hle hcached
                refine ⟨rfl, hguard, ?_, ?_⟩
                · simpa only [cast_cast_symm] using hcurrent
                · exact honestCompiledRun_cached rounds
                    (next chosen.1 PUnit.unit
                      (cast (preserve (Key.here z chosen.1 PUnit.unit)) response)) z
                    continuation (fun key => embed (Key.later chosen.1 PUnit.unit key))
                    (fun key => preserve (Key.later chosen.1 PUnit.unit key))
                    afterQuery (some (suffixMessages, suffixPath), finalCache)
                    hsuffix suffixMessages suffixPath rfl

/-- The concrete guarded native verifier replays a path already present in the cache. Its
pure terminal acceptance test changes only the optional result, never the cache. -/
theorem honestSingleSaltVerify_replay
    {Statement GlobalSalt : Type}
    [DecidableEq Statement] [DecidableEq GlobalSalt]
    {rounds : List Round}
    (guards : GuardSchedule (Statement × GlobalSalt) PUnit rounds)
    (accepts : (Statement × GlobalSalt) → (protocol rounds).tree.ExecutionPath → Bool)
    (z : Statement × GlobalSalt)
    (messages : PublicMessages rounds)
    (path : (protocol rounds).tree.ExecutionPath)
    (cache : (oracleSpec (Statement × GlobalSalt) PUnit rounds).QueryCache)
    (cached : HonestCachedPath rounds guards z id (fun _ => rfl)
      messages path cache) :
    (simulateQ (oracleSpec (Statement × GlobalSalt) PUnit rounds).randomOracle
      (singleSaltVerify rounds guards accepts z messages)).run cache =
    pure ((some path).filter (accepts z), cache) := by
  rw [singleSaltVerify, publicStoppedVerify_eq_with,
    publicStoppedVerifyWith_eq_mapped, simulateQ_map, StateT.run_map]
  rw [honestCachedPath_replay rounds guards z messages id (fun _ => rfl)
    path cache cached]
  rfl

private theorem honestRom_restorationQueries {Input : Type} [DecidableEq Input]
    {rounds : List Round} :
    (oracleSpec Input PUnit rounds).romImpl ∘ₛ
        restorationQueries Input PUnit rounds =
      (oracleSpec Input PUnit rounds).randomOracle := by
  funext key
  simp only [QueryImpl.apply_compose, restorationQueries, simulateQ_query,
    OracleQuery.cont_query, OracleQuery.input_query, id_map,
    OracleSpec.romImpl_apply_inr]

/-- The verifier replay law in the same interleaved `unifSpec + oracleSpec` runtime as the
compiled prover, including its exact final cache. -/
theorem honestSingleSaltVerify_replay_rom
    {Statement GlobalSalt : Type}
    [DecidableEq Statement] [DecidableEq GlobalSalt]
    {rounds : List Round}
    (guards : GuardSchedule (Statement × GlobalSalt) PUnit rounds)
    (accepts : (Statement × GlobalSalt) → (protocol rounds).tree.ExecutionPath → Bool)
    (z : Statement × GlobalSalt)
    (messages : PublicMessages rounds)
    (path : (protocol rounds).tree.ExecutionPath)
    (cache : (oracleSpec (Statement × GlobalSalt) PUnit rounds).QueryCache)
    (cached : HonestCachedPath rounds guards z id (fun _ => rfl)
      messages path cache) :
    (simulateQ (oracleSpec (Statement × GlobalSalt) PUnit rounds).romImpl
      (simulateQ (restorationQueries (Statement × GlobalSalt) PUnit rounds)
        (singleSaltVerify rounds guards accepts z messages))).run cache =
    pure ((some path).filter (accepts z), cache) := by
  rw [← QueryImpl.simulateQ_compose,
    honestRom_restorationQueries]
  exact honestSingleSaltVerify_replay guards accepts z messages path cache cached

/-- Compile an honest strategy and run the actual guarded native verifier against the same
oracle cache. The compiler's path is retained only to state and prove cache consistency;
acceptance is determined by `singleSaltVerify`. -/
def honestCompiledVerify {Statement GlobalSalt Witness : Type}
    (rounds : List Round)
    (guards : GuardSchedule (Statement × GlobalSalt) PUnit rounds)
    (accepts : (Statement × GlobalSalt) → (protocol rounds).tree.ExecutionPath → Bool)
    (statement : Statement) (salt : GlobalSalt) (witness : Witness)
    (prover : HonestProver rounds) :
    OracleComp (unifSpec + oracleSpec (Statement × GlobalSalt) PUnit rounds)
      (Option ((Statement × GlobalSalt) ×
        (protocol rounds).tree.ExecutionPath × Witness)) := do
  let selected ← honestCompiledRun rounds guards (statement, salt) prover id (fun _ => rfl)
  match selected with
  | none => pure none
  | some (messages, _) =>
      let verified ← simulateQ (restorationQueries (Statement × GlobalSalt) PUnit rounds)
        (singleSaltVerify rounds guards accepts (statement, salt) messages)
      pure (verified.map fun path => ((statement, salt), path, witness))

/-- Draw the independent global salt before running any private prover action, then compile
and verify in one shared lazy random-oracle execution. -/
def honestSingleSaltVerifiedProgram {Statement GlobalSalt Witness : Type}
    [SampleableType GlobalSalt]
    (rounds : List Round)
    (guards : GuardSchedule (Statement × GlobalSalt) PUnit rounds)
    (accepts : (Statement × GlobalSalt) → (protocol rounds).tree.ExecutionPath → Bool)
    (statement : Statement) (witness : Witness)
    (prover : GlobalSalt → HonestProver rounds) :
    OracleComp (unifSpec + oracleSpec (Statement × GlobalSalt) PUnit rounds)
      (Option ((Statement × GlobalSalt) ×
        (protocol rounds).tree.ExecutionPath × Witness)) := do
  let salt ← liftM (($ᵗ GlobalSalt) : ProbComp GlobalSalt)
  honestCompiledVerify rounds guards accepts statement salt witness (prover salt)

/-- Filter a completed transcript by the pure terminal acceptance predicate. -/
def honestAcceptedResult {Statement GlobalSalt Witness : Type}
    {rounds : List Round}
    (accepts : (Statement × GlobalSalt) → (protocol rounds).tree.ExecutionPath → Bool)
    (z : Statement × GlobalSalt) (witness : Witness)
    (selected : Option (PublicMessages rounds × (protocol rounds).tree.ExecutionPath)) :
    Option ((Statement × GlobalSalt) × (protocol rounds).tree.ExecutionPath × Witness) :=
  (selected.map fun (_, path) => (z, path, witness)).filter
    (fun accepted => accepts accepted.1 accepted.2.1)

/-- For a fixed salt, executing the compiler and concrete verifier has exactly the accepted
interactive output distribution. This program equality holds for arbitrary private samplers. -/
theorem honestCompiledVerify_eq_interactive
    {Statement GlobalSalt Witness : Type}
    [DecidableEq Statement] [DecidableEq GlobalSalt]
    (rounds : List Round)
    (guards : GuardSchedule (Statement × GlobalSalt) PUnit rounds)
    (accepts : (Statement × GlobalSalt) → (protocol rounds).tree.ExecutionPath → Bool)
    (statement : Statement) (salt : GlobalSalt) (witness : Witness)
    (prover : HonestProver rounds) :
    (simulateQ (oracleSpec (Statement × GlobalSalt) PUnit rounds).romImpl
      (honestCompiledVerify rounds guards accepts statement salt witness prover)).run' ∅ =
    (honestAcceptedResult accepts (statement, salt) witness) <$>
      honestInteractiveRun rounds guards (statement, salt) prover := by
  unfold honestCompiledVerify
  simp only [simulateQ_bind, StateT.run'_bind']
  have hfresh : HonestCacheFresh
      (∅ : (oracleSpec (Statement × GlobalSalt) PUnit rounds).QueryCache) id := by
    intro key
    rfl
  rw [← honestCompiledRun_eq_interactive rounds guards (statement, salt) prover
    id (fun _ => rfl) (fun _ _ h => h) honestSamplePreserving_id ∅ hfresh]
  simp only [StateT.run'_eq, map_eq_pure_bind, bind_assoc, pure_bind]
  apply OracleComp.bind_congr_of_forall_mem_support
  intro ⟨selected, afterCompiled⟩ supported
  cases selected with
  | none =>
      simp [honestAcceptedResult]
  | some selected =>
      rcases selected with ⟨messages, path⟩
      have hcached := honestCompiledRun_cached rounds guards (statement, salt)
        prover id (fun _ => rfl) ∅ (some (messages, path), afterCompiled)
        supported messages path rfl
      simp only [honestAcceptedResult]
      simp only [bind_pure_comp, simulateQ_map, StateT.run_map]
      rw [honestSingleSaltVerify_replay_rom guards accepts
        (statement, salt) messages path afterCompiled hcached]
      cases hacc : accepts (statement, salt) path <;>
        simp [Option.filter, hacc]

/-- The actual guarded native single-salt verifier has the same accepted-output program as
the uniform interactive protocol, for every adaptive private-coin honest strategy. -/
theorem honestSingleSaltVerifiedProgram_eq_interactive
    {Statement GlobalSalt Witness : Type}
    [DecidableEq Statement] [DecidableEq GlobalSalt] [SampleableType GlobalSalt]
    (rounds : List Round)
    (guards : GuardSchedule (Statement × GlobalSalt) PUnit rounds)
    (accepts : (Statement × GlobalSalt) → (protocol rounds).tree.ExecutionPath → Bool)
    (statement : Statement) (witness : Witness) (prover : GlobalSalt → HonestProver rounds) :
    (simulateQ (oracleSpec (Statement × GlobalSalt) PUnit rounds).romImpl
      (honestSingleSaltVerifiedProgram rounds guards accepts
        statement witness prover)).run' ∅ =
    honestInteractiveAccepted rounds guards accepts statement witness prover := by
  unfold honestSingleSaltVerifiedProgram honestInteractiveAccepted
  simp only [simulateQ_bind]
  rw [roSim.run'_liftM_bind
    (hashSpec := oracleSpec (Statement × GlobalSalt) PUnit rounds)
    (ro := (oracleSpec (Statement × GlobalSalt) PUnit rounds).randomOracle)
    (($ᵗ GlobalSalt) : ProbComp GlobalSalt)]
  apply bind_congr
  intro salt
  rw [honestCompiledVerify_eq_interactive rounds guards accepts
    statement salt witness (prover salt)]
  simp only [honestAcceptedResult, map_eq_pure_bind]

private theorem erase_withQueryLog_bind {ι : Type} {spec : OracleSpec ι}
    {α β : Type} (program : OracleComp spec α)
    (continuation : α → OracleComp spec β) :
    (program.withQueryLog >>= fun phase => continuation phase.1) =
      program >>= continuation := by
  change ((simulateQ spec.loggingOracle program).run >>= fun result =>
    continuation result.1) = program >>= continuation
  exact loggingOracle.run_simulateQ_bind_fst program continuation

/-- Erasing only the adversary-phase query log from the existing accepted execution recovers
the direct honest compiler followed by the actual native verifier. -/
theorem honestSingleSaltAccepted_erase_log
    {Statement GlobalSalt Witness : Type}
    [SampleableType GlobalSalt]
    (rounds : List Round)
    (guards : GuardSchedule (Statement × GlobalSalt) PUnit rounds)
    (accepts : (Statement × GlobalSalt) → (protocol rounds).tree.ExecutionPath → Bool)
    (statement : Statement) (witness : Witness) (prover : GlobalSalt → HonestProver rounds) :
    Prod.fst <$> honestSingleSaltAccepted rounds guards accepts
      statement witness prover =
    honestSingleSaltVerifiedProgram rounds guards accepts statement witness prover := by
  unfold honestSingleSaltAccepted
  rw [singleSaltAcceptedExecution_eq_verify]
  simp only [map_eq_pure_bind, bind_assoc]
  let finish : Option (Statement × SaltedProof GlobalSalt rounds × Witness) →
      OracleComp (unifSpec + oracleSpec (Statement × GlobalSalt) PUnit rounds)
        (Option ((Statement × GlobalSalt) ×
          (protocol rounds).tree.ExecutionPath × Witness)) := fun selected =>
    match selected with
    | none => pure none
    | some (s, (salt, messages), w) => do
        let path ← simulateQ (restorationQueries (Statement × GlobalSalt) PUnit rounds)
          (singleSaltVerify rounds guards accepts (s, salt) messages)
        pure (path.map fun p => ((s, salt), p, w))
  calc
    _ = ((honestSingleSaltAdversary rounds guards statement witness prover).withQueryLog
      >>= fun phase => finish phase.1) := by
        apply bind_congr
        intro phase
        rcases phase with ⟨selected, log⟩
        cases selected with
        | none => rfl
        | some selected =>
            rcases selected with ⟨s, ⟨salt, messages⟩, w⟩
            simp only [finish, bind_pure_comp, Functor.map_map]
    _ = honestSingleSaltAdversary rounds guards statement witness prover >>= finish :=
      erase_withQueryLog_bind _ _
    _ = honestSingleSaltVerifiedProgram rounds guards accepts statement witness prover := by
      unfold honestSingleSaltAdversary honestSingleSaltVerifiedProgram honestCompiledVerify
      simp only [bind_assoc]
      congr 1
      funext salt
      simp only [pure_bind]
      congr 1
      funext selected
      cases selected with
      | none => rfl
      | some selected =>
          rcases selected with ⟨messages, path⟩
          rfl

/-- The accepted output of the actual single-salt execution has exactly the honest
interactive distribution, after the adversary-phase log is forgotten. -/
theorem honestSingleSaltAccepted_run'_eq_interactive
    {Statement GlobalSalt Witness : Type}
    [DecidableEq Statement] [DecidableEq GlobalSalt] [SampleableType GlobalSalt]
    (rounds : List Round)
    (guards : GuardSchedule (Statement × GlobalSalt) PUnit rounds)
    (accepts : (Statement × GlobalSalt) → (protocol rounds).tree.ExecutionPath → Bool)
    (statement : Statement) (witness : Witness) (prover : GlobalSalt → HonestProver rounds) :
    Prod.fst <$> (simulateQ (oracleSpec (Statement × GlobalSalt) PUnit rounds).romImpl
      (honestSingleSaltAccepted rounds guards accepts statement witness prover)).run' ∅ =
    honestInteractiveAccepted rounds guards accepts statement witness prover := by
  have h := congrArg (fun program =>
    (simulateQ (oracleSpec (Statement × GlobalSalt) PUnit rounds).romImpl program).run' ∅)
    (honestSingleSaltAccepted_erase_log rounds guards accepts statement witness prover)
  simp only [simulateQ_map, StateT.run'_map'] at h
  exact h.trans (honestSingleSaltVerifiedProgram_eq_interactive rounds guards accepts
    statement witness prover)

/-- Projecting the actual ordered-log experiment to its accepted result yields precisely the
uniform interactive accepted-output program. This includes guard failures and subprobability. -/
theorem honestSingleSaltAccepted_logged_eq_interactive
    {Statement GlobalSalt Witness : Type}
    [DecidableEq Statement] [DecidableEq GlobalSalt] [SampleableType GlobalSalt]
    (rounds : List Round)
    (guards : GuardSchedule (Statement × GlobalSalt) PUnit rounds)
    (accepts : (Statement × GlobalSalt) → (protocol rounds).tree.ExecutionPath → Bool)
    (statement : Statement) (witness : Witness) (prover : GlobalSalt → HonestProver rounds) :
    (fun result => result.1.1.1) <$>
      randomOracleLoggedRun
        (honestSingleSaltAccepted rounds guards accepts statement witness prover) ∅ =
    honestInteractiveAccepted rounds guards accepts statement witness prover := by
  have hproj := randomOracleLoggedRun_project
    (honestSingleSaltAccepted rounds guards accepts statement witness prover)
    (∅ : (oracleSpec (Statement × GlobalSalt) PUnit rounds).QueryCache)
  have hresult := congrArg (fun computation =>
    (fun result => result.1.1) <$> computation) hproj
  simp only [Functor.map_map] at hresult
  have hrun := honestSingleSaltAccepted_run'_eq_interactive rounds guards accepts
    statement witness prover
  rw [StateT.run'_eq] at hrun
  simp only [Functor.map_map] at hrun
  simpa only [Functor.map_map, Function.comp_def] using hresult.trans hrun

/-- Every accepted-output event, including successful completion, has the same probability
in the actual native single-salt execution and the interactive uniform-challenge source. -/
theorem honestSingleSaltAccepted_event_eq_interactive
    {Statement GlobalSalt Witness : Type}
    [DecidableEq Statement] [DecidableEq GlobalSalt] [SampleableType GlobalSalt]
    (rounds : List Round)
    (guards : GuardSchedule (Statement × GlobalSalt) PUnit rounds)
    (accepts : (Statement × GlobalSalt) → (protocol rounds).tree.ExecutionPath → Bool)
    (statement : Statement) (witness : Witness) (prover : GlobalSalt → HonestProver rounds)
    (event : Option ((Statement × GlobalSalt) ×
      (protocol rounds).tree.ExecutionPath × Witness) → Prop) :
    Pr{let result ← randomOracleLoggedRun
        (honestSingleSaltAccepted rounds guards accepts statement witness prover) ∅}[
      event result.1.1.1] =
    Pr{let result ← honestInteractiveAccepted rounds guards accepts statement witness prover}[
      event result] := by
  rw [← prEvent_map]
  exact congrArg (fun program => Pr{let result ← program}[event result])
    (honestSingleSaltAccepted_logged_eq_interactive rounds guards accepts
      statement witness prover)

/-- Honest completeness transfers exactly: a source success probability, possibly below one
or from a subprobabilistic private strategy, is the native single-salt success probability. -/
theorem honestSingleSaltAccepted_completeness
    {Statement GlobalSalt Witness : Type}
    [DecidableEq Statement] [DecidableEq GlobalSalt] [SampleableType GlobalSalt]
    (rounds : List Round)
    (guards : GuardSchedule (Statement × GlobalSalt) PUnit rounds)
    (accepts : (Statement × GlobalSalt) → (protocol rounds).tree.ExecutionPath → Bool)
    (statement : Statement) (witness : Witness) (prover : GlobalSalt → HonestProver rounds) :
    Pr{let result ← randomOracleLoggedRun
        (honestSingleSaltAccepted rounds guards accepts statement witness prover) ∅}[
      result.1.1.1.isSome = true] =
    Pr{let result ← honestInteractiveAccepted rounds guards accepts statement witness prover}[
      result.isSome = true] := by
  exact honestSingleSaltAccepted_event_eq_interactive rounds guards accepts
    statement witness prover (fun selected => selected.isSome = true)

/-- The actual logged single-salt target has the same accepted-output program as the actual
guarded native interactive source, including failed guards and subprobability. -/
theorem honestSingleSaltAccepted_logged_eq_native
    {Statement GlobalSalt Witness : Type}
    [DecidableEq Statement] [DecidableEq GlobalSalt] [SampleableType GlobalSalt]
    (rounds : List Round)
    (guards : GuardSchedule (Statement × GlobalSalt) PUnit rounds)
    (accepts : (Statement × GlobalSalt) → (protocol rounds).tree.ExecutionPath → Bool)
    (statement : Statement) (witness : Witness)
    (prover : GlobalSalt → HonestProver rounds) :
    (fun result => result.1.1.1) <$>
      randomOracleLoggedRun
        (honestSingleSaltAccepted rounds guards accepts statement witness prover) ∅ =
    honestNativeInteractiveAccepted rounds guards accepts statement witness prover :=
  (honestSingleSaltAccepted_logged_eq_interactive rounds guards accepts
    statement witness prover).trans
      (honestNativeInteractiveAccepted_eq rounds guards accepts statement witness prover).symm

/-- Every accepted-result event transfers from the actual guarded native interactive source
to the actual logged single-salt target. -/
theorem honestSingleSaltAccepted_native_event
    {Statement GlobalSalt Witness : Type}
    [DecidableEq Statement] [DecidableEq GlobalSalt] [SampleableType GlobalSalt]
    (rounds : List Round)
    (guards : GuardSchedule (Statement × GlobalSalt) PUnit rounds)
    (accepts : (Statement × GlobalSalt) → (protocol rounds).tree.ExecutionPath → Bool)
    (statement : Statement) (witness : Witness)
    (prover : GlobalSalt → HonestProver rounds)
    (event : Option ((Statement × GlobalSalt) ×
      (protocol rounds).tree.ExecutionPath × Witness) → Prop) :
    Pr{let result ← randomOracleLoggedRun
        (honestSingleSaltAccepted rounds guards accepts statement witness prover) ∅}[
      event result.1.1.1] =
    Pr{let result ← honestNativeInteractiveAccepted rounds guards accepts
        statement witness prover}[event result] := by
  rw [← prEvent_map]
  exact congrArg (fun program => Pr{let result ← program}[event result])
    (honestSingleSaltAccepted_logged_eq_native rounds guards accepts
      statement witness prover)

/-- Honest completeness of the actual native guarded protocol transfers exactly to the
single-salt Fiat–Shamir execution. No losslessness or unit success probability is assumed. -/
theorem honestSingleSaltAccepted_native_completeness
    {Statement GlobalSalt Witness : Type}
    [DecidableEq Statement] [DecidableEq GlobalSalt] [SampleableType GlobalSalt]
    (rounds : List Round)
    (guards : GuardSchedule (Statement × GlobalSalt) PUnit rounds)
    (accepts : (Statement × GlobalSalt) → (protocol rounds).tree.ExecutionPath → Bool)
    (statement : Statement) (witness : Witness)
    (prover : GlobalSalt → HonestProver rounds) :
    Pr{let result ← randomOracleLoggedRun
        (honestSingleSaltAccepted rounds guards accepts statement witness prover) ∅}[
      result.1.1.1.isSome = true] =
    Pr{let result ← honestNativeInteractiveAccepted rounds guards accepts
        statement witness prover}[result.isSome = true] := by
  exact honestSingleSaltAccepted_native_event rounds guards accepts
    statement witness prover (fun selected => selected.isSome = true)

end Interaction.Oracle.FiatShamir

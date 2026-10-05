/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Interaction.Oracle.Security.Soundness
public import ArkLib.ProofSystem.Sumcheck.Interaction.ProtocolSoundness

/-!
# Native Sumcheck round-by-round soundness

The scalar state reconstructs the current claim from every concrete native prefix and retains
one fixed realized original polynomial. At a verifier prefix, the sent polynomial is already
fixed; a failed sum check produces public abort, and a successful check uses a fresh challenge.

The actual verifier satisfies this authored-prefix model after closing its declared source
queries. Native execution preserves the effectful prover response on both branches. Its valid
returned claim implies the scalar terminal state through the same path-derived closing handler.
The generic native local-to-global theorem then bounds ordinary soundness, including missing
mass from an interpreted failing prover and the zero-round false-input case.
-/

@[expose] public section

open Interaction.Oracle Interaction.Oracle.TypeTree Interaction.TwoParty
open OracleComp OracleSpec PFunctor.FreeM
open scoped ENNReal

noncomputable section

namespace Sumcheck.Interaction.Native

variable (F : Type) [Field F] (n deg : ℕ)

/-- The current scalar Sumcheck claim, together with its round. -/
private abbrev CurrentClaim := (round : Fin (n + 1)) × Spec.StatementRound F n round

/-- A sent polynomial and the claim fixed before its verifier challenge. -/
private abbrev PendingMessage := (round : Fin n) ×
  Spec.StatementRound F n round.castSucc × SingleRound.Message F deg

private structure PrefixData (tree : TypeTree) where
  claim : Option (CurrentClaim F n)
  pending : Option (PendingMessage F n deg)
  rank : ℕ
  step : Option F → ExecutionPrefix tree

private def TranscriptObserver : (tree : TypeTree) → Type 1
  | .done => PrefixData F n deg .done
  | .public Moves rest => PrefixData F n deg (.public Moves rest) ×
      ((move : Moves) → TranscriptObserver (rest move))
  | .oracle Messages rest => PrefixData F n deg (.oracle Messages rest) ×
      ((message : Messages) → TranscriptObserver (rest PUnit.unit))

private def rootData : {tree : TypeTree} → TranscriptObserver F n deg tree → PrefixData F n deg tree
  | .done, observer => observer
  | .public _ _, observer => observer.1
  | .oracle _ _, observer => observer.1

private def restrictObserver : {tree residual : TypeTree} → TranscriptObserver F n deg tree →
    (spine : Cursor.Spine tree residual) → PrefixMessages.Along spine →
    TranscriptObserver F n deg residual
  | _, _, observer, .root _, _ => observer
  | .public _ _, _, observer, .down move tail, messages =>
      restrictObserver (observer.2 move) tail messages
  | .oracle _ _, _, observer, .down _ tail, messages =>
      restrictObserver (observer.2 messages.1) tail messages.2

private def prefixData {tree : TypeTree} (observer : TranscriptObserver F n deg tree)
    (pfx : ExecutionPrefix tree) : PrefixData F n deg pfx.cursor.residual :=
  rootData F n deg (restrictObserver F n deg observer pfx.cursor.spine pfx.messages)

private theorem prefixData_root {tree : TypeTree} (observer : TranscriptObserver F n deg tree) :
    prefixData F n deg observer (.root tree) = rootData F n deg observer := rfl

private theorem prefixData_public {Moves : Type} {rest : Moves → TypeTree}
    (data : PrefixData F n deg (.public Moves rest))
    (next : (move : Moves) → TranscriptObserver F n deg (rest move))
    (move : Moves) (pfx : ExecutionPrefix (rest move)) :
    prefixData F n deg (tree := .public Moves rest) (data, next) (.prependPublic move pfx) =
      prefixData F n deg (next move) pfx := rfl

private theorem prefixData_oracle {Messages : Type} {rest : PUnit → TypeTree}
    (data : PrefixData F n deg (.oracle Messages rest))
    (next : Messages → TranscriptObserver F n deg (rest PUnit.unit))
    (message : Messages) (pfx : ExecutionPrefix (rest PUnit.unit)) :
    prefixData F n deg (tree := .oracle Messages rest) (data, next) (.prependOracle message pfx) =
      prefixData F n deg (next message) pfx := rfl

private theorem restrictObserver_comp {tree middle residual : TypeTree}
    (observer : TranscriptObserver F n deg tree) (first : Cursor.Spine tree middle)
    (second : Cursor.Spine middle residual) (left : PrefixMessages.Along first)
    (right : PrefixMessages.Along second) :
    restrictObserver F n deg observer (first.comp second)
      (PrefixMessages.comp first second left right) =
      restrictObserver F n deg (restrictObserver F n deg observer first left) second right := by
  induction first with
  | root => rfl
  | @down position next residual answer tail ih =>
    cases position with
    | «public» Moves =>
      exact ih (observer.2 answer) second left right
    | «oracle» Messages =>
      cases answer
      exact ih (observer.2 left.1) second left.2 right

private theorem prefixData_comp {tree : TypeTree} (observer : TranscriptObserver F n deg tree)
    (first : ExecutionPrefix tree) (second : ExecutionPrefix first.cursor.residual) :
    prefixData F n deg observer (first.comp second) =
      prefixData F n deg
        (restrictObserver F n deg observer first.cursor.spine first.messages) second := by
  unfold prefixData ExecutionPrefix.comp Cursor.comp
  rw [restrictObserver_comp]

set_option backward.isDefEq.respectTransparency false in
private def transcriptObserver : (count start : ℕ) → (finish : start + count = n) →
    Spec.StatementRound F n ⟨start, by omega⟩ → ℕ →
    TranscriptObserver F n deg (protocol F deg count).tree
  | 0, start, _, stmt, rank =>
      ⟨some ⟨⟨start, by omega⟩, stmt⟩, none, rank, fun _ => .root _⟩
  | count + 1, start, _, stmt, rank =>
      ⟨⟨some ⟨⟨start, by omega⟩, stmt⟩, none, rank, fun _ => .root _⟩,
        fun q =>
          ⟨⟨some ⟨⟨start, by omega⟩, stmt⟩, some ⟨⟨start, by omega⟩, stmt, q⟩, rank,
              fun challenge => ExecutionPrefix.prependPublic challenge (.root _)⟩,
            fun challenge => match challenge with
            | none => ⟨none, none, rank + 1, fun _ => .root _⟩
            | some r => transcriptObserver count (start + 1) (by omega)
                ⟨q.val.eval r, Fin.snoc stmt.challenges r⟩ (rank + 1)⟩⟩

private theorem observer_root_rank (count start : ℕ) (finish : start + count = n)
    (stmt : Spec.StatementRound F n ⟨start, by omega⟩) (rank : ℕ) :
    (rootData F n deg (transcriptObserver F n deg count start finish stmt rank)).rank = rank := by
  cases count <;> rfl

private theorem observer_root_claim (count start : ℕ) (finish : start + count = n)
    (stmt : Spec.StatementRound F n ⟨start, by omega⟩) (rank : ℕ) :
    (rootData F n deg (transcriptObserver F n deg count start finish stmt rank)).claim =
      some ⟨⟨start, by omega⟩, stmt⟩ := by
  cases count <;> rfl

variable [Fintype F] [DecidableEq F] [SampleableType F]

/-- Sample a challenge after the sum check, or produce public abort. -/
def nextChallenge {m : ℕ} (D : Fin m ↪ F) (current : F)
    (q : SingleRound.Message F deg) : ProbComp (Option F) :=
  if ((Finset.univ.map D).toList.map (fun x => q.val.eval x)).sum = current
  then some <$> ($ᵗ F) else pure none

private def samplePending {m : ℕ} (D : Fin m ↪ F)
    (pending : Option (PendingMessage F n deg)) : ProbComp (Option F) :=
  match pending with
  | none => pure none
  | some ⟨_, current, q⟩ => nextChallenge F deg D current.target q

private def modelOf {m : ℕ} (D : Fin m ↪ F) (source : Protocol)
    (observer : TranscriptObserver F n deg source.tree) :
    Interaction.Oracle.Security.ChallengeModel source where
  Result := fun _ => Option F
  sample := fun pfx => samplePending F n deg D (prefixData F n deg observer pfx).pending
  extend := fun pfx challenge => pfx.comp ((prefixData F n deg observer pfx).step challenge)

private def stateOf {m : ℕ} (D : Fin m ↪ F) {tree : TypeTree}
    (observer : TranscriptObserver F n deg tree) (p : Spec.OracleStatement F n deg ())
    (pfx : ExecutionPrefix tree) : Prop :=
  match (prefixData F n deg observer pfx).claim with
  | none => False
  | some ⟨round, current⟩ => MultivariateRound.closedRelation F n deg D round
      ⟨current, (MultivariateRound.polynomialFamily F n deg).behaviorOfRealizations (fun _ => p)⟩

private def rankOf {tree : TypeTree} (observer : TranscriptObserver F n deg tree)
    (pfx : ExecutionPrefix tree) : ℕ := (prefixData F n deg observer pfx).rank

/-- A fixed sent polynomial has false-to-true escape probability at most `deg / card F`. -/
theorem nextChallenge_local_soundness {m : ℕ} (D : Fin m ↪ F) (i : Fin n)
    (stmt : Spec.StatementRound F n i.castSucc) (p : Spec.OracleStatement F n deg ())
    (q : SingleRound.Message F deg)
    (hfalse : ¬ MultivariateRound.closedRelation F n deg D i.castSucc
      ⟨stmt, (MultivariateRound.polynomialFamily F n deg).behaviorOfRealizations (fun _ => p)⟩) :
    Pr{let challenge ← nextChallenge F deg D stmt.target q}[
      match challenge with
      | none => False
      | some r => MultivariateRound.closedRelation F n deg D i.succ
          ⟨⟨q.val.eval r, Fin.snoc stmt.challenges r⟩,
            (MultivariateRound.polynomialFamily F n deg).behaviorOfRealizations (fun _ => p)⟩] ≤
      (deg : ENNReal) / Fintype.card F := by
  unfold nextChallenge
  split
  · rw [prEvent_map]
    exact MultivariateRound.uniform_successor_soundness n deg F D i stmt p q hfalse
      (by assumption)
  · simp

open Interaction.Oracle.Security

set_option backward.isDefEq.respectTransparency false in
omit [Fintype F] [DecidableEq F] [SampleableType F] in
private theorem transcriptObserver_prover {m : ℕ} (D : Fin m ↪ F)
    (count start : ℕ) (finish : start + count = n)
    (stmt : Spec.StatementRound F n ⟨start, by omega⟩) (rank : ℕ)
    (p : Spec.OracleStatement F n deg ()) :
    ProverPreserves (protocol F deg count).tree (protocol F deg count).roles
      (stateOf F n deg D (transcriptObserver F n deg count start finish stmt rank) p) := by
  induction count generalizing start rank with
  | zero => trivial
  | succ count ih =>
    change (_ ∧ _)
    constructor
    · intro q h
      exact h
    · intro q
      change (_ ∧ _)
      constructor
      · intro h
        cases h
      · intro challenge
        cases challenge with
        | none => trivial
        | some r =>
          exact ih (start + 1) (by omega)
            ⟨q.val.eval r, Fin.snoc stmt.challenges r⟩ (rank + 1)

set_option backward.isDefEq.respectTransparency false in
omit [Fintype F] [DecidableEq F] [SampleableType F] in
private theorem transcriptObserver_schedule
    (count start : ℕ) (finish : start + count = n)
    (stmt : Spec.StatementRound F n ⟨start, by omega⟩) (rank cap : ℕ)
    (hcap : rank + count ≤ cap) :
    ChallengeSchedule (protocol F deg count).tree (protocol F deg count).roles
      (rankOf F n deg (transcriptObserver F n deg count start finish stmt rank)) cap := by
  induction count generalizing start rank with
  | zero => exact hcap
  | succ count ih =>
    change (_ ∧ _)
    constructor
    · intro q
      rfl
    · intro q
      change (_ ∧ _)
      constructor
      · constructor
        · change rank < cap
          omega
        · intro challenge
          cases challenge
          · rfl
          · change (rootData F n deg (transcriptObserver F n deg count (start + 1)
              (by omega) ⟨q.val.eval _, Fin.snoc stmt.challenges _⟩ (rank + 1))).rank = rank + 1
            exact observer_root_rank F n deg _ _ _ _ _
      · intro challenge
        cases challenge with
        | none => change rank + 1 ≤ cap
                  omega
        | some r =>
          exact ih (start + 1) (by omega)
            ⟨q.val.eval r, Fin.snoc stmt.challenges r⟩ (rank + 1) (by omega)

private def rootBound {m : ℕ} (D : Fin m ↪ F) {tree : TypeTree}
    (observer : TranscriptObserver F n deg tree) (p : Spec.OracleStatement F n deg ()) : Prop :=
  Pr{let challenge ← samplePending F n deg D (rootData F n deg observer).pending}[
    ¬ stateOf F n deg D observer p (.root tree) ∧
      stateOf F n deg D observer p ((rootData F n deg observer).step challenge)] ≤
        (deg : ENNReal) / Fintype.card F

private def LocalCertificate {m : ℕ} (D : Fin m ↪ F) (p : Spec.OracleStatement F n deg ()) :
    (tree : TypeTree) → tree.RoleDecoration → TranscriptObserver F n deg tree → Prop
  | .done, _, _ => True
  | .public _ rest, roles, observer =>
      (roles.1 = .receiver → rootBound F n deg D observer p) ∧
      ∀ move, LocalCertificate D p (rest move) (roles.2 move) (observer.2 move)
  | .oracle _ rest, roles, observer =>
      ∀ message, LocalCertificate D p (rest PUnit.unit) (roles.2 PUnit.unit) (observer.2 message)

private theorem localCertificate_restrict {m : ℕ} (D : Fin m ↪ F)
    (p : Spec.OracleStatement F n deg ()) {tree residual : TypeTree}
    (roles : tree.RoleDecoration) (observer : TranscriptObserver F n deg tree)
    (cert : LocalCertificate F n deg D p tree roles observer)
    (spine : Cursor.Spine tree residual) (messages : PrefixMessages.Along spine) :
    LocalCertificate F n deg D p residual (Displayed.Decoration.restrict ⟨residual, spine⟩ roles)
      (restrictObserver F n deg observer spine messages) := by
  induction spine with
  | root => exact cert
  | @down position next residual answer tail ih =>
    cases position with
    | «public» Moves => exact ih (roles.2 answer) (observer.2 answer) (cert.2 answer) messages
    | «oracle» Messages =>
      cases answer
      exact ih (roles.2 PUnit.unit) (observer.2 messages.1) (cert messages.1) messages.2

private theorem localCertificate_root {m : ℕ} (D : Fin m ↪ F)
    (p : Spec.OracleStatement F n deg ()) {tree : TypeTree}
    (roles : tree.RoleDecoration) (observer : TranscriptObserver F n deg tree)
    (cert : LocalCertificate F n deg D p tree roles observer) (hturn : IsVerifierRoot tree roles) :
    rootBound F n deg D observer p := by
  cases tree with
  | done => cases hturn
  | «public» Moves rest => exact cert.1 hturn
  | «oracle» Messages rest => cases hturn

private theorem localCertificate_bound {m : ℕ} (D : Fin m ↪ F)
    (p : Spec.OracleStatement F n deg ()) (source : Protocol)
    (observer : TranscriptObserver F n deg source.tree)
    (cert : LocalCertificate F n deg D p source.tree source.roles observer)
    (rank : ExecutionPrefix source.tree → ℕ) :
    LocalSoundness (modelOf F n deg D source observer) (stateOf F n deg D observer p) rank
      (fun _ => (deg : ENNReal) / Fintype.card F) := by
  apply (RoundByRound.GameFamily.isBounded_iff _ _).mpr
  intro pfx _
  have hc := localCertificate_restrict F n deg D p source.roles observer cert
    pfx.val.cursor.spine pfx.val.messages
  have hb := localCertificate_root F n deg D p _ _ hc pfx.property
  change Pr{let challenge ← samplePending F n deg D (prefixData F n deg observer pfx.val).pending}[
    ¬ stateOf F n deg D observer p pfx.val ∧
      stateOf F n deg D observer p
        (pfx.val.comp ((prefixData F n deg observer pfx.val).step challenge))] ≤ _
  unfold rootBound at hb
  simp only [stateOf, prefixData_comp, prefixData_root] at hb ⊢
  exact hb

set_option backward.isDefEq.respectTransparency false in
private theorem transcriptObserver_local {m : ℕ} (D : Fin m ↪ F)
    (count start : ℕ) (finish : start + count = n)
    (stmt : Spec.StatementRound F n ⟨start, by omega⟩) (rank : ℕ)
    (p : Spec.OracleStatement F n deg ()) :
    LocalCertificate F n deg D p (protocol F deg count).tree (protocol F deg count).roles
      (transcriptObserver F n deg count start finish stmt rank) := by
  induction count generalizing start rank with
  | zero => trivial
  | succ count ih =>
    intro q
    constructor
    · intro _
      unfold rootBound
      by_cases hfalse : ¬ MultivariateRound.closedRelation F n deg D ⟨start, by omega⟩
        ⟨stmt, (MultivariateRound.polynomialFamily F n deg).behaviorOfRealizations (fun _ => p)⟩
      · have h := nextChallenge_local_soundness F n deg D ⟨start, by omega⟩ stmt p q hfalse
        apply le_trans _ h
        apply prEvent_mono
        intro challenge hevent
        cases challenge with
        | none => exact hevent.2
        | some r =>
          have hs := hevent.2
          change stateOf F n deg D (transcriptObserver F n deg count (start + 1) (by omega)
            ⟨q.val.eval r, Fin.snoc stmt.challenges r⟩ (rank + 1)) p (.root _) at hs
          simpa only [stateOf, prefixData_root, observer_root_claim, Fin.succ,
            Nat.succ_eq_add_one] using hs
      · have htrue := Classical.not_not.mp hfalse
        simp only [stateOf, prefixData_root, transcriptObserver, rootData, htrue,
          not_true_eq_false, false_and, prEvent_false, zero_le]
    · intro challenge
      cases challenge with
      | none => trivial
      | some r =>
        exact ih (start + 1) (by omega)
          ⟨q.val.eval r, Fin.snoc stmt.challenges r⟩ (rank + 1)

universe v

set_option backward.isDefEq.respectTransparency false in
omit [Fintype F] in
private theorem fresh_prependPublic {m₀ : ℕ} (D : Fin m₀ ↪ F)
    {Moves : Type} {rest : Moves → TypeTree}
    (roles : (.public Moves rest : TypeTree).RoleDecoration)
    (oracles : (.public Moves rest : TypeTree).OracleDecoration)
    (data : PrefixData F n deg (.public Moves rest))
    (next : (move : Moves) → TranscriptObserver F n deg (rest move)) (move : Moves)
    {ι : Type} (ambient : OracleSpec ι) {m : Type → Type v}
    [Monad m] [EvalDistSemantics m] [MonadAttach m] (handler : QueryImpl ambient m)
    (tree : TypeTree) (nativeRoles : tree.RoleDecoration) (nativeOracles : tree.OracleDecoration)
    (initial : PFunctor) (impl : QueryImpl (ofPFunctor initial) Id)
    (OutV : tree.BranchPath → Type)
    (native : Verifier.Strategy ambient tree nativeRoles nativeOracles initial OutV)
    (embed : ExecutionPrefix tree → ExecutionPrefix (rest move))
    (fresh : FreshVerifier
      (modelOf F n deg D ⟨rest move, roles.2 move, oracles.2 move⟩ (next move))
      ambient handler tree nativeRoles nativeOracles initial impl OutV native embed) :
    FreshVerifier (modelOf F n deg D ⟨.public Moves rest, roles, oracles⟩ (data, next))
      ambient handler tree nativeRoles nativeOracles initial impl OutV native
      (fun pfx => .prependPublic move (embed pfx)) := by
  refine FreshVerifier.mapPrefixes
    (modelOf F n deg D ⟨rest move, roles.2 move, oracles.2 move⟩ (next move))
    (modelOf F n deg D ⟨.public Moves rest, roles, oracles⟩ (data, next))
    (ExecutionPrefix.prependPublic move) ?_ (fun _ result => result) ?_ ?_
    ambient handler tree nativeRoles nativeOracles initial impl OutV native embed fresh
  · intro pfx hturn
    exact hturn
  · intro pfx _ event
    simp only [modelOf, prefixData_public]
  · intro pfx _ result
    simp only [modelOf, prefixData_public, ExecutionPrefix.prependPublic_comp]

set_option backward.isDefEq.respectTransparency false in
omit [Fintype F] in
private theorem fresh_prependOracle {m₀ : ℕ} (D : Fin m₀ ↪ F)
    {Messages : Type} {rest : PUnit → TypeTree}
    (roles : (.oracle Messages rest : TypeTree).RoleDecoration)
    (oracles : (.oracle Messages rest : TypeTree).OracleDecoration)
    (data : PrefixData F n deg (.oracle Messages rest))
    (next : Messages → TranscriptObserver F n deg (rest PUnit.unit)) (message : Messages)
    {ι : Type} (ambient : OracleSpec ι) {m : Type → Type v}
    [Monad m] [EvalDistSemantics m] [MonadAttach m] (handler : QueryImpl ambient m)
    (tree : TypeTree) (nativeRoles : tree.RoleDecoration) (nativeOracles : tree.OracleDecoration)
    (initial : PFunctor) (impl : QueryImpl (ofPFunctor initial) Id)
    (OutV : tree.BranchPath → Type)
    (native : Verifier.Strategy ambient tree nativeRoles nativeOracles initial OutV)
    (embed : ExecutionPrefix tree → ExecutionPrefix (rest PUnit.unit))
    (fresh : FreshVerifier
      (modelOf F n deg D ⟨rest PUnit.unit, roles.2 PUnit.unit, oracles.2 PUnit.unit⟩ (next message))
      ambient handler tree nativeRoles nativeOracles initial impl OutV native embed) :
    FreshVerifier (modelOf F n deg D ⟨.oracle Messages rest, roles, oracles⟩ (data, next))
      ambient handler tree nativeRoles nativeOracles initial impl OutV native
      (fun pfx => .prependOracle message (embed pfx)) := by
  refine FreshVerifier.mapPrefixes
    (modelOf F n deg D ⟨rest PUnit.unit, roles.2 PUnit.unit, oracles.2 PUnit.unit⟩ (next message))
    (modelOf F n deg D ⟨.oracle Messages rest, roles, oracles⟩ (data, next))
    (ExecutionPrefix.prependOracle message) ?_ (fun _ result => result) ?_ ?_
    ambient handler tree nativeRoles nativeOracles initial impl OutV native embed fresh
  · intro pfx hturn
    exact hturn
  · intro pfx _ event
    simp only [modelOf, prefixData_oracle]
  · intro pfx _ result
    simp only [modelOf, prefixData_oracle, ExecutionPrefix.prependOracle_comp]

set_option backward.isDefEq.respectTransparency false in
omit [Fintype F] in
private theorem transcriptObserver_fresh {m₀ : ℕ} (D : Fin m₀ ↪ F)
    {ι : Type} (ambient : OracleSpec ι) {m : Type → Type v}
    [Monad m] [LawfulMonad m] [EvalDistSemantics m] [LawfulEvalDistSemantics m]
    [MonadAttach m] [ExactMonadAttach m] (handler : QueryImpl ambient m)
    (challenge : OracleComp ambient F)
    (hchallenge : ∀ event : F → Prop,
      Pr{let r ← simulateQ handler challenge}[event r] = Pr{let r ← ($ᵗ F)}[event r])
    (count start : ℕ) (finish : start + count = n)
    (stmt : Spec.StatementRound F n ⟨start, by omega⟩) (rank : ℕ)
    (A : PFunctor)
    (originalOracle : VirtualOracle (ofPFunctor A) (MultivariateRound.polynomialFamily F n deg))
    (impl : QueryImpl (ofPFunctor A) Id) :
    FreshVerifier (modelOf F n deg D (protocol F deg count)
      (transcriptObserver F n deg count start finish stmt rank)) ambient handler
      (protocol F deg count).tree (protocol F deg count).roles (protocol F deg count).oracles
      A impl _
      (verifier F n deg ambient challenge (Finset.univ.map D).toList
        count start finish A originalOracle stmt) id := by
  induction count generalizing start rank A with
  | zero => trivial
  | succ count ih =>
    intro q next hnext
    dsimp only [protocol, Core.protocol, Protocol.oracleWith_oracles] at hnext
    simp only [verifier, Core.verifier, simulateQ_bind, simulateQ_pure,
      Core.simulate_latestSum] at hnext
    simp only [LawfulMonad.pure_bind] at hnext
    rw [mem_support_pure_iff] at hnext
    subst next
    apply fresh_prependOracle F n deg D _ _ _ _ q ambient handler _ _ _ _ _ _ _ id
    constructor
    · rfl
    · constructor
      · refine ⟨id, ?_, ?_⟩
        · intro event
          dsimp only [protocol, Core.protocol, Protocol.oracleWith_oracles]
          dsimp only [modelOf, prefixData, ExecutionPrefix.root, Cursor.root,
            restrictObserver, rootData, id]
          simp only [samplePending, nextChallenge]
          split
          · simp only [simulateQ_bind, simulateQ_pure]
            rw [QueryImpl.simulateQ_liftComp_left_eq_of_apply _ (QueryImpl.id' ambient)
              (fun _ => rfl), simulateQ_id']
            simp only [Core.simulate_latest, LawfulMonad.pure_bind,
              simulateQ_pure, bind_assoc]
            change Pr{let r ← simulateQ handler challenge}[event (some r)] =
              Pr{let result ← (some <$> ($ᵗ F))}[event result]
            rw [prEvent_map]
            exact hchallenge (fun r => event (some r))
          · simp only [simulateQ_pure, LawfulMonad.pure_bind, evalDist_pure]
        · intro move
          rfl
      · intro chosen hchosen
        dsimp only [protocol, Core.protocol, Protocol.oracleWith_oracles] at hchosen
        split at hchosen
        · simp only [simulateQ_bind, simulateQ_pure] at hchosen
          rw [QueryImpl.simulateQ_liftComp_left_eq_of_apply _ (QueryImpl.id' ambient)
            (fun _ => rfl), simulateQ_id'] at hchosen
          simp only [Core.simulate_latest, LawfulMonad.pure_bind,
            simulateQ_pure] at hchosen
          obtain ⟨r, _, heq⟩ := (mem_support_bind_iff _ _ _).mp hchosen
          rw [mem_support_pure_iff] at heq
          subst chosen
          apply fresh_prependPublic F n deg D _ _ _ _ (some r) ambient handler _ _ _ _ _ _ _ id
          exact ih (start + 1) (by omega) ⟨q.val.eval r, Fin.snoc stmt.challenges r⟩ (rank + 1)
            (Access.extend A (SingleRound.polynomialInterface F deg))
            (originalOracle.sumWeaken (SingleRound.polynomialInterface F deg).spec)
            (Access.extendImpl A (SingleRound.polynomialInterface F deg) impl q)
        · simp only [simulateQ_pure, mem_support_pure_iff] at hchosen
          subst chosen
          trivial

set_option backward.isDefEq.respectTransparency false in
omit [Fintype F] [SampleableType F] in
private theorem executeStrategies_succ {ι : Type} (ambient : OracleSpec ι)
    (challenge : OracleComp ambient F) (domain : List F)
    (count start : ℕ) (finish : start + (count + 1) = n) (A : PFunctor)
    (originalOracle : VirtualOracle (ofPFunctor A) (MultivariateRound.polynomialFamily F n deg))
    (stmt : Spec.StatementRound F n ⟨start, by omega⟩) (impl : QueryImpl (ofPFunctor A) Id)
    (prover : Prover.Strategy ambient (protocol F deg (count + 1)).tree
      (protocol F deg (count + 1)).roles (fun _ => Unit)) :
    executeStrategies ambient (protocol F deg (count + 1)).tree
      (protocol F deg (count + 1)).roles (protocol F deg (count + 1)).oracles A impl prover
      (verifier F n deg ambient challenge domain (count + 1) start finish A originalOracle stmt) =
      (do
        let chosen ← prover
        if (domain.map (fun x => chosen.1.val.eval x)).sum = stmt.target then
          let r ← challenge
          let next ← chosen.2 (some r)
          let result ← executeStrategies ambient (protocol F deg count).tree
            (protocol F deg count).roles (protocol F deg count).oracles
            (Access.extend A (SingleRound.polynomialInterface F deg))
            (Access.extendImpl A (SingleRound.polynomialInterface F deg) impl chosen.1)
            (OutP := fun _ => Unit) next
            (verifier F n deg ambient challenge domain count (start + 1) (by omega)
              (Access.extend A (SingleRound.polynomialInterface F deg))
              (originalOracle.sumWeaken (SingleRound.polynomialInterface F deg).spec)
              ⟨chosen.1.val.eval r, Fin.snoc stmt.challenges r⟩)
          return ⟨⟨chosen.1, ⟨some r, result.1⟩⟩, result.2.1, by
            change TerminalClaim (protocol F deg count)
              (Access.extend A (SingleRound.polynomialInterface F deg))
              (fun _ => FinalStatement F n) (fun _ => MultivariateRound.polynomialFamily F n deg)
              result.1.toBranchPath
            exact result.2.2⟩
        else
          let next ← chosen.2 none
          return ⟨⟨chosen.1, ⟨none, PUnit.unit⟩⟩, next, none⟩) := by
  dsimp only [protocol, Core.protocol, Protocol.oracleWith_tree, Protocol.oracleWith_roles,
    Protocol.oracleWith_oracles, Protocol.public_tree, Protocol.public_roles,
    Protocol.public_oracles]
  rw [executeStrategies_oracle]
  simp only [verifier, Core.verifier, simulateQ_bind, simulateQ_pure]
  dsimp only [protocol, Core.protocol, Protocol.oracleWith_oracles]
  simp only [Core.simulate_latestSum, LawfulMonad.pure_bind]
  congr 1
  funext chosen
  rw [executeStrategies_public_receiver]
  split
  · simp only [simulateQ_bind, simulateQ_pure]
    rw [QueryImpl.simulateQ_liftComp_left_eq_of_apply _ (QueryImpl.id' ambient)
      (fun _ => rfl), simulateQ_id']
    simp only [Core.simulate_latest, LawfulMonad.pure_bind, bind_assoc]
    rfl
  · simp only [simulateQ_pure, LawfulMonad.pure_bind]
    dsimp only [Protocol.done_tree, Protocol.done_roles, Protocol.done_oracles]
    simp only [bind_assoc]
    congr 1

private def closeExecution (count : ℕ) (A : PFunctor) (impl : QueryImpl (ofPFunctor A) Id)
    (result : (path : (protocol F deg count).tree.ExecutionPath) × Unit ×
      TerminalClaim (protocol F deg count) A (fun _ => FinalStatement F n)
        (fun _ => MultivariateRound.polynomialFamily F n deg) path.toBranchPath) :
    Option (ClosedClaim (FinalStatement F n) (MultivariateRound.polynomialFamily F n deg)) :=
  result.2.2.map (fun claim =>
    claim.closeWith (result.1.closingImpl (protocol F deg count).oracles A impl))

set_option backward.isDefEq.respectTransparency false in
omit [Fintype F] [SampleableType F] in
private theorem executeStrategies_terminal {m₀ : ℕ} (D : Fin m₀ ↪ F)
    {ι : Type} (ambient : OracleSpec ι) {m : Type → Type v}
    [Monad m] [LawfulMonad m] [EvalDistSemantics m] [LawfulEvalDistSemantics m]
    [MonadAttach m] [ExactMonadAttach m] (handler : QueryImpl ambient m)
    (challenge : OracleComp ambient F) (domain : List F)
    (count start : ℕ) (finish : start + count = n)
    (stmt : Spec.StatementRound F n ⟨start, by omega⟩) (rank : ℕ) (A : PFunctor)
    (originalOracle : VirtualOracle (ofPFunctor A) (MultivariateRound.polynomialFamily F n deg))
    (impl : QueryImpl (ofPFunctor A) Id)
    (prover : Prover.Strategy ambient (protocol F deg count).tree
      (protocol F deg count).roles (fun _ => Unit)) (p : Spec.OracleStatement F n deg ())
    (horiginal : originalOracle.eval impl =
      (MultivariateRound.polynomialFamily F n deg).behaviorOfRealizations (fun _ => p))
    (result : (path : (protocol F deg count).tree.ExecutionPath) × Unit ×
      TerminalClaim (protocol F deg count) A (fun _ => FinalStatement F n)
        (fun _ => MultivariateRound.polynomialFamily F n deg) path.toBranchPath)
    (hrun : result ∈ support (simulateQ handler
      (executeStrategies ambient (protocol F deg count).tree (protocol F deg count).roles
        (protocol F deg count).oracles A impl prover
        (verifier F n deg ambient challenge domain count start finish A originalOracle stmt))))
    (hvalid : (closeExecution F n deg count A impl result).map (outputRelation F n deg) =
      some True) :
    stateOf F n deg D (transcriptObserver F n deg count start finish stmt rank) p
      (.ofExecutionPath result.1) := by
  induction count generalizing start rank A with
  | zero =>
    simp only [Nat.add_zero] at finish
    subst n
    dsimp only [protocol, Core.protocol, Protocol.done_tree, Protocol.done_roles,
      Protocol.done_oracles] at hrun
    rw [executeStrategies_done] at hrun
    simp only [verifier, Core.verifier, simulateQ_pure,
      LawfulMonad.pure_bind] at hrun
    rw [mem_support_pure_iff] at hrun
    subst result
    have hrel := (MultivariateRound.closedRelation_last_iff F start deg D
      ⟨stmt, originalOracle.eval impl⟩).mpr
    change MultivariateRound.closedRelation F start deg D (Fin.last start)
      ⟨stmt, (MultivariateRound.polynomialFamily F start deg).behaviorOfRealizations (fun _ => p)⟩
    rw [← horiginal]
    apply hrel
    simpa [closeExecution, outputRelation, Core.outputRelation, OpenClaim.closeWith] using hvalid
  | succ count ih =>
    rw [executeStrategies_succ] at hrun
    simp only [simulateQ_bind] at hrun
    obtain ⟨chosen, _, htail⟩ := (mem_support_bind_iff _ _ _).mp hrun
    split at htail
    · simp only [simulateQ_bind, simulateQ_pure] at htail
      obtain ⟨r, _, htail⟩ := (mem_support_bind_iff _ _ _).mp htail
      obtain ⟨next, _, htail⟩ := (mem_support_bind_iff _ _ _).mp htail
      obtain ⟨suffix, hsuffix, heq⟩ := (mem_support_bind_iff _ _ _).mp htail
      rw [mem_support_pure_iff] at heq
      subst result
      have hb := ih (start + 1) (by omega) ⟨chosen.1.val.eval r, Fin.snoc stmt.challenges r⟩
        (rank + 1) (Access.extend A (SingleRound.polynomialInterface F deg))
        (originalOracle.sumWeaken (SingleRound.polynomialInterface F deg).spec)
        (Access.extendImpl A (SingleRound.polynomialInterface F deg) impl chosen.1) next
        ((VirtualOracle.eval_sumWeaken_extendImpl A originalOracle
          (SingleRound.polynomialInterface F deg) impl chosen.1).trans horiginal) suffix hsuffix
      change stateOf F n deg D (transcriptObserver F n deg count (start + 1) (by omega)
        ⟨chosen.1.val.eval r, Fin.snoc stmt.challenges r⟩ (rank + 1)) p
          (.ofExecutionPath suffix.1)
      apply hb
      change (closeExecution F n deg count
        (Access.extend A (SingleRound.polynomialInterface F deg))
        (Access.extendImpl A (SingleRound.polynomialInterface F deg) impl chosen.1) suffix).map
          (outputRelation F n deg) = some True at hvalid
      exact hvalid
    · simp only [simulateQ_bind, simulateQ_pure] at htail
      obtain ⟨next, _, heq⟩ := (mem_support_bind_iff _ _ _).mp htail
      rw [mem_support_pure_iff] at heq
      subst result
      simp only [closeExecution, Option.map_none] at hvalid
      cases hvalid

set_option backward.isDefEq.respectTransparency false in
omit [Fintype F] [SampleableType F] in
private theorem execute_eq_closeExecution {ι : Type} (ambient : OracleSpec ι)
    (challenge : OracleComp ambient F) (domain : List F)
    (count start : ℕ) (finish : start + count = n) (A : PFunctor)
    (originalOracle : VirtualOracle (ofPFunctor A) (MultivariateRound.polynomialFamily F n deg))
    (stmt : Spec.StatementRound F n ⟨start, by omega⟩) (impl : QueryImpl (ofPFunctor A) Id)
    (prover : Prover.Strategy ambient (protocol F deg count).tree
      (protocol F deg count).roles (fun _ => Unit)) :
    execute F n deg ambient challenge domain count start finish A originalOracle stmt impl prover =
      closeExecution F n deg count A impl <$>
        executeStrategies ambient (protocol F deg count).tree (protocol F deg count).roles
          (protocol F deg count).oracles A impl prover
          (verifier F n deg ambient challenge domain count start finish A originalOracle stmt) := by
  simp only [execute, Core.execute, executeStrategiesCore, map_eq_bind_pure_comp,
    bind_assoc]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The actual optional native Sumcheck output is valid with probability at most
`count * deg / Fintype.card F` for a false input, by generic round-by-round soundness.

The ambient interpreter may lose probability mass. The original polynomial remains fixed,
and each interpreted challenge has uniform event marginals. The arbitrary native prover's
private effects and its responses to both continuing and aborting public moves are preserved.
The proof uses the ordinary scalar state, whose initial law only needs the false input claim;
this covers the zero-round case as well. -/
theorem roundByRound_soundness {m₀ : ℕ} (D : Fin m₀ ↪ F)
    {ι : Type} (ambient : OracleSpec ι) {m : Type → Type v}
    [Monad m] [LawfulMonad m] [EvalDistSemantics m] [LawfulEvalDistSemantics m]
    [MonadAttach m] [ExactMonadAttach m] (handler : QueryImpl ambient m)
    (challenge : OracleComp ambient F)
    (hchallenge : ∀ event : F → Prop,
      Pr{let r ← simulateQ handler challenge}[event r] = Pr{let r ← ($ᵗ F)}[event r])
    (count start : ℕ) (finish : start + count = n)
    (A : PFunctor)
    (originalOracle : VirtualOracle (ofPFunctor A) (MultivariateRound.polynomialFamily F n deg))
    (stmt : Spec.StatementRound F n ⟨start, by omega⟩) (impl : QueryImpl (ofPFunctor A) Id)
    (prover : Prover.Strategy ambient (protocol F deg count).tree
      (protocol F deg count).roles (fun _ => Unit)) (p : Spec.OracleStatement F n deg ())
    (horiginal : originalOracle.eval impl =
      (MultivariateRound.polynomialFamily F n deg).behaviorOfRealizations (fun _ => p))
    (hfalse : ¬ MultivariateRound.closedRelation F n deg D ⟨start, by omega⟩
      ⟨stmt, originalOracle.eval impl⟩) :
    Pr{let result ← (simulateQ handler
      (execute F n deg ambient challenge (Finset.univ.map D).toList
        count start finish A originalOracle stmt impl prover))}[
      result.map (outputRelation F n deg) = some True] ≤
        (count : ENNReal) * deg / Fintype.card F := by
  let observer := transcriptObserver F n deg count start finish stmt 0
  let state := stateOf F n deg D observer p
  let rank := rankOf F n deg observer
  let certificate : OrdinaryState (protocol F deg count)
      (MultivariateRound.closedRelation F n deg D ⟨start, by omega⟩
        ⟨stmt, originalOracle.eval impl⟩) (fun path => state (.ofExecutionPath path)) :=
    { state := state
      initial := by
        intro hfalse hstate
        apply hfalse
        change stateOf F n deg D observer p (.root _) at hstate
        dsimp only [observer] at hstate
        simpa only [stateOf, prefixData_root, observer_root_claim, ← horiginal] using hstate
      prover := transcriptObserver_prover F n deg D count start finish stmt 0 p
      terminal := fun _ h => h }
  have hlocal : LocalSoundness (modelOf F n deg D (protocol F deg count) observer)
      certificate.state rank (fun _ => (deg : ENNReal) / Fintype.card F) :=
    localCertificate_bound F n deg D p (protocol F deg count) observer
      (transcriptObserver_local F n deg D count start finish stmt 0 p) rank
  have bound := executeStrategies_soundness_uniform ambient handler certificate
    (modelOf F n deg D (protocol F deg count) observer) rank
    ((deg : ENNReal) / Fintype.card F) count
    (observer_root_rank F n deg count start finish stmt 0)
    (transcriptObserver_schedule F n deg count start finish stmt 0 count (by omega))
    (fun _ => hlocal)
    A impl prover
    (verifier F n deg ambient challenge (Finset.univ.map D).toList count start finish A
      originalOracle stmt)
    (transcriptObserver_fresh F n deg D ambient handler challenge hchallenge
      count start finish stmt 0 A originalOracle impl) hfalse
  rw [execute_eq_closeExecution, simulateQ_map, prEvent_map]
  apply le_trans _ (by simpa only [mul_div_assoc] using bound)
  apply _root_.prEvent_mono_of_support
  intro result hrun hvalid
  exact executeStrategies_terminal F n deg D ambient handler challenge (Finset.univ.map D).toList
    count start finish stmt 0 A originalOracle impl prover p horiginal result hrun hvalid

end Sumcheck.Interaction.Native

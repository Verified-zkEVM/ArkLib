/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
module
public import ArkLib.ProofSystem.Sumcheck.Interaction.Computable
public import ArkLib.ToCompPoly.Univariate.ArithmeticHorner
public import ArkLib.ProofSystem.Sumcheck.Impl.ArithmeticVerifierChecks
public import ArkLib.Interaction.Oracle.LoggedExecution
public import ArkLib.ToMathlib.Control.WriterT
-- The proof unfolds the existing runner; its runtime remains owned by LoggedExecution.
import all ArkLib.Interaction.Oracle.LoggedExecution

/-!
# Actual native Sumcheck verifier resource observations

The census folds the existing execution path, retaining the canonical coefficient arrays and
stopping at public abort. Its source-opening count is proved against the existing logged runner,
not a separate verifier or an assumed message kernel. Authentication preserves the same path and
private prover effects. The terminal action's raw trace remains the actual original view-query
trace: one logical invocation can open zero, one or many source entries.

Per-opening and domain-sum profiles consume the same seeded Horner and sum/check kernels selected
by the verifier. Counts exclude original-view reconstruction/backend work, source-view fanout,
prover computations, allocations and machine operations. Challenge counts are invocations of the
supplied verifier draw program; arbitrary draw programs and malicious provers can make additional
ambient queries. No generic bound on their total sampling queries or losslessness is asserted.
-/

@[expose] public section
open Interaction.Oracle OracleComp OracleSpec CompPoly
namespace Sumcheck.Interaction.Computable.Resources
variable {R : Type} [CommSemiring R]

/-- Native verifier local work on a completed path, excluding source-view/backend work. -/
structure Usage where
  /-- Openings of the latest coefficient message, including repeated points. -/
  messageQueries : Nat := 0
  /-- Additions in the declared two-point round sums, including the final + 0. -/
  sumAdds : Nat := 0
  /-- Comparisons against the incoming claim, one per reached round. -/
  roundComparisons : Nat := 0
  /-- Invocations of the supplied native challenge program, one per passed check. -/
  roundSamples : Nat := 0
  /-- Logical original-view invocations after every round passed, even if authentication rejects. -/
  terminalQueries : Nat := 0
  /-- Comparisons made after the original-view answer. -/
  terminalComparisons : Nat := 0
  /-- Stored canonical coefficients read by the latest-message Horner calls. -/
  coefficientReads : Nat := 0
  /-- Multiplications made by those latest-message Horner calls. -/
  hornerMuls : Nat := 0
  /-- Additions made by those latest-message Horner calls. -/
  hornerAdds : Nat := 0
  deriving BEq, Repr

/-- Add sequential native-local observations coordinatewise. -/
def plus (a b : Usage) : Usage :=
  ⟨a.messageQueries + b.messageQueries, a.sumAdds + b.sumAdds,
   a.roundComparisons + b.roundComparisons, a.roundSamples + b.roundSamples,
   a.terminalQueries + b.terminalQueries, a.terminalComparisons + b.terminalComparisons,
   a.coefficientReads + b.coefficientReads, a.hornerMuls + b.hornerMuls,
   a.hornerAdds + b.hornerAdds⟩

/-- One reached round reads two Boolean points and, only after passing, its sampled point. -/
def roundUsage (length : Nat) (passed : Bool) : Usage :=
  let queries := if passed then 3 else 2
  { messageQueries := queries, sumAdds := 2, roundComparisons := 1,
    roundSamples := if passed then 1 else 0,
    coefficientReads := queries * length, hornerMuls := queries * (length - 1),
    hornerAdds := queries * (length - 1) }

/-- Fold actual retained messages and public moves; public abort ends the census. -/
def pathUsage (deg : Nat) : (count : Nat) → (protocol R deg count).tree.ExecutionPath → Usage
  | 0, _ => { terminalQueries := 1, terminalComparisons := 1 }
  | count + 1, ⟨message, ⟨choice, rest⟩⟩ =>
    match choice with
    | none => roundUsage message.val.val.size false
    | some _ => plus (roundUsage message.val.val.size true) (pathUsage deg count rest)

private def extendLabel {deg : Nat} (A : PFunctor) (old : A.A → Bool) :
    (Access.extend A (Native.Core.messageInterface R
      (Impl.Representation.Message R deg) (Impl.Representation.evaluate R deg))).A →
      Bool
  | .inl q => old q
  | .inr _ => true

/-- Mark all native message slots while retaining the caller's classification of initial slots. -/
@[no_expose] def messageLabel (deg : Nat) : (count : Nat) → (A : PFunctor) → (old : A.A → Bool) →
    (path : (protocol R deg count).tree.ExecutionPath) →
    (TypeTree.accessAfter (protocol R deg count).tree (protocol R deg count).oracles A
      path.toBranchPath).A → Bool
  | 0, _, old, _ => old
  | count + 1, A, old, ⟨_, ⟨choice, rest⟩⟩ =>
    match choice with
    | none => extendLabel A old
    | some _ => messageLabel deg count
        (Access.extend A (Native.Core.messageInterface R
          (Impl.Representation.Message R deg) (Impl.Representation.evaluate R deg)))
        (extendLabel A old) rest

/-- Routing earlier entries does not turn them into openings of a newly sent native message. -/
theorem messageLabel_routeEntry (deg count : Nat) (A : PFunctor) (old : A.A → Bool)
    (path : (protocol R deg count).tree.ExecutionPath)
    (entry : (q : A.A) × A.B q) :
    messageLabel deg count A old path
      (TypeTree.routeEntry (protocol R deg count).tree (protocol R deg count).oracles A
        path.toBranchPath entry).1 = old entry.1 := by
  induction count generalizing A with
  | zero => rfl
  | succ count ih =>
    rcases path with ⟨message, ⟨choice, rest⟩⟩
    cases choice with
    | none => rfl
    | some r =>
      exact ih _ (extendLabel A old) rest ⟨.inl entry.1, entry.2⟩

set_option backward.isDefEq.respectTransparency false in
private theorem logged_latest {deg : Nat} {ι : Type}
    (ambient : OracleSpec ι) (A : PFunctor) (impl : QueryImpl (ofPFunctor A) Id)
    (q : Impl.Representation.Message R deg) (x : R) :
    (simulateQ (Verifier.loggedLiftAccessImpl ambient
      (Access.extend A (Native.Core.messageInterface R
        (Impl.Representation.Message R deg) (Impl.Representation.evaluate R deg)))
      (Access.extendImpl A (Native.Core.messageInterface R
        (Impl.Representation.Message R deg) (Impl.Representation.evaluate R deg))
        impl q))
      (Native.Core.latest R (Impl.Representation.Message R deg)
        (Impl.Representation.evaluate R deg) ambient A x)).run =
      pure (Impl.Representation.evaluate R deg q x,
        [⟨.inr x, Impl.Representation.evaluate R deg q x⟩]) := by
  have h := simulateQ_spec_query (impl := Verifier.loggedLiftAccessImpl ambient
      (Access.extend A (Native.Core.messageInterface R
        (Impl.Representation.Message R deg) (Impl.Representation.evaluate R deg)))
      (Access.extendImpl A (Native.Core.messageInterface R
        (Impl.Representation.Message R deg) (Impl.Representation.evaluate R deg))
        impl q)) (.inr (.inr x))
  have hrun := congrArg (fun action => action.run) h
  convert hrun using 1 <;>
    simp [Native.Core.latest, Verifier.loggedLiftAccessImpl,
      Native.Core.messageInterface, OracleInterface.answer]
  rfl
/-- The actual sum action records each point once, in declared order, with its actual answer. -/
theorem logged_latestSum {deg : Nat} {ι : Type} (ambient : OracleSpec ι) (A : PFunctor)
    (prior : QueryImpl (ofPFunctor A) Id)
    (message : Impl.Representation.Message R deg) (domain : List R) :
    (simulateQ (Verifier.loggedLiftAccessImpl ambient
      (Access.extend A (Native.Core.messageInterface R
        (Impl.Representation.Message R deg) (Impl.Representation.evaluate R deg)))
      (Access.extendImpl A (Native.Core.messageInterface R
        (Impl.Representation.Message R deg) (Impl.Representation.evaluate R deg))
        prior message))
      (Native.Core.latestSum R (Impl.Representation.Message R deg)
        (Impl.Representation.evaluate R deg) ambient A domain)).run =
      pure ((domain.map fun x => Impl.Representation.evaluate R deg message x).sum,
        domain.map fun x => ⟨.inr x, Impl.Representation.evaluate R deg message x⟩) := by
  induction domain with
  | nil => rfl
  | cons x xs ih =>
    simp only [Native.Core.latestSum_cons, simulateQ_bind]
    simp only [WriterT.run_bind', logged_latest, pure_bind, simulateQ_pure,
      WriterT.run_pure', map_pure]
    rw [ih]
    simp

private theorem logged_ambient_primitive {ι : Type} (ambient : OracleSpec ι) (A : PFunctor)
    (impl : QueryImpl (ofPFunctor A) Id) (q : ambient.Domain) :
    (Verifier.loggedLiftAccessImpl ambient A impl (.inl q)).run =
      (fun answer => (answer, [])) <$> (QueryImpl.id' ambient q) := by
  simp [Verifier.loggedLiftAccessImpl]

local instance {m : Type → Type} [Monad m] [LawfulMonad m] {ω : Type}
    [EmptyCollection ω] [Append ω] [LawfulAppend ω] :
    LawfulMonadLift m (WriterT ω m) := WriterT.lawfulMonadLiftAppend (by simp)

private theorem logged_liftComp {ι : Type} (ambient : OracleSpec ι) (A : PFunctor)
    (impl : QueryImpl (ofPFunctor A) Id) {α : Type} (program : OracleComp ambient α) :
    (simulateQ (Verifier.loggedLiftAccessImpl ambient A impl)
      (program.liftComp (ambient + ofPFunctor A))).run =
      (fun answer => (answer, [])) <$> program := by
  have hleft (q : ambient.Domain) :
      Verifier.loggedLiftAccessImpl ambient A impl (.inl q) =
        liftM (QueryImpl.id' ambient q) := by
    apply WriterT.ext
    exact logged_ambient_primitive ambient A impl q
  rw [QueryImpl.simulateQ_liftComp_left_eq_of_apply _
    ((QueryImpl.id' ambient).liftTarget (WriterT (QueryLog (ofPFunctor A)) (OracleComp ambient)))
    hleft]
  rw [simulateQ_liftTarget, simulateQ_id']
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The existing logger's actual native run agrees with the path census. Both prover responses
remain effectful, and the terminal claim exists precisely when all round checks passed. -/
theorem logged_verifier_usage [DecidableEq R] (n deg : Nat) {ι : Type}
    (ambient : OracleSpec ι) (challenge : OracleComp ambient R)
    (count start : Nat) (finish : start + count = n) (A : PFunctor)
    (original : VirtualOracle (ofPFunctor A) (MultivariateRound.polynomialFamily R n deg))
    (stmt : Spec.StatementRound R n ⟨start, by omega⟩)
    (impl : QueryImpl (ofPFunctor A) Id)
    {OutP : (protocol R deg count).tree.ExecutionPath → Type}
    (prover : Prover.Strategy ambient (protocol R deg count).tree
      (protocol R deg count).roles OutP) :
    ∀ result ∈ support (executeStrategiesLogged ambient (protocol R deg count).tree
      (protocol R deg count).roles (protocol R deg count).oracles A impl prover
      (verifier R n deg ambient challenge [0, 1] count start finish A original stmt)),
      result.sourceLog.length = (pathUsage deg count result.path).messageQueries ∧
      result.verifierOut.isSome =
        decide ((pathUsage deg count result.path).terminalQueries = 1) := by
  induction count generalizing start A with
  | zero =>
    intro result hresult
    change result ∈ support (pure _) at hresult
    have heq := OracleComp.eq_of_mem_support_pure _ hresult
    subst result
    exact ⟨rfl, rfl⟩
  | succ count ih =>
    intro result hresult
    simp only [Computable.verifier, Native.Core.verifier, Computable.protocol,
      Native.Core.protocol, Protocol.oracleWith_tree, Protocol.oracleWith_roles,
      Protocol.oracleWith_oracles, Protocol.public_tree, Protocol.public_roles,
      Protocol.public_oracles, executeStrategiesLogged] at hresult
    obtain ⟨chosen, _, hresult⟩ := OracleComp.mem_support_bind_peel _ _ hresult
    simp only [simulateQ_bind, simulateQ_pure, WriterT.run_bind', WriterT.run_pure',
      logged_latestSum, pure_bind, map_pure, Prod.map, id_eq,
      Impl.VerifierChecks.equalM, Id.run, decide_eq_true_eq, bind_assoc] at hresult
    by_cases check : ([0, 1].map fun x => Impl.Representation.evaluate R deg chosen.1 x).sum =
        stmt.target
    · simp only [check, ↓reduceIte, simulateQ_bind, simulateQ_pure,
        WriterT.run_bind', WriterT.run_pure', logged_liftComp, logged_latest,
        bind_map_left, pure_bind, map_pure, Prod.map, id_eq, List.nil_append, bind_assoc] at hresult
      obtain ⟨r, _, hresult⟩ := OracleComp.mem_support_bind_peel _ _ hresult
      obtain ⟨nextP, _, hresult⟩ := OracleComp.mem_support_bind_peel _ _ hresult
      obtain ⟨tail, htail, hresult⟩ := OracleComp.mem_support_bind_peel _ _ hresult
      have heq := OracleComp.eq_of_mem_support_pure _ hresult
      subst result
      have ht := ih (start + 1) (by omega) _
        (original.sumWeaken (Native.Core.messageInterface R
          (Impl.Representation.Message R deg) (Impl.Representation.evaluate R deg)).spec)
        ⟨Impl.Representation.evaluate R deg chosen.1 r, Fin.snoc stmt.challenges r⟩
        (Access.extendImpl A (Native.Core.messageInterface R
          (Impl.Representation.Message R deg) (Impl.Representation.evaluate R deg)) impl chosen.1)
        (OutP := fun path => OutP ⟨chosen.1, ⟨some r, path⟩⟩) nextP tail htail
      constructor
      · simpa [pathUsage, roundUsage, plus, ← Nat.add_assoc] using ht.1
      · simpa [pathUsage, roundUsage, plus] using ht.2
    · simp only [check, ↓reduceIte, simulateQ_pure, WriterT.run_pure', pure_bind] at hresult
      obtain ⟨nextP, _, hresult⟩ := OracleComp.mem_support_bind_peel _ _ hresult
      have heq := OracleComp.eq_of_mem_support_pure _ hresult
      subst result
      simp [pathUsage, roundUsage, TypeTree.routeLog]

/-- Bounds use each actual canonical coefficient array, including the empty message. -/
theorem pathUsage_bounds (deg count : Nat) (path : (protocol R deg count).tree.ExecutionPath) :
    (pathUsage deg count path).messageQueries ≤ 3 * count ∧
    (pathUsage deg count path).coefficientReads ≤ 3 * count * (deg + 1) ∧
    (pathUsage deg count path).hornerMuls ≤ 3 * count * deg ∧
    (pathUsage deg count path).hornerAdds = (pathUsage deg count path).hornerMuls ∧
    (pathUsage deg count path).sumAdds ≤ 2 * count ∧
    (pathUsage deg count path).roundComparisons ≤ count ∧
    (pathUsage deg count path).roundSamples ≤ count ∧
    (pathUsage deg count path).terminalQueries ≤ 1 ∧
    (pathUsage deg count path).terminalComparisons =
      (pathUsage deg count path).terminalQueries := by
  induction count with
  | zero => simp [pathUsage]
  | succ count ih =>
    rcases path with ⟨message, ⟨choice, rest⟩⟩
    have hsize := Impl.Representation.size_le R deg message
    have hdegree : message.val.val.size - 1 ≤ deg := by omega
    cases choice with
    | none =>
      simp [pathUsage, roundUsage, Nat.mul_add, Nat.add_mul]
      omega
    | some r =>
      have ht := ih rest
      simp only [pathUsage, roundUsage, plus, ite_true] at *
      simp only [Nat.mul_add, Nat.add_mul] at *
      omega

/-- A completed branch opens three messages per draw; a rejecting round adds two openings. -/
theorem pathUsage_queries_eq (deg count : Nat)
    (path : (protocol R deg count).tree.ExecutionPath) :
    (pathUsage deg count path).messageQueries = 3 * (pathUsage deg count path).roundSamples +
      if (pathUsage deg count path).terminalQueries = 1 then 0 else 2 := by
  induction count with
  | zero => simp [pathUsage]
  | succ count ih =>
    rcases path with ⟨message, ⟨choice, rest⟩⟩
    cases choice with
    | none => simp [pathUsage, roundUsage]
    | some r => simpa [pathUsage, roundUsage, plus, Nat.mul_add, Nat.add_assoc] using ih rest

/-- All round checks passed exactly when every requested native challenge was reached. -/
theorem pathUsage_terminal_iff (deg count : Nat)
    (path : (protocol R deg count).tree.ExecutionPath) :
    (pathUsage deg count path).terminalQueries = 1 ↔
      (pathUsage deg count path).roundSamples = count := by
  induction count with
  | zero => simp [pathUsage]
  | succ count ih =>
    rcases path with ⟨message, ⟨choice, rest⟩⟩
    cases choice with
    | none => simp [pathUsage, roundUsage]
    | some r =>
      simpa only [pathUsage, roundUsage, plus, ite_true, Nat.zero_add,
        Nat.add_comm count 1, Nat.add_left_cancel_iff] using ih rest

set_option backward.isDefEq.respectTransparency false in
/-- Completing authentication preserves the actual path meter, including private prover effects. -/
theorem complete_usage_eq_logged [DecidableEq R] (n deg : Nat) {ι : Type}
    (ambient : OracleSpec ι) (challenge : OracleComp ambient R)
    (count start : Nat) (finish : start + count = n) (A : PFunctor)
    (original : VirtualOracle (ofPFunctor A) (MultivariateRound.polynomialFamily R n deg))
    (stmt : Spec.StatementRound R n ⟨start, by omega⟩) (impl : QueryImpl (ofPFunctor A) Id)
    {OutP : (protocol R deg count).tree.ExecutionPath → Type}
    (prover : Prover.Strategy ambient (protocol R deg count).tree
      (protocol R deg count).roles OutP) :
    (fun result => pathUsage deg count result.1) <$>
      executeStrategies ambient (protocol R deg count).tree (protocol R deg count).roles
        (protocol R deg count).oracles A impl prover
        (verifierWithFinalCheck R n deg ambient challenge [0, 1]
          count start finish A original stmt) =
    (fun result => pathUsage deg count result.path) <$>
      executeStrategiesLogged ambient (protocol R deg count).tree (protocol R deg count).roles
        (protocol R deg count).oracles A impl prover
        (verifier R n deg ambient challenge [0, 1] count start finish A original stmt) := by
  rw [Native.Core.executeStrategies_verifierWithFinalCheck]
  simp only [Functor.map_map]
  rw [← executeStrategiesLogged_erase ambient (protocol R deg count).tree
    (protocol R deg count).roles (protocol R deg count).oracles A impl prover
    (verifier R n deg ambient challenge [0, 1] count start finish A original stmt)]
  simp only [Functor.map_map, LoggedResult.erase]

private theorem logged_source_program {ι : Type} (ambient : OracleSpec ι) (A : PFunctor)
    (impl : QueryImpl (ofPFunctor A) Id) {α : Type}
    (program : OracleComp (ofPFunctor A) α) :
    (simulateQ (Verifier.loggedLiftAccessImpl ambient A impl)
      (program.liftComp (ambient + ofPFunctor A))).run =
      pure (simulateQ impl program.withQueryLog) := by
  let outer := impl.liftTarget (OracleComp ambient)
  have hsource (q : A.A) : Verifier.loggedLiftAccessImpl ambient A impl (.inr q) =
      outer.writerTMapBase (ofPFunctor A).loggingOracle q := by
    apply WriterT.ext
    have hlift : (liftM (impl q) : OracleComp ambient (A.B q)) = pure (impl q) := rfl
    simp [Verifier.loggedLiftAccessImpl, outer, QueryImpl.writerTMapBase,
      OracleSpec.loggingOracle, hlift]
  rw [QueryImpl.simulateQ_liftComp_right_eq_of_apply _ _ hsource]
  rw [← QueryImpl.simulateQ_writerTMapBase_run]
  change simulateQ outer program.withQueryLog = _
  exact simulateQ_liftTarget (n := OracleComp ambient) impl program.withQueryLog

set_option backward.isDefEq.respectTransparency false in
/-- The terminal checker preserves the actual view-query trace; its fanout is unrestricted. -/
theorem logged_checkFinalClaim [DecidableEq R] (n deg : Nat) {ι : Type}
    (ambient : OracleSpec ι) (A : PFunctor) (impl : QueryImpl (ofPFunctor A) Id)
    (claim : OpenClaim (ofPFunctor A) (Native.Core.FinalStatement R n)
      (MultivariateRound.polynomialFamily R n deg)) :
    let observed : R × QueryLog (ofPFunctor A) := (simulateQ impl
      (claim.oracles.query ⟨(), claim.stmt.challenges⟩).withQueryLog).run
    (simulateQ (Verifier.loggedLiftAccessImpl ambient A impl)
      (Native.Core.checkFinalClaim R n deg ambient A claim)).run =
      pure (decide (observed.1 = claim.stmt.target), observed.2) := by
  have hquery := logged_source_program ambient A impl
    (claim.oracles.query ⟨(), claim.stmt.challenges⟩)
  dsimp only
  rw [OracleComp.liftComp_eq_liftM] at hquery
  simp only [Native.Core.checkFinalClaim, simulateQ_bind, WriterT.run_bind',
    simulateQ_pure, WriterT.run_pure', map_pure]
  erw [hquery]
  simp [Impl.VerifierChecks.equalM, Id.run]

/-- Exact request coordinates of one actual canonical coefficient-array opening. -/
def messageCost (length : Nat) : ArithmeticCost
  | .coefficientRead => length
  | .mul | .add => length - 1
  | _ => 0

/-- Each newest-message opening selects the same seeded Horner as this profiled program. -/
theorem profile_message [Sub R] [Inv R] [DecidableEq R] (deg : Nat)
    (message : Impl.Representation.Message R deg) (x : R) :
    profileArithmetic (Arithmetic.evalHornerProgram message.val.val x) =
      (Impl.Representation.evaluate R deg message x, messageCost message.val.val.size) :=
  Arithmetic.profileArithmetic_evalHornerProgram message.val.val x

/-- The actual local domain-sum driver adds once per listed point, including its final + 0. -/
theorem profile_messageSum [Sub R] [Inv R] [DecidableEq R] (deg : Nat)
    (message : Impl.Representation.Message R deg) (domain : List R) :
    profileArithmetic (Impl.VerifierChecks.sumProgram
      (fun x => Arithmetic.evalHornerProgram message.val.val x) domain) =
      ((domain.map fun x => Impl.Representation.evaluate R deg message x).sum,
        Impl.VerifierChecks.sumCost domain (fun _ => messageCost message.val.val.size)) := by
  have h := Impl.VerifierChecks.profileArithmetic_sumProgram
    (fun x => Arithmetic.evalHornerProgram message.val.val x)
    (fun x => Impl.Representation.evaluate R deg message x)
    (fun _ => messageCost message.val.val.size) domain (fun x _ => profile_message deg message x)
  simpa only [Impl.VerifierChecks.sumM_id_eq_sum] using h

/-- Native local arithmetic excludes source-view/backend work and prover or sampler queries. -/
def Usage.arithmeticCost (usage : Usage) : ArithmeticCost
  | .add => usage.sumAdds + usage.hornerAdds
  | .mul => usage.hornerMuls
  | .eq => usage.roundComparisons + usage.terminalComparisons
  | .coefficientRead => usage.coefficientReads
  | _ => 0

/-- Coordinate bounds concern only native local checks and actual message evaluation. -/
theorem pathUsage_arithmeticCost_le (deg count : Nat)
    (path : (protocol R deg count).tree.ExecutionPath) (kind : ArithmeticCostKind) :
    (pathUsage deg count path).arithmeticCost kind ≤ match kind with
      | .add => 3 * count * deg + 2 * count
      | .mul => 3 * count * deg
      | .eq => count + 1
      | .coefficientRead => 3 * count * (deg + 1)
      | _ => 0 := by
  have h := pathUsage_bounds deg count path
  cases kind <;> simp only [Usage.arithmeticCost] <;> omega

end Sumcheck.Interaction.Computable.Resources

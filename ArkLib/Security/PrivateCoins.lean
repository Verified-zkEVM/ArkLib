/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuxi Zheng, Chung Thai Nguyen, Michele Orrù
-/
module

public import VCVio.OracleComp.SimSemantics.Append
public import VCVio.OracleComp.Constructions.SampleableType
public import VCVio.OracleComp.QueryTracking.LoggingOracle.Core
public import VCVio.OracleComp.QueryTracking.QueryBound.Simulation
public import VCVio.OracleComp.QueryTracking.QueryLog
public import VCVio.OracleComp.SimSemantics.OptionT.Basic

/-!
# Private coins and public-query interfaces

These operations and preservation lemmas use only oracle computations. Public queries and private
samples have separate slots; private samples are excluded from public budgets and extractor logs.
-/

@[expose] public section

open OracleComp OracleSpec

/-! ## Private sampling and public query interfaces

The security games append `unifSpec` for private samples. The helpers below select that slot,
exclude it from public budgets and logs, and compile custom samplers to uniform draws.
The preservation lemmas below keep execution, public logs, and query budgets unchanged.
-/

/-- Sample uniformly using the ambient monad's sampling capability. -/
def sampleUniform (α : Type) [SampleableType α] {m : Type → Type} [Monad m]
    [HasQuery unifSpec m] : m α :=
  simulateQ HasQuery.toQueryImpl ($ᵗ α)

namespace QueryImpl

universe u v w

/-- With `open scoped QueryImpl`, append handlers by lifting the right handler to the left
handler's monad. The existing same-monad instance takes precedence. -/
scoped instance (priority := low) instHAddLiftRight
    {ι κ : Type*} {a : OracleSpec.{_, u} ι} {b : OracleSpec.{_, u} κ}
    {m : Type u → Type v} {n : Type u → Type w} [MonadLiftT n m] :
    HAdd (QueryImpl a m) (QueryImpl b n) (QueryImpl (a + b) m) where
  hAdd left right := left + right.liftTarget m

/-- Otherwise, append handlers by lifting the left handler to the right handler's monad.
If lifts exist in both directions, `instHAddLiftRight` takes precedence. -/
scoped instance (priority := low - 1) instHAddLiftLeft
    {ι κ : Type*} {a : OracleSpec.{_, u} ι} {b : OracleSpec.{_, u} κ}
    {m : Type u → Type v} {n : Type u → Type w} [MonadLiftT m n] :
    HAdd (QueryImpl a m) (QueryImpl b n) (QueryImpl (a + b) n) where
  hAdd left right := left.liftTarget n + right

/-- Normalize automatic lifting on the right to the existing same-monad sum. -/
@[simp] theorem add_lift_right
    {ι κ : Type*} {a : OracleSpec.{_, u} ι} {b : OracleSpec.{_, u} κ}
    {m : Type u → Type v} {n : Type u → Type w} [MonadLiftT n m]
    (left : QueryImpl a m) (right : QueryImpl b n) :
    left + right = left + right.liftTarget m := rfl

/-- Normalize automatic lifting on the left to the existing same-monad sum. -/
@[simp] theorem add_lift_left
    {ι κ : Type*} {a : OracleSpec.{_, u} ι} {b : OracleSpec.{_, u} κ}
    {m : Type u → Type v} {n : Type u → Type w} [MonadLiftT m n]
    (left : QueryImpl a m) (right : QueryImpl b n) :
    left + right = left.liftTarget n + right := rfl

/-- Exchange two oracle slots without changing their queries or answers. -/
def swapOracles {ι κ : Type} {a : OracleSpec ι} {b : OracleSpec κ} :
    QueryImpl (a + b) (OracleComp (b + a))
  | .inl q => query (spec := b + a) (.inr q)
  | .inr q => query (spec := b + a) (.inl q)

end QueryImpl

namespace OracleComp

variable {ι κ α σ : Type} {publicSpec : OracleSpec ι} {privateSpec : OracleSpec κ}

/-- Reorder two oracle slots at a public/private interface boundary. -/
def swapOracles (p : OracleComp (publicSpec + privateSpec) α) :
    OracleComp (privateSpec + publicSpec) α :=
  simulateQ QueryImpl.swapOracles p

/-- Embed public queries into the left summand. This fixes the injection even when the
public oracle specification is itself a sum. -/
def liftCompLeft {κ' : Type} {extraSpec : OracleSpec κ'}
    (p : OracleComp publicSpec α) : OracleComp (publicSpec + extraSpec) α :=
  liftComp p (publicSpec + extraSpec)

/-- Sample privately even when the public oracle specification also contains `unifSpec`.
The explicit routing here prevents a structural `HasQuery` instance from choosing that public
slot. -/
def samplePrivateUniform (α : Type) [SampleableType α] :
    OracleComp (publicSpec + unifSpec) α :=
  simulateQ (fun q => liftM ((publicSpec + unifSpec).query (.inr q))) ($ᵗ α)

/-- Compile private requests to their samplers; forward every public query unchanged. -/
def privateCoinsImpl (sampler : QueryImpl privateSpec ProbComp) :
    QueryImpl (publicSpec + privateSpec) (OracleComp (publicSpec + unifSpec))
  | .inl q => liftM ((publicSpec + unifSpec).query (.inl q))
  | .inr q => liftComp (sampler q) _

/-- Express a computation using standard private coins instead of a custom sampling interface. -/
def normalizePrivateCoins (sampler : QueryImpl privateSpec ProbComp)
    (p : OracleComp (publicSpec + privateSpec) α) :
    OracleComp (publicSpec + unifSpec) α :=
  simulateQ (privateCoinsImpl sampler) p

/-- Select public queries for a budget; private samples never count. -/
def publicQuerySelector (counts : ι → Prop) : ι ⊕ κ → Prop
  | .inl q => counts q
  | .inr _ => False

instance (counts : ι → Prop) [DecidablePred counts] :
    DecidablePred (publicQuerySelector (κ := κ) counts) := fun q =>
  match q with
  | .inl q => inferInstanceAs (Decidable (counts q))
  | .inr _ => isFalse id

end OracleComp

namespace OracleSpec.QueryLog

/-- The public-query transcript of a computation with private coins. -/
abbrev publicQueries {ι κ : Type} {publicSpec : OracleSpec ι} {privateSpec : OracleSpec κ}
    (log : QueryLog (publicSpec + privateSpec)) : QueryLog publicSpec := log.fst

end OracleSpec.QueryLog

namespace OracleComp

variable {ι κ α σ : Type} {publicSpec : OracleSpec ι} {privateSpec : OracleSpec κ}

/-- Normalization preserves the entire computation, including its public-oracle state. -/
theorem simulateQ_normalizePrivateCoins
    (publicImpl : QueryImpl publicSpec (StateT σ ProbComp))
    (sampler : QueryImpl privateSpec ProbComp) (p : OracleComp (publicSpec + privateSpec) α) :
    simulateQ (publicImpl.addLift (QueryImpl.id' unifSpec) : QueryImpl _ (StateT σ ProbComp))
      (normalizePrivateCoins sampler p) =
      simulateQ (publicImpl.addLift sampler : QueryImpl _ (StateT σ ProbComp)) p := by
  apply QueryImpl.simulateQ_simulateQ_eq_of_apply
  intro q
  cases q with
  | inl q =>
    change simulateQ _ (liftComp (liftM (publicSpec.query q) : OracleComp publicSpec _) _) = _
    rw [QueryImpl.addLift_def, QueryImpl.simulateQ_add_liftComp_left]
    simp
  | inr q =>
    change simulateQ _ (liftComp (sampler q) _) = _
    rw [QueryImpl.addLift_def, QueryImpl.simulateQ_add_liftComp_right, simulateQ_liftTarget]
    simp

/-- A private sampler consumes none of the public-query budget. -/
theorem isQueryBoundP_lift_private (counts : ι → Prop) [DecidablePred counts]
    (p : ProbComp α) :
    (liftComp p (publicSpec + unifSpec)).IsQueryBoundP (publicQuerySelector counts) 0 := by
  induction p using OracleComp.inductionOn with
  | pure x => simp
  | query_bind q next ih =>
    rw [liftComp_bind, liftComp_query]
    exact (isQueryBoundP_query_bind_iff _ _ _ _).2 ⟨by simp [publicQuerySelector],
      fun u => by simpa [publicQuerySelector] using ih u⟩

/-- The named private sampler never charges a public query, even when the public spec
also contains `unifSpec`. -/
theorem isQueryBoundP_samplePrivateUniform (α : Type) [SampleableType α]
    (counts : ι → Prop) [DecidablePred counts] :
    (samplePrivateUniform (publicSpec := publicSpec) α).IsQueryBoundP
      (publicQuerySelector counts) 0 :=
  isQueryBoundP_lift_private counts ($ᵗ α)

/-- Compiling private samplers preserves any budget on selected public queries. -/
theorem IsQueryBoundP.normalizePrivateCoins
    (sampler : QueryImpl privateSpec ProbComp) (counts : ι → Prop) [DecidablePred counts]
    {p : OracleComp (publicSpec + privateSpec) α} {n : ℕ}
    (h : p.IsQueryBoundP (publicQuerySelector counts) n) :
    (normalizePrivateCoins sampler p).IsQueryBoundP (publicQuerySelector counts) n := by
  apply h.simulateQ_of_step
  · intro q hq
    cases q with
    | inl q => simp [privateCoinsImpl, publicQuerySelector]
    | inr q => exact False.elim hq
  · intro q hq
    cases q with
    | inl q => simpa [privateCoinsImpl, publicQuerySelector] using hq
    | inr q => exact isQueryBoundP_lift_private counts (sampler q)

/-- The named private sampler contributes no entries to the public transcript. -/
theorem publicQueries_withQueryLog_samplePrivateUniform (α : Type) [SampleableType α] :
    (fun r => (r.1, r.2.fst)) <$>
      (samplePrivateUniform (publicSpec := publicSpec) α).withQueryLog =
    (fun x => (x, ([] : QueryLog publicSpec))) <$> samplePrivateUniform α :=
  fst_withQueryLog_liftComp_right ($ᵗ α)

/-- Normalization preserves the public log even when one private request draws many samples. -/
theorem publicQueries_withQueryLog_normalizePrivateCoins
    (sampler : QueryImpl privateSpec ProbComp) (p : OracleComp (publicSpec + privateSpec) α) :
    (fun r => (r.1, r.2.fst)) <$> (normalizePrivateCoins sampler p).withQueryLog =
      normalizePrivateCoins sampler ((fun r => (r.1, r.2.fst)) <$> p.withQueryLog) := by
  apply withQueryLog_simulateQ_project (privateCoinsImpl sampler) QueryLog.fst QueryLog.fst
    rfl rfl QueryLog.fst_append QueryLog.fst_append
  intro q
  cases q with
  | inl q => simp [privateCoinsImpl, withQueryLog_query, QueryLog.fst]
  | inr q =>
    dsimp only [privateCoinsImpl]
    rw [fst_withQueryLog_liftComp_right]
    rfl

end OracleComp

namespace OracleComp

variable {ι κ α : Type} {a : OracleSpec ι} {b : OracleSpec κ}

/-- Reordering a computation and its handlers preserves the interpreted computation. -/
@[simp]
theorem simulateQ_swapOracles {m : Type → Type} [Monad m] [LawfulMonad m]
    (ha : QueryImpl a m) (hb : QueryImpl b m) (p : OracleComp (a + b) α) :
    simulateQ (hb + ha) p.swapOracles = simulateQ (ha + hb) p := by
  apply QueryImpl.simulateQ_simulateQ_eq_of_apply
  intro q
  cases q <;> simp [QueryImpl.swapOracles]

end OracleComp

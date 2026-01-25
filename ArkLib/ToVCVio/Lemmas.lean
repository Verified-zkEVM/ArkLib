import VCVio

open OracleComp OracleSpec

section simp_lemmas -- Some extra lemmas that still need to move to vcv

universe u v w

variable {ι : Type u} {spec : OracleSpec ι} {α β γ ω : Type u}

@[simp]
lemma probFailure_bind_eq_zero_iff [spec.FiniteRange]
    (oa : OracleComp spec α) (ob : α → OracleComp spec β) :
    [⊥ | oa >>= ob] = 0 ↔ [⊥ | oa] = 0 ∧ ∀ x ∈ oa.support, [⊥ | ob x] = 0 := by
  simp [probFailure_bind_eq_tsum, ← imp_iff_not_or]

@[simp] -- TODO: more general version/class for query impls that never have failures
lemma loggingOracle.probFailure_simulateQ [spec.FiniteRange] (oa : OracleComp spec α) :
    [⊥ | (simulateQ loggingOracle oa).run] = [⊥ | oa] := by
  induction oa using OracleComp.induction with
  | pure a => simp
  | query_bind i t oa ih => simp [ih, probFailure_bind_eq_tsum]
  | failure => simp

@[simp]
lemma probFailure_liftComp {ι' : Type w} {superSpec : OracleSpec ι'}
    [spec.FiniteRange] [superSpec.FiniteRange]
    [h : MonadLift (OracleQuery spec) (OracleQuery superSpec)]
    (oa : OracleComp spec α) : [⊥ | liftComp oa superSpec] = [⊥ | oa] := by
  simp only [OracleComp.probFailure_def, OracleComp.evalDist_liftComp]

/-- Spec-lifting preserves the failure probability. -/
@[simp]
lemma probFailure_liftComp_eq {ι' : Type} {superSpec : OracleSpec ι'}
    [spec.FiniteRange] [superSpec.FiniteRange]
    [MonadLift (OracleQuery spec) (OracleQuery superSpec)]
    (oa : OracleComp spec α) : [⊥ | liftComp oa superSpec] = [⊥ | oa] := by
  simp only [OracleComp.probFailure_def, OracleComp.evalDist_liftComp]

@[simp]
lemma liftComp_support {ι' : Type w} {superSpec : OracleSpec ι'}
    [h : MonadLift (OracleQuery spec) (OracleQuery superSpec)]
    (oa : OracleComp spec α) : (liftComp oa superSpec).support = oa.support := by
  induction oa using OracleComp.induction with
  | pure a => simp
  | query_bind i t oa ih => simp [ih]
  | failure => simp

-- Stub lemma for now, will be available in the next VCVio update
lemma neverFails_map_iff' (oa : OracleComp spec α) (f : α → β) :
    neverFails (f <$> oa) ↔ neverFails oa := by
  rw [map_eq_bind_pure_comp]
  simp [neverFails, neverFailsWhen, Function.comp_apply, implies_true, and_true]

/-- Bridge between monadic support and deterministic results for pure ProbComp. -/
@[simp]
lemma support_pure_bind_pure {α β : Type} (x : α) (f : α → ProbComp β) :
    (pure x >>= f).support = (f x).support :=
by simp

alias support_pure_bind := support_pure_bind_pure

/-- Simplifies the probability event of a deterministic pure result. -/
@[simp]
lemma probEvent_pure_iff {α : Type} [DecidableEq α] (p : α → Prop) [DecidablePred p] (x : α) :
    [p | (pure x : ProbComp α)] = 1 ↔ p x :=
by
  simp only [probEvent_pure, ite_eq_left_iff]
  exact ⟨fun h => by simpa using h, fun h => by simp [h]⟩

alias probEvent_eq_one_pure_iff := probEvent_pure_iff

end simp_lemmas

/-! ### StateT Helper Lemmas

Generic helper lemmas for `StateT` operations that simplify reasoning about
`run`, `run'`, and monadic operations in the probability monad.

These lemmas unfold stateful computations into their underlying probability distributions.
-/

namespace StateT

universe u v w

variable {m : Type u → Type v} {σ α β : Type u}

/-- Unfolding lemma for `run'` on `pure`. -/
@[simp]
theorem run'_pure_lib [Monad m] [LawfulMonad m] (x : α) (s : σ) :
    (pure x : StateT σ m α).run' s = (pure x : m α) := by
  simp only [run', pure, StateT.pure, map_pure]

/-- Unfolding lemma for `run'` on `bind`. -/
@[simp]
theorem run'_bind_lib [Monad m] [LawfulMonad m] (ma : StateT σ m α) (f : α → StateT σ m β) (s : σ) :
    (ma >>= f).run' s = ((ma.run s) >>= fun (a, s') => (f a).run' s') := by
  simp only [run', bind, StateT.bind, map_bind, run]

/-- Unfolding lemma for `run` on `liftM`. -/
@[simp]
theorem run_liftM_lib [Monad m] [LawfulMonad m] (ma : m α) (s : σ) :
    (liftM ma : StateT σ m α).run s = (ma >>= fun a => pure (a, s)) := by
  simp only [run, liftM, bind_pure_comp]
  rw [map_eq_pure_bind]; rfl

/-- Simplify a bind following a pure initialization of state. -/
@[simp]
theorem run'_bind_pure [Monad m] [LawfulMonad m] {s : σ} (x : α) (f : α → StateT σ m β) :
    (StateT.run' (pure x >>= f) s) = (StateT.run' (f x) s) :=
by simp [StateT.run']

alias run'_pure_bind := run'_bind_pure

end StateT

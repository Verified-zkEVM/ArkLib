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

end simp_lemmas

/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
module

public import ArkLib.ProofSystem.Logup.Lookup.Tuple.Source
public import ArkLib.ProofSystem.Logup.Algebra.ArithmeticReconstruction
public import ArkLib.ToCompPoly.Univariate.ArithmeticHorner

/-!
# Actual LogUp source openings and local scalar kernels

These laws log the existing source programs after substitution, using the same deterministic
handler for their actual responses. General views retain their real answer-dependent fanout;
identity views give raw counts 2T+K, M+2P+K and (W+1)(M+P)+P+K. Prior-source transport preserves
request order and keeps retained multiplicities distinct from the newest helper source.

After binding answers, Q selects the existing operation-parametric reconstruction. Tuple values
select the shared seeded Horner core over the actual W+1 challenge-field coefficient buffer.
Their local ArithmeticSpec profiles price those selected kernels only: source openings, backend
MLE evaluation, opaque embeddings, storage and machine work remain separate. In particular the
P unary-negation sites of synthetic table weights are not ArithmeticSpec subtraction requests.
The M constant-one/P negation branch census is stated separately.

All source statements allow arbitrary retained mu and helper tables, including poles, without a
lookup-truth or source-realization premise. Cost profiles additionally use the existing arithmetic
carrier's Inv/DecidableEq instances; reconstruction requests no inversion. A Q expansion is local
to an actual terminal source query. Whole execution may stop before that query; endpoint log and
sampling composition require their separate execution laws and are not asserted by these counts.
-/

@[expose] public section

open Interaction.Oracle OracleComp OracleSpec CompPoly
open scoped BigOperators
namespace Logup.Interaction.Resources

private theorem query_log_length {ι : Type} {spec : OracleSpec ι}
    (impl : QueryImpl spec Id) (q : spec.Domain) :
    (simulateQ impl (liftM (spec.query q) : OracleComp spec _).withQueryLog).2.length = 1 := by
  rw [withQueryLog_query, simulateQ_bind, simulateQ_spec_query]
  rfl

private theorem query_return_log_length {ι α : Type} {spec : OracleSpec ι}
    (impl : QueryImpl spec Id) (q : spec.Domain) (result : spec.Range q → α) :
    (simulateQ impl (do
      let answer ← (liftM (spec.query q) : OracleComp spec _)
      return result answer).withQueryLog).2.length = 1 := by
  rw [withQueryLog_bind, withQueryLog_query]
  simp only [simulateQ_bind, simulateQ_map, simulateQ_spec_query, simulateQ_pure,
    withQueryLog_pure]
  rfl

/-- Prior-source routing preserves each actual response and injects its ordered raw log. -/
private theorem prior_withQueryLog {A : PFunctor.{0, 0}} {Msg : Type}
    (interface : OracleInterface Msg)
    (impl : QueryImpl (ofPFunctor A) Id) (message : Msg) {α : Type}
    (program : OracleComp (ofPFunctor A) α) :
    simulateQ (Access.extendImpl A interface impl message)
        (simulateQ (Access.queryPrior A interface) program).withQueryLog =
      let result := simulateQ impl program.withQueryLog
      (result.1, result.2.map fun entry => ⟨Sum.inl entry.1, entry.2⟩) := by
  induction program using OracleComp.inductionOn with
  | pure value =>
    simp only [simulateQ_pure, withQueryLog_pure]
    rfl
  | query_bind q next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query]
    simp only [Access.queryPrior, withQueryLog_bind, withQueryLog_query,
      simulateQ_bind, simulateQ_pure, simulateQ_map]
    simp only [simulateQ_spec_query, Access.extendImpl_prior, ih]
    dsimp only [Bind.bind, Pure.pure, Functor.map, Prod.map]
    cases simulateQ impl (next (impl q)).withQueryLog
    rfl

variable {B E : Type} [CommRing B] [CommRing E]
variable (f : B →+* E) (n T K : Nat)
/-- The actual Q program opens its weakened value/weight programs and each newest helper. -/
private theorem queryQ_log_length_weakened (groups : Vector (List (Fin T)) K)
    (alpha : E) (z : Fin n → E)
    (lambda : Fin K → E) (A : PFunctor.{0, 0})
    (inputView : VirtualOracle (ofPFunctor A) (inputFamily f n T))
    (impl : QueryImpl (ofPFunctor
      (Access.extend A (helperInterface (E := E) n K))) Id)
    (x : Fin n → E) :
    (simulateQ impl
      (queryQ f n T K groups alpha z lambda A inputView x).withQueryLog).2.length =
      ((List.finRange T).map fun i =>
        (simulateQ impl (queryInput f n T
          (Access.extend A (helperInterface (E := E) n K))
          (inputView.substSource (Access.queryPrior A
            (helperInterface (E := E) n K))) 0 i x).withQueryLog).2.length).sum +
      ((List.finRange T).map fun i =>
        (simulateQ impl (queryInput f n T
          (Access.extend A (helperInterface (E := E) n K))
          (inputView.substSource (Access.queryPrior A
            (helperInterface (E := E) n K))) 1 i x).withQueryLog).2.length).sum + K := by
  have hh (k : Fin K) :
      (simulateQ impl (queryHelper n K A k x).withQueryLog).2.length = 1 := by
    exact query_log_length impl (.inr (k, x))
  simp only [queryQ, withQueryLog_bind, withQueryLog_pure,
    simulateQ_bind, simulateQ_map, simulateQ_pure, simulateQ_withQueryLog_ofFnM]
  change (_ ++ (_ ++ (_ ++ []))).length = _
  simp only [List.length_append, List.length_flatMap, hh, List.length_nil, Nat.add_zero]
  simp [Nat.add_assoc]


/-- The actual Q raw opening count is the sum of original-view fanouts plus K helpers. -/
theorem queryQ_log_length (groups : Vector (List (Fin T)) K) (alpha : E) (z : Fin n → E)
    (lambda : Fin K → E) (A : PFunctor.{0, 0})
    (view : VirtualOracle (ofPFunctor A) (inputFamily f n T))
    (impl : QueryImpl (ofPFunctor A) Id) (helpers : Vector (CMlPolynomialEval E n) K)
    (x : Fin n → E) :
    (simulateQ (Access.extendImpl A (helperInterface (E := E) n K) impl helpers)
      (queryQ f n T K groups alpha z lambda A view x).withQueryLog).2.length =
      ((List.finRange T).map fun i =>
        (simulateQ impl (view.query ⟨(0, i), x⟩).withQueryLog).2.length).sum +
      ((List.finRange T).map fun i =>
        (simulateQ impl (view.query ⟨(1, i), x⟩).withQueryLog).2.length).sum + K := by
  rw [queryQ_log_length_weakened]
  have h (kind : Fin 2) (i : Fin T) :
      (simulateQ (Access.extendImpl A (helperInterface (E := E) n K)
          impl helpers)
        (queryInput f n T
          (Access.extend A (helperInterface (E := E) n K))
          (view.substSource (Access.queryPrior A
            (helperInterface (E := E) n K))) kind i x).withQueryLog).2.length =
        (simulateQ impl (view.query ⟨(kind, i), x⟩).withQueryLog).2.length := by
    change (simulateQ
      (Access.extendImpl A (helperInterface (E := E) n K) impl helpers)
      (simulateQ (Access.queryPrior A (helperInterface (E := E) n K))
        (view.query ⟨(kind, i), x⟩)).withQueryLog).2.length = _
    rw [prior_withQueryLog]
    exact List.length_map ..
  simp only [h]


/-- An identity weighted view uses exactly two original openings per column and K helpers. -/
theorem queryQ_identity_log_length (groups : Vector (List (Fin T)) K) (alpha : E)
    (z : Fin n → E) (lambda : Fin K → E)
    (impl : QueryImpl (inputFamily f n T).spec Id)
    (helpers : Vector (CMlPolynomialEval E n) K) (x : Fin n → E) :
    (simulateQ (Access.extendImpl (inputFamily f n T).spec.toPFunctor
        (helperInterface (E := E) n K) impl helpers)
      (queryQ f n T K groups alpha z lambda
        (inputFamily f n T).spec.toPFunctor
        (VirtualOracle.id (inputFamily f n T)) x).withQueryLog).2.length =
      2 * T + K := by
  rw [queryQ_log_length]
  have h (kind : Fin 2) (i : Fin T) :
      (simulateQ impl
        ((VirtualOracle.id (inputFamily f n T)).query
          ⟨(kind, i), x⟩).withQueryLog).2.length = 1 := by
    simpa only [VirtualOracle.id, QueryImpl.id'_apply] using
      (query_log_length impl ⟨(kind, i), x⟩)
  simp only [h]
  simp [Nat.two_mul]


variable (M P : Nat)
/-- A scalar weighted query uses its actual original-view fanout or one retained mu opening. -/
theorem scalar_queryWeighted_log_length (A : PFunctor.{0, 0})
    (view : VirtualOracle (ofPFunctor A) (Logup.Lookup.valuesFamily f n M P))
    (impl : QueryImpl (ofPFunctor A) Id) (mu : Vector (CMlPolynomialEval B n) P)
    (kind : Fin 2) (i : Fin (M + P)) (x : Fin n → E) :
    (simulateQ (Access.extendImpl A (Logup.Lookup.multiplicityInterface f n P) impl mu)
      (Logup.Lookup.queryWeighted f n M P A view kind i x).withQueryLog).2.length =
      if kind = 0 then
        (simulateQ impl (view.query ⟨finSumFinEquiv.symm i, x⟩).withQueryLog).2.length
      else match finSumFinEquiv.symm i with | .inl _ => 0 | .inr _ => 1 := by
  split_ifs with hk
  · simp only [Logup.Lookup.queryWeighted, hk, ↓reduceIte]
    change (simulateQ (Access.extendImpl A (Logup.Lookup.multiplicityInterface f n P) impl mu)
      (simulateQ (Access.queryPrior A (Logup.Lookup.multiplicityInterface f n P))
        (view.query ⟨finSumFinEquiv.symm i, x⟩)).withQueryLog).2.length = _
    rw [prior_withQueryLog]
    exact List.length_map ..
  · simp only [Logup.Lookup.queryWeighted, hk, ↓reduceIte]
    generalize hs : finSumFinEquiv.symm i = slot
    cases slot with
    | inl query => rfl
    | inr piece =>
      exact query_return_log_length
        (Access.extendImpl A (Logup.Lookup.multiplicityInterface f n P) impl mu)
        (.inr (piece, x)) (fun answer : E => -answer)


/-- Exactly P weighted-column positions select a declared physical table piece. -/
private theorem weight_count :
    ((List.finRange (M + P)).map fun i =>
      match finSumFinEquiv.symm i with | .inl _ => 0 | .inr _ => 1).sum = P := by
  rw [← List.ofFn_eq_map, List.sum_ofFn]
  rw [← Equiv.sum_comp (finSumFinEquiv : Fin M ⊕ Fin P ≃ Fin (M + P))]
  simp

set_option backward.isDefEq.respectTransparency false in
/-- A scalar Q expansion uses actual original-value fanouts plus P multiplicities and K helpers. -/
theorem scalar_queryQ_log_length (groups : Vector (List (Fin (M + P))) K)
    (alpha : E) (z : Fin n → E) (lambda : Fin K → E) (A : PFunctor.{0, 0})
    (view : VirtualOracle (ofPFunctor A) (Logup.Lookup.valuesFamily f n M P))
    (impl : QueryImpl (ofPFunctor A) Id) (mu : Vector (CMlPolynomialEval B n) P)
    (helpers : Vector (CMlPolynomialEval E n) K) (x : Fin n → E) :
    (simulateQ (Access.extendImpl (Access.extend A (Logup.Lookup.multiplicityInterface f n P))
        (helperInterface (E := E) n K)
        (Access.extendImpl A (Logup.Lookup.multiplicityInterface f n P) impl mu) helpers)
      (queryQ f n (M + P) K groups alpha z lambda
        (Access.extend A (Logup.Lookup.multiplicityInterface f n P))
        (Logup.Lookup.weightedView f n M P A view) x).withQueryLog).2.length =
      ((List.finRange (M + P)).map fun i =>
        (simulateQ impl (view.query ⟨finSumFinEquiv.symm i, x⟩).withQueryLog).2.length).sum +
        P + K := by
  rw [queryQ_log_length]
  simp only [Logup.Lookup.weightedView, scalar_queryWeighted_log_length,
    show (1 : Fin 2) ≠ 0 by decide, ↓reduceIte]
  rw [weight_count]


variable (W : Nat)
set_option backward.isDefEq.respectTransparency false in
/-- A compressed value uses the actual fanout of each of its W+1 coefficient-view programs. -/
theorem tuple_queryValue_log_length (beta : E) (A : PFunctor.{0, 0})
    (view : VirtualOracle (ofPFunctor A) (Logup.Lookup.Tuple.coefficientFamily f n M P W))
    (impl : QueryImpl (ofPFunctor A) Id) (slot : Fin M ⊕ Fin P) (x : Fin n → E) :
    (simulateQ impl
      (Logup.Lookup.Tuple.queryValue f n M P W beta A view slot x).withQueryLog).2.length =
      ((List.finRange (W + 1)).map fun j =>
        (simulateQ impl (view.query ⟨(slot, j), x⟩).withQueryLog).2.length).sum := by
  simp only [Logup.Lookup.Tuple.queryValue, withQueryLog_bind, withQueryLog_pure,
    simulateQ_bind, simulateQ_map, simulateQ_pure, simulateQ_withQueryLog_ofFnM]
  change (_ ++ []).length = _
  simp only [List.append_nil, List.length_flatMap]

/-- A tuple weighted query uses coefficient-view fanouts or one retained mu opening. -/
theorem tuple_queryWeighted_log_length (beta : E) (A : PFunctor.{0, 0})
    (view : VirtualOracle (ofPFunctor A) (Logup.Lookup.Tuple.coefficientFamily f n M P W))
    (impl : QueryImpl (ofPFunctor A) Id) (mu : Vector (CMlPolynomialEval B n) P)
    (kind : Fin 2) (i : Fin (M + P)) (x : Fin n → E) :
    (simulateQ (Access.extendImpl A (Logup.Lookup.multiplicityInterface f n P) impl mu)
      (Logup.Lookup.Tuple.queryWeighted f n M P W beta A view kind i x).withQueryLog).2.length =
      if kind = 0 then
        ((List.finRange (W + 1)).map fun j =>
          (simulateQ impl
            (view.query ⟨(finSumFinEquiv.symm i, j), x⟩).withQueryLog).2.length).sum
      else match finSumFinEquiv.symm i with | .inl _ => 0 | .inr _ => 1 := by
  split_ifs with hk
  · simp only [Logup.Lookup.Tuple.queryWeighted, hk, ↓reduceIte]
    change (simulateQ (Access.extendImpl A (Logup.Lookup.multiplicityInterface f n P) impl mu)
      (simulateQ (Access.queryPrior A (Logup.Lookup.multiplicityInterface f n P))
        (Logup.Lookup.Tuple.queryValue f n M P W beta A view
          (finSumFinEquiv.symm i) x)).withQueryLog).2.length = _
    rw [prior_withQueryLog, List.length_map, tuple_queryValue_log_length]
  · simp only [Logup.Lookup.Tuple.queryWeighted, hk, ↓reduceIte]
    generalize hs : finSumFinEquiv.symm i = slot
    cases slot with
    | inl query => rfl
    | inr piece =>
      exact query_return_log_length
        (Access.extendImpl A (Logup.Lookup.multiplicityInterface f n P) impl mu)
        (.inr (piece, x)) (fun answer : E => -answer)

set_option backward.isDefEq.respectTransparency false in
/-- A tuple Q expansion sums actual coefficient fanouts and opens P multiplicities and K helpers. -/
theorem tuple_queryQ_log_length (groups : Vector (List (Fin (M + P))) K)
    (beta alpha : E) (z : Fin n → E) (lambda : Fin K → E) (A : PFunctor.{0, 0})
    (view : VirtualOracle (ofPFunctor A) (Logup.Lookup.Tuple.coefficientFamily f n M P W))
    (impl : QueryImpl (ofPFunctor A) Id) (mu : Vector (CMlPolynomialEval B n) P)
    (helpers : Vector (CMlPolynomialEval E n) K) (x : Fin n → E) :
    (simulateQ (Access.extendImpl (Access.extend A (Logup.Lookup.multiplicityInterface f n P))
        (helperInterface (E := E) n K)
        (Access.extendImpl A (Logup.Lookup.multiplicityInterface f n P) impl mu) helpers)
      (queryQ (RingHom.id E) n (M + P) K groups alpha z lambda
        (Access.extend A (Logup.Lookup.multiplicityInterface f n P))
        (Logup.Lookup.Tuple.weightedView f n M P W beta A view) x).withQueryLog).2.length =
      ((List.finRange (M + P)).map fun i =>
        ((List.finRange (W + 1)).map fun j =>
          (simulateQ impl
            (view.query ⟨(finSumFinEquiv.symm i, j), x⟩).withQueryLog).2.length).sum).sum +
        P + K := by
  rw [queryQ_log_length]
  simp only [Logup.Lookup.Tuple.weightedView, tuple_queryWeighted_log_length,
    show (1 : Fin 2) ≠ 0 by decide, ↓reduceIte]
  rw [weight_count]


set_option backward.isDefEq.respectTransparency false in
/-- Identity scalar sources expand one Q query into M+2P+K raw openings. -/
theorem scalar_queryQ_identity_log_length (groups : Vector (List (Fin (M + P))) K)
    (alpha : E) (z : Fin n → E) (lambda : Fin K → E)
    (impl : QueryImpl (Logup.Lookup.valuesFamily f n M P).spec Id)
    (mu : Vector (CMlPolynomialEval B n) P) (helpers : Vector (CMlPolynomialEval E n) K)
    (x : Fin n → E) :
    (simulateQ (Access.extendImpl
        (Access.extend (Logup.Lookup.valuesFamily f n M P).spec.toPFunctor
          (Logup.Lookup.multiplicityInterface f n P))
        (helperInterface (E := E) n K)
        (Access.extendImpl (Logup.Lookup.valuesFamily f n M P).spec.toPFunctor
          (Logup.Lookup.multiplicityInterface f n P) impl mu) helpers)
      (queryQ f n (M + P) K groups alpha z lambda
        (Access.extend (Logup.Lookup.valuesFamily f n M P).spec.toPFunctor
          (Logup.Lookup.multiplicityInterface f n P))
        (Logup.Lookup.weightedView f n M P (Logup.Lookup.valuesFamily f n M P).spec.toPFunctor
          (VirtualOracle.id (Logup.Lookup.valuesFamily f n M P))) x).withQueryLog).2.length =
      M + 2 * P + K := by
  rw [scalar_queryQ_log_length]
  have h (i : Fin (M + P)) :
      (simulateQ impl ((VirtualOracle.id (Logup.Lookup.valuesFamily f n M P)).query
        ⟨finSumFinEquiv.symm i, x⟩).withQueryLog).2.length = 1 := by
    simpa only [VirtualOracle.id, QueryImpl.id'_apply] using
      (query_log_length impl ⟨finSumFinEquiv.symm i, x⟩)
  simp only [h]
  simp [Nat.two_mul, Nat.add_assoc]

set_option backward.isDefEq.respectTransparency false in
/-- Identity tuple sources expand one Q query into (W+1)(M+P)+P+K raw openings. -/
theorem tuple_queryQ_identity_log_length (groups : Vector (List (Fin (M + P))) K)
    (beta alpha : E) (z : Fin n → E) (lambda : Fin K → E)
    (impl : QueryImpl (Logup.Lookup.Tuple.coefficientFamily f n M P W).spec Id)
    (mu : Vector (CMlPolynomialEval B n) P) (helpers : Vector (CMlPolynomialEval E n) K)
    (x : Fin n → E) :
    (simulateQ (Access.extendImpl
        (Access.extend (Logup.Lookup.Tuple.coefficientFamily f n M P W).spec.toPFunctor
          (Logup.Lookup.multiplicityInterface f n P))
        (helperInterface (E := E) n K)
        (Access.extendImpl (Logup.Lookup.Tuple.coefficientFamily f n M P W).spec.toPFunctor
          (Logup.Lookup.multiplicityInterface f n P) impl mu) helpers)
      (queryQ (RingHom.id E) n (M + P) K groups alpha z lambda
        (Access.extend (Logup.Lookup.Tuple.coefficientFamily f n M P W).spec.toPFunctor
          (Logup.Lookup.multiplicityInterface f n P))
        (Logup.Lookup.Tuple.weightedView f n M P W beta
          (Logup.Lookup.Tuple.coefficientFamily f n M P W).spec.toPFunctor
          (VirtualOracle.id
            (Logup.Lookup.Tuple.coefficientFamily f n M P W))) x).withQueryLog).2.length =
      (W + 1) * (M + P) + P + K := by
  rw [tuple_queryQ_log_length]
  have h (i : Fin (M + P)) (j : Fin (W + 1)) :
      (simulateQ impl ((VirtualOracle.id (Logup.Lookup.Tuple.coefficientFamily f n M P W)).query
        ⟨(finSumFinEquiv.symm i, j), x⟩).withQueryLog).2.length = 1 := by
    simpa only [VirtualOracle.id, QueryImpl.id'_apply] using
      (query_log_length impl ⟨(finSumFinEquiv.symm i, j), x⟩)
  simp only [h]
  simp [Nat.mul_comm]


set_option backward.isDefEq.respectTransparency false in
/-- The shared arithmetic reconstruction uses the actual bound source answers and returns Q. -/
theorem queryQ_profile [Inv E] [DecidableEq E]
    (groups : Vector (List (Fin T)) K) (alpha : E) (z : Fin n → E)
    (lambda : Fin K → E) (A : PFunctor.{0, 0})
    (view : VirtualOracle (ofPFunctor A) (inputFamily f n T))
    (impl : QueryImpl (ofPFunctor
      (Access.extend A (helperInterface (E := E) n K))) Id)
    (x : Fin n → E) :
    let values := fun i => simulateQ impl (queryInput f n T
      (Access.extend A (helperInterface (E := E) n K))
      (view.substSource (Access.queryPrior A (helperInterface (E := E) n K)))
      0 i x)
    let weights := fun i => simulateQ impl (queryInput f n T
      (Access.extend A (helperInterface (E := E) n K))
      (view.substSource (Access.queryPrior A (helperInterface (E := E) n K)))
      1 i x)
    let helpers := fun k => simulateQ impl (queryHelper n K A k x)
    profileArithmetic
      (Logup.Reconstruction.program groups alpha z lambda x values weights helpers) =
      (simulateQ impl (queryQ f n T K groups alpha z lambda A view x),
        Logup.Reconstruction.cost groups n) := by
  dsimp only
  rw [Logup.Reconstruction.profile_program_reconstruct]
  simp only [queryQ, simulateQ_bind, simulateQ_ofFnM, simulateQ_pure]
  dsimp only [Bind.bind, Pure.pure]
  simp only [Vector.getElem_ofFn]


set_option backward.isDefEq.respectTransparency false in
/-- The buffered coefficient reader uses W multiplications/additions and W+1 coefficient reads. -/
theorem tuple_queryValue_profile [Inv E] [DecidableEq E] (beta : E) (A : PFunctor.{0, 0})
    (view : VirtualOracle (ofPFunctor A) (Logup.Lookup.Tuple.coefficientFamily f n M P W))
    (impl : QueryImpl (ofPFunctor A) Id) (slot : Fin M ⊕ Fin P) (x : Fin n → E) :
    let coeffs : Vector E (W + 1) := Vector.ofFn fun j =>
      simulateQ impl (view.query ⟨(slot, j), x⟩)
    profileArithmetic (Arithmetic.evalHornerProgram coeffs.toArray beta) =
      (simulateQ impl (Logup.Lookup.Tuple.queryValue f n M P W beta A view slot x),
        fun kind => match kind with
        | .coefficientRead => W + 1
        | .mul | .add => W
        | _ => 0) := by
  dsimp only
  rw [Arithmetic.profileArithmetic_evalHornerProgram]
  simp only [Logup.Lookup.Tuple.queryValue, simulateQ_bind, simulateQ_ofFnM,
    simulateQ_pure, Vector.size_toArray, Nat.add_sub_cancel]
  rfl


set_option backward.isDefEq.respectTransparency false in
/-- Across all value slots, the selected buffered Horner kernels have the stated exact profile. -/
theorem tuple_queryValue_total_profile [Inv E] [DecidableEq E]
    (beta : E) (A : PFunctor.{0, 0})
    (view : VirtualOracle (ofPFunctor A) (Logup.Lookup.Tuple.coefficientFamily f n M P W))
    (impl : QueryImpl (ofPFunctor A) Id) (x : Fin n → E) (kind : ArithmeticCostKind) :
    (∑ slot : Fin M ⊕ Fin P,
      (profileArithmetic (Arithmetic.evalHornerProgram
        (Vector.ofFn (fun j : Fin (W + 1) =>
          simulateQ impl (view.query ⟨(slot, j), x⟩)) : Vector E (W + 1)).toArray beta)).2 kind) =
      match kind with
      | .coefficientRead => (M + P) * (W + 1)
      | .mul | .add => (M + P) * W
      | _ => 0 := by
  simp only [tuple_queryValue_profile]
  cases kind <;> simp [Fintype.card_sum]

/-- The synthetic-weight branch census has M constant-one sites and P unary-negation sites. -/
theorem lookup_weight_sites :
    ((List.finRange (M + P)).map fun i =>
      match finSumFinEquiv.symm i with | .inl _ => 1 | .inr _ => 0).sum = M ∧
    ((List.finRange (M + P)).map fun i =>
      match finSumFinEquiv.symm i with | .inl _ => 0 | .inr _ => 1).sum = P := by
  refine ⟨?_, weight_count M P⟩
  rw [← List.ofFn_eq_map, List.sum_ofFn]
  rw [← Equiv.sum_comp (finSumFinEquiv : Fin M ⊕ Fin P ≃ Fin (M + P))]
  simp

end Logup.Interaction.Resources

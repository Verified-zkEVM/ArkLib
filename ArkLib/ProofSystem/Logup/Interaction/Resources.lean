/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/
module

public import ArkLib.ProofSystem.Logup.Lookup.Tuple.Source
public import ArkLib.ProofSystem.Logup.Interaction.Protocol
public import ArkLib.ProofSystem.Logup.Lookup.Protocol
public import ArkLib.ProofSystem.Logup.Lookup.Tuple.Protocol
public import ArkLib.Interaction.Oracle.PhasedExecution
public import ArkLib.ProofSystem.Sumcheck.Interaction.Resources
-- Prefix routing proofs unfold the defining maps and the existing logged runner only.
import all PolyFun.Interaction.Basic.StrategyOver
import all ArkLib.Interaction.Oracle.LoggedExecution
public import ArkLib.ProofSystem.Logup.Algebra.ArithmeticReconstruction
public import ArkLib.ToCompPoly.Univariate.ArithmeticHorner
import ArkLib.Interaction.Oracle.SourceRouting

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
carrier's Inv/DecidableEq instances; reconstruction requests no inversion.

The complete logged packet laws preserve the actual weighted prefix, scalar multiplicity sender
and tuple beta response, including dependent private outputs and effects. The native suffix then
authenticates the boundary Q at its actual returned challenges, appending its ordered raw trace.
Final rejection still authenticates Q; public round abort has no terminal tail. Reached sampler
phases and honest private-query observations are stated in separate consumer laws.
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
    rw [Access.simulateQ_queryPrior_withQueryLog]
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
    rw [Access.simulateQ_queryPrior_withQueryLog]
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
    rw [Access.simulateQ_queryPrior_withQueryLog, List.length_map, tuple_queryValue_log_length]
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


set_option backward.isDefEq.respectTransparency false in
/-- The actual suffix authenticates Q at its returned challenges, preserving the full packet.
The native message log is followed by the routed boundary Q log, including final rejection. -/
theorem qView_complete_log_eq_boundary [DecidableEq E] (f : B →+* E) (n T K ell : Nat)
    (groups : Vector (List (Fin T)) K) (alpha : E) (z : Fin n → E) (lambda : Fin K → E)
    {ι : Type} (ambient : OracleSpec ι) (roundDraw : OracleComp ambient E)
    (A : PFunctor.{0, 0}) (view : VirtualOracle (ofPFunctor A) (inputFamily f n T))
    (impl : QueryImpl (ofPFunctor A) Id) (helpers : Vector (CMlPolynomialEval E n) K)
    {OutP : (Sumcheck.Interaction.Computable.protocol E (ell + 2) n).tree.ExecutionPath → Type}
    (prover : Prover.Strategy ambient
      (Sumcheck.Interaction.Computable.protocol E (ell + 2) n).tree
      (Sumcheck.Interaction.Computable.protocol E (ell + 2) n).roles OutP) :
    LoggedResult.observe <$> executeStrategiesLogged ambient
      (Sumcheck.Interaction.Computable.protocol E (ell + 2) n).tree
      (Sumcheck.Interaction.Computable.protocol E (ell + 2) n).roles
      (Sumcheck.Interaction.Computable.protocol E (ell + 2) n).oracles
      (Access.extend A (helperInterface (E := E) n K))
      (Access.extendImpl A (helperInterface (E := E) n K) impl helpers) prover
      (Sumcheck.Interaction.Computable.verifierWithFinalCheck E n (ell + 2) ambient roundDraw
        [0, 1] n 0 (Nat.zero_add n) (Access.extend A (helperInterface (E := E) n K))
        (qView f n T K groups alpha z lambda ell A view) (zeroStatement E n)) = (do
      let result ← executeStrategiesLogged ambient
        (Sumcheck.Interaction.Computable.protocol E (ell + 2) n).tree
        (Sumcheck.Interaction.Computable.protocol E (ell + 2) n).roles
        (Sumcheck.Interaction.Computable.protocol E (ell + 2) n).oracles
        (Access.extend A (helperInterface (E := E) n K))
        (Access.extendImpl A (helperInterface (E := E) n K) impl helpers) prover
        (Sumcheck.Interaction.Computable.verifier E n (ell + 2) ambient roundDraw [0, 1] n 0
          (Nat.zero_add n) (Access.extend A (helperInterface (E := E) n K))
          (qView f n T K groups alpha z lambda ell A view) (zeroStatement E n))
      match result.verifierOut with
      | none => return ⟨result.path, result.proverOut, false, result.sourceLog⟩
      | some claim =>
        let boundary := simulateQ
          (Access.extendImpl A (helperInterface (E := E) n K) impl helpers)
          (queryQ f n T K groups alpha z lambda A view claim.stmt.challenges).withQueryLog
        return ⟨result.path, result.proverOut, decide (boundary.1 = claim.stmt.target),
          result.sourceLog ++ TypeTree.routeLog
            (Sumcheck.Interaction.Computable.protocol E (ell + 2) n).tree
            (Sumcheck.Interaction.Computable.protocol E (ell + 2) n).oracles
            (Access.extend A (helperInterface (E := E) n K))
            result.path.toBranchPath boundary.2⟩) := by
  unfold LoggedResult.observe
  erw [Sumcheck.Interaction.Computable.Resources.complete_log_eq]
  apply OracleComp.bind_congr_of_forall_mem_support
  intro result hresult
  cases hc : result.verifierOut with
  | none => rfl
  | some claim =>
    have h := Sumcheck.Interaction.Computable.Resources.logged_final_query_eq_boundary
      n (ell + 2) ambient roundDraw n 0 (Nat.zero_add n)
      (Access.extend A (helperInterface (E := E) n K))
      (qView f n T K groups alpha z lambda ell A view) (zeroStatement E n)
      (Access.extendImpl A (helperInterface (E := E) n K) impl helpers)
      prover result hresult claim hc
    simp only
    erw [h]
    rfl

set_option backward.isDefEq.respectTransparency false in
/-- A reached final claim contributes the actual original fanouts plus retained helpers.
The preceding message count comes from the same supported bare run.
The final Bool is unrestricted. -/
theorem qView_final_log_length [DecidableEq E] (f : B →+* E) (n T K ell : Nat)
    (groups : Vector (List (Fin T)) K) (alpha : E) (z : Fin n → E) (lambda : Fin K → E)
    {ι : Type} (ambient : OracleSpec ι) (roundDraw : OracleComp ambient E)
    (A : PFunctor.{0, 0}) (view : VirtualOracle (ofPFunctor A) (inputFamily f n T))
    (impl : QueryImpl (ofPFunctor A) Id) (helpers : Vector (CMlPolynomialEval E n) K)
    {OutP : (Sumcheck.Interaction.Computable.protocol E (ell + 2) n).tree.ExecutionPath → Type}
    (prover : Prover.Strategy ambient
      (Sumcheck.Interaction.Computable.protocol E (ell + 2) n).tree
      (Sumcheck.Interaction.Computable.protocol E (ell + 2) n).roles OutP) :
    ∀ result ∈ support (executeStrategiesLogged ambient
        (Sumcheck.Interaction.Computable.protocol E (ell + 2) n).tree
        (Sumcheck.Interaction.Computable.protocol E (ell + 2) n).roles
        (Sumcheck.Interaction.Computable.protocol E (ell + 2) n).oracles
        (Access.extend A (helperInterface (E := E) n K))
        (Access.extendImpl A (helperInterface (E := E) n K) impl helpers) prover
        (Sumcheck.Interaction.Computable.verifier E n (ell + 2) ambient roundDraw [0, 1] n 0
          (Nat.zero_add n) (Access.extend A (helperInterface (E := E) n K))
          (qView f n T K groups alpha z lambda ell A view) (zeroStatement E n))),
      ∀ claim, result.verifierOut = some claim →
      (result.sourceLog ++ (simulateQ
        (result.path.closingImpl
          (Sumcheck.Interaction.Computable.protocol E (ell + 2) n).oracles
          (Access.extend A (helperInterface (E := E) n K))
          (Access.extendImpl A (helperInterface (E := E) n K) impl helpers))
        (claim.oracles.query ⟨(), claim.stmt.challenges⟩).withQueryLog).run.2).length =
      (Sumcheck.Interaction.Computable.Resources.pathUsage (ell + 2) n
        result.path).messageQueries +
        (((List.finRange T).map fun i =>
          (simulateQ impl (view.query ⟨(0, i), claim.stmt.challenges⟩).withQueryLog).2.length).sum +
        ((List.finRange T).map fun i =>
          (simulateQ impl (view.query ⟨(1, i), claim.stmt.challenges⟩).withQueryLog).2.length).sum +
          K) := by
  intro result hresult claim hclaim
  have ht := Sumcheck.Interaction.Computable.Resources.logged_final_query_eq_boundary
    n (ell + 2) ambient roundDraw n 0 (Nat.zero_add n)
    (Access.extend A (helperInterface (E := E) n K))
    (qView f n T K groups alpha z lambda ell A view) (zeroStatement E n)
    (Access.extendImpl A (helperInterface (E := E) n K) impl helpers)
    prover result hresult claim hclaim
  have hu := Sumcheck.Interaction.Computable.Resources.logged_verifier_usage
    n (ell + 2) ambient roundDraw n 0 (Nat.zero_add n)
    (Access.extend A (helperInterface (E := E) n K))
    (qView f n T K groups alpha z lambda ell A view) (zeroStatement E n)
    (Access.extendImpl A (helperInterface (E := E) n K) impl helpers)
    prover result hresult
  have hl := congrArg (fun packet => packet.2.length) ht
  simp only [TypeTree.routeLog_length] at hl
  rw [List.length_append, hu.1, hl]
  exact congrArg (fun size =>
    (Sumcheck.Interaction.Computable.Resources.pathUsage (ell + 2) n result.path).messageQueries +
      size) (queryQ_log_length f n T K groups alpha z lambda A view impl helpers
        claim.stmt.challenges)

section WeightedEndpoint

variable [DecidableEq E] (ell : Nat) (cfg : Config n T ell)
variable {ι : Type} (ambient : OracleSpec ι)

set_option backward.isDefEq.respectTransparency false in
/-- The actual weighted verifier exports its retained Q view into the native suffix. -/
theorem verifier_eq_prefix (alphaDraw : OracleComp ambient E)
    (jointDraw : OracleComp ambient ((Fin n → E) × (Fin (T ⌈/⌉ ell) → E)))
    (roundDraw : OracleComp ambient E) (A : PFunctor.{0, 0})
    (inputView : VirtualOracle (ofPFunctor A) (inputFamily f n T)) :
    verifier f n T ell cfg ambient alphaDraw jointDraw roundDraw A inputView = (do
      let alpha ← alphaDraw.liftComp (ambient + ofPFunctor A)
      return ⟨alpha, pure (do
        let joint ← jointDraw.liftComp
          (ambient + ofPFunctor (Access.extend A (helperInterface (E := E) n (T ⌈/⌉ ell))))
        return ⟨joint,
          Sumcheck.Interaction.Native.Core.verifierWithFinalCheck E n (ell + 2)
            (Sumcheck.Impl.Representation.Message E (ell + 2))
            (Sumcheck.Impl.Representation.evaluate E (ell + 2)) ambient roundDraw [0, 1] n 0
            (Nat.zero_add n) (Access.extend A (helperInterface (E := E) n (T ⌈/⌉ ell)))
            (qView f n T (T ⌈/⌉ ell) cfg.groups alpha joint.1 joint.2 ell A inputView)
            (zeroStatement E n)⟩)⟩) := by
  simp only [verifier, reductionVerifier, Verifier.appendExported,
    suffixVerifier, Sumcheck.Interaction.Computable.verifier]
  simp_rw [Sumcheck.Interaction.Native.Core.routeClaimStrategy_verifier]
  simp only [VirtualOracle.substSource, VirtualOracle.id, QueryImpl.compose_id']
  simp only [Interaction.Oracle.Verifier.append, Interaction.Oracle.Verifier.appendFragment,
    protocol, prefixProtocol, prefixVerifier,
    Protocol.public_tree, Protocol.public_roles, Protocol.public_oracles,
    Protocol.done_tree, Protocol.done_roles, Protocol.done_oracles,
    Protocol.oracleWith_tree, Protocol.oracleWith_roles, Protocol.oracleWith_oracles,
    Verifier.Fragment.mapOutput, Interaction.ShapeOver.mapOutput,
    Verifier.localShape, Verifier.decorate,
    PFunctor.FreeM.append, PFunctor.FreeM.Displayed.Decoration.append]
  simp only [map_bind, map_pure, TypeTree.accessAfter_public,
    TypeTree.accessAfter_oracle, TypeTree.accessAfter_done]
  apply bind_congr
  intro alpha
  congr 3
  apply bind_congr
  intro joint
  congr 2
  change Verifier.Fragment.mapOutput ambient
    (fun path action => Sumcheck.Interaction.Native.Core.checkFinalResult E n (ell + 2)
      ambient (TypeTree.accessAfter
        (Sumcheck.Interaction.Computable.protocol E (ell + 2) n).tree
        (Sumcheck.Interaction.Computable.protocol E (ell + 2) n).oracles
        (Access.extend A (helperInterface (E := E) n (T ⌈/⌉ ell))) path) action)
    (Verifier.Fragment.mapOutput ambient (fun _ action => action)
      (Verifier.Fragment.mapOutput ambient (fun _ action => (fun out => out) <$> action)
        (Sumcheck.Interaction.Computable.verifier E n (ell + 2) ambient roundDraw [0, 1]
          n 0 (Nat.zero_add n) (Access.extend A (helperInterface (E := E) n (T ⌈/⌉ ell)))
          (qView f n T (T ⌈/⌉ ell) cfg.groups alpha joint.1 joint.2 ell A inputView)
          (zeroStatement E n)))) = _
  simp only [id_map', Verifier.Fragment.mapOutput_id]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Actual prefix and native execution preserve the full path, private output and raw log. -/
theorem executeStrategiesLogged_eq_prefix_bind (alphaDraw : OracleComp ambient E)
    (jointDraw : OracleComp ambient ((Fin n → E) × (Fin (T ⌈/⌉ ell) → E)))
    (roundDraw : OracleComp ambient E) (A : PFunctor.{0, 0})
    (inputView : VirtualOracle (ofPFunctor A) (inputFamily f n T))
    (impl : QueryImpl (ofPFunctor A) Id)
    {OutP : (protocol E n (T ⌈/⌉ ell) ell).tree.ExecutionPath → Type}
    (wholeProver : Prover.Strategy ambient (protocol E n (T ⌈/⌉ ell) ell).tree
      (protocol E n (T ⌈/⌉ ell) ell).roles OutP) :
    LoggedResult.observe <$> executeStrategiesLogged ambient (protocol E n (T ⌈/⌉ ell) ell).tree
      (protocol E n (T ⌈/⌉ ell) ell).roles (protocol E n (T ⌈/⌉ ell) ell).oracles A
      impl wholeProver (verifier f n T ell cfg ambient alphaDraw jointDraw roundDraw A inputView) =
      (do
        let alpha ← alphaDraw
        let afterAlpha ← wholeProver alpha
        let sent ← afterAlpha
        let joint ← jointDraw
        let suffix ← sent.2 joint
        let result ← executeStrategiesLogged ambient
          (Sumcheck.Interaction.Computable.protocol E (ell + 2) n).tree
          (Sumcheck.Interaction.Computable.protocol E (ell + 2) n).roles
          (Sumcheck.Interaction.Computable.protocol E (ell + 2) n).oracles
          (Access.extend A (helperInterface (E := E) n (T ⌈/⌉ ell)))
          (Access.extendImpl A (helperInterface (E := E) n (T ⌈/⌉ ell)) impl sent.1)
          (OutP := fun path => OutP ⟨alpha, ⟨sent.1, ⟨joint, path⟩⟩⟩) suffix
          (Sumcheck.Interaction.Computable.verifierWithFinalCheck E n (ell + 2) ambient
            roundDraw [0, 1] n 0 (Nat.zero_add n)
            (Access.extend A (helperInterface (E := E) n (T ⌈/⌉ ell)))
            (qView f n T (T ⌈/⌉ ell) cfg.groups alpha joint.1 joint.2 ell A inputView)
            (zeroStatement E n))
        return ⟨⟨alpha, ⟨sent.1, ⟨joint, result.path⟩⟩⟩, result.proverOut,
          result.verifierOut, result.sourceLog⟩) := by
  rw [verifier_eq_prefix]
  simp only [protocol, prefixProtocol, Protocol.public_tree, Protocol.public_roles,
    Protocol.public_oracles, Protocol.oracleWith_tree, Protocol.oracleWith_roles,
    Protocol.oracleWith_oracles, Protocol.done_tree, Protocol.done_roles,
    Protocol.done_oracles, PFunctor.FreeM.append, PFunctor.FreeM.Displayed.Decoration.append,
    executeStrategiesLogged, map_bind, map_pure, LoggedResult.observe, TypeTree.routeLog]
  simp only [simulateQ_bind, simulateQ_pure, WriterT.run_bind', WriterT.run_pure',
    Verifier.loggedLiftAccessImpl_liftComp, bind_map_left, pure_bind, map_pure,
    bind_assoc, Prod.map, id_eq, List.nil_append]
  simp only [List.empty_eq, List.map_nil, List.nil_append]
  rfl

end WeightedEndpoint


section LookupEndpoint

variable [DecidableEq E] (ell : Nat) (cfg : Logup.Lookup.Config B n M P ell)
variable {ι : Type} (ambient : OracleSpec ι)

set_option backward.isDefEq.respectTransparency false in
/-- The actual scalar sender retains its multiplicity slot and complete weighted packet. -/
theorem scalar_executeStrategiesLogged_eq_sender_bind (alphaDraw : OracleComp ambient E)
    (jointDraw : OracleComp ambient ((Fin n → E) × (Fin ((M + P) ⌈/⌉ ell) → E)))
    (roundDraw : OracleComp ambient E) (A : PFunctor.{0, 0})
    (valuesView : VirtualOracle (ofPFunctor A) (Logup.Lookup.valuesFamily f n M P))
    (impl : QueryImpl (ofPFunctor A) Id)
    {OutP : (Logup.Lookup.protocol f n M P ell).tree.ExecutionPath → Type}
    (wholeProver : Prover.Strategy ambient (Logup.Lookup.protocol f n M P ell).tree
      (Logup.Lookup.protocol f n M P ell).roles OutP) :
    LoggedResult.observe <$>
      executeStrategiesLogged ambient (Logup.Lookup.protocol f n M P ell).tree
      (Logup.Lookup.protocol f n M P ell).roles (Logup.Lookup.protocol f n M P ell).oracles A
      impl wholeProver
      (Logup.Lookup.verifier f n M P ell cfg ambient alphaDraw jointDraw roundDraw A valuesView) =
      (do
        let sent ← wholeProver
        let result ← executeStrategiesLogged ambient
          (Logup.Interaction.protocol E n ((M + P) ⌈/⌉ ell) ell).tree
          (Logup.Interaction.protocol E n ((M + P) ⌈/⌉ ell) ell).roles
          (Logup.Interaction.protocol E n ((M + P) ⌈/⌉ ell) ell).oracles
          (Access.extend A (Logup.Lookup.multiplicityInterface f n P))
          (Access.extendImpl A (Logup.Lookup.multiplicityInterface f n P) impl sent.1)
          (OutP := fun path => OutP ⟨sent.1, path⟩) sent.2
          (Logup.Interaction.verifier f n (M + P) ell cfg.weighted ambient alphaDraw jointDraw
            roundDraw (Access.extend A (Logup.Lookup.multiplicityInterface f n P))
            (Logup.Lookup.weightedView f n M P A valuesView))
        return ⟨⟨sent.1, result.path⟩, result.proverOut,
          result.verifierOut, result.sourceLog⟩) := by
  simp only [Logup.Lookup.protocol, Protocol.oracleWith_tree, Protocol.oracleWith_roles,
    Protocol.oracleWith_oracles, Logup.Lookup.verifier, executeStrategiesLogged,
    simulateQ_pure, WriterT.run_pure', pure_bind, map_bind, map_pure, LoggedResult.observe,
    TypeTree.routeLog, List.empty_eq, List.map_nil, List.nil_append]

set_option backward.isDefEq.respectTransparency false in
/-- The actual tuple sender and beta response retain their effects and complete weighted packet. -/
theorem tuple_executeStrategiesLogged_eq_sender_beta_bind
    (betaDraw alphaDraw : OracleComp ambient E)
    (jointDraw : OracleComp ambient ((Fin n → E) × (Fin ((M + P) ⌈/⌉ ell) → E)))
    (roundDraw : OracleComp ambient E) (A : PFunctor.{0, 0})
    (coeffView : VirtualOracle (ofPFunctor A) (Logup.Lookup.Tuple.coefficientFamily f n M P W))
    (impl : QueryImpl (ofPFunctor A) Id)
    {OutP : (Logup.Lookup.Tuple.protocol f n M P ell).tree.ExecutionPath → Type}
    (wholeProver : Prover.Strategy ambient (Logup.Lookup.Tuple.protocol f n M P ell).tree
      (Logup.Lookup.Tuple.protocol f n M P ell).roles OutP) :
    LoggedResult.observe <$>
      executeStrategiesLogged ambient (Logup.Lookup.Tuple.protocol f n M P ell).tree
        (Logup.Lookup.Tuple.protocol f n M P ell).roles
        (Logup.Lookup.Tuple.protocol f n M P ell).oracles A impl wholeProver
        (Logup.Lookup.Tuple.verifier f n M P W ell cfg ambient betaDraw alphaDraw jointDraw
          roundDraw A coeffView) =
      (do
        let sent ← wholeProver
        let beta ← betaDraw
        let suffix ← sent.2 beta
        let result ← executeStrategiesLogged ambient
          (Logup.Interaction.protocol E n ((M + P) ⌈/⌉ ell) ell).tree
          (Logup.Interaction.protocol E n ((M + P) ⌈/⌉ ell) ell).roles
          (Logup.Interaction.protocol E n ((M + P) ⌈/⌉ ell) ell).oracles
          (Access.extend A (Logup.Lookup.multiplicityInterface f n P))
          (Access.extendImpl A (Logup.Lookup.multiplicityInterface f n P) impl sent.1)
          (OutP := fun path => OutP ⟨sent.1, ⟨beta, path⟩⟩) suffix
          (Logup.Interaction.verifier (RingHom.id E) n (M + P) ell cfg.weighted ambient
            alphaDraw jointDraw roundDraw
            (Access.extend A (Logup.Lookup.multiplicityInterface f n P))
            (Logup.Lookup.Tuple.weightedView f n M P W beta A coeffView))
        return ⟨⟨sent.1, ⟨beta, result.path⟩⟩, result.proverOut,
          result.verifierOut, result.sourceLog⟩) := by
  simp only [Logup.Lookup.Tuple.protocol, Protocol.oracleWith_tree, Protocol.oracleWith_roles,
    Protocol.oracleWith_oracles, Protocol.public_tree, Protocol.public_roles,
    Protocol.public_oracles, Logup.Lookup.Tuple.verifier, executeStrategiesLogged,
    simulateQ_bind, simulateQ_pure, WriterT.run_bind', WriterT.run_pure',
    Verifier.loggedLiftAccessImpl_liftComp, pure_bind, map_bind, map_pure, LoggedResult.observe,
    bind_map_left, bind_assoc, Prod.map, id_eq,
    TypeTree.routeLog, List.empty_eq, List.map_nil, List.nil_append]
  rfl

end LookupEndpoint

end Logup.Interaction.Resources

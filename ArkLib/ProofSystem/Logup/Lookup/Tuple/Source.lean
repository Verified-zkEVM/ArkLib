/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
module

public import ArkLib.ProofSystem.Logup.Lookup.Tuple.Provider
public import ArkLib.ProofSystem.Logup.Lookup.Source
public import CompPoly.Univariate.ToPoly.Core
public import ArkLib.ToCompPoly.Univariate.Raw.Basic
public import ArkLib.Data.OracleComp.Vector
-- The coefficient bound proof unfolds the defining raw coefficient getter.
import all CompPoly.Univariate.Raw.Core

/-!
# Tuple lookup sources from fixed coefficient columns

The original source exposes the eagerly stored padded coefficient columns. At any challenge-field
point, the runtime program opens these coefficient MLEs and uses the shared seeded Horner evaluator.
It never interprets a semantic bus or payload away from Boolean rows. The value-source theorem
identifies this linear combination with the MLE of the compressed Boolean keys.

The weighted view retains the actual base-field multiplicity message, returns query weight1 and
negates mapped table multiplicities. Its realization holds for every fingerprint challenge and
every multiplicity message, with no lookup truth, ownership assumption beyond the prepared source,
field characteristic or honest-message premise. A later helper source retains this entire view.
No table is constructed or fingerprint polynomial allocated while answering a source query.
-/

@[expose] public section
open CompPoly
open scoped BigOperators
namespace Logup.Lookup.Tuple
variable {B E : Type} [CommRing B] [CommRing E]

open _root_.Interaction.Oracle OracleComp OracleSpec

/-- Stored padded coefficient columns, queried through the explicit base-to-challenge map. -/
def coefficientFamily (f : B →+* E) (n M P W : Nat) :
    OracleFamily ((Fin M ⊕ Fin P) × Fin (W + 1)) (fun _ => CMlPolynomialEval B n) :=
  ⟨fun _ => Logup.Interaction.baseTableInterface f n⟩

/-- Open all coefficient MLEs once and evaluate their scalar Horner combination. -/
def queryValue (f : B →+* E) (n M P W : Nat) (beta : E) (A : PFunctor.{0, 0})
    (view : VirtualOracle (ofPFunctor A) (coefficientFamily f n M P W))
    (slot : Fin M ⊕ Fin P) (x : Fin n → E) : OracleComp (ofPFunctor A) E := do
  let coeffs : Vector E (W + 1) ← Vector.ofFnM fun j => view.query ⟨(slot, j), x⟩
  return CPolynomial.Raw.evalHornerSeeded beta coeffs.toArray

/-- Compressed Boolean rows; this reference table is not rebuilt by source queries. -/
def PreparedProvider.fingerprintData {b W n M P : Nat} {schema : TaggedTuple.Schema B b W}
    {layout : ProviderLayout b P} (prepared : PreparedProvider schema layout n M)
    (f : B →+* E) (beta : E) : Data E n M P :=
  fun slot => Vector.map (schema.fingerprint f beta) (prepared.keyData slot)

/-- Export the coefficient-Horner program as a scalar value source. -/
def valuesView (f : B →+* E) (n M P W : Nat) (beta : E) (A : PFunctor.{0, 0})
    (view : VirtualOracle (ofPFunctor A) (coefficientFamily f n M P W)) :
    VirtualOracle (ofPFunctor A) (Logup.Lookup.valuesFamily (RingHom.id E) n M P) :=
  ⟨fun q => queryValue f n M P W beta A view q.1 q.2⟩

set_option backward.isDefEq.respectTransparency false in
/-- The actual program opens every stored coefficient once and combines its returned scalar. -/
theorem queryValue_eval (f : B →+* E) (n M P W : Nat) (beta : E) (A : PFunctor.{0, 0})
    (view : VirtualOracle (ofPFunctor A) (coefficientFamily f n M P W))
    (impl : QueryImpl (ofPFunctor A) Id)
    (tables : (Fin M ⊕ Fin P) × Fin (W + 1) → CMlPolynomialEval B n)
    (hinput : view.eval impl = (coefficientFamily f n M P W).behaviorOfRealizations tables)
    (slot : Fin M ⊕ Fin P) (x : Fin n → E) :
    simulateQ impl (queryValue f n M P W beta A view slot x) =
      ∑ j : Fin (W + 1), CMlPolynomialEval.eval₂Mle (tables (slot, j)) f (Vector.ofFn x)
        * beta ^ j.val := by
  have hq (j : Fin (W + 1)) : simulateQ impl (view.query ⟨(slot, j), x⟩) =
      CMlPolynomialEval.eval₂Mle (tables (slot, j)) f (Vector.ofFn x) :=
    congrFun hinput ⟨(slot, j), x⟩
  simp only [queryValue, simulateQ_bind, simulateQ_pure, simulateQ_ofFnM, hq]
  change CPolynomial.Raw.evalHornerSeeded beta
    (Vector.ofFn fun j => CMlPolynomialEval.eval₂Mle (tables (slot, j)) f
      (Vector.ofFn x)).toArray = _
  rw [CPolynomial.Raw.evalHornerSeeded_toArray_eq_sum]
  simp only [Vector.getElem_ofFn]

private theorem eval_fingerprintData {b W n M P : Nat} {schema : TaggedTuple.Schema B b W}
    {layout : ProviderLayout b P} (prepared : PreparedProvider schema layout n M)
    (f : B →+* E) (beta : E) (slot : Fin M ⊕ Fin P) (x : Fin n → E) :
    CMlPolynomialEval.eval₂Mle (prepared.fingerprintData f beta slot) (RingHom.id E)
      (Vector.ofFn x) =
    ∑ j : Fin (W + 1), CMlPolynomialEval.eval₂Mle (prepared.coefficientTable slot j) f
      (Vector.ofFn x) * beta ^ j.val := by
  simp only [CMlPolynomialEval.eval₂Mle_eq_MvPolynomial_MLE, MvPolynomial.MLE_eval,
    PreparedProvider.fingerprintData, Vector.get_eq_getElem, Vector.getElem_map,
    RingHom.id_apply, TaggedTuple.Schema.fingerprint_eq_sum_coefficient]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro u _
  rw [show (prepared.coefficientTable slot j)[(finFunctionFinEquiv u).val] =
      schema.coefficient ((prepared.keyData slot).get (finFunctionFinEquiv u)) j from
    prepared.get_coefficientTable slot j (finFunctionFinEquiv u)]
  simp only [Vector.get_eq_getElem]
  ring

set_option backward.isDefEq.respectTransparency false in
/-- Every stored coefficient source realizes the compressed value MLE at every field point. -/
theorem valuesView_realizes {b W n M P : Nat} {schema : TaggedTuple.Schema B b W}
    {layout : ProviderLayout b P} (prepared : PreparedProvider schema layout n M)
    (f : B →+* E) (beta : E) (A : PFunctor.{0, 0})
    (view : VirtualOracle (ofPFunctor A) (coefficientFamily f n M P W))
    (impl : QueryImpl (ofPFunctor A) Id)
    (hinput : view.eval impl = (coefficientFamily f n M P W).behaviorOfRealizations
      (fun sj => prepared.coefficientTable sj.1 sj.2)) :
    (valuesView f n M P W beta A view).eval impl =
      (Logup.Lookup.valuesFamily (RingHom.id E) n M P).behaviorOfRealizations
        (prepared.fingerprintData f beta) := by
  funext q
  rcases q with ⟨slot,x⟩
  change (Fin n → E) at x
  change simulateQ impl (queryValue f n M P W beta A view slot x) =
    CMlPolynomialEval.eval₂Mle (prepared.fingerprintData f beta slot) (RingHom.id E)
      (Vector.ofFn x)
  rw [queryValue_eval f n M P W beta A view impl _ hinput slot x,
    eval_fingerprintData]

/-- Compressed values and the mapped retained multiplicities in the weighted scalar language. -/
def PreparedProvider.weightedData {b W n M P : Nat} {schema : TaggedTuple.Schema B b W}
    {layout : ProviderLayout b P} (prepared : PreparedProvider schema layout n M)
    (f : B →+* E) (beta : E) (mu : Vector (CMlPolynomialEval B n) P) :
    Fin 2 × Fin (M + P) → CMlPolynomialEval E n :=
  Logup.Lookup.weightedData (prepared.fingerprintData f beta)
    (Vector.map (CMlPolynomialEval.map f) mu)

/-- Read compressed coefficient values, unit query weights, or the retained base multiplicity. -/
def queryWeighted (f : B →+* E) (n M P W : Nat) (beta : E) (A : PFunctor.{0, 0})
    (view : VirtualOracle (ofPFunctor A) (coefficientFamily f n M P W))
    (kind : Fin 2) (i : Fin (M + P)) (x : Fin n → E) :
    OracleComp (ofPFunctor (Access.extend A (multiplicityInterface f n P))) E :=
  if kind = 0 then
    ((valuesView f n M P W beta A view).substSource
      (Access.queryPrior A (multiplicityInterface f n P))).query ⟨finSumFinEquiv.symm i, x⟩
  else match finSumFinEquiv.symm i with
  | .inl _ => pure 1
  | .inr p => do
    let answer : E ← Access.queryLatest A (multiplicityInterface f n P) (p, x)
    return -answer

/-- The weighted source retains original coefficients and the actual base multiplicity slot. -/
def weightedView (f : B →+* E) (n M P W : Nat) (beta : E) (A : PFunctor.{0, 0})
    (view : VirtualOracle (ofPFunctor A) (coefficientFamily f n M P W)) :
    VirtualOracle (ofPFunctor (Access.extend A (multiplicityInterface f n P)))
      (Logup.Interaction.inputFamily (RingHom.id E) n (M + P)) :=
  ⟨fun q => queryWeighted f n M P W beta A view q.1.1 q.1.2 q.2⟩

private theorem eval₂Mle_map (f : B →+* E) {n : Nat}
    (table : CMlPolynomialEval B n) (x : Fin n → E) :
    CMlPolynomialEval.eval₂Mle (CMlPolynomialEval.map f table) (RingHom.id E)
      (Vector.ofFn x) = CMlPolynomialEval.eval₂Mle table f (Vector.ofFn x) := by
  simp [CMlPolynomialEval.eval₂Mle, CMlPolynomialEval.map, Function.comp_def]

private theorem map_weightedData_weight (f : B →+* E) {n M P : Nat}
    (dataB : Data B n M P) (dataE : Data E n M P)
    (mu : Vector (CMlPolynomialEval B n) P) (i : Fin (M + P)) :
    CMlPolynomialEval.map f (Logup.Lookup.weightedData dataB mu (1, i)) =
      Logup.Lookup.weightedData dataE (Vector.map (CMlPolynomialEval.map f) mu) (1, i) := by
  simp only [Logup.Lookup.weightedData, show (1 : Fin 2) ≠ 0 by decide, ↓reduceIte]
  generalize finSumFinEquiv.symm i = slot
  cases slot <;> simp [CMlPolynomialEval.map, Vector.map_map, Function.comp_def]

set_option backward.isDefEq.respectTransparency false in
/-- The exact retained coefficient and multiplicity sources realize weighted compressed tables. -/
theorem weightedView_realizes {b W n M P : Nat} {schema : TaggedTuple.Schema B b W}
    {layout : ProviderLayout b P} (prepared : PreparedProvider schema layout n M)
    (f : B →+* E) (beta : E) (A : PFunctor.{0, 0})
    (view : VirtualOracle (ofPFunctor A) (coefficientFamily f n M P W))
    (impl : QueryImpl (ofPFunctor A) Id)
    (hinput : view.eval impl = (coefficientFamily f n M P W).behaviorOfRealizations
      (fun sj => prepared.coefficientTable sj.1 sj.2))
    (mu : Vector (CMlPolynomialEval B n) P) :
    (weightedView f n M P W beta A view).eval
      (Access.extendImpl A (multiplicityInterface f n P) impl mu) =
      (Logup.Interaction.inputFamily (RingHom.id E) n (M + P)).behaviorOfRealizations
        (prepared.weightedData f beta mu) := by
  let zeroView : VirtualOracle (ofPFunctor A) (Logup.Lookup.valuesFamily f n M P) :=
    ⟨fun q => view.query ⟨(q.1, 0),q.2⟩⟩
  let zeroData : Data B n M P := fun slot => prepared.coefficientTable slot 0
  have hzero : zeroView.eval impl =
      (Logup.Lookup.valuesFamily f n M P).behaviorOfRealizations zeroData := by
    funext q
    exact congrFun hinput ⟨(q.1, 0),q.2⟩
  have hweights := Logup.Lookup.weightedView_realizes f n M P A zeroView impl zeroData hzero mu
  have hext : QueryImpl.compose
      (Access.extendImpl A (multiplicityInterface f n P) impl mu)
      (Access.queryPrior A (multiplicityInterface f n P)) = impl := by
    funext q
    exact Access.eval_queryPrior A (multiplicityInterface f n P) impl mu q
  have hprior : ((valuesView f n M P W beta A view).substSource
      (Access.queryPrior A (multiplicityInterface f n P))).eval
        (Access.extendImpl A (multiplicityInterface f n P) impl mu) =
      (Logup.Lookup.valuesFamily (RingHom.id E) n M P).behaviorOfRealizations
        (prepared.fingerprintData f beta) := by
    rw [VirtualOracle.eval_substSource, hext]
    exact valuesView_realizes prepared f beta A view impl hinput
  funext q
  rcases q with ⟨⟨kind, i⟩,x⟩
  change (Fin n → E) at x
  change simulateQ (Access.extendImpl A (multiplicityInterface f n P) impl mu)
      (queryWeighted f n M P W beta A view kind i x) =
    CMlPolynomialEval.eval₂Mle (prepared.weightedData f beta mu (kind, i)) (RingHom.id E)
      (Vector.ofFn x)
  by_cases hk : kind = 0
  · subst kind
    simp only [queryWeighted, ↓reduceIte, PreparedProvider.weightedData,
      Logup.Lookup.weightedData_value]
    exact congrFun hprior ⟨finSumFinEquiv.symm i, x⟩
  · have hk1 : kind = 1 := Fin.eq_one_of_ne_zero kind hk
    subst kind
    have hw := congrFun hweights ⟨(1, i), x⟩
    change simulateQ (Access.extendImpl A (multiplicityInterface f n P) impl mu)
        (Logup.Lookup.queryWeighted f n M P A zeroView 1 i x) =
      CMlPolynomialEval.eval₂Mle (Logup.Lookup.weightedData zeroData mu (1, i)) f
        (Vector.ofFn x) at hw
    simp only [queryWeighted, Logup.Lookup.queryWeighted, hk, ↓reduceIte] at hw ⊢
    unfold PreparedProvider.weightedData
    rw [← map_weightedData_weight f zeroData, eval₂Mle_map]
    exact hw

end Logup.Lookup.Tuple

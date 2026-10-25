/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
module

public import ArkLib.ProofSystem.Logup.Algebra.Grouped
public import ArkLib.ProofSystem.Sumcheck.Interaction.MultivariateRound
public import ArkLib.ToCompPoly.Multilinear.Basic
public import ArkLib.Data.OracleComp.Vector

/-!
# Retained-source realization of scalar LogUp

Base tables are queried through an explicit scalar map; helpers are arbitrary challenge-ring
Boolean tables. The Q program binds each logical value, weight and helper answer once before
calling the existing scalar reconstruction. Its underlying source-query cost follows the supplied
input view, which may perform several raw openings per logical answer.

The virtual Q view retains the actual original source and newest helper slot. Its realization
holds for every helper table, including at denominator poles, with no honest-helper or initial
truth premise. The degree bound comes from the existing grouped polynomial owner. Mathematical
views are individually noncomputable because they use Mathlib's sparse polynomial operations;
the table interfaces, scalar query program and virtual Q view remain executable.
-/

@[expose] public section

namespace Logup.Interaction

open _root_.Interaction.Oracle OracleComp OracleSpec CompPoly

variable {B E : Type} [CommRing B] [CommRing E] (f : B →+* E) (n T K : ℕ)

/-- Query a base table at challenge-ring points through the supplied scalar map. -/
@[reducible] def baseTableInterface : OracleInterface (CMlPolynomialEval B n) where
  Query := Fin n → E
  toOC.spec := (Fin n → E) →ₒ E
  toOC.impl x := do return CMlPolynomialEval.eval₂Mle (← read) f (Vector.ofFn x)

/-- Retained input columns: index zero selects values and index one selects weights. -/
def inputFamily : OracleFamily (Fin 2 × Fin T) (fun _ => CMlPolynomialEval B n) :=
  ⟨fun _ => baseTableInterface f n⟩

/-- Query arbitrary retained helper tables over the challenge ring. -/
@[reducible] def helperInterface : OracleInterface (Vector (CMlPolynomialEval E n) K) where
  Query := Fin K × (Fin n → E)
  toOC.spec := (Fin K × (Fin n → E)) →ₒ E
  toOC.impl q := do
    let tables ← read
    return CMlPolynomialEval.evalMle tables[q.1.val] (Vector.ofFn q.2)

/-- The degree-one Mathlib view of a Boolean table after applying the scalar map. -/
noncomputable def tablePolynomial (table : CMlPolynomialEval B n) :
    MvPolynomial.restrictDegree (Fin n) E 1 :=
  ⟨MvPolynomial.MLE (fun u => f (table.get (finFunctionFinEquiv u))),
    MvPolynomial.MLE_mem_restrictDegree _⟩

/-- Runtime table evaluation agrees with its degree-one mathematical view. -/
theorem eval₂Mle_eq_tablePolynomial (table : CMlPolynomialEval B n) (x : Fin n → E) :
    CMlPolynomialEval.eval₂Mle table f (Vector.ofFn x) =
      MvPolynomial.eval x (tablePolynomial f n table).val :=
  CMlPolynomialEval.eval₂Mle_eq_MvPolynomial_MLE table f x

/-- Read a logical input column through its actual supplied source view. -/
def queryInput (A : PFunctor.{0, 0})
    (inputView : VirtualOracle (ofPFunctor A) (inputFamily f n T))
    (kind : Fin 2) (i : Fin T) (x : Fin n → E) : OracleComp (ofPFunctor A) E :=
  inputView.query ⟨(kind, i), x⟩

/-- Read a helper column from the actual newly retained oracle slot. -/
def queryHelper (A : PFunctor.{0, 0}) (k : Fin K) (x : Fin n → E) :
    OracleComp (ofPFunctor (Access.extend A (helperInterface (E := E) n K))) E :=
  Access.queryLatest A (helperInterface (E := E) n K) (k, x)

/-- Bind each logical column answer once, then run the division-free scalar reconstruction. -/
def queryQ (groups : Vector (List (Fin T)) K) (alpha : E) (z : Fin n → E)
    (lambda : Fin K → E) (A : PFunctor.{0, 0})
    (inputView : VirtualOracle (ofPFunctor A) (inputFamily f n T)) (x : Fin n → E) :
    OracleComp (ofPFunctor (Access.extend A (helperInterface (E := E) n K))) E := do
  let values : Vector E T ← Vector.ofFnM fun i =>
    queryInput f n T (Access.extend A (helperInterface (E := E) n K))
      (inputView.substSource (Access.queryPrior A (helperInterface (E := E) n K))) 0 i x
  let weights : Vector E T ← Vector.ofFnM fun i =>
    queryInput f n T (Access.extend A (helperInterface (E := E) n K))
      (inputView.substSource (Access.queryPrior A (helperInterface (E := E) n K))) 1 i x
  let helpers : Vector E K ← Vector.ofFnM fun k =>
    queryHelper n K A k x
  return Logup.reconstruct groups alpha z lambda x
    (fun i => values[i.val]) (fun i => weights[i.val]) (fun k => helpers[k.val])

/-- Export the actual Q query program through the existing native Sumcheck oracle family. -/
def qView (groups : Vector (List (Fin T)) K) (alpha : E) (z : Fin n → E)
    (lambda : Fin K → E) (ell : ℕ) (A : PFunctor.{0, 0})
    (inputView : VirtualOracle (ofPFunctor A) (inputFamily f n T)) :
    VirtualOracle (ofPFunctor (Access.extend A (helperInterface (E := E) n K)))
      (Sumcheck.Interaction.MultivariateRound.polynomialFamily E n (ell + 2)) :=
  ⟨fun q => queryQ f n T K groups alpha z lambda A inputView q.2⟩

/-- Closing the actual retained sources reconstructs from those same table evaluations. -/
theorem queryQ_eval (groups : Vector (List (Fin T)) K) (alpha : E) (z : Fin n → E)
    (lambda : Fin K → E) (A : PFunctor.{0, 0})
    (inputView : VirtualOracle (ofPFunctor A) (inputFamily f n T))
    (impl : QueryImpl (ofPFunctor A) Id)
    (data : Fin 2 × Fin T → CMlPolynomialEval B n)
    (hinput : inputView.eval impl = (inputFamily f n T).behaviorOfRealizations data)
    (helpers : Vector (CMlPolynomialEval E n) K)
    (x : Fin n → E) :
    simulateQ (Access.extendImpl A (helperInterface (E := E) n K) impl helpers)
        (queryQ f n T K groups alpha z lambda A inputView x) =
      Logup.reconstruct groups alpha z lambda x
        (fun i => CMlPolynomialEval.eval₂Mle (data (0,i)) f (Vector.ofFn x))
        (fun i => CMlPolynomialEval.eval₂Mle (data (1,i)) f (Vector.ofFn x))
        (fun k => CMlPolynomialEval.evalMle helpers[k.val] (Vector.ofFn x)) := by
  have hext : QueryImpl.compose
      (Access.extendImpl A (helperInterface (E := E) n K) impl helpers)
      (Access.queryPrior A (helperInterface (E := E) n K)) = impl := by
    funext t
    exact Access.eval_queryPrior A (helperInterface (E := E) n K) impl helpers t
  have hprior : (inputView.substSource
      (Access.queryPrior A (helperInterface (E := E) n K))).eval
        (Access.extendImpl A (helperInterface (E := E) n K) impl helpers) =
      (inputFamily f n T).behaviorOfRealizations data := by
    rw [VirtualOracle.eval_substSource, hext]
    exact hinput
  have hbase (kind : Fin 2) (i : Fin T) :
      simulateQ (Access.extendImpl A (helperInterface (E := E) n K) impl helpers)
        (queryInput f n T (Access.extend A (helperInterface (E := E) n K))
          (inputView.substSource (Access.queryPrior A (helperInterface (E := E) n K)))
          kind i x) = CMlPolynomialEval.eval₂Mle (data (kind, i)) f (Vector.ofFn x) :=
    congrFun hprior ⟨(kind, i), x⟩
  have hhelper (k : Fin K) :
      simulateQ (Access.extendImpl A (helperInterface (E := E) n K) impl helpers)
        (queryHelper n K A k x) =
      CMlPolynomialEval.evalMle helpers[k.val] (Vector.ofFn x) :=
    Access.eval_queryLatest A (helperInterface (E := E) n K) impl helpers (k, x)
  unfold queryQ
  simp only [simulateQ_bind, simulateQ_pure, simulateQ_ofFnM, hbase, hhelper]
  change Logup.reconstruct groups alpha z lambda x _ _ _ = _
  simp only [Vector.getElem_ofFn]

private theorem eval₂Mle_id (table : CMlPolynomialEval E n) (x : Vector E n) :
    CMlPolynomialEval.eval₂Mle table (RingHom.id E) x = CMlPolynomialEval.evalMle table x := by
  simp [CMlPolynomialEval.eval₂Mle, CMlPolynomialEval.map]

/-- Package the grouped mathematical polynomial with its checked individual-degree bound. -/
noncomputable def qPolynomial (groups : Vector (List (Fin T)) K) (alpha : E)
    (z : Fin n → E) (lambda : Fin K → E) (ell : ℕ)
    (hgroups : ∀ k : Fin K, groups[k.val].length ≤ ell)
    (data : Fin 2 × Fin T → CMlPolynomialEval B n)
    (helpers : Vector (CMlPolynomialEval E n) K) :
    MvPolynomial.restrictDegree (Fin n) E (ell + 2) :=
  Logup.boundedBatchedPolynomial groups alpha z lambda ell hgroups
    (fun i => tablePolynomial f n (data (0,i)))
    (fun i => tablePolynomial f n (data (1,i)))
    (fun k => tablePolynomial (RingHom.id E) n helpers[k.val])

/-- Every retained helper message gives an exact realization of the bounded grouped Q view. -/
theorem qView_realizes (groups : Vector (List (Fin T)) K) (alpha : E) (z : Fin n → E)
    (lambda : Fin K → E) (ell : ℕ)
    (hgroups : ∀ k : Fin K, groups[k.val].length ≤ ell) (A : PFunctor.{0, 0})
    (inputView : VirtualOracle (ofPFunctor A) (inputFamily f n T))
    (impl : QueryImpl (ofPFunctor A) Id)
    (data : Fin 2 × Fin T → CMlPolynomialEval B n)
    (hinput : inputView.eval impl = (inputFamily f n T).behaviorOfRealizations data)
    (helpers : Vector (CMlPolynomialEval E n) K) :
    (qView f n T K groups alpha z lambda ell A inputView).eval
        (Access.extendImpl A (helperInterface (E := E) n K) impl helpers) =
      (Sumcheck.Interaction.MultivariateRound.polynomialFamily E n (ell + 2)).behaviorOfRealizations
        (fun _ => qPolynomial f n T K groups alpha z lambda ell hgroups data helpers) := by
  funext q
  rcases q with ⟨⟨⟩, x⟩
  change Fin n → E at x
  change simulateQ (Access.extendImpl A (helperInterface (E := E) n K) impl helpers)
      (queryQ f n T K groups alpha z lambda A inputView x) =
    MvPolynomial.eval x (qPolynomial f n T K groups alpha z lambda ell hgroups data helpers).val
  rw [queryQ_eval f n T K groups alpha z lambda A inputView impl data hinput helpers]
  simpa only [qPolynomial, Logup.boundedBatchedPolynomial,
    ← eval₂Mle_eq_tablePolynomial, eval₂Mle_id] using
    (Logup.eval_batchedPolynomial groups alpha z lambda
      (fun i => (tablePolynomial f n (data (0,i))).val)
      (fun i => (tablePolynomial f n (data (1,i))).val)
      (fun k => (tablePolynomial (RingHom.id E) n helpers[k.val]).val) x).symm

end Logup.Interaction

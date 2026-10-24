/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
module

public import ArkLib.ProofSystem.Logup.Lookup.Language
public import ArkLib.ProofSystem.Logup.Interaction.Source

/-!
# Scalar lookup source from retained base-field multiplicities

The original source exposes only query values and every declared physical table piece. A later
retained message supplies one base-field multiplicity table per piece. The weighted view opens the
original value through its prior source, returns query weight1 directly, and opens then negates the
actual retained multiplicity for a table weight. It constructs no value or weight table while
answering a verifier query.

The realization theorem holds for every retained multiplicity assignment and every genuinely
realizing original value view. A later helper slot cannot replace either source: the existing Q
program weakens this entire view through its prior-source route before opening its newest helper.
No lookup truth, witness indices, field characteristic or multiplicity correctness is assumed.
-/

@[expose] public section

open CompPoly
namespace Logup.Lookup
variable {B E : Type} [CommRing B] [CommRing E] (f : B →+* E) (n M P : ℕ)

private theorem eval₂Mle_one (x : Fin n → E) :
    CMlPolynomialEval.eval₂Mle (Vector.replicate (2 ^ n) (1 : B)) f (Vector.ofFn x) = 1 := by
  rw [CMlPolynomialEval.eval₂Mle_eq_MvPolynomial_MLE]
  simp only [Vector.get_eq_getElem, Vector.getElem_replicate, map_one]
  have h : (1 : MvPolynomial (Fin n) E) = MvPolynomial.MLE (fun _ => (1 : E)) := by
    apply MvPolynomial.eq_MLE_of_degreeOf_le_one_of_eval_zeroOne_eq
    · intro i; simp
    · intro u; simp
  rw [← h, map_one]

private theorem eval₂Mle_neg (table : CMlPolynomialEval B n) (x : Fin n → E) :
    CMlPolynomialEval.eval₂Mle (Vector.map Neg.neg table) f (Vector.ofFn x) =
      -CMlPolynomialEval.eval₂Mle table f (Vector.ofFn x) := by
  rw [CMlPolynomialEval.eval₂Mle_eq_MvPolynomial_MLE,
    CMlPolynomialEval.eval₂Mle_eq_MvPolynomial_MLE]
  simp only [Vector.get_eq_getElem, Vector.getElem_map, map_neg]
  simp [MvPolynomial.MLE, Finset.sum_neg_distrib]

open _root_.Interaction.Oracle OracleComp OracleSpec

/-- Original value columns, with query and table-piece roles kept explicit in their indices. -/
def valuesFamily : OracleFamily (Fin M ⊕ Fin P) (fun _ => CMlPolynomialEval B n) :=
  ⟨fun _ => Logup.Interaction.baseTableInterface f n⟩

/-- Evaluate one actually retained base-field multiplicity table at a challenge-field point. -/
@[reducible]
def multiplicityInterface : OracleInterface (Vector (CMlPolynomialEval B n) P) where
  Query := Fin P × (Fin n → E)
  toOC.spec := (Fin P × (Fin n → E)) →ₒ E
  toOC.impl q := do
    let tables ← read
    return CMlPolynomialEval.eval₂Mle tables[q.1.val] f (Vector.ofFn q.2)

/-- Open original values, return query weight1, or negate the retained table multiplicity. -/
def queryWeighted (A : PFunctor.{0, 0})
    (valuesView : VirtualOracle (ofPFunctor A) (valuesFamily f n M P))
    (kind : Fin 2) (i : Fin (M + P)) (x : Fin n → E) :
    OracleComp (ofPFunctor (Access.extend A (multiplicityInterface f n P))) E :=
  if kind = 0 then
    (valuesView.substSource (Access.queryPrior A (multiplicityInterface f n P))).query
      ⟨finSumFinEquiv.symm i, x⟩
  else match finSumFinEquiv.symm i with
  | .inl _ => pure 1
  | .inr p => do
    let answer : E ← Access.queryLatest A (multiplicityInterface f n P) (p, x)
    return -answer

/-- Export the scalar weighted family over the original source plus its multiplicity slot. -/
def weightedView (A : PFunctor.{0, 0})
    (valuesView : VirtualOracle (ofPFunctor A) (valuesFamily f n M P)) :
    VirtualOracle (ofPFunctor (Access.extend A (multiplicityInterface f n P)))
      (Logup.Interaction.inputFamily f n (M + P)) :=
  ⟨fun q => queryWeighted f n M P A valuesView q.1.1 q.1.2 q.2⟩

set_option backward.isDefEq.respectTransparency false in
/-- The actual closed source realizes the signed weighted tables for every multiplicity message. -/
theorem weightedView_realizes (A : PFunctor.{0, 0})
    (valuesView : VirtualOracle (ofPFunctor A) (valuesFamily f n M P))
    (impl : QueryImpl (ofPFunctor A) Id) (data : Data B n M P)
    (hinput : valuesView.eval impl = (valuesFamily f n M P).behaviorOfRealizations data)
    (mu : Vector (CMlPolynomialEval B n) P) :
    (weightedView f n M P A valuesView).eval
      (Access.extendImpl A (multiplicityInterface f n P) impl mu) =
      (Logup.Interaction.inputFamily f n (M + P)).behaviorOfRealizations
        (weightedData data mu) := by
  have hext : QueryImpl.compose
      (Access.extendImpl A (multiplicityInterface f n P) impl mu)
      (Access.queryPrior A (multiplicityInterface f n P)) = impl := by
    funext q
    exact Access.eval_queryPrior A (multiplicityInterface f n P) impl mu q
  have hprior : (valuesView.substSource (Access.queryPrior A (multiplicityInterface f n P))).eval
      (Access.extendImpl A (multiplicityInterface f n P) impl mu) =
      (valuesFamily f n M P).behaviorOfRealizations data := by
    rw [VirtualOracle.eval_substSource, hext]
    exact hinput
  funext q
  rcases q with ⟨⟨kind, i⟩, x⟩
  change (Fin n → E) at x
  change simulateQ (Access.extendImpl A (multiplicityInterface f n P) impl mu)
      (queryWeighted f n M P A valuesView kind i x) =
    CMlPolynomialEval.eval₂Mle (weightedData data mu (kind, i)) f (Vector.ofFn x)
  by_cases hk : kind = 0
  · subst kind
    simp only [queryWeighted, ↓reduceIte, weightedData_value]
    exact congrFun hprior ⟨finSumFinEquiv.symm i, x⟩
  · have hk1 : kind = 1 := Fin.eq_one_of_ne_zero kind hk
    subst kind
    simp only [queryWeighted, hk, ↓reduceIte]
    generalize heq : finSumFinEquiv.symm i = piece
    cases piece with
    | inl query =>
      have hi : i = Fin.castAdd P query := by
        apply finSumFinEquiv.symm.injective
        simpa only [finSumFinEquiv_symm_apply_castAdd] using heq
      subst i
      simp only [weightedData_query_weight, simulateQ_pure]
      exact (eval₂Mle_one f n x).symm
    | inr piece =>
      have hi : i = Fin.natAdd M piece := by
        apply finSumFinEquiv.symm.injective
        simpa only [finSumFinEquiv_symm_apply_natAdd] using heq
      subst i
      simp only [weightedData_table_weight, simulateQ_bind, simulateQ_pure]
      rw [Access.eval_queryLatest]
      exact (eval₂Mle_neg f n mu[piece.val] x).symm
end Logup.Lookup

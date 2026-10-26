/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/
module

public import ArkLib.ProofSystem.Logup.Prover.Helpers
public import ArkLib.ProofSystem.Logup.Interaction.Source
public import ArkLib.ToCompPoly.Multilinear.Fold

/-!
# Executable honest LogUp table state

Before the joint challenge, prepare the cached denominator, weight, and termwise helper tables.
Then cache equality weights and batching coefficients. Each native challenge folds the four
Boolean table families using the existing head-fold algorithm, retaining batching coefficients.
The state stores neither alpha nor a separate mapped-value table.

The individually noncomputable polynomial view reuses the existing denominator circuit: writing
D as zero minus negative D supplies stored denominators without a new runtime kernel. Its initial
value is the actual source Q polynomial, and each table fold is formal head-variable substitution.
These are state invariants, not a full honest-strategy, completeness or resource theorem.
-/

@[expose] public section

open CompPoly
open Logup.Interaction

namespace Logup.Prover

/-- Cached tables computed before the joint batching challenge. -/
structure Prepared (E : Type) (T K n : Nat) where
  /-- Alpha minus each mapped original value, cached once. -/
  denominator : Vector (CMlPolynomialEval E n) T
  /-- Original weights mapped into the challenge field. -/
  weight : Vector (CMlPolynomialEval E n) T
  /-- Actual helper message tables, with termwise total inversion at Boolean rows. -/
  helper : Vector (CMlPolynomialEval E n) K

/-- Remaining Boolean tables and public batching data retained by the honest prover. -/
structure State (E : Type) (T K n : Nat) extends Prepared E T K n where
  /-- Cached equality weights, folded with all other tables. -/
  kernel : CMlPolynomialEval E n
  /-- Batching coefficients retained unchanged across native rounds. -/
  lambda : Vector E K

namespace State

/-- Initialize denominators and weights once, then compute the actual helper message. -/
def prepare {B E : Type} [CommRing B] [Field E] {n T ell : Nat}
    (f : B →+* E) (alpha : E) (cfg : Config n T ell)
    (data : Fin 2 × Fin T → CMlPolynomialEval B n) : Prepared E T (T ⌈/⌉ ell) n :=
  let denominator := denominatorTables f alpha data
  let weight := weightTables f data
  ⟨denominator, weight, helpers cfg.groups denominator weight⟩

/-- Add the equality-weight cache and batching vector after the actual joint challenge. -/
def start {E : Type} [CommRing E] {T K n : Nat} (prepared : Prepared E T K n)
    (z : Fin n → E) (lambda : Fin K → E) : State E T K n :=
  ⟨prepared, CMlPolynomialEval.lagrangeBasis (Vector.ofFn z), Vector.ofFn lambda⟩

/-- Fold every private Boolean table at the next public native challenge. -/
def fold {E : Type} [CommRing E] {T K n : Nat}
    (state : State E T K (n + 1)) (r : E) : State E T K n :=
  ⟨⟨Vector.map (fun t => CMlPolynomialEval.evalMleLayer t r) state.denominator,
      Vector.map (fun t => CMlPolynomialEval.evalMleLayer t r) state.weight,
      Vector.map (fun t => CMlPolynomialEval.evalMleLayer t r) state.helper⟩,
    CMlPolynomialEval.evalMleLayer state.kernel r, state.lambda⟩

open MvPolynomial

/-- Canonical mathematical multilinear interpretation of one retained Boolean table. -/
noncomputable def tableView {E : Type} [CommRing E] {n : Nat}
    (table : CMlPolynomialEval E n) : MvPolynomial (Fin n) E :=
  MLE (fun u => table.get (finFunctionFinEquiv u))

/-- Formal Q of the current stored denominators, weights, helpers, and equality cache. -/
noncomputable def polynomial {E : Type} [CommRing E] {T K n : Nat}
    (groups : Vector (List (Fin T)) K) (state : State E T K n) : MvPolynomial (Fin n) E :=
  Logup.reconstructWithKernel groups 0 (tableView state.kernel)
    (fun k => C state.lambda[k.val])
    (fun i => -tableView state.denominator[i.val])
    (fun i => tableView state.weight[i.val])
    (fun k => tableView state.helper[k.val])

private noncomputable def specializeHead {E : Type} [CommRing E] {n : Nat} (r : E) :
    MvPolynomial (Fin (n + 1)) E →+* MvPolynomial (Fin n) E :=
  (Polynomial.evalRingHom (C r)).comp (MvPolynomial.finSuccEquiv E n).toRingHom

private theorem specializeHead_C {E : Type} [CommRing E] {n : Nat} (r a : E) :
    specializeHead (n := n) r (C a) = C a := by
  simp [specializeHead, MvPolynomial.finSuccEquiv_apply]

private theorem tableView_fold {E : Type} [CommRing E] {n : Nat}
    (table : CMlPolynomialEval E (n + 1)) (r : E) :
    tableView (CMlPolynomialEval.evalMleLayer table r) = specializeHead r (tableView table) :=
  CMlPolynomialEval.MLE_evalMleLayer table r

/-- The actual state fold is formal partial evaluation of the same Q polynomial. -/
theorem polynomial_fold {E : Type} [CommRing E] {T K n : Nat}
    (groups : Vector (List (Fin T)) K) (state : State E T K (n + 1)) (r : E) :
    polynomial groups (fold state r) =
      Polynomial.eval (C r) (MvPolynomial.finSuccEquiv E n (polynomial groups state)) := by
  have h := Logup.map_reconstructWithKernel (specializeHead (n := n) r) groups 0
    (tableView state.kernel) (fun k => C state.lambda[k.val])
    (fun i => -tableView state.denominator[i.val])
    (fun i => tableView state.weight[i.val]) (fun k => tableView state.helper[k.val])
  have hs : polynomial groups (fold state r) = specializeHead r (polynomial groups state) := by
    simpa [polynomial, fold, map_neg, specializeHead_C, ← tableView_fold] using h.symm
  simpa [specializeHead] using hs

/-- Initial private Q agrees with the actual retained source Q, including at poles. -/
theorem polynomial_start_prepare {B E : Type} [CommRing B] [Field E]
    {n T ell : Nat} (f : B →+* E) (alpha : E) (cfg : Config n T ell)
    (data : Fin 2 × Fin T → CMlPolynomialEval B n) (z : Fin n → E)
    (lambda : Fin (T ⌈/⌉ ell) → E) :
    polynomial cfg.groups (start (prepare f alpha cfg data) z lambda) =
      (qPolynomial f n T (T ⌈/⌉ ell) cfg.groups alpha z lambda ell cfg.length_group_le data
        (prepare f alpha cfg data).helper).val := by
  have hD (i : Fin T) : tableView (denominatorTables f alpha data)[i.val] =
      C alpha - (tablePolynomial f n (data (0, i))).val :=
    MLE_denominatorTables f alpha data i
  have hW (i : Fin T) : tableView (weightTables f data)[i.val] =
      (tablePolynomial f n (data (1, i))).val := by
    simp [tableView, tablePolynomial]
  have hH (k : Fin (T ⌈/⌉ ell)) :
      tableView (helpers cfg.groups (denominatorTables f alpha data) (weightTables f data))[k.val]
        = (tablePolynomial (RingHom.id E) n
          (helpers cfg.groups (denominatorTables f alpha data)
            (weightTables f data))[k.val]).val := rfl
  have hK : tableView (CMlPolynomialEval.lagrangeBasis (Vector.ofFn z)) = eqPolynomial z := by
    have hz : (Vector.ofFn z).get = z := by
      funext i
      simp
    simpa only [tableView, CMlPolynomialEval.lagrangeBasisFast_eq, hz] using
      CMlPolynomialEval.MLE_lagrangeBasisFast (Vector.ofFn z)
  change polynomial cfg.groups (start (prepare f alpha cfg data) z lambda) =
    Logup.batchedPolynomial cfg.groups alpha z lambda
      (fun i => (tablePolynomial f n (data (0, i))).val)
      (fun i => (tablePolynomial f n (data (1, i))).val)
      (fun k => (tablePolynomial (RingHom.id E) n (prepare f alpha cfg data).helper[k.val]).val)
  dsimp only [polynomial, start, prepare]
  simp only [Vector.getElem_ofFn, hD, hW, hH, hK]
  simp only [Logup.reconstructWithKernel, Logup.batchedPolynomial, Logup.residualPolynomial,
    Logup.groupResidual, Logup.groupFraction, zero_sub, neg_neg]

end State
end Logup.Prover

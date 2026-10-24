/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
module

public import ArkLib.ProofSystem.Logup.Prover.CoefficientCircuit
public import ArkLib.ToCompPoly.Multilinear.Affine
public import ArkLib.ProofSystem.Sumcheck.Impl.Representation
public import ArkLib.ProofSystem.Sumcheck.Domain

-- The packing proof inspects the dense array stored by `ofArray` and its degree definition.
import all CompPoly.Univariate.Basic

/-!
# Direct Boolean round-message coefficients

Adjacent table entries give affine coefficient rows for the next variable. The constructor
runs the grouped constraint circuit on each Boolean suffix and adds its coefficients directly
into one padded accumulator. It normalizes only the final sum. Runtime never constructs or
evaluates a mathematical multivariate polynomial.

The input circuit is the denominator-cleared grouped constraint from [Hab22]. Formal agreement
uses coefficient ring homomorphisms and finite reindexing, including in small characteristics.
The mathematical substitution map below uses Mathlib's sparse polynomial support operations,
which require classical coefficient choices; it appears only in proofs. A supplied bounded
polynomial connects the resulting message to the existing honest Sumcheck projection.

These are pure correctness constructors. Measured execution, normalization profiles, and transfer
to the eventual default honest runtime belong to the separate arithmetic companion.

## References

* [Haböck, U., *Multivariate lookups based on logarithmic derivatives*][Hab22]
  (source-version metadata: `docs/kb/papers/Hab22.md`).
-/

@[expose] public section

open CompPoly CPolynomial CMlPolynomialEval MvPolynomial
namespace Logup.Prover.RoundCoefficients
variable {R : Type*} [CommRing R] {r T K : ℕ}

/-- Bind every denominator, weight, helper, and kernel affine row once, then run the circuit. -/
def row (groups : Vector (List (Fin T)) K) (lambda : Vector R K)
    (denominator weight : Vector (CMlPolynomialEval R (r + 1)) T)
    (helper : Vector (CMlPolynomialEval R (r + 1)) K)
    (kernel : CMlPolynomialEval R (r + 1)) (j : Fin (2 ^ r)) : Raw R :=
  let d := Vector.ofFn fun i => affineRow (denominator.get i) j
  let w := Vector.ofFn fun i => affineRow (weight.get i) j
  let h := Vector.ofFn fun k => affineRow (helper.get k) j
  CoefficientCircuit.circuitRaw groups (affineRow kernel j) lambda d w h

/-- Stream suffix rows into one padded coefficient accumulator. -/
def coefficientsFrom (rows : List (Fin (2 ^ r))) (groups : Vector (List (Fin T)) K)
    (lambda : Vector R K) (denominator weight : Vector (CMlPolynomialEval R (r + 1)) T)
    (helper : Vector (CMlPolynomialEval R (r + 1)) K)
    (kernel : CMlPolynomialEval R (r + 1)) (acc : Raw R) : Raw R :=
  rows.foldl (fun a j => Raw.addRaw a (row groups lambda denominator weight helper kernel j)) acc

/-- Sum the next-round coefficients over all Boolean suffixes without expanding the full circuit. -/
def coefficients (groups : Vector (List (Fin T)) K) (lambda : Vector R K)
    (denominator weight : Vector (CMlPolynomialEval R (r + 1)) T)
    (helper : Vector (CMlPolynomialEval R (r + 1)) K)
    (kernel : CMlPolynomialEval R (r + 1)) : Raw R :=
  coefficientsFrom (List.finRange (2 ^ r)) groups lambda denominator weight helper kernel #[]

/-- Formal restriction to one Boolean suffix; sparse coefficient support is proof-only. -/
private noncomputable def rowMap (j : Fin (2 ^ r)) :
    MvPolynomial (Fin (r + 1)) R →+* Polynomial R :=
  (Polynomial.mapRingHom (MvPolynomial.eval
    (fun i => (finFunctionFinEquiv.symm j i : R)))).comp
    (MvPolynomial.finSuccEquiv R r).toRingHom

private theorem rowMap_C (j : Fin (2 ^ r)) (a : R) : rowMap j (C a) = Polynomial.C a := by
  simp [rowMap, MvPolynomial.finSuccEquiv_apply]

private theorem rowMap_MLE (j : Fin (2 ^ r)) (table : CMlPolynomialEval R (r + 1)) :
    rowMap j (MLE (fun u => table.get (finFunctionFinEquiv u))) =
      Raw.toPoly (affineRow table j) := (affineRow_toPoly table j).symm

/-- The row coefficients equal formal restriction of the multilinear input circuit.
This is a coefficient-map identity, not equality inferred from finite-field evaluations. -/
theorem toPoly_row (groups : Vector (List (Fin T)) K) (lambda : Vector R K)
    (denominator weight : Vector (CMlPolynomialEval R (r + 1)) T)
    (helper : Vector (CMlPolynomialEval R (r + 1)) K)
    (kernel : CMlPolynomialEval R (r + 1)) (j : Fin (2 ^ r)) :
    Raw.toPoly (row groups lambda denominator weight helper kernel j) =
      Polynomial.map (MvPolynomial.eval (fun i => (finFunctionFinEquiv.symm j i : R)))
        (MvPolynomial.finSuccEquiv R r (reconstructWithKernel groups 0
          (MLE (fun u => kernel.get (finFunctionFinEquiv u)))
          (fun k => C (lambda.get k))
          (fun i => -MLE (fun u => (denominator.get i).get (finFunctionFinEquiv u)))
          (fun i => MLE (fun u => (weight.get i).get (finFunctionFinEquiv u)))
          (fun k => MLE (fun u => (helper.get k).get (finFunctionFinEquiv u))))) := by
  change _ = rowMap j _
  rw [map_reconstructWithKernel]
  simp only [map_zero, map_neg, rowMap_C, rowMap_MLE]
  unfold row
  rw [CoefficientCircuit.toPoly_circuitRaw_denominator]
  simp only [Vector.get_ofFn]

/-- A row circuit stores at most one coefficient beyond its round degree bound. -/
theorem size_row_le (groups : Vector (List (Fin T)) K) (lambda : Vector R K)
    (denominator weight : Vector (CMlPolynomialEval R (r + 1)) T)
    (helper : Vector (CMlPolynomialEval R (r + 1)) K)
    (kernel : CMlPolynomialEval R (r + 1)) (j : Fin (2 ^ r)) (ell : ℕ)
    (hgroups : ∀ k, (groups.get k).length ≤ ell) :
    (row groups lambda denominator weight helper kernel j).size ≤ ell + 3 := by
  unfold row
  apply CoefficientCircuit.size_circuitRaw_le (ell := ell) _ _ _ _ _ _ hgroups <;> simp

/-- Every prefix of the streamed row accumulation preserves the common padded width. -/
theorem size_coefficientsFrom_le (rows : List (Fin (2 ^ r)))
    (groups : Vector (List (Fin T)) K) (lambda : Vector R K)
    (denominator weight : Vector (CMlPolynomialEval R (r + 1)) T)
    (helper : Vector (CMlPolynomialEval R (r + 1)) K)
    (kernel : CMlPolynomialEval R (r + 1)) (acc : Raw R) (ell : ℕ)
    (hgroups : ∀ k, (groups.get k).length ≤ ell) (hacc : acc.size ≤ ell + 3) :
    (coefficientsFrom rows groups lambda denominator weight helper kernel acc).size ≤ ell + 3 := by
  induction rows generalizing acc with
  | nil => exact hacc
  | cons j rows ih =>
    apply ih
    rw [Raw.size_addRaw]
    exact max_le hacc (size_row_le _ _ _ _ _ _ j ell hgroups)

/-- The complete padded round sum stores at most `ell + 3` coefficients. -/
theorem size_coefficients_le (groups : Vector (List (Fin T)) K) (lambda : Vector R K)
    (denominator weight : Vector (CMlPolynomialEval R (r + 1)) T)
    (helper : Vector (CMlPolynomialEval R (r + 1)) K)
    (kernel : CMlPolynomialEval R (r + 1)) (ell : ℕ)
    (hgroups : ∀ k, (groups.get k).length ≤ ell) :
    (coefficients groups lambda denominator weight helper kernel).size ≤ ell + 3 :=
  size_coefficientsFrom_le _ _ _ _ _ _ _ #[] ell hgroups (by simp)

/-- Interpreting the streamed sum gives the sum of the formal row polynomials. -/
theorem toPoly_coefficients (groups : Vector (List (Fin T)) K) (lambda : Vector R K)
    (denominator weight : Vector (CMlPolynomialEval R (r + 1)) T)
    (helper : Vector (CMlPolynomialEval R (r + 1)) K)
    (kernel : CMlPolynomialEval R (r + 1)) :
    Raw.toPoly (coefficients groups lambda denominator weight helper kernel) =
      ∑ j : Fin (2 ^ r), Raw.toPoly (row groups lambda denominator weight helper kernel j) := by
  have hsum : coefficients groups lambda denominator weight helper kernel =
      Raw.sumRaw ((List.finRange (2 ^ r)).map fun j =>
        row groups lambda denominator weight helper kernel j) := by
    simp only [coefficients, coefficientsFrom, Raw.sumRaw, List.foldl_map]
  rw [hsum, Raw.toPoly_sumRaw, List.map_map]
  simp only [Function.comp_def]
  rw [← Fin.sum_univ_def]

/-- The complete coefficient sum is the formal Boolean-suffix projection of the input circuit. -/
theorem toPoly_coefficients_eq_projection (groups : Vector (List (Fin T)) K)
    (lambda : Vector R K) (denominator weight : Vector (CMlPolynomialEval R (r + 1)) T)
    (helper : Vector (CMlPolynomialEval R (r + 1)) K)
    (kernel : CMlPolynomialEval R (r + 1)) :
    let polynomial := reconstructWithKernel groups 0
      (MLE (fun u => kernel.get (finFunctionFinEquiv u))) (fun k => C (lambda.get k))
      (fun i => -MLE (fun u => (denominator.get i).get (finFunctionFinEquiv u)))
      (fun i => MLE (fun u => (weight.get i).get (finFunctionFinEquiv u)))
      (fun k => MLE (fun u => (helper.get k).get (finFunctionFinEquiv u)))
    Raw.toPoly (coefficients groups lambda denominator weight helper kernel) =
      ∑ j : Fin (2 ^ r),
        Polynomial.map (MvPolynomial.eval (fun i => (finFunctionFinEquiv.symm j i : R)))
          (MvPolynomial.finSuccEquiv R r polynomial) := by
  dsimp only
  rw [toPoly_coefficients]
  apply Finset.sum_congr rfl
  intro j _
  exact toPoly_row _ _ _ _ _ _ j

/-- Construct the bounded canonical round message, trimming only the final coefficient sum. -/
def message {E : Type} [CommRing E] [DecidableEq E] {r T K ell : ℕ}
    (groups : Vector (List (Fin T)) K) (hgroups : ∀ k, (groups.get k).length ≤ ell)
    (lambda : Vector E K) (denominator weight : Vector (CMlPolynomialEval E (r + 1)) T)
    (helper : Vector (CMlPolynomialEval E (r + 1)) K)
    (kernel : CMlPolynomialEval E (r + 1)) : Sumcheck.Impl.Representation.Message E (ell + 2) :=
  let raw := coefficients groups lambda denominator weight helper kernel
  let p := CPolynomial.ofArray raw
  ⟨p, by
    have htrim := CPolynomial.Raw.Trim.size_le_size raw
    change p.val.size ≤ raw.size at htrim
    have hbound := htrim.trans (size_coefficients_le _ _ _ _ _ _ ell hgroups)
    generalize h : p.val.size = size at *
    cases size with
    | zero => simp [CPolynomial.degree, h]
    | succ size =>
      simp only [CPolynomial.degree, h]
      exact_mod_cast (show size ≤ ell + 2 by omega)⟩

/-- Final normalization preserves the formal coefficient sum. -/
theorem message_toPoly {E : Type} [CommRing E] [DecidableEq E] {r T K ell : ℕ}
    (groups : Vector (List (Fin T)) K) (hgroups : ∀ k, (groups.get k).length ≤ ell)
    (lambda : Vector E K) (denominator weight : Vector (CMlPolynomialEval E (r + 1)) T)
    (helper : Vector (CMlPolynomialEval E (r + 1)) K)
    (kernel : CMlPolynomialEval E (r + 1)) :
    (message groups hgroups lambda denominator weight helper kernel).val.toPoly =
      Raw.toPoly (coefficients groups lambda denominator weight helper kernel) :=
  CPolynomial.ofArray_toPoly _

private theorem finSuccEquivNth_zero (p : MvPolynomial (Fin (r + 1)) R) :
    MvPolynomial.finSuccEquivNth R (0 : Fin (r + 1)) p =
      MvPolynomial.finSuccEquiv R r p := by
  have h : (MvPolynomial.finSuccEquivNth R (0 : Fin (r + 1))).toAlgHom =
      (MvPolynomial.finSuccEquiv R r).toAlgHom := by
    apply MvPolynomial.algHom_ext
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [MvPolynomial.finSuccEquiv_X_zero]
    · simp only [AlgEquiv.toAlgHom_apply]
      rw [MvPolynomial.finSuccEquivNth_X_above (by simp), MvPolynomial.finSuccEquiv_X_succ]
  exact congrArg (fun f => f p) h

private theorem sum_restrictions_eq_boolCube [Nontrivial R]
    (p : MvPolynomial (Fin (r + 1)) R) :
    (∑ j : Fin (2 ^ r),
      Polynomial.map (MvPolynomial.eval (fun i => (finFunctionFinEquiv.symm j i : R)))
        (MvPolynomial.finSuccEquiv R r p)) =
    ∑ x ∈ (boolDomain R r).cube,
      Polynomial.map (MvPolynomial.eval x) (MvPolynomial.finSuccEquiv R r p) := by
  classical
  rw [sum_cube_boolDomain]
  exact Equiv.sum_comp (finFunctionFinEquiv : (Fin r → Fin 2) ≃ Fin (2 ^ r)).symm
    (fun u => Polynomial.map (MvPolynomial.eval (fun i => (u i : R)))
      (MvPolynomial.finSuccEquiv R r p))

/-- The packed message is exactly the existing honest head-round projection of any supplied
bounded polynomial realizing the denominator-table circuit. -/
theorem message_toMessage {E : Type} [CommRing E] [DecidableEq E] [Nontrivial E]
    {r T K ell : ℕ} (groups : Vector (List (Fin T)) K)
    (hgroups : ∀ k, (groups.get k).length ≤ ell) (lambda : Vector E K)
    (denominator weight : Vector (CMlPolynomialEval E (r + 1)) T)
    (helper : Vector (CMlPolynomialEval E (r + 1)) K)
    (kernel : CMlPolynomialEval E (r + 1)) (poly : E⦃≤ ell + 2⦄[X Fin (r + 1)])
    (hpoly : poly.val = reconstructWithKernel groups 0
      (MLE (fun u => kernel.get (finFunctionFinEquiv u))) (fun k => C (lambda.get k))
      (fun i => -MLE (fun u => (denominator.get i).get (finFunctionFinEquiv u)))
      (fun i => MLE (fun u => (weight.get i).get (finFunctionFinEquiv u)))
      (fun k => MLE (fun u => (helper.get k).get (finFunctionFinEquiv u)))) :
    Sumcheck.Impl.Representation.toMessage E (ell + 2)
      (message groups hgroups lambda denominator weight helper kernel) =
      Sumcheck.Spec.SingleRound.projectedRoundPolynomial E (r + 1) (ell + 2)
        (boolEmbedding E) 0 Fin.elim0 poly := by
  classical
  apply Subtype.ext
  change (message groups hgroups lambda denominator weight helper kernel).val.toPoly =
    ∑ x ∈ (Finset.univ.map (boolEmbedding E)) ^ᶠ r,
      Polynomial.map
        (MvPolynomial.eval (Sumcheck.Spec.SingleRound.roundSuffix E r 0 Fin.elim0 x))
        (MvPolynomial.finSuccEquivNth E 0 poly.val)
  rw [message_toPoly, toPoly_coefficients_eq_projection, ← hpoly,
    sum_restrictions_eq_boolCube, finSuccEquivNth_zero]
  apply Finset.sum_congr rfl
  intro x _
  have hs : Sumcheck.Spec.SingleRound.roundSuffix E r 0 Fin.elim0 x = x := by
    change (fun i : Fin r => Fin.append (Fin.elim0 : Fin 0 → E) x
      (Fin.cast (Nat.zero_add r).symm i)) = x
    rw [Fin.elim0_append]
    funext i
    apply congrArg x
    exact Fin.ext rfl
  rw [hs]

end Logup.Prover.RoundCoefficients

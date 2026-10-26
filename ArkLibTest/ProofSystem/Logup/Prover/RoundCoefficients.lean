/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/
import ArkLib.ProofSystem.Logup.Prover.RoundCoefficients
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.FinCases
import Lean.Compiler.IR

/-! # Direct Boolean coefficient traversal and canonical round messages -/

open Logup CompPoly CPolynomial CMlPolynomialEval MvPolynomial
open Logup.Prover.RoundCoefficients
namespace RoundCoefficientsTests

abbrev F := ZMod 17
def groups : Vector (List (Fin 2)) 2 := #v[[0], [1]]
def denominator : Vector (CMlPolynomialEval F 1) 2 := #v[#v[2, 1], #v[2, 1]]
def weight : Vector (CMlPolynomialEval F 1) 2 := #v[#v[1, 1], #v[-1, -1]]
def helper : Vector (CMlPolynomialEval F 1) 2 := #v[#v[9, 1], #v[8, 16]]
def cubic : Sumcheck.Impl.Representation.Message F 3 :=
  message (r := 0) groups (by intro k; fin_cases k <;> decide) #v[4, 6]
    denominator weight helper #v[-2, 3]

def singleton : Vector (List (Fin 1)) 1 := #v[[0]]
def xTable : CMlPolynomialEval (ZMod 2) 1 := #v[0, 1]
def kTable : CMlPolynomialEval (ZMod 2) 1 := #v[1, 0]
def binary : Sumcheck.Impl.Representation.Message (ZMod 2) 3 :=
  message (r := 0) singleton (by intro k; fin_cases k; decide) #v[1]
    #v[xTable] #v[xTable] #v[xTable] kTable

-- The actual packed formal polynomial is X^3, even though its values agree with X in F2.
theorem binary_toPoly : binary.val.toPoly = Polynomial.X ^ 3 := by
  unfold binary
  rw [message_toPoly, toPoly_coefficients (r := 0)]
  have hsum :
      (∑ j : Fin 1, Raw.toPoly (row (r := 0) singleton #v[1]
        #v[xTable] #v[xTable] #v[xTable] kTable j)) =
      Raw.toPoly (row (r := 0) singleton #v[1]
        #v[xTable] #v[xTable] #v[xTable] kTable 0) := Fin.sum_univ_one _
  trans Raw.toPoly (row (r := 0) singleton #v[1]
    #v[xTable] #v[xTable] #v[xTable] kTable 0)
  · exact hsum
  unfold row
  rw [Logup.Prover.CoefficientCircuit.toPoly_circuitRaw_denominator]
  have hx : affineRow xTable (0 : Fin 1) = Raw.affine (0 : ZMod 2) 1 := rfl
  have hk : affineRow kTable (0 : Fin 1) = Raw.affine (1 : ZMod 2) 0 := rfl
  have htwo : (0 : ZMod 2) - 1 = 1 := by decide
  simp [Vector.get_ofFn, hx, hk, singleton, reconstructWithKernel, groupResidual,
    groupFraction, FractionPair.sum_cons, FractionPair.sum_nil, FractionPair.combine,
    FractionPair.unit, Raw.toPoly_affine, htwo]
  ring

theorem binary_ne_X : binary.val.toPoly ≠ Polynomial.X := by
  intro h
  have hc := congrArg (fun p : Polynomial (ZMod 2) => p.coeff 3) h
  rw [binary_toPoly] at hc
  norm_num [Polynomial.coeff_X] at hc

theorem binary_evaluations (x : ZMod 2) :
    Sumcheck.Impl.Representation.evaluate (ZMod 2) 3 binary x = x := by
  rw [Sumcheck.Impl.Representation.evaluate_eq]
  change binary.val.toPoly.eval x = x
  rw [binary_toPoly]
  simp only [Polynomial.eval_pow, Polynomial.eval_X]
  fin_cases x
  · change (0 : ZMod 2) ^ 3 = 0
    decide
  · change (1 : ZMod 2) ^ 3 = 1
    decide

def asymmetricDenominator : Vector (CMlPolynomialEval ℤ 2) 1 := #v[#v[2, 3, 5, 11]]
def asymmetricWeight : Vector (CMlPolynomialEval ℤ 2) 1 := #v[#v[13, 17, 19, 23]]
def asymmetricHelper : Vector (CMlPolynomialEval ℤ 2) 1 := #v[#v[29, 31, 37, 41]]
def asymmetricKernel : CMlPolynomialEval ℤ 2 := #v[43, 47, 53, 59]
def asymmetric : Sumcheck.Impl.Representation.Message ℤ 3 :=
  message (r := 1) singleton (by intro k; fin_cases k; decide) #v[7]
    asymmetricDenominator asymmetricWeight asymmetricHelper asymmetricKernel

def afterChallenge : Sumcheck.Impl.Representation.Message ℤ 3 :=
  message (r := 0) singleton (by intro k; fin_cases k; decide) #v[7]
    (asymmetricDenominator.map fun p => evalMleLayer p (-2))
    (asymmetricWeight.map fun p => evalMleLayer p (-2))
    (asymmetricHelper.map fun p => evalMleLayer p (-2))
    (evalMleLayer asymmetricKernel (-2))

def caller {E : Type} [CommRing E] [DecidableEq E] {r T K ell : ℕ}
    (g : Vector (List (Fin T)) K) (hg : ∀ k, (g.get k).length ≤ ell)
    (lambda : Vector E K) (d w : Vector (CMlPolynomialEval E (r + 1)) T)
    (h : Vector (CMlPolynomialEval E (r + 1)) K) (b : CMlPolynomialEval E (r + 1)) :
    Sumcheck.Impl.Representation.Message E (ell + 2) :=
  message (r := r) g hg lambda d w h b

open Lean Elab Command in
run_cmd do
  unless cubic.val.val == #[0, 2, 10, 5] && cubic.val.evalHorner 5 == 1 do
    throwError "honest split-group cubic table message changed"
  unless cubic.val.evalHorner 0 + cubic.val.evalHorner 1 == 0 do
    throwError "honest split-group cubic no longer has Boolean sum zero"
  unless binary.val.val == #[0, 0, 0, 1] do
    throwError "formal characteristic-two cubic was collapsed to its field-point function"
  unless asymmetric.val.val == #[75197, 105265, 20314, 1064] do
    throwError "head-first little-endian Boolean suffix traversal changed"
  unless afterChallenge.val.val == #[-1200, -44551, -14462, -1176] do
    throwError "folded-table second message changed"
  unless asymmetric.val.evalHorner (-2) ==
      afterChallenge.val.evalHorner 0 + afterChallenge.val.evalHorner 1 do
    throwError "concrete folded continuation broke the sumcheck recurrence"
  let pole := message (E := F) (r := 0) groups (ell := 1)
    (by intro k; fin_cases k <;> decide) #v[4, 6]
    #v[#v[0, -1], #v[0, -1]] weight #v[#v[0, -1], #v[0, 1]] #v[-2, 3]
  unless pole.val.val == #[13, 10, 4, 7] &&
      pole.val.evalHorner 0 + pole.val.evalHorner 1 == 13 do
    throwError "pole message was changed by a scan, retry, or denominator division"
  let repeated := message (E := ℤ) (r := 0) (#v[[0, 0]] : Vector (List (Fin 1)) 1)
    (ell := 2) (by intro k; fin_cases k; decide) #v[1]
    #v[#v[2, 3]] #v[#v[3, 3]] #v[#v[0, 0]] #v[1, 1]
  unless repeated.val.val == #[-12, -6] do
    throwError "packed message discarded repeated occurrence multiplicity"
  let empty := message (E := ℤ) (r := 0) (#v[[]] : Vector (List (Fin 0)) 1)
    (ell := 0) (by intro k; fin_cases k; decide) (#v[3] : Vector ℤ 1)
    #v[] #v[] #v[#v[7, 11]] #v[2, 3]
  unless empty.val.val == #[49, 49, 12] do
    throwError "no occurrences incorrectly discarded a nonzero helper message"
  let zero := message (E := ℤ) (r := 0) (#v[] : Vector (List (Fin 1)) 0) (ell := 0)
    (fun k => Fin.elim0 k) (#v[] : Vector ℤ 0) #v[#v[2, 3]] #v[#v[5, 7]] #v[] #v[11, 13]
  unless zero.val.val == #[] do
    throwError "zero message retained trailing coefficient padding"
  let trivial := message (E := ZMod 1) (r := 0) singleton (ell := 1)
    (by intro k; fin_cases k; decide)
    (#v[1] : Vector (ZMod 1) 1) #v[#v[1, 1]] #v[#v[1, 1]] #v[#v[1, 1]] #v[1, 1]
  unless trivial.val.val == #[] do
    throwError "pure packing introduced a nontrivial-ring requirement"
  for name in #[``caller, ``row, ``coefficientsFrom, ``coefficients, ``message,
      ``cubic, ``binary, ``asymmetric, ``afterChallenge] do
    unless (Lean.IR.findEnvDecl (← getEnv) name).isSome do
      throwError "direct message caller lacks executable IR: {name}"
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``toPoly_row, ``toPoly_coefficients, ``toPoly_coefficients_eq_projection,
      ``size_row_le, ``size_coefficientsFrom_le, ``size_coefficients_le,
      ``message_toPoly, ``message_toMessage, ``binary_toPoly, ``binary_ne_X,
      ``binary_evaluations] do
    unless (← collectAxioms name).all allowed.contains do
      throwError "round coefficient proof has unexpected axioms: {name}"
  logInfo "packed cubic, F2 formal coefficients, suffix traversal and boundary checks passed"

#eval (show IO _ from do
  let table (c : ℤ) : CMlPolynomialEval ℤ 13 := Vector.replicate (2 ^ 13) c
  let q := message (E := ℤ) (r := 12) singleton (ell := 1)
    (by intro k; fin_cases k; decide) #v[11]
    #v[table 2] #v[table 3] #v[table 5] (table 7)
  unless q.val.val == #[2228224] do
    throw (IO.userError "4096-row streamed coefficient sum returned incorrect data")
  pure q.val.val)

end RoundCoefficientsTests

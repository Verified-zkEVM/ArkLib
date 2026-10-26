/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/
import ArkLib.ProofSystem.Logup.Prover.Helpers
import ArkLib.Data.Probability.KoalaBear
import Mathlib.Algebra.Field.ZMod
import Lean.Compiler.IR

/-! # Termwise honest helper algorithms at poles and away from poles -/

open CompPoly Logup.Prover
open scoped BigOperators

namespace LogupHelperTest

abbrev F := ZMod 17
instance : Fact (Nat.Prime 17) := ⟨by decide⟩
def cfg : Logup.Interaction.Config 0 4 2 :=
  (Logup.Interaction.Config.create? 0 4 2).get (by decide)

def data (i : Fin 2 × Fin 4) : CMlPolynomialEval F 0 :=
  #v[if i.1 = 0 then ![0, 1, 0, 1] i.2 else ![1, 2, -1, -2] i.2]

def denominators (alpha : F) := denominatorTables (RingHom.id F) alpha data
def weights := weightTables (RingHom.id F) data
def actualHelpers (alpha : F) := helpers cfg.groups (denominators alpha) weights

theorem balanced : ∀ v : F,
    ((Finset.univ : Finset (Fin 0 → Fin 2)).product (Finset.univ : Finset (Fin 4))).sumFiber
      (fun p => (data (0, p.2)).get (finFunctionFinEquiv p.1))
      (fun p => (data (1, p.2)).get (finFunctionFinEquiv p.1)) v = 0 := by decide

/-- No off-pole premise is used in this global theorem, even for nonzero helper entries. -/
theorem total_zero (alpha : F) :
    (∑ u : Fin 0 → Fin 2, ∑ k : Fin 2,
      (actualHelpers alpha)[k.val].get (finFunctionFinEquiv u)) = 0 :=
  sum_helpers_eq_zero_of_base_balance cfg (RingHom.id F) alpha data balanced

/-- The actual helpers satisfy their local residual away from their actual denominator poles. -/
theorem local_off_pole (k : Fin 2) :
    Logup.groupResidual cfg.groups[k.val] (2 : F)
      (fun i => (data (0, i)).get 0) (fun i => (data (1, i)).get 0)
      ((actualHelpers 2)[k.val].get 0) = 0 :=
  groupResidual_helpers cfg.groups (RingHom.id F) 2 data k 0
    (by revert k; decide)

def foldedHelperAtPole : F :=
  FractionPair.value (Logup.groupFraction cfg.groups[0] (0 : F)
    (fun i => (data (0, i)).get 0) (fun i => (data (1, i)).get 0))

abbrev Base := KoalaBear.Field
abbrev E := KoalaBear.Ext6

def extData (i : Fin 2 × Fin 1) : CMlPolynomialEval Base 0 :=
  if i.1 = 0 then #v[0] else #v[1]

def extHelper : E :=
  (helpers #v[[0]] (denominatorTables (algebraMap Base E) KoalaBear.ext6Gen extData)
    (weightTables (algebraMap Base E) extData))[0].get 0

def emptyHelpers : Vector (CMlPolynomialEval F 0) 0 := helpers #v[] #v[] #v[]

open Lean Elab Command

run_cmd do
  unless actualHelpers 0 == #v[#v[15], #v[2]] do
    throwError "termwise total inversion changed pole helper behavior"
  unless foldedHelperAtPole == 0 do throwError "folded pair pole fixture changed"
  unless (actualHelpers 0)[0].get 0 != foldedHelperAtPole do
    throwError "termwise helper was replaced by a folded pair quotient"
  unless actualHelpers 2 == #v[#v[11], #v[6]] do
    throwError "off-pole helper values changed"
  unless (List.finRange 17).all (fun a =>
      ((actualHelpers a.val)[0].get 0 + (actualHelpers a.val)[1].get 0) == 0) do
    throwError "balanced helper total is not zero at every scalar"
  unless Logup.groupResidual cfg.groups[0] (0 : F)
      (fun i => (data (0, i)).get 0) (fun i => (data (1, i)).get 0)
      ((actualHelpers 0)[0].get 0) == 1 do
    throwError "local residual pole counterexample disappeared"
  unless KoalaBear.ext6Gen * extHelper == 1 do
    throwError "actual base-to-extension termwise inverse helper failed"
  unless emptyHelpers == #v[] do throwError "empty helper construction failed"

run_cmd do
  for name in #[``denominatorTables, ``weightTables, ``helpers, ``actualHelpers,
      ``extHelper, ``emptyHelpers] do
    unless (Lean.IR.findEnvDecl (← getEnv) name).isSome do
      throwError "missing honest helper executable IR: {name}"
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``get_denominatorTables, ``get_weightTables, ``get_helpers,
      ``MLE_denominatorTables, ``groupResidual_helpers, ``sum_helpers_eq_zero,
      ``sum_helpers_eq_zero_of_base_balance, ``balanced, ``total_zero, ``local_off_pole] do
    unless (← collectAxioms name).all allowed.contains do
      throwError "unexpected honest helper axiom: {name}"

end LogupHelperTest

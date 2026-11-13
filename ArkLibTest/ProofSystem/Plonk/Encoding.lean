/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.ProofSystem.Plonk.Encoding.Computable
import Mathlib.Algebra.Field.ZMod

/-! # Executable Plonk encoding over a four-point subgroup -/

namespace ArkLibTest.PlonkEncoding

open Plonk

private abbrev F := ZMod 13

instance : Fact (Nat.Prime 13) := ⟨by decide⟩

private theorem primitive : IsPrimitiveRoot (5 : F) 4 := by
  apply (IsPrimitiveRoot.iff (by decide)).mpr
  constructor
  · decide
  · intro l hl hlt
    have h : ∀ i : Fin 4, 0 < i.val → (5 : F) ^ i.val ≠ 1 := by decide
    exact h ⟨l, hlt⟩ hl

private def domain : EvaluationDomain F 4 := EvaluationDomain.primitiveRoot 5 primitive

private def cosets : CosetLabels domain where
  k₁ := 2
  k₂ := 4
  k₁_ne_zero := by decide
  k₂_ne_zero := by decide
  disjoint_left_right := Set.disjoint_range_iff.mpr (by decide)
  disjoint_left_output := Set.disjoint_range_iff.mpr (by decide)
  disjoint_right_output := Set.disjoint_range_iff.mpr (by decide)

private def labels : Fin 12 → F := cosets.label

example : Function.Injective labels := cosets.label_injective

example : List.ofFn domain.node = [1, 5, 12, 8] := by decide

-- The public row fixes z₀ = 3; the remaining rows enforce z₁ = 2z₀ and z₂ = z₀z₁ = 5.
private def circuit : ConstraintSystem F 3 3 :=
  ![Gate.add 0 0 1, Gate.mul 0 1 2, Gate.eq 2 5]

private def prepared : ConstraintSystem F 3 4 :=
  circuit.prepare (by decide : 1 ≤ 3) (fun _ => 3)

private def cleared : ConstraintSystem F 3 4 := prepared.clearPublicConstants 1

private def assignment : Fin 3 → F := ![3, 6, 5]

private def badAssignment : Fin 3 → F := ![3, 7, 5]

private def occurrences : Fin 12 → F := prepared.occurrences assignment

private def badOccurrences : Fin 12 → F := prepared.occurrences badAssignment

private def wires : Fin 3 → CompPoly.CPolynomial F :=
  Computable.wirePolynomials domain occurrences

private def selectors : Selector (CompPoly.CPolynomial F) :=
  Computable.selectorPolynomials domain cleared

private def pi : CompPoly.CPolynomial F :=
  Computable.publicInputPolynomial domain (by decide : 1 ≤ 4) (fun _ => 3)

private def gate : CompPoly.CPolynomial F := Computable.gatePolynomial selectors wires pi

private def badGate : CompPoly.CPolynomial F :=
  Computable.gatePolynomial selectors (Computable.wirePolynomials domain badOccurrences) pi

private def permutation : Fin 3 → CompPoly.CPolynomial F :=
  Computable.permutationPolynomials domain prepared labels

example : prepared.perm (0 : Fin 12) ≠ 0 := by decide

example : List.ofFn (fun p => (prepared.perm p).val) =
    [1, 2, 4, 7, 5, 8, 9, 10, 0, 6, 11, 3] := by decide

example : prepared.accepts assignment := by
  unfold ConstraintSystem.accepts Gate.accepts
  decide

example : ¬ prepared.accepts badAssignment := by
  unfold ConstraintSystem.accepts Gate.accepts
  decide

example : gate.toPoly = Plonk.gatePolynomial (Plonk.selectorPolynomials domain cleared)
    (Plonk.wirePolynomials domain occurrences)
    (Plonk.publicInputPolynomial domain (by decide : 1 ≤ 4) (fun _ => 3)) :=
  Computable.gatePolynomial_toPoly domain cleared occurrences (by decide) (fun _ => 3)

-- A right occurrence in the public equality row does not affect its gate equation.
private def copyViolation : Fin 12 → F :=
  fun p => if p = 4 then 4 else occurrences p

private def copyViolationWires : Fin 3 → CompPoly.CPolynomial F :=
  Computable.wirePolynomials domain copyViolation

-- This caller exercises generated code for interpolation and polynomial arithmetic.
private def encodingRuntimeChecks : IO Unit := do
  unless (∀ i, gate.eval (domain.node i) = 0) do
    throw (IO.userError "Unexpected honest gate result")
  unless (badGate.eval (domain.node 1) ≠ 0) do
    throw (IO.userError "Unexpected altered gate result")
  unless (∀ c i, (wires c).eval (domain.node i) =
    occurrences (finProdFinEquiv (c, i))) do
    throw (IO.userError "Unexpected wire values result")
  unless (∀ c i, (permutation c).eval (domain.node i) =
    labels (prepared.perm (finProdFinEquiv (c, i)))) do
    throw (IO.userError "Unexpected permutation labels result")
  unless (pi.eval (domain.node 0) = -3 ∧ ∀ i : Fin 4, i ≠ 0 → pi.eval (domain.node i) = 0) do
    throw (IO.userError "Unexpected public input values result")
  unless (List.ofFn (fun i : Fin 4 => (wires 0).coeff i.val) = [10, 9, 6, 4]) do
    throw (IO.userError "Unexpected wire coefficients result")
  unless (List.ofFn (fun i : Fin 4 => pi.coeff i.val) = [9, 9, 9, 9]) do
    throw (IO.userError "Unexpected public input coefficients result")
  unless (∀ i, (Computable.preparedGatePolynomial domain circuit (by decide : 1 ≤ 3)
    (fun _ => 3) occurrences).eval (domain.node i) = 0) do
    throw (IO.userError "Unexpected prepared honest gate result")
  unless ((Computable.preparedGatePolynomial domain circuit (by decide : 1 ≤ 3)
    (fun _ => 3) badOccurrences).eval (domain.node 1) ≠ 0) do
    throw (IO.userError "Unexpected prepared altered gate result")
  unless (∀ i, (Computable.gatePolynomial selectors copyViolationWires pi).eval
    (domain.node i) = 0) do
    throw (IO.userError "Unexpected copy violation gate result")
  -- Position two maps to position four, whose altered value breaks sigma consistency.
  unless (let p : Fin 12 := 2
    let source := finProdFinEquiv.symm p
    let target := finProdFinEquiv.symm (prepared.perm p)
    (copyViolationWires target.1).eval (domain.node target.2) ≠
      (copyViolationWires source.1).eval (domain.node source.2)) do
    throw (IO.userError "Unexpected copy violation consistency result")
  -- Replacing the public input changes the reserved row residual.
  unless ((Computable.preparedGatePolynomial domain circuit (by decide : 1 ≤ 3)
    (fun _ => 4) occurrences).eval (domain.node 0) = 12) do
    throw (IO.userError "Unexpected incorrect public input result")
  IO.println "Plonk encoding runtime checks passed."

/-- info: Plonk encoding runtime checks passed. -/
#guard_msgs in
#eval encodingRuntimeChecks

#eval (List.ofFn (fun i : Fin 4 => gate.eval (domain.node i)),
  List.ofFn (fun i : Fin 4 => badGate.eval (domain.node i)))

end ArkLibTest.PlonkEncoding

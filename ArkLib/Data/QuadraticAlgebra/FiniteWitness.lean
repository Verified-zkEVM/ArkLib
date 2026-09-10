/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import Mathlib.Algebra.QuadraticAlgebra.Basic
public import Mathlib.FieldTheory.Finite.Basic

/-!
# Concrete quadratic witness fields

Given a certified nonsquare `a` in a field `F`, Mathlib's two-coordinate `QuadraticAlgebra F a 0`
is a field with the same characteristic and squared cardinality. Its values are pairs, rather
than an opaque chosen extension. The coordinate formulas below use only base-field operations
and identify the arithmetic needed by a later operational lowering.

No algorithm for finding the nonsquare or enumerating the extension is asserted here. In
particular the finite-field existence lemma is mathematical, not a free setup operation.
The coordinate refinements do not by themselves constitute a closed execution-cost theorem.
-/

@[expose] public section

namespace QuadraticAlgebra

variable {F : Type*} [Field F]

/-- A supplied nonsquare certifies the existing computable quadratic-algebra field operations. -/
@[instance_reducible]
def fieldOfNonsquare (a : F) (ha : ¬IsSquare a) : Field (QuadraticAlgebra F a 0) := by
  let : Fact (∀ r : F, r ^ 2 ≠ a + 0 * r) := ⟨by
    intro r hr
    apply ha
    refine ⟨r, ?_⟩
    simpa only [zero_mul, add_zero, pow_two] using hr.symm⟩
  infer_instance

/-- The extension values are explicitly two base-field coordinates. -/
theorem finiteWitness_natCard (a : F) [Finite F] :
    Nat.card (QuadraticAlgebra F a 0) = Nat.card F ^ 2 := by
  rw [Nat.card_congr (equivProd a 0), Nat.card_prod, pow_two]

/-- The concrete algebra preserves the base characteristic, without any field-size inference. -/
theorem finiteWitness_ringChar (a : F) :
    ringChar (QuadraticAlgebra F a 0) = ringChar F :=
  (Algebra.ringChar_eq F (QuadraticAlgebra F a 0)).symm

/-- Coordinate addition, with no extension-field oracle. -/
def addCoordinates (a : F) (x y : QuadraticAlgebra F a 0) : QuadraticAlgebra F a 0 :=
  ⟨x.re + y.re, x.im + y.im⟩

/-- Coordinate multiplication specialized to the zero linear coefficient. -/
def mulCoordinates (a : F) (x y : QuadraticAlgebra F a 0) : QuadraticAlgebra F a 0 :=
  ⟨x.re * y.re + a * x.im * y.im, x.re * y.im + x.im * y.re⟩

/-- Coordinate inversion shares the computed inverse norm between its output coordinates.
The zero input is sent to zero, as required by the field convention. -/
def invCoordinates (a : F) (x : QuadraticAlgebra F a 0) : QuadraticAlgebra F a 0 :=
  let normInverse := (x.re * x.re - a * x.im * x.im)⁻¹
  ⟨normInverse * x.re, -(normInverse * x.im)⟩

/-- Addition agrees with the canonical quadratic algebra. -/
theorem addCoordinates_eq (a : F) (x y : QuadraticAlgebra F a 0) :
    addCoordinates a x y = x + y := rfl

/-- Multiplication agrees with the canonical quadratic algebra. -/
theorem mulCoordinates_eq (a : F) (x y : QuadraticAlgebra F a 0) :
    mulCoordinates a x y = x * y := by
  ext <;> simp [mulCoordinates, mul_assoc]

/-- Inversion agrees with the certified field, including at zero. -/
theorem invCoordinates_eq (a : F) (ha : ¬IsSquare a) (x : QuadraticAlgebra F a 0) :
    letI := fieldOfNonsquare a ha
    invCoordinates a x = x⁻¹ := by
  let := fieldOfNonsquare a ha
  change invCoordinates a x = (norm x)⁻¹ • star x
  ext <;> simp [invCoordinates, norm_def]

/-- In a finite field of odd characteristic some parameter certifies such a concrete extension.
This is existence only; a future search must implement and charge its square tests. -/
theorem exists_finiteWitness_parameter [Finite F] (hchar : ringChar F ≠ 2) :
    ∃ a : F, ∀ r : F, r ^ 2 ≠ a := by
  let := Fintype.ofFinite F
  obtain ⟨a, ha⟩ := FiniteField.exists_nonsquare hchar
  refine ⟨a, fun r hr ↦ ha ⟨r, ?_⟩⟩
  simpa only [pow_two] using hr.symm

end QuadraticAlgebra

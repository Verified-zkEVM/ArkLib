/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.Matrix.ReadOnce
import ArkLib.ProofSystem.RingSwitching.Packing.Polynomial

/-!
# A read-once evaluator for the public packing multiplier

Multiplication in the opening algebra is represented by its finite-basis multiplication
matrix over the base ring. Matrix entries are transported into the challenge algebra. Each layer
is interpolated between multiplication by `1-rᵢ` and by `rᵢ`, and the final coordinate observation
uses the batching weights. This evaluates the C-valued multilinear extension of the Boolean table;
it never applies the B-linear observation to an unrelated C-valued point as if it were a ring map.

The implementation performs one square matrix-vector action for each retained variable, with
width equal to the opening rank, followed by one dot product. The instrumented read-once evaluator
certifies that action count. Dense layer interpolation uses two scalar multiplications and one
addition per matrix entry; a dense action uses one dot product of that width per output entry.
These counts concern the explicit online arithmetic, excluding basis/matrix preprocessing.

## References

* [*Ring switching, generalized*][RSG]
* [Bünz, B., Rothblum, R., and Wang, W., *Flock: Fast Proving for Batch Boolean
  Computations*][BRW26]
-/

noncomputable section

namespace RingSwitching.Packing.PackingData

open Module MvPolynomial Matrix

variable {B : Type} [CommRing B] (data : PackingData B)
  {C : Type*} [CommRing C] [Algebra B C]

/-- Opening coordinates transported into the independent challenge algebra. -/
def challengeCoordinates (a : data.E) : data.ιE → C :=
  fun u => algebraMap B C (data.openBasis.repr a u)

open Classical in
/-- The multiplication matrix with its base-ring entries transported to the challenge algebra. -/
def challengeMulMatrix (a : data.E) : Matrix data.ιE data.ιE C :=
  (Algebra.leftMulMatrix data.openBasis a).map (algebraMap B C)

open Classical in
/-- Transported multiplication matrices act on transported opening coordinates. -/
theorem challengeMulMatrix_mulVec (a x : data.E) :
    data.challengeMulMatrix (C := C) a *ᵥ data.challengeCoordinates x =
      data.challengeCoordinates (a * x) := by
  ext u
  change ((Algebra.leftMulMatrix data.openBasis a).map (algebraMap B C) *ᵥ
    ((algebraMap B C) ∘ data.openBasis.repr x)) u = _
  rw [← RingHom.map_mulVec, Algebra.leftMulMatrix_mulVec_repr]
  rfl

/-- Successive multiplication matrices accumulate the product of the opening elements. -/
theorem run_challengeMulMatrix {m : ℕ} (factors : Fin m → data.E) (x : data.E) :
    ReadOnce.run (fun i => data.challengeMulMatrix (C := C) (factors i))
      (data.challengeCoordinates x) = data.challengeCoordinates ((∏ i, factors i) * x) := by
  induction m generalizing x with
  | zero => simp
  | succ m ih =>
    rw [ReadOnce.run_succ, challengeMulMatrix_mulVec, ih, Fin.prod_univ_succ]
    congr 1
    ring

/-- The opening equality factor chosen by one Boolean input bit. -/
def equalityFactor (r : data.E) (b : Fin 2) : data.E := if b = 0 then 1 - r else r

/-- The two matrix branches for each retained coordinate. -/
def multiplierLayers {m : ℕ} (r : Fin m → data.E) :
    Fin m → Fin 2 → Matrix data.ιE data.ιE C :=
  fun i b => data.challengeMulMatrix (data.equalityFactor (r i) b)

/-- On Boolean input, the matrix program computes exactly the coordinates of the equality kernel. -/
theorem multiplierLayers_boolean {m : ℕ} (r : Fin m → data.E) (y : Fin m → Fin 2) :
    ReadOnce.run (fun i => data.multiplierLayers (C := C) r i (y i))
      (data.challengeCoordinates 1) =
      data.challengeCoordinates (eqTilde r (y : Fin m → data.E)) := by
  simp only [multiplierLayers]
  rw [run_challengeMulMatrix, mul_one]
  congr 1
  rw [eqTilde_eq_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  generalize y i = b
  fin_cases b <;> simp [equalityFactor]

/-- A weighted coordinate dot product is precisely the B-linear bridge, with no ring-map law. -/
theorem observe_challengeCoordinates (weight : data.ιE → C) (a : data.E) :
    dotProductBilin C C weight (data.challengeCoordinates a) = data.bridge weight a := by
  rw [data.bridge_apply]
  change (∑ u, weight u * algebraMap B C (data.openBasis.repr a u)) = _
  exact Finset.sum_congr rfl fun u _ => by rw [Algebra.smul_def, mul_comm]

/-- Evaluate the public multiplier by interpolating each layer of the opening-coordinate program. -/
def evaluateMultiplier {m : ℕ} (r : Fin m → data.E) (weight : data.ιE → C)
    (z : Fin m → C) : C :=
  dotProductBilin C C weight
    (ReadOnce.run (fun i => ReadOnce.interpolate (data.multiplierLayers r i) (z i))
      (data.challengeCoordinates 1))

/-- The read-once evaluator equals the multiplier polynomial at every challenge-algebra point. -/
theorem evaluateMultiplier_eq {m : ℕ} (r : Fin m → data.E) (weight : data.ιE → C)
    (z : Fin m → C) :
    data.evaluateMultiplier r weight z = (data.multiplier r weight).val.eval z := by
  rw [evaluateMultiplier, ReadOnce.observe_interpolate]
  change eval z (MLE _) = eval z (MLE _)
  apply congrArg (fun f : (Fin m → Fin 2) → C => eval z (MLE f))
  funext y
  rw [multiplierLayers_boolean, observe_challengeCoordinates]

/-- The instrumented online matrix evaluator performs exactly one action per retained coordinate. -/
theorem evaluateMultiplier_actions {m : ℕ} (r : Fin m → data.E) (z : Fin m → C) :
    (ReadOnce.runCounted (fun i => ReadOnce.interpolate (data.multiplierLayers r i) (z i))
      (data.challengeCoordinates 1)).2 = m := by
  rw [ReadOnce.runCounted_eq]

end RingSwitching.Packing.PackingData

end

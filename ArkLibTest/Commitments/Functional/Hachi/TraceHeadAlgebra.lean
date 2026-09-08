/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Commitments.Functional.Hachi.TraceHead.Coordinates

/-! # Actual Hachi coefficient packing at `q = 5`, `d = 2`, `k = 1` -/

open CompPoly ArkLib.Lattices.CyclotomicModulus
open ArkLib.Lattices.Hachi.TraceHead

namespace HachiTraceHeadAlgebraTest

noncomputable section

private instance : Fact (Nat.Prime 5) := ⟨by decide⟩

abbrev B : Type := ↥(fixedSubring (R := ZMod 5) 1 1)
abbrev A := Rq (powTwoCyclotomic (R := ZMod 5) 1)

/-- All divisibility and characteristic assumptions are jointly inhabited. -/
theorem valid_parameters : (2 : ZMod 5) ≠ 0 ∧ 2 * 2 ^ 0 ∣ 2 ^ 1 := by decide

noncomputable def coordinates : (Fin 2 → B) ≃ₗ[B] A :=
  coefficientEquiv 5 1 0 valid_parameters.1 valid_parameters.2

/-- A nonconstant scalar polynomial in the retained and packed variable: `1 + X + Y + XY`. -/
def f : CMlPolynomial B (1 + 1) := #v[1, 1, 1, 1]

noncomputable def F : CMlPolynomial A 1 := packCoefficients (n := 1) (t := 1) coordinates f

/-- The concrete source polynomial is recovered coefficient by coefficient. -/
theorem actual_coefficient_roundtrip : unpackCoefficients (n := 1) (t := 1) coordinates F = f :=
  unpack_packCoefficients (B := B) (A := A) (n := 1) (t := 1) coordinates f

/-- The scalar evaluation at retained coordinate `0`, packed coordinate `1` is `2`. -/
theorem actual_scalar_evaluation : f.eval (#v[(0 : B)] ++ #v[(1 : B)]) = (2 : B) := by
  rw [ArkLib.Lattices.Hachi.eval_eq_sum]
  simp [f, ArkLib.Lattices.Hachi.monomialBasis_get, Fin.sum_univ_succ, Fin.prod_univ_succ]
  ring

/-- The evaluated source value is genuinely nonzero in the actual quotient ring. -/
theorem actual_value_ne_zero : (2 : A) ≠ 0 := by
  have : Nontrivial A := (Fintype.one_lt_card_iff_nontrivial).mp (by
    rw [Rq.card_powTwo]
    decide)
  exact (isUnit_traceScale (R := ZMod 5) 1 0 valid_parameters.1 valid_parameters.2).ne_zero

/-- The real unnormalized trace check holds at a nonzero source claim. -/
theorem actual_trace_check :
    traceH 1 1 (F.eval ((#v[(0 : B)]).map (algebraMap B A)) *
      conjAut 1 (coordinates (CMlPolynomial.monomialBasis #v[(1 : B)]).get)) =
      2 • (2 : A) := by
  apply (trace_eval_eq_iff 5 1 0 valid_parameters.1 valid_parameters.2
    F #v[0] #v[1] 2).2
  change (unpackCoefficients (n := 1) (t := 1) coordinates F).eval (#v[(0 : B)] ++ #v[(1 : B)]) = 2
  rw [actual_coefficient_roundtrip, actual_scalar_evaluation]

/-- The actual generic algebra adapter has rank two in `Rq` and rank one in the fixed subring. -/
theorem actual_ranks :
    Fintype.card (packingData 5 1 0 valid_parameters.1 valid_parameters.2).ιP = 2 ∧
    Fintype.card (packingData 5 1 0 valid_parameters.1 valid_parameters.2).ιE = 1 := by
  change Fintype.card (Fin (2 ^ 1 / 2 ^ 0)) = 2 ∧ Fintype.card Unit = 1
  decide

end

end HachiTraceHeadAlgebraTest

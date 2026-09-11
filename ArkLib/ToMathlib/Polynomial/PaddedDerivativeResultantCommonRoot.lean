/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.ToMathlib.Polynomial.PaddedDerivativeResultant

/-!
# Common roots and padded derivative resultants

The fixed Sylvester sizes are retained after applying an arbitrary map into a domain.  Thus a
common root of the mapped polynomial and its derivative kills the padded resultant even when
the map lowers either actual degree.
-/

@[expose] public section

namespace Polynomial

noncomputable section

/-- A common root after mapping into a domain kills the original-size padded derivative
resultant.  No degree equality is required after the map. -/
theorem paddedDerivativeResultant_map_eq_zero_of_common_root
    {R S : Type*} [CommRing R] [IsDomain R] [CommRing S] [IsDomain S]
    (A : R[X]) {b : ℕ} (hb : 0 < b) (hdegree : A.natDegree ≤ b)
    (φ : R →+* S) (u : S)
    (hroot : (A.map φ).eval u = 0)
    (hderivative : (A.map φ).derivative.eval u = 0) :
    φ (paddedDerivativeResultant A b) = 0 := by
  let A' := A.map φ
  have hA'degree : A'.natDegree ≤ b := natDegree_map_le.trans hdegree
  have hderivativeDegree : A'.derivative.natDegree ≤ b - 1 :=
    (natDegree_derivative_le A').trans (Nat.sub_le_sub_right hA'degree 1)
  have hmap : φ (paddedDerivativeResultant A b) =
      resultant A'.derivative A' (b - 1) b := by
    rw [paddedDerivativeResultant, ← resultant_map_map]
    congr 2
    exact (derivative_map A φ).symm
  obtain ⟨P, Q, -, -, hbezout⟩ :=
    exists_mul_add_mul_eq_C_resultant A'.derivative A'
      hderivativeDegree hA'degree (Or.inr (Nat.ne_of_gt hb))
  rw [hmap]
  change A'.eval u = 0 at hroot
  change A'.derivative.eval u = 0 at hderivative
  have heval := congrArg (Polynomial.eval u) hbezout
  simpa only [eval_add, eval_mul, eval_C, hderivative, hroot, zero_mul, add_zero]
    using heval.symm

end

end Polynomial

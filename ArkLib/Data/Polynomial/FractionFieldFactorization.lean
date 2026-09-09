/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.Polynomial.FractionFieldExpand
import Mathlib.RingTheory.Polynomial.UniqueFactorization

/-!
# Content-aware fraction-field factorization

Nonconstant factors are represented by a single list of polynomial/exponent pairs. Repeated
entries retain factor multiplicities, and all degree-zero factors are accumulated into content.
Separability is asserted over the fraction field, not as a Bezout identity over the coefficient
ring. This algebraic factorization does not bound specialization exceptions.

## References

* [Ben-Sasson, E., Carmon, D., Haböck, U., Kopparty, S., Saraf, S.,
  *On Proximity Gaps for Reed--Solomon Codes*][BCHKS25], Section 3.2.
-/

namespace Polynomial

variable {R K : Type*} [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R]
  [Field K] [Algebra R K] [IsFractionRing R K]

/-- Every nonzero polynomial is nonzero content times a list of Frobenius expansions of
positive-degree factors that are irreducible and separable over the fraction field.
Repeated list entries encode multiplicity independently of their Frobenius exponents. -/
theorem exists_content_mul_fractionField_separable_factors (p : ℕ) [CharP K p]
    (hp : p ≠ 0) (f : R[X]) (hf : f ≠ 0) :
    ∃ (c : R) (s : List (R[X] × ℕ)), c ≠ 0 ∧
      (∀ t ∈ s, 0 < t.1.natDegree ∧ Irreducible t.1 ∧
        Irreducible (t.1.map (algebraMap R K)) ∧
        (t.1.map (algebraMap R K)).Separable) ∧
      f = C c * (s.map (fun t ↦ expand R (p ^ t.2) t.1)).prod ∧
      f.natDegree = (s.map (fun t ↦ t.1.natDegree * p ^ t.2)).sum := by
  classical
  induction f using WfDvdMonoid.induction_on_irreducible with
  | zero => exact (hf rfl).elim
  | unit u hu =>
    obtain ⟨c, hc, rfl⟩ := Polynomial.isUnit_iff.mp hu
    exact ⟨c, [], hc.ne_zero, by simp, by simp⟩
  | mul a i ha hi ih =>
    obtain ⟨c, s, hc, hs, hprod, hsum⟩ := ih ha
    by_cases hdeg : i.natDegree = 0
    · have hiC : i = C (i.coeff 0) := eq_C_of_natDegree_eq_zero hdeg
      have hi0 : i.coeff 0 ≠ 0 := by
        intro h
        exact hi.ne_zero (by simpa [h] using hiC)
      refine ⟨i.coeff 0 * c, s, mul_ne_zero hi0 hc, hs, ?_, ?_⟩
      · rw [hiC, hprod, C_mul, mul_assoc]
        simp
      · rw [natDegree_mul hi.ne_zero ha, hdeg, zero_add, hsum]
    · have hprim := hi.isPrimitive hdeg
      have hmap := (hprim.irreducible_iff_irreducible_map_fraction_map (K := K)).mp hi
      obtain ⟨n, g, hgi, hgs, hgi_eq, hdegree⟩ :=
        exists_fractionField_separable_expand p hp hmap
      have hgiR : Irreducible g := by
        let := isLocalHom_expand R (Nat.pos_of_ne_zero (pow_ne_zero n hp))
        exact Irreducible.of_map (by rwa [hgi_eq])
      have hgpos : 0 < g.natDegree := by
        by_contra h
        have hz : g.natDegree = 0 := Nat.eq_zero_of_not_pos h
        exact hdeg (by simpa [hz] using hdegree.symm)
      refine ⟨c, (g, n) :: s, hc, ?_, ?_, ?_⟩
      · intro t ht
        rcases List.mem_cons.mp ht with rfl | ht
        · exact ⟨hgpos, hgiR, hgi, hgs⟩
        · exact hs t ht
      · simp only [List.map_cons, List.prod_cons]
        rw [hgi_eq, hprod]
        ring
      · simp only [List.map_cons, List.sum_cons]
        rw [natDegree_mul hi.ne_zero ha, hdegree, hsum]

end Polynomial

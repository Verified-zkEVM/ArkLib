/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elias Judin, Stefano Rocca, Aristotle (Harmonic), Pablo Martín Vinuelas

Derived-source notice:
Copyright (c) 2026 Leanth Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elias Judin, Stefano Rocca, Aristotle (Harmonic)
-/
module

public import ArkLib.ProofSystem.Sumcheck.Spec.SingleRound

/-!
# Polynomial identities for honest sumcheck rounds

The projected round polynomial is a sum of direct polynomial substitutions. This identity
holds over a commutative semiring, including finite and trivial semirings; it does not use
an argument from equality of value tables. Its degree is bounded by the degree of the
selected coordinate, which can be smaller than the global individual-degree cap.

## References

* The honest-round algebra is derived from `Leanth/ProofSystem/ZeroCheck.lean` in
  [leanth PR #16](https://github.com/Verified-zkEVM/leanth/pull/16), source revision
  `23929f8c922cd4461ab22dbfaa6520f3ad23a3b2`.
* The coefficient-map proof adapts the `hright` argument in
  `toPoly_eval₂_CHom_insertNth` from
  `ArkLib/Commitments/Functional/Hachi/Sumcheck/RoundPoly.lean`, introduced by ArkLib revision
  `f06e28ed3af7d4af98cbffddbcf5fd4b8731fefb`. That source credits
  Pablo Martín Vinuelas and bears the 2024–2026 ArkLib Contributors copyright.
-/

@[expose] public section

open Polynomial MvPolynomial Finset

namespace Sumcheck.Spec.SingleRound

/-- Mapping the coefficients of the selected-variable representation is direct substitution. -/
theorem map_finSuccEquivNth_eq_eval₂_insertNth {R : Type} [CommSemiring R] {n : ℕ}
    (k : Fin (n + 1)) (s : Fin n → R) (p : MvPolynomial (Fin (n + 1)) R) :
    Polynomial.map (MvPolynomial.eval s) (finSuccEquivNth R k p) =
      MvPolynomial.eval₂ Polynomial.C
        (Fin.insertNth k Polynomial.X (fun j ↦ Polynomial.C (s j))) p := by
  rw [MvPolynomial.finSuccEquivNth_apply, MvPolynomial.coe_eval₂Hom]
  change (Polynomial.mapRingHom (MvPolynomial.eval s))
    (MvPolynomial.eval₂ _ _ p) = _
  rw [MvPolynomial.eval₂_comp_left]
  congr 1
  · ext a
    simp
  · funext j
    refine Fin.succAboveCases k ?_ ?_ j
    · simp [Fin.insertNth_apply_same]
    · intro l
      simp [Fin.insertNth_apply_succAbove]

/-- The honest round as direct substitution into the original polynomial, before evaluation. -/
theorem projectedRoundPolynomial_eq_sum_eval₂ {R : Type} [CommSemiring R]
    {n deg m : ℕ} (D : Fin m ↪ R) (k : Fin (n + 1))
    (c : Fin k.castSucc → R) (p : OracleStatement R (n + 1) deg ()) :
    (projectedRoundPolynomial R (n + 1) deg D k c p).val =
      ∑ x ∈ (univ.map D) ^ᶠ (n - k),
        MvPolynomial.eval₂ Polynomial.C
          (Fin.insertNth k Polynomial.X (fun j ↦ Polynomial.C (roundSuffix R n k c x j)))
          p.val := by
  change (∑ x ∈ (univ.map D) ^ᶠ (n - k), _) = _
  apply Finset.sum_congr rfl
  intro x _
  exact map_finSuccEquivNth_eq_eval₂_insertNth k (roundSuffix R n k c x) p.val

/-- Only the selected variable's degree bounds the honest round polynomial's degree. -/
theorem projectedRoundPolynomial_natDegree_le {R : Type} [CommSemiring R]
    {n deg m : ℕ} (D : Fin m ↪ R) (k : Fin (n + 1))
    (c : Fin k.castSucc → R) (p : OracleStatement R (n + 1) deg ()) :
    (projectedRoundPolynomial R (n + 1) deg D k c p).val.natDegree ≤ degreeOf k p.val := by
  change (∑ x ∈ (univ.map D) ^ᶠ (n - k),
    Polynomial.map (MvPolynomial.eval (roundSuffix R n k c x))
      (MvPolynomial.finSuccEquivNth R k p.val)).natDegree ≤ _
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro x _
  exact Polynomial.natDegree_map_le.trans (le_of_eq (natDegree_finSuccEquivNth _))

end Sumcheck.Spec.SingleRound

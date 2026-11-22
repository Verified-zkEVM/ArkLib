/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elias Judin, Stefano Rocca, Aristotle (Harmonic)

Derived-source notice:
Copyright (c) 2026 Leanth Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elias Judin, Stefano Rocca, Aristotle (Harmonic)
-/
module

public import ArkLib.ProofSystem.Sumcheck.Spec.SingleRound

/-!
# Polynomial identities for honest sum-check rounds

The honest round polynomial `projectedRoundPolynomial` is a sum of coordinate-line restrictions
(`MvPolynomial.evalExcept`). This file states two consequences at the round polynomial itself:

* `projectedRoundPolynomial_eq_sum_eval₂`: the round polynomial is a sum of direct polynomial
  substitutions into the original polynomial. The identity holds over any commutative semiring,
  including finite and trivial ones, so it does not rest on equality of value tables.
* `projectedRoundPolynomial_natDegree_le`: its degree is at most the degree of the original
  polynomial in the round's variable, which can be smaller than the global individual-degree cap.

## References

* The honest-round algebra comes from `Leanth/ProofSystem/ZeroCheck.lean` in
  [leanth PR #16](https://github.com/Verified-zkEVM/leanth/pull/16), source revision
  `23929f8c922cd4461ab22dbfaa6520f3ad23a3b2`. The underlying identities are in
  `ArkLib.Data.MvPolynomial.EvalExcept`.
-/

@[expose] public section

open Polynomial MvPolynomial Finset

namespace Sumcheck.Spec.SingleRound

variable {R : Type} [CommSemiring R] {m : ℕ} (D : Fin m ↪ R)

/-- The honest round polynomial is a sum of direct substitutions into the original polynomial:
the round's variable becomes `X` and every other variable a constant. -/
theorem projectedRoundPolynomial_eq_sum_eval₂ {n deg : ℕ} (k : Fin (n + 1))
    (c : Fin k.castSucc → R) (p : OracleStatement R (n + 1) deg ()) :
    (projectedRoundPolynomial R (n + 1) deg D k c p).val =
      ∑ x ∈ (univ.map D) ^ᶠ (n + 1 - 1 - k),
        MvPolynomial.eval₂ Polynomial.C
          (Fin.insertNth k Polynomial.X (fun j ↦ Polynomial.C (roundSuffix R (n + 1) k c x j)))
          p.val :=
  Finset.sum_congr rfl fun _ _ ↦ MvPolynomial.evalExcept_eq_eval₂_insertNth k _ p.val

/-- The honest round polynomial's degree is at most the original polynomial's degree in the
round's variable. -/
theorem projectedRoundPolynomial_natDegree_le {n deg : ℕ} (k : Fin n)
    (c : Fin k.castSucc → R) (p : OracleStatement R n deg ()) :
    (projectedRoundPolynomial R n deg D k c p).val.natDegree ≤ degreeOf k p.val :=
  Polynomial.natDegree_sum_le_of_forall_le _ _ fun _ _ ↦
    MvPolynomial.natDegree_evalExcept_le k _ p.val

end Sumcheck.Spec.SingleRound

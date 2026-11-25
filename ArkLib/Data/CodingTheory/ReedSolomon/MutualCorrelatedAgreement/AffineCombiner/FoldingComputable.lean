/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/
module

public import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.AffineCombiner.Computable
public import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.AffineCombiner.Folding

/-!
# Executable equal-degree polynomial folding

The CompPoly implementation uses the row pairing and recursion from `Folding`.
`toPoly_foldPolynomials` identifies the result with the polynomial in the soundness theorem.
-/

@[expose] public section

namespace ReedSolomon.Computable

open CompPoly

variable {F : Type*} [Field F] [DecidableEq F]

/-- Combine every even-odd pair with the same equal-degree challenge. -/
def foldRoundPolynomials {m : ℕ} (c : F × F × F) (P : Fin (2 ^ (m + 1)) → CPolynomial F) :
    Fin (2 ^ m) → CPolynomial F :=
  fun i ↦ equalDegreePolynomial c.1 c.2.1 c.2.2 (evenRows P i) (oddRows P i)

/-- Polynomial conversion commutes with a single folding round. -/
theorem toPoly_foldRoundPolynomials {m : ℕ} (c : F × F × F)
    (P : Fin (2 ^ (m + 1)) → CPolynomial F) :
    CPolynomial.toPoly ∘ foldRoundPolynomials c P =
      ReedSolomon.foldRoundPolynomials c (CPolynomial.toPoly ∘ P) := by
  funext i
  simp [foldRoundPolynomials, ReedSolomon.foldRoundPolynomials, evenRows, oddRows]

/-- Fold `2^r` computable polynomials to one using the `r` shared challenges in order. -/
def foldPolynomials (r : ℕ) (c : Fin r → F × F × F)
    (P : Fin (2 ^ r) → CPolynomial F) : CPolynomial F :=
  foldRows foldRoundPolynomials r c P

/-- The executable fold computes the polynomial used by the semantic folding theorem. -/
theorem toPoly_foldPolynomials (r : ℕ) (c : Fin r → F × F × F)
    (P : Fin (2 ^ r) → CPolynomial F) :
    (foldPolynomials r c P).toPoly = ReedSolomon.foldPolynomials r c (CPolynomial.toPoly ∘ P) := by
  induction r with
  | zero => rfl
  | succ r ih =>
    change (foldPolynomials r (Fin.tail c) (foldRoundPolynomials (c 0) P)).toPoly =
      ReedSolomon.foldPolynomials r (Fin.tail c)
        (ReedSolomon.foldRoundPolynomials (c 0) (CPolynomial.toPoly ∘ P))
    rw [ih, toPoly_foldRoundPolynomials]

end ReedSolomon.Computable

/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ilia Vlasov
-/

import ArkLib.Data.CodingTheory.ReedSolomon
import ArkLib.Data.MvPolynomial.Multilinear
import ArkLib.Data.MvPolynomial.LinearMvExtension

/-! This module provides an equivalent representation
  of RS-codes in terms of multilinear polynomials
  as can be found in [ACFY24].

## References

  * [Arnon, G., Chiesa, A., Fenzi, G., and Yogev, E., *WHIR: Reed–Solomon Proximity Testing
      with Super-Fast Verification*][ACFY24]
-/

namespace ReedSolomon

open MvPolynomial LinearMvExtension

variable {F : Type*} [Field F] {ι : Type*} (domain : ι ↪ F)

/-- A word `f` belongs to the RS-code iff there exists a multilinear polynomial `g`
  such that `f` is evaluation of `powAlgHom g` on points from the eval domain. -/
lemma mem_rs_code_iff_exists_mle
  {f : ι → F} {deg : ℕ} :
  f ∈ code domain (2 ^ deg) ↔
    ∃ g : F⦃≤ 1⦄[X (Fin deg)], f = evalOnPoints domain (powAlgHom g.1) := by
  constructor <;> intro h
  · rw [mem_code_iff_exists_polynomial] at h
    obtain ⟨g, hdeg, h⟩ := h
    let poly := linearMvExtension (m := deg) ⟨g, by
      aesop (add simp [Polynomial.mem_degreeLT])
    ⟩
    exists ⟨poly, by aesop (add simp [mem_restrictDegree_iff_degreeOf_le,
                                       linearMvExtension_degreeOf_lt])⟩
    aesop (add simp powAlgHom_is_right_inverse_to_linearMvExtension)
  · obtain ⟨g, h⟩ := h
    exact mem_code_of_polynomial_of_natDegree_lt_of_eval
      (powAlgHom g.1)
      (lt_of_le_of_lt powAlgHom_of_restrict_degree_natDegree (by grind))
      (by aesop)

/-- To prove a word `f` is in an RS-code, it is enough to
  provide a multilinear polynomial `g` whose `powAlgHom g` coincides
  with the word `f` on the evaluation domain. -/
lemma mem_rs_code_of_mle_of_eval
  {f : ι → F} {deg : ℕ} (g : F⦃≤ 1⦄[X (Fin deg)])
  (heval : ∀ i, f i = (powAlgHom g.1).eval (domain i)) :
  f ∈ code domain (2 ^ deg) := by
  aesop (add simp [mem_rs_code_iff_exists_mle])

end ReedSolomon

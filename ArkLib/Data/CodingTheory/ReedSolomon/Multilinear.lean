/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Julian Sutherland, Ilia Vlasov, Aristotle (Harmonic)
-/

import ArkLib.Data.CodingTheory.ReedSolomon
import ArkLib.Data.MvPolynomial.Multilinear
import ArkLib.Data.MvPolynomial.LinearMvExtension

namespace ReedSolomon

open MvPolynomial LinearMvExtension 

variable {F : Type*} [Field F] {ι : Type*} (domain : ι ↪ F)

lemma mem_rs_code_iff_exists_mle
  {f : ι → F} {deg : ℕ} :
  f ∈ code domain (2 ^ deg) ↔ 
    ∃ g : F⦃≤ 1⦄[X (Fin deg)], f = evalOnPoints domain (powAlgHom g.1) := by
  constructor <;> intro h
  · sorry
  · obtain ⟨g, h⟩ := h 
    apply mem_code_of_polynomial_of_natDegree_lt_of_eval
      (powAlgHom g.1)
    · exact Nat.lt_of_le_of_lt powAlgHom_of_restrict_degree_natDegree <| by
        grind
    · 

end ReedSolomon

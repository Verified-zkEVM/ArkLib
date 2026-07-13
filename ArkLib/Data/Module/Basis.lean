/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

import Mathlib.LinearAlgebra.Basis.Defs

/-!
# Basis recombination lemmas

The finite `R`-linear recombination along a basis, `s ↦ ∑ i, s i • b i`, is exactly
`b.equivFun.symm`, hence a bijection (in particular injective: distinct coordinate tuples
recombine to distinct module elements). Stated once here so both directions of a free-module
"pack/unpack" argument (e.g. the ring-switching packing- and opening-basis sides) consume the
same lemma.
-/

namespace Module.Basis

variable {ι R M : Type*} [Fintype ι] [Semiring R] [AddCommMonoid M] [Module R M]

/-- Recombination along a basis, `s ↦ ∑ i, s i • b i`, is a bijection: it is
`b.equivFun.symm` in pointful form. -/
theorem sum_smul_bijective (b : Basis ι R M) :
    Function.Bijective (fun s : ι → R => ∑ i, s i • b i) := by
  have h : (fun s : ι → R => ∑ i, s i • b i) = b.equivFun.symm := by
    funext s
    rw [Basis.equivFun_symm_apply]
  rw [h]
  exact b.equivFun.symm.bijective

/-- Recombination along a basis is injective: distinct coordinate tuples recombine to
distinct module elements. -/
theorem sum_smul_injective (b : Basis ι R M) :
    Function.Injective (fun s : ι → R => ∑ i, s i • b i) :=
  b.sum_smul_bijective.injective

end Module.Basis

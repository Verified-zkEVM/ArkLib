/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.Polynomial.FractionFieldRoots

/-!
# Frobenius expansion over a coefficient domain

An irreducible fraction-field polynomial descends to a separable factor by contracting exponents.
When the starting coefficients lie in a domain, the contracted coefficients still lie there.
This keeps the polynomial identity and its degree accounting in the original coefficient ring.
It does not factor content or provide bounds for specialization exceptions.

## References

* [Ben-Sasson, E., Carmon, D., Haböck, U., Kopparty, S., Saraf, S.,
  *On Proximity Gaps for Reed--Solomon Codes*][BCHKS25], Section 3.2.
-/

namespace Polynomial

variable {R K : Type*} [CommRing R] [Field K]
  [Algebra R K] [IsFractionRing R K]

/-- Separating a fraction-field irreducible by Frobenius contraction does not introduce
denominators into its coefficients. The expansion identity and degree equality hold over `R`.
The irreducibility premise deliberately applies after mapping, excluding pure content factors. -/
theorem exists_fractionField_separable_expand (p : ℕ) [CharP K p] (hp : p ≠ 0)
    {f : R[X]} (hf : Irreducible (f.map (algebraMap R K))) :
    ∃ (n : ℕ) (g : R[X]), Irreducible (g.map (algebraMap R K)) ∧
      (g.map (algebraMap R K)).Separable ∧
      expand R (p ^ n) g = f ∧ g.natDegree * p ^ n = f.natDegree := by
  obtain ⟨n, g, hg, hgf⟩ := exists_separable_of_irreducible p hf hp
  have hpow : p ^ n ≠ 0 := pow_ne_zero n hp
  have hmap : (contract (p ^ n) f).map (algebraMap R K) = g := by
    rw [map_contract hpow, ← hgf, contract_expand (p ^ n) hpow]
  have hexpand : expand R (p ^ n) (contract (p ^ n) f) = f := by
    apply Polynomial.map_injective (algebraMap R K) (IsFractionRing.injective R K)
    rw [map_expand, hmap, hgf]
  have hgi : Irreducible g := by
    let := isLocalHom_expand K (Nat.pos_of_ne_zero hpow)
    exact Irreducible.of_map (by rwa [hgf])
  exact ⟨n, contract (p ^ n) f, hmap ▸ hgi, hmap ▸ hg, hexpand,
    by rw [← natDegree_expand, hexpand]⟩

end Polynomial

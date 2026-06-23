/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tobias Rothmann
-/
import ArkLib.Data.Lattices.CyclotomicRing.Subfield.Cardinality

/-!
# `ψ` is a Bijection (Hachi §3, Theorem 2)

The packing map `ψ : (R_q^H)^{d/k} → R_q` is bijective over `R = ZMod q`. The two inputs:

* **injectivity** (`psi_injective`), from the non-degenerate trace pairing of Theorem 2
  (`traceH_psi_mul_conj`); and
* the **cardinality match** `|(R_q^H)^{d/k}| = (q^k)^{d/k} = q^d = |R_q|`, from
  `card_fixedSubring_eq` (`|R_q^H| = q^k`) and `Rq.card_powTwo` (`|R_q| = q^{2^α}`).

An injective endo-map of finite sets of equal cardinality is bijective
(`Fintype.bijective_iff_injective_and_card`).

## References

* [Nguyen, N. K., O'Rourke, G., and Zhang, J., *Hachi …*][NOZ26]
-/

open CompPoly Finset

namespace ArkLib.Lattices.CyclotomicModulus

variable (q : ℕ) [Fact (Nat.Prime q)] [NeZero q] [BEq (ZMod q)] [LawfulBEq (ZMod q)]

/-- **`ψ` is bijective** (Hachi [NOZ26, §3, Theorem 2]): injective (from the non-degenerate trace
pairing, `psi_injective`) and a cardinality match `|(R_q^H)^{d/k}| = (q^k)^{d/k} = q^d = |R_q|`. -/
theorem psi_bijective (α κ : ℕ) (h2 : (2 : ZMod q) ≠ 0) (hk : 2 * 2 ^ κ ∣ 2 ^ α) :
    Function.Bijective (psi (R := ZMod q) α (2 ^ κ)) := by
  have hκ : κ + 1 ≤ α := succ_le_of_two_mul_two_pow_dvd hk
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨psi_injective α (2 ^ κ) h2 ⟨κ, rfl⟩ hk, ?_⟩
  rw [Fintype.card_fun, Fintype.card_fin, card_fixedSubring_eq q α κ h2 hk, Rq.card_powTwo,
    Nat.pow_div (by omega) (by norm_num), ← pow_mul]
  congr 1
  rw [← pow_add]; congr 1; omega

end ArkLib.Lattices.CyclotomicModulus

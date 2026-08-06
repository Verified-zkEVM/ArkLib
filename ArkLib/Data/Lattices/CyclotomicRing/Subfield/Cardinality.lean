/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tobias Rothmann
-/
import ArkLib.Data.Lattices.CyclotomicRing.Subfield.TraceInnerProduct

/-!
# The Cardinality `|R_q^H| = q^k` of the Fixed Subring (Hachi §3, Eq. 7)

The number of free `ℤ_q`-parameters of `R_q^H` is exactly `k`. Two bounds:

* **Upper** (`card_fixedSubring_le`, general coefficient ring): from the injection
  `ψ : (R_q^H)^{d/k} ↪ R_q` (`psi_injective`) and `|R_q| = q^{2^α}`.
* **Lower** (`card_fixedSubring_ge`, over `R = ZMod q`): the symmetric basis `{vElt j}_{j<k}` of
  `Subfield/Basis.lean` gives an injection `(ℤ_q)^k ↪ R_q^H`, `c ↦ Σ_j (c_j).val · v_j` (using the
  `ℕ`-scalar `(c_j).val`, which avoids evaluating any ring multiplication). The triangular
  coefficient formula `vElt_coeff` makes the `(d/2k)·s`-th coefficient of the image equal to
  `(c_s).val · (2 if s=0 else 1)`, and `2` is a unit (`q` odd), so the map is injective.

Together (`card_fixedSubring_eq`) this pins `|R_q^H| = q^k`, the cardinality input to bijectivity
of `ψ` (`Subfield/Bijectivity.lean`).

## References

* [Nguyen, N. K., O'Rourke, G., and Zhang, J., *Hachi …*][NOZ26]
-/

open CompPoly Finset

namespace ArkLib.Lattices.CyclotomicModulus

variable {R : Type*} [Field R] [BEq R] [LawfulBEq R] [DecidableEq R]

/-- **`|R_q^H| ≤ q^k`**, from `ψ : (R_q^H)^{d/k} ↪ R_q` injective and `|R_q| = q^{2^α}`:
`|R_q^H|^{d/k} ≤ q^{2^α} = (q^k)^{d/k}`. -/
theorem card_fixedSubring_le (α κ : ℕ) (h2 : (2 : R) ≠ 0) (hk : 2 * 2 ^ κ ∣ 2 ^ α)
    [Fintype R] : Fintype.card (fixedSubring (R := R) α (2 ^ κ)) ≤ Fintype.card R ^ 2 ^ κ := by
  have hκ : κ ≤ α := Nat.le_of_succ_le (succ_le_of_two_mul_two_pow_dvd hk)
  have hle := Fintype.card_le_of_injective _ (psi_injective α (2 ^ κ) h2 ⟨κ, rfl⟩ hk)
  rw [Fintype.card_fun, Fintype.card_fin, Rq.card_powTwo, Nat.pow_div hκ (by norm_num),
    show (2 : ℕ) ^ α = 2 ^ κ * 2 ^ (α - κ) from by rw [← pow_add]; congr 1; omega, pow_mul] at hle
  exact (Nat.pow_le_pow_iff_left (by positivity : (0 : ℕ) < 2 ^ (α - κ)).ne').mp hle

/-! ## The lower bound `|R_q^H| ≥ q^k` and `|R_q^H| = q^k` (over `R = ZMod q`) -/

section ZModLowerBound

variable (q : ℕ) [Fact (Nat.Prime q)] [NeZero q] [BEq (ZMod q)] [LawfulBEq (ZMod q)]

/-- The injection `(ZMod q)^k → R_q^H`, `c ↦ Σ_j (c_j).val · v_j`, built from the symmetric basis
`vElt`. The `ℕ`-scalar `(c_j).val` is `c_j`'s canonical representative. -/
noncomputable def fixedBasisMap (α κ : ℕ) (hκ : κ + 1 ≤ α) (c : Fin (2 ^ κ) → ZMod q) :
    fixedSubring (R := ZMod q) α (2 ^ κ) :=
  ∑ j : Fin (2 ^ κ), (c j).val • vElt (R := ZMod q) α κ hκ j

/-- **`fixedBasisMap` is injective**: distinct coefficient vectors give distinct fixed elements,
read off at coefficient position `(d/2k)·s` via `vElt_coeff` and cancellation of the unit
`2 if s=0 else 1`. -/
theorem fixedBasisMap_injective (α κ : ℕ) (h2 : (2 : ZMod q) ≠ 0) (hκ : κ + 1 ≤ α) :
    Function.Injective (fixedBasisMap q α κ hκ) := by
  intro c c' hcc
  funext s
  set w : ZMod q := if (s : ℕ) = 0 then 2 else 1 with hw_def
  set D : fixedSubring (R := ZMod q) α (2 ^ κ) →+ ZMod q :=
    (Rq.coeffHom (powTwoCyclotomic (R := ZMod q) α) (2 ^ (α - κ - 1) * (s : ℕ))).comp
      (fixedSubring (R := ZMod q) α (2 ^ κ)).subtype.toAddMonoidHom with hD
  have hDvElt : ∀ j : Fin (2 ^ κ), D (vElt (R := ZMod q) α κ hκ j)
      = if s = j then w else 0 := by
    intro j
    rw [hD]
    change (vElt (R := ZMod q) α κ hκ j).val.1.coeff (2 ^ (α - κ - 1) * (s : ℕ))
      = if s = j then w else 0
    rw [vElt_coeff]
    by_cases hsj : s = j <;> simp [hsj, hw_def]
  have key : ∀ d : Fin (2 ^ κ) → ZMod q,
      D (fixedBasisMap q α κ hκ d) = (d s).val • w := by
    intro d
    rw [fixedBasisMap, map_sum]
    rw [Finset.sum_eq_single s (fun j _ hjs => by
        rw [map_nsmul, hDvElt, if_neg (fun h => hjs h.symm), smul_zero])
      (fun h => absurd (Finset.mem_univ s) h)]
    rw [map_nsmul, hDvElt, if_pos rfl]
  have e1 : (c s).val • w = (c' s).val • w := by rw [← key c, ← key c', hcc]
  rw [nsmul_eq_mul, nsmul_eq_mul] at e1
  have hwne : w ≠ 0 := by rw [hw_def]; by_cases hs0 : (s : ℕ) = 0 <;> simp [hs0, h2]
  have e2 := mul_right_cancel₀ hwne e1
  rwa [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val] at e2

/-- **`|R_q^H| ≥ q^k`** from the injection `(ZMod q)^k ↪ R_q^H`. -/
theorem card_fixedSubring_ge (α κ : ℕ) (h2 : (2 : ZMod q) ≠ 0) (hκ : κ + 1 ≤ α) :
    Fintype.card (ZMod q) ^ 2 ^ κ
      ≤ Fintype.card (fixedSubring (R := ZMod q) α (2 ^ κ)) := by
  have hinj := Fintype.card_le_of_injective _ (fixedBasisMap_injective q α κ h2 hκ)
  rwa [Fintype.card_fun, Fintype.card_fin] at hinj

/-- **`|R_q^H| = q^k`** (Hachi [NOZ26, §3, Eq. 7]): the symmetric basis has exactly `k` free
`ℤ_q`-parameters. -/
theorem card_fixedSubring_eq (α κ : ℕ) (h2 : (2 : ZMod q) ≠ 0) (hk : 2 * 2 ^ κ ∣ 2 ^ α) :
    Fintype.card (fixedSubring (R := ZMod q) α (2 ^ κ)) = Fintype.card (ZMod q) ^ 2 ^ κ := by
  have hκ : κ + 1 ≤ α := succ_le_of_two_mul_two_pow_dvd hk
  exact le_antisymm (card_fixedSubring_le α κ h2 hk) (card_fixedSubring_ge q α κ h2 hκ)

/-- **Support of a fixed element (Eq. 7).** Every `x ∈ R_q^H` has its nonzero coefficients on
multiples of `d/2k = 2^{α-κ-1}`: for `p < d` with `2^{α-κ-1} ∤ p`, `x.1.coeff p = 0`. This comes
from the symmetric `vElt` basis (`fixedBasisMap` is surjective by `card_fixedSubring_eq`), each of
whose elements is supported — by `vElt_coeff_full` — on the two multiples `(d/2k)·s` and
`d − (d/2k)·s` of `2^{α-κ-1}`. -/
theorem fixedSubring_coeff_eq_zero (α κ : ℕ) (h2 : (2 : ZMod q) ≠ 0) (hk : 2 * 2 ^ κ ∣ 2 ^ α)
    (x : fixedSubring (R := ZMod q) α (2 ^ κ)) {p : ℕ} (hp : p < 2 ^ α)
    (hdvd : ¬ (2 ^ (α - κ - 1) ∣ p)) :
    (x : Rq (powTwoCyclotomic (R := ZMod q) α)).1.coeff p = 0 := by
  have hκ : κ + 1 ≤ α := succ_le_of_two_mul_two_pow_dvd hk
  have hbij : Function.Bijective (fixedBasisMap q α κ hκ) := by
    rw [Fintype.bijective_iff_injective_and_card]
    exact ⟨fixedBasisMap_injective q α κ h2 hκ, by
      rw [Fintype.card_fun, Fintype.card_fin, card_fixedSubring_eq q α κ h2 hk]⟩
  obtain ⟨c, hc⟩ := hbij.surjective x
  set D : fixedSubring (R := ZMod q) α (2 ^ κ) →+ ZMod q :=
    (Rq.coeffHom (powTwoCyclotomic (R := ZMod q) α) p).comp
      (fixedSubring (R := ZMod q) α (2 ^ κ)).subtype.toAddMonoidHom with hD
  change D x = 0
  rw [← hc, fixedBasisMap, map_sum]
  refine Finset.sum_eq_zero (fun s _ => ?_)
  rw [map_nsmul]
  change (c s).val • (vElt α κ hκ s).val.1.coeff p = _
  rw [vElt_coeff_full α κ hκ s hp]
  have hdvd2 : 2 ^ (α - κ - 1) ∣ 2 ^ α := pow_dvd_pow 2 (by omega)
  have hz : (if (s : ℕ) = 0 then (if p = 0 then (2 : ZMod q) else 0)
      else if p = 2 ^ (α - κ - 1) * (s : ℕ) then 1
           else if p = 2 ^ α - 2 ^ (α - κ - 1) * (s : ℕ) then -1 else 0) = 0 := by
    split_ifs with h1 h2 h3 h4
    · exact absurd (h2 ▸ dvd_zero _) hdvd
    · rfl
    · exact absurd ⟨_, h3⟩ hdvd
    · exact absurd (h4 ▸ Nat.dvd_sub hdvd2 ⟨_, rfl⟩) hdvd
    · rfl
  rw [hz, smul_zero]

end ZModLowerBound

end ArkLib.Lattices.CyclotomicModulus

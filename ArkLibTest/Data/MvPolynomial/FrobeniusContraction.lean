/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.MvPolynomial.FrobeniusContraction
import ArkLib.ToMathlib.MvPolynomial.FrobeniusPullback
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.Algebra.MvPolynomial.Division

/-!
# Acceptance tests for Frobenius contraction in one multivariate variable

The examples cover:

* `X none ^ p + X (some j)` in prime characteristic `p` contracts exactly once, to
  `X none + X (some j)`;
* in characteristic zero, with exponential characteristic `1`, every witness is the input itself;
* positive degree in `none` is needed: `X (some j)` has no witness;
* irreducibility is needed: over `ℚ` the reducible `X none * X none` has no witness;
* the full fraction-field statement over a field, in characteristic `p` and in exponential
  characteristic `p`, with primitivity, the mapped derivative and the mapped degree derived from
  the theorems of the module;
* the inverse Frobenius coefficient twist of a terminal polynomial is irreducible, has nonzero
  partial derivative in `none`, and has the same degree in every variable.
-/

open MvPolynomial

section OneContraction

variable {R σ : Type*} [CommRing R]

/-- `rootExpansion s` sends `X none + X (some j)` to `X none ^ s + X (some j)`. -/
private theorem rootExpansion_X_none_add_X_some (s : ℕ) (j : σ) :
    rootExpansion s (X none + X (some j) : MvPolynomial (Option σ) R) =
      X none ^ s + X (some j) := by
  apply (optionEquivLeft R σ).injective
  simp [rootExpansion, optionEquivLeft_X_some, optionEquivLeft_X_none]

variable [IsDomain R]

/-- `X none ^ s + X (some j)` is irreducible for every `s`: it is monic of degree one in
`X (some j)`. -/
private theorem irreducible_X_none_pow_add_X_some (s : ℕ) (j : σ) :
    Irreducible (X none ^ s + X (some j) : MvPolynomial (Option σ) R) := by
  classical
  let τ : Option σ ≃ Option σ := Equiv.swap none (some j)
  have hlin : Irreducible (Polynomial.X + Polynomial.C (X j ^ s) :
      Polynomial (MvPolynomial σ R)) := by
    simpa only [map_neg, sub_neg_eq_add] using
      Polynomial.irreducible_X_sub_C (-(X j ^ s : MvPolynomial σ R))
  have hlin' : (optionEquivLeft R σ).symm (Polynomial.X + Polynomial.C (X j ^ s)) =
      renameEquiv R τ (X none ^ s + X (some j)) := by
    apply (optionEquivLeft R σ).injective
    simp [τ, optionEquivLeft_X_some, optionEquivLeft_X_none, add_comm]
  have h := hlin.map (optionEquivLeft R σ).symm
  rw [hlin'] at h
  exact (MulEquiv.irreducible_iff (renameEquiv R τ).toMulEquiv).mp h

variable (p : ℕ) [CharP R p] [Fact p.Prime]

/-- In prime characteristic `p`, the terminal contraction of `X none ^ p + X (some j)` has
exponent `e = 1` and terminal polynomial `X none + X (some j)`. -/
example (j : σ) :
    ∃ G : MvPolynomial (Option σ) R,
      rootExpansion (p ^ 1) G = X none ^ p + X (some j) ∧
      pderiv none G ≠ 0 ∧
      G = X none + X (some j) := by
  have hp := (Fact.out : p.Prime)
  have hFdeg : (X none ^ p + X (some j) : MvPolynomial (Option σ) R).degreeOf none = p := by
    rw [← natDegree_optionEquivLeft]
    simp only [map_add, map_pow, optionEquivLeft_X_none, optionEquivLeft_X_some]
    exact Polynomial.natDegree_X_pow_add_C
  have hFder : pderiv none (X none ^ p + X (some j) : MvPolynomial (Option σ) R) = 0 := by
    simp [CharP.cast_eq_zero]
  obtain ⟨e, G, hder, hGF, hdeg, hpos, -, -⟩ :=
    exists_irreducible_frobeniusContraction p (by rw [hFdeg]; exact hp.pos)
      (irreducible_X_none_pow_add_X_some p j)
  have he : e = 1 := by
    rw [hFdeg] at hdeg
    rcases e with _ | _ | e
    · rw [pow_zero, rootExpansion, Polynomial.expand_one, AlgEquiv.symm_apply_apply] at hGF
      exact absurd (hGF ▸ hFder) hder
    · rfl
    · have h1 : p ^ (e + 1 + 1) ≤ G.degreeOf none * p ^ (e + 1 + 1) :=
        Nat.le_mul_of_pos_left _ hpos
      have h2 : p ^ 1 < p ^ (e + 1 + 1) := Nat.pow_lt_pow_right hp.one_lt (by omega)
      rw [pow_one] at h2
      omega
  subst he
  refine ⟨G, hGF, hder, ?_⟩
  rw [← rootContraction_rootExpansion (pow_ne_zero 1 hp.ne_zero) G, hGF, pow_one,
    ← rootExpansion_X_none_add_X_some, rootContraction_rootExpansion hp.ne_zero]

end OneContraction

/-- With exponential characteristic `1`, every witness of
`exists_irreducible_frobeniusContraction_expChar` over `ℚ` is the input itself. -/
example {F : MvPolynomial (Option (Fin 2)) ℚ} (hFpos : 0 < F.degreeOf none)
    (hF : Irreducible F) :
    pderiv none F ≠ 0 := by
  obtain ⟨e, G, hder, hGF, -⟩ := exists_irreducible_frobeniusContraction_expChar 1 hFpos hF
  rw [one_pow, rootExpansion, Polynomial.expand_one, AlgEquiv.symm_apply_apply] at hGF
  rwa [← hGF]

/-- Positive degree in `none` is needed: `X (some j)` is irreducible but has degree `0` in
`none`, and no polynomial of positive degree in `none` satisfies the degree identity. -/
example {R σ : Type*} [CommRing R] [IsDomain R] (p : ℕ) [ExpChar R p] (j : σ) :
    Irreducible (X (some j) : MvPolynomial (Option σ) R) ∧
      ¬∃ e : ℕ, ∃ G : MvPolynomial (Option σ) R,
        G.degreeOf none * p ^ e = (X (some j) : MvPolynomial (Option σ) R).degreeOf none ∧
        0 < G.degreeOf none := by
  refine ⟨X_prime.irreducible, ?_⟩
  rintro ⟨e, G, hdeg, hpos⟩
  rw [degreeOf_X_of_ne (Option.some_ne_none j).symm] at hdeg
  have : 0 < G.degreeOf none * p ^ e := Nat.mul_pos hpos (pow_pos (expChar_pos R p) e)
  omega

/-- Irreducibility is needed: over `ℚ`, with exponential characteristic `1`, a witness for the
reducible `X none * X none` would be `X none * X none` itself, which is not irreducible. -/
example :
    ¬∃ e : ℕ, ∃ G : MvPolynomial (Option (Fin 1)) ℚ,
      rootExpansion (1 ^ e) G = X none * X none ∧ Irreducible G := by
  rintro ⟨e, G, hGF, hG⟩
  rw [one_pow, rootExpansion, Polynomial.expand_one, AlgEquiv.symm_apply_apply] at hGF
  subst hGF
  rcases hG.isUnit_or_isUnit rfl with h | h <;> exact X_prime.not_isUnit h

section FractionRing

variable {K σ L : Type*} [Field K] [Field L]
  [Algebra (MvPolynomial σ K) L] [IsFractionRing (MvPolynomial σ K) L]

/-- A terminal polynomial is primitive in `none`, its image over the fraction field `L` of the
coefficient ring is irreducible with nonzero derivative and is separable, and mapping preserves
its degree in `none`. -/
private theorem terminal_map_fractionRing {G : MvPolynomial (Option σ) K}
    (hder : pderiv none G ≠ 0) (hpos : 0 < G.degreeOf none) (hirr : Irreducible G) :
    (optionEquivLeft K σ G).IsPrimitive ∧
      Irreducible ((optionEquivLeft K σ G).map (algebraMap (MvPolynomial σ K) L)) ∧
      Polynomial.derivative ((optionEquivLeft K σ G).map
        (algebraMap (MvPolynomial σ K) L)) ≠ 0 ∧
      ((optionEquivLeft K σ G).map (algebraMap (MvPolynomial σ K) L)).Separable ∧
      ((optionEquivLeft K σ G).map (algebraMap (MvPolynomial σ K) L)).natDegree =
        G.degreeOf none := by
  have hinj := IsFractionRing.injective (MvPolynomial σ K) L
  refine ⟨(hirr.map (optionEquivLeft K σ)).isPrimitive (by
      rw [natDegree_optionEquivLeft]; exact hpos.ne'),
    irreducible_map_optionEquivLeft_fractionRing hirr hpos, ?_,
    separable_map_optionEquivLeft_fractionRing hirr hder, ?_⟩
  · rw [Polynomial.derivative_map, ← optionEquivLeft_pderiv_none, ne_eq,
      Polynomial.map_eq_zero_iff hinj, map_eq_zero_iff _ (optionEquivLeft K σ).injective]
    exact hder
  · rw [Polynomial.natDegree_map_eq_of_injective hinj, natDegree_optionEquivLeft]

/-- The ten-part statement over a field of prime characteristic `p`: the terminal contraction,
together with primitivity, the irreducible separable image over the fraction field `L`, its
nonzero derivative and its degree. -/
example (p : ℕ) [CharP K p] [Fact p.Prime] {F : MvPolynomial (Option σ) K}
    (hFpos : 0 < F.degreeOf none) (hFirr : Irreducible F) :
    ∃ e : ℕ, ∃ G : MvPolynomial (Option σ) K,
      rootExpansion (p ^ e) G = F ∧
      pderiv none G ≠ 0 ∧
      G.degreeOf none * (p ^ e) = F.degreeOf none ∧
      Irreducible G ∧
      (∀ j : σ, G.degreeOf (some j) ≤ F.degreeOf (some j)) ∧
      (optionEquivLeft K σ G).IsPrimitive ∧
      Irreducible ((optionEquivLeft K σ G).map (algebraMap (MvPolynomial σ K) L)) ∧
      Polynomial.derivative ((optionEquivLeft K σ G).map
        (algebraMap (MvPolynomial σ K) L)) ≠ 0 ∧
      ((optionEquivLeft K σ G).map (algebraMap (MvPolynomial σ K) L)).Separable ∧
      ((optionEquivLeft K σ G).map (algebraMap (MvPolynomial σ K) L)).natDegree =
        G.degreeOf none := by
  obtain ⟨e, G, hder, hGF, hdeg, hpos, hirr, hother, -, -⟩ :=
    exists_frobeniusContraction_fractionRing (L := L) p hFpos hFirr
  obtain ⟨hprim, hmapirr, hmapder, hmapsep, hmapdeg⟩ :=
    terminal_map_fractionRing (L := L) hder hpos hirr
  exact ⟨e, G, hGF, hder, hdeg, hirr, hother, hprim, hmapirr, hmapder, hmapsep, hmapdeg⟩

/-- The same ten-part statement in exponential characteristic `p`. -/
example (p : ℕ) [ExpChar K p] {F : MvPolynomial (Option σ) K}
    (hFpos : 0 < F.degreeOf none) (hFirr : Irreducible F) :
    ∃ e : ℕ, ∃ G : MvPolynomial (Option σ) K,
      rootExpansion (p ^ e) G = F ∧
      pderiv none G ≠ 0 ∧
      G.degreeOf none * (p ^ e) = F.degreeOf none ∧
      Irreducible G ∧
      (∀ j : σ, G.degreeOf (some j) ≤ F.degreeOf (some j)) ∧
      (optionEquivLeft K σ G).IsPrimitive ∧
      Irreducible ((optionEquivLeft K σ G).map (algebraMap (MvPolynomial σ K) L)) ∧
      Polynomial.derivative ((optionEquivLeft K σ G).map
        (algebraMap (MvPolynomial σ K) L)) ≠ 0 ∧
      ((optionEquivLeft K σ G).map (algebraMap (MvPolynomial σ K) L)).Separable ∧
      ((optionEquivLeft K σ G).map (algebraMap (MvPolynomial σ K) L)).natDegree =
        G.degreeOf none := by
  obtain ⟨e, G, hder, hGF, hdeg, hpos, hirr, hother⟩ :=
    exists_irreducible_frobeniusContraction_expChar p hFpos hFirr
  obtain ⟨hprim, hmapirr, hmapder, hmapsep, hmapdeg⟩ :=
    terminal_map_fractionRing (L := L) hder hpos hirr
  exact ⟨e, G, hGF, hder, hdeg, hirr, hother, hprim, hmapirr, hmapder, hmapsep, hmapdeg⟩

end FractionRing

/-- Over a perfect field of exponential characteristic `p`, the inverse Frobenius coefficient
twist of an irreducible polynomial with nonzero partial derivative in `none` is irreducible, has
nonzero partial derivative in `none`, and has the same degree in every variable. -/
example {K σ : Type*} [Field K] [PerfectField K] (p : ℕ) [ExpChar K p] (e : ℕ)
    {G : MvPolynomial (Option σ) K} (hGirr : Irreducible G) (hGder : pderiv none G ≠ 0) :
    Irreducible (inverseFrobeniusTwist p e G) ∧
      pderiv none (inverseFrobeniusTwist p e G) ≠ 0 ∧
      ∀ i : Option σ, (inverseFrobeniusTwist p e G).degreeOf i = G.degreeOf i :=
  ⟨(irreducible_inverseFrobeniusTwist_iff p e).mpr hGirr,
    (pderiv_inverseFrobeniusTwist_ne_zero_iff p e G none).mpr hGder,
    degreeOf_inverseFrobeniusTwist p e G⟩

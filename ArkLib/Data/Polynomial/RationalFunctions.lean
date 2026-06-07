/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Katerina Hristova, František Silváši, Julian Sutherland, Ilia Vlasov
-/

import ArkLib.Data.Polynomial.Bivariate
import ArkLib.Data.Polynomial.Prelims
import Mathlib.FieldTheory.RatFunc.Defs
import Mathlib.RingTheory.Ideal.Quotient.Defs
import Mathlib.RingTheory.Ideal.Span
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.PowerSeries.Substitution

import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Roots
/-!
# Function Fields and Rings of Regular Functions

We define the notions of Appendix A of [BCIKS20].

## References

[BCIKS20] Eli Ben-Sasson, Dan Carmon, Yuval Ishai, Swastik Kopparty, and Shubhangi Saraf.
  Proximity gaps for Reed-Solomon codes. In 2020 IEEE 61st Annual Symposium on Foundations of
  Computer Science (FOCS), 2020. Full paper: https://eprint.iacr.org/2020/654,
  version 20210703:203025.

-/

set_option linter.style.longFile 2000

open Polynomial Polynomial.Bivariate ToRatFunc Ideal

namespace BCIKS20AppendixA

section

variable {F : Type} [CommRing F] [IsDomain F]

/-- Construction of the monicized polynomial `H_tilde` in Appendix A.1 of [BCIKS20].
Note: Here `H ∈ F[X][Y]` translates to `H ∈ F[Z][Y]` in [BCIKS20], and `H_tilde` in
`Polynomial (RatFunc F)` translates to `H_tilde ∈ F(Z)[T]` in [BCIKS20]. -/
noncomputable def H_tilde (H : F[X][Y]) : Polynomial (RatFunc F) :=
  let hᵢ (i : ℕ) := H.coeff i
  let d := H.natDegree
  let W := (RingHom.comp Polynomial.C univPolyHom) (hᵢ d)
  let S : Polynomial (RatFunc F) := Polynomial.X / W
  let H' := Polynomial.eval₂ (RingHom.comp Polynomial.C univPolyHom) S H
  W ^ (d - 1) * H'

section FieldIrreducibility

variable {F : Type} [Field F]

private lemma univPolyHom_injective :
    Function.Injective (univPolyHom (F := F)) := by
  simpa [ToRatFunc.univPolyHom] using (RatFunc.algebraMap_injective (K := F))

private lemma irreducible_comp_C_mul_X_iff {K : Type} [Field K] (a : K) (ha : a ≠ 0)
    (p : K[X]) :
    Irreducible (p.comp (Polynomial.C a * Polynomial.X)) ↔ Irreducible p := by
  letI : Invertible a := invertibleOfNonzero ha
  let e : K[X] ≃ₐ[K] K[X] := Polynomial.algEquivCMulXAddC a 0
  have hp : e p = p.comp (Polynomial.C a * Polynomial.X) := by
    simp [e, ← Polynomial.comp_eq_aeval]
  rw [← hp]
  exact MulEquiv.irreducible_iff (f := (e : K[X] ≃* K[X])) (x := p)

private lemma irreducible_map_univPolyHom_of_irreducible
    {H : Polynomial (Polynomial F)} (hdeg : H.natDegree ≠ 0)
    (hH : Irreducible H) :
    Irreducible (H.map (univPolyHom (F := F))) := by
  have hprim : H.IsPrimitive := Irreducible.isPrimitive hH hdeg
  simpa [ToRatFunc.univPolyHom] using
    (Polynomial.IsPrimitive.irreducible_iff_irreducible_map_fraction_map
      (K := RatFunc F) hprim).mp hH

/-- Corrected irreducibility statement for `H_tilde`: the paper assumes positive `Y`-degree.
Without this hypothesis, a constant irreducible in `F[Z][Y]` can become a unit in `F(Z)[T]`. -/
lemma irreducibleHTildeOfIrreducible_of_natDegree_pos
    {H : Polynomial (Polynomial F)} (hdeg : 0 < H.natDegree)
    (hH : Irreducible H) :
    Irreducible (H_tilde H) := by
  classical
  let d : ℕ := H.natDegree
  let a : RatFunc F := univPolyHom (F := F) H.leadingCoeff
  let W : Polynomial (RatFunc F) := Polynomial.C a
  have hH_ne : H ≠ 0 := Polynomial.ne_zero_of_natDegree_gt hdeg
  have hlead_ne : H.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hH_ne
  have ha_ne : a ≠ 0 := by
    intro ha
    exact hlead_ne (univPolyHom_injective (by simpa [a] using ha))
  have hmap_irreducible : Irreducible (H.map (univPolyHom (F := F))) :=
    irreducible_map_univPolyHom_of_irreducible (Nat.ne_of_gt hdeg) hH
  have hsub :
      Polynomial.X / W = Polynomial.C a⁻¹ * (Polynomial.X : Polynomial (RatFunc F)) := by
    calc
      Polynomial.X / W = Polynomial.X / Polynomial.C a := rfl
      _ = Polynomial.X * Polynomial.C a⁻¹ := Polynomial.div_C
      _ = Polynomial.C a⁻¹ * Polynomial.X := by rw [mul_comm]
  have hcomp_irreducible :
      Irreducible
        ((H.map (univPolyHom (F := F))).comp
          (Polynomial.C a⁻¹ * (Polynomial.X : Polynomial (RatFunc F)))) := by
    exact (irreducible_comp_C_mul_X_iff (a := a⁻¹) (inv_ne_zero ha_ne)
      (H.map (univPolyHom (F := F)))).mpr hmap_irreducible
  have heval :
      Polynomial.eval₂ (RingHom.comp Polynomial.C (univPolyHom (F := F))) (Polynomial.X / W) H =
        (H.map (univPolyHom (F := F))).comp (Polynomial.X / W) := by
    simpa [Polynomial.comp] using
      (Polynomial.eval₂_map (p := H) (f := univPolyHom (F := F))
        (g := (Polynomial.C : RatFunc F →+* Polynomial (RatFunc F)))
        (x := Polynomial.X / W)).symm
  have heval_irreducible :
      Irreducible
        (Polynomial.eval₂ (RingHom.comp Polynomial.C (univPolyHom (F := F))) (Polynomial.X / W)
          H) := by
    rw [heval, hsub]
    exact hcomp_irreducible
  have hunitW : IsUnit (W ^ (d - 1)) := by
    exact (isUnit_C.mpr (Ne.isUnit ha_ne)).pow (d - 1)
  rcases hunitW with ⟨u, hu⟩
  have htilde :
      H_tilde H =
        W ^ (d - 1) *
          Polynomial.eval₂ (RingHom.comp Polynomial.C (univPolyHom (F := F))) (Polynomial.X / W)
            H := by
    rfl
  rw [htilde, ← hu]
  exact (irreducible_units_mul (M := Polynomial (RatFunc F)) (u := u)).2 heval_irreducible

end FieldIrreducibility

/-- The monicized version `H_tilde` is irreducible if the original polynomial `H` is irreducible
and has positive degree in `Y`, as assumed in Appendix A.1 of [BCIKS20]. -/
lemma irreducibleHTildeOfIrreducible {F : Type} [Field F] {H : Polynomial (Polynomial F)}
    (hHdeg : 0 < H.natDegree) :
    Irreducible H → Irreducible (H_tilde H) :=
  irreducibleHTildeOfIrreducible_of_natDegree_pos hHdeg

/-- The function field `𝕃` from Appendix A.1 of [BCIKS20]. -/
abbrev 𝕃 (H : F[X][Y]) : Type :=
  (Polynomial (RatFunc F)) ⧸ (Ideal.span {H_tilde H})

/-- The function field `𝕃` is a field when `H` is irreducible and has positive `Y`-degree. -/
lemma isField_of_irreducible_of_natDegree_pos {F : Type} [Field F] {H : F[X][Y]}
    (hHdeg : 0 < H.natDegree) (hH : Irreducible H) : IsField (𝕃 H) := by
  unfold 𝕃
  erw [← Ideal.Quotient.maximal_ideal_iff_isField_quotient, principal_is_maximal_iff_irred]
  exact irreducibleHTildeOfIrreducible_of_natDegree_pos hHdeg hH

/-- The function field `𝕃` is a field under the standard Appendix A irreducibility hypothesis. -/
lemma isField_of_irreducible {F : Type} [Field F] {H : F[X][Y]} (hHdeg : 0 < H.natDegree) :
    Irreducible H → IsField (𝕃 H) := by
  intro h
  unfold 𝕃
  erw [← Ideal.Quotient.maximal_ideal_iff_isField_quotient, principal_is_maximal_iff_irred]
  exact irreducibleHTildeOfIrreducible hHdeg h

/-- The function field `𝕃` is a field under positive-degree irreducibility assumptions. -/
noncomputable instance {F : Type} [Field F] {H : F[X][Y]} [hHdeg : Fact (0 < H.natDegree)]
    [inst : Fact (Irreducible H)] : Field (𝕃 H) :=
  IsField.toField (isField_of_irreducible hHdeg.out inst.out)

/-- The integral monicized polynomial corresponding to `H_tilde`, with coefficients in `F[X]`. -/
noncomputable def H_tilde' (H : F[X][Y]) : F[X][Y] :=
  if H.natDegree = 0 then
    Polynomial.C (H.coeff 0)
  else
    let hᵢ (i : ℕ) := H.coeff i
    let d := H.natDegree
    let W := hᵢ d
    Polynomial.X ^ d +
      ∑ i ∈ Finset.range d,
        Polynomial.C (hᵢ i * W ^ (d - 1 - i)) * Polynomial.X ^ i

omit [IsDomain F] in
/-- If `H` has positive degree in `Y`, then `H_tilde' H` is monic. -/
lemma H_tilde'_monic (H : F[X][Y]) (hH : 0 < H.natDegree) :
    (H_tilde' H).Monic := by
  classical
  have hdeg : H.natDegree ≠ 0 := Nat.ne_of_gt hH
  rw [H_tilde', if_neg hdeg]
  exact Polynomial.monic_X_pow_add <| (Polynomial.degree_sum_le _ _).trans_lt <| by
    exact (Finset.sup_lt_iff (WithBot.bot_lt_coe H.natDegree)).2 <| by
      intro i hi
      exact (Polynomial.degree_C_mul_X_pow_le i _).trans_lt
        (WithBot.coe_lt_coe.2 (Finset.mem_range.mp hi))

private lemma monicize_term {K : Type} [Field K] (a b : K) (i d : ℕ)
    (ha : a ≠ 0) (hi : i < d) :
    (Polynomial.C a ^ (d - 1)) * (Polynomial.C b * (Polynomial.X / Polynomial.C a) ^ i) =
      Polynomial.C (b * a ^ (d - 1 - i)) * Polynomial.X ^ i := by
  rw [Polynomial.div_C, mul_pow]
  rw [show Polynomial.C a ^ (d - 1) = Polynomial.C (a ^ (d - 1)) by rw [Polynomial.C_pow]]
  rw [show Polynomial.C a⁻¹ ^ i = Polynomial.C (a⁻¹ ^ i) by rw [Polynomial.C_pow]]
  have hscalar : a ^ (d - 1) * b * a⁻¹ ^ i = b * a ^ (d - 1 - i) := by
    have hsplit : d - 1 = (d - 1 - i) + i := by omega
    rw [hsplit, pow_add, inv_pow]
    field_simp [ha]
    have hexp : d - 1 - i + i - i = d - 1 - i := by omega
    rw [hexp]
    ring_nf
  have hscalar' : a ^ (d - 1) * (b * a⁻¹ ^ i) = b * a ^ (d - 1 - i) := by
    simpa [mul_assoc] using hscalar
  calc
    Polynomial.C (a ^ (d - 1)) * (Polynomial.C b * (Polynomial.X ^ i * Polynomial.C (a⁻¹ ^ i))) =
        Polynomial.X ^ i * Polynomial.C (a ^ (d - 1) * (b * a⁻¹ ^ i)) := by
          calc
            Polynomial.C (a ^ (d - 1)) *
                (Polynomial.C b * (Polynomial.X ^ i * Polynomial.C (a⁻¹ ^ i))) =
                Polynomial.X ^ i *
                  (Polynomial.C (a ^ (d - 1)) * Polynomial.C b * Polynomial.C (a⁻¹ ^ i)) := by
                    ring
            _ = Polynomial.X ^ i * Polynomial.C (a ^ (d - 1) * (b * a⁻¹ ^ i)) := by
                  rw [← Polynomial.C_mul, ← Polynomial.C_mul]
                  simp [mul_assoc]
    _ = Polynomial.X ^ i * Polynomial.C (b * a ^ (d - 1 - i)) := by rw [hscalar']
    _ = Polynomial.C (b * a ^ (d - 1 - i)) * Polynomial.X ^ i := by rw [mul_comm]

private lemma monicize_leading_term {K : Type} [Field K] (a : K) (d : ℕ)
    (ha : a ≠ 0) (hd : 0 < d) :
    (Polynomial.C a ^ (d - 1)) * (Polynomial.C a * (Polynomial.X / Polynomial.C a) ^ d) =
      Polynomial.X ^ d := by
  rw [Polynomial.div_C, mul_pow]
  rw [show Polynomial.C a ^ (d - 1) = Polynomial.C (a ^ (d - 1)) by rw [Polynomial.C_pow]]
  rw [show Polynomial.C a⁻¹ ^ d = Polynomial.C (a⁻¹ ^ d) by rw [Polynomial.C_pow]]
  have hscalar : a ^ (d - 1) * a * a⁻¹ ^ d = (1 : K) := by
    have hd' : d = (d - 1) + 1 := by omega
    rw [hd', pow_add, pow_one, inv_pow]
    field_simp [ha]
    have hexp : d - 1 + 1 - 1 = d - 1 := by omega
    rw [hexp]
  have hscalar' : a ^ (d - 1) * (a * a⁻¹ ^ d) = (1 : K) := by
    simpa [mul_assoc] using hscalar
  calc
    Polynomial.C (a ^ (d - 1)) * (Polynomial.C a * (Polynomial.X ^ d * Polynomial.C (a⁻¹ ^ d))) =
        Polynomial.X ^ d * Polynomial.C (a ^ (d - 1) * (a * a⁻¹ ^ d)) := by
          calc
            Polynomial.C (a ^ (d - 1)) *
                (Polynomial.C a * (Polynomial.X ^ d * Polynomial.C (a⁻¹ ^ d))) =
                Polynomial.X ^ d *
                  (Polynomial.C (a ^ (d - 1)) * Polynomial.C a * Polynomial.C (a⁻¹ ^ d)) := by
                    ring
            _ = Polynomial.X ^ d * Polynomial.C (a ^ (d - 1) * (a * a⁻¹ ^ d)) := by
                  rw [← Polynomial.C_mul, ← Polynomial.C_mul]
                  simp [mul_assoc]
    _ = Polynomial.X ^ d * Polynomial.C (1 : K) := by rw [hscalar']
    _ = Polynomial.X ^ d := by simp

/-- The polynomial `H_tilde'` agrees with the monicization `H_tilde` after embedding into
`Polynomial (RatFunc F)`. -/
lemma map_H_tilde'_eq_H_tilde (H : F[X][Y]) : (H_tilde' H).map univPolyHom = H_tilde H := by
  classical
  by_cases hdeg : H.natDegree = 0
  · simp only [H_tilde', hdeg, ↓reduceIte, map_C]
    have hconst : H = Polynomial.C (H.coeff 0) := Polynomial.eq_C_of_natDegree_le_zero (by omega)
    rw [hconst, H_tilde]
    simp
  · have hH_ne : H ≠ 0 := by
      intro hzero
      apply hdeg
      simp [hzero]
    have hw_ne_zero : univPolyHom H.leadingCoeff ≠ 0 := by
      apply IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors
      rw [mem_nonZeroDivisors_iff_ne_zero]
      exact Polynomial.leadingCoeff_ne_zero.mpr hH_ne
    have hd : 0 < H.natDegree := Nat.pos_of_ne_zero hdeg
    have hEval :
        Polynomial.eval₂ (RingHom.comp Polynomial.C univPolyHom)
          (Polynomial.X /
            (RingHom.comp Polynomial.C univPolyHom) ((fun i => H.coeff i) H.natDegree)) H =
        ∑ i ∈ Finset.range (H.natDegree + 1),
          Polynomial.C (univPolyHom (H.coeff i)) *
            (Polynomial.X /
              (RingHom.comp Polynomial.C univPolyHom) ((fun i => H.coeff i) H.natDegree)) ^ i := by
      simpa using
        (Polynomial.eval₂_eq_sum_range
          (p := H) (f := RingHom.comp Polynomial.C univPolyHom)
          (x := Polynomial.X /
            (RingHom.comp Polynomial.C univPolyHom) ((fun i => H.coeff i) H.natDegree)))
    simp only [H_tilde', hdeg, ↓reduceIte, coeff_natDegree, map_mul, map_pow,
      Polynomial.map_add, Polynomial.map_pow, map_X]
    rw [H_tilde, hEval, Finset.sum_range_succ, mul_add, Finset.mul_sum, Polynomial.map_sum]
    have hsum :
        ∑ i ∈ Finset.range H.natDegree,
          ((RingHom.comp Polynomial.C univPolyHom) ((fun i => H.coeff i) H.natDegree) ^
              (H.natDegree - 1)) *
            (Polynomial.C (univPolyHom (H.coeff i)) *
              (Polynomial.X /
                (RingHom.comp Polynomial.C univPolyHom) ((fun i => H.coeff i) H.natDegree)) ^ i) =
        ∑ i ∈ Finset.range H.natDegree,
          Polynomial.map univPolyHom
            (Polynomial.C (H.coeff i) * Polynomial.C H.leadingCoeff ^ (H.natDegree - 1 - i) *
              Polynomial.X ^ i) := by
      refine Finset.sum_congr rfl ?_
      intro i hi
      simpa [Polynomial.coeff_natDegree, map_mul, map_pow] using
        monicize_term (univPolyHom H.leadingCoeff) (univPolyHom (H.coeff i)) i H.natDegree
          hw_ne_zero (Finset.mem_range.mp hi)
    have hlead :
        ((RingHom.comp Polynomial.C univPolyHom) ((fun i => H.coeff i) H.natDegree) ^
            (H.natDegree - 1)) *
          (Polynomial.C (univPolyHom (H.coeff H.natDegree)) *
            (Polynomial.X /
              (RingHom.comp Polynomial.C univPolyHom) ((fun i => H.coeff i) H.natDegree)) ^
              H.natDegree) =
        Polynomial.X ^ H.natDegree := by
      simpa [Polynomial.coeff_natDegree] using
        monicize_leading_term (univPolyHom H.leadingCoeff) H.natDegree hw_ne_zero hd
    rw [hlead]
    calc
      Polynomial.X ^ H.natDegree +
          ∑ i ∈ Finset.range H.natDegree,
            Polynomial.map univPolyHom
              (Polynomial.C (H.coeff i) * Polynomial.C H.leadingCoeff ^ (H.natDegree - 1 - i) *
                Polynomial.X ^ i) =
          Polynomial.X ^ H.natDegree +
            ∑ i ∈ Finset.range H.natDegree,
              (RingHom.comp Polynomial.C univPolyHom) ((fun i => H.coeff i) H.natDegree) ^
                  (H.natDegree - 1) *
                (Polynomial.C (univPolyHom (H.coeff i)) *
                  (Polynomial.X /
                    (RingHom.comp Polynomial.C univPolyHom) ((fun i => H.coeff i) H.natDegree)) ^
                    i) := by
              exact congrArg (fun p => Polynomial.X ^ H.natDegree + p) hsum.symm
      _ =
          ∑ i ∈ Finset.range H.natDegree,
            (RingHom.comp Polynomial.C univPolyHom) ((fun i => H.coeff i) H.natDegree) ^
                (H.natDegree - 1) *
              (Polynomial.C (univPolyHom (H.coeff i)) *
                (Polynomial.X /
                  (RingHom.comp Polynomial.C univPolyHom) ((fun i => H.coeff i) H.natDegree)) ^
                  i) +
            Polynomial.X ^ H.natDegree := by
              rw [add_comm]

section IntegralIrreducibility

variable {F : Type} [Field F]

/-- The integral monicized polynomial `H_tilde'` is irreducible whenever `H` is irreducible and has
positive degree in `Y`. -/
lemma irreducibleHTilde'OfIrreducible {H : F[X][Y]} (hHdeg : 0 < H.natDegree)
    (hH : Irreducible H) :
    Irreducible (H_tilde' H) := by
  have hmap : Irreducible ((H_tilde' H).map (univPolyHom (F := F))) := by
    simpa [map_H_tilde'_eq_H_tilde] using
      irreducibleHTildeOfIrreducible_of_natDegree_pos hHdeg hH
  exact (H_tilde'_monic H hHdeg).isPrimitive.irreducible_of_irreducible_map_of_injective
    (univPolyHom_injective (F := F)) hmap

end IntegralIrreducibility

/-- The ring of regular elements `𝒪` from Appendix A.1 of [BCIKS20]. -/
abbrev 𝒪 (H : F[X][Y]) : Type :=
  (Polynomial (Polynomial F)) ⧸ (Ideal.span {H_tilde' H})

/-- The ring of regular elements `𝒪` is a ring. -/
noncomputable instance {H : F[X][Y]} : Ring (𝒪 H) :=
  Ideal.Quotient.ring (Ideal.span {H_tilde' H})

/-- The ring homomorphism defining the embedding of `𝒪` into `𝕃`. -/
noncomputable def embeddingOf𝒪Into𝕃 (H : F[X][Y]) : 𝒪 H →+* 𝕃 H :=
  Ideal.quotientMap
    (I := Ideal.span {H_tilde' H}) (Ideal.span {H_tilde H})
    bivPolyHom (by
      rw [Ideal.span_le]
      intro x hx
      rw [Set.mem_singleton_iff] at hx
      subst hx
      change bivPolyHom (H_tilde' H) ∈ span {H_tilde H}
      rw [show bivPolyHom (H_tilde' H) = (H_tilde' H).map univPolyHom from rfl,
        map_H_tilde'_eq_H_tilde]
      exact Ideal.subset_span rfl)

section FieldEmbedding

variable {F : Type} [Field F]

private lemma H_tilde'_dvd_of_map_dvd_H_tilde {H p : F[X][Y]} (hHdeg : 0 < H.natDegree)
    (hp : H_tilde H ∣ p.map (univPolyHom (F := F))) :
    H_tilde' H ∣ p := by
  let q : F[X][Y] := H_tilde' H
  have hqmonic : q.Monic := H_tilde'_monic H hHdeg
  rw [← Polynomial.modByMonic_eq_zero_iff_dvd hqmonic]
  rw [← Polynomial.map_eq_zero_iff (univPolyHom_injective (F := F))]
  have hqmap_dvd_p : q.map (univPolyHom (F := F)) ∣ p.map (univPolyHom (F := F)) := by
    simpa [q, map_H_tilde'_eq_H_tilde] using hp
  have hqmap_dvd_rem :
      q.map (univPolyHom (F := F)) ∣
        (p %ₘ q).map (univPolyHom (F := F)) := by
    have hrem :
        (p %ₘ q).map (univPolyHom (F := F)) =
          p.map (univPolyHom (F := F)) -
            q.map (univPolyHom (F := F)) * (p /ₘ q).map (univPolyHom (F := F)) := by
      have h := congrArg (fun r : F[X][Y] => r.map (univPolyHom (F := F)))
        (Polynomial.modByMonic_add_div p q)
      simp only [Polynomial.map_add, Polynomial.map_mul] at h
      rw [← h]
      ring
    rw [hrem]
    exact dvd_sub hqmap_dvd_p (dvd_mul_right _ _)
  have hdegree :
      ((p %ₘ q).map (univPolyHom (F := F))).degree <
        (q.map (univPolyHom (F := F))).degree := by
    rw [Polynomial.degree_map_eq_of_injective (univPolyHom_injective (F := F))]
    rw [Polynomial.degree_map_eq_of_injective (univPolyHom_injective (F := F))]
    exact Polynomial.degree_modByMonic_lt p hqmonic
  exact Polynomial.eq_zero_of_dvd_of_degree_lt hqmap_dvd_rem hdegree

private lemma mem_span_H_tilde'_of_bivPolyHom_mem_span_H_tilde {H p : F[X][Y]}
    (hHdeg : 0 < H.natDegree)
    (hp : bivPolyHom p ∈ Ideal.span {H_tilde H}) :
    p ∈ Ideal.span {H_tilde' H} := by
  rw [Ideal.mem_span_singleton] at hp ⊢
  exact H_tilde'_dvd_of_map_dvd_H_tilde hHdeg (by
    simpa [show bivPolyHom p = p.map (univPolyHom (F := F)) from rfl] using hp)

/-- The regular quotient embeds injectively into the function-field quotient when `H` has positive
degree in `Y`. -/
lemma embeddingOf𝒪Into𝕃_injective {H : F[X][Y]} (hHdeg : 0 < H.natDegree) :
    Function.Injective (embeddingOf𝒪Into𝕃 H) := by
  unfold embeddingOf𝒪Into𝕃
  apply Ideal.quotientMap_injective'
  intro p hp
  exact mem_span_H_tilde'_of_bivPolyHom_mem_span_H_tilde hHdeg hp

end FieldEmbedding

/-- The set of regular elements inside `𝕃 H`, i.e. the set of elements of `𝕃 H`
that in fact lie in `𝒪 H`. -/
def regularElementsSet (H : F[X][Y]) : Set (𝕃 H) :=
  {a : 𝕃 H | ∃ b : 𝒪 H, a = embeddingOf𝒪Into𝕃 _ b}

/-- The regular elements inside `𝕃 H`, i.e. the elements of `𝕃 H` that in fact lie in `𝒪 H`
as Type. -/
def regularElements (H : F[X][Y]) : Type :=
  {a : 𝕃 H // ∃ b : 𝒪 H, a = embeddingOf𝒪Into𝕃 _ b}

/-- Zero is regular. -/
@[simp]
lemma regularElementsSet_zero (H : F[X][Y]) : (0 : 𝕃 H) ∈ regularElementsSet H :=
  ⟨0, by simp⟩

/-- One is regular. -/
@[simp]
lemma regularElementsSet_one (H : F[X][Y]) : (1 : 𝕃 H) ∈ regularElementsSet H :=
  ⟨1, by simp⟩

/-- The regular elements are closed under addition. -/
lemma regularElementsSet_add {H : F[X][Y]} {a b : 𝕃 H}
    (ha : a ∈ regularElementsSet H) (hb : b ∈ regularElementsSet H) :
    a + b ∈ regularElementsSet H := by
  rcases ha with ⟨a', rfl⟩
  rcases hb with ⟨b', rfl⟩
  exact ⟨a' + b', by simp⟩

/-- The regular elements are closed under negation. -/
lemma regularElementsSet_neg {H : F[X][Y]} {a : 𝕃 H}
    (ha : a ∈ regularElementsSet H) : -a ∈ regularElementsSet H := by
  rcases ha with ⟨a', rfl⟩
  exact ⟨-a', by simp⟩

/-- The regular elements are closed under subtraction. -/
lemma regularElementsSet_sub {H : F[X][Y]} {a b : 𝕃 H}
    (ha : a ∈ regularElementsSet H) (hb : b ∈ regularElementsSet H) :
    a - b ∈ regularElementsSet H := by
  simpa [sub_eq_add_neg] using regularElementsSet_add ha (regularElementsSet_neg hb)

/-- The regular elements are closed under multiplication. -/
lemma regularElementsSet_mul {H : F[X][Y]} {a b : 𝕃 H}
    (ha : a ∈ regularElementsSet H) (hb : b ∈ regularElementsSet H) :
    a * b ∈ regularElementsSet H := by
  rcases ha with ⟨a', rfl⟩
  rcases hb with ⟨b', rfl⟩
  exact ⟨a' * b', by simp⟩

/-- The regular elements are closed under natural powers. -/
lemma regularElementsSet_pow {H : F[X][Y]} {a : 𝕃 H}
    (ha : a ∈ regularElementsSet H) (n : ℕ) : a ^ n ∈ regularElementsSet H := by
  induction n with
  | zero => simp
  | succ n ih =>
      simpa [pow_succ] using regularElementsSet_mul ih ha

/-- The regular elements are closed under finite sums. -/
lemma regularElementsSet_sum {ι : Type} {H : F[X][Y]} (s : Finset ι) {f : ι → 𝕃 H}
    (hf : ∀ i ∈ s, f i ∈ regularElementsSet H) :
    (∑ i ∈ s, f i) ∈ regularElementsSet H := by
  classical
  revert hf
  refine Finset.induction_on s ?_ ?_
  · intro _hf
    simp
  · intro a s ha ih hf
    rw [Finset.sum_insert ha]
    exact regularElementsSet_add
      (hf a (by simp [ha]))
      (ih fun i hi => hf i (by simp [hi]))

/-- Given an element `z ∈ F`, `t_z ∈ F` is a rational root of a bivariate polynomial if the pair
`(z, t_z)` is a root of the bivariate polynomial. -/
def rationalRoot (H : F[X][Y]) (z : F) : Type :=
  {t_z : F // evalEval z t_z H = 0}

/-- The rational substitution `π_z` from Appendix A.3 defined on the whole ring of
bivariate polynomials. -/
noncomputable def π_z_lift {H : F[X][Y]} (z : F) (root : rationalRoot (H_tilde' H) z) :
    F[X][Y] →+* F :=
  Polynomial.evalEvalRingHom z root.1

/-- The rational substitution `π_z` from Appendix A.3 of [BCIKS20] is a well-defined map on the
quotient ring `𝒪`. -/
noncomputable def π_z {H : F[X][Y]} (z : F) (root : rationalRoot (H_tilde' H) z) :
    𝒪 H →+* F :=
  Ideal.Quotient.lift (Ideal.span {H_tilde' H}) (π_z_lift z root) (by
    intro a ha
    rw [Ideal.mem_span_singleton] at ha
    obtain ⟨c, rfl⟩ := ha
    simp only [π_z_lift, map_mul]
    rw [show (Polynomial.evalEvalRingHom z root.1) (H_tilde' H) = 0 from root.2]
    ring)

/-- The canonical representative of an element of `F[X][Y]` inside the ring of regular elements
`𝒪`, defined when `H` has positive degree in `Y`. -/
noncomputable def canonicalRepOf𝒪 {H : F[X][Y]} (hH : 0 < H.natDegree) (β : 𝒪 H) : F[X][Y] :=
  let _hHt := H_tilde'_monic H hH
  Polynomial.modByMonic β.out (H_tilde' H)

/-- The canonical representative has degree strictly smaller than the defining relation. -/
lemma canonicalRepOf𝒪_degree_lt {H : F[X][Y]} (hH : 0 < H.natDegree) (β : 𝒪 H) :
    (canonicalRepOf𝒪 hH β).degree < (H_tilde' H).degree := by
  rw [canonicalRepOf𝒪]
  exact Polynomial.degree_modByMonic_lt _ (H_tilde'_monic H hH)

omit [IsDomain F] in
/-- The canonical representative has natural degree bounded by the defining relation. -/
lemma canonicalRepOf𝒪_natDegree_le {H : F[X][Y]} (hH : 0 < H.natDegree) (β : 𝒪 H) :
    (canonicalRepOf𝒪 hH β).natDegree ≤ (H_tilde' H).natDegree := by
  rw [canonicalRepOf𝒪]
  exact Polynomial.natDegree_modByMonic_le _ (H_tilde'_monic H hH)

omit [IsDomain F] in
/-- The canonical representative maps back to the original quotient element of `𝒪`. -/
@[simp]
lemma mk_canonicalRepOf𝒪 {H : F[X][Y]} (hH : 0 < H.natDegree) (β : 𝒪 H) :
    Ideal.Quotient.mk (Ideal.span {H_tilde' H}) (canonicalRepOf𝒪 hH β) = β := by
  let I : Ideal F[X][Y] := Ideal.span {H_tilde' H}
  let q : F[X][Y] := H_tilde' H
  let p : F[X][Y] := β.out
  have hq_zero : Ideal.Quotient.mk I (q * (p /ₘ q)) = 0 := by
    rw [Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)
  calc
    Ideal.Quotient.mk (Ideal.span {H_tilde' H}) (canonicalRepOf𝒪 hH β)
        = Ideal.Quotient.mk I (p %ₘ q) := by
            simp [canonicalRepOf𝒪, I, q, p]
    _ = Ideal.Quotient.mk I (p %ₘ q) + Ideal.Quotient.mk I (q * (p /ₘ q)) := by
            simp [hq_zero]
    _ = Ideal.Quotient.mk I (p %ₘ q + q * (p /ₘ q)) := by
            rw [map_add]
    _ = Ideal.Quotient.mk I p := by
            rw [Polynomial.modByMonic_add_div]
    _ = β := by
            simp [I, p]

omit [IsDomain F] in
/-- Canonical representatives of quotient constructors are computed by `modByMonic`. -/
lemma canonicalRepOf𝒪_mk {H : F[X][Y]} (hH : 0 < H.natDegree) (p : F[X][Y]) :
    canonicalRepOf𝒪 hH (Ideal.Quotient.mk (Ideal.span {H_tilde' H}) p : 𝒪 H) =
      p %ₘ H_tilde' H := by
  apply Polynomial.modByMonic_eq_of_dvd_sub (H_tilde'_monic H hH)
  rw [← Ideal.mem_span_singleton]
  rw [← Ideal.Quotient.mk_eq_mk_iff_sub_mem]
  calc
    Ideal.Quotient.mk (Ideal.span {H_tilde' H})
        ((Ideal.Quotient.mk (Ideal.span {H_tilde' H}) p : 𝒪 H).out)
        = (Ideal.Quotient.mk (Ideal.span {H_tilde' H}) p : 𝒪 H) := by simp
    _ = Ideal.Quotient.mk (Ideal.span {H_tilde' H}) p := rfl

omit [IsDomain F] in
/-- The canonical representative of zero is zero. -/
@[simp]
lemma canonicalRepOf𝒪_zero {H : F[X][Y]} (hH : 0 < H.natDegree) :
    canonicalRepOf𝒪 hH (0 : 𝒪 H) = 0 := by
  simpa using (canonicalRepOf𝒪_mk (H := H) hH 0)

/-- A polynomial whose degree is already below the relation is its own canonical representative. -/
lemma canonicalRepOf𝒪_mk_eq_self_of_degree_lt {H : F[X][Y]} (hH : 0 < H.natDegree)
    {p : F[X][Y]} (hp : p.degree < (H_tilde' H).degree) :
    canonicalRepOf𝒪 hH (Ideal.Quotient.mk (Ideal.span {H_tilde' H}) p : 𝒪 H) = p := by
  rw [canonicalRepOf𝒪_mk]
  exact (Polynomial.modByMonic_eq_self_iff (H_tilde'_monic H hH)).2 hp

/-- `Λ` is a weight function on the ring of bivariate polynomials `F[X][Y]`. The weight of
a polynomial is the maximal weight of all monomials appearing in it with non-zero coefficients.
The weight of the zero polynomial is `−∞`.
Requires `D ≥ Bivariate.totalDegree H` to match definition in [BCIKS20]. -/
noncomputable def weight_Λ (f H : F[X][Y]) (D : ℕ) : WithBot ℕ :=
  Finset.sup
    f.support
    (fun deg =>
      WithBot.some <| deg * (D + 1 - Bivariate.natDegreeY H) + (f.coeff deg).natDegree
    )

omit [IsDomain F] in
/-- The zero polynomial has bottom `Λ`-weight. -/
@[simp]
lemma weight_Λ_zero (H : F[X][Y]) (D : ℕ) :
    weight_Λ (0 : F[X][Y]) H D = ⊥ := by
  simp [weight_Λ]

/-- The weight function `Λ` on regular elements is the weight of their canonical representatives
in `F[X][Y]`. -/
noncomputable def weight_Λ_over_𝒪 {H : F[X][Y]} (hH : 0 < H.natDegree) (f : 𝒪 H) (D : ℕ) :
    WithBot ℕ := weight_Λ (canonicalRepOf𝒪 hH f) H D

omit [IsDomain F] in
/-- The `𝒪`-weight of zero is bottom. -/
@[simp]
lemma weight_Λ_over_𝒪_zero {H : F[X][Y]} (hH : 0 < H.natDegree) (D : ℕ) :
    weight_Λ_over_𝒪 hH (0 : 𝒪 H) D = ⊥ := by
  simp [weight_Λ_over_𝒪]

omit [IsDomain F] in
/-- The `𝒪`-weight of a quotient constructor is computed on its canonical remainder. -/
lemma weight_Λ_over_𝒪_mk {H : F[X][Y]} (hH : 0 < H.natDegree) (p : F[X][Y])
    (D : ℕ) :
    weight_Λ_over_𝒪 hH (Ideal.Quotient.mk (Ideal.span {H_tilde' H}) p : 𝒪 H) D =
      weight_Λ (p %ₘ H_tilde' H) H D := by
  simp [weight_Λ_over_𝒪, canonicalRepOf𝒪_mk]

/-- If a representative is already reduced, its `𝒪`-weight is its polynomial `Λ`-weight. -/
lemma weight_Λ_over_𝒪_mk_eq_self_of_degree_lt {H : F[X][Y]} (hH : 0 < H.natDegree)
    {p : F[X][Y]} (hp : p.degree < (H_tilde' H).degree) (D : ℕ) :
    weight_Λ_over_𝒪 hH (Ideal.Quotient.mk (Ideal.span {H_tilde' H}) p : 𝒪 H) D =
      weight_Λ p H D := by
  simp [weight_Λ_over_𝒪, canonicalRepOf𝒪_mk_eq_self_of_degree_lt hH hp]

/-! ### Λ-weight calculus

Algebraic identities for the bivariate `Λ`-weight from Appendix A.2 of [BCIKS20]. The weight
`m := D + 1 − natDegreeY H` is the per-Y-power contribution; constants in `F[X]` contribute their
`natDegree`. -/

omit [IsDomain F] in
/-- A monomial `n` in `f`'s support contributes a lower bound on `Λ(f)`. -/
lemma le_weight_Λ_of_mem_support {f H : F[X][Y]} {D : ℕ} {n : ℕ} (hn : n ∈ f.support) :
    (WithBot.some (n * (D + 1 - Bivariate.natDegreeY H) + (f.coeff n).natDegree) :
      WithBot ℕ) ≤ weight_Λ f H D := by
  classical
  exact Finset.le_sup (f := fun deg =>
    (WithBot.some (deg * (D + 1 - Bivariate.natDegreeY H) + (f.coeff deg).natDegree) :
      WithBot ℕ)) hn

omit [IsDomain F] in
/-- Characterization: `Λ(f) ≤ b` iff every monomial in `f`'s support contributes at most `b`. -/
lemma weight_Λ_le_iff {f H : F[X][Y]} {D b : ℕ} :
    weight_Λ f H D ≤ (WithBot.some b : WithBot ℕ) ↔
      ∀ n ∈ f.support,
        n * (D + 1 - Bivariate.natDegreeY H) + (f.coeff n).natDegree ≤ b := by
  classical
  refine ⟨fun h n hn => ?_, fun h => ?_⟩
  · have := (le_weight_Λ_of_mem_support hn).trans h
    exact_mod_cast this
  · refine Finset.sup_le (fun n hn => ?_)
    exact_mod_cast (h n hn)

omit [IsDomain F] in
/-- `Λ(C c) ≤ c.natDegree`. -/
lemma weight_Λ_C_le (H : F[X][Y]) (D : ℕ) (c : F[X]) :
    weight_Λ (Polynomial.C c) H D ≤ (WithBot.some c.natDegree : WithBot ℕ) := by
  classical
  rw [weight_Λ_le_iff]
  intro n hn
  have : (Polynomial.C c : F[X][Y]).coeff n ≠ 0 := Polynomial.mem_support_iff.mp hn
  have hn0 : n = 0 := by
    by_contra h
    simp [Polynomial.coeff_C, h] at this
  subst hn0
  simp [Polynomial.coeff_C]

omit [IsDomain F] in
/-- `Λ(Y^k) ≤ k · m`. -/
lemma weight_Λ_X_pow_le (H : F[X][Y]) (D k : ℕ) :
    weight_Λ ((Polynomial.X : F[X][Y]) ^ k) H D ≤
      (WithBot.some (k * (D + 1 - Bivariate.natDegreeY H)) : WithBot ℕ) := by
  classical
  rw [weight_Λ_le_iff]
  intro n hn
  have : ((Polynomial.X : F[X][Y]) ^ k).coeff n ≠ 0 := Polynomial.mem_support_iff.mp hn
  have hnk : n = k := by
    by_contra h
    simp [Polynomial.coeff_X_pow, h] at this
  subst hnk
  simp [Polynomial.coeff_X_pow]

omit [IsDomain F] in
/-- `Λ(C c · Y^k) ≤ k · m + c.natDegree`. -/
lemma weight_Λ_C_mul_X_pow_le (H : F[X][Y]) (D : ℕ) (c : F[X]) (k : ℕ) :
    weight_Λ (Polynomial.C c * Polynomial.X ^ k) H D ≤
      (WithBot.some (k * (D + 1 - Bivariate.natDegreeY H) + c.natDegree) : WithBot ℕ) := by
  classical
  rw [weight_Λ_le_iff]
  intro n hn
  have : (Polynomial.C c * Polynomial.X ^ k : F[X][Y]).coeff n ≠ 0 :=
    Polynomial.mem_support_iff.mp hn
  have hnk : n = k := by
    by_contra h
    simp [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, h] at this
  subst hnk
  simp [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]

omit [IsDomain F] in
/-- The `Λ`-weight is invariant under negation. -/
@[simp]
lemma weight_Λ_neg (f H : F[X][Y]) (D : ℕ) : weight_Λ (-f) H D = weight_Λ f H D := by
  classical
  unfold weight_Λ
  rw [Polynomial.support_neg]
  refine Finset.sup_congr rfl (fun n _ => ?_)
  simp [Polynomial.coeff_neg]

omit [IsDomain F] in
/-- `Λ(f + g) ≤ max(Λ(f), Λ(g))`. -/
lemma weight_Λ_add_le (f g H : F[X][Y]) (D : ℕ) :
    weight_Λ (f + g) H D ≤ max (weight_Λ f H D) (weight_Λ g H D) := by
  classical
  refine Finset.sup_le (fun n hn => ?_)
  -- The contribution at `n` to weight_Λ (f + g) is bounded by f's or g's contribution.
  have hcoeff : (f + g).coeff n = f.coeff n + g.coeff n := Polynomial.coeff_add _ _ _
  have hsum_ne : f.coeff n + g.coeff n ≠ 0 := by
    rw [← hcoeff]
    exact Polynomial.mem_support_iff.mp hn
  by_cases hf : f.coeff n = 0
  · -- f.coeff n = 0, so g.coeff n ≠ 0
    have hg : g.coeff n ≠ 0 := by simpa [hf] using hsum_ne
    have hng : n ∈ g.support := Polynomial.mem_support_iff.mpr hg
    have heq : (f + g).coeff n = g.coeff n := by simp [hcoeff, hf]
    change (WithBot.some _ : WithBot ℕ) ≤ _
    rw [heq]
    exact (le_weight_Λ_of_mem_support hng).trans (le_max_right _ _)
  · have hnf : n ∈ f.support := Polynomial.mem_support_iff.mpr hf
    by_cases hg : g.coeff n = 0
    · have heq : (f + g).coeff n = f.coeff n := by simp [hcoeff, hg]
      change (WithBot.some _ : WithBot ℕ) ≤ _
      rw [heq]
      exact (le_weight_Λ_of_mem_support hnf).trans (le_max_left _ _)
    · have hng : n ∈ g.support := Polynomial.mem_support_iff.mpr hg
      have hdeg : ((f + g).coeff n).natDegree ≤
          max (f.coeff n).natDegree (g.coeff n).natDegree := by
        rw [hcoeff]
        exact Polynomial.natDegree_add_le _ _
      rcases le_total (f.coeff n).natDegree (g.coeff n).natDegree with h | h
      · -- bound by g's contribution
        have hbound : ((f + g).coeff n).natDegree ≤ (g.coeff n).natDegree :=
          hdeg.trans_eq (max_eq_right h)
        have hle : n * (D + 1 - Bivariate.natDegreeY H) + ((f + g).coeff n).natDegree ≤
            n * (D + 1 - Bivariate.natDegreeY H) + (g.coeff n).natDegree :=
          Nat.add_le_add_left hbound _
        calc (WithBot.some
                (n * (D + 1 - Bivariate.natDegreeY H) + ((f + g).coeff n).natDegree) :
                WithBot ℕ)
            ≤ WithBot.some (n * (D + 1 - Bivariate.natDegreeY H) + (g.coeff n).natDegree) :=
              by exact_mod_cast hle
          _ ≤ weight_Λ g H D := le_weight_Λ_of_mem_support hng
          _ ≤ max (weight_Λ f H D) (weight_Λ g H D) := le_max_right _ _
      · have hbound : ((f + g).coeff n).natDegree ≤ (f.coeff n).natDegree :=
          hdeg.trans_eq (max_eq_left h)
        have hle : n * (D + 1 - Bivariate.natDegreeY H) + ((f + g).coeff n).natDegree ≤
            n * (D + 1 - Bivariate.natDegreeY H) + (f.coeff n).natDegree :=
          Nat.add_le_add_left hbound _
        calc (WithBot.some
                (n * (D + 1 - Bivariate.natDegreeY H) + ((f + g).coeff n).natDegree) :
                WithBot ℕ)
            ≤ WithBot.some (n * (D + 1 - Bivariate.natDegreeY H) + (f.coeff n).natDegree) :=
              by exact_mod_cast hle
          _ ≤ weight_Λ f H D := le_weight_Λ_of_mem_support hnf
          _ ≤ max (weight_Λ f H D) (weight_Λ g H D) := le_max_left _ _

omit [IsDomain F] in
/-- `Λ(f − g) ≤ max(Λ(f), Λ(g))`. -/
lemma weight_Λ_sub_le (f g H : F[X][Y]) (D : ℕ) :
    weight_Λ (f - g) H D ≤ max (weight_Λ f H D) (weight_Λ g H D) := by
  rw [sub_eq_add_neg]
  exact (weight_Λ_add_le f (-g) H D).trans_eq (by rw [weight_Λ_neg])

omit [IsDomain F] in
/-- `Λ` of a finite sum is bounded by the max of the summands' weights. -/
lemma weight_Λ_sum_le {ι : Type} (s : Finset ι) (f : ι → F[X][Y]) (H : F[X][Y]) (D : ℕ) :
    weight_Λ (∑ i ∈ s, f i) H D ≤ s.sup (fun i => weight_Λ (f i) H D) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sup_insert]
      exact (weight_Λ_add_le _ _ _ _).trans (max_le_max le_rfl ih)

omit [IsDomain F] in
/-- Bound on the `X`-degree of a coefficient of `H` from a `totalDegree` bound. -/
lemma natDegree_coeff_le_of_totalDegree_le (f : F[X][Y]) {D : ℕ}
    (hD : Bivariate.totalDegree f ≤ D) (i : ℕ) :
    (f.coeff i).natDegree ≤ D - i := by
  classical
  by_cases hi : f.coeff i = 0
  · simp [hi]
  · have hi_in : i ∈ f.support := Polynomial.mem_support_iff.mpr hi
    have h1 : (f.coeff i).natDegree + i ≤ Bivariate.totalDegree f :=
      Bivariate.coeff_totalDegree_le f hi_in
    omega

omit [IsDomain F] in
/-- Sub-additivity for `C c · Y^k · f`: given `Λ(f) ≤ b`, multiplying by `C c · Y^k` adds
`k · m + c.natDegree` to the weight. -/
lemma weight_Λ_C_mul_X_pow_mul_le {c : F[X]} {k : ℕ} {f H : F[X][Y]} {D b : ℕ}
    (hf : weight_Λ f H D ≤ (WithBot.some b : WithBot ℕ)) :
    weight_Λ (Polynomial.C c * Polynomial.X ^ k * f) H D ≤
      (WithBot.some (k * (D + 1 - Bivariate.natDegreeY H) + c.natDegree + b) :
        WithBot ℕ) := by
  classical
  rw [weight_Λ_le_iff]
  rw [weight_Λ_le_iff] at hf
  intro n hn
  have hcoeff_ne : (Polynomial.C c * Polynomial.X ^ k * f : F[X][Y]).coeff n ≠ 0 :=
    Polynomial.mem_support_iff.mp hn
  have hcoeff_eq :
      (Polynomial.C c * Polynomial.X ^ k * f : F[X][Y]).coeff n =
        (if k ≤ n then c * f.coeff (n - k) else 0) := by
    rw [show (Polynomial.C c * Polynomial.X ^ k * f : F[X][Y]) =
           Polynomial.C c * (f * Polynomial.X ^ k) by ring]
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_mul_X_pow']
    split <;> simp
  by_cases hkn : k ≤ n
  · rw [hcoeff_eq, if_pos hkn] at hcoeff_ne
    have hf_ne : f.coeff (n - k) ≠ 0 := by
      intro h0
      apply hcoeff_ne
      rw [h0, mul_zero]
    have hn_k_in : n - k ∈ f.support := Polynomial.mem_support_iff.mpr hf_ne
    have hf_bound := hf (n - k) hn_k_in
    rw [hcoeff_eq, if_pos hkn]
    have hdeg : (c * f.coeff (n - k)).natDegree ≤ c.natDegree + (f.coeff (n - k)).natDegree :=
      Polynomial.natDegree_mul_le
    have hsplit : n = k + (n - k) := (Nat.add_sub_cancel' hkn).symm
    have hgoal :
        n * (D + 1 - Bivariate.natDegreeY H) + (c * f.coeff (n - k)).natDegree ≤
          k * (D + 1 - Bivariate.natDegreeY H) + c.natDegree + b := by
      have h1 :
          n * (D + 1 - Bivariate.natDegreeY H) + (c * f.coeff (n - k)).natDegree ≤
            n * (D + 1 - Bivariate.natDegreeY H) +
              (c.natDegree + (f.coeff (n - k)).natDegree) :=
        Nat.add_le_add_left hdeg _
      have h2 :
          n * (D + 1 - Bivariate.natDegreeY H) +
              (c.natDegree + (f.coeff (n - k)).natDegree) =
            k * (D + 1 - Bivariate.natDegreeY H) + c.natDegree +
              ((n - k) * (D + 1 - Bivariate.natDegreeY H) +
                (f.coeff (n - k)).natDegree) := by
        have hnk : k + (n - k) = n := Nat.add_sub_cancel' hkn
        conv_lhs => rw [hsplit, Nat.add_mul]
        rw [show k + (n - k) - k = n - k from by omega]
        ring
      rw [h2] at h1
      exact h1.trans (Nat.add_le_add_left hf_bound _)
    exact hgoal
  · rw [hcoeff_eq, if_neg hkn] at hcoeff_ne
    exact (hcoeff_ne rfl).elim

/-- The `natDegree` of `H_tilde' H` matches that of `H` when `0 < H.natDegree`. -/
lemma natDegree_H_tilde' {H : F[X][Y]} (hH : 0 < H.natDegree) :
    (H_tilde' H).natDegree = H.natDegree := by
  classical
  rw [H_tilde', if_neg (Nat.ne_of_gt hH)]
  have hsum_deg :
      (∑ i ∈ Finset.range H.natDegree,
          Polynomial.C (H.coeff i * H.coeff H.natDegree ^ (H.natDegree - 1 - i)) *
            Polynomial.X ^ i : F[X][Y]).degree < (H.natDegree : WithBot ℕ) :=
    (Polynomial.degree_sum_le _ _).trans_lt <|
      (Finset.sup_lt_iff (WithBot.bot_lt_coe _)).mpr <| by
        intro i hi
        exact (Polynomial.degree_C_mul_X_pow_le i _).trans_lt
          (WithBot.coe_lt_coe.mpr (Finset.mem_range.mp hi))
  rw [show (Polynomial.X ^ H.natDegree +
        ∑ i ∈ Finset.range H.natDegree,
          Polynomial.C (H.coeff i * H.coeff H.natDegree ^ (H.natDegree - 1 - i)) *
            Polynomial.X ^ i : F[X][Y]) =
      (∑ i ∈ Finset.range H.natDegree,
          Polynomial.C (H.coeff i * H.coeff H.natDegree ^ (H.natDegree - 1 - i)) *
            Polynomial.X ^ i) + Polynomial.X ^ H.natDegree by ring]
  have hX_deg : (Polynomial.X ^ H.natDegree : F[X][Y]).degree = (H.natDegree : WithBot ℕ) :=
    Polynomial.degree_X_pow _
  apply Polynomial.natDegree_eq_of_degree_eq_some
  rw [Polynomial.degree_add_eq_right_of_degree_lt (hsum_deg.trans_eq hX_deg.symm), hX_deg]

/-- The canonical representative has `Y`-degree strictly smaller than `H`. -/
lemma canonicalRepOf𝒪_natDegree_lt_H {H : F[X][Y]} (hH : 0 < H.natDegree) (β : 𝒪 H) :
    (canonicalRepOf𝒪 hH β).natDegree < H.natDegree := by
  classical
  by_cases hβ : canonicalRepOf𝒪 hH β = 0
  · simp [hβ, hH]
  · have hdeg := canonicalRepOf𝒪_degree_lt hH β
    have hq_ne : H_tilde' H ≠ 0 := (H_tilde'_monic H hH).ne_zero
    rw [Polynomial.degree_eq_natDegree hβ, Polynomial.degree_eq_natDegree hq_ne] at hdeg
    exact_mod_cast (by simpa [natDegree_H_tilde' hH] using hdeg)

omit [IsDomain F] in
/-- The `Λ`-weight of `H_tilde' H` is bounded by `d_H · m`, where `d_H = H.natDegree`. -/
lemma weight_Λ_H_tilde'_le {H : F[X][Y]} {D : ℕ}
    (hD : Bivariate.totalDegree H ≤ D) (hH : 0 < H.natDegree) :
    weight_Λ (H_tilde' H) H D ≤
      (WithBot.some (H.natDegree * (D + 1 - Bivariate.natDegreeY H)) : WithBot ℕ) := by
  classical
  have hbY : Bivariate.natDegreeY H = H.natDegree := rfl
  have hH_ne : H ≠ 0 := Polynomial.ne_zero_of_natDegree_gt hH
  have hH_in : H.natDegree ∈ H.support :=
    Polynomial.mem_support_iff.mpr (Polynomial.leadingCoeff_ne_zero.mpr hH_ne)
  have hd_le_D : H.natDegree ≤ D := by
    have : (H.coeff H.natDegree).natDegree + H.natDegree ≤ Bivariate.totalDegree H :=
      Bivariate.coeff_totalDegree_le H hH_in
    omega
  rw [H_tilde', if_neg (Nat.ne_of_gt hH)]
  refine (weight_Λ_add_le _ _ _ _).trans ?_
  refine max_le ?_ ?_
  · -- weight_Λ Y^d ≤ d · m
    refine (weight_Λ_X_pow_le H D _).trans ?_
    rw [WithBot.coe_le_coe]
  · -- weight_Λ (∑ ... · Y^i) ≤ d · m
    refine (weight_Λ_sum_le _ _ _ _).trans ?_
    refine Finset.sup_le (fun i hi => ?_)
    have hi_lt : i < H.natDegree := Finset.mem_range.mp hi
    refine (weight_Λ_C_mul_X_pow_le H D _ _).trans ?_
    -- Goal: WithBot.some (i·m + (H.coeff i · W^(d-1-i)).natDegree) ≤ WithBot.some (d·m)
    rw [WithBot.coe_le_coe]
    rw [hbY]
    have hcoeff_natDeg :
        (H.coeff i * H.coeff H.natDegree ^ (H.natDegree - 1 - i)).natDegree ≤
          (D - i) + (H.natDegree - 1 - i) * (D - H.natDegree) := by
      have h1 :
          (H.coeff i * H.coeff H.natDegree ^ (H.natDegree - 1 - i)).natDegree ≤
            (H.coeff i).natDegree +
              (H.coeff H.natDegree ^ (H.natDegree - 1 - i)).natDegree :=
        Polynomial.natDegree_mul_le
      have h2 :
          (H.coeff H.natDegree ^ (H.natDegree - 1 - i)).natDegree ≤
            (H.natDegree - 1 - i) * (H.coeff H.natDegree).natDegree :=
        Polynomial.natDegree_pow_le
      have hi_deg : (H.coeff i).natDegree ≤ D - i :=
        natDegree_coeff_le_of_totalDegree_le H hD i
      have hd_deg : (H.coeff H.natDegree).natDegree ≤ D - H.natDegree :=
        natDegree_coeff_le_of_totalDegree_le H hD H.natDegree
      calc (H.coeff i * H.coeff H.natDegree ^ (H.natDegree - 1 - i)).natDegree
          ≤ (H.coeff i).natDegree +
              (H.coeff H.natDegree ^ (H.natDegree - 1 - i)).natDegree := h1
        _ ≤ (D - i) + (H.natDegree - 1 - i) * (H.coeff H.natDegree).natDegree := by
            exact Nat.add_le_add hi_deg h2
        _ ≤ (D - i) + (H.natDegree - 1 - i) * (D - H.natDegree) :=
            Nat.add_le_add_left (Nat.mul_le_mul_left _ hd_deg) _
    -- numeric bound: i·m + (D-i) + (d-1-i)(D-d) = d·m
    have hadd : i * (D + 1 - H.natDegree) +
        (H.coeff i * H.coeff H.natDegree ^ (H.natDegree - 1 - i)).natDegree ≤
          i * (D + 1 - H.natDegree) +
            ((D - i) + (H.natDegree - 1 - i) * (D - H.natDegree)) :=
      Nat.add_le_add_left hcoeff_natDeg _
    refine hadd.trans ?_
    -- Numeric identity: i*(D+1-d) + (D-i) + (d-1-i)(D-d) = d*(D+1-d)
    have hkey : i * (D + 1 - H.natDegree) +
        ((D - i) + (H.natDegree - 1 - i) * (D - H.natDegree)) =
        H.natDegree * (D + 1 - H.natDegree) := by
      have hi_le : i ≤ H.natDegree - 1 := by omega
      have hi_le_D : i ≤ D := by omega
      have hd_le_D1 : H.natDegree ≤ 1 + D := by omega
      have hd_le_D' : H.natDegree ≤ D + 1 := by omega
      zify [hd_le_D, hd_le_D', hi_le, hi_le_D, hH]
      ring
    omega

omit [IsDomain F] in
/-- One reduction step in `modByMonic` does not increase `Λ`-weight: subtracting
`C(p.leadingCoeff) · Y^(p.natDegree - d_H) · H_tilde' H` from `p` keeps the weight bounded by
`Λ(p)`. -/
lemma weight_Λ_sub_leadingCoeff_mul_H_tilde'_le {p H : F[X][Y]} {D : ℕ}
    (hD : Bivariate.totalDegree H ≤ D) (hH : 0 < H.natDegree)
    (hp_deg : H.natDegree ≤ p.natDegree) :
    weight_Λ (p - Polynomial.C p.leadingCoeff *
        Polynomial.X ^ (p.natDegree - H.natDegree) * H_tilde' H) H D ≤
      weight_Λ p H D := by
  classical
  refine (weight_Λ_sub_le _ _ _ _).trans ?_
  refine max_le le_rfl ?_
  refine (weight_Λ_C_mul_X_pow_mul_le (weight_Λ_H_tilde'_le hD hH)).trans ?_
  by_cases hp : p = 0
  · subst hp
    simp at hp_deg
    omega
  · have hp_lead_ne : p.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hp
    have hp_in : p.natDegree ∈ p.support := Polynomial.mem_support_iff.mpr hp_lead_ne
    refine le_trans ?_ (le_weight_Λ_of_mem_support hp_in)
    rw [WithBot.coe_le_coe]
    change (p.natDegree - H.natDegree) * (D + 1 - Bivariate.natDegreeY H) +
        (p.coeff p.natDegree).natDegree + H.natDegree * (D + 1 - Bivariate.natDegreeY H) ≤
        p.natDegree * (D + 1 - Bivariate.natDegreeY H) + (p.coeff p.natDegree).natDegree
    have hsum : (p.natDegree - H.natDegree) + H.natDegree = p.natDegree := by omega
    have hadd_mul :
        (p.natDegree - H.natDegree) * (D + 1 - Bivariate.natDegreeY H) +
            H.natDegree * (D + 1 - Bivariate.natDegreeY H) =
          p.natDegree * (D + 1 - Bivariate.natDegreeY H) := by
      rw [← Nat.add_mul, hsum]
    linarith [hadd_mul]

/-- Reduction modulo `H_tilde' H` does not increase `Λ`-weight. -/
lemma weight_Λ_modByMonic_H_tilde'_le {H : F[X][Y]} {D : ℕ}
    (hD : Bivariate.totalDegree H ≤ D) (hH : 0 < H.natDegree) :
    ∀ p : F[X][Y], weight_Λ (p %ₘ H_tilde' H) H D ≤ weight_Λ p H D
  | p => by
      classical
      have hq : (H_tilde' H).Monic := H_tilde'_monic H hH
      unfold Polynomial.modByMonic Polynomial.divModByMonicAux
      rw [dif_pos hq]
      by_cases h : (H_tilde' H).degree ≤ p.degree ∧ p ≠ 0
      · have _wf := Polynomial.div_wf_lemma h hq
        simp only [ne_eq, dite_eq_ite, ge_iff_le, p, h]
        let z := Polynomial.C p.leadingCoeff *
          Polynomial.X ^ (p.natDegree - (H_tilde' H).natDegree)
        have ih := weight_Λ_modByMonic_H_tilde'_le hD hH (p - H_tilde' H * z)
        have ih' :
            weight_Λ ((Polynomial.divModByMonicAux (p - H_tilde' H * z) hq).2) H D ≤
              weight_Λ (p - H_tilde' H * z) H D := by
          simpa [Polynomial.modByMonic, hq, z] using ih
        have hqnat : (H_tilde' H).natDegree = H.natDegree := natDegree_H_tilde' hH
        have hp_deg : H.natDegree ≤ p.natDegree := by
          have hdeg := h.1
          rw [Polynomial.degree_eq_natDegree h.2, Polynomial.degree_eq_natDegree hq.ne_zero]
            at hdeg
          exact_mod_cast (by simpa [hqnat] using hdeg)
        have hstep0 :=
          weight_Λ_sub_leadingCoeff_mul_H_tilde'_le (p := p) (H := H) hD hH hp_deg
        have hstep : weight_Λ (p - H_tilde' H * z) H D ≤ weight_Λ p H D := by
          have hz :
              z = Polynomial.C p.leadingCoeff * Polynomial.X ^ (p.natDegree - H.natDegree) := by
            simp [z, hqnat]
          rw [hz]
          convert hstep0 using 1
          ring_nf
        exact ih'.trans hstep
      · simp only [ne_eq, dite_eq_ite, ge_iff_le, p, h]
        exact le_rfl
termination_by p => p

/-- The `𝒪`-weight of a quotient constructor is bounded by any representative's `Λ`-weight. -/
lemma weight_Λ_over_𝒪_mk_le {H : F[X][Y]} {D : ℕ}
    (hD : Bivariate.totalDegree H ≤ D) (hH : 0 < H.natDegree) (p : F[X][Y]) :
    weight_Λ_over_𝒪 hH (Ideal.Quotient.mk (Ideal.span {H_tilde' H}) p : 𝒪 H) D ≤
      weight_Λ p H D := by
  rw [weight_Λ_over_𝒪_mk]
  exact weight_Λ_modByMonic_H_tilde'_le hD hH p

/-- The set `S_β` from the statement of Lemma A.1 in Appendix A of [BCIKS20].
Note: Here `F[X][Y]` is `F[Z][T]`. -/
noncomputable def S_β {H : F[X][Y]} (β : 𝒪 H) : Set F :=
  {z : F | ∃ root : rationalRoot (H_tilde' H) z, (π_z z root) β = 0}

omit [IsDomain F] in
/-- The rational substitution `π_z` can be computed on the canonical representative. -/
lemma π_z_eq_eval_canonicalRepOf𝒪 {H : F[X][Y]} (hH : 0 < H.natDegree)
    (z : F) (root : rationalRoot (H_tilde' H) z) (β : 𝒪 H) :
    (π_z z root) β = Polynomial.evalEvalRingHom z root.1 (canonicalRepOf𝒪 hH β) := by
  conv_lhs => rw [← mk_canonicalRepOf𝒪 hH β]
  rfl

end

section LemmaA1

variable {F : Type} [Field F]

theorem H_tilde_prime_coeff_natDegree_le_of_totalDegree {H : F[X][Y]} {D : ℕ} (hD : Bivariate.totalDegree H ≤ D)
    (hH : 0 < H.natDegree) {j : ℕ}
    (hj : j ∈ (H_tilde' H).support) :
  j * (D + 1 - Bivariate.natDegreeY H) +
    ((H_tilde' H).coeff j).natDegree ≤
      H.natDegree * (D + 1 - Bivariate.natDegreeY H) := by
  exact (weight_Λ_le_iff.mp (weight_Λ_H_tilde'_le hD hH)) j hj

theorem canonicalRep_coeff_natDegree_le_of_weight_bound {H : F[X][Y]} (hH : 0 < H.natDegree) {D B : ℕ} (β : 𝒪 H)
    (hβw : weight_Λ_over_𝒪 hH β D ≤ (WithBot.some B : WithBot ℕ))
    {i : ℕ} (hi : i ∈ (canonicalRepOf𝒪 hH β).support) :
  i * (D + 1 - Bivariate.natDegreeY H) +
    ((canonicalRepOf𝒪 hH β).coeff i).natDegree ≤ B := by
  unfold weight_Λ_over_𝒪 at hβw
  exact (weight_Λ_le_iff.mp hβw) i hi

theorem embedding_eq_zero_of_resultant_zero {H : F[X][Y]} [Fact (Irreducible H)] (hH : 0 < H.natDegree) (β : 𝒪 H)
    (hres : Polynomial.resultant (canonicalRepOf𝒪 hH β) (H_tilde' H) = 0) :
  embeddingOf𝒪Into𝕃 H β = 0 := by
  classical
  let p : F[X][Y] := canonicalRepOf𝒪 hH β
  have hres_map : Polynomial.resultant (p.map (univPolyHom (F := F))) (H_tilde H) = 0 := by
    have h := congrArg (univPolyHom (F := F)) hres
    rw [← Polynomial.resultant_map_map (p) (H_tilde' H) p.natDegree (H_tilde' H).natDegree (univPolyHom (F := F))] at h
    rw [map_H_tilde'_eq_H_tilde H] at h
    have hn : (H_tilde H).natDegree = (H_tilde' H).natDegree := by
      rw [← map_H_tilde'_eq_H_tilde H]
      exact Polynomial.natDegree_map_eq_of_injective (univPolyHom_injective (F := F)) (H_tilde' H)
    simpa only [p, Polynomial.natDegree_map_eq_of_injective (univPolyHom_injective (F := F)), map_zero, hn] using h
  have hnot_coprime : ¬ IsCoprime (p.map (univPolyHom (F := F))) (H_tilde H) := by
    exact (Polynomial.resultant_eq_zero_iff.mp hres_map).2
  have hHT_irred : Irreducible (H_tilde H) :=
    irreducibleHTildeOfIrreducible_of_natDegree_pos hH (Fact.out)
  have hdvd_map : H_tilde H ∣ p.map (univPolyHom (F := F)) := by
    exact (Irreducible.dvd_iff_not_isCoprime hHT_irred).2 (by
      intro hc
      exact hnot_coprime hc.symm)
  have hdvd : H_tilde' H ∣ p := H_tilde'_dvd_of_map_dvd_H_tilde hH hdvd_map
  have hp_zero : p = 0 := by
    by_contra hp_ne
    have hdegp : p.natDegree < (H_tilde' H).natDegree := by
      simpa only [p, natDegree_H_tilde' hH] using canonicalRepOf𝒪_natDegree_lt_H hH β
    exact (Polynomial.not_dvd_of_natDegree_lt (p := H_tilde' H) (q := p) hp_ne hdegp) hdvd
  rw [← mk_canonicalRepOf𝒪 hH β]
  change embeddingOf𝒪Into𝕃 H (Ideal.Quotient.mk (Ideal.span {H_tilde' H}) p : 𝒪 H) = 0
  rw [hp_zero]
  simp

theorem natDegree_det_le_of_perm_products_le {ι : Type} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι F[X]) {N : ℕ}
    (h : ∀ σ : Equiv.Perm ι, (∏ i : ι, M (σ i) i).natDegree ≤ N) :
  M.det.natDegree ≤ N := by
  classical
  rw [Matrix.det_apply']
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro σ hσ
  exact le_trans (Polynomial.natDegree_C_mul_le ((Equiv.Perm.sign σ : ℤ) : F) (∏ i : ι, M (σ i) i)) (h σ)

theorem natDegree_resultant_le_weight_bound {H : F[X][Y]} (hH : 0 < H.natDegree) {D B : ℕ}
    (hD : Bivariate.totalDegree H ≤ D) (β : 𝒪 H)
    (hβw : weight_Λ_over_𝒪 hH β D ≤ (WithBot.some B : WithBot ℕ)) :
  (Polynomial.resultant (canonicalRepOf𝒪 hH β) (H_tilde' H)).natDegree ≤ B * H.natDegree := by
  classical
  set p : F[X][Y] := canonicalRepOf𝒪 hH β
  set q : F[X][Y] := H_tilde' H
  set e : ℕ := p.natDegree
  set d : ℕ := H.natDegree
  set lam : ℕ := D + 1 - Bivariate.natDegreeY H
  have hqdeg : q.natDegree = d := by
    simpa [q, d] using natDegree_H_tilde' (H := H) hH
  let M : Matrix (Fin (e + d)) (Fin (e + d)) F[X] := Polynomial.sylvester p q e d
  rw [Polynomial.resultant]
  rw [hqdeg]
  change M.det.natDegree ≤ B * H.natDegree
  rw [show H.natDegree = d by rfl]
  apply natDegree_det_le_of_perm_products_le (M := M)
  intro σ
  by_cases hzero : ∃ i : Fin (e + d), M (σ i) i = 0
  · rcases hzero with ⟨i, hi⟩
    have hprod : (∏ i : Fin (e + d), M (σ i) i) = 0 := by
      exact Finset.prod_eq_zero (s := Finset.univ) (by simp) hi
    rw [hprod]
    simp
  · have hne (i : Fin (e + d)) : M (σ i) i ≠ 0 := by
      intro hi
      exact hzero ⟨i, hi⟩
    let lidx : Fin e → ℕ := fun j => ((σ (Fin.castAdd d j) : Fin (e + d)) : ℕ) - (j : ℕ)
    let ridx : Fin d → ℕ := fun j => ((σ (Fin.natAdd e j) : Fin (e + d)) : ℕ) - (j : ℕ)
    let ldeg : Fin e → ℕ := fun j => (M (σ (Fin.castAdd d j)) (Fin.castAdd d j)).natDegree
    let rdeg : Fin d → ℕ := fun j => (M (σ (Fin.natAdd e j)) (Fin.natAdd e j)).natDegree
    have hleft_Icc (j : Fin e) :
        ((σ (Fin.castAdd d j) : Fin (e + d)) : ℕ) ∈ Set.Icc (j : ℕ) ((j : ℕ) + d) := by
      have hentry : M (σ (Fin.castAdd d j)) (Fin.castAdd d j) =
          if ((σ (Fin.castAdd d j) : Fin (e + d)) : ℕ) ∈ Set.Icc (j : ℕ) ((j : ℕ) + d) then
            q.coeff (((σ (Fin.castAdd d j) : Fin (e + d)) : ℕ) - (j : ℕ))
          else 0 := by
        simp [M, Polynomial.sylvester]
      by_contra hc
      have hentry_zero : M (σ (Fin.castAdd d j)) (Fin.castAdd d j) = 0 := by
        simpa [hentry, hc]
      exact hne (Fin.castAdd d j) hentry_zero
    have hright_Icc (j : Fin d) :
        ((σ (Fin.natAdd e j) : Fin (e + d)) : ℕ) ∈ Set.Icc (j : ℕ) ((j : ℕ) + e) := by
      have hentry : M (σ (Fin.natAdd e j)) (Fin.natAdd e j) =
          if ((σ (Fin.natAdd e j) : Fin (e + d)) : ℕ) ∈ Set.Icc (j : ℕ) ((j : ℕ) + e) then
            p.coeff (((σ (Fin.natAdd e j) : Fin (e + d)) : ℕ) - (j : ℕ))
          else 0 := by
        simp [M, Polynomial.sylvester]
      by_contra hc
      have hentry_zero : M (σ (Fin.natAdd e j)) (Fin.natAdd e j) = 0 := by
        simpa [hentry, hc]
      exact hne (Fin.natAdd e j) hentry_zero
    have hleft (j : Fin e) : lidx j * lam + ldeg j ≤ d * lam := by
      dsimp [lidx, ldeg]
      have hentry : M (σ (Fin.castAdd d j)) (Fin.castAdd d j) =
          if ((σ (Fin.castAdd d j) : Fin (e + d)) : ℕ) ∈ Set.Icc (j : ℕ) ((j : ℕ) + d) then
            q.coeff (((σ (Fin.castAdd d j) : Fin (e + d)) : ℕ) - (j : ℕ))
          else 0 := by
        simp [M, Polynomial.sylvester]
      have hc := hleft_Icc j
      have hcoeff_ne : q.coeff (((σ (Fin.castAdd d j) : Fin (e + d)) : ℕ) - (j : ℕ)) ≠ 0 := by
        have hne' := hne (Fin.castAdd d j)
        rwa [hentry, if_pos hc] at hne'
      have hsup : (((σ (Fin.castAdd d j) : Fin (e + d)) : ℕ) - (j : ℕ)) ∈ q.support :=
        Polynomial.mem_support_iff.mpr hcoeff_ne
      have hbound := H_tilde_prime_coeff_natDegree_le_of_totalDegree (F := F) (H := H) (D := D) hD hH (j := (((σ (Fin.castAdd d j) : Fin (e + d)) : ℕ) - (j : ℕ))) (by simpa [q] using hsup)
      simpa [q, d, lam, hentry, hc, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hbound
    have hright (j : Fin d) : ridx j * lam + rdeg j ≤ B := by
      dsimp [ridx, rdeg]
      have hentry : M (σ (Fin.natAdd e j)) (Fin.natAdd e j) =
          if ((σ (Fin.natAdd e j) : Fin (e + d)) : ℕ) ∈ Set.Icc (j : ℕ) ((j : ℕ) + e) then
            p.coeff (((σ (Fin.natAdd e j) : Fin (e + d)) : ℕ) - (j : ℕ))
          else 0 := by
        simp [M, Polynomial.sylvester]
      have hc := hright_Icc j
      have hcoeff_ne : p.coeff (((σ (Fin.natAdd e j) : Fin (e + d)) : ℕ) - (j : ℕ)) ≠ 0 := by
        have hne' := hne (Fin.natAdd e j)
        rwa [hentry, if_pos hc] at hne'
      have hsup : (((σ (Fin.natAdd e j) : Fin (e + d)) : ℕ) - (j : ℕ)) ∈ p.support :=
        Polynomial.mem_support_iff.mpr hcoeff_ne
      have hbound := canonicalRep_coeff_natDegree_le_of_weight_bound (F := F) (H := H) hH β hβw (i := (((σ (Fin.natAdd e j) : Fin (e + d)) : ℕ) - (j : ℕ))) (by simpa [p] using hsup)
      simpa [p, lam, hentry, hc, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hbound
    have hleft_sum : (∑ j : Fin e, (lidx j * lam + ldeg j)) ≤ e * (d * lam) := by
      calc
        (∑ j : Fin e, (lidx j * lam + ldeg j)) ≤ ∑ j : Fin e, d * lam := by
          exact Finset.sum_le_sum (by intro j _; exact hleft j)
        _ = e * (d * lam) := by simp
    have hright_sum : (∑ j : Fin d, (ridx j * lam + rdeg j)) ≤ d * B := by
      calc
        (∑ j : Fin d, (ridx j * lam + rdeg j)) ≤ ∑ j : Fin d, B := by
          exact Finset.sum_le_sum (by intro j _; exact hright j)
        _ = d * B := by simp
    have hidxsum : (∑ j : Fin e, lidx j) + (∑ j : Fin d, ridx j) = d * e := by
      have hleft_row (j : Fin e) :
          ((σ (Fin.castAdd d j) : Fin (e + d)) : ℕ) = (j : ℕ) + lidx j := by
        dsimp [lidx]
        have hle := (Set.mem_Icc.mp (hleft_Icc j)).1
        omega
      have hright_row (j : Fin d) :
          ((σ (Fin.natAdd e j) : Fin (e + d)) : ℕ) = (j : ℕ) + ridx j := by
        dsimp [ridx]
        have hle := (Set.mem_Icc.mp (hright_Icc j)).1
        omega
      have hsum_left_rows :
          (∑ j : Fin e, ((σ (Fin.castAdd d j) : Fin (e + d)) : ℕ)) =
            (∑ j : Fin e, (j : ℕ)) + (∑ j : Fin e, lidx j) := by
        calc
          (∑ j : Fin e, ((σ (Fin.castAdd d j) : Fin (e + d)) : ℕ)) =
              (∑ j : Fin e, ((j : ℕ) + lidx j)) := by
                refine Finset.sum_congr rfl ?_
                intro j _
                exact hleft_row j
          _ = (∑ j : Fin e, (j : ℕ)) + (∑ j : Fin e, lidx j) := by
                rw [Finset.sum_add_distrib]
      have hsum_right_rows :
          (∑ j : Fin d, ((σ (Fin.natAdd e j) : Fin (e + d)) : ℕ)) =
            (∑ j : Fin d, (j : ℕ)) + (∑ j : Fin d, ridx j) := by
        calc
          (∑ j : Fin d, ((σ (Fin.natAdd e j) : Fin (e + d)) : ℕ)) =
              (∑ j : Fin d, ((j : ℕ) + ridx j)) := by
                refine Finset.sum_congr rfl ?_
                intro j _
                exact hright_row j
          _ = (∑ j : Fin d, (j : ℕ)) + (∑ j : Fin d, ridx j) := by
                rw [Finset.sum_add_distrib]
      have hperm_sum : (∑ i : Fin (e + d), ((σ i : Fin (e + d)) : ℕ)) = ∑ i : Fin (e + d), (i : ℕ) := by
        simpa using (Equiv.sum_comp σ (fun i : Fin (e + d) => (i : ℕ)))
      have hrows_split : (∑ i : Fin (e + d), ((σ i : Fin (e + d)) : ℕ)) =
          (∑ j : Fin e, ((σ (Fin.castAdd d j) : Fin (e + d)) : ℕ)) +
          (∑ j : Fin d, ((σ (Fin.natAdd e j) : Fin (e + d)) : ℕ)) := by
        simpa using (Fin.sum_univ_add (fun i : Fin (e + d) => ((σ i : Fin (e + d)) : ℕ)))
      have hcols_split : (∑ i : Fin (e + d), (i : ℕ)) =
          (∑ j : Fin e, (j : ℕ)) + (∑ j : Fin d, (e + (j : ℕ))) := by
        simpa using (Fin.sum_univ_add (fun i : Fin (e + d) => (i : ℕ)))
      have hright_cols : (∑ j : Fin d, (e + (j : ℕ))) = d * e + ∑ j : Fin d, (j : ℕ) := by
        simp [Finset.sum_add_distrib, Finset.sum_const, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
      have hmain :
          (∑ j : Fin e, ((σ (Fin.castAdd d j) : Fin (e + d)) : ℕ)) +
          (∑ j : Fin d, ((σ (Fin.natAdd e j) : Fin (e + d)) : ℕ)) =
          (∑ j : Fin e, (j : ℕ)) + (d * e + ∑ j : Fin d, (j : ℕ)) := by
        rw [← hrows_split, hperm_sum, hcols_split, hright_cols]
      omega
    have hweighted :
        ((∑ j : Fin e, lidx j) + (∑ j : Fin d, ridx j)) * lam +
          ((∑ j : Fin e, ldeg j) + (∑ j : Fin d, rdeg j)) ≤ e * (d * lam) + d * B := by
      have h := Nat.add_le_add hleft_sum hright_sum
      have hleft_expand : (∑ j : Fin e, (lidx j * lam + ldeg j)) = (∑ j : Fin e, lidx j) * lam + ∑ j : Fin e, ldeg j := by
        rw [Finset.sum_add_distrib]
        rw [← Finset.sum_mul]
      have hright_expand : (∑ j : Fin d, (ridx j * lam + rdeg j)) = (∑ j : Fin d, ridx j) * lam + ∑ j : Fin d, rdeg j := by
        rw [Finset.sum_add_distrib]
        rw [← Finset.sum_mul]
      rw [hleft_expand, hright_expand] at h
      nlinarith [h]
    have hdeg_parts : (∑ j : Fin e, ldeg j) + (∑ j : Fin d, rdeg j) ≤ d * B := by
      rw [hidxsum] at hweighted
      have hrew : e * (d * lam) = (d * e) * lam := by ring
      rw [hrew] at hweighted
      omega
    have hsum_deg_split :
        (∑ i : Fin (e + d), (M (σ i) i).natDegree) =
          (∑ j : Fin e, ldeg j) + (∑ j : Fin d, rdeg j) := by
      simpa only [ldeg, rdeg] using (Fin.sum_univ_add (fun i : Fin (e + d) => (M (σ i) i).natDegree))
    calc
      (∏ i : Fin (e + d), M (σ i) i).natDegree ≤
          ∑ i : Fin (e + d), (M (σ i) i).natDegree := by
            simpa using (Polynomial.natDegree_prod_le (s := Finset.univ) (f := fun i : Fin (e + d) => M (σ i) i))
      _ = (∑ j : Fin e, ldeg j) + (∑ j : Fin d, rdeg j) := hsum_deg_split
      _ ≤ B * d := by simpa [Nat.mul_comm] using hdeg_parts

theorem poly_eq_zero_of_ncard_gt_bound_of_subset_roots {p : F[X]} {S : Set F} {N : ℕ}
    (hS : S ⊆ {z | p.eval z = 0})
    (hdeg : p.natDegree ≤ N)
    (hcard : Set.ncard S > N) :
  p = 0 := by
  by_contra hp
  have hsubset : S ⊆ p.rootSet F := by
    intro z hz
    have hzroot : p.eval z = 0 := hS hz
    exact (Polynomial.mem_rootSet_of_ne hp).2 (by simpa using hzroot)
  have hncard : Set.ncard S ≤ Set.ncard (p.rootSet F) := by
    exact Set.ncard_le_ncard hsubset
  have hrootcard : Set.ncard (p.rootSet F) ≤ p.natDegree := Polynomial.ncard_rootSet_le p F
  omega

theorem resultant_eval_eq_resultant_map_eval_fixed_degrees (p q : F[X][Y]) (z : F) :
  (Polynomial.resultant p q).eval z =
    Polynomial.resultant (p.map (Polynomial.evalRingHom z))
      (q.map (Polynomial.evalRingHom z)) p.natDegree q.natDegree := by
  exact (Polynomial.resultant_map_map p q p.natDegree q.natDegree (Polynomial.evalRingHom z)).symm

theorem resultant_fixed_degree_eq_zero_of_common_root_of_monic_right {p q : F[X]} {m n : ℕ} {t : F}
    (hm : p.natDegree ≤ m) (hqmonic : q.Monic) (hn : q.natDegree = n)
    (hp : p.eval t = 0) (hq : q.eval t = 0) :
  Polynomial.resultant p q m n = 0 := by
  have hres0 : Polynomial.resultant p q = 0 := by
    rw [Polynomial.resultant_eq_zero_iff]
    constructor
    · exact Or.inr hqmonic.ne_zero
    · intro hcop
      rcases hcop with ⟨a, b, hab⟩
      have h_eval := congrArg (fun r : F[X] => r.eval t) hab
      simp [eval_add, eval_mul, hp, hq] at h_eval
  have hdeg : p.natDegree + (m - p.natDegree) = m := Nat.add_sub_of_le hm
  rw [← hdeg]
  rw [← hn]
  rw [Polynomial.resultant_add_left_deg]
  · simp [hres0]
  · exact le_rfl

theorem Sbeta_subset_resultant_roots {H : F[X][Y]} (hH : 0 < H.natDegree) (β : 𝒪 H) :
  S_β β ⊆
    {z | (Polynomial.resultant (canonicalRepOf𝒪 hH β) (H_tilde' H)).eval z = 0} := by
  intro z hz
  rcases hz with ⟨root, hβ⟩
  let p : F[X][Y] := canonicalRepOf𝒪 hH β
  let q : F[X][Y] := H_tilde' H
  have hp : (p.map (Polynomial.evalRingHom z)).eval root.1 = 0 := by
    have h := π_z_eq_eval_canonicalRepOf𝒪 hH z root β
    rw [h] at hβ
    rw [Polynomial.map_evalRingHom_eval]
    simpa [p, Polynomial.coe_evalEvalRingHom] using hβ
  have hq : (q.map (Polynomial.evalRingHom z)).eval root.1 = 0 := by
    rw [Polynomial.map_evalRingHom_eval]
    exact root.2
  have hqmonic : (q.map (Polynomial.evalRingHom z)).Monic := by
    exact (H_tilde'_monic H hH).map (Polynomial.evalRingHom z)
  have hn : (q.map (Polynomial.evalRingHom z)).natDegree = q.natDegree := by
    exact (H_tilde'_monic H hH).natDegree_map (Polynomial.evalRingHom z)
  have hres : Polynomial.resultant (p.map (Polynomial.evalRingHom z)) (q.map (Polynomial.evalRingHom z)) p.natDegree q.natDegree = 0 := by
    exact resultant_fixed_degree_eq_zero_of_common_root_of_monic_right
      (Polynomial.natDegree_map_le (f := Polynomial.evalRingHom z) (p := p)) hqmonic hn hp hq
  change (Polynomial.resultant p q).eval z = 0
  rw [resultant_eval_eq_resultant_map_eval_fixed_degrees]
  exact hres

theorem weight_bot_embedding_zero {H : F[X][Y]} (hH : 0 < H.natDegree) (β : 𝒪 H) (D : ℕ)
    (hw : weight_Λ_over_𝒪 hH β D = ⊥) :
  embeddingOf𝒪Into𝕃 H β = 0 := by
  classical
  let p : F[X][Y] := canonicalRepOf𝒪 hH β
  have hp : p = 0 := by
    by_contra hp_ne
    have hsup : p.support.Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro h_empty
      exact hp_ne (Polynomial.support_eq_empty.mp h_empty)
    rcases hsup with ⟨n, hn⟩
    have hle : (WithBot.some (n * (D + 1 - Bivariate.natDegreeY H) + (p.coeff n).natDegree) : WithBot ℕ) ≤ weight_Λ p H D :=
      le_weight_Λ_of_mem_support hn
    have hle_bot : (WithBot.some (n * (D + 1 - Bivariate.natDegreeY H) + (p.coeff n).natDegree) : WithBot ℕ) ≤ (⊥ : WithBot ℕ) := by
      exact hle.trans (by simpa [p, weight_Λ_over_𝒪] using le_of_eq hw)
    exact (not_le_of_gt (WithBot.bot_lt_coe _)) hle_bot
  rw [← mk_canonicalRepOf𝒪 hH β]
  change embeddingOf𝒪Into𝕃 H (Ideal.Quotient.mk (Ideal.span {H_tilde' H}) p : 𝒪 H) = 0
  rw [hp]
  simp


/-- The statement of Lemma A.1 in Appendix A.3 of [BCIKS20]. -/
lemma lemmaA1_embedding_eq_zero_of_many_rational_roots {H : F[X][Y]}
    [hHirreducible : Fact (Irreducible H)]
    (hH : 0 < H.natDegree) (β : 𝒪 H) (D : ℕ)
    (hD : D ≥ Bivariate.totalDegree H)
    (S_β_card : Set.ncard (S_β β) > (weight_Λ_over_𝒪 hH β D) * H.natDegree) :
  embeddingOf𝒪Into𝕃 _ β = 0 := by
  classical
  set R : F[X] := Polynomial.resultant (canonicalRepOf𝒪 hH β) (H_tilde' H)
  cases hweight : weight_Λ_over_𝒪 hH β D with
  | bot =>
      exact weight_bot_embedding_zero hH β D hweight
  | coe B =>
      have hβw : weight_Λ_over_𝒪 hH β D ≤ (WithBot.some B : WithBot ℕ) := by
        rw [hweight]
      have hdeg : R.natDegree ≤ B * H.natDegree := by
        dsimp [R]
        exact natDegree_resultant_le_weight_bound hH hD β hβw
      have hcard : Set.ncard (S_β β) > B * H.natDegree := by
        rw [hweight] at S_β_card
        change ((B * H.natDegree : ℕ) : WithBot ℕ) < ((Set.ncard (S_β β) : ℕ) : WithBot ℕ) at S_β_card
        exact WithBot.coe_lt_coe.mp S_β_card
      have hRzero : R = 0 := by
        apply poly_eq_zero_of_ncard_gt_bound_of_subset_roots
        · dsimp [R]
          exact Sbeta_subset_resultant_roots hH β
        · exact hdeg
        · exact hcard
      apply embedding_eq_zero_of_resultant_zero hH β
      dsimp [R] at hRzero
      exact hRzero

end LemmaA1

section

variable {F : Type} [CommRing F] [IsDomain F]

/-- The embedding of the coefficients of a bivariate polynomial into the bivariate polynomial ring
with rational coefficients. -/
noncomputable def coeffAsRatFunc : F[X] →+* Polynomial (RatFunc F) :=
  RingHom.comp bivPolyHom Polynomial.C

/-- The embedding of coefficient polynomials into the function field `𝕃`. -/
noncomputable def liftToFunctionField {H : F[X][Y]} : F[X] →+* 𝕃 H :=
  RingHom.comp (Ideal.Quotient.mk (Ideal.span {H_tilde H})) coeffAsRatFunc

/-- The embedding of bivariate polynomials into the function field `𝕃`. -/
noncomputable def liftBivariate {H : F[X][Y]} : F[X][Y] →+* 𝕃 H :=
  RingHom.comp (Ideal.Quotient.mk (Ideal.span {H_tilde H})) bivPolyHom

/-- The image of the polynomial variable `T` in the function field `𝕃 H`. -/
noncomputable def functionFieldT {H : F[X][Y]} : 𝕃 H :=
  Ideal.Quotient.mk (Ideal.span {H_tilde H}) Polynomial.X

/-- Quotient constructors in `𝒪` embed by applying the bivariate lift. -/
@[simp]
lemma embeddingOf𝒪Into𝕃_mk (H : F[X][Y]) (p : F[X][Y]) :
    embeddingOf𝒪Into𝕃 H (Ideal.Quotient.mk (Ideal.span {H_tilde' H}) p : 𝒪 H) =
      liftBivariate (H := H) p := by
  rfl

/-- Every bivariate polynomial representative gives a regular element of the function field. -/
lemma regular_liftBivariate (H : F[X][Y]) (p : F[X][Y]) :
    ∃ pre : 𝒪 H, embeddingOf𝒪Into𝕃 H pre = liftBivariate (H := H) p :=
  ⟨Ideal.Quotient.mk (Ideal.span {H_tilde' H}) p, by simp⟩

/-- Bivariate-polynomial images are regular elements of the function field. -/
lemma regularElementsSet_liftBivariate (H : F[X][Y]) (p : F[X][Y]) :
    liftBivariate (H := H) p ∈ regularElementsSet H := by
  rcases regular_liftBivariate H p with ⟨pre, hpre⟩
  exact ⟨pre, hpre.symm⟩

/-- Coefficients embedded into `𝕃` are regular elements. -/
lemma regular_liftToFunctionField (H : F[X][Y]) (p : F[X]) :
    ∃ pre : 𝒪 H, embeddingOf𝒪Into𝕃 H pre = liftToFunctionField (H := H) p :=
  regular_liftBivariate H (Polynomial.C p)

/-- Coefficient-polynomial images are regular elements of the function field. -/
lemma regularElementsSet_liftToFunctionField (H : F[X][Y]) (p : F[X]) :
    liftToFunctionField (H := H) p ∈ regularElementsSet H := by
  simpa using regularElementsSet_liftBivariate H (Polynomial.C p)

/-- Nonzero coefficient polynomials remain nonzero after embedding into the function field. -/
lemma liftToFunctionField_ne_zero {F : Type} [Field F] {H : F[X][Y]}
    [H_irreducible : Fact (Irreducible H)] [H_natDegree_pos : Fact (0 < H.natDegree)]
    {p : F[X]} (hp : p ≠ 0) :
    liftToFunctionField (H := H) p ≠ 0 := by
  intro hzero
  have hmem : coeffAsRatFunc p ∈ Ideal.span ({H_tilde H} : Set (Polynomial (RatFunc F))) := by
    simpa [liftToFunctionField] using (Ideal.Quotient.eq_zero_iff_mem.mp hzero)
  rw [Ideal.mem_span_singleton] at hmem
  have hp_map : univPolyHom (F := F) p ≠ 0 := by
    intro hp_zero
    exact hp (univPolyHom_injective (F := F) (by simpa using hp_zero))
  have hunit : IsUnit (coeffAsRatFunc p) := by
    have hunitC : IsUnit (Polynomial.C (univPolyHom (F := F) p) :
        Polynomial (RatFunc F)) :=
      Polynomial.isUnit_C.mpr (Ne.isUnit hp_map)
    simpa only [coeffAsRatFunc, RingHom.comp_apply, ToRatFunc.bivPolyHom,
      Polynomial.coe_mapRingHom, Polynomial.map_C] using hunitC
  exact (irreducibleHTildeOfIrreducible_of_natDegree_pos H_natDegree_pos.out
    H_irreducible.out).not_dvd_isUnit hunit hmem

/-- The leading coefficient `W` of a positive-`Y`-degree `H` is nonzero in the function field. -/
lemma liftToFunctionField_leadingCoeff_ne_zero {F : Type} [Field F] {H : F[X][Y]}
    [H_irreducible : Fact (Irreducible H)] [H_natDegree_pos : Fact (0 < H.natDegree)] :
    liftToFunctionField (H := H) H.leadingCoeff ≠ 0 := by
  exact liftToFunctionField_ne_zero
    (Polynomial.leadingCoeff_ne_zero.mpr (Polynomial.ne_zero_of_natDegree_gt H_natDegree_pos.out))

/-- If `q ∣ p` in `F[X]`, then `p / q` is regular after embedding into `𝕃`. -/
lemma regularElementsSet_liftToFunctionField_div_of_dvd {F : Type} [Field F] {H : F[X][Y]}
    [H_irreducible : Fact (Irreducible H)] [H_natDegree_pos : Fact (0 < H.natDegree)]
    {p q : F[X]} (hq : q ≠ 0) (hdiv : q ∣ p) :
    liftToFunctionField (H := H) p / liftToFunctionField (H := H) q ∈ regularElementsSet H := by
  rcases hdiv with ⟨r, rfl⟩
  have hq_lift : liftToFunctionField (H := H) q ≠ 0 := liftToFunctionField_ne_zero hq
  have heq :
      liftToFunctionField (H := H) (q * r) / liftToFunctionField (H := H) q =
        liftToFunctionField (H := H) r := by
    rw [map_mul]
    field_simp [hq_lift]
  rw [heq]
  exact regularElementsSet_liftToFunctionField H r

/-- If `W = H.leadingCoeff` divides `p`, then `p / W` is regular after embedding into `𝕃`. -/
lemma regularElementsSet_liftToFunctionField_div_leadingCoeff_of_dvd {F : Type} [Field F]
    {H : F[X][Y]} [H_irreducible : Fact (Irreducible H)]
    [H_natDegree_pos : Fact (0 < H.natDegree)] {p : F[X]}
    (hdiv : H.leadingCoeff ∣ p) :
    liftToFunctionField (H := H) p / liftToFunctionField (H := H) H.leadingCoeff ∈
      regularElementsSet H := by
  exact regularElementsSet_liftToFunctionField_div_of_dvd
    (Polynomial.leadingCoeff_ne_zero.mpr (Polynomial.ne_zero_of_natDegree_gt H_natDegree_pos.out))
    hdiv

private lemma mul_pow_mul_div_pow_eq_lower {K : Type} [Field K] {W T a : K}
    (hW : W ≠ 0) {k i : ℕ} (hi : i ≤ k) :
    W ^ k * (a * (T / W) ^ i) = a * (T ^ i * W ^ (k - i)) := by
  rw [div_pow]
  have hk : k = k - i + i := (Nat.sub_add_cancel hi).symm
  calc
    W ^ k * (a * (T ^ i / W ^ i)) = a * (T ^ i * (W ^ k / W ^ i)) := by
      ring
    _ = a * (T ^ i * W ^ (k - i)) := by
      rw [hk, pow_add]
      field_simp [hW]
      have hsub : k - i + i - i = k - i := by omega
      rw [hsub]

private lemma mul_pow_mul_div_pow_succ_eq_top {K : Type} [Field K] {W T a : K}
    (hW : W ≠ 0) (k : ℕ) :
    W ^ k * (a * (T / W) ^ (k + 1)) = (a / W) * T ^ (k + 1) := by
  rw [div_pow, pow_succ]
  field_simp [hW]
  ring

/-- Clearing denominators in `W^k · P(T/W)` as an explicit sum: if `P.natDegree ≤ k + 1`, then
`W^k * eval₂ lift (T/W) P` decomposes into a low-degree polynomial sum plus a single
`(P.coeff(k+1)/W) · T^(k+1)` term. The divisibility `W ∣ P.coeff(k+1)` is not needed here -
the formula holds in `𝕃 H` directly via field division. -/
lemma W_pow_mul_eval₂_div_eq_sum {F : Type} [Field F] {H : F[X][Y]}
    [H_irreducible : Fact (Irreducible H)] [H_natDegree_pos : Fact (0 < H.natDegree)]
    {P : F[X][Y]} {k : ℕ} (hP : P.natDegree ≤ k + 1) :
    liftToFunctionField (H := H) H.leadingCoeff ^ k *
      Polynomial.eval₂ liftToFunctionField
        (functionFieldT (H := H) / liftToFunctionField (H := H) H.leadingCoeff) P =
      (∑ i ∈ Finset.range (k + 1),
          liftToFunctionField (H := H) (P.coeff i) *
            (functionFieldT (H := H) ^ i *
              liftToFunctionField (H := H) H.leadingCoeff ^ (k - i))) +
        (liftToFunctionField (H := H) (P.coeff (k + 1)) /
            liftToFunctionField (H := H) H.leadingCoeff) *
          functionFieldT (H := H) ^ (k + 1) := by
  set W : 𝕃 H := liftToFunctionField (H := H) H.leadingCoeff with hW_def
  set T : 𝕃 H := functionFieldT (H := H) with hT_def
  have hW : W ≠ 0 := by
    simpa [W] using (liftToFunctionField_leadingCoeff_ne_zero (H := H))
  have hP_lt : P.natDegree < k + 2 := by omega
  rw [Polynomial.eval₂_eq_sum_range' liftToFunctionField hP_lt (T / W)]
  rw [Finset.mul_sum]
  rw [show k + 2 = k + 1 + 1 by omega, Finset.sum_range_succ]
  congr 1
  · refine Finset.sum_congr rfl (fun i hi => ?_)
    have hi_le : i ≤ k := by
      have hi_lt := Finset.mem_range.mp hi
      omega
    exact mul_pow_mul_div_pow_eq_lower (W := W) (T := T)
      (a := liftToFunctionField (H := H) (P.coeff i)) hW hi_le
  · exact mul_pow_mul_div_pow_succ_eq_top (W := W) (T := T)
      (a := liftToFunctionField (H := H) (P.coeff (k + 1))) hW k

/-- The bivariate variable maps to the function-field variable `T`. -/
@[simp]
lemma liftBivariate_X {H : F[X][Y]} :
    liftBivariate (H := H) (Polynomial.X : F[X][Y]) = functionFieldT (H := H) := by
  simp [liftBivariate, functionFieldT, bivPolyHom]

/-- The function-field variable `T` is regular. -/
lemma regularElementsSet_functionFieldT (H : F[X][Y]) :
    functionFieldT (H := H) ∈ regularElementsSet H := by
  simpa using regularElementsSet_liftBivariate H (Polynomial.X : F[X][Y])

/-- A linear polynomial evaluated at `T / W` is regular when its linear coefficient is divisible by
`W = H.leadingCoeff`. -/
lemma regularElementsSet_eval₂_linear_of_coeff_one_dvd {F : Type} [Field F] {H : F[X][Y]}
    [H_irreducible : Fact (Irreducible H)] [H_natDegree_pos : Fact (0 < H.natDegree)]
    {P : F[X][Y]} (hP : P.natDegree ≤ 1) (hdiv : H.leadingCoeff ∣ P.coeff 1) :
    Polynomial.eval₂ liftToFunctionField
      (functionFieldT (H := H) / liftToFunctionField (H := H) H.leadingCoeff) P ∈
      regularElementsSet H := by
  rw [Polynomial.eq_X_add_C_of_natDegree_le_one hP]
  simp only [Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_C,
    Polynomial.eval₂_X]
  have hterm :
      liftToFunctionField (H := H) (P.coeff 1) *
          (functionFieldT (H := H) / liftToFunctionField (H := H) H.leadingCoeff) =
        (liftToFunctionField (H := H) (P.coeff 1) /
            liftToFunctionField (H := H) H.leadingCoeff) * functionFieldT (H := H) := by
    rw [div_eq_mul_inv, div_eq_mul_inv]
    ring
  rw [hterm]
  exact regularElementsSet_add
    (regularElementsSet_mul
      (regularElementsSet_liftToFunctionField_div_leadingCoeff_of_dvd hdiv)
      (regularElementsSet_functionFieldT H))
    (regularElementsSet_liftToFunctionField H (P.coeff 0))

/-- Clearing denominators in `P(T / W)`: if `P` has degree at most `k + 1` and its top
coefficient is divisible by `W = H.leadingCoeff`, then `W^k * P(T/W)` is regular. -/
lemma regularElementsSet_mul_pow_eval₂_div_of_natDegree_le_succ_of_coeff_succ_dvd
    {F : Type} [Field F] {H : F[X][Y]}
    [H_irreducible : Fact (Irreducible H)] [H_natDegree_pos : Fact (0 < H.natDegree)]
    {P : F[X][Y]} {k : ℕ} (hP : P.natDegree ≤ k + 1)
    (hdiv : H.leadingCoeff ∣ P.coeff (k + 1)) :
    liftToFunctionField (H := H) H.leadingCoeff ^ k *
      Polynomial.eval₂ liftToFunctionField
        (functionFieldT (H := H) / liftToFunctionField (H := H) H.leadingCoeff) P ∈
      regularElementsSet H := by
  let W : 𝕃 H := liftToFunctionField (H := H) H.leadingCoeff
  let T : 𝕃 H := functionFieldT (H := H)
  have hW : W ≠ 0 := by
    simpa [W] using (liftToFunctionField_leadingCoeff_ne_zero (H := H))
  have hP_lt : P.natDegree < k + 2 := by omega
  change W ^ k * Polynomial.eval₂ liftToFunctionField (T / W) P ∈ regularElementsSet H
  rw [Polynomial.eval₂_eq_sum_range' liftToFunctionField hP_lt (T / W)]
  rw [Finset.mul_sum]
  rw [show k + 2 = k + 1 + 1 by omega, Finset.sum_range_succ]
  refine regularElementsSet_add ?_ ?_
  · refine regularElementsSet_sum (Finset.range (k + 1)) ?_
    intro i hi
    have hi_lt : i < k + 1 := Finset.mem_range.mp hi
    have hi_le : i ≤ k := by omega
    rw [mul_pow_mul_div_pow_eq_lower (W := W) (T := T)
      (a := liftToFunctionField (H := H) (P.coeff i)) hW hi_le]
    exact regularElementsSet_mul
      (regularElementsSet_liftToFunctionField H (P.coeff i))
      (regularElementsSet_mul
        (by simpa [T] using regularElementsSet_pow (regularElementsSet_functionFieldT H) i)
        (by
          simpa [W] using
            regularElementsSet_pow
              (regularElementsSet_liftToFunctionField H H.leadingCoeff) (k - i)))
  · rw [mul_pow_mul_div_pow_succ_eq_top (W := W) (T := T)
      (a := liftToFunctionField (H := H) (P.coeff (k + 1))) hW k]
    exact regularElementsSet_mul
      (by
        simpa [W] using
          regularElementsSet_liftToFunctionField_div_leadingCoeff_of_dvd (H := H) hdiv)
      (by simpa [T] using regularElementsSet_pow (regularElementsSet_functionFieldT H) (k + 1))

/-- Constant bivariate polynomials map through the coefficient embedding. -/
@[simp]
lemma liftBivariate_C {H : F[X][Y]} (p : F[X]) :
    liftBivariate (H := H) (Polynomial.C p : F[X][Y]) = liftToFunctionField (H := H) p := by
  rfl

/-- The embedding of scalars into the function field `𝕃`. -/
noncomputable def fieldTo𝕃 {H : F[X][Y]} : F →+* 𝕃 H :=
  RingHom.comp liftToFunctionField Polynomial.C

/-- View a bivariate polynomial as a power series over `𝕃 H` by lifting its coefficients. -/
noncomputable def polyToPowerSeries𝕃 (H : F[X][Y]) (P : F[X][Y]) : PowerSeries (𝕃 H) :=
  PowerSeries.mk <| fun n => liftToFunctionField (P.coeff n)


end

noncomputable section

namespace ClaimA2

variable {F : Type} [Field F] {R : F[X][X][X]} {H : F[X][Y]}
  [H_irreducible : Fact (Irreducible H)] [H_natDegree_pos : Fact (0 < H.natDegree)]

/-! ### Claim A.2 hypotheses and derivative setup -/

/-- The algebraic hypotheses for Claim A.2 from Appendix A.4 of [BCIKS20], after specializing
`R` at `X = x₀`. -/
structure Hypotheses (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y]) : Prop where
  dvd_evalX : H ∣ Bivariate.evalX (Polynomial.C x₀) R
  separable_evalX : (Bivariate.evalX (Polynomial.C x₀) R).Separable

private lemma evalX_natDegree_le {K : Type} [CommSemiring K] (x : K) (P : K[X][Y]) :
    (Bivariate.evalX x P).natDegree ≤ P.natDegree := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro n hn
  have hcoeff : P.coeff n = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt hn
  simp [Bivariate.evalX_eq_map, Polynomial.coeff_map, hcoeff]

lemma evalX_ne_zero_of_Hypotheses {x₀ : F} {R : F[X][X][Y]} {H : F[X][Y]}
    (hHyp : Hypotheses x₀ R H) :
    Bivariate.evalX (Polynomial.C x₀) R ≠ 0 :=
  hHyp.separable_evalX.ne_zero

lemma H_natDegree_le_R_natDegree_of_Hypotheses {x₀ : F} {R : F[X][X][Y]} {H : F[X][Y]}
    (hHyp : Hypotheses x₀ R H) :
    H.natDegree ≤ R.natDegree :=
  (Polynomial.natDegree_le_of_dvd hHyp.dvd_evalX (evalX_ne_zero_of_Hypotheses hHyp)).trans
    (evalX_natDegree_le (Polynomial.C x₀) R)

lemma derivative_evalX_coeff (x₀ : F) (R : F[X][X][Y]) (i : ℕ) :
    (Bivariate.evalX (Polynomial.C x₀) R.derivative).coeff i =
      (Bivariate.evalX (Polynomial.C x₀) R).coeff (i + 1) * ((i + 1 : ℕ) : F[X]) := by
  have hsucc_cast : (((i : ℕ) : F[X][X]) + 1) = ((i + 1 : ℕ) : F[X][X]) := by
    rw [← Nat.cast_one (R := F[X][X]), ← Nat.cast_add]
  calc
    (Bivariate.evalX (Polynomial.C x₀) R.derivative).coeff i =
        ((R.derivative).coeff i).eval (Polynomial.C x₀) := by
      simp [Bivariate.evalX_eq_map, Polynomial.coeff_map]
    _ = (R.coeff (i + 1) * ((i + 1 : ℕ) : F[X][X])).eval (Polynomial.C x₀) := by
      rw [Polynomial.coeff_derivative, hsucc_cast]
    _ = (Bivariate.evalX (Polynomial.C x₀) R).coeff (i + 1) * ((i + 1 : ℕ) : F[X]) := by
      simp [Bivariate.evalX_eq_map, Polynomial.coeff_map]

lemma natDegree_derivative_evalX_coeff_le (x₀ : F) (R : F[X][X][Y]) {D i : ℕ}
    (hD : Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R) ≤ D) :
    ((Bivariate.evalX (Polynomial.C x₀) R.derivative).coeff i).natDegree ≤ D - (i + 1) := by
  rw [derivative_evalX_coeff]
  calc
    (((Bivariate.evalX (Polynomial.C x₀) R).coeff (i + 1) * ((i + 1 : ℕ) : F[X])).natDegree)
        ≤ ((Bivariate.evalX (Polynomial.C x₀) R).coeff (i + 1)).natDegree +
            (((i + 1 : ℕ) : F[X]).natDegree) := Polynomial.natDegree_mul_le
    _ = ((Bivariate.evalX (Polynomial.C x₀) R).coeff (i + 1)).natDegree := by
        rw [← Polynomial.C_eq_natCast, Polynomial.natDegree_C, Nat.add_zero]
    _ ≤ D - (i + 1) :=
        natDegree_coeff_le_of_totalDegree_le (Bivariate.evalX (Polynomial.C x₀) R) hD (i + 1)

/-- The leading coefficient `W` of `H` divides the leading coefficient of `R(x₀,Y,Z)`. -/
lemma leadingCoeff_dvd_evalX_leadingCoeff {x₀ : F} {R : F[X][X][Y]} {H : F[X][Y]}
    (hHyp : Hypotheses x₀ R H) :
    H.leadingCoeff ∣ (Bivariate.evalX (Polynomial.C x₀) R).leadingCoeff := by
  rcases hHyp.dvd_evalX with ⟨q, hq⟩
  refine ⟨q.leadingCoeff, ?_⟩
  calc
    (Bivariate.evalX (Polynomial.C x₀) R).leadingCoeff = (H * q).leadingCoeff := by rw [hq]
    _ = H.leadingCoeff * q.leadingCoeff := Polynomial.leadingCoeff_mul H q

/-- The leading coefficient `W` of `H` divides the coefficient of `Y ^ R.natDegree` in
`R(x₀,Y,Z)`. If specialization lowers the `Y`-degree, that coefficient is zero. -/
lemma leadingCoeff_dvd_evalX_coeff_natDegree {x₀ : F} {R : F[X][X][Y]} {H : F[X][Y]}
    (hHyp : Hypotheses x₀ R H) :
    H.leadingCoeff ∣ (Bivariate.evalX (Polynomial.C x₀) R).coeff R.natDegree := by
  let P : F[X][Y] := Bivariate.evalX (Polynomial.C x₀) R
  have hdeg : P.natDegree ≤ R.natDegree := evalX_natDegree_le (Polynomial.C x₀) R
  by_cases hEq : P.natDegree = R.natDegree
  · simpa [P, hEq.symm] using leadingCoeff_dvd_evalX_leadingCoeff hHyp
  · have hlt : P.natDegree < R.natDegree := lt_of_le_of_ne hdeg hEq
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt hlt]
    exact dvd_zero H.leadingCoeff

/-- The leading coefficient `W` of `H` divides the top possible coefficient of
`∂R/∂Y(x₀,Y,Z)`. This is the coefficient that remains after multiplying `ζ` by `W^(d-2)`. -/
lemma leadingCoeff_dvd_evalX_derivative_coeff_pred {x₀ : F} {R : F[X][X][Y]} {H : F[X][Y]}
    (hHyp : Hypotheses x₀ R H) :
    H.leadingCoeff ∣
      (Bivariate.evalX (Polynomial.C x₀) R.derivative).coeff (R.natDegree - 1) := by
  by_cases hR : R.natDegree = 0
  · have hderiv : R.derivative = 0 := Polynomial.derivative_of_natDegree_zero hR
    rw [hderiv]
    exact ⟨0, by simp [Bivariate.evalX_eq_map]⟩
  · have hsucc : R.natDegree - 1 + 1 = R.natDegree :=
      Nat.sub_add_cancel (Nat.pos_of_ne_zero hR)
    have hsucc_cast : (((R.natDegree - 1 : ℕ) : F[X][X]) + 1) =
        (R.natDegree : F[X][X]) := by
      rw [← Nat.cast_one (R := F[X][X])]
      rw [← Nat.cast_add, hsucc]
    have hcoeff :
        (Bivariate.evalX (Polynomial.C x₀) R.derivative).coeff (R.natDegree - 1) =
          (Bivariate.evalX (Polynomial.C x₀) R).coeff R.natDegree *
            (R.natDegree : F[X]) := by
      calc
        (Bivariate.evalX (Polynomial.C x₀) R.derivative).coeff (R.natDegree - 1) =
            ((R.derivative).coeff (R.natDegree - 1)).eval (Polynomial.C x₀) := by
          simp [Bivariate.evalX_eq_map, Polynomial.coeff_map]
        _ = (R.coeff R.natDegree * (R.natDegree : F[X][X])).eval (Polynomial.C x₀) := by
          rw [Polynomial.coeff_derivative, hsucc, hsucc_cast]
        _ = (Bivariate.evalX (Polynomial.C x₀) R).coeff R.natDegree *
            (R.natDegree : F[X]) := by
          simp [Bivariate.evalX_eq_map, Polynomial.coeff_map]
    rcases leadingCoeff_dvd_evalX_coeff_natDegree hHyp with ⟨q, hq⟩
    refine ⟨q * (R.natDegree : F[X]), ?_⟩
    rw [hcoeff, hq]
    ring

/-- The element `ζ` from Appendix A.4 of [BCIKS20]. -/
def ζ (R : F[X][X][Y]) (x₀ : F) (H : F[X][Y]) [H_irreducible : Fact (Irreducible H)]
    [H_natDegree_pos : Fact (0 < H.natDegree)] : 𝕃 H :=
  let W : 𝕃 H := liftToFunctionField (H.leadingCoeff)
  let T : 𝕃 H := functionFieldT (H := H)
  Polynomial.eval₂ liftToFunctionField (T / W)
    (Bivariate.evalX (Polynomial.C x₀) R.derivative)

/-- If the derivative specialization is constant in the function-field variable, then `ζ` is
regular. -/
lemma ζ_regular_of_derivative_evalX_eq_C (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [H_irreducible : Fact (Irreducible H)] [H_natDegree_pos : Fact (0 < H.natDegree)] {p : F[X]}
    (hp : Bivariate.evalX (Polynomial.C x₀) R.derivative = Polynomial.C p) :
    ζ R x₀ H ∈ regularElementsSet H := by
  rw [ζ, hp]
  simp only [Polynomial.eval₂_C]
  exact regularElementsSet_liftToFunctionField H p

/-- If `R` has `Y`-degree at most one, then the specialized derivative is constant. -/
lemma derivative_evalX_eq_C_of_natDegree_le_one
    (x₀ : F) (R : F[X][X][Y]) (hR : R.natDegree ≤ 1) :
    ∃ p : F[X], Bivariate.evalX (Polynomial.C x₀) R.derivative = Polynomial.C p := by
  let P : F[X][Y] := Bivariate.evalX (Polynomial.C x₀) R.derivative
  refine ⟨P.coeff 0, ?_⟩
  have hderiv : R.derivative.natDegree ≤ 0 := by
    calc
      R.derivative.natDegree ≤ R.natDegree - 1 := Polynomial.natDegree_derivative_le R
      _ = 0 := by omega
  have hP : P.natDegree ≤ 0 :=
    (evalX_natDegree_le (Polynomial.C x₀) R.derivative).trans hderiv
  exact Polynomial.eq_C_of_natDegree_le_zero hP

/-- In the constant-derivative, low-`Y`-degree case, the `ξ` regularity witness is explicit. -/
lemma ξ_regular_of_derivative_evalX_eq_C_of_natDegree_le_one
    (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y]) [H_irreducible : Fact (Irreducible H)]
    [H_natDegree_pos : Fact (0 < H.natDegree)]
    {p : F[X]} (hp : Bivariate.evalX (Polynomial.C x₀) R.derivative = Polynomial.C p)
    (hR : R.natDegree ≤ 1) :
    ∃ pre : 𝒪 H,
    let d := R.natDegree
    let W : 𝕃 H := liftToFunctionField (H.leadingCoeff)
    embeddingOf𝒪Into𝕃 _ pre = W ^ (d - 2) * ζ R x₀ H := by
  rcases ζ_regular_of_derivative_evalX_eq_C x₀ R H hp with ⟨pre, hpre⟩
  refine ⟨pre, ?_⟩
  have hd : R.natDegree - 2 = 0 := by omega
  simpa [hd] using hpre.symm

/-- If `R` has `Y`-degree at most one, the regularity statement for `ξ` follows from the
constant-derivative case. -/
lemma ξ_regular_of_natDegree_le_one
    (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y]) [H_irreducible : Fact (Irreducible H)]
    [H_natDegree_pos : Fact (0 < H.natDegree)] (hR : R.natDegree ≤ 1) :
    ∃ pre : 𝒪 H,
    let d := R.natDegree
    let W : 𝕃 H := liftToFunctionField (H.leadingCoeff)
    embeddingOf𝒪Into𝕃 _ pre = W ^ (d - 2) * ζ R x₀ H := by
  rcases derivative_evalX_eq_C_of_natDegree_le_one x₀ R hR with ⟨p, hp⟩
  exact ξ_regular_of_derivative_evalX_eq_C_of_natDegree_le_one x₀ R H hp hR

/-- In the quadratic case, `ξ = ζ` is regular by clearing the single denominator with the
divisibility of the top derivative coefficient. -/
lemma ξ_regular_of_natDegree_eq_two
    (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y]) [H_irreducible : Fact (Irreducible H)]
    [H_natDegree_pos : Fact (0 < H.natDegree)] (hHyp : Hypotheses x₀ R H)
    (hR : R.natDegree = 2) :
    ∃ pre : 𝒪 H,
    let d := R.natDegree
    let W : 𝕃 H := liftToFunctionField (H.leadingCoeff)
    embeddingOf𝒪Into𝕃 _ pre = W ^ (d - 2) * ζ R x₀ H := by
  let P : F[X][Y] := Bivariate.evalX (Polynomial.C x₀) R.derivative
  have hP : P.natDegree ≤ 1 := by
    calc
      P.natDegree ≤ R.derivative.natDegree := evalX_natDegree_le (Polynomial.C x₀) R.derivative
      _ ≤ R.natDegree - 1 := Polynomial.natDegree_derivative_le R
      _ = 1 := by omega
  have hdiv : H.leadingCoeff ∣ P.coeff 1 := by
    simpa [P, hR] using leadingCoeff_dvd_evalX_derivative_coeff_pred hHyp
  have hreg : ζ R x₀ H ∈ regularElementsSet H := by
    simpa [ζ, P] using regularElementsSet_eval₂_linear_of_coeff_one_dvd (H := H) hP hdiv
  rcases hreg with ⟨pre, hpre⟩
  refine ⟨pre, ?_⟩
  have hd : R.natDegree - 2 = 0 := by omega
  simpa [hd] using hpre.symm

/-- Explicit polynomial representative for the regular element `ξ = W^(d-2) · ζ` of Claim A.2.
For `2 ≤ R.natDegree`, this is the polynomial obtained by clearing the single denominator that
appears in `W^(d-2) · ζ`; the divisibility `W ∣ R'(x₀, Z)_{d-1}` is captured implicitly by
Euclidean division in `F[X]`. For `R.natDegree ≤ 1`, the derivative specialization is constant
in `Y`, so we take it as the representative. -/
noncomputable def ξ_pre (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y]) : F[X][Y] :=
  let P : F[X][Y] := Bivariate.evalX (Polynomial.C x₀) R.derivative
  let d : ℕ := R.natDegree
  let W : F[X] := H.leadingCoeff
  if 2 ≤ d then
    (∑ i ∈ Finset.range (d - 1),
        Polynomial.C (P.coeff i * W ^ (d - 2 - i)) * Polynomial.X ^ i) +
      Polynomial.C (P.coeff (d - 1) / W) * Polynomial.X ^ (d - 1)
  else
    P

/-- The image of `⟦ξ_pre⟧` in the function field equals `W^(d-2) · ζ`, matching Claim A.2's
algebraic identity. -/
lemma embeddingOf𝒪Into𝕃_mk_ξ_pre (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [H_irreducible : Fact (Irreducible H)] [H_natDegree_pos : Fact (0 < H.natDegree)]
    (hHyp : Hypotheses x₀ R H) :
    embeddingOf𝒪Into𝕃 H (Ideal.Quotient.mk _ (ξ_pre x₀ R H) : 𝒪 H) =
      liftToFunctionField (H := H) H.leadingCoeff ^ (R.natDegree - 2) * ζ R x₀ H := by
  rw [embeddingOf𝒪Into𝕃_mk]
  by_cases hRle : R.natDegree ≤ 1
  · -- d ≤ 1: ξ_pre = R'(x₀, Z), constant in Y; ζ is the lift of that constant.
    rcases derivative_evalX_eq_C_of_natDegree_le_one x₀ R hRle with ⟨p, hp⟩
    have hd2 : R.natDegree - 2 = 0 := by omega
    have hbranch : ¬ 2 ≤ R.natDegree := by omega
    have hξ_pre : ξ_pre x₀ R H = Polynomial.C p := by
      simp [ξ_pre, hbranch, hp]
    rw [hξ_pre, hd2, pow_zero, one_mul, liftBivariate_C]
    change liftToFunctionField (H := H) p =
      Polynomial.eval₂ liftToFunctionField
        (functionFieldT (H := H) / liftToFunctionField (H := H) H.leadingCoeff)
        (Bivariate.evalX (Polynomial.C x₀) R.derivative)
    rw [hp, Polynomial.eval₂_C]
  · have hd2 : 2 ≤ R.natDegree := by omega
    set P : F[X][Y] := Bivariate.evalX (Polynomial.C x₀) R.derivative with hP_def
    set W_poly : F[X] := H.leadingCoeff with hW_poly_def
    have hkk : R.natDegree - 1 = R.natDegree - 2 + 1 := by omega
    have hP_le : P.natDegree ≤ R.natDegree - 2 + 1 := by
      have h1 : P.natDegree ≤ R.derivative.natDegree := evalX_natDegree_le _ R.derivative
      have h2 : R.derivative.natDegree ≤ R.natDegree - 1 := Polynomial.natDegree_derivative_le R
      omega
    have hdiv : W_poly ∣ P.coeff (R.natDegree - 2 + 1) := by
      have h := leadingCoeff_dvd_evalX_derivative_coeff_pred (H := H) hHyp
      rwa [hkk] at h
    have hW_poly_ne : W_poly ≠ 0 :=
      Polynomial.leadingCoeff_ne_zero.mpr
        (Polynomial.ne_zero_of_natDegree_gt H_natDegree_pos.out)
    have hW_ne : (liftToFunctionField (H := H) W_poly : 𝕃 H) ≠ 0 :=
      liftToFunctionField_leadingCoeff_ne_zero (H := H)
    have hξ_pre_eq : ξ_pre x₀ R H =
        (∑ i ∈ Finset.range (R.natDegree - 2 + 1),
            Polynomial.C (P.coeff i * W_poly ^ (R.natDegree - 2 - i)) * Polynomial.X ^ i) +
          Polynomial.C (P.coeff (R.natDegree - 2 + 1) / W_poly) *
            Polynomial.X ^ (R.natDegree - 2 + 1) := by
      simp only [ξ_pre, hd2, ↓reduceIte, ← hP_def, ← hW_poly_def, hkk]
    rw [hξ_pre_eq]
    rw [show (ζ R x₀ H : 𝕃 H) =
      Polynomial.eval₂ liftToFunctionField
        (functionFieldT (H := H) / liftToFunctionField (H := H) W_poly) P from rfl]
    rw [W_pow_mul_eval₂_div_eq_sum (H := H) (P := P) (k := R.natDegree - 2) hP_le]
    have hlift_div :
        liftToFunctionField (H := H) (P.coeff (R.natDegree - 2 + 1) / W_poly) =
          liftToFunctionField (H := H) (P.coeff (R.natDegree - 2 + 1)) /
            liftToFunctionField (H := H) W_poly := by
      rw [eq_div_iff hW_ne, ← map_mul, mul_comm,
          EuclideanDomain.mul_div_cancel' hW_poly_ne hdiv]
    simp only [map_add, map_sum, map_mul, map_pow, liftBivariate_C, liftBivariate_X, hlift_div]
    refine congr_arg₂ (· + ·) ?_ rfl
    refine Finset.sum_congr rfl (fun i _ => ?_)
    ring

/-- The regular element `ξ = W(Z)^(d-2) * ζ` has a quotient representative in the total Lean
form of Claim A.2 of Appendix A.4 of [BCIKS20].

For `R.natDegree < 2`, the natural-number exponent truncates to zero. The paper's weight
bound is therefore stated separately with the explicit hypothesis `2 ≤ R.natDegree`. -/
lemma ξ_regular (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y]) [H_irreducible : Fact (Irreducible H)]
    [H_natDegree_pos : Fact (0 < H.natDegree)] (hHyp : Hypotheses x₀ R H) :
    ∃ pre : 𝒪 H,
    let d := R.natDegree
    let W : 𝕃 H := liftToFunctionField (H.leadingCoeff)
    embeddingOf𝒪Into𝕃 _ pre = W ^ (d - 2) * ζ R x₀ H :=
  ⟨Ideal.Quotient.mk _ (ξ_pre x₀ R H),
    by simpa using embeddingOf𝒪Into𝕃_mk_ξ_pre x₀ R H hHyp⟩

/-- The regular element `ξ = W(Z)^(d-2) * ζ` used in the Lean version of Claim A.2.

The `Fact` and `Hypotheses` arguments are kept for API compatibility with downstream callers
(`α`, `γ`); they are needed for the embedding equation in `embeddingOf𝒪Into𝕃_ξ`. -/
noncomputable def ξ (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y]) [_φ : Fact (Irreducible H)]
    [_H_natDegree_pos : Fact (0 < H.natDegree)] (_hHyp : Hypotheses x₀ R H) : 𝒪 H :=
  Ideal.Quotient.mk _ (ξ_pre x₀ R H)

/-- The defining equation `embedding ξ = W^(d-2) · ζ`, the specialization of
`embeddingOf𝒪Into𝕃_mk_ξ_pre` to `ξ`. -/
lemma embeddingOf𝒪Into𝕃_ξ (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [H_irreducible : Fact (Irreducible H)] [H_natDegree_pos : Fact (0 < H.natDegree)]
    (hHyp : Hypotheses x₀ R H) :
    embeddingOf𝒪Into𝕃 H (ξ x₀ R H hHyp) =
      liftToFunctionField (H := H) H.leadingCoeff ^ (R.natDegree - 2) * ζ R x₀ H :=
  embeddingOf𝒪Into𝕃_mk_ξ_pre x₀ R H hHyp

/-- The bound of the weight `Λ` of the elements `ξ` as stated in Claim A.2 of Appendix A.4
of [BCIKS20].

The explicit hypothesis `2 ≤ R.natDegree` is needed because the paper uses `W^(d-2)`, while
Lean's natural-number exponent would otherwise totalize the low-degree cases by truncation. -/
lemma ξ_weight_le (x₀ : F) (hH : 0 < H.natDegree) (hHyp : Hypotheses x₀ R H)
    (hRdeg : 2 ≤ Bivariate.natDegreeY R)
    {D : ℕ} (hD_H : D ≥ Bivariate.totalDegree H)
    (hD_Rx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R)) :
    weight_Λ_over_𝒪 hH (ξ x₀ R H hHyp) D ≤
    WithBot.some ((Bivariate.natDegreeY R - 1) * (D - Bivariate.natDegreeY H + 1)) := by
  sorry

/-- The exponent of `ξ` in the denominator of the `t`-th Hensel coefficient.

The paper separates `t = 0`, where no `ξ` factor appears, from `t ≥ 1`, where the exponent is
`2*t - 1`. -/
def henselDenominatorExponent (t : ℕ) : ℕ :=
  if t = 0 then 0 else 2 * t - 1

@[simp]
lemma henselDenominatorExponent_zero : henselDenominatorExponent 0 = 0 := by
  simp [henselDenominatorExponent]

@[simp]
lemma henselDenominatorExponent_succ (t : ℕ) :
    henselDenominatorExponent (t + 1) = 2 * (t + 1) - 1 := by
  simp [henselDenominatorExponent]

/-- A total degree for the trivariate polynomial `R`, represented as a polynomial in `Y` with
bivariate coefficients in the `Z` and `X` variables. -/
def trivariateTotalDegree (R : F[X][X][Y]) : ℕ :=
  R.support.sup (fun i => Bivariate.totalDegree (R.coeff i) + i)

/-- Each coefficient of `R` is bounded by `trivariateTotalDegree R`. -/
lemma coeff_totalDegree_add_index_le_trivariateTotalDegree (R : F[X][X][Y]) {i : ℕ}
    (hi : i ∈ R.support) :
    Bivariate.totalDegree (R.coeff i) + i ≤ trivariateTotalDegree R := by
  classical
  unfold trivariateTotalDegree
  exact Finset.le_sup (f := fun i => Bivariate.totalDegree (R.coeff i) + i) hi

/-- A canonical degree bound large enough for both `H` and all coefficients of `R`. -/
def defaultDegreeBound (R : F[X][X][Y]) (H : F[X][Y]) : ℕ :=
  max (Bivariate.totalDegree H) (trivariateTotalDegree R)

lemma defaultDegreeBound_ge_H (R : F[X][X][Y]) (H : F[X][Y]) :
    Bivariate.totalDegree H ≤ defaultDegreeBound R H :=
  le_max_left _ _

lemma defaultDegreeBound_ge_R_coeff (R : F[X][X][Y]) (H : F[X][Y]) {i : ℕ}
    (hi : i ∈ R.support) :
    Bivariate.totalDegree (R.coeff i) + i ≤ defaultDegreeBound R H :=
  (coeff_totalDegree_add_index_le_trivariateTotalDegree R hi).trans (le_max_right _ _)

/-- Coefficients in `F[Z][X]` evaluated as power series over the function field: `Z` is sent to
the function-field coefficient embedding, and `X` is sent to the power-series variable. -/
noncomputable def liftCoeffToPowerSeries (H : F[X][Y]) :
    F[X][X] →+* PowerSeries (𝕃 H) :=
  Polynomial.eval₂RingHom (RingHom.comp PowerSeries.C (liftToFunctionField (H := H)))
    PowerSeries.X

/-- Evaluation of the trivariate polynomial `R(X,Y,Z)` at a power series `Γ` for the `Y`
variable, with the `X` variable interpreted as the power-series variable and `Z` interpreted in
the function field of `H`. -/
noncomputable def evalRAtPowerSeries (H : F[X][Y]) (R : F[X][X][Y])
    (Γ : PowerSeries (𝕃 H)) : PowerSeries (𝕃 H) :=
  Polynomial.eval₂ (liftCoeffToPowerSeries H) Γ R

/-- The coefficient sequence obtained from a candidate sequence of regular numerators. -/
noncomputable def alphaOfNumerators (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [φ : Fact (Irreducible H)] [H_natDegree_pos : Fact (0 < H.natDegree)]
    (hHyp : Hypotheses x₀ R H) (βseq : ℕ → 𝒪 H) (t : ℕ) : 𝕃 H :=
  let W : 𝕃 H := liftToFunctionField (H.leadingCoeff)
  embeddingOf𝒪Into𝕃 _ (βseq t) /
    (W ^ (t + 1) * (embeddingOf𝒪Into𝕃 _ (ξ x₀ R H hHyp)) ^
      henselDenominatorExponent t)

/-- The power series induced by a candidate sequence of regular numerators. -/
noncomputable def gammaOfNumerators (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [φ : Fact (Irreducible H)] [H_natDegree_pos : Fact (0 < H.natDegree)]
    (hHyp : Hypotheses x₀ R H) (βseq : ℕ → 𝒪 H) :
    PowerSeries (𝕃 H) :=
  let subst (t : ℕ) : 𝕃 H :=
    match t with
    | 0 => fieldTo𝕃 (-x₀)
    | 1 => 1
    | _ => 0
  PowerSeries.subst (PowerSeries.mk subst)
    (PowerSeries.mk (alphaOfNumerators x₀ R H hHyp βseq))

/-- A numerator sequence has the semantic content required by Claim A.2: it gives the Hensel
lift starting at `T / W`, and the induced power series is a root of `R(X,Y,Z)`. -/
def IsHenselNumeratorSequence (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [φ : Fact (Irreducible H)] [H_natDegree_pos : Fact (0 < H.natDegree)]
    (hHyp : Hypotheses x₀ R H) (βseq : ℕ → 𝒪 H) : Prop :=
  alphaOfNumerators x₀ R H hHyp βseq 0 =
      functionFieldT (H := H) / liftToFunctionField (H := H) H.leadingCoeff ∧
    evalRAtPowerSeries H R (gammaOfNumerators x₀ R H hHyp βseq) = 0

/-- There is a sequence of regular numerators `β_t` with the Hensel-lift semantics and the
weight bound stated in Claim A.2 of Appendix A.4 of [BCIKS20]. -/
lemma exists_hensel_numerator_sequence (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [_H_irreducible : Fact (Irreducible H)] [_H_natDegree_pos : Fact (0 < H.natDegree)]
    (hHyp : Hypotheses x₀ R H) (hH : 0 < H.natDegree)
    {D : ℕ} (hD_H : Bivariate.totalDegree H ≤ D)
    (hD_R : ∀ i ∈ R.support, Bivariate.totalDegree (R.coeff i) + i ≤ D) :
    ∃ βseq : ℕ → 𝒪 H,
      IsHenselNumeratorSequence x₀ R H hHyp βseq ∧
      ∀ t : ℕ,
        weight_Λ_over_𝒪 hH (βseq t) D ≤
          (WithBot.some ((2 * t + 1) * Bivariate.natDegreeY R * D) : WithBot ℕ) := by
  sorry

/-- The chosen regular numerator sequence supplied by `exists_hensel_numerator_sequence`. -/
noncomputable def βSeq (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [φ : Fact (Irreducible H)] [H_natDegree_pos : Fact (0 < H.natDegree)]
    (hHyp : Hypotheses x₀ R H) : ℕ → 𝒪 H :=
  if hH : 0 < H.natDegree then
    (exists_hensel_numerator_sequence x₀ R H hHyp hH
      (defaultDegreeBound_ge_H R H) (fun _ hi => defaultDegreeBound_ge_R_coeff R H hi)).choose
  else
    fun _ => 0

/-- The specification satisfied by the chosen numerator sequence. -/
lemma βSeq_spec (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [φ : Fact (Irreducible H)] [H_natDegree_pos : Fact (0 < H.natDegree)]
    (hHyp : Hypotheses x₀ R H) (hH : 0 < H.natDegree) :
    IsHenselNumeratorSequence x₀ R H hHyp (βSeq x₀ R H hHyp) ∧
      ∀ t : ℕ,
        weight_Λ_over_𝒪 hH ((βSeq x₀ R H hHyp) t) (defaultDegreeBound R H) ≤
          (WithBot.some ((2 * t + 1) * Bivariate.natDegreeY R * defaultDegreeBound R H) :
            WithBot ℕ) := by
  unfold βSeq
  rw [dif_pos hH]
  exact (exists_hensel_numerator_sequence x₀ R H hHyp hH
    (defaultDegreeBound_ge_H R H) (fun _ hi => defaultDegreeBound_ge_R_coeff R H hi)).choose_spec

/-- The regular element `β_t` giving the numerator of the `t`-th chosen Hensel coefficient. -/
noncomputable def β (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [φ : Fact (Irreducible H)] [H_natDegree_pos : Fact (0 < H.natDegree)]
    (hHyp : Hypotheses x₀ R H) (t : ℕ) : 𝒪 H :=
  βSeq x₀ R H hHyp t

/-- The chosen Hensel-lift coefficients induced by the regular numerator sequence. -/
def α (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y]) [φ : Fact (Irreducible H)]
    [H_natDegree_pos : Fact (0 < H.natDegree)] (hHyp : Hypotheses x₀ R H) (t : ℕ) : 𝕃 H :=
  alphaOfNumerators x₀ R H hHyp (βSeq x₀ R H hHyp) t

/-- Variant of `α` taking explicit irreducibility and positive-degree hypotheses. -/
def α' (x₀ : F) (R : F[X][X][Y]) (H_irreducible : Irreducible H)
    (hHdeg : 0 < H.natDegree) (hHyp : Hypotheses x₀ R H) (t : ℕ) : 𝕃 H :=
  α x₀ R _ (φ := ⟨H_irreducible⟩) (H_natDegree_pos := ⟨hHdeg⟩) hHyp t

/-- The chosen power series `γ = ∑ α_t (X - x₀)^t`, induced by the selected regular numerator
sequence from `exists_hensel_numerator_sequence`. -/
def γ (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y]) [φ : Fact (Irreducible H)]
    [H_natDegree_pos : Fact (0 < H.natDegree)] (hHyp : Hypotheses x₀ R H) :
    PowerSeries (𝕃 H) :=
  gammaOfNumerators x₀ R H hHyp (βSeq x₀ R H hHyp)

/-- Variant of `γ` taking explicit irreducibility and positive-degree hypotheses. -/
def γ' (x₀ : F) (R : F[X][X][Y]) (H_irreducible : Irreducible H)
    (hHdeg : 0 < H.natDegree) (hHyp : Hypotheses x₀ R H) : PowerSeries (𝕃 H) :=
  γ x₀ R H (φ := ⟨H_irreducible⟩) (H_natDegree_pos := ⟨hHdeg⟩) hHyp

end ClaimA2
end
end BCIKS20AppendixA

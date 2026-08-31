/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Katerina Hristova, František Silváši, Julian Sutherland, Ilia Vlasov
-/

import ArkLib.Data.Polynomial.Bivariate
import ArkLib.Data.Polynomial.Prelims
import Mathlib.RingTheory.Polynomial.GaussLemma

/-!
# The Algebraic Extension and its Regular Elements

Appendix A.1 of [BCIKS20]: the monicization `H̃` of an irreducible `H ∈ F[Z][Y]`, the function
field `𝕃 H = F(Z)[T]/(H̃)`, its ring of regular elements `𝒪 H = F[Z][T]/(H̃)`, the embedding
`𝒪 H ↪ 𝕃 H`, canonical representatives of degree `< deg_Y H`, and the rational substitutions
`π_z : 𝒪 H →+* F` of Appendix A.3.

## References

[BCIKS20] Eli Ben-Sasson, Dan Carmon, Yuval Ishai, Swastik Kopparty, and Shubhangi Saraf.
  Proximity gaps for Reed-Solomon codes. In 2020 IEEE 61st Annual Symposium on Foundations of
  Computer Science (FOCS), 2020. Full paper: https://eprint.iacr.org/2020/654,
  version 20210703:203025.

-/


open Polynomial Polynomial.Bivariate ToRatFunc Ideal

namespace RationalFunctions

section Monicization

variable {F : Type} [CommRing F] [IsDomain F]

/-- The monicization of `H` over the fraction field: `H̃ = W^{d-1} · H(T/W)` where `d = deg_Y H`
and `W` is its leading coefficient.  Substituting `T/W` for `Y` makes the result monic, and the
factor `W^{d-1}` clears the denominators this introduces, so `H̃ ∈ F(Z)[T]` is monic of degree `d`
and generates the same extension of `F(Z)` as `H`. -/
noncomputable def monicizeRatFunc (H : F[X][Y]) : Polynomial (RatFunc F) :=
  let hᵢ (i : ℕ) := H.coeff i
  let d := H.natDegree
  let W := (RingHom.comp Polynomial.C univPolyHom) (hᵢ d)
  let S : Polynomial (RatFunc F) := Polynomial.X / W
  let H' := Polynomial.eval₂ (RingHom.comp Polynomial.C univPolyHom) S H
  W ^ (d - 1) * H'

/-- The defining formula for `monicizeRatFunc`, stated as a rewrite lemma so clients need not
unfold its implementation-local `let` bindings. -/
lemma monicizeRatFunc_eq (H : F[X][Y]) :
    monicizeRatFunc H =
      Polynomial.C (univPolyHom (F := F) H.leadingCoeff) ^ (H.natDegree - 1) *
        Polynomial.eval₂ (RingHom.comp Polynomial.C (univPolyHom (F := F)))
          (Polynomial.X / Polynomial.C (univPolyHom (F := F) H.leadingCoeff)) H := by
  rfl

section FieldIrreducibility

variable {F : Type} [Field F]

/-- The embedding `F[Z] → F(Z)` of a domain into its fraction field is injective. -/
lemma univPolyHom_injective :
    Function.Injective (univPolyHom (F := F)) := by
  simpa [ToRatFunc.univPolyHom] using (RatFunc.algebraMap_injective (K := F))

private lemma irreducible_comp_C_mul_X_iff {K : Type} [Field K] (a : K) (ha : a ≠ 0)
    (p : K[X]) :
    Irreducible (p.comp (Polynomial.C a * Polynomial.X)) ↔ Irreducible p := by
  let : Invertible a := invertibleOfNonzero ha
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

/-- Corrected irreducibility statement for `monicizeRatFunc`: the paper assumes positive `Y`-degree.
Without this hypothesis, a constant irreducible in `F[Z][Y]` can become a unit in `F(Z)[T]`. -/
lemma irreducible_monicizeRatFunc_of_natDegree_pos
    {H : Polynomial (Polynomial F)} (hdeg : 0 < H.natDegree)
    (hH : Irreducible H) :
    Irreducible (monicizeRatFunc H) := by
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
      monicizeRatFunc H =
        W ^ (d - 1) *
          Polynomial.eval₂ (RingHom.comp Polynomial.C (univPolyHom (F := F))) (Polynomial.X / W)
            H := by
    rfl
  rw [htilde, ← hu]
  exact (irreducible_units_mul (M := Polynomial (RatFunc F)) (u := u)).2 heval_irreducible

end FieldIrreducibility

/-- Monicization preserves irreducibility, for `H` of positive `Y`-degree. -/
lemma irreducible_monicizeRatFunc {F : Type} [Field F] {H : Polynomial (Polynomial F)}
    (hHdeg : 0 < H.natDegree) :
    Irreducible H → Irreducible (monicizeRatFunc H) :=
  irreducible_monicizeRatFunc_of_natDegree_pos hHdeg

/-- The function field `𝕃 H = F(Z)[T]/(H̃)`, obtained by adjoining a root of `H` to `F(Z)`.  The
root is `Y = T/W`; see `H_eval2_T_div_W_eq_zero`. -/
abbrev 𝕃 (H : F[X][Y]) : Type :=
  (Polynomial (RatFunc F)) ⧸ (Ideal.span {monicizeRatFunc H})

/-- The function field `𝕃` is a field when `H` is irreducible and has positive `Y`-degree. -/
lemma isField_of_irreducible_of_natDegree_pos {F : Type} [Field F] {H : F[X][Y]}
    (hHdeg : 0 < H.natDegree) (hH : Irreducible H) : IsField (𝕃 H) := by
  unfold 𝕃
  erw [← Ideal.Quotient.maximal_ideal_iff_isField_quotient, principal_is_maximal_iff_irred]
  exact irreducible_monicizeRatFunc_of_natDegree_pos hHdeg hH

/-- `𝕃 H` is a field when `H` is irreducible of positive `Y`-degree. -/
lemma isField_of_irreducible {F : Type} [Field F] {H : F[X][Y]} (hHdeg : 0 < H.natDegree) :
    Irreducible H → IsField (𝕃 H) := by
  intro h
  unfold 𝕃
  erw [← Ideal.Quotient.maximal_ideal_iff_isField_quotient, principal_is_maximal_iff_irred]
  exact irreducible_monicizeRatFunc hHdeg h

/-- The function field `𝕃` is a field under positive-degree irreducibility assumptions. -/
noncomputable instance {F : Type} [Field F] {H : F[X][Y]} [hHdeg : Fact (0 < H.natDegree)]
    [inst : Fact (Irreducible H)] : Field (𝕃 H) :=
  IsField.toField (isField_of_irreducible hHdeg.out inst.out)

/-- The integral monicized polynomial corresponding to `monicizeRatFunc`, with coefficients
in `F[X]`. -/
noncomputable def monicize (H : F[X][Y]) : F[X][Y] :=
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
/-- If `H` has positive degree in `Y`, then `monicize H` is monic. -/
lemma monicize_monic (H : F[X][Y]) (hH : 0 < H.natDegree) :
    (monicize H).Monic := by
  classical
  have hdeg : H.natDegree ≠ 0 := Nat.ne_of_gt hH
  rw [monicize, if_neg hdeg]
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

/-- The polynomial `monicize` agrees with the monicization `monicizeRatFunc` after embedding into
`Polynomial (RatFunc F)`. -/
lemma map_monicize_eq_monicizeRatFunc (H : F[X][Y]) : (monicize H).map univPolyHom = monicizeRatFunc
    H := by
  classical
  by_cases hdeg : H.natDegree = 0
  · simp only [monicize, hdeg, ↓reduceIte, map_C]
    have hconst : H = Polynomial.C (H.coeff 0) := Polynomial.eq_C_of_natDegree_le_zero (by omega)
    rw [hconst, monicizeRatFunc]
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
    simp only [monicize, hdeg, ↓reduceIte, coeff_natDegree, map_mul, map_pow,
      Polynomial.map_add, Polynomial.map_pow, map_X]
    rw [monicizeRatFunc, hEval, Finset.sum_range_succ, mul_add, Finset.mul_sum, Polynomial.map_sum]
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

/-- The integral monicized polynomial `monicize` is irreducible whenever `H` is irreducible and has
positive degree in `Y`. -/
lemma irreducible_monicize {H : F[X][Y]} (hHdeg : 0 < H.natDegree)
    (hH : Irreducible H) :
    Irreducible (monicize H) := by
  have hmap : Irreducible ((monicize H).map (univPolyHom (F := F))) := by
    simpa [map_monicize_eq_monicizeRatFunc] using
      irreducible_monicizeRatFunc_of_natDegree_pos hHdeg hH
  exact (monicize_monic H hHdeg).isPrimitive.irreducible_of_irreducible_map_of_injective
    (univPolyHom_injective (F := F)) hmap

end IntegralIrreducibility

/-- The ring of regular elements `𝒪 H = F[Z][T]/(H̃)`: the elements of `𝕃 H` expressible as
polynomials in `T` with coefficients in `F[Z]` rather than in `F(Z)`. -/
abbrev 𝒪 (H : F[X][Y]) : Type :=
  (Polynomial (Polynomial F)) ⧸ (Ideal.span {monicize H})

/-- The ring of regular elements `𝒪` is a ring. -/
noncomputable instance {H : F[X][Y]} : Ring (𝒪 H) :=
  Ideal.Quotient.ring (Ideal.span {monicize H})

/-- The ring homomorphism defining the embedding of `𝒪` into `𝕃`. -/
noncomputable def embeddingOf𝒪Into𝕃 (H : F[X][Y]) : 𝒪 H →+* 𝕃 H :=
  Ideal.quotientMap
    (I := Ideal.span {monicize H}) (Ideal.span {monicizeRatFunc H})
    bivPolyHom (by
      rw [Ideal.span_le]
      intro x hx
      rw [Set.mem_singleton_iff] at hx
      subst hx
      change bivPolyHom (monicize H) ∈ span {monicizeRatFunc H}
      rw [show bivPolyHom (monicize H) = (monicize H).map univPolyHom from rfl,
        map_monicize_eq_monicizeRatFunc]
      exact Ideal.subset_span rfl)

section FieldEmbedding

variable {F : Type} [Field F]

/-- Divisibility by the monicization descends from `F(Z)[T]` to `F[Z][T]`: if `monicizeRatFunc H`
divides the image of `p`, then `monicize H` already divides `p`.  This is what makes
`embeddingOf𝒪Into𝕃` injective. -/
lemma monicize_dvd_of_map_dvd_monicizeRatFunc {H p : F[X][Y]} (hHdeg : 0 < H.natDegree)
    (hp : monicizeRatFunc H ∣ p.map (univPolyHom (F := F))) :
    monicize H ∣ p := by
  let q : F[X][Y] := monicize H
  have hqmonic : q.Monic := monicize_monic H hHdeg
  rw [← Polynomial.modByMonic_eq_zero_iff_dvd hqmonic]
  rw [← Polynomial.map_eq_zero_iff (univPolyHom_injective (F := F))]
  have hqmap_dvd_p : q.map (univPolyHom (F := F)) ∣ p.map (univPolyHom (F := F)) := by
    simpa [q, map_monicize_eq_monicizeRatFunc] using hp
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

private lemma mem_span_monicize_of_bivPolyHom_mem_span_monicizeRatFunc {H p : F[X][Y]}
    (hHdeg : 0 < H.natDegree)
    (hp : bivPolyHom p ∈ Ideal.span {monicizeRatFunc H}) :
    p ∈ Ideal.span {monicize H} := by
  rw [Ideal.mem_span_singleton] at hp ⊢
  exact monicize_dvd_of_map_dvd_monicizeRatFunc hHdeg (by
    simpa [show bivPolyHom p = p.map (univPolyHom (F := F)) from rfl] using hp)

/-- The regular quotient embeds injectively into the function-field quotient when `H` has positive
degree in `Y`. -/
lemma embeddingOf𝒪Into𝕃_injective {H : F[X][Y]} (hHdeg : 0 < H.natDegree) :
    Function.Injective (embeddingOf𝒪Into𝕃 H) := by
  unfold embeddingOf𝒪Into𝕃
  apply Ideal.quotientMap_injective'
  intro p hp
  exact mem_span_monicize_of_bivPolyHom_mem_span_monicizeRatFunc hHdeg hp

end FieldEmbedding

/-- The set of regular elements inside `𝕃 H`, i.e. the set of elements of `𝕃 H`
that in fact lie in `𝒪 H`. -/
def regularElementsSet (H : F[X][Y]) : Set (𝕃 H) :=
  {a : 𝕃 H | ∃ b : 𝒪 H, a = embeddingOf𝒪Into𝕃 _ b}


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

/-- Finite products of regular elements are regular. -/
lemma regularElementsSet_prod {ι : Type} {H : F[X][Y]} (s : Finset ι) {f : ι → 𝕃 H}
    (hf : ∀ i ∈ s, f i ∈ regularElementsSet H) :
    (∏ i ∈ s, f i) ∈ regularElementsSet H := by
  classical
  revert hf
  refine Finset.induction_on s ?_ ?_
  · intro _hf
    simp
  · intro a s ha ih hf
    rw [Finset.prod_insert ha]
    exact regularElementsSet_mul
      (hf a (by simp [ha]))
      (ih fun i hi => hf i (by simp [hi]))

/-- Given an element `z ∈ F`, `t_z ∈ F` is a rational root of a bivariate polynomial if the pair
`(z, t_z)` is a root of the bivariate polynomial. -/
def rationalRoot (H : F[X][Y]) (z : F) : Type :=
  {t_z : F // evalEval z t_z H = 0}

/-- The substitution `Z ↦ z`, `T ↦ t_z` on the whole polynomial ring, before descending to the
quotient. -/
noncomputable def piZLift {H : F[X][Y]} (z : F) (root : rationalRoot (monicize H) z) :
    F[X][Y] →+* F :=
  Polynomial.evalEvalRingHom z root.1

/-- The substitution `Z ↦ z`, `T ↦ t_z` as a ring homomorphism `𝒪 H →+* F`.  It descends to the
quotient because `(t_z, z)` is a root of `H̃`, so `H̃` lies in the kernel.  This is the analogue for
`𝒪 H` of evaluating a rational function at `Z = z`. -/
noncomputable def piZ {H : F[X][Y]} (z : F) (root : rationalRoot (monicize H) z) :
    𝒪 H →+* F :=
  Ideal.Quotient.lift (Ideal.span {monicize H}) (piZLift z root) (by
    intro a ha
    rw [Ideal.mem_span_singleton] at ha
    obtain ⟨c, rfl⟩ := ha
    simp only [piZLift, map_mul]
    rw [show (Polynomial.evalEvalRingHom z root.1) (monicize H) = 0 from root.2]
    ring)

/-- The canonical representative of an element of `F[X][Y]` inside the ring of regular elements
`𝒪`, defined when `H` has positive degree in `Y`. -/
noncomputable def canonicalRepOf𝒪 {H : F[X][Y]} (hH : 0 < H.natDegree) (β : 𝒪 H) : F[X][Y] :=
  let _hHt := monicize_monic H hH
  Polynomial.modByMonic β.out (monicize H)

/-- The canonical representative has degree strictly smaller than the defining relation. -/
lemma canonicalRepOf𝒪_degree_lt {H : F[X][Y]} (hH : 0 < H.natDegree) (β : 𝒪 H) :
    (canonicalRepOf𝒪 hH β).degree < (monicize H).degree := by
  rw [canonicalRepOf𝒪]
  exact Polynomial.degree_modByMonic_lt _ (monicize_monic H hH)


omit [IsDomain F] in
/-- The canonical representative maps back to the original quotient element of `𝒪`. -/
@[simp]
lemma mk_canonicalRepOf𝒪 {H : F[X][Y]} (hH : 0 < H.natDegree) (β : 𝒪 H) :
    Ideal.Quotient.mk (Ideal.span {monicize H}) (canonicalRepOf𝒪 hH β) = β := by
  let I : Ideal F[X][Y] := Ideal.span {monicize H}
  let q : F[X][Y] := monicize H
  let p : F[X][Y] := β.out
  have hq_zero : Ideal.Quotient.mk I (q * (p /ₘ q)) = 0 := by
    rw [Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)
  calc
    Ideal.Quotient.mk (Ideal.span {monicize H}) (canonicalRepOf𝒪 hH β)
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
    canonicalRepOf𝒪 hH (Ideal.Quotient.mk (Ideal.span {monicize H}) p : 𝒪 H) =
      p %ₘ monicize H := by
  apply Polynomial.modByMonic_eq_of_dvd_sub (monicize_monic H hH)
  rw [← Ideal.mem_span_singleton]
  rw [← Ideal.Quotient.mk_eq_mk_iff_sub_mem]
  calc
    Ideal.Quotient.mk (Ideal.span {monicize H})
        ((Ideal.Quotient.mk (Ideal.span {monicize H}) p : 𝒪 H).out)
        = (Ideal.Quotient.mk (Ideal.span {monicize H}) p : 𝒪 H) := by simp
    _ = Ideal.Quotient.mk (Ideal.span {monicize H}) p := rfl

omit [IsDomain F] in
/-- The canonical representative of zero is zero. -/
@[simp]
lemma canonicalRepOf𝒪_zero {H : F[X][Y]} (hH : 0 < H.natDegree) :
    canonicalRepOf𝒪 hH (0 : 𝒪 H) = 0 := by
  simpa using (canonicalRepOf𝒪_mk (H := H) hH 0)

/-- A polynomial whose degree is already below the relation is its own canonical representative. -/
lemma canonicalRepOf𝒪_mk_eq_self_of_degree_lt {H : F[X][Y]} (hH : 0 < H.natDegree)
    {p : F[X][Y]} (hp : p.degree < (monicize H).degree) :
    canonicalRepOf𝒪 hH (Ideal.Quotient.mk (Ideal.span {monicize H}) p : 𝒪 H) = p := by
  rw [canonicalRepOf𝒪_mk]
  exact (Polynomial.modByMonic_eq_self_iff (monicize_monic H hH)).2 hp


end Monicization
end RationalFunctions

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

import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Roots
import ArkLib.Data.Polynomial.RationalFunctions.Weight
/-!
# Vanishing of Regular Elements

Appendix A.3 of [BCIKS20], Lemma A.1: a regular `β ∈ 𝒪 H` that vanishes under more than
`deg_Y H · Λ(β)` rational substitutions `π_z` is zero in `𝕃 H`. Proved along the paper's route,
via the resultant `res_T(β, H̃)` and a Sylvester-matrix degree bound.

## References

[BCIKS20] Eli Ben-Sasson, Dan Carmon, Yuval Ishai, Swastik Kopparty, and Shubhangi Saraf.
  Proximity gaps for Reed-Solomon codes. In 2020 IEEE 61st Annual Symposium on Foundations of
  Computer Science (FOCS), 2020. Full paper: https://eprint.iacr.org/2020/654,
  version 20210703:203025.

-/


open Polynomial Polynomial.Bivariate ToRatFunc Ideal

namespace RationalFunctions
section RationalRootVanishing

variable {F : Type} [Field F]

/-- Every monomial of `H̃` has `Λ`-weight at most `dH·(D + 1 - dH)`, in the unpacked form used by
the Sylvester-matrix degree count below.  Restatement of `weight_monicize_le`. -/
theorem natDegree_coeff_monicize_le_of_totalDegree_le {H : F[X][Y]} {D : ℕ}
    (hD : Bivariate.totalDegree H ≤ D)
    (hH : 0 < H.natDegree) {j : ℕ}
    (hj : j ∈ (monicize H).support) :
  j * (D + 1 - Bivariate.natDegreeY H) +
    ((monicize H).coeff j).natDegree ≤
      H.natDegree * (D + 1 - Bivariate.natDegreeY H) := by
  exact (weight_le_iff.mp (weight_monicize_le hD hH)) j hj

/-- A weight bound on `β` read off monomial-by-monomial on its canonical representative: each
monomial `Tⁱ · (coeff i)` obeys `i·(D + 1 - dH) + deg_Z (coeff i) ≤ B`. -/
theorem canonicalRep_coeff_natDegree_le_of_weight_bound {H : F[X][Y]} (hH : 0 < H.natDegree)
    {D B : ℕ} (β : 𝒪 H)
    (hβw : regularWeight hH β D ≤ (WithBot.some B : WithBot ℕ))
    {i : ℕ} (hi : i ∈ (canonicalRepOf𝒪 hH β).support) :
  i * (D + 1 - Bivariate.natDegreeY H) +
    ((canonicalRepOf𝒪 hH β).coeff i).natDegree ≤ B := by
  unfold regularWeight at hβw
  exact (weight_le_iff.mp hβw) i hi

/-- If the resultant `res_T(β, H̃)` vanishes then `β` is zero in `𝕃`.  A vanishing resultant makes
the canonical representative and `H̃` non-coprime; irreducibility of `H̃` and the degree bound
`deg_T β < deg_T H̃` then force `β = 0`.  This is the last step of the vanishing criterion. -/
theorem embedding_eq_zero_of_resultant_zero {H : F[X][Y]} [Fact (Irreducible H)]
    (hH : 0 < H.natDegree) (β : 𝒪 H)
    (hres : Polynomial.resultant (canonicalRepOf𝒪 hH β) (monicize H) = 0) :
  embeddingOf𝒪Into𝕃 H β = 0 := by
  classical
  let p : F[X][Y] := canonicalRepOf𝒪 hH β
  have hres_map : Polynomial.resultant (p.map (univPolyHom (F := F))) (monicizeRatFunc H) = 0 := by
    have h := congrArg (univPolyHom (F := F)) hres
    rw [← Polynomial.resultant_map_map (p) (monicize H) p.natDegree (monicize H).natDegree
          (univPolyHom (F := F))] at h
    rw [map_monicize_eq_monicizeRatFunc H] at h
    have hn : (monicizeRatFunc H).natDegree = (monicize H).natDegree := by
      rw [← map_monicize_eq_monicizeRatFunc H]
      exact Polynomial.natDegree_map_eq_of_injective (univPolyHom_injective (F := F)) (monicize H)
    simpa only
        [p, Polynomial.natDegree_map_eq_of_injective (univPolyHom_injective (F := F)), map_zero, hn]
            using h
  have hnot_coprime : ¬ IsCoprime (p.map (univPolyHom (F := F))) (monicizeRatFunc H) := by
    exact (Polynomial.resultant_eq_zero_iff.mp hres_map).2
  have hHT_irred : Irreducible (monicizeRatFunc H) :=
    irreducible_monicizeRatFunc_of_natDegree_pos hH (Fact.out)
  have hdvd_map : monicizeRatFunc H ∣ p.map (univPolyHom (F := F)) := by
    exact (Irreducible.dvd_iff_not_isCoprime hHT_irred).2 (by
      intro hc
      exact hnot_coprime hc.symm)
  have hdvd : monicize H ∣ p := monicize_dvd_of_map_dvd_monicizeRatFunc hH hdvd_map
  have hp_zero : p = 0 := by
    by_contra hp_ne
    have hdegp : p.natDegree < (monicize H).natDegree := by
      simpa only [p, natDegree_monicize hH] using canonicalRepOf𝒪_natDegree_lt_H hH β
    exact (Polynomial.not_dvd_of_natDegree_lt (p := monicize H) (q := p) hp_ne hdegp) hdvd
  rw [← mk_canonicalRepOf𝒪 hH β]
  change embeddingOf𝒪Into𝕃 H (Ideal.Quotient.mk (Ideal.span {monicize H}) p : 𝒪 H) = 0
  rw [hp_zero]
  simp

/-- A determinant has degree at most `N` as soon as every permutation product does, since the
Leibniz expansion is a sum of such products. -/
theorem natDegree_det_le_of_perm_products_le {ι : Type} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι F[X]) {N : ℕ}
    (h : ∀ σ : Equiv.Perm ι, (∏ i : ι, M (σ i) i).natDegree ≤ N) :
  M.det.natDegree ≤ N := by
  classical
  rw [Matrix.det_apply']
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro σ hσ
  exact le_trans (Polynomial.natDegree_C_mul_le ((Equiv.Perm.sign σ : ℤ) : F) (∏ i : ι, M (σ i) i))
      (h σ)

/-- The degree count behind the vanishing criterion: `deg_Z res_T(β, H̃) ≤ Λ(β)·dH`.  Proved from
the Sylvester matrix, bounding each permutation product by summing the weight budgets of the
`β`-rows and the `H̃`-rows. -/
theorem natDegree_resultant_le_weight_bound {H : F[X][Y]} (hH : 0 < H.natDegree) {D B : ℕ}
    (hD : Bivariate.totalDegree H ≤ D) (β : 𝒪 H)
    (hβw : regularWeight hH β D ≤ (WithBot.some B : WithBot ℕ)) :
  (Polynomial.resultant (canonicalRepOf𝒪 hH β) (monicize H)).natDegree ≤ B * H.natDegree := by
  classical
  set p : F[X][Y] := canonicalRepOf𝒪 hH β
  set q : F[X][Y] := monicize H
  set e : ℕ := p.natDegree
  set d : ℕ := H.natDegree
  set lam : ℕ := D + 1 - Bivariate.natDegreeY H
  have hqdeg : q.natDegree = d := by
    simpa [q, d] using natDegree_monicize (H := H) hH
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
        simp [hentry, hc]
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
        simp [hentry, hc]
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
      have hbound := natDegree_coeff_monicize_le_of_totalDegree_le (F := F) (H := H) (D := D) hD
          hH (j := (((σ (Fin.castAdd d j) : Fin (e + d)) : ℕ) - (j : ℕ))) (by simpa [q] using hsup)
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
      have hbound := canonicalRep_coeff_natDegree_le_of_weight_bound (F := F) (H := H) hH β hβw
          (i := (((σ (Fin.natAdd e j) : Fin (e + d)) : ℕ) - (j : ℕ))) (by simpa [p] using hsup)
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
      have hperm_sum :
          (∑ i : Fin (e + d), ((σ i : Fin (e + d)) : ℕ)) = ∑ i : Fin (e + d), (i : ℕ) := by
        simpa using (Equiv.sum_comp σ (fun i : Fin (e + d) => (i : ℕ)))
      have hrows_split : (∑ i : Fin (e + d), ((σ i : Fin (e + d)) : ℕ)) =
          (∑ j : Fin e, ((σ (Fin.castAdd d j) : Fin (e + d)) : ℕ)) +
          (∑ j : Fin d, ((σ (Fin.natAdd e j) : Fin (e + d)) : ℕ)) := by
        simpa using (Fin.sum_univ_add (fun i : Fin (e + d) => ((σ i : Fin (e + d)) : ℕ)))
      have hcols_split : (∑ i : Fin (e + d), (i : ℕ)) =
          (∑ j : Fin e, (j : ℕ)) + (∑ j : Fin d, (e + (j : ℕ))) := by
        simpa using (Fin.sum_univ_add (fun i : Fin (e + d) => (i : ℕ)))
      have hright_cols : (∑ j : Fin d, (e + (j : ℕ))) = d * e + ∑ j : Fin d, (j : ℕ) := by
        simp [Finset.sum_add_distrib, Finset.sum_const]
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
      have hleft_expand :
          (∑ j : Fin e, (lidx j * lam + ldeg j)) =
            (∑ j : Fin e, lidx j) * lam + ∑ j : Fin e, ldeg j := by
        rw [Finset.sum_add_distrib]
        rw [← Finset.sum_mul]
      have hright_expand : (∑ j : Fin d, (ridx j * lam + rdeg j)) = (∑ j : Fin d, ridx j) * lam + ∑
          j : Fin d, rdeg j := by
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
      simpa only [ldeg, rdeg] using
          (Fin.sum_univ_add (fun i : Fin (e + d) => (M (σ i) i).natDegree))
    calc
      (∏ i : Fin (e + d), M (σ i) i).natDegree ≤
          ∑ i : Fin (e + d), (M (σ i) i).natDegree := by
            simpa using
                (Polynomial.natDegree_prod_le (s := Finset.univ)
                    (f := fun i : Fin (e + d) => M (σ i) i))
      _ = (∑ j : Fin e, ldeg j) + (∑ j : Fin d, rdeg j) := hsum_deg_split
      _ ≤ B * d := by simpa [Nat.mul_comm] using hdeg_parts

/-- A univariate polynomial of degree at most `N` with more than `N` roots is zero. -/
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

/-- Evaluating a resultant at `Z = z` is the fixed-degree resultant of the evaluated polynomials.
The degrees must be fixed to the *original* ones, since evaluation can drop degree. -/
theorem resultant_eval_eq_resultant_map_eval_fixed_degrees (p q : F[X][Y]) (z : F) :
    (Polynomial.resultant p q).eval z =
      Polynomial.resultant (p.map (Polynomial.evalRingHom z))
        (q.map (Polynomial.evalRingHom z)) p.natDegree q.natDegree := by
  exact (Polynomial.resultant_map_map p q p.natDegree q.natDegree (Polynomial.evalRingHom z)).symm

/-- The fixed-degree resultant of two polynomials with a common root vanishes, when the right
factor is monic of the declared degree. -/
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

/-- Every substitution killing `β` is a root of `res_T(β, H̃)`: at such a `z`, the pair `(t_z, z)`
is a common root of `β` and `H̃`, so the specialized resultant vanishes. -/
theorem rationalVanishingSet_subset_resultant_roots {H : F[X][Y]} (hH : 0 < H.natDegree)
    (β : 𝒪 H) :
    rationalVanishingSet β ⊆
      {z | (Polynomial.resultant (canonicalRepOf𝒪 hH β) (monicize H)).eval z = 0} := by
  intro z hz
  rcases hz with ⟨root, hβ⟩
  let p : F[X][Y] := canonicalRepOf𝒪 hH β
  let q : F[X][Y] := monicize H
  have hp : (p.map (Polynomial.evalRingHom z)).eval root.1 = 0 := by
    have h := piZ_eq_eval_canonicalRepOf𝒪 hH z root β
    rw [h] at hβ
    rw [Polynomial.map_evalRingHom_eval]
    simpa [p, Polynomial.coe_evalEvalRingHom] using hβ
  have hq : (q.map (Polynomial.evalRingHom z)).eval root.1 = 0 := by
    rw [Polynomial.map_evalRingHom_eval]
    exact root.2
  have hqmonic : (q.map (Polynomial.evalRingHom z)).Monic := by
    exact (monicize_monic H hH).map (Polynomial.evalRingHom z)
  have hn : (q.map (Polynomial.evalRingHom z)).natDegree = q.natDegree := by
    exact (monicize_monic H hH).natDegree_map (Polynomial.evalRingHom z)
  have hres : Polynomial.resultant (p.map (Polynomial.evalRingHom z))
      (q.map (Polynomial.evalRingHom z)) p.natDegree q.natDegree = 0 := by
    exact resultant_fixed_degree_eq_zero_of_common_root_of_monic_right
      (Polynomial.natDegree_map_le (f := Polynomial.evalRingHom z) (p := p)) hqmonic hn hp hq
  change (Polynomial.resultant p q).eval z = 0
  rw [resultant_eval_eq_resultant_map_eval_fixed_degrees]
  exact hres

/-- Weight `⊥` means the canonical representative is the zero polynomial, hence `β = 0` in `𝕃`.
This is the degenerate branch of the vanishing criterion. -/
theorem embedding_eq_zero_of_weight_eq_bot {H : F[X][Y]} (hH : 0 < H.natDegree) (β : 𝒪 H) (D : ℕ)
    (hw : regularWeight hH β D = ⊥) :
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
    have hle :
        (WithBot.some (n * (D + 1 - Bivariate.natDegreeY H) + (p.coeff n).natDegree) : WithBot ℕ) ≤
            weight p H D :=
      le_weight_of_mem_support hn
    have hle_bot :
        (WithBot.some (n * (D + 1 - Bivariate.natDegreeY H) + (p.coeff n).natDegree) : WithBot ℕ) ≤
            (⊥ : WithBot ℕ) := by
      exact hle.trans (by simpa [p, regularWeight] using le_of_eq hw)
    exact (not_le_of_gt (WithBot.bot_lt_coe _)) hle_bot
  rw [← mk_canonicalRepOf𝒪 hH β]
  change embeddingOf𝒪Into𝕃 H (Ideal.Quotient.mk (Ideal.span {monicize H}) p : 𝒪 H) = 0
  rw [hp]
  simp


/-- **A regular element with too many vanishing substitutions is zero.**  If `β ∈ 𝒪 H` satisfies
`π_z β = 0` for more than `Λ(β) · deg_Y H` values of `z`, then `β = 0` in `𝕃 H`.

This is the analogue for `𝒪 H` of "a polynomial of degree `≤ n` with more than `n` roots is zero",
and the reason `Λ` is worth tracking at all: every weight bound on a regular element converts into
a bound on the number of substitutions that can kill it.  Proved via the resultant `res_T(β, H̃)`,
whose `Z`-degree is at most `Λ(β) · deg_Y H` and which vanishes at every such `z`. -/
lemma embedding_eq_zero_of_many_rational_roots {H : F[X][Y]}
    [hHirreducible : Fact (Irreducible H)]
    (hH : 0 < H.natDegree) (β : 𝒪 H) (D : ℕ)
    (hD : D ≥ Bivariate.totalDegree H)
    (hncard : Set.ncard (rationalVanishingSet β) > (regularWeight hH β D) * H.natDegree) :
  embeddingOf𝒪Into𝕃 _ β = 0 := by
  classical
  set R : F[X] := Polynomial.resultant (canonicalRepOf𝒪 hH β) (monicize H)
  cases hweight : regularWeight hH β D with
  | bot =>
      exact embedding_eq_zero_of_weight_eq_bot hH β D hweight
  | coe B =>
      have hβw : regularWeight hH β D ≤ (WithBot.some B : WithBot ℕ) := by
        rw [hweight]
      have hdeg : R.natDegree ≤ B * H.natDegree := by
        dsimp [R]
        exact natDegree_resultant_le_weight_bound hH hD β hβw
      have hcard : Set.ncard (rationalVanishingSet β) > B * H.natDegree := by
        rw [hweight] at hncard
        change ((B * H.natDegree : ℕ) : WithBot ℕ) <
            ((Set.ncard (rationalVanishingSet β) : ℕ) : WithBot ℕ) at hncard
        exact WithBot.coe_lt_coe.mp hncard
      have hRzero : R = 0 := by
        apply poly_eq_zero_of_ncard_gt_bound_of_subset_roots
        · dsimp [R]
          exact rationalVanishingSet_subset_resultant_roots hH β
        · exact hdeg
        · exact hcard
      apply embedding_eq_zero_of_resultant_zero hH β
      dsimp [R] at hRzero
      exact hRzero

end RationalRootVanishing

end RationalFunctions

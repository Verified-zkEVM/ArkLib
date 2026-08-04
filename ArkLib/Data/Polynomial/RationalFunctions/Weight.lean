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
import ArkLib.Data.Polynomial.RationalFunctions.FunctionField
/-!
# Weight Bounds for Bivariate Polynomials

We define the notions of Appendix A of [BCIKS20].

## References

[BCIKS20] Eli Ben-Sasson, Dan Carmon, Yuval Ishai, Swastik Kopparty, and Shubhangi Saraf.
  Proximity gaps for Reed-Solomon codes. In 2020 IEEE 61st Annual Symposium on Foundations of
  Computer Science (FOCS), 2020. Full paper: https://eprint.iacr.org/2020/654,
  version 20210703:203025.

-/


open Polynomial Polynomial.Bivariate ToRatFunc Ideal

namespace RationalFunctions

section

variable {F : Type} [CommRing F] [IsDomain F]
/-- `Λ` is a weight function on the ring of bivariate polynomials `F[X][Y]`. The weight of
a polynomial is the maximal weight of all monomials appearing in it with non-zero coefficients.
The weight of the zero polynomial is `−∞`.
Requires `D ≥ Bivariate.totalDegree H` to match definition in [BCIKS20]. -/
noncomputable def weight (f H : F[X][Y]) (D : ℕ) : WithBot ℕ :=
  Finset.sup
    f.support
    (fun deg =>
      WithBot.some <| deg * (D + 1 - Bivariate.natDegreeY H) + (f.coeff deg).natDegree
    )

omit [IsDomain F] in
/-- The zero polynomial has bottom `Λ`-weight. -/
@[simp]
lemma weight_zero (H : F[X][Y]) (D : ℕ) :
    weight (0 : F[X][Y]) H D = ⊥ := by
  simp [weight]

/-- The weight function `Λ` on regular elements is the weight of their canonical representatives
in `F[X][Y]`. -/
noncomputable def regularWeight {H : F[X][Y]} (hH : 0 < H.natDegree) (f : 𝒪 H) (D : ℕ) :
    WithBot ℕ := weight (canonicalRepOf𝒪 hH f) H D

omit [IsDomain F] in
/-- The `𝒪`-weight of zero is bottom. -/
@[simp]
lemma regularWeight_zero {H : F[X][Y]} (hH : 0 < H.natDegree) (D : ℕ) :
    regularWeight hH (0 : 𝒪 H) D = ⊥ := by
  simp [regularWeight]

omit [IsDomain F] in
/-- The `𝒪`-weight of a quotient constructor is computed on its canonical remainder. -/
lemma regularWeight_mk {H : F[X][Y]} (hH : 0 < H.natDegree) (p : F[X][Y])
    (D : ℕ) :
    regularWeight hH (Ideal.Quotient.mk (Ideal.span {monicize H}) p : 𝒪 H) D =
      weight (p %ₘ monicize H) H D := by
  simp [regularWeight, canonicalRepOf𝒪_mk]

/-- If a representative is already reduced, its `𝒪`-weight is its polynomial `Λ`-weight. -/
lemma regularWeight_mk_eq_self_of_degree_lt {H : F[X][Y]} (hH : 0 < H.natDegree)
    {p : F[X][Y]} (hp : p.degree < (monicize H).degree) (D : ℕ) :
    regularWeight hH (Ideal.Quotient.mk (Ideal.span {monicize H}) p : 𝒪 H) D =
      weight p H D := by
  simp [regularWeight, canonicalRepOf𝒪_mk_eq_self_of_degree_lt hH hp]

/-! ### Λ-weight calculus

Algebraic identities for the bivariate `Λ`-weight from Appendix A.2 of [BCIKS20]. The weight
`m := D + 1 − natDegreeY H` is the per-Y-power contribution; constants in `F[X]` contribute their
`natDegree`. -/

omit [IsDomain F] in
/-- A monomial `n` in `f`'s support contributes a lower bound on `Λ(f)`. -/
lemma le_weight_of_mem_support {f H : F[X][Y]} {D : ℕ} {n : ℕ} (hn : n ∈ f.support) :
    (WithBot.some (n * (D + 1 - Bivariate.natDegreeY H) + (f.coeff n).natDegree) :
      WithBot ℕ) ≤ weight f H D := by
  classical
  exact Finset.le_sup (f := fun deg =>
    (WithBot.some (deg * (D + 1 - Bivariate.natDegreeY H) + (f.coeff deg).natDegree) :
      WithBot ℕ)) hn

omit [IsDomain F] in
/-- Characterization: `Λ(f) ≤ b` iff every monomial in `f`'s support contributes at most `b`. -/
lemma weight_le_iff {f H : F[X][Y]} {D b : ℕ} :
    weight f H D ≤ (WithBot.some b : WithBot ℕ) ↔
      ∀ n ∈ f.support,
        n * (D + 1 - Bivariate.natDegreeY H) + (f.coeff n).natDegree ≤ b := by
  classical
  refine ⟨fun h n hn => ?_, fun h => ?_⟩
  · have := (le_weight_of_mem_support hn).trans h
    exact_mod_cast this
  · refine Finset.sup_le (fun n hn => ?_)
    exact_mod_cast (h n hn)

omit [IsDomain F] in
/-- `Λ(C c) ≤ c.natDegree`. -/
lemma weight_C_le (H : F[X][Y]) (D : ℕ) (c : F[X]) :
    weight (Polynomial.C c) H D ≤ (WithBot.some c.natDegree : WithBot ℕ) := by
  classical
  rw [weight_le_iff]
  intro n hn
  have : (Polynomial.C c : F[X][Y]).coeff n ≠ 0 := Polynomial.mem_support_iff.mp hn
  have hn0 : n = 0 := by
    by_contra h
    simp [Polynomial.coeff_C, h] at this
  subst hn0
  simp [Polynomial.coeff_C]

omit [IsDomain F] in
/-- `Λ(Y^k) ≤ k · m`. -/
lemma weight_X_pow_le (H : F[X][Y]) (D k : ℕ) :
    weight ((Polynomial.X : F[X][Y]) ^ k) H D ≤
      (WithBot.some (k * (D + 1 - Bivariate.natDegreeY H)) : WithBot ℕ) := by
  classical
  rw [weight_le_iff]
  intro n hn
  have : ((Polynomial.X : F[X][Y]) ^ k).coeff n ≠ 0 := Polynomial.mem_support_iff.mp hn
  have hnk : n = k := by
    by_contra h
    simp [Polynomial.coeff_X_pow, h] at this
  subst hnk
  simp [Polynomial.coeff_X_pow]

omit [IsDomain F] in
/-- `Λ(C c · Y^k) ≤ k · m + c.natDegree`. -/
lemma weight_C_mul_X_pow_le (H : F[X][Y]) (D : ℕ) (c : F[X]) (k : ℕ) :
    weight (Polynomial.C c * Polynomial.X ^ k) H D ≤
      (WithBot.some (k * (D + 1 - Bivariate.natDegreeY H) + c.natDegree) : WithBot ℕ) := by
  classical
  rw [weight_le_iff]
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
lemma weight_neg (f H : F[X][Y]) (D : ℕ) : weight (-f) H D = weight f H D := by
  classical
  unfold weight
  rw [Polynomial.support_neg]
  refine Finset.sup_congr rfl (fun n _ => ?_)
  simp [Polynomial.coeff_neg]

omit [IsDomain F] in
/-- `Λ(f + g) ≤ max(Λ(f), Λ(g))`. -/
lemma weight_add_le (f g H : F[X][Y]) (D : ℕ) :
    weight (f + g) H D ≤ max (weight f H D) (weight g H D) := by
  classical
  refine Finset.sup_le (fun n hn => ?_)
  -- The contribution at `n` to weight (f + g) is bounded by f's or g's contribution.
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
    exact (le_weight_of_mem_support hng).trans (le_max_right _ _)
  · have hnf : n ∈ f.support := Polynomial.mem_support_iff.mpr hf
    by_cases hg : g.coeff n = 0
    · have heq : (f + g).coeff n = f.coeff n := by simp [hcoeff, hg]
      change (WithBot.some _ : WithBot ℕ) ≤ _
      rw [heq]
      exact (le_weight_of_mem_support hnf).trans (le_max_left _ _)
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
          _ ≤ weight g H D := le_weight_of_mem_support hng
          _ ≤ max (weight f H D) (weight g H D) := le_max_right _ _
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
          _ ≤ weight f H D := le_weight_of_mem_support hnf
          _ ≤ max (weight f H D) (weight g H D) := le_max_left _ _

omit [IsDomain F] in
/-- `Λ(f − g) ≤ max(Λ(f), Λ(g))`. -/
lemma weight_sub_le (f g H : F[X][Y]) (D : ℕ) :
    weight (f - g) H D ≤ max (weight f H D) (weight g H D) := by
  rw [sub_eq_add_neg]
  exact (weight_add_le f (-g) H D).trans_eq (by rw [weight_neg])

omit [IsDomain F] in
/-- `Λ` of a finite sum is bounded by the max of the summands' weights. -/
lemma weight_sum_le {ι : Type} (s : Finset ι) (f : ι → F[X][Y]) (H : F[X][Y]) (D : ℕ) :
    weight (∑ i ∈ s, f i) H D ≤ s.sup (fun i => weight (f i) H D) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sup_insert]
      exact (weight_add_le _ _ _ _).trans (max_le_max le_rfl ih)

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
lemma weight_C_mul_X_pow_mul_le {c : F[X]} {k : ℕ} {f H : F[X][Y]} {D b : ℕ}
    (hf : weight f H D ≤ (WithBot.some b : WithBot ℕ)) :
    weight (Polynomial.C c * Polynomial.X ^ k * f) H D ≤
      (WithBot.some (k * (D + 1 - Bivariate.natDegreeY H) + c.natDegree + b) :
        WithBot ℕ) := by
  classical
  rw [weight_le_iff]
  rw [weight_le_iff] at hf
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

/-- The `natDegree` of `monicize H` matches that of `H` when `0 < H.natDegree`. -/
lemma natDegree_monicize {H : F[X][Y]} (hH : 0 < H.natDegree) :
    (monicize H).natDegree = H.natDegree := by
  classical
  rw [monicize, if_neg (Nat.ne_of_gt hH)]
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
    have hq_ne : monicize H ≠ 0 := (monicize_monic H hH).ne_zero
    rw [Polynomial.degree_eq_natDegree hβ, Polynomial.degree_eq_natDegree hq_ne] at hdeg
    exact_mod_cast (by simpa [natDegree_monicize hH] using hdeg)

omit [IsDomain F] in
/-- The `Λ`-weight of `monicize H` is bounded by `d_H · m`, where `d_H = H.natDegree`. -/
lemma weight_monicize_le {H : F[X][Y]} {D : ℕ}
    (hD : Bivariate.totalDegree H ≤ D) (hH : 0 < H.natDegree) :
    weight (monicize H) H D ≤
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
  rw [monicize, if_neg (Nat.ne_of_gt hH)]
  refine (weight_add_le _ _ _ _).trans ?_
  refine max_le ?_ ?_
  · -- weight Y^d ≤ d · m
    refine (weight_X_pow_le H D _).trans ?_
    rw [WithBot.coe_le_coe]
  · -- weight (∑ ... · Y^i) ≤ d · m
    refine (weight_sum_le _ _ _ _).trans ?_
    refine Finset.sup_le (fun i hi => ?_)
    have hi_lt : i < H.natDegree := Finset.mem_range.mp hi
    refine (weight_C_mul_X_pow_le H D _ _).trans ?_
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
`C(p.leadingCoeff) · Y^(p.natDegree - d_H) · monicize H` from `p` keeps the weight bounded by
`Λ(p)`. -/
lemma weight_sub_leadingCoeff_mul_monicize_le {p H : F[X][Y]} {D : ℕ}
    (hD : Bivariate.totalDegree H ≤ D) (hH : 0 < H.natDegree)
    (hp_deg : H.natDegree ≤ p.natDegree) :
    weight (p - Polynomial.C p.leadingCoeff *
        Polynomial.X ^ (p.natDegree - H.natDegree) * monicize H) H D ≤
      weight p H D := by
  classical
  refine (weight_sub_le _ _ _ _).trans ?_
  refine max_le le_rfl ?_
  refine (weight_C_mul_X_pow_mul_le (weight_monicize_le hD hH)).trans ?_
  by_cases hp : p = 0
  · subst hp
    simp at hp_deg
    omega
  · have hp_lead_ne : p.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hp
    have hp_in : p.natDegree ∈ p.support := Polynomial.mem_support_iff.mpr hp_lead_ne
    refine le_trans ?_ (le_weight_of_mem_support hp_in)
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

/-- Reduction modulo `monicize H` does not increase `Λ`-weight. -/
lemma weight_modByMonic_monicize_le {H : F[X][Y]} {D : ℕ}
    (hD : Bivariate.totalDegree H ≤ D) (hH : 0 < H.natDegree) :
    ∀ p : F[X][Y], weight (p %ₘ monicize H) H D ≤ weight p H D
  | p => by
      classical
      have hq : (monicize H).Monic := monicize_monic H hH
      unfold Polynomial.modByMonic Polynomial.divModByMonicAux
      rw [dif_pos hq]
      by_cases h : (monicize H).degree ≤ p.degree ∧ p ≠ 0
      · have _wf := Polynomial.div_wf_lemma h hq
        simp only [ne_eq, dite_eq_ite, ge_iff_le, p, h]
        let z := Polynomial.C p.leadingCoeff *
          Polynomial.X ^ (p.natDegree - (monicize H).natDegree)
        have ih := weight_modByMonic_monicize_le hD hH (p - monicize H * z)
        have ih' :
            weight ((Polynomial.divModByMonicAux (p - monicize H * z) hq).2) H D ≤
              weight (p - monicize H * z) H D := by
          simpa [Polynomial.modByMonic, hq, z] using ih
        have hqnat : (monicize H).natDegree = H.natDegree := natDegree_monicize hH
        have hp_deg : H.natDegree ≤ p.natDegree := by
          have hdeg := h.1
          rw [Polynomial.degree_eq_natDegree h.2, Polynomial.degree_eq_natDegree hq.ne_zero]
            at hdeg
          exact_mod_cast (by simpa [hqnat] using hdeg)
        have hstep0 :=
          weight_sub_leadingCoeff_mul_monicize_le (p := p) (H := H) hD hH hp_deg
        have hstep : weight (p - monicize H * z) H D ≤ weight p H D := by
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
lemma regularWeight_mk_le {H : F[X][Y]} {D : ℕ}
    (hD : Bivariate.totalDegree H ≤ D) (hH : 0 < H.natDegree) (p : F[X][Y]) :
    regularWeight hH (Ideal.Quotient.mk (Ideal.span {monicize H}) p : 𝒪 H) D ≤
      weight p H D := by
  rw [regularWeight_mk]
  exact weight_modByMonic_monicize_le hD hH p

/-- The set `rationalVanishingSet` from the statement of Lemma A.1 in Appendix A of [BCIKS20].
Note: Here `F[X][Y]` is `F[Z][T]`. -/
noncomputable def rationalVanishingSet {H : F[X][Y]} (β : 𝒪 H) : Set F :=
  {z : F | ∃ root : rationalRoot (monicize H) z, (piZ z root) β = 0}

omit [IsDomain F] in
/-- The rational substitution `piZ` can be computed on the canonical representative. -/
lemma piZ_eq_eval_canonicalRepOf𝒪 {H : F[X][Y]} (hH : 0 < H.natDegree)
    (z : F) (root : rationalRoot (monicize H) z) (β : 𝒪 H) :
    (piZ z root) β = Polynomial.evalEvalRingHom z root.1 (canonicalRepOf𝒪 hH β) := by
  conv_lhs => rw [← mk_canonicalRepOf𝒪 hH β]
  rfl

end

end RationalFunctions

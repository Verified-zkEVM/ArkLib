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

import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Roots
import ArkLib.Data.Polynomial.RationalFunctions.FunctionField
/-!
# Algebraic Weights

Appendix A.2 of [BCIKS20]: the weight function `Λ` on `F[Z][T]`, given by `Λ(Z) = 1` and
`Λ(T) = D + 1 - deg_Y H` extended additively (`weight`), its transport to `𝒪 H` via canonical
representatives (`regularWeight`), sub-additivity, and the key fact that reduction modulo `H̃`
never increases `Λ` (`weight_modByMonic_monicize_le`).

## References

[BCIKS20] Eli Ben-Sasson, Dan Carmon, Yuval Ishai, Swastik Kopparty, and Shubhangi Saraf.
  Proximity gaps for Reed-Solomon codes. In 2020 IEEE 61st Annual Symposium on Foundations of
  Computer Science (FOCS), 2020. Full paper: https://eprint.iacr.org/2020/654,
  version 20210703:203025.

-/


open Polynomial Polynomial.Bivariate ToRatFunc Ideal

namespace RationalFunctions

section AlgebraicWeights

variable {F : Type} [CommRing F] [IsDomain F]
/-- `Λ` is a weight function on the ring of bivariate polynomials `F[X][Y]`. The weight of
a polynomial is the maximal weight of all monomials appearing in it with non-zero coefficients.
The weight of the zero polynomial is `−∞`.
The grading unit `D + 1 - deg_Y H` is intended to be used with `D ≥ Bivariate.totalDegree H`;
below that the truncated subtraction distorts it. -/
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

Algebraic identities for the bivariate `Λ`-weight. The weight
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
/-- `Λ` is subadditive under multiplication of bivariate polynomials (bound form). -/
lemma weight_mul_le' {f g H : F[X][Y]} {D bf bg : ℕ}
    (hf : weight f H D ≤ (WithBot.some bf : WithBot ℕ))
    (hg : weight g H D ≤ (WithBot.some bg : WithBot ℕ)) :
    weight (f * g) H D ≤ (WithBot.some (bf + bg) : WithBot ℕ) := by
  classical
  rw [weight_le_iff]
  rw [weight_le_iff] at hf hg
  intro n hn
  set m := D + 1 - Bivariate.natDegreeY H with hm
  have hcoeff_ne : (f * g).coeff n ≠ 0 := Polynomial.mem_support_iff.mp hn
  have hexists : ∃ x ∈ Finset.antidiagonal n, f.coeff x.1 * g.coeff x.2 ≠ 0 := by
    by_contra h
    push Not at h
    exact hcoeff_ne (by rw [Polynomial.coeff_mul]; exact Finset.sum_eq_zero h)
  obtain ⟨x0, hx0mem, hx0ne⟩ := hexists
  have hx0sum : x0.1 + x0.2 = n := Finset.mem_antidiagonal.mp hx0mem
  have hfb0 := hf x0.1 (Polynomial.mem_support_iff.mpr (left_ne_zero_of_mul hx0ne))
  have hgb0 := hg x0.2 (Polynomial.mem_support_iff.mpr (right_ne_zero_of_mul hx0ne))
  have hnm_le : n * m ≤ bf + bg := by
    have : n * m = x0.1 * m + x0.2 * m := by rw [← hx0sum, Nat.add_mul]
    omega
  have hdeg : ((f * g).coeff n).natDegree ≤ bf + bg - n * m := by
    rw [Polynomial.coeff_mul]
    refine Polynomial.natDegree_sum_le_of_forall_le _ _ ?_
    intro x hx
    have hxsum : x.1 + x.2 = n := Finset.mem_antidiagonal.mp hx
    by_cases hxz : f.coeff x.1 * g.coeff x.2 = 0
    · simp [hxz]
    · have hfb := hf x.1 (Polynomial.mem_support_iff.mpr (left_ne_zero_of_mul hxz))
      have hgb := hg x.2 (Polynomial.mem_support_iff.mpr (right_ne_zero_of_mul hxz))
      have hprod : (f.coeff x.1 * g.coeff x.2).natDegree ≤
          (f.coeff x.1).natDegree + (g.coeff x.2).natDegree := Polynomial.natDegree_mul_le
      have hnm : n * m = x.1 * m + x.2 * m := by rw [← hxsum, Nat.add_mul]
      omega
  omega

omit [IsDomain F] in
/-- The largest index attaining the maximal weight of a nonzero `f`, together with that maximum.
Used to prove full additivity: the *largest* maximizer is what prevents the top-weight parts of two
factors from cancelling. -/
private lemma exists_top_weight_index {f : F[X][Y]} (H : F[X][Y]) (D : ℕ) (hf : f ≠ 0) :
    ∃ N b : ℕ, weight f H D = (WithBot.some b : WithBot ℕ) ∧ f.coeff N ≠ 0 ∧
      N * (D + 1 - Bivariate.natDegreeY H) + (f.coeff N).natDegree = b ∧
      ∀ m, f.coeff m ≠ 0 → N < m →
        m * (D + 1 - Bivariate.natDegreeY H) + (f.coeff m).natDegree < b := by
  classical
  set u := D + 1 - Bivariate.natDegreeY H with hu
  have hne : f.support.Nonempty := Polynomial.support_nonempty.mpr hf
  obtain ⟨n₀, hn₀mem, hn₀⟩ := Finset.exists_mem_eq_sup f.support hne
    (fun d => (WithBot.some (d * u + (f.coeff d).natDegree) : WithBot ℕ))
  set b := n₀ * u + (f.coeff n₀).natDegree with hb
  have hw : weight f H D = (WithBot.some b : WithBot ℕ) := hn₀
  have hall : ∀ m ∈ f.support, m * u + (f.coeff m).natDegree ≤ b :=
    weight_le_iff.mp (le_of_eq hw)
  set S := f.support.filter (fun m => m * u + (f.coeff m).natDegree = b) with hS
  have hSne : S.Nonempty := ⟨n₀, Finset.mem_filter.mpr ⟨hn₀mem, rfl⟩⟩
  refine ⟨S.max' hSne, b, hw, ?_, ?_, ?_⟩
  · exact Polynomial.mem_support_iff.mp (Finset.mem_filter.mp (S.max'_mem hSne)).1
  · exact (Finset.mem_filter.mp (S.max'_mem hSne)).2
  · intro m hm hlt
    have hmem : m ∈ f.support := Polynomial.mem_support_iff.mpr hm
    have hle := hall m hmem
    rcases Nat.lt_or_ge (m * u + (f.coeff m).natDegree) b with h | h
    · exact h
    · exact absurd (S.le_max' m (Finset.mem_filter.mpr ⟨hmem, by omega⟩)) (by omega)

/-- **`Λ` is fully additive**: `Λ(f · g) = Λ(f) + Λ(g)`.

Sub-additivity is `weight_mul_le'`.  The reverse inequality holds because the weight assignment
grades `F[Z][T]` — each `Λ`-homogeneous piece is spanned by monomials of that weight — so the
associated graded ring is again a polynomial ring, hence a domain, and the top-weight parts of `f`
and `g` cannot cancel.  Concretely: at the *largest* maximizing index `N_f` of `f` and `N_g` of `g`,
the coefficient of `T^{N_f + N_g}` in `f · g` is `f_{N_f} · g_{N_g}` plus terms of strictly smaller
`Z`-degree, because any other `(i, j)` with `i + j = N_f + N_g` has `i > N_f` or `j > N_g` and
maximality then costs at least one degree.  So that coefficient has `Z`-degree exactly
`deg f_{N_f} + deg g_{N_g}`, witnessing `Λ(f) + Λ(g) ≤ Λ(f · g)`. -/
theorem weight_mul (f g H : F[X][Y]) (D : ℕ) :
    weight (f * g) H D = weight f H D + weight g H D := by
  classical
  rcases eq_or_ne f 0 with rfl | hf
  · simp
  rcases eq_or_ne g 0 with rfl | hg
  · simp
  obtain ⟨Nf, bf, hwf, hfNe, hfEq, hfMax⟩ := exists_top_weight_index H D hf
  obtain ⟨Ng, bg, hwg, hgNe, hgEq, hgMax⟩ := exists_top_weight_index H D hg
  obtain ⟨u, hu⟩ : ∃ u : ℕ, u = D + 1 - Bivariate.natDegreeY H := ⟨_, rfl⟩
  simp only [← hu] at hfEq hfMax hgEq hgMax
  rw [hwf, hwg, ← WithBot.coe_add]
  refine le_antisymm (weight_mul_le' (le_of_eq hwf) (le_of_eq hwg)) ?_
  have hallf : ∀ m ∈ f.support, m * u + (f.coeff m).natDegree ≤ bf := by
    simpa only [← hu] using weight_le_iff.mp (le_of_eq hwf)
  have hallg : ∀ m ∈ g.support, m * u + (g.coeff m).natDegree ≤ bg := by
    simpa only [← hu] using weight_le_iff.mp (le_of_eq hwg)
  set df := (f.coeff Nf).natDegree with hdf
  set dg := (g.coeff Ng).natDegree with hdg
  have hAne : f.coeff Nf * g.coeff Ng ≠ 0 := mul_ne_zero hfNe hgNe
  have hAdeg : (f.coeff Nf * g.coeff Ng).degree = ((df + dg : ℕ) : WithBot ℕ) := by
    rw [Polynomial.degree_eq_natDegree hAne, Polynomial.natDegree_mul hfNe hgNe]
  -- every other contribution to the `(N_f + N_g)`-th coefficient is of strictly smaller degree
  have hrest : ∀ x ∈ (Finset.antidiagonal (Nf + Ng)).erase (Nf, Ng),
      (f.coeff x.1 * g.coeff x.2).degree < ((df + dg : ℕ) : WithBot ℕ) := by
    intro x hx
    obtain ⟨hxne, hxmem⟩ := Finset.mem_erase.mp hx
    have hxsum : x.1 + x.2 = Nf + Ng := Finset.mem_antidiagonal.mp hxmem
    by_cases hz : f.coeff x.1 * g.coeff x.2 = 0
    · rw [hz, Polynomial.degree_zero]
      exact WithBot.bot_lt_coe _
    · have hfx : f.coeff x.1 ≠ 0 := left_ne_zero_of_mul hz
      have hgx : g.coeff x.2 ≠ 0 := right_ne_zero_of_mul hz
      have hmul : x.1 * u + x.2 * u = Nf * u + Ng * u := by
        rw [← Nat.add_mul, ← Nat.add_mul, hxsum]
      have hstrict : (f.coeff x.1).natDegree + (g.coeff x.2).natDegree < df + dg := by
        rcases Nat.lt_trichotomy x.1 Nf with h1 | h1 | h1
        · have h2 : Ng < x.2 := by omega
          have hgs := hgMax x.2 hgx h2
          have hfl := hallf x.1 (Polynomial.mem_support_iff.mpr hfx)
          omega
        · exact absurd (Prod.ext h1 (by omega)) hxne
        · have hfs := hfMax x.1 hfx h1
          have hgl := hallg x.2 (Polynomial.mem_support_iff.mpr hgx)
          omega
      rw [Polynomial.degree_eq_natDegree hz, Polynomial.natDegree_mul hfx hgx]
      exact_mod_cast hstrict
  have hsplit : (f * g).coeff (Nf + Ng) =
      f.coeff Nf * g.coeff Ng +
        ∑ x ∈ (Finset.antidiagonal (Nf + Ng)).erase (Nf, Ng), f.coeff x.1 * g.coeff x.2 := by
    have hpair : (Nf, Ng) ∈ Finset.antidiagonal (Nf + Ng) :=
      Finset.mem_antidiagonal.mpr rfl
    rw [Polynomial.coeff_mul, ← Finset.add_sum_erase _ _ hpair]
  have hBdeg : (∑ x ∈ (Finset.antidiagonal (Nf + Ng)).erase (Nf, Ng),
      f.coeff x.1 * g.coeff x.2).degree < ((df + dg : ℕ) : WithBot ℕ) :=
    lt_of_le_of_lt (Polynomial.degree_sum_le _ _)
      ((Finset.sup_lt_iff (WithBot.bot_lt_coe _)).mpr hrest)
  have hlt : (∑ x ∈ (Finset.antidiagonal (Nf + Ng)).erase (Nf, Ng),
      f.coeff x.1 * g.coeff x.2).degree < (f.coeff Nf * g.coeff Ng).degree := by
    rw [hAdeg]; exact hBdeg
  have hcoeff_deg : ((f * g).coeff (Nf + Ng)).degree = ((df + dg : ℕ) : WithBot ℕ) := by
    rw [hsplit, Polynomial.degree_add_eq_left_of_degree_lt hlt, hAdeg]
  have hcoeff_ne : (f * g).coeff (Nf + Ng) ≠ 0 := by
    intro h0
    rw [h0, Polynomial.degree_zero] at hcoeff_deg
    exact WithBot.bot_ne_coe hcoeff_deg
  have hnd : ((f * g).coeff (Nf + Ng)).natDegree = df + dg :=
    Polynomial.natDegree_eq_of_degree_eq_some hcoeff_deg
  have hbound := le_weight_of_mem_support (f := f * g) (H := H) (D := D)
    (Polynomial.mem_support_iff.mpr hcoeff_ne)
  simp only [hnd, ← hu] at hbound
  have harith : (Nf + Ng) * u + (df + dg) = bf + bg := by
    have hd : (Nf + Ng) * u = Nf * u + Ng * u := Nat.add_mul _ _ _
    omega
  rwa [harith] at hbound

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

/-- The **exact** weight of the monicization: `Λ(H̃) = d·(D + 1 - d)`, the weight of its leading
monomial `Tᵈ`, every other monomial being bounded by it.  The upper
bound is `weight_monicize_le`; the lower bound is the leading monomial `Tᵈ`, whose coefficient is
`1` because `H̃` is monic. -/
lemma weight_monicize {H : F[X][Y]} {D : ℕ}
    (hD : Bivariate.totalDegree H ≤ D) (hH : 0 < H.natDegree) :
    weight (monicize H) H D =
      (WithBot.some (H.natDegree * (D + 1 - Bivariate.natDegreeY H)) : WithBot ℕ) := by
  refine le_antisymm (weight_monicize_le hD hH) ?_
  have hmonic : (monicize H).Monic := monicize_monic H hH
  have hdeg : (monicize H).natDegree = H.natDegree := natDegree_monicize hH
  have hlead : (monicize H).coeff H.natDegree = 1 := by
    rw [← hdeg]; exact hmonic.coeff_natDegree
  have hmem : H.natDegree ∈ (monicize H).support :=
    Polynomial.mem_support_iff.mpr (by rw [hlead]; exact one_ne_zero)
  have h := le_weight_of_mem_support (f := monicize H) (H := H) (D := D) hmem
  rwa [hlead, Polynomial.natDegree_one, Nat.add_zero] at h

/-- `regularWeight` is the **minimum** of `weight` over all representatives of a class, attained by
definition at `canonicalRepOf𝒪`. -/
lemma regularWeight_le_of_mk_eq {H : F[X][Y]} {D : ℕ}
    (hD : Bivariate.totalDegree H ≤ D) (hH : 0 < H.natDegree) {α : 𝒪 H} {p : F[X][Y]}
    (hp : (Ideal.Quotient.mk (Ideal.span {monicize H}) p : 𝒪 H) = α) :
    regularWeight hH α D ≤ weight p H D := by
  subst hp
  exact regularWeight_mk_le hD hH p

/-- The set of substitution points at which a regular element vanishes: those `z` admitting a
rational root `t_z` of `H̃(·, z)` with `π_z β = 0`.  Bounding its size bounds `Λ(β)` from below; see
`embedding_eq_zero_of_many_rational_roots`. -/
noncomputable def rationalVanishingSet {H : F[X][Y]} (β : 𝒪 H) : Set F :=
  {z : F | ∃ root : rationalRoot (monicize H) z, (piZ z root) β = 0}

omit [IsDomain F] in
/-- The rational substitution `piZ` can be computed on the canonical representative. -/
lemma piZ_eq_eval_canonicalRepOf𝒪 {H : F[X][Y]} (hH : 0 < H.natDegree)
    (z : F) (root : rationalRoot (monicize H) z) (β : 𝒪 H) :
    (piZ z root) β = Polynomial.evalEvalRingHom z root.1 (canonicalRepOf𝒪 hH β) := by
  conv_lhs => rw [← mk_canonicalRepOf𝒪 hH β]
  rfl

end AlgebraicWeights

end RationalFunctions

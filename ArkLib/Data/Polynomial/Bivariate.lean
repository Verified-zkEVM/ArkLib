/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Katerina Hristova, František Silváši, Julian Sutherland, Ilia Vlasov
-/

import CompPoly.ToMathlib.Polynomial.BivariateWeightedDegree
import CompPoly.ToMathlib.Polynomial.BivariateMultiplicity

import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
/-!
# ArkLib-Specific Bivariate Polynomial Extensions

The core bivariate polynomial definitions and degree/eval/multiplicity theory are provided
by CompPoly (`CompPoly.ToMathlib.Polynomial.BivariateDegree`, `BivariateWeightedDegree`,
`BivariateMultiplicity`). This file contains only ArkLib-specific extensions:

- Finset-level coefficient and evaluation helpers (`coeffs`, `evalSetX`, `evalSetY`)
- Quotient (divisibility) predicates and degree bounds
- Linear-map monomial constructors (`monomialY`, `monomialXY`) and their algebra
-/

open Polynomial
open Polynomial.Bivariate

namespace Polynomial.Bivariate

noncomputable section

variable {F : Type} [Semiring F]

/-- The set of coefficients of a bivariate polynomial. -/
def coeffs [DecidableEq F] (f : F[X][Y]) : Finset F[X] := f.support.image f.coeff

/-- A bivariate polynomial is non-zero if and only if its coefficient function is non-zero. -/
@[grind =_]
lemma ne_zero_iff_coeffs_ne_zero (f : F[X][Y]) : f ≠ 0 ↔ f.coeff ≠ 0 :=
  ⟨
    fun hf ↦ by have f_finsupp : f.toFinsupp ≠ 0 := by aesop
                simpa [Polynomial.coeff],
    fun f_coeffs ↦ by aesop (add simp Polynomial.coeff)
  ⟩

/-- The set of `Y`-degrees is non-empty. -/
lemma degreesY_nonempty {f : F[X][Y]} (hf : f ≠ 0) : (f.toFinsupp.support).Nonempty :=
  Finsupp.support_nonempty_iff.mpr
    fun h ↦ hf (Polynomial.ext (fun n => by rw [← Polynomial.toFinsupp_apply, h]; rfl))

variable {f : F[X][Y]}

attribute [local grind] Finsupp.support_nonempty_iff natDegree_mul_le degree_eq_bot
                        WithBot.bot_lt_coe isMaxOn_iff sup_eq_of_isMaxOn monomial_eq_monomial_iff
attribute [local grind ←] toFinsupp_eq_zero
attribute [local grind _=_] Finsupp.mem_support_iff toFinsupp_apply smul_monomial
attribute [local grind =] natDegree_mul natDegree_add_eq_right_of_degree_lt
                          natDegree_zero

theorem natDegree_sum_lt_of_forall_lt {F : Type} [Semiring F]
    {α : Type} {s : Finset α} {g : α → F[X]} {deg : ℕ} :
  0 < deg → (∀ x ∈ s, (g x).natDegree < deg) → (∑ x ∈ s, g x).natDegree < deg := by
  intro deg_pos h
  have hle : (∑ x ∈ s, g x).natDegree ≤ Nat.pred deg := by
    refine Polynomial.natDegree_sum_le_of_forall_le (s := s) (f := g) (n := Nat.pred deg) ?_
    intro x hx
    exact Nat.le_pred_of_lt (h x hx)
  exact lt_of_le_of_lt hle (Nat.pred_lt_self deg_pos)


theorem natDeg_sum_eq_of_unique {α : Type} {s : Finset α} {f : α → F[X]} {deg : ℕ}
  (mx : α) (h : mx ∈ s) :
    (f mx).natDegree = deg →
    (∀ y ∈ s, y ≠ mx → (f y).natDegree < deg ∨ f y = 0) →
    (∑ x ∈ s, f x).natDegree = deg := by
  classical
  intro hmxdeg others
  by_cases hdeg0 : deg = 0
  · have hothers0 : ∀ y ∈ s, y ≠ mx → f y = 0 := by
      intro y hy hne
      have h' := others y hy hne
      rcases h' with hlt | hy0
      · simp [hdeg0] at hlt
      · exact hy0
    have hsum : (∑ x ∈ s, f x) = f mx := by
      classical
      refine Finset.sum_eq_single_of_mem mx h ?_?
      intro y hy hne
      exact hothers0 y hy hne
    calc
      (∑ x ∈ s, f x).natDegree = (f mx).natDegree := by simp [hsum]
      _ = deg := hmxdeg
  · have deg_pos : 0 < deg := Nat.pos_of_ne_zero hdeg0
    have hlt_sum : (∑ x ∈ s \ {mx}, f x).natDegree < deg := by
      refine natDegree_sum_lt_of_forall_lt (s := s \ {mx}) (g := f) (deg := deg) deg_pos ?_
      intro y hy
      have hy_s : y ∈ s := (Finset.mem_sdiff.mp hy).1
      have hy_not : y ∉ ({mx} : Finset α) := (Finset.mem_sdiff.mp hy).2
      have hy_ne : y ≠ mx := by
        simpa [Finset.mem_singleton] using hy_not
      have h' := others y hy_s hy_ne
      rcases h' with hlt | hy0
      · exact hlt
      · simpa [hy0] using deg_pos
    have hlt_mx : (∑ x ∈ s \ {mx}, f x).natDegree < (f mx).natDegree := by
      simpa [hmxdeg] using hlt_sum
    have hsum_decomp : (∑ x ∈ s, f x) = (∑ x ∈ s \ {mx}, f x) + f mx := by
      classical
      simpa using (Finset.sum_eq_sum_diff_singleton_add (s := s) (i := mx) (f := f) h)
    calc
      (∑ x ∈ s, f x).natDegree = ((∑ x ∈ s \ {mx}, f x) + f mx).natDegree := by
        simp [hsum_decomp]
      _ = (f mx).natDegree := by
        exact Polynomial.natDegree_add_eq_right_of_natDegree_lt hlt_mx
      _ = deg := hmxdeg


/-- If some element `x ∈ s` maps to `y` under `f`, and every element of `s` maps to a value
less than or equal to `y`, then the supremum of `f` over `s` is exactly `y`. -/
lemma sup_eq_of_le_of_reach {α β : Type} [SemilatticeSup β] [OrderBot β] {s : Finset α} {f : α → β}
      (x : α) {y : β} (h : x ∈ s) :
    f x = y →
    (∀ x ∈ s, f x ≤ y) →
    s.sup f = y := by
  grind

/-- Evaluating a bivariate polynomial in the first variable `X` on a set of points. This results in
a set of univariate polynomials in `Y`. -/
def evalSetX [DecidableEq F] (f : F[X][Y]) (P : Finset F) [Nonempty P] : Finset (Polynomial F) :=
  P.image (fun a => evalX a f)

/-- Evaluating a bivariate polynomial in the second variable `Y` on a set of points resulting
in a set of univariate polynomials in `X`. -/
def evalSetY [DecidableEq F] (f : F[X][Y]) (P : Finset F) [Nonempty P] : Finset (Polynomial F) :=
  P.image (fun a => evalY a f)

/-- The bivariate quotient polynomial. -/
def quotient (f g : F[X][Y]) : Prop := ∃ q : F[X][Y], g = q * f

/-- The quotient of two non-zero bivariate polynomials is non-zero. -/
@[grind .]
lemma quotient_nezero {f q : F[X][Y]} (hg : q * f ≠ 0) : q ≠ 0 := by by_contra h; apply hg; simp [h]

/-- If a non-zero bivariate polynomial `f` divides a non-zero bivariate polynomial `g`, then
all the coefficients of the quoetient are non-zero. -/
@[grind .]
lemma coeff_ne_zero {f q : F[X][Y]} (hg : q * f ≠ 0) : q.coeff ≠ 0 :=
  (ne_zero_iff_coeffs_ne_zero q).1 (quotient_nezero hg)

/-
If `q * f ≠ 0`, then the `X`-degree of `q` is bounded above by the difference of the
`X`-degrees: `degreeX q ≤ degreeX (q * f) - degreeX f`.
-/
@[grind .]
lemma degreeX_le_degreeX_sub_degreeX [IsDomain F] {f q : F[X][Y]} (hf : f ≠ 0) (hg : q * f ≠ 0) :
  degreeX q ≤ degreeX (q * f) - degreeX f := by
  have hq : q ≠ 0 := quotient_nezero (f := f) (q := q) hg
  have hmul : degreeX (q * f) = degreeX q + degreeX f := degreeX_mul q f hq hf
  have hsum : degreeX q + degreeX f ≤ degreeX (q * f) := by
    simp [hmul]
  have hfb : degreeX f ≤ degreeX (q * f) := by
    exact le_trans (Nat.le_add_left _ _) hsum
  exact (Nat.le_sub_iff_add_le hfb).2 hsum

/-
If `q * f ≠ 0`, then the `Y`-degree of `q` is bounded above by the difference of the
`Y`-degrees: `natDegreeY q ≤ natDegreeY (q * f) - natDegreeY f`.
-/
@[grind .]
lemma degreeY_le_degreeY_sub_degreeY [IsDomain F] {f q : F[X][Y]} (hf : f ≠ 0) (hg : q * f ≠ 0) :
  natDegreeY q ≤ natDegreeY (q * f) - natDegreeY f := by grind

/-- Each coefficient's total-degree contribution is bounded by `totalDegree` when in support. -/
theorem coeff_totalDegree_le (f : F[X][Y]) {n : ℕ} (hn : n ∈ f.support) :
    (f.coeff n).natDegree + n ≤ totalDegree f := by
  classical
  unfold totalDegree
  exact Finset.le_sup (f := fun m => (f.coeff m).natDegree + m) hn

theorem coeff_totalDegree_le' (f : F[X][Y]) (n : ℕ) :
    (f.coeff n).natDegree + n ≤ totalDegree f ∨ f.coeff n = 0 := by
  by_cases hn : n ∈ f.support
  · exact Or.inl (coeff_totalDegree_le f hn)
  · exact Or.inr (Polynomial.notMem_support_iff.mp hn)

/-- There exists a maximal Y-index achieving `totalDegree`. Above it, total-degree contributions
    are strictly smaller or the coefficient vanishes. -/
theorem exists_max_index_totalDegree (f : F[X][Y]) (hf : f ≠ 0) :
    ∃ mm ∈ f.support,
      (f.coeff mm).natDegree + mm = totalDegree f ∧
      ∀ n, mm < n → (f.coeff n).natDegree + n < totalDegree f ∨ f.coeff n = 0 := by
  classical
  let s₁ : Finset ℕ := f.support.filter (fun n => (f.coeff n).natDegree + n = totalDegree f)
  have hs₁ : s₁.Nonempty := by
    have hsupp : f.support.Nonempty := Polynomial.support_nonempty.2 hf
    obtain ⟨m, hm_mem, hm_sup⟩ :=
      Finset.exists_mem_eq_sup _ hsupp (fun n => (f.coeff n).natDegree + n)
    have hm_deg : (f.coeff m).natDegree + m = totalDegree f := by
      simpa [totalDegree] using hm_sup.symm
    exact ⟨m, Finset.mem_filter.mpr ⟨hm_mem, hm_deg⟩⟩
  set mm : ℕ := s₁.max' hs₁ with hmm
  have hmm_mem_s₁ : mm ∈ s₁ := by simpa [hmm] using Finset.max'_mem s₁ hs₁
  have hmm_filter : mm ∈ f.support ∧ (f.coeff mm).natDegree + mm = totalDegree f := by
    simpa [s₁] using Finset.mem_filter.mp hmm_mem_s₁
  refine ⟨mm, hmm_filter.1, hmm_filter.2, ?_⟩
  intro n hmn
  by_cases hn0 : f.coeff n = 0
  · exact Or.inr hn0
  · have hn_support : n ∈ f.support := Polynomial.mem_support_iff.2 hn0
    have hn_le : (f.coeff n).natDegree + n ≤ totalDegree f := coeff_totalDegree_le f hn_support
    have hn_ne : (f.coeff n).natDegree + n ≠ totalDegree f := by
      intro hEq
      have hn_s₁ : n ∈ s₁ := Finset.mem_filter.mpr ⟨hn_support, hEq⟩
      have : n ≤ mm := Finset.le_max' s₁ n hn_s₁
      exact not_le_of_gt hmn this
    exact Or.inl (lt_of_le_of_ne hn_le hn_ne)

theorem totalDegree_mul_le (f g : F[X][Y]) :
    totalDegree (f * g) ≤ totalDegree f + totalDegree g := by
  classical
  unfold totalDegree
  refine Finset.sup_le ?_
  intro k hk
  have hk_supp : k ∈ (f * g).support := hk
  rw [Polynomial.coeff_mul]
  -- Bound: natDegree of each antidiagonal term
  have hnd_le : ∀ x ∈ Finset.antidiagonal k,
      (f.coeff x.1 * g.coeff x.2).natDegree ≤ totalDegree f + totalDegree g - k := by
    intro x hx
    have hij : x.1 + x.2 = k := Finset.mem_antidiagonal.mp hx
    by_cases hfx : f.coeff x.1 = 0
    · simp [hfx]
    · by_cases hgx : g.coeff x.2 = 0
      · simp [hgx]
      · have hf_le : (f.coeff x.1).natDegree + x.1 ≤ totalDegree f :=
          coeff_totalDegree_le f (Polynomial.mem_support_iff.2 hfx)
        have hg_le : (g.coeff x.2).natDegree + x.2 ≤ totalDegree g :=
          coeff_totalDegree_le g (Polynomial.mem_support_iff.2 hgx)
        have hmul_le := Polynomial.natDegree_mul_le (p := f.coeff x.1) (q := g.coeff x.2)
        omega
  -- k ∈ (f*g).support means some f.coeff i * g.coeff j ≠ 0 with i + j = k
  -- Hence i ∈ f.support, j ∈ g.support, and k ≤ totalDegree f + totalDegree g
  have hk_le : k ≤ totalDegree f + totalDegree g := by
    have hcoeff_ne : (f * g).coeff k ≠ 0 := Polynomial.mem_support_iff.mp hk_supp
    rw [Polynomial.coeff_mul] at hcoeff_ne
    obtain ⟨⟨i, j⟩, hij_mem, hij_ne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hcoeff_ne
    have hij : i + j = k := Finset.mem_antidiagonal.mp hij_mem
    have hfi : f.coeff i ≠ 0 := left_ne_zero_of_mul hij_ne
    have hgj : g.coeff j ≠ 0 := right_ne_zero_of_mul hij_ne
    have hi_supp : i ∈ f.support := Polynomial.mem_support_iff.mpr hfi
    have hj_supp : j ∈ g.support := Polynomial.mem_support_iff.mpr hgj
    have hi_le := coeff_totalDegree_le f hi_supp
    have hj_le := coeff_totalDegree_le g hj_supp
    omega
  have hsum_nd := Polynomial.natDegree_sum_le_of_forall_le
    (s := Finset.antidiagonal k)
    (f := fun x => f.coeff x.1 * g.coeff x.2)
    (n := totalDegree f + totalDegree g - k) hnd_le
  -- natDegree(sum) ≤ (td_f + td_g) - k, and k ≤ td_f + td_g
  -- so natDegree(sum) + k ≤ td_f + td_g
  calc (∑ x ∈ Finset.antidiagonal k, f.coeff x.1 * g.coeff x.2).natDegree + k
      ≤ (totalDegree f + totalDegree g - k) + k := Nat.add_le_add_right hsum_nd k
    _ = totalDegree f + totalDegree g := Nat.sub_add_cancel hk_le

/-- The total degree of the product of two bivariate polynomials is the sum of their total degrees.
-/
@[simp, grind _=_]
theorem totalDegree_mul [IsDomain F] {f g : F[X][Y]} (hf : f ≠ 0) (hg : g ≠ 0) :
    totalDegree (f * g) = totalDegree f + totalDegree g := by
  apply le_antisymm (totalDegree_mul_le f g)
  classical
  rcases exists_max_index_totalDegree f hf with ⟨mmf, hmmf, hmmf_deg, hmmf_max⟩
  rcases exists_max_index_totalDegree g hg with ⟨mmg, hmmg, hmmg_deg, hmmg_max⟩
  let N := mmf + mmg
  let deg := (f.coeff mmf).natDegree + (g.coeff mmg).natDegree
  let term : ℕ × ℕ → F[X] := fun x => f.coeff x.1 * g.coeff x.2
  have hmx : (mmf, mmg) ∈ Finset.antidiagonal N := by simp [N]
  have hfx0 : f.coeff mmf ≠ 0 := Polynomial.mem_support_iff.mp hmmf
  have hgx0 : g.coeff mmg ≠ 0 := Polynomial.mem_support_iff.mp hmmg
  have hterm_mx : (term (mmf, mmg)).natDegree = deg := by
    simpa [term, deg] using
      Polynomial.natDegree_mul (p := f.coeff mmf) (q := g.coeff mmg) hfx0 hgx0
  have hterm_other : ∀ y ∈ Finset.antidiagonal N, y ≠ (mmf, mmg) →
      (term y).natDegree < deg ∨ term y = 0 := by
    intro y hy hyne
    rcases y with ⟨i, j⟩
    have hij : i + j = mmf + mmg := by simpa [N] using Finset.mem_antidiagonal.mp hy
    have hlt : mmf < i ∨ mmg < j := by
      by_contra hcontra
      push_neg at hcontra
      have hi : i ≤ mmf := hcontra.1
      have hj : j ≤ mmg := hcontra.2
      have : i = mmf ∧ j = mmg := by omega
      exact hyne (by simp [this.1, this.2])
    cases hlt with
    | inl hi_lt =>
      have hfi := hmmf_max i hi_lt
      cases hfi with
      | inr hfi0 => exact Or.inr (by simp [term, hfi0])
      | inl hfi_lt =>
        by_cases hgj0 : g.coeff j = 0
        · exact Or.inr (by simp [term, hgj0])
        · left
          have hg_le : (g.coeff j).natDegree + j ≤ totalDegree g := by
            rcases coeff_totalDegree_le' g j with h | h
            · exact h
            · exact absurd h hgj0
          have hnat_le : (term (i, j)).natDegree ≤
              (f.coeff i).natDegree + (g.coeff j).natDegree := by
            simpa [term] using Polynomial.natDegree_mul_le (p := f.coeff i) (q := g.coeff j)
          have hsum_lt : (f.coeff i).natDegree + (g.coeff j).natDegree < deg := by
            change _ < (f.coeff mmf).natDegree + (g.coeff mmg).natDegree
            have h1 := Nat.add_lt_add_of_lt_of_le hfi_lt hg_le
            have h2 : totalDegree f + totalDegree g =
                ((f.coeff mmf).natDegree + mmf) + ((g.coeff mmg).natDegree + mmg) := by
              rw [hmmf_deg, hmmg_deg]
            omega
          exact lt_of_le_of_lt hnat_le hsum_lt
    | inr hj_lt =>
      have hgj := hmmg_max j hj_lt
      cases hgj with
      | inr hgj0 => exact Or.inr (by simp [term, hgj0])
      | inl hgj_lt =>
        by_cases hfi0 : f.coeff i = 0
        · exact Or.inr (by simp [term, hfi0])
        · left
          have hf_le : (f.coeff i).natDegree + i ≤ totalDegree f := by
            rcases coeff_totalDegree_le' f i with h | h
            · exact h
            · exact absurd h hfi0
          have hnat_le : (term (i, j)).natDegree ≤
              (f.coeff i).natDegree + (g.coeff j).natDegree := by
            simpa [term] using Polynomial.natDegree_mul_le (p := f.coeff i) (q := g.coeff j)
          have hsum_lt : (f.coeff i).natDegree + (g.coeff j).natDegree < deg := by
            change _ < (f.coeff mmf).natDegree + (g.coeff mmg).natDegree
            have h1 := Nat.add_lt_add_of_le_of_lt hf_le hgj_lt
            have h2 : totalDegree f + totalDegree g =
                ((f.coeff mmf).natDegree + mmf) + ((g.coeff mmg).natDegree + mmg) := by
              rw [hmmf_deg, hmmg_deg]
            omega
          exact lt_of_le_of_lt hnat_le hsum_lt
  have hsum_nat : (∑ x ∈ Finset.antidiagonal N, term x).natDegree = deg :=
    natDegree_sum_eq_of_unique (mmf, mmg) hmx hterm_mx hterm_other
  have hcoeff_nat : ((f * g).coeff N).natDegree = deg := by
    have : (f * g).coeff N = ∑ x ∈ Finset.antidiagonal N, term x := by
      simpa [term] using Polynomial.coeff_mul f g N
    simpa [this] using hsum_nat
  have hcoeff_ne : (f * g).coeff N ≠ 0 := by
    intro h0
    have hfg_nd : ((f * g).coeff N).natDegree = 0 := by simp [h0]
    rw [hcoeff_nat] at hfg_nd
    -- deg = 0 means all other antidiag terms are zero (natDegree < 0 impossible)
    have hfg_sum : (f * g).coeff N = ∑ x ∈ Finset.antidiagonal N, term x := by
      simpa [term] using Polynomial.coeff_mul f g N
    -- Since deg = 0, all non-(mmf,mmg) terms are zero
    have hall_zero : ∀ y ∈ Finset.antidiagonal N, y ≠ (mmf, mmg) → term y = 0 := by
      intro y hy hyne
      rcases hterm_other y hy hyne with h | h
      · omega  -- natDegree < 0 impossible
      · exact h
    have : (f * g).coeff N = term (mmf, mmg) := by
      rw [hfg_sum]
      exact Finset.sum_eq_single_of_mem (mmf, mmg) hmx (fun y hy hyne => hall_zero y hy hyne)
    rw [this] at h0
    exact _root_.mul_ne_zero hfx0 hgx0 h0
  have hfg_support : N ∈ (f * g).support := Polynomial.mem_support_iff.2 hcoeff_ne
  have hle := coeff_totalDegree_le (f * g) hfg_support
  omega

/-- Definition of a monomial when the bivariate polynomial is considered as a univariate
polynomial in `Y`. -/
def monomialY (n : ℕ) : F[X] →ₗ[F[X]] F[X][Y] where
  toFun t := ⟨Finsupp.single n t⟩
  map_add' x y := by rw [Finsupp.single_add]; aesop
  map_smul' r x := by simp only [RingHom.id_apply, ofFinsupp_single]; rw [Polynomial.smul_monomial]

/-- Definition of the bivariate monomial `X^n * Y^m` -/
def monomialXY (n m : ℕ) : F →ₗ[F] F[X][Y] where
  toFun t := ⟨Finsupp.single m ⟨(Finsupp.single n t)⟩⟩
  map_add' x y := by
    simp only [ofFinsupp_single, map_add]
  map_smul' x y := by
    simp only [smul_eq_mul, ofFinsupp_single, RingHom.id_apply]
    rw [Polynomial.smul_monomial, Polynomial.smul_monomial]
    simp

/-- The bivariate monomial is well-defined. -/
@[grind _=_]
theorem monomialXY_def {n m : ℕ} {a : F} :
    monomialXY n m a = Polynomial.monomial m (Polynomial.monomial n a) := by
  unfold monomialXY
  simp

/-- Adding bivariate monomials works as expected.
In particular, `(a + b) * X^n * Y^m = a * X^n * Y^m + b * X^n * Y^m`. -/
@[simp, grind =]
theorem monomialXY_add {n m : ℕ} {a b : F} :
  monomialXY n m (a + b) = monomialXY n m a + monomialXY n m b :=
  (monomialXY n m).map_add _ _

/-- Multiplying bivariate monomials works as expected.
In particular, `(a * X^n * Y^m) * (b * X^p * Y^q) = (a * b) * X^(n+p) * Y^(m+q)`. -/
@[grind _=_]
theorem monomialXY_mul_monomialXY {n m p q : ℕ} {a b : F} :
    monomialXY n m a * monomialXY p q b = monomialXY (n + p) (m + q) (a * b) :=
  toFinsupp_injective <| by
  unfold monomialXY
  rw [@toFinsupp_mul, @AddMonoidAlgebra.mul_def]
  simp only [ofFinsupp_single, LinearMap.coe_mk, AddHom.coe_mk, Polynomial.toFinsupp_monomial,
    mul_zero, Finsupp.single_zero, Finsupp.sum_single_index, zero_mul]
  rw [@Polynomial.monomial_mul_monomial]

/-- Taking a bivariate monomial to a power works as expected.
In particular, ` (a * X^n * Y^m)^k = (a^k) * X^(n * k) * Y^(m * k)`. -/
@[simp, grind _=_]
theorem monomialXY_pow {n m k : ℕ} {a : F} :
  monomialXY n m a ^ k = monomialXY (n * k) (m * k) (a ^ k) := by
  simp [monomialXY]

/-- Multiplying a bivariate monomial by a scalar works as expected.
In particular, ` b * a * X^n * Y^m = b * (a * X^n * Y^m)`. -/
@[simp, grind _=_]
theorem smul_monomialXY {n m : ℕ} {a : F} {S} [SMulZeroClass S F] {b : S} :
  monomialXY n m (b • a) = b • monomialXY n m a := by
  grind [monomialXY]

/-- A bivariate monimial `a * X^n * Y^m` is equal to zero if and only if `a = 0`. -/
@[simp, grind =]
theorem monomialXY_eq_zero_iff {n m : ℕ} {a : F} : monomialXY n m a = 0 ↔ a = 0 := by
  simp [monomialXY]

/-- Two bivariate monomials `a * X^n * Y^m` and `b * X^p * Y^q` are equal if and only if `a = b`
`n = p` and `m = q` or if both are zero, i.e., `a = b = 0`. -/
@[grind =]
theorem monomialXY_eq_monomialXY_iff {n m p q : ℕ} {a b : F} :
  monomialXY n m a = monomialXY p q b ↔ n = p ∧ m = q ∧ a = b ∨ a = 0 ∧ b = 0 := by
  aesop (add simp [monomialXY, Polynomial.monomial_eq_monomial_iff])

/-- The total degree of the monomial `a * X^n * Y^m` is `n + m`. -/
@[simp, grind =]
lemma totalDegree_monomialXY {n m : ℕ} {a : F} (ha : a ≠ 0) :
  totalDegree (monomialXY n m a) = n + m := by
  classical
  have hma : Polynomial.monomial n a ≠ 0 := by simp [ha]
  unfold totalDegree
  rw [monomialXY_def, Polynomial.support_monomial _ hma]
  simp [Polynomial.natDegree_monomial_eq n ha]

/-- The `X`-degree of the monomial `a * X^n * Y^m` is `n`. -/
@[simp]
lemma degreeX_monomialXY {n m : ℕ} {a : F} (ha : a ≠ 0) :
    degreeX (monomialXY n m a) = n := by
  classical
  have hma : Polynomial.monomial n a ≠ 0 := by simp [ha]
  unfold degreeX
  rw [monomialXY_def, Polynomial.support_monomial _ hma]
  simp [Polynomial.natDegree_monomial_eq n ha]

/-- The `Y`-degree of the monomial `a * X^n * Y^m` is `m`. -/
@[simp]
lemma degreeY_monomialXY {n m : ℕ} {a : F} (ha : a ≠ 0) :
  natDegreeY (monomialXY n m a) = m := by
  classical
  have hma : Polynomial.monomial n a ≠ 0 := by simp [ha]
  unfold natDegreeY
  rw [monomialXY_def, Polynomial.natDegree_monomial_eq m hma]

/-- `(a,b)`-weighted degree of a monomial `X^i * Y^j` -/
def weightedDegreeMonomialXY {n m : ℕ} (a b t : ℕ) : ℕ :=
  a * (degreeX (monomialXY n m t)) + b * natDegreeY (monomialXY n m t)

/-- `evalX` is multiplicative. -/
lemma evalX_mul {F : Type} [CommSemiring F] (x : F) (f g : F[X][Y]) :
    evalX x (f * g) = evalX x f * evalX x g := by
  simp [evalX_eq_map]

end
end Polynomial.Bivariate

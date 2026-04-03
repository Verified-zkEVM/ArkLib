/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Katerina Hristova, František Silváši, Julian Sutherland, Ilia Vlasov
-/

import ArkLib.Data.Polynomial.Prelims

import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
/-!
  # Definitions and Theorems about Bivariate Polynomials with coefficients in a semiring

  We develop the basic definitions needed to argue about bivariate polynomials and monomials
  explictly.

## Main Definitions

  The file is organised as follows:
   - We start off by defining coeffiecients of bivariate polynomials, the degrees in
   `X` and `Y`, total degree and weighted degree. We expess the `X`- `Y` and total degrees as
   weighted degrees and prove the equivalence of the definitions.
   - We define root multiplicity, discriminant and resultant.
   - We prove that the `X`-degree of a product of two bivariate polynomials is the sum of their
   individual `X`-degrees.
   - We define and prove some basic properties about quotients of bivariate polynomials.
   - We define and prove some basic properties of monomials of bivariate polynomials.

-/

open Polynomial
open Polynomial.Bivariate

namespace Polynomial.Bivariate

noncomputable section

variable {F : Type} [Semiring F]

/-- The set of coefficients of a bivariate polynomial. -/
def coeffs [DecidableEq F] (f : F[X][Y]) : Finset F[X] := f.support.image f.coeff

/-- `(i, j)`-coefficient of a polynomial, i.e. the coefficient of `X^i Y^j`.
-/
def coeff.{u} {F : Type u} [Semiring F] (f : F[X][Y]) (i j : ℕ) : F := (f.coeff j).coeff i

/-- The polynomial coefficient of the highest power of `Y`. This is the leading coefficient in the
classical sense if the bivariate polynomial is interpreted as a univariate polynomial over `F[X]`.
-/
def leadingCoeffY (f : F[X][Y]) : F[X] := f.coeff (natDegree f)

/-- The polynomial coefficient of the highest power of `Y` is `0` if and only if the bivariate
polynomial is the zero polynomial. -/
@[simp, grind =]
theorem leadingCoeffY_eq_zero (f : F[X][Y]) : leadingCoeffY f = 0 ↔ f = 0 :=
  ⟨fun h =>
    Classical.by_contradiction fun hp =>
      mt mem_support_iff.1 (Classical.not_not.2 h) (Finset.mem_of_max (degree_eq_natDegree hp)),
    fun h => h.symm ▸ leadingCoeff_zero⟩

/-- The polynomial coefficient of the highest power of `Y` is not `0` if and only if the
bivariate polynomial is non-zero. -/
@[simp, grind =]
lemma leadingCoeffY_ne_zero (f : F[X][Y]) : leadingCoeffY f ≠ 0 ↔ f ≠ 0 := by
  rw [Ne, leadingCoeffY_eq_zero]

/-- A bivariate polynomial is non-zero if and only if all its coefficients are non-zero. -/
@[grind =_]
lemma ne_zero_iff_coeffs_ne_zero (f : F[X][Y]) : f ≠ 0 ↔ f.coeff ≠ 0 :=
  ⟨
    fun hf ↦ by have f_finsupp : f.toFinsupp ≠ 0 := by aesop
                simpa [Polynomial.coeff],
    fun f_coeffs ↦ by aesop (add simp Polynomial.coeff)
  ⟩

/--
The `Y`-degree of a bivariate polynomial, as a natural number.
-/
def natDegreeY (f : F[X][Y]) : ℕ := Polynomial.natDegree f

/-- The set of `Y`-degrees is non-empty. -/
lemma degreesY_nonempty {f : F[X][Y]} (hf : f ≠ 0) : (f.toFinsupp.support).Nonempty :=
  Finsupp.support_nonempty_iff.mpr
    fun h ↦ hf (Polynomial.ext (fun n => by rw [← Polynomial.toFinsupp_apply, h]; rfl))

/-- The `X`-degree of a bivariate polynomial. -/
def degreeX (f : F[X][Y]) : ℕ := f.support.sup (fun n => (f.coeff n).natDegree)

/-- The total degree of a bivariate polynomial. -/
def totalDegree (f : F[X][Y]) : ℕ :=
  f.support.sup (fun m => (f.coeff m).natDegree + m)

/-- `(u,v)`-weighted degree of a polynomial.
The maximal `u * i + v * j` such that the polynomial `p`
contains a monomial `x^i * y^j`. -/
def weightedDegree.{u} {F : Type u} [Semiring F] (p : F[X][Y]) (u v : ℕ) : Option ℕ :=
  List.max? <|
    List.map (fun n => u * (p.coeff n).natDegree + v * n) (List.range p.natDegree.succ)

def natWeightedDegree.{u} {F : Type u} [Semiring F] (f : F[X][Y]) (u v : ℕ) : ℕ :=
  f.support.sup (fun m => u * (f.coeff m).natDegree + v * m)

variable {f : F[X][Y]}

/-- The weighted degree is always defined (never none). -/
lemma weightedDegree_ne_none {F : Type} [Semiring F] (f : F[X][Y]) (u v : ℕ) :
    weightedDegree f u v ≠ none := by
  unfold weightedDegree; aesop

theorem natWeightedDegree_mem_weight_list {u v : ℕ} (hf : f ≠ 0) :
    natWeightedDegree f u v ∈
      List.map (fun n => u * (f.coeff n).natDegree + v * n)
        (List.range f.natDegree.succ) := by
  classical
  have hsupp : f.support.Nonempty := by
    refine ⟨f.natDegree, ?_⟩
    exact Polynomial.natDegree_mem_support_of_nonzero (p := f) hf
  obtain ⟨m, hm, hsup⟩ :=
    Finset.exists_mem_eq_sup (s := f.support) hsupp
      (fun n => u * (f.coeff n).natDegree + v * n)
  have hm_le : m ≤ f.natDegree := Polynomial.le_natDegree_of_mem_supp (p := f) m hm
  have hm_range : m ∈ List.range f.natDegree.succ := by
    exact List.mem_range.mpr (Nat.lt_succ_of_le hm_le)
  have hw_mem :
      (u * (f.coeff m).natDegree + v * m) ∈
        List.map (fun n => u * (f.coeff n).natDegree + v * n)
          (List.range f.natDegree.succ) := by
    exact List.mem_map_of_mem (f := fun n => u * (f.coeff n).natDegree + v * n) hm_range
  unfold natWeightedDegree
  simpa [hsup] using hw_mem

theorem weight_le_natWeightedDegree_of_lt_natDegree_succ {u v n : ℕ} (hf : f ≠ 0) (hn : n < f.natDegree.succ) :
    u * (f.coeff n).natDegree + v * n ≤ natWeightedDegree f u v := by
  classical
  unfold natWeightedDegree
  by_cases hns : n ∈ f.support
  ·
    exact
      Finset.le_sup (f := fun m => u * (f.coeff m).natDegree + v * m) hns
  ·
    have hcoeff : f.coeff n = 0 := Polynomial.notMem_support_iff.1 hns
    have hnle : n ≤ f.natDegree := Nat.lt_succ_iff.mp hn
    have hmul : v * n ≤ v * f.natDegree := Nat.mul_le_mul_left v hnle
    have hdegmem : f.natDegree ∈ f.support := Polynomial.natDegree_mem_support_of_nonzero hf
    have hsup : u * (f.coeff f.natDegree).natDegree + v * f.natDegree ≤
        f.support.sup (fun m => u * (f.coeff m).natDegree + v * m) := by
      exact
        Finset.le_sup (f := fun m => u * (f.coeff m).natDegree + v * m) hdegmem
    have hvdeg : v * f.natDegree ≤ u * (f.coeff f.natDegree).natDegree + v * f.natDegree := by
      exact Nat.le_add_left _ _
    have hvdeg' : v * f.natDegree ≤
        f.support.sup (fun m => u * (f.coeff m).natDegree + v * m) :=
      le_trans hvdeg hsup
    have : v * n ≤ f.support.sup (fun m => u * (f.coeff m).natDegree + v * m) :=
      le_trans hmul hvdeg'
    simpa [hcoeff] using this

@[grind _=_]
lemma weightedDegree_eq_natWeightedDegree {u v : ℕ} :
  f ≠ 0 → weightedDegree f u v = natWeightedDegree f u v := by
  intro hf
  let w : ℕ → ℕ := fun n => u * (f.coeff n).natDegree + v * n
  let xs : List ℕ := List.map w (List.range f.natDegree.succ)
  have ha : natWeightedDegree f u v ∈ xs := by
    simpa [xs, w] using (natWeightedDegree_mem_weight_list (f := f) (u := u) (v := v) hf)
  have hle : ∀ b, b ∈ xs → b ≤ natWeightedDegree f u v := by
    intro b hb
    rcases List.mem_map.1 hb with ⟨n, hn, rfl⟩
    have hnlt : n < f.natDegree.succ := (List.mem_range.1 hn)
    exact
      weight_le_natWeightedDegree_of_lt_natDegree_succ (f := f) (u := u) (v := v) (n := n) hf hnlt
  have hmax : xs.max? = some (natWeightedDegree f u v) := by
    apply (List.max?_eq_some_iff (xs := xs) (a := natWeightedDegree f u v)).2
    refine ⟨ha, ?_⟩
    intro b hb
    exact hle b hb
  simpa [weightedDegree, xs, w] using hmax


/-- The total degree of a bivariate polynomial is equal to the `(1,1)`-weighted degree -/
@[grind _=_]
lemma total_deg_as_weighted_deg :
  totalDegree f = natWeightedDegree f 1 1 := by
  unfold natWeightedDegree totalDegree
  simp

/-- The `X`-degree of a bivariate polynomial is equal to the `(1,0)`-weighted degree. -/
@[grind _=_]
lemma degreeX_as_weighted_deg :
  degreeX f = natWeightedDegree f 1 0 := by
  grind [degreeX, natWeightedDegree]

/-- The `Y`-degree of a bivariate polynomial is equal to the `(0,1)`-weighted degree. -/
@[grind _=_]
lemma degreeY_as_weighted_deg (hf : f ≠ 0) :
  natDegreeY f = natWeightedDegree f 0 1 := by
  rw [
    natDegreeY, natWeightedDegree,
    Polynomial.natDegree_eq_support_max' (p := f) hf, Finset.max'_eq_sup'
  ]
  simp [Finset.sup'_eq_sup]

/-- Root multiplicity of a bivariate polynomial. -/
def rootMultiplicity₀.{u} {F : Type u} [Semiring F] [DecidableEq F] (f : F[X][Y]) : Option ℕ :=
  let deg := weightedDegree f 1 1
  match deg with
  | none => none
  | some deg => List.min?
    (List.filterMap
      (fun p ↦ if coeff f p.1 p.2 = 0 then none else some (p.1 + p.2))
        (List.product (List.range deg.succ) (List.range deg.succ)))

/-- Root multiplicity (order of vanishing) of a bivariate polynomial at `(x,y)`.
It is the smallest total degree `s+t` of a nonzero coefficient after shifting
the root to `(0,0)`. The zero polynomial has multiplicity `none`. -/
def rootMultiplicity.{u} {F : Type u} [CommSemiring F] [DecidableEq F]
    (f : F[X][Y]) (x y : F) : Option ℕ :=
  rootMultiplicity₀ <| (f.comp (Y + C (C y))).map (Polynomial.compRingHom (X + C x))

/-- If the multiplicity of a pair `(x,y)` is non-negative, then the pair is a root of `f`. -/
theorem rootMultiplicity_some_implies_root {F : Type} [CommRing F]
  {x y : F} {f : F[X][Y]} (h : 0 < ((f.eval (C y)).rootMultiplicity x))
  : (f.eval (C y)).eval x = 0 := by
  simp_all only [rootMultiplicity_pos', ne_eq, IsRoot.def]

open Univariate in
/-- In the case of a bivariate polynomial we cannot easily use `discriminant`.
   We are using the fact that the resultant in question is always
   divisible by the leading coefficient of the polynomial.
-/
def discr_y {F : Type} [CommRing F] (f : F[X][Y]) : F[X] :=
  /- TODO: use `Polynomial.discr` once Mathlib is bumped. -/
  by
    classical
    by_cases h : 0 < f.degree
    · exact Classical.choose (resultant_is_divisible_by_leadingCoeff f h)
    · exact 0

/-- Over an intergal domain, the product of two non-zero bivariate polynomials is non-zero. -/
@[grind ←]
lemma mul_ne_zero [IsDomain F] (f g : F[X][Y]) (hf : f ≠ 0) (hg : g ≠ 0) :
  f * g ≠ 0 := _root_.mul_ne_zero hf hg

/-- Over an integral domain, the `Y`-degree of the product of two non-zero bivariate polynomials is
equal to the sum of their degrees. -/
@[simp, grind _=_]
lemma degreeY_mul [IsDomain F] (f g : F[X][Y]) (hf : f ≠ 0) (hg : g ≠ 0)
  : natDegreeY (f * g) = natDegreeY f + natDegreeY g := by
  unfold natDegreeY
  rw [←leadingCoeffY_ne_zero] at hf hg
  have h_lc : leadingCoeffY f * leadingCoeffY g ≠ 0 := _root_.mul_ne_zero hf hg
  exact Polynomial.natDegree_mul' h_lc

attribute [local grind] Finsupp.support_nonempty_iff natDegree_mul_le degree_eq_bot
                        WithBot.bot_lt_coe isMaxOn_iff sup_eq_of_isMaxOn monomial_eq_monomial_iff
attribute [local grind ←] toFinsupp_eq_zero
attribute [local grind _=_] Finsupp.mem_support_iff toFinsupp_apply smul_monomial
attribute [local grind =] natDegree_mul natDegree_add_eq_right_of_degree_lt
                          natDegree_zero
@[local grind _=_]
private lemma support_eq_support_toFinsupp {f : F[X][Y]} : f.support = f.toFinsupp.support := rfl

theorem natDegree_sum_lt_of_forall_lt {F : Type} [Semiring F] {α : Type} {s : Finset α} {g : α → F[X]} {deg : ℕ} :
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
  ·
    have hothers0 : ∀ y ∈ s, y ≠ mx → f y = 0 := by
      intro y hy hne
      have h' := others y hy hne
      rcases h' with hlt | hy0
      · have hlt0 : (f y).natDegree < 0 := by simpa [hdeg0] using hlt
        exact (False.elim ((Nat.not_lt_zero _ ) hlt0))
      · exact hy0
    have hsum : (∑ x ∈ s, f x) = f mx := by
      classical
      refine Finset.sum_eq_single_of_mem mx h ?_?
      intro y hy hne
      exact hothers0 y hy hne
    calc
      (∑ x ∈ s, f x).natDegree = (f mx).natDegree := by simpa [hsum]
      _ = deg := hmxdeg
  ·
    have deg_pos : 0 < deg := Nat.pos_of_ne_zero hdeg0
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
        simpa [hsum_decomp]
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

theorem coeff_natDegree_le_degreeX (f : F[X][Y]) (n : ℕ) : (f.coeff n).natDegree ≤ degreeX f := by
  classical
  unfold degreeX
  by_cases hn : n ∈ f.support
  ·
    exact (Finset.le_sup (s := f.support) (f := fun m => (f.coeff m).natDegree) hn)
  ·
    have hcoeff : f.coeff n = 0 := by
      exact Polynomial.notMem_support_iff.mp hn
    simpa [hcoeff] using (Nat.zero_le (f.support.sup fun m => (f.coeff m).natDegree))


theorem degreeX_mul_le (f g : F[X][Y]) : degreeX (f * g) ≤ degreeX f + degreeX g := by
  classical
  unfold degreeX
  refine Finset.sup_le ?_
  intro k hk
  rw [Polynomial.coeff_mul]
  refine Polynomial.natDegree_sum_le_of_forall_le
    (s := Finset.antidiagonal k)
    (f := fun x : ℕ × ℕ => f.coeff x.1 * g.coeff x.2)
    (n := degreeX f + degreeX g) ?_
  intro x hx
  have hf : (f.coeff x.1).natDegree ≤ degreeX f := coeff_natDegree_le_degreeX f x.1
  have hg : (g.coeff x.2).natDegree ≤ degreeX g := coeff_natDegree_le_degreeX g x.2
  exact le_trans (Polynomial.natDegree_mul_le (p := f.coeff x.1) (q := g.coeff x.2))
    (Nat.add_le_add hf hg)


theorem exists_max_index_degreeX (f : F[X][Y]) (hf : f ≠ 0) :
  ∃ mm ∈ f.support,
    (f.coeff mm).natDegree = degreeX f ∧
    ∀ n, mm < n → (f.coeff n).natDegree < degreeX f ∨ f.coeff n = 0 := by
  classical
  -- indices in the support where the X-degree of the coefficient attains `degreeX f`
  let s₁ : Finset ℕ := f.support.filter (fun n => (f.coeff n).natDegree = degreeX f)
  have hs₁ : s₁.Nonempty := by
    have hsupp : f.support.Nonempty := (Polynomial.support_nonempty).2 hf
    obtain ⟨m, hm_mem, hm_sup⟩ :=
      Finset.exists_mem_eq_sup (s := f.support) (h := hsupp)
        (f := fun n => (f.coeff n).natDegree)
    refine ⟨m, ?_⟩
    -- `m` is in the filter because its coefficient reaches the supremum, i.e. `degreeX f`
    have hm_deg : (f.coeff m).natDegree = degreeX f := by
      -- unfold `degreeX` and use the characterization of `m`
      simpa [Polynomial.Bivariate.degreeX] using hm_sup.symm
    -- now show membership in the filtered set
    simp [s₁, hm_mem, hm_deg]

  set mm : ℕ := s₁.max' hs₁ with hmm
  refine ⟨mm, ?_, ?_, ?_⟩
  · -- `mm` lies in the support
    have hmm_mem : mm ∈ s₁ := by
      simpa [hmm] using (Finset.max'_mem s₁ hs₁)
    -- unpack membership in the filter
    have : mm ∈ f.support ∧ (f.coeff mm).natDegree = degreeX f := by
      simpa [s₁] using (Finset.mem_filter.1 hmm_mem)
    exact this.1
  · -- coefficient at `mm` has maximal X-degree
    have hmm_mem : mm ∈ s₁ := by
      simpa [hmm] using (Finset.max'_mem s₁ hs₁)
    have : mm ∈ f.support ∧ (f.coeff mm).natDegree = degreeX f := by
      simpa [s₁] using (Finset.mem_filter.1 hmm_mem)
    exact this.2
  · -- maximality among indices attaining `degreeX f`
    have hmm_mem : mm ∈ s₁ := by
      simpa [hmm] using (Finset.max'_mem s₁ hs₁)
    have hmm_upper : ∀ b ∈ s₁, b ≤ mm := by
      -- characterize `mm` as the maximum of `s₁`
      have hchar : mm ∈ s₁ ∧ ∀ b, b ∈ s₁ → b ≤ mm := by
        -- `mm = s₁.max' hs₁`
        simpa [hmm] using
          (Finset.max'_eq_iff (s := s₁) (H := hs₁) (a := mm)).1 rfl
      exact fun b hb => hchar.2 b hb

    intro n hmn
    by_cases hn0 : f.coeff n = 0
    · exact Or.inr hn0
    · -- otherwise, show strict inequality of degrees
      have hn_support : n ∈ f.support := by
        -- `n` is in the support iff its coefficient is nonzero
        exact (Polynomial.mem_support_iff).2 hn0
      have hn_le : (f.coeff n).natDegree ≤ degreeX f := coeff_natDegree_le_degreeX f n
      have hn_ne : (f.coeff n).natDegree ≠ degreeX f := by
        intro hEq
        have hn_s₁ : n ∈ s₁ := by
          simp [s₁, hn_support, hEq]
        have hn_le_mm : n ≤ mm := hmm_upper n hn_s₁
        exact (not_le_of_gt hmn) hn_le_mm
      exact Or.inl (lt_of_le_of_ne hn_le hn_ne)


theorem natDegree_sum_eq_of_unique {α : Type} {s : Finset α} {f : α → F[X]} {deg : ℕ} (mx : α) (hmx : mx ∈ s) :
    (f mx).natDegree = deg →
    (∀ y ∈ s, y ≠ mx → (f y).natDegree < deg ∨ f y = 0) →
    (∑ x ∈ s, f x).natDegree = deg := by
  intro hdeg hothers
  classical
  have hle : ∀ y ∈ s, (f y).natDegree ≤ deg := by
    intro y hy
    by_cases hym : y = mx
    · subst hym
      simpa [hdeg]
    · have hy' := hothers y hy hym
      cases hy' with
      | inl hlt =>
          exact le_of_lt hlt
      | inr hy0 =>
          simpa [hy0] using (Nat.zero_le deg)
  have hSle : (∑ x ∈ s, f x).natDegree ≤ deg :=
    Polynomial.natDegree_sum_le_of_forall_le (s := s) (f := f) (n := deg) hle
  by_cases hdeg0 : deg = 0
  · subst hdeg0
    exact Nat.eq_zero_of_le_zero hSle
  · have hmx_ne0 : f mx ≠ 0 := by
      intro h0
      apply hdeg0
      have : (0 : ℕ) = deg := by
        simpa [h0] using hdeg
      exact this.symm
    have hmx_coeff_ne0 : (f mx).coeff deg ≠ 0 := by
      have hlc : (f mx).leadingCoeff ≠ 0 :=
        (Polynomial.leadingCoeff_ne_zero).2 hmx_ne0
      simpa [Polynomial.leadingCoeff, hdeg] using hlc
    have hcoeff_others : ∀ y ∈ s, y ≠ mx → (f y).coeff deg = 0 := by
      intro y hy hym
      have hy' := hothers y hy hym
      cases hy' with
      | inl hlt =>
          exact Polynomial.coeff_eq_zero_of_natDegree_lt hlt
      | inr hy0 =>
          simpa [hy0]
    have hsum_coeff : (∑ y ∈ s, (f y).coeff deg) = (f mx).coeff deg := by
      refine Finset.sum_eq_single_of_mem mx hmx ?_
      intro y hy hym
      exact hcoeff_others y hy hym
    have hcoeff_eq : (∑ x ∈ s, f x).coeff deg = (f mx).coeff deg := by
      rw [Polynomial.finset_sum_coeff (s := s) (f := f) (n := deg)]
      exact hsum_coeff
    have hcoeff_ne0 : (∑ x ∈ s, f x).coeff deg ≠ 0 := by
      simpa [hcoeff_eq] using hmx_coeff_ne0
    exact Polynomial.natDegree_eq_of_le_of_coeff_ne_zero hSle hcoeff_ne0

theorem degreeX_mul_ge [IsDomain F] (f g : F[X][Y]) (hf : f ≠ 0) (hg : g ≠ 0) :
  degreeX f + degreeX g ≤ degreeX (f * g) := by
  classical
  rcases exists_max_index_degreeX f hf with ⟨mmfx, hmmfx, hmmfx_deg, hmmfx_max⟩
  rcases exists_max_index_degreeX g hg with ⟨mmgx, hmmgx, hmmgx_deg, hmmgx_max⟩
  let N : ℕ := mmfx + mmgx
  let deg : ℕ := degreeX f + degreeX g
  let term : ℕ × ℕ → F[X] := fun x => f.coeff x.1 * g.coeff x.2
  have hmx : (mmfx, mmgx) ∈ Finset.antidiagonal N := by
    simp [Finset.mem_antidiagonal, N]
  have hfx0 : f.coeff mmfx ≠ 0 := by
    exact (mem_support_iff.mp hmmfx)
  have hgx0 : g.coeff mmgx ≠ 0 := by
    exact (mem_support_iff.mp hmmgx)
  have hterm_mx : (term (mmfx, mmgx)).natDegree = deg := by
    simpa [term, deg, hmmfx_deg, hmmgx_deg] using
      (Polynomial.natDegree_mul (p := f.coeff mmfx) (q := g.coeff mmgx) hfx0 hgx0)
  have hterm_other :
      ∀ y ∈ Finset.antidiagonal N, y ≠ (mmfx, mmgx) →
        (term y).natDegree < deg ∨ term y = 0 := by
    intro y hy hyne
    rcases y with ⟨i, j⟩
    have hij : i + j = N := by
      simpa [Finset.mem_antidiagonal] using hy
    have hij' : i + j = mmfx + mmgx := by
      simpa [N] using hij
    have hlt : mmfx < i ∨ mmgx < j := by
      by_contra hcontra
      have hi : i ≤ mmfx :=
        le_of_not_gt (fun hlt => hcontra (Or.inl hlt))
      have hj : j ≤ mmgx :=
        le_of_not_gt (fun hlt => hcontra (Or.inr hlt))
      have h1 : i + j ≤ i + mmgx := Nat.add_le_add_left hj i
      have h2 : mmfx + mmgx ≤ i + mmgx := by
        simpa [hij'] using h1
      have hmmfx_le_i : mmfx ≤ i := (Nat.add_le_add_iff_right).1 h2
      have h3 : i + j ≤ mmfx + j := Nat.add_le_add_right hi j
      have h4 : mmfx + mmgx ≤ mmfx + j := by
        simpa [hij'] using h3
      have hmmgx_le_j : mmgx ≤ j := (Nat.add_le_add_iff_left).1 h4
      have hi_eq : i = mmfx := Nat.le_antisymm hi hmmfx_le_i
      have hj_eq : j = mmgx := Nat.le_antisymm hj hmmgx_le_j
      exact hyne (by
        cases hi_eq
        cases hj_eq
        rfl)
    cases hlt with
    | inl hi_lt =>
        have hfi : (f.coeff i).natDegree < degreeX f ∨ f.coeff i = 0 :=
          hmmfx_max i hi_lt
        cases hfi with
        | inr hfi0 =>
            right
            simp [term, hfi0]
        | inl hfi_lt =>
            by_cases hgj0 : g.coeff j = 0
            · right
              simp [term, hgj0]
            · left
              have hnat_le : (term (i, j)).natDegree ≤ (f.coeff i).natDegree + (g.coeff j).natDegree := by
                simpa [term] using
                  (Polynomial.natDegree_mul_le (p := f.coeff i) (q := g.coeff j))
              have hgj_le : (g.coeff j).natDegree ≤ degreeX g :=
                coeff_natDegree_le_degreeX g j
              have hsum_lt : (f.coeff i).natDegree + (g.coeff j).natDegree < deg := by
                have := Nat.add_lt_add_of_lt_of_le hfi_lt hgj_le
                simpa [deg] using this
              exact lt_of_le_of_lt hnat_le hsum_lt
    | inr hj_lt =>
        have hgj : (g.coeff j).natDegree < degreeX g ∨ g.coeff j = 0 :=
          hmmgx_max j hj_lt
        cases hgj with
        | inr hgj0 =>
            right
            simp [term, hgj0]
        | inl hgj_lt =>
            by_cases hfi0 : f.coeff i = 0
            · right
              simp [term, hfi0]
            · left
              have hnat_le : (term (i, j)).natDegree ≤ (f.coeff i).natDegree + (g.coeff j).natDegree := by
                simpa [term] using
                  (Polynomial.natDegree_mul_le (p := f.coeff i) (q := g.coeff j))
              have hfi_le : (f.coeff i).natDegree ≤ degreeX f :=
                coeff_natDegree_le_degreeX f i
              have hsum_lt : (f.coeff i).natDegree + (g.coeff j).natDegree < deg := by
                have := Nat.add_lt_add_of_le_of_lt hfi_le hgj_lt
                simpa [deg] using this
              exact lt_of_le_of_lt hnat_le hsum_lt
  have hsum_nat : (∑ x ∈ Finset.antidiagonal N, term x).natDegree = deg := by
    exact natDegree_sum_eq_of_unique (mx := (mmfx, mmgx)) (hmx := hmx) hterm_mx hterm_other
  have hcoeff_nat : ((f * g).coeff N).natDegree = deg := by
    have hcoeff : (f * g).coeff N = ∑ x ∈ Finset.antidiagonal N, term x := by
      simpa [term] using (Polynomial.coeff_mul f g N)
    -- rewrite using hcoeff
    simpa [hcoeff] using hsum_nat
  have hle : deg ≤ degreeX (f * g) := by
    have hle' : ((f * g).coeff N).natDegree ≤ degreeX (f * g) :=
      coeff_natDegree_le_degreeX (f * g) N
    simpa [hcoeff_nat] using hle'
  simpa [deg] using hle

theorem degreeX_mul [IsDomain F] (f g : F[X][Y]) (hf : f ≠ 0) (hg : g ≠ 0) :
  degreeX (f * g) = degreeX f + degreeX g := by
  exact le_antisymm (degreeX_mul_le f g) (degreeX_mul_ge f g hf hg)


  -- letI s₁ := {n ∈ f.support | (f.coeff n).natDegree = degreeX f}
  -- letI s₂ := {n ∈ g.support | (g.coeff n).natDegree = degreeX g}
  -- have f_mdeg_nonempty : s₁.Nonempty := by
  --   obtain ⟨mfx, _, _⟩ :=
  --     Finset.exists_mem_eq_sup _ (show f.support.Nonempty by grind) fun n ↦ (f.coeff n).natDegree
  --   use mfx
  --   grind [degreeX]
  -- have g_mdeg_nonempty : s₂.Nonempty := by
  --   obtain ⟨mfx, _, _⟩ :=
  --     Finset.exists_mem_eq_sup _ (show g.support.Nonempty by grind) fun n ↦ (g.coeff n).natDegree
  --   use mfx
  --   grind [degreeX]
  -- set mmfx := s₁.max' f_mdeg_nonempty with hmmfx
  -- set mmgx := s₂.max' g_mdeg_nonempty with hmmgx
  -- have mmfx_def : (f.coeff mmfx).natDegree = degreeX f := by
  --   have h := Finset.max'_mem _ f_mdeg_nonempty
  --   grind
  -- have mmgx_def : (g.coeff mmgx).natDegree = degreeX g := by
  --   have h := Finset.max'_mem _ g_mdeg_nonempty
  --   grind
  -- have h₁ : mmfx ∈ s₁ := Finset.max'_mem _ f_mdeg_nonempty
  -- have h₂ : mmgx ∈ s₂ := Finset.max'_mem _ g_mdeg_nonempty
  -- have mmfx_neq_0 : f.coeff mmfx ≠ 0 := by grind
  -- have mmgx_neq_0 : g.coeff mmgx ≠ 0 := by grind
  -- have h₁ {n} : (f.coeff n).natDegree ≤ degreeX f := by
  --   have : degreeX f = (f.coeff mmfx).natDegree := by grind
  --   by_cases h : n ∈ f.toFinsupp.support
  --   · convert Finset.sup_le_iff.mp (le_of_eq this) n h
  --   · simp [Polynomial.notMem_support_iff.1 h]
  -- have h₂ {n} : (g.coeff n).natDegree ≤ (g.coeff mmgx).natDegree := by
  --   have : degreeX g = (g.coeff mmgx).natDegree := by grind
  --   by_cases h : n ∈ g.toFinsupp.support
  --   · convert Finset.sup_le_iff.mp (le_of_eq this) n h
  --   · simp [Polynomial.notMem_support_iff.1 h]
  -- have h₁' {n} (h : mmfx < n) :
  --   (f.coeff n).natDegree < (f.coeff mmfx).natDegree ∨ f.coeff n = 0 := by
  --   suffices f.coeff n ≠ 0 → (f.coeff mmfx).natDegree ≤ (f.coeff n).natDegree → False by grind
  --   intros h' contra
  --   have : (f.coeff mmfx).natDegree = (f.coeff n).natDegree := by grind
  --   have : n ≤ mmfx := Finset.le_sup'_of_le (hb := show n ∈ s₁ by grind) (h := by simp)
  --   grind
  -- have h₂' {n} (h : mmgx < n) :
  --   (g.coeff n).natDegree < (g.coeff mmgx).natDegree ∨ g.coeff n = 0 := by
  --   suffices g.coeff n ≠ 0 → (g.coeff mmgx).natDegree ≤ (g.coeff n).natDegree → False by grind
  --   intros h' contra
  --   have : (g.coeff mmgx).natDegree = (g.coeff n).natDegree := by grind
  --   have : n ≤ mmgx := Finset.le_sup'_of_le (hb := show n ∈ s₂ by grind) (h := by simp)
  --   grind
  -- unfold degreeX
  -- have : (fun n ↦ ((f * g).coeff n).natDegree) =
  --        fun n ↦ (∑ x ∈ Finset.antidiagonal n, f.coeff x.1 * g.coeff x.2).natDegree := by
  --   funext n; rw [Polynomial.coeff_mul]
  -- rw [this]
  -- have : (∑ x ∈ Finset.antidiagonal (mmfx + mmgx), f.coeff x.1 * g.coeff x.2).natDegree =
  --        degreeX f + degreeX g := by
  --   apply natDeg_sum_eq_of_unique (mmfx, mmgx) (by simp) (by grind)
  --   rintro ⟨y₁, y₂⟩ h h'
  --   have : mmfx < y₁ ∨ mmgx < y₂ := by
  --     have h_anti : y₁ + y₂ = mmfx + mmgx := by simpa using h
  --     grind [mul_eq_zero]
  --   grind [mul_eq_zero]
  -- apply sup_eq_of_le_of_reach (mmfx + mmgx) _ this
  -- swap
  -- · rw [Polynomial.mem_support_iff, Polynomial.coeff_mul]
  --   by_contra h
  --   rw [h, natDegree_zero] at this
  --   have : ∑ x ∈ Finset.antidiagonal (mmfx + mmgx), f.coeff x.1 * g.coeff x.2 =
  --          f.coeff mmfx * g.coeff mmgx := by
  --     apply Finset.sum_eq_single
  --             (f := (fun x ↦ f.coeff x.1 * g.coeff x.2)) (mmfx, mmgx) (h₁ := by simp)
  --     rintro ⟨b₁, b₂⟩ h h'
  --     have : mmfx < b₁ ∨ mmgx < b₂ := by
  --       have h_anti : b₁ + b₂ = mmfx + mmgx := by simpa using h
  --       have fdegx_eq_0 : degreeX f = 0 := by grind
  --       have gdegx_eq_0 : degreeX g = 0 := by grind
  --       grind [mul_eq_zero]
  --     grind [mul_eq_zero]
  --   grind [zero_eq_mul]
  -- · intros x h
  --   apply le_trans
  --     (Polynomial.natDegree_sum_le (Finset.antidiagonal x) (fun x ↦ f.coeff x.1 * g.coeff x.2))
  --   rw [Finset.fold_max_le]
  --   grind [degreeX]


/-- The evaluation at a point of a bivariate polynomial in the first variable `X`. -/
def evalX (a : F) (f : F[X][Y]) : Polynomial F :=
  ⟨Finsupp.mapRange (Polynomial.eval a) eval_zero f.toFinsupp⟩

/-- Evaluating a bivariate polynomial in the first variable `X` on a set of points. This results in
a set of univariate polynomials in `Y`. -/
def evalSetX [DecidableEq F] (f : F[X][Y]) (P : Finset F) [Nonempty P] : Finset (Polynomial F) :=
  P.image (fun a => evalX a f)

/-- The evaluation at a point of a bivariate polynomial in the second variable `Y`. -/
def evalY (a : F) (f : F[X][Y]) : Polynomial F := Polynomial.eval (Polynomial.C a) f

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
    simpa [hmul] using (le_rfl : degreeX q + degreeX f ≤ degreeX q + degreeX f)
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
            show _ < (f.coeff mmf).natDegree + (g.coeff mmg).natDegree
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
            show _ < (f.coeff mmf).natDegree + (g.coeff mmg).natDegree
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
  map_smul' r x := by simp only [RingHom.id_apply, ofFinsupp_single]; rw [smul_monomial]

/-- Definition of the bivariate monomial `X^n * Y^m` -/
def monomialXY (n m : ℕ) : F →ₗ[F] F[X][Y] where
  toFun t := ⟨Finsupp.single m ⟨(Finsupp.single n t)⟩⟩
  map_add' x y := by
    simp only [ofFinsupp_single, map_add]
  map_smul' x y := by
    simp only [smul_eq_mul, ofFinsupp_single, RingHom.id_apply]
    rw [smul_monomial, smul_monomial]
    simp

/-- The bivariate monomial is well-defined. -/
@[grind _=_]
theorem monomialXY_def {n m : ℕ} {a : F} : monomialXY n m a = monomial m (monomial n a) := by
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
  simp only [ofFinsupp_single, LinearMap.coe_mk, AddHom.coe_mk, toFinsupp_monomial, mul_zero,
    Finsupp.single_zero, Finsupp.sum_single_index, zero_mul]
  rw [@monomial_mul_monomial]

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
  aesop (add simp [monomialXY, monomial_eq_monomial_iff])

/-- The total degree of the monomial `a * X^n * Y^m` is `n + m`. -/
@[simp, grind =]
lemma totalDegree_monomialXY {n m : ℕ} {a : F} (ha : a ≠ 0) :
  totalDegree (monomialXY n m a) = n + m := by
  classical
  rw [totalDegree, monomialXY_def, Polynomial.support_monomial] <;> simp +arith [*]

/-- The `X`-degree of the monomial `a * X^n * Y^m` is `n`. -/
@[simp]
lemma degreeX_monomialXY {n m : ℕ} {a : F} (ha : a ≠ 0) :
    degreeX (monomialXY n m a) = n := by
  classical
  aesop (add simp [degreeX, monomialXY_def, support_monomial])

/-- The `Y`-degree of the monomial `a * X^n * Y^m` is `m`. -/
@[simp]
lemma degreeY_monomialXY {n m : ℕ} {a : F} (ha : a ≠ 0) :
  natDegreeY (monomialXY n m a) = m := by
  classical
  aesop (add simp [natDegreeY, monomialXY_def])

/-- `(a,b)`-weighted degree of a monomial `X^i * Y^j` -/
def weightedDegreeMonomialXY {n m : ℕ} (a b t : ℕ) : ℕ :=
  a * (degreeX (monomialXY n m t)) + b * natDegreeY (monomialXY n m t)

/-- Shift a bivariate polynomial by (x, y). -/
noncomputable def shift {F : Type} [Field F] (f : F[X][Y]) (x y : F) : F[X][Y] :=
  (f.comp (X + C (C y))).map ((X + C x).compRingHom)

end
end Polynomial.Bivariate

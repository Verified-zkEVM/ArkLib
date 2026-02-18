/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Katerina Hristova, František Silváši, Julian Sutherland, Ilia Vlasov
-/

import Mathlib.Algebra.Polynomial.Bivariate
import Mathlib.Data.Finset.Max
import Mathlib.RingTheory.Polynomial.Resultant.Basic

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

variable {F : Type*} [Semiring F]

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
    fun h ↦ hf (Polynomial.ext (fun n => by rw [←Polynomial.toFinsupp_apply, h]; rfl))

/-- The `X`-degree of a bivariate polynomial. -/
def degreeX (f : F[X][Y]) : ℕ := f.support.sup (fun n => (f.coeff n).natDegree)

/-- The total degree of a bivariate polynomial. -/
def totalDegree (f : F[X][Y]) : ℕ :=
  f.support.sup (fun m => (f.coeff m).natDegree + m)

/-- `(u,v)`-weighted degree of a polynomial.
The maximal `u * i + v * j` such that the polynomial `p`
contains a monomial `x^i * y^j`. -/
def natWeightedDegree.{u} {F : Type u} [Semiring F] (f : F[X][Y]) (u v : ℕ) : ℕ :=
  f.support.sup (fun m => u * (f.coeff m).natDegree + v * m)

def weightedDegree.{u} {F : Type u} [Semiring F] (p : F[X][Y]) (u v : ℕ) : Option ℕ :=
  natWeightedDegree p u v

variable {f : F[X][Y]}

@[grind _=_]
lemma weightedDegree_eq_natWeightedDegree {u v : ℕ} :
  f ≠ 0 → weightedDegree f u v = natWeightedDegree f u v := by
  intro _
  simp [weightedDegree]

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
def rootMultiplicity₀ {F : Type*} [Semiring F] [DecidableEq F] (f : F[X][Y]) : Option ℕ :=
  let deg := Polynomial.Bivariate.totalDegree f
  List.min? <|
    (List.product (List.range deg.succ) (List.range deg.succ)).filterMap fun x =>
      if h : coeff f x.1 x.2 ≠ 0 then some (x.1 + x.2) else none

/-- The multiplicity of a pair `(x,y)` of a bivariate polynomial `f`. -/
def rootMultiplicity.{u} {F : Type u} [CommSemiring F] [DecidableEq F]
  (f : F[X][Y]) (x y : F) : Option ℕ :=
  let X := (Polynomial.X : Polynomial F)
  rootMultiplicity₀ (F := F) ((f.comp (Y + (C (C y)))).map (Polynomial.compRingHom (X + C x)))

/-- If the multiplicity of a pair `(x,y)` is non-negative, then the pair is a root of `f`. -/
lemma rootMultiplicity_some_implies_root {F : Type} [CommSemiring F] [DecidableEq F]
  {x y : F} {f : F[X][Y]} (h : some 0 < (rootMultiplicity (f := f) x y))
  : (f.eval (Polynomial.C y)).eval x = 0 := by
  classical
  -- Unfold the shifted polynomial used by `rootMultiplicity`.
  unfold rootMultiplicity at h
  -- Let `g(X,Y) = f(X + x, Y + y)`.
  set X : Polynomial F := Polynomial.X
  set g : F[X][Y] :=
    ((f.comp (Y + Polynomial.C (Polynomial.C y))).map (Polynomial.compRingHom (X + Polynomial.C x)))
  have hg_def : g =
      ((f.comp (Y + Polynomial.C (Polynomial.C y))).map (Polynomial.compRingHom (X + Polynomial.C x))) := by
    rfl
  -- If the constant coefficient of `g` were nonzero, then `rootMultiplicity₀ g = some 0`,
  -- contradicting `some 0 < rootMultiplicity₀ g`.
  have hcoeff00 : coeff g 0 0 = 0 := by
    by_contra h00
    have h0mem :
        0 ∈
          (List.product (List.range (totalDegree g).succ) (List.range (totalDegree g).succ)).filterMap
              (fun x => if h : coeff g x.1 x.2 ≠ 0 then some (x.1 + x.2) else none) := by
      -- The pair `(0,0)` appears in the product, and its image is `0`.
      simp [h00]
    -- A list containing `0` has `min? = some 0`.
    have hmin : rootMultiplicity₀ g = (some 0 : Option ℕ) := by
      -- Prove `List.min?` is `some 0` by induction on the list.
      -- We reuse a general lemma: if `0 ∈ l` then `l.min? = some 0`.
      have min?_eq_some_zero_of_zero_mem :
          ∀ {l : List ℕ}, 0 ∈ l → l.min? = some 0 := by
        intro l hl
        induction l with
        | nil =>
            cases hl
        | cons a l ih =>
            simp at hl
            rcases hl with rfl | hl
            · -- If the head is `0`, then `min?` is `0` regardless of the tail.
              cases hmin : l.min? <;> simp [List.min?_cons, hmin]
            · have := ih hl
              -- Use the inductive hypothesis and `min  a 0 = 0`.
              simp [List.min?_cons, this, Nat.min_eq_right (Nat.zero_le a)]
      -- Apply the lemma to the concrete list used by `rootMultiplicity₀`.
      have h0mem' :
          0 ∈
            (List.product (List.range (totalDegree g).succ) (List.range (totalDegree g).succ)).filterMap
                (fun x => if h : coeff g x.1 x.2 ≠ 0 then some (x.1 + x.2) else none) := by
        simpa using h0mem
      simpa [rootMultiplicity₀] using (min?_eq_some_zero_of_zero_mem (l := _) h0mem')
    -- Contradiction with `some 0 < rootMultiplicity₀ g`.
    have : ¬ (some 0 : Option ℕ) < rootMultiplicity₀ g := by
      simpa [hmin] using (lt_irrefl (some 0 : Option ℕ))
    exact this (by simpa [g, hg_def] using h)
  -- The constant term of `g` is `g(0,0)`.
  have hg00 : (g.eval 0).eval 0 = 0 := by
    have h_evalY : g.eval 0 = g.coeff 0 := by
      symm
      simpa using (Polynomial.coeff_zero_eq_eval_zero (p := g))
    have h_evalX : (g.eval 0).eval 0 = (g.eval 0).coeff 0 := by
      symm
      simpa using (Polynomial.coeff_zero_eq_eval_zero (p := g.eval 0))
    calc
      (g.eval 0).eval 0 = (g.eval 0).coeff 0 := h_evalX
      _ = (g.coeff 0).coeff 0 := by simpa [h_evalY]
      _ = 0 := by
        simpa [Polynomial.Bivariate.coeff] using hcoeff00
  -- Unshift.
  have hshift : (f.eval (Polynomial.C y)).eval x = (g.eval 0).eval 0 := by
    simp [g, hg_def, X]
  simpa [hshift] using hg00

/-- Discriminant in `Y`, computed as `resultant_Y(f, ∂f/∂Y)`. -/
def discr_y {F : Type} [CommRing F] (f : F[X][Y]) : F[X] :=
  Polynomial.resultant f (Polynomial.derivative f)

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

open Classical in
/-- If a summand in a finite sum has degree `deg`, and the degree of every other summand
is strictly less than `deg`, then the degree of the whole sum is exactly `deg`. -/
lemma natDeg_sum_eq_of_unique {α : Type} {s : Finset α} {f : α → F[X]} {deg : ℕ}
  (mx : α) (h : mx ∈ s) :
    (f mx).natDegree = deg →
    (∀ y ∈ s, y ≠ mx → (f y).natDegree < deg ∨ f y = 0) →
    (∑ x ∈ s, f x).natDegree = deg := by
  intros f_x_deg others_le
  by_cases deg_zero : deg = 0
  · rw [←f_x_deg, Finset.sum_eq_single] <;> grind
  · suffices (∑ x ∈ s with x ≠ mx, f x).degree < (f mx).degree by
      have : ∑ x ∈ s, f x = (∑ x ∈ s.filter (fun x => x ≠ mx), f x) + f mx := by
        rw (occs := .pos [1]) [
          show s = s.filter (fun x => x ≠ mx) ∪ {mx} by grind,
          Finset.sum_union (by simp)
        ]
        grind
      grind
    apply lt_of_le_of_lt (Polynomial.degree_sum_le _ _)
    rw [
      Finset.sup_lt_iff (by rw [Polynomial.degree_eq_natDegree (by aesop)]
                            exact WithBot.bot_lt_coe _)
    ]
    intros b h''
    obtain ⟨h₁, h₂⟩ : b ∈ s ∧ ¬b = mx := by grind
    rcases others_le b h₁ h₂ with h' | h'
    · exact Polynomial.degree_lt_degree (f_x_deg.symm ▸ h')
    · cases cs : (f mx).degree <;> grind    

/-- If some element `x ∈ s` maps to `y` under `f`, and every element of `s` maps to a value
less than or equal to `y`, then the supremum of `f` over `s` is exactly `y`. -/
lemma sup_eq_of_le_of_reach {α β : Type} [SemilatticeSup β] [OrderBot β] {s : Finset α} {f : α → β}
      (x : α) {y : β} (h : x ∈ s) :
    f x = y →
    (∀ x ∈ s, f x ≤ y) →
    s.sup f = y := by
  grind

/-- The `X`-degree of the product of two non-zero bivariate polynomials is
equal to the sum of their degrees. -/
@[simp, grind _=_]
lemma degreeX_mul [IsDomain F] (f g : F[X][Y]) (hf : f ≠ 0) (hg : g ≠ 0) :
  degreeX (f * g) = degreeX f + degreeX g := by
  letI s₁ := {n ∈ f.support | (f.coeff n).natDegree = degreeX f}
  letI s₂ := {n ∈ g.support | (g.coeff n).natDegree = degreeX g}
  have f_mdeg_nonempty : s₁.Nonempty := by
    obtain ⟨mfx, _, _⟩ :=
      Finset.exists_mem_eq_sup _ (show f.support.Nonempty by grind) fun n ↦ (f.coeff n).natDegree
    use mfx
    grind [degreeX]
  have g_mdeg_nonempty : s₂.Nonempty := by
    obtain ⟨mfx, _, _⟩ :=
      Finset.exists_mem_eq_sup _ (show g.support.Nonempty by grind) fun n ↦ (g.coeff n).natDegree
    use mfx
    grind [degreeX]
  set mmfx := s₁.max' f_mdeg_nonempty with hmmfx
  set mmgx := s₂.max' g_mdeg_nonempty with hmmgx
  have mmfx_def : (f.coeff mmfx).natDegree = degreeX f := by
    have h := Finset.max'_mem _ f_mdeg_nonempty
    grind
  have mmgx_def : (g.coeff mmgx).natDegree = degreeX g := by
    have h := Finset.max'_mem _ g_mdeg_nonempty
    grind
  have h₁ : mmfx ∈ s₁ := Finset.max'_mem _ f_mdeg_nonempty
  have h₂ : mmgx ∈ s₂ := Finset.max'_mem _ g_mdeg_nonempty
  have mmfx_neq_0 : f.coeff mmfx ≠ 0 := by grind
  have mmgx_neq_0 : g.coeff mmgx ≠ 0 := by grind
  have h₁ {n} : (f.coeff n).natDegree ≤ degreeX f := by
    have : degreeX f = (f.coeff mmfx).natDegree := by grind
    by_cases h : n ∈ f.toFinsupp.support
    · convert Finset.sup_le_iff.mp (le_of_eq this) n h
    · simp [Polynomial.notMem_support_iff.1 h]
  have h₂ {n} : (g.coeff n).natDegree ≤ (g.coeff mmgx).natDegree := by
    have : degreeX g = (g.coeff mmgx).natDegree := by grind
    by_cases h : n ∈ g.toFinsupp.support
    · convert Finset.sup_le_iff.mp (le_of_eq this) n h
    · simp [Polynomial.notMem_support_iff.1 h]
  have h₁' {n} (h : mmfx < n) :
    (f.coeff n).natDegree < (f.coeff mmfx).natDegree ∨ f.coeff n = 0 := by
    suffices f.coeff n ≠ 0 → (f.coeff mmfx).natDegree ≤ (f.coeff n).natDegree → False by grind
    intros h' contra
    have : (f.coeff mmfx).natDegree = (f.coeff n).natDegree := by grind
    have : n ≤ mmfx := Finset.le_sup'_of_le (hb := show n ∈ s₁ by grind) (h := by simp)
    grind
  have h₂' {n} (h : mmgx < n) :
    (g.coeff n).natDegree < (g.coeff mmgx).natDegree ∨ g.coeff n = 0 := by
    suffices g.coeff n ≠ 0 → (g.coeff mmgx).natDegree ≤ (g.coeff n).natDegree → False by grind
    intros h' contra
    have : (g.coeff mmgx).natDegree = (g.coeff n).natDegree := by grind
    have : n ≤ mmgx := Finset.le_sup'_of_le (hb := show n ∈ s₂ by grind) (h := by simp)
    grind
  unfold degreeX
  have : (fun n ↦ ((f * g).coeff n).natDegree) =
         fun n ↦ (∑ x ∈ Finset.antidiagonal n, f.coeff x.1 * g.coeff x.2).natDegree := by
    funext n; rw [Polynomial.coeff_mul]
  rw [this]
  have : (∑ x ∈ Finset.antidiagonal (mmfx + mmgx), f.coeff x.1 * g.coeff x.2).natDegree =
         degreeX f + degreeX g := by
    apply natDeg_sum_eq_of_unique (mmfx, mmgx) (by simp) (by grind)
    rintro ⟨y₁, y₂⟩ h h'
    have : mmfx < y₁ ∨ mmgx < y₂ := by
      have h_anti : y₁ + y₂ = mmfx + mmgx := by simpa using h
      grind [mul_eq_zero]
    grind [mul_eq_zero]
  apply sup_eq_of_le_of_reach (mmfx + mmgx) _ this
  swap
  · rw [Polynomial.mem_support_iff, Polynomial.coeff_mul]
    by_contra h
    rw [h, natDegree_zero] at this
    have : ∑ x ∈ Finset.antidiagonal (mmfx + mmgx), f.coeff x.1 * g.coeff x.2 =
           f.coeff mmfx * g.coeff mmgx := by
      apply Finset.sum_eq_single
              (f := (fun x ↦ f.coeff x.1 * g.coeff x.2)) (mmfx, mmgx) (h₁ := by simp)
      rintro ⟨b₁, b₂⟩ h h'
      have : mmfx < b₁ ∨ mmgx < b₂ := by
        have h_anti : b₁ + b₂ = mmfx + mmgx := by simpa using h
        have fdegx_eq_0 : degreeX f = 0 := by grind
        have gdegx_eq_0 : degreeX g = 0 := by grind
        grind [mul_eq_zero]
      grind [mul_eq_zero]
    grind [zero_eq_mul]
  · intros x h
    apply le_trans
      (Polynomial.natDegree_sum_le (Finset.antidiagonal x) (fun x ↦ f.coeff x.1 * g.coeff x.2))
    rw [Finset.fold_max_le]
    grind [degreeX]
        

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
@[grind]
lemma quotient_nezero {f q : F[X][Y]} (hg : q * f ≠ 0) : q ≠ 0 := by by_contra h; apply hg; simp [h]

/-- If a non-zero bivariate polynomial `f` divides a non-zero bivariate polynomial `g`, then
all the coefficients of the quoetient are non-zero. -/
@[grind]
lemma coeff_ne_zero {f q : F[X][Y]} (hg : q * f ≠ 0) : q.coeff ≠ 0 :=
  (ne_zero_iff_coeffs_ne_zero q).1 (quotient_nezero hg)

/-
If `q * f ≠ 0`, then the `X`-degree of `q` is bounded above by the difference of the
`X`-degrees: `degreeX q ≤ degreeX (q * f) - degreeX f`.
-/
@[grind]
lemma degreeX_le_degreeX_sub_degreeX [IsDomain F] {f q : F[X][Y]} (hf : f ≠ 0) (hg : q * f ≠ 0) :
  degreeX q ≤ degreeX (q * f) - degreeX f := by grind

/-
If `q * f ≠ 0`, then the `Y`-degree of `q` is bounded above by the difference of the
`Y`-degrees: `natDegreeY q ≤ natDegreeY (q * f) - natDegreeY f`.
-/
@[grind]
lemma degreeY_le_degreeY_sub_degreeY [IsDomain F] {f q : F[X][Y]} (hf : f ≠ 0) (hg : q * f ≠ 0) :
  natDegreeY q ≤ natDegreeY (q * f) - natDegreeY f := by grind

/-- The total degree of the product of two bivariate polynomials is the sum of their total degrees.
-/
@[simp, grind _=_]
theorem totalDegree_mul [IsDomain F] {f g : F[X][Y]} (hf : f ≠ 0) (hg : g ≠ 0) :
    totalDegree (f * g) = totalDegree f + totalDegree g := by
  classical
  let s₁ : Finset ℕ := {n ∈ f.support | (f.coeff n).natDegree + n = totalDegree f}
  let s₂ : Finset ℕ := {n ∈ g.support | (g.coeff n).natDegree + n = totalDegree g}
  have hs₁ : s₁.Nonempty := by
    obtain ⟨m, hm, hm_sup⟩ :=
      Finset.exists_mem_eq_sup f.support
        (by
          simpa [support_eq_support_toFinsupp] using degreesY_nonempty (f := f) hf)
        (fun n ↦ (f.coeff n).natDegree + n)
    refine ⟨m, ?_⟩
    have hm_eq : (f.coeff m).natDegree + m = totalDegree f := by
      simpa [totalDegree] using hm_sup.symm
    simp [s₁, hm, hm_eq]
  have hs₂ : s₂.Nonempty := by
    obtain ⟨m, hm, hm_sup⟩ :=
      Finset.exists_mem_eq_sup g.support
        (by
          simpa [support_eq_support_toFinsupp] using degreesY_nonempty (f := g) hg)
        (fun n ↦ (g.coeff n).natDegree + n)
    refine ⟨m, ?_⟩
    have hm_eq : (g.coeff m).natDegree + m = totalDegree g := by
      simpa [totalDegree] using hm_sup.symm
    simp [s₂, hm, hm_eq]
  set mmf := s₁.max' hs₁ with hmmf
  set mmg := s₂.max' hs₂ with hmmg
  have hmmf_mem : mmf ∈ s₁ := Finset.max'_mem _ hs₁
  have hmmg_mem : mmg ∈ s₂ := Finset.max'_mem _ hs₂
  have hmmf_support : mmf ∈ f.support := by
    have h : mmf ∈ f.support ∧ (f.coeff mmf).natDegree + mmf = totalDegree f := by
      simpa [s₁] using hmmf_mem
    exact h.1
  have hmmg_support : mmg ∈ g.support := by
    have h : mmg ∈ g.support ∧ (g.coeff mmg).natDegree + mmg = totalDegree g := by
      simpa [s₂] using hmmg_mem
    exact h.1
  have hmmf_def : (f.coeff mmf).natDegree + mmf = totalDegree f := by
    have h : mmf ∈ f.support ∧ (f.coeff mmf).natDegree + mmf = totalDegree f := by
      simpa [s₁] using hmmf_mem
    exact h.2
  have hmmg_def : (g.coeff mmg).natDegree + mmg = totalDegree g := by
    have h : mmg ∈ g.support ∧ (g.coeff mmg).natDegree + mmg = totalDegree g := by
      simpa [s₂] using hmmg_mem
    exact h.2
  have hmmf_coeff_ne : f.coeff mmf ≠ 0 := (Polynomial.mem_support_iff.mp hmmf_support)
  have hmmg_coeff_ne : g.coeff mmg ≠ 0 := (Polynomial.mem_support_iff.mp hmmg_support)
  have hlt_f {n : ℕ} (hn : mmf < n) :
      (f.coeff n).natDegree + n < totalDegree f ∨ f.coeff n = 0 := by
    by_cases h0 : f.coeff n = 0
    · exact Or.inr h0
    · left
      have hn_support : n ∈ f.support := (Polynomial.mem_support_iff.mpr h0)
      have hle : (f.coeff n).natDegree + n ≤ totalDegree f := by
        simpa [totalDegree] using
          (Finset.le_sup (s := f.support) (f := fun m ↦ (f.coeff m).natDegree + m) hn_support)
      have hne : (f.coeff n).natDegree + n ≠ totalDegree f := by
        intro hEq
        have hn_s₁ : n ∈ s₁ := by
          simp [s₁, hn_support, hEq]
        have hn_le : n ≤ mmf := by
          have : n ≤ s₁.max' hs₁ := Finset.le_max' s₁ n hn_s₁
          simpa [hmmf] using this
        exact (not_le_of_gt hn) hn_le
      exact lt_of_le_of_ne hle hne
  have hlt_g {n : ℕ} (hn : mmg < n) :
      (g.coeff n).natDegree + n < totalDegree g ∨ g.coeff n = 0 := by
    by_cases h0 : g.coeff n = 0
    · exact Or.inr h0
    · left
      have hn_support : n ∈ g.support := (Polynomial.mem_support_iff.mpr h0)
      have hle : (g.coeff n).natDegree + n ≤ totalDegree g := by
        simpa [totalDegree] using
          (Finset.le_sup (s := g.support) (f := fun m ↦ (g.coeff m).natDegree + m) hn_support)
      have hne : (g.coeff n).natDegree + n ≠ totalDegree g := by
        intro hEq
        have hn_s₂ : n ∈ s₂ := by
          simp [s₂, hn_support, hEq]
        have hn_le : n ≤ mmg := by
          have : n ≤ s₂.max' hs₂ := Finset.le_max' s₂ n hn_s₂
          simpa [hmmg] using this
        exact (not_le_of_gt hn) hn_le
      exact lt_of_le_of_ne hle hne
  let deg : ℕ := (f.coeff mmf).natDegree + (g.coeff mmg).natDegree
  have hdeg_term : (f.coeff mmf * g.coeff mmg).natDegree = deg := by
    simpa [deg] using (natDegree_mul hmmf_coeff_ne hmmg_coeff_ne)
  have hother :
      ∀ y ∈ Finset.antidiagonal (mmf + mmg),
        y ≠ (mmf, mmg) →
          (f.coeff y.1 * g.coeff y.2).natDegree < deg ∨ f.coeff y.1 * g.coeff y.2 = 0 := by
    rintro ⟨y₁, y₂⟩ hy hne
    have hy_sum : y₁ + y₂ = mmf + mmg := by
      simpa [Finset.mem_antidiagonal] using hy
    have hbig : mmf < y₁ ∨ mmg < y₂ := by
      by_cases hy₁ : y₁ = mmf
      · have hy₂ : y₂ = mmg := by
          have : mmf + y₂ = mmf + mmg := by simpa [hy₁] using hy_sum
          exact (Nat.add_left_cancel this)
        exact (hne (by simpa [hy₁, hy₂])).elim
      · rcases lt_or_gt_of_ne hy₁ with hy₁_lt | hy₁_gt
        · right
          have : y₁ + y₂ < mmf + y₂ := Nat.add_lt_add_right hy₁_lt y₂
          have : mmf + mmg < mmf + y₂ := by simpa [hy_sum] using this
          exact (Nat.add_lt_add_iff_left).1 this
        · left
          exact hy₁_gt
    by_cases hterm : f.coeff y₁ * g.coeff y₂ = 0
    · exact Or.inr hterm
    · left
      have hfy₁ : f.coeff y₁ ≠ 0 := by
        intro h0
        exact hterm (by simp [h0])
      have hgy₂ : g.coeff y₂ ≠ 0 := by
        intro h0
        exact hterm (by simp [h0])
      have hy₁_support : y₁ ∈ f.support := (Polynomial.mem_support_iff.mpr hfy₁)
      have hy₂_support : y₂ ∈ g.support := (Polynomial.mem_support_iff.mpr hgy₂)
      have hle₁ : (f.coeff y₁).natDegree + y₁ ≤ totalDegree f := by
        simpa [totalDegree] using
          (Finset.le_sup (s := f.support) (f := fun m ↦ (f.coeff m).natDegree + m) hy₁_support)
      have hle₂ : (g.coeff y₂).natDegree + y₂ ≤ totalDegree g := by
        simpa [totalDegree] using
          (Finset.le_sup (s := g.support) (f := fun m ↦ (g.coeff m).natDegree + m) hy₂_support)
      have hlt_total :
          (f.coeff y₁).natDegree + y₁ + ((g.coeff y₂).natDegree + y₂) <
            totalDegree f + totalDegree g := by
        rcases hbig with hy₁_gt | hy₂_gt
        · have hy₁_lt : (f.coeff y₁).natDegree + y₁ < totalDegree f := by
            rcases hlt_f hy₁_gt with hlt | hz
            · exact hlt
            · exact (hfy₁ hz).elim
          exact Nat.add_lt_add_of_lt_of_le hy₁_lt hle₂
        · have hy₂_lt : (g.coeff y₂).natDegree + y₂ < totalDegree g := by
            rcases hlt_g hy₂_gt with hlt | hz
            · exact hlt
            · exact (hgy₂ hz).elim
          exact Nat.add_lt_add_of_le_of_lt hle₁ hy₂_lt
      have hlt_total' :
          (f.coeff y₁).natDegree + (g.coeff y₂).natDegree + (mmf + mmg) < deg + (mmf + mmg) := by
        -- Rearrange `hlt_total` and rewrite degrees using the chosen maxima.
        have hlt_total'' :
            (f.coeff y₁).natDegree + (g.coeff y₂).natDegree + (y₁ + y₂) <
              (f.coeff mmf).natDegree + (g.coeff mmg).natDegree + (mmf + mmg) := by
          simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm, hmmf_def.symm, hmmg_def.symm] using
            hlt_total
        simpa [hy_sum, deg, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hlt_total''
      have hnatDeg_term :
          (f.coeff y₁ * g.coeff y₂).natDegree =
            (f.coeff y₁).natDegree + (g.coeff y₂).natDegree := by
        simpa using (natDegree_mul hfy₁ hgy₂)
      -- Cancel the common `(mmf + mmg)` on both sides.
      have :
          (f.coeff y₁).natDegree + (g.coeff y₂).natDegree < deg := by
        exact (Nat.add_lt_add_iff_right (k := mmf + mmg)).1 (by
          simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hlt_total')
      simpa [hnatDeg_term] using this
  have hdeg_coeff :
      (∑ x ∈ Finset.antidiagonal (mmf + mmg), f.coeff x.1 * g.coeff x.2).natDegree = deg := by
    apply natDeg_sum_eq_of_unique (mx := (mmf, mmg)) (s := Finset.antidiagonal (mmf + mmg))
      (h := by simp [Finset.mem_antidiagonal])
    · exact hdeg_term
    · exact hother
  have hcoeff_ne :
      ∑ x ∈ Finset.antidiagonal (mmf + mmg), f.coeff x.1 * g.coeff x.2 ≠ 0 := by
    by_cases hdeg0 : deg = 0
    · have hother0 :
          ∀ y ∈ Finset.antidiagonal (mmf + mmg),
            y ≠ (mmf, mmg) → f.coeff y.1 * g.coeff y.2 = 0 := by
        intro y hy hyne
        rcases hother y hy hyne with hlt | hz
        ·
          have : (f.coeff y.1 * g.coeff y.2).natDegree < 0 := by
            simpa [hdeg0] using hlt
          exact (Nat.not_lt_zero ((f.coeff y.1 * g.coeff y.2).natDegree) this).elim
        · exact hz
      have hsum_eq :
          ∑ x ∈ Finset.antidiagonal (mmf + mmg), f.coeff x.1 * g.coeff x.2 =
            f.coeff mmf * g.coeff mmg := by
        apply Finset.sum_eq_single (a := (mmf, mmg))
        · intro b hb hbne
          simpa using hother0 b hb hbne
        · intro hb
          exact (hb (by simp [Finset.mem_antidiagonal])).elim
      have hterm_ne : f.coeff mmf * g.coeff mmg ≠ 0 :=
        _root_.mul_ne_zero hmmf_coeff_ne hmmg_coeff_ne
      simpa [hsum_eq] using hterm_ne
    · intro hsum0
      have : (0 : ℕ) = deg := by
        simpa [hsum0] using hdeg_coeff
      exact hdeg0 this.symm
  -- The total degree is witnessed at the coefficient of `Y^(mmf + mmg)`.
  have hreach :
      (fun n ↦ ((f * g).coeff n).natDegree + n) (mmf + mmg) = totalDegree f + totalDegree g := by
    have hcoeff_sum :
        (f * g).coeff (mmf + mmg) =
          ∑ x ∈ Finset.antidiagonal (mmf + mmg), f.coeff x.1 * g.coeff x.2 := by
      simp [Polynomial.coeff_mul]
    have hcoeff_natDeg : ((f * g).coeff (mmf + mmg)).natDegree = deg := by
      have h := hdeg_coeff
      -- Rewrite the sum as the corresponding coefficient of `f * g`.
      rw [← hcoeff_sum] at h
      exact h
    -- Substitute the computed `X`-degree and unfold `deg`.
    dsimp
    rw [hcoeff_natDeg]
    -- Reduce the arithmetic using the defining equalities for `mmf` and `mmg`.
    dsimp [deg]
    calc
      (f.coeff mmf).natDegree + (g.coeff mmg).natDegree + (mmf + mmg) =
          (f.coeff mmf).natDegree + mmf + ((g.coeff mmg).natDegree + mmg) := by
        simpa using
          (Nat.add_add_add_comm (f.coeff mmf).natDegree (g.coeff mmg).natDegree mmf mmg)
      _ = totalDegree f + totalDegree g := by
        simpa [Nat.add_assoc, hmmf_def, hmmg_def]
  have hm_support : mmf + mmg ∈ (f * g).support := by
    rw [Polynomial.mem_support_iff, Polynomial.coeff_mul]
    exact hcoeff_ne
  -- Upper bound: every coefficient contributes at most `totalDegree f + totalDegree g`.
  have hle_all :
      ∀ n ∈ (f * g).support,
        ((f * g).coeff n).natDegree + n ≤ totalDegree f + totalDegree g := by
    intro n hn
    have hsum_ne : (∑ x ∈ Finset.antidiagonal n, f.coeff x.1 * g.coeff x.2) ≠ 0 := by
      simpa [Polynomial.mem_support_iff, Polynomial.coeff_mul] using hn
    obtain ⟨⟨i, j⟩, hij, hij_ne⟩ :=
      Finset.exists_ne_zero_of_sum_ne_zero hsum_ne
    have hij_sum : i + j = n := by simpa [Finset.mem_antidiagonal] using hij
    have hi_ne : f.coeff i ≠ 0 := by
      intro h0
      exact hij_ne (by simp [h0])
    have hj_ne : g.coeff j ≠ 0 := by
      intro h0
      exact hij_ne (by simp [h0])
    have hi_support : i ∈ f.support := (Polynomial.mem_support_iff.mpr hi_ne)
    have hj_support : j ∈ g.support := (Polynomial.mem_support_iff.mpr hj_ne)
    have hi_le : i ≤ totalDegree f := by
      have hi' : (f.coeff i).natDegree + i ≤ totalDegree f := by
        simpa [totalDegree] using
          (Finset.le_sup (s := f.support) (f := fun m ↦ (f.coeff m).natDegree + m) hi_support)
      exact (Nat.le_add_left _ _).trans hi'
    have hj_le : j ≤ totalDegree g := by
      have hj' : (g.coeff j).natDegree + j ≤ totalDegree g := by
        simpa [totalDegree] using
          (Finset.le_sup (s := g.support) (f := fun m ↦ (g.coeff m).natDegree + m) hj_support)
      exact (Nat.le_add_left _ _).trans hj'
    have hn_le : n ≤ totalDegree f + totalDegree g := by
      simpa [hij_sum, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
        Nat.add_le_add hi_le hj_le
    -- Bound the `X`-degree of the coefficient using `natDegree_sum_le`.
    have hnatDeg_le :
        ((f * g).coeff n).natDegree ≤ totalDegree f + totalDegree g - n := by
      -- Rewrite the coefficient as a sum over the antidiagonal.
      have hcoeff :
          ((f * g).coeff n).natDegree =
            (∑ x ∈ Finset.antidiagonal n, f.coeff x.1 * g.coeff x.2).natDegree := by
        simp [Polynomial.coeff_mul]
      rw [hcoeff]
      apply le_trans (Polynomial.natDegree_sum_le (Finset.antidiagonal n)
        (fun x ↦ f.coeff x.1 * g.coeff x.2))
      -- Bound the maximum degree of the summands.
      have hfold :
          Finset.fold max 0 (natDegree ∘ fun x : ℕ × ℕ ↦ f.coeff x.1 * g.coeff x.2)
              (Finset.antidiagonal n) ≤ totalDegree f + totalDegree g - n := by
        -- Use `fold_max_le`.
        have h0 : (0 : ℕ) ≤ totalDegree f + totalDegree g - n := Nat.zero_le _
        refine (Finset.fold_max_le (s := Finset.antidiagonal n)
          (f := natDegree ∘ fun x : ℕ × ℕ ↦ f.coeff x.1 * g.coeff x.2)
          (b := 0) (c := totalDegree f + totalDegree g - n)).2 ?_
        refine ⟨h0, ?_⟩
        intro x hx
        -- Convert to an additive bound using `Nat.le_sub_iff_add_le`.
        refine (Nat.le_sub_iff_add_le hn_le).2 ?_
        -- Split on whether the summand is zero.
        by_cases hx0 : f.coeff x.1 * g.coeff x.2 = 0
        · simpa [hx0] using hn_le
        · have hx1 : f.coeff x.1 ≠ 0 := by
            intro h0
            exact hx0 (by simp [h0])
          have hx2 : g.coeff x.2 ≠ 0 := by
            intro h0
            exact hx0 (by simp [h0])
          have hx1_support : x.1 ∈ f.support := (Polynomial.mem_support_iff.mpr hx1)
          have hx2_support : x.2 ∈ g.support := (Polynomial.mem_support_iff.mpr hx2)
          have hx1_le : (f.coeff x.1).natDegree + x.1 ≤ totalDegree f := by
            simpa [totalDegree] using
              (Finset.le_sup (s := f.support) (f := fun m ↦ (f.coeff m).natDegree + m) hx1_support)
          have hx2_le : (g.coeff x.2).natDegree + x.2 ≤ totalDegree g := by
            simpa [totalDegree] using
              (Finset.le_sup (s := g.support) (f := fun m ↦ (g.coeff m).natDegree + m) hx2_support)
          have hx_sum : x.1 + x.2 = n := by
            simpa [Finset.mem_antidiagonal] using hx
          have hx_natDeg :
              (f.coeff x.1 * g.coeff x.2).natDegree =
                (f.coeff x.1).natDegree + (g.coeff x.2).natDegree := by
            simpa using (natDegree_mul hx1 hx2)
          -- Put everything together.
          have :
              (f.coeff x.1 * g.coeff x.2).natDegree + n ≤ totalDegree f + totalDegree g := by
            -- Rewrite and apply `add_le_add`.
            rw [hx_natDeg, ← hx_sum]
            have :
                (f.coeff x.1).natDegree + x.1 + ((g.coeff x.2).natDegree + x.2) ≤
                  totalDegree f + totalDegree g := by
              exact Nat.add_le_add hx1_le hx2_le
            simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using this
          simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using this
      exact hfold
  -- Finish the bound.
    have : ((f * g).coeff n).natDegree + n ≤ (totalDegree f + totalDegree g - n) + n :=
      Nat.add_le_add_right hnatDeg_le n
    simpa [Nat.sub_add_cancel hn_le] using this
  -- Conclude by characterising the supremum over the support.
  change
      (f * g).support.sup (fun m ↦ ((f * g).coeff m).natDegree + m) =
        totalDegree f + totalDegree g
  refine
    sup_eq_of_le_of_reach (s := (f * g).support)
      (f := fun m ↦ ((f * g).coeff m).natDegree + m) (x := mmf + mmg) (y := totalDegree f + totalDegree g)
      hm_support hreach ?_
  intro n hn
  exact hle_all n hn

/-- Definition of a monomial when the bivariate polynomial is considered as a univariate
polynomial in `Y`. -/
def monomialY (n : ℕ) : F[X] →ₗ[F[X]] F[X][Y] where
  toFun t := ⟨Finsupp.single n t⟩
  map_add' x y := by rw [Finsupp.single_add]; aesop
  map_smul' r x := by simp; rw[smul_monomial]; aesop

/-- Definition of the bivariate monomial `X^n * Y^m` -/
def monomialXY (n m : ℕ) : F →ₗ[F] F[X][Y] where
  toFun t := ⟨Finsupp.single m ⟨(Finsupp.single n t)⟩⟩
  map_add' x y := by
    simp only [ofFinsupp_single, Polynomial.monomial_add, Polynomial.monomial_add]
  map_smul' x y := by
    simp only [smul_eq_mul, ofFinsupp_single, RingHom.id_apply]
    rw[smul_monomial, smul_monomial]
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

end
end Polynomial.Bivariate

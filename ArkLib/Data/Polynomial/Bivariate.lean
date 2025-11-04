/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Katerina Hristova, František Silváši, Julian Sutherland, Ilia Vlasov
-/

import ArkLib.Data.Polynomial.Prelims

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
    fun h ↦ hf (Polynomial.ext (fun n => by rw [←Polynomial.toFinsupp_apply, h]; rfl))

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

@[grind _=_]
lemma weightedDegree_eq_natWeightedDegree {u v : ℕ} :
  f ≠ 0 → weightedDegree f u v = natWeightedDegree f u v := by
  sorry

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
  | some deg => List.max?
    (List.map
      (fun x => if coeff f x.1 x.2 ≠ 0 then x.1 + x.2 else 0)
      (List.product (List.range deg.succ) (List.range deg.succ)))

/-- The multiplicity of a pair `(x,y)` of a bivariate polynomial `f`. -/
def rootMultiplicity.{u} {F : Type u} [CommSemiring F] [DecidableEq F]
  (f : F[X][Y]) (x y : F) : Option ℕ :=
  let X := (Polynomial.X : Polynomial F)
  rootMultiplicity₀ (F := F) ((f.comp (Y + (C (C y)))).map (Polynomial.compRingHom (X + C x)))

/-- If the multiplicity of a pair `(x,y)` is non-negative, then the pair is a root of `f`. -/
lemma rootMultiplicity_some_implies_root {F : Type} [CommSemiring F] [DecidableEq F]
  {x y : F} {f : F[X][Y]} (h : some 0 < (rootMultiplicity (f := f) x y))
  : (f.eval 0).eval 0 = 0 := by
  sorry

open Univariate in
/-- In the case of a bivariate polynomial we cannot easily use `discriminant`.
   We are using the fact that the resultant in question is always
   divisible by the leading coefficient of the polynomial.
-/
def discr_y {F : Type} [CommRing F] (f : F[X][Y]) : F[X] :=
  /- TODO: use `Polynomial.discr` once Mathlib is bumped. -/
  Classical.choose (resultant_is_divisible_by_leadingCoeff f)

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
theorem totalDegree_mul {f g : F[X][Y]} (hf : f ≠ 0) (hg : g ≠ 0) :
    totalDegree (f * g) = totalDegree f + totalDegree g := by
    sorry

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

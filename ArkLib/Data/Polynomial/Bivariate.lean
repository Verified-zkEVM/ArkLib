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
  unfold weightedDegree;
  rw [ List.max?_eq_some_iff ];
  -- If the polynomial is non-zero, then the weighted degree is equal to the maximum value of the weighted degrees of its coefficients.
  intro hf_nonzero
  simp [natWeightedDegree];
  refine' ⟨ _, fun a ha => _ ⟩;
  · -- Since the support of $f$ is finite, there exists some $a$ in the support such that $u * (f.coeff a).natDegree + v * a$ is the maximum.
    obtain ⟨a, ha⟩ : ∃ a ∈ f.support, ∀ b ∈ f.support, u * (f.coeff a).natDegree + v * a ≥ u * (f.coeff b).natDegree + v * b := by
      exact Finset.exists_max_image _ _ ⟨ _, Finset.mem_coe.mpr ( Classical.choose_spec <| Finset.nonempty_of_ne_empty <| by aesop ) ⟩;
    refine' ⟨ a, _, _ ⟩;
    · exact Nat.lt_succ_of_le ( Polynomial.le_natDegree_of_mem_supp _ ha.1 );
    · exact le_antisymm ( Finset.le_sup ( f := fun n => u * ( f.coeff n |> Polynomial.natDegree ) + v * n ) ha.1 ) ( Finset.sup_le fun n hn => ha.2 n hn );
  · by_cases ha' : f.coeff a = 0;
    · simp +decide [ ha' ];
      refine' le_trans _ ( Finset.le_sup <| Finsupp.mem_support_iff.mpr <| show f.coeff ( f.natDegree ) ≠ 0 from _ );
      · exact le_add_of_nonneg_of_le ( Nat.zero_le _ ) ( Nat.mul_le_mul_left _ ( Nat.le_of_lt_succ ha ) );
      · aesop;
    · exact Finset.le_sup ( f := fun n => u * ( f.coeff n |> Polynomial.natDegree ) + v * n ) ( by aesop )

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
    · rw [h']; exact bot_lt_iff_ne_bot.mpr fun h0 => by
        have : f mx ≠ 0 := fun heq => deg_zero (by rw [← f_x_deg, heq, natDegree_zero])
        exact absurd h0 (ne_of_eq_of_ne (degree_eq_natDegree this) (WithBot.coe_ne_bot))

/-- If some element `x ∈ s` maps to `y` under `f`, and every element of `s` maps to a value
less than or equal to `y`, then the supremum of `f` over `s` is exactly `y`. -/
lemma sup_eq_of_le_of_reach {α β : Type} [SemilatticeSup β] [OrderBot β] {s : Finset α} {f : α → β}
      (x : α) {y : β} (h : x ∈ s) :
    f x = y →
    (∀ x ∈ s, f x ≤ y) →
    s.sup f = y := by
  grind

/-
Upper bound: each Y-coefficient of f*g has X-degree ≤ degreeX f + degreeX g
-/
lemma degreeX_coeff_mul_le [IsDomain F] (f g : F[X][Y]) (n : ℕ) :
    ((f * g).coeff n).natDegree ≤ degreeX f + degreeX g := by
  -- By definition of polynomial multiplication, we can expand the coefficient of $y^n$ in $f * g$.
  have h_coeff_expansion : (f * g).coeff n = Finset.sum (Finset.antidiagonal n) (fun (i, j) => f.coeff i * g.coeff j) := by
    exact?;
  rw [ h_coeff_expansion, Polynomial.natDegree_le_iff_coeff_eq_zero ];
  intro N hN
  simp [Finset.sum_apply', Polynomial.coeff_mul];
  refine Finset.sum_eq_zero fun x hx => Finset.sum_eq_zero fun y hy => ?_;
  by_cases hfx : (f.coeff x.1).natDegree < y.1;
  · rw [ Polynomial.coeff_eq_zero_of_natDegree_lt hfx, MulZeroClass.zero_mul ];
  · by_cases hgx : (g.coeff x.2).natDegree < y.2;
    · rw [ Polynomial.coeff_eq_zero_of_natDegree_lt hgx, MulZeroClass.mul_zero ];
    · contrapose! hN;
      refine' le_trans _ ( add_le_add ( Finset.le_sup ( f := fun m => ( f.coeff m |> Polynomial.natDegree ) ) ( show x.1 ∈ f.support from _ ) ) ( Finset.le_sup ( f := fun m => ( g.coeff m |> Polynomial.natDegree ) ) ( show x.2 ∈ g.support from _ ) ) );
      · linarith [ Finset.mem_antidiagonal.mp hx, Finset.mem_antidiagonal.mp hy ];
      · aesop;
      · aesop

/-
The set of Y-indices achieving degreeX is nonempty for a nonzero polynomial
-/
lemma degreeX_achievers_nonempty [IsDomain F] (f : F[X][Y]) (hf : f ≠ 0) :
    ({n ∈ f.support | (f.coeff n).natDegree = degreeX f}).Nonempty := by
  -- By definition of supremum, there exists some $n$ in the support of $f$ such that the degree of $f.coeff n$ is equal to the supremum.
  obtain ⟨n, hn⟩ : ∃ n ∈ f.support, (f.coeff n).natDegree = f.support.sup (fun n => (f.coeff n).natDegree) := by
    obtain ⟨n, hn⟩ : ∃ n ∈ f.support, ∀ m ∈ f.support, (f.coeff m).natDegree ≤ (f.coeff n).natDegree := by
      apply_rules [ Finset.exists_max_image ];
      exact?;
    exact ⟨ n, hn.1, le_antisymm ( Finset.le_sup ( f := fun n => ( f.coeff n |> Polynomial.natDegree ) ) hn.1 ) ( Finset.sup_le fun m hm => hn.2 m hm ) ⟩;
  exact ⟨ n, by aesop ⟩

/-
For the max Y-index achieving degreeX, any larger Y-index has strictly less X-degree or
    zero coefficient
-/
lemma degreeX_strict_above_max [IsDomain F] (f : F[X][Y]) (hf : f ≠ 0) :
    let s := {n ∈ f.support | (f.coeff n).natDegree = degreeX f}
    ∀ k, s.max' (degreeX_achievers_nonempty f hf) < k →
      (f.coeff k).natDegree < degreeX f ∨ f.coeff k = 0 := by
  field_simp;
  intro k hk;
  by_cases h : Polynomial.coeff f k = 0;
  · exact Or.inr h;
  · refine' Or.inl ( lt_of_le_of_ne _ _ );
    · exact Finset.le_sup ( f := fun n => ( f.coeff n |> Polynomial.natDegree ) ) ( by aesop );
    · intro H;
      exact hk.not_le ( Finset.le_max' _ _ <| by aesop )

/-
PROBLEM
Show that there exists a Y-index n in the support of f*g such that
((f*g).coeff n).natDegree = degreeX f + degreeX g.

There exists a Y-index where f*g achieves X-degree = degreeX f + degreeX g

PROVIDED SOLUTION
Let i₁ = max of {n ∈ f.support | (f.coeff n).natDegree = degreeX f} (the largest Y-index
achieving the X-degree of f), and similarly i₂ for g. Use `degreeX_achievers_nonempty`.

Consider n = i₁ + i₂. By `Polynomial.coeff_mul`, (f*g).coeff n = ∑_{(a,b) ∈ antidiagonal n}
f.coeff a * g.coeff b.

Apply `natDeg_sum_eq_of_unique` with mx = (i₁, i₂):
- The term f.coeff i₁ * g.coeff i₂ has natDegree = degreeX f + degreeX g
  (by `Polynomial.natDegree_mul` since both are nonzero, as they are in support).
- For any other (a, b) with a + b = i₁ + i₂ and (a,b) ≠ (i₁,i₂): either a > i₁ (so b < i₂)
  or a < i₁ (so b > i₂). In the first case, use `degreeX_strict_above_max` for f to get
  natDegree(f.coeff a) < degreeX f or f.coeff a = 0. Similarly for the other case with g.
  Either way, the product has natDegree < degreeX f + degreeX g, or is zero.

This gives ((f*g).coeff n).natDegree = degreeX f + degreeX g. Then show n ∈ (f*g).support
because the natDegree is degreeX f + degreeX g which is nonzero (since f,g are nonzero
and have support, so degreeX f and degreeX g could be 0 — but even if the natDegree is 0,
the coeff is nonzero since its natDegree is well-defined at 0 meaning it's a nonzero constant).
Actually, just show (f*g).coeff n ≠ 0 by using that its natDegree = degreeX f + degreeX g ≥ 0
which doesn't immediately help. Instead, note that a polynomial with natDegree d has nonzero
coeff at d, so (f*g).coeff n ≠ 0 follows from having a nonzero leading coefficient.
Or more directly: if (f*g).coeff n = 0, then natDegree would be 0, contradicting the equation
unless degreeX f = degreeX g = 0. In that case, still (f*g).coeff n = ∑... and the dominant
term is f.coeff i₁ * g.coeff i₂ which is nonzero (product of nonzero elements in domain), contradiction.
-/
lemma degreeX_mul_achieved [IsDomain F] (f g : F[X][Y]) (hf : f ≠ 0) (hg : g ≠ 0) :
    ∃ n ∈ (f * g).support, ((f * g).coeff n).natDegree = degreeX f + degreeX g := by
  by_contra h_contra;
  obtain ⟨i₁, hi₁⟩ : ∃ i₁, i₁ ∈ f.support ∧ (f.coeff i₁).natDegree = degreeX f ∧ ∀ j ∈ f.support, j > i₁ → (f.coeff j).natDegree < degreeX f ∨ f.coeff j = 0 := by
    have := degreeX_achievers_nonempty f hf;
    obtain ⟨i₁, hi₁⟩ : ∃ i₁, i₁ ∈ {n ∈ f.support | (f.coeff n).natDegree = degreeX f} ∧ ∀ j ∈ {n ∈ f.support | (f.coeff n).natDegree = degreeX f}, j ≤ i₁ := by
      exact ⟨ Finset.max' ( f.support.filter fun n => ( f.coeff n |> Polynomial.natDegree ) = degreeX f ) this, Finset.max'_mem _ _, fun j hj => Finset.le_max' _ _ hj ⟩;
    exact ⟨ i₁, Finset.filter_subset _ _ hi₁.1, Finset.mem_filter.mp hi₁.1 |>.2, fun j hj hj' => Classical.or_iff_not_imp_right.2 fun hj'' => lt_of_le_of_ne ( show ( f.coeff j |> Polynomial.natDegree ) ≤ degreeX f from Finset.le_sup ( f := fun m => ( f.coeff m |> Polynomial.natDegree ) ) hj |> le_trans <| by simp +decide [ degreeX ] ) fun hj''' => hj'.not_le <| hi₁.2 j <| Finset.mem_filter.mpr ⟨ hj, hj''' ⟩ ⟩;
  obtain ⟨i₂, hi₂⟩ : ∃ i₂, i₂ ∈ g.support ∧ (g.coeff i₂).natDegree = degreeX g ∧ ∀ j ∈ g.support, j > i₂ → (g.coeff j).natDegree < degreeX g ∨ g.coeff j = 0 := by
    have := degreeX_achievers_nonempty g hg;
    obtain ⟨ i₂, hi₂ ⟩ := Finset.exists_max_image _ ( fun x => x ) this;
    exact ⟨ i₂, by aesop, by aesop, fun j hj₁ hj₂ => Classical.or_iff_not_imp_right.2 fun hj₃ => lt_of_le_of_ne ( Finset.le_sup ( f := fun x => Polynomial.natDegree ( g.coeff x ) ) hj₁ ) fun h => hj₂.not_le <| hi₂.2 j <| by aesop ⟩;
  -- Consider the coefficient of $Y^{i₁ + i₂}$ in the product $f * g$.
  have h_coeff : ((f * g).coeff (i₁ + i₂)).natDegree = degreeX f + degreeX g := by
    rw [ Polynomial.coeff_mul ];
    apply natDeg_sum_eq_of_unique ( i₁, i₂ ) ( Finset.mem_antidiagonal.mpr rfl ) _ _;
    · rw [ Polynomial.natDegree_mul' ] <;> aesop;
    · intro y hy hy_ne
      by_cases hy₁ : y.1 > i₁;
      · by_cases hy₃ : f.coeff y.1 = 0 <;> by_cases hy₄ : g.coeff y.2 = 0 <;> simp_all +decide [ Polynomial.natDegree_mul' ];
        linarith [ hi₁.2.2 _ hy₃ hy₁, Polynomial.natDegree_le_of_degree_le ( Polynomial.degree_le_of_natDegree_le ( show Polynomial.natDegree ( g.coeff y.2 ) ≤ degreeX g from by linarith [ show Polynomial.natDegree ( g.coeff y.2 ) ≤ degreeX g from by exact Finset.le_sup ( f := fun m => Polynomial.natDegree ( g.coeff m ) ) ( by aesop ) ] ) ) ];
      · by_cases hy₂ : y.2 > i₂ <;> simp_all +decide [ Finset.mem_antidiagonal ];
        · by_cases hy₃ : f.coeff y.1 = 0 <;> by_cases hy₄ : g.coeff y.2 = 0 <;> simp_all +decide [ Polynomial.natDegree_mul' ];
          linarith [ hi₂.2.2 _ hy₄ hy₂, Polynomial.natDegree_le_of_degree_le ( Polynomial.degree_le_of_natDegree_le ( show Polynomial.natDegree ( f.coeff y.1 ) ≤ degreeX f from by exact Finset.le_sup ( f := fun m => Polynomial.natDegree ( f.coeff m ) ) ( by aesop ) ) ) ];
        · exact False.elim <| hy_ne <| Prod.ext ( by linarith ) ( by linarith );
  refine h_contra ⟨ i₁ + i₂, ?_, h_coeff ⟩ ; simp_all +decide [ Polynomial.coeff_mul ] ;
  intro H; simp_all +decide [ Polynomial.natDegree_mul' ] ;
  rw [ Finset.sum_eq_single ( i₁, i₂ ) ] at H <;> simp_all +decide [ Finset.mem_antidiagonal ];
  grind +ring

/-
PROBLEM
Show that degreeX (f * g) = degreeX f + degreeX g, where degreeX is f.support.sup (fun n => (f.coeff n).natDegree).

The `X`-degree of the product of two non-zero bivariate polynomials is
equal to the sum of their degrees.

PROVIDED SOLUTION
Use `le_antisymm`. For ≤, use `Finset.sup_le` with `degreeX_coeff_mul_le`.
For ≥, use `degreeX_mul_achieved` to get an index achieving the sum, then `Finset.le_sup`.
-/
@[simp, grind _=_]
lemma degreeX_mul [IsDomain F] (f g : F[X][Y]) (hf : f ≠ 0) (hg : g ≠ 0) :
  degreeX (f * g) = degreeX f + degreeX g := by
  refine' le_antisymm ( Finset.sup_le _ ) ( _ );
  · intro n hn;
    convert degreeX_coeff_mul_le f g n using 1;
  · obtain ⟨ n, hn₁, hn₂ ⟩ := degreeX_mul_achieved f g hf hg;
    exact hn₂ ▸ Finset.le_sup ( f := fun n => Polynomial.natDegree ( Polynomial.coeff ( f * g ) n ) ) hn₁



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
  degreeX q ≤ degreeX (q * f) - degreeX f := by grind

/-
If `q * f ≠ 0`, then the `Y`-degree of `q` is bounded above by the difference of the
`Y`-degrees: `natDegreeY q ≤ natDegreeY (q * f) - natDegreeY f`.
-/
@[grind .]
lemma degreeY_le_degreeY_sub_degreeY [IsDomain F] {f q : F[X][Y]} (hf : f ≠ 0) (hg : q * f ≠ 0) :
  natDegreeY q ≤ natDegreeY (q * f) - natDegreeY f := by grind

/- The original statement is false for general semirings (counterexample: ZMod 4 with
   f = g = monomial 0 (monomial 1 2), where f * g = 0 but totalDegree f + totalDegree g = 2).
   An IsDomain hypothesis is required, analogous to degreeX_mul and degreeY_mul. -/
-- @[simp, grind _=_]
-- theorem totalDegree_mul {f g : F[X][Y]} (hf : f ≠ 0) (hg : g ≠ 0) :
--     totalDegree (f * g) = totalDegree f + totalDegree g := by
--     sorry

private lemma totalDegree_mul_le [IsDomain F] (f g : F[X][Y]) :
    totalDegree (f * g) ≤ totalDegree f + totalDegree g := by
  unfold totalDegree
  set tf := f.support.sup (fun m => (f.coeff m).natDegree + m)
  set tg := g.support.sup (fun m => (g.coeff m).natDegree + m)
  apply Finset.sup_le; intro n hn
  have hn' : (f * g).coeff n ≠ 0 := Polynomial.mem_support_iff.mp hn
  rw [Polynomial.coeff_mul] at hn' ⊢
  obtain ⟨⟨a, b⟩, hab_mem, hab_ne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hn'
  have hab : a + b = n := Finset.mem_antidiagonal.mp hab_mem
  have ha : f.coeff a ≠ 0 := left_ne_zero_of_mul hab_ne
  have hb : g.coeff b ≠ 0 := right_ne_zero_of_mul hab_ne
  have h1 : (f.coeff a).natDegree + a ≤ tf :=
    Finset.le_sup (f := fun m => (f.coeff m).natDegree + m) (Polynomial.mem_support_iff.mpr ha)
  have h2 : (g.coeff b).natDegree + b ≤ tg :=
    Finset.le_sup (f := fun m => (g.coeff m).natDegree + m) (Polynomial.mem_support_iff.mpr hb)
  have n_le : n ≤ tf + tg := by omega
  have h_bound : ∀ x ∈ Finset.antidiagonal n,
      (f.coeff x.1 * g.coeff x.2).natDegree ≤ tf + tg - n := by
    intro ⟨i, j⟩ hij
    have hij' : i + j = n := Finset.mem_antidiagonal.mp hij
    by_cases hfi : f.coeff i = 0
    · simp [hfi]
    · by_cases hgj : g.coeff j = 0
      · simp [hgj]
      · rw [Polynomial.natDegree_mul hfi hgj]
        have h3 : (f.coeff i).natDegree + i ≤ tf :=
          Finset.le_sup (f := fun m => (f.coeff m).natDegree + m)
            (Polynomial.mem_support_iff.mpr hfi)
        have h4 : (g.coeff j).natDegree + j ≤ tg :=
          Finset.le_sup (f := fun m => (g.coeff m).natDegree + m)
            (Polynomial.mem_support_iff.mpr hgj)
        omega
  calc (∑ x ∈ Finset.antidiagonal n, f.coeff x.1 * g.coeff x.2).natDegree + n
      ≤ (Finset.fold max 0 (Polynomial.natDegree ∘ fun x => f.coeff x.1 * g.coeff x.2)
          (Finset.antidiagonal n)) + n :=
        Nat.add_le_add_right (Polynomial.natDegree_sum_le _ _) n
    _ ≤ (tf + tg - n) + n := by
        apply Nat.add_le_add_right
        rw [Finset.fold_max_le]
        exact ⟨by omega, fun x hx => h_bound x hx⟩
    _ = tf + tg := by omega

private lemma totalDegree_achievers_nonempty' [IsDomain F] (f : F[X][Y]) (hf : f ≠ 0) :
    ({n ∈ f.support | (f.coeff n).natDegree + n = totalDegree f}).Nonempty := by
  obtain ⟨n, hn⟩ : ∃ n ∈ f.support, ∀ m ∈ f.support,
      (f.coeff m).natDegree + m ≤ (f.coeff n).natDegree + n :=
    Finset.exists_max_image _ _ (Finsupp.support_nonempty_iff.mpr
      (fun h ↦ hf (Polynomial.ext (fun n => by rw [←Polynomial.toFinsupp_apply, h]; rfl))))
  refine ⟨n, Finset.mem_filter.mpr ⟨hn.1, ?_⟩⟩
  exact le_antisymm
    (Finset.le_sup (f := fun m => (f.coeff m).natDegree + m) hn.1)
    (Finset.sup_le fun m hm => hn.2 m hm)

private lemma totalDegree_mul_ge [IsDomain F] (f g : F[X][Y]) (hf : f ≠ 0) (hg : g ≠ 0) :
    totalDegree f + totalDegree g ≤ totalDegree (f * g) := by
  have hf_ne := totalDegree_achievers_nonempty' f hf
  have hg_ne := totalDegree_achievers_nonempty' g hg
  set i₁ := ({n ∈ f.support | (f.coeff n).natDegree + n = totalDegree f}).max' hf_ne
  set i₂ := ({n ∈ g.support | (g.coeff n).natDegree + n = totalDegree g}).max' hg_ne
  have hi₁_deg : (f.coeff i₁).natDegree + i₁ = totalDegree f :=
    (Finset.mem_filter.mp (Finset.max'_mem _ hf_ne)).2
  have hi₂_deg : (g.coeff i₂).natDegree + i₂ = totalDegree g :=
    (Finset.mem_filter.mp (Finset.max'_mem _ hg_ne)).2
  have hi₁_ne : f.coeff i₁ ≠ 0 :=
    Polynomial.mem_support_iff.mp (Finset.mem_filter.mp (Finset.max'_mem _ hf_ne)).1
  have hi₂_ne : g.coeff i₂ ≠ 0 :=
    Polynomial.mem_support_iff.mp (Finset.mem_filter.mp (Finset.max'_mem _ hg_ne)).1
  -- Helper for other antidiagonal terms
  have h_other : ∀ y ∈ Finset.antidiagonal (i₁ + i₂), y ≠ (i₁, i₂) →
      (f.coeff y.1 * g.coeff y.2).natDegree <
        (f.coeff i₁).natDegree + (g.coeff i₂).natDegree ∨
      f.coeff y.1 * g.coeff y.2 = 0 := by
    intro ⟨y₁, y₂⟩ hy hy_ne
    have hy' : y₁ + y₂ = i₁ + i₂ := Finset.mem_antidiagonal.mp hy
    have hd : y₁ > i₁ ∨ y₂ > i₂ := by
      by_contra hc; push_neg at hc; exact hy_ne (Prod.ext (by omega) (by omega))
    rcases hd with h | h
    · by_cases hfy : f.coeff y₁ = 0
      · exact Or.inr (by simp [hfy])
      · by_cases hgy : g.coeff y₂ = 0
        · exact Or.inr (by simp [hgy])
        · left; rw [Polynomial.natDegree_mul hfy hgy]
          have h1 : (f.coeff y₁).natDegree + y₁ < totalDegree f := by
            have hle := Finset.le_sup (f := fun m => (f.coeff m).natDegree + m)
              (Polynomial.mem_support_iff.mpr hfy)
            exact lt_of_le_of_ne hle fun heq =>
              Nat.lt_irrefl _ (lt_of_lt_of_le h (Finset.le_max' _ _
                (Finset.mem_filter.mpr ⟨Polynomial.mem_support_iff.mpr hfy, heq⟩)))
          have h2 : (g.coeff y₂).natDegree + y₂ ≤ totalDegree g :=
            Finset.le_sup (f := fun m => (g.coeff m).natDegree + m)
              (Polynomial.mem_support_iff.mpr hgy)
          linarith
    · by_cases hfy : f.coeff y₁ = 0
      · exact Or.inr (by simp [hfy])
      · by_cases hgy : g.coeff y₂ = 0
        · exact Or.inr (by simp [hgy])
        · left; rw [Polynomial.natDegree_mul hfy hgy]
          have h1 : (g.coeff y₂).natDegree + y₂ < totalDegree g := by
            have hle := Finset.le_sup (f := fun m => (g.coeff m).natDegree + m)
              (Polynomial.mem_support_iff.mpr hgy)
            exact lt_of_le_of_ne hle fun heq =>
              Nat.lt_irrefl _ (lt_of_lt_of_le h (Finset.le_max' _ _
                (Finset.mem_filter.mpr ⟨Polynomial.mem_support_iff.mpr hgy, heq⟩)))
          have h2 : (f.coeff y₁).natDegree + y₁ ≤ totalDegree f :=
            Finset.le_sup (f := fun m => (f.coeff m).natDegree + m)
              (Polynomial.mem_support_iff.mpr hfy)
          linarith
  -- natDeg of sum = natDeg(f.coeff i₁) + natDeg(g.coeff i₂)
  have h_sum_deg : ((f * g).coeff (i₁ + i₂)).natDegree =
      (f.coeff i₁).natDegree + (g.coeff i₂).natDegree := by
    rw [Polynomial.coeff_mul]
    exact natDeg_sum_eq_of_unique (mx := (i₁, i₂)) (Finset.mem_antidiagonal.mpr rfl)
      (Polynomial.natDegree_mul hi₁_ne hi₂_ne) h_other
  -- (f*g).coeff (i₁+i₂) ≠ 0
  have h_ne : (f * g).coeff (i₁ + i₂) ≠ 0 := by
    intro h
    have hdeg0 : (f.coeff i₁).natDegree + (g.coeff i₂).natDegree = 0 := by
      rw [← h_sum_deg, h, Polynomial.natDegree_zero]
    have h_single : (f * g).coeff (i₁ + i₂) = f.coeff i₁ * g.coeff i₂ := by
      rw [Polynomial.coeff_mul]
      exact Finset.sum_eq_single_of_mem (i₁, i₂) (Finset.mem_antidiagonal.mpr rfl)
        fun b hb hb_ne => by
          rcases h_other b hb hb_ne with h' | h'
          · omega
          · exact h'
    exact _root_.mul_ne_zero hi₁_ne hi₂_ne (h_single ▸ h)
  -- Conclude
  have h_mem : i₁ + i₂ ∈ (f * g).support := Polynomial.mem_support_iff.mpr h_ne
  have h_le : ((f * g).coeff (i₁ + i₂)).natDegree + (i₁ + i₂) ≤ totalDegree (f * g) :=
    Finset.le_sup (f := fun m => ((f * g).coeff m).natDegree + m) h_mem
  linarith

/-- The total degree of the product of two bivariate polynomials over an integral domain
is the sum of their total degrees. Corrected version of `totalDegree_mul` with the
required `IsDomain` hypothesis. -/
@[simp, grind _=_]
theorem totalDegree_mul [IsDomain F] {f g : F[X][Y]} (hf : f ≠ 0) (hg : g ≠ 0) :
    totalDegree (f * g) = totalDegree f + totalDegree g :=
  le_antisymm (totalDegree_mul_le f g) (totalDegree_mul_ge f g hf hg)

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
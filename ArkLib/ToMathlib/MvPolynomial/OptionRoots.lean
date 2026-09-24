/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.Algebra.Polynomial.Roots

/-!
# Roots of a multivariate polynomial in one distinguished variable

Let `R` be a commutative semiring and `g : MvPolynomial (Option σ) R`. Mathlib's
`MvPolynomial.optionEquivLeft` writes `g` as a univariate polynomial in `X none` whose
coefficients are polynomials in the variables `X (some i)`; its natural degree is
`g.degreeOf none`.

Let `A` be a domain that is an `R`-algebra and `φ : σ → A` a family such that `aeval φ` is
injective on `MvPolynomial σ R`. Substituting `y` for `X none` and `φ i` for `X (some i)` evaluates
the image of `optionEquivLeft g` under `aeval φ` at `y`. So a nonzero `g` has at most
`g.degreeOf none` such roots `y ∈ A`.

For `A = R[X]` this counts polynomial graphs on a plane curve: if `g(t, y)` is a nonzero
polynomial in the parameter `t = X none` and the graph coordinate `y = X (some 0)`, then at most
`g.degreeOf (some 0)` distinct polynomials `q` satisfy `g(t, q(t)) = 0`. The bound does not depend
on the degrees of the `q`.

## Main statements

* `MvPolynomial.eval_map_aeval_optionEquivLeft`: evaluating the image of `optionEquivLeft g`
  under `aeval φ` at `y` is `aeval (Option.elim · y φ) g`.
* `MvPolynomial.card_le_degreeOf_none_of_aeval_eq_zero`: the root count in the distinguished
  variable `none`.
* `MvPolynomial.card_le_degreeOf_some_of_aeval_eq_zero`: the count of polynomial graphs on a plane
  curve.
* `MvPolynomial.card_le_degreeOf_some_of_aeval_eq_zero_of_injOn`: the same bound for a finite
  family mapped injectively to polynomial graphs.

## References

* [DKT26]
-/

@[expose] public section

open scoped Finset Polynomial

namespace MvPolynomial

/-- Mapping the coefficients of `optionEquivLeft R σ g` by `aeval φ` and evaluating at `y` is
evaluation of `g` at the point that is `y` on `none` and `φ i` on `some i`. -/
theorem eval_map_aeval_optionEquivLeft {R A σ : Type*} [CommSemiring R] [CommSemiring A]
    [Algebra R A] (φ : σ → A) (y : A) (g : MvPolynomial (Option σ) R) :
    ((optionEquivLeft R σ g).map (aeval (R := R) φ : MvPolynomial σ R →+* A)).eval y =
      aeval (fun o ↦ o.elim y φ) g := by
  induction g using MvPolynomial.induction_on with
  | C r => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p o hp => cases o <;> simp [hp]

/-- Let `A` be a domain and an `R`-algebra, and let `φ : σ → A` be such that `aeval φ` is
injective. A nonzero `g : MvPolynomial (Option σ) R` has at most `g.degreeOf none` roots `y ∈ A`
after substituting `φ i` for `X (some i)`: every finite set `Y` of such `y` has
`#Y ≤ g.degreeOf none`.

The substituted polynomial is the image of `optionEquivLeft R σ g` under `aeval φ`, which is
nonzero by injectivity. Injectivity is needed: for `σ = Unit`, `φ = 0` and `g = X (some ()) * X
none`, every `y` is a root. -/
theorem card_le_degreeOf_none_of_aeval_eq_zero {R A σ : Type*} [CommSemiring R] [CommRing A]
    [IsDomain A] [Algebra R A] {φ : σ → A} (hφ : Function.Injective (aeval (R := R) φ))
    {g : MvPolynomial (Option σ) R} (hg : g ≠ 0) (Y : Finset A)
    (hY : ∀ y ∈ Y, aeval (fun o ↦ o.elim y φ) g = 0) :
    #Y ≤ g.degreeOf none := by
  classical
  set p := (optionEquivLeft R σ g).map (aeval (R := R) φ : MvPolynomial σ R →+* A)
  have hp : p ≠ 0 := fun h ↦ hg <| (optionEquivLeft R σ).injective <| by
    rw [map_zero]
    exact Polynomial.map_injective _ hφ (h.trans (Polynomial.map_zero _).symm)
  have hroots : Y.val ⊆ p.roots := fun y hy ↦ (Polynomial.mem_roots hp).mpr <| by
    rw [Polynomial.IsRoot.def, eval_map_aeval_optionEquivLeft]
    exact hY y hy
  exact (Polynomial.card_le_degree_of_subset_roots hroots).trans
    (Polynomial.natDegree_map_le.trans (natDegree_optionEquivLeft R g).le)

/-- **Polynomial graphs on a plane curve.** Over a domain `R`, let `ι` have one element and let
`g : MvPolynomial (Option ι) R` be nonzero, with parameter `X none` and graph coordinate
`X (some default)`. Every finite set `Q` of polynomials `q : R[X]` with `g(X, q) = 0` has
`#Q ≤ g.degreeOf (some default)`, whatever the degrees of the `q`.

Exchanging the two variables turns this into `card_le_degreeOf_none_of_aeval_eq_zero` with
`A = R[X]` and `φ = fun _ ↦ X`. -/
theorem card_le_degreeOf_some_of_aeval_eq_zero {R ι : Type*} [CommRing R] [IsDomain R] [Unique ι]
    {g : MvPolynomial (Option ι) R} (hg : g ≠ 0) (Q : Finset R[X])
    (hQ : ∀ q ∈ Q, aeval (fun o ↦ o.elim Polynomial.X fun _ ↦ q) g = 0) :
    #Q ≤ g.degreeOf (some default) := by
  set e : Option ι ≃ Option ι := Equiv.swap none (some default)
  have hφ : Function.Injective (aeval (R := R) fun _ : ι ↦ (Polynomial.X : R[X])) := by
    have : (aeval fun _ : ι ↦ (Polynomial.X : R[X])) = (uniqueAlgEquiv R ι).toAlgHom :=
      algHom_ext fun i ↦ by simp
    rw [this]
    exact (uniqueAlgEquiv R ι).injective
  have hdeg : (rename e g).degreeOf none = g.degreeOf (some default) := by
    simpa [e] using degreeOf_rename_of_injective (p := g) e.injective (some default)
  rw [← hdeg]
  refine card_le_degreeOf_none_of_aeval_eq_zero hφ
    (fun h ↦ hg (rename_injective e e.injective (h.trans (map_zero _).symm))) Q fun q hq ↦ ?_
  rw [aeval_rename, ← hQ q hq]
  congr 2
  funext o
  rcases o with _ | i
  · simp [e]
  · rw [Unique.eq_default i]
    simp [e]

/-- A finite family mapped injectively to polynomial graphs on the zero locus of a nonzero
multivariate polynomial has cardinality at most its degree in the graph variable. -/
theorem card_le_degreeOf_some_of_aeval_eq_zero_of_injOn {R ι α : Type*} [CommRing R]
    [IsDomain R] [Unique ι] {g : MvPolynomial (Option ι) R} (hg : g ≠ 0) (T : Finset α)
    (f : α → R[X]) (hinj : Set.InjOn f (T : Set α))
    (hT : ∀ a ∈ T, aeval (fun o ↦ o.elim Polynomial.X fun _ ↦ f a) g = 0) :
    T.card ≤ g.degreeOf (some default) := by
  classical
  have hcount := card_le_degreeOf_some_of_aeval_eq_zero hg (T.image f) (by
    intro q hq
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hq
    exact hT a ha)
  rwa [Finset.card_image_of_injOn hinj] at hcount

end MvPolynomial

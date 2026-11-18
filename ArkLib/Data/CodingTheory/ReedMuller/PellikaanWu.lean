/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Coratger
-/
module

public import ArkLib.Data.CodingTheory.ReedMuller.Grid
public import ArkLib.ToMathlib.FieldTheory.Finite.TracePolynomial
public import Mathlib.Combinatorics.Nullstellensatz
public import Mathlib.RingTheory.Polynomial.Basic

/-!
# The Pellikaan–Wu substitution

Let `L` be an extension of degree `k` of a finite field `K₀` with `q₀` elements, so `n = q₀ᵏ`.
A basis `b` of `L` over `K₀` gives the trace coordinates `ψ(x) = (Tr(b₁ x), …, Tr(bₖ x))`.
They identify `L` with the grid `K₀ᵏ` through a `K₀`-linear bijection.

Let `F'` be a field containing `L`.
Substituting the trace polynomial `T_{bᵢ}` for `Xᵢ` maps `P ∈ F'[X₁, …, Xₖ]` to `P̃ ∈ F'[X]`.
The polynomial `P̃` has degree at most `deg P · q₀ᵏ⁻¹`, where `deg` is the total degree.
Its value at `x ∈ L` is the value of `P` at the grid point `ψ(x)`.
Polynomials of degree below `q₀` in each variable are determined by their substitutions.

This is the reduction to univariate polynomials in Appendix A of [CWYZ26], following [PW04].
The paper takes the trace with respect to an arbitrary basis `γ`; here the basis `b` is that `γ`.
The paper asks for total degree below `q₀` in the injectivity step.
The form here asks only for degree below `q₀` in each variable.

The exponent `k - 1` uses subtraction in `ℕ`.
The substitution is noncomputable, as polynomial arithmetic over a field is.

The [paper page](../../../../docs/kb/papers/CWYZ26.md) records the correspondence.

## Main definitions

* `ReedMuller.traceSubstitution`: the algebra map `P ↦ P̃` substituting trace polynomials.

## Main statements

* `ReedMuller.traceSubstitution_X`: the substitution of `Xᵢ` is the trace polynomial of `bᵢ`.
* `ReedMuller.natDegree_traceSubstitution_le`: `deg P̃ ≤ deg P · q₀ᵏ⁻¹`.
* `ReedMuller.eval_traceSubstitution`: `P̃(x) = P(ψ(x))` for `x ∈ L`.
* `ReedMuller.eq_zero_of_traceSubstitution_eq_zero` and
  `ReedMuller.eq_of_traceSubstitution_eq`: injectivity for degrees below `q₀` in each variable.
* `ReedMuller.eq_of_traceSubstitution_eq_of_totalDegree_lt`: the same for total degree below `q₀`.

## References

* [Chiesa, A., Weissenberg, G., Yogev, E., and Zheng, K. Z.,
    *Affine combiners for Reed–Solomon proximity gaps*][CWYZ26]
* [Pellikaan, R., and Wu, X.-W., *List decoding of q-ary Reed–Muller codes*][PW04]
-/

@[expose] public section

open Polynomial FiniteField

namespace ReedMuller

variable {K₀ L F' : Type*} [Field K₀] [Fintype K₀] [Field L] [Algebra K₀ L] [Field F']
  [Algebra L F'] {k : ℕ}

/-- The substitution of the trace polynomial `T_{bᵢ}` for `Xᵢ`, mapped into `F'[X]`. -/
noncomputable def traceSubstitution (b : Module.Basis (Fin k) K₀ L) :
    MvPolynomial (Fin k) F' →ₐ[F'] F'[X] :=
  MvPolynomial.aeval fun i ↦ (tracePolynomial K₀ (b i)).map (algebraMap L F')

/-- The substitution of `Xᵢ` is the trace polynomial of `bᵢ`. -/
@[simp]
theorem traceSubstitution_X (b : Module.Basis (Fin k) K₀ L) (i : Fin k) :
    traceSubstitution b (MvPolynomial.X i : MvPolynomial (Fin k) F') =
      (tracePolynomial K₀ (b i)).map (algebraMap L F') :=
  MvPolynomial.aeval_X _ _

/-- Let `b` be a basis of `L` over `K₀` with `k` elements, and `q₀ = |K₀|`.
The substitution of `P` has degree at most `deg P · q₀ᵏ⁻¹`, where `deg` is the total degree. -/
theorem natDegree_traceSubstitution_le (b : Module.Basis (Fin k) K₀ L)
    (P : MvPolynomial (Fin k) F') :
    (traceSubstitution b P).natDegree ≤ P.totalDegree * Fintype.card K₀ ^ (k - 1) := by
  refine MvPolynomial.aeval_natDegree_le P le_rfl _ fun i ↦ ?_
  refine natDegree_map_le.trans ((natDegree_tracePolynomial_le _).trans ?_)
  rw [Module.finrank_eq_card_basis b, Fintype.card_fin]

variable [Finite L] [Algebra K₀ F'] [IsScalarTower K₀ L F']

/-- Let `b` be a basis of the finite field `L` over `K₀`, and `ψ(x) = (Tr(bᵢ x))ᵢ`.
At every `x ∈ L`, the substitution of `P` takes the value of `P` at the grid point `ψ(x)`. -/
theorem eval_traceSubstitution (b : Module.Basis (Fin k) K₀ L) (P : MvPolynomial (Fin k) F')
    (x : L) :
    (traceSubstitution b P).eval (algebraMap L F' x) =
      MvPolynomial.eval (gridPoint F' (traceCoordinateEquiv K₀ b x)) P := by
  induction P using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp =>
    simp [hp, eval_map_algebraMap, aeval_algebraMap_apply, eval_tracePolynomial,
      IsScalarTower.algebraMap_apply K₀ L F']

/-- Let `b` be a basis of the finite field `L` over `K₀`, where `q₀ = |K₀|`.
A polynomial over `F'` of degree below `q₀` in each variable whose substitution vanishes is zero.
It vanishes on the whole grid `K₀ᵏ`, since the trace coordinates are onto. -/
theorem eq_zero_of_traceSubstitution_eq_zero (b : Module.Basis (Fin k) K₀ L)
    {P : MvPolynomial (Fin k) F'} (hP : ∀ i, P.degreeOf i < Fintype.card K₀)
    (h : traceSubstitution b P = 0) : P = 0 := by
  classical
  set S : Finset F' := Finset.univ.image (algebraMap K₀ F')
  have hS : S.card = Fintype.card K₀ :=
    Finset.card_image_of_injective _ (algebraMap K₀ F').injective
  refine MvPolynomial.eq_zero_of_eval_zero_at_prod_finset P (fun _ ↦ S) (by simpa [hS]) ?_
  intro y hy
  choose z hz using fun i ↦ Finset.mem_image.mp (hy i)
  obtain ⟨x, hx⟩ := (traceCoordinateEquiv K₀ b).surjective z
  have hy' : y = gridPoint F' (traceCoordinateEquiv K₀ b x) := by
    funext i
    simp [hx, (hz i).2]
  rw [hy', ← eval_traceSubstitution, h, eval_zero]

/-- Let `b` be a basis of the finite field `L` over `K₀`, where `q₀ = |K₀|`.
Let `P₁, P₂` over `F'` have degree below `q₀` in each variable.
If their substitutions are equal, then `P₁ = P₂`. -/
theorem eq_of_traceSubstitution_eq (b : Module.Basis (Fin k) K₀ L)
    {P₁ P₂ : MvPolynomial (Fin k) F'} (h₁ : ∀ i, P₁.degreeOf i < Fintype.card K₀)
    (h₂ : ∀ i, P₂.degreeOf i < Fintype.card K₀)
    (h : traceSubstitution b P₁ = traceSubstitution b P₂) : P₁ = P₂ := by
  refine sub_eq_zero.mp (eq_zero_of_traceSubstitution_eq_zero b (fun i ↦ ?_) ?_)
  · exact (MvPolynomial.degreeOf_sub_le i P₁ P₂).trans_lt (max_lt (h₁ i) (h₂ i))
  · rw [map_sub, h, sub_self]

/-- Let `b` be a basis of the finite field `L` over `K₀`, where `q₀ = |K₀|`.
Two polynomials over `F'` of total degree below `q₀` with equal substitutions are equal. -/
theorem eq_of_traceSubstitution_eq_of_totalDegree_lt (b : Module.Basis (Fin k) K₀ L)
    {P₁ P₂ : MvPolynomial (Fin k) F'} (h₁ : P₁.totalDegree < Fintype.card K₀)
    (h₂ : P₂.totalDegree < Fintype.card K₀)
    (h : traceSubstitution b P₁ = traceSubstitution b P₂) : P₁ = P₂ :=
  eq_of_traceSubstitution_eq b
    (fun i ↦ (MvPolynomial.degreeOf_le_totalDegree P₁ i).trans_lt h₁)
    (fun i ↦ (MvPolynomial.degreeOf_le_totalDegree P₂ i).trans_lt h₂) h

end ReedMuller

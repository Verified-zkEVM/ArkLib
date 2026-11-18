/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Coratger
-/
module

public import ArkLib.Data.CodingTheory.ReedMuller.Grid
public import ArkLib.ToMathlib.FieldTheory.Finite.TracePolynomial
public import Mathlib.RingTheory.MvPolynomial.Basic
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

Polynomials over a field `F` that need not contain `L` are first mapped into `F'`.
Those of total degree below `q₀` are still determined by their substitutions.

This is the reduction to univariate polynomials in Appendix A of [CWYZ26], following [PW04].
The paper takes the trace with respect to an arbitrary basis `γ`; here the basis `b` is that `γ`.
The paper asks for total degree below `q₀` in the injectivity step.
The strongest form here asks only for degree below `q₀` in each variable.

The exponent `k - 1` uses subtraction in `ℕ`.
The substitution is noncomputable, as polynomial arithmetic over a field is.

The [paper page](../../../../docs/kb/papers/CWYZ26.md) records the correspondence.

## Main definitions

* `ReedMuller.traceSubstitution`: the algebra map `P ↦ P̃` substituting trace polynomials.

## Main statements

* `ReedMuller.traceSubstitution_X`: the substitution of `Xᵢ` is the trace polynomial of `bᵢ`.
* `ReedMuller.natDegree_traceSubstitution_le`: `deg P̃ ≤ deg P · q₀ᵏ⁻¹`.
* `ReedMuller.eval_traceSubstitution`: `P̃(x) = P(ψ(x))` for `x ∈ L`.
* `ReedMuller.injOn_traceSubstitution`: injectivity for degrees below `q₀` in each variable.
* `ReedMuller.injOn_traceSubstitution_totalDegree_lt`: injectivity for total degree below `q₀`.
* `ReedMuller.injOn_traceSubstitution_map`: the same for polynomials over a subfield of `F'`.

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

/-- Let `b` be a basis of a field `L` over a finite field `K₀`, and let `F'` be an `L`-algebra.
For `c ∈ L`, let `T_c = ∑_{j < k} c^{q₀ʲ} X^{q₀ʲ}` be its trace polynomial, where `q₀ = |K₀|`.
This is the `F'`-algebra map from `F'[X₁, …, Xₖ]` to `F'[X]` substituting `T_{bᵢ}` for `Xᵢ`. -/
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

variable [Algebra K₀ F'] [IsScalarTower K₀ L F']

/-- Let `b` be a basis of `L` over `K₀`, and `ψ(x) = (Tr(bᵢ x))ᵢ`.
At every `x ∈ L`, the substitution of `P` takes the value of `P` at the grid point `ψ(x)`. -/
theorem eval_traceSubstitution (b : Module.Basis (Fin k) K₀ L) (P : MvPolynomial (Fin k) F')
    (x : L) :
    (traceSubstitution b P).eval (algebraMap L F' x) =
      MvPolynomial.eval (gridPoint F' (traceCoordinateEquiv K₀ b x)) P := by
  have := Module.Finite.of_basis b
  have : Finite L := Module.finite_of_finite K₀
  induction P using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp =>
    simp [hp, eval_map_algebraMap, aeval_algebraMap_apply, eval_tracePolynomial,
      IsScalarTower.algebraMap_apply K₀ L F']

/-- Polynomials of degree below `q₀` in each variable with equal substitutions are equal. -/
private theorem eq_of_traceSubstitution_eq (b : Module.Basis (Fin k) K₀ L)
    {P₁ P₂ : MvPolynomial (Fin k) F'} (h₁ : ∀ i, P₁.degreeOf i < Fintype.card K₀)
    (h₂ : ∀ i, P₂.degreeOf i < Fintype.card K₀)
    (h : traceSubstitution b P₁ = traceSubstitution b P₂) : P₁ = P₂ := by
  refine sub_eq_zero.mp (eq_zero_of_forall_eval_gridPoint_eq_zero
    (fun i ↦ (MvPolynomial.degreeOf_sub_le i P₁ P₂).trans_lt (max_lt (h₁ i) (h₂ i))) fun z ↦ ?_)
  obtain ⟨x, rfl⟩ := (traceCoordinateEquiv K₀ b).surjective z
  rw [← eval_traceSubstitution, map_sub, h, sub_self, eval_zero]

/-- Let `b` be a basis of `L` over `K₀`, where `q₀ = |K₀|`.
The substitution is injective on polynomials over `F'` of degree below `q₀` in each variable. -/
theorem injOn_traceSubstitution (b : Module.Basis (Fin k) K₀ L) :
    Set.InjOn (traceSubstitution (F' := F') b)
      (MvPolynomial.restrictDegree (Fin k) F' (Fintype.card K₀ - 1)) := by
  have hlt (P : MvPolynomial (Fin k) F')
      (hP : P ∈ MvPolynomial.restrictDegree (Fin k) F' (Fintype.card K₀ - 1)) (i : Fin k) :
      P.degreeOf i < Fintype.card K₀ := by
    rw [MvPolynomial.degreeOf_lt_iff Fintype.card_pos]
    intro s hs
    have := (MvPolynomial.mem_restrictDegree _ _ _).mp hP s hs i
    have := Fintype.card_pos (α := K₀)
    omega
  exact fun P₁ h₁ P₂ h₂ h ↦ eq_of_traceSubstitution_eq b (hlt P₁ h₁) (hlt P₂ h₂) h

/-- Let `b` be a basis of `L` over `K₀`, where `q₀ = |K₀|`.
The substitution is injective on polynomials over `F'` of total degree below `q₀`. -/
theorem injOn_traceSubstitution_totalDegree_lt (b : Module.Basis (Fin k) K₀ L) :
    Set.InjOn (traceSubstitution b)
      {P : MvPolynomial (Fin k) F' | P.totalDegree < Fintype.card K₀} :=
  fun P₁ h₁ P₂ h₂ h ↦ eq_of_traceSubstitution_eq b
    (fun i ↦ (MvPolynomial.degreeOf_le_totalDegree P₁ i).trans_lt h₁)
    (fun i ↦ (MvPolynomial.degreeOf_le_totalDegree P₂ i).trans_lt h₂) h

/-- Let `b` be a basis of `L` over `K₀`, where `q₀ = |K₀|`, and let `F` be a field inside `F'`.
Map polynomials over `F` into `F'`, then substitute.
This is injective on polynomials of total degree below `q₀`. -/
theorem injOn_traceSubstitution_map {F : Type*} [Field F] [Algebra F F']
    (b : Module.Basis (Fin k) K₀ L) :
    Set.InjOn (fun P : MvPolynomial (Fin k) F ↦ traceSubstitution b (P.map (algebraMap F F')))
      {P | P.totalDegree < Fintype.card K₀} := by
  have hdeg (P : MvPolynomial (Fin k) F) :
      (P.map (algebraMap F F')).totalDegree ≤ P.totalDegree :=
    Finset.sup_mono (MvPolynomial.support_map_subset (algebraMap F F') P)
  intro P₁ h₁ P₂ h₂ h
  exact MvPolynomial.map_injective _ (algebraMap F F').injective
    (injOn_traceSubstitution_totalDegree_lt b ((hdeg P₁).trans_lt h₁)
      ((hdeg P₂).trans_lt h₂) h)

end ReedMuller

/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Coratger
-/
module

public import ArkLib.Data.CodingTheory.ReedMuller.AffineCombiner.PellikaanWu
public import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.AffineCombiner.ChartIncidence
public import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.AffineCombiner.Interpolation
public import ArkLib.ToMathlib.Polynomial.DegreeLEFunctionals

/-!
# Reed–Muller candidates in the univariate chart count

Let `L` be an extension of degree `k` of a finite field `K₀` with `q₀` elements, so `n = q₀ᵏ`.
A basis `b` of `L` over `K₀` gives trace polynomials `T_{bᵢ}` and coordinates `ψ : L ≃ K₀ᵏ`.
Let `E` be a field containing `L` and the field `F` of the received words, compatibly over `K₀`.
Write `e = q₀ᵏ⁻¹`, with natural-number subtraction.

The trace family `θ` is `(1, T_{b₁}, …, T_{bₖ})` over `E`.
Its multiplier at `φ ∘ α` is the trace substitution `L̃_α` of the affine multiplier `L_α`.
Here `φ` embeds `F` into `E`.
Distinct `α` give distinct multipliers.
A ring endomorphism of `E`, such as an inverse Frobenius power, maps it to the mapped family.

The chart target at `x ∈ L` is `f(ψ x) + (∑ⱼ θⱼ(x) aⱼ ^ s) g(ψ x)`, of total degree at most `s`.
A Reed–Muller candidate `P` gives the univariate candidate `P̃`, its trace substitution.
Agreement counts are preserved.
Take an interpolant on `L` for multipliers of degree `e` and candidates of degree `d e`.
It vanishes along `L̃_α` and `P̃`.

Finitely many linear functionals cut out the image of the polynomials of total degree `≤ d`.
They cut it out among the polynomials of degree at most `d e`.
These are the high cuts of the generic chart count.

This module gives the reduction to univariate polynomials of Appendix A of [CWYZ26].
It also gives the inputs of the nonpersistent count there.
The paper intersects its algebraic sets with the image of `(α, P) ↦ (α, P̃)`.
Here the cuts state that image as linear equations on the reconstructed polynomial.

The trace family, targets and cuts are noncomputable, as polynomial arithmetic over a field is.
The cuts are given by an existence statement through a basis of a quotient space.

The [paper page](../../../../../docs/kb/papers/CWYZ26.md) records the correspondence.

## Main definitions

* `ReedMuller.traceFamily`: the family `(1, T_{b₁}, …, T_{bₖ})` over `E`.
* `ReedMuller.traceChartTarget`: the chart target at a point of `L`.
* `ReedMuller.IsTraceImageCuts`: functionals cutting out the substituted polynomials.

## Main statements

* `ReedMuller.familyMultiplier_traceFamily` and
  `ReedMuller.traceSubstitution_map_affineMultiplier_eq_familyMultiplier`: the multipliers are
  `L̃_α`.
* `ReedMuller.map_familyMultiplier_traceFamily`: compatibility with a ring endomorphism.
* `ReedMuller.familyMultiplier_traceFamily_injective`: distinct `α` give distinct multipliers.
* `ReedMuller.eval_familyMultiplier_traceFamily`: the value at `x` is `L_c(ψ x)`.
* `ReedMuller.totalDegree_traceChartTarget_le` and `ReedMuller.aeval_traceChartTarget`: the
  targets.
* `ReedMuller.ncard_eval_traceSubstitution_eq`: agreement counts are preserved.
* `ReedMuller.multiplierEval_traceSubstitution_eq_zero`: the interpolant vanishes along the
  transported candidate.
* `ReedMuller.exists_isTraceImageCuts`: the cuts exist.

## References

* [Chiesa, A., Weissenberg, G., Yogev, E., and Zheng, K. Z.,
    *Affine combiners for Reed–Solomon proximity gaps*][CWYZ26]
* [Pellikaan, R., and Wu, X.-W., *List decoding of q-ary Reed–Muller codes*][PW04]
-/

@[expose] public section

namespace ReedMuller

open Polynomial FiniteField Finset

variable {K₀ L F : Type*} (E : Type*) [Field K₀] [Fintype K₀] [Field L] [Algebra K₀ L]
  [Field F] [Field E] [Algebra L E] {k : ℕ}

/-- The family `(1, T_{b₁}, …, T_{bₖ})` of trace polynomials over `E`, led by the constant `1`. -/
noncomputable def traceFamily (b : Module.Basis (Fin k) K₀ L) : Fin (k + 1) → E[X] :=
  Fin.cons 1 fun i ↦ (tracePolynomial K₀ (b i)).map (algebraMap L E)

variable {E}

/-- The multiplier of the trace family at `c` substitutes the affine multiplier `L_c`. -/
theorem familyMultiplier_traceFamily (b : Module.Basis (Fin k) K₀ L) (c : Fin (k + 1) → E) :
    ReedSolomon.familyMultiplier (traceFamily E b) c =
      traceSubstitution b (affineMultiplier c) := by
  simp [ReedSolomon.familyMultiplier_apply, traceFamily, affineMultiplier, Fin.sum_univ_succ]

/-- A ring endomorphism `σ` of `E` maps the multiplier of the trace family at `c`.
The image is the multiplier of the mapped family at `σ ∘ c`. -/
theorem map_familyMultiplier_traceFamily (b : Module.Basis (Fin k) K₀ L) (σ : E →+* E)
    (c : Fin (k + 1) → E) :
    (ReedSolomon.familyMultiplier (traceFamily E b) c).map σ =
      ReedSolomon.familyMultiplier (fun j ↦ (traceFamily E b j).map σ) (σ ∘ c) := by
  simp [ReedSolomon.familyMultiplier_apply, Polynomial.map_sum]

section Multiplier

variable [Algebra F E]

/-- Mapping `L_α` from `F` to `E` and substituting gives the trace family at the image of `α`. -/
theorem traceSubstitution_map_affineMultiplier_eq_familyMultiplier
    (b : Module.Basis (Fin k) K₀ L) (α : Fin (k + 1) → F) :
    traceSubstitution b ((affineMultiplier α).map (algebraMap F E)) =
      ReedSolomon.familyMultiplier (traceFamily E b) (algebraMap F E ∘ α) := by
  rw [familyMultiplier_traceFamily, map_affineMultiplier]

variable [Algebra K₀ E] [IsScalarTower K₀ L E]

/-- Distinct `α` over `F` give distinct multipliers of the trace family at their images. -/
theorem familyMultiplier_traceFamily_injective (b : Module.Basis (Fin k) K₀ L) :
    Function.Injective fun α : Fin (k + 1) → F ↦
      ReedSolomon.familyMultiplier (traceFamily E b) (algebraMap F E ∘ α) := by
  simpa only [← traceSubstitution_map_affineMultiplier_eq_familyMultiplier] using
    traceSubstitution_map_affineMultiplier_injective (F' := E) b

/-- At `x ∈ L`, the multiplier of the trace family at `c` is `L_c` at the grid point `ψ(x)`.
Here `ψ(x) = (Tr(bᵢ x))ᵢ`. -/
theorem eval_familyMultiplier_traceFamily (b : Module.Basis (Fin k) K₀ L) (c : Fin (k + 1) → E)
    (x : L) :
    (ReedSolomon.familyMultiplier (traceFamily E b) c).eval (algebraMap L E x) =
      MvPolynomial.eval (gridPoint E (traceCoordinateEquiv K₀ b x)) (affineMultiplier c) := by
  rw [familyMultiplier_traceFamily, eval_traceSubstitution]

end Multiplier

section Target

variable [Algebra F E]

variable (E) in
/-- The chart target at `x ∈ L`, a polynomial in coefficient variables `aⱼ`.
It is `f(ψ x) + (∑ⱼ θⱼ(x) aⱼ ^ s) g(ψ x)`, with `θ` the trace family and `ψ(x) = (Tr(bᵢ x))ᵢ`.
The received values are mapped from `F` to `E`. -/
noncomputable def traceChartTarget (b : Module.Basis (Fin k) K₀ L) (f g : (Fin k → K₀) → F)
    (s : ℕ) (x : L) : MvPolynomial (Fin (k + 1)) E :=
  MvPolynomial.C (algebraMap F E (f (traceCoordinateEquiv K₀ b x))) +
    (∑ j, MvPolynomial.C ((traceFamily E b j).eval (algebraMap L E x)) *
      MvPolynomial.X j ^ s) * MvPolynomial.C (algebraMap F E (g (traceCoordinateEquiv K₀ b x)))

/-- The chart target has total degree at most `s`. -/
theorem totalDegree_traceChartTarget_le (b : Module.Basis (Fin k) K₀ L)
    (f g : (Fin k → K₀) → F) (s : ℕ) (x : L) :
    (traceChartTarget E b f g s x).totalDegree ≤ s := by
  refine (MvPolynomial.totalDegree_add _ _).trans (max_le (by simp) ?_)
  refine (MvPolynomial.totalDegree_mul _ _).trans ?_
  rw [MvPolynomial.totalDegree_C, Nat.add_zero]
  refine MvPolynomial.totalDegree_finsetSum_le fun j _ ↦ ?_
  refine (MvPolynomial.totalDegree_mul _ _).trans ?_
  rw [MvPolynomial.totalDegree_C, zero_add]
  exact (MvPolynomial.totalDegree_pow _ _).trans (by simp [MvPolynomial.totalDegree_X])

/-- At `a`, the chart target is `f(ψ x) + L(x) g(ψ x)`.
Here `L` is the multiplier of the trace family at `(aⱼ ^ s)ⱼ`. -/
theorem aeval_traceChartTarget (b : Module.Basis (Fin k) K₀ L) (f g : (Fin k → K₀) → F)
    (s : ℕ) (x : L) (a : Fin (k + 1) → E) :
    MvPolynomial.aeval a (traceChartTarget E b f g s x) =
      algebraMap F E (f (traceCoordinateEquiv K₀ b x)) +
        (ReedSolomon.familyMultiplier (traceFamily E b) fun j ↦ a j ^ s).eval
          (algebraMap L E x) * algebraMap F E (g (traceCoordinateEquiv K₀ b x)) := by
  simp [traceChartTarget, ReedSolomon.familyMultiplier_apply, Polynomial.eval_finsetSum,
    mul_comm]

end Target

section Transport

variable [Algebra F E] [Algebra K₀ F] [Algebra K₀ E] [IsScalarTower K₀ L E]
  [IsScalarTower K₀ F E] [DecidableEq F]

/-- The agreements of `P̃` with `f ∘ ψ + L̃_α (g ∘ ψ)` on `L` are as many as those of `P`.
Here `P̃` and `L̃_α` are the trace substitutions of `P` and `L_α` mapped into `E`.
The agreements of `P` are with `f + L_α g` on the grid, and `ψ(x) = (Tr(bᵢ x))ᵢ`. -/
theorem ncard_eval_traceSubstitution_eq (b : Module.Basis (Fin k) K₀ L)
    (f g : (Fin k → K₀) → F) (α : Fin (k + 1) → F) (P : MvPolynomial (Fin k) F) :
    {x : L | (traceSubstitution b (P.map (algebraMap F E))).eval (algebraMap L E x) =
        algebraMap F E (f (traceCoordinateEquiv K₀ b x)) +
          (ReedSolomon.familyMultiplier (traceFamily E b) (algebraMap F E ∘ α)).eval
            (algebraMap L E x) * algebraMap F E (g (traceCoordinateEquiv K₀ b x))}.ncard =
      #(agreementSet (combinedWord f g (affineMultiplier α)) P) := by
  classical
  have := Module.Finite.of_basis b
  have : Finite L := Module.finite_of_finite K₀
  have : Fintype L := Fintype.ofFinite L
  rw [← card_polynomialAgreementSet_traceSubstitution (F' := E) b f g (affineMultiplier α) P,
    ← Set.ncard_coe_finset]
  congr 1
  ext x
  simp [ReedSolomon.combinedWord, traceSubstitution_map_affineMultiplier_eq_familyMultiplier]

/-- An interpolant on `L` vanishes along the substituted multiplier and candidate.

Let `q₀ = |K₀|`, and let `e = q₀ᵏ⁻¹`, with natural-number subtraction.
The interpolant is for the words `f ∘ ψ, g ∘ ψ` on `L ⊆ E`.
It covers multipliers of degree at most `e` and candidates of degree at most `d e`.
Let `P` have total degree at most `d` and `A` agreements with `f + L_α g` on the grid.
Then the interpolant vanishes along `L̃_α` and `P̃`, the trace substitutions mapped into `E`. -/
theorem multiplierEval_traceSubstitution_eq_zero [Fintype L] [DecidableEq E]
    (b : Module.Basis (Fin k) K₀ L) (f g : (Fin k → K₀) → F) {d A m D M : ℕ}
    {Q : MvPolynomial ReedSolomon.AffineVar E}
    (hQ : ReedSolomon.IsMultiplierInterpolant (ReedSolomon.algebraMapDomain L E)
      (fun x ↦ algebraMap F E (f (traceCoordinateEquiv K₀ b x)))
      (fun x ↦ algebraMap F E (g (traceCoordinateEquiv K₀ b x))) (Fintype.card K₀ ^ (k - 1))
      (d * Fintype.card K₀ ^ (k - 1)) A m D M Q)
    (α : Fin (k + 1) → F) {P : MvPolynomial (Fin k) F} (hP : P.totalDegree ≤ d)
    (hA : A ≤ #(agreementSet (combinedWord f g (affineMultiplier α)) P)) :
    ReedSolomon.multiplierEval
      (ReedSolomon.familyMultiplier (traceFamily E b) (algebraMap F E ∘ α))
      (traceSubstitution b (P.map (algebraMap F E))) Q = 0 := by
  rw [← traceSubstitution_map_affineMultiplier_eq_familyMultiplier]
  refine hQ.vanish _ _ (natDegree_traceSubstitution_map_affineMultiplier_le b α)
    (degree_le_of_natDegree_le ((natDegree_traceSubstitution_le b _).trans
      (Nat.mul_le_mul_right _ ((Finset.sup_mono
        (MvPolynomial.support_map_subset (algebraMap F E) P)).trans hP)))) ?_
  rwa [card_polynomialAgreementSet_traceSubstitution]

end Transport

section Cuts

/-- Linear functionals cutting out the substituted polynomials of total degree at most `d`.

Every functional kills `T(P)` for each `P` over `E` of total degree at most `d`.
Here `T` is the trace substitution.
A polynomial of degree at most `d q₀ᵏ⁻¹` killed by every functional is such a `T(P)`.
Here `q₀ = |K₀|`, and `k - 1` is natural-number subtraction. -/
structure IsTraceImageCuts (b : Module.Basis (Fin k) K₀ L) (d : ℕ)
    (cuts : List (E[X] →ₗ[E] E)) : Prop where
  /-- Every functional kills the substituted polynomials of total degree at most `d`. -/
  apply_traceSubstitution_eq_zero : ∀ P : MvPolynomial (Fin k) E, P.totalDegree ≤ d →
    ∀ Λ ∈ cuts, Λ (traceSubstitution b P) = 0
  /-- A polynomial of degree at most `d q₀ᵏ⁻¹` killed by every functional is substituted. -/
  exists_traceSubstitution_eq : ∀ H : E[X], H.degree ≤ (d * Fintype.card K₀ ^ (k - 1) : ℕ) →
    (∀ Λ ∈ cuts, Λ H = 0) → ∃ P : MvPolynomial (Fin k) E, P.totalDegree ≤ d ∧
      traceSubstitution b P = H

variable (E) in
/-- Finitely many functionals cut out the substituted polynomials of total degree at most `d`.
The substitution is by trace polynomials of a basis `b` of `L` over `K₀`. -/
theorem exists_isTraceImageCuts (b : Module.Basis (Fin k) K₀ L) (d : ℕ) :
    ∃ cuts : List (E[X] →ₗ[E] E), IsTraceImageCuts b d cuts := by
  obtain ⟨l, h₁, h₂⟩ := exists_list_linearMap_of_le_degreeLE
    (V := (MvPolynomial.restrictTotalDegree (Fin k) E d).map (traceSubstitution b).toLinearMap)
    (N := d * Fintype.card K₀ ^ (k - 1)) (by
      rintro _ ⟨P, hP, rfl⟩
      exact mem_degreeLE.mpr (degree_le_of_natDegree_le ((natDegree_traceSubstitution_le b P).trans
        (Nat.mul_le_mul_right _ ((MvPolynomial.mem_restrictTotalDegree _ _ _).mp hP)))))
  refine ⟨l, fun P hP Λ hΛ ↦ h₁ Λ hΛ _ ⟨P, (MvPolynomial.mem_restrictTotalDegree _ _ _).mpr hP,
    rfl⟩, fun H hH hl ↦ ?_⟩
  obtain ⟨P, hP, rfl⟩ := h₂ H hH hl
  exact ⟨P, (MvPolynomial.mem_restrictTotalDegree _ _ _).mp hP, rfl⟩

end Cuts

end ReedMuller

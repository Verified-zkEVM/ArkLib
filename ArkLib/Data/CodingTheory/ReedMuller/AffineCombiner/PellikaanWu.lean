/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Coratger
-/
module

public import ArkLib.Data.CodingTheory.ReedMuller.AffineCombiner.Basic
public import ArkLib.Data.CodingTheory.ReedMuller.PellikaanWu
public import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.AffineCombiner.Basic

/-!
# Reed–Muller candidates as Reed–Solomon candidates

Let `L` be an extension of degree `k` of a finite field `K₀` with `q₀` elements, so `n = q₀ᵏ`.
A basis `b` of `L` over `K₀` gives the trace coordinates `ψ : L ≃ K₀ᵏ`.
Let `F'` be a field containing `L`, and view `L` as an evaluation domain inside `F'`.

Received words `f, g` on the grid become the words `f ∘ ψ, g ∘ ψ` on `L`.
A multiplier `M` and a candidate `P` become their trace substitutions `M̃` and `P̃`.
Then `ψ` maps the agreement set of `P̃` with `f ∘ ψ + M̃ (g ∘ ψ)` onto that of `P` with `f + M g`.
It also maps the agreement loss of the substituted witnesses onto that of `(F₀, G₀)`.
Since substitution is a ring homomorphism, a witness pair maps to a witness pair.

Take the affine multiplier `L_α = α₀ + α₁ X₁ + ⋯ + αₖ Xₖ`.
Its substitution is `L̃_α = α₀ + ∑ αᵢ T_{bᵢ}`, of degree at most `q₀ᵏ⁻¹`.
Distinct coefficient vectors `α` give distinct `L̃_α`.

This is the candidate correspondence of Appendix A of [CWYZ26], following [PW04].
It is part of the reduction to univariate polynomials.
The paper works over the smallest field containing `F_q` and `F_n`.
Here `F'` is any field containing `L`, and words take values in `F'`.

The exponent `k - 1` uses subtraction in `ℕ`.

The [paper page](../../../../../docs/kb/papers/CWYZ26.md) records the correspondence.

## Main definitions

* `ReedMuller.traceDomain`: the evaluation domain `L ↪ F'`.

## Main statements

* `ReedMuller.traceDomain_apply`: a domain point is its image in `F'`.
* `ReedMuller.map_polynomialAgreementSet_traceSubstitution` and
  `ReedMuller.card_polynomialAgreementSet_traceSubstitution`: agreement sets correspond.
* `ReedMuller.map_agreementLoss_traceSubstitution` and
  `ReedMuller.card_agreementLoss_traceSubstitution`: agreement losses correspond.
* `ReedMuller.isLossWitness_traceSubstitution`: witness pairs map to witness pairs.
* `ReedMuller.traceSubstitution_affineMultiplier`: the substituted multiplier.
* `ReedMuller.natDegree_traceSubstitution_affineMultiplier_le`: its degree is at most
  `q₀ᵏ⁻¹`.
* `ReedMuller.traceSubstitution_affineMultiplier_injective`: distinct coefficient vectors
  give distinct substituted multipliers.

## References

* [Chiesa, A., Weissenberg, G., Yogev, E., and Zheng, K. Z.,
    *Affine combiners for Reed–Solomon proximity gaps*][CWYZ26]
* [Pellikaan, R., and Wu, X.-W., *List decoding of q-ary Reed–Muller codes*][PW04]
-/

@[expose] public section

open Polynomial FiniteField Finset

namespace ReedMuller

variable (L F' : Type*) [Field L] [Field F'] [Algebra L F']

/-- The field `L` as an evaluation domain inside `F'`. -/
def traceDomain : L ↪ F' :=
  ⟨algebraMap L F', (algebraMap L F').injective⟩

/-- The domain point `x ∈ L` is `x` viewed in `F'`. -/
@[simp]
theorem traceDomain_apply (x : L) : traceDomain L F' x = algebraMap L F' x :=
  rfl

variable {K₀ L F'} [Field K₀] [Fintype K₀] [Algebra K₀ L] {k : ℕ}

/-- Let `b` be a basis of `L` over `K₀` with `k` elements.
The affine multiplier `α₀ + α₁ X₁ + ⋯ + αₖ Xₖ` substitutes to `α₀ + ∑ αᵢ T_{bᵢ}`.
Here `T_c` is the trace polynomial of `c`. -/
theorem traceSubstitution_affineMultiplier (b : Module.Basis (Fin k) K₀ L)
    (α : Fin (k + 1) → F') :
    traceSubstitution b (affineMultiplier α) =
      C (α 0) + ∑ i, C (α i.succ) * (tracePolynomial K₀ (b i)).map (algebraMap L F') := by
  simp [affineMultiplier]

/-- Let `b` be a basis of `L` over `K₀` with `k` elements, and `q₀ = |K₀|`.
The substituted affine multiplier has degree at most `q₀ᵏ⁻¹`. -/
theorem natDegree_traceSubstitution_affineMultiplier_le (b : Module.Basis (Fin k) K₀ L)
    (α : Fin (k + 1) → F') :
    (traceSubstitution b (affineMultiplier α)).natDegree ≤ Fintype.card K₀ ^ (k - 1) :=
  (natDegree_traceSubstitution_le b _).trans <|
    (Nat.mul_le_mul_right _ (totalDegree_affineMultiplier_le α)).trans_eq (one_mul _)

variable [Finite L] [Algebra K₀ F'] [IsScalarTower K₀ L F']

/-- Let `b` be a basis of the finite field `L` over `K₀`.
Distinct coefficient vectors give distinct substituted affine multipliers. -/
theorem traceSubstitution_affineMultiplier_injective (b : Module.Basis (Fin k) K₀ L) :
    Function.Injective fun α : Fin (k + 1) → F' ↦ traceSubstitution b (affineMultiplier α) :=
  fun _ _ h ↦ affineMultiplier_injective <| eq_of_traceSubstitution_eq_of_totalDegree_lt b
    ((totalDegree_affineMultiplier_le _).trans_lt Fintype.one_lt_card)
    ((totalDegree_affineMultiplier_le _).trans_lt Fintype.one_lt_card) h

variable [Fintype L] [DecidableEq F']

/-- Let `b` be a basis of the finite field `L` over `K₀`, and `ψ(x) = (Tr(bᵢ x))ᵢ`.
Let `f, g` be words on the grid `K₀ᵏ`, and `M, P` polynomials over `F'`.
Let `M̃` and `P̃` be the trace substitutions of `M` and `P`.
Then `ψ` maps the agreement set of `P̃` with `f ∘ ψ + M̃ (g ∘ ψ)` on `L` onto that of `P`.
The latter is the agreement set of `P` with `f + M g` on the grid. -/
theorem map_polynomialAgreementSet_traceSubstitution (b : Module.Basis (Fin k) K₀ L)
    (f g : (Fin k → K₀) → F') (M P : MvPolynomial (Fin k) F') :
    (ReedSolomon.polynomialAgreementSet (traceDomain L F')
        (ReedSolomon.combinedWord (traceDomain L F') (fun x ↦ f (traceCoordinateEquiv K₀ b x))
          (fun x ↦ g (traceCoordinateEquiv K₀ b x)) (traceSubstitution b M))
        (traceSubstitution b P)).map
      (traceCoordinateEquiv K₀ b).toEquiv.toEmbedding =
      agreementSet (combinedWord f g M) P := by
  ext z
  obtain ⟨x, rfl⟩ := (traceCoordinateEquiv K₀ b).surjective z
  simp [ReedSolomon.combinedWord, eval_traceSubstitution]

/-- Let `b` be a basis of the finite field `L` over `K₀`, and `ψ(x) = (Tr(bᵢ x))ᵢ`.
Let `f, g` be words on the grid `K₀ᵏ`, and `M, P` polynomials over `F'`.
Let `M̃` and `P̃` be the trace substitutions of `M` and `P`.
The agreement set of `P̃` with `f ∘ ψ + M̃ (g ∘ ψ)` on `L` has as many points as that of `P`.
The latter is the agreement set of `P` with `f + M g` on the grid. -/
theorem card_polynomialAgreementSet_traceSubstitution (b : Module.Basis (Fin k) K₀ L)
    (f g : (Fin k → K₀) → F') (M P : MvPolynomial (Fin k) F') :
    #(ReedSolomon.polynomialAgreementSet (traceDomain L F')
        (ReedSolomon.combinedWord (traceDomain L F') (fun x ↦ f (traceCoordinateEquiv K₀ b x))
          (fun x ↦ g (traceCoordinateEquiv K₀ b x)) (traceSubstitution b M))
        (traceSubstitution b P)) =
      #(agreementSet (combinedWord f g M) P) := by
  rw [← map_polynomialAgreementSet_traceSubstitution b f g M P, card_map]

/-- Let `b` be a basis of the finite field `L` over `K₀`, and `ψ(x) = (Tr(bᵢ x))ᵢ`.
Let `f, g` be words on the grid `K₀ᵏ`, and `M, P, F₀, G₀` polynomials over `F'`.
Take the agreement loss of their substitutions for the words `f ∘ ψ, g ∘ ψ` on `L`.
The bijection `ψ` maps it onto the agreement loss of `P, F₀, G₀` for `f, g` on the grid. -/
theorem map_agreementLoss_traceSubstitution (b : Module.Basis (Fin k) K₀ L)
    (f g : (Fin k → K₀) → F') (M P F₀ G₀ : MvPolynomial (Fin k) F') :
    (ReedSolomon.agreementLoss (traceDomain L F') (fun x ↦ f (traceCoordinateEquiv K₀ b x))
        (fun x ↦ g (traceCoordinateEquiv K₀ b x)) (traceSubstitution b M)
        (traceSubstitution b P) (traceSubstitution b F₀) (traceSubstitution b G₀)).map
      (traceCoordinateEquiv K₀ b).toEquiv.toEmbedding =
      agreementLoss f g M P F₀ G₀ := by
  ext z
  obtain ⟨x, rfl⟩ := (traceCoordinateEquiv K₀ b).surjective z
  simp [ReedSolomon.agreementLoss, ReedSolomon.combinedWord, eval_traceSubstitution]

/-- Let `b` be a basis of the finite field `L` over `K₀`, and `ψ(x) = (Tr(bᵢ x))ᵢ`.
Let `f, g` be words on the grid `K₀ᵏ`, and `M, P, F₀, G₀` polynomials over `F'`.
Take the agreement loss of their substitutions for the words `f ∘ ψ, g ∘ ψ` on `L`.
It has as many points as the agreement loss of `P, F₀, G₀` for `f, g` on the grid. -/
theorem card_agreementLoss_traceSubstitution (b : Module.Basis (Fin k) K₀ L)
    (f g : (Fin k → K₀) → F') (M P F₀ G₀ : MvPolynomial (Fin k) F') :
    #(ReedSolomon.agreementLoss (traceDomain L F') (fun x ↦ f (traceCoordinateEquiv K₀ b x))
        (fun x ↦ g (traceCoordinateEquiv K₀ b x)) (traceSubstitution b M)
        (traceSubstitution b P) (traceSubstitution b F₀) (traceSubstitution b G₀)) =
      #(agreementLoss f g M P F₀ G₀) := by
  rw [← map_agreementLoss_traceSubstitution b f g M P F₀ G₀, card_map]

/-- Let `b` be a basis of the finite field `L` over `K₀`, and `ψ(x) = (Tr(bᵢ x))ᵢ`.
Let `P = F₀ + M G₀` over `F'`, with at most `s` lost points for words `f, g` on the grid `K₀ᵏ`.
Then `P̃ = F̃₀ + M̃ G̃₀`, with at most `s` lost points for the words `f ∘ ψ, g ∘ ψ` on `L`. -/
theorem isLossWitness_traceSubstitution (b : Module.Basis (Fin k) K₀ L)
    {f g : (Fin k → K₀) → F'} {s : ℕ} {M P F₀ G₀ : MvPolynomial (Fin k) F'}
    (h : IsLossWitness f g s M P F₀ G₀) :
    ReedSolomon.IsLossWitness (traceDomain L F') (fun x ↦ f (traceCoordinateEquiv K₀ b x))
      (fun x ↦ g (traceCoordinateEquiv K₀ b x)) s (traceSubstitution b M)
      (traceSubstitution b P) (traceSubstitution b F₀) (traceSubstitution b G₀) :=
  ⟨by rw [h.1, map_add, map_mul],
    (card_agreementLoss_traceSubstitution b f g M P F₀ G₀).trans_le h.2⟩

end ReedMuller

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
Received words, candidates and multipliers live over a field `F ⊇ K₀`.
Let `F'` be a field containing both `F` and `L`, and view `L` as an evaluation domain in `F'`.

Received words `f, g` on the grid become the words `f ∘ ψ, g ∘ ψ` on `L`, with values in `F'`.
A multiplier `M` and a candidate `P` are mapped into `F'`.
Their trace substitutions are `M̃` and `P̃`.
The reduction uses three facts.

First, `ψ` maps the agreement set of `P̃` with `f ∘ ψ + M̃ (g ∘ ψ)` onto that of `P`.
The latter is the agreement set of `P` with `f + M g` on the grid.
So the agreement counts are equal, and `deg P̃ ≤ deg P · q₀ᵏ⁻¹` bounds the degree.

Second, the affine multiplier `L_α = α₀ + α₁ X₁ + ⋯ + αₖ Xₖ` becomes `L̃_α = α₀ + ∑ αᵢ T_{bᵢ}`.
It has degree at most `q₀ᵏ⁻¹`, and distinct coefficient vectors `α` give distinct `L̃_α`.

Third, candidates of total degree below `q₀` are determined by their substitutions.
That injectivity is proved with the substitution, not here.

This is the candidate correspondence of Appendix A of [CWYZ26], following [PW04].
The paper works over the smallest field containing `F_q` and `F_n`.
Here `F'` is any field containing `F` and `L` compatibly over `K₀`.

The exponent `k - 1` uses subtraction in `ℕ`.

The [paper page](../../../../../docs/kb/papers/CWYZ26.md) records the correspondence.

## Main statements

* `ReedMuller.map_polynomialAgreementSet_traceSubstitution` and
  `ReedMuller.card_polynomialAgreementSet_traceSubstitution`: agreement sets correspond.
* `ReedMuller.natDegree_traceSubstitution_map_affineMultiplier_le`: the substituted multiplier
  `L̃_α` has degree at most `q₀ᵏ⁻¹`.
* `ReedMuller.traceSubstitution_map_affineMultiplier_injective`: distinct coefficient vectors
  give distinct substituted multipliers.

## References

* [Chiesa, A., Weissenberg, G., Yogev, E., and Zheng, K. Z.,
    *Affine combiners for Reed–Solomon proximity gaps*][CWYZ26]
* [Pellikaan, R., and Wu, X.-W., *List decoding of q-ary Reed–Muller codes*][PW04]
-/

@[expose] public section

open Polynomial FiniteField Finset

namespace ReedMuller

variable {K₀ L F F' : Type*} [Field K₀] [Fintype K₀] [Field L] [Algebra K₀ L] [Field F]
  [Field F'] [Algebra L F'] [Algebra F F'] {k : ℕ}

/-- Let `b` be a basis of `L` over `K₀` with `k` elements, `q₀ = |K₀|` and `F, L ⊆ F'`.
The substituted affine multiplier has degree at most `q₀ᵏ⁻¹`. -/
theorem natDegree_traceSubstitution_map_affineMultiplier_le (b : Module.Basis (Fin k) K₀ L)
    (α : Fin (k + 1) → F) :
    (traceSubstitution b ((affineMultiplier α).map (algebraMap F F'))).natDegree ≤
      Fintype.card K₀ ^ (k - 1) := by
  rw [map_affineMultiplier]
  exact (natDegree_traceSubstitution_le b _).trans
    ((Nat.mul_le_mul_right _ (totalDegree_affineMultiplier_le _)).trans_eq (one_mul _))

variable [Algebra K₀ F'] [IsScalarTower K₀ L F']

/-- Let `b` be a basis of `L` over `K₀`, and `F, L ⊆ F'`.
Distinct coefficient vectors over `F` give distinct substituted affine multipliers. -/
theorem traceSubstitution_map_affineMultiplier_injective (b : Module.Basis (Fin k) K₀ L) :
    Function.Injective fun α : Fin (k + 1) → F ↦
      traceSubstitution b ((affineMultiplier α).map (algebraMap F F')) :=
  fun _ _ h ↦ affineMultiplier_injective <| injOn_traceSubstitution_map b
    ((totalDegree_affineMultiplier_le _).trans_lt Fintype.one_lt_card)
    ((totalDegree_affineMultiplier_le _).trans_lt Fintype.one_lt_card) h

variable [Algebra K₀ F] [IsScalarTower K₀ F F'] [Fintype L] [DecidableEq F] [DecidableEq F']

/-- Let `b` be a basis of `L` over `K₀`, `ψ(x) = (Tr(bᵢ x))ᵢ`, and `K₀ ⊆ F ⊆ F'` with `L ⊆ F'`.
Let `f, g` be words on the grid `K₀ᵏ` over `F`, and `M, P` polynomials over `F`.
Let `M̃` and `P̃` be the trace substitutions of their images in `F'`.
Then `ψ` maps the agreement set of `P̃` with `f ∘ ψ + M̃ (g ∘ ψ)` on `L` onto that of `P`.
The latter is the agreement set of `P` with `f + M g` on the grid. -/
theorem map_polynomialAgreementSet_traceSubstitution (b : Module.Basis (Fin k) K₀ L)
    (f g : (Fin k → K₀) → F) (M P : MvPolynomial (Fin k) F) :
    (ReedSolomon.polynomialAgreementSet (ReedSolomon.algebraMapDomain L F')
        (ReedSolomon.combinedWord (ReedSolomon.algebraMapDomain L F')
          (fun x ↦ algebraMap F F' (f (traceCoordinateEquiv K₀ b x)))
          (fun x ↦ algebraMap F F' (g (traceCoordinateEquiv K₀ b x)))
          (traceSubstitution b (M.map (algebraMap F F'))))
        (traceSubstitution b (P.map (algebraMap F F')))).map
      (traceCoordinateEquiv K₀ b).toEquiv.toEmbedding =
      agreementSet (combinedWord f g M) P := by
  ext z
  obtain ⟨x, rfl⟩ := (traceCoordinateEquiv K₀ b).surjective z
  simp [ReedSolomon.combinedWord, eval_traceSubstitution, eval_gridPoint_map, ← map_mul,
    ← map_add, -MvPolynomial.eval_map]

/-- Let `b` be a basis of `L` over `K₀`, `ψ(x) = (Tr(bᵢ x))ᵢ`, and `K₀ ⊆ F ⊆ F'` with `L ⊆ F'`.
Let `f, g` be words on the grid `K₀ᵏ` over `F`, and `M, P` polynomials over `F`.
Let `M̃` and `P̃` be the trace substitutions of their images in `F'`.
The agreement set of `P̃` with `f ∘ ψ + M̃ (g ∘ ψ)` on `L` has as many points as that of `P`.
The latter is the agreement set of `P` with `f + M g` on the grid. -/
theorem card_polynomialAgreementSet_traceSubstitution (b : Module.Basis (Fin k) K₀ L)
    (f g : (Fin k → K₀) → F) (M P : MvPolynomial (Fin k) F) :
    #(ReedSolomon.polynomialAgreementSet (ReedSolomon.algebraMapDomain L F')
        (ReedSolomon.combinedWord (ReedSolomon.algebraMapDomain L F')
          (fun x ↦ algebraMap F F' (f (traceCoordinateEquiv K₀ b x)))
          (fun x ↦ algebraMap F F' (g (traceCoordinateEquiv K₀ b x)))
          (traceSubstitution b (M.map (algebraMap F F'))))
        (traceSubstitution b (P.map (algebraMap F F')))) =
      #(agreementSet (combinedWord f g M) P) := by
  rw [← map_polynomialAgreementSet_traceSubstitution (F' := F') b f g M P, card_map]

end ReedMuller

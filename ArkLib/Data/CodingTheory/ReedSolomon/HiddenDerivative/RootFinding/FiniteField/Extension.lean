/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.Polynomial.Differential.Basic
public import ArkLib.ToMathlib.FieldTheory.FiniteExtension


/-!
# Extension-field transport for differential solutions

This file supplies the base-to-extension direction needed by differential root counting. Mapping
coefficients commutes with differential specialization, preserves the bounded-degree condition,
and therefore embeds base-field solutions into extension-field solutions. The reverse direction is
intentionally absent: an equation can acquire new solutions after extending the field.

The characteristic contract is transported separately. A larger extension has more elements, but
has exactly the same characteristic as its base field.
-/

@[expose] public section

open PolynomialDifferential


namespace ReedSolomon
namespace HiddenDerivative

noncomputable section

open Polynomial

variable {F E : Type*} {d D : ℕ}

/-! ### Finiteness of bounded solutions -/

/-- Over a finite field, the type of degree-bounded solutions to any differential equation is
finite. The degree bound is essential: the ambient polynomial type itself is infinite. -/
instance _root_.PolynomialDifferential.BoundedSolution.instFinite
    [Field F] [Finite F]
    (Q : DifferentialPolynomial F d) (D : ℕ) : Finite (BoundedSolution Q D) := by
  let := Fintype.ofFinite F
  let : Fintype (Polynomial.degreeLT F (D + 1)) :=
    Fintype.ofEquiv (Fin (D + 1) → F) (Polynomial.degreeLTEquiv F (D + 1)).toEquiv.symm
  exact Subtype.finite

/-! ### Naturality of differential specialization -/

/-- Differential specialization commutes with mapping coefficients along a ring homomorphism. -/
theorem map_differentialSpecialization [CommSemiring F] [CommSemiring E]
    (f : F →+* E) (Q : DifferentialPolynomial F d) (P : F[X]) :
    (differentialSpecialization Q P).map f =
      differentialSpecialization (MvPolynomial.map f Q) (P.map f) := by
  rw [differentialSpecialization, differentialSpecialization,
    MvPolynomial.eval₂Hom_map_hom]
  change (Polynomial.mapRingHom f)
      ((MvPolynomial.eval₂Hom Polynomial.C
        (fun v ↦ match v with
          | none => Polynomial.X
          | some j => Polynomial.hasseDeriv j P)) Q) = _
  rw [MvPolynomial.map_eval₂Hom]
  apply MvPolynomial.eval₂Hom_congr
  · ext a
    simp
  · funext v
    cases v with
    | none => simp
    | some j => simp
  · rfl

/-! ### Mapping bounded solutions -/

/-- Map a degree-bounded polynomial along a coefficient-ring homomorphism. -/
def mapDegreeLT [CommSemiring F] [CommSemiring E] (f : F →+* E)
    (P : Polynomial.degreeLT F (D + 1)) : Polynomial.degreeLT E (D + 1) :=
  ⟨P.1.map f, by
    rw [Polynomial.mem_degreeLT]
    exact Polynomial.degree_map_le.trans_lt (Polynomial.mem_degreeLT.mp P.2)⟩

@[simp]
theorem mapDegreeLT_polynomial [CommSemiring F] [CommSemiring E] (f : F →+* E)
    (P : Polynomial.degreeLT F (D + 1)) : (mapDegreeLT f P : E[X]) = P.1.map f :=
  rfl

/-- Map a bounded differential solution to a bounded solution of the coefficient-mapped
equation. -/
def _root_.PolynomialDifferential.BoundedSolution.map
    [CommSemiring F] [CommSemiring E] (f : F →+* E)
    {Q : DifferentialPolynomial F d} {D : ℕ} (P : BoundedSolution Q D) :
    BoundedSolution (MvPolynomial.map f Q) D :=
  ⟨mapDegreeLT f P.1, by
    change differentialSpecialization (MvPolynomial.map f Q) (P.polynomial.map f) = 0
    rw [← map_differentialSpecialization, P.equation, Polynomial.map_zero]⟩

@[simp]
theorem _root_.PolynomialDifferential.BoundedSolution.map_polynomial
    [CommSemiring F] [CommSemiring E]
    (f : F →+* E) {Q : DifferentialPolynomial F d} {D : ℕ} (P : BoundedSolution Q D) :
    (P.map f).polynomial = P.polynomial.map f :=
  rfl

/-- Mapping bounded solutions is injective whenever the coefficient map is injective. -/
theorem _root_.PolynomialDifferential.BoundedSolution.map_injective
    [CommSemiring F] [CommSemiring E]
    (f : F →+* E) (hf : Function.Injective f) {Q : DifferentialPolynomial F d} {D : ℕ} :
    Function.Injective (BoundedSolution.map f : BoundedSolution Q D →
      BoundedSolution (MvPolynomial.map f Q) D) := by
  intro P R hPR
  apply Subtype.ext
  apply Subtype.ext
  apply Polynomial.map_injective f hf
  exact congrArg (fun S : BoundedSolution (MvPolynomial.map f Q) D ↦ S.polynomial) hPR

/-- The canonical embedding of bounded base-field solutions into bounded extension-field
solutions. -/
def _root_.PolynomialDifferential.BoundedSolution.algebraMapEmbedding
    [Field F] [Field E] [Algebra F E]
    (Q : DifferentialPolynomial F d) (D : ℕ) :
    BoundedSolution Q D ↪ BoundedSolution (MvPolynomial.map (algebraMap F E) Q) D :=
  ⟨BoundedSolution.map (algebraMap F E),
    BoundedSolution.map_injective (algebraMap F E) (algebraMap F E).injective⟩

/-- Base-field bounded solutions inject into extension-field bounded solutions. This is the
cardinality direction used for descent after counting over a larger witness field. -/
theorem _root_.PolynomialDifferential.BoundedSolution.natCard_le_extension
    [Field F] [Field E] [Algebra F E]
    [Finite F] [Finite E] (Q : DifferentialPolynomial F d) (D : ℕ) :
    Nat.card (BoundedSolution Q D) ≤
      Nat.card (BoundedSolution (MvPolynomial.map (algebraMap F E) Q) D) := by
  exact Nat.card_le_card_of_injective (BoundedSolution.algebraMapEmbedding Q D)
    (BoundedSolution.algebraMapEmbedding Q D).injective

/-- Any cardinality bound proved after mapping the equation to an extension field descends to the
base-field bounded solutions. The mapped equation is explicit in the premise to prevent accidental
use of an unrelated extension-field equation. -/
theorem _root_.PolynomialDifferential.BoundedSolution.natCard_le_of_extension_bound
    [Field F] [Field E] [Algebra F E]
    [Finite F] [Finite E] (Q : DifferentialPolynomial F d) (D bound : ℕ)
    (hbound :
      Nat.card (BoundedSolution (MvPolynomial.map (algebraMap F E) Q) D) ≤ bound) :
    Nat.card (BoundedSolution Q D) ≤ bound :=
  (BoundedSolution.natCard_le_extension Q D).trans hbound

/-- Finite subsets of base-field solutions inherit the same one-way cardinality comparison when
their images lie in a chosen finite subset of extension-field solutions. -/
theorem _root_.PolynomialDifferential.BoundedSolution.finset_card_le_extension
    [Field F] [Field E] [Algebra F E]
    (Q : DifferentialPolynomial F d) (D : ℕ)
    (base : Finset (BoundedSolution Q D))
    (extension : Finset (BoundedSolution (MvPolynomial.map (algebraMap F E) Q) D))
    (hmaps : ∀ P ∈ base, P.map (algebraMap F E) ∈ extension) :
    base.card ≤ extension.card := by
  exact Finset.card_le_card_of_injOn (BoundedSolution.map (algebraMap F E)) hmaps
    (BoundedSolution.map_injective (algebraMap F E) (algebraMap F E).injective).injOn

/-! ### Characteristic-sensitive hypotheses -/

/-- An injective coefficient map preserves every individual jet degree. -/
theorem jetDegree_map_eq [CommSemiring F] [CommSemiring E]
    (f : F →+* E) (hf : Function.Injective f) (Q : DifferentialPolynomial F d)
    (j : Fin (d + 1)) : jetDegree (MvPolynomial.map f Q) j = jetDegree Q j := by
  unfold jetDegree MvPolynomial.degreeOf
  rw [MvPolynomial.degrees_map_of_injective Q hf]

/-- Passing from a field to an extension field preserves, rather than improves, the complete
characteristic contract required by coefficient lifting. -/
theorem isBelowCharacteristic_map_iff [Field F] [Field E] [Algebra F E]
    (Q : DifferentialPolynomial F d) (D : ℕ) :
    IsBelowCharacteristic D (MvPolynomial.map (algebraMap F E) Q) ↔
      IsBelowCharacteristic D Q := by
  simp only [IsBelowCharacteristic, jetDegree_map_eq (algebraMap F E) (algebraMap F E).injective,
    ← Algebra.ringChar_eq F E]

/-! ### Direction and naturality canaries -/

private def boundedSolutionZeroEquivDegreeLT [CommSemiring F] (d D : ℕ) :
    BoundedSolution (0 : DifferentialPolynomial F d) D ≃ Polynomial.degreeLT F (D + 1) where
  toFun P := P.1
  invFun P := ⟨P, by simp [differentialSpecialization]⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := rfl

private theorem natCard_boundedSolution_zero [Field F] [Finite F] (d D : ℕ) :
    Nat.card (BoundedSolution (0 : DifferentialPolynomial F d) D) = Nat.card F ^ (D + 1) := by
  calc
    Nat.card (BoundedSolution (0 : DifferentialPolynomial F d) D) =
        Nat.card (Polynomial.degreeLT F (D + 1)) :=
      Nat.card_congr (boundedSolutionZeroEquivDegreeLT d D)
    _ = Nat.card (Fin (D + 1) → F) :=
      Nat.card_congr (Polynomial.degreeLTEquiv F (D + 1)).toEquiv
    _ = Nat.card F ^ (D + 1) := by rw [Nat.card_fun, Nat.card_fin]

/-- The canonical finiteness instance supplies an ordinary `Fintype`, while a bound on mapped
extension solutions transfers directly back to the base field. -/
example :
    let E₂ := FiniteField.ExtensionAbove (ZMod 2) 2 2
    let Q : DifferentialPolynomial (ZMod 2) 0 := 0
    Nonempty (Fintype (BoundedSolution Q 0)) ∧
      Nat.card (BoundedSolution Q 0) ≤
        Nat.card (BoundedSolution (MvPolynomial.map (algebraMap (ZMod 2) E₂) Q) 0) := by
  dsimp only
  exact ⟨⟨Fintype.ofFinite _⟩,
    BoundedSolution.natCard_le_of_extension_bound _ _ _ le_rfl⟩

/-- For `Q = X + Y₀` and `P = X + 1` in characteristic two, both sides of specialization
naturality compute independently to `1`. This detects swapping the distinguished `X` and Hasse-jet
substitutions. -/
example :
    let E₂ := FiniteField.ExtensionAbove (ZMod 2) 2 2
    let f := algebraMap (ZMod 2) E₂
    let Q : DifferentialPolynomial (ZMod 2) 0 :=
      MvPolynomial.X none + MvPolynomial.X (some (0 : Fin 1))
    let P : (ZMod 2)[X] := Polynomial.X + 1
    (differentialSpecialization Q P).map f = 1 ∧
      differentialSpecialization (MvPolynomial.map f Q) (P.map f) = 1 := by
  dsimp only
  let _ : CharP (FiniteField.ExtensionAbove (ZMod 2) 2 2) 2 :=
    FiniteField.charP_extensionAbove (ZMod 2) 2 2
  have htwoCoeff : (2 : FiniteField.ExtensionAbove (ZMod 2) 2 2) = 0 :=
    CharP.cast_eq_zero _ _
  have htwo :
      (2 : (FiniteField.ExtensionAbove (ZMod 2) 2 2)[X]) = 0 := by
    change Polynomial.C (2 : FiniteField.ExtensionAbove (ZMod 2) 2 2) = 0
    rw [htwoCoeff, Polynomial.C_0]
  constructor <;>
    simp [differentialSpecialization, ← add_assoc, ← two_mul, htwo]

/-- The cardinality comparison cannot be reversed: the zero equation of degree zero has strictly
more constant solutions after passing from the two-element field to the chosen four-element
extension. -/
example :
    let E₂ := FiniteField.ExtensionAbove (ZMod 2) 2 2
    Nat.card (BoundedSolution (0 : DifferentialPolynomial (ZMod 2) 0) 0) <
      Nat.card (BoundedSolution
        (MvPolynomial.map (algebraMap (ZMod 2) E₂) 0 : DifferentialPolynomial E₂ 0) 0) := by
  dsimp only
  have hlog : Nat.log 2 2 = 1 := Nat.log_eq_of_pow_le_of_lt_pow (by decide) (by decide)
  have hmapZero :
      MvPolynomial.map (algebraMap (ZMod 2) (FiniteField.ExtensionAbove (ZMod 2) 2 2))
          (0 : DifferentialPolynomial (ZMod 2) 0) = 0 :=
    map_zero _
  rw [hmapZero]
  change Nat.card (BoundedSolution (0 : DifferentialPolynomial (ZMod 2) 0) 0) <
    Nat.card (BoundedSolution
      (0 : DifferentialPolynomial (FiniteField.ExtensionAbove (ZMod 2) 2 2) 0) 0)
  rw [natCard_boundedSolution_zero, natCard_boundedSolution_zero,
    FiniteField.natCard_extensionAbove, Nat.card_zmod]
  norm_num [FiniteField.extensionDegreeAbove, hlog]

end

end HiddenDerivative
end ReedSolomon

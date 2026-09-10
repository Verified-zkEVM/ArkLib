/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.Taylor.Numerator


/-!
# Taylor numerators over coefficient algebras

The recurrence retains polynomial parameters in the coefficient ring. Its only inverse is
the binomial scalar inverse in the base field; it never inverts a coefficient-ring separant.
Coefficient specialization is therefore meaningful even where the separant vanishes.
-/

@[expose] public section

open PolynomialDifferential


namespace MvPolynomial

/-- Separating the Taylor variable commutes with coefficient specialization. -/
theorem map_optionEquivLeft {A B σ : Type*} [CommRing A] [CommRing B]
    (f : A →+* B) (Q : MvPolynomial (Option σ) A) :
    Polynomial.map (MvPolynomial.map f) (optionEquivLeft A σ Q) =
      optionEquivLeft B σ (MvPolynomial.map f Q) := by
  have he : (Polynomial.mapRingHom (MvPolynomial.map f)).comp
      (optionEquivLeft A σ).toRingHom =
      (optionEquivLeft B σ).toRingHom.comp (MvPolynomial.map f) := by
    ext a : 2
    · simp
    · cases a <;> simp
  exact DFunLike.congr_fun he Q

end MvPolynomial

namespace ReedSolomon.HiddenDerivative

noncomputable section

open MvPolynomial

variable {F A B : Type*} [Field F] [CommRing A] [CommRing B] {r : ℕ}

/-- The initial separant with its coefficient ring retained. -/
def initialJetSeparantOver (center : A) (Q : DifferentialPolynomial A r) :
    MvPolynomial (Fin (r + 1)) A :=
  aeval (fun i ↦ i.elim (C center) X) (separant Q (Fin.last r))

/-- The initial separant commutes with arbitrary coefficient-ring specialization. -/
theorem map_initialJetSeparantOver (f : A →+* B) (center : A)
    (Q : DifferentialPolynomial A r) :
    MvPolynomial.map f (initialJetSeparantOver center Q) =
      initialJetSeparantOver (f center) (MvPolynomial.map f Q) := by
  simp only [initialJetSeparantOver, aeval_def, algebraMap_eq, map_eval₂]
  simp only [separant, ← pderiv_map]
  congr 1
  funext i
  cases i <;> simp

/-- Universal Hasse jets commute with coefficient specialization. -/
theorem map_universalTaylorJet (f : A →+* B) (K j : ℕ) :
    MvPolynomial.map f (universalTaylorJet (F := A) K j) =
      universalTaylorJet (F := B) K j := by
  classical
  simp [universalTaylorJet]

/-- The universal residual commutes with coefficient specialization. -/
theorem map_universalTaylorResidual (f : A →+* B) (K : ℕ) (center : A)
    (Q : DifferentialPolynomial A r) :
    MvPolynomial.map f (universalTaylorResidual K center Q) =
      universalTaylorResidual K (f center) (MvPolynomial.map f Q) := by
  simp only [universalTaylorResidual, aeval_def, algebraMap_eq, map_eval₂]
  congr 1
  funext i
  cases i <;> simp [map_universalTaylorJet]

/-- Every extracted residual coefficient commutes with coefficient specialization. -/
theorem map_universalTaylorResidual_coeff (f : A →+* B) (K : ℕ) (center : A)
    (Q : DifferentialPolynomial A r) (h : ℕ) :
    MvPolynomial.map f
        ((optionEquivLeft A (Fin K) (universalTaylorResidual K center Q)).coeff h) =
      (optionEquivLeft B (Fin K)
        (universalTaylorResidual K (f center) (MvPolynomial.map f Q))).coeff h := by
  rw [← Polynomial.coeff_map, map_optionEquivLeft, map_universalTaylorResidual]

variable [Algebra F A]

/-- Literal Taylor numerators over an algebra, using inverses only in the base field. -/
def rationalTaylorNumeratorOver (center : A) (Q : DifferentialPolynomial A r)
    (l : ℕ) : MvPolynomial (Fin (r + 1)) A :=
  if hl : l < r + 1 then X ⟨l, hl⟩ else
    -C (algebraMap F A ((l.choose r : F)⁻¹)) *
      clearedSubstitution C (initialJetSeparantOver center Q)
        (fun i : Fin l ↦ rationalTaylorNumeratorOver center Q i.val)
        (fun i ↦ 2 * (i.val - r) - 1) (2 * (l - r) - 2)
        ((optionEquivLeft A (Fin l) (universalTaylorResidual l center Q)).coeff (l - r))
termination_by l

/-- Taylor numerators commute with algebra maps without regularity assumptions. -/
theorem map_rationalTaylorNumeratorOver [Algebra F B] (φ : A →ₐ[F] B)
    (center : A) (Q : DifferentialPolynomial A r) (l : ℕ) :
    MvPolynomial.map φ.toRingHom (rationalTaylorNumeratorOver (F := F) center Q l) =
      rationalTaylorNumeratorOver (F := F) (φ center)
        (MvPolynomial.map φ.toRingHom Q) l := by
  change MvPolynomial.map φ.toRingHom
      (rationalTaylorNumeratorOver (F := F) center Q l) =
    rationalTaylorNumeratorOver (F := F) (φ.toRingHom center)
      (MvPolynomial.map φ.toRingHom Q) l
  induction l using Nat.strong_induction_on with
  | h l ih =>
    rw [rationalTaylorNumeratorOver, rationalTaylorNumeratorOver]
    split_ifs with hl
    · simp
    · rw [map_mul, map_neg, map_C, ringHom_clearedSubstitution]
      have hscalar : φ.toRingHom (algebraMap F A ((l.choose r : F)⁻¹)) =
          algebraMap F B ((l.choose r : F)⁻¹) := φ.commutes _
      rw [hscalar]
      rw [map_initialJetSeparantOver,
        ← map_universalTaylorResidual_coeff φ.toRingHom l center Q (l - r)]
      rw [clearedSubstitution_map]
      have hC : (MvPolynomial.map (σ := Fin (r + 1)) φ.toRingHom).comp C =
          C.comp φ.toRingHom := by
        ext a
        simp
      rw [hC]
      congr 2
      funext i
      exact ih i.val i.isLt

/-- Over a field extension the scalar inverse agrees with the inverse in that field. -/
theorem rationalTaylorNumeratorOver_eq {E : Type*} [Field E] [Algebra F E]
    (center : E) (Q : DifferentialPolynomial E r)
    (l : ℕ) :
    rationalTaylorNumeratorOver (F := F) center Q l = rationalTaylorNumerator center Q l := by
  induction l using Nat.strong_induction_on with
  | h l ih =>
    rw [rationalTaylorNumeratorOver, rationalTaylorNumerator]
    split_ifs with hl
    · rfl
    · simp only [map_inv₀, map_natCast]
      congr 2
      funext i
      exact ih i.val i.isLt

/-- A common separant-power numerator with its coefficient algebra retained. The optional
exponent defaults to the coarse arbitrary-order value `2K`; reconstruction theorems require
it to satisfy `TaylorExponentSufficient`. -/
def commonTaylorNumeratorOver (center : A) (Q : DifferentialPolynomial A r) (K : ℕ)
    (l : Fin K) (τ : ℕ := 2 * K) : MvPolynomial (Fin (r + 1)) A :=
  rationalTaylorNumeratorOver (F := F) center Q l.val *
    initialJetSeparantOver center Q ^ (τ - (2 * (l.val - r) - 1))

/-- Common numerators commute with coefficient-algebra specialization. -/
theorem map_commonTaylorNumeratorOver [Algebra F B] (φ : A →ₐ[F] B)
    (center : A) (Q : DifferentialPolynomial A r) (K : ℕ) (l : Fin K)
    (τ : ℕ := 2 * K) :
    MvPolynomial.map φ.toRingHom
        (commonTaylorNumeratorOver (F := F) center Q K l (τ := τ)) =
      commonTaylorNumeratorOver (F := F) (φ center)
        (MvPolynomial.map φ.toRingHom Q) K l (τ := τ) := by
  simp only [commonTaylorNumeratorOver, map_mul, map_pow,
    map_rationalTaylorNumeratorOver, map_initialJetSeparantOver]
  rfl

end

end ReedSolomon.HiddenDerivative

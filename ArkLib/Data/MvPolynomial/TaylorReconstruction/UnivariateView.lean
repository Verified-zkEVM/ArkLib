/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.ToCompPoly.Multivariate.Eval
public import ArkLib.ToCompPoly.Univariate.Basic
public import CompPoly.Multivariate.Rename

/-!
# The last-variable univariate view of stored multivariate polynomials

Variables remain ordered `[t₀, …, tᵣ₋₁, z]`: the last coordinate becomes the univariate
variable, and the others remain coefficient variables. Both conversions execute stored
polynomial evaluation. Semantic equivalences occur only in proofs.
-/

@[expose] public section

namespace CPoly.TaylorReconstruction

open CompPoly

variable {E : Type*} [CommRing E] [DecidableEq E] [BEq E] [LawfulBEq E] [Nontrivial E] {r : ℕ}

/-- Stored coefficient polynomials over a nontrivial ring remain nontrivial. -/
instance coefficientNontrivial : Nontrivial (CMvPolynomial r E) :=
  (polyRingEquiv (n := r) (R := E)).toEquiv.nontrivial

/-- Executable embedding of scalars into the stored coefficient polynomial ring. -/
def coefficientConstant : E →+* CMvPolynomial r E where
  toFun := CMvPolynomial.C
  map_one' := by
    apply eq_iff_fromCMvPolynomial.mpr
    simp [CMvPolynomial.fromCMvPolynomial_C, CPoly.map_one]
  map_zero' := by
    apply eq_iff_fromCMvPolynomial.mpr
    simp [CMvPolynomial.fromCMvPolynomial_C, CPoly.map_zero]
  map_add' a b := by
    apply eq_iff_fromCMvPolynomial.mpr
    simp [CMvPolynomial.fromCMvPolynomial_C, CPoly.map_add]
  map_mul' a b := by
    apply eq_iff_fromCMvPolynomial.mpr
    simp [CMvPolynomial.fromCMvPolynomial_C, CPoly.map_mul]

/-- Include the free coefficient variables before the final variable. -/
def coefficientRename : CMvPolynomial r E →+* CMvPolynomial (r + 1) E where
  toFun := CMvPolynomial.rename Fin.castSucc
  map_one' := by
    apply eq_iff_fromCMvPolynomial.mpr
    simp [fromCMvPolynomial_rename, CPoly.map_one]
  map_zero' := by
    apply eq_iff_fromCMvPolynomial.mpr
    simp [fromCMvPolynomial_rename, CPoly.map_zero]
  map_add' := rename_add Fin.castSucc
  map_mul' := rename_mul Fin.castSucc

/-- Split the final variable into an actual stored univariate polynomial. -/
def splitLast : CMvPolynomial (r + 1) E →+* CPolynomial (CMvPolynomial r E) :=
  CMvPolynomial.eval₂Hom (CPolynomial.CHom.comp coefficientConstant)
    (Fin.lastCases CPolynomial.X (fun i => CPolynomial.C (CMvPolynomial.X i)))

/-- Flatten by renaming coefficient variables and evaluating at the last stored variable. -/
def flattenLast : CPolynomial (CMvPolynomial r E) →+* CMvPolynomial (r + 1) E where
  toFun := CPolynomial.eval₂ coefficientRename (CMvPolynomial.X (Fin.last r))
  map_one' := by
    rw [CPolynomial.eval₂_toPoly, CPolynomial.toPoly_one, Polynomial.eval₂_one]
  map_zero' := by
    rw [CPolynomial.eval₂_toPoly, CPolynomial.toPoly_zero, Polynomial.eval₂_zero]
  map_add' p q := by
    simp only [CPolynomial.eval₂_toPoly, CPolynomial.toPoly_add, Polynomial.eval₂_add]
  map_mul' p q := by
    simp only [CPolynomial.eval₂_toPoly, CPolynomial.toPoly_mul, Polynomial.eval₂_mul]

/-- Splitting preserves scalar coefficients as nested constants. -/
@[simp] theorem splitLast_C (a : E) :
    splitLast (CMvPolynomial.C a : CMvPolynomial (r + 1) E) =
      CPolynomial.C (CMvPolynomial.C a : CMvPolynomial r E) := by
  simp [splitLast, CMvPolynomial.eval₂Hom_apply, eval₂_equiv,
    CMvPolynomial.fromCMvPolynomial_C, coefficientConstant]

/-- A free coordinate becomes a constant coefficient polynomial. -/
@[simp] theorem splitLast_X_castSucc (i : Fin r) :
    splitLast (CMvPolynomial.X i.castSucc : CMvPolynomial (r + 1) E) =
      CPolynomial.C (CMvPolynomial.X i) := by
  simp [splitLast, CMvPolynomial.eval₂Hom_apply, eval₂_equiv,
    CMvPolynomial.fromCMvPolynomial_X]

/-- The last coordinate becomes the univariate variable. -/
@[simp] theorem splitLast_X_last :
    splitLast (CMvPolynomial.X (Fin.last r) : CMvPolynomial (r + 1) E) = CPolynomial.X := by
  simp [splitLast, CMvPolynomial.eval₂Hom_apply, eval₂_equiv,
    CMvPolynomial.fromCMvPolynomial_X]

/-- Flattening a constant embeds its free variables into the flat polynomial. -/
@[simp] theorem flattenLast_C (p : CMvPolynomial r E) :
    flattenLast (CPolynomial.C p) = CMvPolynomial.rename Fin.castSucc p := by
  simp [flattenLast, CPolynomial.eval₂_toPoly, CPolynomial.C_toPoly, coefficientRename]

/-- Flattening sends the univariate variable to the final flat variable. -/
@[simp] theorem flattenLast_X :
    flattenLast (CPolynomial.X : CPolynomial (CMvPolynomial r E)) =
      CMvPolynomial.X (Fin.last r) := by
  simp [flattenLast, CPolynomial.eval₂_toPoly, CPolynomial.X_toPoly]

omit [DecidableEq E] [Nontrivial E] in
private theorem storedMv_hom_ext {A : Type*} [CommSemiring A] {n : ℕ}
    (f g : CMvPolynomial n E →+* A)
    (hC : ∀ a, f (CMvPolynomial.C a) = g (CMvPolynomial.C a))
    (hX : ∀ i, f (CMvPolynomial.X i) = g (CMvPolynomial.X i)) : f = g := by
  have hc (a : E) : polyRingEquiv.symm (MvPolynomial.C a) =
      (CMvPolynomial.C a : CMvPolynomial n E) := by
    apply polyRingEquiv.injective
    rw [RingEquiv.apply_symm_apply]
    exact (CMvPolynomial.fromCMvPolynomial_C a).symm
  have hx (i : Fin n) : polyRingEquiv.symm (MvPolynomial.X i) =
      (CMvPolynomial.X i : CMvPolynomial n E) := by
    apply polyRingEquiv.injective
    rw [RingEquiv.apply_symm_apply]
    exact (CMvPolynomial.fromCMvPolynomial_X i).symm
  have h : f.comp polyRingEquiv.symm.toRingHom = g.comp polyRingEquiv.symm.toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simpa [hc] using hC a
    · intro i
      simpa [hx] using hX i
  ext p
  simpa using RingHom.congr_fun h (polyRingEquiv p)

/-- Splitting a renamed coefficient recovers its constant univariate representation. -/
@[simp] theorem splitLast_rename (p : CMvPolynomial r E) :
    splitLast (CMvPolynomial.rename Fin.castSucc p) = CPolynomial.C p := by
  have h : (splitLast (r := r) (E := E)).comp coefficientRename = CPolynomial.CHom := by
    apply storedMv_hom_ext
    · intro a
      simp [coefficientRename, rename_C]
    · intro i
      simp [coefficientRename, rename_X]
  exact RingHom.congr_fun h p

/-- Exact stored-polynomial roundtrip, not merely equality on finite-field points. -/
@[simp] theorem flattenLast_splitLast (p : CMvPolynomial (r + 1) E) :
    flattenLast (splitLast p) = p := by
  have h : (flattenLast (r := r) (E := E)).comp splitLast = RingHom.id _ := by
    apply storedMv_hom_ext
    · intro a
      simp [rename_C]
    · intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp
      · simp [rename_X]
  exact RingHom.congr_fun h p

/-- Exact roundtrip from the univariate coefficient representation. -/
@[simp] theorem splitLast_flattenLast (p : CPolynomial (CMvPolynomial r E)) :
    splitLast (flattenLast p) = p := by
  induction p using CPolynomial.induction_on with
  | h0 => simp
  | hC a => simp
  | hadd p q hp hq => simp [hp, hq]
  | hX p hp => simp [hp]

/-- Splitting refines semantic polynomial substitution with the last variable distinguished. -/
theorem splitLast_toPoly (p : CMvPolynomial (r + 1) E) :
    (splitLast p).toPoly =
      MvPolynomial.eval₂ (Polynomial.C.comp coefficientConstant)
        (Fin.lastCases Polynomial.X (fun i : Fin r => Polynomial.C (CMvPolynomial.X i)))
        (fromCMvPolynomial p) := by
  rw [← CPolynomial.toPolyRingHom_apply]
  change CPolynomial.toPolyRingHom (R := CMvPolynomial r E)
    (CMvPolynomial.eval₂ (CPolynomial.CHom.comp coefficientConstant)
      (Fin.lastCases CPolynomial.X (fun i => CPolynomial.C (CMvPolynomial.X i))) p) = _
  rw [eval₂_equiv, MvPolynomial.eval₂_comp_left]
  congr 1
  · apply RingHom.ext
    intro a
    simp [coefficientConstant, CPolynomial.C_toPoly]
  · funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp [CPolynomial.X_toPoly]
    · simp [CPolynomial.C_toPoly]

/-- Flattening refines semantic univariate evaluation with coefficient-variable renaming. -/
theorem flattenLast_semantics (p : CPolynomial (CMvPolynomial r E)) :
    fromCMvPolynomial (flattenLast p) =
      p.toPoly.eval₂
        ((MvPolynomial.rename Fin.castSucc).toRingHom.comp polyRingEquiv.toRingHom)
        (MvPolynomial.X (Fin.last r)) := by
  change (polyRingEquiv (n := r + 1) (R := E)).toRingHom
    (CPolynomial.eval₂ coefficientRename (CMvPolynomial.X (Fin.last r)) p) = _
  rw [CPolynomial.eval₂_toPoly, Polynomial.hom_eval₂]
  congr 1
  · apply RingHom.ext
    intro q
    exact fromCMvPolynomial_rename Fin.castSucc q
  · exact CMvPolynomial.fromCMvPolynomial_X (Fin.last r)

end CPoly.TaylorReconstruction

/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.MvPolynomial.TaylorReconstruction.AffineShift
public import ArkLib.Data.MvPolynomial.TaylorReconstruction.UnivariateView
public import ArkLib.Data.MvPolynomial.BoxAlgebraNilpotence
public import ArkLib.Data.Polynomial.ConfluentAlgebra.MonicArithmetic

/-!
# Construct the local monic equation from a flat chart polynomial

The final variable is kept as the quotient variable. Free coefficient variables are
translated by the supplied sample and reduced into the parameter box. This is the
stored bridge from the global chart representation to the nonreduced local algebra.
-/

@[expose] public section

namespace CPoly.TaylorReconstruction

open CompPoly ArkLib.ConfluentAlgebra

variable {E : Type*} [CommRing E] [DecidableEq E] [BEq E] [LawfulBEq E] [Nontrivial E]
variable {r : ℕ}

/-- Affine parameter translation as an executable ring homomorphism. -/
def shiftHom (a : Fin r → E) : CMvPolynomial r E →+* CMvPolynomial r E where
  toFun := shift a
  map_one' := by
    apply eq_iff_fromCMvPolynomial.mpr
    rw [shift_semantics, CPoly.map_one, MvPolynomial.eval₂_one]
  map_zero' := by
    exact shift_C a (0 : E)
  map_add' := shift_add a
  map_mul' := shift_mul a

/-- Translate parameters and project into the canonical coordinatewise box. -/
def parameterHom (N : ℕ) (a : Fin r → E) : CMvPolynomial r E →+* BoxAlgebra.Carrier r N E :=
  BoxAlgebra.projection.comp (shiftHom a)

/-- Execute the coefficient shift of the chart equation while retaining the final variable. -/
def localEquation (N : ℕ) (a : Fin r → E) (p : CMvPolynomial (r + 1) E) :
    CPolynomial (BoxAlgebra.Carrier r N E) :=
  mapCoefficients (parameterHom N a) (splitLast p)

/-- Monicity is preserved by the actual shift into the box; no separability is needed. -/
theorem localEquation_monic (N : ℕ) (a : Fin r → E) (p : CMvPolynomial (r + 1) E)
    (h : (splitLast p).monic) : (localEquation N a p).monic :=
  monic_mapCoefficients (parameterHom N a) (splitLast p) h

omit [DecidableEq E] [Nontrivial E] in
/-- Zero-parameter specialization of the local coefficient map is evaluation at the sample. -/
theorem constantSpecialization_parameterHom (N : ℕ) (hN : 0 < N) (a : Fin r → E)
    (p : CMvPolynomial r E) :
    BoxAlgebra.constantSpecialization hN (parameterHom N a p) = CMvPolynomial.eval a p := by
  change MvPolynomial.coeff 0
    (fromCMvPolynomial (BoxTruncation.truncate N (shift a p))) = _
  rw [BoxTruncation.coeff_semantics, if_pos (by simpa using fun _ : Fin r => hN)]
  rw [shift_semantics, eval_equiv]
  change MvPolynomial.constantCoeff
    (MvPolynomial.eval₂ MvPolynomial.C (fun i => MvPolynomial.X i + MvPolynomial.C (a i))
      (fromCMvPolynomial p)) = _
  rw [MvPolynomial.eval₂_comp_left]
  simp only [MvPolynomial.constantCoeff_comp_C, MvPolynomial.eval₂_id]
  congr 2
  funext i
  simp

/-- Execute the original chart equation's fiber at the supplied free-parameter sample. -/
def constantFiber (a : Fin r → E) (p : CMvPolynomial (r + 1) E) : CPolynomial E :=
  mapCoefficients (CMvPolynomial.eval₂Hom (RingHom.id E) a) (splitLast p)

/-- Specializing the computed local equation recovers its original sample fiber exactly. -/
theorem localEquation_constantFiber (N : ℕ) (hN : 0 < N) (a : Fin r → E)
    (p : CMvPolynomial (r + 1) E) :
    mapCoefficients (BoxAlgebra.constantSpecialization hN) (localEquation N a p) =
      constantFiber a p := by
  apply CPolynomial.toPoly_injective
  rw [toPoly_mapCoefficients, localEquation, toPoly_mapCoefficients, Polynomial.map_map,
    constantFiber, toPoly_mapCoefficients]
  congr 1
  apply RingHom.ext
  intro q
  exact constantSpecialization_parameterHom N hN a q

end CPoly.TaylorReconstruction

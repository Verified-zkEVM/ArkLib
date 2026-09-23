/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.Polynomial.Differential.FrobeniusEquation
import ArkLib.ToMathlib.MvPolynomial.PDeriv
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.ComputeDegree

/-!
# Acceptance tests for Frobenius contraction of ordinary equations

These examples check the coordinate order in the flattening, compute a specialized polynomial
after expansion, exercise coefficient-height transport, and show why the positive root-degree
hypothesis is needed for a nonzero root derivative.
-/

open MvPolynomial Polynomial PolynomialDifferential

section Flattening

example (n : ℕ) (a : ℚ) :
    ordinaryFlatten ℚ
        (MvPolynomial.C (Polynomial.monomial n a) : DifferentialPolynomial ℚ[X] 0) =
      MvPolynomial.C a * MvPolynomial.X (some 1) ^ n := by
  exact ordinaryFlatten_C_monomial n a

example :
    MvPolynomial.eval
        (fun o : Option (Fin 2) => o.elim 2 (fun i => Fin.cases 3 (fun _ => 5) i))
        (ordinaryFlatten ℚ
          (MvPolynomial.X (some 0) + MvPolynomial.C Polynomial.X :
            DifferentialPolynomial ℚ[X] 0)) = 7 := by
  have hflat : ordinaryFlatten ℚ
      (MvPolynomial.X (some 0) + MvPolynomial.C Polynomial.X :
        DifferentialPolynomial ℚ[X] 0) =
      MvPolynomial.X none + MvPolynomial.X (some 1) := by
    simp
  have hcase : Fin.cases (3 : ℚ) (fun _ : Fin 1 => (5 : ℚ)) (1 : Fin 2) = (5 : ℚ) := by
    rw [show (1 : Fin 2) = Fin.succ 0 by norm_num, Fin.cases_succ]
  rw [hflat]
  simp [hcase]
  norm_num

example (z : ℚ) :
    Polynomial.expand ℚ 2
        (differentialSpecialization
          (MvPolynomial.map (Polynomial.evalRingHom z)
            (MvPolynomial.X (some 0) + MvPolynomial.C Polynomial.X :
              DifferentialPolynomial ℚ[X] 0))
          Polynomial.X) = Polynomial.X ^ 2 + Polynomial.C z := by
  let Q : DifferentialPolynomial ℚ[X] 0 :=
    MvPolynomial.X (some 0) + MvPolynomial.C Polynomial.X
  have hflat : ordinaryFlatten ℚ Q =
      MvPolynomial.X none + MvPolynomial.X (some 1) := by
    simp [Q]
  change Polynomial.expand ℚ 2
      (differentialSpecialization
        (MvPolynomial.map (Polynomial.evalRingHom z) Q) Polynomial.X) = _
  rw [expand_differentialSpecialization_map_eq_eval₂_flatten]
  rw [hflat]
  have hcase :
      Fin.cases (Polynomial.X ^ 2 : ℚ[X]) (fun _ : Fin 1 => Polynomial.C z)
        (1 : Fin 2) = Polynomial.C z := by
    rw [show (1 : Fin 2) = Fin.succ 0 by norm_num, Fin.cases_succ]
  simp [MvPolynomial.eval₂_add, MvPolynomial.eval₂_X, hcase]

example :
    ¬ MvPolynomial.CoeffNatDegreeLE
      (ordinaryUnflatten ℚ
        (MvPolynomial.X (some 1) ^ 2 : MvPolynomial (Option (Fin 2)) ℚ)) 1 := by
  intro h
  have hgen : ordinaryUnflatten ℚ
      (MvPolynomial.X (some 1) : MvPolynomial (Option (Fin 2)) ℚ) =
      (MvPolynomial.C Polynomial.X : DifferentialPolynomial ℚ[X] 0) := by
    apply (ordinaryFlatten ℚ).injective
    simp [ordinaryUnflatten]
  have hpow : ordinaryUnflatten ℚ
      (MvPolynomial.X (some 1) ^ 2 : MvPolynomial (Option (Fin 2)) ℚ) =
      (MvPolynomial.C (Polynomial.X ^ 2) : DifferentialPolynomial ℚ[X] 0) := by
    calc
      _ = ordinaryUnflatten ℚ (MvPolynomial.X (some 1)) ^ 2 := by simp
      _ = (MvPolynomial.C Polynomial.X : DifferentialPolynomial ℚ[X] 0) ^ 2 := by
        rw [hgen]
      _ = _ := by rw [← MvPolynomial.C_pow]
  rw [hpow] at h
  have hcoeff := h (0 : JetVariable 0 →₀ ℕ)
  rw [MvPolynomial.coeff_C] at hcoeff
  norm_num [Polynomial.natDegree_X_pow] at hcoeff

end Flattening

section RootDegreeBoundary

variable {E : Type*} [Field E]

/-- If the input has root degree zero, the degree identity cannot produce a nonzero root
derivative. This is the boundary excluded by the positive-degree hypothesis. -/
example (p e : ℕ) [ExpChar E p] (H : DifferentialPolynomial E[X] 0)
    (hder : MvPolynomial.pderiv (some 0) H ≠ 0)
    (hdegree : H.degreeOf (some 0) * (p ^ e) = 0) : False := by
  have hpos : 0 < H.degreeOf (some 0) := by
    have hne : H.degreeOf (some 0) ≠ 0 := by
      intro hzero
      exact hder (MvPolynomial.pderiv_eq_zero_of_degreeOf_eq_zero hzero)
    omega
  have hp : 0 < p := expChar_pos E p
  have hpow : 0 < p ^ e := pow_pos hp _
  exact (Nat.ne_of_gt (Nat.mul_pos hpos hpow)) hdegree

end RootDegreeBoundary

section NonconstantChallenge

variable {E : Type*} [Field E]

/-- The equation `Y + W` retains its symbolic challenge under Frobenius contraction. -/
example (p : ℕ) [ExpChar E p] [PerfectField E] :
    ∃ e : ℕ, ∃ H : DifferentialPolynomial E[X] 0,
      Irreducible H ∧
      MvPolynomial.pderiv (some 0) H ≠ 0 ∧
      H.degreeOf (some 0) * (p ^ e) = 1 ∧
      H.degreeOf none = 0 ∧
      MvPolynomial.CoeffNatDegreeLE H 1 ∧
      ∀ (P : E[X]) (w : E),
        differentialSpecialization
            (MvPolynomial.map (Polynomial.evalRingHom (w ^ (p ^ e)))
              (MvPolynomial.X (some 0) + MvPolynomial.C Polynomial.X :
                DifferentialPolynomial E[X] 0)) P = 0 →
          differentialSpecialization
            (MvPolynomial.map (Polynomial.evalRingHom w) H)
              (Polynomial.expand E (p ^ e) P) = 0 := by
  let Q : DifferentialPolynomial E[X] 0 :=
    MvPolynomial.X (some 0) + MvPolynomial.C Polynomial.X
  have hflat : ordinaryFlatten E Q =
      MvPolynomial.X none + MvPolynomial.X (some 1) := by
    simp only [Q, map_add, ordinaryFlatten_Y, ordinaryFlatten_coeff_X]
  have hpoly :
      optionEquivLeft E (Fin 2) (ordinaryFlatten E Q) =
        Polynomial.X + Polynomial.C (MvPolynomial.X 1) := by
    simp only [hflat, map_add, optionEquivLeft_X_none, optionEquivLeft_X_some]
  have hpolyirr : Irreducible
      (Polynomial.X + Polynomial.C (MvPolynomial.X 1) :
        Polynomial (MvPolynomial (Fin 2) E)) := by
    simpa only [map_neg, sub_neg_eq_add] using
      Polynomial.irreducible_X_sub_C
        (-(MvPolynomial.X 1 : MvPolynomial (Fin 2) E))
  have hflatirr : Irreducible (ordinaryFlatten E Q) := by
    have hi := hpolyirr.map (optionEquivLeft E (Fin 2)).symm
    rw [← hpoly] at hi
    simpa only [AlgEquiv.symm_apply_apply] using hi
  have hQirr : Irreducible Q := by
    simpa only [Q, ordinaryUnflatten, AlgEquiv.symm_apply_apply] using
      hflatirr.map (ordinaryUnflatten E)
  have hQdegree : Q.degreeOf (some 0) = 1 := by
    rw [← degreeOf_none_ordinaryFlatten, ← natDegree_optionEquivLeft, hflat]
    simp
  have hQindependent : Q.degreeOf none = 0 := by
    apply Nat.eq_zero_of_le_zero
    exact (MvPolynomial.degreeOf_add_le none
      (MvPolynomial.X (some 0) : DifferentialPolynomial E[X] 0)
      (MvPolynomial.C Polynomial.X)).trans (by
        apply max_le
        · exact (MvPolynomial.degreeOf_X_of_ne (by simp)).le
        · exact (MvPolynomial.degreeOf_C _ _).le)
  have hQheight : MvPolynomial.CoeffNatDegreeLE Q 1 := by
    have hX := MvPolynomial.coeffNatDegreeLE_X (R := E) (σ := JetVariable 0) (some 0)
    have hC := MvPolynomial.coeffNatDegreeLE_C (R := E) (σ := JetVariable 0)
      (p := (Polynomial.X : Polynomial E)) (h := 1) (by
        rw [Polynomial.natDegree_X])
    simpa only [Q] using
      (MvPolynomial.CoeffNatDegreeLE.add (hX.mono (by omega)) hC)
  obtain ⟨e, H, hHirr, hHder, hHdegree, hHindependent, hHheight, htransport⟩ :=
    exists_frobeniusEquation p (Q := Q) (by omega) hQirr hQheight
  refine ⟨e, H, hHirr, hHder, hHdegree.trans hQdegree,
    Nat.eq_zero_of_le_zero (hHindependent.trans_eq hQindependent),
    hHheight, ?_⟩
  simpa only [Q] using htransport

end NonconstantChallenge

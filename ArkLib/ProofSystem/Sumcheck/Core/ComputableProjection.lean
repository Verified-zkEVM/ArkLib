/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.ProofSystem.Sumcheck.Core.Domain
public import ArkLib.ProofSystem.Sumcheck.Impl.Representation
public import CompPoly.Multivariate.FinSuccEquiv
public import CompPoly.Multivariate.Eval
public import CompPoly.Univariate.ToPoly.RingHom

/-! # Computable honest projections over indexed domains -/

@[expose] public section

namespace Sumcheck.Core.Computable
open CPoly CompPoly Finset Polynomial MvPolynomial
open CPoly.CMvPolynomial
variable {R : Type} [CommSemiring R] [BEq R] [LawfulBEq R] [Nontrivial R]
  {n d deg : ℕ}

/-- The mathematical interpretation retains every individual degree bound. -/
def toPolynomial (poly : CMvPolynomial n R) (hpoly : ∀ j, poly.degreeOf j ≤ deg) :
    R⦃≤ deg⦄[X Fin n] :=
  ⟨CPoly.fromCMvPolynomial poly, by
    apply (MvPolynomial.mem_restrictDegree (Fin n) _ deg).mpr
    intro mon hmon j
    apply MvPolynomial.degreeOf_le_iff.mp _ mon hmon
    rw [← congrFun (CPoly.degreeOf_equiv (S := R) (p := poly)) j]
    exact hpoly j⟩

/-- Compute the honest projection by enumerating suffix indices, including repeated points. -/
def projectedPolynomial (D : Fin d → R) (i : Fin (n + 1))
    (c : Fin i.castSucc → R) (poly : CMvPolynomial (n + 1) R) : CPolynomial R :=
  ∑ x : Fin (n - i) → Fin d,
    CPolynomial.mapRingHom (evalHom (roundSuffix i c (D ∘ x))) (finSuccEquivNth i poly)

/-- Computational projection interprets to the native indexed polynomial. -/
theorem projectedPolynomial_toPoly (D : Fin d → R) (i : Fin (n + 1))
    (c : Fin i.castSucc → R) (poly : CMvPolynomial (n + 1) R)
    (hpoly : ∀ j, poly.degreeOf j ≤ deg) :
    (projectedPolynomial D i c poly).toPoly =
      (projectedRoundPolynomial D i c (toPolynomial poly hpoly)).val := by
  classical
  have heval (v : Fin n → R) : evalHom v =
      (MvPolynomial.eval v).comp (CPoly.polyRingEquiv (n := n) (R := R)).toRingHom := by
    ext p
    simp [eval_equiv, CPoly.coe_polyRingEquiv]
  unfold projectedPolynomial projectedRoundPolynomial
  rw [CPolynomial.toPoly_sum]
  apply Finset.sum_congr rfl
  intro x _
  rw [CPolynomial.toPoly_mapRingHom, heval, ← Polynomial.map_map]
  rw [CPoly.CMvPolynomial.finSuccEquivNth_apply, map_polyRingEquiv_toPoly_finSuccEquivNth]
  rfl

/-- The computed honest message has the required global degree cap. -/
theorem projectedPolynomial_degree_le (D : Fin d → R) (i : Fin (n + 1))
    (c : Fin i.castSucc → R) (poly : CMvPolynomial (n + 1) R)
    (hpoly : ∀ j, poly.degreeOf j ≤ deg) :
    (projectedPolynomial D i c poly).degree ≤ (deg : WithBot ℕ) := by
  rw [CPolynomial.degree_toPoly, projectedPolynomial_toPoly D i c poly hpoly]
  exact Polynomial.mem_degreeLE.mp (projectedRoundPolynomial D i c
    (toPolynomial poly hpoly)).property

/-- Package the actual coefficient array as a bounded message. -/
def projectedMessage (D : Fin d → R) : {n : ℕ} → (i : Fin n) →
    (Fin i.castSucc → R) → (poly : CMvPolynomial n R) →
    (∀ j, poly.degreeOf j ≤ deg) → Impl.Representation.Message R deg
  | 0, i, _, _, _ => i.elim0
  | _ + 1, i, c, poly, hpoly =>
    ⟨projectedPolynomial D i c poly, projectedPolynomial_degree_le D i c poly hpoly⟩

/-- Interpreting the computed array gives exactly the indexed honest message. -/
theorem projectedMessage_toMessage (D : Fin d → R) (i : Fin n)
    (c : Fin i.castSucc → R) (poly : CMvPolynomial n R)
    (hpoly : ∀ j, poly.degreeOf j ≤ deg) :
    Impl.Representation.toMessage R deg (projectedMessage D i c poly hpoly) =
      projectedRoundPolynomial D i c (toPolynomial poly hpoly) := by
  cases n with
  | zero => exact i.elim0
  | succ n =>
    apply Subtype.ext
    rw [Impl.Representation.toMessage_val]
    exact projectedPolynomial_toPoly D i c poly hpoly

/-- Runtime Horner evaluation answers exactly the native honest projection. -/
theorem projectedMessage_evaluate (D : Fin d → R) (i : Fin n)
    (c : Fin i.castSucc → R) (poly : CMvPolynomial n R)
    (hpoly : ∀ j, poly.degreeOf j ≤ deg) (r : R) :
    Impl.Representation.evaluate R deg (projectedMessage D i c poly hpoly) r =
      (projectedRoundPolynomial D i c (toPolynomial poly hpoly)).val.eval r := by
  rw [Impl.Representation.evaluate_eq, projectedMessage_toMessage]

end Sumcheck.Core.Computable

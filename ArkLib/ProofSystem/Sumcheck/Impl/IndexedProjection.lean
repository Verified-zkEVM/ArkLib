/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.MvPolynomial.EvalExcept
public import ArkLib.ProofSystem.Sumcheck.Impl.Representation
public import CompPoly.Multivariate.FinSuccEquiv
public import CompPoly.Multivariate.Eval
public import CompPoly.Univariate.ToPoly.RingHom

/-!
# Computable honest round polynomials over indexed domains

`indexedRoundPolynomial D i c poly` computes the honest round-`i` message on CompPoly's carriers.
It splits the round variable, evaluates the coefficients at the challenge prefix `c` followed by
`D ∘ x`, and sums over every assignment `x` of suffix domain indices. A repeated point of `D`
contributes once for each index. The construction accepts arbitrary individual degree bounds and
arbitrary finite domains. It is a direct enumeration and makes no running-time claim.

This module owns the enumeration and the proofs that every client shares: interpretation as a sum
of restrictions, the degree bound and the bounded message. `projectedRoundPolynomial` in
`Sumcheck.Impl.Projection` specializes it to an injective domain and relates it to
`Sumcheck.Spec`. `Sumcheck.Core.Computable.indexedRoundPolynomial_toPoly` relates it to the
indexed projection of `Sumcheck.Core`. This module imports neither of those layers.
-/

@[expose] public section

open CPoly CompPoly Finset Polynomial MvPolynomial
open CPoly.CMvPolynomial

namespace Sumcheck.Impl.Computable

variable {R : Type} [CommSemiring R] [BEq R] [LawfulBEq R] [Nontrivial R]
  {n m deg : ℕ}

omit [Nontrivial R] in
/-- Transport coefficient evaluation to mathematical multivariate evaluation. -/
theorem evalHom_transport (v : Fin n → R) :
    evalHom v = (MvPolynomial.eval v).comp (CPoly.polyRingEquiv (n := n) (R := R)).toRingHom := by
  ext p
  simp [eval_equiv, CPoly.coe_polyRingEquiv]

/-- Each computational summand has precisely the polynomial interpretation used by the spec. -/
theorem projectedSummand_toPoly (i : Fin (n + 1)) (poly : CMvPolynomial (n + 1) R)
    (v : Fin n → R) :
    (CPolynomial.mapRingHom (evalHom v) (finSuccEquivNth i poly)).toPoly =
      Polynomial.map (MvPolynomial.eval v)
        (MvPolynomial.finSuccEquivNth R i (CPoly.fromCMvPolynomial poly)) := by
  rw [CPolynomial.toPoly_mapRingHom, evalHom_transport, ← Polynomial.map_map]
  rw [CPoly.CMvPolynomial.finSuccEquivNth_apply, map_polyRingEquiv_toPoly_finSuccEquivNth]

omit [Nontrivial R] in
/-- Interpretation commutes with a finite sum of computational messages. -/
theorem toPoly_sum {ι : Type*} (s : Finset ι) (f : ι → CPolynomial R) :
    (∑ x ∈ s, f x).toPoly = ∑ x ∈ s, (f x).toPoly := by
  classical
  exact CPolynomial.toPoly_sum

/-- Enumerate the honest round-`i` polynomial over the suffix domain indices. The point fixes the
first `i` coordinates to the challenges and the remaining `n - i` coordinates to `D ∘ x`. -/
def indexedRoundPolynomial (D : Fin m → R) (i : Fin (n + 1))
    (challenges : Fin i.castSucc → R) (poly : CMvPolynomial (n + 1) R) : CPolynomial R :=
  ∑ x : Fin (n - i) → Fin m,
    CPolynomial.mapRingHom
      (evalHom (Fin.append challenges (D ∘ x) ∘ Fin.cast (by have := i.isLt; simp; omega)))
      (finSuccEquivNth i poly)

/-- The enumeration interprets as the sum of the restrictions at every suffix index assignment. -/
theorem indexedRoundPolynomial_toPoly (D : Fin m → R) (i : Fin (n + 1))
    (challenges : Fin i.castSucc → R) (poly : CMvPolynomial (n + 1) R) :
    (indexedRoundPolynomial D i challenges poly).toPoly =
      ∑ x : Fin (n - i) → Fin m, (CPoly.fromCMvPolynomial poly).evalExcept i
        (Fin.append challenges (D ∘ x) ∘ Fin.cast (by have := i.isLt; simp; omega)) := by
  unfold indexedRoundPolynomial
  rw [toPoly_sum]
  simp_rw [projectedSummand_toPoly]
  rfl

/-- Individual degree bounds on the input bound the degree of each enumerated message. -/
theorem indexedRoundPolynomial_natDegree_le (D : Fin m → R) (i : Fin (n + 1))
    (challenges : Fin i.castSucc → R) (poly : CMvPolynomial (n + 1) R)
    (hpoly : ∀ j, poly.degreeOf j ≤ deg) :
    (indexedRoundPolynomial D i challenges poly).natDegree ≤ deg := by
  classical
  rw [CPolynomial.natDegree_toPoly, indexedRoundPolynomial_toPoly]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro x _
  exact (MvPolynomial.natDegree_evalExcept_le i _ _).trans
    ((congrFun (CPoly.degreeOf_equiv (S := R) (p := poly)) i).symm.le.trans (hpoly i))

/-- Individual degree bounds also bound the extended natural degree used by messages. -/
theorem indexedRoundPolynomial_degree_le (D : Fin m → R) (i : Fin (n + 1))
    (challenges : Fin i.castSucc → R) (poly : CMvPolynomial (n + 1) R)
    (hpoly : ∀ j, poly.degreeOf j ≤ deg) :
    (indexedRoundPolynomial D i challenges poly).degree ≤ (deg : WithBot ℕ) := by
  rw [CPolynomial.degree_toPoly]
  apply Polynomial.natDegree_le_iff_degree_le.mp
  rw [← CPolynomial.natDegree_toPoly]
  exact indexedRoundPolynomial_natDegree_le D i challenges poly hpoly

/-- Package the enumerated round polynomial as a degree-bounded coefficient array. -/
def indexedRoundMessage (D : Fin m → R) (i : Fin (n + 1))
    (challenges : Fin i.castSucc → R) (poly : CMvPolynomial (n + 1) R)
    (hpoly : ∀ j, poly.degreeOf j ≤ deg) : Representation.Message R deg :=
  ⟨indexedRoundPolynomial D i challenges poly,
    indexedRoundPolynomial_degree_le D i challenges poly hpoly⟩

/-- The round message for an arbitrary variable count. There is no round at zero variables, so
the empty case is eliminated by its impossible round index. -/
def indexedMessage (D : Fin m → R) {n : ℕ} (i : Fin n)
    (challenges : Fin i.castSucc → R) (poly : CMvPolynomial n R)
    (hpoly : ∀ j, poly.degreeOf j ≤ deg) : Representation.Message R deg :=
  match n, i, challenges, poly, hpoly with
  | 0, i, _, _, _ => i.elim0
  | _ + 1, i, challenges, poly, hpoly => indexedRoundMessage D i challenges poly hpoly

omit [Nontrivial R] in
/-- Interpret a computational polynomial with individual degree bound `deg` as a bounded
mathematical polynomial. -/
def toRestrictDegree (poly : CMvPolynomial n R) (hpoly : ∀ j, poly.degreeOf j ≤ deg) :
    R⦃≤ deg⦄[X Fin n] :=
  ⟨CPoly.fromCMvPolynomial poly, by
    apply (MvPolynomial.mem_restrictDegree (Fin n) _ deg).mpr
    intro mon hmon j
    apply MvPolynomial.degreeOf_le_iff.mp _ mon hmon
    rw [← congrFun (CPoly.degreeOf_equiv (S := R) (p := poly)) j]
    exact hpoly j⟩

end Sumcheck.Impl.Computable

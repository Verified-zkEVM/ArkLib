/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.TowerAlgebra.Inverse
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-! # Geometric separation of canonical tower elements -/

@[expose] public section

namespace ReedSolomon.ListDecoding.TowerRepresentation

open CompPoly Polynomial

/-- A squarefree polynomial divides any polynomial vanishing on all its geometric roots.
The argument descends irreducible factors, so the ground field need not be perfect. -/
theorem dvd_of_squarefree_geometric_vanishing
    {F K : Type*} [Field F] [Field K] [Algebra F K] [IsAlgClosed K]
    (g p : F[X]) (hg : Squarefree g)
    (hv : ∀ x : K, g.aeval x = 0 → p.aeval x = 0) : g ∣ p := by
  induction g using WfDvdMonoid.induction_on_irreducible with
  | zero => exact (hg.ne_zero rfl).elim
  | unit g hu => exact hu.dvd
  | mul g i _ hi ih =>
    have hg' : Squarefree g := hg.squarefree_of_dvd (dvd_mul_left _ _)
    have hiG : i ∣ p := by
      obtain ⟨x, hx⟩ := IsAlgClosed.exists_eval₂_eq_zero (algebraMap F K) i hi.degree_pos.ne'
      apply (hi.dvd_iff_aeval_eq_zero hx).mp
      apply hv x
      simp [hx, Polynomial.aeval_def]
    have hgP : g ∣ p := ih hg' (fun x hx => hv x (by simp [Polynomial.aeval_mul, hx]))
    exact (IsRelPrime.of_squarefree_mul hg).mul_dvd hiG hgP

/-- Degree-bounded representatives are separated by geometric roots of a squarefree modulus. -/
theorem eq_zero_of_degree_lt_of_geometric_vanishing
    {F K : Type*} [Field F] [Field K] [Algebra F K] [IsAlgClosed K]
    (g p : F[X]) (hg : g.Monic) (hsq : Squarefree g) (hd : p.degree < g.degree)
    (hv : ∀ x : K, g.aeval x = 0 → p.aeval x = 0) : p = 0 := by
  by_contra hp
  exact hg.not_dvd_of_degree_lt hp hd (dvd_of_squarefree_geometric_vanishing g p hsq hv)

variable {F : Type} [Field F] [BEq F] [LawfulBEq F]

/-- A canonical tower element vanishing at every geometric point is zero. -/
theorem eq_zero_of_geometric_vanishing
    (r : TowerRepresentation (F := F)) {width : ℕ} (hr : r.WellFormed width)
    {p : CPolynomial (CPolynomial F)} (hp : ElementReduced r.modulus r.fiber p)
    (hv : ∀ x y : AlgebraicClosure F,
      r.Point (algebraMap F (AlgebraicClosure F)) x y →
        evalNested p (algebraMap F (AlgebraicClosure F)) x y = 0) : p = 0 := by
  have hs : ∀ x : AlgebraicClosure F,
      r.modulus.toPoly.aeval x = 0 →
      FirstOrderNormDecoder.D5.specializeFiberCPolynomial p
        (algebraMap F (AlgebraicClosure F)) x = 0 := by
    intro x hx
    let phi := algebraMap F (AlgebraicClosure F)
    let fiber := FirstOrderNormDecoder.D5.specializeFiberCPolynomial r.fiber phi x
    let element := FirstOrderNormDecoder.D5.specializeFiberCPolynomial p phi x
    have hmon : r.fiber.toPoly.Monic := (CPolynomial.monic_toPoly_iff _).mp hr.2.2.2.1
    have hmon' : fiber.Monic := hmon.map _
    apply eq_zero_of_degree_lt_of_geometric_vanishing (K := AlgebraicClosure F)
      fiber element hmon' (hr.2.2.2.2.2.2.1 _ phi x hx)
    · change (p.toPoly.map _).degree < (r.fiber.toPoly.map _).degree
      rw [hmon.degree_map]
      exact Polynomial.degree_map_le.trans_lt hp.1
    · intro y hy
      exact hv x y ⟨hx, by simpa [fiber, phi, evalNested, Polynomial.aeval_def] using hy⟩
  apply CPolynomial.toPoly_injective
  apply Polynomial.ext
  intro i
  rw [CPolynomial.toPoly_zero, Polynomial.coeff_zero, ← CPolynomial.coeff_toPoly]
  apply CPolynomial.toPoly_injective
  rw [CPolynomial.toPoly_zero]
  apply eq_zero_of_degree_lt_of_geometric_vanishing (K := AlgebraicClosure F)
    r.modulus.toPoly (p.coeff i).toPoly ((CPolynomial.monic_toPoly_iff _).mp hr.1)
    hr.2.1 (hp.2 i)
  intro x hx
  have hc := congrArg (fun q => q.coeff i) (hs x hx)
  simpa [FirstOrderNormDecoder.D5.specializeFiberCPolynomial,
    ← CPolynomial.coeff_toPoly, FirstOrderNormDecoder.D5.coefficientEval_apply,
    Polynomial.aeval_def] using hc

/-- Subtracting canonical representatives preserves both degree bounds. -/
theorem elementReduced_sub {G : CPolynomial F} {h p q : CPolynomial (CPolynomial F)}
    (hp : ElementReduced G h p) (hq : ElementReduced G h q) :
    ElementReduced G h (p - q) := by
  constructor
  · rw [CPolynomial.toPoly_sub]
    exact (Polynomial.degree_sub_le _ _).trans_lt (max_lt hp.1 hq.1)
  · intro i
    rw [CPolynomial.coeff_sub, CPolynomial.toPoly_sub]
    exact (Polynomial.degree_sub_le _ _).trans_lt (max_lt (hp.2 i) (hq.2 i))

/-- Geometric nonvanishing makes reduced multiplication injective on the canonical slice. -/
theorem reduced_mul_injective_of_geometric_nonvanishing
    (r : TowerRepresentation (F := F)) {width : ℕ} (hr : r.WellFormed width)
    (u : CPolynomial (CPolynomial F))
    (hu : ∀ x y : AlgebraicClosure F,
      r.Point (algebraMap F (AlgebraicClosure F)) x y →
        evalNested u (algebraMap F (AlgebraicClosure F)) x y ≠ 0)
    {p q : CPolynomial (CPolynomial F)}
    (hp : ElementReduced r.modulus r.fiber p) (hq : ElementReduced r.modulus r.fiber q)
    (he : reduceElement r.modulus r.fiber (u * p) =
      reduceElement r.modulus r.fiber (u * q)) : p = q := by
  apply sub_eq_zero.mp
  apply eq_zero_of_geometric_vanishing r hr (elementReduced_sub hp hq)
  intro x y hxy
  have heval := congrArg (fun a => evalNested a (algebraMap F (AlgebraicClosure F)) x y) he
  rw [evalNested_reduceElement _ _ _ hr.1 hxy.1 hr.2.2.2.1 hxy.2,
    evalNested_reduceElement _ _ _ hr.1 hxy.1 hr.2.2.2.1 hxy.2] at heval
  have heval' : evalNested u (algebraMap F (AlgebraicClosure F)) x y *
      evalNested p (algebraMap F (AlgebraicClosure F)) x y =
      evalNested u (algebraMap F (AlgebraicClosure F)) x y *
      evalNested q (algebraMap F (AlgebraicClosure F)) x y := by
    simpa [evalNested, FirstOrderNormDecoder.D5.specializeFiberCPolynomial,
      CPolynomial.toPoly_mul] using heval
  have heq := mul_left_cancel₀ (hu x y hxy) heval'
  simpa [evalNested, FirstOrderNormDecoder.D5.specializeFiberCPolynomial,
    CPolynomial.toPoly_sub] using sub_eq_zero.mpr heq

end ReedSolomon.ListDecoding.TowerRepresentation

namespace ReedSolomon.ListDecoding.TowerAlgebra

open CompPoly

variable {F : Type} [Field F] [BEq F] [LawfulBEq F]

/-- Geometric nonvanishing guarantees success of the concrete inverse algorithm. -/
theorem inverseRepresentative?_exists_of_geometric_nonvanishing
    (r : TowerRepresentation (F := F)) {width : ℕ} (hr : r.WellFormed width)
    (u : CPolynomial (CPolynomial F))
    (hu : ∀ x y : AlgebraicClosure F,
      r.Point (algebraMap F (AlgebraicClosure F)) x y →
        TowerRepresentation.evalNested u (algebraMap F (AlgebraicClosure F)) x y ≠ 0) :
    ∃ v, inverseRepresentative? r.modulus r.fiber u = some v := by
  apply inverseRepresentative?_exists_of_det_ne_zero hr.1 hr.2.2.2.1 hr.2.2.2.2.1
  apply multiplicationMatrix_det_ne_zero_of_injective hr.1 hr.2.2.2.1
  exact TowerRepresentation.reduced_mul_injective_of_geometric_nonvanishing r hr u hu

end ReedSolomon.ListDecoding.TowerAlgebra

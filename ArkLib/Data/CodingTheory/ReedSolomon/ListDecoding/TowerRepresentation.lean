/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
  ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.FirstOrderNormDecoder.D5.SeparantTower
public import ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.FiniteRepresentation

/-!
# Canonical bounded-fiber tower representations

This file is the common runtime and semantic representation of the paper's finite algebras
`(F[U]/G)[V]/h`.  It stores only executable reduced polynomial data: the base modulus `G`, the
monic bounded fiber `h`, and the coefficients of the represented message in the tower basis.
Geometric roots and residue-field factorizations occur only in the predicates interpreting that
data.
-/

@[expose] public section

namespace ReedSolomon.ListDecoding

open CompPoly Polynomial Polynomial.JetHornerMachine

variable {F : Type*} [Field F] [BEq F] [LawfulBEq F]

/-- Executable coefficient data for `(F[U]/G)[V]/h`.  Every nested polynomial is represented in
ascending `V` coefficients by `CPolynomial`; `WellFormed` states the canonical reduction bounds. -/
structure TowerRepresentation where
  /-- The squarefree base modulus `G(U)`. -/
  modulus : CPolynomial F
  /-- The monic bounded fiber polynomial `h(U,V)`. -/
  fiber : CPolynomial (CPolynomial F)
  /-- The fixed-width message coefficients, each represented in the tower basis. -/
  coefficients : List (CPolynomial (CPolynomial F))

namespace TowerRepresentation

/-- Dimension of the represented quotient algebra over its coefficient field. -/
def dimension (r : TowerRepresentation (F := F)) : ℕ :=
  r.modulus.natDegree * r.fiber.natDegree

/-- Evaluate a nested polynomial at a geometric pair `(u,v)`. -/
noncomputable def evalNested {K : Type*} [Field K] (p : CPolynomial (CPolynomial F))
    (phi : F →+* K) (u v : K) : K :=
  (FirstOrderNormDecoder.D5.specializeFiberCPolynomial p phi u).eval v

/-- A geometric point of `(F[U]/G)[V]/h`. -/
noncomputable def Point {K : Type*} [Field K] (r : TowerRepresentation (F := F))
    (phi : F →+* K) (u v : K) : Prop :=
  r.modulus.toPoly.eval₂ phi u = 0 ∧ evalNested r.fiber phi u v = 0

/-- Specialize the represented coefficient vector at one geometric tower point. -/
noncomputable def specialize {K : Type*} [Field K] (r : TowerRepresentation (F := F))
    (phi : F →+* K) (u v : K) : K[X] :=
  coefficientPolynomial (r.coefficients.map fun c ↦ evalNested c phi u v)

/-- A tower point represents the indicated message polynomial. -/
noncomputable def Represents {K : Type*} [Field K] (r : TowerRepresentation (F := F))
    (phi : F →+* K) (u v : K) (message : K[X]) : Prop :=
  r.Point phi u v ∧ r.specialize phi u v = message

/-- Every `U` coefficient of a nested polynomial has degree below `G`.  For a monic positive
degree `G`, this is exactly the uniqueness condition for coefficientwise reduction modulo `G`. -/
def BaseReduced (G : CPolynomial F) (p : CPolynomial (CPolynomial F)) : Prop :=
  ∀ i, (p.coeff i).toPoly.degree < G.toPoly.degree

/-- A tower element is in the canonical `U,V` basis determined by `G` and `h`. -/
def ElementReduced (G : CPolynomial F) (h p : CPolynomial (CPolynomial F)) : Prop :=
  p.toPoly.degree < h.toPoly.degree ∧ BaseReduced G p

/-- Fiberwise squarefreeness is the geometric étaleness condition needed by zero/unit splitting.
It is required after every coefficient-field extension and at every root of the base modulus. -/
def FiberwiseSquarefree (r : TowerRepresentation (F := F)) : Prop :=
  ∀ (K : Type) [Field K] (phi : F →+* K) (u : K),
    r.modulus.toPoly.eval₂ phi u = 0 →
      Squarefree (FirstOrderNormDecoder.D5.specializeFiberCPolynomial r.fiber phi u)

/-- Semantic and canonical invariants of a retained tower block.

The width is the number of message coefficients.  Positive base and fiber degrees ensure the
runtime contains no empty component; monicity and reduction bounds make every stored element a
canonical quotient representative. -/
def WellFormed (r : TowerRepresentation (F := F)) (width : ℕ) : Prop :=
  r.modulus.monic ∧
    Squarefree r.modulus.toPoly ∧
    0 < r.modulus.natDegree ∧
    r.fiber.monic ∧
    0 < r.fiber.natDegree ∧
    BaseReduced r.modulus r.fiber ∧
    FiberwiseSquarefree r ∧
    r.coefficients.length = width ∧
    ∀ coefficient ∈ r.coefficients,
      ElementReduced r.modulus r.fiber coefficient

/-- A retained tower has positive quotient dimension. -/
theorem dimension_ne_zero (r : TowerRepresentation (F := F)) {width : ℕ}
    (hr : r.WellFormed width) : r.dimension ≠ 0 := by
  exact Nat.mul_ne_zero hr.2.2.1.ne' hr.2.2.2.2.1.ne'

/-- A tower point lies over a root of the base modulus. -/
theorem point_base (r : TowerRepresentation (F := F))
    {K : Type*} [Field K] {phi : F →+* K} {u v : K}
    (hpoint : r.Point phi u v) : r.modulus.toPoly.eval₂ phi u = 0 :=
  hpoint.1

/-- A tower point is a root of its specialized fiber polynomial. -/
theorem point_fiber (r : TowerRepresentation (F := F))
    {K : Type*} [Field K] {phi : F →+* K} {u v : K}
    (hpoint : r.Point phi u v) : evalNested r.fiber phi u v = 0 :=
  hpoint.2

/-- A geometric point on a monic child forces both quotient degrees, hence its dimension, to be
positive.  This justifies discarding constant D5 branches. -/
theorem dimension_ne_zero_of_point
    (r : TowerRepresentation (F := F))
    (hmodulusNe : r.modulus ≠ 0) (hfiberMonic : r.fiber.monic)
    {K : Type*} [Field K] (phi : F →+* K) (u v : K)
    (hpoint : r.Point phi u v) : r.dimension ≠ 0 := by
  have hbasePos : 0 < r.modulus.natDegree := by
    rw [CPolynomial.natDegree_toPoly]
    exact Polynomial.natDegree_pos_of_eval₂_root
      ((CPolynomial.toPoly_eq_zero_iff _).not.mpr hmodulusNe) phi hpoint.1
      (fun x hx ↦ phi.injective (hx.trans phi.map_zero.symm))
  have hspecializedMonic :
      (FirstOrderNormDecoder.D5.specializeFiberCPolynomial r.fiber phi u).Monic :=
    ((CPolynomial.monic_toPoly_iff _).mp hfiberMonic).map _
  have hspecializedPos :
      0 < (FirstOrderNormDecoder.D5.specializeFiberCPolynomial r.fiber phi u).natDegree := by
    apply Polynomial.natDegree_pos_of_eval₂_root hspecializedMonic.ne_zero (RingHom.id K)
    · simpa [Point, evalNested] using hpoint.2
    · intro x hx
      simpa using hx
  have hfiberPos : 0 < r.fiber.natDegree :=
    hspecializedPos.trans_le <| by
      rw [FirstOrderNormDecoder.D5.specializeFiberCPolynomial]
      simpa only [← CPolynomial.natDegree_toPoly] using
        (Polynomial.natDegree_map_le :
          (r.fiber.toPoly.map (FirstOrderNormDecoder.D5.coefficientEval phi u)).natDegree ≤
            r.fiber.toPoly.natDegree)
  exact Nat.mul_ne_zero hbasePos.ne' hfiberPos.ne'

/-- Canonically reduce every `U` coefficient modulo a child base modulus. -/
def reduceBase (G : CPolynomial F) (p : CPolynomial (CPolynomial F)) :
    CPolynomial (CPolynomial F) :=
  FirstOrderNormDecoder.D5.reduceFiberCoefficients G p

/-- Canonically reduce a tower element first in `V` and then coefficientwise in `U`. -/
def reduceElement (G : CPolynomial F) (h p : CPolynomial (CPolynomial F)) :
    CPolynomial (CPolynomial F) :=
  reduceBase G (p.modByMonic h)

/-- Base reduction preserves evaluation at every geometric root of the new base modulus. -/
theorem evalNested_reduceBase
    {K : Type*} [Field K] (phi : F →+* K) (u v : K)
    {G : CPolynomial F} (hG : G.monic) (hu : G.toPoly.eval₂ phi u = 0)
    (p : CPolynomial (CPolynomial F)) :
    evalNested (reduceBase G p) phi u v = evalNested p phi u v := by
  rw [evalNested, evalNested, reduceBase,
    FirstOrderNormDecoder.D5.specialize_reduceFiberCoefficients phi u hG hu]

/-- Monic remainder reduction preserves evaluation at every root of the fiber modulus. -/
theorem evalNested_modByMonic
    {K : Type*} [Field K] (phi : F →+* K) (u v : K)
    {h : CPolynomial (CPolynomial F)} (hh : h.monic)
    (hv : evalNested h phi u v = 0) (p : CPolynomial (CPolynomial F)) :
    evalNested (p.modByMonic h) phi u v = evalNested p phi u v := by
  rw [evalNested, evalNested,
    FirstOrderNormDecoder.D5.specializeFiberCPolynomial,
    FirstOrderNormDecoder.D5.specializeFiberCPolynomial,
    CPolynomial.modByMonic_toPoly_eq_modByMonic p h hh]
  rw [Polynomial.map_modByMonic _ ((CPolynomial.monic_toPoly_iff h).mp hh)]
  exact Polynomial.eval₂_modByMonic_eq_self_of_root hv

/-- Full tower reduction preserves evaluation at a geometric point of the reduced child. -/
theorem evalNested_reduceElement
    {K : Type*} [Field K] (phi : F →+* K) (u v : K)
    {G : CPolynomial F} (hG : G.monic) (hu : G.toPoly.eval₂ phi u = 0)
    {h : CPolynomial (CPolynomial F)} (hh : h.monic)
    (hv : evalNested h phi u v = 0) (p : CPolynomial (CPolynomial F)) :
    evalNested (reduceElement G h p) phi u v = evalNested p phi u v := by
  rw [reduceElement, evalNested_reduceBase phi u v hG hu,
    evalNested_modByMonic phi u v hh hv]

/-- Every base-reduced nested polynomial satisfies the canonical coefficient-degree bound. -/
theorem baseReduced_reduceBase {G : CPolynomial F} (hG : G.monic)
    (p : CPolynomial (CPolynomial F)) : BaseReduced G (reduceBase G p) := by
  intro i
  exact FirstOrderNormDecoder.D5.degree_coeff_reduceFiberCoefficients_lt hG p i

/-- Coefficientwise reduction modulo a positive-degree monic base preserves outer monicity. -/
theorem monic_reduceBase {G : CPolynomial F} (hG : G.monic) (hGpos : 0 < G.natDegree)
    {p : CPolynomial (CPolynomial F)} (hp : p.monic) : (reduceBase G p).monic := by
  rw [CPolynomial.monic_toPoly_iff]
  apply Polynomial.monic_of_natDegree_le_of_coeff_eq_one p.natDegree
  · rw [← CPolynomial.natDegree_toPoly]
    by_cases hzero : reduceBase G p = 0
    · simp [hzero, CPolynomial.natDegree_toPoly, CPolynomial.toPoly_zero]
    · exact FirstOrderNormDecoder.D5.natDegree_reduceFiberCoefficients_le G p hzero
  · rw [← CPolynomial.coeff_toPoly, reduceBase,
      FirstOrderNormDecoder.D5.coeff_reduceFiberCoefficients]
    split
    · rw [← CPolynomial.leadingCoeff_eq_coeff_natDegree]
      have hpLeading : p.leadingCoeff = 1 := by
        simpa only [CPolynomial.leadingCoeff_toPoly] using
          ((CPolynomial.monic_toPoly_iff p).mp hp).leadingCoeff
      rw [hpLeading]
      apply CPolynomial.toPoly_injective
      rw [CPolynomial.modByMonic_toPoly_eq_modByMonic _ _ hG,
        CPolynomial.toPoly_one]
      exact (Polynomial.modByMonic_eq_self_iff
        ((CPolynomial.monic_toPoly_iff G).mp hG)).mpr (by
          rw [Polynomial.degree_one, ← CPolynomial.degree_toPoly,
            CPolynomial.degree_eq_natDegree G
              ((CPolynomial.toPoly_eq_zero_iff G).not.mp
                ((CPolynomial.monic_toPoly_iff G).mp hG).ne_zero)]
          exact WithBot.coe_lt_coe.mpr hGpos)
    · rename_i hlt
      exact (hlt (Nat.lt_add_one _)).elim

/-- The executable two-stage reduction lands in the canonical tower basis. -/
theorem elementReduced_reduceElement {G : CPolynomial F} (hG : G.monic)
    {h : CPolynomial (CPolynomial F)} (hh : h.monic) (_hhpos : 0 < h.natDegree)
    (p : CPolynomial (CPolynomial F)) : ElementReduced G h (reduceElement G h p) := by
  refine ⟨?_, baseReduced_reduceBase hG _⟩
  have hhPoly : h.toPoly.Monic := (CPolynomial.monic_toPoly_iff h).mp hh
  have hhNe : h ≠ 0 :=
    (CPolynomial.toPoly_eq_zero_iff h).not.mp hhPoly.ne_zero
  have hqDegree : (p.modByMonic h).toPoly.degree < h.toPoly.degree := by
    rw [CPolynomial.modByMonic_toPoly_eq_modByMonic p h hh]
    exact Polynomial.degree_modByMonic_lt _ hhPoly
  by_cases hreduce : reduceElement G h p = 0
  · rw [hreduce, CPolynomial.toPoly_zero, Polynomial.degree_zero]
    exact WithBot.bot_lt_iff_ne_bot.mpr (Polynomial.degree_ne_bot.mpr hhPoly.ne_zero)
  · have hreduce' : reduceBase G (p.modByMonic h) ≠ 0 := by
      simpa [reduceElement] using hreduce
    have hqNe : p.modByMonic h ≠ 0 := by
      intro hq
      apply hreduce'
      rw [hq, reduceBase]
      exact FirstOrderNormDecoder.D5.reduceFiberCoefficients_zero G hG
    have hnat := FirstOrderNormDecoder.D5.natDegree_reduceFiberCoefficients_le G
      (p.modByMonic h) hreduce'
    rw [reduceElement, ← CPolynomial.degree_toPoly,
      CPolynomial.degree_eq_natDegree _ hreduce',
      ← CPolynomial.degree_toPoly,
      CPolynomial.degree_eq_natDegree h hhNe]
    rw [← CPolynomial.degree_toPoly,
      CPolynomial.degree_eq_natDegree (p.modByMonic h) hqNe,
      ← CPolynomial.degree_toPoly,
      CPolynomial.degree_eq_natDegree h hhNe] at hqDegree
    exact WithBot.coe_lt_coe.mpr (hnat.trans_lt (WithBot.coe_lt_coe.mp hqDegree))

end TowerRepresentation

end ReedSolomon.ListDecoding

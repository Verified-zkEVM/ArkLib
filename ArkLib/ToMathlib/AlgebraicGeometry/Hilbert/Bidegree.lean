/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import ArkLib.Data.MvPolynomial.WeightedDegree
public import ArkLib.ToMathlib.AlgebraicGeometry.Hilbert.Degree
public import ArkLib.ToMathlib.AlgebraicGeometry.Hilbert.FiniteExtensionDegree
public import ArkLib.ToMathlib.AlgebraicGeometry.Hilbert.PolynomialGrowthRescaling
public import ArkLib.ToMathlib.AlgebraicGeometry.PrincipalCut.Purity
public import ArkLib.ToMathlib.Polynomial.RectangleDifference
public import ArkLib.ToMathlib.Polynomial.RectangleDifferenceGeneral
public import Mathlib.Data.Finsupp.Option

/-!
# A challenge/jet bidegree filtration

This file supplies the elementary two-block filtration used by sharp symbolic
correlated-agreement geometry.  The distinguished `none` variable is the challenge;
the `some` variables are the Taylor jets.  A rectangle bounds the challenge exponent
and the total jet exponent separately.

The definitions are independent of Reed--Solomon codes.  In particular, they isolate
the algebraic input behind the mixed hypersurface degree

```text
h * b^(r+1) + (r+1) * v * a * b^r.
```
-/

@[expose] public section

noncomputable section

namespace AffineHilbert

open MvPolynomial
open Polynomial Filter
open scoped Topology

variable {F σ : Type*} [Field F]

/-- Weight one on the distinguished challenge coordinate and zero on all jet coordinates. -/
def challengeWeight : Option σ → ℕ
  | none => 1
  | some _ => 0

/-- Weight zero on the distinguished challenge coordinate and one on every jet coordinate. -/
def jetWeight : Option σ → ℕ
  | none => 0
  | some _ => 1

/-- Polynomials with challenge degree at most `a` and total jet degree at most `b`. -/
def restrictBidegree (a b : ℕ) : Submodule F (MvPolynomial (Option σ) F) :=
  restrictSupport F {m | m.weight (challengeWeight (σ := σ)) ≤ a ∧
    m.weight (jetWeight (σ := σ)) ≤ b}

theorem mem_restrictBidegree {a b : ℕ} {P : MvPolynomial (Option σ) F} :
    P ∈ restrictBidegree (F := F) (σ := σ) a b ↔
      ∀ m ∈ P.support, m.weight (challengeWeight (σ := σ)) ≤ a ∧
        m.weight (jetWeight (σ := σ)) ≤ b := by
  rfl

/-- Bidegree rectangles are closed under multiplication, with componentwise addition
of the two budgets. -/
theorem mul_mem_restrictBidegree {a b c d : ℕ}
    {P Q : MvPolynomial (Option σ) F}
    (hP : P ∈ restrictBidegree (F := F) (σ := σ) a b)
    (hQ : Q ∈ restrictBidegree (F := F) (σ := σ) c d) :
    P * Q ∈ restrictBidegree (F := F) (σ := σ) (a + c) (b + d) := by
  classical
  rw [mem_restrictBidegree] at hP hQ ⊢
  intro m hm
  obtain ⟨i, hi, j, hj, rfl⟩ := Finset.mem_add.mp (support_mul P Q hm)
  simpa only [map_add] using
    ⟨Nat.add_le_add (hP i hi).1 (hQ j hj).1,
      Nat.add_le_add (hP i hi).2 (hQ j hj).2⟩

/-- The exponent rectangle is finite when the jet-variable type is finite. -/
theorem bidegreeExponentSet_finite [Finite σ] (a b : ℕ) :
    Set.Finite {m : Option σ →₀ ℕ |
      m.weight (challengeWeight (σ := σ)) ≤ a ∧
        m.weight (jetWeight (σ := σ)) ≤ b} := by
  let _ : Fintype σ := Fintype.ofFinite σ
  apply (Finsupp.finite_of_degree_le (a + b)).subset
  intro m hm
  change m.weight (challengeWeight (σ := σ)) ≤ a ∧
    m.weight (jetWeight (σ := σ)) ≤ b at hm
  change m.degree ≤ a + b
  rw [Finsupp.degree_eq_sum, Fintype.sum_option]
  have hc : m.weight (challengeWeight (σ := σ)) = m none := by
    rw [Finsupp.weight_eq_sum, Fintype.sum_option]
    simp [challengeWeight]
  have hj : m.weight (jetWeight (σ := σ)) = ∑ i : σ, m (some i) := by
    rw [Finsupp.weight_eq_sum, Fintype.sum_option]
    simp [jetWeight]
  rw [hc, hj] at hm
  omega

instance [Finite σ] (a b : ℕ) :
    Module.Finite F (restrictBidegree (F := F) (σ := σ) a b) := by
  let S : Set (Option σ →₀ ℕ) := {m |
    m.weight (challengeWeight (σ := σ)) ≤ a ∧
      m.weight (jetWeight (σ := σ)) ≤ b}
  have hS : S.Finite := bidegreeExponentSet_finite (σ := σ) a b
  let _ : Finite S := hS.to_subtype
  let basis := basisRestrictSupport F S
  change Module.Finite F (restrictSupport F S)
  exact Module.Finite.of_basis basis

/-- The bidegree rectangle has the product cardinality expected from separating the
challenge exponent and the total jet exponent. -/
theorem finrank_restrictBidegree [Finite σ] (a b : ℕ) :
    Module.finrank F (restrictBidegree (F := F) (σ := σ) a b) =
      (a + 1) * (b + Nat.card σ).choose (Nat.card σ) := by
  classical
  let _ : Fintype σ := Fintype.ofFinite σ
  let A := {m : Option σ →₀ ℕ //
    m.weight (challengeWeight (σ := σ)) ≤ a ∧
      m.weight (jetWeight (σ := σ)) ≤ b}
  let B := Fin (a + 1) × {m : σ →₀ ℕ // m.degree ≤ b}
  let _ : Finite A := (bidegreeExponentSet_finite (σ := σ) a b).to_subtype
  let _ : Finite {m : σ →₀ ℕ // m.degree ≤ b} :=
    (Finsupp.finite_of_degree_le b).to_subtype
  let e : A ≃ B :=
    { toFun := fun m ↦
        (⟨m.val none, by
          have hc : m.val.weight (challengeWeight (σ := σ)) = m.val none := by
            rw [Finsupp.weight_eq_sum, Fintype.sum_option]
            simp [challengeWeight]
          omega⟩,
        ⟨m.val.some, by
          have hj : m.val.weight (jetWeight (σ := σ)) = m.val.some.degree := by
            rw [Finsupp.weight_eq_sum, Fintype.sum_option, Finsupp.degree_eq_sum]
            simp [jetWeight]
          omega⟩)
      invFun := fun p ↦
        ⟨Finsupp.optionElim p.1.val p.2.val, by
          constructor
          · rw [Finsupp.weight_eq_sum, Fintype.sum_option]
            simp [challengeWeight]
            omega
          · rw [Finsupp.weight_eq_sum, Fintype.sum_option]
            simp [jetWeight]
            simpa only [Finsupp.degree_eq_sum] using p.2.property⟩
      left_inv := by
        intro m
        apply Subtype.ext
        exact Finsupp.optionElim_some m.val
      right_inv := by
        intro p
        apply Prod.ext
        · apply Fin.ext
          simp
        · apply Subtype.ext
          simp }
  let S : Set (Option σ →₀ ℕ) := {m |
    m.weight (challengeWeight (σ := σ)) ≤ a ∧
      m.weight (jetWeight (σ := σ)) ≤ b}
  have hS : S.Finite := bidegreeExponentSet_finite (σ := σ) a b
  let basis := basisRestrictSupport F S
  let _ : Fintype S := hS.fintype
  let _ : Fintype A := Fintype.ofFinite A
  have hfinrank : Module.finrank F (restrictBidegree (F := F) (σ := σ) a b) = Nat.card A := by
    change Module.finrank F (restrictSupport F S) = Nat.card A
    rw [Module.finrank_eq_card_basis basis, Nat.card_eq_fintype_card]
    rfl
  rw [hfinrank, Nat.card_congr e, show Nat.card B =
      (a + 1) * Nat.card {m : σ →₀ ℕ // m.degree ≤ b} by
        simp only [B, Nat.card_prod, Nat.card_fin]]
  congr 1
  rw [show Nat.card {m : σ →₀ ℕ // m.degree ≤ b} =
      Set.ncard {m : σ →₀ ℕ | m.degree ≤ b} by exact Nat.card_coe_set_eq _]
  rw [show {m : σ →₀ ℕ | m.degree ≤ b} =
      (MonomialHilbertCounting.degreeBall σ b : Set (σ →₀ ℕ)) by
        ext m
        simp [MonomialHilbertCounting.mem_degreeBall]]
  simp only [Set.ncard_coe_finset, MonomialHilbertCounting.card_degreeBall]
  simp only [Nat.card_eq_fintype_card]

/-! ## The affine rectangle embedding -/

/-- Coordinates of the affine Segre--Veronese rectangle of bidegree `(a,b)`. -/
abbrev BidegreeIndex (a b : ℕ) (σ : Type*) :=
  {m : Option σ →₀ ℕ //
    m.weight (challengeWeight (σ := σ)) ≤ a ∧
      m.weight (jetWeight (σ := σ)) ≤ b}

noncomputable instance [Finite σ] (a b : ℕ) : Fintype (BidegreeIndex a b σ) :=
  (bidegreeExponentSet_finite (σ := σ) a b).fintype

/-- Evaluate a polynomial in rectangle coordinates at the corresponding challenge/jet
monomials. -/
def bidegreeMap (a b : ℕ) :
    MvPolynomial (BidegreeIndex a b σ) F →ₐ[F] MvPolynomial (Option σ) F :=
  MvPolynomial.aeval fun m ↦ MvPolynomial.monomial m.val 1

/-- Positive rectangle side lengths make the affine rectangle map onto: the coordinate
set contains the challenge variable and every jet variable. -/
theorem bidegreeMap_surjective (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    Function.Surjective (bidegreeMap (F := F) (σ := σ) a b) := by
  intro P
  induction P using MvPolynomial.induction_on with
  | C c => exact ⟨MvPolynomial.C c, by simp [bidegreeMap]⟩
  | add P Q hP hQ =>
      obtain ⟨P', rfl⟩ := hP
      obtain ⟨Q', rfl⟩ := hQ
      exact ⟨P' + Q', by simp⟩
  | mul_X P i hP =>
      obtain ⟨P', rfl⟩ := hP
      let exponent : Option σ →₀ ℕ := Finsupp.single i 1
      have hexponent : exponent.weight (challengeWeight (σ := σ)) ≤ a ∧
          exponent.weight (jetWeight (σ := σ)) ≤ b := by
        cases i with
        | none =>
            simp only [exponent, Finsupp.weight_single, one_smul, challengeWeight, jetWeight]
            omega
        | some i =>
            simp only [exponent, Finsupp.weight_single, one_smul, challengeWeight, jetWeight]
            omega
      refine ⟨P' * MvPolynomial.X (⟨exponent, hexponent⟩ : BidegreeIndex a b σ), ?_⟩
      simp only [map_mul, bidegreeMap, MvPolynomial.aeval_X]
      congr 1

/-- The coordinate lift of a polynomial already lying in the rectangle. -/
def bidegreeLift (a b : ℕ) (P : MvPolynomial (Option σ) F)
    (hP : P ∈ restrictBidegree (F := F) (σ := σ) a b) :
    MvPolynomial (BidegreeIndex a b σ) F :=
  ∑ m : P.support, MvPolynomial.C (MvPolynomial.coeff m.val P) *
    MvPolynomial.X (⟨m.val, (mem_restrictBidegree.mp hP) m.val m.property⟩ :
      BidegreeIndex a b σ)

/-- The rectangle lift is a section of `bidegreeMap`. -/
theorem bidegreeMap_bidegreeLift (a b : ℕ) (P : MvPolynomial (Option σ) F)
    (hP : P ∈ restrictBidegree (F := F) (σ := σ) a b) :
    bidegreeMap a b (bidegreeLift a b P hP) = P := by
  classical
  rw [bidegreeLift, map_sum]
  simp only [map_mul, bidegreeMap, MvPolynomial.aeval_C, algebraMap_eq,
    MvPolynomial.aeval_X]
  calc
    ∑ m : P.support, MvPolynomial.C (MvPolynomial.coeff m.val P) *
        MvPolynomial.monomial m.val 1 =
        ∑ m ∈ P.support, MvPolynomial.C (MvPolynomial.coeff m P) *
          MvPolynomial.monomial m 1 := by
            simpa using Finset.sum_attach P.support (fun m ↦
              MvPolynomial.C (MvPolynomial.coeff m P) * MvPolynomial.monomial m 1)
    _ = P := by simpa [monomial_eq] using P.as_sum.symm

private theorem bidegreeMap_weightedTotalDegree_le [Finite σ] (a b : ℕ)
    (w : Option σ → ℕ) (c : ℕ)
    (hw : ∀ m : BidegreeIndex a b σ, m.val.weight w ≤ c)
    (P : MvPolynomial (BidegreeIndex a b σ) F) :
    (bidegreeMap a b P).weightedTotalDegree w ≤ c * P.totalDegree := by
  classical
  let _ : Fintype (BidegreeIndex a b σ) := Fintype.ofFinite _
  apply (MvPolynomial.weightedTotalDegree_aeval_le_of_le
    (fun _ : BidegreeIndex a b σ ↦ c) w
    (fun m ↦ MvPolynomial.monomial m.val 1) P ?_).trans
  · unfold MvPolynomial.weightedTotalDegree
    rw [Finset.sup_le_iff]
    intro m hm
    calc
      Finsupp.weight (fun _ : BidegreeIndex a b σ ↦ c) m = c * m.degree := by
        rw [Finsupp.weight_apply, Finsupp.degree_eq_sum]
        simp only [Finsupp.sum, nsmul_eq_mul, Finset.mul_sum, Nat.mul_comm]
        rw [← Finsupp.sum_fintype m (fun _ n ↦ c * n) (by simp)]
        rfl
      _ ≤ c * P.totalDegree := Nat.mul_le_mul_left c (MvPolynomial.le_totalDegree hm)
  · intro m
    rw [MvPolynomial.weightedTotalDegree_monomial _ _ _ one_ne_zero]
    exact hw m

/-- Ordinary lifted degree `N` maps into challenge degree `a*N`. -/
theorem bidegreeMap_challengeDegree_le [Finite σ] (a b : ℕ)
    (P : MvPolynomial (BidegreeIndex a b σ) F) :
    (bidegreeMap a b P).weightedTotalDegree challengeWeight ≤ a * P.totalDegree :=
  bidegreeMap_weightedTotalDegree_le a b challengeWeight a (fun m ↦ m.property.1) P

/-- Ordinary lifted degree `N` maps into total jet degree `b*N`. -/
theorem bidegreeMap_jetDegree_le [Finite σ] (a b : ℕ)
    (P : MvPolynomial (BidegreeIndex a b σ) F) :
    (bidegreeMap a b P).weightedTotalDegree jetWeight ≤ b * P.totalDegree :=
  bidegreeMap_weightedTotalDegree_le a b jetWeight b (fun m ↦ m.property.2) P

/-- Rectangle lifts are linear equations in the embedding coordinates. -/
theorem bidegreeLift_totalDegree_le_one (a b : ℕ)
    (P : MvPolynomial (Option σ) F)
    (hP : P ∈ restrictBidegree (F := F) (σ := σ) a b) :
    (bidegreeLift a b P hP).totalDegree ≤ 1 := by
  classical
  rw [bidegreeLift]
  apply MvPolynomial.totalDegree_finsetSum_le
  intro m hm
  exact (MvPolynomial.totalDegree_mul _ _).trans (by simp)

/-- The ideal of the rectangle embedding. -/
def bidegreeIdeal (a b : ℕ) : Ideal (MvPolynomial (BidegreeIndex a b σ) F) :=
  RingHom.ker (bidegreeMap (F := F) (σ := σ) a b).toRingHom

theorem bidegreeIdeal_isPrime (a b : ℕ) :
    (bidegreeIdeal (F := F) (σ := σ) a b).IsPrime :=
  RingHom.ker_isPrime (bidegreeMap a b).toRingHom

theorem bidegreeIdeal_hilbertPolynomial_natDegree [Finite σ]
    (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    (hilbertPolynomial (bidegreeIdeal (F := F) (σ := σ) a b)).natDegree =
      Nat.card (Option σ) := by
  let e₀ : (MvPolynomial (BidegreeIndex a b σ) F ⧸ bidegreeIdeal a b) ≃ₐ[F]
      MvPolynomial (Option σ) F := Ideal.quotientKerAlgEquivOfSurjective
    (bidegreeMap_surjective (F := F) a b ha hb)
  let e : (MvPolynomial (BidegreeIndex a b σ) F ⧸ bidegreeIdeal a b) ≃ₐ[F]
      (MvPolynomial (Option σ) F ⧸ (⊥ : Ideal (MvPolynomial (Option σ) F))) :=
    e₀.trans (AlgEquiv.quotientBot F (MvPolynomial (Option σ) F)).symm
  rw [← hilbertPolynomial_bot_natDegree (F := F) (σ := Option σ)]
  symm
  apply hilbertPolynomial_natDegree_eq_of_finite_injective_algHom e.toAlgHom e.injective
    (show (⊥ : Ideal (MvPolynomial (Option σ) F)) ≠ ⊤ by exact bot_ne_top)
  let _ : Algebra (MvPolynomial (BidegreeIndex a b σ) F ⧸ bidegreeIdeal a b)
      (MvPolynomial (Option σ) F ⧸ (⊥ : Ideal (MvPolynomial (Option σ) F))) :=
    e.toRingHom.toAlgebra
  exact Module.Finite.of_surjective (Algebra.linearMap _ _) e.surjective

/-! ## Rectangular filtration of a hypersurface quotient -/

/-- The image of a bidegree rectangle in an affine quotient. -/
def quotientBidegreeLE (I : Ideal (MvPolynomial (Option σ) F)) (a b : ℕ) :
    Submodule F (MvPolynomial (Option σ) F ⧸ I) :=
  (restrictBidegree (F := F) (σ := σ) a b).map (Ideal.Quotient.mkₐ F I).toLinearMap

instance [Finite σ] (I : Ideal (MvPolynomial (Option σ) F)) (a b : ℕ) :
    Module.Finite F (quotientBidegreeLE I a b) := by
  unfold quotientBidegreeLE
  infer_instance

private def bidegreeQuotientMap (I : Ideal (MvPolynomial (Option σ) F)) (a b : ℕ) :
    restrictBidegree (F := F) (σ := σ) a b →ₗ[F] quotientBidegreeLE I a b :=
  ((Ideal.Quotient.mkₐ F I).toLinearMap.domRestrict
    (restrictBidegree (F := F) (σ := σ) a b)).codRestrict _ (fun p ↦
      ⟨p.val, ⟨p.property, rfl⟩⟩)

private theorem bidegreeQuotientMap_surjective
    (I : Ideal (MvPolynomial (Option σ) F)) (a b : ℕ) :
    Function.Surjective (bidegreeQuotientMap I a b) := by
  rintro ⟨x, ⟨p, hp⟩⟩
  exact ⟨⟨p, hp.1⟩, Subtype.ext hp.2⟩

private def bidegreeMulToBig {g : MvPolynomial (Option σ) F} {h v A B : ℕ}
    (hg : g ∈ restrictBidegree (F := F) (σ := σ) h v) (hhA : h ≤ A) (hvB : v ≤ B) :
    restrictBidegree (F := F) (σ := σ) (A - h) (B - v) →ₗ[F]
      restrictBidegree (F := F) (σ := σ) A B :=
  ((LinearMap.mulLeft F g).domRestrict
    (restrictBidegree (F := F) (σ := σ) (A - h) (B - v))).codRestrict _ (fun p ↦ by
      have hp := mul_mem_restrictBidegree hg p.property
      change g * p.val ∈ restrictBidegree (F := F) (σ := σ) A B
      simpa only [Nat.add_sub_of_le hhA, Nat.add_sub_of_le hvB] using hp)

set_option maxHeartbeats 800000 in
-- The nested quotient and subtype maps require extra elaboration heartbeats.
/-- A nonzero bidegree-`(h,v)` equation removes a full shifted rectangle from the
rectangle of bidegree `(A,B)`.  This is the filtered linear-algebra core of the
mixed Bezout bound. -/
theorem quotientBidegreeLE_finrank_add_le [Finite σ]
    {g : MvPolynomial (Option σ) F} {h v A B : ℕ}
    (hne : g ≠ 0) (hg : g ∈ restrictBidegree (F := F) (σ := σ) h v)
    (hhA : h ≤ A) (hvB : v ≤ B) :
    Module.finrank F (quotientBidegreeLE (Ideal.span {g}) A B) +
        Module.finrank F (restrictBidegree (F := F) (σ := σ) (A - h) (B - v)) ≤
      Module.finrank F (restrictBidegree (F := F) (σ := σ) A B) := by
  let cut := bidegreeQuotientMap (Ideal.span {g}) A B
  let mulToKer : restrictBidegree (F := F) (σ := σ) (A - h) (B - v) →ₗ[F]
      LinearMap.ker cut :=
    (bidegreeMulToBig hg hhA hvB).codRestrict _ (fun p ↦ by
      change cut (bidegreeMulToBig hg hhA hvB p) = 0
      dsimp only [cut]
      apply Subtype.ext
      change Ideal.Quotient.mk (Ideal.span {g}) (g * p.val) = 0
      rw [Ideal.Quotient.eq_zero_iff_mem]
      simpa [mul_comm] using
        (Ideal.span {g}).mul_mem_left p.val (Ideal.subset_span (Set.mem_singleton g)))
  have hmul : Function.Injective mulToKer := by
    intro x y hxy
    apply Subtype.ext
    have hval := congrArg (fun p : LinearMap.ker cut ↦ p.val.val) hxy
    change g * x.val = g * y.val at hval
    exact mul_left_cancel₀ hne hval
  have hsmall : Module.finrank F
      (restrictBidegree (F := F) (σ := σ) (A - h) (B - v)) ≤
      Module.finrank F (LinearMap.ker cut) :=
    LinearMap.finrank_le_finrank_of_injective hmul
  have hsurj : Function.Surjective cut := bidegreeQuotientMap_surjective _ _ _
  have hrank := cut.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hsurj, finrank_top] at hrank
  omega

/-- Explicit rectangular Hilbert-function bound for a nonzero bidegree hypersurface. -/
theorem quotientBidegreeLE_finrank_le [Finite σ]
    {g : MvPolynomial (Option σ) F} {h v A B : ℕ}
    (hne : g ≠ 0) (hg : g ∈ restrictBidegree (F := F) (σ := σ) h v)
    (hhA : h ≤ A) (hvB : v ≤ B) :
    Module.finrank F (quotientBidegreeLE (Ideal.span {g}) A B) ≤
      (A + 1) * (B + Nat.card σ).choose (Nat.card σ) -
        (A - h + 1) * (B - v + Nat.card σ).choose (Nat.card σ) := by
  have h := quotientBidegreeLE_finrank_add_le hne hg hhA hvB
  rw [finrank_restrictBidegree, finrank_restrictBidegree] at h
  omega

/-! ## Comparison with the ordinary filtration of the lifted hypersurface -/

/-- Compose the rectangle parametrization with the quotient by one source equation. -/
def bidegreeCutMap (a b : ℕ) (g : MvPolynomial (Option σ) F) :
    MvPolynomial (BidegreeIndex a b σ) F →ₐ[F]
      MvPolynomial (Option σ) F ⧸ Ideal.span {g} :=
  (Ideal.Quotient.mkₐ F (Ideal.span {g})).comp (bidegreeMap a b)

/-- The lifted ideal defining the pullback of the source hypersurface. -/
abbrev bidegreeHypersurfaceIdeal (a b : ℕ) (g : MvPolynomial (Option σ) F) :
    Ideal (MvPolynomial (BidegreeIndex a b σ) F) :=
  RingHom.ker (bidegreeCutMap a b g).toRingHom

theorem bidegreeCutMap_surjective (a b : ℕ) (g : MvPolynomial (Option σ) F)
    (ha : 0 < a) (hb : 0 < b) : Function.Surjective (bidegreeCutMap a b g) := by
  exact (Ideal.Quotient.mk_surjective.comp (bidegreeMap_surjective a b ha hb))

/-- The rectangle presentation preserves the dimension of a proper source hypersurface. -/
theorem bidegreeHypersurface_hilbertPolynomial_natDegree [Finite σ]
    (a b : ℕ) (g : MvPolynomial (Option σ) F) (ha : 0 < a) (hb : 0 < b)
    (hproper : Ideal.span ({g} : Set (MvPolynomial (Option σ) F)) ≠ ⊤) :
    (hilbertPolynomial (bidegreeHypersurfaceIdeal a b g)).natDegree =
      (hilbertPolynomial (Ideal.span {g})).natDegree := by
  let e₀ : (MvPolynomial (BidegreeIndex a b σ) F ⧸
      bidegreeHypersurfaceIdeal a b g) ≃ₐ[F]
      MvPolynomial (Option σ) F ⧸ Ideal.span {g} :=
    Ideal.quotientKerAlgEquivOfSurjective (bidegreeCutMap_surjective a b g ha hb)
  symm
  apply hilbertPolynomial_natDegree_eq_of_finite_injective_algHom e₀.toAlgHom e₀.injective hproper
  let _ : Algebra (MvPolynomial (BidegreeIndex a b σ) F ⧸
      bidegreeHypersurfaceIdeal a b g)
      (MvPolynomial (Option σ) F ⧸ Ideal.span {g}) := e₀.toRingHom.toAlgebra
  exact Module.Finite.of_surjective
    (Algebra.linearMap (MvPolynomial (BidegreeIndex a b σ) F ⧸
      bidegreeHypersurfaceIdeal a b g)
      (MvPolynomial (Option σ) F ⧸ Ideal.span {g})) e₀.surjective

/-- A bounded source hypersurface pulls back to the linear lift modulo the
prime ideal of the rectangle presentation. -/
theorem bidegreeHypersurfaceIdeal_eq_sup (a b : ℕ)
    (g : MvPolynomial (Option σ) F)
    (hg : g ∈ restrictBidegree (F := F) (σ := σ) a b)
    (ha : 0 < a) (hb : 0 < b) :
    bidegreeHypersurfaceIdeal a b g =
      bidegreeIdeal a b ⊔ Ideal.span {bidegreeLift a b g hg} := by
  apply le_antisymm
  · intro P hP
    change Ideal.Quotient.mk (Ideal.span {g}) (bidegreeMap a b P) = 0 at hP
    rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton'] at hP
    obtain ⟨r, hr⟩ := hP
    obtain ⟨R, hR⟩ := bidegreeMap_surjective (F := F) a b ha hb r
    rw [← hR] at hr
    have hk : P - R * bidegreeLift a b g hg ∈ bidegreeIdeal a b := by
      change bidegreeMap a b (P - R * bidegreeLift a b g hg) = 0
      rw [map_sub, map_mul, bidegreeMap_bidegreeLift, hr, sub_self]
    have hl : R * bidegreeLift a b g hg ∈ Ideal.span {bidegreeLift a b g hg} :=
      (Ideal.span {bidegreeLift a b g hg}).mul_mem_left R
        (Ideal.subset_span (Set.mem_singleton _))
    rw [show P = (P - R * bidegreeLift a b g hg) + R * bidegreeLift a b g hg by ring]
    exact (bidegreeIdeal a b ⊔ Ideal.span {bidegreeLift a b g hg}).add_mem
      (Ideal.mem_sup_left hk) (Ideal.mem_sup_right hl)
  · apply sup_le
    · intro P hP
      change Ideal.Quotient.mk (Ideal.span {g}) (bidegreeMap a b P) = 0
      rw [Ideal.Quotient.eq_zero_iff_mem]
      rw [show bidegreeMap a b P = 0 from hP]
      exact Ideal.zero_mem _
    · rw [Ideal.span_le]
      intro P hP
      simp only [Set.mem_singleton_iff] at hP
      subst P
      change Ideal.Quotient.mk (Ideal.span {g})
        (bidegreeMap a b (bidegreeLift a b g hg)) = 0
      rw [bidegreeMap_bidegreeLift, Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.subset_span (Set.mem_singleton g)

/-- The ordinary degree-`N` filtration of the lifted hypersurface injects into its
source rectangle of bidegree `(a*N,b*N)`. -/
theorem bidegreeHypersurface_hilbertFunction_le [Finite σ]
    (a b N : ℕ) (g : MvPolynomial (Option σ) F) (ha : 0 < a) (hb : 0 < b) :
    hilbertFunction (bidegreeHypersurfaceIdeal a b g) N ≤
      Module.finrank F (quotientBidegreeLE (Ideal.span {g}) (a * N) (b * N)) := by
  let e₀ : (MvPolynomial (BidegreeIndex a b σ) F ⧸
      bidegreeHypersurfaceIdeal a b g) ≃ₐ[F]
      MvPolynomial (Option σ) F ⧸ Ideal.span {g} :=
    Ideal.quotientKerAlgEquivOfSurjective (bidegreeCutMap_surjective a b g ha hb)
  let L : quotientDegreeLE (bidegreeHypersurfaceIdeal a b g) N →ₗ[F]
      quotientBidegreeLE (Ideal.span {g}) (a * N) (b * N) :=
    (e₀.toLinearMap.domRestrict
      (quotientDegreeLE (bidegreeHypersurfaceIdeal a b g) N)).codRestrict _
      (fun x ↦ by
        obtain ⟨P, hP, hPx⟩ := x.property
        have hdeg : P.totalDegree ≤ N := (MvPolynomial.mem_restrictTotalDegree _ _ P).mp hP
        have he : e₀ x = Ideal.Quotient.mk (Ideal.span {g}) (bidegreeMap a b P) := by
          rw [← hPx]
          exact Ideal.quotientKerAlgEquivOfSurjective_mk
            (bidegreeCutMap_surjective a b g ha hb) P
        change e₀ x ∈ quotientBidegreeLE (Ideal.span {g}) (a * N) (b * N)
        rw [he]
        refine ⟨bidegreeMap a b P, ?_, rfl⟩
        change ∀ m ∈ (bidegreeMap a b P).support,
          m.weight challengeWeight ≤ a * N ∧ m.weight jetWeight ≤ b * N
        intro m hm
        constructor
        · exact (Finset.le_sup (f := fun n ↦ n.weight challengeWeight) hm).trans
            ((bidegreeMap_challengeDegree_le a b P).trans (Nat.mul_le_mul_left a hdeg))
        · exact (Finset.le_sup (f := fun n ↦ n.weight jetWeight) hm).trans
            ((bidegreeMap_jetDegree_le a b P).trans (Nat.mul_le_mul_left b hdeg)))
  rw [hilbertFunction]
  apply LinearMap.finrank_le_finrank_of_injective (f := L)
  intro x y hxy
  apply Subtype.ext
  have heq := congrArg Subtype.val hxy
  simp only [L, LinearMap.codRestrict_apply, LinearMap.domRestrict_apply] at heq
  exact e₀.injective heq

/-- Combined sharp Hilbert-function bound for the lifted source hypersurface. -/
theorem bidegreeHypersurface_hilbertFunction_le_rectangleDifference [Finite σ]
    {a b h v N : ℕ} {g : MvPolynomial (Option σ) F}
    (ha : 0 < a) (hb : 0 < b) (hne : g ≠ 0)
    (hg : g ∈ restrictBidegree (F := F) (σ := σ) h v)
    (hh : h ≤ a * N) (hv : v ≤ b * N) :
    hilbertFunction (bidegreeHypersurfaceIdeal a b g) N ≤
      (a * N + 1) * (b * N + Nat.card σ).choose (Nat.card σ) -
        (a * N - h + 1) * (b * N - v + Nat.card σ).choose (Nat.card σ) := by
  exact (bidegreeHypersurface_hilbertFunction_le a b N g ha hb).trans
    (quotientBidegreeLE_finrank_le hne hg hh hv)

/-- Extract an affine-degree bound from any eventual polynomial upper bound for the
actual Hilbert function at its known dimension. -/
theorem affineDegree_le_of_eventually_hilbertFunction_le
    [Finite σ] {I : Ideal (MvPolynomial σ F)} {s : ℕ} {R : ℚ[X]} {c : ℚ}
    (hdim : (hilbertPolynomial I).natDegree = s) (hRdeg : R.natDegree ≤ s)
    (hRc : R.coeff s = c)
    (hbound : ∀ᶠ N : ℕ in atTop, (hilbertFunction I N : ℚ) ≤ R.eval (N : ℚ)) :
    affineDegree I ≤ (s.factorial : ℚ) * c := by
  have heval : ∀ᶠ N : ℕ in atTop,
      (hilbertPolynomial I).eval (N : ℚ) ≤ R.eval (N : ℚ) := by
    filter_upwards [hilbertPolynomial_eventually_eval I, hbound] with N hN hRN
    rw [hN]
    exact hRN
  have hc := coeff_le_of_natDegree_le_of_eventually_eval_nat_le
    (le_of_eq hdim) hRdeg heval
  rw [hRc] at hc
  rw [affineDegree, hdim]
  calc
    (s.factorial : ℚ) * (hilbertPolynomial I).leadingCoeff =
        (s.factorial : ℚ) * (hilbertPolynomial I).coeff s := by
          rw [← hdim, Polynomial.coeff_natDegree]
    _ ≤ (s.factorial : ℚ) * c := mul_le_mul_of_nonneg_left hc (by positivity)

/-- Sharp mixed degree of a pulled-back hypersurface with `r + 1` jet coordinates. -/
theorem bidegreeHypersurface_affineDegree_le
    {r a b h v : ℕ} {g : MvPolynomial (Option (Fin (r + 1))) F}
    (ha : 0 < a) (hb : 0 < b) (hne : g ≠ 0)
    (hproper : Ideal.span ({g} : Set (MvPolynomial (Option (Fin (r + 1))) F)) ≠ ⊤)
    (hg : g ∈ restrictBidegree (F := F) (σ := Fin (r + 1)) h v) :
    affineDegree (bidegreeHypersurfaceIdeal a b g) ≤
      (h * b ^ (r + 1) + (r + 1) * v * a * b ^ r : ℕ) := by
  have hdim :
      (hilbertPolynomial (bidegreeHypersurfaceIdeal a b g)).natDegree = r + 1 := by
    rw [bidegreeHypersurface_hilbertPolynomial_natDegree a b g ha hb hproper]
    have hs := hilbertPolynomial_span_singleton_natDegree_add_one hne hproper
    simp only [Nat.card_eq_fintype_card, Fintype.card_option, Fintype.card_fin] at hs
    omega
  apply (affineDegree_le_of_eventually_hilbertFunction_le hdim
    (Polynomial.rectangleDifference_natDegree_le_succ r a b h v)
    (Polynomial.rectangleDifference_coeff_succ r a b h v) ?_).trans_eq
  · push_cast
    field_simp
  · filter_upwards [eventually_ge_atTop (max h v)] with N hN
    have hh : h ≤ a * N := (le_max_left h v).trans hN |>.trans
      (Nat.le_mul_of_pos_left N ha)
    have hv : v ≤ b * N := (le_max_right h v).trans hN |>.trans
      (Nat.le_mul_of_pos_left N hb)
    rw [Polynomial.eval_rectangleDifference_natCast (r + 1) a b h v N hh hv]
    have ht := bidegreeHypersurface_hilbertFunction_le_rectangleDifference
      ha hb hne hg hh hv
    simp only [Nat.card_eq_fintype_card, Fintype.card_fin] at ht
    exact_mod_cast ht

/-- Sharp mixed degree of a pulled-back plane hypersurface (one jet coordinate). -/
theorem bidegreeHypersurface_affineDegree_le_one
    {a b h v : ℕ} {g : MvPolynomial (Option (Fin 1)) F}
    (ha : 0 < a) (hb : 0 < b) (hne : g ≠ 0)
    (hproper : Ideal.span ({g} : Set (MvPolynomial (Option (Fin 1)) F)) ≠ ⊤)
    (hg : g ∈ restrictBidegree (F := F) (σ := Fin 1) h v) :
    affineDegree (bidegreeHypersurfaceIdeal a b g) ≤ (h * b + v * a : ℕ) := by
  have hdim : (hilbertPolynomial (bidegreeHypersurfaceIdeal a b g)).natDegree = 1 := by
    rw [bidegreeHypersurface_hilbertPolynomial_natDegree a b g ha hb hproper]
    have hs := hilbertPolynomial_span_singleton_natDegree_add_one hne hproper
    simp only [Nat.card_eq_fintype_card, Fintype.card_option, Fintype.card_fin] at hs
    omega
  apply (affineDegree_le_of_eventually_hilbertFunction_le hdim
    (Polynomial.rectangleDifferenceOne_natDegree_le a b h v)
    (Polynomial.rectangleDifferenceOne_coeff_one a b h v) ?_).trans_eq
  · push_cast
    ring
  · filter_upwards [eventually_ge_atTop (max h v)] with N hN
    have hh : h ≤ a * N := (le_max_left h v).trans hN |>.trans
      (Nat.le_mul_of_pos_left N ha)
    have hv : v ≤ b * N := (le_max_right h v).trans hN |>.trans
      (Nat.le_mul_of_pos_left N hb)
    rw [Polynomial.eval_rectangleDifferenceOne_natCast a b h v N hh hv]
    have ht := bidegreeHypersurface_hilbertFunction_le_rectangleDifference
      ha hb hne hg hh hv
    simp only [Nat.card_eq_fintype_card, Fintype.card_fin, Nat.choose_one_right] at ht
    exact_mod_cast ht

/-- Sharp mixed degree of a pulled-back three-variable hypersurface (two jet coordinates). -/
theorem bidegreeHypersurface_affineDegree_le_two
    {a b h v : ℕ} {g : MvPolynomial (Option (Fin 2)) F}
    (ha : 0 < a) (hb : 0 < b) (hne : g ≠ 0)
    (hproper : Ideal.span ({g} : Set (MvPolynomial (Option (Fin 2)) F)) ≠ ⊤)
    (hg : g ∈ restrictBidegree (F := F) (σ := Fin 2) h v) :
    affineDegree (bidegreeHypersurfaceIdeal a b g) ≤
      (h * b ^ 2 + 2 * v * a * b : ℕ) := by
  have hdim : (hilbertPolynomial (bidegreeHypersurfaceIdeal a b g)).natDegree = 2 := by
    rw [bidegreeHypersurface_hilbertPolynomial_natDegree a b g ha hb hproper]
    have hs := hilbertPolynomial_span_singleton_natDegree_add_one hne hproper
    simp only [Nat.card_eq_fintype_card, Fintype.card_option, Fintype.card_fin] at hs
    omega
  apply (affineDegree_le_of_eventually_hilbertFunction_le hdim
    (Polynomial.rectangleDifferenceTwo_natDegree_le a b h v)
    (Polynomial.rectangleDifferenceTwo_coeff_two a b h v) ?_).trans_eq
  · norm_num [Nat.factorial]
    ring
  · filter_upwards [eventually_ge_atTop (max h v)] with N hN
    have hh : h ≤ a * N := (le_max_left h v).trans hN |>.trans
      (Nat.le_mul_of_pos_left N ha)
    have hv : v ≤ b * N := (le_max_right h v).trans hN |>.trans
      (Nat.le_mul_of_pos_left N hb)
    rw [Polynomial.eval_rectangleDifferenceTwo_natCast a b h v N hh hv]
    have ht := bidegreeHypersurface_hilbertFunction_le_rectangleDifference
      ha hb hne hg hh hv
    simp only [Nat.card_eq_fintype_card, Fintype.card_fin] at ht
    exact_mod_cast ht

/-- For an equidimensional ideal, the sum of the degrees of its actual minimal
components is bounded by the degree of the ideal itself. -/
theorem sum_minimalPrimes_affineDegree_le_of_equidimensional [Finite σ]
    (I : Ideal (MvPolynomial σ F)) (d : ℕ)
    (hIdeg : (hilbertPolynomial I).natDegree = d)
    (hQdeg : ∀ Q ∈ minimalPrimesFinset I, (hilbertPolynomial Q).natDegree = d) :
    ∑ Q ∈ minimalPrimesFinset I, affineDegree Q ≤ affineDegree I := by
  classical
  let ι := I.minimalPrimes
  let _ : Fintype ι := (I.finite_minimalPrimes_of_isNoetherianRing _).fintype
  let Q : ι → Ideal (MvPolynomial σ F) := fun q ↦ q
  have hprime : ∀ q, (Q q).IsPrime := fun q ↦ q.property.isPrime
  have hinc : ∀ ⦃q r⦄, q ≠ r → ¬ Q q ≤ Q r := by
    intro q r hqr hle
    apply hqr
    apply Subtype.ext
    exact le_antisymm hle (r.property.2 q.property.1 hle)
  have hInf : (⨅ q, Q q) = I.radical := by
    rw [← Ideal.sInf_minimalPrimes, sInf_eq_iInf']
  have hqdeg' : ∀ q, (hilbertPolynomial (Q q)).natDegree ≤ d := by
    intro q
    exact le_of_eq (hQdeg q (mem_minimalPrimesFinset.mpr q.property))
  have hraddeg : (hilbertPolynomial I.radical).natDegree ≤ d := by
    rw [hilbertPolynomial_radical_natDegree, hIdeg]
  have hc := sum_hilbertPolynomial_coeff_le_iInf Q hprime hinc d hqdeg' (hInf ▸ hraddeg)
  rw [hInf] at hc
  have hrad : (hilbertPolynomial I.radical).coeff d ≤ (hilbertPolynomial I).coeff d := by
    apply coeff_le_of_natDegree_le_of_eventually_eval_nat_le hraddeg (le_of_eq hIdeg)
    filter_upwards [hilbertPolynomial_eventually_eval I.radical,
      hilbertPolynomial_eventually_eval I] with N hr hN
    rw [hr, hN]
    exact_mod_cast hilbertFunction_antitone Ideal.le_radical N
  calc
    ∑ R ∈ minimalPrimesFinset I, affineDegree R =
        (d.factorial : ℚ) * ∑ q : ι, (hilbertPolynomial (Q q)).coeff d := by
      rw [Finset.mul_sum]
      calc
        ∑ R ∈ minimalPrimesFinset I, affineDegree R = ∑ q : ι, affineDegree (Q q) := by
          exact Finset.sum_subtype (minimalPrimesFinset I)
            (fun _ ↦ mem_minimalPrimesFinset) _
        _ = _ := by
          apply Finset.sum_congr rfl
          intro q _
          have hqd := hQdeg q (mem_minimalPrimesFinset.mpr q.property)
          rw [affineDegree, hqd]
          congr 1
          rw [← hqd, Polynomial.coeff_natDegree]
    _ ≤ (d.factorial : ℚ) * (hilbertPolynomial I).coeff d :=
      mul_le_mul_of_nonneg_left (hc.trans hrad) (by positivity)
    _ = affineDegree I := by
      rw [affineDegree, hIdeg]
      congr 1
      rw [← hIdeg, Polynomial.coeff_natDegree]

/-- The minimal components of a bounded pulled-back hypersurface have total degree at most
the actual degree of the pulled-back ideal. -/
theorem bidegreeHypersurface_sum_minimalPrimes_affineDegree_le [Finite σ]
    {a b : ℕ} {g : MvPolynomial (Option σ) F}
    (ha : 0 < a) (hb : 0 < b) (hne : g ≠ 0)
    (hproper : Ideal.span ({g} : Set (MvPolynomial (Option σ) F)) ≠ ⊤)
    (hg : g ∈ restrictBidegree (F := F) (σ := σ) a b) :
    ∑ Q ∈ minimalPrimesFinset (bidegreeHypersurfaceIdeal a b g), affineDegree Q ≤
      affineDegree (bidegreeHypersurfaceIdeal a b g) := by
  let d := (hilbertPolynomial (Ideal.span {g})).natDegree
  have hJdeg : (hilbertPolynomial (bidegreeHypersurfaceIdeal a b g)).natDegree = d :=
    bidegreeHypersurface_hilbertPolynomial_natDegree a b g ha hb hproper
  have hbase := bidegreeIdeal_hilbertPolynomial_natDegree (F := F) (σ := σ) a b ha hb
  have hsource := hilbertPolynomial_span_singleton_natDegree_add_one hne hproper
  have hlift : bidegreeLift a b g hg ∉ bidegreeIdeal a b := by
    intro h
    change bidegreeMap a b (bidegreeLift a b g hg) = 0 at h
    rw [bidegreeMap_bidegreeLift] at h
    exact hne h
  apply sum_minimalPrimes_affineDegree_le_of_equidimensional
    (bidegreeHypersurfaceIdeal a b g) d hJdeg
  intro Q hQ
  have hQ' : Q ∈ (bidegreeIdeal a b ⊔ Ideal.span {bidegreeLift a b g hg}).minimalPrimes := by
    rw [← bidegreeHypersurfaceIdeal_eq_sup a b g hg ha hb]
    exact mem_minimalPrimesFinset.mp hQ
  have hpure := principalCut_component_hilbertPolynomial_natDegree_add_one
    (bidegreeIdeal_isPrime a b) hlift hQ'
  dsimp only [d]
  rw [hbase, ← hsource] at hpure
  omega

theorem bidegreeHypersurface_sum_minimalPrimes_affineDegree_le_one
    {a b h v : ℕ} {g : MvPolynomial (Option (Fin 1)) F}
    (ha : 0 < a) (hb : 0 < b) (hne : g ≠ 0)
    (hproper : Ideal.span ({g} : Set (MvPolynomial (Option (Fin 1)) F)) ≠ ⊤)
    (hg : g ∈ restrictBidegree (F := F) (σ := Fin 1) h v)
    (hgAB : g ∈ restrictBidegree (F := F) (σ := Fin 1) a b) :
    ∑ Q ∈ minimalPrimesFinset (bidegreeHypersurfaceIdeal a b g), affineDegree Q ≤
      (h * b + v * a : ℕ) :=
  (bidegreeHypersurface_sum_minimalPrimes_affineDegree_le ha hb hne hproper hgAB).trans
    (bidegreeHypersurface_affineDegree_le_one ha hb hne hproper hg)

theorem bidegreeHypersurface_sum_minimalPrimes_affineDegree_le_two
    {a b h v : ℕ} {g : MvPolynomial (Option (Fin 2)) F}
    (ha : 0 < a) (hb : 0 < b) (hne : g ≠ 0)
    (hproper : Ideal.span ({g} : Set (MvPolynomial (Option (Fin 2)) F)) ≠ ⊤)
    (hg : g ∈ restrictBidegree (F := F) (σ := Fin 2) h v)
    (hgAB : g ∈ restrictBidegree (F := F) (σ := Fin 2) a b) :
    ∑ Q ∈ minimalPrimesFinset (bidegreeHypersurfaceIdeal a b g), affineDegree Q ≤
      (h * b ^ 2 + 2 * v * a * b : ℕ) :=
  (bidegreeHypersurface_sum_minimalPrimes_affineDegree_le ha hb hne hproper hgAB).trans
    (bidegreeHypersurface_affineDegree_le_two ha hb hne hproper hg)

end AffineHilbert

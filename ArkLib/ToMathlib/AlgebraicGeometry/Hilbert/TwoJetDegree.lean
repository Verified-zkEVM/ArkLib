/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import ArkLib.ToMathlib.AlgebraicGeometry.Hilbert.DerivativeBidegree

/-!
# Degree of a curve in the two-jet monomial presentation

The coordinates have total degree at most `b` and derivative-variable degree at most `c`.
Their number is the truncated-triangle count `S(b,c)`. On a source curve of total degree
`j` and derivative degree `r`, quotienting the scaled coordinate space by the equation
leaves linear growth with coefficient `j*c+r*(b-c)`. This is the fiber-degree counterpart
of the joint challenge/jet degree bound.
-/

@[expose] public section

noncomputable section

namespace AffineHilbert

open MvPolynomial Polynomial Filter
open scoped BigOperators Topology

variable {F : Type*} [Field F]

/-- The two-jet polynomial space with a separate derivative-degree bound. -/
def restrictTwoJet (b c : ℕ) : Submodule F (MvPolynomial (Fin 2) F) :=
  restrictSupport F {m | m.degree ≤ b ∧ m 1 ≤ c}

theorem mem_restrictTwoJet {b c : ℕ} {P : MvPolynomial (Fin 2) F} :
    P ∈ restrictTwoJet (F := F) b c ↔ ∀ m ∈ P.support, m.degree ≤ b ∧ m 1 ≤ c := by
  rfl

theorem mul_mem_restrictTwoJet {b c b' c' : ℕ} {P Q : MvPolynomial (Fin 2) F}
    (hP : P ∈ restrictTwoJet (F := F) b c) (hQ : Q ∈ restrictTwoJet (F := F) b' c') :
    P * Q ∈ restrictTwoJet (F := F) (b+b') (c+c') := by
  classical
  rw [mem_restrictTwoJet] at hP hQ ⊢
  intro m hm
  obtain ⟨u, hu, v, hv, rfl⟩ := Finset.mem_add.mp (support_mul P Q hm)
  constructor
  · simpa [Finsupp.degree_eq_sum, Fin.sum_univ_two, Nat.add_assoc, Nat.add_left_comm,
      Nat.add_comm] using Nat.add_le_add (hP u hu).1 (hQ v hv).1
  · exact Nat.add_le_add (hP u hu).2 (hQ v hv).2

instance (b c : ℕ) : Module.Finite F (restrictTwoJet (F := F) b c) := by
  let S : Set (Fin 2 →₀ ℕ) := {m | m.degree ≤ b ∧ m 1 ≤ c}
  let _ : Finite S := (Finsupp.finite_of_degree_le b).subset (fun _ hm ↦ hm.1) |>.to_subtype
  exact Module.Finite.of_basis (basisRestrictSupport F S)

theorem finrank_restrictTwoJet (b c : ℕ) (hcb : c ≤ b) :
    Module.finrank F (restrictTwoJet (F := F) b c) = twoJetMonomialCount b c := by
  classical
  let S : Set (Fin 2 →₀ ℕ) := {m | m.degree ≤ b ∧ m 1 ≤ c}
  let _ : Fintype S := ((Finsupp.finite_of_degree_le b).subset (fun _ hm ↦ hm.1)).fintype
  change Module.finrank F (restrictSupport F S) = _
  rw [Module.finrank_eq_card_basis (basisRestrictSupport F S), ← Nat.card_eq_fintype_card]
  exact natCard_cappedTwoJetIndex b c hcb

/-- Evaluation at every monomial in the truncated two-jet triangle. -/
def twoJetMap (b c : ℕ) :
    MvPolynomial (CappedTwoJetIndex b c) F →ₐ[F] MvPolynomial (Fin 2) F :=
  MvPolynomial.aeval fun m ↦ MvPolynomial.monomial m.val 1

theorem twoJetMap_surjective (b c : ℕ) (hb : 0 < b) (hc : 0 < c) :
    Function.Surjective (twoJetMap (F := F) b c) := by
  intro P
  induction P using MvPolynomial.induction_on with
  | C d => exact ⟨MvPolynomial.C d, by simp [twoJetMap]⟩
  | add P Q hP hQ =>
    obtain ⟨P', rfl⟩ := hP
    obtain ⟨Q', rfl⟩ := hQ
    exact ⟨P'+Q', by simp⟩
  | mul_X P i hP =>
    obtain ⟨P', rfl⟩ := hP
    have hm : (Finsupp.single i 1 : Fin 2 →₀ ℕ).degree ≤ b ∧
        (Finsupp.single i 1 : Fin 2 →₀ ℕ) 1 ≤ c := by
      constructor
      · simpa using Nat.succ_le_of_lt hb
      · fin_cases i
        · simp
        · simpa using Nat.succ_le_of_lt hc
    refine ⟨P' * MvPolynomial.X (⟨Finsupp.single i 1, hm⟩ : CappedTwoJetIndex b c), ?_⟩
    simp only [map_mul, twoJetMap, MvPolynomial.aeval_X]
    rfl

/-- The linear coordinate lift of a source polynomial in the capped filtration. -/
def twoJetLift (b c : ℕ) (P : MvPolynomial (Fin 2) F)
    (hP : P ∈ restrictTwoJet (F := F) b c) :
    MvPolynomial (CappedTwoJetIndex b c) F :=
  ∑ m : P.support, MvPolynomial.C (MvPolynomial.coeff m.val P) *
    MvPolynomial.X (⟨m.val, (mem_restrictTwoJet.mp hP) m.val m.property⟩ :
      CappedTwoJetIndex b c)

theorem twoJetMap_twoJetLift
    (b c : ℕ) (P : MvPolynomial (Fin 2) F)
    (hP : P ∈ restrictTwoJet (F := F) b c) :
    twoJetMap b c (twoJetLift b c P hP) = P := by
  classical
  rw [twoJetLift, map_sum]
  simp only [map_mul, twoJetMap, MvPolynomial.aeval_C, algebraMap_eq,
    MvPolynomial.aeval_X]
  calc
    ∑ m : P.support, MvPolynomial.C (MvPolynomial.coeff m.val P) *
        MvPolynomial.monomial m.val 1 =
        ∑ m ∈ P.support, MvPolynomial.C (MvPolynomial.coeff m P) *
          MvPolynomial.monomial m 1 := by
            simpa using Finset.sum_attach P.support (fun m ↦
              MvPolynomial.C (MvPolynomial.coeff m P) * MvPolynomial.monomial m 1)
    _ = P := by simpa [monomial_eq] using P.as_sum.symm

theorem twoJetLift_totalDegree_le_one
    (b c : ℕ) (P : MvPolynomial (Fin 2) F)
    (hP : P ∈ restrictTwoJet (F := F) b c) :
    (twoJetLift b c P hP).totalDegree ≤ 1 := by
  classical
  rw [twoJetLift]
  apply MvPolynomial.totalDegree_finsetSum_le
  intro m hm
  exact (MvPolynomial.totalDegree_mul _ _).trans (by simp)

/-- The defining ideal of the capped embedding. -/
def twoJetIdeal (b c : ℕ) :
    Ideal (MvPolynomial (CappedTwoJetIndex b c) F) :=
  RingHom.ker (twoJetMap (F := F) b c).toRingHom

theorem twoJetIdeal_isPrime (b c : ℕ) :
    (twoJetIdeal (F := F) b c).IsPrime :=
  RingHom.ker_isPrime (twoJetMap b c).toRingHom

/-- The image of a capped source space in an affine quotient. -/
def quotientTwoJetLE
    (I : Ideal (MvPolynomial (Fin 2) F)) (b c : ℕ) :
    Submodule F (MvPolynomial (Fin 2) F ⧸ I) :=
  (restrictTwoJet (F := F) b c).map
    (Ideal.Quotient.mkₐ F I).toLinearMap

instance (I : Ideal (MvPolynomial (Fin 2) F)) (b c : ℕ) :
    Module.Finite F (quotientTwoJetLE I b c) := by
  unfold quotientTwoJetLE
  infer_instance

private def twoJetQuotientMap
    (I : Ideal (MvPolynomial (Fin 2) F)) (b c : ℕ) :
    restrictTwoJet (F := F) b c →ₗ[F]
      quotientTwoJetLE I b c :=
  ((Ideal.Quotient.mkₐ F I).toLinearMap.domRestrict
    (restrictTwoJet (F := F) b c)).codRestrict _ (fun p ↦
      ⟨p.val, ⟨p.property, rfl⟩⟩)

private theorem twoJetQuotientMap_surjective
    (I : Ideal (MvPolynomial (Fin 2) F)) (b c : ℕ) :
    Function.Surjective (twoJetQuotientMap I b c) := by
  rintro ⟨x, ⟨p, hp⟩⟩
  exact ⟨⟨p, hp.1⟩, Subtype.ext hp.2⟩

private def twoJetMulToBig
    {g : MvPolynomial (Fin 2) F} {j r B C : ℕ}
    (hg : g ∈ restrictTwoJet (F := F) j r)
    (hjB : j ≤ B) (hrC : r ≤ C) :
    restrictTwoJet (F := F) (B - j) (C - r) →ₗ[F]
      restrictTwoJet (F := F) B C :=
  ((LinearMap.mulLeft F g).domRestrict
    (restrictTwoJet (F := F) (B - j) (C - r))).codRestrict _
      (fun p ↦ by
        have hp := mul_mem_restrictTwoJet hg p.property
        change g * p.val ∈ restrictTwoJet (F := F) B C
        simpa only [Nat.add_sub_of_le hjB,
          Nat.add_sub_of_le hrC] using hp)

set_option maxHeartbeats 800000 in
-- The nested quotient and subtype maps require extra elaboration heartbeats.
theorem quotientTwoJetLE_finrank_add_le
    {g : MvPolynomial (Fin 2) F} {j r B C : ℕ}
    (hne : g ≠ 0) (hg : g ∈ restrictTwoJet (F := F) j r)
    (hjB : j ≤ B) (hrC : r ≤ C) :
    Module.finrank F (quotientTwoJetLE (Ideal.span {g}) B C) +
        Module.finrank F
          (restrictTwoJet (F := F) (B - j) (C - r)) ≤
      Module.finrank F (restrictTwoJet (F := F) B C) := by
  let cut := twoJetQuotientMap (Ideal.span {g}) B C
  let mulToKer :
      restrictTwoJet (F := F) (B - j) (C - r) →ₗ[F]
        LinearMap.ker cut :=
    (twoJetMulToBig hg hjB hrC).codRestrict _ (fun p ↦ by
      change cut (twoJetMulToBig hg hjB hrC p) = 0
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
      (restrictTwoJet (F := F) (B - j) (C - r)) ≤
      Module.finrank F (LinearMap.ker cut) :=
    LinearMap.finrank_le_finrank_of_injective hmul
  have hsurj : Function.Surjective cut := twoJetQuotientMap_surjective _ _ _
  have hrank := cut.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hsurj, finrank_top] at hrank
  omega

theorem quotientTwoJetLE_finrank_le
    {g : MvPolynomial (Fin 2) F} {j r B C : ℕ}
    (hCB : C ≤ B) (hshift : C - r ≤ B - j)
    (hne : g ≠ 0) (hg : g ∈ restrictTwoJet (F := F) j r)
    (hjB : j ≤ B) (hrC : r ≤ C) :
    Module.finrank F (quotientTwoJetLE (Ideal.span {g}) B C) ≤
      twoJetMonomialCount B C - twoJetMonomialCount (B - j) (C - r) := by
  have hbound := quotientTwoJetLE_finrank_add_le hne hg hjB hrC
  rw [finrank_restrictTwoJet B C hCB,
    finrank_restrictTwoJet (B - j) (C - r) hshift] at hbound
  omega


private theorem twoJetMap_weightedTotalDegree_le
    (b c : ℕ) (w : Fin 2 → ℕ) (d : ℕ)
    (hw : ∀ m : CappedTwoJetIndex b c, m.val.weight w ≤ d)
    (P : MvPolynomial (CappedTwoJetIndex b c) F) :
    (twoJetMap b c P).weightedTotalDegree w ≤ d * P.totalDegree := by
  classical
  apply (MvPolynomial.weightedTotalDegree_aeval_le_of_le
    (fun _ : CappedTwoJetIndex b c ↦ d) w
    (fun m ↦ MvPolynomial.monomial m.val 1) P ?_).trans
  · unfold MvPolynomial.weightedTotalDegree
    rw [Finset.sup_le_iff]
    intro m hm
    calc
      Finsupp.weight (fun _ : CappedTwoJetIndex b c ↦ d) m = d * m.degree := by
        rw [Finsupp.weight_apply, Finsupp.degree_eq_sum]
        simp only [Finsupp.sum, nsmul_eq_mul, Finset.mul_sum, Nat.mul_comm]
        rw [← Finsupp.sum_fintype m (fun _ n ↦ d * n) (by simp)]
        rfl
      _ ≤ d * P.totalDegree := Nat.mul_le_mul_left d (MvPolynomial.le_totalDegree hm)
  · intro m
    rw [MvPolynomial.weightedTotalDegree_monomial _ _ _ one_ne_zero]
    exact hw m


theorem twoJetMap_totalDegree_le (b c : ℕ)
    (P : MvPolynomial (CappedTwoJetIndex b c) F) :
    (twoJetMap b c P).totalDegree ≤ b * P.totalDegree := by
  rw [← weightedTotalDegree_one]
  exact twoJetMap_weightedTotalDegree_le b c 1 b
    (fun m ↦ by simpa [Finsupp.degree_eq_weight_one, Pi.one_def] using m.property.1) P

theorem twoJetMap_derivativeDegree_le (b c : ℕ)
    (P : MvPolynomial (CappedTwoJetIndex b c) F) :
    (twoJetMap b c P).degreeOf 1 ≤ c * P.totalDegree := by
  rw [← weightedTotalDegree_piSingle]
  exact twoJetMap_weightedTotalDegree_le b c (Pi.single 1 1) c
    (fun m ↦ by simpa [Finsupp.weight_single_one_apply] using m.property.2) P

theorem twoJetIdeal_hilbertPolynomial_natDegree
    (b c : ℕ) (hb : 0 < b) (hc : 0 < c) :
    (hilbertPolynomial (twoJetIdeal (F := F) b c)).natDegree = 2 := by
  let e₀ : (MvPolynomial (CappedTwoJetIndex b c) F ⧸
      twoJetIdeal b c) ≃ₐ[F] MvPolynomial (Fin 2) F :=
    Ideal.quotientKerAlgEquivOfSurjective
      (twoJetMap_surjective (F := F) b c hb hc)
  let e : (MvPolynomial (CappedTwoJetIndex b c) F ⧸
      twoJetIdeal b c) ≃ₐ[F]
      (MvPolynomial (Fin 2) F ⧸
        (⊥ : Ideal (MvPolynomial (Fin 2) F))) :=
    e₀.trans (AlgEquiv.quotientBot F _).symm
  have hcard : Nat.card (Fin 2) = 2 := by
    simp only [Nat.card_eq_fintype_card, Fintype.card_fin]
  rw [← hcard]
  rw [← hilbertPolynomial_bot_natDegree (F := F) (σ := Fin 2)]
  symm
  apply hilbertPolynomial_natDegree_eq_of_finite_injective_algHom
    e.toAlgHom e.injective (show (⊥ : Ideal (MvPolynomial (Fin 2) F)) ≠ ⊤ by
      exact bot_ne_top)
  let _ : Algebra (MvPolynomial (CappedTwoJetIndex b c) F ⧸
      twoJetIdeal b c)
      (MvPolynomial (Fin 2) F ⧸
        (⊥ : Ideal (MvPolynomial (Fin 2) F))) := e.toRingHom.toAlgebra
  exact Module.Finite.of_surjective (Algebra.linearMap _ _) e.surjective


def twoJetCutMap (b c : ℕ)
    (g : MvPolynomial (Fin 2) F) :
    MvPolynomial (CappedTwoJetIndex b c) F →ₐ[F]
      MvPolynomial (Fin 2) F ⧸ Ideal.span {g} :=
  (Ideal.Quotient.mkₐ F (Ideal.span {g})).comp (twoJetMap b c)

abbrev twoJetHypersurfaceIdeal (b c : ℕ)
    (g : MvPolynomial (Fin 2) F) :
    Ideal (MvPolynomial (CappedTwoJetIndex b c) F) :=
  RingHom.ker (twoJetCutMap b c g).toRingHom

theorem twoJetCutMap_surjective (b c : ℕ)
    (g : MvPolynomial (Fin 2) F)
    (hb : 0 < b) (hc : 0 < c) :
    Function.Surjective (twoJetCutMap b c g) :=
  Ideal.Quotient.mk_surjective.comp (twoJetMap_surjective b c hb hc)

theorem twoJetHypersurface_hilbertPolynomial_natDegree
    (b c : ℕ) (g : MvPolynomial (Fin 2) F)
    (hb : 0 < b) (hc : 0 < c)
    (hproper : Ideal.span ({g} : Set (MvPolynomial (Fin 2) F)) ≠ ⊤) :
    (hilbertPolynomial (twoJetHypersurfaceIdeal b c g)).natDegree =
      (hilbertPolynomial (Ideal.span {g})).natDegree := by
  let e₀ : (MvPolynomial (CappedTwoJetIndex b c) F ⧸
      twoJetHypersurfaceIdeal b c g) ≃ₐ[F]
      MvPolynomial (Fin 2) F ⧸ Ideal.span {g} :=
    Ideal.quotientKerAlgEquivOfSurjective
      (twoJetCutMap_surjective b c g hb hc)
  symm
  apply hilbertPolynomial_natDegree_eq_of_finite_injective_algHom
    e₀.toAlgHom e₀.injective hproper
  let _ : Algebra (MvPolynomial (CappedTwoJetIndex b c) F ⧸
      twoJetHypersurfaceIdeal b c g)
      (MvPolynomial (Fin 2) F ⧸ Ideal.span {g}) := e₀.toRingHom.toAlgebra
  exact Module.Finite.of_surjective (Algebra.linearMap _ _) e₀.surjective

theorem twoJetHypersurfaceIdeal_eq_sup
    (b c : ℕ) (g : MvPolynomial (Fin 2) F)
    (hg : g ∈ restrictTwoJet (F := F) b c)
    (hb : 0 < b) (hc : 0 < c) :
    twoJetHypersurfaceIdeal b c g =
      twoJetIdeal b c ⊔
        Ideal.span {twoJetLift b c g hg} := by
  apply le_antisymm
  · intro P hP
    change Ideal.Quotient.mk (Ideal.span {g}) (twoJetMap b c P) = 0 at hP
    rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton'] at hP
    obtain ⟨r, hr⟩ := hP
    obtain ⟨R, hR⟩ := twoJetMap_surjective (F := F) b c hb hc r
    rw [← hR] at hr
    have hk : P - R * twoJetLift b c g hg ∈
        twoJetIdeal b c := by
      change twoJetMap b c
        (P - R * twoJetLift b c g hg) = 0
      rw [map_sub, map_mul, twoJetMap_twoJetLift, hr, sub_self]
    have hl : R * twoJetLift b c g hg ∈
        Ideal.span {twoJetLift b c g hg} :=
      (Ideal.span {twoJetLift b c g hg}).mul_mem_left R
        (Ideal.subset_span (Set.mem_singleton _))
    rw [show P = (P - R * twoJetLift b c g hg) +
        R * twoJetLift b c g hg by ring]
    exact (twoJetIdeal b c ⊔
      Ideal.span {twoJetLift b c g hg}).add_mem
        (Ideal.mem_sup_left hk) (Ideal.mem_sup_right hl)
  · apply sup_le
    · intro P hP
      change Ideal.Quotient.mk (Ideal.span {g}) (twoJetMap b c P) = 0
      rw [Ideal.Quotient.eq_zero_iff_mem, show twoJetMap b c P = 0 from hP]
      exact Ideal.zero_mem _
    · rw [Ideal.span_le]
      intro P hP
      simp only [Set.mem_singleton_iff] at hP
      subst P
      change Ideal.Quotient.mk (Ideal.span {g})
        (twoJetMap b c (twoJetLift b c g hg)) = 0
      rw [twoJetMap_twoJetLift,
        Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.subset_span (Set.mem_singleton g)



/-- Ordinary degree in the monomial presentation pulls back into the scaled two-jet space. -/
theorem twoJetHypersurface_hilbertFunction_le
    (b c N : ℕ) (g : MvPolynomial (Fin 2) F) (hb : 0 < b) (hc : 0 < c) :
    hilbertFunction (twoJetHypersurfaceIdeal b c g) N ≤
      Module.finrank F (quotientTwoJetLE (Ideal.span {g}) (b * N) (c * N)) := by
  let e₀ : (MvPolynomial (CappedTwoJetIndex b c) F ⧸
      twoJetHypersurfaceIdeal b c g) ≃ₐ[F]
      MvPolynomial (Fin 2) F ⧸ Ideal.span {g} :=
    Ideal.quotientKerAlgEquivOfSurjective (twoJetCutMap_surjective b c g hb hc)
  let L : quotientDegreeLE (twoJetHypersurfaceIdeal b c g) N →ₗ[F]
      quotientTwoJetLE (Ideal.span {g}) (b * N) (c * N) :=
    (e₀.toLinearMap.domRestrict
      (quotientDegreeLE (twoJetHypersurfaceIdeal b c g) N)).codRestrict _
      (fun x ↦ by
        obtain ⟨P, hP, hPx⟩ := x.property
        have hdeg : P.totalDegree ≤ N := (MvPolynomial.mem_restrictTotalDegree _ _ P).mp hP
        have he : e₀ x = Ideal.Quotient.mk (Ideal.span {g}) (twoJetMap b c P) := by
          rw [← hPx]
          exact Ideal.quotientKerAlgEquivOfSurjective_mk (twoJetCutMap_surjective b c g hb hc) P
        change e₀ x ∈ quotientTwoJetLE (Ideal.span {g}) (b * N) (c * N)
        rw [he]
        refine ⟨twoJetMap b c P, ?_, rfl⟩
        change ∀ m ∈ (twoJetMap b c P).support, m.degree ≤ b * N ∧ m 1 ≤ c * N
        intro m hm
        exact ⟨(MvPolynomial.le_totalDegree hm).trans
          ((twoJetMap_totalDegree_le b c P).trans (Nat.mul_le_mul_left b hdeg)),
          (MvPolynomial.monomial_le_degreeOf 1 hm).trans
          ((twoJetMap_derivativeDegree_le b c P).trans (Nat.mul_le_mul_left c hdeg))⟩)
  rw [hilbertFunction]
  apply LinearMap.finrank_le_finrank_of_injective (f := L)
  intro x y hxy
  apply Subtype.ext
  have heq := congrArg Subtype.val hxy
  simp only [L, LinearMap.codRestrict_apply, LinearMap.domRestrict_apply] at heq
  exact e₀.injective heq

/-- The first difference of the scaled truncated-triangle count. -/
def twoJetDifference (b c j r : ℚ) : ℚ[X] :=
  Polynomial.C (j*c+r*(b-c)) * Polynomial.X +
    Polynomial.C (j+r/2+r^2/2-j*r)

theorem twoJetDifference_natDegree_le (b c j r : ℚ) :
    (twoJetDifference b c j r).natDegree ≤ 1 := by
  unfold twoJetDifference
  exact (natDegree_add_le _ _).trans (max_le
    (natDegree_mul_le.trans (by simp only [natDegree_C, natDegree_X, zero_add, le_refl]))
    (by simp only [natDegree_C, Nat.zero_le]))

@[simp] theorem twoJetDifference_coeff_one (b c j r : ℚ) :
    (twoJetDifference b c j r).coeff 1 = j*c+r*(b-c) := by
  simp [twoJetDifference]

theorem eval_twoJetDifference_natCast (b c j r N : ℕ)
    (hcb : c ≤ b) (hj : j ≤ b * N) (hr : r ≤ c * N)
    (hshift : c * N - r ≤ b * N - j) :
    (twoJetDifference b c j r).eval (N : ℚ) =
      ((twoJetMonomialCount (b*N) (c*N) -
        twoJetMonomialCount (b*N-j) (c*N-r) : ℕ) : ℚ) := by
  have hcap : c*N ≤ b*N := Nat.mul_le_mul_right N hcb
  have hcount := twoJetMonomialCount_mono hshift hcap (Nat.sub_le _ _) (Nat.sub_le _ _)
  rw [Nat.cast_sub hcount, cast_twoJetMonomialCount (b*N) (c*N) hcap,
    cast_twoJetMonomialCount (b*N-j) (c*N-r) hshift]
  push_cast [Nat.cast_sub hj, Nat.cast_sub hr]
  simp only [twoJetDifference, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X]
  ring

/-- Degree of a source curve in the truncated-triangle presentation. The disjunction handles
the full-triangle boundary by charging the redundant derivative bound its total degree. -/
theorem twoJetHypersurface_affineDegree_le_of_shift
    {b c j r : ℕ} {g : MvPolynomial (Fin 2) F}
    (hb : 0 < b) (hc : 0 < c) (hcb : c ≤ b) (hshiftcase : c < b ∨ r = j)
    (hne : g ≠ 0)
    (hproper : Ideal.span ({g} : Set (MvPolynomial (Fin 2) F)) ≠ ⊤)
    (hg : g ∈ restrictTwoJet (F := F) j r) :
    affineDegree (twoJetHypersurfaceIdeal b c g) ≤ fixedFiberDerivativeImageDegree j r b c := by
  have hdim : (hilbertPolynomial (twoJetHypersurfaceIdeal b c g)).natDegree = 1 := by
    rw [twoJetHypersurface_hilbertPolynomial_natDegree b c g hb hc hproper]
    have hs := hilbertPolynomial_span_singleton_natDegree_add_one hne hproper
    simp only [Nat.card_eq_fintype_card, Fintype.card_fin] at hs
    omega
  apply (affineDegree_le_of_eventually_hilbertFunction_le hdim
    (twoJetDifference_natDegree_le b c j r) (twoJetDifference_coeff_one b c j r) ?_).trans_eq
  · simp only [Nat.factorial_one, Nat.cast_one, one_mul, fixedFiberDerivativeImageDegree,
      Nat.cast_add, Nat.cast_mul, Nat.cast_sub hcb]
  · filter_upwards [eventually_ge_atTop (j+r+(j-r))] with N hN
    have hjN : j ≤ b*N := (show j ≤ N by omega).trans (Nat.le_mul_of_pos_left N hb)
    have hrN : r ≤ c*N := (show r ≤ N by omega).trans (Nat.le_mul_of_pos_left N hc)
    have hshift : c*N-r ≤ b*N-j := by
      rcases hshiftcase with hlt | rfl
      · have hgap : 0 < b-c := Nat.sub_pos_of_lt hlt
        have hjr : j-r ≤ (b-c)*N :=
          (show j-r ≤ N by omega).trans (Nat.le_mul_of_pos_left N hgap)
        have hdecomp : b*N = c*N+(b-c)*N := by
          rw [← Nat.add_mul, Nat.add_comm c, Nat.sub_add_cancel hcb]
        omega
      · exact Nat.sub_le_sub_right (Nat.mul_le_mul_right N hcb) r
    rw [eval_twoJetDifference_natCast b c j r N hcb hjN hrN hshift]
    exact_mod_cast (twoJetHypersurface_hilbertFunction_le b c N g hb hc).trans
      (quotientTwoJetLE_finrank_le (Nat.mul_le_mul_right N hcb) hshift hne hg hjN hrN)

/-- The bound includes the full-triangle boundary, even if the source derivative degree is
strictly smaller than its total degree. -/
theorem twoJetHypersurface_affineDegree_le
    {b c j r : ℕ} {g : MvPolynomial (Fin 2) F}
    (hb : 0 < b) (hc : 0 < c) (hcb : c ≤ b)
    (hne : g ≠ 0)
    (hproper : Ideal.span ({g} : Set (MvPolynomial (Fin 2) F)) ≠ ⊤)
    (hg : g ∈ restrictTwoJet (F := F) j r) :
    affineDegree (twoJetHypersurfaceIdeal b c g) ≤ fixedFiberDerivativeImageDegree j r b c := by
  by_cases hlt : c < b
  · exact twoJetHypersurface_affineDegree_le_of_shift hb hc hcb (Or.inl hlt) hne hproper hg
  · have hcb' : c = b := by omega
    subst c
    have hg' : g ∈ restrictTwoJet (F := F) j j := by
      rw [mem_restrictTwoJet] at hg ⊢
      intro m hm
      refine ⟨(hg m hm).1, ?_⟩
      have hdegree : m.degree = m 0 + m 1 := by
        simp [Finsupp.degree_eq_sum, Fin.sum_univ_two]
      have hd := (hg m hm).1
      omega
    simpa only [fixedFiberDerivativeImageDegree, Nat.sub_self, Nat.mul_zero, Nat.add_zero] using
      twoJetHypersurface_affineDegree_le_of_shift hb hc le_rfl (Or.inr rfl) hne hproper hg'

theorem twoJetHypersurface_sum_minimalPrimes_affineDegree_le
    {b c : ℕ} {g : MvPolynomial (Fin 2) F}
    (hb : 0 < b) (hc : 0 < c) (hne : g ≠ 0)
    (hproper : Ideal.span ({g} : Set (MvPolynomial (Fin 2) F)) ≠ ⊤)
    (hg : g ∈ restrictTwoJet (F := F) b c) :
    ∑ Q ∈ minimalPrimesFinset (twoJetHypersurfaceIdeal b c g),
        affineDegree Q ≤ affineDegree (twoJetHypersurfaceIdeal b c g) := by
  let d := (hilbertPolynomial (Ideal.span {g})).natDegree
  have hJdeg :
      (hilbertPolynomial (twoJetHypersurfaceIdeal b c g)).natDegree = d :=
    twoJetHypersurface_hilbertPolynomial_natDegree b c g hb hc hproper
  have hbase := twoJetIdeal_hilbertPolynomial_natDegree
    (F := F) b c hb hc
  have hsource := hilbertPolynomial_span_singleton_natDegree_add_one hne hproper
  simp only [Nat.card_eq_fintype_card, Fintype.card_fin] at hsource
  have hlift : twoJetLift b c g hg ∉ twoJetIdeal b c := by
    intro hmem
    change twoJetMap b c (twoJetLift b c g hg) = 0 at hmem
    rw [twoJetMap_twoJetLift] at hmem
    exact hne hmem
  apply sum_minimalPrimes_affineDegree_le_of_equidimensional
    (twoJetHypersurfaceIdeal b c g) d hJdeg
  intro Q hQ
  have hQ' : Q ∈ (twoJetIdeal b c ⊔
      Ideal.span {twoJetLift b c g hg}).minimalPrimes := by
    rw [← twoJetHypersurfaceIdeal_eq_sup b c g hg hb hc]
    exact mem_minimalPrimesFinset.mp hQ
  have hpure := principalCut_component_hilbertPolynomial_natDegree_add_one
    (twoJetIdeal_isPrime b c) hlift hQ'
  dsimp only [d]
  rw [hbase] at hpure
  omega


/-- The degrees of the actual irreducible curve components obey the same bound. -/
theorem twoJetHypersurface_sum_minimalPrimes_affineDegree_le_bound
    {b c j r : ℕ} {g : MvPolynomial (Fin 2) F}
    (hb : 0 < b) (hc : 0 < c) (hcb : c ≤ b)
    (hne : g ≠ 0)
    (hproper : Ideal.span ({g} : Set (MvPolynomial (Fin 2) F)) ≠ ⊤)
    (hg : g ∈ restrictTwoJet (F := F) j r)
    (hgbc : g ∈ restrictTwoJet (F := F) b c) :
    ∑ Q ∈ minimalPrimesFinset (twoJetHypersurfaceIdeal b c g),
      affineDegree Q ≤ fixedFiberDerivativeImageDegree j r b c :=
  (twoJetHypersurface_sum_minimalPrimes_affineDegree_le hb hc hne hproper hgbc).trans
    (twoJetHypersurface_affineDegree_le hb hc hcb hne hproper hg)

end AffineHilbert

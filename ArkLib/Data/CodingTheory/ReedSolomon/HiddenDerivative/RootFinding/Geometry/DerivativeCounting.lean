/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.Geometry.SharpCounting
public import
  ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.Symbolic.TaylorDerivativeDegree
public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Parameters.FirstOrder.StageCharges
public import ArkLib.ToMathlib.AlgebraicGeometry.Incidence.TwoJet
/-!
# Derivative-capped counting on the first-order Taylor chart

At source total degree `j` and first-derivative degree `r`, write
`b = 1 + τ * (j - 1)` for the common Taylor total-degree cap and
`c = min b (τ * (r - 1) + (K - 1))` for its actual derivative cap.  The truncated
two-jet presentation turns every fixed high cut and agreement cut into a linear equation.
Its curve degree is therefore `j*c + r*(b-c)`, including the full-triangle boundary `c=b`.
-/

@[expose] public section

open PolynomialDifferential

namespace ReedSolomon.HiddenDerivative

noncomputable section

open Polynomial MvPolynomial AffineHilbert

variable {F : Type*} [Field F]

private theorem degreeOf_map_le {σ : Type*} (f : F →+* F[X]) (P : MvPolynomial σ F)
    (i : σ) : (MvPolynomial.map f P).degreeOf i ≤ P.degreeOf i := by
  apply MvPolynomial.degreeOf_le_iff.mpr
  intro m hm
  exact MvPolynomial.monomial_le_degreeOf i
    (MvPolynomial.support_map_subset f P hm)

private theorem degreeOf_map_eval_le {σ : Type*} (z : F) (P : MvPolynomial σ F[X])
    (i : σ) :
    (MvPolynomial.map (Polynomial.evalRingHom z) P).degreeOf i ≤ P.degreeOf i := by
  apply MvPolynomial.degreeOf_le_iff.mpr
  intro m hm
  exact MvPolynomial.monomial_le_degreeOf i
    (MvPolynomial.support_map_subset (Polynomial.evalRingHom z) P hm)

theorem degreeOf_initialJetEquation_firstOrder_le
    (center : F) (Q : DifferentialPolynomial F 1) :
    (initialJetEquation center Q).degreeOf 1 ≤ Q.degreeOf (some 1) := by
  rw [← MvPolynomial.weightedTotalDegree_piSingle]
  apply le_trans (MvPolynomial.weightedTotalDegree_aeval_le_of_le
    (Pi.single (some (1 : Fin 2)) 1) (Pi.single (1 : Fin 2) 1) _ Q ?_)
  · rw [MvPolynomial.weightedTotalDegree_piSingle]
  · intro i
    cases i with
    | none => simp
    | some j => fin_cases j <;>
        simp [MvPolynomial.weightedTotalDegree_piSingle, MvPolynomial.degreeOf_X]

theorem degreeOf_initialJetSeparant_firstOrder_le
    (center : F) (Q : DifferentialPolynomial F 1) :
    (initialJetSeparant center Q).degreeOf 1 ≤ Q.degreeOf (some 1) - 1 := by
  rw [← MvPolynomial.weightedTotalDegree_piSingle]
  apply le_trans (MvPolynomial.weightedTotalDegree_aeval_le_of_le
    (Pi.single (some (1 : Fin 2)) 1) (Pi.single (1 : Fin 2) 1) _ _ ?_)
  · simpa [separant] using weightedTotalDegree_pderiv_le_sub
      (Pi.single (some (1 : Fin 2)) 1) (some (1 : Fin 2)) Q
  · intro i
    cases i with
    | none => simp
    | some j => fin_cases j <;>
        simp [MvPolynomial.weightedTotalDegree_piSingle, MvPolynomial.degreeOf_X]

theorem degreeOf_commonTaylorNumerator_firstOrder_le
    (center : F) (Q : DifferentialPolynomial F 1) (r K τ : ℕ)
    (hτ : TaylorExponentSufficient 1 K τ) (hr : 0 < r)
    (hdegree : Q.degreeOf (some 1) ≤ r) (l : Fin K) :
    (commonTaylorNumerator center Q K l (τ := τ)).degreeOf 1 ≤
      τ * (r - 1) + l.val := by
  let Qover : DifferentialPolynomial F[X] 1 := MvPolynomial.map Polynomial.C Q
  have hQover : Qover.degreeOf (some 1) ≤ r :=
    (degreeOf_map_le Polynomial.C Q (some 1)).trans hdegree
  have hover := degreeOf_commonTaylorNumeratorOver_firstOrder
    (Polynomial.C center) Qover r K τ hτ hr hQover l
  have hmap := degreeOf_map_eval_le (0 : F)
    (commonTaylorNumeratorOver (F := F) (Polynomial.C center) Qover K l (τ := τ)) 1
  have hQeval : MvPolynomial.map (Polynomial.evalRingHom (0 : F)) Qover = Q := by
    dsimp only [Qover]
    rw [MvPolynomial.map_map]
    have he : (Polynomial.evalRingHom (0 : F)).comp Polynomial.C = RingHom.id F := by
      ext x
      simp
    rw [he]
    exact MvPolynomial.map_id Q
  have hspec := eval_commonTaylorNumeratorOver center (0 : F) Qover K l τ
  rw [hQeval] at hspec
  rw [← hspec]
  exact hmap.trans hover

theorem degreeOf_taylorAgreementEquation_firstOrder_le
    (center : F) (Q : DifferentialPolynomial F 1) (r K τ : ℕ)
    (hτ : TaylorExponentSufficient 1 K τ) (hr : 0 < r)
    (hdegree : Q.degreeOf (some 1) ≤ r) (x y : F) :
    (taylorAgreementEquation center Q K x y (τ := τ)).degreeOf 1 ≤
      τ * (r - 1) + (K - 1) := by
  apply (degreeOf_sub_le _ _ _).trans
  apply max_le
  · apply (degreeOf_sum_le _ _ _).trans
    apply Finset.sup_le
    intro l _
    apply (degreeOf_mul_le _ _ _).trans
    rw [degreeOf_C, zero_add]
    exact (degreeOf_commonTaylorNumerator_firstOrder_le
      center Q r K τ hτ hr hdegree l).trans (Nat.add_le_add_left (by omega) _)
  · apply (degreeOf_mul_le _ _ _).trans
    rw [degreeOf_C, zero_add]
    exact ((degreeOf_pow_le _ _ _).trans (Nat.mul_le_mul_left _
      ((degreeOf_initialJetSeparant_firstOrder_le center Q).trans
        (Nat.sub_le_sub_right hdegree 1)))).trans (Nat.le_add_right _ _)

private theorem mem_restrictTwoJet_of_bounds (P : MvPolynomial (Fin 2) F)
    {b c : ℕ} (hb : P.totalDegree ≤ b) (hc : P.degreeOf 1 ≤ c) :
    P ∈ restrictTwoJet (F := F) b c := by
  rw [mem_restrictTwoJet]
  intro m hm
  exact ⟨(le_totalDegree hm).trans hb, (monomial_le_degreeOf 1 hm).trans hc⟩

private theorem totalJetDegree_pos_of_initialSeparant_ne_zero (center : F)
    (Q : DifferentialPolynomial F 1) (hsep : initialJetSeparant center Q ≠ 0) :
    0 < Q.weightedTotalDegree (fun i ↦ i.elim (0 : ℕ) (fun _ ↦ 1)) := by
  by_contra! h
  have hdeg : (initialJetEquation center Q).totalDegree = 0 :=
    Nat.eq_zero_of_le_zero ((totalDegree_initialJetEquation_le center Q).trans h)
  have hC := totalDegree_eq_zero_iff_eq_C.mp hdeg
  have hd := pderiv_initialJetEquation center Q (Fin.last 1)
  rw [hC, pderiv_C] at hd
  exact hsep hd.symm

/-- Finite regular first-order chart points obey the fixed-fiber derivative-capped degree
`j*c+r*(b-c)` and the sharp coefficient-space ratio. -/
theorem finite_regularHighCutJets_card_le_derivativeCapped_of_exponent
    [IsAlgClosed F]
    (center : F) (Q : DifferentialPolynomial F 1) (K k j r τ : ℕ)
    (hτ : TaylorExponentSufficient 1 K τ) (hτpos : 0 < τ) (hK : 1 < K)
    (hsep : initialJetSeparant center Q ≠ 0) (hj : 0 < j) (hr : 0 < r)
    (hrj : r ≤ j)
    (hjet : Q.weightedTotalDegree (fun i ↦ i.elim 0 (fun _ ↦ 1)) ≤ j)
    (hderiv : Q.degreeOf (some 1) ≤ r)
    {n A : ℕ} (domain : Fin n ↪ F) (received : Fin n → F)
    (hk : 0 < k) (hkA : k ≤ A) (hAn : A ≤ n)
    (S : Finset (Fin 2 → F))
    (hS : ∀ jet ∈ S,
      aeval jet (initialJetEquation center Q) = 0 ∧
      aeval jet (initialJetSeparant center Q) ≠ 0 ∧
      ∀ l : {l : Fin K // k ≤ l.val},
        aeval jet (commonTaylorNumerator center Q K l.val (τ := τ)) = 0)
    (hA : ∀ jet ∈ S, A ≤ (agreementIndices
      (fun i ↦ taylorAgreementEquation center Q K (domain i) (received i) (τ := τ))
        jet).card) :
    (S.card : ℚ) ≤ firstOrderCurveFiberStageOne K j r τ *
      (((n - k + 1 : ℕ) : ℚ) / ((A - k + 1 : ℕ) : ℚ)) := by
  classical
  by_cases hempty : S = ∅
  · subst S
    simp only [Finset.card_empty, Nat.cast_zero]
    positivity
  let b := firstOrderTaylorTotalCap j τ
  let c := firstOrderTaylorDerivativeCap K j r τ
  let g := initialJetEquation center Q
  let s := initialJetSeparant center Q
  let highCuts := highTaylorCutList center Q K k (τ := τ)
  let cuts : Fin n → MvPolynomial (Fin 2) F := fun i ↦
    taylorAgreementEquation center Q K (domain i) (received i) (τ := τ)
  have hb : 0 < b := by simp [b, firstOrderTaylorTotalCap]
  have hc : 0 < c := by
    simp only [c, firstOrderTaylorDerivativeCap]
    apply lt_min hb
    have : 0 < K - 1 := by omega
    omega
  have hcb : c ≤ b := min_le_left _ _
  have hjb : j ≤ b := by
    simp only [b, firstOrderTaylorTotalCap]
    calc
      j = 1 + (j - 1) := by omega
      _ ≤ 1 + τ * (j - 1) := Nat.add_le_add_left
        (Nat.le_mul_of_pos_left (j - 1) hτpos) 1
  have hrc : r ≤ c := by
    apply le_min
    · exact hrj.trans hjb
    · calc
        r = 1 + (r - 1) := by omega
        _ ≤ (K - 1) + τ * (r - 1) := Nat.add_le_add
          (by omega) (Nat.le_mul_of_pos_left (r - 1) hτpos)
        _ = τ * (r - 1) + (K - 1) := by omega
  have hg0 : g ≠ 0 := initialJetEquation_ne_zero_of_separant_ne_zero center Q hsep
  have hvQ := totalJetDegree_pos_of_initialSeparant_ne_zero center Q hsep
  obtain ⟨x₀, hx₀⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
  have hproper : Ideal.span ({g} : Set (MvPolynomial (Fin 2) F)) ≠ ⊤ := by
    intro htop
    have hunit : IsUnit g := Ideal.span_singleton_eq_top.mp htop
    have heval : IsUnit (MvPolynomial.aeval x₀ g) := hunit.map (MvPolynomial.aeval x₀)
    rw [(hS x₀ hx₀).1] at heval
    exact not_isUnit_zero heval
  have hg : g ∈ restrictTwoJet (F := F) j r := mem_restrictTwoJet_of_bounds g
    ((totalDegree_initialJetEquation_le center Q).trans hjet)
    ((degreeOf_initialJetEquation_firstOrder_le center Q).trans hderiv)
  have hgbc : g ∈ restrictTwoJet (F := F) b c := mem_restrictTwoJet_of_bounds g
    ((totalDegree_initialJetEquation_le center Q).trans (hjet.trans hjb))
    ((degreeOf_initialJetEquation_firstOrder_le center Q).trans (hderiv.trans hrc))
  have hsbc : s ∈ restrictTwoJet (F := F) b c := mem_restrictTwoJet_of_bounds s
    ((totalDegree_initialJetSeparant_le center Q).trans
      ((Nat.sub_le_sub_right hjet 1).trans (by omega)))
    ((degreeOf_initialJetSeparant_firstOrder_le center Q).trans
      ((Nat.sub_le_sub_right hderiv 1).trans (by omega)))
  have hchartTotal :
      1 + τ * (Q.weightedTotalDegree (fun i ↦ i.elim 0 (fun _ ↦ 1)) - 1) ≤ b := by
    simp only [b, firstOrderTaylorTotalCap]
    gcongr
  have hhigh : ∀ f ∈ highCuts, f ∈ restrictTwoJet (F := F) b c := by
    intro f hf
    simp only [highCuts, highTaylorCutList, List.mem_map, Finset.mem_toList] at hf
    obtain ⟨l, _, rfl⟩ := hf
    apply mem_restrictTwoJet_of_bounds
    · exact (totalDegree_commonTaylorNumerator_le_of_exponent
        center Q hvQ K τ hτ l.val).trans hchartTotal
    · apply le_min
      · exact (degreeOf_le_totalDegree _ _).trans
          ((totalDegree_commonTaylorNumerator_le_of_exponent
            center Q hvQ K τ hτ l.val).trans hchartTotal)
      · exact (degreeOf_commonTaylorNumerator_firstOrder_le
          center Q r K τ hτ hr hderiv l.val).trans (Nat.add_le_add_left (by omega) _)
  have hcuts : ∀ i, cuts i ∈ restrictTwoJet (F := F) b c := by
    intro i
    apply mem_restrictTwoJet_of_bounds
    · exact (totalDegree_taylorAgreementEquation_le_of_exponent
        center Q hvQ K τ hτ _ _).trans hchartTotal
    · apply le_min
      · exact (degreeOf_le_totalDegree _ _).trans
          ((totalDegree_taylorAgreementEquation_le_of_exponent
            center Q hvQ K τ hτ _ _).trans hchartTotal)
      · exact degreeOf_taylorAgreementEquation_firstOrder_le
          center Q r K τ hτ hr hderiv _ _
  refine twoJetHypersurface_source_incidence_sharp hb hc hcb hk hkA hAn
    g s hg0 hproper hg hgbc hsbc highCuts hhigh cuts hcuts S ?_ hA ?_
  · intro x hx
    refine ⟨(hS x hx).1, (hS x hx).2.1, ?_⟩
    intro f hf
    simp only [highCuts, highTaylorCutList, List.mem_map, Finset.mem_toList] at hf
    obtain ⟨l, _, rfl⟩ := hf
    exact (hS x hx).2.2 l
  · intro J hJ hsJ hgJ hhighJ U hU x y hxJ hxs hyJ hys hzero
    have hhighIdeal := highTaylorCutsIdeal_le_of_highTaylorCutList_le
      center Q K k (τ := τ) (fun f hf ↦ hhighJ f (by simpa only [highCuts] using hf))
    exact eq_of_mem_principalOpen_of_highCuts_of_agreementFinset_of_exponent
      center Q K k τ hτ hK J hhighIdeal domain received U hU
        ⟨hxJ, hxs⟩ ⟨hyJ, hys⟩ (fun i hi ↦ (hzero i hi).1)
          (fun i hi ↦ (hzero i hi).2)

end

end ReedSolomon.HiddenDerivative

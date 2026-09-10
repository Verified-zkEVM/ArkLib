/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.Ordinary.Frobenius.Incidence
public import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.Ordinary.Frobenius.RetainedFamily
public import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.Ordinary.Frobenius.WitnessEmbedding
public import
ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.Symbolic.RegularEquation
public import ArkLib.ToMathlib.MvPolynomial.FrobeniusPullback
/-!
# The regular ordinary Frobenius incidence bound

Actual regular solutions give source points. Retained pairs account for at most `n-k`
accidental challenges each in the original coordinate, and the remaining witnesses obey
the mixed source incidence bound.
-/

@[expose] public section

noncomputable section

namespace ReedSolomon

open Polynomial MvPolynomial PolynomialDifferential HiddenDerivative AffineHilbert

variable {F E : Type*} [Field F] [Field E] {n k K : ℕ}

open Classical in
/-- A finite family of actual regular bad witnesses satisfies the ordinary mixed bound.
The polynomial root degree, rather than the Frobenius exponent, controls retained pairs. -/
theorem finite_frobeniusRegularBadWitnesses_card_le [IsAlgClosed E]
    (domain : Fin n ↪ F) (f g : Fin n → F) (ι : F →+* E)
    (roots : Fin n → E) (center : E) (Q : DifferentialPolynomial E[X] 0)
    (p e τ h b A : ℕ) [ExpChar E p]
    (hroots : ∀ i, roots i ^ (p ^ e) = ι (domain i))
    (hK : 0 < K) (hKk : K ≤ p ^ e * k) (hτ : TaylorExponentSufficient 0 K τ)
    (hτpos : 0 < τ) (hb : 0 < b) (hkA : k ≤ A) (hAn : A ≤ n)
    (hheight : ChallengeHeightLE Q h)
    (hjet : Q.weightedTotalDegree (fun i ↦ i.elim 0 (fun _ ↦ 1)) ≤ b)
    (hinit : symbolicSourceInitialEquation center Q ≠ 0)
    (hproper : Ideal.span ({symbolicSourceInitialEquation center Q} :
      Set (MvPolynomial (Option (Fin 1)) E)) ≠ ⊤)
    (challenges : Finset E) (witness : E → E[X])
    (hdegree : ∀ w ∈ challenges, (expand E (p ^ e) (witness w)).degree < K)
    (hsol : ∀ w ∈ challenges, differentialSpecialization (challengeSpecialization Q w)
      (expand E (p ^ e) (witness w)) = 0)
    (hsep : ∀ w ∈ challenges,
      jetEvaluation (separant (challengeSpecialization Q w) (Fin.last 0)) center
        (polynomialJet center (expand E (p ^ e) (witness w))) ≠ 0)
    (hagree : ∀ w ∈ challenges, A ≤
      (polynomialAgreementSet (mappedDomain domain ι)
        (fun i ↦ ι (f i) + w ^ (p ^ e) * ι (g i)) (witness w)).card)
    (hbad : ∀ w ∈ challenges,
      ¬HasExactCorrelatedPair domain f g ι k (w ^ (p ^ e)) (witness w)) :
    (challenges.card : ℚ) ≤
      (h * (1 + τ * (b - 1)) + b * (p ^ e + τ * h) : ℕ) *
        (((n - k + 1 : ℕ) : ℚ) / ((A - k + 1 : ℕ) : ℚ)) +
      ((n - k) * b : ℕ) := by
  classical
  let pairs := frobeniusRetainedPairFamily domain f g ι roots center Q K k τ (p ^ e)
  obtain ⟨exceptional, hexc, hexact⟩ := exists_exceptional_frobeniusRetainedPairFamily
    domain f g ι roots center Q K k τ (p ^ e)
  let discarded := challenges.filter (fun w ↦ w ^ (p ^ e) ∈ exceptional)
  let remaining := challenges.filter (fun w ↦ w ^ (p ^ e) ∉ exceptional)
  let point : E → Option (Fin 1) → E := fun w ↦
    symbolicWitnessPoint center w (expand E (p ^ e) (witness w))
  have hpointinj : Function.Injective point := by
    intro w v heq
    exact congrFun heq none
  have hchart (w : E) (hw : w ∈ challenges) :=
    symbolicFrobeniusWitness_equations Q center w (witness w) p e K τ hτ
      (hdegree w hw) (hsol w hw) (hsep w hw)
  have hoff (w : E) (hw : w ∈ remaining) :
      point w ∉ sourceFrobeniusGraphLocus domain f g ι roots center Q K k τ (p ^ e) := by
    obtain ⟨hwc, hwe⟩ := Finset.mem_filter.mp hw
    rintro ⟨F₀, G₀, hP, heq⟩
    have hjetEq : polynomialJet center (expand E (p ^ e) (witness w)) =
        fun j ↦ (frobeniusInitialGraph center (p ^ e) (F₀.map ι) (G₀.map ι) j).eval w := by
      funext j
      exact congrFun heq (some j)
    have hregular : (polynomialGraphPullback
        (frobeniusInitialGraph center (p ^ e) (F₀.map ι) (G₀.map ι))
        (symbolicSourceSeparant center Q)).eval w ≠ 0 := by
      change point w = polynomialGraphPoint
        (frobeniusInitialGraph center (p ^ e) (F₀.map ι) (G₀.map ι)) w at heq
      rw [eval_polynomialGraphPullback, ← heq]
      exact (hchart w hwc).2.1
    have hrec := hP.specialize hroots hK hKk hτ w hregular
    have hwitness : witness w = F₀.map ι + Polynomial.C (w ^ (p ^ e)) * G₀.map ι := by
      apply Polynomial.expand_injective (pow_pos (expChar_pos E p) e)
      rw [← symbolicFrobeniusWitness_reconstruction Q center w (witness w) p e K
        (hdegree w hwc) (hsol w hwc) (hchart w hwc).2.1, hjetEq]
      exact hrec
    have hPmem : (F₀, G₀) ∈ pairs :=
      (mem_frobeniusRetainedPairFamily_iff domain f g ι roots center Q K k τ
        (p ^ e) (F₀, G₀)).mpr hP
    apply hbad w hwc
    refine ⟨(F₀, G₀), hP.degree_left, hP.degree_right, hwitness, ?_⟩
    rw [hwitness]
    exact hexact _ hPmem _ hwe
  have hoffbound : (remaining.card : ℚ) ≤
      (h * (1 + τ * (b - 1)) + b * (p ^ e + τ * h) : ℕ) *
        (((n - k + 1 : ℕ) : ℚ) / ((A - k + 1 : ℕ) : ℚ)) := by
    rw [← Finset.card_image_of_injective remaining hpointinj]
    apply finite_sourceFrobenius_points_off_graphs_card_le domain f g ι p e roots
      hroots center Q hK hKk τ h b A hτ hτpos hb hkA hAn hheight hjet hinit hproper
      (remaining.image point)
    · intro x hx
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hx
      have hwc := (Finset.mem_filter.mp hw).1
      refine ⟨(hchart w hwc).1, (hchart w hwc).2.1, ?_, hoff w hw⟩
      intro q hq
      simp only [sourceFrobeniusSparseCuts, List.mem_map, Finset.mem_toList,
        Finset.mem_filter, Finset.mem_univ, true_and] at hq
      obtain ⟨l, hl, rfl⟩ := hq
      exact (hchart w hwc).2.2.1 l hl
    · intro x hx
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hx
      have hwc := (Finset.mem_filter.mp hw).1
      apply (hagree w hwc).trans
      apply Finset.card_le_card
      intro i hi
      rw [mem_agreementIndices]
      apply ((hchart w hwc).2.2.2 (roots i) (ι (f i)) (ι (g i))).mpr
      rw [hroots]
      exact (Finset.mem_filter.mp hi).2
  have hdiscarded : discarded.card ≤ exceptional.card :=
    Finset.card_le_card_of_injOn (fun w ↦ w ^ (p ^ e))
      (fun _ hw ↦ (Finset.mem_filter.mp hw).2)
      (MvPolynomial.pow_primePow_injective (K := E) p e).injOn
  have hpaircount : pairs.card ≤ b := by
    apply (frobeniusRetainedPairFamily_card_le domain f g ι roots center Q p e τ
      hroots hK hKk hτ hinit).trans
    have hsupport := symbolicSourceInitialEquation_mem_restrictBidegree center Q h b
      hheight hjet
    rw [mem_restrictBidegree] at hsupport
    apply degreeOf_le_iff.mpr
    intro u hu
    exact (Finsupp.le_weight jetWeight (by decide) u).trans (hsupport u hu).2
  have hexcbound : discarded.card ≤ (n - k) * b :=
    hdiscarded.trans (hexc.trans (Nat.mul_le_mul_left _ hpaircount))
  have hcover : discarded.card + remaining.card = challenges.card :=
    Finset.card_filter_add_card_filter_not (fun w ↦ w ^ (p ^ e) ∈ exceptional)
  have hcoverQ : (challenges.card : ℚ) = discarded.card + remaining.card := by
    exact_mod_cast hcover.symm
  rw [hcoverQ]
  have hdQ : (discarded.card : ℚ) ≤ ((n - k) * b : ℕ) := by exact_mod_cast hexcbound
  linarith

end ReedSolomon

/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.Ordinary.PolynomialCurve.Admissible
public import
ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.PolynomialCurve.SharpRegularEquation
public import ArkLib.ToMathlib.AlgebraicGeometry.Incidence.BidegreeExcluded
/-!
# Incidence for sparse Frobenius power curves

The sparse numerator and received-curve agreement cuts satisfy the same source incidence theorem
as the ordinary line.  The pulled challenge degree is `p ^ e * ℓ`, so the resulting estimate is
linear in the polynomial-curve degree while retaining the original interpolation threshold `k`.
-/

@[expose] public section

noncomputable section

namespace ReedSolomon

open Polynomial MvPolynomial PolynomialDifferential HiddenDerivative AffineHilbert

variable {F E : Type*} [Field F] [Field E] {n k K ℓ : ℕ}

/-- The actual sparse Taylor numerator equations. -/
def sourceFrobeniusPowerSparseCuts (center : E) (Q : DifferentialPolynomial E[X] 0)
    (K τ s : ℕ) : List (MvPolynomial (Option (Fin 1)) E) :=
  ((Finset.univ : Finset (Fin K)).filter (fun l ↦ ¬s ∣ l.val)).toList.map
    (fun l ↦ symbolicSourceNumerator center Q K l (τ := τ))

/-- The union of retained admissible original-degree tuple graphs. -/
def sourceFrobeniusPowerGraphLocus
    (domain : Fin n ↪ F) (values : Fin (ℓ + 1) → Fin n → F)
    (ι : F →+* E) (roots : Fin n → E) (center : E)
    (Q : DifferentialPolynomial E[X] 0) (K k τ s : ℕ) : Set (Option (Fin 1) → E) :=
  {x | ∃ P : Fin (ℓ + 1) → F[X],
    IsAdmissibleFrobeniusPowerTuple domain values ι roots center Q K k τ s P ∧
    x = polynomialGraphPoint
      (frobeniusPowerInitialGraph center s (fun t ↦ (P t).map ι)) (x none)}

/-- A pulled power-curve agreement cut has challenge degree `s * ℓ + τ * h`. -/
theorem symbolicSourceFrobeniusPowerAgreement_mem_restrictBidegree
    (center alpha : E) (values : Fin (ℓ + 1) → E)
    (Q : DifferentialPolynomial E[X] 0)
    (s h b K τ : ℕ) (hτ : TaylorExponentSufficient 0 K τ) (hb : 0 < b)
    (hheight : ChallengeHeightLE Q h)
    (hjet : Q.weightedTotalDegree (fun i ↦ i.elim 0 (fun _ ↦ 1)) ≤ b) :
    symbolicSourceFrobeniusPowerAgreement center Q K τ s alpha values ∈
      restrictBidegree (F := E) (s * ℓ + τ * h) (1 + τ * (b - 1)) := by
  apply taylorAgreementEquationOver_mem_restrictBidegree_of_exponent
    center alpha (frobeniusPowerCoordinate s values) Q (s * ℓ) h b K τ hτ _ hb
      hheight hjet
  exact frobeniusPowerCoordinate_natDegree_le s values

/-- Every positive-dimensional regular prime containing `k` curve cuts lies in a recognized
original-degree Frobenius tuple graph. -/
theorem principalOpen_subset_sourceFrobeniusPowerGraphLocus [IsAlgClosed E]
    (domain : Fin n ↪ F) (values : Fin (ℓ + 1) → Fin n → F) (ι : F →+* E)
    (p e : ℕ) [ExpChar E p] (roots : Fin n → E)
    (hroots : ∀ i, roots i ^ (p ^ e) = ι (domain i))
    (center : E) (Q : DifferentialPolynomial E[X] 0)
    (hK : 0 < K) (hKk : K ≤ p ^ e * k) (τ : ℕ)
    (hτ : TaylorExponentSufficient 0 K τ)
    (I : Ideal (MvPolynomial (Option (Fin 1)) E)) (hI : I.IsPrime)
    (hs : symbolicSourceSeparant center Q ∉ I)
    (hinit : symbolicSourceInitialEquation center Q ∈ I)
    (hsparse : ∀ q ∈ sourceFrobeniusPowerSparseCuts center Q K τ (p ^ e), q ∈ I)
    (hd : 0 < (hilbertPolynomial I).natDegree)
    (hcuts : k ≤ (cutsInIdeal I (fun i ↦
      symbolicSourceFrobeniusPowerAgreement center Q K τ (p ^ e)
        (roots i) (fun t ↦ ι (values t i)))).card) :
    principalOpenZeroLocus I (symbolicSourceSeparant center Q) ⊆
      sourceFrobeniusPowerGraphLocus
        domain values ι roots center Q K k τ (p ^ e) := by
  classical
  obtain ⟨sample, hsub, hcard⟩ := Finset.exists_subset_card_eq hcuts
  obtain ⟨P, htuple, hgraph⟩ :=
    exists_admissibleFrobeniusPowerTuple_of_symbolic_prime_sample
      domain values sample hcard ι p e roots hroots center Q hK hKk τ hτ
      I hI hs hinit hd
      (fun l hl ↦ hsparse _ (by
        simp only [sourceFrobeniusPowerSparseCuts, List.mem_map, Finset.mem_toList,
          Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨l, hl, rfl⟩))
      (fun i hi ↦ mem_cutsInIdeal.mp (hsub hi))
  intro x hx
  exact ⟨P, htuple, hgraph x hx⟩

/-- Mixed source incidence away from all recognized tuple graphs.  The curve degree occurs only
in the linear pulled challenge degree `p ^ e * ℓ`. -/
theorem finite_sourceFrobeniusPower_points_off_graphs_card_le [IsAlgClosed E]
    (domain : Fin n ↪ F) (values : Fin (ℓ + 1) → Fin n → F) (ι : F →+* E)
    (p e : ℕ) [ExpChar E p] (roots : Fin n → E)
    (hroots : ∀ i, roots i ^ (p ^ e) = ι (domain i))
    (center : E) (Q : DifferentialPolynomial E[X] 0)
    (hK : 0 < K) (hKk : K ≤ p ^ e * k) (τ h b A : ℕ)
    (hτ : TaylorExponentSufficient 0 K τ) (hτpos : 0 < τ) (hℓ : 0 < ℓ)
    (hb : 0 < b) (hkA : k ≤ A) (hAn : A ≤ n)
    (hheight : ChallengeHeightLE Q h)
    (hjet : Q.weightedTotalDegree (fun i ↦ i.elim 0 (fun _ ↦ 1)) ≤ b)
    (hinit : symbolicSourceInitialEquation center Q ≠ 0)
    (hproper : Ideal.span ({symbolicSourceInitialEquation center Q} :
      Set (MvPolynomial (Option (Fin 1)) E)) ≠ ⊤)
    (S : Finset (Option (Fin 1) → E))
    (hS : ∀ x ∈ S,
      aeval x (symbolicSourceInitialEquation center Q) = 0 ∧
      aeval x (symbolicSourceSeparant center Q) ≠ 0 ∧
      (∀ q ∈ sourceFrobeniusPowerSparseCuts center Q K τ (p ^ e), aeval x q = 0) ∧
      x ∉ sourceFrobeniusPowerGraphLocus
        domain values ι roots center Q K k τ (p ^ e))
    (hA : ∀ x ∈ S, A ≤ (agreementIndices (fun i ↦
      symbolicSourceFrobeniusPowerAgreement center Q K τ (p ^ e)
        (roots i) (fun t ↦ ι (values t i))) x).card) :
    (S.card : ℚ) ≤
      (h * (1 + τ * (b - 1)) + b * (p ^ e * ℓ + τ * h) : ℕ) *
        (((n - k + 1 : ℕ) : ℚ) / ((A - k + 1 : ℕ) : ℚ)) := by
  classical
  have hp : 0 < p ^ e := pow_pos (expChar_pos E p) e
  apply bidegreeHypersurface_source_incidence_off_excluded_sharp_one
    (a := p ^ e * ℓ + τ * h) (b := 1 + τ * (b - 1))
    (h := h) (v := b) (L := k) (by positivity) (by omega) hkA hAn
    (symbolicSourceInitialEquation center Q) (symbolicSourceSeparant center Q)
    hinit hproper
    (symbolicSourceInitialEquation_mem_restrictBidegree center Q h b hheight hjet)
    (symbolicSourceInitialEquation_mem_sourceCurveCutBidegree_of_exponent
      center Q (p ^ e * ℓ) K h b τ hτpos hb hheight hjet)
    (symbolicSourceSeparant_mem_sourceCurveCutBidegree_of_exponent
      center Q (p ^ e * ℓ) K h b τ hτpos hheight hjet)
    (sourceFrobeniusPowerSparseCuts center Q K τ (p ^ e))
    ?_ (fun i ↦ symbolicSourceFrobeniusPowerAgreement center Q K τ (p ^ e)
      (roots i) (fun t ↦ ι (values t i)))
    (fun i ↦ symbolicSourceFrobeniusPowerAgreement_mem_restrictBidegree
      center (roots i) (fun t ↦ ι (values t i)) Q (p ^ e) h b K τ hτ hb hheight hjet)
    (sourceFrobeniusPowerGraphLocus
      domain values ι roots center Q K k τ (p ^ e))
    (fun I hI hs hi hsp hd hc ↦ principalOpen_subset_sourceFrobeniusPowerGraphLocus
      domain values ι p e roots hroots center Q hK hKk τ hτ I hI hs hi hsp hd hc)
    S hS hA
  intro q hq
  simp only [sourceFrobeniusPowerSparseCuts, List.mem_map, Finset.mem_toList] at hq
  obtain ⟨l, _, rfl⟩ := hq
  exact commonTaylorNumeratorOver_mem_sourceCurveCutBidegree_of_exponent
    center Q (p ^ e * ℓ) K h b τ hτ hb hheight hjet l

end ReedSolomon

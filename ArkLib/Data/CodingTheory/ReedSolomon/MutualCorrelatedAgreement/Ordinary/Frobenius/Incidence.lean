/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.Ordinary.Frobenius.GraphAdmissibility
public import
ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.PolynomialCurve.SharpRegularEquation
public import ArkLib.ToMathlib.AlgebraicGeometry.Incidence.BidegreeExcluded
/-!
# Incidence for sparse Frobenius charts

The actual numerator and agreement cuts satisfy the mixed bidegree estimate. Prime
components with an original-size common sample are excluded by their recognized graphs.
-/

@[expose] public section

noncomputable section

namespace ReedSolomon

open Polynomial MvPolynomial PolynomialDifferential HiddenDerivative AffineHilbert

variable {F E : Type*} [Field F] [Field E] {n k K : ℕ}

/-- The finite list of actual sparse numerator equations. -/
def sourceFrobeniusSparseCuts (center : E) (Q : DifferentialPolynomial E[X] 0)
    (K τ s : ℕ) : List (MvPolynomial (Option (Fin 1)) E) :=
  ((Finset.univ : Finset (Fin K)).filter (fun l ↦ ¬s ∣ l.val)).toList.map
    (fun l ↦ symbolicSourceNumerator center Q K l (τ := τ))

/-- Retained graphs carry the actual source, sparse, and sampled agreement identities. -/
def sourceFrobeniusGraphLocus (domain : Fin n ↪ F) (f g : Fin n → F)
    (ι : F →+* E) (roots : Fin n → E) (center : E)
    (Q : DifferentialPolynomial E[X] 0) (K k τ s : ℕ) : Set (Option (Fin 1) → E) :=
  {x | ∃ F₀ G₀ : F[X],
    IsAdmissibleFrobeniusPair domain f g ι roots center Q K k τ s F₀ G₀ ∧
    x = polynomialGraphPoint (frobeniusInitialGraph center s (F₀.map ι) (G₀.map ι)) (x none)}

/-- Agreement cuts in the pulled coordinate have challenge degree `s + τ*h`. -/
theorem symbolicSourceFrobeniusAgreement_mem_restrictBidegree
    (center alpha u v : E) (Q : DifferentialPolynomial E[X] 0)
    (s h b K τ : ℕ) (hτ : TaylorExponentSufficient 0 K τ) (hb : 0 < b)
    (hheight : ChallengeHeightLE Q h)
    (hjet : Q.weightedTotalDegree (fun i ↦ i.elim 0 (fun _ ↦ 1)) ≤ b) :
    symbolicSourceFrobeniusAgreement center Q K τ s alpha u v ∈
      restrictBidegree (F := E) (s + τ * h) (1 + τ * (b - 1)) := by
  apply taylorAgreementEquationOver_mem_restrictBidegree_of_exponent
    center alpha (Polynomial.C u + Polynomial.X ^ s * Polynomial.C v)
    Q s h b K τ hτ _ hb hheight hjet
  apply natDegree_add_le_of_degree_le
  · simp
  · exact (natDegree_mul_C_le _ _).trans (natDegree_X_pow_le s)

/-- Positive-dimensional regular prime components with `k` common cuts lie in the
recognized graph locus. -/
theorem principalOpen_subset_sourceFrobeniusGraphLocus [IsAlgClosed E]
    (domain : Fin n ↪ F) (f g : Fin n → F) (ι : F →+* E)
    (p e : ℕ) [ExpChar E p] (roots : Fin n → E)
    (hroots : ∀ i, roots i ^ (p ^ e) = ι (domain i))
    (center : E) (Q : DifferentialPolynomial E[X] 0)
    (hK : 0 < K) (hKk : K ≤ p ^ e * k) (τ : ℕ)
    (hτ : TaylorExponentSufficient 0 K τ)
    (I : Ideal (MvPolynomial (Option (Fin 1)) E)) (hI : I.IsPrime)
    (hs : symbolicSourceSeparant center Q ∉ I)
    (hinit : symbolicSourceInitialEquation center Q ∈ I)
    (hsparse : ∀ q ∈ sourceFrobeniusSparseCuts center Q K τ (p ^ e), q ∈ I)
    (hd : 0 < (hilbertPolynomial I).natDegree)
    (hcuts : k ≤ (cutsInIdeal I (fun i ↦
      symbolicSourceFrobeniusAgreement center Q K τ (p ^ e)
        (roots i) (ι (f i)) (ι (g i)))).card) :
    principalOpenZeroLocus I (symbolicSourceSeparant center Q) ⊆
      sourceFrobeniusGraphLocus domain f g ι roots center Q K k τ (p ^ e) := by
  classical
  obtain ⟨sample, hsub, hcard⟩ := Finset.exists_subset_card_eq hcuts
  obtain ⟨F₀, G₀, hpair, hgraph⟩ :=
    exists_admissibleFrobeniusPair_of_symbolic_prime_sample domain f g sample hcard
      ι p e roots hroots center Q hK hKk τ hτ I hI hs hinit hd
      (fun l hl ↦ hsparse _ (by
        simp only [sourceFrobeniusSparseCuts, List.mem_map, Finset.mem_toList,
          Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨l, hl, rfl⟩))
      (fun i hi ↦ mem_cutsInIdeal.mp (hsub hi))
  intro x hx
  exact ⟨F₀, G₀, hpair, hgraph x hx⟩

/-- The mixed source incidence bound for actual sparse charts. The threshold remains `k`,
so its ratio is `(n-k+1)/(A-k+1)` in every characteristic. -/
theorem finite_sourceFrobenius_points_off_graphs_card_le [IsAlgClosed E]
    (domain : Fin n ↪ F) (f g : Fin n → F) (ι : F →+* E)
    (p e : ℕ) [ExpChar E p] (roots : Fin n → E)
    (hroots : ∀ i, roots i ^ (p ^ e) = ι (domain i))
    (center : E) (Q : DifferentialPolynomial E[X] 0)
    (hK : 0 < K) (hKk : K ≤ p ^ e * k) (τ h b A : ℕ)
    (hτ : TaylorExponentSufficient 0 K τ) (hτpos : 0 < τ)
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
      (∀ q ∈ sourceFrobeniusSparseCuts center Q K τ (p ^ e), aeval x q = 0) ∧
      x ∉ sourceFrobeniusGraphLocus domain f g ι roots center Q K k τ (p ^ e))
    (hA : ∀ x ∈ S, A ≤ (agreementIndices (fun i ↦
      symbolicSourceFrobeniusAgreement center Q K τ (p ^ e)
        (roots i) (ι (f i)) (ι (g i))) x).card) :
    (S.card : ℚ) ≤ (h * (1 + τ * (b - 1)) + b * (p ^ e + τ * h) : ℕ) *
      (((n - k + 1 : ℕ) : ℚ) / ((A - k + 1 : ℕ) : ℚ)) := by
  classical
  have hp : 0 < p ^ e := pow_pos (expChar_pos E p) e
  apply bidegreeHypersurface_source_incidence_off_excluded_sharp_one
    (a := p ^ e + τ * h) (b := 1 + τ * (b - 1))
    (h := h) (v := b) (L := k) (by omega) (by omega) hkA hAn
    (symbolicSourceInitialEquation center Q) (symbolicSourceSeparant center Q)
    hinit hproper
    (symbolicSourceInitialEquation_mem_restrictBidegree center Q h b hheight hjet)
    (symbolicSourceInitialEquation_mem_sourceCurveCutBidegree_of_exponent
      center Q (p ^ e) K h b τ hτpos hb hheight hjet)
    (symbolicSourceSeparant_mem_sourceCurveCutBidegree_of_exponent
      center Q (p ^ e) K h b τ hτpos hheight hjet)
    (sourceFrobeniusSparseCuts center Q K τ (p ^ e))
    ?_ (fun i ↦ symbolicSourceFrobeniusAgreement center Q K τ (p ^ e)
      (roots i) (ι (f i)) (ι (g i)))
    (fun i ↦ symbolicSourceFrobeniusAgreement_mem_restrictBidegree
      center (roots i) (ι (f i)) (ι (g i)) Q (p ^ e) h b K τ hτ hb hheight hjet)
    (sourceFrobeniusGraphLocus domain f g ι roots center Q K k τ (p ^ e))
    (fun I hI hs hi hsp hd hc ↦ principalOpen_subset_sourceFrobeniusGraphLocus
      domain f g ι p e roots hroots center Q hK hKk τ hτ I hI hs hi hsp hd hc)
    S hS hA
  intro q hq
  simp only [sourceFrobeniusSparseCuts, List.mem_map, Finset.mem_toList] at hq
  obtain ⟨l, _, rfl⟩ := hq
  exact commonTaylorNumeratorOver_mem_sourceCurveCutBidegree_of_exponent
    center Q (p ^ e) K h b τ hτ hb hheight hjet l

end ReedSolomon

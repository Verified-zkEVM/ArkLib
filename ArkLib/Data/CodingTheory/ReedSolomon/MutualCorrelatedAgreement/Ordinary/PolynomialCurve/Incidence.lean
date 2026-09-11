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
public import ArkLib.ToMathlib.MvPolynomial.FrobeniusPullback
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

/-- The union of admissible Frobenius-power graphs retained at a free common-agreement
threshold `L`. -/
def sourceFrobeniusPowerGraphLocusAt
    (domain : Fin n ↪ F) (values : Fin (ℓ + 1) → Fin n → F)
    (ι : F →+* E) (roots : Fin n → E) (center : E)
    (Q : DifferentialPolynomial E[X] 0) (K k L τ s : ℕ) : Set (Option (Fin 1) → E) :=
  {x | ∃ P : Fin (ℓ + 1) → F[X],
    IsAdmissibleFrobeniusPowerTuple domain values ι roots center Q K k τ s P ∧
    L ≤ (commonCurveAgreementSet domain values P).card ∧
    x = polynomialGraphPoint
      (frobeniusPowerInitialGraph center s (fun t ↦ (P t).map ι)) (x none)}

/-- A Frobenius-power agreement cut containing a recognized positive-dimensional component
forces agreement of every base-field constituent.  Injectivity of the prime-power map replaces
any characteristic restriction involving the received-curve degree. -/
theorem commonAgreement_of_frobeniusPowerCut_mem_prime [IsAlgClosed E]
    (domain : Fin n ↪ F) (values : Fin (ℓ + 1) → Fin n → F) (ι : F →+* E)
    (p e : ℕ) [ExpChar E p] (roots : Fin n → E)
    (hroots : ∀ i, roots i ^ (p ^ e) = ι (domain i))
    (center : E) (Q : DifferentialPolynomial E[X] 0)
    (hK : 0 < K) (hKk : K ≤ p ^ e * k) (τ : ℕ)
    (hτ : TaylorExponentSufficient 0 K τ)
    (I : Ideal (MvPolynomial (Option (Fin 1)) E)) (hI : I.IsPrime)
    (hs : symbolicSourceSeparant center Q ∉ I)
    (hd : 0 < (hilbertPolynomial I).natDegree)
    (P : Fin (ℓ + 1) → F[X])
    (hP : IsAdmissibleFrobeniusPowerTuple
      domain values ι roots center Q K k τ (p ^ e) P)
    (hgraph : ∀ x ∈ principalOpenZeroLocus I (symbolicSourceSeparant center Q),
      x = polynomialGraphPoint
        (frobeniusPowerInitialGraph center (p ^ e) (fun t ↦ (P t).map ι)) (x none))
    (i : Fin n)
    (hcut : symbolicSourceFrobeniusPowerAgreement center Q K τ (p ^ e)
      (roots i) (fun t ↦ ι (values t i)) ∈ I) :
    ∀ t, (P t).eval (domain i) = values t i := by
  have hinfinite : (principalOpenZeroLocus I (symbolicSourceSeparant center Q)).Infinite := by
    intro hfinite
    have hz := hilbertPolynomial_natDegree_zero_of_finite_principalOpen hI hs hfinite
    omega
  have hchallengeInj : Set.InjOn
      (fun x : Option (Fin 1) → E ↦ (x none) ^ (p ^ e))
      (principalOpenZeroLocus I (symbolicSourceSeparant center Q)) := by
    intro x hx y hy hxy
    have hpow : x none = y none :=
      MvPolynomial.pow_primePow_injective (K := E) p e hxy
    rw [hgraph x hx, hgraph y hy, hpow]
  let mismatch := curveDiscrepancy (mappedDomain domain ι)
    (fun t i ↦ ι (values t i)) (fun t ↦ (P t).map ι) i
  have hzero : mismatch = 0 := by
    apply Polynomial.eq_zero_of_infinite_isRoot
    apply (hinfinite.image hchallengeInj).mono
    rintro z ⟨x, hx, rfl⟩
    let φ : E[X] →ₐ[E] E := Polynomial.aeval (x none)
    have hφ : φ.toRingHom = Polynomial.evalRingHom (x none) := by
      ext a <;> simp [φ]
    have hs' : aeval (fun j ↦ x (some j))
        (MvPolynomial.map φ.toRingHom (initialJetSeparantOver (Polynomial.C center) Q)) ≠ 0 := by
      simpa only [symbolicSourceSeparant, aeval_optionEquivRight_symm, hφ] using hx.2
    have hcutzero := hx.1 _ hcut
    rw [symbolicSourceFrobeniusPowerAgreement, aeval_optionEquivRight_symm] at hcutzero
    have heval := (aeval_map_taylorAgreementEquationOver_eq_zero_iff_of_exponent
      φ (Polynomial.C center) Q K τ hτ (fun j ↦ x (some j)) hs'
      (Polynomial.C (roots i))
      (frobeniusPowerCoordinate (p ^ e) (fun t ↦ ι (values t i)))).mp hcutzero
    have hregular : (polynomialGraphPullback
        (frobeniusPowerInitialGraph center (p ^ e) (fun t ↦ (P t).map ι))
        (symbolicSourceSeparant center Q)).eval (x none) ≠ 0 := by
      rw [eval_polynomialGraphPullback, ← hgraph x hx]
      exact hx.2
    have hspecial := hP.specialize hroots hK hKk hτ (x none) hregular
    simp only [hφ, φ, Polynomial.aeval_def, Algebra.algebraMap_self,
      Polynomial.eval₂_id, Polynomial.eval_C, frobeniusPowerCoordinate_eval] at heval
    rw [hgraph x hx] at heval
    simp only [polynomialGraphPoint, Option.elim_none, Option.elim_some] at heval
    rw [hspecial] at heval
    change mismatch.eval ((x none) ^ (p ^ e)) = 0
    rw [curveDiscrepancy_eval]
    apply sub_eq_zero.mpr
    simpa only [expand_eval, hroots, powerBatchedPolynomial_eval, powerBatchedWord,
      mappedDomain, Function.Embedding.trans_apply, Function.Embedding.coeFn_mk,
      Polynomial.eval_map, Polynomial.eval₂_at_apply, pow_mul] using heval
  have hcommon := (curveDiscrepancy_eq_zero_iff _ _ _ i).mp hzero
  intro t
  apply ι.injective
  simpa only [mappedDomain, Function.Embedding.trans_apply, Function.Embedding.coeFn_mk,
    Polynomial.eval_map, Polynomial.eval₂_at_apply] using hcommon t

/-- Every positive-dimensional regular prime containing `L` agreement cuts lies in a retained
original-degree Frobenius tuple graph with at least `L` common base-field positions. -/
theorem principalOpen_subset_sourceFrobeniusPowerGraphLocusAt [IsAlgClosed E]
    {L : ℕ}
    (domain : Fin n ↪ F) (values : Fin (ℓ + 1) → Fin n → F) (ι : F →+* E)
    (p e : ℕ) [ExpChar E p] (roots : Fin n → E)
    (hroots : ∀ i, roots i ^ (p ^ e) = ι (domain i))
    (center : E) (Q : DifferentialPolynomial E[X] 0)
    (hK : 0 < K) (hKk : K ≤ p ^ e * k) (hkL : k ≤ L) (τ : ℕ)
    (hτ : TaylorExponentSufficient 0 K τ)
    (I : Ideal (MvPolynomial (Option (Fin 1)) E)) (hI : I.IsPrime)
    (hs : symbolicSourceSeparant center Q ∉ I)
    (hinit : symbolicSourceInitialEquation center Q ∈ I)
    (hsparse : ∀ q ∈ sourceFrobeniusPowerSparseCuts center Q K τ (p ^ e), q ∈ I)
    (hd : 0 < (hilbertPolynomial I).natDegree)
    (hcuts : L ≤ (cutsInIdeal I (fun i ↦
      symbolicSourceFrobeniusPowerAgreement center Q K τ (p ^ e)
        (roots i) (fun t ↦ ι (values t i)))).card) :
    principalOpenZeroLocus I (symbolicSourceSeparant center Q) ⊆
      sourceFrobeniusPowerGraphLocusAt
        domain values ι roots center Q K k L τ (p ^ e) := by
  classical
  obtain ⟨indices, hindices, hcard⟩ := Finset.exists_subset_card_eq hcuts
  obtain ⟨sample, hsampleSub, hsampleCard⟩ :=
    Finset.exists_subset_card_eq (hcard ▸ hkL)
  obtain ⟨P, hP, hgraph⟩ :=
    exists_admissibleFrobeniusPowerTuple_of_symbolic_prime_sample
      domain values sample hsampleCard ι p e roots hroots center Q hK hKk τ hτ
      I hI hs hinit hd
      (fun l hl ↦ hsparse _ (by
        simp only [sourceFrobeniusPowerSparseCuts, List.mem_map, Finset.mem_toList,
          Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨l, hl, rfl⟩))
      (fun i hi ↦ mem_cutsInIdeal.mp (hindices (hsampleSub hi)))
  have hcommon : L ≤ (commonCurveAgreementSet domain values P).card := by
    rw [← hcard]
    apply Finset.card_le_card
    intro i hi
    simp only [commonCurveAgreementSet, Finset.mem_filter, Finset.mem_univ, true_and]
    apply commonAgreement_of_frobeniusPowerCut_mem_prime domain values ι p e roots hroots
      center Q hK hKk τ hτ I hI hs hd P hP hgraph i
    exact mem_cutsInIdeal.mp (hindices hi)
  intro x hx
  exact ⟨P, hP, hcommon, hgraph x hx⟩

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

/-- Mixed source incidence away from the tuple graphs retained at a free threshold `L`.  This is
the Frobenius-pulled `L`-common-position form of the source-incidence estimate. -/
theorem finite_sourceFrobeniusPower_points_off_graphs_card_le_at [IsAlgClosed E]
    {L : ℕ}
    (domain : Fin n ↪ F) (values : Fin (ℓ + 1) → Fin n → F) (ι : F →+* E)
    (p e : ℕ) [ExpChar E p] (roots : Fin n → E)
    (hroots : ∀ i, roots i ^ (p ^ e) = ι (domain i))
    (center : E) (Q : DifferentialPolynomial E[X] 0)
    (hK : 0 < K) (hKk : K ≤ p ^ e * k) (τ h b A : ℕ)
    (hτ : TaylorExponentSufficient 0 K τ) (hτpos : 0 < τ) (hℓ : 0 < ℓ)
    (hb : 0 < b) (hkL : k ≤ L) (hLA : L ≤ A) (hAn : A ≤ n)
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
      x ∉ sourceFrobeniusPowerGraphLocusAt
        domain values ι roots center Q K k L τ (p ^ e))
    (hA : ∀ x ∈ S, A ≤ (agreementIndices (fun i ↦
      symbolicSourceFrobeniusPowerAgreement center Q K τ (p ^ e)
        (roots i) (fun t ↦ ι (values t i))) x).card) :
    (S.card : ℚ) ≤
      (h * (1 + τ * (b - 1)) + b * (p ^ e * ℓ + τ * h) : ℕ) *
        (((n - L + 1 : ℕ) : ℚ) / ((A - L + 1 : ℕ) : ℚ)) := by
  classical
  have hp : 0 < p ^ e := pow_pos (expChar_pos E p) e
  apply bidegreeHypersurface_source_incidence_off_excluded_sharp_one
    (a := p ^ e * ℓ + τ * h) (b := 1 + τ * (b - 1))
    (h := h) (v := b) (L := L) (by positivity) (by omega) hLA hAn
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
    (sourceFrobeniusPowerGraphLocusAt
      domain values ι roots center Q K k L τ (p ^ e))
    (fun I hI hs hi hsp hd hc ↦ principalOpen_subset_sourceFrobeniusPowerGraphLocusAt
      domain values ι p e roots hroots center Q hK hKk hkL τ hτ I hI hs hi hsp hd hc)
    S hS hA
  intro q hq
  simp only [sourceFrobeniusPowerSparseCuts, List.mem_map, Finset.mem_toList] at hq
  obtain ⟨l, _, rfl⟩ := hq
  exact commonTaylorNumeratorOver_mem_sourceCurveCutBidegree_of_exponent
    center Q (p ^ e * ℓ) K h b τ hτ hb hheight hjet l

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

/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.Geometry.InitialGeometry
public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.Geometry.AgreementGeometry
public import ArkLib.ToMathlib.AlgebraicGeometry.CutFamily.Iteration


/-!
# Finite high-cut geometry of the rational Taylor chart

The finitely many high Taylor numerators cut the initial hypersurface into retained prime
components.  These components cover every regular high-cut solution, contain the entire high-cut
ideal, and retain the sharp initial Bezout potential.
-/

@[expose] public section

open PolynomialDifferential


noncomputable section

open MvPolynomial AffineHilbert
open scoped BigOperators

namespace ReedSolomon.HiddenDerivative

variable {F : Type*} [Field F] {r : ℕ}

/-- Uniform total-degree bound for the common Taylor numerator cuts. -/
def rationalTaylorCutDegreeBound (Q : DifferentialPolynomial F r) (K : ℕ)
    (τ : ℕ := 2 * K) : ℕ :=
  1 + τ * (Q.weightedTotalDegree (fun i ↦ i.elim (0 : ℕ) (fun _ ↦ 1)) - 1)

/-- The finite list of common Taylor numerators whose indices are at least `k`. -/
def highTaylorCutList (center : F) (Q : DifferentialPolynomial F r) (K k : ℕ)
    (τ : ℕ := 2 * K) :
    List (MvPolynomial (Fin (r + 1)) F) :=
  ((Finset.univ : Finset {l : Fin K // k ≤ l.val}).toList.map fun l ↦
    commonTaylorNumerator center Q K l.val (τ := τ))

@[simp] theorem commonTaylorNumerator_mem_highTaylorCutList
    (center : F) (Q : DifferentialPolynomial F r) (K k : ℕ)
    (l : {l : Fin K // k ≤ l.val}) (τ : ℕ := 2 * K) :
    commonTaylorNumerator center Q K l.val (τ := τ) ∈
      highTaylorCutList center Q K k (τ := τ) := by
  classical
  simp only [highTaylorCutList, List.mem_map, Finset.mem_toList, Finset.mem_univ]
  exact ⟨l, trivial, rfl⟩

/-- Membership of every finite high cut in an ideal is exactly enough to contain the generated
high-cut ideal. -/
theorem highTaylorCutsIdeal_le_of_highTaylorCutList_le
    (center : F) (Q : DifferentialPolynomial F r) (K k : ℕ)
    (τ : ℕ := 2 * K)
    {P : Ideal (MvPolynomial (Fin (r + 1)) F)}
    (hcuts : ∀ f ∈ highTaylorCutList center Q K k (τ := τ), f ∈ P) :
    highTaylorCutsIdeal center Q K k (τ := τ) ≤ P := by
  rw [highTaylorCutsIdeal, Ideal.span_le]
  rintro f ⟨l, rfl⟩
  exact hcuts _ (commonTaylorNumerator_mem_highTaylorCutList center Q K k l (τ := τ))

/-- Every high cut padded to a sufficient exponent obeys the matching chart degree bound. -/
theorem highTaylorCutList_totalDegree_le_of_exponent
    (center : F) (Q : DifferentialPolynomial F r)
    (hv : 0 < Q.weightedTotalDegree (fun i ↦ i.elim (0 : ℕ) (fun _ ↦ 1)))
    (K k τ : ℕ) (hτ : TaylorExponentSufficient r K τ) :
    ∀ f ∈ highTaylorCutList center Q K k (τ := τ),
      f.totalDegree ≤ rationalTaylorCutDegreeBound Q K (τ := τ) := by
  intro f hf
  simp only [highTaylorCutList, List.mem_map, Finset.mem_toList] at hf
  obtain ⟨l, _, rfl⟩ := hf
  exact totalDegree_commonTaylorNumerator_le_of_exponent center Q hv K τ hτ l.val

/-- Every high-cut numerator obeys the uniform chart degree bound. -/
theorem highTaylorCutList_totalDegree_le
    (center : F) (Q : DifferentialPolynomial F r)
    (hv : 0 < Q.weightedTotalDegree (fun i ↦ i.elim (0 : ℕ) (fun _ ↦ 1)))
    (K k : ℕ) :
    ∀ f ∈ highTaylorCutList center Q K k,
      f.totalDegree ≤ rationalTaylorCutDegreeBound Q K := by
  exact highTaylorCutList_totalDegree_le_of_exponent center Q hv K k (2 * K)
    (taylorExponentSufficient_two_mul r K)

/-- Final retained prime components after imposing all high Taylor numerator equations. -/
def highTaylorPrimeFamily (center : F) (Q : DifferentialPolynomial F r) (K k : ℕ)
    (τ : ℕ := 2 * K) :
    Finset (Ideal (MvPolynomial (Fin (r + 1)) F)) :=
  iteratedRetainedCutFamily (initialJetPrimeFamily center Q)
    (initialJetSeparant center Q) (highTaylorCutList center Q K k (τ := τ))

/-- The high-cut family has the same prime/open/cover specification at every exponent. -/
theorem highTaylorPrimeFamily_spec
    {E : Type*} [Field E] [Algebra F E]
    (center : F) (Q : DifferentialPolynomial F r) (K k : ℕ)
    (τ : ℕ := 2 * K) :
    let T := highTaylorPrimeFamily center Q K k (τ := τ)
    (∀ P ∈ T, P.IsPrime ∧ initialJetSeparant center Q ∉ P ∧
      highTaylorCutsIdeal center Q K k (τ := τ) ≤ P) ∧
    ∀ jet : Fin (r + 1) → E,
      aeval jet (initialJetEquation center Q) = 0 →
      aeval jet (initialJetSeparant center Q) ≠ 0 →
      (∀ l : {l : Fin K // k ≤ l.val},
        aeval jet (commonTaylorNumerator center Q K l.val (τ := τ)) = 0) →
      ∃ P ∈ T, jet ∈ zeroLocus E P := by
  dsimp only
  have hinitialPrime : ∀ P ∈ initialJetPrimeFamily center Q, P.IsPrime :=
    fun P hP ↦ (initialJetPrimeFamily_prime_open center Q P hP).1
  have hinitialOpen : ∀ P ∈ initialJetPrimeFamily center Q,
      initialJetSeparant center Q ∉ P :=
    fun P hP ↦ (initialJetPrimeFamily_prime_open center Q P hP).2
  constructor
  · intro P hP
    have hpo := iteratedRetainedCutFamily_prime_open
      (initialJetPrimeFamily center Q) hinitialPrime hinitialOpen
      (highTaylorCutList center Q K k (τ := τ)) P hP
    obtain ⟨P₀, hP₀, _, hcuts⟩ := mem_iteratedRetainedCutFamily_contains
      (initialJetPrimeFamily center Q) (highTaylorCutList center Q K k (τ := τ)) hP
    exact ⟨hpo.1, hpo.2,
      highTaylorCutsIdeal_le_of_highTaylorCutList_le center Q K k (τ := τ) hcuts⟩
  · intro jet hinit hsep hhigh
    apply exists_mem_iteratedRetainedCutFamily_of_mem_zeroLocus
      (initialJetPrimeFamily center Q) (highTaylorCutList center Q K k (τ := τ)) jet
    · exact exists_mem_initialJetPrimeFamily_of_regular center Q jet hinit hsep
    · exact hsep
    · intro f hf
      simp only [highTaylorCutList, List.mem_map, Finset.mem_toList] at hf
      obtain ⟨l, _, rfl⟩ := hf
      exact hhigh l

/-- Iterating all high cuts preserves the initial `ν B^r` Bezout potential. -/
theorem sum_highTaylorPrimeFamily_affineDegree_mul_pow_le_of_exponent
    (center : F) (Q : DifferentialPolynomial F r)
    (hsep : initialJetSeparant center Q ≠ 0)
    (hv : 0 < Q.weightedTotalDegree (fun i ↦ i.elim (0 : ℕ) (fun _ ↦ 1)))
    (K k τ : ℕ) (hτ : TaylorExponentSufficient r K τ) :
    ∑ P ∈ highTaylorPrimeFamily center Q K k (τ := τ),
        affineDegree P * (rationalTaylorCutDegreeBound Q K (τ := τ) : ℚ) ^
          (hilbertPolynomial P).natDegree ≤
      (Q.weightedTotalDegree (fun i ↦ i.elim (0 : ℕ) (fun _ ↦ 1)) : ℕ) *
        (rationalTaylorCutDegreeBound Q K (τ := τ) : ℚ) ^ r := by
  let B := rationalTaylorCutDegreeBound Q K (τ := τ)
  have hB : 1 ≤ B := by simp [B, rationalTaylorCutDegreeBound]
  have hiter := sum_iteratedRetainedCutFamily_affineDegree_mul_pow_le
    (initialJetPrimeFamily center Q)
    (fun P hP ↦ (initialJetPrimeFamily_prime_open center Q P hP).1)
    (fun P hP ↦ (initialJetPrimeFamily_prime_open center Q P hP).2)
    hB (highTaylorCutList center Q K k (τ := τ))
    (highTaylorCutList_totalDegree_le_of_exponent center Q hv K k τ hτ)
  exact hiter.trans
    (sum_initialJetPrimeFamily_affineDegree_mul_pow_le_totalJetDegree center Q hsep B)

/-- The default `2K` high-cut family preserves the coarse Bezout potential. -/
theorem sum_highTaylorPrimeFamily_affineDegree_mul_pow_le
    (center : F) (Q : DifferentialPolynomial F r)
    (hsep : initialJetSeparant center Q ≠ 0)
    (hv : 0 < Q.weightedTotalDegree (fun i ↦ i.elim (0 : ℕ) (fun _ ↦ 1)))
    (K k : ℕ) :
    ∑ P ∈ highTaylorPrimeFamily center Q K k,
        affineDegree P * (rationalTaylorCutDegreeBound Q K : ℚ) ^
          (hilbertPolynomial P).natDegree ≤
      (Q.weightedTotalDegree (fun i ↦ i.elim (0 : ℕ) (fun _ ↦ 1)) : ℕ) *
        (rationalTaylorCutDegreeBound Q K : ℚ) ^ r := by
  exact sum_highTaylorPrimeFamily_affineDegree_mul_pow_le_of_exponent
    center Q hsep hv K k (2 * K) (taylorExponentSufficient_two_mul r K)


/-- Every final high-cut component has Hilbert-polynomial degree at most the initial value `r`. -/
theorem highTaylorPrimeFamily_hilbertPolynomial_natDegree_le
    (center : F) (Q : DifferentialPolynomial F r) (K k : ℕ)
    (τ : ℕ := 2 * K)
    (hinit : initialJetEquation center Q ≠ 0)
    {P : Ideal (MvPolynomial (Fin (r + 1)) F)}
    (hP : P ∈ highTaylorPrimeFamily center Q K k (τ := τ)) :
    (hilbertPolynomial P).natDegree ≤ r := by
  obtain ⟨P₀, hP₀, hP₀P, _⟩ := mem_iteratedRetainedCutFamily_contains
    (initialJetPrimeFamily center Q) (highTaylorCutList center Q K k (τ := τ)) hP
  have hPprime :=
    (highTaylorPrimeFamily_spec (F := F) (E := F) center Q K k (τ := τ)).1 P hP |>.1
  exact (hilbertPolynomial_degree_and_leadingCoeff_antitone hP₀P hPprime.ne_top).1.trans_eq
    (initialJetPrimeFamily_hilbertPolynomial_natDegree center Q hinit hP₀)

/-- Finite regular high-cut jets that agree with at least `A` received symbols satisfy the sharp
chart incidence bound. -/
theorem finite_regularHighCutJets_card_le_of_exponent
    [IsAlgClosed F]
    (center : F) (Q : DifferentialPolynomial F r) (K k τ : ℕ)
    (hτ : TaylorExponentSufficient r K τ) (hK : r < K)
    (hsep : initialJetSeparant center Q ≠ 0)
    (hv : 0 < Q.weightedTotalDegree (fun i ↦ i.elim (0 : ℕ) (fun _ ↦ 1)))
    {n A : ℕ} (domain : Fin n ↪ F) (received : Fin n → F)
    (hk : 0 < k) (hkA : k ≤ A) (hAn : A ≤ n)
    (S : Finset (Fin (r + 1) → F))
    (hS : ∀ jet ∈ S,
      aeval jet (initialJetEquation center Q) = 0 ∧
      aeval jet (initialJetSeparant center Q) ≠ 0 ∧
      ∀ l : {l : Fin K // k ≤ l.val},
        aeval jet (commonTaylorNumerator center Q K l.val (τ := τ)) = 0)
    (hA : ∀ jet ∈ S, A ≤ (AffineHilbert.agreementIndices
      (fun i ↦ taylorAgreementEquation center Q K (domain i) (received i) (τ := τ))
        jet).card) :
    (S.card : ℚ) ≤
      (Q.weightedTotalDegree (fun i ↦ i.elim (0 : ℕ) (fun _ ↦ 1)) : ℕ) *
        ((((n * rationalTaylorCutDegreeBound Q K (τ := τ) : ℕ) : ℚ) /
          ((A - k + 1 : ℕ) : ℚ)) ^ r) := by
  classical
  let B := rationalTaylorCutDegreeBound Q K (τ := τ)
  let T := highTaylorPrimeFamily center Q K k (τ := τ)
  let cuts : Fin n → MvPolynomial (Fin (r + 1)) F := fun i ↦
    taylorAgreementEquation center Q K (domain i) (received i) (τ := τ)
  let R : ℚ := ((n * B : ℕ) : ℚ) / ((A - k + 1 : ℕ) : ℚ)
  let t : ℚ := (n : ℚ) / ((A - k + 1 : ℕ) : ℚ)
  have hinit : initialJetEquation center Q ≠ 0 :=
    initialJetEquation_ne_zero_of_separant_ne_zero center Q hsep
  have hB : 0 < B := by simp [B, rationalTaylorCutDegreeBound]
  have hcNat : 0 < A - k + 1 := by omega
  have hcn : A - k + 1 ≤ n := by omega
  have ht : 1 ≤ t := by
    apply (le_div_iff₀ (by exact_mod_cast hcNat)).2
    simpa using (show ((A - k + 1 : ℕ) : ℚ) ≤ (n : ℚ) by exact_mod_cast hcn)
  have hR : R = (B : ℚ) * t := by
    dsimp only [R, t]
    push_cast
    field_simp
  have hspec := highTaylorPrimeFamily_spec (F := F) (E := F) center Q K k (τ := τ)
  have hcoverNat : S.card ≤
      ∑ P ∈ T, (AffineHilbert.componentPoints S P).card := by
    calc
      S.card ≤ (T.biUnion fun P ↦ AffineHilbert.componentPoints S P).card := by
        apply Finset.card_le_card
        intro jet hjet
        obtain ⟨P, hPT, hjetP⟩ := hspec.2 jet
          (hS jet hjet).1 (hS jet hjet).2.1 (hS jet hjet).2.2
        exact Finset.mem_biUnion.mpr ⟨P, hPT, by
          rw [AffineHilbert.mem_componentPoints]
          exact ⟨hjet, hjetP⟩⟩
      _ ≤ ∑ P ∈ T, (AffineHilbert.componentPoints S P).card := Finset.card_biUnion_le
  have hcover : (S.card : ℚ) ≤
      ∑ P ∈ T, ((AffineHilbert.componentPoints S P).card : ℚ) := by
    exact_mod_cast hcoverNat
  have hcomponent : ∀ P ∈ T,
      ((AffineHilbert.componentPoints S P).card : ℚ) ≤
        affineDegree P * R ^ (hilbertPolynomial P).natDegree := by
    intro P hPT
    have hPspec := hspec.1 P hPT
    apply AffineHilbert.affineAgreementIncidence_bound hPspec.1 hPspec.2.1
      cuts (fun i ↦ totalDegree_taylorAgreementEquation_le_of_exponent
        center Q hv K τ hτ _ _)
      hB hk hkA hAn (AffineHilbert.componentPoints S P)
    · intro jet hjet
      rw [AffineHilbert.mem_componentPoints] at hjet
      exact ⟨hjet.2, (hS jet hjet.1).2.1⟩
    · intro jet hjet
      rw [AffineHilbert.mem_componentPoints] at hjet
      exact hA jet hjet.1
    · intro U hU jet jet' hjetP hjetS hjetP' hjetS' hzero
      apply eq_of_mem_principalOpen_of_highCuts_of_agreementFinset_of_exponent
        center Q K k τ hτ hK P hPspec.2.2 domain received U hU
        ⟨hjetP, hjetS⟩ ⟨hjetP', hjetS'⟩
      · intro i hi
        exact (hzero i hi).1
      · intro i hi
        exact (hzero i hi).2
  have hpotential := sum_highTaylorPrimeFamily_affineDegree_mul_pow_le_of_exponent
    center Q hsep hv K k τ hτ
  calc
    (S.card : ℚ) ≤ ∑ P ∈ T,
        ((AffineHilbert.componentPoints S P).card : ℚ) := hcover
    _ ≤ ∑ P ∈ T, affineDegree P * R ^ (hilbertPolynomial P).natDegree :=
      Finset.sum_le_sum hcomponent
    _ = ∑ P ∈ T, affineDegree P * (B : ℚ) ^ (hilbertPolynomial P).natDegree *
          t ^ (hilbertPolynomial P).natDegree := by
      apply Finset.sum_congr rfl
      intro P hPT
      rw [hR, mul_pow]
      ring
    _ ≤ ∑ P ∈ T, affineDegree P * (B : ℚ) ^ (hilbertPolynomial P).natDegree *
          t ^ r := by
      apply Finset.sum_le_sum
      intro P hPT
      apply mul_le_mul_of_nonneg_left
      · exact pow_le_pow_right₀ ht
          (highTaylorPrimeFamily_hilbertPolynomial_natDegree_le
            center Q K k (τ := τ) hinit hPT)
      · exact mul_nonneg (affineDegree_nonneg P) (by positivity)
    _ = (∑ P ∈ T, affineDegree P * (B : ℚ) ^ (hilbertPolynomial P).natDegree) *
          t ^ r := by rw [Finset.sum_mul]
    _ ≤ (((Q.weightedTotalDegree (fun i ↦ i.elim (0 : ℕ) (fun _ ↦ 1)) : ℕ) : ℚ) *
          (B : ℚ) ^ r) * t ^ r :=
      mul_le_mul_of_nonneg_right hpotential (by positivity)
    _ = ((Q.weightedTotalDegree (fun i ↦ i.elim (0 : ℕ) (fun _ ↦ 1)) : ℕ) : ℚ) *
          R ^ r := by
      rw [hR, mul_pow]
      ring

/-- The default `2K` chart satisfies the original finite regular high-cut incidence bound. -/
theorem finite_regularHighCutJets_card_le
    [IsAlgClosed F]
    (center : F) (Q : DifferentialPolynomial F r) (K k : ℕ) (hK : r < K)
    (hsep : initialJetSeparant center Q ≠ 0)
    (hv : 0 < Q.weightedTotalDegree (fun i ↦ i.elim (0 : ℕ) (fun _ ↦ 1)))
    {n A : ℕ} (domain : Fin n ↪ F) (received : Fin n → F)
    (hk : 0 < k) (hkA : k ≤ A) (hAn : A ≤ n)
    (S : Finset (Fin (r + 1) → F))
    (hS : ∀ jet ∈ S,
      aeval jet (initialJetEquation center Q) = 0 ∧
      aeval jet (initialJetSeparant center Q) ≠ 0 ∧
      ∀ l : {l : Fin K // k ≤ l.val},
        aeval jet (commonTaylorNumerator center Q K l.val) = 0)
    (hA : ∀ jet ∈ S, A ≤ (AffineHilbert.agreementIndices
      (fun i ↦ taylorAgreementEquation center Q K (domain i) (received i)) jet).card) :
    (S.card : ℚ) ≤
      (Q.weightedTotalDegree (fun i ↦ i.elim (0 : ℕ) (fun _ ↦ 1)) : ℕ) *
        ((((n * rationalTaylorCutDegreeBound Q K : ℕ) : ℚ) /
          ((A - k + 1 : ℕ) : ℚ)) ^ r) := by
  exact finite_regularHighCutJets_card_le_of_exponent center Q K k (2 * K)
    (taylorExponentSufficient_two_mul r K) hK hsep hv domain received hk hkA hAn S hS hA

end ReedSolomon.HiddenDerivative

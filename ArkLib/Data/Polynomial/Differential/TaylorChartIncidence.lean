/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.Polynomial.Differential.TaylorChartGeometry
public import ArkLib.Data.Polynomial.Differential.RationalTaylorBidegree
public import ArkLib.ToMathlib.RingTheory.Nullstellensatz.CappedDegreeIncidence
public import ArkLib.ToMathlib.RingTheory.Nullstellensatz.AgreementIncidence

/-!
# Incidence of regular high-cut jets in the rational Taylor chart

Let `Q` be a differential polynomial of order `r` over a field `F`, fix a center, and write `S`
for the initial separant, `v = jetTotalDegree Q`, and `B = rationalTaylorCutDegreeBound Q τ` for
the degree bound `1 + τ (v - 1)` of the chart equations with a sufficient exponent `τ`.

A *regular high-cut jet* is a zero of the initial equation with `S ≠ 0` at which the high cuts
`commonTaylorNumerator center Q τ l`, `k ≤ l < K`, vanish. On `S ≠ 0` these are the initial jets
whose reconstructed polynomial has degree below `k`.

* `highTaylorCutList center Q K k τ` lists the high cuts, and `highTaylorPrimeFamily center Q K k τ`
  is the family of prime components obtained by cutting `initialJetPrimeFamily center Q`
  successively by them, keeping at each step the minimal primes that do not contain `S`.
  Its members are primes containing the initial equation and the high cuts, not containing `S`,
  of dimension at most `r`; they cover every regular high-cut jet over any extension field; and
  their potential `∑ P, affineDegree P * B ^ dim P` is at most `v * B ^ r`.
* Over an algebraically closed field, fewer than `k` agreement equations lie in a
  positive-dimensional prime containing the high cuts and not containing `S`, because `k`
  agreement equations at distinct points determine a regular jet on it.
* Combining these with the agreement incidence bound on a cut hypersurface: if the agreement
  points `domain i`, `i : ι`, are distinct and `k ≤ A` with `A - k + 1 ≤ #ι`, every finite set of
  regular high-cut jets, each satisfying at least `A` agreement equations, has at most
  `v * (#ι * B / (A - k + 1)) ^ r` elements.

## Main statements

* `mem_highTaylorCutList`, `span_setOf_mem_highTaylorCutList` and
  `totalDegree_le_of_mem_highTaylorCutList`: the list of high cuts.
* `exists_mem_highTaylorPrimeFamily_of_regular`: the high-cut prime family covers the regular
  high-cut jets.
* `natDegree_affineHilbertPolynomial_le_of_mem_highTaylorPrimeFamily` and
  `sum_affineDegree_mul_pow_highTaylorPrimeFamily_le`: dimension and potential of the family.
* `ncard_setOf_taylorAgreementEquation_mem_lt`: positive-dimensional primes containing the high
  cuts contain fewer than `k` agreement equations.
* `card_le_of_highTaylorCuts_of_agreement`: the incidence bound for regular high-cut jets.
* `card_le_of_highTaylorCuts_of_agreement_sharp`: the sharp incidence bound with numerator
  `#ι - k + 1`.
* `card_le_of_firstOrderHighTaylorCuts_of_agreement_capped`: the first-order bound using separate
  total-degree and derivative-degree caps.

## References

* [Dao, Q., Kominers, S. D., and Thaler, J., *Reed–Solomon Codes Beyond Johnson: Efficient
  Decoding and Smaller Cryptographic Proofs*][DKT26], Appendix A.6.
-/

@[expose] public section

namespace PolynomialDifferential

noncomputable section

open MvPolynomial
open scoped Finset

variable {F : Type*} [Field F] {r : ℕ}

/-! ### The list of high cuts -/

/-- The common numerators `commonTaylorNumerator center Q τ l` for `k ≤ l < K`, in increasing
order of `l`. -/
def highTaylorCutList (center : F) (Q : DifferentialPolynomial F r) (K k τ : ℕ) :
    List (MvPolynomial (Fin (r + 1)) F) :=
  (List.range' k (K - k)).map (commonTaylorNumerator center Q τ)

/-- A polynomial lies in the high-cut list exactly when it is the common numerator of `c_l` for
some `k ≤ l < K`. -/
theorem mem_highTaylorCutList {center : F} {Q : DifferentialPolynomial F r} {K k τ : ℕ}
    {f : MvPolynomial (Fin (r + 1)) F} :
    f ∈ highTaylorCutList center Q K k τ ↔
      ∃ l, k ≤ l ∧ l < K ∧ commonTaylorNumerator center Q τ l = f := by
  simp only [highTaylorCutList, List.mem_map, List.mem_range'_1]
  constructor
  · rintro ⟨l, ⟨hkl, hlK⟩, rfl⟩
    exact ⟨l, hkl, by omega, rfl⟩
  · rintro ⟨l, hkl, hlK, rfl⟩
    exact ⟨l, ⟨hkl, by omega⟩, rfl⟩

/-- The high-cut list generates the high-cuts ideal. -/
theorem span_setOf_mem_highTaylorCutList (center : F) (Q : DifferentialPolynomial F r)
    (K k τ : ℕ) :
    Ideal.span {f | f ∈ highTaylorCutList center Q K k τ} = highTaylorCutsIdeal center Q K k τ := by
  rw [highTaylorCutsIdeal]
  congr 1
  ext f
  simp only [Set.mem_ofPred_eq, mem_highTaylorCutList, Set.mem_image, Set.mem_Ico, and_assoc]

/-- For a sufficient exponent `τ`, every high cut has total degree at most
`rationalTaylorCutDegreeBound Q τ`. -/
theorem totalDegree_le_of_mem_highTaylorCutList (center : F) (Q : DifferentialPolynomial F r)
    {K k τ : ℕ} (hτ : TaylorExponentSufficient r K τ) {f : MvPolynomial (Fin (r + 1)) F}
    (hf : f ∈ highTaylorCutList center Q K k τ) :
    f.totalDegree ≤ rationalTaylorCutDegreeBound Q τ := by
  obtain ⟨l, -, hlK, rfl⟩ := mem_highTaylorCutList.mp hf
  exact totalDegree_commonTaylorNumerator_le center Q (hτ ⟨l, hlK⟩)

/-! ### The high-cut prime family -/

/-- The prime components obtained from the initial prime family by cutting successively with the
high cuts `commonTaylorNumerator center Q τ l`, `k ≤ l < K`, keeping at each step the minimal
primes that do not contain the initial separant. -/
def highTaylorPrimeFamily (center : F) (Q : DifferentialPolynomial F r) (K k τ : ℕ) :
    Finset (Ideal (MvPolynomial (Fin (r + 1)) F)) :=
  Ideal.iteratedRetainedCutFamily (initialJetPrimeFamily center Q) (initialJetSeparant center Q)
    (highTaylorCutList center Q K k τ)

/-- Every member of the high-cut prime family is prime. -/
theorem isPrime_of_mem_highTaylorPrimeFamily {center : F} {Q : DifferentialPolynomial F r}
    {K k τ : ℕ} {P : Ideal (MvPolynomial (Fin (r + 1)) F)}
    (hP : P ∈ highTaylorPrimeFamily center Q K k τ) : P.IsPrime :=
  Ideal.isPrime_of_mem_iteratedRetainedCutFamily
    (fun _ h ↦ isPrime_of_mem_initialJetPrimeFamily h) _ _ hP

/-- No member of the high-cut prime family contains the initial separant. -/
theorem initialJetSeparant_notMem_of_mem_highTaylorPrimeFamily {center : F}
    {Q : DifferentialPolynomial F r} {K k τ : ℕ} {P : Ideal (MvPolynomial (Fin (r + 1)) F)}
    (hP : P ∈ highTaylorPrimeFamily center Q K k τ) : initialJetSeparant center Q ∉ P :=
  Ideal.notMem_of_mem_iteratedRetainedCutFamily
    (fun _ h ↦ initialJetSeparant_notMem_of_mem_initialJetPrimeFamily h) _ hP

/-- Every member of the high-cut prime family contains the initial equation. -/
theorem initialJetEquation_mem_of_mem_highTaylorPrimeFamily {center : F}
    {Q : DifferentialPolynomial F r} {K k τ : ℕ} {P : Ideal (MvPolynomial (Fin (r + 1)) F)}
    (hP : P ∈ highTaylorPrimeFamily center Q K k τ) : initialJetEquation center Q ∈ P := by
  obtain ⟨P₀, hP₀, hP₀P, -⟩ := Ideal.exists_le_of_mem_iteratedRetainedCutFamily hP
  exact hP₀P (initialJetEquation_mem_of_mem_initialJetPrimeFamily hP₀)

/-- Every member of the high-cut prime family contains the high-cuts ideal. -/
theorem highTaylorCutsIdeal_le_of_mem_highTaylorPrimeFamily {center : F}
    {Q : DifferentialPolynomial F r} {K k τ : ℕ} {P : Ideal (MvPolynomial (Fin (r + 1)) F)}
    (hP : P ∈ highTaylorPrimeFamily center Q K k τ) : highTaylorCutsIdeal center Q K k τ ≤ P := by
  obtain ⟨-, -, -, hcuts⟩ := Ideal.exists_le_of_mem_iteratedRetainedCutFamily hP
  rw [← span_setOf_mem_highTaylorCutList, Ideal.span_le]
  exact fun f hf ↦ hcuts f hf

/-- Every zero over an extension field of the initial equation and of the high cuts at which the
initial separant does not vanish is a zero of some member of the high-cut prime family. -/
theorem exists_mem_highTaylorPrimeFamily_of_regular {E : Type*} [Field E] [Algebra F E]
    (center : F) (Q : DifferentialPolynomial F r) {K k τ : ℕ} (jet : Fin (r + 1) → E)
    (hinit : aeval jet (initialJetEquation center Q) = 0)
    (hS : aeval jet (initialJetSeparant center Q) ≠ 0)
    (hhigh : ∀ l, k ≤ l → l < K → aeval jet (commonTaylorNumerator center Q τ l) = 0) :
    ∃ P ∈ highTaylorPrimeFamily center Q K k τ, jet ∈ zeroLocus E P := by
  obtain ⟨P₀, hP₀, hjet⟩ := exists_mem_initialJetPrimeFamily_of_regular center Q jet hinit hS
  obtain ⟨P, hP, -, hjetP⟩ := exists_mem_iteratedRetainedCutFamily_of_mem_zeroLocus hP₀ hjet hS
    fun f hf ↦ by
      obtain ⟨l, hkl, hlK, rfl⟩ := mem_highTaylorCutList.mp hf
      exact hhigh l hkl hlK
  exact ⟨P, hP, hjetP⟩

/-- Every member of the high-cut prime family has dimension at most `r`: its affine Hilbert
polynomial has natural degree at most `r`. -/
theorem natDegree_affineHilbertPolynomial_le_of_mem_highTaylorPrimeFamily {center : F}
    {Q : DifferentialPolynomial F r} {K k τ : ℕ} {P : Ideal (MvPolynomial (Fin (r + 1)) F)}
    (hP : P ∈ highTaylorPrimeFamily center Q K k τ) :
    (affineHilbertPolynomial P).natDegree ≤ r := by
  have h := natDegree_affineHilbertPolynomial_le_of_mem
    (initialJetEquation_ne_zero_of_initialJetSeparant_notMem
      (initialJetSeparant_notMem_of_mem_highTaylorPrimeFamily hP))
    (initialJetEquation_mem_of_mem_highTaylorPrimeFamily hP)
  rwa [Nat.card_eq_fintype_card, Fintype.card_fin, Nat.add_sub_cancel] at h

/-- For a sufficient exponent `τ`, with `B = rationalTaylorCutDegreeBound Q τ`, the members `P` of
the high-cut prime family satisfy `∑ P, affineDegree P * B ^ dim P ≤ jetTotalDegree Q * B ^ r`,
where `dim P` is the natural degree of the affine Hilbert polynomial of `P`. -/
theorem sum_affineDegree_mul_pow_highTaylorPrimeFamily_le (center : F)
    (Q : DifferentialPolynomial F r) {K k τ : ℕ} (hτ : TaylorExponentSufficient r K τ) :
    ∑ P ∈ highTaylorPrimeFamily center Q K k τ, affineDegree P *
        (rationalTaylorCutDegreeBound Q τ : ℚ) ^ (affineHilbertPolynomial P).natDegree ≤
      jetTotalDegree Q * (rationalTaylorCutDegreeBound Q τ : ℚ) ^ r := by
  rcases (highTaylorPrimeFamily center Q K k τ).eq_empty_or_nonempty with h | ⟨P, hP⟩
  · rw [h, Finset.sum_empty]
    positivity
  have h := sum_affineDegree_mul_pow_iteratedRetainedCutFamily_span_singleton_le
    (initialJetEquation_ne_zero_of_initialJetSeparant_notMem
      (initialJetSeparant_notMem_of_mem_highTaylorPrimeFamily hP))
    (initialJetSeparant center Q) (totalDegree_initialJetEquation_le center Q)
    (fun f hf ↦ totalDegree_le_of_mem_highTaylorCutList center Q (k := k) hτ hf)
  rwa [Nat.card_eq_fintype_card, Fintype.card_fin, Nat.add_sub_cancel] at h

/-! ### The incidence bound -/

/-- Over an algebraically closed field, let `r < K`, let `τ` be sufficient for `K`, and let `J` be
a prime of positive dimension that contains the high cuts for `k` and does not contain the initial
separant. If the agreement points `domain i` are distinct, fewer than `k` of the agreement
equations at `(domain i, received i)` lie in `J`. -/
theorem ncard_setOf_taylorAgreementEquation_mem_lt [IsAlgClosed F] (center : F)
    (Q : DifferentialPolynomial F r) {K k τ : ℕ} (hτ : TaylorExponentSufficient r K τ)
    (hK : r < K) {J : Ideal (MvPolynomial (Fin (r + 1)) F)} [J.IsPrime]
    (hSJ : initialJetSeparant center Q ∉ J) (hhigh : highTaylorCutsIdeal center Q K k τ ≤ J)
    (hd : 0 < (affineHilbertPolynomial J).natDegree) {ι : Type*} [Finite ι]
    (domain received : ι → F) (hinj : Function.Injective domain) :
    {i | taylorAgreementEquation center Q K τ (domain i) (received i) ∈ J}.ncard < k :=
  ncard_setOf_mem_lt_of_subsingleton hSJ _ hd fun T hT _ hx _ hy ↦
    eq_of_mem_zeroLocus_of_highTaylorCutsIdeal_le center Q hτ hK hhigh domain received T
      hinj.injOn hT.ge hx.1 hy.1 hx.2.1 hy.2.1 hx.2.2 hy.2.2

/-- **Incidence of regular high-cut jets.** Over an algebraically closed field, let `r < K`, let
`τ` be sufficient for `K`, and write `B = rationalTaylorCutDegreeBound Q τ`. Let the agreement
points `domain i`, `i : ι`, be distinct, and let `k ≤ A` with `A - k + 1 ≤ #ι`. Every finite set
of zeros of the initial equation with nonzero initial separant, at which the high cuts for `k`
vanish and at least `A` of the agreement equations at `(domain i, received i)` vanish, has at most
`jetTotalDegree Q * (#ι * B / (A - k + 1)) ^ r` elements. -/
theorem card_le_of_highTaylorCuts_of_agreement [IsAlgClosed F] (center : F)
    (Q : DifferentialPolynomial F r) {K k τ : ℕ} (hτ : TaylorExponentSufficient r K τ)
    (hK : r < K) {ι : Type*} [Fintype ι] (domain received : ι → F)
    (hinj : Function.Injective domain) {A : ℕ} (hkA : k ≤ A) (hAι : A - k + 1 ≤ Fintype.card ι)
    (S : Finset (Fin (r + 1) → F))
    (hS : ∀ jet ∈ S, aeval jet (initialJetEquation center Q) = 0 ∧
      aeval jet (initialJetSeparant center Q) ≠ 0 ∧
      ∀ l, k ≤ l → l < K → aeval jet (commonTaylorNumerator center Q τ l) = 0)
    (hA : ∀ jet ∈ S, A ≤
      {i | aeval jet (taylorAgreementEquation center Q K τ (domain i) (received i)) = 0}.ncard) :
    (#S : ℚ) ≤ jetTotalDegree Q *
      (((Fintype.card ι * rationalTaylorCutDegreeBound Q τ : ℕ) : ℚ) / ((A - k + 1 : ℕ) : ℚ)) ^
        r := by
  rcases S.eq_empty_or_nonempty with rfl | ⟨jet₀, hjet₀⟩
  · rw [Finset.card_empty, Nat.cast_zero]
    positivity
  have hinit : initialJetEquation center Q ≠ 0 :=
    initialJetEquation_ne_zero_of_initialJetSeparant_ne_zero center Q
      fun h ↦ (hS jet₀ hjet₀).2.1 (by rw [h, map_zero])
  have h := card_le_of_agreement_off_excluded_of_hypersurface hinit (initialJetSeparant center Q)
    (totalDegree_initialJetEquation_le center Q) (highTaylorCutList center Q K k τ)
    (fun f hf ↦ totalDegree_le_of_mem_highTaylorCutList center Q hτ hf)
    (fun i ↦ taylorAgreementEquation center Q K τ (domain i) (received i))
    (fun i ↦ totalDegree_taylorAgreementEquation_le center Q hτ _ _) hkA hAι ∅
    (fun J hJ hSJ _ hhigh hd hk ↦ absurd hk (not_le.mpr
      (ncard_setOf_taylorAgreementEquation_mem_lt center Q hτ hK hSJ
        (by rw [← span_setOf_mem_highTaylorCutList, Ideal.span_le]; exact hhigh) hd domain
        received hinj)))
    S (fun jet hjet ↦ ⟨(hS jet hjet).1, (hS jet hjet).2.1, fun f hf ↦ by
      obtain ⟨l, hkl, hlK, rfl⟩ := mem_highTaylorCutList.mp hf
      exact (hS jet hjet).2.2 l hkl hlK, Set.notMem_empty jet⟩) hA
  rwa [Nat.card_eq_fintype_card, Fintype.card_fin, Nat.add_sub_cancel] at h

/-- **Sharp incidence of regular high-cut jets.** Over an algebraically closed field, let
`r < K`, let `τ` be sufficient for `K`, and write `B = rationalTaylorCutDegreeBound Q τ`.
Suppose the agreement points `domain i`, `i : ι`, are distinct, `k ≤ A ≤ #ι`, and each
member of a finite set of regular high-cut jets satisfies at least `A` agreement equations.
Then the set has at most
`jetTotalDegree Q * (((#ι - k + 1) * B) / (A - k + 1)) ^ r` elements. -/
theorem card_le_of_highTaylorCuts_of_agreement_sharp [IsAlgClosed F] (center : F)
    (Q : DifferentialPolynomial F r) {K k τ : ℕ} (hτ : TaylorExponentSufficient r K τ)
    (hK : r < K) {ι : Type*} [Fintype ι] (domain received : ι → F)
    (hinj : Function.Injective domain) {A : ℕ} (hkA : k ≤ A)
    (hAn : A ≤ Fintype.card ι) (S : Finset (Fin (r + 1) → F))
    (hS : ∀ jet ∈ S, aeval jet (initialJetEquation center Q) = 0 ∧
      aeval jet (initialJetSeparant center Q) ≠ 0 ∧
      ∀ l, k ≤ l → l < K → aeval jet (commonTaylorNumerator center Q τ l) = 0)
    (hA : ∀ jet ∈ S, A ≤ {i | aeval jet
      (taylorAgreementEquation center Q K τ (domain i) (received i)) = 0}.ncard) :
    (S.card : ℚ) ≤ jetTotalDegree Q *
      (((((Fintype.card ι - k + 1) * rationalTaylorCutDegreeBound Q τ : ℕ) : ℚ) /
        ((A - k + 1 : ℕ) : ℚ))) ^ r := by
  classical
  let T := highTaylorPrimeFamily center Q K k τ
  let B := rationalTaylorCutDegreeBound Q τ
  let cuts : ι → MvPolynomial (Fin (r + 1)) F := fun i ↦
    taylorAgreementEquation center Q K τ (domain i) (received i)
  let R : ℚ := ((((Fintype.card ι - k + 1) * B : ℕ) : ℚ) /
    ((A - k + 1 : ℕ) : ℚ))
  let t : ℚ := ((Fintype.card ι - k + 1 : ℕ) : ℚ) /
    ((A - k + 1 : ℕ) : ℚ)
  have hB : 1 ≤ B := by
    dsimp [B, rationalTaylorCutDegreeBound]
    exact Nat.le_add_right _ _
  have hBpos : 0 < B := by omega
  have hden : 0 < A - k + 1 := by omega
  have hnum : A - k + 1 ≤ Fintype.card ι - k + 1 := by omega
  have ht : 1 ≤ t := by
    apply (le_div_iff₀ (by exact_mod_cast hden)).2
    simpa using (show ((A - k + 1 : ℕ) : ℚ) ≤
      ((Fintype.card ι - k + 1 : ℕ) : ℚ) by exact_mod_cast hnum)
  have hR : R = (B : ℚ) * t := by
    dsimp only [R, t]
    push_cast
    field_simp
  have hcoverNat : S.card ≤
      ∑ P ∈ T, (S.filter fun jet ↦ jet ∈ zeroLocus F P).card := by
    calc
      S.card ≤ (T.biUnion fun P ↦ S.filter fun jet ↦ jet ∈ zeroLocus F P).card := by
        apply Finset.card_le_card
        intro jet hjet
        obtain ⟨P, hPT, hjetP⟩ := exists_mem_highTaylorPrimeFamily_of_regular
          center Q (K := K) (k := k) (τ := τ) jet (hS jet hjet).1 (hS jet hjet).2.1
          (fun l hkl hlK ↦ (hS jet hjet).2.2 l hkl hlK)
        exact Finset.mem_biUnion.mpr ⟨P, hPT,
          Finset.mem_filter.mpr ⟨hjet, hjetP⟩⟩
      _ ≤ ∑ P ∈ T, (S.filter fun jet ↦ jet ∈ zeroLocus F P).card :=
        Finset.card_biUnion_le
  have hcover : (S.card : ℚ) ≤
      ∑ P ∈ T, ((S.filter fun jet ↦ jet ∈ zeroLocus F P).card : ℚ) := by
    exact_mod_cast hcoverNat
  have hcomponent : ∀ P ∈ T,
      ((S.filter fun jet ↦ jet ∈ zeroLocus F P).card : ℚ) ≤
        affineDegree P * R ^ (affineHilbertPolynomial P).natDegree := by
    intro P hPT
    have hPprime : P.IsPrime := isPrime_of_mem_highTaylorPrimeFamily hPT
    have hhigh : highTaylorCutsIdeal center Q K k τ ≤ P :=
      highTaylorCutsIdeal_le_of_mem_highTaylorPrimeFamily hPT
    have hbound := @card_le_of_agreement_off_excluded_sharp
      F F (Fin (r + 1)) ι _ _ _ _ _ P hPprime (initialJetSeparant center Q) cuts B A k
      (fun i ↦ totalDegree_taylorAgreementEquation_le center Q hτ _ _) hkA ∅
      (fun J hPJ hJ hSJ hdim hcuts ↦ by
        have hhighJ : highTaylorCutsIdeal center Q K k τ ≤ J := hhigh.trans hPJ
        have hncard : {i | cuts i ∈ J}.ncard < k := by
          simpa [cuts] using ncard_setOf_taylorAgreementEquation_mem_lt center Q hτ hK hSJ
            hhighJ hdim domain received hinj
        intro jet hjet
        exact False.elim ((not_le_of_gt hncard) hcuts))
      (S.filter fun jet ↦ jet ∈ zeroLocus F P)
      (fun jet hj ↦ by
        rw [Finset.mem_filter] at hj
        exact ⟨hj.2, (hS jet hj.1).2.1, Set.notMem_empty jet⟩)
      (fun jet hj ↦ hA jet (Finset.mem_filter.mp hj).1)
    simpa [cuts, R, B] using hbound
  have hpotential := sum_affineDegree_mul_pow_highTaylorPrimeFamily_le
    (k := k) center Q hτ
  have hratio : R = (B : ℚ) * t := hR
  calc
    (S.card : ℚ) ≤ ∑ P ∈ T,
        ((S.filter fun jet ↦ jet ∈ zeroLocus F P).card : ℚ) := hcover
    _ ≤ ∑ P ∈ T, affineDegree P * R ^ (affineHilbertPolynomial P).natDegree :=
      Finset.sum_le_sum hcomponent
    _ = ∑ P ∈ T, affineDegree P * (B : ℚ) ^ (affineHilbertPolynomial P).natDegree *
          t ^ (affineHilbertPolynomial P).natDegree := by
      apply Finset.sum_congr rfl
      intro P hPT
      rw [hratio, mul_pow]
      ring
    _ ≤ ∑ P ∈ T, affineDegree P * (B : ℚ) ^ (affineHilbertPolynomial P).natDegree *
          t ^ r := by
      apply Finset.sum_le_sum
      intro P hPT
      apply mul_le_mul_of_nonneg_left
      · exact pow_le_pow_right₀ ht
          (natDegree_affineHilbertPolynomial_le_of_mem_highTaylorPrimeFamily hPT)
      · exact mul_nonneg (affineDegree_nonneg P) (by positivity)
    _ = (∑ P ∈ T, affineDegree P * (B : ℚ) ^
          (affineHilbertPolynomial P).natDegree) * t ^ r := by
      rw [Finset.sum_mul]
    _ ≤ (jetTotalDegree Q * (B : ℚ) ^ r) * t ^ r :=
      mul_le_mul_of_nonneg_right hpotential (by positivity)
    _ = jetTotalDegree Q * R ^ r := by
      rw [hratio, mul_pow]
      ring
    _ = jetTotalDegree Q *
        (((((Fintype.card ι - k + 1) * rationalTaylorCutDegreeBound Q τ : ℕ) : ℚ) /
          ((A - k + 1 : ℕ) : ℚ))) ^ r := by
      simp [R, B]

private theorem mem_restrictCappedDegree_of_bounds (P : MvPolynomial (Fin 2) F)
    {b c : ℕ} (hb : P.totalDegree ≤ b) (hc : P.degreeOf 1 ≤ c) :
    P ∈ restrictCappedDegree (Fin 2) F 1 b c := by
  rw [mem_restrictCappedDegree]
  intro m hm
  exact ⟨(le_totalDegree hm).trans hb, (monomial_le_degreeOf 1 hm).trans hc⟩

/-- Let `Q` have total jet degree at most `j` and first-derivative degree at most `r`. If the
first-order Taylor chart equations fit total-degree cap `b`, every finite set of regular jets
satisfying all high cuts and at least `A` agreement equations has size at most the capped mixed
volume for derivative cap `min b (τ * (r - 1) + (K - 1))` times `(n-k+1)/(A-k+1)`. -/
theorem card_le_of_firstOrderHighTaylorCuts_of_agreement_capped [IsAlgClosed F]
    (center : F) (Q : DifferentialPolynomial F 1) {K k τ j r b : ℕ}
    (hτ : TaylorExponentSufficient 1 K τ) (hK : 1 < K)
    (hb : 0 < b) (hc : 0 < min b (τ * (r - 1) + (K - 1))) (hjb : j ≤ b)
    (hrc : r ≤ min b (τ * (r - 1) + (K - 1)))
    (hchart : 1 + τ * (j - 1) ≤ b)
    (hr : 0 < r) (hjet : jetTotalDegree Q ≤ j)
    (hderiv : Q.degreeOf (some 1) ≤ r)
    {n A : ℕ} (domain : Fin n ↪ F) (received : Fin n → F)
    (hkA : k ≤ A) (hAn : A ≤ n) (S : Finset (Fin 2 → F))
    (hS : ∀ jet ∈ S,
      aeval jet (initialJetEquation center Q) = 0 ∧
      aeval jet (initialJetSeparant center Q) ≠ 0 ∧
      ∀ l : {l : Fin K // k ≤ l.val},
        aeval jet (commonTaylorNumerator center Q τ l.val) = 0)
    (hA : ∀ jet ∈ S, A ≤
      {i | aeval jet (taylorAgreementEquation center Q K τ (domain i) (received i)) = 0}.ncard) :
    (S.card : ℚ) ≤
      (cappedDegreeMixedVolume j r b (min b (τ * (r - 1) + (K - 1))) : ℕ) *
      (((n - k + 1 : ℕ) : ℚ) / ((A - k + 1 : ℕ) : ℚ)) := by
  classical
  by_cases hempty : S = ∅
  · subst S
    simp only [Finset.card_empty, Nat.cast_zero]
    positivity
  obtain ⟨x₀, hx₀⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
  have hB : rationalTaylorCutDegreeBound Q τ ≤ b := by
    simp only [rationalTaylorCutDegreeBound]
    calc
      1 + τ * (jetTotalDegree Q - 1) ≤ 1 + τ * (j - 1) := by
        exact Nat.add_le_add_left (Nat.mul_le_mul_left τ
          (Nat.sub_le_sub_right hjet 1)) 1
      _ ≤ b := hchart
  let c := min b (τ * (r - 1) + (K - 1))
  let highCuts := highTaylorCutList center Q K k τ
  let cuts : Fin n → MvPolynomial (Fin 2) F := fun i ↦
    taylorAgreementEquation center Q K τ (domain i) (received i)
  have hg0 : initialJetEquation center Q ≠ 0 :=
    initialJetEquation_ne_zero_of_initialJetSeparant_ne_zero center Q
      fun hs ↦ (hS x₀ hx₀).2.1 (by rw [hs, map_zero])
  have hg : initialJetEquation center Q ∈ restrictCappedDegree (Fin 2) F 1 j r :=
    mem_restrictCappedDegree_of_bounds _
      ((totalDegree_initialJetEquation_le center Q).trans hjet)
      ((degreeOf_initialJetEquation_le center Q).trans hderiv)
  have hgbc : initialJetEquation center Q ∈ restrictCappedDegree (Fin 2) F 1 b c :=
    mem_restrictCappedDegree_of_bounds _
      ((totalDegree_initialJetEquation_le center Q).trans (hjet.trans hjb))
      ((degreeOf_initialJetEquation_le center Q).trans (hderiv.trans hrc))
  have hsbc : initialJetSeparant center Q ∈ restrictCappedDegree (Fin 2) F 1 b c :=
    mem_restrictCappedDegree_of_bounds _
      ((totalDegree_initialJetSeparant_le center Q).trans
        ((Nat.sub_le_sub_right hjet 1).trans (by omega)))
      ((degreeOf_initialJetSeparant_firstOrder_le center Q).trans
        ((Nat.sub_le_sub_right hderiv 1).trans (by omega)))
  have hhigh : ∀ f ∈ highCuts, f ∈ restrictCappedDegree (Fin 2) F 1 b c := by
    intro f hf
    obtain ⟨l, hkl, hlK, rfl⟩ := mem_highTaylorCutList.mp hf
    have htotal :=
      (totalDegree_commonTaylorNumerator_le center Q (hτ ⟨l, hlK⟩)).trans hB
    have hdegree :
        (commonTaylorNumerator center Q τ l).degreeOf 1 ≤ τ * (r - 1) + (K - 1) :=
      (degreeOf_commonTaylorNumerator_firstOrder_le center Q r K τ hτ hr hderiv
        ⟨l, hlK⟩).trans (Nat.add_le_add_left (by omega) _)
    apply mem_restrictCappedDegree_of_bounds
    · exact htotal
    · simpa [c] using le_min ((degreeOf_le_totalDegree _ _).trans htotal) hdegree
  have hcuts : ∀ i, cuts i ∈ restrictCappedDegree (Fin 2) F 1 b c := by
    intro i
    have htotal :=
      (totalDegree_taylorAgreementEquation_le center Q hτ (domain i) (received i)).trans hB
    have hdegree :
        (cuts i).degreeOf 1 ≤ τ * (r - 1) + (K - 1) :=
      (degreeOf_taylorAgreementEquation_firstOrder_le center Q r K τ hτ hr hderiv
        (domain i) (received i))
    apply mem_restrictCappedDegree_of_bounds
    · exact htotal
    · simpa [c] using le_min ((degreeOf_le_totalDegree _ _).trans htotal) hdegree
  have hS' : ∀ jet ∈ S, aeval jet (initialJetEquation center Q) = 0 ∧
      aeval jet (initialJetSeparant center Q) ≠ 0 ∧
      ∀ f ∈ highCuts, aeval jet f = 0 := by
    intro jet hjetS
    refine ⟨(hS jet hjetS).1, (hS jet hjetS).2.1, ?_⟩
    intro f hf
    obtain ⟨l, hkl, hlK, rfl⟩ := mem_highTaylorCutList.mp hf
    exact (hS jet hjetS).2.2 ⟨⟨l, hlK⟩, hkl⟩
  have hUnique : ∀ J : Ideal (MvPolynomial (Fin 2) F),
      J.IsPrime → initialJetSeparant center Q ∉ J → initialJetEquation center Q ∈ J →
      (∀ f ∈ highCuts, f ∈ J) →
      ∀ U : Finset (Fin n), U.card = k →
      ∀ x y : Fin 2 → F,
        x ∈ zeroLocus F J → aeval x (initialJetSeparant center Q) ≠ 0 →
        y ∈ zeroLocus F J → aeval y (initialJetSeparant center Q) ≠ 0 →
        (∀ i ∈ U, aeval x (cuts i) = 0 ∧ aeval y (cuts i) = 0) → x = y := by
    intro J hJ hSJ hgJ hhighJ U hU x y hxJ hxs hyJ hys hzero
    have hhighIdeal : highTaylorCutsIdeal center Q K k τ ≤ J := by
      rw [← span_setOf_mem_highTaylorCutList]
      apply Ideal.span_le.mpr
      intro f hf
      exact hhighJ f hf
    exact eq_of_mem_zeroLocus_of_highTaylorCutsIdeal_le center Q hτ hK hhighIdeal
      domain received U domain.injective.injOn (by rw [hU]) hxJ hyJ hxs hys
      (fun i hi ↦ (hzero i hi).1) (fun i hi ↦ (hzero i hi).2)
  exact cappedDegreeHypersurface_incidence_sharp hb hc hkA hAn
    (initialJetEquation center Q) (initialJetSeparant center Q) hg0 hg hgbc hsbc
    highCuts hhigh cuts hcuts S hS' hA hUnique

end

end PolynomialDifferential

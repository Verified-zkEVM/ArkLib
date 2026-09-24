/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.Polynomial.Differential.BaseChange
public import ArkLib.Data.Polynomial.Differential.TaylorChartGeometry
public import ArkLib.Data.Polynomial.Differential.TaylorChartIncidence

/-!
# Coefficient extension of rational Taylor charts

An injective coefficient map preserves nonzero separant specializations. Over an infinite target
domain, finite families of regular solutions share a center after mapping coefficients. Over an
infinite extension field, their polynomial jets form a cardinality-preserving family satisfying the
initial equation, high Taylor cuts, and received-word agreement bounds.

## Main statements

* `exists_forall_jetEvaluation_ne_zero_map`: mapped nonzero separants share a center over an
  infinite target domain.
* `exists_regular_solution_jet_family_of_exponent`: regular solution families embed into a chart
  with any sufficient common Taylor exponent.
* `card_le_of_regular_solutions_agreement`: regular polynomial solutions obey the sharp agreement
  bound after passage to an algebraically closed extension.

## References

* [DKT26]
-/

@[expose] public section

namespace PolynomialDifferential

open MvPolynomial

open Classical in
/-- A finite family with nonzero separant specialization has a common regular center after an
injective coefficient map into an infinite domain. The jet coordinate may be any `j`. -/
theorem exists_forall_jetEvaluation_ne_zero_map {F E : Type*} [CommSemiring F] [CommRing E]
    [IsDomain E] [Infinite E] {r : ℕ} (f : F →+* E) (hf : Function.Injective f)
    (Q : DifferentialPolynomial F r) (S : Finset (Polynomial F)) (j : Fin (r + 1))
    (hregular : ∀ P ∈ S, differentialSpecialization (separant Q j) P ≠ 0) :
    ∃ center : E, ∀ P ∈ S,
      jetEvaluation (separant (MvPolynomial.map f Q) j) center
        (polynomialJet center (P.map f)) ≠ 0 := by
  classical
  have hregularMap : ∀ P ∈ S.image (Polynomial.map f),
      differentialSpecialization (separant (MvPolynomial.map f Q) j) P ≠ 0 := by
    intro P hP
    obtain ⟨P, hPS, rfl⟩ := Finset.mem_image.mp hP
    rw [← map_separant]
    exact (map_differentialSpecialization_ne_zero_iff hf (separant Q j) P).2
      (hregular P hPS)
  obtain ⟨center, hc⟩ :=
    exists_forall_jetEvaluation_ne_zero (separant (MvPolynomial.map f Q) j)
      (S.image (Polynomial.map f)) hregularMap
  exact ⟨center, fun P hP ↦ hc _ (Finset.mem_image.mpr ⟨P, hP, rfl⟩)⟩

open Classical in
/-- A finite family of regular polynomial solutions embeds into a rational Taylor chart over an
infinite extension field. Each jet satisfies the initial equation, all high cuts for degree below
`k`, and the agreement equations at the mapped evaluation points. The chart exponent `τ` may be
any exponent sufficient for all coefficients before `K`. The pivot nonvanishing conditions are
required over the chart field `E`. -/
theorem exists_regular_solution_jet_family_of_exponent
    {F E : Type*} [Field F] [Field E] [Infinite E] {r : ℕ}
    (f : F →+* E) (Q : DifferentialPolynomial F r) (K k τ : ℕ)
    (hτ : TaylorExponentSufficient r K τ) (hkK : k ≤ K)
    (S : Finset (Polynomial F)) {A : ℕ} {ι : Type*} [Fintype ι]
    (domain received : ι → F)
    (hdegree : ∀ P ∈ S, P.degree < k)
    (hsol : ∀ P ∈ S, differentialSpecialization Q P = 0)
    (hsep : ∀ P ∈ S, differentialSpecialization (separant Q (Fin.last r)) P ≠ 0)
    (hbin : ∀ i, r < i → i < K → (i.choose r : E) ≠ 0)
    (hagree : ∀ P ∈ S,
      A ≤ (Finset.univ.filter (fun i ↦ P.eval (domain i) = received i)).card) :
    ∃ (center : E) (J : Finset (Fin (r + 1) → E)), J.card = S.card ∧
      ∀ jet ∈ J,
        aeval jet (initialJetEquation center (MvPolynomial.map f Q)) = 0 ∧
        aeval jet (initialJetSeparant center (MvPolynomial.map f Q)) ≠ 0 ∧
        (∀ l : Fin K, k ≤ l.val →
          aeval jet (commonTaylorNumerator center (MvPolynomial.map f Q) τ l.val) = 0) ∧
        A ≤ (Finset.univ.filter (fun i ↦
          aeval jet (taylorAgreementEquation center (MvPolynomial.map f Q) K τ
            (f (domain i)) (f (received i))) = 0)).card := by
  classical
  let QE := MvPolynomial.map f Q
  let SE := S.image (Polynomial.map f)
  have hSE := map_regularSolutionFamily (f := f) f.injective Q S (j := Fin.last r) k
    hdegree hsol hsep
  obtain ⟨center, hcenter⟩ :=
    exists_forall_jetEvaluation_ne_zero_map f f.injective Q S (Fin.last r) hsep
  have hcenterMapped : ∀ P ∈ SE,
      jetEvaluation (separant QE (Fin.last r)) center (polynomialJet center P) ≠ 0 := by
    intro P hP
    obtain ⟨P₀, hP₀, rfl⟩ := Finset.mem_image.mp hP
    exact hcenter P₀ hP₀
  refine ⟨center, SE.image (polynomialJet (d := r) center), ?_, ?_⟩
  · rw [card_image_polynomialJet center QE K hbin SE
      (fun P hP ↦ (hSE P hP).1.trans_le (Nat.cast_le.mpr hkK))
      (fun P hP ↦ (hSE P hP).2.1)
      (fun P hP ↦ hcenterMapped P hP)]
    exact Finset.card_image_of_injective _ (Polynomial.map_injective f f.injective)
  · intro jet hjet
    obtain ⟨P, hP, rfl⟩ := Finset.mem_image.mp hjet
    obtain ⟨P₀, hP₀, rfl⟩ := Finset.mem_image.mp hP
    have hp := hSE (Polynomial.map f P₀) (Finset.mem_image.mpr ⟨P₀, hP₀, rfl⟩)
    have hs := hcenter P₀ hP₀
    refine ⟨aeval_initialJetEquation_polynomialJet center QE (Polynomial.map f P₀) hp.2.1,
      ?_, ?_, ?_⟩
    · rwa [aeval_initialJetSeparant]
    · intro l hl
      exact (mem_zeroLocus_highTaylorCutsIdeal_iff center QE).mp
        (polynomialJet_mem_zeroLocus_highTaylorCutsIdeal center QE (Polynomial.map f P₀)
          hp.2.1 hs τ hp.1 hbin) l.val hl l.isLt
    · have hcut :
          (Finset.univ.filter (fun i ↦
            aeval (polynomialJet center (Polynomial.map f P₀))
              (taylorAgreementEquation center QE K τ (f (domain i)) (f (received i))) = 0)) =
          Finset.univ.filter (fun i ↦
            (Polynomial.map f P₀).eval (f (domain i)) = f (received i)) := by
        ext i
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        rw [taylorAgreementEquation_eq_zero_iff center QE hτ
          (polynomialJet center (Polynomial.map f P₀))
          (by rwa [aeval_initialJetSeparant]) (f (domain i)) (f (received i))]
        rw [rationalTaylorPolynomial_polynomialJet center QE (Polynomial.map f P₀)
          hp.2.1 hs (hp.1.trans_le (Nat.cast_le.mpr hkK)) hbin]
      calc
        A ≤ (Finset.univ.filter (fun i ↦ P₀.eval (domain i) = received i)).card :=
          hagree P₀ hP₀
        _ = (Finset.univ.filter (fun i ↦
            (Polynomial.map f P₀).eval (f (domain i)) = f (received i))).card :=
          by simp only [Polynomial.eval_map_apply, f.injective.eq_iff]
        _ = (Finset.univ.filter (fun i ↦
            aeval (polynomialJet center (Polynomial.map f P₀))
              (taylorAgreementEquation center QE K τ (f (domain i)) (f (received i))) = 0)).card :=
          by rw [hcut]

open Classical in
/-- A finite family of regular polynomial solutions over `F` with degree below `k` and at least
`A` agreements on distinct evaluation points has size at most
`jetTotalDegree Q * (((n - k + 1) * B) / (A - k + 1)) ^ r` over any algebraically closed field
extension, where `B = rationalTaylorCutDegreeBound Q τ` for a sufficient exponent `τ`. -/
theorem card_le_of_regular_solutions_agreement
    {F E : Type*} [Field F] [Field E] [IsAlgClosed E] [Algebra F E] {r : ℕ}
    (Q : DifferentialPolynomial F r) (K k τ : ℕ)
    (hτ : TaylorExponentSufficient r K τ) (hK : r < K) (hkK : k ≤ K)
    {n A : ℕ} (domain : Fin n ↪ F) (received : Fin n → F)
    (hkA : k ≤ A) (hAn : A ≤ n)
    (S : Finset (Polynomial F))
    (hdegree : ∀ P ∈ S, P.degree < k)
    (hsol : ∀ P ∈ S, differentialSpecialization Q P = 0)
    (hsep : ∀ P ∈ S, differentialSpecialization (separant Q (Fin.last r)) P ≠ 0)
    (hbin : ∀ i, r < i → i < K → (i.choose r : F) ≠ 0)
    (hagree : ∀ P ∈ S,
      A ≤ (Finset.univ.filter fun i ↦ P.eval (domain i) = received i).card) :
    (S.card : ℚ) ≤ jetTotalDegree Q *
      (((((n - k + 1) * rationalTaylorCutDegreeBound Q τ : ℕ) : ℚ) /
        ((A - k + 1 : ℕ) : ℚ))) ^ r := by
  classical
  let f : F →+* E := algebraMap F E
  let QE := MvPolynomial.map f Q
  have hbinE : ∀ i, r < i → i < K → (i.choose r : E) ≠ 0 := by
    intro i hir hiK hz
    apply hbin i hir hiK
    exact f.injective (by simpa using hz)
  obtain ⟨center, J, hcard, hJ⟩ := exists_regular_solution_jet_family_of_exponent
    f Q K k τ hτ hkK S domain received hdegree hsol hsep hbinE hagree
  let domainE : Fin n ↪ E := domain.trans ⟨f, f.injective⟩
  have hcount := card_le_of_highTaylorCuts_of_agreement_sharp center QE hτ hK
    domainE (fun i ↦ f (received i)) domainE.injective hkA (by simpa using hAn) J
    (fun jet hjet ↦ by
      obtain ⟨hinit, hsep, hcuts, -⟩ := hJ jet hjet
      refine ⟨hinit, hsep, ?_⟩
      intro l hkl hlK
      exact hcuts ⟨l, hlK⟩ hkl)
    (fun jet hjet ↦ by
      obtain ⟨-, -, -, hagreeJet⟩ := hJ jet hjet
      have hfilter : ({i | aeval jet
          (taylorAgreementEquation center QE K τ (domainE i) (f (received i))) = 0} :
          Set (Fin n)) =
          (Finset.univ.filter (fun i ↦ aeval jet
            (taylorAgreementEquation center QE K τ (domainE i) (f (received i))) = 0) :
            Finset (Fin n)) := by
        ext i
        simp only [Set.mem_ofPred_eq, Finset.mem_coe, Finset.mem_filter,
          Finset.mem_univ, true_and]
      rw [hfilter, Set.ncard_coe_finset]
      exact hagreeJet)
  rw [hcard] at hcount
  simpa [QE, rationalTaylorCutDegreeBound, jetTotalDegree_map_eq f.injective] using hcount
end PolynomialDifferential

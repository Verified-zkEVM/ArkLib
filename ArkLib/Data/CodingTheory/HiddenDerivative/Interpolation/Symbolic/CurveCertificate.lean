/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.Global.Multiplicity
public import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.Local.Contact
public import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.Symbolic.ReceivedCurve
public import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.WeightedSupport.Basic
public import ArkLib.Data.Polynomial.Differential.SeparantChain
public import Mathlib.Algebra.CharP.Algebra

/-!
# Symbolic curve certificates

A symbolic curve certificate is a differential equation over a polynomial challenge. It bounds
the challenge degree of every coefficient and its total jet degree, remains nonzero after every
field specialization, and vanishes on every sufficiently agreeing low-degree polynomial. A rank
bound on a finite family of source monomials constructs such a certificate.

## Main statements

* `Certificate`: a symbolic curve equation with challenge, jet-degree, and specialization bounds;
  `Certificate.nonzero` derives that its equation is nonzero.
* `Certificate.exists_separantChain` and
  `Certificate.exists_exceptional_stage_coverage`: the equation has a separant chain, and outside
  a bounded exceptional set every solution reaches a regular stage.
* `exists_certificate_of_monomial_rank_bound` and `exists_certificate_of_rank_bound`: a finite
  matrix rank bound or weighted-support bound constructs a certificate.

## References

* [DKT26]
-/

@[expose] public section

open PolynomialDifferential

noncomputable section

namespace ReedSolomon.HiddenDerivative.SymbolicReceivedCurve

open Polynomial MvPolynomial
universe uι uκ uK u

/-- A symbolic received curve has a differential equation whose coefficients have bounded
challenge degree, whose monomials have bounded total jet degree, and whose specializations are
nonzero and vanish on sufficiently agreeing low-degree polynomials. -/
structure Certificate {ι : Type uι} {F : Type u} [Fintype ι] [Field F] (A k ℓ ν d h : ℕ)
    (centers : ι ↪ F) (w : ι → F[X]) where
  /-- The differential equation with coefficients in the challenge polynomial ring `F[X]`. -/
  Q : DifferentialPolynomial F[X] d
  /-- Every coefficient of the equation has challenge degree at most `h`. -/
  challengeDegree_le : ∀ u, (Q.coeff u).natDegree ≤ h
  /-- Every monomial of the equation has total jet degree at most `ν`. -/
  totalJetDegree_le : ∀ u ∈ Q.support, totalJetDegree u ≤ ν
  /-- Every field specialization is nonzero and vanishes on sufficiently agreeing polynomials. -/
  specialization_sound : ∀ {E : Type u} [Field E] (ρ : F →+* E) (z : E),
    MvPolynomial.map (Polynomial.eval₂RingHom ρ z) Q ≠ 0 ∧
      jetTotalDegree (MvPolynomial.map (Polynomial.eval₂RingHom ρ z) Q) ≤ ν ∧
      ∀ (indices : Finset ι) (P : E[X]), P.degree < k → A ≤ indices.card →
        (∀ i ∈ indices, P.eval (ρ (centers i)) = (w i).eval₂ ρ z) →
        differentialSpecialization (MvPolynomial.map (Polynomial.eval₂RingHom ρ z) Q) P = 0

namespace Certificate

variable {ι : Type uι} {F : Type u} [Fintype ι] [Field F] {A k ℓ ν d h : ℕ}
  {centers : ι ↪ F} {w : ι → F[X]}

/-- Universal nonvanishing under specialization implies the equation is nonzero. -/
theorem nonzero (cert : Certificate.{uι, u} A k ℓ ν d h centers w) : cert.Q ≠ 0 := by
  intro hzero
  have h := (cert.specialization_sound (E := F) (RingHom.id F) 0).1
  rw [hzero, map_zero] at h
  exact h rfl

/-- The support bound of a certificate gives the corresponding polynomial total jet-degree bound. -/
theorem jetTotalDegree_le (cert : Certificate.{uι, u} A k ℓ ν d h centers w) :
    jetTotalDegree cert.Q ≤ ν := by
  rw [jetTotalDegree_le_iff]
  exact cert.totalJetDegree_le

/-- A certificate equation has a separant chain when its jet degrees satisfy the characteristic
bound. -/
theorem exists_separantChain (cert : Certificate.{uι, u} A k ℓ ν d h centers w)
    (hchar : ringChar F = 0 ∨ ν < ringChar F) :
    ∃ stages terminal, SeparantChain cert.Q stages terminal := by
  apply exists_separantChain_of_ringChar cert.nonzero
  have hchar' : ringChar F[X] = 0 ∨ ν < ringChar F[X] := by
    rw [Algebra.ringChar_eq F F[X]] at hchar
    exact hchar
  exact hchar'.imp_right (fun h ↦ cert.jetTotalDegree_le.trans_lt h)

/-- Outside at most `h` challenge values, every sufficiently agreeing solution of a specialized
certificate equation solves a listed stage with nonzero specialized separant. -/
theorem exists_exceptional_stage_coverage
    (cert : Certificate.{uι, u} A k ℓ ν d h centers w)
    {stages : List (SeparantStage F[X] d)} {terminal : DifferentialPolynomial F[X] d}
    (hc : SeparantChain cert.Q stages terminal) {E : Type u} [Field E] (ρ : F →+* E) :
    ∃ exceptional : Finset E, exceptional.card ≤ h ∧
      ∀ z ∉ exceptional, ∀ (indices : Finset ι) (P : E[X]),
        P.degree < k → A ≤ indices.card →
        (∀ i ∈ indices, P.eval (ρ (centers i)) = (w i).eval₂ ρ z) →
        ∃ stage ∈ stages,
          differentialSpecialization
            (MvPolynomial.map (Polynomial.eval₂RingHom ρ z) stage.1) P = 0 ∧
          differentialSpecialization
            (separant (MvPolynomial.map (Polynomial.eval₂RingHom ρ z) stage.1) stage.2) P ≠
              0 := by
  obtain ⟨exceptional, hcard, hcover⟩ :=
    hc.exists_finset_regular_stage cert.challengeDegree_le ρ ρ.injective
  refine ⟨exceptional, hcard, ?_⟩
  intro z hz indices P hdegree hsize hagree
  exact hcover z hz P ((cert.specialization_sound (E := E) ρ z).2.2 indices P
    hdegree hsize hagree)

end Certificate

/-- A finite monomial family and a bound on its constraint-matrix rank produce a symbolic curve
certificate. The rank is measured after an injective map into any field. -/
theorem exists_certificate_of_monomial_rank_bound {F : Type u} {ι : Type uι} {κ : Type uκ}
    {K : Type uK} [Field F] [Fintype ι]
    [Fintype κ] [Field K] {d D m A k ℓ ν r : ℕ}
    (hbudget : 0 < m * A) (hkD : k ≤ D + 1) (centers : ι ↪ F) (w : ι → F[X])
    (hw : ∀ i, (w i).natDegree ≤ ℓ) (columns : κ → SourceColumn d)
    (hcolumns : Function.Injective columns) (hy₀ : ∀ j, (columns j).y₀ ≤ ν)
    (hdegree : ∀ j, totalJetDegree (columns j).exponent ≤ ν)
    (hweight : ∀ j, Finsupp.weight (differentialWeight D) (columns j).exponent < m * A)
    (φ : F[X] →+* K) (hφ : Function.Injective φ)
    (hrank :
      ((supportedLocalConstraintMatrix m (fun i ↦ Polynomial.C (centers i)) w columns).map
        φ).rank ≤ r)
    (hrκ : r < Fintype.card κ) :
    Nonempty
      (Certificate.{uι, u} A k ℓ ν d
        (r * (ℓ * ν) / (Fintype.card κ - r)) centers w) := by
  classical
  have hrankLocal :
      ((localConstraintMatrix m (fun i ↦ Polynomial.C (centers i)) w columns).map φ).rank ≤
        r := by
    rw [← rank_map_supportedLocalConstraintMatrix φ m
      (fun i ↦ Polynomial.C (centers i)) w columns]
    exact hrank
  obtain ⟨v, _, hvdegree, hspan, _, hconstraints⟩ :=
    exists_primitive_interpolant_of_rank_le.{u, uι, uκ, uK, u} m ℓ ν
      (fun i ↦ centers i) w hw columns
      hcolumns hy₀ φ hφ hrankLocal hrκ
  let Q : DifferentialPolynomial F[X] d := SourceColumn.interpolant columns v
  have hcoeffdegree := SourceColumn.coeff_interpolant_natDegree_le columns hcolumns v hvdegree
  have hQweight : differentialWeightedDegree D Q < m * A := by
    rw [differentialWeightedDegree, MvPolynomial.weightedTotalDegree,
      Finset.sup_lt_iff hbudget]
    intro u hu
    obtain ⟨j, _, hj⟩ := Finset.mem_biUnion.mp (MvPolynomial.support_sum hu)
    have heq : u = (columns j).exponent := by
      simpa using MvPolynomial.support_monomial_subset hj
    exact heq ▸ hweight j
  refine ⟨⟨Q, ?_, SourceColumn.interpolant_totalJetDegree_le columns hdegree v, ?_⟩⟩
  · intro u
    exact hcoeffdegree u
  · intro E _ ρ z
    let ψ := Polynomial.eval₂RingHom ρ z
    have hnonzero' : MvPolynomial.map ψ Q ≠ 0 := by
      simpa only [Q] using SourceColumn.map_interpolant_ne_zero hcolumns ψ
        (Ideal.comp_ne_zero_of_span_range_eq_top hspan ψ)
    refine ⟨hnonzero', ?_, ?_⟩
    · simpa only [Q] using SourceColumn.map_interpolant_jetTotalDegree_le ψ columns hdegree v
    · intro indices P hP hsize hagree
      have hPdegree : P.natDegree ≤ D := by
        by_cases hP0 : P = 0
        · simp [hP0]
        · have hdeg := (Polynomial.natDegree_lt_iff_degree_lt hP0).mpr hP
          omega
      have hQweight_map :
          differentialWeightedDegree D (MvPolynomial.map ψ Q) < m * A := by
        rw [differentialWeightedDegree, MvPolynomial.weightedTotalDegree,
          Finset.sup_lt_iff hbudget]
        intro u hu
        have hsource := MvPolynomial.support_map_subset ψ Q hu
        obtain ⟨j, _, hj⟩ := Finset.mem_biUnion.mp (MvPolynomial.support_sum hsource)
        have heq : u = (columns j).exponent := by
          simpa [Q] using MvPolynomial.support_monomial_subset hj
        exact heq ▸ hweight j
      have hlocal : ∀ i, SatisfiesLocalConstraints m (ρ (centers i))
          ((w i).eval₂ ρ z) (MvPolynomial.map ψ Q) := by
        intro i
        have hi := SatisfiesLocalConstraints.map ψ m (Polynomial.C (centers i))
          (w i) Q (hconstraints i)
        change SatisfiesLocalConstraints m
          (Polynomial.eval₂ ρ z (Polynomial.C (centers i))) ((w i).eval₂ ρ z)
          (MvPolynomial.map ψ Q) at hi
        simpa only [Polynomial.eval₂_C] using hi
      have hinj : Set.InjOn (fun i ↦ ρ (centers i)) (indices : Set ι) := by
        intro i _ j _ hij
        exact centers.injective (ρ.injective hij)
      exact differentialSpecialization_eq_zero_of_differentialWeightedDegree_lt
        (fun i ↦ ρ (centers i)) (fun i ↦ (w i).eval₂ ρ z) indices hQweight_map
        (fun i _ ↦ hlocal i) P hPdegree hinj hsize hagree

/-- A weighted-support cutoff supplies the monomial-weight bounds needed for certificate
construction from a matrix-rank estimate. -/
theorem exists_certificate_of_rank_bound {F : Type u} {ι : Type uι} {κ : Type uκ}
    {K : Type uK} [Field F] [Fintype ι]
    [Fintype κ] [Field K] {d D m W A k ℓ ν r : ℕ} {L : ℝ}
    (hL : L ≤ (m * A : ℕ)) (hbudget : 0 < m * A) (hkD : k ≤ D + 1)
    (centers : ι ↪ F) (w : ι → F[X]) (hw : ∀ i, (w i).natDegree ≤ ℓ)
    (columns : κ → SourceColumn d) (hcolumns : Function.Injective columns)
    (hy₀ : ∀ j, (columns j).y₀ ≤ ν)
    (hdegree : ∀ j, totalJetDegree (columns j).exponent ≤ ν)
    (hband : ∀ j, WeightedSupportEligible D d W L (columns j).exponent)
    (φ : F[X] →+* K) (hφ : Function.Injective φ)
    (hrank :
      ((supportedLocalConstraintMatrix m (fun i ↦ Polynomial.C (centers i)) w columns).map
        φ).rank ≤ r)
    (hrκ : r < Fintype.card κ) :
    Nonempty
      (Certificate.{uι, u} A k ℓ ν d
        (r * (ℓ * ν) / (Fintype.card κ - r)) centers w) := by
  exact exists_certificate_of_monomial_rank_bound hbudget hkD centers w hw columns hcolumns
    hy₀ hdegree
    (fun j ↦ weight_differentialWeight_lt_of_weightedSupportEligible hL (hband j))
    φ hφ hrank hrκ

end ReedSolomon.HiddenDerivative.SymbolicReceivedCurve

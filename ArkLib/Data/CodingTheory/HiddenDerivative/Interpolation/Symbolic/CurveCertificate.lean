/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.Global.Multiplicity
public import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.Index
public import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.Symbolic.ReceivedCurve
public import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.Symbolic.LocalRank
public import Mathlib.FieldTheory.RatFunc.Basic

/-!
# Certificates for symbolic received curves

A polynomial-coefficient differential equation certifies a received curve when its coefficients
have bounded challenge degree, its jet degree is bounded, and every challenge specialization is
nonzero and vanishes on every sufficiently agreeing message polynomial. A finite rank surplus
constructs such a certificate from distinct source columns with bounded specialization weight.

## Main statements

* `CurveCertificate`: the challenge-degree, jet-degree and specialization guarantees.
* `exists_curveCertificate_of_rank_bound`: construction from a finite matrix rank bound.

## References

* [DKT26]
-/

@[expose] public section

open Polynomial PolynomialDifferential

noncomputable section

namespace ReedSolomon.HiddenDerivative.SymbolicReceivedCurve

open MvPolynomial

/-- A symbolic differential equation for a received polynomial curve, with certified challenge
height `h` and jet-degree cap `ν`. -/
structure CurveCertificate (F : Type*) [Field F] {n : ℕ} (A k ℓ ν d h : ℕ)
    (centers : Fin n ↪ F) (received : Fin n → F[X]) where
  /-- The polynomial-coefficient differential equation. -/
  Q : DifferentialPolynomial F[X] d
  /-- Every coefficient of `Q` has challenge degree at most `h`. -/
  challengeDegree_le : ∀ u, (Q.coeff u).natDegree ≤ h
  /-- Every monomial of `Q` has total jet degree at most `ν`. -/
  totalJetDegree_le : ∀ u ∈ Q.support, totalJetDegree u ≤ ν
  /-- Every challenge specialization is nonzero, has jet degree at most `ν`, and vanishes on each
  degree-bounded polynomial agreeing with the received curve at at least `A` coordinates. -/
  specialization_sound : ∀ {E : Type*} [Field E] (ι : F →+* E) (z : E),
    MvPolynomial.map (Polynomial.eval₂RingHom ι z) Q ≠ 0 ∧
    jetTotalDegree (MvPolynomial.map (Polynomial.eval₂RingHom ι z) Q) ≤ ν ∧
    ∀ (indices : Finset (Fin n)) (P : E[X]), P.degree < k → A ≤ indices.card →
      (∀ i ∈ indices, P.eval (ι (centers i)) = (received i).eval₂ ι z) →
      differentialSpecialization (MvPolynomial.map (Polynomial.eval₂RingHom ι z) Q) P = 0

private theorem satisfiesLocalConstraints_map {R S : Type*} [CommRing R] [CommRing S] {d : ℕ}
    (φ : R →+* S) (m : ℕ) (center received : R) (Q : DifferentialPolynomial R d)
    (hQ : SatisfiesLocalConstraints m center received Q) :
    SatisfiesLocalConstraints m (φ center) (φ received) (MvPolynomial.map φ Q) := by
  rw [satisfiesLocalConstraints_iff_coeff_eq_zero] at hQ ⊢
  intro e he
  rw [← map_unscaledLocalSubstitution, MvPolynomial.coeff_map]
  simpa using congrArg φ (hQ e he)

private theorem totalJetDegree_interpolant_le {F : Type*} [Field F] {d N ν : ℕ}
    (columns : Fin N → SourceColumn d)
    (hdegree : ∀ j, totalJetDegree (columns j).exponent ≤ ν) (v : Fin N → F[X]) :
    ∀ u ∈ (SourceColumn.interpolant columns v).support, totalJetDegree u ≤ ν := by
  classical
  intro u hu
  obtain ⟨j, _, hj⟩ := Finset.mem_biUnion.mp (MvPolynomial.support_sum hu)
  have heq : u = (columns j).exponent := by
    simpa using MvPolynomial.support_monomial_subset hj
  simpa [heq] using hdegree j

private theorem jetTotalDegree_map_interpolant_le {F E : Type*} [Field F] [Field E]
    {d N ν : ℕ} (columns : Fin N → SourceColumn d)
    (hdegree : ∀ j, totalJetDegree (columns j).exponent ≤ ν) (v : Fin N → F[X])
    (ι : F →+* E) (z : E) :
    jetTotalDegree (MvPolynomial.map (Polynomial.eval₂RingHom ι z)
      (SourceColumn.interpolant columns v)) ≤ ν := by
  rw [jetTotalDegree_le_iff]
  intro u hu
  have hs := MvPolynomial.support_map_subset _ _ hu
  simpa [totalJetDegree, Finsupp.degree_eq_sum] using
    totalJetDegree_interpolant_le columns hdegree v u hs

/-- Distinct source columns with bounded specialization weight and a strict surplus over the
symbolic local-constraint rank give a uniformly nonvanishing curve certificate. Its challenge
height is `r * (ℓ * ν) / (N - r)`, where `r` bounds the matrix rank and `N` is the number of
columns. -/
theorem exists_curveCertificate_of_rank_bound {F : Type*} [Field F]
    {d D m n N A k ℓ ν r : ℕ}
    (hbudget : 0 < m * A) (hkD : k ≤ D + 1)
    (centers : Fin n ↪ F) (received : Fin n → F[X])
    (hreceived : ∀ i, (received i).natDegree ≤ ℓ)
    (columns : Fin N → SourceColumn d) (hcolumns : Function.Injective columns)
    (hy₀ : ∀ j, (columns j).y₀ ≤ ν)
    (hdegree : ∀ j, totalJetDegree (columns j).exponent ≤ ν)
    (hweight : ∀ j, (columns j).exponent.weight (differentialWeight D) < m * A)
    (hrank : ((localConstraintMatrix m (fun i ↦ Polynomial.C (centers i)) received columns).map
      (algebraMap F[X] (RatFunc F))).rank ≤ r) (hrN : r < N) :
    Nonempty (CurveCertificate F A k ℓ ν d (r * (ℓ * ν) / (N - r)) centers received) := by
  classical
  obtain ⟨v, hv, hvdegree, _, hnonzero, hconstraints⟩ :=
    exists_primitive_interpolant_of_rank_le m ℓ ν (fun i ↦ centers i) received hreceived
      columns hcolumns hy₀ (algebraMap F[X] (RatFunc F))
      (RatFunc.algebraMap_injective F) hrank (by simpa using hrN)
  let Q : DifferentialPolynomial F[X] d := SourceColumn.interpolant columns v
  have hchallenge : ∀ u, (Q.coeff u).natDegree ≤ r * (ℓ * ν) / (N - r) := by
    intro u
    by_cases hu : ∃ j, (columns j).exponent = u
    · obtain ⟨j, rfl⟩ := hu
      rw [show Q = SourceColumn.interpolant columns v by rfl,
        SourceColumn.coeff_interpolant hcolumns v j]
      simpa only [Fintype.card_fin] using hvdegree j
    · have hcoeff : Q.coeff u = 0 := by
        rw [show Q = SourceColumn.interpolant columns v by rfl,
          SourceColumn.interpolant, MvPolynomial.coeff_sum]
        apply Finset.sum_eq_zero
        intro j _
        rw [MvPolynomial.coeff_monomial]
        split
        · rename_i heq
          exact (hu ⟨j, heq⟩).elim
        · rfl
      simp [hcoeff]
  have htotal : ∀ u ∈ Q.support, totalJetDegree u ≤ ν := by
    intro u hu
    have hu' : u ∈ (SourceColumn.interpolant columns v).support := by simpa [Q] using hu
    exact totalJetDegree_interpolant_le columns hdegree v u hu'
  refine ⟨⟨Q, hchallenge, htotal, ?_⟩⟩
  intro E _ ι z
  let φ := Polynomial.eval₂RingHom ι z
  let Qz := MvPolynomial.map φ Q
  refine ⟨?_, ?_, ?_⟩
  · simpa only [Q] using hnonzero φ
  · simpa only [Q] using jetTotalDegree_map_interpolant_le columns hdegree v ι z
  · intro indices P hP hcard hagreement
    have hweightQ : differentialWeightedDegree D Qz < m * A := by
      rw [differentialWeightedDegree, MvPolynomial.weightedTotalDegree,
        Finset.sup_lt_iff hbudget]
      intro u hu
      have hs := MvPolynomial.support_map_subset φ Q hu
      obtain ⟨j, _, hj⟩ := Finset.mem_biUnion.mp (MvPolynomial.support_sum hs)
      have heq : u = (columns j).exponent := by
        simpa using MvPolynomial.support_monomial_subset hj
      simpa [heq] using hweight j
    have hlocal : ∀ i, SatisfiesLocalConstraints m (ι (centers i))
        ((received i).eval₂ ι z) Qz := by
      intro i
      have hi := satisfiesLocalConstraints_map φ m (C (centers i)) (received i) Q
        (hconstraints i)
      change SatisfiesLocalConstraints m
        (Polynomial.eval₂ ι z (C (centers i))) ((received i).eval₂ ι z) Qz at hi
      simpa only [Polynomial.eval₂_C] using hi
    have hPdegree : P.natDegree ≤ D := by
      by_cases hPzero : P = 0
      · simp [hPzero]
      · have hPk : P.natDegree < k :=
          (Polynomial.natDegree_lt_iff_degree_lt hPzero).mpr hP
        omega
    have hpoints : Set.InjOn (fun i ↦ ι (centers i)) (indices : Set (Fin n)) := by
      intro i _ j _ hij
      exact centers.injective (ι.injective hij)
    exact differentialSpecialization_eq_zero_of_differentialWeightedDegree_lt
      (fun i ↦ ι (centers i)) (fun i ↦ (received i).eval₂ ι z) indices hweightQ
      (fun i _ ↦ hlocal i) P hPdegree hpoints hcard hagreement

end ReedSolomon.HiddenDerivative.SymbolicReceivedCurve

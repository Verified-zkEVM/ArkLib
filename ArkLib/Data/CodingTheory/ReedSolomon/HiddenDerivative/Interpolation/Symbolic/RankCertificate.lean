/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.Symbolic.CurveSupportCertificate

/-!
# Symbolic certificates from a finite rank surplus

A finite selection of `N` monomials and a rank bound `r < N` give a primitive
polynomial kernel vector of height at most `r * (ℓ * ν) / (N - r)`.
The total jet bound `ν` is independent of multiplicity. This interface accepts
restricted weighted supports: their own rank estimate can be sharper than the
rank of the larger space containing them.

The certificate remains nonzero at every challenge over every field extension.
Local multiplicity then explains all sufficiently agreeing messages. Analytic
rate estimates supply the finite rank surplus to this algebraic construction.
-/

@[expose] public section

noncomputable section

open Polynomial PolynomialDifferential

namespace ReedSolomon.HiddenDerivative.SymbolicReceivedInterpolation

/-- The jet degree of a linear combination is bounded by those of its monomials. -/
theorem interpolant_totalJetDegree_le {F : Type*} [Field F] {d N ν : ℕ}
    (columns : Fin N → SourceColumn d)
    (hdegree : ∀ j, totalJetDegree (columns j).exponent ≤ ν)
    (v : Fin N → F[X]) :
    ∀ u ∈ (interpolant columns v).support, totalJetDegree u ≤ ν := by
  classical
  intro u hu
  obtain ⟨j, _, hj⟩ := Finset.mem_biUnion.mp (MvPolynomial.support_sum hu)
  have heq : u = (columns j).exponent := by
    simpa using MvPolynomial.support_monomial_subset hj
  subst u
  exact hdegree j

/-- Coefficient specialization preserves a uniform jet bound on the selected columns. -/
theorem map_interpolant_jetTotalDegree_le {F E : Type*} [Field F] [Field E]
    {d N ν : ℕ} (columns : Fin N → SourceColumn d)
    (hdegree : ∀ j, totalJetDegree (columns j).exponent ≤ ν)
    (v : Fin N → F[X]) (ι : F →+* E) (z : E) :
    jetTotalDegree (MvPolynomial.map (Polynomial.eval₂RingHom ι z)
      (interpolant columns v)) ≤ ν := by
  rw [jetTotalDegree_le_iff]
  intro u hu
  have hs := MvPolynomial.support_map_subset _ _ hu
  simpa [totalJetDegree, Finsupp.degree_eq_sum] using
    interpolant_totalJetDegree_le columns hdegree v u hs

end ReedSolomon.HiddenDerivative.SymbolicReceivedInterpolation

namespace ReedSolomon.HiddenDerivative.SymbolicReceivedCurve

open SymbolicReceivedInterpolation

/-- Any finite monomial support with the specialization-weight cutoff gives a symbolic
certificate from its actual matrix rank. This includes first-order differential weights. -/
theorem exists_certificate_of_monomial_rank_bound {F : Type*} [Field F]
    {d D m n N A k ℓ ν r : ℕ}
    (hbudget : 0 < m * A) (hkD : k ≤ D + 1)
    (centers : Fin n ↪ F) (w : Fin n → F[X]) (hw : ∀ i, (w i).natDegree ≤ ℓ)
    (columns : Fin N → SourceColumn d) (hcolumns : Function.Injective columns)
    (hy₀ : ∀ j, (columns j).y₀ ≤ ν)
    (hdegree : ∀ j, totalJetDegree (columns j).exponent ≤ ν)
    (hweight : ∀ j, exactInterpolationMonomialWeight D (columns j).exponent < m * A)
    (hrank : ((finiteConstraintMatrix m (fun i ↦ centers i) w columns).map
      (algebraMap F[X] (RatFunc F))).rank ≤ r) (hrN : r < N) :
    Nonempty (Certificate F A k ℓ ν d (r * (ℓ * ν) / (N - r)) centers w) := by
  classical
  obtain ⟨v, _, hvdegree, _, hnonzero, hconstraints⟩ :=
    exists_primitive_interpolant_of_rank_le m ℓ ν r (fun i ↦ centers i) w hw
      columns hcolumns hy₀ hrank hrN
  refine ⟨⟨interpolant columns v, ?_, interpolant_totalJetDegree_le columns hdegree v, ?_⟩⟩
  · intro u
    exact Nat.lt_succ_iff.mp (coeff_interpolant_natDegree_lt columns hcolumns v
      (Nat.succ_pos _) (fun j ↦ Nat.lt_succ_iff.mpr (hvdegree j)) u)
  · intro E _ ι z
    refine ⟨hnonzero ι z, map_interpolant_jetTotalDegree_le columns hdegree v ι z, ?_⟩
    intro indices P hP hcard hagreement
    let φ := Polynomial.eval₂RingHom ι z
    let Q := MvPolynomial.map φ (interpolant columns v)
    have hQweight : differentialWeightedDegree D Q < m * A := by
      rw [differentialWeightedDegree, MvPolynomial.weightedTotalDegree,
        Finset.sup_lt_iff hbudget]
      intro u hu
      have hsource := MvPolynomial.support_map_subset φ (interpolant columns v) hu
      obtain ⟨j, _, hj⟩ := Finset.mem_biUnion.mp (MvPolynomial.support_sum hsource)
      have heq : u = (columns j).exponent := by
        simpa using MvPolynomial.support_monomial_subset hj
      exact heq ▸ hweight j
    have hnat : P.natDegree ≤ D := by
      by_cases hz : P = 0
      · simp [hz]
      · have := (Polynomial.natDegree_lt_iff_degree_lt hz).mpr hP
        omega
    have hlocal : ∀ i, SatisfiesLocalConstraints m (ι (centers i)) ((w i).eval₂ ι z) Q := by
      intro i
      have hi := SatisfiesLocalConstraints.map φ m (Polynomial.C (centers i))
        (w i) (interpolant columns v) (hconstraints i)
      change SatisfiesLocalConstraints m (Polynomial.eval₂ ι z (Polynomial.C (centers i)))
        ((w i).eval₂ ι z) Q at hi
      simpa only [Polynomial.eval₂_C] using hi
    have hinj : Set.InjOn (fun i ↦ ι (centers i)) (indices : Set (Fin n)) := by
      intro i _ j _ hij
      exact centers.injective (ι.injective hij)
    apply differentialSpecialization_eq_zero_of_global_multiplicity
      (fun i ↦ ι (centers i)) indices m A Q P hinj hcard
    · intro i hi
      exact X_sub_C_pow_dvd_differentialSpecialization_of_contact
        Q P (ι (centers i)) ((w i).eval₂ ι z) (hagreement i hi) (hlocal i)
    · exact (natDegree_differentialSpecialization_le Q P hnat).trans_lt hQweight

/-- A selected finite support and its actual matrix rank produce a symbolic certificate.
The rank premise is a finite algebraic input, to be proved by the support counting layer. -/
theorem exists_certificate_of_rank_bound {F : Type*} [Field F]
    {d D m W n N A k ℓ ν r : ℕ} {L : ℝ}
    (hL : L ≤ (m * A : ℕ)) (hbudget : 0 < m * A)
    (hkD : k ≤ D + 1) (centers : Fin n ↪ F) (w : Fin n → F[X])
    (hw : ∀ i, (w i).natDegree ≤ ℓ)
    (columns : Fin N → SourceColumn d) (hcolumns : Function.Injective columns)
    (hy₀ : ∀ j, (columns j).y₀ ≤ ν)
    (hdegree : ∀ j, totalJetDegree (columns j).exponent ≤ ν)
    (hband : ∀ j, WeightedSupportEligible D d W L (columns j).exponent)
    (hrank : ((finiteConstraintMatrix m (fun i ↦ centers i) w columns).map
      (algebraMap F[X] (RatFunc F))).rank ≤ r) (hrN : r < N) :
    Nonempty (Certificate F A k ℓ ν d (r * (ℓ * ν) / (N - r)) centers w) := by
  exact exists_certificate_of_monomial_rank_bound hbudget hkD centers w hw columns
    hcolumns hy₀ hdegree
    (fun j ↦ exactInterpolationMonomialWeight_lt_of_weightedSupportEligible hL (hband j))
    hrank hrN

/-- A strict real ratio bounds the integer polynomial-kernel height, including rank zero. -/
theorem kernel_height_lt_div_margin {N r b : ℕ} {γ : ℝ}
    (hγ : 1 < γ) (hb : 0 < b) (hmargin : γ * r < N) :
    ((r * b / (N - r) : ℕ) : ℝ) < (b : ℝ) / (γ - 1) := by
  have hr : (r : ℝ) < N := by
    nlinarith [Nat.cast_nonneg r (α := ℝ)]
  have hrN : r < N := by exact_mod_cast hr
  have hquot : ((r * b / (N - r) : ℕ) : ℝ) ≤
      (r : ℝ) * b / (N - r) := by
    simpa [Nat.cast_sub hrN.le] using
      (Nat.cast_div_le (α := ℝ) (m := r * b) (n := N - r))
  apply hquot.trans_lt
  apply (div_lt_div_iff₀ (sub_pos.mpr hr) (sub_pos.mpr hγ)).mpr
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  nlinarith

end ReedSolomon.HiddenDerivative.SymbolicReceivedCurve

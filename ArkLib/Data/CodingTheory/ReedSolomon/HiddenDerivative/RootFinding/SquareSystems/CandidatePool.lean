/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.SquareSystems.ChartDifferential
/-!
# Literal agreement-and-tail equation pool

The square-system pool contains the cleared agreement equation for each of `k` selected agreeing
positions and every common Taylor numerator from message degree `k` through ambient degree `K-1`.
Every equation in this pool vanishes at the chart point of a degree-`< k` regular solution.
-/

@[expose] public section

open PolynomialDifferential

namespace ReedSolomon.HiddenDerivative.SquareSystems

open MvPolynomial

variable {F : Type*} [Field F] {r : ℕ}

/-- Literal pool of cleared agreement and high-coefficient equations. -/
noncomputable def candidatePoolEquation (center : F) (Q : DifferentialPolynomial F r) (K k τ : ℕ)
    (hk : k ≤ K) (points : Fin k ↪ F) (received : Fin k → F) :
    Fin k ⊕ Fin (K - k) → MvPolynomial (Fin (r + 1)) F
  | Sum.inl i => taylorAgreementEquation center Q K (points i) (received i) (τ := τ)
  | Sum.inr j => commonTaylorNumerator center Q K (tailIndex hk j) (τ := τ)

/-- Formal differentials of all literal cleared equations in the candidate pool. -/
noncomputable def candidatePoolDifferential (center : F) (Q : DifferentialPolynomial F r)
    (K k τ : ℕ) (hk : k ≤ K) (points : Fin k ↪ F) (received : Fin k → F)
    (jet : Fin (r + 1) → F) :
    (Fin (r + 1) → F) →ₗ[F] (Fin k ⊕ Fin (K - k) → F) :=
  LinearMap.pi fun equation ↦
    mvPolynomialDifferential jet
      (candidatePoolEquation center Q K k τ hk points received equation)

/-- Quotient differentials of the pool equations before clearing the common denominator. -/
noncomputable def candidatePoolQuotientDifferential (center : F)
    (Q : DifferentialPolynomial F r) (K k τ : ℕ) (hk : k ≤ K)
    (points : Fin k ↪ F) (received : Fin k → F) (jet : Fin (r + 1) → F) :
    (Fin (r + 1) → F) →ₗ[F] (Fin k ⊕ Fin (K - k) → F) :=
  LinearMap.pi fun equation ↦
    quotientDifferential jet
      (candidatePoolEquation center Q K k τ hk points received equation)
      (initialJetSeparant center Q ^ τ)

/-- The quotient-differential pool is exactly evaluation-and-tail applied to the Taylor
coefficient differential. -/
theorem candidatePoolQuotientDifferential_eq (center : F)
    (Q : DifferentialPolynomial F r) (K k τ : ℕ) (hk : k ≤ K)
    (points : Fin k ↪ F) (received : Fin k → F) (jet : Fin (r + 1) → F)
    (hseparant : aeval jet (initialJetSeparant center Q) ≠ 0) :
    candidatePoolQuotientDifferential center Q K k τ hk points received jet =
      (evaluationTailPoolMap K k hk center points).comp
        (rationalTaylorMapDifferential center Q K τ jet) := by
  apply LinearMap.ext
  intro direction
  funext equation
  cases equation with
  | inl i =>
      change quotientDifferential jet
        (taylorAgreementEquation center Q K (points i) (received i) (τ := τ))
          (initialJetSeparant center Q ^ τ) direction = _
      rw [quotientDifferential_taylorAgreementEquation center Q K τ jet hseparant]
      simp only [LinearMap.coe_sum, LinearMap.coe_smul, Finset.sum_apply, Pi.smul_apply,
        smul_eq_mul, evaluationTailPoolMap, evaluationTailMap, rationalTaylorMapDifferential,
        LinearMap.coe_comp, LinearEquiv.coe_coe, LinearMap.coe_mk, AddHom.coe_mk,
        Function.comp_apply, LinearMap.pi_apply,
        LinearEquiv.sumArrowLequivProdArrow_symm_apply_inl]
      apply Finset.sum_congr rfl
      intro j _
      ring
  | inr j =>
      rfl

/-- At a common zero of the pool, clearing denominators multiplies every quotient row by the same
nonzero separant power. -/
theorem candidatePoolDifferential_eq_smul (center : F)
    (Q : DifferentialPolynomial F r) (K k τ : ℕ) (hk : k ≤ K)
    (points : Fin k ↪ F) (received : Fin k → F) (jet : Fin (r + 1) → F)
    (hseparant : aeval jet (initialJetSeparant center Q) ≠ 0)
    (hzero : ∀ equation,
      aeval jet (candidatePoolEquation center Q K k τ hk points received equation) = 0) :
    candidatePoolDifferential center Q K k τ hk points received jet =
      aeval jet (initialJetSeparant center Q ^ τ) •
        candidatePoolQuotientDifferential center Q K k τ hk points received jet := by
  apply LinearMap.ext
  intro direction
  funext equation
  change mvPolynomialDifferential jet
      (candidatePoolEquation center Q K k τ hk points received equation) direction =
    aeval jet (initialJetSeparant center Q ^ τ) *
      quotientDifferential jet
        (candidatePoolEquation center Q K k τ hk points received equation)
        (initialJetSeparant center Q ^ τ) direction
  exact LinearMap.congr_fun
    (mvPolynomialDifferential_eq_smul_quotientDifferential jet _ _
      (by simpa only [map_pow] using pow_ne_zero τ hseparant) (hzero equation)) direction

/-- At a regular common zero, `r` actual cleared agreement-or-tail equations join the initial
equation to give an injective square differential. This is the literal square-capture statement:
the selected rows are equations from the candidate pool, rather than linear combinations. -/
theorem exists_regularCandidate_squareRows (center : F)
    (Q : DifferentialPolynomial F r) (K k τ : ℕ) (hK : r < K) (hk : k ≤ K)
    (points : Fin k ↪ F) (received : Fin k → F) (jet : Fin (r + 1) → F)
    (hseparant : aeval jet (initialJetSeparant center Q) ≠ 0)
    (hzero : ∀ equation,
      aeval jet (candidatePoolEquation center Q K k τ hk points received equation) = 0) :
    ∃ selected : Fin r ↪ (Fin k ⊕ Fin (K - k)),
      Function.Injective
        (normalSelectedMap (initialJetDifferential center Q jet)
          (candidatePoolDifferential center Q K k τ hk points received jet) selected) := by
  obtain ⟨selected, hselected⟩ :=
    exists_regularChart_squareRows center Q K k τ hK hk points jet hseparant
  refine ⟨selected, ?_⟩
  have hquotient : Function.Injective
      (normalSelectedMap (initialJetDifferential center Q jet)
        (candidatePoolQuotientDifferential center Q K k τ hk points received jet)
        selected) := by
    rw [candidatePoolQuotientDifferential_eq center Q K k τ hk points received jet hseparant]
    exact hselected
  rw [candidatePoolDifferential_eq_smul center Q K k τ hk points received jet
    hseparant hzero]
  intro direction direction' hequal
  apply hquotient
  apply Prod.ext
  · have hfirst := congrArg Prod.fst hequal
    change initialJetDifferential center Q jet direction =
      initialJetDifferential center Q jet direction' at hfirst
    exact hfirst
  · funext j
    have hj := congrFun (congrArg Prod.snd hequal) j
    change aeval jet (initialJetSeparant center Q ^ τ) *
        candidatePoolQuotientDifferential center Q K k τ hk points received jet
          direction (selected j) =
      aeval jet (initialJetSeparant center Q ^ τ) *
        candidatePoolQuotientDifferential center Q K k τ hk points received jet
          direction' (selected j) at hj
    exact mul_left_cancel₀ (by simpa only [map_pow] using pow_ne_zero τ hseparant) hj

/-- Every literal pool equation vanishes at a degree-`< k` regular solution on the chosen `k`
agreement positions. The theorem uses the exact binomial-pivot and common-exponent hypotheses of
the existing Taylor chart. -/
theorem candidatePoolEquation_solution (center : F) (Q : DifferentialPolynomial F r)
    (K k τ : ℕ) (hk : k ≤ K) (hτ : TaylorExponentSufficient r K τ)
    (points : Fin k ↪ F) (received : Fin k → F) (P : Polynomial F)
    (hsolution : differentialSpecialization Q P = 0)
    (hseparant : jetEvaluation (separant Q (Fin.last r)) center
      (polynomialJet center P) ≠ 0)
    (hbinomial : ∀ i, r < i → i < K → (i.choose r : F) ≠ 0)
    (hdegree : P.degree < k) (hagreement : ∀ i, P.eval (points i) = received i) :
    ∀ equation,
      aeval (polynomialJet center P)
        (candidatePoolEquation center Q K k τ hk points received equation) = 0 := by
  intro equation
  cases equation with
  | inl i =>
      rw [candidatePoolEquation,
        taylorAgreementEquation_solution_of_exponent center Q P hsolution hseparant
          K τ hτ (hdegree.trans_le (Nat.cast_le.mpr hk)) hbinomial,
        hagreement]
      simp
  | inr j =>
      rw [candidatePoolEquation,
        commonTaylorNumerator_solution_of_exponent center Q P hsolution hseparant
          K τ hτ hbinomial]
      have hTaylorDegree : (Polynomial.taylor center P).degree < k := by
        simpa only [Polynomial.degree_taylor] using hdegree
      have hcoefficient :
          (Polynomial.taylor center P).coeff (tailIndex hk j).val = 0 :=
        (Polynomial.degree_lt_iff_coeff_zero _ k).mp hTaylorDegree _ (by
          simp [tailIndex])
      rw [hcoefficient, mul_zero]

/-- Paper-facing square capture at an actual polynomial solution. The initial equation and every
pool equation vanish, and the initial row together with `r` selected literal pool rows has
injective differential. -/
theorem exists_candidateSquareRows_at_solution (center : F)
    (Q : DifferentialPolynomial F r) (K k τ : ℕ) (hK : r < K) (hk : k ≤ K)
    (hτ : TaylorExponentSufficient r K τ) (points : Fin k ↪ F)
    (received : Fin k → F) (P : Polynomial F)
    (hsolution : differentialSpecialization Q P = 0)
    (hseparant : jetEvaluation (separant Q (Fin.last r)) center
      (polynomialJet center P) ≠ 0)
    (hbinomial : ∀ i, r < i → i < K → (i.choose r : F) ≠ 0)
    (hdegree : P.degree < k) (hagreement : ∀ i, P.eval (points i) = received i) :
    ∃ selected : Fin r ↪ (Fin k ⊕ Fin (K - k)),
      aeval (polynomialJet center P) (initialJetEquation center Q) = 0 ∧
      (∀ equation,
        aeval (polynomialJet center P)
          (candidatePoolEquation center Q K k τ hk points received equation) = 0) ∧
      Function.Injective
        (normalSelectedMap
          (initialJetDifferential center Q (polynomialJet center P))
          (candidatePoolDifferential center Q K k τ hk points received
            (polynomialJet center P)) selected) := by
  have hpool := candidatePoolEquation_solution center Q K k τ hk hτ points received P
    hsolution hseparant hbinomial hdegree hagreement
  have hseparant' :
      aeval (polynomialJet center P) (initialJetSeparant center Q) ≠ 0 := by
    rwa [aeval_initialJetSeparant]
  obtain ⟨selected, hselected⟩ := exists_regularCandidate_squareRows center Q K k τ hK hk
    points received (polynomialJet center P) hseparant' hpool
  exact ⟨selected, initialJetEquation_solution center Q P hsolution, hpool, hselected⟩

end ReedSolomon.HiddenDerivative.SquareSystems

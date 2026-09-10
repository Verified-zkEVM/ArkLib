/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.Symbolic.TaylorHeight


/-!
# Joint degree for symbolic Taylor numerators

Flattening retains the challenge as one additional source coordinate. Degree estimates here
measure that challenge together with the initial jet coordinates.
-/

@[expose] public section

open PolynomialDifferential


namespace MvPolynomial

noncomputable section

open scoped BigOperators

variable {F σ τ : Type*} [Field F]

/-- Retain the polynomial coefficient parameter as the distinguished source coordinate. -/
def flattenChallenge : MvPolynomial σ (Polynomial F) ≃ₐ[F] MvPolynomial (Option σ) F :=
  (optionEquivRight F σ).symm

/-- Ordinary total degree after retaining the challenge as a source coordinate. -/
def jointTotalDegree (P : MvPolynomial σ (Polynomial F)) : ℕ :=
  (flattenChallenge P).totalDegree

/-- A jet coordinate remains a coordinate after flattening the challenge. -/
@[simp]
theorem flattenChallenge_X (i : σ) :
    flattenChallenge (X i : MvPolynomial σ (Polynomial F)) = X (some i) := by
  apply (optionEquivRight F σ).injective
  simp [flattenChallenge]

/-- A polynomial coefficient becomes its literal evaluation in the challenge coordinate. -/
@[simp]
theorem flattenChallenge_C (p : Polynomial F) :
    flattenChallenge (C p : MvPolynomial σ (Polynomial F)) =
      Polynomial.aeval (X none) p := by
  simp [flattenChallenge, optionEquivRight]

/-- Base-field scalars have zero joint degree. -/
@[simp]
theorem jointTotalDegree_scalar (a : F) :
    jointTotalDegree (C (Polynomial.C a) : MvPolynomial σ (Polynomial F)) = 0 := by
  simp [jointTotalDegree]

/-- Jet coordinates have joint degree one. -/
@[simp]
theorem jointTotalDegree_X (i : σ) :
    jointTotalDegree (X i : MvPolynomial σ (Polynomial F)) = 1 := by
  simp [jointTotalDegree]

/-- Joint degree is subadditive under products. -/
theorem jointTotalDegree_mul_le (P Q : MvPolynomial σ (Polynomial F)) :
    jointTotalDegree (P * Q) ≤ jointTotalDegree P + jointTotalDegree Q := by
  simp only [jointTotalDegree, map_mul]
  exact totalDegree_mul _ _

/-- Taking powers multiplies the joint-degree bound. -/
theorem jointTotalDegree_pow_le (P : MvPolynomial σ (Polynomial F)) (n : ℕ) :
    jointTotalDegree (P ^ n) ≤ n * jointTotalDegree P := by
  simp only [jointTotalDegree, map_pow]
  exact totalDegree_pow _ _

/-- Negation preserves joint degree. -/
@[simp]
theorem jointTotalDegree_neg (P : MvPolynomial σ (Polynomial F)) :
    jointTotalDegree (-P) = jointTotalDegree P := by
  simp [jointTotalDegree]

/-- Subtraction preserves the larger joint-degree bound. -/
theorem jointTotalDegree_sub_le (P Q : MvPolynomial σ (Polynomial F)) :
    jointTotalDegree (P - Q) ≤ max (jointTotalDegree P) (jointTotalDegree Q) := by
  simp only [jointTotalDegree, map_sub]
  exact totalDegree_sub _ _

/-- A finite sum preserves a uniform joint-degree bound. -/
theorem jointTotalDegree_finsetSum_le {ι : Type*} (s : Finset ι)
    (P : ι → MvPolynomial σ (Polynomial F)) (d : ℕ)
    (hP : ∀ i ∈ s, jointTotalDegree (P i) ≤ d) :
    jointTotalDegree (∑ i ∈ s, P i) ≤ d := by
  simp only [jointTotalDegree, map_sum]
  exact totalDegree_finsetSum_le hP

/-- An affine received symbol is linear in the retained challenge coordinate. -/
theorem jointTotalDegree_affine_le (a b : F) :
    jointTotalDegree
      (C (Polynomial.C a + Polynomial.X * Polynomial.C b) :
        MvPolynomial σ (Polynomial F)) ≤ 1 := by
  simp only [jointTotalDegree, flattenChallenge_C, map_add, map_mul,
    Polynomial.aeval_C, Polynomial.aeval_X, algebraMap_eq]
  apply (totalDegree_add _ _).trans
  apply max_le
  · simp
  · exact (totalDegree_mul _ _).trans (by simp)

/-- A retained coefficient has joint degree at most its univariate degree. -/
theorem jointTotalDegree_C_le (p : Polynomial F) :
    jointTotalDegree (C p : MvPolynomial σ (Polynomial F)) ≤ p.natDegree := by
  classical
  have he : Polynomial.aeval (X none : MvPolynomial (Option σ) F) p =
      ∑ n ∈ p.support, C (p.coeff n) * X none ^ n := by
    simpa [Polynomial.sum_def] using congrArg
      (Polynomial.aeval (X none : MvPolynomial (Option σ) F)) p.sum_monomial_eq.symm
  rw [jointTotalDegree, flattenChallenge_C, he]
  apply totalDegree_finsetSum_le
  intro n hn
  apply (totalDegree_mul _ _).trans
  simp only [totalDegree_C, zero_add]
  exact (totalDegree_pow _ _).trans (by
    simpa using Polynomial.le_natDegree_of_mem_supp n hn)

/-- Uniform coefficient height plus total variable degree bounds the joint degree. -/
theorem jointTotalDegree_le_coeff_degree_add (P : MvPolynomial σ (Polynomial F))
    (h : ℕ) (hcoeff : ∀ m ∈ P.support, (coeff m P).natDegree ≤ h) :
    jointTotalDegree P ≤ h + P.totalDegree := by
  classical
  have he : flattenChallenge P =
      ∑ m ∈ P.support, flattenChallenge (C (coeff m P)) *
        ∏ i ∈ m.support, (X (some i) : MvPolynomial (Option σ) F) ^ m i := by
    conv_lhs => rw [P.as_sum]
    simp only [map_sum, monomial_eq, map_mul, Finsupp.prod, map_prod, map_pow,
      flattenChallenge_X]
  rw [jointTotalDegree, he]
  apply totalDegree_finsetSum_le
  intro m hm
  have hc := (jointTotalDegree_C_le (σ := σ) (coeff m P)).trans (hcoeff m hm)
  have hp : (∏ i ∈ m.support, (X (some i) : MvPolynomial (Option σ) F) ^ m i).totalDegree ≤
      m.sum (fun _ e ↦ e) := by
    apply (totalDegree_finsetProd _ _).trans
    simp [Finsupp.sum, totalDegree_X_pow]
  exact (totalDegree_mul _ _).trans (Nat.add_le_add hc (hp.trans (le_totalDegree hm)))

/-- Clearing a separant denominator accounts for both coefficient and variable degrees.
The source hypothesis is monomialwise, so it is valid even when coefficients cancel. -/
theorem jointTotalDegree_clearedSubstitution
    (S : MvPolynomial σ (Polynomial F)) (N : τ → MvPolynomial σ (Polynomial F))
    (d : τ → ℕ) (H b v : ℕ) (Q : MvPolynomial τ (Polynomial F))
    (hS : jointTotalDegree S ≤ b)
    (hN : ∀ i, jointTotalDegree (N i) ≤ d i * b + 1)
    (hden : ∀ m ∈ Q.support, Finsupp.weight d m ≤ H)
    (hQ : ∀ m ∈ Q.support,
      jointTotalDegree (C (coeff m Q) : MvPolynomial σ (Polynomial F)) +
        m.sum (fun _ e ↦ e) ≤ v) :
    jointTotalDegree (clearedSubstitution C S N d H Q) ≤ H * b + v := by
  classical
  unfold jointTotalDegree
  change ((flattenChallenge (F := F) (σ := σ)).toRingHom
    (clearedSubstitution C S N d H Q)).totalDegree ≤ _
  rw [ringHom_clearedSubstitution]
  apply totalDegree_finsetSum_le
  intro m hm
  have hprod : (∏ i ∈ m.support, flattenChallenge (N i) ^ m i).totalDegree ≤
      Finsupp.weight d m * b + m.sum (fun _ e ↦ e) := by
    apply (totalDegree_finsetProd _ _).trans
    calc
      _ ≤ ∑ i ∈ m.support, m i * (d i * b + 1) := by
        apply Finset.sum_le_sum
        intro i _
        exact (totalDegree_pow _ _).trans (Nat.mul_le_mul_left _ (hN i))
      _ = Finsupp.weight d m * b + m.sum (fun _ e ↦ e) := by
        simp only [Finsupp.weight_apply, Finsupp.sum, smul_eq_mul]
        rw [Finset.sum_mul, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro i _
        ring
  have hpow := (totalDegree_pow (flattenChallenge S)
    (H - Finsupp.weight d m)).trans (Nat.mul_le_mul_left _ hS)
  have hbudget := Nat.sub_add_cancel (hden m hm)
  have hcoeff := hQ m hm
  have hmul := totalDegree_mul
    ((flattenChallenge (C (coeff m Q))) * ∏ i ∈ m.support, flattenChallenge (N i) ^ m i)
    (flattenChallenge S ^ (H - Finsupp.weight d m))
  have hleft := totalDegree_mul
    (flattenChallenge (C (coeff m Q))) (∏ i ∈ m.support, flattenChallenge (N i) ^ m i)
  unfold jointTotalDegree at hcoeff
  change ((flattenChallenge (C (coeff m Q)) *
    ∏ i ∈ m.support, flattenChallenge (N i) ^ m i) *
    flattenChallenge S ^ (H - Finsupp.weight d m)).totalDegree ≤ H * b + v
  nlinarith

end

end MvPolynomial

namespace ReedSolomon.HiddenDerivative

noncomputable section

open MvPolynomial

variable {F : Type*} [Field F] {r : ℕ}

/-- Keeping a coefficient parameter does not affect the separant's jet-degree decrease. -/
theorem totalDegree_initialJetSeparantOver_le (center : Polynomial F)
    (Q : DifferentialPolynomial (Polynomial F) r) :
    (initialJetSeparantOver center Q).totalDegree ≤
      Q.weightedTotalDegree (fun i ↦ i.elim 0 (fun _ ↦ 1)) - 1 := by
  rw [← weightedTotalDegree_one]
  apply le_trans (weightedTotalDegree_aeval_le_of_le
    (fun i : Option (Fin (r + 1)) ↦ i.elim 0 (fun _ ↦ 1))
    (1 : Fin (r + 1) → ℕ) _ _ ?_)
  · exact weightedTotalDegree_pderiv_le_sub _ _ Q
  · intro i
    cases i with
    | none => simp
    | some j => simp only [Option.elim_some, weightedTotalDegree_one,
        totalDegree_X, le_refl]

/-- Coefficient height and the separant's jet-degree decrease give its joint-degree budget. -/
theorem jointTotalDegree_initialJetSeparantOver_le (center : Polynomial F)
    (Q : DifferentialPolynomial (Polynomial F) r) (v h : ℕ)
    (hv : Q.weightedTotalDegree (fun i ↦ i.elim 0 (fun _ ↦ 1)) ≤ v)
    (hh : ∀ m ∈ (initialJetSeparantOver center Q).support,
      (coeff m (initialJetSeparantOver center Q)).natDegree ≤ h) :
    jointTotalDegree (initialJetSeparantOver center Q) ≤ v - 1 + h := by
  have hd := jointTotalDegree_le_coeff_degree_add (initialJetSeparantOver center Q) h hh
  have hs := (totalDegree_initialJetSeparantOver_le center Q).trans (Nat.sub_le_sub_right hv 1)
  omega

/-- A joint-degree budget for the initial separant and every actual truncated residual
gives the linear-in-order degree estimate for the literal symbolic recurrence. -/
theorem jointTotalDegree_rationalTaylorNumeratorOver_le
    (center : Polynomial F) (Q : DifferentialPolynomial (Polynomial F) r) (b : ℕ)
    (hS : jointTotalDegree (initialJetSeparantOver center Q) ≤ b)
    (hres : ∀ l, r < l → ∀ m ∈
      ((optionEquivLeft (Polynomial F) (Fin l)
        (universalTaylorResidual l center Q)).coeff (l - r)).support,
      jointTotalDegree (C (coeff m
        ((optionEquivLeft (Polynomial F) (Fin l)
          (universalTaylorResidual l center Q)).coeff (l - r))) :
          MvPolynomial (Fin (r + 1)) (Polynomial F)) + m.sum (fun _ e ↦ e) ≤ b + 1)
    (l : ℕ) :
    jointTotalDegree (rationalTaylorNumeratorOver (F := F) center Q l) ≤
      (2 * (l - r) - 1) * b + 1 := by
  induction l using Nat.strong_induction_on with
  | h l ih =>
    rw [rationalTaylorNumeratorOver]
    split_ifs with hl
    · simp only [jointTotalDegree_X]
      omega
    · have hh : 0 < l - r := by omega
      have hlr : r + (l - r) = l := by omega
      have hden := denominator_weight_le_of_mem_universalTaylorResidual_coeff
        (r := r) (h := l - r) hh center Q
      rw [hlr] at hden
      have hd := jointTotalDegree_clearedSubstitution
        (initialJetSeparantOver center Q)
        (fun i : Fin l ↦ rationalTaylorNumeratorOver (F := F) center Q i.val)
        (fun i ↦ 2 * (i.val - r) - 1) (2 * (l - r) - 2) b (b + 1)
        ((optionEquivLeft (Polynomial F) (Fin l)
          (universalTaylorResidual l center Q)).coeff (l - r)) hS
        (fun i ↦ ih i.val i.isLt) hden (hres l (by omega))
      have hm := jointTotalDegree_mul_le
        (-C (algebraMap F (Polynomial F) ((l.choose r : F)⁻¹)) :
          MvPolynomial (Fin (r + 1)) (Polynomial F))
        (clearedSubstitution C (initialJetSeparantOver center Q)
          (fun i : Fin l ↦ rationalTaylorNumeratorOver (F := F) center Q i.val)
          (fun i ↦ 2 * (i.val - r) - 1) (2 * (l - r) - 2)
          ((optionEquivLeft (Polynomial F) (Fin l)
            (universalTaylorResidual l center Q)).coeff (l - r)))
      simp only [jointTotalDegree_neg, Polynomial.algebraMap_eq,
        jointTotalDegree_scalar, zero_add] at hm
      have he : 2 * (l - r) - 1 = (2 * (l - r) - 2) + 1 := by omega
      rw [he]
      simp only [Polynomial.algebraMap_eq]
      nlinarith [hm.trans hd]

/-- Separate coefficient-height and jet-degree bounds give the joint recurrence estimate. -/
theorem jointTotalDegree_rationalTaylorNumeratorOver_le_of_coeff_height
    (center : Polynomial F) (Q : DifferentialPolynomial (Polynomial F) r) (v h : ℕ)
    (hv : 0 < v)
    (hjet : Q.weightedTotalDegree (fun i ↦ i.elim 0 (fun _ ↦ 1)) ≤ v)
    (hsep : ∀ m ∈ (initialJetSeparantOver center Q).support,
      (coeff m (initialJetSeparantOver center Q)).natDegree ≤ h)
    (hres : ∀ l t m,
      (coeff m ((optionEquivLeft (Polynomial F) (Fin l)
        (universalTaylorResidual l center Q)).coeff t)).natDegree ≤ h)
    (l : ℕ) :
    jointTotalDegree (rationalTaylorNumeratorOver (F := F) center Q l) ≤
      (2 * (l - r) - 1) * (v - 1 + h) + 1 := by
  apply jointTotalDegree_rationalTaylorNumeratorOver_le center Q (v - 1 + h)
    (jointTotalDegree_initialJetSeparantOver_le center Q v h hjet hsep) _ l
  intro j _ m hm
  have hc := (jointTotalDegree_C_le (σ := Fin (r + 1))
    (coeff m ((optionEquivLeft (Polynomial F) (Fin j)
      (universalTaylorResidual j center Q)).coeff (j - r)))).trans (hres j (j - r) m)
  have hd := (le_totalDegree hm).trans
    ((totalDegree_universalTaylorResidual_coeff_le j center Q (j - r)).trans hjet)
  omega

/-- Padding to a sufficient exponent converts the exact recurrence bounds into a uniform
common-numerator bound. -/
theorem jointTotalDegree_commonTaylorNumeratorOver_le_of_exponent
    (center : Polynomial F) (Q : DifferentialPolynomial (Polynomial F) r) (b K τ : ℕ)
    (hτ : TaylorExponentSufficient r K τ)
    (hS : jointTotalDegree (initialJetSeparantOver center Q) ≤ b)
    (hN : ∀ l < K,
      jointTotalDegree (rationalTaylorNumeratorOver (F := F) center Q l) ≤
        (2 * (l - r) - 1) * b + 1) (l : Fin K) :
    jointTotalDegree (commonTaylorNumeratorOver (F := F) center Q K l (τ := τ)) ≤
      1 + τ * b := by
  have hd := hN l.val l.isLt
  have hp := (jointTotalDegree_pow_le (initialJetSeparantOver center Q)
    (τ - (2 * (l.val - r) - 1))).trans (Nat.mul_le_mul_left _ hS)
  have hm := jointTotalDegree_mul_le
    (rationalTaylorNumeratorOver (F := F) center Q l.val)
    (initialJetSeparantOver center Q ^ (τ - (2 * (l.val - r) - 1)))
  have he := Nat.sub_add_cancel (hτ l)
  unfold commonTaylorNumeratorOver
  nlinarith

/-- The default exponent `2K` gives the arbitrary-order common-numerator bound. -/
theorem jointTotalDegree_commonTaylorNumeratorOver_le
    (center : Polynomial F) (Q : DifferentialPolynomial (Polynomial F) r) (b K : ℕ)
    (hS : jointTotalDegree (initialJetSeparantOver center Q) ≤ b)
    (hN : ∀ l < K,
      jointTotalDegree (rationalTaylorNumeratorOver (F := F) center Q l) ≤
        (2 * (l - r) - 1) * b + 1) (l : Fin K) :
    jointTotalDegree (commonTaylorNumeratorOver (F := F) center Q K l) ≤
      1 + 2 * K * b := by
  exact jointTotalDegree_commonTaylorNumeratorOver_le_of_exponent center Q b K (2 * K)
    (taylorExponentSufficient_two_mul r K) hS hN l

/-- The source jet degree and challenge height give the actual symbolic numerator bound. -/
theorem jointTotalDegree_rationalTaylorNumeratorOver_le_of_source
    (center : F) (Q : DifferentialPolynomial (Polynomial F) r) (v h : ℕ)
    (hv : 0 < v)
    (hjet : Q.weightedTotalDegree (fun i ↦ i.elim 0 (fun _ ↦ 1)) ≤ v)
    (hheight : ChallengeHeightLE Q h) (l : ℕ) :
    jointTotalDegree (rationalTaylorNumeratorOver (F := F) (Polynomial.C center) Q l) ≤
      (2 * (l - r) - 1) * (v - 1 + h) + 1 := by
  apply jointTotalDegree_rationalTaylorNumeratorOver_le_of_coeff_height
    (Polynomial.C center) Q v h hv hjet
  · intro m _
    exact challengeHeightLE_initialJetSeparantOver Q center hheight m
  · exact universalTaylorResidual_coeff_natDegree_le Q center hheight

/-- Source degree and challenge height bound every numerator padded to a sufficient exponent. -/
theorem jointTotalDegree_commonTaylorNumeratorOver_le_of_source_and_exponent
    (center : F) (Q : DifferentialPolynomial (Polynomial F) r) (v h K τ : ℕ)
    (hτ : TaylorExponentSufficient r K τ)
    (hv : 0 < v)
    (hjet : Q.weightedTotalDegree (fun i ↦ i.elim 0 (fun _ ↦ 1)) ≤ v)
    (hheight : ChallengeHeightLE Q h) (l : Fin K) :
    jointTotalDegree
        (commonTaylorNumeratorOver (F := F) (Polynomial.C center) Q K l (τ := τ)) ≤
      1 + τ * (v - 1 + h) := by
  apply jointTotalDegree_commonTaylorNumeratorOver_le_of_exponent
    (Polynomial.C center) Q (v - 1 + h) K τ hτ
  · apply jointTotalDegree_initialJetSeparantOver_le _ Q v h hjet
    intro m _
    exact challengeHeightLE_initialJetSeparantOver Q center hheight m
  · intro j _
    exact jointTotalDegree_rationalTaylorNumeratorOver_le_of_source center Q v h hv hjet
      hheight j

/-- All default common symbolic numerators have the coarse source-derived joint-degree bound. -/
theorem jointTotalDegree_commonTaylorNumeratorOver_le_of_source
    (center : F) (Q : DifferentialPolynomial (Polynomial F) r) (v h K : ℕ)
    (hv : 0 < v)
    (hjet : Q.weightedTotalDegree (fun i ↦ i.elim 0 (fun _ ↦ 1)) ≤ v)
    (hheight : ChallengeHeightLE Q h) (l : Fin K) :
    jointTotalDegree (commonTaylorNumeratorOver (F := F) (Polynomial.C center) Q K l) ≤
      1 + 2 * K * (v - 1 + h) := by
  exact jointTotalDegree_commonTaylorNumeratorOver_le_of_source_and_exponent
    center Q v h K (2 * K) (taylorExponentSufficient_two_mul r K) hv hjet hheight l

end

end ReedSolomon.HiddenDerivative

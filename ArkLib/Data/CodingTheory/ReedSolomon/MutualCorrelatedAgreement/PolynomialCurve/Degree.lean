/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.PolynomialCurve.ComponentRecognition
public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.Symbolic.TaylorCutDegree
/-!
# Joint degree of polynomial-curve agreement cuts

Power batching contributes its univariate challenge degree additively to the literal joint
total degree of a Taylor agreement cut.  The separate challenge/jet bidegree estimates below
also support the coefficient-linearized power lift used for polynomial-curve incidence:
the batching degree is charged in the degree of the moment base, not at every geometric cut.
-/

@[expose] public section

open PolynomialDifferential

noncomputable section

namespace ReedSolomon

open Polynomial MvPolynomial HiddenDerivative

variable {F : Type*} [Field F] {r ℓ : ℕ}

namespace HiddenDerivative.ChallengeHeightLE

/-- Increase a coefficient-height upper bound. -/
theorem mono {σ : Type*} {P : MvPolynomial σ F[X]} {a b : ℕ}
    (hP : ChallengeHeightLE P a) (hab : a ≤ b) : ChallengeHeightLE P b :=
  fun m ↦ (hP m).trans hab

/-- A coefficient polynomial viewed as a constant in the jet variables. -/
theorem const {σ : Type*} {p : F[X]} {h : ℕ} (hp : p.natDegree ≤ h) :
    ChallengeHeightLE (MvPolynomial.C p : MvPolynomial σ F[X]) h := by
  classical
  intro m
  by_cases hm : m = 0
  · subst m
    simpa using hp
  · simp [MvPolynomial.coeff_C, Ne.symm hm]

/-- Challenge heights add under multiplication. -/
theorem mul_bound {σ : Type*} {P Q : MvPolynomial σ F[X]} {a b : ℕ}
    (hP : ChallengeHeightLE P a) (hQ : ChallengeHeightLE Q b) :
    ChallengeHeightLE (P * Q) (a + b) := by
  classical
  intro m
  rw [MvPolynomial.coeff_mul]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro pair _
  exact Polynomial.natDegree_mul_le_of_le (hP pair.1) (hQ pair.2)

/-- Challenge heights scale under powers. -/
theorem pow_bound {σ : Type*} {P : MvPolynomial σ F[X]} {a : ℕ}
    (hP : ChallengeHeightLE P a) (n : ℕ) : ChallengeHeightLE (P ^ n) (n * a) := by
  induction n with
  | zero => simpa using (const (σ := σ) (p := (1 : F[X])) (h := 0) (by simp))
  | succ n ih => simpa [pow_succ, Nat.succ_mul] using ih.mul_bound hP

/-- A uniform challenge-height bound is stable under finite sums. -/
theorem sum_bound {σ ι : Type*} (s : Finset ι) (P : ι → MvPolynomial σ F[X]) {h : ℕ}
    (hP : ∀ i ∈ s, ChallengeHeightLE (P i) h) : ChallengeHeightLE (∑ i ∈ s, P i) h := by
  intro m
  rw [MvPolynomial.coeff_sum]
  apply Polynomial.natDegree_sum_le_of_forall_le
  exact fun i hi ↦ hP i hi m

/-- Individual challenge-height bounds add under finite products. -/
theorem prod_bound {σ ι : Type*} (s : Finset ι) (P : ι → MvPolynomial σ F[X])
    (a : ι → ℕ) (hP : ∀ i ∈ s, ChallengeHeightLE (P i) (a i)) :
    ChallengeHeightLE (∏ i ∈ s, P i) (∑ i ∈ s, a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (const (σ := σ) (p := (1 : F[X])) (h := 0) (by simp))
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi]
    exact (hP i (Finset.mem_insert_self i s)).mul_bound
      (ih fun j hj ↦ hP j (Finset.mem_insert_of_mem hj))

end HiddenDerivative.ChallengeHeightLE

/-- Clearing denominators of budget `H` costs exactly `H * h` challenge degree, plus
the source coefficient height; unlike jet degree there is no monomial-degree term. -/
theorem challengeHeightLE_clearedSubstitution {σ τ : Type*}
    (S : MvPolynomial σ F[X]) (N : τ → MvPolynomial σ F[X])
    (d : τ → ℕ) (H h a : ℕ) (Q : MvPolynomial τ F[X])
    (hS : ChallengeHeightLE S h) (hN : ∀ i, ChallengeHeightLE (N i) (d i * h))
    (hQ : ChallengeHeightLE Q a)
    (hbudget : ∀ m ∈ Q.support, Finsupp.weight d m ≤ H) :
    ChallengeHeightLE (clearedSubstitution MvPolynomial.C S N d H Q) (a + H * h) := by
  classical
  apply ChallengeHeightLE.sum_bound
  intro m hm
  have hp := ChallengeHeightLE.prod_bound m.support (fun i ↦ N i ^ m i)
    (fun i ↦ m i * (d i * h)) (fun i _ ↦ (hN i).pow_bound (m i))
  have he : (∑ i ∈ m.support, m i * (d i * h)) = Finsupp.weight d m * h := by
    simp only [Finsupp.weight_apply, Finsupp.sum, smul_eq_mul, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [he] at hp
  have ht := ((ChallengeHeightLE.const (σ := σ) (hQ m)).mul_bound hp).mul_bound
    (hS.pow_bound (H - Finsupp.weight d m))
  have hb := Nat.sub_add_cancel (hbudget m hm)
  convert ht using 1
  nlinarith

/-- The recursive Taylor numerator has challenge degree given only by its denominator exponent
and source challenge height. -/
theorem challengeHeightLE_rationalTaylorNumeratorOver
    (Q : DifferentialPolynomial F[X] r) (center : F) (hQ : ChallengeHeightLE Q ℓ)
    (l : ℕ) :
    ChallengeHeightLE (rationalTaylorNumeratorOver (F := F) (Polynomial.C center) Q l)
      ((2 * (l - r) - 1) * ℓ) := by
  induction l using Nat.strong_induction_on with
  | h l ih =>
    rw [rationalTaylorNumeratorOver]
    split_ifs with hl
    · apply ChallengeHeightLE.mono
      · intro m
        simp only [MvPolynomial.coeff_X]
        split_ifs <;> simp
      · exact Nat.zero_le _
    · have hh : 0 < l - r := by omega
      have hlr : r + (l - r) = l := by omega
      have hden := denominator_weight_le_of_mem_universalTaylorResidual_coeff
        (r := r) (h := l - r) hh (Polynomial.C center) Q
      rw [hlr] at hden
      have hd := challengeHeightLE_clearedSubstitution
        (initialJetSeparantOver (Polynomial.C center) Q)
        (fun i : Fin l ↦ rationalTaylorNumeratorOver (F := F) (Polynomial.C center) Q i.val)
        (fun i ↦ 2 * (i.val - r) - 1) (2 * (l - r) - 2) ℓ ℓ
        ((optionEquivLeft F[X] (Fin l)
          (universalTaylorResidual l (Polynomial.C center) Q)).coeff (l - r))
        (challengeHeightLE_initialJetSeparantOver Q center hQ)
        (fun i ↦ ih i.val i.isLt)
        (universalTaylorResidual_coeff_natDegree_le Q center hQ l (l - r)) hden
      have hc : ChallengeHeightLE
          (-MvPolynomial.C (algebraMap F F[X] ((l.choose r : F)⁻¹)) :
            MvPolynomial (Fin (r + 1)) F[X]) 0 := by
        rw [← map_neg]
        apply ChallengeHeightLE.const
        simp
      have ht := hc.mul_bound hd
      have he : 2 * (l - r) - 1 = (2 * (l - r) - 2) + 1 := by omega
      convert ht using 1
      simp only [he, Nat.add_mul, Nat.one_mul, zero_add]
      omega

/-- Clearing at a sufficient exponent `τ` gives challenge degree at most `τ * h`. -/
theorem challengeHeightLE_commonTaylorNumeratorOver_of_exponent
    (Q : DifferentialPolynomial F[X] r) (center : F) (hQ : ChallengeHeightLE Q ℓ)
    (K τ : ℕ) (hτ : TaylorExponentSufficient r K τ) (l : Fin K) :
    ChallengeHeightLE
      (commonTaylorNumeratorOver (F := F) (Polynomial.C center) Q K l (τ := τ))
      (τ * ℓ) := by
  unfold commonTaylorNumeratorOver
  have ht := (challengeHeightLE_rationalTaylorNumeratorOver Q center hQ l.val).mul_bound
    ((challengeHeightLE_initialJetSeparantOver Q center hQ).pow_bound
      (τ - (2 * (l.val - r) - 1)))
  have he := Nat.add_sub_of_le (hτ l)
  convert ht using 1
  nlinarith

/-- Common clearing at the default exponent `2K` gives challenge degree at most `2K * h`. -/
theorem challengeHeightLE_commonTaylorNumeratorOver
    (Q : DifferentialPolynomial F[X] r) (center : F) (hQ : ChallengeHeightLE Q ℓ)
    (K : ℕ) (l : Fin K) :
    ChallengeHeightLE (commonTaylorNumeratorOver (F := F) (Polynomial.C center) Q K l)
      (2 * K * ℓ) := by
  exact challengeHeightLE_commonTaylorNumeratorOver_of_exponent Q center hQ K (2 * K)
    (taylorExponentSufficient_two_mul r K) l

/-- Jet total degree of the recursive Taylor numerator is independent of challenge height. -/
theorem totalDegree_rationalTaylorNumeratorOver_le
    (center : F[X]) (Q : DifferentialPolynomial F[X] r) (v : ℕ) (hv : 0 < v)
    (hjet : Q.weightedTotalDegree (fun i ↦ i.elim 0 (fun _ ↦ 1)) ≤ v) (l : ℕ) :
    (rationalTaylorNumeratorOver (F := F) center Q l).totalDegree ≤
      (2 * (l - r) - 1) * (v - 1) + 1 := by
  induction l using Nat.strong_induction_on with
  | h l ih =>
    rw [rationalTaylorNumeratorOver]
    split_ifs with hl
    · simp only [totalDegree_X]
      omega
    · have hh : 0 < l - r := by omega
      have hlr : r + (l - r) = l := by omega
      have hden := denominator_weight_le_of_mem_universalTaylorResidual_coeff
        (r := r) (h := l - r) hh center Q
      rw [hlr] at hden
      have hd := totalDegree_clearedSubstitution
        (initialJetSeparantOver center Q)
        (fun i : Fin l ↦ rationalTaylorNumeratorOver (F := F) center Q i.val)
        (fun i ↦ 2 * (i.val - r) - 1) (2 * (l - r) - 2) (v - 1) v
        ((optionEquivLeft F[X] (Fin l) (universalTaylorResidual l center Q)).coeff (l - r))
        ((totalDegree_initialJetSeparantOver_le center Q).trans (Nat.sub_le_sub_right hjet 1))
        (fun i ↦ ih i.val i.isLt) hden
        ((totalDegree_universalTaylorResidual_coeff_le l center Q (l - r)).trans hjet)
      have hp := totalDegree_mul
        (-MvPolynomial.C (algebraMap F F[X] ((l.choose r : F)⁻¹)))
        (clearedSubstitution MvPolynomial.C (initialJetSeparantOver center Q)
          (fun i : Fin l ↦ rationalTaylorNumeratorOver (F := F) center Q i.val)
          (fun i ↦ 2 * (i.val - r) - 1) (2 * (l - r) - 2)
          ((optionEquivLeft F[X] (Fin l) (universalTaylorResidual l center Q)).coeff (l - r)))
      simp only [totalDegree_neg, totalDegree_C, zero_add] at hp
      have he : 2 * (l - r) - 1 = (2 * (l - r) - 2) + 1 := by omega
      have hvsub := Nat.sub_add_cancel (Nat.succ_le_of_lt hv)
      rw [he]
      nlinarith [hp.trans hd]

/-- Taylor numerators padded to a sufficient exponent have separate challenge and jet bounds. -/
theorem commonTaylorNumeratorOver_bidegree_of_exponent
    (center : F) (Q : DifferentialPolynomial F[X] r) (v h : ℕ) (hv : 0 < v)
    (hjet : Q.weightedTotalDegree (fun i ↦ i.elim 0 (fun _ ↦ 1)) ≤ v)
    (hQ : ChallengeHeightLE Q h) (K τ : ℕ) (hτ : TaylorExponentSufficient r K τ)
    (l : Fin K) :
    ChallengeHeightLE
        (commonTaylorNumeratorOver (F := F) (Polynomial.C center) Q K l (τ := τ))
        (τ * h) ∧
      (commonTaylorNumeratorOver (F := F) (Polynomial.C center) Q K l
        (τ := τ)).totalDegree ≤ 1 + τ * (v - 1) := by
  refine ⟨challengeHeightLE_commonTaylorNumeratorOver_of_exponent
    Q center hQ K τ hτ l, ?_⟩
  unfold commonTaylorNumeratorOver
  have hS := (totalDegree_initialJetSeparantOver_le (Polynomial.C center) Q).trans
    (Nat.sub_le_sub_right hjet 1)
  have hN := totalDegree_rationalTaylorNumeratorOver_le (Polynomial.C center) Q v hv hjet l.val
  have hp := (totalDegree_pow (initialJetSeparantOver (Polynomial.C center) Q)
    (τ - (2 * (l.val - r) - 1))).trans (Nat.mul_le_mul_left _ hS)
  have hm := totalDegree_mul
    (rationalTaylorNumeratorOver (F := F) (Polynomial.C center) Q l.val)
    (initialJetSeparantOver (Polynomial.C center) Q ^ (τ - (2 * (l.val - r) - 1)))
  have he := Nat.add_sub_of_le (hτ l)
  nlinarith

/-- Default common Taylor numerators have the original separate degree bounds. -/
theorem commonTaylorNumeratorOver_bidegree
    (center : F) (Q : DifferentialPolynomial F[X] r) (v h : ℕ) (hv : 0 < v)
    (hjet : Q.weightedTotalDegree (fun i ↦ i.elim 0 (fun _ ↦ 1)) ≤ v)
    (hQ : ChallengeHeightLE Q h) (K : ℕ) (l : Fin K) :
    ChallengeHeightLE (commonTaylorNumeratorOver (F := F) (Polynomial.C center) Q K l)
        (2 * K * h) ∧
      (commonTaylorNumeratorOver (F := F) (Polynomial.C center) Q K l).totalDegree ≤
        1 + 2 * K * (v - 1) := by
  exact commonTaylorNumeratorOver_bidegree_of_exponent center Q v h hv hjet hQ
    K (2 * K) (taylorExponentSufficient_two_mul r K) l

/-- An explicit common denominator retains both degree bounds without mixing coordinates. -/
theorem commonTaylorDenominatorOver_bidegree_of_exponent
    (center : F) (Q : DifferentialPolynomial F[X] r) (v h : ℕ)
    (hjet : Q.weightedTotalDegree (fun i ↦ i.elim 0 (fun _ ↦ 1)) ≤ v)
    (hQ : ChallengeHeightLE Q h) (τ : ℕ) :
    ChallengeHeightLE (initialJetSeparantOver (Polynomial.C center) Q ^ τ) (τ * h) ∧
      (initialJetSeparantOver (Polynomial.C center) Q ^ τ).totalDegree ≤
        τ * (v - 1) := by
  refine ⟨(challengeHeightLE_initialJetSeparantOver Q center hQ).pow_bound _, ?_⟩
  exact (totalDegree_pow _ _).trans (Nat.mul_le_mul_left _
    ((totalDegree_initialJetSeparantOver_le (Polynomial.C center) Q).trans
      (Nat.sub_le_sub_right hjet 1)))

/-- The default common denominator retains both degree bounds without counting challenge
degree as jet degree. -/
theorem commonTaylorDenominatorOver_bidegree
    (center : F) (Q : DifferentialPolynomial F[X] r) (v h : ℕ)
    (hjet : Q.weightedTotalDegree (fun i ↦ i.elim 0 (fun _ ↦ 1)) ≤ v)
    (hQ : ChallengeHeightLE Q h) (K : ℕ) :
    ChallengeHeightLE (initialJetSeparantOver (Polynomial.C center) Q ^ (2 * K))
        (2 * K * h) ∧
      (initialJetSeparantOver (Polynomial.C center) Q ^ (2 * K)).totalDegree ≤
        2 * K * (v - 1) := by
  exact commonTaylorDenominatorOver_bidegree_of_exponent center Q v h hjet hQ (2 * K)

/-- A sufficiently padded polynomial-curve agreement cut has challenge degree linear in the
batching degree, while its jet total degree is independent of the batching degree. -/
theorem taylorCurveAgreementEquationOver_bidegree_of_exponent
    (center : F) (Q : DifferentialPolynomial F[X] r) (v h : ℕ) (hv : 0 < v)
    (hjet : Q.weightedTotalDegree (fun i ↦ i.elim 0 (fun _ ↦ 1)) ≤ v)
    (hQ : ChallengeHeightLE Q h) (K τ : ℕ) (hτ : TaylorExponentSufficient r K τ)
    (x : F) (y : F[X])
    (hy : y.natDegree ≤ ℓ) :
    let cut := taylorAgreementEquationOver (F := F) (Polynomial.C center) Q K
      (Polynomial.C x) y (τ := τ)
    ChallengeHeightLE cut (ℓ + τ * h) ∧
      cut.totalDegree ≤ 1 + τ * (v - 1) := by
  dsimp only
  unfold taylorAgreementEquationOver
  have hd := commonTaylorDenominatorOver_bidegree_of_exponent center Q v h hjet hQ τ
  have hcoeff (l : Fin K) : ChallengeHeightLE
      (MvPolynomial.C ((Polynomial.C x - Polynomial.C center) ^ l.val) :
        MvPolynomial (Fin (r + 1)) F[X]) 0 := by
    apply ChallengeHeightLE.const
    rw [← map_sub, ← map_pow, Polynomial.natDegree_C]
  have hsum := ChallengeHeightLE.sum_bound Finset.univ
    (fun l : Fin K ↦ MvPolynomial.C ((Polynomial.C x - Polynomial.C center) ^ l.val) *
      commonTaylorNumeratorOver (F := F) (Polynomial.C center) Q K l (τ := τ))
        (h := ℓ + τ * h)
    (fun l _ ↦ ((hcoeff l).mul_bound
      (challengeHeightLE_commonTaylorNumeratorOver_of_exponent Q center hQ K τ hτ l)).mono
        (by omega))
  have hy' : ChallengeHeightLE
      (MvPolynomial.C y : MvPolynomial (Fin (r + 1)) F[X]) ℓ :=
    ChallengeHeightLE.const hy
  refine ⟨?_, ?_⟩
  · intro m
    rw [MvPolynomial.coeff_sub]
    exact (Polynomial.natDegree_sub_le _ _).trans
      (max_le (hsum m) ((hy'.mul_bound hd.1) m))
  · apply (totalDegree_sub _ _).trans
    apply max_le
    · apply totalDegree_finsetSum_le
      intro l _
      exact (totalDegree_mul _ _).trans (by
        simpa only [totalDegree_C, zero_add] using
          (commonTaylorNumeratorOver_bidegree_of_exponent
            center Q v h hv hjet hQ K τ hτ l).2)
    · exact (totalDegree_mul _ _).trans (by
        simp only [totalDegree_C, zero_add]
        exact hd.2.trans (Nat.le_add_left _ _))

/-- The default polynomial-curve agreement cut has the original separate degree bounds. -/
theorem taylorCurveAgreementEquationOver_bidegree
    (center : F) (Q : DifferentialPolynomial F[X] r) (v h : ℕ) (hv : 0 < v)
    (hjet : Q.weightedTotalDegree (fun i ↦ i.elim 0 (fun _ ↦ 1)) ≤ v)
    (hQ : ChallengeHeightLE Q h) (K : ℕ) (x : F) (y : F[X])
    (hy : y.natDegree ≤ ℓ) :
    let cut := taylorAgreementEquationOver (F := F) (Polynomial.C center) Q K
      (Polynomial.C x) y
    ChallengeHeightLE cut (ℓ + 2 * K * h) ∧
      cut.totalDegree ≤ 1 + 2 * K * (v - 1) := by
  exact taylorCurveAgreementEquationOver_bidegree_of_exponent center Q v h hv hjet hQ
    K (2 * K) (taylorExponentSufficient_two_mul r K) x y hy

/-! ## Coefficient-linearized lifted-power cuts -/

/-- Coordinates for the degree-`D` power lift, together with the original jet coordinates.
The power coordinate `j` represents the challenge monomial `z ^ j`. -/
abbrev PowerLiftIndex (D : ℕ) (σ : Type*) := Sum (Fin (D + 1)) σ

/-- Evaluation of lifted-power coordinates on the actual challenge/jet source space. -/
def powerMomentMap {σ : Type*} (D : ℕ) :
    MvPolynomial (PowerLiftIndex D σ) F →ₐ[F] MvPolynomial (Option σ) F :=
  MvPolynomial.aeval fun i ↦ i.elim
    (fun j ↦ (MvPolynomial.X none) ^ j.val) (fun j ↦ MvPolynomial.X (some j))

/-- The concrete lifted-power base variety. -/
def powerMomentIdeal {σ : Type*} (D : ℕ) :
    Ideal (MvPolynomial (PowerLiftIndex D σ) F) :=
  RingHom.ker (powerMomentMap D).toRingHom

/-- The lifted-power base is irreducible, since its coordinate map lands in a polynomial
domain. -/
theorem powerMomentIdeal_isPrime {σ : Type*} (D : ℕ) :
    (powerMomentIdeal (F := F) (σ := σ) D).IsPrime :=
  RingHom.ker_isPrime (powerMomentMap D).toRingHom

/-- When a positive power coordinate is present, the moment map is onto the ordinary
challenge/jet polynomial ring. -/
theorem powerMomentMap_surjective {σ : Type*} (D : ℕ) (hD : 0 < D) :
    Function.Surjective (powerMomentMap (F := F) (σ := σ) D) := by
  intro P
  induction P using MvPolynomial.induction_on with
  | C a => exact ⟨MvPolynomial.C a, by simp [powerMomentMap]⟩
  | add P Q hP hQ =>
      obtain ⟨P', rfl⟩ := hP
      obtain ⟨Q', rfl⟩ := hQ
      exact ⟨P' + Q', by simp⟩
  | mul_X P i hP =>
      obtain ⟨P', rfl⟩ := hP
      cases i with
      | none =>
          exact ⟨P' * MvPolynomial.X (Sum.inl ⟨1, by omega⟩), by
            simp [powerMomentMap]⟩
      | some i =>
          exact ⟨P' * MvPolynomial.X (Sum.inr i), by simp [powerMomentMap]⟩

/-- Linearize one bounded-degree challenge coefficient in the power coordinates. -/
def coefficientPowerLift {σ : Type*} (D : ℕ) (p : F[X]) (_hp : p.natDegree ≤ D) :
    MvPolynomial (PowerLiftIndex D σ) F :=
  ∑ j : Fin (D + 1), MvPolynomial.C (p.coeff j.val) * MvPolynomial.X (Sum.inl j)

/-- The coefficient lift evaluates to the original coefficient polynomial in the challenge
coordinate. -/
theorem powerMomentMap_coefficientPowerLift {σ : Type*} (D : ℕ) (p : F[X])
    (hp : p.natDegree ≤ D) :
    powerMomentMap D (coefficientPowerLift (σ := σ) D p hp) =
      Polynomial.aeval (MvPolynomial.X none : MvPolynomial (Option σ) F) p := by
  classical
  rw [coefficientPowerLift, map_sum]
  simp only [map_mul, powerMomentMap, MvPolynomial.aeval_X, MvPolynomial.aeval_C,
    MvPolynomial.algebraMap_eq, Sum.elim_inl]
  change (∑ j : Fin (D + 1), MvPolynomial.C (p.coeff j.val) *
    (MvPolynomial.X none : MvPolynomial (Option σ) F) ^ j.val) = _
  rw [Polynomial.aeval_def,
    Polynomial.eval₂_eq_sum_range' (algebraMap F (MvPolynomial (Option σ) F))
      (by omega : p.natDegree < D + 1) (MvPolynomial.X none)]
  exact Fin.sum_univ_eq_sum_range
    (fun j : ℕ ↦ MvPolynomial.C (p.coeff j) *
      (MvPolynomial.X none : MvPolynomial (Option σ) F) ^ j) (D + 1)

/-- Linearize every challenge coefficient of a joint challenge/jet polynomial. -/
def polynomialPowerLift {σ : Type*} (D : ℕ) (P : MvPolynomial σ F[X])
    (hP : ChallengeHeightLE P D) : MvPolynomial (PowerLiftIndex D σ) F :=
  ∑ m ∈ P.support,
    coefficientPowerLift D (MvPolynomial.coeff m P) (hP m) *
      ∏ i ∈ m.support, MvPolynomial.X (Sum.inr i) ^ m i

/-- Coefficient linearization is an exact lift: evaluating on the power-moment variety recovers
the ordinary challenge flattening. -/
theorem powerMomentMap_polynomialPowerLift {σ : Type*} (D : ℕ)
    (P : MvPolynomial σ F[X]) (hP : ChallengeHeightLE P D) :
    powerMomentMap D (polynomialPowerLift D P hP) = flattenChallenge P := by
  classical
  rw [polynomialPowerLift, map_sum]
  conv_rhs => rw [P.as_sum]
  simp only [map_sum, monomial_eq, map_mul, Finsupp.prod, map_prod, map_pow,
    flattenChallenge_C, flattenChallenge_X]
  apply Finset.sum_congr rfl
  intro m hm
  change powerMomentMap D (coefficientPowerLift D (MvPolynomial.coeff m P) (hP m)) * _ = _
  rw [powerMomentMap_coefficientPowerLift]
  simp [powerMomentMap]

/-- Each lifted coefficient is linear in the power coordinates. -/
theorem coefficientPowerLift_totalDegree_le_one {σ : Type*} (D : ℕ) (p : F[X])
    (hp : p.natDegree ≤ D) :
    (coefficientPowerLift (σ := σ) D p hp).totalDegree ≤ 1 := by
  classical
  apply MvPolynomial.totalDegree_finsetSum_le
  intro j hj
  exact (MvPolynomial.totalDegree_mul _ _).trans (by simp)

/-- A bidegree `(D, B)` cut becomes an ordinary lifted cut of total degree at most `B + 1`,
independent of `D`. -/
theorem polynomialPowerLift_totalDegree_le {σ : Type*} (D B : ℕ)
    (P : MvPolynomial σ F[X]) (hP : ChallengeHeightLE P D) (hdeg : P.totalDegree ≤ B) :
    (polynomialPowerLift D P hP).totalDegree ≤ B + 1 := by
  classical
  rw [polynomialPowerLift]
  apply MvPolynomial.totalDegree_finsetSum_le
  intro m hm
  apply (MvPolynomial.totalDegree_mul _ _).trans
  have hc := coefficientPowerLift_totalDegree_le_one (σ := σ) D (MvPolynomial.coeff m P)
    (hP m)
  have hj : (∏ i ∈ m.support,
      (MvPolynomial.X (Sum.inr i) : MvPolynomial (PowerLiftIndex D σ) F) ^ m i).totalDegree ≤
      m.sum fun _ e ↦ e := by
    apply (MvPolynomial.totalDegree_finsetProd _ _).trans
    simp [Finsupp.sum, MvPolynomial.totalDegree_X_pow]
  exact (Nat.add_le_add hc (hj.trans (MvPolynomial.le_totalDegree hm))).trans (by omega)

end ReedSolomon

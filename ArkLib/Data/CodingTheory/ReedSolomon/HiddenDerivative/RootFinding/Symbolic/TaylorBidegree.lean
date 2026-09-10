/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.Symbolic.TaylorCutDegree
public import ArkLib.ToMathlib.AlgebraicGeometry.Hilbert.Bidegree

/-!
# Bidegrees of symbolic Taylor cuts

This file keeps the challenge degree and the total jet degree separate.  For a source
differential polynomial of challenge height `h` and jet degree `v`, the initial equation lies
in the `(h,v)` rectangle. With a sufficient common exponent `τ`, every common Taylor
numerator lies in `(τ*h, 1 + τ*(v-1))`; an agreement cut against a received polynomial of
degree at most `ell` lies in `(ell + τ*h, 1 + τ*(v-1))`.

The conclusions are stated as membership in `AffineHilbert.restrictBidegree`, so the cuts can
be passed directly to `AffineHilbert.bidegreeLift`.
-/

@[expose] public section

open PolynomialDifferential

namespace ReedSolomon.HiddenDerivative

noncomputable section

open MvPolynomial Polynomial
open scoped BigOperators

variable {F σ τ : Type*} [Field F] {r : ℕ}

private theorem ChallengeHeightLE.mono {P : MvPolynomial σ F[X]} {a b : ℕ}
    (hP : ChallengeHeightLE P a) (hab : a ≤ b) : ChallengeHeightLE P b :=
  fun m ↦ (hP m).trans hab

private theorem height_C {p : F[X]} {h : ℕ} (hp : p.natDegree ≤ h) :
    ChallengeHeightLE (C p : MvPolynomial σ F[X]) h := by
  classical
  intro m
  by_cases hm : m = 0
  · subst m
    simpa using hp
  · simp [MvPolynomial.coeff_C, Ne.symm hm]

private theorem height_X (i : σ) :
    ChallengeHeightLE (X i : MvPolynomial σ F[X]) 0 := by
  classical
  intro m
  by_cases hm : m = Finsupp.single i 1
  · subst m
    simp
  · simp [MvPolynomial.coeff_X, Ne.symm hm]

private theorem ChallengeHeightLE.add {P Q : MvPolynomial σ F[X]} {h : ℕ}
    (hP : ChallengeHeightLE P h) (hQ : ChallengeHeightLE Q h) :
    ChallengeHeightLE (P + Q) h := by
  intro m
  rw [MvPolynomial.coeff_add]
  exact (Polynomial.natDegree_add_le _ _).trans (max_le (hP m) (hQ m))

private theorem ChallengeHeightLE.neg {P : MvPolynomial σ F[X]} {h : ℕ}
    (hP : ChallengeHeightLE P h) : ChallengeHeightLE (-P) h := by
  intro m
  simpa using hP m

private theorem ChallengeHeightLE.sub {P Q : MvPolynomial σ F[X]} {h : ℕ}
    (hP : ChallengeHeightLE P h) (hQ : ChallengeHeightLE Q h) :
    ChallengeHeightLE (P - Q) h := by
  rw [sub_eq_add_neg]
  exact hP.add hQ.neg

private theorem ChallengeHeightLE.mul {P Q : MvPolynomial σ F[X]} {a b : ℕ}
    (hP : ChallengeHeightLE P a) (hQ : ChallengeHeightLE Q b) :
    ChallengeHeightLE (P * Q) (a + b) := by
  classical
  intro m
  rw [MvPolynomial.coeff_mul]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro pair _
  exact Polynomial.natDegree_mul_le_of_le (hP pair.1) (hQ pair.2)

private theorem ChallengeHeightLE.pow {P : MvPolynomial σ F[X]} {h : ℕ}
    (hP : ChallengeHeightLE P h) (n : ℕ) : ChallengeHeightLE (P ^ n) (n * h) := by
  induction n with
  | zero => simpa using height_C (σ := σ) (p := (1 : F[X])) (h := 0) (by simp)
  | succ n ih =>
      rw [pow_succ, Nat.succ_mul]
      exact ih.mul hP

private theorem height_sum {ι : Type*} (s : Finset ι)
    (P : ι → MvPolynomial σ F[X]) {h : ℕ}
    (hP : ∀ i ∈ s, ChallengeHeightLE (P i) h) :
    ChallengeHeightLE (∑ i ∈ s, P i) h := by
  intro m
  rw [MvPolynomial.coeff_sum]
  apply Polynomial.natDegree_sum_le_of_forall_le
  exact fun i hi ↦ hP i hi m

private theorem height_prod_weighted {ι : Type*} (s : Finset ι)
    (P : ι → MvPolynomial σ F[X]) (d : ι → ℕ) (h : ℕ)
    (hP : ∀ i ∈ s, ChallengeHeightLE (P i) (d i * h)) :
    ChallengeHeightLE (∏ i ∈ s, P i) ((∑ i ∈ s, d i) * h) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using height_C (σ := σ) (p := (1 : F[X])) (h := 0) (by simp)
  | @insert i s hi ih =>
      rw [Finset.prod_insert hi, Finset.sum_insert hi, add_mul]
      exact (hP i (Finset.mem_insert_self i s)).mul
        (ih fun j hj ↦ hP j (Finset.mem_insert_of_mem hj))

private theorem challengeHeightLE_clearedSubstitution
    (S : MvPolynomial σ F[X]) (N : τ → MvPolynomial σ F[X])
    (d : τ → ℕ) (H h : ℕ) (Q : MvPolynomial τ F[X])
    (hS : ChallengeHeightLE S h)
    (hN : ∀ i, ChallengeHeightLE (N i) (d i * h))
    (hden : ∀ m ∈ Q.support, Finsupp.weight d m ≤ H)
    (hQ : ∀ m ∈ Q.support, (coeff m Q).natDegree ≤ h) :
    ChallengeHeightLE (clearedSubstitution C S N d H Q) (H * h + h) := by
  classical
  unfold clearedSubstitution
  apply height_sum
  intro m hm
  have hprod : ChallengeHeightLE (∏ i ∈ m.support, N i ^ m i)
      (Finsupp.weight d m * h) := by
    have hp := height_prod_weighted (F := F) (m.support)
      (fun i ↦ N i ^ m i) (fun i ↦ m i * d i) h
      (fun i _ ↦ by
        simpa only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using
          (hN i).pow (m i))
    simpa only [Finsupp.weight_apply, Finsupp.sum, smul_eq_mul, Nat.mul_comm] using hp
  have hpow := hS.pow (H - Finsupp.weight d m)
  have hterm := ((height_C (hQ m hm)).mul hprod).mul hpow
  apply hterm.mono
  have hbudget := Nat.sub_add_cancel (hden m hm)
  nlinarith

/-- The exact challenge-height recurrence for a symbolic Taylor numerator. -/
theorem challengeHeightLE_rationalTaylorNumeratorOver
    (center : F) (Q : DifferentialPolynomial F[X] r) (h : ℕ)
    (hQ : ChallengeHeightLE Q h) (l : ℕ) :
    ChallengeHeightLE
      (rationalTaylorNumeratorOver (F := F) (Polynomial.C center) Q l)
      ((2 * (l - r) - 1) * h) := by
  induction l using Nat.strong_induction_on with
  | h l ih =>
      rw [rationalTaylorNumeratorOver]
      split_ifs with hl
      · exact ChallengeHeightLE.mono
          (height_X (F := F) (σ := Fin (r + 1)) ⟨l, hl⟩) (Nat.zero_le _)
      · have hh : 0 < l - r := by omega
        have hlr : r + (l - r) = l := by omega
        have hden := denominator_weight_le_of_mem_universalTaylorResidual_coeff
          (r := r) (h := l - r) hh (Polynomial.C center) Q
        rw [hlr] at hden
        have hd := challengeHeightLE_clearedSubstitution
          (initialJetSeparantOver (Polynomial.C center) Q)
          (fun i : Fin l ↦ rationalTaylorNumeratorOver (F := F)
            (Polynomial.C center) Q i.val)
          (fun i ↦ 2 * (i.val - r) - 1) (2 * (l - r) - 2) h
          ((optionEquivLeft F[X] (Fin l)
            (universalTaylorResidual l (Polynomial.C center) Q)).coeff (l - r))
          (challengeHeightLE_initialJetSeparantOver Q center hQ)
          (fun i ↦ ih i.val i.isLt) hden
          (fun m _ ↦ universalTaylorResidual_coeff_natDegree_le Q center hQ l (l - r) m)
        have hc : ChallengeHeightLE
            (-MvPolynomial.C (algebraMap F F[X] ((l.choose r : F)⁻¹)) :
              MvPolynomial (Fin (r + 1)) F[X]) 0 := by
          apply (height_C (by simp)).neg
        have hm := hc.mul hd
        have he : 2 * (l - r) - 1 = (2 * (l - r) - 2) + 1 := by omega
        rw [he]
        simpa only [Polynomial.algebraMap_eq, zero_add, add_mul, one_mul] using hm

/-- A numerator padded to a sufficient exponent has challenge degree at most `τ*h`. -/
theorem challengeHeightLE_commonTaylorNumeratorOver_of_exponent
    (center : F) (Q : DifferentialPolynomial F[X] r) (h K τ : ℕ)
    (hτ : TaylorExponentSufficient r K τ)
    (hQ : ChallengeHeightLE Q h) (l : Fin K) :
    ChallengeHeightLE
      (commonTaylorNumeratorOver (F := F) (Polynomial.C center) Q K l (τ := τ))
      (τ * h) := by
  unfold commonTaylorNumeratorOver
  have hn := challengeHeightLE_rationalTaylorNumeratorOver center Q h hQ l.val
  have hs := (challengeHeightLE_initialJetSeparantOver Q center hQ).pow
    (τ - (2 * (l.val - r) - 1))
  have hm := hn.mul hs
  apply hm.mono
  have he := Nat.sub_add_cancel (hτ l)
  nlinarith

/-- Every default common symbolic numerator has challenge degree at most `2*K*h`. -/
theorem challengeHeightLE_commonTaylorNumeratorOver
    (center : F) (Q : DifferentialPolynomial F[X] r) (h K : ℕ)
    (hQ : ChallengeHeightLE Q h) (l : Fin K) :
    ChallengeHeightLE
      (commonTaylorNumeratorOver (F := F) (Polynomial.C center) Q K l)
      (2 * K * h) := by
  exact challengeHeightLE_commonTaylorNumeratorOver_of_exponent center Q h K (2 * K)
    (taylorExponentSufficient_two_mul r K) hQ l

/-- The exact jet-degree recurrence for a symbolic Taylor numerator. -/
theorem totalDegree_rationalTaylorNumeratorOver_le_of_jet
    (center : Polynomial F) (Q : DifferentialPolynomial F[X] r) (v : ℕ)
    (hv : 0 < v)
    (hjet : Q.weightedTotalDegree (fun i ↦ i.elim 0 (fun _ ↦ 1)) ≤ v)
    (l : ℕ) :
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
          ((optionEquivLeft F[X] (Fin l)
            (universalTaylorResidual l center Q)).coeff (l - r))
          ((totalDegree_initialJetSeparantOver_le center Q).trans
            (Nat.sub_le_sub_right hjet 1))
          (fun i ↦ ih i.val i.isLt) hden
          ((totalDegree_universalTaylorResidual_coeff_le l center Q (l - r)).trans hjet)
        have hm := totalDegree_mul
          (-MvPolynomial.C (algebraMap F F[X] ((l.choose r : F)⁻¹)) :
            MvPolynomial (Fin (r + 1)) F[X])
          (clearedSubstitution C (initialJetSeparantOver center Q)
            (fun i : Fin l ↦ rationalTaylorNumeratorOver (F := F) center Q i.val)
            (fun i ↦ 2 * (i.val - r) - 1) (2 * (l - r) - 2)
            ((optionEquivLeft F[X] (Fin l)
              (universalTaylorResidual l center Q)).coeff (l - r)))
        simp only [totalDegree_neg, totalDegree_C, zero_add] at hm
        have he : 2 * (l - r) - 1 = (2 * (l - r) - 2) + 1 := by omega
        rw [he]
        have hvsub := Nat.sub_add_cancel (Nat.succ_le_of_lt hv)
        nlinarith [hm.trans hd]

/-- Every numerator padded to a sufficient exponent has total jet degree at most
`1 + τ*(v-1)`. -/
theorem totalDegree_commonTaylorNumeratorOver_le_of_jet_and_exponent
    (center : Polynomial F) (Q : DifferentialPolynomial F[X] r) (v K τ : ℕ)
    (hτ : TaylorExponentSufficient r K τ)
    (hv : 0 < v)
    (hjet : Q.weightedTotalDegree (fun i ↦ i.elim 0 (fun _ ↦ 1)) ≤ v)
    (l : Fin K) :
    (commonTaylorNumeratorOver (F := F) center Q K l (τ := τ)).totalDegree ≤
      1 + τ * (v - 1) := by
  have hd := totalDegree_rationalTaylorNumeratorOver_le_of_jet center Q v hv hjet l.val
  have hs := (totalDegree_initialJetSeparantOver_le center Q).trans
    (Nat.sub_le_sub_right hjet 1)
  have hp := (totalDegree_pow (initialJetSeparantOver center Q)
    (τ - (2 * (l.val - r) - 1))).trans (Nat.mul_le_mul_left _ hs)
  have hm := totalDegree_mul (rationalTaylorNumeratorOver (F := F) center Q l.val)
    (initialJetSeparantOver center Q ^ (τ - (2 * (l.val - r) - 1)))
  have he := Nat.sub_add_cancel (hτ l)
  unfold commonTaylorNumeratorOver
  nlinarith

/-- Every default common symbolic numerator has total jet degree at most
`1 + 2*K*(v-1)`. -/
theorem totalDegree_commonTaylorNumeratorOver_le_of_jet
    (center : Polynomial F) (Q : DifferentialPolynomial F[X] r) (v K : ℕ)
    (hv : 0 < v)
    (hjet : Q.weightedTotalDegree (fun i ↦ i.elim 0 (fun _ ↦ 1)) ≤ v)
    (l : Fin K) :
    (commonTaylorNumeratorOver (F := F) center Q K l).totalDegree ≤
      1 + 2 * K * (v - 1) := by
  exact totalDegree_commonTaylorNumeratorOver_le_of_jet_and_exponent
    center Q v K (2 * K) (taylorExponentSufficient_two_mul r K) hv hjet l

private theorem weightedTotalDegree_finsetSum_le {R ι : Type*} [CommSemiring R]
    (w : σ → ℕ) (s : Finset ι) (P : ι → MvPolynomial σ R) (d : ℕ)
    (hP : ∀ i ∈ s, (P i).weightedTotalDegree w ≤ d) :
    (∑ i ∈ s, P i).weightedTotalDegree w ≤ d := by
  unfold MvPolynomial.weightedTotalDegree
  exact (AddMonoidAlgebra.supDegree_sum_le.trans
    (Finset.sup_le fun i hi ↦ hP i hi))

private theorem weightedTotalDegree_X_eq {R : Type*} [CommSemiring R] [Nontrivial R]
    (w : σ → ℕ) (i : σ) :
    (X i : MvPolynomial σ R).weightedTotalDegree w = w i := by
  classical
  rw [show (X i : MvPolynomial σ R) = monomial (Finsupp.single i 1) 1 by rfl]
  rw [weightedTotalDegree_monomial _ _ _ one_ne_zero]
  rw [Finsupp.weight_single]
  simp

private theorem flattenChallenge_C_challengeDegree_le (p : F[X]) :
    (flattenChallenge (C p : MvPolynomial σ F[X])).weightedTotalDegree
      (AffineHilbert.challengeWeight (σ := σ)) ≤ p.natDegree := by
  classical
  rw [flattenChallenge_C]
  have he : Polynomial.aeval (X none : MvPolynomial (Option σ) F) p =
      ∑ n ∈ p.support, MvPolynomial.C (p.coeff n) * X none ^ n := by
    simpa [Polynomial.sum_def] using congrArg
      (Polynomial.aeval (X none : MvPolynomial (Option σ) F)) p.sum_monomial_eq.symm
  rw [he]
  apply weightedTotalDegree_finsetSum_le
  intro n hn
  apply (weightedTotalDegree_mul_le _ _ _).trans
  simp only [weightedTotalDegree_C, zero_add]
  apply (weightedTotalDegree_pow_le _ _ _).trans
  rw [weightedTotalDegree_X_eq]
  simpa [AffineHilbert.challengeWeight] using Polynomial.le_natDegree_of_mem_supp n hn

private theorem flattenChallenge_C_jetDegree_zero (p : F[X]) :
    (flattenChallenge (C p : MvPolynomial σ F[X])).weightedTotalDegree
      (AffineHilbert.jetWeight (σ := σ)) = 0 := by
  classical
  rw [flattenChallenge_C]
  have he : Polynomial.aeval (X none : MvPolynomial (Option σ) F) p =
      ∑ n ∈ p.support, MvPolynomial.C (p.coeff n) * X none ^ n := by
    simpa [Polynomial.sum_def] using congrArg
      (Polynomial.aeval (X none : MvPolynomial (Option σ) F)) p.sum_monomial_eq.symm
  rw [he]
  apply Nat.eq_zero_of_le_zero
  apply weightedTotalDegree_finsetSum_le
  intro n _
  apply (weightedTotalDegree_mul_le _ _ _).trans
  simp only [weightedTotalDegree_C, zero_add]
  exact (weightedTotalDegree_pow_le _ _ _).trans (by
    rw [weightedTotalDegree_X_eq]
    simp [AffineHilbert.jetWeight])

/-- Coefficient height becomes the challenge-weighted degree after flattening. -/
theorem flattenChallenge_challengeDegree_le {P : MvPolynomial σ F[X]} {h : ℕ}
    (hP : ChallengeHeightLE P h) :
    (flattenChallenge P).weightedTotalDegree (AffineHilbert.challengeWeight (σ := σ)) ≤ h := by
  classical
  have he : flattenChallenge P =
      ∑ m ∈ P.support, flattenChallenge (C (coeff m P)) *
        ∏ i ∈ m.support, (X (some i) : MvPolynomial (Option σ) F) ^ m i := by
    conv_lhs => rw [P.as_sum]
    simp only [map_sum, monomial_eq, map_mul, Finsupp.prod, map_prod, map_pow,
      flattenChallenge_X]
  rw [he]
  apply weightedTotalDegree_finsetSum_le
  intro m hm
  apply (weightedTotalDegree_mul_le _ _ _).trans
  have hc := (flattenChallenge_C_challengeDegree_le (F := F) (σ := σ)
    (coeff m P)).trans (hP m)
  have hj : (∏ i ∈ m.support,
      (X (some i) : MvPolynomial (Option σ) F) ^ m i).weightedTotalDegree
        (AffineHilbert.challengeWeight (σ := σ)) = 0 := by
    apply Nat.eq_zero_of_le_zero
    exact (AddMonoidAlgebra.supDegree_prod_le (R := F) (A := Option σ →₀ ℕ) (B := ℕ)
      (D := Finsupp.weight (AffineHilbert.challengeWeight (σ := σ)))
      (map_zero _) (fun a b ↦ map_add _ a b)).trans (by
        rw [Nat.le_zero]
        apply Finset.sum_eq_zero
        intro i hi
        apply Nat.eq_zero_of_le_zero
        exact (weightedTotalDegree_pow_le _ _ _).trans (by
          rw [weightedTotalDegree_X_eq]
          simp [AffineHilbert.challengeWeight]))
  omega

/-- Total source-variable degree becomes the jet-weighted degree after flattening. -/
theorem flattenChallenge_jetDegree_le (P : MvPolynomial σ F[X]) :
    (flattenChallenge P).weightedTotalDegree (AffineHilbert.jetWeight (σ := σ)) ≤
      P.totalDegree := by
  classical
  have he : flattenChallenge P =
      ∑ m ∈ P.support, flattenChallenge (C (coeff m P)) *
        ∏ i ∈ m.support, (X (some i) : MvPolynomial (Option σ) F) ^ m i := by
    conv_lhs => rw [P.as_sum]
    simp only [map_sum, monomial_eq, map_mul, Finsupp.prod, map_prod, map_pow,
      flattenChallenge_X]
  rw [he]
  apply weightedTotalDegree_finsetSum_le
  intro m hm
  apply (weightedTotalDegree_mul_le _ _ _).trans
  rw [flattenChallenge_C_jetDegree_zero, zero_add]
  apply (AddMonoidAlgebra.supDegree_prod_le (R := F) (A := Option σ →₀ ℕ) (B := ℕ)
    (D := Finsupp.weight (AffineHilbert.jetWeight (σ := σ)))
    (map_zero _) (fun a b ↦ map_add _ a b)).trans
  calc
    ∑ i ∈ m.support, ((X (some i) : MvPolynomial (Option σ) F) ^ m i).weightedTotalDegree
        (AffineHilbert.jetWeight (σ := σ)) ≤ ∑ i ∈ m.support, m i := by
          apply Finset.sum_le_sum
          intro i _
          exact (weightedTotalDegree_pow_le _ _ _).trans (by
            rw [weightedTotalDegree_X_eq]
            simp [AffineHilbert.jetWeight])
    _ = m.sum (fun _ e ↦ e) := by simp [Finsupp.sum]
    _ ≤ P.totalDegree := le_totalDegree hm

/-- Separate coefficient-height and jet-degree estimates place a flattened source polynomial in
the corresponding bidegree rectangle. -/
theorem flattenChallenge_mem_restrictBidegree {P : MvPolynomial σ F[X]} {a b : ℕ}
    (ha : ChallengeHeightLE P a) (hb : P.totalDegree ≤ b) :
    flattenChallenge P ∈
      AffineHilbert.restrictBidegree (F := F) (σ := σ) a b := by
  rw [AffineHilbert.mem_restrictBidegree]
  intro m hm
  exact ⟨(le_weightedTotalDegree _ hm).trans (flattenChallenge_challengeDegree_le ha),
    (le_weightedTotalDegree _ hm).trans ((flattenChallenge_jetDegree_le P).trans hb)⟩

/-- Componentwise enlargement preserves membership in a bidegree rectangle. -/
theorem source_mem_restrictBidegree_mono {P : MvPolynomial (Option σ) F}
    {a b c d : ℕ}
    (hP : P ∈ AffineHilbert.restrictBidegree (F := F) (σ := σ) a b)
    (hac : a ≤ c) (hbd : b ≤ d) :
    P ∈ AffineHilbert.restrictBidegree (F := F) (σ := σ) c d := by
  rw [AffineHilbert.mem_restrictBidegree] at hP ⊢
  intro m hm
  exact ⟨(hP m hm).1.trans hac, (hP m hm).2.trans hbd⟩

/-- The flattened initial source equation lies in the exact `(h,v)` rectangle. -/
theorem initialJetEquationOver_mem_restrictBidegree
    (center : F) (Q : DifferentialPolynomial F[X] r) (h v : ℕ)
    (hheight : ChallengeHeightLE Q h)
    (hjet : Q.weightedTotalDegree (fun i ↦ i.elim 0 (fun _ ↦ 1)) ≤ v) :
    flattenChallenge (initialJetEquationOver (Polynomial.C center) Q) ∈
      AffineHilbert.restrictBidegree (F := F) (σ := Fin (r + 1)) h v := by
  apply flattenChallenge_mem_restrictBidegree
  · exact challengeHeightLE_initialJetEquationOver center Q hheight
  · exact (totalDegree_initialJetEquationOver_le _ Q).trans hjet

/-- The flattened initial separant lies in the exact `(h,v-1)` rectangle. -/
theorem initialJetSeparantOver_mem_restrictBidegree
    (center : F) (Q : DifferentialPolynomial F[X] r) (h v : ℕ)
    (hheight : ChallengeHeightLE Q h)
    (hjet : Q.weightedTotalDegree (fun i ↦ i.elim 0 (fun _ ↦ 1)) ≤ v) :
    flattenChallenge (initialJetSeparantOver (Polynomial.C center) Q) ∈
      AffineHilbert.restrictBidegree (F := F) (σ := Fin (r + 1)) h (v - 1) := by
  apply flattenChallenge_mem_restrictBidegree
  · exact challengeHeightLE_initialJetSeparantOver Q center hheight
  · exact (totalDegree_initialJetSeparantOver_le _ Q).trans
      (Nat.sub_le_sub_right hjet 1)

/-- Every flattened numerator padded to a sufficient exponent lies in its source-cut
rectangle. -/
theorem commonTaylorNumeratorOver_mem_restrictBidegree_of_exponent
    (center : F) (Q : DifferentialPolynomial F[X] r) (h v K τ : ℕ)
    (hτ : TaylorExponentSufficient r K τ)
    (hv : 0 < v) (hheight : ChallengeHeightLE Q h)
    (hjet : Q.weightedTotalDegree (fun i ↦ i.elim 0 (fun _ ↦ 1)) ≤ v)
    (l : Fin K) :
    flattenChallenge
        (commonTaylorNumeratorOver (F := F) (Polynomial.C center) Q K l (τ := τ)) ∈
      AffineHilbert.restrictBidegree (F := F) (σ := Fin (r + 1))
        (τ * h) (1 + τ * (v - 1)) := by
  apply flattenChallenge_mem_restrictBidegree
  · exact challengeHeightLE_commonTaylorNumeratorOver_of_exponent
      center Q h K τ hτ hheight l
  · exact totalDegree_commonTaylorNumeratorOver_le_of_jet_and_exponent
      (Polynomial.C center) Q v K τ hτ hv hjet l

/-- Every flattened default common Taylor numerator lies in the coarse source-cut rectangle. -/
theorem commonTaylorNumeratorOver_mem_restrictBidegree
    (center : F) (Q : DifferentialPolynomial F[X] r) (h v K : ℕ)
    (hv : 0 < v) (hheight : ChallengeHeightLE Q h)
    (hjet : Q.weightedTotalDegree (fun i ↦ i.elim 0 (fun _ ↦ 1)) ≤ v)
    (l : Fin K) :
    flattenChallenge
        (commonTaylorNumeratorOver (F := F) (Polynomial.C center) Q K l) ∈
      AffineHilbert.restrictBidegree (F := F) (σ := Fin (r + 1))
        (2 * K * h) (1 + 2 * K * (v - 1)) := by
  exact commonTaylorNumeratorOver_mem_restrictBidegree_of_exponent
    center Q h v K (2 * K) (taylorExponentSufficient_two_mul r K) hv hheight hjet l

/-- Agreement with a degree-`ell` received curve, padded to a sufficient exponent, lies in
the corresponding source-cut rectangle. -/
theorem taylorAgreementEquationOver_mem_restrictBidegree_of_exponent
    (center x : F) (y : F[X]) (Q : DifferentialPolynomial F[X] r)
    (ell h v K τ : ℕ) (hτ : TaylorExponentSufficient r K τ)
    (hy : y.natDegree ≤ ell) (hv : 0 < v)
    (hheight : ChallengeHeightLE Q h)
    (hjet : Q.weightedTotalDegree (fun i ↦ i.elim 0 (fun _ ↦ 1)) ≤ v) :
    flattenChallenge
        (taylorAgreementEquationOver (F := F) (Polynomial.C center) Q K
          (Polynomial.C x) y (τ := τ)) ∈
      AffineHilbert.restrictBidegree (F := F) (σ := Fin (r + 1))
        (ell + τ * h) (1 + τ * (v - 1)) := by
  apply flattenChallenge_mem_restrictBidegree
  · unfold taylorAgreementEquationOver
    apply ChallengeHeightLE.sub
    · apply (height_sum (Finset.univ) _)
      intro l _
      have hc : ChallengeHeightLE
          (C ((Polynomial.C x - Polynomial.C center) ^ l.val) :
            MvPolynomial (Fin (r + 1)) F[X]) 0 := height_C (by simp)
      exact (hc.mul (challengeHeightLE_commonTaylorNumeratorOver_of_exponent
        center Q h K τ hτ hheight l)).mono
        (by omega)
    · exact ((height_C hy).mul
        ((challengeHeightLE_initialJetSeparantOver Q center hheight).pow τ)).mono
          (by omega)
  · unfold taylorAgreementEquationOver
    apply (totalDegree_sub _ _).trans
    apply max_le
    · apply totalDegree_finsetSum_le
      intro l _
      apply (totalDegree_mul _ _).trans
      simpa only [totalDegree_C, zero_add] using
        totalDegree_commonTaylorNumeratorOver_le_of_jet_and_exponent
          (Polynomial.C center) Q v K τ hτ hv hjet l
    · apply (totalDegree_mul _ _).trans
      simp only [totalDegree_C, zero_add]
      have hs := (totalDegree_pow
          (initialJetSeparantOver (Polynomial.C center) Q) τ).trans
        (Nat.mul_le_mul_left τ
          ((totalDegree_initialJetSeparantOver_le (Polynomial.C center) Q).trans
          (Nat.sub_le_sub_right hjet 1)))
      omega

/-- Agreement with a degree-`ell` received curve lies in the default coarse rectangle. -/
theorem taylorAgreementEquationOver_mem_restrictBidegree
    (center x : F) (y : F[X]) (Q : DifferentialPolynomial F[X] r)
    (ell h v K : ℕ) (hy : y.natDegree ≤ ell) (hv : 0 < v)
    (hheight : ChallengeHeightLE Q h)
    (hjet : Q.weightedTotalDegree (fun i ↦ i.elim 0 (fun _ ↦ 1)) ≤ v) :
    flattenChallenge
        (taylorAgreementEquationOver (F := F) (Polynomial.C center) Q K
          (Polynomial.C x) y) ∈
      AffineHilbert.restrictBidegree (F := F) (σ := Fin (r + 1))
        (ell + 2 * K * h) (1 + 2 * K * (v - 1)) := by
  exact taylorAgreementEquationOver_mem_restrictBidegree_of_exponent
    center x y Q ell h v K (2 * K) (taylorExponentSufficient_two_mul r K)
      hy hv hheight hjet

end

end ReedSolomon.HiddenDerivative

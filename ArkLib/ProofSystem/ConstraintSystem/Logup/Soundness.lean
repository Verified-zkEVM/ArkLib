/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aristotle (Harmonic), Elias Judin
-/

import ArkLib.Data.MvPolynomial.SchwartzZippelCounting
import ArkLib.ProofSystem.ConstraintSystem.Logup.Basic
import Mathlib.Algebra.MvPolynomial.Monad

/-!
# Sampled LogUp bounds

This module proves the finite-uniform `K / q` pole bound and the multivariate
`K * ell / q` soundness bound for the LogUp rational identity. Poles are rejection events rather
than accepted values under Lean's totalized division.

## References

* [Haböck, U., *Multivariate lookups based on logarithmic derivatives*][Hab22]
-/

open scoped ENNReal
open scoped BigOperators ProbabilityTheory

namespace Logup

open MvPolynomial

/-- Reindexing a uniform event along an equivalence cannot increase its
probability when the source event maps into the target event. -/
private theorem uniform_prob_le_of_equiv {Ω Ω' : Type}
    [Fintype Ω] [Fintype Ω'] [Nonempty Ω] [Nonempty Ω']
    (e : Ω ≃ Ω') (P : Ω → Prop) (Q : Ω' → Prop)
    (hPQ : ∀ x, P x → Q (e x)) :
    Pr_{let x ←$ᵖ Ω}[P x] ≤ Pr_{let x ←$ᵖ Ω'}[Q x] := by
  classical
  rw [uniform_prob_eq_card_div, uniform_prob_eq_card_div, Fintype.card_congr e]
  apply ENNReal.div_le_div_right
  norm_cast
  apply Finset.card_le_card_of_injOn e
  · intro x hx
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, hPQ x (Finset.mem_filter.mp hx).2⟩
  · exact e.injective.injOn

/-- A pair `(beta, gamma)` is equivalent to a point of `Fq^(ell+1)`, with
gamma at coordinate zero and beta at successor coordinates. -/
def challengeEquiv (Fq : Type*) (ell : ℕ) :
    Challenge Fq ell ≃ (Fin (ell + 1) → Fq) where
  toFun c := Fin.cases c.2 c.1
  invFun x := (fun j ↦ x j.succ, x 0)
  left_inv c := by
    rcases c with ⟨β, γ⟩
    apply Prod.ext
    · funext j
      rfl
    · rfl
  right_inv x := by
    funext i
    exact Fin.cases rfl (fun _ ↦ rfl) i

section Pole

variable {Fp : Type*} {Fq : Type} [Field Fp] [Field Fq] [Fintype Fq]

/-- A uniformly sampled rational challenge hits one of the at most `K`
denominators with probability at most `K / #Fq`, for every fixed fingerprint
challenge. This is the `K / q` term in leanVM §5.3.3. -/
theorem pole_probability_le {w K ell : ℕ} (ι : Fp →+* Fq)
    (I : Fin K → ProtocolInteraction Fp w) (β : Fin ell → Fq) :
    Pr_{let γ ←$ᵖ Fq}[¬DenominatorsNonzero ι I (β, γ)] ≤
      (K : ℝ≥0∞) / Fintype.card Fq := by
  classical
  rw [uniform_prob_eq_card_div]
  apply ENNReal.div_le_div_right
  norm_cast
  let bad : Finset Fq := Finset.univ.filter fun γ ↦ ¬DenominatorsNonzero ι I (β, γ)
  let poles : Finset Fq :=
    Finset.univ.image fun k : Fin K ↦ protocolFingerprint ι β (I k)
  have hsubset : bad ⊆ poles := by
    intro γ hγ
    simp only [bad, Finset.mem_filter, Finset.mem_univ, true_and] at hγ
    simp only [DenominatorsNonzero, not_forall] at hγ
    obtain ⟨k, hk⟩ := hγ
    push Not at hk
    have hγeq : γ = protocolFingerprint ι β (I k) := sub_eq_zero.mp hk
    exact Finset.mem_image.mpr ⟨k, Finset.mem_univ k, hγeq.symm⟩
  calc
    _ = bad.card := by simp [bad]
    _ ≤ poles.card := Finset.card_le_card hsubset
    _ ≤ Finset.univ.card := Finset.card_image_le
    _ = K := Fintype.card_fin K

/-- For every fixed beta challenge, a balanced bus rejects with
probability at most `K / #Fq`; the only possible rejection is a pole. -/
theorem balanced_rejection_probability_le {p w K ell : ℕ} [CharP Fp p]
    (ι : Fp →+* Fq) (I : Fin K → ProtocolInteraction Fp w)
    (hcap : NoWrap p I) (hbalanced : CountBalanced I) (β : Fin ell → Fq) :
    Pr_{let γ ←$ᵖ Fq}[¬Accepts ι I (β, γ)] ≤
      (K : ℝ≥0∞) / Fintype.card Fq := by
  have hevent : (fun γ : Fq ↦ ¬Accepts ι I (β, γ)) =
      (fun γ : Fq ↦ ¬DenominatorsNonzero ι I (β, γ)) := by
    funext γ
    apply propext
    constructor
    · contrapose!
      exact accepts_of_countBalanced ι I hcap hbalanced (β, γ)
    · intro hpole haccepts
      exact hpole haccepts.1
  classical
  simpa only [uniform_prob_eq_card_div, hevent] using pole_probability_le ι I β

/-- A balanced bus rejects a uniformly sampled joint challenge `(beta, gamma)`
with probability at most `K / #Fq`. Averaging the fixed-beta pole bound does
not add a factor for the fingerprint challenge space. -/
theorem balanced_joint_rejection_probability_le {p w K ell : ℕ} [CharP Fp p]
    (ι : Fp →+* Fq) (I : Fin K → ProtocolInteraction Fp w)
    (hcap : NoWrap p I) (hbalanced : CountBalanced I) :
    Pr_{let c ←$ᵖ (Challenge Fq ell)}[¬Accepts ι I c] ≤
      (K : ℝ≥0∞) / Fintype.card Fq := by
  classical
  let bad : Finset (Challenge Fq ell) :=
    Finset.univ.filter fun c ↦ ¬Accepts ι I c
  let badFiber (beta : Fin ell → Fq) : Finset Fq :=
    Finset.univ.filter fun gamma ↦ ¬Accepts ι I (beta, gamma)
  have hcardF : 0 < Fintype.card Fq := Fintype.card_pos
  have hcardF_ne_zero : (Fintype.card Fq : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast hcardF.ne'
  have hcardF_ne_top : (Fintype.card Fq : ℝ≥0∞) ≠ ∞ := ENNReal.natCast_ne_top _
  have hFiber (beta : Fin ell → Fq) : (badFiber beta).card ≤ K := by
    have hprob : ((badFiber beta).card : ℝ≥0∞) / Fintype.card Fq ≤
        (K : ℝ≥0∞) / Fintype.card Fq := by
      calc
        ((badFiber beta).card : ℝ≥0∞) / Fintype.card Fq =
            Pr_{let gamma ←$ᵖ Fq}[¬Accepts ι I (beta, gamma)] := by
          simpa [badFiber] using
            (uniform_prob_eq_card_div
              (fun gamma : Fq ↦ ¬Accepts ι I (beta, gamma))).symm
        _ ≤ (K : ℝ≥0∞) / Fintype.card Fq :=
          balanced_rejection_probability_le ι I hcap hbalanced beta
    have hcount := (ENNReal.div_le_iff hcardF_ne_zero hcardF_ne_top).mp hprob
    rw [ENNReal.div_mul_cancel hcardF_ne_zero hcardF_ne_top] at hcount
    exact_mod_cast hcount
  have hbadCard : bad.card = ∑ beta, (badFiber beta).card := by
    change (Finset.univ.filter
        (fun c : Challenge Fq ell ↦ ¬Accepts ι I c)).card =
      ∑ beta : Fin ell → Fq,
        (Finset.univ.filter fun gamma : Fq ↦ ¬Accepts ι I (beta, gamma)).card
    simp_rw [Finset.card_eq_sum_ones, Finset.sum_filter]
    rw [← Finset.univ_product_univ, Finset.sum_product]
  have hbadLe : bad.card ≤ Fintype.card (Fin ell → Fq) * K := by
    rw [hbadCard]
    calc
      ∑ beta, (badFiber beta).card ≤ ∑ _beta : Fin ell → Fq, K := by
        apply Finset.sum_le_sum
        intro beta _
        exact hFiber beta
      _ = Fintype.card (Fin ell → Fq) * K := by simp
  have hmul : bad.card * Fintype.card Fq ≤
      K * Fintype.card (Challenge Fq ell) := by
    calc
      bad.card * Fintype.card Fq ≤
        (Fintype.card (Fin ell → Fq) * K) * Fintype.card Fq :=
        Nat.mul_le_mul_right (Fintype.card Fq) hbadLe
      _ = K * (Fintype.card (Fin ell → Fq) * Fintype.card Fq) := by ac_rfl
      _ = K * Fintype.card (Challenge Fq ell) := by rw [Fintype.card_prod]
  have hratio := ENNReal.div_le_div_of_mul_le hcardF Fintype.card_pos hmul
  calc
    Pr_{let c ←$ᵖ (Challenge Fq ell)}[¬Accepts ι I c] =
        (bad.card : ℝ≥0∞) / Fintype.card (Challenge Fq ell) := by
      simpa [bad] using
        uniform_prob_eq_card_div (fun c : Challenge Fq ell ↦ ¬Accepts ι I c)
    _ ≤ (K : ℝ≥0∞) / Fintype.card Fq := hratio

end Pole

section JointNumerator

variable {Fp : Type*} {Fq : Type} [Field Fp] [Field Fq]

open Classical in
/-- The distinct base-field tuples occurring in the interaction list. -/
noncomputable def tupleSupport {w K : ℕ} (I : Fin K → ProtocolInteraction Fp w) :
    Finset (Fin w → Fp) :=
  Finset.univ.image fun k ↦ (I k).sigma

open Classical in
/-- The extension-field signed multiplicity of one base-field tuple. -/
noncomputable def tupleMultiplicity {w K : ℕ} (ι : Fp →+* Fq)
    (I : Fin K → ProtocolInteraction Fp w) (σ : Fin w → Fp) : Fq :=
  ∑ k, if (I k).sigma = σ then (embeddedInteraction ι (I k)).m else 0

open Classical in
/-- The active support: the occurring tuples whose grouped signed
multiplicity is nonzero. -/
noncomputable def activeTupleSupport {w K : ℕ} (ι : Fp →+* Fq)
    (I : Fin K → ProtocolInteraction Fp w) : Finset (Fin w → Fp) :=
  (tupleSupport I).filter fun σ ↦ tupleMultiplicity ι I σ ≠ 0

/-- Fingerprint a base-field tuple after applying the explicit embedding. -/
def tupleFingerprint {w ell : ℕ} (ι : Fp →+* Fq) (β : Fin ell → Fq)
    (σ : Fin w → Fp) : Fq :=
  fingerprint (Vector.ofFn β) fun i ↦ ι (σ i)

/-- The interaction-facing and tuple-facing fingerprint definitions agree. -/
theorem protocolFingerprint_eq_tupleFingerprint {w ell : ℕ} (ι : Fp →+* Fq)
    (β : Fin ell → Fq) (x : ProtocolInteraction Fp w) :
    protocolFingerprint ι β x = tupleFingerprint ι β x.sigma := rfl

/-- The big-endian fingerprint as a polynomial in the `ell` beta variables.

Variable zero of the ambient `Fin (ell + 1)` family is reserved for gamma;
`beta_j` is variable `j.succ`. -/
noncomputable def fingerprintPolynomial {w ell : ℕ} (ι : Fp →+* Fq)
    (σ : Fin w → Fp) :
    MvPolynomial (Fin (ell + 1)) Fq :=
  ∑ i : Fin w, C (ι (σ i)) *
    ∏ j : Fin ell,
      if (bitsBE ell i)[j] then X j.succ else 1 - X j.succ

/-- Evaluating the polynomial fingerprint gives the protocol fingerprint in
big-endian bit order. -/
theorem eval_fingerprintPolynomial {w ell : ℕ} (ι : Fp →+* Fq)
    (σ : Fin w → Fp)
    (β : Fin ell → Fq) (γ : Fq) :
    eval (Fin.cases γ β) (fingerprintPolynomial ι σ) =
      fingerprint (Vector.ofFn β) (fun i ↦ ι (σ i)) := by
  classical
  unfold fingerprintPolynomial fingerprint eqTildeVector
  simp only [map_sum, map_mul, map_prod, eval_C]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  apply Finset.prod_congr rfl
  intro j _
  by_cases hbit : (bitsBE ell i.val)[j.val]
  · simp [hbit, Vector.get_eq_getElem]
  · simp [hbit, Vector.get_eq_getElem]

/-- The fingerprint polynomial has total degree at most `ell`. -/
theorem fingerprintPolynomial_totalDegree_le {w ell : ℕ} (ι : Fp →+* Fq)
    (σ : Fin w → Fp) :
    (fingerprintPolynomial (ell := ell) ι σ).totalDegree ≤ ell := by
  classical
  unfold fingerprintPolynomial
  apply MvPolynomial.totalDegree_finsetSum_le
  intro i _
  calc
    (C (ι (σ i)) *
        ∏ j : Fin ell,
          if (bitsBE ell i)[j] then X j.succ else 1 - X j.succ).totalDegree ≤
        (C (ι (σ i)) : MvPolynomial (Fin (ell + 1)) Fq).totalDegree +
          (∏ j : Fin ell,
            if (bitsBE ell i)[j] then
              (X j.succ : MvPolynomial (Fin (ell + 1)) Fq)
            else 1 - X j.succ).totalDegree :=
      MvPolynomial.totalDegree_mul _ _
    _ = (∏ j : Fin ell,
          if (bitsBE ell i)[j] then
            (X j.succ : MvPolynomial (Fin (ell + 1)) Fq)
          else 1 - X j.succ).totalDegree :=
      by simp
    _ ≤ ∑ j : Fin ell,
          (if (bitsBE ell i)[j] then X j.succ else 1 - X j.succ :
            MvPolynomial (Fin (ell + 1)) Fq).totalDegree :=
      MvPolynomial.totalDegree_finsetProd _ _
    _ ≤ ∑ _j : Fin ell, 1 := by
      apply Finset.sum_le_sum
      intro j _
      by_cases hbit : (bitsBE ell i)[j]
      · simp [hbit]
      · rw [if_neg hbit]
        exact (MvPolynomial.totalDegree_sub _ _).trans (by simp)
    _ = ell := by simp

/-- The bit vector used by `fingerprint` is the big-endian Boolean
cube point for the same index. -/
theorem bitsToField_eq_cubePoint {w ell : ℕ} (i : Fin w) (hfit : w ≤ 2 ^ ell) :
    (bitsBE ell i).map (fun b ↦ if b then (1 : Fq) else 0) =
      cubePointBE ell ⟨i, lt_of_lt_of_le i.isLt hfit⟩ := by
  apply Vector.ext
  intro j hj
  simp [bitsBE, cubePointBE]

/-- At a big-endian Boolean cube point, the fingerprint selects the
corresponding tuple coordinate. -/
theorem fingerprint_cubePoint {w ell : ℕ} (ι : Fp →+* Fq) (σ : Fin w → Fp)
    (hfit : w ≤ 2 ^ ell) (i : Fin w) :
    fingerprint (cubePointBE ell ⟨i, lt_of_lt_of_le i.isLt hfit⟩)
        (fun k ↦ ι (σ k)) = ι (σ i) := by
  classical
  unfold fingerprint
  simp_rw [bitsToField_eq_cubePoint (Fq := Fq) (hfit := hfit)]
  rw [Finset.sum_eq_single i]
  · simp [eqTildeVector_cubePointBE_delta]
  · intro j _ hji
    have hne : (⟨i, lt_of_lt_of_le i.isLt hfit⟩ : Fin (2 ^ ell)) ≠
        ⟨j, lt_of_lt_of_le j.isLt hfit⟩ := by
      intro h
      exact hji (Fin.ext (congrArg Fin.val h).symm)
    simp [eqTildeVector_cubePointBE_delta, hne]
  · simp

/-- Distinct tuples give distinct fingerprint polynomials when their indices
fit in `ell` bits. This is a polynomial identity, not an assertion that a
collision-free sampled beta exists. -/
theorem fingerprintPolynomial_ne {w ell : ℕ} (ι : Fp →+* Fq)
    (hfit : w ≤ 2 ^ ell)
    {σ τ : Fin w → Fp} (hne : σ ≠ τ) :
    fingerprintPolynomial (ell := ell) ι σ ≠ fingerprintPolynomial ι τ := by
  classical
  obtain ⟨i, hi⟩ : ∃ i, σ i ≠ τ i := by
    contrapose! hne
    exact funext hne
  intro hpoly
  have heval := congrArg
    (eval (Fin.cases 0 (cubePointBE (R := Fq) ell
      ⟨i, lt_of_lt_of_le i.isLt hfit⟩).get)) hpoly
  rw [eval_fingerprintPolynomial, eval_fingerprintPolynomial] at heval
  have hvec : Vector.ofFn (cubePointBE (R := Fq) ell
      ⟨i, lt_of_lt_of_le i.isLt hfit⟩).get =
      cubePointBE (R := Fq) ell ⟨i, lt_of_lt_of_le i.isLt hfit⟩ := by
    apply Vector.ext
    intro j hj
    change (Vector.ofFn (cubePointBE (R := Fq) ell
      ⟨i, lt_of_lt_of_le i.isLt hfit⟩).get).get ⟨j, hj⟩ =
      (cubePointBE (R := Fq) ell
        ⟨i, lt_of_lt_of_le i.isLt hfit⟩).get ⟨j, hj⟩
    simp
  rw [hvec] at heval
  rw [fingerprint_cubePoint ι σ hfit i, fingerprint_cubePoint ι τ hfit i] at heval
  exact hi (ι.injective heval)

/-- The fingerprint polynomial over exactly the `ell` sampled beta variables.
The joint numerator uses `fingerprintPolynomial`, whose extra variable zero is
reserved for gamma; this private form is used to state the standalone
collision probability over beta alone. -/
private noncomputable def betaFingerprintPolynomial {w ell : ℕ}
    (ι : Fp →+* Fq) (σ : Fin w → Fp) : MvPolynomial (Fin ell) Fq :=
  ∑ i : Fin w, C (ι (σ i)) *
    ∏ j : Fin ell,
      if (bitsBE ell i)[j] then X j else 1 - X j

/-- Evaluation of the beta-only polynomial is the protocol fingerprint. -/
private theorem eval_betaFingerprintPolynomial {w ell : ℕ}
    (ι : Fp →+* Fq) (σ : Fin w → Fp) (β : Fin ell → Fq) :
    eval β (betaFingerprintPolynomial ι σ) = tupleFingerprint ι β σ := by
  classical
  unfold betaFingerprintPolynomial tupleFingerprint fingerprint eqTildeVector
  simp only [map_sum, map_mul, map_prod, eval_C]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  apply Finset.prod_congr rfl
  intro j _
  by_cases hbit : (bitsBE ell i.val)[j.val]
  · simp [hbit, Vector.get_eq_getElem]
  · simp [hbit, Vector.get_eq_getElem]

/-- The beta-only fingerprint polynomial has total degree at most `ell`. -/
private theorem betaFingerprintPolynomial_totalDegree_le {w ell : ℕ}
    (ι : Fp →+* Fq) (σ : Fin w → Fp) :
    (betaFingerprintPolynomial (ell := ell) ι σ).totalDegree ≤ ell := by
  classical
  unfold betaFingerprintPolynomial
  apply MvPolynomial.totalDegree_finsetSum_le
  intro i _
  calc
    (C (ι (σ i)) *
        ∏ j : Fin ell,
          if (bitsBE ell i)[j] then X j else 1 - X j).totalDegree ≤
        (C (ι (σ i)) : MvPolynomial (Fin ell) Fq).totalDegree +
          (∏ j : Fin ell,
            if (bitsBE ell i)[j] then
              (X j : MvPolynomial (Fin ell) Fq)
            else 1 - X j).totalDegree :=
      MvPolynomial.totalDegree_mul _ _
    _ = (∏ j : Fin ell,
          if (bitsBE ell i)[j] then
            (X j : MvPolynomial (Fin ell) Fq)
          else 1 - X j).totalDegree := by simp
    _ ≤ ∑ j : Fin ell,
          (if (bitsBE ell i)[j] then X j else 1 - X j :
            MvPolynomial (Fin ell) Fq).totalDegree :=
      MvPolynomial.totalDegree_finsetProd _ _
    _ ≤ ∑ _j : Fin ell, 1 := by
      apply Finset.sum_le_sum
      intro j _
      by_cases hbit : (bitsBE ell i)[j]
      · simp [hbit]
      · rw [if_neg hbit]
        exact (MvPolynomial.totalDegree_sub _ _).trans (by simp)
    _ = ell := by simp

/-- Distinct tuples induce distinct beta-only fingerprint polynomials. -/
private theorem betaFingerprintPolynomial_ne {w ell : ℕ}
    (ι : Fp →+* Fq) (hfit : w ≤ 2 ^ ell)
    {σ τ : Fin w → Fp} (hne : σ ≠ τ) :
    betaFingerprintPolynomial (ell := ell) ι σ ≠ betaFingerprintPolynomial ι τ := by
  classical
  obtain ⟨i, hi⟩ : ∃ i, σ i ≠ τ i := by
    contrapose! hne
    exact funext hne
  intro hpoly
  let point := cubePointBE (R := Fq) ell
    ⟨i, lt_of_lt_of_le i.isLt hfit⟩
  have heval := congrArg (eval point.get) hpoly
  rw [eval_betaFingerprintPolynomial, eval_betaFingerprintPolynomial] at heval
  change fingerprint (Vector.ofFn point.get) (fun k ↦ ι (σ k)) =
    fingerprint (Vector.ofFn point.get) (fun k ↦ ι (τ k)) at heval
  have hpoint : Vector.ofFn point.get = point := by
    apply Vector.ext
    intro j hj
    change (Vector.ofFn point.get).get ⟨j, hj⟩ = point.get ⟨j, hj⟩
    simp
  rw [hpoint] at heval
  rw [fingerprint_cubePoint ι σ hfit i, fingerprint_cubePoint ι τ hfit i] at heval
  exact hi (ι.injective heval)

/-- For two distinct base-field tuples whose `w` coordinates fit in the
`ell`-bit bus domain, a uniformly sampled fingerprint challenge makes their
fingerprints collide with probability at most `ell / #Fq`. -/
theorem tupleFingerprint_collision_probability_le {w ell : ℕ} [Fintype Fq]
    (ι : Fp →+* Fq) (hfit : w ≤ 2 ^ ell) {σ τ : Fin w → Fp} (hne : σ ≠ τ) :
    Pr_{let β ←$ᵖ (Fin ell → Fq)}[
      tupleFingerprint ι β σ = tupleFingerprint ι β τ] ≤
      (ell : ℝ≥0∞) / Fintype.card Fq := by
  classical
  let P := betaFingerprintPolynomial (ell := ell) ι σ - betaFingerprintPolynomial ι τ
  have hP : P ≠ 0 := sub_ne_zero.mpr (betaFingerprintPolynomial_ne ι hfit hne)
  have hdegree : P.totalDegree ≤ ell := by
    apply (MvPolynomial.totalDegree_sub _ _).trans
    exact max_le (betaFingerprintPolynomial_totalDegree_le ι σ)
      (betaFingerprintPolynomial_totalDegree_le ι τ)
  rw [uniform_prob_eq_card_div]
  have hevent :
      Finset.univ.filter
          (fun β : Fin ell → Fq ↦ tupleFingerprint ι β σ = tupleFingerprint ι β τ) =
        Finset.univ.filter (fun β : Fin ell → Fq ↦ eval β P = 0) := by
    ext β
    simp [P, eval_betaFingerprintPolynomial, sub_eq_zero]
  rw [hevent]
  have hcardF : 0 < Fintype.card Fq := Fintype.card_pos
  have hcount := schwartz_zippel_counting P hP (fun _ ↦ Finset.univ) ell
    (Fintype.card Fq) hdegree hcardF (by intro i; simp)
  rw [Fintype.piFinset_univ] at hcount
  have hcardpi : Fintype.card (Fin ell → Fq) = Fintype.card Fq ^ ell := by
    simp [Fintype.card_pi]
  rw [hcardpi]
  refine ENNReal.div_le_div_of_mul_le hcardF (by positivity) ?_
  simpa [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using hcount

/-- The polynomial denominator `gamma - pi_beta(σ)`. -/
noncomputable def denominatorPolynomial {w ell : ℕ} (ι : Fp →+* Fq)
    (σ : Fin w → Fp) :
    MvPolynomial (Fin (ell + 1)) Fq :=
  X 0 - fingerprintPolynomial ι σ

/-- Evaluating a denominator polynomial gives `gamma - pi_beta(σ)`. -/
theorem eval_denominatorPolynomial {w ell : ℕ} (ι : Fp →+* Fq)
    (σ : Fin w → Fp) (β : Fin ell → Fq) (γ : Fq) :
    eval (Fin.cases γ β) (denominatorPolynomial ι σ) =
      γ - tupleFingerprint ι β σ := by
  simp [denominatorPolynomial, tupleFingerprint, eval_fingerprintPolynomial,
    MvPolynomial.eval_X]

open Classical in
/-- The joint LogUp numerator

`N(beta,gamma) = sum_sigma M(sigma) * product_{sigma' != sigma}
  (gamma - pi_beta(sigma'))`.

It is a polynomial in all fingerprint coordinates and the rational challenge.
No collision-free `beta` is assumed. -/
noncomputable def jointNumerator {w K ell : ℕ} (ι : Fp →+* Fq)
    (I : Fin K → ProtocolInteraction Fp w) : MvPolynomial (Fin (ell + 1)) Fq :=
  ∑ σ ∈ activeTupleSupport ι I,
    C (tupleMultiplicity ι I σ) *
      ∏ σ' ∈ (activeTupleSupport ι I).erase σ,
        denominatorPolynomial ι σ'

open Classical in
/-- Evaluation formula for `jointNumerator`. -/
theorem eval_jointNumerator {w K ell : ℕ} (ι : Fp →+* Fq)
    (I : Fin K → ProtocolInteraction Fp w) (β : Fin ell → Fq) (γ : Fq) :
    eval (Fin.cases γ β) (jointNumerator ι I) =
      ∑ σ ∈ activeTupleSupport ι I,
        tupleMultiplicity ι I σ *
          ∏ τ ∈ (activeTupleSupport ι I).erase σ,
            (γ - tupleFingerprint ι β τ) := by
  classical
  unfold jointNumerator
  simp only [map_sum, map_mul, map_prod, eval_C]
  apply Finset.sum_congr rfl
  intro σ _
  congr 1
  apply Finset.prod_congr rfl
  intro τ _
  exact eval_denominatorPolynomial ι τ β γ

/-- Clearing a finite family of nonzero denominators produces the standard
sum of products with one factor omitted. -/
private theorem sum_div_mul_prod_eq_sum_prod_erase {α : Type*} [DecidableEq α]
    (S : Finset α)
    (m d : α → Fq) (hd : ∀ a ∈ S, d a ≠ 0) :
    (∑ a ∈ S, m a / d a) * (∏ a ∈ S, d a) =
      ∑ a ∈ S, m a * ∏ b ∈ S.erase a, d b := by
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a ha
  calc
    m a / d a * ∏ b ∈ S, d b =
        m a / d a * (d a * ∏ b ∈ S.erase a, d b) := by
      rw [Finset.mul_prod_erase S d ha]
    _ = m a * ∏ b ∈ S.erase a, d b := by
      field_simp [hd a ha]

open Classical in
/-- Group the interaction-level rational sum by base-field tuple, discarding
the zero-multiplicity groups outside the active support. -/
theorem rationalSum_eq_activeGrouped {w K ell : ℕ} (ι : Fp →+* Fq)
    (I : Fin K → ProtocolInteraction Fp w) (β : Fin ell → Fq) (γ : Fq) :
    (∑ k, (embeddedInteraction ι (I k)).m /
        (γ - protocolFingerprint ι β (I k))) =
      ∑ σ ∈ activeTupleSupport ι I,
        tupleMultiplicity ι I σ / (γ - tupleFingerprint ι β σ) := by
  classical
  calc
    (∑ k, (embeddedInteraction ι (I k)).m /
        (γ - protocolFingerprint ι β (I k))) =
        ∑ σ ∈ tupleSupport I,
          tupleMultiplicity ι I σ / (γ - tupleFingerprint ι β σ) := by
      rw [← Finset.sum_fiberwise_of_maps_to (g := fun k ↦ (I k).sigma)
        (t := tupleSupport I)
        (by intro k _; exact Finset.mem_image_of_mem _ (Finset.mem_univ k))]
      apply Finset.sum_congr rfl
      intro σ _
      have hden : ∀ k ∈ Finset.univ.filter (fun k ↦ (I k).sigma = σ),
          (embeddedInteraction ι (I k)).m /
              (γ - protocolFingerprint ι β (I k)) =
            (embeddedInteraction ι (I k)).m /
              (γ - tupleFingerprint ι β σ) := by
        intro k hk
        rw [protocolFingerprint_eq_tupleFingerprint, (Finset.mem_filter.mp hk).2]
      rw [Finset.sum_congr rfl hden]
      simp_rw [div_eq_mul_inv]
      rw [← Finset.sum_mul]
      congr 1
      unfold tupleMultiplicity
      rw [← Finset.sum_filter]
    _ = ∑ σ ∈ activeTupleSupport ι I,
          tupleMultiplicity ι I σ / (γ - tupleFingerprint ι β σ) := by
      unfold activeTupleSupport
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro σ _
      by_cases hmult : tupleMultiplicity ι I σ = 0 <;> simp [hmult]

/-- Every accepted challenge is a root of the joint numerator. Poles are
excluded by `Accepts`, so clearing denominators is sound. -/
theorem accepts_implies_eval_jointNumerator_eq_zero {w K ell : ℕ}
    (ι : Fp →+* Fq) (I : Fin K → ProtocolInteraction Fp w)
    (β : Fin ell → Fq) (γ : Fq) (haccepts : Accepts ι I (β, γ)) :
    eval (Fin.cases γ β) (jointNumerator ι I) = 0 := by
  classical
  have hden : ∀ σ ∈ activeTupleSupport ι I,
      γ - tupleFingerprint ι β σ ≠ 0 := by
    intro σ hσ
    obtain ⟨hsupp, _⟩ := Finset.mem_filter.mp hσ
    obtain ⟨k, _, hk⟩ := Finset.mem_image.mp hsupp
    have hkden := haccepts.1 k
    rw [protocolFingerprint_eq_tupleFingerprint, hk] at hkden
    exact hkden
  have hgrouped :
      (∑ σ ∈ activeTupleSupport ι I,
          tupleMultiplicity ι I σ / (γ - tupleFingerprint ι β σ)) = 0 := by
    rw [← rationalSum_eq_activeGrouped]
    exact haccepts.2
  have hclear := sum_div_mul_prod_eq_sum_prod_erase (activeTupleSupport ι I)
    (tupleMultiplicity ι I) (fun σ ↦ γ - tupleFingerprint ι β σ) hden
  rw [hgrouped, zero_mul] at hclear
  rw [eval_jointNumerator]
  exact hclear.symm

/-- Substitute the fingerprint polynomial of `σ` for gamma while leaving all
beta variables unchanged. -/
noncomputable def substituteGamma {w ell : ℕ} (ι : Fp →+* Fq)
    (σ : Fin w → Fp) :
    Fin (ell + 1) → MvPolynomial (Fin (ell + 1)) Fq :=
  Fin.cases (fingerprintPolynomial ι σ) fun j ↦ X j.succ

/-- Gamma substitution leaves every fingerprint polynomial unchanged. -/
private theorem bind_fingerprintPolynomial {w ell : ℕ} (ι : Fp →+* Fq)
    (σ τ : Fin w → Fp) :
    bind₁ (substituteGamma (ell := ell) ι σ) (fingerprintPolynomial ι τ) =
      fingerprintPolynomial ι τ := by
  classical
  unfold substituteGamma fingerprintPolynomial
  simp only [map_sum, map_mul, map_prod, bind₁_C_right]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  apply Finset.prod_congr rfl
  intro j _
  by_cases hbit : (bitsBE ell i)[j]
  · simp [hbit, bind₁_X_right]
  · simp [hbit, bind₁_X_right]

/-- Under gamma substitution, a denominator becomes the difference of the two
fingerprint polynomials. -/
private theorem bind_denominatorPolynomial {w ell : ℕ} (ι : Fp →+* Fq)
    (σ τ : Fin w → Fp) :
    bind₁ (substituteGamma (ell := ell) ι σ) (denominatorPolynomial ι τ) =
      fingerprintPolynomial ι σ - fingerprintPolynomial ι τ := by
  simp [denominatorPolynomial, substituteGamma, bind_fingerprintPolynomial]

omit [Field Fp] in
/-- There are at most `K` distinct tuples among `K` interactions. -/
theorem tupleSupport_card_le {w K : ℕ} (I : Fin K → ProtocolInteraction Fp w) :
    (tupleSupport I).card ≤ K := by
  classical
  unfold tupleSupport
  calc
    (Finset.univ.image fun k : Fin K ↦ (I k).sigma).card ≤ Finset.univ.card :=
      Finset.card_image_le
    _ = K := Fintype.card_fin K

open Classical in
/-- The nonzero-multiplicity support also has cardinality at most `K`. -/
theorem activeTupleSupport_card_le {w K : ℕ} (ι : Fp →+* Fq)
    (I : Fin K → ProtocolInteraction Fp w) : (activeTupleSupport ι I).card ≤ K :=
  (Finset.card_filter_le _ _).trans (tupleSupport_card_le I)

/-- If `s` is the number of active tuples, the joint numerator has total degree
at most `(s - 1) * ell`. -/
theorem jointNumerator_totalDegree_le_support {w K ell : ℕ} (ι : Fp →+* Fq)
    (I : Fin K → ProtocolInteraction Fp w) (hEll : 0 < ell) :
    (jointNumerator (ell := ell) ι I).totalDegree ≤
      ((activeTupleSupport ι I).card - 1) * ell := by
  classical
  have hden : ∀ σ : Fin w → Fp,
      (denominatorPolynomial (ell := ell) ι σ).totalDegree ≤ ell := by
    intro σ
    unfold denominatorPolynomial
    refine (MvPolynomial.totalDegree_sub _ _).trans ?_
    rw [MvPolynomial.totalDegree_X]
    exact max_le (Nat.succ_le_iff.mpr hEll) (fingerprintPolynomial_totalDegree_le ι σ)
  unfold jointNumerator
  apply MvPolynomial.totalDegree_finsetSum_le
  intro σ hσ
  calc
    (C (tupleMultiplicity ι I σ) *
        ∏ σ' ∈ (activeTupleSupport ι I).erase σ,
          denominatorPolynomial (ell := ell) ι σ').totalDegree ≤
        (C (tupleMultiplicity ι I σ) : MvPolynomial (Fin (ell + 1)) Fq).totalDegree +
          (∏ σ' ∈ (activeTupleSupport ι I).erase σ,
            denominatorPolynomial (ell := ell) ι σ').totalDegree :=
      MvPolynomial.totalDegree_mul _ _
    _ ≤ ∑ σ' ∈ (activeTupleSupport ι I).erase σ,
          (denominatorPolynomial (ell := ell) ι σ').totalDegree := by
      simpa only [MvPolynomial.totalDegree_C, zero_add] using
        (MvPolynomial.totalDegree_finsetProd ((activeTupleSupport ι I).erase σ)
          (fun σ' ↦ denominatorPolynomial (ell := ell) ι σ'))
    _ ≤ ∑ _σ' ∈ (activeTupleSupport ι I).erase σ, ell := by
      apply Finset.sum_le_sum
      intro σ' _
      exact hden σ'
    _ = ((activeTupleSupport ι I).erase σ).card * ell := by simp
    _ = ((activeTupleSupport ι I).card - 1) * ell := by
      rw [Finset.card_erase_of_mem hσ]

/-- Since the active support has at most `K` elements, the joint numerator has
total degree at most `K * ell`. -/
theorem jointNumerator_totalDegree_le {w K ell : ℕ} (ι : Fp →+* Fq)
    (I : Fin K → ProtocolInteraction Fp w) (hEll : 0 < ell) :
    (jointNumerator (ell := ell) ι I).totalDegree ≤ K * ell :=
  (jointNumerator_totalDegree_le_support ι I hEll).trans <| by
    gcongr
    exact (Nat.sub_le _ _).trans (activeTupleSupport_card_le ι I)

open Classical in
/-- If one tuple belongs to the active support, then the joint numerator is nonzero. -/
theorem jointNumerator_ne_zero_of_mem {w K ell : ℕ} (ι : Fp →+* Fq)
    (I : Fin K → ProtocolInteraction Fp w) (hfit : w ≤ 2 ^ ell)
    {σ : Fin w → Fp} (hσ : σ ∈ activeTupleSupport ι I) :
    jointNumerator (ell := ell) ι I ≠ 0 := by
  classical
  have hmult : tupleMultiplicity ι I σ ≠ 0 :=
    (Finset.mem_filter.mp hσ).2
  let subst := substituteGamma (ell := ell) ι σ
  have hisolate :
      bind₁ subst (jointNumerator (ell := ell) ι I) =
        C (tupleMultiplicity ι I σ) *
          ∏ τ ∈ (activeTupleSupport ι I).erase σ,
            (fingerprintPolynomial (ell := ell) ι σ - fingerprintPolynomial ι τ) := by
    unfold jointNumerator
    simp only [map_sum, map_mul, map_prod, bind₁_C_right]
    rw [Finset.sum_eq_single σ]
    · apply congrArg (C (tupleMultiplicity ι I σ) * ·)
      apply Finset.prod_congr rfl
      intro τ _
      exact bind_denominatorPolynomial ι σ τ
    · intro τ hτ hτσ
      have hστ : σ ∈ (activeTupleSupport ι I).erase τ :=
        Finset.mem_erase.mpr ⟨fun h ↦ hτσ h.symm, hσ⟩
      have hzero :
          ∏ υ ∈ (activeTupleSupport ι I).erase τ,
              bind₁ subst (denominatorPolynomial ι υ) = 0 :=
        Finset.prod_eq_zero hστ (by
          rw [bind_denominatorPolynomial]
          exact sub_self _)
      rw [hzero, mul_zero]
    · exact fun h ↦ (h hσ).elim
  have hprod :
      (∏ τ ∈ (activeTupleSupport ι I).erase σ,
          (fingerprintPolynomial (ell := ell) ι σ - fingerprintPolynomial ι τ)) ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]
    intro τ hτ
    have hτσ : τ ≠ σ := (Finset.mem_erase.mp hτ).1
    exact sub_ne_zero.mpr (fingerprintPolynomial_ne ι hfit hτσ.symm)
  intro hzero
  have hmap := congrArg (bind₁ subst) hzero
  rw [map_zero, hisolate] at hmap
  exact (mul_ne_zero (by simpa using hmult) hprod) hmap

/-- The grouped extension-field multiplicity is the embedded difference of the
actual per-tuple push and pull totals. -/
theorem tupleMultiplicity_eq_map_cast_sub {w K : ℕ} (ι : Fp →+* Fq)
    (I : Fin K → ProtocolInteraction Fp w) (σ : Fin w → Fp) :
    tupleMultiplicity ι I σ =
      ι ((pushTotal I σ : Fp) - (pullTotal I σ : Fp)) := by
  classical
  calc
    tupleMultiplicity ι I σ =
        ι (∑ k, if (toBaseInteraction (I k)).sigma = σ then
          (toBaseInteraction (I k)).m else 0) := by
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro k _
      by_cases hk : (I k).sigma = σ <;> simp [embeddedInteraction,
        mapInteraction, toBaseInteraction, hk]
    _ = ι ((pushTotal I σ : Fp) - (pullTotal I σ : Fp)) := by
      rw [groupedMultiplicity_eq_cast_sub]

/-- Under the no-wrap condition, an unbalanced bus gives a
nonzero joint numerator. -/
theorem jointNumerator_ne_zero_of_not_countBalanced {p w K ell : ℕ} [CharP Fp p]
    (ι : Fp →+* Fq) (I : Fin K → ProtocolInteraction Fp w)
    (hfit : w ≤ 2 ^ ell) (hcap : NoWrap p I) (hunbalanced : ¬CountBalanced I) :
    jointNumerator (ell := ell) ι I ≠ 0 := by
  classical
  unfold CountBalanced at hunbalanced
  push Not at hunbalanced
  obtain ⟨σ, hcounts⟩ := hunbalanced
  have hcast : (pushTotal I σ : Fp) ≠ (pullTotal I σ : Fp) := by
    intro h
    exact hcounts (CharP.natCast_injOn_Iio Fp p (hcap σ).1 (hcap σ).2 h)
  have hmult : tupleMultiplicity ι I σ ≠ 0 := by
    rw [tupleMultiplicity_eq_map_cast_sub]
    intro hzero
    apply sub_ne_zero.mpr hcast
    apply ι.injective
    simpa using hzero
  have hsupp : σ ∈ tupleSupport I := by
    by_contra hσ
    have hall : ∀ k, (I k).sigma ≠ σ := by
      intro k hk
      apply hσ
      exact Finset.mem_image.mpr ⟨k, Finset.mem_univ k, hk⟩
    apply hmult
    unfold tupleMultiplicity
    simp [hall]
  exact jointNumerator_ne_zero_of_mem ι I hfit
    (Finset.mem_filter.mpr ⟨hsupp, hmult⟩)

end JointNumerator

section SampledSoundness

variable {Fp : Type*} {Fq : Type} [Field Fp] [Field Fq]

/-- If the per-tuple counts are unbalanced, satisfy `NoWrap`, and the `w` tuple
coordinates fit in `ell` bits, then a uniform
joint challenge `(beta, gamma)` is accepted with probability at most
`K * ell / #Fq`. No collision-free sampled `beta` is assumed. -/
theorem unbalanced_acceptance_probability_le {p w K ell : ℕ} [CharP Fp p]
    [Fintype Fq] (ι : Fp →+* Fq) (I : Fin K → ProtocolInteraction Fp w)
    (hfit : w ≤ 2 ^ ell) (hEll : 0 < ell) (hcap : NoWrap p I)
    (hunbalanced : ¬CountBalanced I) :
    Pr_{let c ←$ᵖ (Challenge Fq ell)}[Accepts ι I c] ≤
      (K * ell : ℝ≥0∞) / Fintype.card Fq := by
  classical
  let P := jointNumerator (ell := ell) ι I
  have hP : P ≠ 0 := jointNumerator_ne_zero_of_not_countBalanced
    ι I hfit hcap hunbalanced
  have hdegree : P.totalDegree ≤ K * ell := jointNumerator_totalDegree_le ι I hEll
  have hsz := prob_eval_zero_uniform_le_div P hP (K * ell) hdegree
  refine (uniform_prob_le_of_equiv (challengeEquiv Fq ell)
    (fun c : Challenge Fq ell ↦ Accepts ι I c)
    (fun x : Fin (ell + 1) → Fq ↦ eval x P = 0) ?_).trans ?_
  · rintro ⟨β, γ⟩ haccepts
    exact accepts_implies_eval_jointNumerator_eq_zero ι I β γ haccepts
  · simpa using hsz

end SampledSoundness

end Logup

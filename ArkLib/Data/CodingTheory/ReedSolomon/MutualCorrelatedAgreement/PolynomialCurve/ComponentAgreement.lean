/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.PolynomialCurve.ComponentRecognition
/-!
# Common agreements of polynomial-graph components

An agreement cut containing a positive-dimensional regular component cannot be merely
accidental. Its discrepancy polynomial vanishes at infinitely many retained challenges,
so every constituent agrees. Thus `L` containing cuts give `L` common agreements, with no
restriction on the characteristic relative to the batching degree.

## References

* [Dao, Kominers, Thaler, and Zheng, *Reed--Solomon List Decoding and Mutual Correlated Agreement
  up to Capacity*][DKTZ26], Section 5.6 (Theorem 5.14), common and accidental agreements
  on polynomial graphs.
-/

@[expose] public section

noncomputable section

namespace ReedSolomon

open Polynomial MvPolynomial PolynomialDifferential HiddenDerivative AffineHilbert

variable {F E : Type*} [Field F] [Field E] {n k K r ℓ : ℕ}

/-- A regular received-curve cut records evaluation of the reconstructed message. -/
theorem symbolicSourceCurveAgreement_eq_zero_iff_of_exponent
    (center : E) (Q : DifferentialPolynomial E[X] r) (K τ : ℕ)
    (hτ : TaylorExponentSufficient r K τ)
    (x : Option (Fin (r + 1)) → E)
    (hs : aeval x (symbolicSourceSeparant center Q) ≠ 0)
    (alpha : E) (w : Fin (ℓ + 1) → E) :
    aeval x (symbolicSourceCurveAgreement_of_exponent center Q K τ alpha w) = 0 ↔
      (rationalTaylorPolynomial center (MvPolynomial.map (Polynomial.evalRingHom (x none)) Q)
        K (fun j ↦ x (some j))).eval alpha = ∑ t, x none ^ t.val * w t := by
  let φ : E[X] →ₐ[E] E := Polynomial.aeval (x none)
  have hφ : φ.toRingHom = Polynomial.evalRingHom (x none) := by ext a <;> simp [φ]
  have hs' : aeval (fun j ↦ x (some j))
      (MvPolynomial.map φ.toRingHom (initialJetSeparantOver (Polynomial.C center) Q)) ≠ 0 := by
    simpa only [symbolicSourceSeparant, aeval_optionEquivRight_symm, hφ] using hs
  rw [symbolicSourceCurveAgreement_of_exponent, aeval_optionEquivRight_symm]
  have hiff := aeval_map_taylorAgreementEquationOver_eq_zero_iff_of_exponent φ
    (Polynomial.C center) Q K τ hτ (fun j ↦ x (some j)) hs'
      (Polynomial.C alpha) (powerBatchedCoordinate w)
  simpa only [hφ, φ, Polynomial.aeval_def, Algebra.algebraMap_self,
    Polynomial.eval₂_id, Polynomial.eval_C, powerBatchedCoordinate_eval] using hiff

/-- Containing an agreement cut forces agreement of every constituent of a recognized
polynomial graph. The proof uses infinitely many parameter values, not evaluations at
a fixed collection of field elements. -/
theorem commonAgreement_of_curveCut_mem_prime_of_exponent [IsAlgClosed E]
    (domain : Fin n ↪ F) (w : Fin (ℓ + 1) → Fin n → F) (ι : F →+* E)
    (center : E) (Q : DifferentialPolynomial E[X] r) (K τ : ℕ)
    (hτ : TaylorExponentSufficient r K τ)
    (I : Ideal (MvPolynomial (Option (Fin (r + 1))) E)) (hI : I.IsPrime)
    (hs : symbolicSourceSeparant center Q ∉ I)
    (hd : 0 < (hilbertPolynomial I).natDegree) (P : Fin (ℓ + 1) → F[X])
    (hgraph : ∀ x ∈ principalOpenZeroLocus I (symbolicSourceSeparant center Q),
      x = polynomialGraphPoint
        (powerBatchedJetGraph (r := r) center (fun t ↦ (P t).map ι)) (x none))
    (hpoly : ∀ x ∈ principalOpenZeroLocus I (symbolicSourceSeparant center Q),
      rationalTaylorPolynomial center (MvPolynomial.map (Polynomial.evalRingHom (x none)) Q)
        K (fun j ↦ x (some j)) = powerBatchedPolynomial (fun t ↦ (P t).map ι) (x none))
    (i : Fin n)
    (hcut : symbolicSourceCurveAgreement_of_exponent center Q K τ
      (ι (domain i)) (fun t ↦ ι (w t i)) ∈ I) :
    ∀ t, (P t).eval (domain i) = w t i := by
  have hinfinite : (principalOpenZeroLocus I (symbolicSourceSeparant center Q)).Infinite := by
    intro hfinite
    have hz := hilbertPolynomial_natDegree_zero_of_finite_principalOpen hI hs hfinite
    omega
  have hinj : Set.InjOn (fun x : Option (Fin (r + 1)) → E ↦ x none)
      (principalOpenZeroLocus I (symbolicSourceSeparant center Q)) := by
    intro x hx y hy hxy
    change x none = y none at hxy
    rw [hgraph x hx, hgraph y hy, hxy]
  let mismatch := curveDiscrepancy (mappedDomain domain ι)
    (fun t i ↦ ι (w t i)) (fun t ↦ (P t).map ι) i
  have hzero : mismatch = 0 := by
    apply Polynomial.eq_zero_of_infinite_isRoot
    apply (hinfinite.image hinj).mono
    rintro z ⟨x, hx, rfl⟩
    have heval := (symbolicSourceCurveAgreement_eq_zero_iff_of_exponent
      center Q K τ hτ x hx.2 (ι (domain i)) (fun t ↦ ι (w t i))).mp (hx.1 _ hcut)
    rw [hpoly x hx] at heval
    change mismatch.eval (x none) = 0
    rw [curveDiscrepancy_eval]
    exact sub_eq_zero.mpr heval
  have hcommon := (curveDiscrepancy_eq_zero_iff _ _ _ i).mp hzero
  intro t
  apply ι.injective
  simpa only [mappedDomain, Function.Embedding.trans_apply, Function.Embedding.coeFn_mk,
    Polynomial.eval_map, Polynomial.eval₂_at_apply] using hcommon t

/-- Any `L` agreement cuts containing a regular positive-dimensional component yield one
tuple with at least `L` common agreements. Only `k ≤ L` is required; we do not replace `L`
by the full block length. All equations of the component restrict to zero on its graph. -/
theorem exists_polynomialGraph_of_symbolic_prime_agreements_of_exponent
    [IsAlgClosed E] {L : ℕ}
    (domain : Fin n ↪ F) (w : Fin (ℓ + 1) → Fin n → F)
    (indices : Finset (Fin n)) (hcard : indices.card = L) (hkL : k ≤ L)
    (ι : F →+* E) (center : E) (Q : DifferentialPolynomial E[X] r)
    (hK : r < K) (τ : ℕ) (hτ : TaylorExponentSufficient r K τ)
    (I : Ideal (MvPolynomial (Option (Fin (r + 1))) E)) (hI : I.IsPrime)
    (hs : symbolicSourceSeparant center Q ∉ I)
    (hd : 0 < (hilbertPolynomial I).natDegree)
    (hhigh : ∀ l : Fin K, k ≤ l.val → symbolicSourceNumerator center Q K l (τ := τ) ∈ I)
    (hcuts : ∀ i ∈ indices,
      symbolicSourceCurveAgreement_of_exponent center Q K τ
        (ι (domain i)) (fun t ↦ ι (w t i)) ∈ I) :
    ∃ P : Fin (ℓ + 1) → F[X], (∀ t, (P t).degree < k) ∧
      L ≤ (commonCurveAgreementSet domain w P).card ∧
      (∀ x ∈ principalOpenZeroLocus I (symbolicSourceSeparant center Q),
        x = polynomialGraphPoint
          (powerBatchedJetGraph (r := r) center (fun t ↦ (P t).map ι)) (x none)) ∧
      (∀ x ∈ principalOpenZeroLocus I (symbolicSourceSeparant center Q),
        rationalTaylorPolynomial center (MvPolynomial.map (Polynomial.evalRingHom (x none)) Q)
          K (fun j ↦ x (some j)) = powerBatchedPolynomial (fun t ↦ (P t).map ι) (x none)) ∧
      (∀ p ∈ I, polynomialGraphPullback
        (powerBatchedJetGraph (r := r) center (fun t ↦ (P t).map ι)) p = 0) ∧
      polynomialGraphPullback
        (powerBatchedJetGraph (r := r) center (fun t ↦ (P t).map ι))
        (symbolicSourceSeparant center Q) ≠ 0 := by
  classical
  obtain ⟨sample, hsub, hsample⟩ := Finset.exists_subset_card_eq (hcard ▸ hkL)
  obtain ⟨P, hP, _hsampleP, hgraph, hpoly, hvanish, hsep⟩ :=
    exists_polynomialGraph_of_symbolic_prime_sample_of_exponent domain w sample hsample
      ι center Q hK τ hτ I hI hs hd hhigh (fun i hi ↦ hcuts i (hsub hi))
  refine ⟨P, hP, ?_, hgraph, hpoly, hvanish, hsep⟩
  rw [← hcard]
  apply Finset.card_le_card
  intro i hi
  simp only [commonCurveAgreementSet, Finset.mem_filter, Finset.mem_univ, true_and]
  exact commonAgreement_of_curveCut_mem_prime_of_exponent domain w ι center Q K τ hτ
    I hI hs hd P hgraph hpoly i (hcuts i hi)


end ReedSolomon

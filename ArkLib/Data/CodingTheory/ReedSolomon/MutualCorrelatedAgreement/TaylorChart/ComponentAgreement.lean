/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.TaylorChart.ComponentRecognition
/-!
# Common agreements of symbolic source components

An agreement cut containing a positive-dimensional regular source component gives a common
agreement of its recognized pair. Infinitely many source challenges eliminate accidental
agreements. Thus any prescribed number of containing cuts gives that many common agreements.
-/

@[expose] public section

open PolynomialDifferential


noncomputable section

namespace ReedSolomon

open Polynomial MvPolynomial HiddenDerivative AffineHilbert

variable {F E : Type*} [Field F] [Field E] {n k K r : ℕ}

/-- Exponent-aware regular source agreement identity. -/
theorem symbolicSourceAgreement_eq_zero_iff_of_exponent
    (center : E) (Q : DifferentialPolynomial E[X] r) (K τ : ℕ)
    (hτ : TaylorExponentSufficient r K τ)
    (x : Option (Fin (r + 1)) → E)
    (hs : aeval x (symbolicSourceSeparant center Q) ≠ 0) (alpha f g : E) :
    aeval x (symbolicSourceAgreement center Q K alpha f g (τ := τ)) = 0 ↔
      (rationalTaylorPolynomial center (MvPolynomial.map (Polynomial.evalRingHom (x none)) Q)
        K (fun j ↦ x (some j))).eval alpha = f + x none * g := by
  let φ : E[X] →ₐ[E] E := Polynomial.aeval (x none)
  have hφ : φ.toRingHom = Polynomial.evalRingHom (x none) := by
    ext a <;> simp [φ]
  have hs' : aeval (fun j ↦ x (some j))
      (MvPolynomial.map φ.toRingHom (initialJetSeparantOver (Polynomial.C center) Q)) ≠ 0 := by
    simpa only [symbolicSourceSeparant, aeval_optionEquivRight_symm, hφ] using hs
  rw [symbolicSourceAgreement, aeval_optionEquivRight_symm]
  have hiff := aeval_map_taylorAgreementEquationOver_eq_zero_iff_of_exponent φ
    (Polynomial.C center) Q K τ hτ (fun j ↦ x (some j)) hs' (Polynomial.C alpha)
    (Polynomial.C f + Polynomial.X * Polynomial.C g)
  simpa only [hφ, φ, map_add, map_mul, Polynomial.aeval_C, Polynomial.aeval_X,
    Algebra.algebraMap_self, RingHom.id_apply] using hiff

/-- A regular source agreement cut records the actual reconstructed received value. -/
theorem symbolicSourceAgreement_eq_zero_iff
    (center : E) (Q : DifferentialPolynomial E[X] r) (K : ℕ)
    (x : Option (Fin (r + 1)) → E)
    (hs : aeval x (symbolicSourceSeparant center Q) ≠ 0) (alpha f g : E) :
    aeval x (symbolicSourceAgreement center Q K alpha f g) = 0 ↔
      (rationalTaylorPolynomial center (MvPolynomial.map (Polynomial.evalRingHom (x none)) Q)
        K (fun j ↦ x (some j))).eval alpha = f + x none * g := by
  let φ : E[X] →ₐ[E] E := Polynomial.aeval (x none)
  have hφ : φ.toRingHom = Polynomial.evalRingHom (x none) := by
    ext a <;> simp [φ]
  have hs' : aeval (fun j ↦ x (some j))
      (MvPolynomial.map φ.toRingHom (initialJetSeparantOver (Polynomial.C center) Q)) ≠ 0 := by
    simpa only [symbolicSourceSeparant, aeval_optionEquivRight_symm, hφ] using hs
  rw [symbolicSourceAgreement, aeval_optionEquivRight_symm]
  have hiff := aeval_map_taylorAgreementEquationOver_eq_zero_iff φ (Polynomial.C center)
    Q K (fun j ↦ x (some j)) hs' (Polynomial.C alpha)
    (Polynomial.C f + Polynomial.X * Polynomial.C g)
  simpa only [hφ, φ, map_add, map_mul, Polynomial.aeval_C, Polynomial.aeval_X,
    Algebra.algebraMap_self, RingHom.id_apply] using hiff

/-- Exponent-aware common-agreement extraction from a recognized source graph. -/
theorem commonAgreement_of_symbolicSourceAgreement_mem_prime_of_exponent
    [IsAlgClosed E] (domain : Fin n ↪ F) (f g : Fin n → F) (iota : F →+* E)
    (center : E) (Q : DifferentialPolynomial E[X] r) (K τ : ℕ)
    (hτ : TaylorExponentSufficient r K τ)
    (P : Ideal (MvPolynomial (Option (Fin (r + 1))) E))
    (hP : P.IsPrime) (hs : symbolicSourceSeparant center Q ∉ P)
    (hd : 0 < (hilbertPolynomial P).natDegree) (P₀ P₁ : F[X])
    (hgraph : ∀ x ∈ principalOpenZeroLocus P (symbolicSourceSeparant center Q),
      x = affineGraphPoint (polynomialJet (d := r) center (P₀.map iota))
        (polynomialJet (d := r) center (P₁.map iota)) (x none))
    (hpoly : ∀ x ∈ principalOpenZeroLocus P (symbolicSourceSeparant center Q),
      rationalTaylorPolynomial center (MvPolynomial.map (Polynomial.evalRingHom (x none)) Q)
        K (fun j ↦ x (some j)) = P₀.map iota + Polynomial.C (x none) * P₁.map iota)
    (i : Fin n)
    (hcut : symbolicSourceAgreement center Q K (iota (domain i)) (iota (f i))
      (iota (g i)) (τ := τ) ∈ P) :
    P₀.eval (domain i) = f i ∧ P₁.eval (domain i) = g i := by
  have hinfinite : (principalOpenZeroLocus P (symbolicSourceSeparant center Q)).Infinite := by
    intro hfinite
    have hz := hilbertPolynomial_natDegree_zero_of_finite_principalOpen hP hs hfinite
    omega
  have hinj : Set.InjOn (fun x : Option (Fin (r + 1)) → E ↦ x none)
      (principalOpenZeroLocus P (symbolicSourceSeparant center Q)) := by
    intro x hx y hy hxy
    change x none = y none at hxy
    rw [hgraph x hx, hgraph y hy, hxy]
  let mismatch : E[X] := Polynomial.C (iota (P₀.eval (domain i)) - iota (f i)) +
    Polynomial.X * Polynomial.C (iota (P₁.eval (domain i)) - iota (g i))
  have hzero : mismatch = 0 := by
    apply Polynomial.eq_zero_of_infinite_isRoot
    apply (hinfinite.image hinj).mono
    rintro z ⟨x, hx, rfl⟩
    have heval := (symbolicSourceAgreement_eq_zero_iff_of_exponent center Q K τ hτ x hx.2
      (iota (domain i)) (iota (f i)) (iota (g i))).mp (hx.1 _ hcut)
    rw [hpoly x hx] at heval
    have heval' : iota (P₀.eval (domain i)) + x none * iota (P₁.eval (domain i)) =
        iota (f i) + x none * iota (g i) := by
      simpa only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
        Polynomial.eval_map, Polynomial.eval₂_at_apply] using heval
    change mismatch.eval (x none) = 0
    simp only [mismatch, Polynomial.eval_add, Polynomial.eval_C,
      Polynomial.eval_mul, Polynomial.eval_X]
    linear_combination heval'
  have hconst := congrArg (fun R : E[X] ↦ R.eval 0) hzero
  have hone := congrArg (fun R : E[X] ↦ R.eval 1) hzero
  simp only [mismatch, Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_mul,
    Polynomial.eval_X, zero_mul, add_zero, Polynomial.eval_zero] at hconst
  simp only [mismatch, Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_mul,
    Polynomial.eval_X, one_mul, Polynomial.eval_zero] at hone
  refine ⟨iota.injective (sub_eq_zero.mp hconst), ?_⟩
  rw [hconst, zero_add] at hone
  exact iota.injective (sub_eq_zero.mp hone)

/-- If the reconstructed polynomial is a fixed affine pair on a positive-dimensional
regular source component, every agreement cut in its ideal is a common agreement. -/
theorem commonAgreement_of_symbolicSourceAgreement_mem_prime
    [IsAlgClosed E] (domain : Fin n ↪ F) (f g : Fin n → F) (iota : F →+* E)
    (center : E) (Q : DifferentialPolynomial E[X] r) (K : ℕ)
    (P : Ideal (MvPolynomial (Option (Fin (r + 1))) E))
    (hP : P.IsPrime) (hs : symbolicSourceSeparant center Q ∉ P)
    (hd : 0 < (hilbertPolynomial P).natDegree) (P₀ P₁ : F[X])
    (hgraph : ∀ x ∈ principalOpenZeroLocus P (symbolicSourceSeparant center Q),
      x = affineGraphPoint (polynomialJet (d := r) center (P₀.map iota))
        (polynomialJet (d := r) center (P₁.map iota)) (x none))
    (hpoly : ∀ x ∈ principalOpenZeroLocus P (symbolicSourceSeparant center Q),
      rationalTaylorPolynomial center (MvPolynomial.map (Polynomial.evalRingHom (x none)) Q)
        K (fun j ↦ x (some j)) = P₀.map iota + Polynomial.C (x none) * P₁.map iota)
    (i : Fin n)
    (hcut : symbolicSourceAgreement center Q K (iota (domain i)) (iota (f i)) (iota (g i)) ∈ P) :
    P₀.eval (domain i) = f i ∧ P₁.eval (domain i) = g i := by
  have hinfinite : (principalOpenZeroLocus P (symbolicSourceSeparant center Q)).Infinite := by
    intro hfinite
    have hz := hilbertPolynomial_natDegree_zero_of_finite_principalOpen hP hs hfinite
    omega
  have hinj : Set.InjOn (fun x : Option (Fin (r + 1)) → E ↦ x none)
      (principalOpenZeroLocus P (symbolicSourceSeparant center Q)) := by
    intro x hx y hy hxy
    change x none = y none at hxy
    rw [hgraph x hx, hgraph y hy, hxy]
  let mismatch : E[X] := Polynomial.C (iota (P₀.eval (domain i)) - iota (f i)) +
    Polynomial.X * Polynomial.C (iota (P₁.eval (domain i)) - iota (g i))
  have hzero : mismatch = 0 := by
    apply Polynomial.eq_zero_of_infinite_isRoot
    apply (hinfinite.image hinj).mono
    rintro z ⟨x, hx, rfl⟩
    have heval := (symbolicSourceAgreement_eq_zero_iff center Q K x hx.2
      (iota (domain i)) (iota (f i)) (iota (g i))).mp (hx.1 _ hcut)
    rw [hpoly x hx] at heval
    have heval' : iota (P₀.eval (domain i)) + x none * iota (P₁.eval (domain i)) =
        iota (f i) + x none * iota (g i) := by
      simpa only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
        Polynomial.eval_map, Polynomial.eval₂_at_apply] using heval
    change mismatch.eval (x none) = 0
    simp only [mismatch, Polynomial.eval_add, Polynomial.eval_C,
      Polynomial.eval_mul, Polynomial.eval_X]
    linear_combination heval'
  have hconst := congrArg (fun R : E[X] ↦ R.eval 0) hzero
  have hone := congrArg (fun R : E[X] ↦ R.eval 1) hzero
  simp only [mismatch, Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_mul,
    Polynomial.eval_X, zero_mul, add_zero, Polynomial.eval_zero] at hconst
  simp only [mismatch, Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_mul,
    Polynomial.eval_X, one_mul, Polynomial.eval_zero] at hone
  refine ⟨iota.injective (sub_eq_zero.mp hconst), ?_⟩
  rw [hconst, zero_add] at hone
  exact iota.injective (sub_eq_zero.mp hone)

/-- Exponent-aware extraction of a common base-field pair from a positive-dimensional
regular component supported on an arbitrary threshold of agreement cuts. -/
theorem exists_graphLine_pair_of_symbolic_prime_agreements_of_exponent
    [IsAlgClosed E] [DecidableEq F] {L : ℕ} (domain : Fin n ↪ F) (f g : Fin n → F)
    (indices : Finset (Fin n)) (hcard : indices.card = L) (hkL : k ≤ L)
    (iota : F →+* E) (center : E) (Q : DifferentialPolynomial E[X] r)
    (hK : r < K) (τ : ℕ) (hτ : TaylorExponentSufficient r K τ)
    (P : Ideal (MvPolynomial (Option (Fin (r + 1))) E))
    (hP : P.IsPrime) (hs : symbolicSourceSeparant center Q ∉ P)
    (hd : 0 < (hilbertPolynomial P).natDegree)
    (hinit : symbolicSourceInitialEquation center Q ∈ P)
    (hhigh : ∀ l : Fin K, k ≤ l.val → symbolicSourceNumerator center Q K l (τ := τ) ∈ P)
    (hcuts : ∀ i ∈ indices,
      symbolicSourceAgreement center Q K (iota (domain i)) (iota (f i)) (iota (g i)) (τ := τ) ∈ P) :
    ∃ P₀ P₁ : F[X], P₀.degree < k ∧ P₁.degree < k ∧
      L ≤ (commonPolynomialAgreementSet domain f g P₀ P₁).card ∧
      (∀ x ∈ principalOpenZeroLocus P (symbolicSourceSeparant center Q),
        x = affineGraphPoint (polynomialJet (d := r) center (P₀.map iota))
          (polynomialJet (d := r) center (P₁.map iota)) (x none)) ∧
      (∀ p ∈ P,
        affineGraphPullback (polynomialJet (d := r) center (P₀.map iota))
          (polynomialJet (d := r) center (P₁.map iota)) p = 0) ∧
      affineGraphPullback (polynomialJet (d := r) center (P₀.map iota))
        (polynomialJet (d := r) center (P₁.map iota))
        (symbolicSourceInitialEquation center Q) = 0 ∧
      (∀ l : Fin K, k ≤ l.val →
        affineGraphPullback (polynomialJet (d := r) center (P₀.map iota))
          (polynomialJet (d := r) center (P₁.map iota))
          (symbolicSourceNumerator center Q K l (τ := τ)) = 0) ∧
      affineGraphPullback (polynomialJet (d := r) center (P₀.map iota))
        (polynomialJet (d := r) center (P₁.map iota)) (symbolicSourceSeparant center Q) ≠ 0 ∧
      ∀ l : Fin K,
        affineGraphPullback (polynomialJet (d := r) center (P₀.map iota))
          (polynomialJet (d := r) center (P₁.map iota))
          (symbolicSourceReconstructionError center Q K (P₀.map iota) (P₁.map iota) l
            (τ := τ)) = 0 := by
  classical
  obtain ⟨sample, hsub, hsample⟩ := Finset.exists_subset_card_eq (hcard ▸ hkL)
  obtain ⟨P₀, P₁, hP₀, hP₁, hsamplePair, hgraph, hvanish, hinitPair,
      hhighPair, hregularPair, hreconstruction⟩ :=
    exists_graphLine_pair_of_symbolic_prime_sample_of_exponent domain f g sample hsample
      iota center Q hK τ hτ P hP hs hd hinit hhigh (fun i hi ↦ hcuts i (hsub hi))
  have hpoly : ∀ x ∈ principalOpenZeroLocus P (symbolicSourceSeparant center Q),
      rationalTaylorPolynomial center (MvPolynomial.map (Polynomial.evalRingHom (x none)) Q)
        K (fun j ↦ x (some j)) = P₀.map iota + Polynomial.C (x none) * P₁.map iota := by
    intro x hx
    let φ : E[X] →ₐ[E] E := Polynomial.aeval (x none)
    have hφ : φ.toRingHom = Polynomial.evalRingHom (x none) := by
      ext a <;> simp [φ]
    have hS : aeval (fun j ↦ x (some j))
        (MvPolynomial.map φ.toRingHom (initialJetSeparantOver (Polynomial.C center) Q)) ≠ 0 := by
      simpa only [symbolicSourceSeparant, aeval_optionEquivRight_symm, hφ] using hx.2
    have hdegree := degree_rationalTaylorPolynomial_lt_of_symbolic_high_cuts_and_exponent
      φ (Polynomial.C center) Q K k τ hτ (fun j ↦ x (some j)) hS
      (fun l hl ↦ by
        have hz := hx.1 _ (hhigh l hl)
        simpa only [symbolicSourceNumerator, aeval_optionEquivRight_symm, hφ] using hz)
    have hcenter : φ (Polynomial.C center) = center := by simp [φ]
    rw [hcenter, hφ] at hdegree
    have hpairdegree : (P₀.map iota + Polynomial.C (x none) * P₁.map iota).degree < k := by
      apply (Polynomial.degree_add_le _ _).trans_lt
      apply max_lt (Polynomial.degree_map_le.trans_lt hP₀)
      rw [← Polynomial.smul_eq_C_mul]
      exact (Polynomial.degree_smul_le _ _).trans_lt (Polynomial.degree_map_le.trans_lt hP₁)
    apply Polynomial.eq_of_degrees_lt_of_eval_index_eq sample
      (mappedDomain domain iota).injective.injOn
    · simpa only [hsample] using hdegree
    · simpa only [hsample] using hpairdegree
    · intro i hi
      have heval := (symbolicSourceAgreement_eq_zero_iff_of_exponent center Q K τ hτ x hx.2
        (iota (domain i)) (iota (f i)) (iota (g i))).mp (hx.1 _ (hcuts i (hsub hi)))
      simpa only [mappedDomain, Function.Embedding.trans_apply, Function.Embedding.coeFn_mk,
        Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
        Polynomial.eval_map, Polynomial.eval₂_at_apply,
        (hsamplePair i hi).1, (hsamplePair i hi).2] using heval
  refine ⟨P₀, P₁, hP₀, hP₁, ?_, hgraph, hvanish, hinitPair, hhighPair,
    hregularPair, hreconstruction⟩
  rw [← hcard]
  apply Finset.card_le_card
  intro i hi
  simp only [commonPolynomialAgreementSet, Finset.mem_filter, Finset.mem_univ, true_and]
  exact commonAgreement_of_symbolicSourceAgreement_mem_prime_of_exponent domain f g iota
    center Q K τ hτ P hP hs hd P₀ P₁ hgraph hpoly i (hcuts i hi)


/-- A regular positive-dimensional component supported on `L` agreement cuts yields an
actual pair with at least `L` common agreements and all chart restriction identities.
The agreement threshold is arbitrary subject only to `k ≤ L`. -/
theorem exists_graphLine_pair_of_symbolic_prime_agreements
    [IsAlgClosed E] [DecidableEq F] {L : ℕ} (domain : Fin n ↪ F) (f g : Fin n → F)
    (indices : Finset (Fin n)) (hcard : indices.card = L) (hkL : k ≤ L)
    (iota : F →+* E) (center : E) (Q : DifferentialPolynomial E[X] r)
    (hK : r < K) (P : Ideal (MvPolynomial (Option (Fin (r + 1))) E))
    (hP : P.IsPrime) (hs : symbolicSourceSeparant center Q ∉ P)
    (hd : 0 < (hilbertPolynomial P).natDegree)
    (hinit : symbolicSourceInitialEquation center Q ∈ P)
    (hhigh : ∀ l : Fin K, k ≤ l.val → symbolicSourceNumerator center Q K l ∈ P)
    (hcuts : ∀ i ∈ indices,
      symbolicSourceAgreement center Q K (iota (domain i)) (iota (f i)) (iota (g i)) ∈ P) :
    ∃ P₀ P₁ : F[X], P₀.degree < k ∧ P₁.degree < k ∧
      L ≤ (commonPolynomialAgreementSet domain f g P₀ P₁).card ∧
      (∀ x ∈ principalOpenZeroLocus P (symbolicSourceSeparant center Q),
        x = affineGraphPoint (polynomialJet (d := r) center (P₀.map iota))
          (polynomialJet (d := r) center (P₁.map iota)) (x none)) ∧
      (∀ p ∈ P,
        affineGraphPullback (polynomialJet (d := r) center (P₀.map iota))
          (polynomialJet (d := r) center (P₁.map iota)) p = 0) ∧
      affineGraphPullback (polynomialJet (d := r) center (P₀.map iota))
        (polynomialJet (d := r) center (P₁.map iota))
        (symbolicSourceInitialEquation center Q) = 0 ∧
      (∀ l : Fin K, k ≤ l.val →
        affineGraphPullback (polynomialJet (d := r) center (P₀.map iota))
          (polynomialJet (d := r) center (P₁.map iota))
          (symbolicSourceNumerator center Q K l) = 0) ∧
      affineGraphPullback (polynomialJet (d := r) center (P₀.map iota))
        (polynomialJet (d := r) center (P₁.map iota)) (symbolicSourceSeparant center Q) ≠ 0 ∧
      ∀ l : Fin K,
        affineGraphPullback (polynomialJet (d := r) center (P₀.map iota))
          (polynomialJet (d := r) center (P₁.map iota))
          (symbolicSourceReconstructionError center Q K (P₀.map iota) (P₁.map iota) l) = 0 := by
  classical
  obtain ⟨sample, hsub, hsample⟩ := Finset.exists_subset_card_eq (hcard ▸ hkL)
  obtain ⟨P₀, P₁, hP₀, hP₁, hsamplePair, hgraph, hvanish, hinitPair,
      hhighPair, hregularPair, hreconstruction⟩ :=
    exists_graphLine_pair_of_symbolic_prime_sample domain f g sample hsample
      iota center Q hK P hP hs hd hinit hhigh (fun i hi ↦ hcuts i (hsub hi))
  have hpoly : ∀ x ∈ principalOpenZeroLocus P (symbolicSourceSeparant center Q),
      rationalTaylorPolynomial center (MvPolynomial.map (Polynomial.evalRingHom (x none)) Q)
        K (fun j ↦ x (some j)) = P₀.map iota + Polynomial.C (x none) * P₁.map iota := by
    intro x hx
    let φ : E[X] →ₐ[E] E := Polynomial.aeval (x none)
    have hφ : φ.toRingHom = Polynomial.evalRingHom (x none) := by
      ext a <;> simp [φ]
    have hS : aeval (fun j ↦ x (some j))
        (MvPolynomial.map φ.toRingHom (initialJetSeparantOver (Polynomial.C center) Q)) ≠ 0 := by
      simpa only [symbolicSourceSeparant, aeval_optionEquivRight_symm, hφ] using hx.2
    have hdegree := degree_rationalTaylorPolynomial_lt_of_symbolic_high_cuts
      φ (Polynomial.C center) Q K k (fun j ↦ x (some j)) hS
      (fun l hl ↦ by
        have hz := hx.1 _ (hhigh l hl)
        simpa only [symbolicSourceNumerator, aeval_optionEquivRight_symm, hφ] using hz)
    have hcenter : φ (Polynomial.C center) = center := by simp [φ]
    rw [hcenter, hφ] at hdegree
    have hpairdegree : (P₀.map iota + Polynomial.C (x none) * P₁.map iota).degree < k := by
      apply (Polynomial.degree_add_le _ _).trans_lt
      apply max_lt (Polynomial.degree_map_le.trans_lt hP₀)
      rw [← Polynomial.smul_eq_C_mul]
      exact (Polynomial.degree_smul_le _ _).trans_lt (Polynomial.degree_map_le.trans_lt hP₁)
    apply Polynomial.eq_of_degrees_lt_of_eval_index_eq sample
      (mappedDomain domain iota).injective.injOn
    · simpa only [hsample] using hdegree
    · simpa only [hsample] using hpairdegree
    · intro i hi
      have heval := (symbolicSourceAgreement_eq_zero_iff center Q K x hx.2
        (iota (domain i)) (iota (f i)) (iota (g i))).mp (hx.1 _ (hcuts i (hsub hi)))
      simpa only [mappedDomain, Function.Embedding.trans_apply, Function.Embedding.coeFn_mk,
        Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
        Polynomial.eval_map, Polynomial.eval₂_at_apply,
        (hsamplePair i hi).1, (hsamplePair i hi).2] using heval
  refine ⟨P₀, P₁, hP₀, hP₁, ?_, hgraph, hvanish, hinitPair, hhighPair,
    hregularPair, hreconstruction⟩
  rw [← hcard]
  apply Finset.card_le_card
  intro i hi
  simp only [commonPolynomialAgreementSet, Finset.mem_filter, Finset.mem_univ, true_and]
  exact commonAgreement_of_symbolicSourceAgreement_mem_prime domain f g iota center Q K
    P hP hs hd P₀ P₁ hgraph hpoly i (hcuts i hi)

end ReedSolomon

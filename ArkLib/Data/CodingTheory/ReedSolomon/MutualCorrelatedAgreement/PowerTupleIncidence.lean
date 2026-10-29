/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.PowerTupleCounting
public import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.PowerBatchedComponentRecognition
public import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.PowerBatchedSharpRegularAgreement
public import ArkLib.ToMathlib.MvPolynomial.FrobeniusPullback
public import ArkLib.ToMathlib.RingTheory.Nullstellensatz.PrincipalOpenParametrization
/-!
# Incidence away from Frobenius power tuple graphs

Sparse Taylor equations and agreement equations constrain regular prime components to
Frobenius power tuple graphs. A sharp bidegree incidence estimate bounds finite families of
regular points outside these graphs.

## Main statements

* `frobeniusPowerSparseTaylorNumerators` lists the Taylor numerators with indices not divisible
  by the Frobenius exponent.
* `admissibleFrobeniusPowerTupleGraphLocus` collects the retained tuple graphs with a given
  common-agreement threshold.
* `commonAgreement_of_frobeniusPowerAgreementEquation_mem_prime`: a cut in a regular prime
  component forces coordinatewise agreement.
* `principalOpen_subset_admissibleFrobeniusPowerTupleGraphLocus` covers positive-dimensional
  regular prime components by a retained tuple graph.
* `finite_frobeniusPowerTupleIncidence_off_graphs_card_le` bounds regular points outside the
  retained tuple graphs.

## References

* [DKT26]
-/

@[expose] public section

noncomputable section

namespace ReedSolomon

open Polynomial MvPolynomial PolynomialDifferential

variable {F E α : Type*} [Field F] [Field E] {n k K ℓ : ℕ}

/-- The Taylor numerators whose indices are not divisible by the Frobenius exponent. -/
def frobeniusPowerSparseTaylorNumerators (center : E)
    (Q : DifferentialPolynomial E[X] 0) (K τ s : ℕ) :
    List (MvPolynomial (Option (Fin 1)) E) :=
  ((Finset.univ : Finset (Fin K)).filter (fun l ↦ ¬s ∣ l.val)).toList.map
    (fun l ↦ jointCommonTaylorNumerator center Q τ l)

/-- Retained admissible tuple graphs with at least `L` common agreement positions. -/
def admissibleFrobeniusPowerTupleGraphLocus [Fintype α]
    (domain : α ↪ F) (values : Fin (ℓ + 1) → α → F)
    (ι : F →+* E) (roots : α → E) (center : E)
    (Q : DifferentialPolynomial E[X] 0) (K k L τ s : ℕ) :
    Set (Option (Fin 1) → E) :=
  {x | ∃ P : Fin (ℓ + 1) → F[X],
    IsAdmissibleFrobeniusPowerTuple domain values ι roots center Q K k τ s P ∧
    L ≤ {i : α | ∀ t, (P t).eval (domain i) = values t i}.ncard ∧
    x = fun i ↦
      (frobeniusPowerGraphMap center s (fun t ↦ (P t).map ι) i).eval (x none)}

/-- An agreement equation in a regular prime component forces every tuple polynomial to agree at
the corresponding base-field position. -/
theorem commonAgreement_of_frobeniusPowerAgreementEquation_mem_prime [IsAlgClosed E]
    (domain : α ↪ F) (values : Fin (ℓ + 1) → α → F) (ι : F →+* E)
    (p e : ℕ) [ExpChar E p] (roots : α → E)
    (hroots : ∀ i, roots i ^ (p ^ e) = ι (domain i))
    (center : E) (Q : DifferentialPolynomial E[X] 0)
    (hK : 0 < K) (hKk : K ≤ p ^ e * k) (τ : ℕ)
    (hτ : TaylorExponentSufficient 0 K τ)
    (I : Ideal (MvPolynomial (Option (Fin 1)) E)) [hI : I.IsPrime]
    (hs : jointInitialJetSeparant center Q ∉ I)
    (hd : 0 < (affineHilbertPolynomial I).natDegree)
    (P : Fin (ℓ + 1) → F[X])
    (hP : IsAdmissibleFrobeniusPowerTuple
      domain values ι roots center Q K k τ (p ^ e) P)
    (hgraph : ∀ x ∈ {x | x ∈ zeroLocus E I ∧
      aeval x (jointInitialJetSeparant center Q) ≠ 0},
      x = fun i ↦
        (frobeniusPowerGraphMap center (p ^ e) (fun t ↦ (P t).map ι) i).eval (x none))
    (i : α)
    (hcut : jointTaylorAgreementEquation center Q K τ (Polynomial.C (roots i))
      (frobeniusPowerCoordinate (p ^ e) (fun t ↦ ι (values t i))) ∈ I) :
    ∀ t, (P t).eval (domain i) = values t i := by
  let regularSet := {x | x ∈ zeroLocus E I ∧
    aeval x (jointInitialJetSeparant center Q) ≠ 0}
  have hregular : IsLeftRegular
      (Ideal.Quotient.mk I (jointInitialJetSeparant center Q)) :=
    IsLeftCancelMulZero.mul_left_cancel_of_ne_zero
      (mt Ideal.Quotient.eq_zero_iff_mem.mp hs)
  have hinfinite : regularSet.Infinite := by
    intro hfinite
    have hzero := (finite_principalOpen_iff_natDegree_affineHilbertPolynomial_eq_zero
      hregular).mp hfinite
    omega
  have hchallengeInj : Set.InjOn
      (fun x : Option (Fin 1) → E ↦ (x none) ^ (p ^ e)) regularSet := by
    intro x hx y hy hxy
    have hpowInj : Function.Injective (fun z : E ↦ z ^ (p ^ e)) := by
      intro z w hzw
      apply iterateFrobenius_inj E p e
      simpa only [iterateFrobenius_def] using hzw
    have hpow : x none = y none := hpowInj hxy
    rw [hgraph x hx, hgraph y hy, hpow]
  let domainE := domain.trans ⟨ι, ι.injective⟩
  let wordE : Fin (ℓ + 1) → α → E := fun t j ↦ ι (values t j)
  let tupleE : Fin (ℓ + 1) → E[X] := fun t ↦ (P t).map ι
  let mismatch := curveDiscrepancy domainE wordE tupleE i
  have hzero : mismatch = 0 := by
    apply Polynomial.eq_zero_of_infinite_isRoot
    apply (hinfinite.image hchallengeInj).mono
    rintro z ⟨x, hx, rfl⟩
    let φ : E[X] →ₐ[E] E := Polynomial.aeval (x none)
    have hφ : φ.toRingHom = Polynomial.evalRingHom (x none) := by
      ext a <;> simp [φ, Polynomial.evalRingHom]
    have hs' : aeval (fun j ↦ x (some j))
        (MvPolynomial.map φ.toRingHom
      (initialJetSeparant (Polynomial.C center) Q)) ≠ 0 := by
      have hsx := hx.2
      rw [jointInitialJetSeparant, aeval_optionEquivRight_symm] at hsx
      simpa only [φ] using hsx
    have hcutzero := hx.1 _ hcut
    rw [jointTaylorAgreementEquation, aeval_optionEquivRight_symm] at hcutzero
    have heval := (aeval_map_taylorAgreementEquationOver_eq_zero_iff_of_exponent
      φ (Polynomial.C center) Q K τ hτ (fun j ↦ x (some j)) hs'
      (Polynomial.C (roots i))
      (frobeniusPowerCoordinate (p ^ e) (fun t ↦ ι (values t i)))).mp hcutzero
    have hregularGraph :
        (aeval (frobeniusPowerGraphMap center (p ^ e)
          (fun t ↦ (P t).map ι)) (jointInitialJetSeparant center Q)).eval (x none) ≠ 0 := by
      rw [MvPolynomial.polynomial_eval_aeval, ← hgraph x hx]
      exact hx.2
    have hspecial := hP.specialize hroots hK hKk hτ (x none) hregularGraph
    have hspecial' : rationalTaylorPolynomial center
        (MvPolynomial.map (Polynomial.evalRingHom (x none)) Q) K
        (fun j ↦ (frobeniusPowerInitialGraph center (p ^ e)
          (fun t ↦ (P t).map ι) j).eval (x none)) =
        Polynomial.expand E (p ^ e)
          (powerBatchedPolynomial (fun t ↦ (P t).map ι) ((x none) ^ (p ^ e))) := by
      simpa only [frobeniusPowerGraphMap, Option.elim_some] using hspecial
    simp only [hφ, φ, Polynomial.aeval_def, Algebra.algebraMap_self,
      Polynomial.eval₂_id, Polynomial.eval_C, frobeniusPowerCoordinate_eval] at heval
    rw [hgraph x hx] at heval
    simp only [frobeniusPowerGraphMap, Option.elim_none, Option.elim_some,
      Polynomial.eval_X] at heval
    rw [hspecial'] at heval
    change mismatch.eval ((x none) ^ (p ^ e)) = 0
    rw [curveDiscrepancy_eval]
    apply sub_eq_zero.mpr
    simpa only [expand_eval, hroots, powerBatchedPolynomial_eval, powerBatchedWord,
      domainE, wordE, tupleE, Function.Embedding.trans_apply, Function.Embedding.coeFn_mk,
      Polynomial.eval_map, Polynomial.eval₂_at_apply, pow_mul] using heval
  have hcommon := (curveDiscrepancy_eq_zero_iff domainE wordE tupleE i).mp hzero
  intro t
  apply ι.injective
  simpa only [domainE, wordE, tupleE, Function.Embedding.trans_apply,
    Function.Embedding.coeFn_mk, Polynomial.eval_map, Polynomial.eval₂_at_apply] using hcommon t

/-- A regular positive-dimensional prime component containing `L` agreement cuts lies in a
retained Frobenius power tuple graph with at least `L` common agreements. -/
theorem principalOpen_subset_admissibleFrobeniusPowerTupleGraphLocus [IsAlgClosed E]
    [Fintype α] {L : ℕ}
    (domain : α ↪ F) (values : Fin (ℓ + 1) → α → F) (ι : F →+* E)
    (p e : ℕ) [ExpChar E p] (roots : α → E)
    (hroots : ∀ i, roots i ^ (p ^ e) = ι (domain i))
    (center : E) (Q : DifferentialPolynomial E[X] 0)
    (hK : 0 < K) (hKk : K ≤ p ^ e * k) (hkL : k ≤ L) (τ : ℕ)
    (hτ : TaylorExponentSufficient 0 K τ)
    (I : Ideal (MvPolynomial (Option (Fin 1)) E)) [hI : I.IsPrime]
    (hs : jointInitialJetSeparant center Q ∉ I)
    (hinit : jointInitialJetEquation center Q ∈ I)
    (hsparse : ∀ q ∈ frobeniusPowerSparseTaylorNumerators center Q K τ (p ^ e), q ∈ I)
    (hd : 0 < (affineHilbertPolynomial I).natDegree)
    (hcuts : L ≤ {i : α | jointTaylorAgreementEquation center Q K τ
      (Polynomial.C (roots i))
      (frobeniusPowerCoordinate (p ^ e) (fun t ↦ ι (values t i))) ∈ I}.ncard) :
    {x | x ∈ zeroLocus E I ∧ aeval x (jointInitialJetSeparant center Q) ≠ 0} ⊆
      admissibleFrobeniusPowerTupleGraphLocus
        domain values ι roots center Q K k L τ (p ^ e) := by
  classical
  let cutIndices : Set α := {i | jointTaylorAgreementEquation center Q K τ
    (Polynomial.C (roots i))
    (frobeniusPowerCoordinate (p ^ e) (fun t ↦ ι (values t i))) ∈ I}
  have hfinite : cutIndices.Finite := Set.toFinite _
  have hcutsCard : L ≤ hfinite.toFinset.card := by
    rw [Set.ncard_eq_toFinset_card cutIndices hfinite] at hcuts
    exact hcuts
  obtain ⟨indices, hindices, hcard⟩ := Finset.exists_subset_card_eq hcutsCard
  obtain ⟨sample, hsampleSub, hsampleCard⟩ :=
    Finset.exists_subset_card_eq (hcard ▸ hkL)
  obtain ⟨P, hdegree, hagree, hgraph, hvanish, hseparant⟩ :=
    exists_frobeniusPowerGraph_of_symbolic_prime_sample
      domain values sample hsampleCard ι p e roots (fun i _ ↦ hroots i) center Q hK hKk τ hτ
      I hs hd (fun l hl ↦ hsparse _ (by
        simp only [frobeniusPowerSparseTaylorNumerators, List.mem_map,
          Finset.mem_toList, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨l, hl, rfl⟩))
      (fun i hi ↦ by
        have hi' : i ∈ hfinite.toFinset := hindices (hsampleSub hi)
        have hi'' : i ∈ cutIndices := by
          exact hfinite.mem_toFinset.mp hi'
        exact hi'')
  have hP : IsAdmissibleFrobeniusPowerTuple
      domain values ι roots center Q K k τ (p ^ e) P := by
    refine ⟨hdegree, hvanish _ hinit, hseparant, ?_, ?_⟩
    · intro l hl
      exact hvanish _ (hsparse _ (by
        simp only [frobeniusPowerSparseTaylorNumerators, List.mem_map,
          Finset.mem_toList, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨l, hl, rfl⟩))
    · exact ⟨sample, hsampleCard, hagree, fun i hi ↦ by
        have hi' : i ∈ hfinite.toFinset := hindices (hsampleSub hi)
        have hi'' : i ∈ cutIndices := by
          exact hfinite.mem_toFinset.mp hi'
        exact hvanish _ hi''⟩
  have hcommon : L ≤ {i : α | ∀ t, (P t).eval (domain i) = values t i}.ncard := by
    have hsubset : (indices : Set α) ⊆
        {i : α | ∀ t, (P t).eval (domain i) = values t i} := by
      intro i hi t
      have hcut : jointTaylorAgreementEquation center Q K τ (Polynomial.C (roots i))
          (frobeniusPowerCoordinate (p ^ e) (fun t ↦ ι (values t i))) ∈ I := by
        have hi' : i ∈ hfinite.toFinset := hindices hi
        have hi'' : i ∈ cutIndices := by
          exact hfinite.mem_toFinset.mp hi'
        exact hi''
      exact (commonAgreement_of_frobeniusPowerAgreementEquation_mem_prime
        domain values ι p e roots hroots center Q hK hKk τ hτ I (hI := hI) hs hd P hP
        (fun x hx ↦ hgraph x hx) i hcut) t
    calc
      L = indices.card := hcard.symm
      _ = (indices : Set α).ncard := by simp
      _ ≤ _ := Set.ncard_mono hsubset
  intro x hx
  exact ⟨P, hP, hcommon, hgraph x hx⟩

/-- A finite family of regular points outside retained Frobenius power tuple graphs satisfies a
sharp one-coordinate bidegree incidence bound. -/
theorem finite_frobeniusPowerTupleIncidence_off_graphs_card_le [IsAlgClosed E]
    {L : ℕ}
    (domain : Fin n ↪ F) (values : Fin (ℓ + 1) → Fin n → F) (ι : F →+* E)
    (p e : ℕ) [ExpChar E p] (roots : Fin n → E)
    (hroots : ∀ i, roots i ^ (p ^ e) = ι (domain i))
    (center : E) (Q : DifferentialPolynomial E[X] 0)
    (hK : 0 < K) (hKk : K ≤ p ^ e * k) (τ h b A : ℕ)
    (hτ : TaylorExponentSufficient 0 K τ) (hτpos : 0 < τ) (hℓ : 0 < ℓ)
    (hb : 0 < b) (hkL : k ≤ L) (hLA : L ≤ A)
    (hheight : CoeffNatDegreeLE Q h) (hjet : jetTotalDegree Q ≤ b)
    (hinit : jointInitialJetEquation center Q ≠ 0)
    (hproper : Ideal.span ({jointInitialJetEquation center Q} :
      Set (MvPolynomial (Option (Fin 1)) E)) ≠ ⊤)
    (S : Finset (Option (Fin 1) → E))
    (hS : ∀ x ∈ S,
      aeval x (jointInitialJetEquation center Q) = 0 ∧
      aeval x (jointInitialJetSeparant center Q) ≠ 0 ∧
      (∀ q ∈ frobeniusPowerSparseTaylorNumerators center Q K τ (p ^ e), aeval x q = 0) ∧
      x ∉ admissibleFrobeniusPowerTupleGraphLocus
        domain values ι roots center Q K k L τ (p ^ e))
    (hA : ∀ x ∈ S, A ≤ {i : Fin n | aeval x
      (jointTaylorAgreementEquation center Q K τ (Polynomial.C (roots i))
        (frobeniusPowerCoordinate (p ^ e) (fun t ↦ ι (values t i)))) = 0}.ncard) :
    (S.card : ℚ) ≤
      (h * (1 + τ * (b - 1)) + b * (p ^ e * ℓ + τ * h) : ℕ) *
        (((n - L + 1 : ℕ) : ℚ) / ((A - L + 1 : ℕ) : ℚ)) := by
  classical
  have hp : 0 < p ^ e := pow_pos (expChar_pos E p) e
  have hτone : 1 ≤ τ := Nat.succ_le_of_lt hτpos
  have hchallengeLe : h ≤ p ^ e * ℓ + τ * h := by
    have hh : h ≤ τ * h := by
      simpa only [Nat.one_mul] using Nat.mul_le_mul_right h hτone
    exact hh.trans (Nat.le_add_left _ _)
  have hjetLe : b ≤ 1 + τ * (b - 1) := by
    have hmul : b - 1 ≤ τ * (b - 1) := by
      simpa only [Nat.one_mul] using Nat.mul_le_mul_right (b - 1) hτone
    rw [← Nat.sub_add_cancel (by omega : 1 ≤ b)]
    calc
      (b - 1) + 1 ≤ τ * (b - 1) + 1 := Nat.add_le_add_right hmul 1
      _ = 1 + τ * (b - 1) := by omega
  apply bidegreeHypersurface_incidence_off_excluded_sharp_one
    (a := p ^ e * ℓ + τ * h) (b := 1 + τ * (b - 1)) (h := h) (v := b)
    (by positivity) (by omega) hLA
    (jointInitialJetEquation center Q) (jointInitialJetSeparant center Q)
    hinit hproper
    (by simpa only [jointInitialJetEquation] using
      initialJetEquation_mem_restrictBidegree center Q h b hheight hjet)
    ?_ ?_ (frobeniusPowerSparseTaylorNumerators center Q K τ (p ^ e)) ?_
    (fun i ↦ jointTaylorAgreementEquation center Q K τ (Polynomial.C (roots i))
      (frobeniusPowerCoordinate (p ^ e) (fun t ↦ ι (values t i))))
    ?_ (admissibleFrobeniusPowerTupleGraphLocus
      domain values ι roots center Q K k L τ (p ^ e))
    (fun I hI hs hi hsp hd hc ↦
      principalOpen_subset_admissibleFrobeniusPowerTupleGraphLocus
        domain values ι p e roots hroots center Q hK hKk hkL τ hτ I (hI := hI)
        hs hi hsp hd hc)
    S hS hA
  · apply mem_restrictBidegree_mono
      (by simpa only [jointInitialJetEquation] using
        initialJetEquation_mem_restrictBidegree center Q h b hheight hjet)
    · exact hchallengeLe
    · exact hjetLe
  · apply mem_restrictBidegree_mono
      (by simpa only [jointInitialJetSeparant] using
        initialJetSeparant_mem_restrictBidegree center Q h b hheight hjet)
    · exact hchallengeLe
    · calc
        b - 1 = 1 * (b - 1) := by rw [Nat.one_mul]
        _ ≤ τ * (b - 1) := Nat.mul_le_mul_right _ (Nat.succ_le_of_lt hτpos)
        _ ≤ 1 + τ * (b - 1) := Nat.le_add_left _ _
  · intro q hq
    simp only [frobeniusPowerSparseTaylorNumerators, List.mem_map,
      Finset.mem_toList, Finset.mem_filter, Finset.mem_univ, true_and] at hq
    obtain ⟨l, _, rfl⟩ := hq
    exact jointCommonTaylorNumerator_mem_regularPowerBatchedCutBidegree_of_exponent
      center Q (p ^ e * ℓ) K h b τ hτ hb hheight hjet l
  · intro i
    apply jointTaylorAgreementEquation_mem_regularPowerBatchedCutBidegree_of_exponent
      center (roots i) (frobeniusPowerCoordinate (p ^ e) (fun t ↦ ι (values t i)))
      Q (p ^ e * ℓ) K h b τ hτ ?_ hb hheight hjet
    exact (frobeniusPowerCoordinate_natDegree_le (p ^ e) _)

end ReedSolomon

end

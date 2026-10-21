/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.FrobeniusAdmissibility
public import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.PowerBatchedSharpRegularAgreement
public import ArkLib.ToMathlib.RingTheory.Nullstellensatz.BidegreeIncidence
/-!
# Incidence for sparse Frobenius Taylor cuts

Sparse Taylor cuts and agreement equations place regular chart points on admissible Frobenius
pair graphs whenever their component contains enough agreement cuts. A bidegree incidence bound
then controls finite sets of regular points outside those graphs.

## Main statements

* `frobeniusSparseTaylorCuts` and `admissibleFrobeniusPairGraphLocus` describe the sparse cuts and
  admissible graph locus.
* `principalOpen_subset_admissibleFrobeniusPairGraphLocus` identifies the regular locus of a
  positive-dimensional prime component with an admissible pair graph.
* `finite_frobeniusChartPoints_off_admissiblePairGraphs_card_le` bounds finite sets of regular
  chart points outside the admissible graphs.

## References

* [DKT26]
-/

@[expose] public section

open Polynomial MvPolynomial PolynomialDifferential

namespace ReedSolomon

noncomputable section

variable {F E : Type*} [Field F] [Field E] {n k K : ℕ}

/-- The common Taylor numerators whose indices are not divisible by the Frobenius exponent. -/
def frobeniusSparseTaylorCuts (center : E) (Q : DifferentialPolynomial E[X] 0)
    (K τ s : ℕ) : List (MvPolynomial (Option (Fin 1)) E) :=
  ((Finset.univ : Finset (Fin K)).filter (fun l ↦ ¬s ∣ l.val)).toList.map
    (fun l ↦ jointCommonTaylorNumerator center Q τ l)

/-- Points on regular graphs of admissible Frobenius polynomial pairs. -/
def admissibleFrobeniusPairGraphLocus (domain : Fin n ↪ F) (f g : Fin n → F)
    (iota : F →+* E) (roots : Fin n → E) (center : E)
    (Q : DifferentialPolynomial E[X] 0) (K k τ s : ℕ) :
    Set (Option (Fin 1) → E) :=
  {x | ∃ F₀ G₀ : F[X],
    IsAdmissibleFrobeniusPair domain f g iota roots center Q K k τ s F₀ G₀ ∧
    x = fun i ↦ (frobeniusInitialGraph center s (F₀.map iota) (G₀.map iota) i).eval
      (x none)}

/-- Positive-dimensional regular prime components with enough agreement cuts lie on an
admissible Frobenius pair graph. -/
theorem principalOpen_subset_admissibleFrobeniusPairGraphLocus [IsAlgClosed E]
    (domain : Fin n ↪ F) (f g : Fin n → F) (iota : F →+* E)
    (p e : ℕ) [ExpChar E p] (roots : Fin n → E)
    (hroots : ∀ i, roots i ^ (p ^ e) = iota (domain i))
    (center : E) (Q : DifferentialPolynomial E[X] 0)
    (hK : 0 < K) (hKk : K ≤ p ^ e * k) (τ : ℕ)
    (hτ : TaylorExponentSufficient 0 K τ)
    (I : Ideal (MvPolynomial (Option (Fin 1)) E)) [hI : I.IsPrime]
    (hs : jointInitialJetSeparant center Q ∉ I)
    (hinit : jointInitialJetEquation center Q ∈ I)
    (hsparse : ∀ q ∈ frobeniusSparseTaylorCuts center Q K τ (p ^ e), q ∈ I)
    (hd : 0 < (affineHilbertPolynomial I).natDegree)
    (hcuts : k ≤ {i : Fin n | jointTaylorAgreementEquation center Q K τ
      (Polynomial.C (roots i))
      (Polynomial.C (iota (f i)) + Polynomial.X ^ (p ^ e) * Polynomial.C (iota (g i))) ∈ I
        }.ncard) :
    {x | x ∈ zeroLocus E I ∧ aeval x (jointInitialJetSeparant center Q) ≠ 0} ⊆
      admissibleFrobeniusPairGraphLocus domain f g iota roots center Q K k τ (p ^ e) := by
  classical
  let cutsInI : Finset (Fin n) := Finset.univ.filter fun i ↦
    jointTaylorAgreementEquation center Q K τ (Polynomial.C (roots i))
      (Polynomial.C (iota (f i)) + Polynomial.X ^ (p ^ e) * Polynomial.C (iota (g i))) ∈ I
  have hset : (cutsInI : Set (Fin n)) = {i | jointTaylorAgreementEquation center Q K τ
      (Polynomial.C (roots i))
      (Polynomial.C (iota (f i)) + Polynomial.X ^ (p ^ e) * Polynomial.C (iota (g i))) ∈ I} := by
    ext i
    simp [cutsInI]
  have hcutsCard : k ≤ cutsInI.card := by
    calc
      k ≤ {i : Fin n | jointTaylorAgreementEquation center Q K τ
          (Polynomial.C (roots i))
          (Polynomial.C (iota (f i)) + Polynomial.X ^ (p ^ e) * Polynomial.C (iota (g i))) ∈ I
            }.ncard := hcuts
      _ = (cutsInI : Set (Fin n)).ncard := by rw [hset]
      _ = cutsInI.card := Set.ncard_coe_finset _
  obtain ⟨sample, hsub, hcard⟩ := Finset.exists_subset_card_eq hcutsCard
  have hsampleCuts : ∀ i ∈ sample,
      jointTaylorAgreementEquation center Q K τ (Polynomial.C (roots i))
        (Polynomial.C (iota (f i)) + Polynomial.X ^ (p ^ e) *
          Polynomial.C (iota (g i))) ∈ I := by
    intro i hi
    have hi' : i ∈ cutsInI := hsub hi
    simpa only [cutsInI, Finset.mem_filter, Finset.mem_univ, true_and] using hi'
  obtain ⟨F₀, G₀, hpair, hgraph⟩ :=
    exists_admissibleFrobeniusPair_of_symbolic_prime_sample domain f g sample hcard iota p e
      roots (fun i hi ↦ hroots i) center Q hK hKk τ hτ I hs hinit hd
      (fun l hl ↦ hsparse _ (by
        simp only [frobeniusSparseTaylorCuts, List.mem_map, Finset.mem_toList,
          Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨l, hl, rfl⟩))
      (fun i hi ↦ hsampleCuts i hi)
  intro x hx
  exact ⟨F₀, G₀, hpair, hgraph x hx⟩

/-- A finite set of regular Frobenius chart points outside admissible pair graphs satisfies the
mixed bidegree incidence bound. -/
theorem finite_frobeniusChartPoints_off_admissiblePairGraphs_card_le [IsAlgClosed E]
    (domain : Fin n ↪ F) (f g : Fin n → F) (iota : F →+* E)
    (p e : ℕ) [ExpChar E p] (roots : Fin n → E)
    (hroots : ∀ i, roots i ^ (p ^ e) = iota (domain i))
    (center : E) (Q : DifferentialPolynomial E[X] 0)
    (hK : 0 < K) (hKk : K ≤ p ^ e * k) (τ h b A : ℕ)
    (hτ : TaylorExponentSufficient 0 K τ) (hτpos : 0 < τ)
    (hb : 0 < b) (hkA : k ≤ A)
    (hheight : CoeffNatDegreeLE Q h)
    (hjet : Q.weightedTotalDegree (fun i ↦ i.elim 0 (fun _ ↦ 1)) ≤ b)
    (hinit : jointInitialJetEquation center Q ≠ 0)
    (hproper : Ideal.span ({jointInitialJetEquation center Q} :
      Set (MvPolynomial (Option (Fin 1)) E)) ≠ ⊤)
    (S : Finset (Option (Fin 1) → E))
    (hS : ∀ x ∈ S,
      aeval x (jointInitialJetEquation center Q) = 0 ∧
      aeval x (jointInitialJetSeparant center Q) ≠ 0 ∧
      (∀ q ∈ frobeniusSparseTaylorCuts center Q K τ (p ^ e), aeval x q = 0) ∧
      x ∉ admissibleFrobeniusPairGraphLocus domain f g iota roots center Q K k τ (p ^ e))
    (hA : ∀ x ∈ S, A ≤ {i : Fin n | aeval x
      (jointTaylorAgreementEquation center Q K τ (Polynomial.C (roots i))
        (Polynomial.C (iota (f i)) + Polynomial.X ^ (p ^ e) *
          Polynomial.C (iota (g i)))) = 0}.ncard) :
    (S.card : ℚ) ≤ (h * (1 + τ * (b - 1)) + b * (p ^ e + τ * h) : ℕ) *
      (((n - k + 1 : ℕ) : ℚ) / ((A - k + 1 : ℕ) : ℚ)) := by
  classical
  have hp : 0 < p ^ e := pow_pos (expChar_pos E p) e
  have hjet' : jetTotalDegree Q ≤ b := by
    have hw : (jetDegreeWeight : JetVariable 0 → ℕ) =
        fun i ↦ i.elim 0 (fun _ ↦ 1) := by
      funext i
      cases i <;> rfl
    rw [jetTotalDegree, hw]
    exact hjet
  have hτone : 1 ≤ τ := by omega
  have hjetBound : b ≤ 1 + τ * (b - 1) := by
    calc
      b = 1 + (b - 1) := by omega
      _ ≤ 1 + τ * (b - 1) := by
        exact Nat.add_le_add_left (by simpa using Nat.mul_le_mul_right (b - 1) hτone) _
  have hchallengeBound : h ≤ p ^ e + τ * h := by
    calc
      h ≤ τ * h := by simpa using Nat.mul_le_mul_right h hτone
      _ ≤ p ^ e + τ * h := Nat.le_add_left _ _
  apply bidegreeHypersurface_incidence_off_excluded_sharp_one
    (a := p ^ e + τ * h) (b := 1 + τ * (b - 1)) (h := h) (v := b) (L := k)
    (by omega) (by omega) hkA (jointInitialJetEquation center Q)
    (jointInitialJetSeparant center Q) hinit hproper
    (by
      simpa only [jointInitialJetEquation] using
        initialJetEquation_mem_restrictBidegree center Q h b hheight hjet')
    (by
      exact mem_restrictBidegree_mono
        (by
          simpa only [jointInitialJetEquation] using
            initialJetEquation_mem_restrictBidegree center Q h b hheight hjet')
        hchallengeBound hjetBound)
    (by
      exact mem_restrictBidegree_mono
        (by
          simpa only [jointInitialJetSeparant] using
            initialJetSeparant_mem_restrictBidegree center Q h b hheight hjet')
        hchallengeBound (by omega))
    (frobeniusSparseTaylorCuts center Q K τ (p ^ e))
    (by
      intro q hq
      simp only [frobeniusSparseTaylorCuts, List.mem_map, Finset.mem_toList] at hq
      obtain ⟨l, _, rfl⟩ := hq
      exact jointCommonTaylorNumerator_mem_regularPowerBatchedCutBidegree_of_exponent
        center Q (p ^ e) K h b τ hτ hb hheight hjet' l)
    (fun i ↦ jointTaylorAgreementEquation center Q K τ
      (Polynomial.C (roots i))
      (Polynomial.C (iota (f i)) + Polynomial.X ^ (p ^ e) * Polynomial.C (iota (g i))))
    (by
      intro i
      have hy : (Polynomial.C (iota (f i)) + Polynomial.X ^ (p ^ e) *
          Polynomial.C (iota (g i))).natDegree ≤ p ^ e := by
        apply natDegree_add_le_of_degree_le
        · simp
        · exact (natDegree_mul_C_le _ _).trans (natDegree_X_pow_le _)
      have hjet' : jetTotalDegree Q ≤ b := by
        have hw : (jetDegreeWeight : JetVariable 0 → ℕ) =
            fun i ↦ i.elim 0 (fun _ ↦ 1) := by
          funext i
          cases i <;> rfl
        rw [jetTotalDegree, hw]
        exact hjet
      simpa only [jointTaylorAgreementEquation, regularPowerBatchedCutChallengeDegree,
        regularPowerBatchedCutJetDegree] using
        jointTaylorAgreementEquation_mem_regularPowerBatchedCutBidegree_of_exponent
          center (roots i) (Polynomial.C (iota (f i)) + Polynomial.X ^ (p ^ e) *
            Polynomial.C (iota (g i))) Q (p ^ e) K h b τ hτ hy hb hheight hjet')
    (admissibleFrobeniusPairGraphLocus domain f g iota roots center Q K k τ (p ^ e))
    (fun I hI hs hi hsp hd hc ↦ principalOpen_subset_admissibleFrobeniusPairGraphLocus
      domain f g iota p e roots hroots center Q hK hKk τ hτ I (hI := hI) hs hi hsp hd hc)
    S hS hA

end

end ReedSolomon

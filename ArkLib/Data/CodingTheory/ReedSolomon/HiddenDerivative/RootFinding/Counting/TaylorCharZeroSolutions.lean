/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.Counting.TaylorAllSolutions
/-!
# Agreement-sensitive differential root counting in characteristic zero

In characteristic zero every active separant is nonzero.  Direct strong induction on total jet
degree therefore gives the same square-total-degree count without the positive-characteristic
contract used by the general singular-step relation.
-/

@[expose] public section

open PolynomialDifferential


namespace ReedSolomon.HiddenDerivative

noncomputable section

open Polynomial

variable {F : Type*} {d D : ℕ} [Field F] [CharZero F]

/-- An active formal partial derivative is nonzero in characteristic zero. -/
theorem separant_ne_zero_of_dependsOnJet_charZero (Q : DifferentialPolynomial F d)
    (s : Fin (d + 1)) (hs : DependsOnJet Q s) : separant Q s ≠ 0 := by
  classical
  have hsupp : Q.support.Nonempty := MvPolynomial.support_nonempty.mpr <|
    MvPolynomial.ne_zero_of_degreeOf_ne_zero (i := some s) (Nat.ne_of_gt hs)
  obtain ⟨m, hm, heq⟩ := Finset.exists_mem_eq_sup Q.support hsupp fun m ↦ m (some s)
  rw [← MvPolynomial.degreeOf_eq_sup (some s) Q] at heq
  have hdegreepos : 0 < MvPolynomial.degreeOf (some s) Q := hs
  rw [heq] at hdegreepos
  have hmi : m (some s) ≠ 0 := Nat.ne_of_gt hdegreepos
  let m' := m - Finsupp.single (some s) 1
  have hm'_add : m' + Finsupp.single (some s) 1 = m :=
    Finsupp.sub_add_single_one_cancel hmi
  have hm'i : m' (some s) + 1 = m (some s) := by
    dsimp [m']
    rw [Finsupp.single_eq_same]
    omega
  have hcast : (m (some s) : F) ≠ 0 := Nat.cast_ne_zero.mpr hmi
  have hcast_eq : (↑(m' (some s)) + 1 : F) = (m (some s) : F) := by
    exact_mod_cast hm'i
  intro hderiv
  change MvPolynomial.pderiv (some s) Q = 0 at hderiv
  have hzero : MvPolynomial.coeff m' (MvPolynomial.pderiv (some s) Q) = 0 := by
    rw [hderiv, MvPolynomial.coeff_zero]
  rw [MvPolynomial.coeff_pderiv, hm'_add, hcast_eq] at hzero
  exact mul_ne_zero (MvPolynomial.mem_support_iff.mp hm) hcast hzero

omit [CharZero F] in
/-- A regular branch at an arbitrary active order has the global Taylor budget. -/
theorem regularSolutions_card_le_of_agreement_charZero
    (current : DifferentialPolynomial F d) (s : Fin (d + 1))
    (hhighest : highestActiveJet current = some s)
    (K k ν : ℕ) (hK : d < K) (hkK : k ≤ K)
    {n A : ℕ} (domain : Fin n ↪ F) (received : Fin n → F)
    (hk : 0 < k) (hkA : k ≤ A) (hAn : A ≤ n)
    (hdegree : jetTotalDegree current ≤ ν)
    (hbin : ∀ r, r ≤ d → ∀ i, r < i → i < K → (i.choose r : F) ≠ 0)
    (regular : Finset (BoundedSolution current D))
    (haccepts : ∀ solution ∈ regular,
      IsAgreementSolution domain received k A solution.polynomial)
    (hseparant : ∀ solution ∈ regular,
      differentialSpecialization (separant current s) solution.polynomial ≠ 0) :
    (regular.card : ℚ) ≤ (ν : ℚ) *
      ((((n * (1 + 2 * K * (ν - 1)) : ℕ) : ℚ) /
        ((A - k + 1 : ℕ) : ℚ)) ^ d) := by
  classical
  obtain ⟨Q', hQ'⟩ := exists_prefixDifferentialPolynomial current s
    (isHighestActiveJet_of_highestActiveJet_eq_some hhighest)
  let polys : Finset F[X] := regular.image fun solution ↦ solution.polynomial
  have hinjective : Function.Injective (fun solution : BoundedSolution current D ↦
      solution.polynomial) := by
    intro left right heq
    exact Subtype.ext (Subtype.ext heq)
  have hcard : polys.card = regular.card :=
    Finset.card_image_of_injective regular hinjective
  have hsle : s.val ≤ d := Nat.le_of_lt_succ s.isLt
  have hQ'Degree : jetTotalDegree Q' ≤ ν := by
    rw [← jetTotalDegree_rename_jetPrefixEmbedding s Q', hQ']
    exact hdegree
  have hv : 0 < jetTotalDegree Q' := by
    have hactive : 0 < jetDegree current s :=
      (isHighestActiveJet_of_highestActiveJet_eq_some hhighest).1
    have hactive' : 0 < jetDegree Q' (Fin.last s.val) := by
      unfold jetDegree
      rw [← MvPolynomial.degreeOf_rename_of_injective (jetPrefixEmbedding s).injective
        (some (Fin.last s.val)), jetPrefixEmbedding_top, hQ']
      exact hactive
    exact hactive'.trans_le (jetDegree_le_total Q' (Fin.last s.val))
  have hstage := finite_regular_solutions_card_le Q' K k (hsle.trans_lt hK) hkK
    (by rw [← jetTotalDegree_eq_weightedTotalDegree_elim]; exact hv)
    domain received hk hkA hAn polys
    (fun P hP ↦ by
      rcases Finset.mem_image.mp hP with ⟨solution, hsolution, rfl⟩
      exact (haccepts solution hsolution).1)
    (fun P hP ↦ by
      rcases Finset.mem_image.mp hP with ⟨solution, hsolution, rfl⟩
      simpa only [← hQ', differentialSpecialization_rename_jetPrefixEmbedding] using
        solution.equation)
    (fun P hP ↦ by
      rcases Finset.mem_image.mp hP with ⟨solution, hsolution, rfl⟩
      have hs := hseparant solution hsolution
      have heqsep :
          differentialSpecialization (separant current s) solution.polynomial =
            differentialSpecialization (separant Q' (Fin.last s.val)) solution.polynomial := by
        calc
          _ = differentialSpecialization
              (MvPolynomial.rename (jetPrefixEmbedding s)
                (separant Q' (Fin.last s.val))) solution.polynomial := by
              rw [← separant_rename_jetPrefixEmbedding, hQ']
          _ = _ := differentialSpecialization_rename_jetPrefixEmbedding _ _ _
      exact fun hz ↦ hs (heqsep.trans hz))
    (fun i hsi hiK ↦ hbin s.val hsle i hsi hiK)
    (fun P hP ↦ by
      rcases Finset.mem_image.mp hP with ⟨solution, hsolution, rfl⟩
      exact (haccepts solution hsolution).2)
  rw [hcard, ← jetTotalDegree_eq_weightedTotalDegree_elim] at hstage
  have hB : rationalTaylorCutDegreeBound Q' K ≤ 1 + 2 * K * (ν - 1) := by
    unfold rationalTaylorCutDegreeBound
    gcongr
    rw [← jetTotalDegree_eq_weightedTotalDegree_elim]
    exact hQ'Degree
  have hden : 0 < A - k + 1 := by omega
  have hglobalBaseOne :
      1 ≤ ((((n * (1 + 2 * K * (ν - 1)) : ℕ) : ℚ) /
        ((A - k + 1 : ℕ) : ℚ))) := by
    rw [le_div_iff₀ (by exact_mod_cast hden)]
    norm_cast
    have hdenle : A - k + 1 ≤ n := by omega
    calc
      1 * (A - k + 1) = A - k + 1 := one_mul _
      _ ≤ n := hdenle
      _ = n * 1 := by omega
      _ ≤ n * (1 + 2 * K * (ν - 1)) := Nat.mul_le_mul_left n (by omega)
  calc
    (regular.card : ℚ) ≤ (jetTotalDegree Q' : ℚ) *
        ((((n * rationalTaylorCutDegreeBound Q' K : ℕ) : ℚ) /
          ((A - k + 1 : ℕ) : ℚ)) ^ s.val) := hstage
    _ ≤ (ν : ℚ) *
        ((((n * (1 + 2 * K * (ν - 1)) : ℕ) : ℚ) /
          ((A - k + 1 : ℕ) : ℚ)) ^ s.val) := by gcongr
    _ ≤ (ν : ℚ) *
        ((((n * (1 + 2 * K * (ν - 1)) : ℕ) : ℚ) /
          ((A - k + 1 : ℕ) : ℚ)) ^ d) := by gcongr

/-- Direct total-jet-degree induction sums all regular branches in characteristic zero. -/
theorem boundedSolution_card_le_sq_totalJetDegree_charZero
    (Q : DifferentialPolynomial F d) (hQ : Q ≠ 0)
    (K k ν : ℕ) (hK : d < K) (hkK : k ≤ K)
    {n A : ℕ} (domain : Fin n ↪ F) (received : Fin n → F)
    (hk : 0 < k) (hkA : k ≤ A) (hAn : A ≤ n)
    (hdegree : jetTotalDegree Q ≤ ν)
    (hbin : ∀ r, r ≤ d → ∀ i, r < i → i < K → (i.choose r : F) ≠ 0)
    (roots : Finset (BoundedSolution Q D))
    (hroots : ∀ solution ∈ roots,
      IsAgreementSolution domain received k A solution.polynomial) :
    (roots.card : ℚ) ≤ (ν : ℚ) ^ 2 *
      ((((n * (1 + 2 * K * (ν - 1)) : ℕ) : ℚ) /
        ((A - k + 1 : ℕ) : ℚ)) ^ d) := by
  classical
  let R : ℚ :=
    ((n * (1 + 2 * K * (ν - 1)) : ℕ) : ℚ) / ((A - k + 1 : ℕ) : ℚ)
  let cost : ℚ := (ν : ℚ) * R ^ d
  have hcost : 0 ≤ cost := by unfold cost R; positivity
  generalize hΔ : jetTotalDegree Q = Δ
  have recurse : (roots.card : ℚ) ≤ (Δ : ℚ) * cost := by
    induction Δ using Nat.strong_induction_on generalizing Q roots with
    | h Δ ih =>
        cases hactive : highestActiveJet Q with
        | none =>
            let _ : IsEmpty (BoundedSolution Q D) :=
              isEmpty_boundedSolution_of_highestActiveJet_eq_none Q hQ hactive
            have hrootsEmpty : roots = ∅ := by
              ext solution
              exact isEmptyElim solution
            rw [hrootsEmpty]
            exact mul_nonneg (Nat.cast_nonneg _) hcost
        | some s =>
            let regularRoots := regularSolutions Q s D roots
            let singularRoots := singularSolutions Q s D roots
            let nextRoots := singularDescendants Q s D roots
            have hactiveJet : DependsOnJet Q s :=
              (isHighestActiveJet_of_highestActiveJet_eq_some hactive).1
            have hnextNe : separant Q s ≠ 0 :=
              separant_ne_zero_of_dependsOnJet_charZero Q s hactiveJet
            have hregularAccepts : ∀ solution ∈ regularRoots,
                IsAgreementSolution domain received k A solution.polynomial := by
              intro solution hsolution
              apply hroots solution
              exact (Finset.mem_filter.mp (show
                solution ∈ roots.filter fun candidate ↦
                  differentialSpecialization (separant Q s) candidate.polynomial ≠ 0 by
                simpa [regularRoots, regularSolutions] using hsolution)).1
            have hregularSep : ∀ solution ∈ regularRoots,
                differentialSpecialization (separant Q s) solution.polynomial ≠ 0 := by
              intro solution hsolution
              exact (Finset.mem_filter.mp (show
                solution ∈ roots.filter fun candidate ↦
                  differentialSpecialization (separant Q s) candidate.polynomial ≠ 0 by
                simpa [regularRoots, regularSolutions] using hsolution)).2
            have hΔν : jetTotalDegree Q ≤ ν := hdegree
            have hregular : (regularRoots.card : ℚ) ≤ cost := by
              simpa only [cost, R] using regularSolutions_card_le_of_agreement_charZero
                Q s hactive K k ν hK hkK domain received hk hkA hAn hΔν hbin regularRoots
                hregularAccepts hregularSep
            have hnextAccepts : ∀ solution ∈ nextRoots,
                IsAgreementSolution domain received k A solution.polynomial := by
              intro solution hsolution
              change solution ∈ singularDescendants Q s D roots at hsolution
              unfold singularDescendants at hsolution
              rcases Finset.mem_image.mp hsolution with ⟨source, _hsource, heq⟩
              rw [← heq]
              apply hroots source.1
              exact (Finset.mem_filter.mp source.2).1
            have htotalPos : 0 < jetTotalDegree Q :=
              hactiveJet.trans_le (jetDegree_le_total Q s)
            have hmeasure : jetTotalDegree (separant Q s) + 1 ≤ jetTotalDegree Q := by
              have := separant_total_le Q s
              omega
            have hnextDegree : jetTotalDegree (separant Q s) ≤ ν := by omega
            have hmeasureLt : jetTotalDegree (separant Q s) < Δ := by omega
            have hnext : (nextRoots.card : ℚ) ≤
                (jetTotalDegree (separant Q s) : ℚ) * cost := by
              exact ih _ hmeasureLt (separant Q s) hnextNe hnextDegree nextRoots
                hnextAccepts rfl
            have hsingular : (singularRoots.card : ℚ) ≤
                (jetTotalDegree (separant Q s) : ℚ) * cost := by
              rw [← card_singularDescendants Q s D roots]
              exact hnext
            have hpartition : regularRoots.card + singularRoots.card = roots.card :=
              card_regular_add_card_singular Q s D roots
            calc
              (roots.card : ℚ) =
                  (regularRoots.card : ℚ) + (singularRoots.card : ℚ) := by
                exact_mod_cast hpartition.symm
              _ ≤ cost + (jetTotalDegree (separant Q s) : ℚ) * cost :=
                add_le_add hregular hsingular
              _ = ((jetTotalDegree (separant Q s) + 1 : ℕ) : ℚ) * cost := by
                push_cast
                ring
              _ ≤ (Δ : ℚ) * cost := by
                apply mul_le_mul_of_nonneg_right _ hcost
                exact_mod_cast hΔ ▸ hmeasure
  calc
    (roots.card : ℚ) ≤ (Δ : ℚ) * cost := recurse
    _ ≤ (ν : ℚ) * cost := by
      apply mul_le_mul_of_nonneg_right _ hcost
      exact_mod_cast hΔ ▸ hdegree
    _ = (ν : ℚ) ^ 2 * R ^ d := by unfold cost; ring

/-- Characteristic-zero all-solutions form of the agreement-sensitive differential root bound. -/
theorem finite_agreement_solutions_card_le_charZero
    (Q : DifferentialPolynomial F d) (K k ν : ℕ) (hK : d < K) (hkK : k ≤ K)
    (hQ : Q ≠ 0) (hdegreeQ : jetTotalDegree Q ≤ ν)
    {n A : ℕ} (domain : Fin n ↪ F) (received : Fin n → F)
    (hk : 0 < k) (hkA : k ≤ A) (hAn : A ≤ n)
    (hbin : ∀ r, r ≤ d → ∀ i, r < i → i < K → (i.choose r : F) ≠ 0)
    (S : Finset F[X])
    (hsol : ∀ P ∈ S, differentialSpecialization Q P = 0)
    (haccept : ∀ P ∈ S, IsAgreementSolution domain received k A P) :
    (S.card : ℚ) ≤ (ν : ℚ) ^ 2 *
      ((((n * (1 + 2 * K * (ν - 1)) : ℕ) : ℚ) /
        ((A - k + 1 : ℕ) : ℚ)) ^ d) := by
  classical
  let toRoot : {P // P ∈ S} → BoundedSolution Q (k - 1) := fun P ↦
    ⟨⟨P.1, by
      rw [Polynomial.mem_degreeLT]
      simpa [Nat.sub_add_cancel hk] using (haccept P.1 P.2).1⟩, hsol P.1 P.2⟩
  let roots : Finset (BoundedSolution Q (k - 1)) := S.attach.image toRoot
  have htoRoot : Function.Injective toRoot := by
    intro left right heq
    apply Subtype.ext
    exact congrArg BoundedSolution.polynomial heq
  have hcard : roots.card = S.card := by
    change (S.attach.image toRoot).card = S.card
    rw [Finset.card_image_of_injective _ htoRoot, Finset.card_attach]
  have hroots : ∀ solution ∈ roots,
      IsAgreementSolution domain received k A solution.polynomial := by
    intro solution hsolution
    change solution ∈ S.attach.image toRoot at hsolution
    rcases Finset.mem_image.mp hsolution with ⟨source, _hsource, rfl⟩
    exact haccept source.1 source.2
  have hcount := boundedSolution_card_le_sq_totalJetDegree_charZero Q hQ K k ν hK hkK
    domain received hk hkA hAn hdegreeQ hbin roots hroots
  rw [hcard] at hcount
  exact hcount

end

end ReedSolomon.HiddenDerivative

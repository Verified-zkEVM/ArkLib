/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
  ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.FiniteField.RecursiveCounting
public import
  ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.Counting.TotalJetDegreeRootCount
public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.Geometry.RegularCounting
/-!
# Rational counting through the singular separant recursion

This file accumulates a rational cardinality bound for the regular solutions at every stage of
the canonical singular recursion.  Using total jet degree as the decreasing potential loses only
one factor of the initial total jet degree, which is the form needed by the agreement-sensitive
Taylor count.
-/

@[expose] public section

open PolynomialDifferential


namespace ReedSolomon.HiddenDerivative

noncomputable section

open Polynomial

variable {F : Type*} {d D : ℕ} [Field F]

/-- Restricting an equation to a jet prefix preserves total jet degree. -/
theorem jetTotalDegree_rename_jetPrefixEmbedding (s : Fin (d + 1))
    (Q : DifferentialPolynomial F s.val) :
    jetTotalDegree (MvPolynomial.rename (jetPrefixEmbedding s) Q) = jetTotalDegree Q := by
  classical
  unfold jetTotalDegree MvPolynomial.weightedTotalDegree
  rw [MvPolynomial.support_rename_of_injective (jetPrefixEmbedding s).injective,
    Finset.sup_image]
  congr 1
  funext u
  simp only [Function.comp_apply, Finsupp.weight_apply]
  rw [Finsupp.sum_mapDomain_index (by intro v; simp) (by intro v a b; simp [add_mul])]
  congr 1
  funext v n
  cases v <;> rfl

/-- Total jet degree cannot increase down the singular separant chain. -/
theorem jetTotalDegree_le_of_reflTransGen_singularStep
    {descendant root : DifferentialPolynomial F d}
    (hreaches : Relation.ReflTransGen (SingularStep (F := F) (d := d)) descendant root) :
    jetTotalDegree descendant ≤ jetTotalDegree root := by
  induction hreaches using Relation.ReflTransGen.trans_induction_on with
  | refl _ => exact le_rfl
  | single hstep =>
      obtain ⟨s, _hs, _hchar, rfl⟩ := hstep
      exact (separant_total_le _ s).trans (Nat.sub_le _ _)
  | trans _ _ ihleft ihveryright => exact ihleft.trans ihveryright

/-- The degree and agreement predicate retained while the equation changes along the singular
separant chain. -/
def IsAgreementSolution {n : ℕ} (domain : Fin n ↪ F) (received : Fin n → F)
    (k A : ℕ) (P : F[X]) : Prop := by
  classical
  exact P.degree < k ∧
    A ≤ (Finset.univ.filter fun i ↦ P.eval (domain i) = received i).card

/-- The `Option.elim` spelling of total jet degree used by the Taylor geometry API. -/
theorem jetTotalDegree_eq_weightedTotalDegree_elim (Q : DifferentialPolynomial F d) :
    jetTotalDegree Q =
      Q.weightedTotalDegree (fun i ↦ i.elim (0 : ℕ) (fun _ ↦ 1)) := by
  unfold jetTotalDegree
  congr 2
  funext i
  cases i <;> rfl

/-- A rational cardinality budget for every regular branch below `root`, restricted to solutions
satisfying a predicate that is unchanged when the equation moves down the separant chain. -/
def RegularBranchRatBudget (root : DifferentialPolynomial F d) (D : ℕ)
    (accepts : F[X] → Prop) (cost : ℚ) : Prop :=
  ∀ (current : DifferentialPolynomial F d) (s : Fin (d + 1)),
    Relation.ReflTransGen (SingularStep (F := F) (d := d)) current root →
      highestActiveJet current = some s →
        IsBelowCharacteristic D current →
          ∀ regular : Finset (BoundedSolution current D),
            (∀ solution ∈ regular, accepts solution.polynomial) →
            (∀ solution ∈ regular,
              differentialSpecialization (separant current s) solution.polynomial ≠ 0) →
              (regular.card : ℚ) ≤ cost

/-- Rational regular-branch bounds accumulate by at most the initial total jet degree. -/
theorem boundedSolution_recursive_counting_totalJetDegree
    (Q : DifferentialPolynomial F d) (hQ : Q ≠ 0) (hchar : IsBelowCharacteristic D Q)
    (accepts : F[X] → Prop) (cost : ℚ) (hcost : 0 ≤ cost)
    (roots : Finset (BoundedSolution Q D))
    (hroots : ∀ solution ∈ roots, accepts solution.polynomial)
    (hRegular : RegularBranchRatBudget Q D accepts cost) :
    (roots.card : ℚ) ≤ (jetTotalDegree Q : ℚ) * cost := by
  classical
  let motive := fun current : DifferentialPolynomial F d ↦
    Relation.ReflTransGen (SingularStep (F := F) (d := d)) current Q →
      current ≠ 0 →
        IsBelowCharacteristic D current →
          ∀ currentRoots : Finset (BoundedSolution current D),
            (∀ solution ∈ currentRoots, accepts solution.polynomial) →
            (currentRoots.card : ℚ) ≤ (jetTotalDegree current : ℚ) * cost
  have recurse : ∀ current, motive current := by
    intro current
    apply (singularStep_wellFounded (F := F) (d := d)).induction current
    intro equation ih hreachable hne heqChar currentRoots hcurrentAccepts
    cases hactive : highestActiveJet equation with
    | none =>
        let _ : IsEmpty (BoundedSolution equation D) :=
          isEmpty_boundedSolution_of_highestActiveJet_eq_none equation hne hactive
        have hroots : currentRoots = ∅ := by
          ext solution
          exact isEmptyElim solution
        rw [hroots]
        exact mul_nonneg (Nat.cast_nonneg _) hcost
    | some s =>
        let regularRoots := regularSolutions equation s D currentRoots
        let singularRoots := singularSolutions equation s D currentRoots
        let nextRoots := singularDescendants equation s D currentRoots
        have hstep : SingularStep (separant equation s) equation :=
          singularStep_separant equation s hactive (heqChar.2 s)
        have hnextContract := singularStep_preserves_contract heqChar hstep
        have hregular : (regularRoots.card : ℚ) ≤ cost := by
          apply hRegular equation s hreachable hactive heqChar regularRoots
          · intro solution hsolution
            apply hcurrentAccepts solution
            exact (Finset.mem_filter.mp (show
              solution ∈ currentRoots.filter fun candidate ↦
                differentialSpecialization (separant equation s) candidate.polynomial ≠ 0 by
              simpa [regularRoots, regularSolutions] using hsolution)).1
          · intro solution hsolution
            exact (Finset.mem_filter.mp (show
              solution ∈ currentRoots.filter fun candidate ↦
                differentialSpecialization (separant equation s) candidate.polynomial ≠ 0 by
              simpa [regularRoots, regularSolutions] using hsolution)).2
        have hnextAccepts : ∀ solution ∈ nextRoots, accepts solution.polynomial := by
          intro solution hsolution
          change solution ∈ singularDescendants equation s D currentRoots at hsolution
          unfold singularDescendants at hsolution
          rcases Finset.mem_image.mp hsolution with ⟨source, _hsource, heq⟩
          rw [← heq]
          apply hcurrentAccepts source.1
          exact (Finset.mem_filter.mp source.2).1
        have hnext : (nextRoots.card : ℚ) ≤
            (jetTotalDegree (separant equation s) : ℚ) * cost := by
          exact ih (separant equation s) hstep
            (Relation.ReflTransGen.head hstep hreachable) hnextContract.1 hnextContract.2 nextRoots
            hnextAccepts
        have hsingular : (singularRoots.card : ℚ) ≤
            (jetTotalDegree (separant equation s) : ℚ) * cost := by
          rw [← card_singularDescendants equation s D currentRoots]
          exact hnext
        have hpartition : regularRoots.card + singularRoots.card = currentRoots.card :=
          card_regular_add_card_singular equation s D currentRoots
        have hactiveDegree : 0 < jetDegree equation s :=
          (isHighestActiveJet_of_highestActiveJet_eq_some hactive).1
        have htotalPos : 0 < jetTotalDegree equation :=
          hactiveDegree.trans_le
            (jetDegree_le_total equation s)
        have hmeasure : jetTotalDegree (separant equation s) + 1 ≤
            jetTotalDegree equation := by
          have := separant_total_le equation s
          omega
        calc
          (currentRoots.card : ℚ) =
              (regularRoots.card : ℚ) + (singularRoots.card : ℚ) := by
            exact_mod_cast hpartition.symm
          _ ≤ cost + (jetTotalDegree (separant equation s) : ℚ) * cost :=
            add_le_add hregular hsingular
          _ = ((jetTotalDegree (separant equation s) + 1 : ℕ) : ℚ) * cost := by
            push_cast
            ring
          _ ≤ (jetTotalDegree equation : ℚ) * cost := by
            exact mul_le_mul_of_nonneg_right (by exact_mod_cast hmeasure) hcost
  exact recurse Q Relation.ReflTransGen.refl hQ hchar roots hroots

/-- Agreement-sensitive Taylor counting supplies a uniform budget for every regular branch of
the singular recursion.  The equation is restricted to its actual highest active jet before the
regular theorem is applied. -/
theorem regularBranchRatBudget_of_agreement
    (Q : DifferentialPolynomial F d) (D K k ν : ℕ) (hK : d < K) (hkK : k ≤ K)
    {n A : ℕ} (domain : Fin n ↪ F) (received : Fin n → F)
    (hk : 0 < k) (hkA : k ≤ A) (hAn : A ≤ n)
    (hdegree : jetTotalDegree Q ≤ ν)
    (hbin : ∀ r, r ≤ d → ∀ i, r < i → i < K → (i.choose r : F) ≠ 0) :
    RegularBranchRatBudget Q D (IsAgreementSolution domain received k A)
      ((ν : ℚ) *
        ((((n * (1 + 2 * K * (ν - 1)) : ℕ) : ℚ) /
          ((A - k + 1 : ℕ) : ℚ)) ^ d)) := by
  classical
  intro current s hreachable hhighest _hcurrentChar regular haccepts hseparant
  obtain ⟨Q', hQ'⟩ := exists_prefixDifferentialPolynomial current s
    (isHighestActiveJet_of_highestActiveJet_eq_some hhighest)
  let polys : Finset F[X] := regular.image fun solution ↦ solution.polynomial
  have hinjective : Function.Injective (fun solution : BoundedSolution current D ↦
      solution.polynomial) := by
    intro left right heq
    exact Subtype.ext (Subtype.ext heq)
  have hcard : polys.card = regular.card := by
    exact Finset.card_image_of_injective regular hinjective
  have hsle : s.val ≤ d := Nat.le_of_lt_succ s.isLt
  have hcurrentDegree : jetTotalDegree current ≤ ν :=
    (jetTotalDegree_le_of_reflTransGen_singularStep hreachable).trans hdegree
  have hQ'Degree : jetTotalDegree Q' ≤ ν := by
    rw [← jetTotalDegree_rename_jetPrefixEmbedding s Q', hQ']
    exact hcurrentDegree
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
  rw [hcard] at hstage
  rw [← jetTotalDegree_eq_weightedTotalDegree_elim] at hstage
  have hB : rationalTaylorCutDegreeBound Q' K ≤ 1 + 2 * K * (ν - 1) := by
    unfold rationalTaylorCutDegreeBound
    gcongr
    rw [← jetTotalDegree_eq_weightedTotalDegree_elim]
    exact hQ'Degree
  have hden : 0 < (A - k + 1 : ℕ) := by omega
  have hbase :
      ((((n * rationalTaylorCutDegreeBound Q' K : ℕ) : ℚ) /
          ((A - k + 1 : ℕ) : ℚ))) ≤
        ((((n * (1 + 2 * K * (ν - 1)) : ℕ) : ℚ) /
          ((A - k + 1 : ℕ) : ℚ))) := by
    gcongr
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
    (regular.card : ℚ) ≤
        (jetTotalDegree Q' : ℚ) *
          ((((n * rationalTaylorCutDegreeBound Q' K : ℕ) : ℚ) /
            ((A - k + 1 : ℕ) : ℚ)) ^ s.val) := hstage
    _ ≤ (ν : ℚ) *
          ((((n * (1 + 2 * K * (ν - 1)) : ℕ) : ℚ) /
            ((A - k + 1 : ℕ) : ℚ)) ^ s.val) := by
      gcongr
    _ ≤ (ν : ℚ) *
          ((((n * (1 + 2 * K * (ν - 1)) : ℕ) : ℚ) /
            ((A - k + 1 : ℕ) : ℚ)) ^ d) := by
      gcongr

/-- If every regular branch has cost `ν * R ^ d`, an equation of total jet degree at most `ν`
has at most `ν ^ 2 * R ^ d` solutions in any finite family. -/
theorem boundedSolution_card_le_sq_totalJetDegree
    (Q : DifferentialPolynomial F d) (hQ : Q ≠ 0) (hchar : IsBelowCharacteristic D Q)
    (accepts : F[X] → Prop) (ν : ℕ) (R : ℚ) (hR : 0 ≤ R)
    (roots : Finset (BoundedSolution Q D))
    (hroots : ∀ solution ∈ roots, accepts solution.polynomial)
    (hdegree : jetTotalDegree Q ≤ ν)
    (hRegular : RegularBranchRatBudget Q D accepts ((ν : ℚ) * R ^ d)) :
    (roots.card : ℚ) ≤ (ν : ℚ) ^ 2 * R ^ d := by
  have hcost : 0 ≤ (ν : ℚ) * R ^ d :=
    mul_nonneg (Nat.cast_nonneg ν) (pow_nonneg hR d)
  calc
    (roots.card : ℚ) ≤ (jetTotalDegree Q : ℚ) * ((ν : ℚ) * R ^ d) :=
      boundedSolution_recursive_counting_totalJetDegree Q hQ hchar accepts _ hcost roots hroots
        hRegular
    _ ≤ (ν : ℚ) * ((ν : ℚ) * R ^ d) := by
      gcongr
    _ = (ν : ℚ) ^ 2 * R ^ d := by ring

/-- All degree-`< k` solutions with at least `A` agreements obey the square-total-degree bound.
The explicit characteristic contract is the one needed to keep every singular separant nonzero. -/
theorem finite_agreement_solutions_card_le
    (Q : DifferentialPolynomial F d) (K k ν : ℕ) (hK : d < K) (hkK : k ≤ K)
    (hQ : Q ≠ 0) (hchar : IsBelowCharacteristic (k - 1) Q)
    (hdegreeQ : jetTotalDegree Q ≤ ν)
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
  let R : ℚ :=
    ((n * (1 + 2 * K * (ν - 1)) : ℕ) : ℚ) / ((A - k + 1 : ℕ) : ℚ)
  have hR : 0 ≤ R := by unfold R; positivity
  have hRegular : RegularBranchRatBudget Q (k - 1)
      (IsAgreementSolution domain received k A) ((ν : ℚ) * R ^ d) := by
    simpa only [R] using regularBranchRatBudget_of_agreement Q (k - 1) K k ν hK hkK
      domain received hk hkA hAn hdegreeQ hbin
  have hcount := boundedSolution_card_le_sq_totalJetDegree Q hQ hchar
    (IsAgreementSolution domain received k A) ν R hR roots hroots hdegreeQ hRegular
  rw [hcard] at hcount
  exact hcount

end

end ReedSolomon.HiddenDerivative

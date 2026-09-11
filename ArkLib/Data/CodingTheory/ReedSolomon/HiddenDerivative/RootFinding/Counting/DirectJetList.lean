/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
  ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.Geometry.DimensionSensitive
public import
  ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.Counting.TaylorAllSolutions
public import
  ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.Symbolic.SeparantChain
public import
  ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Parameters.GeometricCounting
/-!
# Direct all-order agreement lists from actual separant stages

Every differential root is assigned to a regular stage of the actual symbolic separant chain.
At a stage of current jet weight `j` and highest active order `r`, the regular Taylor chart
contributes exactly

```text
dimensionSensitiveIncidenceProduct n A k 1 r * j * (1 + 2*K*(j-1))^r.
```

The result is over an arbitrary field.  Characteristic zero, or characteristic larger than both
the Taylor cutoff and the initial jet weight, supplies the two independent scalar conditions.
-/

@[expose] public section

open PolynomialDifferential

namespace ReedSolomon.HiddenDerivative

noncomputable section

open Polynomial MvPolynomial AffineHilbert SymbolicSeparantChain
open scoped BigOperators

variable {F : Type*} [Field F] {d : ℕ}

/-- Complete degree-`< k`, agreement-`A` solution set of one differential equation. -/
def directJetAgreementSolutions {n : ℕ} (Q : DifferentialPolynomial F d)
    (domain : Fin n ↪ F) (received : Fin n → F) (k A : ℕ) : Set F[X] := by
  classical
  exact {P | differentialSpecialization Q P = 0 ∧
    IsAgreementSolution domain received k A P}

/-- The exact charge of one actual separant stage. -/
def directJetStageCharge (domainSize A k K : ℕ)
    (stage : SymbolicSeparantChain.Stage F d) : ℚ :=
  dimensionSensitiveIncidenceProduct domainSize A k 1 stage.2.val *
    (jetWeight stage.1 : ℚ) *
      (1 + 2 * K * (jetWeight stage.1 - 1) : ℕ) ^ stage.2.val

/-- The paper's common-order comparison sum, indexed by every possible positive stage weight. -/
def directJetCommonOrderSum (n A k K B d : ℕ) : ℚ :=
  ∑ j ∈ Finset.range (B + 1),
    dimensionSensitiveIncidenceProduct n A k 1 d * (j : ℚ) *
      (1 + 2 * K * (j - 1) : ℕ) ^ d

open Classical in
/-- A regular family at one actual stage obeys the current jet weight and current active-order
charge, without replacing either by a global bound. -/
theorem finite_actualStage_regularSolutions_card_le_dimensionSensitive
    (current : DifferentialPolynomial F d) (s : Fin (d + 1))
    (hhighest : highestActiveJet current = some s)
    (K k : ℕ) (hK : d < K) (hkK : k ≤ K)
    {n A : ℕ} (domain : Fin n ↪ F) (received : Fin n → F)
    (hkA : k ≤ A) (hAn : A ≤ n)
    (hbin : ∀ r, r ≤ d → ∀ i, r < i → i < K → (i.choose r : F) ≠ 0)
    (S : Finset F[X])
    (hdegree : ∀ P ∈ S, P.degree < k)
    (hsol : ∀ P ∈ S, differentialSpecialization current P = 0)
    (hsep : ∀ P ∈ S, differentialSpecialization (separant current s) P ≠ 0)
    (hagree : ∀ P ∈ S, IsAgreementSolution domain received k A P) :
    (S.card : ℚ) ≤ directJetStageCharge n A k K (current, s) := by
  classical
  obtain ⟨Q', hQ'⟩ := exists_prefixDifferentialPolynomial current s
    (isHighestActiveJet_of_highestActiveJet_eq_some hhighest)
  have hsle : s.val ≤ d := Nat.le_of_lt_succ s.isLt
  have hweight :
      Q'.weightedTotalDegree (fun i ↦ i.elim (0 : ℕ) (fun _ ↦ 1)) =
        jetWeight current := by
    rw [← jetTotalDegree_eq_weightedTotalDegree_elim,
      ← jetTotalDegree_rename_jetPrefixEmbedding s Q', hQ',
      jetTotalDegree_eq_weightedTotalDegree_elim]
    rfl
  have hv : 0 < Q'.weightedTotalDegree (fun i ↦ i.elim (0 : ℕ) (fun _ ↦ 1)) := by
    rw [hweight]
    exact (isHighestActiveJet_of_highestActiveJet_eq_some hhighest).1.trans_le
      (jetDegree_le_jetWeight current s)
  have hstage := finite_regular_solutions_card_le_dimensionSensitive
    Q' K k (hsle.trans_lt hK) hkK hv domain received hkA hAn S hdegree
    (fun P hP ↦ by
      simpa only [← hQ', differentialSpecialization_rename_jetPrefixEmbedding] using hsol P hP)
    (fun P hP ↦ by
      have heqsep :
          differentialSpecialization (separant current s) P =
            differentialSpecialization (separant Q' (Fin.last s.val)) P := by
        calc
          _ = differentialSpecialization
              (MvPolynomial.rename (jetPrefixEmbedding s)
                (separant Q' (Fin.last s.val))) P := by
              rw [← separant_rename_jetPrefixEmbedding, hQ']
          _ = _ := differentialSpecialization_rename_jetPrefixEmbedding _ _ _
      exact fun hz ↦ hsep P hP (heqsep.trans hz))
    (fun i hsi hiK ↦ hbin s.val hsle i hsi hiK)
    (fun P hP ↦ (hagree P hP).2)
  simp only [rationalTaylorCutDegreeBound, hweight] at hstage
  change (S.card : ℚ) ≤ dimensionSensitiveIncidenceProduct n A k 1 s.val *
    (jetWeight current : ℚ) *
      (1 + 2 * K * (jetWeight current - 1) : ℕ) ^ s.val
  calc
    (S.card : ℚ) ≤
      (jetWeight current : ℕ) *
        (1 + 2 * K * (jetWeight current - 1) : ℕ) ^ s.val *
          dimensionSensitiveIncidenceProduct n A k 1 s.val := hstage
    _ = _ := by ring

/-- Every finite family of accepted roots is bounded by the sum of the exact actual-stage
charges in its supplied separant chain. -/
theorem finset_card_le_directJetStageCharge_sum
    {Q terminal : DifferentialPolynomial F d}
    {stages : List (SymbolicSeparantChain.Stage F d)}
    (hchain : SymbolicSeparantChain.Chain Q stages terminal)
    (K k : ℕ) (hK : d < K) (hkK : k ≤ K)
    {n A : ℕ} (domain : Fin n ↪ F) (received : Fin n → F)
    (hkA : k ≤ A) (hAn : A ≤ n)
    (hbin : ∀ r, r ≤ d → ∀ i, r < i → i < K → (i.choose r : F) ≠ 0)
    (S : Finset F[X])
    (hS : ∀ P ∈ S, P ∈ directJetAgreementSolutions Q domain received k A) :
    (S.card : ℚ) ≤
      (stages.map (directJetStageCharge n A k K)).sum := by
  classical
  induction hchain generalizing S with
  | @terminal equation hne hterminal =>
      have hEmpty : S = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro P hP
        obtain ⟨q, hq⟩ :=
          exists_toMvPolynomial_eq_of_highestActiveJet_eq_none equation hterminal
        have hqne : q ≠ 0 := by
          intro hz
          apply hne
          rw [← hq, hz]
          simp
        apply hqne
        rw [← differentialSpecialization_toMvPolynomial (d := d) q P, hq]
        exact (hS P hP).1
      subst S
      simp
  | @active current tail terminal s hne hhighest next ih =>
      let regular := S.filter fun P ↦
        differentialSpecialization (separant current s) P ≠ 0
      let singular := S.filter fun P ↦
        ¬ differentialSpecialization (separant current s) P ≠ 0
      have hregular := finite_actualStage_regularSolutions_card_le_dimensionSensitive
        current s hhighest K k hK hkK domain received hkA hAn hbin regular
        (fun P hP ↦ (hS P (Finset.mem_filter.mp hP).1).2.1)
        (fun P hP ↦ (hS P (Finset.mem_filter.mp hP).1).1)
        (fun P hP ↦ (Finset.mem_filter.mp hP).2)
        (fun P hP ↦ (hS P (Finset.mem_filter.mp hP).1).2)
      have hsingularAccept :
          ∀ P ∈ singular, P ∈ directJetAgreementSolutions (separant current s)
            domain received k A := by
        intro P hP
        have hm := Finset.mem_filter.mp hP
        exact ⟨not_ne_iff.mp hm.2, (hS P hm.1).2⟩
      have hsingular := ih singular hsingularAccept
      have hpartition : regular.card + singular.card = S.card := by
        exact Finset.card_filter_add_card_filter_not
          (s := S) (p := fun P ↦ differentialSpecialization (separant current s) P ≠ 0)
      simp only [List.map_cons, List.sum_cons]
      calc
        (S.card : ℚ) = (regular.card : ℚ) + (singular.card : ℚ) := by
          exact_mod_cast hpartition.symm
        _ ≤ directJetStageCharge n A k K (current, s) +
            (tail.map (directJetStageCharge n A k K)).sum :=
          add_le_add hregular hsingular

/-- The complete solution set is finite and satisfies the exact actual-stage sum. -/
theorem directJetAgreementSolutions_finite_and_ncard_le_chain
    {Q terminal : DifferentialPolynomial F d}
    {stages : List (SymbolicSeparantChain.Stage F d)}
    (hchain : SymbolicSeparantChain.Chain Q stages terminal)
    (K k : ℕ) (hK : d < K) (hkK : k ≤ K)
    {n A : ℕ} (domain : Fin n ↪ F) (received : Fin n → F)
    (hkA : k ≤ A) (hAn : A ≤ n)
    (hbin : ∀ r, r ≤ d → ∀ i, r < i → i < K → (i.choose r : F) ≠ 0) :
    (directJetAgreementSolutions Q domain received k A).Finite ∧
      ((directJetAgreementSolutions Q domain received k A).ncard : ℚ) ≤
        (stages.map (directJetStageCharge n A k K)).sum := by
  classical
  let T := directJetAgreementSolutions Q domain received k A
  have hbound (S : Finset F[X]) (hST : (S : Set F[X]) ⊆ T) :
      (S.card : ℚ) ≤ (stages.map (directJetStageCharge n A k K)).sum :=
    finset_card_le_directJetStageCharge_sum hchain K k hK hkK domain received
      hkA hAn hbin S (fun P hP ↦ hST hP)
  have hfinite : T.Finite := Set.finite_of_forall_finset_card_le hbound
  refine ⟨hfinite, ?_⟩
  rw [Set.ncard_eq_toFinset_card T hfinite]
  exact hbound hfinite.toFinset (fun _ h ↦ hfinite.mem_toFinset.mp h)

/-- The exact actual-stage sum is bounded by the common-order sum over all possible stage
weights.  Strict descent of `jetWeight` ensures that no weight is charged twice. -/
theorem directJetStageCharge_sum_le_commonOrderSum
    {Q terminal : DifferentialPolynomial F d}
    {stages : List (SymbolicSeparantChain.Stage F d)}
    (hchain : SymbolicSeparantChain.Chain Q stages terminal)
    (n A k K B : ℕ) (hAn : A ≤ n) (hweight : jetWeight Q ≤ B) :
    (stages.map (directJetStageCharge n A k K)).sum ≤
      directJetCommonOrderSum n A k K B d := by
  classical
  let f : ℕ → ℚ := fun j ↦
    dimensionSensitiveIncidenceProduct n A k 1 d * (j : ℚ) *
      (1 + 2 * K * (j - 1) : ℕ) ^ d
  have hpoint : ∀ stage ∈ stages, directJetStageCharge n A k K stage ≤
      f (jetWeight stage.1) := by
    intro stage hstage
    have hc := hchain.stage_contract stage hstage
    have hr : stage.2.val ≤ d := Nat.le_of_lt_succ stage.2.isLt
    have hp := dimensionSensitiveIncidenceProduct_mono_dimension
      n A k 1 stage.2.val d hAn Nat.zero_lt_one hr
    have hb : (1 : ℚ) ≤ (1 + 2 * K * (jetWeight stage.1 - 1) : ℕ) := by
      exact_mod_cast (Nat.le_add_right 1 _)
    dsimp only [directJetStageCharge, f]
    calc
      dimensionSensitiveIncidenceProduct n A k 1 stage.2.val *
          (jetWeight stage.1 : ℚ) *
            (1 + 2 * K * (jetWeight stage.1 - 1) : ℕ) ^ stage.2.val ≤
        dimensionSensitiveIncidenceProduct n A k 1 d *
          (jetWeight stage.1 : ℚ) *
            (1 + 2 * K * (jetWeight stage.1 - 1) : ℕ) ^ stage.2.val := by
          gcongr
      _ ≤ dimensionSensitiveIncidenceProduct n A k 1 d *
          (jetWeight stage.1 : ℚ) *
            (1 + 2 * K * (jetWeight stage.1 - 1) : ℕ) ^ d := by
          gcongr
          exact mul_nonneg (dimensionSensitiveIncidenceProduct_nonneg n A k 1 d)
            (Nat.cast_nonneg _)
  have hstageSum : (stages.map (directJetStageCharge n A k K)).sum ≤
      (stages.map fun stage ↦ f (jetWeight stage.1)).sum :=
    List.sum_le_sum hpoint
  let weights := stages.map fun stage ↦ jetWeight stage.1
  have hweightsPairwise : weights.Pairwise (· > ·) := by
    dsimp only [weights]
    rw [List.pairwise_map]
    exact hchain.ordered_stage_metadata.imp fun h ↦ h.1
  have hweightsNodup : weights.Nodup := hweightsPairwise.nodup
  have hweightsSubset : weights.toFinset ⊆ Finset.range (B + 1) := by
    intro j hj
    rw [List.mem_toFinset] at hj
    obtain ⟨stage, hstage, rfl⟩ := List.mem_map.mp hj
    rw [Finset.mem_range]
    exact Nat.lt_succ_of_le ((hchain.stage_contract stage hstage).2.2.1.trans hweight)
  calc
    (stages.map (directJetStageCharge n A k K)).sum ≤
        (stages.map fun stage ↦ f (jetWeight stage.1)).sum := hstageSum
    _ = (weights.map f).sum := by simp [weights, List.map_map, Function.comp_def]
    _ = ∑ j ∈ weights.toFinset, f j := (List.sum_toFinset f hweightsNodup).symm
    _ ≤ ∑ j ∈ Finset.range (B + 1), f j :=
      Finset.sum_le_sum_of_subset_of_nonneg hweightsSubset (fun _ _ _ ↦ by
        dsimp only [f]
        exact mul_nonneg
          (mul_nonneg (dimensionSensitiveIncidenceProduct_nonneg n A k 1 d)
            (Nat.cast_nonneg _)) (by positivity))
    _ = directJetCommonOrderSum n A k K B d := by
      simp only [directJetCommonOrderSum, f]

/-- The common-order sum implies the earlier square-jet-weight coarse bound. -/
theorem directJetCommonOrderSum_le_coarse
    (n A k K B d : ℕ) (hk : 0 < k) (hkA : k ≤ A) (hAn : A ≤ n) :
    directJetCommonOrderSum n A k K B d ≤
      (B : ℚ) ^ 2 *
        ((((n * (1 + 2 * K * (B - 1)) : ℕ) : ℚ) /
          ((A - k + 1 : ℕ) : ℚ)) ^ d) := by
  let P := dimensionSensitiveIncidenceProduct n A k 1 d
  let b := 1 + 2 * K * (B - 1)
  let R : ℚ := ((n * b : ℕ) : ℚ) / ((A - k + 1 : ℕ) : ℚ)
  have hterm : ∀ i ∈ Finset.range B,
      P * ((i + 1 : ℕ) : ℚ) * (1 + 2 * K * ((i + 1) - 1) : ℕ) ^ d ≤
        P * (B : ℚ) * (b : ℚ) ^ d := by
    intro i hi
    have hiB : i + 1 ≤ B := Nat.succ_le_iff.mpr (by
      simpa only [Finset.mem_range] using hi)
    have hiPred : i ≤ B - 1 := by omega
    have hbase : 1 + 2 * K * ((i + 1) - 1) ≤ b := by
      dsimp only [b]
      rw [show (i + 1 : ℕ) - 1 = i by omega]
      exact Nat.add_le_add_left (Nat.mul_le_mul_left (2 * K) hiPred) 1
    dsimp only [P]
    gcongr
    · exact mul_nonneg (dimensionSensitiveIncidenceProduct_nonneg n A k 1 d)
        (Nat.cast_nonneg _)
    · exact dimensionSensitiveIncidenceProduct_nonneg n A k 1 d
  have hproduct := dimensionSensitiveIncidenceProduct_le_first_pow
    n A k d hkA hAn
  have hratio : ((n - k + 1 : ℕ) : ℚ) / ((A - k + 1 : ℕ) : ℚ) ≤
      (n : ℚ) / ((A - k + 1 : ℕ) : ℚ) := by
    gcongr
    exact_mod_cast (show n - k + 1 ≤ n by omega)
  have hproductN : P ≤ (((n : ℚ) / ((A - k + 1 : ℕ) : ℚ)) ^ d) :=
    hproduct.trans (pow_le_pow_left₀ (by positivity) hratio d)
  have hR : R = (b : ℚ) * ((n : ℚ) / ((A - k + 1 : ℕ) : ℚ)) := by
    dsimp only [R]
    push_cast
    ring
  calc
    directJetCommonOrderSum n A k K B d =
        ∑ i ∈ Finset.range B,
          P * ((i + 1 : ℕ) : ℚ) *
            (1 + 2 * K * ((i + 1) - 1) : ℕ) ^ d := by
      rw [directJetCommonOrderSum, Finset.sum_range_succ']
      simp only [Nat.cast_zero, mul_zero, zero_mul, add_zero, P]
    _ ≤ ∑ _i ∈ Finset.range B, P * (B : ℚ) * (b : ℚ) ^ d :=
      Finset.sum_le_sum hterm
    _ = (B : ℚ) * (P * (B : ℚ) * (b : ℚ) ^ d) := by simp
    _ = (B : ℚ) ^ 2 * (b : ℚ) ^ d * P := by ring
    _ ≤ (B : ℚ) ^ 2 * (b : ℚ) ^ d *
        (((n : ℚ) / ((A - k + 1 : ℕ) : ℚ)) ^ d) := by
      exact mul_le_mul_of_nonneg_left hproductN
        (mul_nonneg (by positivity) (by positivity))
    _ = (B : ℚ) ^ 2 * R ^ d := by
      rw [hR, mul_pow]
      ring
    _ = _ := by rfl

/-- Characteristic zero or characteristic larger than `max (K-1) (jetWeight Q)` produces an
actual chain and the direct finite-list bound on that chain. -/
theorem exists_chain_directJetAgreementSolutions_finite_and_ncard_le
    (Q : DifferentialPolynomial F d) (hQ : Q ≠ 0)
    (K k : ℕ) (hK : d < K) (hkK : k ≤ K)
    {n A : ℕ} (domain : Fin n ↪ F) (received : Fin n → F)
    (hkA : k ≤ A) (hAn : A ≤ n)
    (hchar : ringChar F = 0 ∨ max (K - 1) (jetWeight Q) < ringChar F) :
    ∃ stages terminal, SymbolicSeparantChain.Chain Q stages terminal ∧
      (directJetAgreementSolutions Q domain received k A).Finite ∧
      ((directJetAgreementSolutions Q domain received k A).ncard : ℚ) ≤
        (stages.map (directJetStageCharge n A k K)).sum := by
  have hchainChar : ringChar F = 0 ∨ jetWeight Q < ringChar F :=
    hchar.imp_right (fun h ↦ (Nat.le_max_right (K - 1) (jetWeight Q)).trans_lt h)
  have hTaylorChar : ringChar F = 0 ∨ K ≤ ringChar F := by
    apply hchar.imp_right
    intro h
    have : K - 1 < ringChar F :=
      (Nat.le_max_left (K - 1) (jetWeight Q)).trans_lt h
    omega
  obtain ⟨stages, terminal, hchain⟩ : ∃ stages terminal,
      SymbolicSeparantChain.Chain Q stages terminal := by
    rcases hchainChar with hzero | hpositive
    · let _ : CharP F 0 := hzero ▸ inferInstanceAs (CharP F (ringChar F))
      let _ : CharZero F := CharP.charP_to_charZero F
      exact SymbolicSeparantChain.exists_chain_charZero Q hQ
    · exact SymbolicSeparantChain.exists_chain_of_lt_ringChar Q hQ hpositive
  have hbin := ReedSolomon.HiddenDerivative.binomial_pivots_of_characteristic
    (F := F) hTaylorChar
  obtain ⟨hfinite, hbound⟩ :=
    directJetAgreementSolutions_finite_and_ncard_le_chain hchain K k hK hkK
      domain received hkA hAn (fun r _ ↦ hbin r)
  exact ⟨stages, terminal, hchain, hfinite, hbound⟩

/-- Direct-jet-list theorem in the paper's parameterization.  The witness exposes the actual
separant stages, followed by the exact-stage, common-order, and legacy coarse inequalities. -/
theorem exists_directJetList_actualStages_and_bounds
    (Q : DifferentialPolynomial F d) (hQ : Q ≠ 0)
    (K k B : ℕ) (hK : d < K) (hk : 0 < k) (hkK : k ≤ K)
    (hweight : jetWeight Q ≤ B)
    {n A : ℕ} (domain : Fin n ↪ F) (received : Fin n → F)
    (hkA : k ≤ A) (hAn : A ≤ n)
    (hchar : ringChar F = 0 ∨ max (K - 1) B < ringChar F) :
    ∃ stages terminal, SymbolicSeparantChain.Chain Q stages terminal ∧
      (directJetAgreementSolutions Q domain received k A).Finite ∧
      ((directJetAgreementSolutions Q domain received k A).ncard : ℚ) ≤
        (stages.map (directJetStageCharge n A k K)).sum ∧
      (stages.map (directJetStageCharge n A k K)).sum ≤
        directJetCommonOrderSum n A k K B d ∧
      directJetCommonOrderSum n A k K B d ≤
        (B : ℚ) ^ 2 *
          ((((n * (1 + 2 * K * (B - 1)) : ℕ) : ℚ) /
            ((A - k + 1 : ℕ) : ℚ)) ^ d) := by
  have hchar' : ringChar F = 0 ∨
      max (K - 1) (jetWeight Q) < ringChar F := by
    apply hchar.imp_right
    intro h
    exact max_lt
      ((Nat.le_max_left (K - 1) B).trans_lt h)
      (hweight.trans_lt ((Nat.le_max_right (K - 1) B).trans_lt h))
  obtain ⟨stages, terminal, hchain, hfinite, hactual⟩ :=
    exists_chain_directJetAgreementSolutions_finite_and_ncard_le
      Q hQ K k hK hkK domain received hkA hAn hchar'
  have hcommon := directJetStageCharge_sum_le_commonOrderSum
    hchain n A k K B hAn hweight
  have hcoarse := directJetCommonOrderSum_le_coarse n A k K B d hk hkA hAn
  exact ⟨stages, terminal, hchain, hfinite, hactual, hcommon, hcoarse⟩

/-- Compatibility projection of the direct theorem to the earlier coarse bound. -/
theorem directJetAgreementSolutions_finite_and_ncard_le_coarse
    (Q : DifferentialPolynomial F d) (hQ : Q ≠ 0)
    (K k B : ℕ) (hK : d < K) (hk : 0 < k) (hkK : k ≤ K)
    (hweight : jetWeight Q ≤ B)
    {n A : ℕ} (domain : Fin n ↪ F) (received : Fin n → F)
    (hkA : k ≤ A) (hAn : A ≤ n)
    (hchar : ringChar F = 0 ∨ max (K - 1) B < ringChar F) :
    (directJetAgreementSolutions Q domain received k A).Finite ∧
      ((directJetAgreementSolutions Q domain received k A).ncard : ℚ) ≤
        (B : ℚ) ^ 2 *
          ((((n * (1 + 2 * K * (B - 1)) : ℕ) : ℚ) /
            ((A - k + 1 : ℕ) : ℚ)) ^ d) := by
  obtain ⟨_stages, _terminal, _hchain, hfinite, hactual, hcommon, hcoarse⟩ :=
    exists_directJetList_actualStages_and_bounds Q hQ K k B hK hk hkK hweight
      domain received hkA hAn hchar
  exact ⟨hfinite, hactual.trans (hcommon.trans hcoarse)⟩

end

end ReedSolomon.HiddenDerivative

/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen
-/

import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.BadEventsProb.FiniteTarget
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.BadEventsProb.SampleProduct
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.BadEventsProb.PermTraceFacts
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.BadEventsProb.PermCausality

/-!
# No-replacement bounds for a uniform permutation

This is the finite counting core of the eager-sponge `E_p` / `E_{p^{-1}}` proof.  A prefix may
have exposed a finite set `X` of full permutation states.  The next unseen image is uniform over
the complement of `X`, not over the entire state space.  If every state in `X` has a capacity in
the target set `T`, removing `X` only *decreases* the fraction of remaining states whose capacity
is a target:

`(|T| - |X|) / (|A| - |X|) ≤ |T| / |A|`.

The permutation theorem below expresses the group-action half of this argument.  It is deliberately
generic over full states; the sponge specialization will take `T` to the union of capacity fibers.
-/

open OracleComp OracleSpec ProtocolSpec

open scoped ENNReal

namespace DuplexSpongeFS

namespace BadEventDS

/-- Rearranging a product with a common ENNReal denominator.  Keeping this explicit avoids
opaque normalization in the no-replacement counting calculations. -/
lemma mul_div_swap (a b c : ℝ≥0∞) : a * (b / c) = b * (a / c) := by
  rw [ENNReal.div_eq_inv_mul, ENNReal.div_eq_inv_mul]
  calc
    a * (c⁻¹ * b) = c⁻¹ * (a * b) := mul_left_comm _ _ _
    _ = c⁻¹ * (b * a) :=
      congrArg (fun z : ℝ≥0∞ => c⁻¹ * z) (mul_comm _ _)
    _ = b * (c⁻¹ * a) := mul_left_comm _ _ _

/-- Elementary no-replacement arithmetic.  If the excluded states `X` are among the target
states `T`, the target fraction cannot increase after excluding `X`. -/
lemma noReplacement_fraction_le
    {α : Type} [Fintype α] [DecidableEq α]
    (X T : Finset α) (hXT : X ⊆ T)
    (hproper : X.card < Fintype.card α) :
    ((T \ X).card : ℝ≥0∞) / ((Finset.univ \ X).card : ℝ≥0∞)
      ≤ (T.card : ℝ≥0∞) / (Fintype.card α : ℝ≥0∞) := by
  have hT : T.card ≤ Fintype.card α := by
    rw [← Finset.card_univ]
    exact Finset.card_le_card (Finset.subset_univ T)
  have hX : X.card ≤ T.card := Finset.card_le_card hXT
  have hcardpos : 0 < Fintype.card α :=
    lt_of_le_of_lt (Nat.zero_le X.card) hproper
  have hXN : X.card * T.card ≤ X.card * Fintype.card α :=
    Nat.mul_le_mul_left X.card hT
  have hmul : (T.card - X.card) * Fintype.card α
      ≤ T.card * (Fintype.card α - X.card) := by
    calc
      (T.card - X.card) * Fintype.card α =
          T.card * Fintype.card α - X.card * Fintype.card α :=
            Nat.sub_mul _ _ _
      _ ≤ T.card * Fintype.card α - X.card * T.card :=
            Nat.sub_le_sub_left hXN _
      _ = T.card * Fintype.card α - T.card * X.card := by
            rw [Nat.mul_comm X.card T.card]
      _ = T.card * (Fintype.card α - X.card) := by
            rw [Nat.mul_sub_left_distrib]
  rw [Finset.card_sdiff_of_subset hXT]
  rw [Finset.card_sdiff_of_subset (Finset.subset_univ X)]
  rw [Finset.card_univ]
  rw [ENNReal.div_le_iff_le_mul]
  · rw [show (T.card : ℝ≥0∞) / Fintype.card α *
        ((Fintype.card α - X.card : ℕ) : ℝ≥0∞) =
        ((T.card : ℝ≥0∞) * (Fintype.card α - X.card : ℝ≥0∞)) /
          Fintype.card α by
          rw [← ENNReal.natCast_sub]
          rw [div_eq_mul_inv, div_eq_mul_inv]
          ac_rfl]
    rw [ENNReal.le_div_iff_mul_le]
    · exact_mod_cast hmul
    · left
      norm_cast
      exact Nat.ne_of_gt hcardpos
    · exact Or.inl ENNReal.coe_ne_top
  · left
    norm_cast
    exact Nat.ne_of_gt (Nat.sub_pos_of_lt hproper)
  · exact Or.inl ENNReal.coe_ne_top

/-- One-way restricted-swap freshness.  For the no-replacement count, it is enough that every
accepted output can be moved to every unexposed state; reverse invariance is unnecessary. -/
lemma probEvent_uniformPerm_freshApply_eq_le_of_exposed_step
    {α : Type} [Fintype α] [DecidableEq α] [Nonempty α]
    [SampleableType (Equiv.Perm α)]
    (P : Equiv.Perm α → Prop) (x : α) (X : Finset α) (y : α)
    (hstep : ∀ (p : Equiv.Perm α) (y' : α), y' ∉ X → P p →
      P (p.trans (Equiv.swap (p x) y')))
    (hproper : X.card < Fintype.card α) :
    Pr[ fun p : Equiv.Perm α => P p ∧ p x = y | ($ᵗ (Equiv.Perm α)) ]
      ≤ Pr[ fun p : Equiv.Perm α => P p | ($ᵗ (Equiv.Perm α)) ]
        / ((Finset.univ \ X).card : ℝ≥0∞) := by
  classical
  have hle : ∀ y' : α, y' ∉ X →
      Pr[ fun p : Equiv.Perm α => P p ∧ p x = y | ($ᵗ (Equiv.Perm α)) ]
        ≤ Pr[ fun p : Equiv.Perm α => P p ∧ p x = y' | ($ᵗ (Equiv.Perm α)) ] := by
    intro y' hy'X
    let e : α ≃ α := Equiv.swap y y'
    let T : Equiv.Perm α ≃ Equiv.Perm α :=
      { toFun := fun p => p.trans e
        invFun := fun p => p.trans e.symm
        left_inv := by
          intro p
          ext a
          simp [e]
        right_inv := by
          intro p
          ext a
          simp [e] }
    calc
      Pr[ fun p : Equiv.Perm α => P p ∧ p x = y | ($ᵗ (Equiv.Perm α)) ]
        ≤ Pr[ fun p : Equiv.Perm α => P (T p) ∧ (T p) x = y' |
            ($ᵗ (Equiv.Perm α)) ] := by
          apply probEvent_mono
          intro p _hp hp
          rcases hp with ⟨hP, hpx⟩
          have hT : p.trans (Equiv.swap (p x) y') = T p := by
            ext a
            simp [T, e, hpx]
          have hP' : P (T p) := by
            rw [← hT]
            exact hstep p y' hy'X hP
          have hpx' : (T p) x = y' := by
            change (Equiv.swap y y') (p x) = y'
            rw [hpx]
            simp
          exact ⟨hP', hpx'⟩
      _ = Pr[ fun p : Equiv.Perm α => P p ∧ p x = y' |
            ($ᵗ (Equiv.Perm α)) ] :=
          (probEvent_uniformSample_equiv_invariant T
            (fun p : Equiv.Perm α => P p ∧ p x = y')).symm
  have hsum :
      ((Finset.univ \ X).card : ℝ≥0∞) *
          Pr[ fun p : Equiv.Perm α => P p ∧ p x = y | ($ᵗ (Equiv.Perm α)) ]
        ≤ Pr[ fun p : Equiv.Perm α => P p | ($ᵗ (Equiv.Perm α)) ] := by
    calc
      ((Finset.univ \ X).card : ℝ≥0∞) *
          Pr[ fun p : Equiv.Perm α => P p ∧ p x = y | ($ᵗ (Equiv.Perm α)) ]
          = ∑ _y' ∈ (Finset.univ \ X),
              Pr[ fun p : Equiv.Perm α => P p ∧ p x = y | ($ᵗ (Equiv.Perm α)) ] := by
            rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ y' ∈ (Finset.univ \ X),
              Pr[ fun p : Equiv.Perm α => P p ∧ p x = y' | ($ᵗ (Equiv.Perm α)) ] := by
            apply Finset.sum_le_sum
            intro y' hy'
            exact hle y' (Finset.mem_sdiff.mp hy').2
      _ ≤ ∑ y' : α,
              Pr[ fun p : Equiv.Perm α => P p ∧ p x = y' | ($ᵗ (Equiv.Perm α)) ] := by
            apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
            intro y' _hy' _hy''
            exact bot_le
      _ ≤ Pr[ fun p : Equiv.Perm α => P p | ($ᵗ (Equiv.Perm α)) ] :=
            sum_probEvent_and_eq_le _ P (fun p => p x)
  rw [ENNReal.le_div_iff_mul_le]
  · rw [mul_comm]
    exact hsum
  · left
    norm_cast
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ X), Finset.card_univ]
    exact Nat.ne_of_gt (Nat.sub_pos_of_lt hproper)
  · left
    exact ENNReal.coe_ne_top

/-- Finite-target no-replacement freshness from one-way restricted swap stability. -/
lemma probEvent_uniformPerm_freshApply_mem_finset_le_of_exposed_step
    {α : Type} [Fintype α] [DecidableEq α] [Nonempty α]
    [SampleableType (Equiv.Perm α)]
    (P : Equiv.Perm α → Prop) (x : α) (X T : Finset α)
    (hXT : X ⊆ T)
    (himage : ∀ p : Equiv.Perm α, P p → p x ∉ X)
    (hstep : ∀ (p : Equiv.Perm α) (y' : α), y' ∉ X → P p →
      P (p.trans (Equiv.swap (p x) y')))
    (hproper : X.card < Fintype.card α) :
    Pr[ fun p : Equiv.Perm α => P p ∧ p x ∈ T | ($ᵗ (Equiv.Perm α)) ]
      ≤ (T.card : ℝ≥0∞) *
        (Pr[ fun p : Equiv.Perm α => P p | ($ᵗ (Equiv.Perm α)) ] /
          (Fintype.card α : ℝ≥0∞)) := by
  classical
  have hEvent : (fun p : Equiv.Perm α => P p ∧ p x ∈ T) =
      fun p => ∃ y ∈ T \ X, P p ∧ p x = y := by
    funext p
    apply propext
    constructor
    · intro hp
      rcases hp with ⟨hP, hpT⟩
      exact ⟨p x, Finset.mem_sdiff.mpr ⟨hpT, himage p hP⟩, hP, rfl⟩
    · intro hp
      rcases hp with ⟨y, hy, hP, hpx⟩
      rw [hpx]
      exact ⟨hP, (Finset.mem_sdiff.mp hy).1⟩
  rw [hEvent]
  calc
    Pr[ fun p : Equiv.Perm α => ∃ y ∈ T \ X, P p ∧ p x = y |
        ($ᵗ (Equiv.Perm α)) ]
        ≤ ∑ y ∈ T \ X,
            Pr[ fun p : Equiv.Perm α => P p ∧ p x = y | ($ᵗ (Equiv.Perm α)) ] :=
          probEvent_exists_finset_le_sum _ _ _
    _ ≤ ∑ _y ∈ T \ X,
          Pr[ fun p : Equiv.Perm α => P p | ($ᵗ (Equiv.Perm α)) ] /
            ((Finset.univ \ X).card : ℝ≥0∞) := by
        apply Finset.sum_le_sum
        intro y _hy
        exact probEvent_uniformPerm_freshApply_eq_le_of_exposed_step
          P x X y hstep hproper
    _ = ((T \ X).card : ℝ≥0∞) *
          (Pr[ fun p : Equiv.Perm α => P p | ($ᵗ (Equiv.Perm α)) ] /
            ((Finset.univ \ X).card : ℝ≥0∞)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ = Pr[ fun p : Equiv.Perm α => P p | ($ᵗ (Equiv.Perm α)) ] *
          (((T \ X).card : ℝ≥0∞) /
            ((Finset.univ \ X).card : ℝ≥0∞)) :=
        mul_div_swap _ _ _
    _ ≤ Pr[ fun p : Equiv.Perm α => P p | ($ᵗ (Equiv.Perm α)) ] *
          ((T.card : ℝ≥0∞) / (Fintype.card α : ℝ≥0∞)) := by
        exact mul_le_mul_right (noReplacement_fraction_le X T hXT hproper) _
    _ = (T.card : ℝ≥0∞) *
          (Pr[ fun p : Equiv.Perm α => P p | ($ᵗ (Equiv.Perm α)) ] /
            (Fintype.card α : ℝ≥0∞)) :=
        (mul_div_swap _ _ _).symm

/-- The one-way finite-target theorem with the full-exposed-set branch discharged as an empty
event. -/
lemma probEvent_uniformPerm_freshApply_mem_finset_le_of_exposed_step_or_empty
    {α : Type} [Fintype α] [DecidableEq α] [Nonempty α]
    [SampleableType (Equiv.Perm α)]
    (P : Equiv.Perm α → Prop) (x : α) (X T : Finset α)
    (hXT : X ⊆ T)
    (himage : ∀ p : Equiv.Perm α, P p → p x ∉ X)
    (hstep : ∀ (p : Equiv.Perm α) (y' : α), y' ∉ X → P p →
      P (p.trans (Equiv.swap (p x) y'))) :
    Pr[ fun p : Equiv.Perm α => P p ∧ p x ∈ T | ($ᵗ (Equiv.Perm α)) ]
      ≤ (T.card : ℝ≥0∞) *
        (Pr[ fun p : Equiv.Perm α => P p | ($ᵗ (Equiv.Perm α)) ] /
          (Fintype.card α : ℝ≥0∞)) := by
  by_cases hproper : X.card < Fintype.card α
  · exact probEvent_uniformPerm_freshApply_mem_finset_le_of_exposed_step
      P x X T hXT himage hstep hproper
  · have hle : X.card ≤ Fintype.card α := by
      rw [← Finset.card_univ]
      exact Finset.card_le_card (Finset.subset_univ X)
    have hge : Fintype.card α ≤ X.card := by
      omega
    have hcard : X.card = Fintype.card α := Nat.le_antisymm hle hge
    have hfull : X = Finset.univ := Finset.eq_univ_of_card X hcard
    have hPfalse : ∀ p : Equiv.Perm α, ¬ P p := by
      intro p hP
      have hnot := himage p hP
      rw [hfull] at hnot
      exact hnot (Finset.mem_univ _)
    have hEvent : (fun p : Equiv.Perm α => P p ∧ p x ∈ T) = fun _p => False := by
      funext p
      apply propext
      constructor
      · intro hp
        exact False.elim (hPfalse p hp.1)
      · intro hp
        exact False.elim hp
    rw [hEvent]
    change Pr[fun _p : Equiv.Perm α => False | ($ᵗ (Equiv.Perm α))] ≤ _
    have hzero : Pr[fun _p : Equiv.Perm α => False | ($ᵗ (Equiv.Perm α))] = 0 := by
      apply probEvent_eq_zero
      intro p _hp hp
      exact hp
    rw [hzero]
    exact bot_le

/-- Support-local target inclusion for the one-way no-replacement theorem. -/
lemma probEvent_uniformPerm_freshApply_mem_finset_le_of_exposed_step_on_support
    {α : Type} [Fintype α] [DecidableEq α] [Nonempty α]
    [SampleableType (Equiv.Perm α)]
    (P : Equiv.Perm α → Prop) (x : α) (X T : Finset α)
    (hXT : ∀ p : Equiv.Perm α, P p → X ⊆ T)
    (himage : ∀ p : Equiv.Perm α, P p → p x ∉ X)
    (hstep : ∀ (p : Equiv.Perm α) (y' : α), y' ∉ X → P p →
      P (p.trans (Equiv.swap (p x) y'))) :
    Pr[ fun p : Equiv.Perm α => P p ∧ p x ∈ T | ($ᵗ (Equiv.Perm α)) ]
      ≤ (T.card : ℝ≥0∞) *
        (Pr[ fun p : Equiv.Perm α => P p | ($ᵗ (Equiv.Perm α)) ] /
          (Fintype.card α : ℝ≥0∞)) := by
  by_cases hnonempty : ∃ p : Equiv.Perm α, P p
  · obtain ⟨p, hp⟩ := hnonempty
    exact probEvent_uniformPerm_freshApply_mem_finset_le_of_exposed_step_or_empty
      P x X T (hXT p hp) himage hstep
  · have hPfalse : ∀ p : Equiv.Perm α, ¬ P p := by
      intro p hp
      exact hnonempty ⟨p, hp⟩
    have hEvent : (fun p : Equiv.Perm α => P p ∧ p x ∈ T) = fun _p => False := by
      funext p
      apply propext
      constructor
      · intro hp
        exact False.elim (hPfalse p hp.1)
      · intro hp
        exact False.elim hp
    rw [hEvent]
    change Pr[fun _p : Equiv.Perm α => False | ($ᵗ (Equiv.Perm α))] ≤ _
    have hzero : Pr[fun _p : Equiv.Perm α => False | ($ᵗ (Equiv.Perm α))] = 0 := by
      apply probEvent_eq_zero
      intro p _hp hp
      exact hp
    rw [hzero]
    exact bot_le

/-! ## Capacity-fiber specialization -/

/-- The full sponge states whose capacity segment belongs to `S`.  The no-replacement proof works
over this set of full states; the fiber-counting lemma below then restores the paper's
`|S| / |Σ|^c` denominator. -/
noncomputable def capacityTargetStateFinset
    {U : Type} [SpongeUnit U] [SpongeSize] [VCVCompatible U] [DecidableEq U]
    (S : Finset (Vector U SpongeSize.C)) : Finset (CanonicalSpongeState U) :=
  letI : Fintype (CanonicalSpongeState U) := Vector.instFintype
  Finset.univ.filter fun s => s.capacitySegment ∈ S

/-- The capacity-fiber counting step for `capacityTargetStateFinset`.  This is the same finite
combinatorics used for a directly uniform sponge state, stated as the ratio needed after the
permutation no-replacement argument. -/
lemma capacityTargetStateFinset_ratio_le
    {U : Type} [SpongeUnit U] [SpongeSize] [VCVCompatible U] [DecidableEq U]
    [fU : Fintype U]
    [SampleableType (CanonicalSpongeState U)]
    (S : Finset (Vector U SpongeSize.C)) :
    ((capacityTargetStateFinset S).card : ℝ≥0∞) /
        (Fintype.card (CanonicalSpongeState U) : ℝ≥0∞)
      ≤ (S.card : ℝ≥0∞) / capacitySpaceSize (U := U) := by
  letI : Fintype U := fU
  change ((@Finset.univ (CanonicalSpongeState U) Vector.instFintype).filter
      (fun s => s.capacitySegment ∈ S)).card / (@Fintype.card (CanonicalSpongeState U)
        Vector.instFintype : ℝ≥0∞) ≤ (S.card : ℝ≥0∞) / capacitySpaceSize (U := U)
  have h := probEvent_uniformState_capacitySegment_mem_finset_le (U := U) S
  rw [probEvent_uniformSample] at h
  exact h

/-- Capacity-fiber specialization of one-way restricted-swap freshness.  This is the form used
when trace causality says that changing a fresh output cannot invalidate an already fixed prefix,
without requiring an artificial reverse swap invariant. -/
lemma probEvent_uniformPerm_freshApply_capacitySegment_mem_finset_le_of_exposed_step
    {U : Type} [SpongeUnit U] [SpongeSize] [VCVCompatible U] [DecidableEq U]
    [fU : Fintype U]
    [SampleableType (CanonicalSpongeState U)]
    [SampleableType (Equiv.Perm (CanonicalSpongeState U))]
    (P : Equiv.Perm (CanonicalSpongeState U) → Prop)
    (x : CanonicalSpongeState U) (X : Finset (CanonicalSpongeState U))
    (S : Finset (Vector U SpongeSize.C))
    (hXT : ∀ p : Equiv.Perm (CanonicalSpongeState U), P p →
      X ⊆ capacityTargetStateFinset S)
    (himage : ∀ p : Equiv.Perm (CanonicalSpongeState U), P p → p x ∉ X)
    (hstep : ∀ (p : Equiv.Perm (CanonicalSpongeState U))
      (y' : CanonicalSpongeState U), y' ∉ X → P p →
      P (p.trans (Equiv.swap (p x) y'))) :
    Pr[ fun p : Equiv.Perm (CanonicalSpongeState U) =>
        P p ∧ (p x).capacitySegment ∈ S |
        ($ᵗ (Equiv.Perm (CanonicalSpongeState U))) ]
      ≤ (S.card : ℝ≥0∞) *
        (Pr[ fun p : Equiv.Perm (CanonicalSpongeState U) => P p |
          ($ᵗ (Equiv.Perm (CanonicalSpongeState U))) ] /
          capacitySpaceSize (U := U)) := by
  letI : Fintype U := fU
  letI : Fintype (CanonicalSpongeState U) := Vector.instFintype
  have hTarget : (fun p : Equiv.Perm (CanonicalSpongeState U) =>
      P p ∧ p x ∈ capacityTargetStateFinset S) =
      fun p => P p ∧ (p x).capacitySegment ∈ S := by
    funext p
    apply propext
    constructor
    · intro hp
      rcases hp with ⟨hP, hmem⟩
      unfold capacityTargetStateFinset at hmem
      exact ⟨hP, (Finset.mem_filter.mp hmem).2⟩
    · intro hp
      rcases hp with ⟨hP, hcap⟩
      unfold capacityTargetStateFinset
      exact ⟨hP, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcap⟩⟩
  have hFresh := probEvent_uniformPerm_freshApply_mem_finset_le_of_exposed_step_on_support
    P x X (capacityTargetStateFinset S) hXT himage hstep
  rw [hTarget] at hFresh
  have hRatio := capacityTargetStateFinset_ratio_le (U := U) S
  calc
    Pr[ fun p : Equiv.Perm (CanonicalSpongeState U) =>
        P p ∧ (p x).capacitySegment ∈ S |
        ($ᵗ (Equiv.Perm (CanonicalSpongeState U))) ]
        ≤ ((capacityTargetStateFinset S).card : ℝ≥0∞) *
          (Pr[ fun p : Equiv.Perm (CanonicalSpongeState U) => P p |
            ($ᵗ (Equiv.Perm (CanonicalSpongeState U))) ] /
            (Fintype.card (CanonicalSpongeState U) : ℝ≥0∞)) := hFresh
    _ = Pr[ fun p : Equiv.Perm (CanonicalSpongeState U) => P p |
          ($ᵗ (Equiv.Perm (CanonicalSpongeState U))) ] *
          (((capacityTargetStateFinset S).card : ℝ≥0∞) /
            (Fintype.card (CanonicalSpongeState U) : ℝ≥0∞)) :=
        mul_div_swap _ _ _
    _ ≤ Pr[ fun p : Equiv.Perm (CanonicalSpongeState U) => P p |
          ($ᵗ (Equiv.Perm (CanonicalSpongeState U))) ] *
          ((S.card : ℝ≥0∞) / capacitySpaceSize (U := U)) :=
        mul_le_mul_right hRatio _
    _ = (S.card : ℝ≥0∞) *
          (Pr[ fun p : Equiv.Perm (CanonicalSpongeState U) => P p |
            ($ᵗ (Equiv.Perm (CanonicalSpongeState U))) ] /
          capacitySpaceSize (U := U)) :=
        mul_div_swap _ _ _

/-- Adaptive no-replacement freshness for a charged forward permutation query.  The optional
readout, exposed-state set, and capacity target set may all depend on the sampled permutation.
The proof partitions successful executions by their realized `(X,S,x)` triple; these cases are
disjoint, so this partition introduces no cardinality loss. -/
lemma probEvent_uniformPerm_freshOptionalApply_capacitySegment_mem_finset_le_of_exposed_step
    {U : Type} [SpongeUnit U] [SpongeSize] [VCVCompatible U] [DecidableEq U]
    [fU : Fintype U]
    [SampleableType (CanonicalSpongeState U)]
    [SampleableType (Equiv.Perm (CanonicalSpongeState U))]
    (P : Equiv.Perm (CanonicalSpongeState U) → Prop)
    (read : Equiv.Perm (CanonicalSpongeState U) → Option (CanonicalSpongeState U))
    (X : Equiv.Perm (CanonicalSpongeState U) → Finset (CanonicalSpongeState U))
    (S : Equiv.Perm (CanonicalSpongeState U) → Finset (Vector U SpongeSize.C))
    (B : ℝ≥0∞)
    (hcard : ∀ p, ((S p).card : ℝ≥0∞) ≤ B)
    (hXT : ∀ p, P p → X p ⊆ capacityTargetStateFinset (S p))
    (himage : ∀ p x, P p → read p = some x → p x ∉ X p)
    (hstep : ∀ (p : Equiv.Perm (CanonicalSpongeState U))
      (x y' : CanonicalSpongeState U) (X₀ : Finset (CanonicalSpongeState U))
      (S₀ : Finset (Vector U SpongeSize.C)), y' ∉ X₀ →
      P p ∧ X p = X₀ ∧ S p = S₀ ∧ read p = some x →
        let p' := p.trans (Equiv.swap (p x) y')
        P p' ∧ X p' = X₀ ∧ S p' = S₀ ∧ read p' = some x) :
    Pr[ fun p => P p ∧ ∃ x : CanonicalSpongeState U,
        read p = some x ∧ (p x).capacitySegment ∈ S p |
        ($ᵗ (Equiv.Perm (CanonicalSpongeState U))) ]
      ≤ B * (Pr[ P | ($ᵗ (Equiv.Perm (CanonicalSpongeState U))) ] /
          capacitySpaceSize (U := U)) := by
  classical
  letI : Fintype U := fU
  letI : Fintype (CanonicalSpongeState U) := Vector.instFintype
  let Γ := Finset (CanonicalSpongeState U) ×
    Finset (Vector U SpongeSize.C) × CanonicalSpongeState U
  let Pq : Γ → Equiv.Perm (CanonicalSpongeState U) → Prop :=
    fun q p => P p ∧ X p = q.1 ∧ S p = q.2.1 ∧ read p = some q.2.2
  let selector : Equiv.Perm (CanonicalSpongeState U) → Option Γ := fun p =>
    match read p with
    | none => none
    | some x => some (X p, S p, x)
  have hPq_selector : ∀ (q : Γ) (p : Equiv.Perm (CanonicalSpongeState U)),
      Pq q p ↔ P p ∧ selector p = some q := by
    intro q p
    unfold Pq selector
    cases read p with
    | none =>
        simp
    | some x =>
        simp only [Option.some.injEq]
        constructor
        · intro hp
          rcases hp with ⟨hP, hX, hS, hread'⟩
          have hx : x = q.2.2 := hread'
          subst x
          exact ⟨hP, Prod.ext hX (Prod.ext hS rfl)⟩
        · intro hp
          rcases hp with ⟨hP, hpq⟩
          have hX : X p = q.1 := congrArg Prod.fst hpq
          have hSx : (S p, x) = q.2 := congrArg Prod.snd hpq
          have hS : S p = q.2.1 := congrArg Prod.fst hSx
          have hx : x = q.2.2 := congrArg Prod.snd hSx
          subst x
          exact ⟨hP, hX, hS, rfl⟩
  have hEvent : (fun p : Equiv.Perm (CanonicalSpongeState U) =>
      P p ∧ ∃ x : CanonicalSpongeState U,
        read p = some x ∧ (p x).capacitySegment ∈ S p) =
      fun p => ∃ q ∈ (Finset.univ : Finset Γ),
        Pq q p ∧ (p q.2.2).capacitySegment ∈ q.2.1 := by
    funext p
    apply propext
    constructor
    · intro hp
      rcases hp with ⟨hP, x, hread, hcap⟩
      refine ⟨(X p, S p, x), Finset.mem_univ _, ?_, ?_⟩
      · exact ⟨hP, rfl, rfl, hread⟩
      · exact hcap
    · intro hp
      rcases hp with ⟨q, _hq, hPq, hcap⟩
      rcases hPq with ⟨hP, _hX, hS, hread⟩
      refine ⟨hP, q.2.2, hread, ?_⟩
      rw [hS]
      exact hcap
  have hsumP :
      (∑ q : Γ, Pr[ fun p : Equiv.Perm (CanonicalSpongeState U) => Pq q p |
        ($ᵗ (Equiv.Perm (CanonicalSpongeState U))) ])
        ≤ Pr[ P | ($ᵗ (Equiv.Perm (CanonicalSpongeState U))) ] := by
    calc
      ∑ q : Γ, Pr[ fun p : Equiv.Perm (CanonicalSpongeState U) => Pq q p |
          ($ᵗ (Equiv.Perm (CanonicalSpongeState U))) ]
          = ∑ q : Γ, Pr[ fun p : Equiv.Perm (CanonicalSpongeState U) =>
              P p ∧ selector p = some q |
              ($ᵗ (Equiv.Perm (CanonicalSpongeState U))) ] := by
            apply Finset.sum_congr rfl
            intro q _hq
            congr 1
            funext p
            apply propext
            exact hPq_selector q p
      _ ≤ ∑ oq : Option Γ, Pr[ fun p : Equiv.Perm (CanonicalSpongeState U) =>
              P p ∧ selector p = oq |
              ($ᵗ (Equiv.Perm (CanonicalSpongeState U))) ] := by
            rw [Fintype.sum_option]
            exact le_add_self
      _ ≤ Pr[ P | ($ᵗ (Equiv.Perm (CanonicalSpongeState U))) ] :=
            sum_probEvent_and_eq_le _ P selector
  rw [hEvent]
  calc
    Pr[ fun p : Equiv.Perm (CanonicalSpongeState U) => ∃ q ∈ (Finset.univ : Finset Γ),
        Pq q p ∧ (p q.2.2).capacitySegment ∈ q.2.1 |
        ($ᵗ (Equiv.Perm (CanonicalSpongeState U))) ]
        ≤ ∑ q : Γ, Pr[ fun p : Equiv.Perm (CanonicalSpongeState U) =>
            Pq q p ∧ (p q.2.2).capacitySegment ∈ q.2.1 |
            ($ᵗ (Equiv.Perm (CanonicalSpongeState U))) ] :=
          probEvent_exists_finset_le_sum (Finset.univ : Finset Γ) _ _
    _ ≤ ∑ q : Γ, ((q.2.1).card : ℝ≥0∞) *
          (Pr[ fun p : Equiv.Perm (CanonicalSpongeState U) => Pq q p |
            ($ᵗ (Equiv.Perm (CanonicalSpongeState U))) ] /
            capacitySpaceSize (U := U)) := by
        apply Finset.sum_le_sum
        intro q _hq
        exact probEvent_uniformPerm_freshApply_capacitySegment_mem_finset_le_of_exposed_step
          (P := Pq q) (x := q.2.2) (X := q.1) (S := q.2.1)
          (by
            intro p hp
            rcases hp with ⟨hP, hX, hS, _hread⟩
            rw [← hX, ← hS]
            exact hXT p hP)
          (by
            intro p hp
            rcases hp with ⟨hP, hX, _hS, hread⟩
            have hnot := himage p q.2.2 hP hread
            rw [hX] at hnot
            exact hnot)
          (by
            intro p y' hy hp
            rcases hp with ⟨hP, hX, hS, hread⟩
            exact hstep p q.2.2 y' q.1 q.2.1 hy ⟨hP, hX, hS, hread⟩)
    _ ≤ ∑ q : Γ, B *
          (Pr[ fun p : Equiv.Perm (CanonicalSpongeState U) => Pq q p |
            ($ᵗ (Equiv.Perm (CanonicalSpongeState U))) ] /
            capacitySpaceSize (U := U)) := by
        apply Finset.sum_le_sum
        intro q _hq
        by_cases hq : ∃ p : Equiv.Perm (CanonicalSpongeState U), Pq q p
        · obtain ⟨p, hp⟩ := hq
          rcases hp with ⟨_hP, _hX, hS, _hread⟩
          have hqcard := hcard p
          rw [hS] at hqcard
          exact mul_le_mul_left hqcard _
        · have hzero : Pr[ fun p : Equiv.Perm (CanonicalSpongeState U) => Pq q p |
              ($ᵗ (Equiv.Perm (CanonicalSpongeState U))) ] = 0 := by
            apply probEvent_eq_zero
            intro p _hp hp
            exact hq ⟨p, hp⟩
          rw [hzero]
          simp
    _ = B *
          ((∑ q : Γ, Pr[ fun p : Equiv.Perm (CanonicalSpongeState U) => Pq q p |
            ($ᵗ (Equiv.Perm (CanonicalSpongeState U))) ]) /
            capacitySpaceSize (U := U)) := by
        rw [← Finset.mul_sum]
        congr 1
        calc
          ∑ q : Γ, Pr[ fun p : Equiv.Perm (CanonicalSpongeState U) => Pq q p |
              ($ᵗ (Equiv.Perm (CanonicalSpongeState U))) ] /
              capacitySpaceSize (U := U)
              = ∑ q : Γ, Pr[ fun p : Equiv.Perm (CanonicalSpongeState U) => Pq q p |
                  ($ᵗ (Equiv.Perm (CanonicalSpongeState U))) ] *
                  (capacitySpaceSize (U := U))⁻¹ := by
                apply Finset.sum_congr rfl
                intro q _hq
                rw [ENNReal.div_eq_inv_mul]
                exact mul_comm _ _
          _ = (∑ q : Γ, Pr[ fun p : Equiv.Perm (CanonicalSpongeState U) => Pq q p |
                  ($ᵗ (Equiv.Perm (CanonicalSpongeState U))) ]) *
                  (capacitySpaceSize (U := U))⁻¹ := by
                rw [Finset.sum_mul]
          _ = (∑ q : Γ, Pr[ fun p : Equiv.Perm (CanonicalSpongeState U) => Pq q p |
                  ($ᵗ (Equiv.Perm (CanonicalSpongeState U))) ]) /
                  capacitySpaceSize (U := U) := by
                rw [ENNReal.div_eq_inv_mul]
                exact mul_comm _ _
    _ ≤ B * (Pr[ P | ($ᵗ (Equiv.Perm (CanonicalSpongeState U))) ] /
          capacitySpaceSize (U := U)) := by
        apply mul_le_mul_right
        exact ENNReal.div_le_div_right hsumP _

/-- Adaptive inverse-query no-replacement freshness, obtained by applying the forward theorem
to the inverse sampled permutation.  The left swap on `p` becomes the forward/range swap on
`p⁻¹`, so no second counting argument is required. -/
lemma probEvent_uniformPerm_freshOptionalSymmApply_capacitySegment_mem_finset_le_of_exposed_step
    {U : Type} [SpongeUnit U] [SpongeSize] [VCVCompatible U] [DecidableEq U]
    [fU : Fintype U]
    [SampleableType (CanonicalSpongeState U)]
    [SampleableType (Equiv.Perm (CanonicalSpongeState U))]
    (P : Equiv.Perm (CanonicalSpongeState U) → Prop)
    (read : Equiv.Perm (CanonicalSpongeState U) → Option (CanonicalSpongeState U))
    (X : Equiv.Perm (CanonicalSpongeState U) → Finset (CanonicalSpongeState U))
    (S : Equiv.Perm (CanonicalSpongeState U) → Finset (Vector U SpongeSize.C))
    (B : ℝ≥0∞)
    (hcard : ∀ p, ((S p).card : ℝ≥0∞) ≤ B)
    (hXT : ∀ p, P p → X p ⊆ capacityTargetStateFinset (S p))
    (himage : ∀ p y, P p → read p = some y → p.symm y ∉ X p)
    (hstep : ∀ (p : Equiv.Perm (CanonicalSpongeState U))
      (y x' : CanonicalSpongeState U) (X₀ : Finset (CanonicalSpongeState U))
      (S₀ : Finset (Vector U SpongeSize.C)), x' ∉ X₀ →
      P p ∧ X p = X₀ ∧ S p = S₀ ∧ read p = some y →
        let p' := (Equiv.swap (p.symm y) x').trans p
        P p' ∧ X p' = X₀ ∧ S p' = S₀ ∧ read p' = some y) :
    Pr[ fun p => P p ∧ ∃ y : CanonicalSpongeState U,
        read p = some y ∧ (p.symm y).capacitySegment ∈ S p |
        ($ᵗ (Equiv.Perm (CanonicalSpongeState U))) ]
      ≤ B * (Pr[ P | ($ᵗ (Equiv.Perm (CanonicalSpongeState U))) ] /
          capacitySpaceSize (U := U)) := by
  classical
  letI : Fintype U := fU
  let invEquiv :
      Equiv.Perm (CanonicalSpongeState U) ≃ Equiv.Perm (CanonicalSpongeState U) :=
    { toFun := fun p => p.symm
      invFun := fun p => p.symm
      left_inv := by intro p; ext z; rfl
      right_inv := by intro p; ext z; rfl }
  let P' : Equiv.Perm (CanonicalSpongeState U) → Prop := fun q => P q.symm
  let read' : Equiv.Perm (CanonicalSpongeState U) → Option (CanonicalSpongeState U) :=
    fun q => read q.symm
  let X' : Equiv.Perm (CanonicalSpongeState U) → Finset (CanonicalSpongeState U) :=
    fun q => X q.symm
  let S' : Equiv.Perm (CanonicalSpongeState U) → Finset (Vector U SpongeSize.C) :=
    fun q => S q.symm
  have hEvent :
      Pr[ fun p => P p ∧ ∃ y : CanonicalSpongeState U,
          read p = some y ∧ (p.symm y).capacitySegment ∈ S p |
          ($ᵗ (Equiv.Perm (CanonicalSpongeState U))) ] =
        Pr[ fun q => P' q ∧ ∃ y : CanonicalSpongeState U,
          read' q = some y ∧ (q y).capacitySegment ∈ S' q |
          ($ᵗ (Equiv.Perm (CanonicalSpongeState U))) ] := by
    rw [probEvent_uniformSample_equiv_invariant invEquiv
      (fun p => P p ∧ ∃ y : CanonicalSpongeState U,
        read p = some y ∧ (p.symm y).capacitySegment ∈ S p)]
    rfl
  have hPred :
      Pr[ P' | ($ᵗ (Equiv.Perm (CanonicalSpongeState U))) ] =
        Pr[ P | ($ᵗ (Equiv.Perm (CanonicalSpongeState U))) ] := by
    exact (probEvent_uniformSample_equiv_invariant invEquiv P).symm
  rw [hEvent]
  have hforward := probEvent_uniformPerm_freshOptionalApply_capacitySegment_mem_finset_le_of_exposed_step
    (P := P') (read := read') (X := X') (S := S') B
    (by
      intro q
      exact hcard q.symm)
    (by
      intro q hq
      exact hXT q.symm hq)
    (by
      intro q y hq hread
      exact himage q.symm y hq hread)
    (by
      intro q y x' X₀ S₀ hx' hstate
      rcases hstate with ⟨hP, hX, hS, hread⟩
      have hstep' := hstep q.symm y x' X₀ S₀ hx' ⟨hP, hX, hS, hread⟩
      have hEq :
          (q.trans (Equiv.swap (q y) x')).symm =
            (Equiv.swap (q y) x').trans q.symm := by
        ext z
        have hswap : (Equiv.swap (q y) x').symm z =
            (Equiv.swap (q y) x') z := by
          apply (Equiv.swap (q y) x').injective
          rw [Equiv.apply_symm_apply]
          exact (Equiv.swap_apply_self (q y) x' z).symm
        rw [Equiv.symm_trans_apply, Equiv.trans_apply, hswap]
      dsimp only [P', X', S', read']
      rw [hEq]
      exact hstep')
  calc
    Pr[ fun q => P' q ∧ ∃ y : CanonicalSpongeState U,
        read' q = some y ∧ (q y).capacitySegment ∈ S' q |
        ($ᵗ (Equiv.Perm (CanonicalSpongeState U))) ]
        ≤ B * (Pr[ P' | ($ᵗ (Equiv.Perm (CanonicalSpongeState U))) ] /
            capacitySpaceSize (U := U)) := hforward
    _ = B * (Pr[ P | ($ᵗ (Equiv.Perm (CanonicalSpongeState U))) ] /
            capacitySpaceSize (U := U)) := by rw [hPred]

/-- Product lift of adaptive no-replacement freshness.  It is intentionally stated with the
unconditional paper bound `B / |Σ|^c`; conditioning on the independent side sampler is handled
by `probEvent_bind_le_of_forall_le`, so no independence axiom is introduced. -/
lemma probEvent_uniformPerm_prod_freshOptionalApply_capacitySegment_mem_finset_le_of_exposed_step
    {U : Type} [SpongeUnit U] [SpongeSize] [VCVCompatible U] [DecidableEq U]
    [fU : Fintype U]
    [SampleableType (CanonicalSpongeState U)]
    [SampleableType (Equiv.Perm (CanonicalSpongeState U))]
    {Γ : Type} (side : ProbComp Γ)
    (P : Γ × Equiv.Perm (CanonicalSpongeState U) → Prop)
    (read : Γ × Equiv.Perm (CanonicalSpongeState U) → Option (CanonicalSpongeState U))
    (X : Γ × Equiv.Perm (CanonicalSpongeState U) → Finset (CanonicalSpongeState U))
    (S : Γ × Equiv.Perm (CanonicalSpongeState U) → Finset (Vector U SpongeSize.C))
    (B : ℝ≥0∞)
    (hcard : ∀ γ p, ((S (γ, p)).card : ℝ≥0∞) ≤ B)
    (hXT : ∀ γ p, P (γ, p) → X (γ, p) ⊆ capacityTargetStateFinset (S (γ, p)))
    (himage : ∀ γ p x, P (γ, p) → read (γ, p) = some x → p x ∉ X (γ, p))
    (hstep : ∀ (γ : Γ) (p : Equiv.Perm (CanonicalSpongeState U))
      (x y' : CanonicalSpongeState U) (X₀ : Finset (CanonicalSpongeState U))
      (S₀ : Finset (Vector U SpongeSize.C)), y' ∉ X₀ →
      P (γ, p) ∧ X (γ, p) = X₀ ∧ S (γ, p) = S₀ ∧ read (γ, p) = some x →
        let p' := p.trans (Equiv.swap (p x) y')
        P (γ, p') ∧ X (γ, p') = X₀ ∧ S (γ, p') = S₀ ∧ read (γ, p') = some x) :
    Pr[ fun γp => P γp ∧ ∃ x : CanonicalSpongeState U,
        read γp = some x ∧ (γp.2 x).capacitySegment ∈ S γp |
        (do
          let γ ← side
          let p ← ($ᵗ (Equiv.Perm (CanonicalSpongeState U)))
          pure (γ, p)) ]
      ≤ B / capacitySpaceSize (U := U) := by
  letI : Fintype U := fU
  let sampleP : ProbComp (Equiv.Perm (CanonicalSpongeState U)) :=
    ($ᵗ (Equiv.Perm (CanonicalSpongeState U)))
  change Pr[ fun γp => P γp ∧ ∃ x : CanonicalSpongeState U,
      read γp = some x ∧ (γp.2 x).capacitySegment ∈ S γp |
      side >>= fun γ => sampleP >>= fun p => pure (γ, p)]
      ≤ B / capacitySpaceSize (U := U)
  apply probEvent_bind_le_of_forall_le
  intro γ _hγ
  rw [probEvent_bind_pure_left_pair sampleP γ
    (fun γp => P γp ∧ ∃ x : CanonicalSpongeState U,
      read γp = some x ∧ (γp.2 x).capacitySegment ∈ S γp)]
  calc
    Pr[ fun p : Equiv.Perm (CanonicalSpongeState U) =>
        P (γ, p) ∧ ∃ x : CanonicalSpongeState U,
          read (γ, p) = some x ∧ (p x).capacitySegment ∈ S (γ, p) | sampleP]
        ≤ B *
          (Pr[ fun p : Equiv.Perm (CanonicalSpongeState U) => P (γ, p) | sampleP] /
            capacitySpaceSize (U := U)) :=
          probEvent_uniformPerm_freshOptionalApply_capacitySegment_mem_finset_le_of_exposed_step
            (P := fun p => P (γ, p))
            (read := fun p => read (γ, p))
            (X := fun p => X (γ, p)) (S := fun p => S (γ, p)) B
            (by
              intro p
              exact hcard γ p)
            (by
              intro p hp
              exact hXT γ p hp)
            (by
              intro p x hp hread
              exact himage γ p x hp hread)
            (by
              intro p x y' X₀ S₀ hy hp
              exact hstep γ p x y' X₀ S₀ hy hp)
    _ ≤ B * (1 / capacitySpaceSize (U := U)) := by
        apply mul_le_mul_right
        exact ENNReal.div_le_div_right probEvent_le_one _
    _ = B / capacitySpaceSize (U := U) := by
        rw [ENNReal.div_eq_inv_mul]
        rw [mul_one]
        rw [ENNReal.div_eq_inv_mul]
        exact mul_comm _ _

/-- Product lift of the adaptive inverse-image no-replacement theorem. -/
lemma probEvent_uniformPerm_prod_freshOptionalSymmApply_capacitySegment_mem_finset_le_of_exposed_step
    {U : Type} [SpongeUnit U] [SpongeSize] [VCVCompatible U] [DecidableEq U]
    [fU : Fintype U]
    [SampleableType (CanonicalSpongeState U)]
    [SampleableType (Equiv.Perm (CanonicalSpongeState U))]
    {Γ : Type} (side : ProbComp Γ)
    (P : Γ × Equiv.Perm (CanonicalSpongeState U) → Prop)
    (read : Γ × Equiv.Perm (CanonicalSpongeState U) → Option (CanonicalSpongeState U))
    (X : Γ × Equiv.Perm (CanonicalSpongeState U) → Finset (CanonicalSpongeState U))
    (S : Γ × Equiv.Perm (CanonicalSpongeState U) → Finset (Vector U SpongeSize.C))
    (B : ℝ≥0∞)
    (hcard : ∀ γ p, ((S (γ, p)).card : ℝ≥0∞) ≤ B)
    (hXT : ∀ γ p, P (γ, p) → X (γ, p) ⊆ capacityTargetStateFinset (S (γ, p)))
    (himage : ∀ γ p y, P (γ, p) → read (γ, p) = some y → p.symm y ∉ X (γ, p))
    (hstep : ∀ (γ : Γ) (p : Equiv.Perm (CanonicalSpongeState U))
      (y x' : CanonicalSpongeState U) (X₀ : Finset (CanonicalSpongeState U))
      (S₀ : Finset (Vector U SpongeSize.C)), x' ∉ X₀ →
      P (γ, p) ∧ X (γ, p) = X₀ ∧ S (γ, p) = S₀ ∧ read (γ, p) = some y →
        let p' := (Equiv.swap (p.symm y) x').trans p
        P (γ, p') ∧ X (γ, p') = X₀ ∧ S (γ, p') = S₀ ∧ read (γ, p') = some y) :
    Pr[ fun γp => P γp ∧ ∃ y : CanonicalSpongeState U,
        read γp = some y ∧ (γp.2.symm y).capacitySegment ∈ S γp |
        (do
          let γ ← side
          let p ← ($ᵗ (Equiv.Perm (CanonicalSpongeState U)))
          pure (γ, p)) ]
      ≤ B / capacitySpaceSize (U := U) := by
  letI : Fintype U := fU
  let sampleP : ProbComp (Equiv.Perm (CanonicalSpongeState U)) :=
    ($ᵗ (Equiv.Perm (CanonicalSpongeState U)))
  change Pr[ fun γp => P γp ∧ ∃ y : CanonicalSpongeState U,
      read γp = some y ∧ (γp.2.symm y).capacitySegment ∈ S γp |
      side >>= fun γ => sampleP >>= fun p => pure (γ, p)]
      ≤ B / capacitySpaceSize (U := U)
  apply probEvent_bind_le_of_forall_le
  intro γ _hγ
  rw [probEvent_bind_pure_left_pair sampleP γ
    (fun γp => P γp ∧ ∃ y : CanonicalSpongeState U,
      read γp = some y ∧ (γp.2.symm y).capacitySegment ∈ S γp)]
  calc
    Pr[ fun p : Equiv.Perm (CanonicalSpongeState U) =>
        P (γ, p) ∧ ∃ y : CanonicalSpongeState U,
          read (γ, p) = some y ∧ (p.symm y).capacitySegment ∈ S (γ, p) | sampleP]
        ≤ B *
          (Pr[ fun p : Equiv.Perm (CanonicalSpongeState U) => P (γ, p) | sampleP] /
            capacitySpaceSize (U := U)) :=
          probEvent_uniformPerm_freshOptionalSymmApply_capacitySegment_mem_finset_le_of_exposed_step
            (P := fun p => P (γ, p))
            (read := fun p => read (γ, p))
            (X := fun p => X (γ, p)) (S := fun p => S (γ, p)) B
            (by
              intro p
              exact hcard γ p)
            (by
              intro p hp
              exact hXT γ p hp)
            (by
              intro p y hp hread
              exact himage γ p y hp hread)
            (by
              intro p y x' X₀ S₀ hx' hp
              exact hstep γ p y x' X₀ S₀ hx' hp)
    _ ≤ B * (1 / capacitySpaceSize (U := U)) := by
        apply mul_le_mul_right
        exact ENNReal.div_le_div_right probEvent_le_one _
    _ = B / capacitySpaceSize (U := U) := by
        rw [ENNReal.div_eq_inv_mul]
        rw [mul_one]
        rw [ENNReal.div_eq_inv_mul]
        exact mul_comm _ _

/-! ## Eager-sponge `E_p` contract -/

variable {StmtIn : Type} {n : ℕ} {pSpec : ProtocolSpec n}
  {U : Type} [SpongeUnit U] [SpongeSize]

variable {StmtOut : Type}
  [VCVCompatible StmtIn] [∀ i, VCVCompatible (pSpec.Challenge i)]
  [codec : CodecCore pSpec U] {δ : ℕ} [DecidableEq StmtIn] [DecidableEq U]
  [VCVCompatible U] [SampleableType U]
  [∀ i, Fintype (pSpec.Message i)]
  [∀ i, DecidableEq (pSpec.Message i)]

/-- The eager-sponge forward fresh-hit bound, obtained directly from the stopped-prefix
transposition theorem and the generic no-replacement count.  `E_first_at` is used only to
weaken the event: the deferred decision charges every forward fresh-hit representative. -/
lemma sponge_permFwdFreshHit_first_noReplacement_contract
    [fU : Fintype U] [Nonempty U]
    (V : Verifier []ₒ StmtIn StmtOut pSpec)
    (maliciousProver : MaliciousProver []ₒ pSpec StmtIn U δ) (j : ℕ) :
    Pr[ fun tr => E_first_at (tr.1 ++ tr.2) j ∧
        permFwdFreshHitAt (getBaseTrace (tr.1 ++ tr.2)) j |
        lemma5_8SpongeTraceDist (StmtIn := StmtIn) (StmtOut := StmtOut) (n := n)
          (pSpec := pSpec) (U := U) (δ := δ) (initSponge := (D_𝔖 StmtIn U).sample)
          (implSponge := (D_𝔖 StmtIn U).eagerImpl) V maliciousProver]
      ≤ (2 * (j : ℝ≥0∞) + 1) / capacitySpaceSize (U := U) := by
  classical
  letI : Fintype U := fU
  let exp := lemma5_8SpongeTraceDist (StmtIn := StmtIn) (StmtOut := StmtOut) (n := n)
    (pSpec := pSpec) (U := U) (δ := δ) (initSponge := (D_𝔖 StmtIn U).sample)
    (implSponge := (D_𝔖 StmtIn U).eagerImpl) V maliciousProver
  let det := spongeDetTrace (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec)
    (U := U) (δ := δ) V maliciousProver
  let Qleft : QueryLog (duplexSpongeChallengeOracle StmtIn U) ×
      QueryLog (duplexSpongeChallengeOracle StmtIn U) → Prop :=
    fun tr => E_first_at (tr.1 ++ tr.2) j ∧
      permFwdFreshHitAt (getBaseTrace (tr.1 ++ tr.2)) j
  have hLeftMap :
      Pr[ Qleft | exp] =
        Pr[ Qleft ∘ det | (D_𝔖 StmtIn U).sample] := by
    exact probEvent_lemma5_8SpongeTraceDist_eq_map
      (StmtIn := StmtIn) (StmtOut := StmtOut) (n := n) (pSpec := pSpec)
      (U := U) (δ := δ) V maliciousProver Qleft
  change Pr[ Qleft | exp] ≤ (2 * (j : ℝ≥0∞) + 1) / capacitySpaceSize (U := U)
  rw [hLeftMap]
  let sampleH : ProbComp (StmtIn → Vector U SpongeSize.C) :=
    ($ᵗ (OracleReduction.OracleFamily (StmtIn →ₒ Vector U SpongeSize.C)))
  let sampleHP : ProbComp ((StmtIn → Vector U SpongeSize.C) ×
      Equiv.Perm (CanonicalSpongeState U)) := do
    let h ← sampleH
    let p ← $ᵗ (Equiv.Perm (CanonicalSpongeState U))
    pure (h, p)
  rw [show (D_𝔖 StmtIn U).sample = sampleHP by rfl]
  let P : (StmtIn → Vector U SpongeSize.C) × Equiv.Perm (CanonicalSpongeState U) → Prop :=
    fun _ => True
  let read : (StmtIn → Vector U SpongeSize.C) × Equiv.Perm (CanonicalSpongeState U) →
      Option (CanonicalSpongeState U) :=
    fun hp => permFwdInputAt (getBaseTrace ((det hp).1 ++ (det hp).2)) j
  let X : (StmtIn → Vector U SpongeSize.C) × Equiv.Perm (CanonicalSpongeState U) →
      Finset (CanonicalSpongeState U) :=
    fun hp => permExposedRangeFinset (getBaseTrace ((det hp).1 ++ (det hp).2)) j
  let S : (StmtIn → Vector U SpongeSize.C) × Equiv.Perm (CanonicalSpongeState U) →
      Finset (Vector U SpongeSize.C) :=
    fun hp => permFwdCapacityTargetFinset (getBaseTrace ((det hp).1 ++ (det hp).2)) j
  calc
    Pr[ Qleft ∘ det | sampleHP]
        ≤ Pr[ fun hp => P hp ∧ ∃ x : CanonicalSpongeState U,
            read hp = some x ∧ (hp.2 x).capacitySegment ∈ S hp | sampleHP] := by
          apply probEvent_mono
          intro hp _ hhit
          rcases hp with ⟨h, p⟩
          obtain ⟨_hfirst, hfresh⟩ := hhit
          obtain ⟨c, hout, hmem⟩ :=
            permFwdFreshHitAt_imp_mem_targetFinset (StmtIn := StmtIn) (U := U)
              (j := j) hfresh
          obtain ⟨x, hread⟩ := exists_permFwdInputAt_of_permOutCapAt_target hout
          dsimp [det] at hfresh hout hmem hread
          have houtTable := spongeDetTrace_permFwdInput_outputCap_eq
            (StmtIn := StmtIn) (StmtOut := StmtOut) (n := n) (pSpec := pSpec)
            (U := U) (δ := δ) V maliciousProver (h, p) hread
          have hval : (p x).capacitySegment = c := by
            have hsome : some (p x).capacitySegment = some c := by
              rw [← houtTable]
              exact hout
            exact Option.some.inj hsome
          refine ⟨trivial, x, ?_, ?_⟩
          · exact hread
          · change (p x).capacitySegment ∈
              permFwdCapacityTargetFinset
                (getBaseTrace ((det (h, p)).1 ++ (det (h, p)).2)) j
            rw [hval]
            exact hmem
    _ ≤ (2 * (j : ℝ≥0∞) + 1) / capacitySpaceSize (U := U) := by
          have hbound :=
            probEvent_uniformPerm_prod_freshOptionalApply_capacitySegment_mem_finset_le_of_exposed_step
              (side := sampleH) (P := P) (read := read) (X := X) (S := S)
              (B := (2 * (j : ℝ≥0∞) + 1))
              (by
                intro hp p
                change ((permFwdCapacityTargetFinset
                  (getBaseTrace ((det (hp, p)).1 ++ (det (hp, p)).2)) j).card : ℝ≥0∞)
                    ≤ 2 * (j : ℝ≥0∞) + 1
                exact_mod_cast permFwdCapacityTargetFinset_card_le
                  (StmtIn := StmtIn) (U := U)
                  (bt := getBaseTrace ((det (hp, p)).1 ++ (det (hp, p)).2)) j)
              (by
                intro hp p _hp z hz
                dsimp only [X, S] at hz ⊢
                unfold capacityTargetStateFinset
                rw [Finset.mem_filter]
                refine ⟨Finset.mem_univ z, ?_⟩
                unfold permFwdCapacityTargetFinset
                exact Finset.mem_union.mpr (Or.inl
                  (mem_priorCapacityTargetFinset_of_mem_permExposedRangeFinset hz)))
              (by
                intro hp p x _hp hread
                dsimp only [X, read] at hread ⊢
                exact spongeDetTrace_permFwd_image_not_mem_exposedRange
                  (StmtIn := StmtIn) (StmtOut := StmtOut) (n := n) (pSpec := pSpec)
                  (U := U) (δ := δ) V maliciousProver (hp, p) hread)
              (by
                intro h p x y' X₀ S₀ hy' hstate
                rcases hstate with ⟨_hp, hX, hS, hread⟩
                have hy : y' ∉ permExposedRangeFinset
                    (getBaseTrace ((det (h, p)).1 ++ (det (h, p)).2)) j := by
                  dsimp only [X] at hX
                  intro hmem
                  apply hy'
                  exact hX ▸ hmem
                have hswap := spongeDetTrace_permFwd_swap_prefix_read_targets
                  (StmtIn := StmtIn) (StmtOut := StmtOut) (n := n) (pSpec := pSpec)
                  (U := U) (δ := δ) V maliciousProver h p hread hy
                obtain ⟨hprefix, hread', htargets⟩ := hswap
                refine ⟨trivial, ?_, ?_, ?_⟩
                · dsimp only [X]
                  dsimp only [det]
                  exact (permExposedRangeFinset_eq_of_take_eq hprefix).trans hX
                · dsimp only [S]
                  dsimp only [det]
                  exact htargets.trans hS
                · dsimp only [read]
                  dsimp only [det]
                  exact hread')
          exact hbound

/-- The eager-sponge inverse fresh-hit bound.  This is the `E_{p^{-1}}` companion of the
forward contract and uses the exposed *domain* set together with inverse permutation sampling. -/
lemma sponge_permBwdFreshHit_first_noReplacement_contract
    [fU : Fintype U] [Nonempty U]
    (V : Verifier []ₒ StmtIn StmtOut pSpec)
    (maliciousProver : MaliciousProver []ₒ pSpec StmtIn U δ) (j : ℕ) :
    Pr[ fun tr => E_first_at (tr.1 ++ tr.2) j ∧
        permBwdFreshHitAt (getBaseTrace (tr.1 ++ tr.2)) j |
        lemma5_8SpongeTraceDist (StmtIn := StmtIn) (StmtOut := StmtOut) (n := n)
          (pSpec := pSpec) (U := U) (δ := δ) (initSponge := (D_𝔖 StmtIn U).sample)
          (implSponge := (D_𝔖 StmtIn U).eagerImpl) V maliciousProver]
      ≤ (2 * (j : ℝ≥0∞) + 1) / capacitySpaceSize (U := U) := by
  classical
  letI : Fintype U := fU
  let exp := lemma5_8SpongeTraceDist (StmtIn := StmtIn) (StmtOut := StmtOut) (n := n)
    (pSpec := pSpec) (U := U) (δ := δ) (initSponge := (D_𝔖 StmtIn U).sample)
    (implSponge := (D_𝔖 StmtIn U).eagerImpl) V maliciousProver
  let det := spongeDetTrace (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec)
    (U := U) (δ := δ) V maliciousProver
  let Qleft : QueryLog (duplexSpongeChallengeOracle StmtIn U) ×
      QueryLog (duplexSpongeChallengeOracle StmtIn U) → Prop :=
    fun tr => E_first_at (tr.1 ++ tr.2) j ∧
      permBwdFreshHitAt (getBaseTrace (tr.1 ++ tr.2)) j
  have hLeftMap :
      Pr[ Qleft | exp] =
        Pr[ Qleft ∘ det | (D_𝔖 StmtIn U).sample] := by
    exact probEvent_lemma5_8SpongeTraceDist_eq_map
      (StmtIn := StmtIn) (StmtOut := StmtOut) (n := n) (pSpec := pSpec)
      (U := U) (δ := δ) V maliciousProver Qleft
  change Pr[ Qleft | exp] ≤ (2 * (j : ℝ≥0∞) + 1) / capacitySpaceSize (U := U)
  rw [hLeftMap]
  let sampleH : ProbComp (StmtIn → Vector U SpongeSize.C) :=
    ($ᵗ (OracleReduction.OracleFamily (StmtIn →ₒ Vector U SpongeSize.C)))
  let sampleHP : ProbComp ((StmtIn → Vector U SpongeSize.C) ×
      Equiv.Perm (CanonicalSpongeState U)) := do
    let h ← sampleH
    let p ← $ᵗ (Equiv.Perm (CanonicalSpongeState U))
    pure (h, p)
  rw [show (D_𝔖 StmtIn U).sample = sampleHP by rfl]
  let P : (StmtIn → Vector U SpongeSize.C) × Equiv.Perm (CanonicalSpongeState U) → Prop :=
    fun _ => True
  let read : (StmtIn → Vector U SpongeSize.C) × Equiv.Perm (CanonicalSpongeState U) →
      Option (CanonicalSpongeState U) :=
    fun hp => permBwdOutputAt (getBaseTrace ((det hp).1 ++ (det hp).2)) j
  let X : (StmtIn → Vector U SpongeSize.C) × Equiv.Perm (CanonicalSpongeState U) →
      Finset (CanonicalSpongeState U) :=
    fun hp => permExposedDomainFinset (getBaseTrace ((det hp).1 ++ (det hp).2)) j
  let S : (StmtIn → Vector U SpongeSize.C) × Equiv.Perm (CanonicalSpongeState U) →
      Finset (Vector U SpongeSize.C) :=
    fun hp => permBwdCapacityTargetFinset (getBaseTrace ((det hp).1 ++ (det hp).2)) j
  calc
    Pr[ Qleft ∘ det | sampleHP]
        ≤ Pr[ fun hp => P hp ∧ ∃ y : CanonicalSpongeState U,
            read hp = some y ∧ (hp.2.symm y).capacitySegment ∈ S hp | sampleHP] := by
          apply probEvent_mono
          intro hp _ hhit
          rcases hp with ⟨h, p⟩
          obtain ⟨_hfirst, hfresh⟩ := hhit
          obtain ⟨c, hout, hmem⟩ :=
            permBwdFreshHitAt_imp_mem_targetFinset (StmtIn := StmtIn) (U := U)
              (j := j) hfresh
          obtain ⟨y, hread⟩ := exists_permBwdOutputAt_of_permInvRangeCapAt_target hout
          dsimp [det] at hfresh hout hmem hread
          have houtTable := spongeDetTrace_permBwdOutput_rangeCap_eq
            (StmtIn := StmtIn) (StmtOut := StmtOut) (n := n) (pSpec := pSpec)
            (U := U) (δ := δ) V maliciousProver (h, p) hread
          have hval : (p.symm y).capacitySegment = c := by
            have hsome : some (p.symm y).capacitySegment = some c := by
              rw [← houtTable]
              exact hout
            exact Option.some.inj hsome
          refine ⟨trivial, y, ?_, ?_⟩
          · exact hread
          · change (p.symm y).capacitySegment ∈
              permBwdCapacityTargetFinset
                (getBaseTrace ((det (h, p)).1 ++ (det (h, p)).2)) j
            rw [hval]
            exact hmem
    _ ≤ (2 * (j : ℝ≥0∞) + 1) / capacitySpaceSize (U := U) := by
          have hbound :=
            probEvent_uniformPerm_prod_freshOptionalSymmApply_capacitySegment_mem_finset_le_of_exposed_step
              (side := sampleH) (P := P) (read := read) (X := X) (S := S)
              (B := (2 * (j : ℝ≥0∞) + 1))
              (by
                intro hp p
                change ((permBwdCapacityTargetFinset
                  (getBaseTrace ((det (hp, p)).1 ++ (det (hp, p)).2)) j).card : ℝ≥0∞)
                    ≤ 2 * (j : ℝ≥0∞) + 1
                exact_mod_cast permBwdCapacityTargetFinset_card_le
                  (StmtIn := StmtIn) (U := U)
                  (bt := getBaseTrace ((det (hp, p)).1 ++ (det (hp, p)).2)) j)
              (by
                intro hp p _hp z hz
                dsimp only [X, S] at hz ⊢
                unfold capacityTargetStateFinset
                rw [Finset.mem_filter]
                refine ⟨Finset.mem_univ z, ?_⟩
                unfold permBwdCapacityTargetFinset
                exact Finset.mem_union.mpr (Or.inl
                  (mem_priorCapacityTargetFinset_of_mem_permExposedDomainFinset hz)))
              (by
                intro hp p y _hp hread
                dsimp only [X, read] at hread ⊢
                exact spongeDetTrace_permBwd_preimage_not_mem_exposedDomain
                  (StmtIn := StmtIn) (StmtOut := StmtOut) (n := n) (pSpec := pSpec)
                  (U := U) (δ := δ) V maliciousProver (hp, p) hread)
              (by
                intro h p y x' X₀ S₀ hx' hstate
                rcases hstate with ⟨_hp, hX, hS, hread⟩
                have hx : x' ∉ permExposedDomainFinset
                    (getBaseTrace ((det (h, p)).1 ++ (det (h, p)).2)) j := by
                  dsimp only [X] at hX
                  intro hmem
                  apply hx'
                  exact hX ▸ hmem
                have hswap := spongeDetTrace_permBwd_swap_prefix_read_targets
                  (StmtIn := StmtIn) (StmtOut := StmtOut) (n := n) (pSpec := pSpec)
                  (U := U) (δ := δ) V maliciousProver h p hread hx
                obtain ⟨hprefix, hread', htargets⟩ := hswap
                refine ⟨trivial, ?_, ?_, ?_⟩
                · dsimp only [X, det]
                  exact (permExposedDomainFinset_eq_of_take_eq hprefix).trans hX
                · dsimp only [S, det]
                  exact htargets.trans hS
                · dsimp only [read, det]
                  exact hread')
          exact hbound

end BadEventDS

end DuplexSpongeFS

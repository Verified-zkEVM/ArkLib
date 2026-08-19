/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen
-/

import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.BadEventsProb.FiniteTarget

/-!
# Product fresh-sample probability lemmas

These are small probability primitives for Lemma 5.8 atom contracts.  They capture the paper's
deferred-decision step after a transcript prefix has already fixed a side event: an independent
fresh uniform sample hits one fixed capacity value with probability `1 / |Σ|^c`.
-/

open OracleComp OracleSpec ProtocolSpec

open scoped ENNReal

namespace DuplexSpongeFS

namespace BadEventDS

variable {U : Type} [SpongeUnit U] [SpongeSize]

/-- Reading a rate-coordinate of a canonical sponge state agrees with reading the same coordinate
from the full state. -/
private lemma canonicalSpongeState_rateSegment_get
    (s : CanonicalSpongeState U) {i : ℕ} (hi : i < SpongeSize.R) :
    s.rateSegment[i] = s[i]'(lt_of_lt_of_le hi SpongeSize.R_le_N) := by
  unfold CanonicalSpongeState.rateSegment
  unfold CanonicalSpongeState.takeExact
  rw [Vector.getElem_cast]
  rw [Vector.getElem_take]

/-- Reading a capacity-coordinate of a canonical sponge state agrees with reading the
corresponding full-state coordinate. -/
private lemma canonicalSpongeState_capacitySegment_get
    (s : CanonicalSpongeState U) {i : ℕ} (hi : i < SpongeSize.N)
    (hleR : SpongeSize.R ≤ i) (hiC : i - SpongeSize.R < SpongeSize.C) :
    s.capacitySegment[i - SpongeSize.R] = s[i] := by
  calc
    s.capacitySegment[i - SpongeSize.R] = (Vector.drop s SpongeSize.R)[i - SpongeSize.R] := rfl
    _ = s[SpongeSize.R + (i - SpongeSize.R)] :=
        @Vector.getElem_drop U SpongeSize.N (i - SpongeSize.R) s SpongeSize.R hiC
    _ = s[i] := by
        congr 1
        exact Nat.add_sub_of_le hleR

/-- The capacity fiber of a full sponge state has the expected finite cardinality bound. -/
lemma canonicalSpongeState_capacitySegment_fiber_card_mul_le
    [VCVCompatible U] [Fintype U] [Nonempty U] [DecidableEq U]
    (c : Vector U SpongeSize.C) :
    ((@Finset.univ (CanonicalSpongeState U) Vector.instFintype).filter
      (fun s => s.capacitySegment = c)).card * Fintype.card (Vector U SpongeSize.C) ≤
        @Fintype.card (CanonicalSpongeState U) Vector.instFintype := by
  classical
  let fiber : Type := {s : CanonicalSpongeState U // s.capacitySegment = c}
  have hfintypeCard :
      ((@Finset.univ (CanonicalSpongeState U) Vector.instFintype).filter
        (fun s => s.capacitySegment = c)).card = Fintype.card fiber := by
    rw [Fintype.card_subtype]
  have hinj : Function.Injective (fun s : fiber => s.1.rateSegment) := by
    intro a b hrate
    apply Subtype.ext
    apply Vector.ext
    intro i hi
    by_cases hir : i < SpongeSize.R
    · have hget := congrArg (fun v : Vector U SpongeSize.R => v[i]'hir) hrate
      rw [← canonicalSpongeState_rateSegment_get a.1 hir]
      rw [← canonicalSpongeState_rateSegment_get b.1 hir]
      exact hget
    · have hleR : SpongeSize.R ≤ i := Nat.le_of_not_gt hir
      have hiC : i - SpongeSize.R < SpongeSize.C := by
        have hN : SpongeSize.R + SpongeSize.C = SpongeSize.N := SpongeSize.R_plus_C_eq_N
        omega
      have hcap : a.1.capacitySegment = b.1.capacitySegment := by
        rw [a.2, b.2]
      have hget := congrArg (fun v : Vector U SpongeSize.C => v[i - SpongeSize.R]'hiC) hcap
      rw [← canonicalSpongeState_capacitySegment_get a.1 hi hleR hiC]
      rw [← canonicalSpongeState_capacitySegment_get b.1 hi hleR hiC]
      exact hget
  have hfiber_le : Fintype.card fiber ≤ Fintype.card (Vector U SpongeSize.R) :=
    Fintype.card_le_of_injective (fun s : fiber => s.1.rateSegment) hinj
  have hstateCard :
      Fintype.card (CanonicalSpongeState U) =
        Fintype.card (Vector U SpongeSize.R) * Fintype.card (Vector U SpongeSize.C) := by
    rw [show Fintype.card (CanonicalSpongeState U) =
        Fintype.card (Fin SpongeSize.N → U) by
      exact Fintype.card_congr (Equiv.rootVectorEquivFin (α := U) (n := SpongeSize.N))]
    rw [show Fintype.card (Vector U SpongeSize.R) =
        Fintype.card (Fin SpongeSize.R → U) by
      exact Fintype.card_congr (Equiv.rootVectorEquivFin (α := U) (n := SpongeSize.R))]
    rw [show Fintype.card (Vector U SpongeSize.C) =
        Fintype.card (Fin SpongeSize.C → U) by
      exact Fintype.card_congr (Equiv.rootVectorEquivFin (α := U) (n := SpongeSize.C))]
    rw [Fintype.card_fun, Fintype.card_fun, Fintype.card_fun]
    rw [Fintype.card_fin, Fintype.card_fin, Fintype.card_fin]
    rw [← Nat.pow_add]
    rw [SpongeSize.R_plus_C_eq_N]
  rw [hfintypeCard, hstateCard]
  exact Nat.mul_le_mul_right _ hfiber_le

omit [SpongeUnit U] [SpongeSize] in
/-- Pairing a fixed left component with a sampled right component. -/
lemma probEvent_bind_pure_left_pair {α β : Type} (my : ProbComp β) (x : α)
    (Q : α × β → Prop) :
    Pr[ Q | (my >>= fun y => pure (x, y)) ] = Pr[ fun y => Q (x, y) | my] := by
  have hfun :
      (fun y : β => (pure (x, y) : ProbComp (α × β))) =
        (pure ∘ fun y : β => (x, y)) := by
    funext y
    rfl
  rw [hfun]
  rw [probEvent_bind_pure_comp]
  rfl

omit [SpongeUnit U] [SpongeSize] in
/-- Pairing a sampled left component with a fixed right component. -/
lemma probEvent_bind_pure_pair {α β : Type} (mx : ProbComp α) (y : β)
    (Q : α × β → Prop) :
    Pr[ Q | (mx >>= fun x => pure (x, y)) ] = Pr[ fun x => Q (x, y) | mx] := by
  have hfun :
      (fun x : α => (pure (x, y) : ProbComp (α × β))) =
        (pure ∘ fun x : α => (x, y)) := by
    funext x
    rfl
  rw [hfun]
  rw [probEvent_bind_pure_comp]
  rfl

omit [SpongeUnit U] [SpongeSize] in
/-- Uniform sampling is invariant under a bijection of the sample space. -/
lemma probEvent_uniformSample_equiv_invariant {α : Type} [Fintype α] [Nonempty α]
    [SampleableType α] (T : α ≃ α) (Q : α → Prop) :
    Pr[ Q | ($ᵗ α) ] = Pr[ fun a => Q (T a) | ($ᵗ α) ] := by
  classical
  simp only [probEvent_eq_tsum_ite]
  rw [← Equiv.tsum_eq T (fun a => if Q a then Pr[= a | ($ᵗ α)] else 0)]
  refine tsum_congr (fun a => ?_)
  congr 1
  exact SampleableType.probOutput_selectElem_eq (T a) a

section ProductFreshSample

/-- A uniformly sampled full sponge state has a capacity segment distributed with point
probability at most `1 / |Σ|^c`. -/
lemma probEvent_uniformState_capacitySegment_eq_le
    [Fintype U] [Nonempty U] [DecidableEq U] [VCVCompatible U]
    [SampleableType (CanonicalSpongeState U)]
    (c : Vector U SpongeSize.C) :
    Pr[ fun s : CanonicalSpongeState U => s.capacitySegment = c |
        ($ᵗ (CanonicalSpongeState U)) ]
      ≤ 1 / capacitySpaceSize (U := U) := by
  classical
  rw [probEvent_uniformSample]
  have hfiberNat :=
    canonicalSpongeState_capacitySegment_fiber_card_mul_le (U := U) c
  have hfiber :
      ((Finset.univ.filter (fun s : CanonicalSpongeState U =>
          s.capacitySegment = c)).card : ℝ≥0∞) *
        (@Fintype.card (Vector U SpongeSize.C) Vector.instFintype : ℝ≥0∞)
        ≤ (Fintype.card (CanonicalSpongeState U) : ℝ≥0∞) := by
    exact_mod_cast hfiberNat
  have hcapacityCard :
      (@Fintype.card (Vector U SpongeSize.C) Vector.instFintype : ℝ≥0∞) =
        capacitySpaceSize (U := U) := by
    have hcardVec :
        @Fintype.card (Vector U SpongeSize.C) Vector.instFintype =
          Fintype.card (Fin SpongeSize.C → U) := by
      exact Fintype.card_congr (Equiv.rootVectorEquivFin (α := U) (n := SpongeSize.C))
    rw [hcardVec, Fintype.card_fun, Fintype.card_fin, capacitySpaceSize, Nat.cast_pow]
  rw [hcapacityCard] at hfiber
  rw [ENNReal.div_le_iff_le_mul
    (Or.inl (by simp [Fintype.card_ne_zero]))
    (Or.inl (by simp))]
  rw [show (1 / capacitySpaceSize (U := U)) *
      (Fintype.card (CanonicalSpongeState U) : ℝ≥0∞) =
      (Fintype.card (CanonicalSpongeState U) : ℝ≥0∞) /
        capacitySpaceSize (U := U) by
        rw [div_eq_mul_inv]
        rw [one_mul]
        exact mul_comm ((capacitySpaceSize (U := U))⁻¹)
          (Fintype.card (CanonicalSpongeState U) : ℝ≥0∞)]
  rw [ENNReal.le_div_iff_mul_le
    (Or.inl (by simp [capacitySpaceSize]))
    (Or.inl (by simp [capacitySpaceSize]))]
  exact hfiber

/-- A uniformly sampled full sponge state has capacity segment in a fixed finite set `S` with
probability at most `|S| / |Σ|^c`. -/
lemma probEvent_uniformState_capacitySegment_mem_finset_le
    [Fintype U] [Nonempty U] [DecidableEq U] [VCVCompatible U]
    [SampleableType (CanonicalSpongeState U)]
    (S : Finset (Vector U SpongeSize.C)) :
    Pr[ fun s : CanonicalSpongeState U => s.capacitySegment ∈ S |
        ($ᵗ (CanonicalSpongeState U)) ]
      ≤ (S.card : ℝ≥0∞) / capacitySpaceSize (U := U) := by
  classical
  have hEvent : (fun s : CanonicalSpongeState U => s.capacitySegment ∈ S) =
      fun s : CanonicalSpongeState U =>
        ∃ c ∈ S, s.capacitySegment = c := by
    funext s
    apply propext
    constructor
    · intro hmem
      exact ⟨s.capacitySegment, hmem, rfl⟩
    · intro h
      obtain ⟨c, hmem, hcap⟩ := h
      rw [hcap]
      exact hmem
  rw [hEvent]
  calc
    Pr[ fun s : CanonicalSpongeState U =>
        ∃ c ∈ S, s.capacitySegment = c | ($ᵗ (CanonicalSpongeState U)) ]
        ≤ ∑ c ∈ S,
            Pr[ fun s : CanonicalSpongeState U =>
              s.capacitySegment = c | ($ᵗ (CanonicalSpongeState U)) ] :=
          probEvent_exists_finset_le_sum S _ _
    _ ≤ ∑ _c ∈ S, (1 / capacitySpaceSize (U := U)) := by
        apply Finset.sum_le_sum
        intro c _hc
        exact probEvent_uniformState_capacitySegment_eq_le (U := U) c
    _ = (S.card : ℝ≥0∞) * (capacitySpaceSize (U := U))⁻¹ := by
        rw [Finset.sum_const, nsmul_eq_mul]
        rw [div_eq_mul_inv]
        rw [one_mul]
    _ = (S.card : ℝ≥0∞) / capacitySpaceSize (U := U) := by
        rw [div_eq_mul_inv]

/-- A uniformly sampled capacity block lands in a fixed finite target set with probability at
most `|S| / |Σ|^c`.  This is the direct deferred-decision charge used by a rate-only tail: unlike
the former full-state cache, the sampled value is exactly the capacity exposed at consumption. -/
lemma probEvent_uniformCapacity_mem_finset_le
    [Fintype U] [Nonempty U] [DecidableEq U] [VCVCompatible U]
    [SampleableType (Vector U SpongeSize.C)]
    (S : Finset (Vector U SpongeSize.C)) :
    Pr[ fun c : Vector U SpongeSize.C => c ∈ S |
        ($ᵗ (Vector U SpongeSize.C)) ]
      ≤ (S.card : ℝ≥0∞) / capacitySpaceSize (U := U) := by
  classical
  have hcapacityCard :
      (@Fintype.card (Vector U SpongeSize.C) Vector.instFintype : ℝ≥0∞) =
        capacitySpaceSize (U := U) := by
    have hcardVec :
        @Fintype.card (Vector U SpongeSize.C) Vector.instFintype =
          Fintype.card (Fin SpongeSize.C → U) := by
      exact Fintype.card_congr (Equiv.rootVectorEquivFin (α := U) (n := SpongeSize.C))
    rw [hcardVec, Fintype.card_fun, Fintype.card_fin, capacitySpaceSize, Nat.cast_pow]
  have hEvent : (fun c : Vector U SpongeSize.C => c ∈ S) =
      fun c : Vector U SpongeSize.C => ∃ target ∈ S, c = target := by
    funext c
    apply propext
    constructor
    · intro hmem
      exact ⟨c, hmem, rfl⟩
    · rintro ⟨target, hmem, rfl⟩
      exact hmem
  rw [hEvent]
  calc
    Pr[ fun c : Vector U SpongeSize.C => ∃ target ∈ S, c = target |
        ($ᵗ (Vector U SpongeSize.C)) ]
        ≤ ∑ target ∈ S,
            Pr[ fun c : Vector U SpongeSize.C => c = target |
              ($ᵗ (Vector U SpongeSize.C)) ] :=
          probEvent_exists_finset_le_sum S _ _
    _ = ∑ _target ∈ S, 1 / capacitySpaceSize (U := U) := by
        apply Finset.sum_congr rfl
        intro target htarget
        rw [probEvent_eq_eq_probOutput, probOutput_uniformSample, hcapacityCard, div_eq_mul_inv]
        simp
    _ = (S.card : ℝ≥0∞) / capacitySpaceSize (U := U) := by
        rw [Finset.sum_const, nsmul_eq_mul, div_eq_mul_inv, div_eq_mul_inv]
        simp

end ProductFreshSample

end BadEventDS

end DuplexSpongeFS

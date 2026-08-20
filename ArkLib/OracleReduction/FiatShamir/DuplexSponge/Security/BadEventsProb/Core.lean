/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen
-/

import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.BadEvents
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.QueryCounting
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.ExactVerifierCounting

/-!
# Probabilistic analysis of the duplex-sponge bad event `E` (CO25 Lemma 5.8)

`BadEvents.lean` defines the trace-only bad event `E := E_dup ∨ E_func` (Def 5.7), where each
component is an existential `∃ j : Fin (getBaseTrace tr).length, …` over the deduped base trace
`tr̄`.  To prove the CO25 Lemma 5.8 birthday bound
`max{Pr[E | 𝒟_𝔖], Pr[E | 𝒟_Σ]} ≤ (7T² − 3T)/(2|Σ|^c)` we first refactor `E` into a **per-index**
family and apply a union bound over `Finset.range T`.

This file provides that scaffolding:

- **Per-index predicates** `E_h_at` / `E_p_at` / `E_pinv_at` / `E_func_at` / `E_at` — the body of the
  corresponding `BadEvents.lean` predicate with the outer `∃ j` stripped and `j : ℕ` carrying an
  explicit `j < length` proof.
- **Refactor lemmas** `E_h_iff_exists_at` … and `E_iff_exists_E_at` — `E tr ↔ ∃ j, E_at tr j`.
- **Union bound** `probEvent_E_le_sum_range` — for any experiment whose combined base trace has
  length `≤ T` on its support, `Pr[E] ≤ ∑_{j < T} Pr[E_at · j]`, plus the four-way split
  `probEvent_E_at_le` via subadditivity.
-/

open OracleComp OracleSpec ProtocolSpec

open scoped ENNReal

namespace DuplexSpongeFS

namespace BadEventDS

open DuplexSpongeFS.DSTraceStorage

variable {StmtIn : Type} {n : ℕ} {pSpec : ProtocolSpec n}
  {U : Type} [SpongeUnit U] [SpongeSize]

variable (trace : QueryLog (duplexSpongeChallengeOracle StmtIn U))

/-! ## Per-index bad-event predicates (outer `∃ j` stripped) -/

section PerIndexPredicates

/-- Per-index form of `E_h` (`capacitySegmentDupHash`) at base-trace position `j`. -/
def E_h_at (j : ℕ) : Prop :=
  let baseTrace := getBaseTrace trace
  ∃ hj : j < baseTrace.length, ∃ capSeg : Vector U SpongeSize.C,
    (∃ stmt : StmtIn, baseTrace[j] = ⟨.inl stmt, capSeg⟩) ∧
    isDuplicatedPriorCapacity baseTrace ⟨j, hj⟩ capSeg

/-- Per-index form of `E_p` (`capacitySegmentDupPerm`) at base-trace position `j`. -/
def E_p_at (j : ℕ) : Prop :=
  let baseTrace := getBaseTrace trace
  ∃ hj : j < baseTrace.length, ∃ capSeg : Vector U SpongeSize.C,
    (∃ stateIn stateOut, baseTrace[j] = ⟨.inr <| .inl stateIn, stateOut⟩ ∧
      stateOut.capacitySegment = capSeg) ∧
    isDuplicatedPriorCapacity baseTrace ⟨j, hj⟩ capSeg

/-- Per-index form of `E_pinv` (`capacitySegmentDupPermInv`) at base-trace position `j`. -/
def E_pinv_at (j : ℕ) : Prop :=
  let baseTrace := getBaseTrace trace
  ∃ hj : j < baseTrace.length, ∃ capSeg : Vector U SpongeSize.C,
    (∃ stateOut stateIn, baseTrace[j] = ⟨.inr <| .inr stateOut, stateIn⟩ ∧
      stateIn.capacitySegment = capSeg) ∧
    isDuplicatedPriorCapacity baseTrace ⟨j, hj⟩ capSeg

/-- Per-index form of `E_func` at base-trace position `j`. -/
def E_func_at (j : ℕ) : Prop :=
  let baseTrace := getBaseTrace trace
  ∃ hj : j < baseTrace.length, ∃ stateIn stateOut : CanonicalSpongeState U,
    (baseTrace[j] = ⟨.inr <| .inl stateIn, stateOut⟩ ∧
      ∃ j' < (⟨j, hj⟩ : Fin baseTrace.length),
        (∃ stateOut1 : CanonicalSpongeState U,
          baseTrace[j'] = ⟨.inr <| .inl stateIn, stateOut1⟩ ∧ stateOut1 ≠ stateOut) ∨
        (∃ stateOut2 : CanonicalSpongeState U,
          baseTrace[j'] = ⟨.inr <| .inr stateOut2, stateIn⟩ ∧ stateOut2 ≠ stateOut)) ∨
    (baseTrace[j] = ⟨.inr <| .inr stateOut, stateIn⟩ ∧
      ∃ j' < (⟨j, hj⟩ : Fin baseTrace.length),
        (∃ stateIn1 : CanonicalSpongeState U,
          baseTrace[j'] = ⟨.inr <| .inr stateOut, stateIn1⟩ ∧ stateIn1 ≠ stateIn) ∨
        (∃ stateIn2 : CanonicalSpongeState U,
          baseTrace[j'] = ⟨.inr <| .inl stateIn2, stateOut⟩ ∧ stateIn2 ≠ stateIn))

/-- The forward half of the canonical bidirectional `E_func`, at base-trace position `j`.  This is
the original CO25 Eq. 26 direction and retains its cache-driven probability contribution. -/
def E_func_fwd_at (j : ℕ) : Prop :=
  let baseTrace := getBaseTrace trace
  ∃ hj : j < baseTrace.length, ∃ stateIn stateOut : CanonicalSpongeState U,
    baseTrace[j] = ⟨.inr <| .inl stateIn, stateOut⟩ ∧
      ∃ j' < (⟨j, hj⟩ : Fin baseTrace.length),
        (∃ stateOut1 : CanonicalSpongeState U,
          baseTrace[j'] = ⟨.inr <| .inl stateIn, stateOut1⟩ ∧ stateOut1 ≠ stateOut) ∨
        (∃ stateOut2 : CanonicalSpongeState U,
          baseTrace[j'] = ⟨.inr <| .inr stateOut2, stateIn⟩ ∧ stateOut2 ≠ stateOut)

/-- The backward half of the canonical bidirectional `E_func`, at base-trace position `j`.  It is
needed for Lemma 5.10; in the simulator it contributes zero at an *earliest* bad-event witness. -/
def E_func_bwd_at (j : ℕ) : Prop :=
  let baseTrace := getBaseTrace trace
  ∃ hj : j < baseTrace.length, ∃ stateIn stateOut : CanonicalSpongeState U,
    baseTrace[j] = ⟨.inr <| .inr stateOut, stateIn⟩ ∧
      ∃ j' < (⟨j, hj⟩ : Fin baseTrace.length),
        (∃ stateIn1 : CanonicalSpongeState U,
          baseTrace[j'] = ⟨.inr <| .inr stateOut, stateIn1⟩ ∧ stateIn1 ≠ stateIn) ∨
        (∃ stateIn2 : CanonicalSpongeState U,
          baseTrace[j'] = ⟨.inr <| .inl stateIn2, stateOut⟩ ∧ stateIn2 ≠ stateIn)

/-- Split the single, canonical bidirectional `E_func` into its forward and backward clauses. -/
lemma E_func_at_iff_fwd_or_bwd {j : ℕ} :
    E_func_at trace j ↔ E_func_fwd_at trace j ∨ E_func_bwd_at trace j := by
  constructor
  · rintro ⟨hj, stateIn, stateOut, hF | hB⟩
    · exact Or.inl ⟨hj, stateIn, stateOut, hF⟩
    · exact Or.inr ⟨hj, stateIn, stateOut, hB⟩
  · rintro (⟨hj, stateIn, stateOut, hF⟩ | ⟨hj, stateIn, stateOut, hB⟩)
    · exact ⟨hj, stateIn, stateOut, Or.inl hF⟩
    · exact ⟨hj, stateIn, stateOut, Or.inr hB⟩

/-- Per-index combined bad event: `E_h_at ∨ E_p_at ∨ E_pinv_at ∨ E_func_at` at position `j`. -/
def E_at (j : ℕ) : Prop :=
  E_h_at trace j ∨ E_p_at trace j ∨ E_pinv_at trace j ∨ E_func_at trace j

/-- No canonical bad-event component occurs at any strict earlier base index.  This is the
deferred-decision prefix condition used by first-bad probability arguments.  Keeping it named
separates the stable prefix information from the fresh event at index `j`, whose output capacity is
precisely what gets re-randomized in the sponge permutation proofs. -/
def NoPriorBadAt (j : ℕ) : Prop :=
  ∀ j' < j, ¬ E_at trace j'

/-- The earliest index at which any canonical bad-event component fires.  This is the
first-witness refinement needed for the bidirectional `E_func` analysis: a backward clause can
only appear after an earlier capacity-duplication witness in the sigma experiment. -/
def E_first_at (j : ℕ) : Prop :=
  E_at trace j ∧ NoPriorBadAt trace j

end PerIndexPredicates

/-! ## Refactor: `E ↔ ∃ j, E_at` -/

section TraceEventDecomposition

/-- A per-index bad event fires only at a valid base-trace index. -/
lemma E_at_lt_length {j : ℕ} (h : E_at trace j) : j < (getBaseTrace trace).length := by
  rcases h with h | h | h | h
  · exact h.1
  · exact h.1
  · exact h.1
  · exact h.1

lemma E_h_iff_exists_at : E_h trace ↔ ∃ j, E_h_at trace j := by
  unfold E_h capacitySegmentDupHash E_h_at
  rw [Fin.exists_iff]; simp only [Fin.getElem_fin]

lemma E_p_iff_exists_at : E_p trace ↔ ∃ j, E_p_at trace j := by
  unfold E_p capacitySegmentDupPerm E_p_at
  rw [Fin.exists_iff]; simp only [Fin.getElem_fin]

lemma E_pinv_iff_exists_at : E_pinv trace ↔ ∃ j, E_pinv_at trace j := by
  unfold E_pinv capacitySegmentDupPermInv E_pinv_at
  rw [Fin.exists_iff]; simp only [Fin.getElem_fin]

lemma E_func_iff_exists_at : E_func trace ↔ ∃ j, E_func_at trace j := by
  unfold E_func E_func_at
  rw [Fin.exists_iff]; simp only [Fin.getElem_fin]

/-- **Decomposition refactor.** The trace-only bad event `E` is the pointwise disjunction of the
per-index events over all base-trace positions. -/
lemma E_iff_exists_E_at : E trace ↔ ∃ j, E_at trace j := by
  constructor
  · rintro ((hh | hp | hpi) | hfunc)
    · obtain ⟨j, hj⟩ := (E_h_iff_exists_at trace).mp hh
      exact ⟨j, Or.inl hj⟩
    · obtain ⟨j, hj⟩ := (E_p_iff_exists_at trace).mp hp
      exact ⟨j, Or.inr (Or.inl hj)⟩
    · obtain ⟨j, hj⟩ := (E_pinv_iff_exists_at trace).mp hpi
      exact ⟨j, Or.inr (Or.inr (Or.inl hj))⟩
    · obtain ⟨j, hj⟩ := (E_func_iff_exists_at trace).mp hfunc
      exact ⟨j, Or.inr (Or.inr (Or.inr hj))⟩
  · rintro ⟨j, hj | hj | hj | hj⟩
    · exact Or.inl (Or.inl ((E_h_iff_exists_at trace).mpr ⟨j, hj⟩))
    · exact Or.inl (Or.inr (Or.inl ((E_p_iff_exists_at trace).mpr ⟨j, hj⟩)))
    · exact Or.inl (Or.inr (Or.inr ((E_pinv_iff_exists_at trace).mpr ⟨j, hj⟩)))
    · exact Or.inr ((E_func_iff_exists_at trace).mpr ⟨j, hj⟩)

/-- **First-witness decomposition.** `E` holds iff it has an earliest per-index witness. -/
lemma E_iff_exists_E_first_at : E trace ↔ ∃ j, E_first_at trace j := by
  classical
  constructor
  · intro hE
    obtain ⟨j, hj⟩ := (E_iff_exists_E_at trace).mp hE
    let hExists : ∃ i, E_at trace i := ⟨j, hj⟩
    refine ⟨Nat.find hExists, Nat.find_spec hExists, ?_⟩
    intro j' hj' hj'E
    exact (Nat.not_lt_of_ge (Nat.find_min' hExists hj'E)) hj'
  · rintro ⟨j, hj, _⟩
    exact (E_iff_exists_E_at trace).mpr ⟨j, hj⟩

end TraceEventDecomposition

/-! ## Union bound: `Pr[E] ≤ ∑_{j < T} Pr[E_at · j]`


Both stated generically over an experiment `exp : ProbComp α` and a base-trace extraction
`f : α → QueryLog (…)`.  For Lemma 5.8's combined trace `tr_P̃ ‖ tr_V` take
`f := fun tr => tr.1 ++ tr.2`. -/
section TraceEventUnionBound


variable {α : Type}

/-- Monotonicity helper for first-witness refinements: adding a left conjunct can only shrink an
event. -/
lemma probEvent_and_left_le
    (exp : ProbComp α) (P Q : α → Prop) :
    Pr[ fun x => P x ∧ Q x | exp] ≤ Pr[ Q | exp] := by
  apply probEvent_mono
  intro x _ hx
  exact hx.2

/-- **First-witness union bound.** The same event bound, refined to the earliest per-index
witness.  This is the form used to charge the forward `E_func` clause while proving that the
backward clause has zero probability in the sigma experiment. -/
lemma probEvent_E_le_sum_range_first
    (exp : ProbComp α) (f : α → QueryLog (duplexSpongeChallengeOracle StmtIn U)) (T : ℕ)
    (h_basetrace_len : ∀ x ∈ support exp, (getBaseTrace (f x)).length ≤ T) :
    Pr[ fun x => E (f x) | exp] ≤ ∑ j ∈ Finset.range T, Pr[ fun x => E_first_at (f x) j | exp] := by
  have hmono :
      Pr[ fun x => E (f x) | exp]
        ≤ Pr[ fun x => ∃ j ∈ Finset.range T, E_first_at (f x) j | exp] := by
    apply probEvent_mono
    intro x hx hE
    obtain ⟨j, hj⟩ := (E_iff_exists_E_first_at (f x)).mp hE
    exact ⟨j, Finset.mem_range.mpr
      (lt_of_lt_of_le (E_at_lt_length (f x) hj.1) (h_basetrace_len x hx)), hj⟩
  exact le_trans hmono
    (probEvent_exists_finset_le_sum (Finset.range T) exp (fun j x => E_first_at (f x) j))

/-- Fully first-witness split.  Unlike `probEvent_E_first_at_le_split`, this keeps the earliest
bad-index conjunct on the capacity events too.  This is the right interface for sponge-side
permutation atoms: a random-permutation deferred-decision proof is sound under the no-prior-bad
prefix, but unconditional adaptive swap-invariance is not. -/
lemma probEvent_E_first_at_le_split_all_first
    (exp : ProbComp α) (f : α → QueryLog (duplexSpongeChallengeOracle StmtIn U)) (j : ℕ) :
    Pr[ fun x => E_first_at (f x) j | exp]
      ≤ Pr[ fun x => E_first_at (f x) j ∧ E_h_at (f x) j | exp]
        + Pr[ fun x => E_first_at (f x) j ∧ E_p_at (f x) j | exp]
        + Pr[ fun x => E_first_at (f x) j ∧ E_pinv_at (f x) j | exp]
        + Pr[ fun x => E_first_at (f x) j ∧ E_func_at (f x) j | exp] := by
  have hmono :
      Pr[ fun x => E_first_at (f x) j | exp]
        ≤ Pr[ fun x =>
          (E_first_at (f x) j ∧ E_h_at (f x) j)
            ∨ (E_first_at (f x) j ∧ E_p_at (f x) j)
            ∨ (E_first_at (f x) j ∧ E_pinv_at (f x) j)
            ∨ (E_first_at (f x) j ∧ E_func_at (f x) j) | exp] := by
    apply probEvent_mono
    intro x _ hFirst
    rcases hFirst.1 with hH | hP | hPinv | hFunc
    · exact Or.inl ⟨hFirst, hH⟩
    · exact Or.inr (Or.inl ⟨hFirst, hP⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨hFirst, hPinv⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨hFirst, hFunc⟩))
  calc Pr[ fun x => E_first_at (f x) j | exp]
      ≤ Pr[ fun x =>
          (E_first_at (f x) j ∧ E_h_at (f x) j)
            ∨ (E_first_at (f x) j ∧ E_p_at (f x) j)
            ∨ (E_first_at (f x) j ∧ E_pinv_at (f x) j)
            ∨ (E_first_at (f x) j ∧ E_func_at (f x) j) | exp] := hmono
    _ ≤ Pr[ fun x => E_first_at (f x) j ∧ E_h_at (f x) j | exp]
        + Pr[ fun x =>
            (E_first_at (f x) j ∧ E_p_at (f x) j)
              ∨ (E_first_at (f x) j ∧ E_pinv_at (f x) j)
              ∨ (E_first_at (f x) j ∧ E_func_at (f x) j) | exp] :=
        probEvent_or_le exp _ _
    _ ≤ Pr[ fun x => E_first_at (f x) j ∧ E_h_at (f x) j | exp]
        + (Pr[ fun x => E_first_at (f x) j ∧ E_p_at (f x) j | exp]
          + Pr[ fun x =>
              (E_first_at (f x) j ∧ E_pinv_at (f x) j)
                ∨ (E_first_at (f x) j ∧ E_func_at (f x) j) | exp]) := by
          gcongr
          exact probEvent_or_le exp _ _
    _ ≤ Pr[ fun x => E_first_at (f x) j ∧ E_h_at (f x) j | exp]
        + (Pr[ fun x => E_first_at (f x) j ∧ E_p_at (f x) j | exp]
          + (Pr[ fun x => E_first_at (f x) j ∧ E_pinv_at (f x) j | exp]
            + Pr[ fun x => E_first_at (f x) j ∧ E_func_at (f x) j | exp])) := by
          gcongr
          exact probEvent_or_le exp _ _
    _ = _ := by ring

/-- First-witness union bound with the earliest-index conjunct retained on all four clauses. -/
lemma probEvent_E_le_sum_range_first_split_all_first
    (exp : ProbComp α) (f : α → QueryLog (duplexSpongeChallengeOracle StmtIn U)) (T : ℕ)
    (h_basetrace_len : ∀ x ∈ support exp, (getBaseTrace (f x)).length ≤ T) :
    Pr[ fun x => E (f x) | exp]
      ≤ ∑ j ∈ Finset.range T,
          (Pr[ fun x => E_first_at (f x) j ∧ E_h_at (f x) j | exp]
            + Pr[ fun x => E_first_at (f x) j ∧ E_p_at (f x) j | exp]
            + Pr[ fun x => E_first_at (f x) j ∧ E_pinv_at (f x) j | exp]
            + Pr[ fun x => E_first_at (f x) j ∧ E_func_at (f x) j | exp]) := by
  refine le_trans (probEvent_E_le_sum_range_first exp f T h_basetrace_len) ?_
  exact Finset.sum_le_sum (fun j _ => probEvent_E_first_at_le_split_all_first exp f j)

end TraceEventUnionBound

/-! ## Event count summation: the per-index count sums to `(7T² − 3T)/2`


With `Finset.range T` running over base-trace positions `0, …, T−1`, position `j` contributes
`2j` (from `E_h`, ≤ `2j` prior output/input caps) `+ (2j+1)` (`E_p`) `+ (2j+1)` (`E_pinv`) `+ j`
(`E_func`) `= 7j + 2` collision targets (paper's `2(j−1)+(2j−1)+(2j−1)+(j−1)` under the
`0`-indexed shift). Summing: `∑_{j<T} (7j+2) = 7·T(T−1)/2 + 2T = (7T²−3T)/2`, matching
`lemma5_8Bound`'s numerator `(7·T² − 3·T)`. -/
section EventCountSummation

omit [SpongeUnit U] [SpongeSize] in
lemma sum_range_perIndexCount (T : ℕ) :
    ∑ j ∈ Finset.range T, (7 * (j : ℝ) + 2) = (7 * (T : ℝ) ^ 2 - 3 * T) / 2 := by
  induction T with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    ring

omit [SpongeUnit U] [SpongeSize] in
/-- `ℝ≥0∞` form of `sum_range_perIndexCount`, packaged as `ENNReal.ofReal` of the closed form. -/
lemma sum_range_perIndexCount_ennreal (T : ℕ) :
    ∑ j ∈ Finset.range T, (7 * (j : ℝ≥0∞) + 2)
      = ENNReal.ofReal ((7 * (T : ℝ) ^ 2 - 3 * T) / 2) := by
  have hnn : ∀ j ∈ Finset.range T, (7 * (j : ℝ) + 2) = ((7 * j + 2 : ℕ) : ℝ) := by
    intro j _; push_cast; ring
  rw [← sum_range_perIndexCount T, ENNReal.ofReal_sum_of_nonneg (by intro j _; positivity)]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [show (7 * (j : ℝ≥0∞) + 2) = ((7 * j + 2 : ℕ) : ℝ≥0∞) by push_cast; ring,
    show (7 * (j : ℝ) + 2) = ((7 * j + 2 : ℕ) : ℝ) by push_cast; ring,
    ENNReal.ofReal_natCast]

end EventCountSummation

/-! ## Generic trace combiner


Given, for a fixed experiment, the per-index freshness bounds
`Pr[E_h_at · j] ≤ 2j/|Σ|^c`, `Pr[E_p_at · j] ≤ (2j+1)/|Σ|^c`, `Pr[E_pinv_at · j] ≤ (2j+1)/|Σ|^c`,
`Pr[E_func_at · j] ≤ j/|Σ|^c`, together with the trace-length bound `≤ T`, the bad-event
probability is at most `lemma5_8Bound = (7T² − 3T)/(2|Σ|^c)`.  This packages the bound summations into the
final numeric bound; only the four per-index bounds and the length bound remain experiment-specific. -/
section GenericTraceCombiner


variable [Fintype U] [Nonempty U] {α : Type}

/-- `|Σ|^c` as an `ℝ≥0∞`, the common denominator of the per-index bounds. -/
noncomputable abbrev capacitySpaceSize : ℝ≥0∞ := (Fintype.card U : ℝ≥0∞) ^ SpongeSize.C

omit [SpongeUnit U] in
private lemma capacitySpaceSize_pos : 0 < (Fintype.card U : ℝ) ^ SpongeSize.C := by
  have : 0 < Fintype.card U := Fintype.card_pos
  positivity

/-- **First-witness combiner, all clauses.** This variant keeps the `E_first_at` conjunct on
hash, permutation, inverse-permutation, and functional clauses.  It is the sound assembly target
for deferred-decision atom proofs, especially the sponge-side random-permutation atoms where the
conditioning information is exactly "no earlier bad event". -/
lemma probEvent_E_le_lemma5_8Bound_all_first
    (exp : ProbComp α) (f : α → QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (tₕ tₚ tₚᵢ L : ℕ)
    (h_basetrace_len : ∀ x ∈ support exp, (getBaseTrace (f x)).length ≤ tₕ + 1 + tₚ + L + tₚᵢ)
    (hh : ∀ j, Pr[ fun x => E_first_at (f x) j ∧ E_h_at (f x) j | exp]
      ≤ (2 * (j : ℝ≥0∞)) / capacitySpaceSize (U := U))
    (hp : ∀ j, Pr[ fun x => E_first_at (f x) j ∧ E_p_at (f x) j | exp]
      ≤ (2 * (j : ℝ≥0∞) + 1) / capacitySpaceSize (U := U))
    (hpi : ∀ j, Pr[ fun x => E_first_at (f x) j ∧ E_pinv_at (f x) j | exp]
      ≤ (2 * (j : ℝ≥0∞) + 1) / capacitySpaceSize (U := U))
    (hfunc : ∀ j, Pr[ fun x => E_first_at (f x) j ∧ E_func_at (f x) j | exp]
      ≤ (j : ℝ≥0∞) / capacitySpaceSize (U := U)) :
    Pr[ fun x => E (f x) | exp]
      ≤ ENNReal.ofReal (lemma5_8Bound U tₕ tₚ tₚᵢ L) := by
  set T := tₕ + 1 + tₚ + L + tₚᵢ with hT
  set K : ℝ≥0∞ := capacitySpaceSize (U := U) with hK
  calc Pr[ fun x => E (f x) | exp]
      ≤ ∑ j ∈ Finset.range T,
          (Pr[ fun x => E_first_at (f x) j ∧ E_h_at (f x) j | exp]
            + Pr[ fun x => E_first_at (f x) j ∧ E_p_at (f x) j | exp]
            + Pr[ fun x => E_first_at (f x) j ∧ E_pinv_at (f x) j | exp]
            + Pr[ fun x => E_first_at (f x) j ∧ E_func_at (f x) j | exp]) :=
        probEvent_E_le_sum_range_first_split_all_first exp f T h_basetrace_len
    _ ≤ ∑ j ∈ Finset.range T,
          ((2 * (j : ℝ≥0∞)) / K + (2 * (j : ℝ≥0∞) + 1) / K
            + (2 * (j : ℝ≥0∞) + 1) / K + (j : ℝ≥0∞) / K) := by
        refine Finset.sum_le_sum (fun j _ => ?_)
        gcongr
        · exact hh j
        · exact hp j
        · exact hpi j
        · exact hfunc j
    _ = ∑ j ∈ Finset.range T, ((7 * (j : ℝ≥0∞) + 2) / K) := by
        refine Finset.sum_congr rfl (fun j _ => ?_)
        simp only [div_eq_mul_inv]
        ring
    _ = (∑ j ∈ Finset.range T, (7 * (j : ℝ≥0∞) + 2)) / K := by
        simp only [div_eq_mul_inv, ← Finset.sum_mul]
    _ = ENNReal.ofReal ((7 * (T : ℝ) ^ 2 - 3 * T) / 2) / K := by
        rw [sum_range_perIndexCount_ennreal]
    _ = ENNReal.ofReal (lemma5_8Bound U tₕ tₚ tₚᵢ L) := by
        have hKeq : K = ENNReal.ofReal ((Fintype.card U : ℝ) ^ SpongeSize.C) := by
          rw [hK]
          simp only [capacitySpaceSize]
          rw [ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_natCast]
        rw [hKeq, ← ENNReal.ofReal_div_of_pos (capacitySpaceSize_pos (U := U))]
        congr 1
        rw [lemma5_8Bound]
        push_cast [hT]
        rw [div_div]

end GenericTraceCombiner

/-! ## Assembly of Lemma 5.8

`lemma_5_8` is now proven **modulo** the two experiment-specific inputs to
`probEvent_E_le_lemma5_8Bound` — the trace-length bound and the four per-index freshness
bounds — for each of the sponge (`𝒟_𝔖`) and simulator (`𝒟_Σ`) sides.  Those obligations are
factored out as the named helper lemmas below so each can be attacked independently; the numeric
`max`-assembly is complete and verified. -/

variable {StmtOut : Type}
  [VCVCompatible StmtIn] [∀ i, VCVCompatible (pSpec.Challenge i)]
  [codec : CodecCore pSpec U] {δ : ℕ} [DecidableEq StmtIn] [DecidableEq U]
  [VCVCompatible U] [SampleableType U]
  [∀ i, Fintype (pSpec.Message i)]
  [∀ i, DecidableEq (pSpec.Message i)]
  {T_H : Type} {T_P : Type}
  [LawfulTraceNablaImpl T_H T_P StmtIn U]

/-! ### Trace length growth bound — the log grows by at most the number of DS queries


Running any computation under `lemma5_8CombinedImpl` appends one log entry per *successful*
DS (`Sum.inr`) query and nothing else; aborts keep the log.  So on the support of the run, the
final log length is bounded by the initial length plus the computation's total DS-query bound. -/
section TraceLengthGrowthBound


/-- Support-level log-length bound for the Lemma-5.8 combined implementation. -/
lemma logLength_le_of_isQueryBoundP {σ : Type}
    (impl : QueryImpl (duplexSpongeChallengeOracle StmtIn U) (StateT σ (OptionT ProbComp)))
    {α : Type} {oa : OracleComp ([]ₒ + duplexSpongeChallengeOracle StmtIn U) α} {n : ℕ}
    (hb : OracleComp.IsQueryBoundP oa (fun t => t.isRight = true) n)
    (st : σ × QueryLog ([]ₒ + duplexSpongeChallengeOracle StmtIn U))
    {r : Option α × (σ × QueryLog ([]ₒ + duplexSpongeChallengeOracle StmtIn U))}
    (hr : r ∈ support (((simulateQ (lemma5_8CombinedImpl impl) oa).run).run st)) :
    r.2.2.length ≤ st.2.length + n := by
  induction oa using OracleComp.inductionOn generalizing st n r with
  | pure x =>
    simp only [simulateQ_pure] at hr
    have : r = (some x, st) := by simpa using hr
    subst this
    exact Nat.le_add_right _ _
  | query_bind t mx ih =>
    rw [OracleComp.isQueryBoundP_query_bind_iff] at hb
    match t with
    | Sum.inl q => exact PEmpty.elim q
    | Sum.inr q =>
      have hn : 0 < n := hb.1.resolve_left (by simp)
      simp only [simulateQ_query_bind, lemma5_8CombinedImpl, OracleQuery.input_query,
        OracleQuery.cont_query, QueryImpl.add_apply_inr, lemma5_8WrappedDSImpl,
        Option.elimM, monadLift_self, OptionT.run_bind, OptionT.run_mk, StateT.run_bind,
        support_bind, Set.mem_iUnion] at hr
      obtain ⟨i, hi, hri⟩ := hr
      have hi' : i ∈ support ((impl q st.1).run >>= fun r₀ =>
          match r₀ with
          | none => (pure (none, st) :
              ProbComp (Option (([]ₒ + duplexSpongeChallengeOracle StmtIn U).Range (Sum.inr q)) ×
                (σ × QueryLog ([]ₒ + duplexSpongeChallengeOracle StmtIn U))))
          | some (a, s') => pure (some a, (s', st.2 ++ [⟨Sum.inr q, a⟩]))) := hi
      rw [mem_support_bind_iff] at hi'
      obtain ⟨r₀, hr₀, hi'⟩ := hi'
      match r₀ with
      | none =>
        rw [mem_support_pure_iff] at hi'
        subst hi'
        have hri' : r ∈ support ((pure ((none : Option α), st) :
            ProbComp (Option α × (σ × QueryLog ([]ₒ + duplexSpongeChallengeOracle StmtIn U))))) :=
          hri
        rw [mem_support_pure_iff] at hri'
        subst hri'
        exact Nat.le_add_right _ _
      | some (a, s') =>
        rw [mem_support_pure_iff] at hi'
        subst hi'
        have hri' : r ∈ support ((simulateQ (lemma5_8CombinedImpl impl) (mx a)).run.run
            (s', st.2 ++ [⟨Sum.inr q, a⟩])) := hri
        have hbnd := hb.2 a
        rw [if_pos (by simp : (Sum.inr q : ([]ₒ + duplexSpongeChallengeOracle StmtIn U).Domain
          ).isRight = true)] at hbnd
        have hlen := ih a hbnd _ hri'
        simp only [List.length_append, List.length_singleton] at hlen
        omega

/-- The empty oracle spec is (vacuously) finite and inhabited per query point. -/
instance : (([]ₒ : OracleSpec.{0, 0} PEmpty.{1})).Fintype where
  fintype_B t := t.elim

instance : (([]ₒ : OracleSpec.{0, 0} PEmpty.{1})).Inhabited where
  inhabited_B t := t.elim

/-- The concrete `IsUniformSpec` instances for the Lemma-5.8 oracle surfaces (uniform
challenge/permutation answers are well-defined since `U` is a finite nonempty sponge unit). -/
noncomputable instance : IsUniformSpec (duplexSpongeForwardOracle StmtIn U) :=
  IsUniformSpec.ofFintypeInhabited _

noncomputable instance :
    IsUniformSpec (([]ₒ : OracleSpec.{0, 0} PEmpty.{1}) + duplexSpongeForwardOracle StmtIn U) :=
  IsUniformSpec.ofFintypeInhabited _

noncomputable instance :
    IsUniformSpec (([]ₒ : OracleSpec.{0, 0} PEmpty.{1}) + duplexSpongeChallengeOracle StmtIn U) :=
  IsUniformSpec.ofFintypeInhabited _

end TraceLengthGrowthBound

/-! ### Combining the per-class totals into the total DS-query bound -/

section TotalQueryBound

/-- The three DS classes are exhaustive on `Sum.inr` and disjoint: per-class totals combine
into the total DS (`Sum.isRight`) bound. -/
lemma isQueryBoundP_isRight_of_classes {α : Type}
    {oa : OracleComp ([]ₒ + duplexSpongeChallengeOracle StmtIn U) α} {tₕ tₚ tₚᵢ : ℕ}
    (hh : OracleComp.IsQueryBoundP oa
      (fun t => isHashQueryPoint (StmtIn := StmtIn) (U := U) t = true) tₕ)
    (hp : OracleComp.IsQueryBoundP oa
      (fun t => isFwdPermQueryPoint (StmtIn := StmtIn) (U := U) t = true) tₚ)
    (hpi : OracleComp.IsQueryBoundP oa
      (fun t => isBwdPermQueryPoint (StmtIn := StmtIn) (U := U) t = true) tₚᵢ) :
    OracleComp.IsQueryBoundP oa (fun t => t.isRight = true) (tₕ + tₚ + tₚᵢ) := by
  have h2 := IsQueryBoundP.or_add hh hp (by
    rintro (e | (s | (c | c))) ⟨h1, h2⟩ <;>
      simp_all [isHashQueryPoint, isFwdPermQueryPoint])
  have h3 := IsQueryBoundP.or_add h2 hpi (by
    rintro (e | (s | (c | c))) ⟨h1, h2⟩ <;>
      simp_all [isHashQueryPoint, isFwdPermQueryPoint, isBwdPermQueryPoint])
  rw [isQueryBoundP_congr_pred (p' := fun t => Sum.isRight t = true)] at h3
  · exact h3
  · rintro (e | (s | (c | c))) <;>
      simp [isHashQueryPoint, isFwdPermQueryPoint, isBwdPermQueryPoint]

end TotalQueryBound

/-! ### Verifier query bounds: the wide forward verifier is a `(1, L, 0)`-query algorithm -/

section VerifierQueryBound

/-- Wide-spec forward verifier, exact stateful count: `≤ N_𝒱`.

Unlike the historical `L` and `\bar L` variants below, this is obtained by
following the live cursor through `Start`, salt absorption, and every
subsequent absorb/squeeze action.  It is therefore valid when any action
begins within a partially used rate block. -/
lemma runForwardVerifierWide_fwd_bound_exact
    [IsUniformSpec (([]ₒ : OracleSpec.{0, 0} PEmpty.{1}) + duplexSpongeForwardOracle StmtIn U)]
    [IsUniformSpec (([]ₒ : OracleSpec.{0, 0} PEmpty.{1}) + duplexSpongeChallengeOracle StmtIn U)]
    (V : Verifier ([]ₒ : OracleSpec.{0, 0} PEmpty.{1}) StmtIn StmtOut pSpec) (stmtIn : StmtIn)
    (proof : DSSaltedProof (pSpec := pSpec) (U := U) δ) :
    OracleComp.IsQueryBoundP (runForwardVerifierWide (oSpec := []ₒ) δ V stmtIn proof)
      (fun t => isFwdPermQueryPoint (StmtIn := StmtIn) (U := U) t = true)
      (verifierPermCallCount (pSpec := pSpec) (δ := δ)) := by
  rw [runForwardVerifierWide]
  refine isQueryBoundP_liftComp' _
    (p := fun t => isNarrowFwdPermPoint (oSpec := []ₒ) (StmtIn := StmtIn) (U := U) t = true)
    (fun t => ?_) (dsfsForwardVerify_fwd_bound_exact V stmtIn proof)
  rcases t with e | (s | c)
  · exact e.elim
  · rfl
  · rfl

/-- Wide-spec forward verifier, hash class: `≤ 1`. -/
lemma runForwardVerifierWide_hash_bound
    [IsUniformSpec (([]ₒ : OracleSpec.{0, 0} PEmpty.{1}) + duplexSpongeForwardOracle StmtIn U)]
    [IsUniformSpec (([]ₒ : OracleSpec.{0, 0} PEmpty.{1}) + duplexSpongeChallengeOracle StmtIn U)]
    (V : Verifier ([]ₒ : OracleSpec.{0, 0} PEmpty.{1}) StmtIn StmtOut pSpec) (stmtIn : StmtIn)
    (proof : DSSaltedProof (pSpec := pSpec) (U := U) δ) :
    OracleComp.IsQueryBoundP (runForwardVerifierWide (oSpec := []ₒ) δ V stmtIn proof)
      (fun t => isHashQueryPoint (StmtIn := StmtIn) (U := U) t = true) 1 := by
  rw [runForwardVerifierWide]
  refine isQueryBoundP_liftComp' _
    (p := fun t => isNarrowHashPoint (oSpec := []ₒ) (StmtIn := StmtIn) (U := U) t = true)
    (fun t => ?_) (dsfsForwardVerify_hash_bound V stmtIn proof)
  rcases t with e | (s | c)
  · exact e.elim
  · rfl
  · rfl

/-- Wide-spec forward verifier, inverse-permutation class: `0` — the narrow spec has no `p⁻¹`
slot, so no narrow query can land in the wide inverse class. -/
lemma runForwardVerifierWide_bwd_bound
    [IsUniformSpec (([]ₒ : OracleSpec.{0, 0} PEmpty.{1}) + duplexSpongeForwardOracle StmtIn U)]
    [IsUniformSpec (([]ₒ : OracleSpec.{0, 0} PEmpty.{1}) + duplexSpongeChallengeOracle StmtIn U)]
    (V : Verifier ([]ₒ : OracleSpec.{0, 0} PEmpty.{1}) StmtIn StmtOut pSpec) (stmtIn : StmtIn)
    (proof : DSSaltedProof (pSpec := pSpec) (U := U) δ) :
    OracleComp.IsQueryBoundP (runForwardVerifierWide (oSpec := []ₒ) δ V stmtIn proof)
      (fun t => isBwdPermQueryPoint (StmtIn := StmtIn) (U := U) t = true) 0 := by
  rw [runForwardVerifierWide]
  refine isQueryBoundP_liftComp' _
    (p := fun _ => False)
    (fun t => ?_) (isQueryBoundP_zero_of_forall_not _ (by simp))
  rcases t with e | (s | c)
  · exact e.elim
  · exact iff_of_false Bool.false_ne_true not_false
  · exact iff_of_false Bool.false_ne_true not_false

end VerifierQueryBound

/-! ### Generic length bound for the abortable experiment -/

section AbortableExperimentLengthBound

/-- Exact stateful trace-length form of the abortable Lemma-5.8 experiment.

The verifier segment has one `DS.Start` hash occurrence and at most the actual
stateful number `N_𝒱` of forward permutation occurrences.  In contrast to the
historical `L` and `\bar L` bounds, no action is charged as if it began at a
fresh rate block. -/
lemma lemma5_8ProjectedTraceDistAbortable_length_exact {σ : Type}
    [IsUniformSpec (duplexSpongeForwardOracle StmtIn U)]
    [IsUniformSpec (([]ₒ : OracleSpec.{0, 0} PEmpty.{1}) + duplexSpongeForwardOracle StmtIn U)]
    [IsUniformSpec (([]ₒ : OracleSpec.{0, 0} PEmpty.{1}) + duplexSpongeChallengeOracle StmtIn U)]
    (init : ProbComp σ)
    (impl : QueryImpl (duplexSpongeChallengeOracle StmtIn U) (StateT σ (OptionT ProbComp)))
    (V : Verifier ([]ₒ : OracleSpec.{0, 0} PEmpty.{1}) StmtIn StmtOut pSpec)
    (maliciousProver : MaliciousProver []ₒ pSpec StmtIn U δ)
    (tₕ tₚ tₚᵢ : ℕ)
    (hMaliciousBound : IsLemma5_8QueryBound
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) maliciousProver tₕ tₚ tₚᵢ) :
    ∀ tr ∈ support (lemma5_8ProjectedTraceDistAbortable (StmtIn := StmtIn) (StmtOut := StmtOut)
        (pSpec := pSpec) (U := U) (δ := δ) init impl V maliciousProver),
      (getBaseTrace (tr.1 ++ tr.2)).length ≤
        tₕ + 1 + tₚ + verifierPermCallCount (pSpec := pSpec) (δ := δ) + tₚᵢ := by
  intro tr htr
  have hproverBound : OracleComp.IsQueryBoundP maliciousProver
      (fun t => t.isRight = true) (tₕ + tₚ + tₚᵢ) :=
    isQueryBoundP_isRight_of_classes hMaliciousBound.1 hMaliciousBound.2.1 hMaliciousBound.2.2
  rw [lemma5_8ProjectedTraceDistAbortable] at htr
  rw [mem_support_bind_iff] at htr
  obtain ⟨s₀, _, htr⟩ := htr
  rw [mem_support_bind_iff] at htr
  obtain ⟨proverResult, hpr, htr⟩ := htr
  have hplen := logLength_le_of_isQueryBoundP impl hproverBound (s₀, ([] : QueryLog _)) hpr
  simp only [List.length_nil, Nat.zero_add] at hplen
  obtain ⟨res, s₁, trP⟩ := proverResult
  rcases res with _ | ⟨stmtIn, proof⟩
  · rw [mem_support_pure_iff] at htr
    subst htr
    calc
      (getBaseTrace (lemma5_8ProjectTraceLog (StmtIn := StmtIn) (U := U) trP ++ [])).length
          ≤ (lemma5_8ProjectTraceLog (StmtIn := StmtIn) (U := U) trP ++ []).length :=
        (getBaseTrace_sublist _).length_le
      _ ≤ trP.length := by
        rw [List.append_nil, lemma5_8ProjectTraceLog]
        exact List.length_filterMap_le _ _
      _ ≤ tₕ + 1 + tₚ + verifierPermCallCount (pSpec := pSpec) (δ := δ) + tₚᵢ := by
        have hp : trP.length ≤ tₕ + tₚ + tₚᵢ := hplen
        omega
  · rw [mem_support_bind_iff] at htr
    obtain ⟨verifierResult, hvr, htr⟩ := htr
    rw [mem_support_pure_iff] at htr
    subst htr
    have hverifBound : OracleComp.IsQueryBoundP
        (runForwardVerifierWide (oSpec := []ₒ) δ V stmtIn proof)
        (fun t => t.isRight = true)
        (1 + verifierPermCallCount (pSpec := pSpec) (δ := δ) + 0) :=
      isQueryBoundP_isRight_of_classes
        (runForwardVerifierWide_hash_bound V stmtIn proof)
        (runForwardVerifierWide_fwd_bound_exact V stmtIn proof)
        (runForwardVerifierWide_bwd_bound V stmtIn proof)
    have hvlen := logLength_le_of_isQueryBoundP impl hverifBound (s₁, ([] : QueryLog _)) hvr
    simp only [List.length_nil, Nat.zero_add] at hvlen
    calc
      (getBaseTrace (lemma5_8ProjectTraceLog (StmtIn := StmtIn) (U := U) trP ++
          lemma5_8ProjectTraceLog (StmtIn := StmtIn) (U := U) verifierResult.2.2)).length
          ≤ (lemma5_8ProjectTraceLog (StmtIn := StmtIn) (U := U) trP ++
            lemma5_8ProjectTraceLog (StmtIn := StmtIn) (U := U) verifierResult.2.2).length :=
        (getBaseTrace_sublist _).length_le
      _ ≤ trP.length + verifierResult.2.2.length := by
        rw [List.length_append]
        gcongr <;> · rw [lemma5_8ProjectTraceLog]; exact List.length_filterMap_le _ _
      _ ≤ tₕ + 1 + tₚ + verifierPermCallCount (pSpec := pSpec) (δ := δ) + tₚᵢ := by
        have hp : trP.length ≤ tₕ + tₚ + tₚᵢ := hplen
        omega

end AbortableExperimentLengthBound

/-! ### Sponge and Sigma trace-length bounds


Instantiations of the generic bound for the two concrete experiments. -/
section SpongeTraceLengthBounds


/-- Exact stateful base-trace length for the ideal-permutation experiment. -/
lemma lemma5_8_sponge_length_exact
    (V : Verifier []ₒ StmtIn StmtOut pSpec)
    (maliciousProver : MaliciousProver []ₒ pSpec StmtIn U δ)
    (tₕ tₚ tₚᵢ : ℕ)
    (hMaliciousBound : IsLemma5_8QueryBound
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) maliciousProver tₕ tₚ tₚᵢ) :
    ∀ tr ∈ support (lemma5_8SpongeTraceDist (StmtIn := StmtIn) (StmtOut := StmtOut)
        (n := n) (pSpec := pSpec) (U := U) (δ := δ)
        (initSponge := (D_𝔖 StmtIn U).sample)
        (implSponge := (D_𝔖 StmtIn U).eagerImpl) V maliciousProver),
      (getBaseTrace (tr.1 ++ tr.2)).length ≤
        tₕ + 1 + tₚ + verifierPermCallCount (pSpec := pSpec) (δ := δ) + tₚᵢ := by
  rw [lemma5_8SpongeTraceDist]
  exact lemma5_8ProjectedTraceDistAbortable_length_exact _ _ V maliciousProver tₕ tₚ tₚᵢ
    hMaliciousBound

end SpongeTraceLengthBounds

/-! ## Shared base-trace capacity readouts -/

/-- The (≤ 2) capacity segments a base-trace entry exposes as collision sources, indexed by
`Fin 2`: a hash entry exposes only its output (`k = 0`); a permutation entry exposes both its
domain- and range-state capacities. -/
def entryCapAt :
    ((t : (duplexSpongeChallengeOracle StmtIn U).Domain) ×
      (duplexSpongeChallengeOracle StmtIn U).Range t) → Fin 2 → Option (Vector U SpongeSize.C)
  | ⟨.inl _, out⟩, k => if k = 0 then some out else none
  | ⟨.inr (.inl sIn), sOut⟩, k =>
      if k = 0 then some sIn.capacitySegment else some sOut.capacitySegment
  | ⟨.inr (.inr sOut), sIn⟩, k =>
      if k = 0 then some sOut.capacitySegment else some sIn.capacitySegment

end BadEventDS

end DuplexSpongeFS

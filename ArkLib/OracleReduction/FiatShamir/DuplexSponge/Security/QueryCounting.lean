/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen
-/

import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Defs

/-!
# Query counting for the lazy duplex sponge (CO25 Lemma 5.8 support)

CO25's Lemma 5.8 needs the forward DSFS verifier to be a `(1, L, 0)`-query algorithm
(`L = pSpec.totalNumPermQueries`).  The verifier's oracle queries all come from the sponge
transcript re-derivation (`deriveTranscriptDSFSSalted`): one `h` query (`DuplexSponge.start`)
plus the permutation queries of the `absorb`/`squeeze` phases.

The sponge is **lazy**: `absorb` permutes only when the absorb position is at the end of the
rate segment *and* input remains; `squeeze` permutes only when the squeeze position is at the
end of the rate segment.  Consequently a phase processing `m` units from position `a ≤ R`
makes exactly `(a + m − 1)/R − (a − 1)/R` permutation queries (`ℕ`-division), which is:

- `0` for the salt phase (`a = 0`, `m = δ ≤ R`): the stated `(1, L, 0)`
  budget requires `δ ≤ SpongeSize.R`;
- at most `⌈m/R⌉ = L_P(i)` (resp. `L_V(i)`) for each message (resp. challenge) phase,
  from *any* starting position `a ≤ R` — so no cross-phase position invariant is needed
  (positions are `≤ R` by their `Fin (R+1)` type).

This file provides:

- `spongeOpCount` — the shared query-count recursion of `absorb`/`squeeze`, with its closed
  form and the two bounds above;
- `IsQueryBoundP` transport along `liftComp`/`liftM` (sub-spec embeddings), plus a disjoint
  per-class sum lemma;
- `IsQueryBoundP` bounds for `DuplexSponge.absorb` / `DuplexSponge.squeeze`.

The verifier-level `(1, L, 0)` bound and the Lemma 5.8 trace-length bound build on these in
`BadEventsProb.lean`.
-/

open OracleComp OracleSpec

namespace DuplexSpongeFS

/-! ## The shared `absorb`/`squeeze` query-count recursion -/

/-- Number of permutation queries made by a lazy sponge phase (`absorb` or `squeeze`)
processing `m` units starting at position `a`, for rate `R`: a query fires exactly when the
position is at `R` with units remaining, after which the position resets to `1` (one unit
consumed by the freshly permuted block). -/
def spongeOpCount (R : ℕ) : ℕ → ℕ → ℕ
  | _, 0 => 0
  | a, m + 1 => if a = R then spongeOpCount R 1 m + 1 else spongeOpCount R (a + 1) m

@[simp]
lemma spongeOpCount_zero (R a : ℕ) : spongeOpCount R a 0 = 0 := rfl

lemma spongeOpCount_succ (R a m : ℕ) :
    spongeOpCount R a (m + 1) =
      if a = R then spongeOpCount R 1 m + 1 else spongeOpCount R (a + 1) m := rfl

/-- Closed form for the lazy sponge query count: processing `m` units from position `a ≤ R`
makes `(a + m − 1)/R − (a − 1)/R` permutation queries. -/
lemma spongeOpCount_eq (R : ℕ) (hR : 0 < R) :
    ∀ (m a : ℕ), a ≤ R → spongeOpCount R a m = (a + m - 1) / R - (a - 1) / R := by
  intro m
  induction m with
  | zero => intro a _; simp
  | succ m ih =>
    intro a ha
    rw [spongeOpCount_succ]
    by_cases haR : a = R
    · rw [if_pos haR, ih 1 (by omega), haR,
        show 1 + m - 1 = m by omega, show (1 : ℕ) - 1 = 0 by rfl,
        show R + (m + 1) - 1 = m + R by omega,
        Nat.zero_div, Nat.add_div_right _ hR,
        Nat.div_eq_of_lt (show R - 1 < R by omega)]
      simp
    · have haR' : a < R := lt_of_le_of_ne ha haR
      rw [if_neg haR, ih (a + 1) (by omega),
        show a + 1 + m - 1 = a + (m + 1) - 1 by omega,
        show a + 1 - 1 = a by omega,
        Nat.div_eq_of_lt haR',
        Nat.div_eq_of_lt (show a - 1 < R by omega)]

/-- The salt phase makes no permutation query: `m ≤ R` units from the fresh position `0`. -/
lemma spongeOpCount_zero_pos (R m : ℕ) (hR : 0 < R) (hm : m ≤ R) :
    spongeOpCount R 0 m = 0 := by
  rw [spongeOpCount_eq R hR m 0 (by omega),
    show (0 : ℕ) + m - 1 = m - 1 by omega,
    Nat.div_eq_of_lt (show m - 1 < R by omega)]
  simp

/-- Phase-local bound: from *any* position `a ≤ R`, processing `m` units makes at most
`(m + R − 1)/R` (i.e. `⌈m/R⌉`) permutation queries. -/
lemma spongeOpCount_le (R : ℕ) (hR : 0 < R) (a m : ℕ) (ha : a ≤ R) :
    spongeOpCount R a m ≤ (m + R - 1) / R := by
  rw [spongeOpCount_eq R hR m a ha]
  calc (a + m - 1) / R - (a - 1) / R ≤ (a + m - 1) / R := Nat.sub_le _ _
    _ ≤ (m + R - 1) / R := Nat.div_le_div_right (by omega)

/-- Bridge to the `ℚ`-valued ceiling used by the paper's block counts
(`numPermQueriesMessage`, `numPermQueriesChallenge`): `⌈m/R⌉ = (m + R − 1)/R`. -/
lemma nat_ceil_div_eq (m R : ℕ) (hR : 0 < R) :
    ⌈(m : ℚ) / (R : ℚ)⌉₊ = (m + R - 1) / R := by
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    simp only [Nat.cast_zero, zero_div, Nat.ceil_zero]
    exact (Nat.div_eq_of_lt (by omega)).symm
  · have hdm := Nat.div_add_mod (m + R - 1) R
    have hmod := Nat.mod_lt (m + R - 1) hR
    set k := (m + R - 1) / R with hk
    rw [Nat.mul_comm] at hdm
    have hkpos : 1 ≤ k := by rw [hk, Nat.one_le_div_iff hR]; omega
    have hRQ : (0 : ℚ) < (R : ℚ) := by exact_mod_cast hR
    -- `m ≤ k·R` and `(k−1)·R < m`, in `ℕ`.
    have hle : m ≤ k * R := by omega
    have hlt : (k - 1) * R < m := by
      have e : (k - 1) * R = k * R - 1 * R := by rw [Nat.sub_mul]
      rw [e, one_mul]
      omega
    refine le_antisymm ?_ ?_
    · rw [Nat.ceil_le, div_le_iff₀ hRQ]
      exact_mod_cast hle
    · have hstep : (k - 1 : ℕ) < ⌈(m : ℚ) / (R : ℚ)⌉₊ := by
        rw [Nat.lt_ceil, lt_div_iff₀ hRQ]
        exact_mod_cast hlt
      omega

/-! ## Generic `IsQueryBoundP` helpers -/

section IsQueryBoundPHelpers

open OracleComp

universe u

variable {ι τ : Type u} {spec : OracleSpec.{u, u} ι} {superSpec : OracleSpec.{u, u} τ}
  {α β : Type u}

/-- A computation trivially satisfies bound `0` for a class it never queries because the
class is empty. -/
lemma isQueryBoundP_zero_of_forall_not {p : spec.Domain → Prop} [DecidablePred p]
    (oa : OracleComp spec α) (h : ∀ t, ¬ p t) :
    IsQueryBoundP oa p 0 := by
  induction oa using OracleComp.inductionOn with
  | pure x => simp
  | query_bind t mx ih =>
    rw [isQueryBoundP_query_bind_iff]
    exact ⟨Or.inl (h t), fun u => by simpa [h t] using ih u⟩

/-- Per-class totals add over a disjunction of disjoint classes. -/
lemma IsQueryBoundP.or_add {oa : OracleComp spec α}
    {p₁ p₂ : spec.Domain → Prop} [DecidablePred p₁] [DecidablePred p₂] {n₁ n₂ : ℕ}
    (h₁ : IsQueryBoundP oa p₁ n₁) (h₂ : IsQueryBoundP oa p₂ n₂)
    (hdisj : ∀ t, ¬ (p₁ t ∧ p₂ t)) :
    IsQueryBoundP oa (fun t => p₁ t ∨ p₂ t) (n₁ + n₂) := by
  induction oa using OracleComp.inductionOn generalizing n₁ n₂ with
  | pure x => simp
  | query_bind t mx ih =>
    rw [isQueryBoundP_query_bind_iff] at h₁ h₂ ⊢
    refine ⟨?_, fun u => ?_⟩
    · by_cases hp₁ : p₁ t
      · rcases h₁.1 with h | h
        · exact absurd hp₁ h
        · exact Or.inr (by omega)
      · by_cases hp₂ : p₂ t
        · rcases h₂.1 with h | h
          · exact absurd hp₂ h
          · exact Or.inr (by omega)
        · exact Or.inl (by tauto)
    · have hih := ih u (h₁.2 u) (h₂.2 u)
      refine hih.mono ?_
      by_cases hp₁ : p₁ t
      · have hp₂ : ¬ p₂ t := fun hp₂ => hdisj t ⟨hp₁, hp₂⟩
        have hn₁ : 0 < n₁ := (h₁.1).resolve_left (not_not_intro hp₁)
        simp only [if_pos hp₁, if_neg hp₂, if_pos (Or.inl hp₁)]
        omega
      · by_cases hp₂ : p₂ t
        · have hn₂ : 0 < n₂ := (h₂.1).resolve_left (not_not_intro hp₂)
          simp only [if_neg hp₁, if_pos hp₂, if_pos (Or.inr hp₂)]
          omega
        · simp only [if_neg hp₁, if_neg hp₂, if_neg (show ¬ (p₁ t ∨ p₂ t) by tauto)]
          omega

/-- Transport an `IsQueryBoundP` bound along a sub-spec lift (`liftComp`): if the lifted image
of each source query point satisfies the target-class predicate iff the point satisfies the
source-class predicate, the per-class total is preserved. -/
lemma isQueryBoundP_liftComp [IsUniformSpec superSpec]
    [MonadLiftT (OracleQuery spec) (OracleQuery superSpec)]
    {p : spec.Domain → Prop} [DecidablePred p]
    {q : superSpec.Domain → Prop} [DecidablePred q]
    (hpq : ∀ t : spec.Domain,
      q ((liftM (OracleSpec.query t) : OracleQuery superSpec (spec.Range t)).input) ↔ p t)
    {oa : OracleComp spec α} {n : ℕ}
    (hb : IsQueryBoundP oa p n) :
    IsQueryBoundP (liftComp oa superSpec) q n := by
  rw [liftComp_def]
  have hre : ∀ t : spec.Domain,
      (liftM (OracleSpec.query t) : OracleComp superSpec (spec.Range t))
        = (liftM (OracleSpec.query t) : OracleQuery superSpec (spec.Range t)).cont <$>
            liftM (OracleSpec.query
              ((liftM (OracleSpec.query t) : OracleQuery superSpec (spec.Range t)).input)) := by
    intro t
    conv_lhs => rw [show (liftM (OracleSpec.query t) : OracleComp superSpec (spec.Range t))
        = liftM (liftM (OracleSpec.query t) : OracleQuery superSpec (spec.Range t)) from rfl]
    conv_lhs => rw [← OracleQuery.cont_map_query_input
      (q := (liftM (OracleSpec.query t) : OracleQuery superSpec (spec.Range t)))]
    exact OracleComp.liftM_map _ _
  refine hb.simulateQ_of_step (fun t _ => ?_) (fun t hnpt => ?_)
  · rw [hre t, isQueryBoundP_map_iff, isQueryBoundP_query_iff]
    exact fun _ => one_pos
  · rw [hre t, isQueryBoundP_map_iff, isQueryBoundP_query_iff]
    exact fun hq => absurd ((hpq t).mp hq) hnpt

/-- Transport an `IsQueryBoundP` bound along **any lawful** computation-level lift
`OracleComp spec → OracleComp superSpec`.  The lift instance is an **explicit** argument so it
is solved by unification against the goal (never re-synthesized — the composite
`MonadLiftT (OracleComp _) (OracleComp _)` instances arising from sub-spec chains are only
propositionally, not definitionally, equal across synthesis paths).  The single-query image
obligation `hquery` is discharged at the application site. -/
lemma isQueryBoundP_liftM_of_lawful
    (instL : MonadLiftT (OracleComp spec) (OracleComp superSpec))
    [instLaw : @LawfulMonadLiftT (OracleComp spec) (OracleComp superSpec) _ _ instL]
    {p : spec.Domain → Prop} [DecidablePred p]
    {q : superSpec.Domain → Prop} [DecidablePred q]
    (hquery : ∀ t : spec.Domain,
      IsQueryBoundP
        (@liftM _ _ instL _ (liftM (OracleSpec.query t) : OracleComp spec (spec.Range t)))
        q (if p t then 1 else 0))
    {oa : OracleComp spec α} {n : ℕ}
    (hb : IsQueryBoundP oa p n) :
    IsQueryBoundP (@liftM _ _ instL _ oa) q n := by
  induction oa using OracleComp.inductionOn generalizing n with
  | pure x =>
    have h : @liftM _ _ instL _ (pure x : OracleComp spec α) = pure x :=
      instLaw.monadLift_pure x
    rw [h]
    simp
  | query_bind t mx ih =>
    rw [isQueryBoundP_query_bind_iff] at hb
    have h : @liftM _ _ instL _ (liftM (OracleSpec.query t) >>= mx : OracleComp spec α)
        = @liftM _ _ instL _ (liftM (OracleSpec.query t) : OracleComp spec (spec.Range t))
            >>= fun u => @liftM _ _ instL _ (mx u) :=
      instLaw.monadLift_bind _ _
    rw [h]
    have hcomb := isQueryBoundP_bind (hquery t) (fun u _ => ih u (hb.2 u))
    refine hcomb.mono ?_
    by_cases hpt : p t
    · rcases hb.1 with hnp | hn
      · exact absurd hpt hnp
      · simp only [if_pos hpt]
        omega
    · simp only [if_neg hpt]
      omega

/-- Reshape the computation-level lift of a single query into map-of-query form, exposing the
lifted query's input point for `isQueryBoundP_query_iff`. -/
lemma liftM_query_reshape [MonadLiftT (OracleQuery spec) (OracleQuery superSpec)]
    (t : spec.Domain) :
    (liftM (liftM (OracleSpec.query t) : OracleQuery superSpec (spec.Range t)) :
      OracleComp superSpec (spec.Range t))
      = (liftM (OracleSpec.query t) : OracleQuery superSpec (spec.Range t)).cont <$>
          (liftM (OracleSpec.query ((liftM (OracleSpec.query t) :
            OracleQuery superSpec (spec.Range t)).input)) : OracleComp superSpec _) := by
  conv_lhs => rw [← OracleQuery.cont_map_query_input
    (q := (liftM (OracleSpec.query t) : OracleQuery superSpec (spec.Range t)))]
  exact OracleComp.liftM_map _ _

/-- Explicit-instance variant of `isQueryBoundP_liftComp`: the query-level lift instance is an
explicit argument solved by unification against the goal (sub-spec instance chains are
path-dependent; see `isQueryBoundP_liftM_of_lawful`). -/
lemma isQueryBoundP_liftComp' [IsUniformSpec superSpec]
    (instQ : MonadLiftT (OracleQuery spec) (OracleQuery superSpec))
    {p : spec.Domain → Prop} [DecidablePred p]
    {q : superSpec.Domain → Prop} [DecidablePred q]
    (hpq : ∀ t : spec.Domain,
      q ((@liftM _ _ instQ _ (OracleSpec.query t) :
        OracleQuery superSpec (spec.Range t)).input) ↔ p t)
    {oa : OracleComp spec α} {n : ℕ}
    (hb : IsQueryBoundP oa p n) :
    IsQueryBoundP (liftComp oa superSpec (h := instQ)) q n := by
  letI : MonadLiftT (OracleQuery spec) (OracleQuery superSpec) := instQ
  rw [liftComp_def]
  have hre : ∀ t : spec.Domain,
      (liftM (OracleSpec.query t) : OracleComp superSpec (spec.Range t))
        = (liftM (OracleSpec.query t) : OracleQuery superSpec (spec.Range t)).cont <$>
            liftM (OracleSpec.query
              ((liftM (OracleSpec.query t) :
                OracleQuery superSpec (spec.Range t)).input)) := by
    intro t
    conv_lhs => rw [show (liftM (OracleSpec.query t) : OracleComp superSpec (spec.Range t))
        = liftM (liftM (OracleSpec.query t) : OracleQuery superSpec (spec.Range t)) from rfl]
    conv_lhs => rw [← OracleQuery.cont_map_query_input
      (q := (liftM (OracleSpec.query t) : OracleQuery superSpec (spec.Range t)))]
    exact OracleComp.liftM_map _ _
  refine hb.simulateQ_of_step (fun t _ => ?_) (fun t hnpt => ?_)
  · rw [hre t, isQueryBoundP_map_iff, isQueryBoundP_query_iff]
    exact fun _ => one_pos
  · rw [hre t, isQueryBoundP_map_iff, isQueryBoundP_query_iff]
    exact fun hq => absurd ((hpq t).mp hq) hnpt

end IsQueryBoundPHelpers

/-- A computation over the empty spec makes no queries: it is a `pure`. -/
lemma emptySpec_eq_pure {α : Type} (oa : OracleComp ([]ₒ : OracleSpec.{0, 0} PEmpty.{1}) α) :
    ∃ x, oa = pure x := by
  induction oa using OracleComp.inductionOn with
  | pure x => exact ⟨x, rfl⟩
  | query_bind t mx ih => exact PEmpty.elim t

/-! ## Query bounds for the sponge operations -/

section SpongeOps

variable {U : Type} [SpongeUnit U] [SpongeSize] {C : Type} [SpongeState U C]

/-- Structural upper bound for the forward-permutation queries made by `absorb`.

The equality-level dynamic statement is `absorb_counting_exact` below.  Keeping the two facts
separate matters: `IsQueryBoundP` is an upper-bound predicate, whereas the stateful replay needs
the path-by-path equality supplied by the counting-oracle theorem. -/
lemma absorb_isQueryBoundP (ls : List U) (sponge : DuplexSponge U C) :
    IsQueryBoundP (DuplexSponge.absorb sponge ls) (fun _ => True)
      (spongeOpCount SpongeSize.R sponge.absorbPos.val ls.length) := by
  induction ls generalizing sponge with
  | nil => simp [DuplexSponge.absorb]
  | cons x xs ih =>
    rw [DuplexSponge.absorb]
    by_cases hpos : (sponge.absorbPos : ℕ) = SpongeSize.R
    · rw [if_pos hpos, List.length_cons, hpos, spongeOpCount_succ, if_pos rfl]
      simp only [HasQuery.instOfMonadLift_query]
      rw [isQueryBoundP_query_bind_iff]
      refine ⟨Or.inr (by omega), fun u => ?_⟩
      refine (ih _).mono (le_of_eq ?_)
      have hR : 0 < SpongeSize.R := Nat.pos_of_ne_zero (NeZero.ne _)
      simp [Nat.mod_eq_of_lt (show 1 < SpongeSize.R + 1 by omega)]
    · rw [if_neg hpos]
      have hval : sponge.absorbPos.val < SpongeSize.R :=
        lt_of_le_of_ne (Fin.is_le _) hpos
      have hsucc : ((sponge.absorbPos + 1 : Fin (SpongeSize.R + 1)) : ℕ)
          = sponge.absorbPos.val + 1 := by
        rw [Fin.val_add_one_of_lt]
        rw [Fin.lt_def, Fin.val_last]
        exact hval
      rw [List.length_cons, spongeOpCount_succ, if_neg hpos]
      refine (ih _).mono (le_of_eq ?_)
      simp [hsucc]

/-- Sum the per-query-state counters emitted by `countingOracle`.  A forward permutation has
query index `C` (its complete input state), so its total number of calls is the finite sum here,
not the count at one distinguished index. -/
def queryCountTotal [Fintype C] (qc : QueryCount C) : ℕ :=
  ∑ c, qc c

/-- Removing the one query at `t` from a positive count decreases the finite total by exactly
one.  This is the accounting step used when the support characterization peels a real oracle
query from a lazy sponge execution. -/
lemma queryCountTotal_update_pred [Fintype C] [DecidableEq C]
    (qc : QueryCount C) (t : C) (ht : qc t ≠ 0) :
    queryCountTotal (Function.update qc t (qc t - 1)) = queryCountTotal qc - 1 := by
  unfold queryCountTotal
  rw [Finset.sum_update_of_mem (Finset.mem_univ t)]
  rw [← Finset.sum_erase_add Finset.univ qc (Finset.mem_univ t)]
  rw [Finset.sdiff_singleton_eq_erase]
  have hpos : 0 < qc t := Nat.pos_of_ne_zero ht
  omega

/-- Exact dynamic count for a lazy absorb: on every concrete counting-oracle execution path,
the total number of forward calls is the value-free stateful schedule count.  This is the first
operational half of the `N_𝒱` bridge; in particular it covers salt and prover-message absorbs
that start or end in a partially used rate block. -/
lemma absorb_counting_exact [Fintype C] [DecidableEq C]
    (ls : List U) (sponge : DuplexSponge U C)
    (z : DuplexSponge U C × QueryCount C)
    (hz : z ∈ support (countingOracle.simulate (DuplexSponge.absorb sponge ls) 0)) :
    queryCountTotal z.2 = spongeOpCount SpongeSize.R sponge.absorbPos.val ls.length := by
  induction ls generalizing sponge z with
  | nil =>
      rw [DuplexSponge.absorb.eq_def, countingOracle.mem_support_simulate_pure_iff] at hz
      subst z
      simp [queryCountTotal, spongeOpCount]
  | cons x xs ih =>
      unfold DuplexSponge.absorb at hz
      change queryCountTotal z.2 =
        spongeOpCount SpongeSize.R sponge.absorbPos.val (xs.length + 1)
      by_cases hpos : (sponge.absorbPos : ℕ) = SpongeSize.R
      · rw [if_pos hpos] at hz
        simp only [HasQuery.instOfMonadLift_query] at hz
        rw [countingOracle.mem_support_simulate_queryBind_iff] at hz
        rcases hz with ⟨hCount, permuted, htail⟩
        have htailCount := ih _ _ htail
        change queryCountTotal (Function.update z.2 sponge.state (z.2 sponge.state - 1)) =
          spongeOpCount SpongeSize.R ((1 : Fin (SpongeSize.R + 1)) : ℕ) xs.length at htailCount
        have hR : 0 < SpongeSize.R := SpongeSize.R_pos
        have hOne : ((1 : Fin (SpongeSize.R + 1)) : ℕ) = 1 := by
          change 1 % (SpongeSize.R + 1) = 1
          exact Nat.mod_eq_of_lt (by omega)
        rw [hOne] at htailCount
        rw [spongeOpCount_succ, hpos, if_pos rfl]
        have hupdate := queryCountTotal_update_pred z.2 sponge.state hCount
        have hsum : z.2 sponge.state ≤ queryCountTotal z.2 := by
          exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ _)
        calc
          queryCountTotal z.2 =
              queryCountTotal (Function.update z.2 sponge.state (z.2 sponge.state - 1)) + 1 := by
            omega
          _ = spongeOpCount SpongeSize.R 1 xs.length + 1 := by
            rw [htailCount]
      · rw [if_neg hpos] at hz
        have htailCount := ih _ _ hz
        rw [spongeOpCount_succ, if_neg hpos]
        have hval : sponge.absorbPos.val < SpongeSize.R :=
          lt_of_le_of_ne (Fin.is_le _) hpos
        have hsucc : ((sponge.absorbPos + 1 : Fin (SpongeSize.R + 1)) : ℕ) =
            sponge.absorbPos.val + 1 := by
          rw [Fin.val_add_one_of_lt]
          rw [Fin.lt_def, Fin.val_last]
          exact hval
        simpa [hsucc] using htailCount

/-- Exact dynamic count for a lazy squeeze.  This is the squeeze counterpart of
`absorb_counting_exact`: on every counting-oracle execution path, the number of actual forward
permutation calls is the value-free stateful cursor count.  In particular, this does not round a
partially consumed rate block to a fresh block. -/
lemma squeeze_counting_exact [Fintype C] [DecidableEq C]
    (len : Nat) (sponge : DuplexSponge U C)
    (z : (Vector U len × DuplexSponge U C) × QueryCount C)
    (hz : z ∈ support (countingOracle.simulate (DuplexSponge.squeeze sponge len) 0)) :
    queryCountTotal z.2 = spongeOpCount SpongeSize.R sponge.squeezePos.val len := by
  induction len generalizing sponge with
  | zero =>
      rw [DuplexSponge.squeeze.eq_def, countingOracle.mem_support_simulate_pure_iff] at hz
      subst z
      simp [queryCountTotal, spongeOpCount]
  | succ n ih =>
      unfold DuplexSponge.squeeze at hz
      by_cases hpos : (sponge.squeezePos : ℕ) = SpongeSize.R
      · rw [if_pos hpos] at hz
        simp only [HasQuery.instOfMonadLift_query] at hz
        rw [countingOracle.mem_support_simulate_queryBind_iff] at hz
        rcases hz with ⟨hCount, permuted, htail⟩
        simp [countingOracle.simulate] at htail
        rcases htail with ⟨a, b, htail, _⟩
        have htail' :
            ((a, b), Function.update z.2 sponge.state (z.2 sponge.state - 1)) ∈
              support (countingOracle.simulate
                (DuplexSponge.squeeze
                  { state := permuted, absorbPos := 0, squeezePos := 1 } n) 0) := by
          simpa [countingOracle.simulate] using htail
        have htailCount :=
          ih { state := permuted, absorbPos := 0, squeezePos := 1 }
            ((a, b), Function.update z.2 sponge.state (z.2 sponge.state - 1)) htail'
        change queryCountTotal (Function.update z.2 sponge.state (z.2 sponge.state - 1)) =
          spongeOpCount SpongeSize.R ((1 : Fin (SpongeSize.R + 1)) : ℕ) n at htailCount
        have hR : 0 < SpongeSize.R := SpongeSize.R_pos
        have hOne : ((1 : Fin (SpongeSize.R + 1)) : ℕ) = 1 := by
          change 1 % (SpongeSize.R + 1) = 1
          exact Nat.mod_eq_of_lt (by omega)
        rw [hOne] at htailCount
        rw [spongeOpCount_succ, hpos, if_pos rfl]
        have hupdate := queryCountTotal_update_pred z.2 sponge.state hCount
        have hsum : z.2 sponge.state ≤ queryCountTotal z.2 := by
          exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ _)
        have hstatePos : 0 < z.2 sponge.state := Nat.pos_of_ne_zero hCount
        have htotalPos : 0 < queryCountTotal z.2 := lt_of_lt_of_le hstatePos hsum
        calc
          queryCountTotal z.2 = queryCountTotal z.2 - 1 + 1 :=
            (Nat.sub_add_cancel htotalPos).symm
          _ = queryCountTotal (Function.update z.2 sponge.state (z.2 sponge.state - 1)) + 1 := by
            rw [hupdate]
          _ = spongeOpCount SpongeSize.R 1 n + 1 := by rw [htailCount]
      · rw [if_neg (show ¬ ((({ sponge with absorbPos := 0 } : DuplexSponge U C)).squeezePos : ℕ)
            = SpongeSize.R from hpos)] at hz
        simp [countingOracle.simulate] at hz
        rcases hz with ⟨a, b, qc, htail, hEq⟩
        subst z
        let next : DuplexSponge U C :=
          { state := sponge.state, absorbPos := 0, squeezePos := sponge.squeezePos + 1 }
        have htail' : ((a, b), qc) ∈
            support (countingOracle.simulate (DuplexSponge.squeeze next n) 0) := by
          simpa [next, countingOracle.simulate] using htail
        have htailCount := ih next ((a, b), qc) htail'
        rw [spongeOpCount_succ, if_neg hpos]
        have hval : sponge.squeezePos.val < SpongeSize.R :=
          lt_of_le_of_ne (Fin.is_le _) hpos
        have hsucc : ((sponge.squeezePos + 1 : Fin (SpongeSize.R + 1)) : ℕ) =
            sponge.squeezePos.val + 1 := by
          rw [Fin.val_add_one_of_lt]
          rw [Fin.lt_def, Fin.val_last]
          exact hval
        simpa [next, hsucc] using htailCount

/-- Structural upper bound for the forward-permutation queries made by `squeeze`.

As with `absorb_isQueryBoundP`, this remains an upper-bound theorem; the equality-level dynamic
statement is `squeeze_counting_exact`. -/
lemma squeeze_isQueryBoundP (len : Nat) (sponge : DuplexSponge U C) :
    IsQueryBoundP (DuplexSponge.squeeze sponge len) (fun _ => True)
      (spongeOpCount SpongeSize.R sponge.squeezePos.val len) := by
  induction len generalizing sponge with
  | zero => simp [DuplexSponge.squeeze]
  | succ n ih =>
    rw [DuplexSponge.squeeze]
    by_cases hpos : (sponge.squeezePos : ℕ) = SpongeSize.R
    · rw [if_pos (show ((({ sponge with absorbPos := 0 } : DuplexSponge U C)).squeezePos : ℕ)
          = SpongeSize.R from hpos)]
      simp only [HasQuery.instOfMonadLift_query, pure_bind]
      rw [hpos, spongeOpCount_succ, if_pos rfl]
      rw [isQueryBoundP_query_bind_iff]
      refine ⟨Or.inr (by omega), fun u => ?_⟩
      simp only [bind_pure_comp, isQueryBoundP_map_iff]
      refine (ih _).mono (le_of_eq ?_)
      have hR : 0 < SpongeSize.R := Nat.pos_of_ne_zero (NeZero.ne _)
      simp [Nat.mod_eq_of_lt (show 1 < SpongeSize.R + 1 by omega)]
    · rw [if_neg (show ¬ ((({ sponge with absorbPos := 0 } : DuplexSponge U C)).squeezePos : ℕ)
          = SpongeSize.R from hpos)]
      simp only [pure_bind, bind_pure_comp, isQueryBoundP_map_iff]
      have hval : sponge.squeezePos.val < SpongeSize.R :=
        lt_of_le_of_ne (Fin.is_le _) hpos
      have hsucc : ((sponge.squeezePos + 1 : Fin (SpongeSize.R + 1)) : ℕ)
          = sponge.squeezePos.val + 1 := by
        rw [Fin.val_add_one_of_lt]
        rw [Fin.lt_def, Fin.val_last]
        exact hval
      rw [spongeOpCount_succ, if_neg hpos]
      refine (ih _).mono (le_of_eq ?_)
      simp [hsucc]

end SpongeOps

/-! ## The forward DSFS verifier is a `(1, L, 0)`-query algorithm

`deriveTranscriptDSFSAux` makes only forward-permutation queries, at most `L_P(i)` (message
rounds, `absorb`) resp. `L_V(i)` (challenge rounds, `squeeze`) per round; `DuplexSponge.start`
makes the single hash query; the salt phase is free for `δ ≤ R`. -/

section DeriveTranscript

open ProtocolSpec

variable {n : ℕ} {pSpec : ProtocolSpec n} {ι : Type} {oSpec : OracleSpec ι}
  {StmtIn : Type}
  [VCVCompatible StmtIn] [∀ i, VCVCompatible (pSpec.Challenge i)]
  {U : Type} [SpongeUnit U] [SpongeSize]
  [CodecCore pSpec U]

/-- Forward-permutation query points of the narrow (`𝒱^{h,p}`) spec. -/
def isNarrowFwdPermPoint : (oSpec + duplexSpongeForwardOracle StmtIn U).Domain → Bool
  | .inr (.inr _) => true
  | _ => false

/-- Hash query points of the narrow (`𝒱^{h,p}`) spec. -/
def isNarrowHashPoint : (oSpec + duplexSpongeForwardOracle StmtIn U).Domain → Bool
  | .inr (.inl _) => true
  | _ => false

/-- Per-round permutation budget of the transcript re-derivation: `L_P(i)` to absorb a message
round, `L_V(i)` to squeeze a challenge round. -/
def roundPermBudget (pSpec : ProtocolSpec n) [HasMessageSize pSpec] [HasChallengeSize pSpec]
    (i : Fin n) : ℕ :=
  match hdir : pSpec.dir i with
  | .P_to_V => pSpec.Lₚᵢ ⟨i, hdir⟩
  | .V_to_P => pSpec.Lᵥᵢ ⟨i, hdir⟩

/-- Match-reduction: message round. -/
lemma roundPermBudget_eq_msg {i : Fin n} (h : pSpec.dir i = .P_to_V) :
    roundPermBudget pSpec i = pSpec.Lₚᵢ ⟨i, h⟩ := by
  unfold roundPermBudget
  split
  · rfl
  · next hdir => rw [hdir] at h; exact absurd h (by simp)

/-- Match-reduction: challenge round. -/
lemma roundPermBudget_eq_chal {i : Fin n} (h : pSpec.dir i = .V_to_P) :
    roundPermBudget pSpec i = pSpec.Lᵥᵢ ⟨i, h⟩ := by
  unfold roundPermBudget
  split
  · next hdir => rw [hdir] at h; exact absurd h (by simp)
  · rfl

/-- Cumulative permutation budget of the first `k` rounds. -/
def permBudgetUpTo (pSpec : ProtocolSpec n) [HasMessageSize pSpec] [HasChallengeSize pSpec]
    (k : Fin (n + 1)) : ℕ :=
  Fin.induction 0 (fun i acc => acc + roundPermBudget pSpec i) k

@[simp]
lemma permBudgetUpTo_zero : permBudgetUpTo pSpec 0 = 0 := rfl

@[simp]
lemma permBudgetUpTo_succ (i : Fin n) :
    permBudgetUpTo pSpec i.succ = permBudgetUpTo pSpec i.castSucc + roundPermBudget pSpec i := by
  simp [permBudgetUpTo]

/-- The total budget over all rounds is the paper's `L = L_P + L_V`. -/
lemma permBudgetUpTo_last :
    permBudgetUpTo pSpec (Fin.last n) = pSpec.totalNumPermQueries := by
  have hsum : ∀ k : Fin (n + 1), permBudgetUpTo pSpec k
      = ∑ i ∈ Finset.univ.filter (fun i : Fin n => (i : ℕ) < (k : ℕ)),
          roundPermBudget pSpec i := by
    intro k
    induction k using Fin.induction with
    | zero => simp
    | succ i ih =>
      rw [permBudgetUpTo_succ, ih]
      have hins : Finset.univ.filter (fun j : Fin n => (j : ℕ) < (i.succ : ℕ))
          = insert i (Finset.univ.filter (fun j : Fin n => (j : ℕ) < (i.castSucc : ℕ))) := by
        ext j
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
          Fin.val_succ, Fin.coe_castSucc]
        constructor
        · intro hj
          rcases Nat.lt_or_ge (j : ℕ) (i : ℕ) with h | h
          · exact Or.inr h
          · exact Or.inl (Fin.ext (by omega))
        · rintro (rfl | hj) <;> omega
      rw [hins, Finset.sum_insert (by simp)]
      ring
  rw [hsum]
  have hall : Finset.univ.filter (fun i : Fin n => (i : ℕ) < ((Fin.last n : Fin (n + 1)) : ℕ))
      = Finset.univ := by
    ext j
    simp [Fin.val_last, j.isLt]
  rw [hall]
  -- split the full sum by round direction
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ
    (fun i : Fin n => pSpec.dir i = Direction.P_to_V) (roundPermBudget pSpec)]
  have hmsg : ∑ i ∈ Finset.univ.filter (fun i : Fin n => pSpec.dir i = Direction.P_to_V),
      roundPermBudget pSpec i = pSpec.totalNumPermQueriesMessage := by
    rw [Finset.sum_subtype (p := fun i : Fin n => pSpec.dir i = Direction.P_to_V)
      (Finset.univ.filter (fun i : Fin n => pSpec.dir i = Direction.P_to_V))
      (by simp) (fun i : Fin n => roundPermBudget pSpec i)]
    exact Finset.sum_congr rfl (fun i _ => roundPermBudget_eq_msg i.2)
  have hchal : ∑ i ∈ Finset.univ.filter
      (fun i : Fin n => ¬ pSpec.dir i = Direction.P_to_V),
      roundPermBudget pSpec i = pSpec.totalNumPermQueriesChallenge := by
    have hset : Finset.univ.filter (fun i : Fin n => ¬ pSpec.dir i = Direction.P_to_V)
        = Finset.univ.filter (fun i : Fin n => pSpec.dir i = Direction.V_to_P) := by
      ext j
      cases hdir : pSpec.dir j <;> simp [hdir]
    rw [hset, Finset.sum_subtype (p := fun i : Fin n => pSpec.dir i = Direction.V_to_P)
      (Finset.univ.filter (fun i : Fin n => pSpec.dir i = Direction.V_to_P))
      (by simp) (fun i : Fin n => roundPermBudget pSpec i)]
    exact Finset.sum_congr rfl (fun i _ => roundPermBudget_eq_chal i.2)
  rw [hmsg, hchal]
  rfl

/-- **Round induction (forward class).** The transcript re-derivation up to round `k` makes at
most `permBudgetUpTo k` forward-permutation queries. -/
lemma deriveTranscriptDSFSAux_fwd_bound (sponge : CanonicalDuplexSponge U)
    (messages : pSpec.Messages) (k : Fin (n + 1)) :
    IsQueryBoundP
      (ProtocolSpec.Messages.deriveTranscriptDSFSAux (oSpec := oSpec) (StmtIn := StmtIn)
        (U := U) sponge messages k)
      (fun t => isNarrowFwdPermPoint (oSpec := oSpec) (StmtIn := StmtIn) (U := U) t = true)
      (permBudgetUpTo pSpec k) := by
  induction k using Fin.induction with
  | zero =>
    simp [ProtocolSpec.Messages.deriveTranscriptDSFSAux]
  | succ i ih =>
    rw [ProtocolSpec.Messages.deriveTranscriptDSFSAux, Fin.induction_succ,
      permBudgetUpTo_succ]
    rw [ProtocolSpec.Messages.deriveTranscriptDSFSAux] at ih
    refine isQueryBoundP_bind ih (fun x _ => ?_)
    obtain ⟨curSponge, prevTranscript⟩ := x
    split
    next _ curS prevT heq =>
      split
      · next hDir =>
        dsimp only
        refine (isQueryBoundP_bind
          (n := (challengeSize (pSpec := pSpec) ⟨i, hDir⟩ + SpongeSize.R - 1) / SpongeSize.R)
          (m := 0)
          ((isQueryBoundP_liftM_of_lawful _
              (p := fun _ : (forwardPermutationOracle (CanonicalSpongeState U)).Domain => True)
              (fun t => ?_) (squeeze_isQueryBoundP _ curS)).mono
            (spongeOpCount_le _ (Nat.pos_of_ne_zero (NeZero.ne _)) _ _ (Fin.is_le _)))
          (fun y _ => ?_)).mono ?_
        · show IsQueryBoundP (liftM (liftM (OracleSpec.query t) :
              OracleQuery (oSpec + duplexSpongeForwardOracle StmtIn U) _)) _ _
          rw [liftM_query_reshape, isQueryBoundP_map_iff, isQueryBoundP_query_iff]
          exact fun _ => by simp
        · rcases y with ⟨c, ns⟩
          simp
        · rw [roundPermBudget_eq_chal hDir]
          unfold ProtocolSpec.Lᵥᵢ ProtocolSpec.numPermQueriesChallenge
          rw [nat_ceil_div_eq _ _ (Nat.pos_of_ne_zero (NeZero.ne _))]
          omega
      · next hDir =>
        dsimp only
        refine (isQueryBoundP_bind
          (n := (((Codec.instSerializeMessage (pSpec := pSpec) (U := U) ⟨i, hDir⟩).serialize
              (messages ⟨i, hDir⟩)).toList.length + SpongeSize.R - 1) / SpongeSize.R)
          (m := 0)
          ((isQueryBoundP_liftM_of_lawful _
              (p := fun _ : (forwardPermutationOracle (CanonicalSpongeState U)).Domain => True)
              (fun t => ?_) (absorb_isQueryBoundP _ curS)).mono
            (spongeOpCount_le _ (Nat.pos_of_ne_zero (NeZero.ne _)) _ _ (Fin.is_le _)))
          (fun y _ => ?_)).mono ?_
        · show IsQueryBoundP (liftM (liftM (OracleSpec.query t) :
              OracleQuery (oSpec + duplexSpongeForwardOracle StmtIn U) _)) _ _
          rw [liftM_query_reshape, isQueryBoundP_map_iff, isQueryBoundP_query_iff]
          exact fun _ => by simp
        · simp
        · rw [roundPermBudget_eq_msg hDir]
          unfold ProtocolSpec.Lₚᵢ ProtocolSpec.numPermQueriesMessage
          rw [nat_ceil_div_eq _ _ (Nat.pos_of_ne_zero (NeZero.ne _))]
          simp

/-- **Round induction (hash class).** The transcript re-derivation makes no hash query. -/
lemma deriveTranscriptDSFSAux_hash_bound (sponge : CanonicalDuplexSponge U)
    (messages : pSpec.Messages) (k : Fin (n + 1)) :
    IsQueryBoundP
      (ProtocolSpec.Messages.deriveTranscriptDSFSAux (oSpec := oSpec) (StmtIn := StmtIn)
        (U := U) sponge messages k)
      (fun t => isNarrowHashPoint (oSpec := oSpec) (StmtIn := StmtIn) (U := U) t = true)
      0 := by
  induction k using Fin.induction with
  | zero =>
    simp [ProtocolSpec.Messages.deriveTranscriptDSFSAux]
  | succ i ih =>
    rw [ProtocolSpec.Messages.deriveTranscriptDSFSAux, Fin.induction_succ]
    rw [ProtocolSpec.Messages.deriveTranscriptDSFSAux] at ih
    refine (isQueryBoundP_bind (n := 0) (m := 0) ih (fun x _ => ?_)).mono (by omega)
    obtain ⟨curSponge, prevTranscript⟩ := x
    split
    next _ curS prevT heq =>
      split
      · next hDir =>
        dsimp only
        refine (isQueryBoundP_bind (n := 0) (m := 0)
          (isQueryBoundP_liftM_of_lawful _
            (p := fun _ : (forwardPermutationOracle (CanonicalSpongeState U)).Domain => False)
            (fun t => ?_)
            (isQueryBoundP_zero_of_forall_not _ (by simp)))
          (fun y _ => ?_)).mono (by omega)
        · show IsQueryBoundP (liftM (liftM (OracleSpec.query t) :
              OracleQuery (oSpec + duplexSpongeForwardOracle StmtIn U) _)) _ _
          rw [liftM_query_reshape, isQueryBoundP_map_iff, isQueryBoundP_query_iff]
          rw [show ((liftM (OracleSpec.query t) :
              OracleQuery (oSpec + duplexSpongeForwardOracle StmtIn U) _).input)
            = Sum.inr (Sum.inr t) from rfl]
          simp [isNarrowHashPoint]
        · rcases y with ⟨c, ns⟩
          simp
      · next hDir =>
        dsimp only
        refine (isQueryBoundP_bind (n := 0) (m := 0)
          (isQueryBoundP_liftM_of_lawful _
            (p := fun _ : (forwardPermutationOracle (CanonicalSpongeState U)).Domain => False)
            (fun t => ?_)
            (isQueryBoundP_zero_of_forall_not _ (by simp)))
          (fun y _ => ?_)).mono (by omega)
        · show IsQueryBoundP (liftM (liftM (OracleSpec.query t) :
              OracleQuery (oSpec + duplexSpongeForwardOracle StmtIn U) _)) _ _
          rw [liftM_query_reshape, isQueryBoundP_map_iff, isQueryBoundP_query_iff]
          rw [show ((liftM (OracleSpec.query t) :
              OracleQuery (oSpec + duplexSpongeForwardOracle StmtIn U) _).input)
            = Sum.inr (Sum.inr t) from rfl]
          simp [isNarrowHashPoint]
        · simp

/-- **Salted derivation, forward class.** For `δ ≤ R` the salted transcript derivation makes at
most `L = totalNumPermQueries` forward-permutation queries: `start` is a hash query, the salt
phase is free (the lazy sponge starts at the fresh position `0`), and the rounds
contribute `permBudgetUpTo (last n) = L`. -/
lemma deriveTranscriptDSFSSalted_fwd_bound {δ : ℕ} (hδR : δ ≤ SpongeSize.R)
    (stmtIn : StmtIn) (salt : Vector U δ) (messages : pSpec.Messages) :
    IsQueryBoundP
      (ProtocolSpec.Messages.deriveTranscriptDSFSSalted (oSpec := oSpec) (U := U)
        stmtIn salt messages)
      (fun t => isNarrowFwdPermPoint (oSpec := oSpec) (StmtIn := StmtIn) (U := U) t = true)
      pSpec.totalNumPermQueries := by
  rw [ProtocolSpec.Messages.deriveTranscriptDSFSSalted]
  refine (isQueryBoundP_bind (n := 0) (m := pSpec.totalNumPermQueries) ?_
    (fun sponge0 hs0 => ?_)).mono (by omega)
  · -- `start` makes one hash query — no forward-perm query.
    show IsQueryBoundP
      ((liftM (liftM (OracleSpec.query (spec := StmtIn →ₒ Vector U SpongeSize.C) stmtIn) :
          OracleQuery (oSpec + duplexSpongeForwardOracle StmtIn U)
            (Vector U SpongeSize.C)) :
        OracleComp (oSpec + duplexSpongeForwardOracle StmtIn U) (Vector U SpongeSize.C))
        >>= fun c =>
          pure ({
              state := SpongeState.update (0 : CanonicalSpongeState U)
                (((Vector.replicate SpongeSize.R (0 : U)) ++ c).cast (by simp)),
              absorbPos := 0,
              squeezePos := Fin.last SpongeSize.R } : CanonicalDuplexSponge U))
      (fun t => isNarrowFwdPermPoint (oSpec := oSpec) (StmtIn := StmtIn) (U := U) t = true) 0
    refine (isQueryBoundP_bind (n := 0) (m := 0) ?_ (fun c _ => by simp)).mono (by omega)
    rw [liftM_query_reshape, isQueryBoundP_map_iff, isQueryBoundP_query_iff]
    rw [show ((liftM (OracleSpec.query (spec := StmtIn →ₒ Vector U SpongeSize.C) stmtIn) :
        OracleQuery (oSpec + duplexSpongeForwardOracle StmtIn U) _).input)
      = Sum.inr (Sum.inl stmtIn) from rfl]
    simp [isNarrowFwdPermPoint]
  · -- the salt phase is free, the rounds contribute `L`.
    -- Characterize `sponge0` from the support: `absorbPos = 0`.
    have hs0' : sponge0 ∈ support
        ((liftM (liftM (OracleSpec.query (spec := StmtIn →ₒ Vector U SpongeSize.C) stmtIn) :
            OracleQuery (oSpec + duplexSpongeForwardOracle StmtIn U)
              (Vector U SpongeSize.C)) :
          OracleComp (oSpec + duplexSpongeForwardOracle StmtIn U) (Vector U SpongeSize.C))
          >>= fun c =>
            pure ({
                state := SpongeState.update (0 : CanonicalSpongeState U)
                  (((Vector.replicate SpongeSize.R (0 : U)) ++ c).cast (by simp)),
                absorbPos := 0,
                squeezePos := Fin.last SpongeSize.R } :
              CanonicalDuplexSponge U)) := hs0
    rw [mem_support_bind_iff] at hs0'
    obtain ⟨c, _, hs0'⟩ := hs0'
    rw [mem_support_pure_iff] at hs0'
    subst hs0'
    refine (isQueryBoundP_bind (n := 0) (m := pSpec.totalNumPermQueries)
      ?_ (fun sponge _ => ?_)).mono (by omega)
    · -- salt absorb from `absorbPos = 0` with `δ ≤ R` units: zero queries
      refine (isQueryBoundP_liftM_of_lawful _
        (p := fun _ : (forwardPermutationOracle (CanonicalSpongeState U)).Domain => True)
        (fun t => ?_) (absorb_isQueryBoundP _ _)).mono (le_of_eq ?_)
      · show IsQueryBoundP (liftM (liftM (OracleSpec.query t) :
            OracleQuery (oSpec + duplexSpongeForwardOracle StmtIn U) _)) _ _
        rw [liftM_query_reshape, isQueryBoundP_map_iff, isQueryBoundP_query_iff]
        exact fun _ => by simp
      · show spongeOpCount SpongeSize.R ((0 : Fin (SpongeSize.R + 1)) : ℕ)
            salt.toList.length = 0
        rw [show ((0 : Fin (SpongeSize.R + 1)) : ℕ) = 0 from rfl,
          show salt.toList.length = δ from by simp]
        exact spongeOpCount_zero_pos _ _ (Nat.pos_of_ne_zero (NeZero.ne _)) hδR
    · -- the rounds
      have h := deriveTranscriptDSFSAux_fwd_bound (oSpec := oSpec) (StmtIn := StmtIn)
        sponge messages (Fin.last n)
      rwa [permBudgetUpTo_last] at h

/-- **Salted derivation, general forward class.** Without the extra hypothesis `δ ≤ R`, the
salted derivation makes at most `\bar L = L_δ + L` forward-permutation queries.  This is the
bound required by the stateful Backtrack repair: it is sound for salts ending in a partial rate
block and deliberately does not assert that all of those blocks are queried. -/
lemma deriveTranscriptDSFSSalted_fwd_bound_salted {δ : ℕ}
    (stmtIn : StmtIn) (salt : Vector U δ) (messages : pSpec.Messages) :
    IsQueryBoundP
      (ProtocolSpec.Messages.deriveTranscriptDSFSSalted (oSpec := oSpec) (U := U)
        stmtIn salt messages)
      (fun t => isNarrowFwdPermPoint (oSpec := oSpec) (StmtIn := StmtIn) (U := U) t = true)
      (pSpec.totalNumPermQueriesSalted δ) := by
  rw [ProtocolSpec.Messages.deriveTranscriptDSFSSalted]
  refine (isQueryBoundP_bind (n := 0) (m := pSpec.totalNumPermQueriesSalted δ) ?_
    (fun sponge0 hs0 => ?_)).mono (by omega)
  · -- `start` makes one hash query — no forward-perm query.
    show IsQueryBoundP
      ((liftM (liftM (OracleSpec.query (spec := StmtIn →ₒ Vector U SpongeSize.C) stmtIn) :
          OracleQuery (oSpec + duplexSpongeForwardOracle StmtIn U)
            (Vector U SpongeSize.C)) :
        OracleComp (oSpec + duplexSpongeForwardOracle StmtIn U) (Vector U SpongeSize.C))
        >>= fun c =>
          pure ({
              state := SpongeState.update (0 : CanonicalSpongeState U)
                (((Vector.replicate SpongeSize.R (0 : U)) ++ c).cast (by simp)),
              absorbPos := 0,
              squeezePos := Fin.last SpongeSize.R } : CanonicalDuplexSponge U))
      (fun t => isNarrowFwdPermPoint (oSpec := oSpec) (StmtIn := StmtIn) (U := U) t = true) 0
    refine (isQueryBoundP_bind (n := 0) (m := 0) ?_ (fun c _ => by simp)).mono (by omega)
    rw [liftM_query_reshape, isQueryBoundP_map_iff, isQueryBoundP_query_iff]
    rw [show ((liftM (OracleSpec.query (spec := StmtIn →ₒ Vector U SpongeSize.C) stmtIn) :
        OracleQuery (oSpec + duplexSpongeForwardOracle StmtIn U) _).input)
      = Sum.inr (Sum.inl stmtIn) from rfl]
    simp [isNarrowFwdPermPoint]
  · -- Bound the salt and the protocol phases separately; the exact boundary position is irrelevant.
    have hs0' : sponge0 ∈ support
        ((liftM (liftM (OracleSpec.query (spec := StmtIn →ₒ Vector U SpongeSize.C) stmtIn) :
            OracleQuery (oSpec + duplexSpongeForwardOracle StmtIn U)
              (Vector U SpongeSize.C)) :
          OracleComp (oSpec + duplexSpongeForwardOracle StmtIn U) (Vector U SpongeSize.C))
          >>= fun c =>
            pure ({
                state := SpongeState.update (0 : CanonicalSpongeState U)
                  (((Vector.replicate SpongeSize.R (0 : U)) ++ c).cast (by simp)),
                absorbPos := 0,
                squeezePos := Fin.last SpongeSize.R } :
              CanonicalDuplexSponge U)) := hs0
    rw [mem_support_bind_iff] at hs0'
    obtain ⟨c, _, hs0'⟩ := hs0'
    rw [mem_support_pure_iff] at hs0'
    subst hs0'
    refine (isQueryBoundP_bind (n := ProtocolSpec.numSaltBlocks δ)
      (m := pSpec.totalNumPermQueries) ?_ (fun sponge _ => ?_)).mono (by
        unfold ProtocolSpec.totalNumPermQueriesSalted
        omega)
    · refine (isQueryBoundP_liftM_of_lawful _
        (p := fun _ : (forwardPermutationOracle (CanonicalSpongeState U)).Domain => True)
        (fun t => ?_) (absorb_isQueryBoundP _ _)).mono ?_
      · show IsQueryBoundP (liftM (liftM (OracleSpec.query t) :
            OracleQuery (oSpec + duplexSpongeForwardOracle StmtIn U) _)) _ _
        rw [liftM_query_reshape, isQueryBoundP_map_iff, isQueryBoundP_query_iff]
        exact fun _ => by simp
      · rw [show salt.toList.length = δ from by simp,
          ProtocolSpec.numSaltBlocks,
          nat_ceil_div_eq _ _ (Nat.pos_of_ne_zero (NeZero.ne _))]
        exact spongeOpCount_le _ (Nat.pos_of_ne_zero (NeZero.ne _)) _ _ (Fin.is_le _)
    · have h := deriveTranscriptDSFSAux_fwd_bound (oSpec := oSpec) (StmtIn := StmtIn)
        sponge messages (Fin.last n)
      rwa [permBudgetUpTo_last] at h

/-- **Salted derivation, hash class.** The salted transcript derivation makes exactly one hash
query (the `start` query); the salt absorption and the rounds are permutation-only. -/
lemma deriveTranscriptDSFSSalted_hash_bound {δ : ℕ}
    (stmtIn : StmtIn) (salt : Vector U δ) (messages : pSpec.Messages) :
    IsQueryBoundP
      (ProtocolSpec.Messages.deriveTranscriptDSFSSalted (oSpec := oSpec) (U := U)
        stmtIn salt messages)
      (fun t => isNarrowHashPoint (oSpec := oSpec) (StmtIn := StmtIn) (U := U) t = true)
      1 := by
  rw [ProtocolSpec.Messages.deriveTranscriptDSFSSalted]
  refine (isQueryBoundP_bind (n := 1) (m := 0) ?_ (fun sponge0 _ => ?_)).mono (by omega)
  · -- `start` makes the single hash query.
    show IsQueryBoundP
      ((liftM (liftM (OracleSpec.query (spec := StmtIn →ₒ Vector U SpongeSize.C) stmtIn) :
          OracleQuery (oSpec + duplexSpongeForwardOracle StmtIn U)
            (Vector U SpongeSize.C)) :
        OracleComp (oSpec + duplexSpongeForwardOracle StmtIn U) (Vector U SpongeSize.C))
        >>= fun c =>
          pure ({
              state := SpongeState.update (0 : CanonicalSpongeState U)
                (((Vector.replicate SpongeSize.R (0 : U)) ++ c).cast (by simp)),
              absorbPos := 0,
              squeezePos := Fin.last SpongeSize.R } : CanonicalDuplexSponge U))
      (fun t => isNarrowHashPoint (oSpec := oSpec) (StmtIn := StmtIn) (U := U) t = true) 1
    refine (isQueryBoundP_bind (n := 1) (m := 0) ?_ (fun c _ => by simp)).mono (by omega)
    rw [liftM_query_reshape, isQueryBoundP_map_iff, isQueryBoundP_query_iff]
    exact fun _ => by omega
  · -- salt absorption and rounds: permutation-only.
    refine (isQueryBoundP_bind (n := 0) (m := 0)
      (isQueryBoundP_liftM_of_lawful _
        (p := fun _ : (forwardPermutationOracle (CanonicalSpongeState U)).Domain => False)
        (fun t => ?_)
        (isQueryBoundP_zero_of_forall_not _ (by simp)))
      (fun sponge _ => deriveTranscriptDSFSAux_hash_bound (oSpec := oSpec) (StmtIn := StmtIn)
        sponge messages (Fin.last n))).mono (by omega)
    show IsQueryBoundP (liftM (liftM (OracleSpec.query t) :
        OracleQuery (oSpec + duplexSpongeForwardOracle StmtIn U) _)) _ _
    rw [liftM_query_reshape, isQueryBoundP_map_iff, isQueryBoundP_query_iff]
    rw [show ((liftM (OracleSpec.query t) :
        OracleQuery (oSpec + duplexSpongeForwardOracle StmtIn U) _).input)
      = Sum.inr (Sum.inr t) from rfl]
    simp [isNarrowHashPoint]

/-! ## The forward verifier `𝒱^{h,p}` is `(1, L, 0)`-query (narrow spec, `oSpec = []ₒ`) -/

section VerifierNarrow

variable {StmtOut : Type} {δ : ℕ}

/-- Narrow-spec forward-verifier bound, forward class: `≤ L` permutation queries. -/
lemma dsfsForwardVerify_fwd_bound
    [IsUniformSpec (([]ₒ : OracleSpec.{0, 0} PEmpty.{1}) + duplexSpongeForwardOracle StmtIn U)]
    (hδR : δ ≤ SpongeSize.R)
    (V : Verifier ([]ₒ : OracleSpec.{0, 0} PEmpty.{1}) StmtIn StmtOut pSpec) (stmtIn : StmtIn)
    (proof : DSSaltedProof (pSpec := pSpec) (U := U) δ) :
    IsQueryBoundP
      (((Verifier.toDSFS (oSpec := []ₒ) (U := U) δ V).run stmtIn
        (fun i => match i with | ⟨0, _⟩ => proof)).run)
      (fun t => isNarrowFwdPermPoint (oSpec := []ₒ) (StmtIn := StmtIn) (U := U) t = true)
      pSpec.totalNumPermQueries := by
  rw [Verifier.run, Verifier.toDSFS, Verifier.duplexSpongeFiatShamirSaltedForward]
  dsimp only
  simp only [OptionT.run_bind, OptionT.run_bind_lift, OptionT.run_lift, Option.getM,
    OptionT.run_pure, OptionT.run_failure, Option.elimM]
  refine (isQueryBoundP_bind (n := pSpec.totalNumPermQueries) (m := 0) ?_
    (fun o _ => ?_)).mono (by omega)
  · show IsQueryBoundP
      ((ProtocolSpec.Messages.deriveTranscriptDSFSSalted (oSpec := []ₒ) (U := U)
          stmtIn proof.1 proof.2) >>= fun a => pure (some a))
      (fun t => isNarrowFwdPermPoint (oSpec := []ₒ) (StmtIn := StmtIn) (U := U) t = true)
      pSpec.totalNumPermQueries
    exact (isQueryBoundP_bind (n := pSpec.totalNumPermQueries) (m := 0)
      (deriveTranscriptDSFSSalted_fwd_bound hδR stmtIn proof.1 proof.2)
      (fun a _ => by simp)).mono (by omega)
  · rcases o with _ | x
    · simp
    · simp only [Option.elim]
      obtain ⟨v, hv⟩ := emptySpec_eq_pure ((V.verify stmtIn x.2).run)
      rw [hv]
      show IsQueryBoundP
        ((pure (some v) : OracleComp ([]ₒ + duplexSpongeForwardOracle StmtIn U) _)
          >>= fun o' => Option.elim o' (pure none) fun v' =>
            (match v' with
              | none => (failure : OptionT (OracleComp ([]ₒ + duplexSpongeForwardOracle
                  StmtIn U)) StmtOut)
              | some a => pure a).run) _ _
      rcases v with _ | a <;> simp

/-- Narrow-spec forward verifier, salt-aware forward bound.  No `δ ≤ R` side condition is
needed: the lazy salt absorption is charged to `L_δ`, yielding the safe `(1, \bar L, 0)`
interface used by the repaired Section 5 analysis. -/
lemma dsfsForwardVerify_fwd_bound_salted
    [IsUniformSpec (([]ₒ : OracleSpec.{0, 0} PEmpty.{1}) + duplexSpongeForwardOracle StmtIn U)]
    (V : Verifier ([]ₒ : OracleSpec.{0, 0} PEmpty.{1}) StmtIn StmtOut pSpec) (stmtIn : StmtIn)
    (proof : DSSaltedProof (pSpec := pSpec) (U := U) δ) :
    IsQueryBoundP
      (((Verifier.toDSFS (oSpec := []ₒ) (U := U) δ V).run stmtIn
        (fun i => match i with | ⟨0, _⟩ => proof)).run)
      (fun t => isNarrowFwdPermPoint (oSpec := []ₒ) (StmtIn := StmtIn) (U := U) t = true)
      (pSpec.totalNumPermQueriesSalted δ) := by
  rw [Verifier.run, Verifier.toDSFS, Verifier.duplexSpongeFiatShamirSaltedForward]
  dsimp only
  simp only [OptionT.run_bind, OptionT.run_bind_lift, OptionT.run_lift, Option.getM,
    OptionT.run_pure, OptionT.run_failure, Option.elimM]
  refine (isQueryBoundP_bind (n := pSpec.totalNumPermQueriesSalted δ) (m := 0) ?_
    (fun o _ => ?_)).mono (by omega)
  · show IsQueryBoundP
      ((ProtocolSpec.Messages.deriveTranscriptDSFSSalted (oSpec := []ₒ) (U := U)
          stmtIn proof.1 proof.2) >>= fun a => pure (some a))
      (fun t => isNarrowFwdPermPoint (oSpec := []ₒ) (StmtIn := StmtIn) (U := U) t = true)
      (pSpec.totalNumPermQueriesSalted δ)
    exact (isQueryBoundP_bind (n := pSpec.totalNumPermQueriesSalted δ) (m := 0)
      (deriveTranscriptDSFSSalted_fwd_bound_salted stmtIn proof.1 proof.2)
      (fun a _ => by simp)).mono (by omega)
  · rcases o with _ | x
    · simp
    · simp only [Option.elim]
      obtain ⟨v, hv⟩ := emptySpec_eq_pure ((V.verify stmtIn x.2).run)
      rw [hv]
      show IsQueryBoundP
        ((pure (some v) : OracleComp ([]ₒ + duplexSpongeForwardOracle StmtIn U) _)
          >>= fun o' => Option.elim o' (pure none) fun v' =>
            (match v' with
              | none => (failure : OptionT (OracleComp ([]ₒ + duplexSpongeForwardOracle
                  StmtIn U)) StmtOut)
              | some a => pure a).run) _ _
      rcases v with _ | a <;> simp


/-- Narrow-spec forward-verifier bound, hash class: exactly the one `start` query. -/
lemma dsfsForwardVerify_hash_bound
    [IsUniformSpec (([]ₒ : OracleSpec.{0, 0} PEmpty.{1}) + duplexSpongeForwardOracle StmtIn U)]
    (V : Verifier ([]ₒ : OracleSpec.{0, 0} PEmpty.{1}) StmtIn StmtOut pSpec) (stmtIn : StmtIn)
    (proof : DSSaltedProof (pSpec := pSpec) (U := U) δ) :
    IsQueryBoundP
      (((Verifier.toDSFS (oSpec := []ₒ) (U := U) δ V).run stmtIn
        (fun i => match i with | ⟨0, _⟩ => proof)).run)
      (fun t => isNarrowHashPoint (oSpec := []ₒ) (StmtIn := StmtIn) (U := U) t = true)
      1 := by
  rw [Verifier.run, Verifier.toDSFS, Verifier.duplexSpongeFiatShamirSaltedForward]
  dsimp only
  simp only [OptionT.run_bind, OptionT.run_bind_lift, OptionT.run_lift, Option.getM,
    OptionT.run_pure, OptionT.run_failure, Option.elimM]
  refine (isQueryBoundP_bind (n := 1) (m := 0) ?_ (fun o _ => ?_)).mono (by omega)
  · show IsQueryBoundP
      ((ProtocolSpec.Messages.deriveTranscriptDSFSSalted (oSpec := []ₒ) (U := U)
          stmtIn proof.1 proof.2) >>= fun a => pure (some a))
      (fun t => isNarrowHashPoint (oSpec := []ₒ) (StmtIn := StmtIn) (U := U) t = true) 1
    exact (isQueryBoundP_bind (n := 1) (m := 0)
      (deriveTranscriptDSFSSalted_hash_bound stmtIn proof.1 proof.2)
      (fun a _ => by simp)).mono (by omega)
  · rcases o with _ | x
    · simp
    · simp only [Option.elim]
      obtain ⟨v, hv⟩ := emptySpec_eq_pure ((V.verify stmtIn x.2).run)
      rw [hv]
      show IsQueryBoundP
        ((pure (some v) : OracleComp ([]ₒ + duplexSpongeForwardOracle StmtIn U) _)
          >>= fun o' => Option.elim o' (pure none) fun v' =>
            (match v' with
              | none => (failure : OptionT (OracleComp ([]ₒ + duplexSpongeForwardOracle
                  StmtIn U)) StmtOut)
              | some a => pure a).run) _ _
      rcases v with _ | a <;> simp
end VerifierNarrow
end DeriveTranscript

end DuplexSpongeFS

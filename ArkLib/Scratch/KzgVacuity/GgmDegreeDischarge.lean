/-
Copyright (c) 2026 Ember Arlynx. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ember Arlynx
-/
import ArkLib.Scratch.KzgVacuity.GgmRandomEncoding
import ArkLib.Scratch.KzgVacuity.GgmDegreeInvariant

/-!
# Degree discharge for the linear generic-group oracle

`GgmAdaptive` (adaptive bound) and `GgmRandomEncoding` (all-pairs bound) consume the SRS degree
invariant as external hypotheses (`hdeg_out`, `hdeg_pairs`, `hdeg_handles`): the committed output
polynomial and every handle polynomial have `natDegree ≤ D`. Since the oracle is purely linear
(`Move.lin` only — no pairing move; ArkLib's `tSdhAdversary` is granted no pairing map), those
facts are true by construction. This file proves them, by induction on the actual run recursion
(`runAux` / `runTable`, not the separate `GgmDegreeInvariant.buildPaired` peer model):

* `natDegree_combine_le` — a `lin` move's linear combination
  $\sum_i C(c_i) \cdot \mathrm{table}[k_i]$ over a degree-$\le D$ table stays $\le D$
  (`natDegree_add_le` is a max-bound; `natDegree_C_mul_le`
  absorbs the scalar; a defaulted out-of-range read is $0$).
* `runTable_natDegree_le` / `handlePolys_natDegree_le` — every polynomial in the run's final handle
  table (resp. the `insert 0` handle set) has `natDegree ≤ D`, by induction on fuel.
* `runAux_output_natDegree_le` / `symOutput_natDegree_le` — the committed output polynomial has
  `natDegree ≤ D` (it is a defaulted table read at commit time).
* `badPolys_natDegree_le` — every Shoup [Sho97] bad-event polynomial (difference of a formally
  distinct queried pair) has `natDegree ≤ D` (`natDegree_sub_le` is a max-bound — the linear oracle
  pays $\delta = D$, never $2D$).
* `srsSt_table_natDegree_le` — the SRS seed $1, X, \dots, X^D, 1, X$ meets the bound ($1 \le D$
  because the $G_2$ handle $X$ has degree $1$).
* the `_of_run` corollaries — `hdeg_out_of_run` / `hdeg_pairs_of_run` / `hdeg_handles_of_run` in
  exactly the shape the existing theorems consume, plus the composed hypothesis-free bounds
  `adaptive_ggm_sound_of_run` / `adaptive_ggm_sound_srs` / `rand_encoding_bound_D_of_run` /
  `rand_encoding_bound_srs_D_of_run`. The degree facts are now theorems about the actual oracle,
  not assumptions a downstream caller must supply.

Reused: `GgmDegreeInvariant.natDegree_getD_le` (the defaulted-read bound); everything else here
targets the real `runAux`/`runTable` recursion directly.

## References

* [Shoup, V., *Lower Bounds for Discrete Logarithms and Related Problems*][Sho97]
-/

open Polynomial

namespace GgmDegreeDischarge

open GgmCandidate GgmAdaptive GgmRandomEncoding GgmDegreeInvariant

variable {p : ℕ} [Fact (Nat.Prime p)]

/-! ## § Combine — a `lin` move preserves the degree bound -/

/-- `combine` on a cons: peel one summand. -/
lemma combine_cons (ci : ZMod p × ℕ) (cs : List (ZMod p × ℕ)) (table : List ((ZMod p)[X])) :
    combine (ci :: cs) table = C ci.1 * table.getD ci.2 0 + combine cs table := by
  simp [combine]

/-- **A `ZMod p`-linear combination of degree-≤D handles has degree ≤ D.** Induction on the
coefficient list: `natDegree_add_le` is a MAX bound, `natDegree_C_mul_le` absorbs the scalar,
and a defaulted table read is either a genuine (bounded) entry or the zero polynomial. -/
theorem natDegree_combine_le {table : List ((ZMod p)[X])} {D : ℕ}
    (h : ∀ q ∈ table, q.natDegree ≤ D) (spec : List (ZMod p × ℕ)) :
    (combine spec table).natDegree ≤ D := by
  induction spec with
  | nil => simp [combine]
  | cons ci cs ih =>
    rw [combine_cons]
    refine (natDegree_add_le _ _).trans (max_le ?_ ih)
    exact (natDegree_C_mul_le ci.1 _).trans (natDegree_getD_le h ci.2)

/-! ## § Table — the run's final handle table stays degree-bounded

Induction on fuel over the REAL `runTable` recursion: a `lin` step appends a `combine`
(bounded by `natDegree_combine_le`), a `query` step leaves the table unchanged, and a commit
stops. -/

/-- **The degree invariant of the real handle table.** If every seed polynomial has
`natDegree ≤ D`, so does every polynomial in the run's final table — for ANY answer function
(the table extension never consults the oracle's answers' values, only the history length
through the strategy). -/
theorem runTable_natDegree_le (ans : AnswerFn p) (strat : Strat p) {D : ℕ} :
    ∀ (fuel : ℕ) (st : St p), (∀ q ∈ st.table, q.natDegree ≤ D) →
      ∀ q ∈ runTable ans strat fuel st, q.natDegree ≤ D := by
  intro fuel
  induction fuel with
  | zero =>
    intro st hst q hq
    simp only [runTable] at hq
    exact hst q hq
  | succ fuel ih =>
    intro st hst q hq
    rcases hdec : strat st.hist with m | out
    · cases m with
      | lin spec =>
        have e : runTable ans strat (fuel + 1) st
            = runTable ans strat fuel ⟨st.table ++ [combine spec st.table], st.hist⟩ := by
          simp only [runTable, hdec]
        rw [e] at hq
        refine ih _ ?_ q hq
        intro r hr
        rcases List.mem_append.mp hr with h | h
        · exact hst r h
        · rw [List.mem_singleton.mp h]
          exact natDegree_combine_le hst spec
      | query i j =>
        have e : runTable ans strat (fuel + 1) st
            = runTable ans strat fuel
                ⟨st.table, st.hist ++ [ans (st.table.getD i 0) (st.table.getD j 0)]⟩ := by
          simp only [runTable, hdec]
        rw [e] at hq
        exact ih ⟨st.table, st.hist ++ [ans (st.table.getD i 0) (st.table.getD j 0)]⟩ hst q hq
    · have e : runTable ans strat (fuel + 1) st = st.table := by
        simp only [runTable, hdec]
      rw [e] at hq
      exact hst q hq

/-- **The handle-set degree invariant** — `runTable_natDegree_le` extended to
`handlePolys = insert 0 (runTable …).toFinset` (the zero/identity handle has degree 0). -/
theorem handlePolys_natDegree_le (ans : AnswerFn p) (strat : Strat p) (fuel : ℕ) (st₀ : St p)
    {D : ℕ} (hseed : ∀ q ∈ st₀.table, q.natDegree ≤ D) :
    ∀ q ∈ handlePolys ans strat fuel st₀, q.natDegree ≤ D := by
  intro q hq
  unfold handlePolys at hq
  rcases Finset.mem_insert.mp hq with h | h
  · rw [h]; simp
  · exact runTable_natDegree_le ans strat fuel st₀ hseed q (List.mem_toFinset.mp h)

/-! ## § Output — the committed output polynomial is degree-bounded -/

/-- **The output degree invariant, over the real `runAux`.** The committed output is a
defaulted table read at commit time (or `0` on fuel exhaustion); every intermediate table is
bounded, so the output is. Induction on fuel, for ANY answer function. -/
theorem runAux_output_natDegree_le (ans : AnswerFn p) (strat : Strat p) {D : ℕ} :
    ∀ (fuel : ℕ) (st : St p), (∀ q ∈ st.table, q.natDegree ≤ D) →
      ((runAux ans strat fuel st).1.2).natDegree ≤ D := by
  intro fuel
  induction fuel with
  | zero =>
    intro st _
    simp [runAux]
  | succ fuel ih =>
    intro st hst
    rcases hdec : strat st.hist with m | out
    · cases m with
      | lin spec =>
        have e : runAux ans strat (fuel + 1) st
            = runAux ans strat fuel ⟨st.table ++ [combine spec st.table], st.hist⟩ := by
          simp only [runAux, hdec]
        rw [e]
        refine ih _ ?_
        intro r hr
        rcases List.mem_append.mp hr with h | h
        · exact hst r h
        · rw [List.mem_singleton.mp h]
          exact natDegree_combine_le hst spec
      | query i j =>
        have e : runAux ans strat (fuel + 1) st
            = ((runAux ans strat fuel
                  ⟨st.table, st.hist ++ [ans (st.table.getD i 0) (st.table.getD j 0)]⟩).1,
                (st.table.getD i 0, st.table.getD j 0) ::
                  (runAux ans strat fuel
                    ⟨st.table, st.hist ++ [ans (st.table.getD i 0) (st.table.getD j 0)]⟩).2) := by
          simp only [runAux, hdec]
        rw [e]
        exact ih _ hst
    · have e : runAux ans strat (fuel + 1) st = ((out.1, st.table.getD out.2 0), []) := by
        simp only [runAux, hdec]
      rw [e]
      exact natDegree_getD_le hst out.2

/-- **The symbolic committed output has degree ≤ D** — the `hdeg_out` fact, proven about the
real run. -/
theorem symOutput_natDegree_le (strat : Strat p) (st₀ : St p) (fuel : ℕ) {D : ℕ}
    (hseed : ∀ q ∈ st₀.table, q.natDegree ≤ D) :
    (symOutput strat st₀ fuel).2.natDegree ≤ D := by
  simpa only [symOutput, runOutput] using
    runAux_output_natDegree_le symAns strat fuel st₀ hseed

/-! ## § Pairs — the Shoup bad-event polynomials are degree-bounded -/

/-- **Every bad-event polynomial has degree ≤ D** — the `hdeg_pairs` fact at `Δ = D`, proven
about the real run: each is a difference of two queried handles, each of which lives in the
final table (or is `0`) by `runAux_pairs_mem_runTable`, and `natDegree_sub_le` is a MAX
bound — the linear oracle pays δ = D, never 2D. -/
theorem badPolys_natDegree_le (strat : Strat p) (st₀ : St p) (fuel : ℕ) {D : ℕ}
    (hseed : ∀ q ∈ st₀.table, q.natDegree ≤ D) :
    ∀ q ∈ badPolys strat st₀ fuel, q.natDegree ≤ D := by
  intro q hq
  unfold badPolys at hq
  rw [List.mem_toFinset, List.mem_map] at hq
  obtain ⟨ab, habf, rfl⟩ := hq
  rw [List.mem_filter] at habf
  obtain ⟨hab, -⟩ := habf
  have hab' : ab ∈ (runAux symAns strat fuel st₀).2 := hab
  have hmem := runAux_pairs_mem_runTable symAns strat fuel st₀ ab hab'
  have h1 : ab.1.natDegree ≤ D := by
    rcases hmem.1 with h | h
    · exact runTable_natDegree_le symAns strat fuel st₀ hseed ab.1 h
    · rw [h]; simp
  have h2 : ab.2.natDegree ≤ D := by
    rcases hmem.2 with h | h
    · exact runTable_natDegree_le symAns strat fuel st₀ hseed ab.2 h
    · rw [h]; simp
  exact (natDegree_sub_le ab.1 ab.2).trans (max_le h1 h2)

/-! ## § Seed — the SRS table meets the bound -/

/-- The SRS-seeded table `1, X, …, X^D, 1, X` has every entry of degree ≤ D. Needs `1 ≤ D`:
the G₂ handle `X` has degree 1 (at `D = 0` the seed itself would break the bound). -/
theorem srsSt_table_natDegree_le (D : ℕ) (hD : 1 ≤ D) :
    ∀ q ∈ (srsSt (p := p) D).table, q.natDegree ≤ D := by
  intro q hq
  simp only [srsSt] at hq
  rcases List.mem_append.mp hq with h | h
  · obtain ⟨k, hk, rfl⟩ := List.mem_map.mp h
    exact (natDegree_X_pow_le k).trans (Nat.lt_succ_iff.mp (List.mem_range.mp hk))
  · rcases List.mem_cons.mp h with rfl | h
    · simp
    · rw [List.mem_singleton.mp h]
      exact natDegree_X_le.trans hD

/-! ## § Discharge — the `hdeg_*` hypotheses as theorems about the real oracle

Thin named sockets in EXACTLY the hypothesis shapes `GgmAdaptive.adaptive_ggm_sound` /
`card_realWinSet_le` (`hdeg_out`, `hdeg_pairs`) and `GgmRandomEncoding.rand_encoding_bound_D`
& friends (`hdeg_out`, `hdeg_handles`) consume, followed by the composed bounds with the
degree hypotheses GONE. -/

/-- `hdeg_out`, discharged: the symbolic output degree bound holds for the real run. -/
theorem hdeg_out_of_run (strat : Strat p) (st₀ : St p) (fuel D : ℕ)
    (hseed : ∀ q ∈ st₀.table, q.natDegree ≤ D) :
    (symOutput strat st₀ fuel).2.natDegree ≤ D :=
  symOutput_natDegree_le strat st₀ fuel hseed

/-- `hdeg_pairs` (at `Δ = D`), discharged: the bad-event degree bound holds for the real
run. -/
theorem hdeg_pairs_of_run (strat : Strat p) (st₀ : St p) (fuel D : ℕ)
    (hseed : ∀ q ∈ st₀.table, q.natDegree ≤ D) :
    ∀ q ∈ badPolys strat st₀ fuel, q.natDegree ≤ D :=
  badPolys_natDegree_le strat st₀ fuel hseed

/-- `hdeg_handles` (at δ = D), discharged: the handle-set degree bound holds for the real
run's table (`runTable`, not a peer model). -/
theorem hdeg_handles_of_run (strat : Strat p) (st₀ : St p) (fuel D : ℕ)
    (hseed : ∀ q ∈ st₀.table, q.natDegree ≤ D) :
    ∀ q ∈ handlePolys symAns strat fuel st₀, q.natDegree ≤ D :=
  handlePolys_natDegree_le symAns strat fuel st₀ hseed

/-- `GgmAdaptive.card_realWinSet_le` with both degree hypotheses DISCHARGED (Δ = D): only the
seed-table bound remains, and that is a theorem at the SRS seeding (below). -/
theorem card_realWinSet_le_of_run (strat : Strat p) (st₀ : St p) (fuel D : ℕ)
    (hseed : ∀ q ∈ st₀.table, q.natDegree ≤ D) :
    (realWinSet strat st₀ fuel).card ≤ fuel * D + (D + 1) :=
  card_realWinSet_le strat st₀ fuel D D
    (symOutput_natDegree_le strat st₀ fuel hseed)
    (badPolys_natDegree_le strat st₀ fuel hseed)

/-- **`GgmAdaptive.adaptive_ggm_sound` with the degree hypotheses DISCHARGED** (Δ = D). -/
theorem adaptive_ggm_sound_of_run (strat : Strat p) (st₀ : St p) (fuel D : ℕ) (hp : 2 ≤ p)
    (hseed : ∀ q ∈ st₀.table, q.natDegree ≤ D) :
    adaptiveExperiment strat st₀ fuel ≤ ((fuel * D + (D + 1) : ℕ) : ℚ) / (p - 1) :=
  adaptive_ggm_sound strat st₀ fuel D D hp
    (symOutput_natDegree_le strat st₀ fuel hseed)
    (badPolys_natDegree_le strat st₀ fuel hseed)

/-- **The adaptive bound at the SRS seeding, hypothesis-free** (`1 ≤ D` and `2 ≤ p` only):
every deterministic `Strat` against the SRS-seeded linear oracle wins on at most a
`(fuel·D + (D+1))/(p−1)` fraction of trapdoors — no degree assumption left. -/
theorem adaptive_ggm_sound_srs (strat : Strat p) (fuel D : ℕ) (hD : 1 ≤ D) (hp : 2 ≤ p) :
    adaptiveExperiment strat (srsSt D) fuel ≤ ((fuel * D + (D + 1) : ℕ) : ℚ) / (p - 1) :=
  adaptive_ggm_sound_of_run strat (srsSt D) fuel D hp (srsSt_table_natDegree_le D hD)

/-- **`GgmRandomEncoding.rand_encoding_bound_D` with the degree hypotheses DISCHARGED**. -/
theorem rand_encoding_bound_D_of_run (strat : Strat p) (st₀ : St p) (fuel D n : ℕ)
    (hp : 2 ≤ p) (hseed : ∀ q ∈ st₀.table, q.natDegree ≤ D)
    (hn : st₀.table.length + fuel + 1 ≤ n) :
    adaptiveExperiment strat st₀ fuel ≤ ((n.choose 2 * D + (D + 1) : ℕ) : ℚ) / (p - 1) :=
  rand_encoding_bound_D strat st₀ fuel D n hp
    (symOutput_natDegree_le strat st₀ fuel hseed)
    (handlePolys_natDegree_le symAns strat fuel st₀ hseed) hn

/-- **The all-pairs δ = D bound at the SRS seeding, hypothesis-free** (`1 ≤ D`,
`2 ≤ p`): the concrete `(C(fuel+D+4, 2)·D + (D+1))/(p−1)` Shoup number with every degree
fact a theorem about the actual oracle. -/
theorem rand_encoding_bound_srs_D_of_run (strat : Strat p) (fuel D : ℕ) (hD : 1 ≤ D)
    (hp : 2 ≤ p) :
    adaptiveExperiment strat (srsSt D) fuel ≤
      (((fuel + D + 4).choose 2 * D + (D + 1) : ℕ) : ℚ) / (p - 1) :=
  rand_encoding_bound_srs_D strat fuel D hp
    (symOutput_natDegree_le strat (srsSt D) fuel (srsSt_table_natDegree_le D hD))
    (handlePolys_natDegree_le symAns strat fuel (srsSt D) (srsSt_table_natDegree_le D hD))

end GgmDegreeDischarge

-- Axiom receipts: every theorem is sorry-free on the standard three axioms.
#print axioms GgmDegreeDischarge.natDegree_combine_le
#print axioms GgmDegreeDischarge.runTable_natDegree_le
#print axioms GgmDegreeDischarge.handlePolys_natDegree_le
#print axioms GgmDegreeDischarge.runAux_output_natDegree_le
#print axioms GgmDegreeDischarge.symOutput_natDegree_le
#print axioms GgmDegreeDischarge.badPolys_natDegree_le
#print axioms GgmDegreeDischarge.srsSt_table_natDegree_le
#print axioms GgmDegreeDischarge.hdeg_out_of_run
#print axioms GgmDegreeDischarge.hdeg_pairs_of_run
#print axioms GgmDegreeDischarge.hdeg_handles_of_run
#print axioms GgmDegreeDischarge.card_realWinSet_le_of_run
#print axioms GgmDegreeDischarge.adaptive_ggm_sound_of_run
#print axioms GgmDegreeDischarge.adaptive_ggm_sound_srs
#print axioms GgmDegreeDischarge.rand_encoding_bound_D_of_run
#print axioms GgmDegreeDischarge.rand_encoding_bound_srs_D_of_run

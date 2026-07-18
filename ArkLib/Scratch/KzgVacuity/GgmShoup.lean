/-
Copyright (c) 2026 Ember Arlynx. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ember Arlynx
-/
import ArkLib.Scratch.KzgVacuity.GgmDegreeDischarge

/-!
# The Shoup random-encoding GGM $t$-SDH bound with a free-comparison adversary

This file mechanizes the random-encoding (Shoup) generic-group model for the $t$-SDH problem
[Sho97], [BB04] — the second standard GGM track, alongside the Maurer explicit-equality track
[Mau05]. In Maurer's model the adversary must spend a query step to test one handle pair, and only
queried pairs enter the bad event. Here the model is genuinely different: comparison is free.

## The Shoup random-encoding model

Group elements are lazily-sampled encodings under an injection
$\sigma : \mathbb{Z}_p \hookrightarrow E$. The adversary holds a `List E`, applies the group-op
oracle (`lin` — degree $\le D$, pairing-free, matching ArkLib's $G_1$-only `tSdhAdversary`), and —
the crux distinction from Maurer — may compare any two encodings it holds for free via
`DecidableEq E`. So at every step it observes the full $|tbl| \times |tbl|$ equality pattern of all
its held handles at zero fuel and handle cost, and branches on the entire pattern-history.

Because $\sigma$ is injective, the equality pattern it observes,
$\sigma(f_i(\tau)) = \sigma(f_j(\tau)) \iff f_i(\tau) = f_j(\tau)$, is exactly the eval-at-$\tau$
pattern (`realAns τ`); the symbolic ($\tau$-independent) pattern is formal equality (`symAns`). So
the encoding $\sigma$ never enters the mechanization — injectivity folds it away, exactly as
`GgmArkLibTransport.gpow_val_inj_iff` folds the concrete encoding $a \mapsto g^{a.\mathrm{val}}$
away in the Maurer embed. $E$ and $\sigma$ live only in this docstring, where they name the model.

Free comparison makes the all-pairs collision event tight: the adversary really can compare any
pair, so the leak is on exactly `pairRootUnion (handleSet)` — no $\subseteq$ slack, no `badSet`
indirection.

## Structure

* The model: `eqPattern` (the free full-table equality matrix, `Σ n, Fin n → Fin n → Bool`),
  `ShoupMove` (`lin`-only — no query, equality is ambient), `ShoupStrat` (decides on the
  pattern-history), `ShSt`, `runShoup`, `realWinSetShoup`, `shoupExperiment`.
* The hybrid, the crux, proven not assumed: `runShoup_congr_off_bad` — a matrix-valued
  identical-until-bad. If $\tau \notin$ `pairRootUnion (handleSet)` then the real run equals the
  symbolic run, with step-wise full-pattern agreement discharged from the single global
  non-collision fact (every reachable table is a subset of the final handle set). This is the
  free-comparison analogue of `GgmAdaptive.runAux_congr_of_agree`, but the branching input is a
  whole equality matrix, and the bad event is the all-pairs union.
* The bound: `realWinSetShoup ⊆ pairRootUnion (handleSet) ∪ winningPoints sym`, composed with the
  reused `GgmRandomEncoding.card_pairRootUnion_le_D` (all-pairs Schwartz–Zippel [Sch80], [Zip79])
  and `GgmCandidate.card_winningPoints_le` (static Boneh–Boyen root event [BB04]), giving numerator
  $\binom{fuel+D+4}{2} \cdot D + (D+1)$.

## References

* [Boneh, D., and Boyen, X., *Short Signatures Without Random Oracles*][BB04]
* [Shoup, V., *Lower Bounds for Discrete Logarithms and Related Problems*][Sho97]
* [Maurer, U., *Abstract Models of Computation in Cryptography*][Mau05]
* [Schwartz, J. T., *Fast Probabilistic Algorithms for Verification of Polynomial
    Identities*][Sch80]
* [Zippel, R., *Probabilistic Algorithms for Sparse Polynomials*][Zip79]
-/

open Polynomial

namespace GgmShoup

open GgmCandidate GgmAdaptive GgmRandomEncoding GgmDegreeDischarge GgmDegreeInvariant

variable {p : ℕ} [Fact (Nat.Prime p)]

/-! ## § Model — the free-comparison random-encoding oracle

The crux distinction from Maurer. Comparison is AMBIENT and FREE: at every step the adversary
observes the full equality pattern (the pairwise-equality matrix under the oracle) of ALL handles it
holds, at no fuel and no handle cost, and branches on the entire pattern-history. There is no
`query` move — equality is not a spent step. `lin` is the only oracle-consuming move (degree ≤ D,
pairing-free: ArkLib's `tSdhAdversary` is granted no pairing map). -/

/-- The free-comparison observation: the `|tbl|×|tbl|` equality matrix under the oracle `ans`.
Packaged with its dimension so successive (growing) observations have a uniform type. -/
noncomputable def eqPattern (ans : AnswerFn p) (tbl : List ((ZMod p)[X])) :
    Σ n : ℕ, Fin n → Fin n → Bool :=
  ⟨tbl.length, fun i j => ans (tbl.get i) (tbl.get j)⟩

/-- A Shoup (random-encoding) group-op move: `lin` appends `Σ cᵢ · handleᵢ`. There is NO `query`
constructor — equality is ambient (see `eqPattern`), never a spent step. `lin` is pairing-free
(degree ≤ D), matching ArkLib's G₁-only `tSdhAdversary`. -/
inductive ShoupMove (p : ℕ) where
  | lin : List (ZMod p × ℕ) → ShoupMove p

/-- A Shoup (random-encoding) strategy: decides on the HISTORY OF FULL EQUALITY PATTERNS observed so
far — never on a chosen single query. Equality is ambient, so the input is a `List` of full-table
patterns, one per step, not a `List Bool` of chosen-pair answers (the Maurer input). This typing is
what makes the model random-encoding-and-free-comparison rather than Maurer. -/
abbrev ShoupStrat (p : ℕ) := List (Σ n : ℕ, Fin n → Fin n → Bool) → ShoupMove p ⊕ (ZMod p × ℕ)

/-- Shoup oracle state: the handle table and the pattern-history. -/
structure ShSt (p : ℕ) where
  table : List ((ZMod p)[X])
  phist : List (Σ n : ℕ, Fin n → Fin n → Bool)

/-- **The Shoup run.** Each step: observe the current table's FULL equality pattern under `ans`
(free comparison), append it to the pattern-history, let `strat` decide. `lin` appends a `combine`;
output reads out `(offset, table.getD k 0)`. Mirrors `GgmAdaptive.runAux` but threads PATTERNS, not
booleans, and has no `query` branch. -/
noncomputable def runShoup (ans : AnswerFn p) (strat : ShoupStrat p) :
    ℕ → ShSt p → (ZMod p × (ZMod p)[X])
  | 0, _ => (0, 0)
  | fuel + 1, st =>
    match strat (st.phist ++ [eqPattern ans st.table]) with
    | Sum.inr (c, k) => (c, st.table.getD k 0)
    | Sum.inl (ShoupMove.lin spec) =>
        runShoup ans strat fuel
          ⟨st.table ++ [combine spec st.table], st.phist ++ [eqPattern ans st.table]⟩

/-- The final handle table of a Shoup run (mirrors `GgmRandomEncoding.runTable`, `lin`-only). -/
noncomputable def runTableShoup (ans : AnswerFn p) (strat : ShoupStrat p) :
    ℕ → ShSt p → List ((ZMod p)[X])
  | 0, st => st.table
  | fuel + 1, st =>
    match strat (st.phist ++ [eqPattern ans st.table]) with
    | Sum.inr _ => st.table
    | Sum.inl (ShoupMove.lin spec) =>
        runTableShoup ans strat fuel
          ⟨st.table ++ [combine spec st.table], st.phist ++ [eqPattern ans st.table]⟩

/-- The finite set of handle polynomials the SYMBOLIC run can ever hold: the final symbolic table
plus the zero/identity handle (the out-of-range `getD` default). This is the set whose all-pairs
collision event is TIGHT for the free-comparison adversary. -/
noncomputable def handleSetShoup (strat : ShoupStrat p) (st₀ : ShSt p) (fuel : ℕ) :
    Finset ((ZMod p)[X]) :=
  insert 0 (runTableShoup symAns strat fuel st₀).toFinset

/-- The trapdoors on which the free-comparison adversary wins t-SDH against the REAL encoding oracle
at `τ`. Same τ+c≠0-guarded win predicate reused verbatim from the static/Maurer files. -/
noncomputable def realWinSetShoup (strat : ShoupStrat p) (st₀ : ShSt p) (fuel : ℕ) :
    Finset (ZMod p) :=
  nonzeroPoints.filter (fun τ =>
    τ + (runShoup (realAns τ) strat fuel st₀).1 ≠ 0 ∧
      (runShoup (realAns τ) strat fuel st₀).2.eval τ
        = 1 / (τ + (runShoup (realAns τ) strat fuel st₀).1))

/-- The Shoup success fraction: winning trapdoors over the `p−1` nonzero trapdoors. -/
noncomputable def shoupExperiment (strat : ShoupStrat p) (st₀ : ShSt p) (fuel : ℕ) : ℚ :=
  (realWinSetShoup strat st₀ fuel).card / (p - 1)

/-! ## § Table — structural lemmas for the Shoup handle table

`runTableShoup` only grows the table (one `combine` per `lin` step), so its final table has the
current table as a prefix and length ≤ initial + fuel. Both by induction on fuel. -/

/-- The table only ever grows: the current table is a prefix of the final one. -/
theorem table_prefix_runTableShoup (ans : AnswerFn p) (strat : ShoupStrat p) :
    ∀ (fuel : ℕ) (st : ShSt p), st.table <+: runTableShoup ans strat fuel st := by
  intro fuel
  induction fuel with
  | zero => intro st; simp only [runTableShoup]; exact List.prefix_rfl
  | succ fuel ih =>
    intro st
    rcases hdec : strat (st.phist ++ [eqPattern ans st.table]) with m | out
    · cases m with
      | lin spec =>
        have e : runTableShoup ans strat (fuel + 1) st
            = runTableShoup ans strat fuel
                ⟨st.table ++ [combine spec st.table], st.phist ++ [eqPattern ans st.table]⟩ := by
          simp only [runTableShoup, hdec]
        rw [e]
        exact (List.prefix_append _ _).trans
          (ih ⟨st.table ++ [combine spec st.table], st.phist ++ [eqPattern ans st.table]⟩)
    · have e : runTableShoup ans strat (fuel + 1) st = st.table := by
        simp only [runTableShoup, hdec]
      rw [e]

/-- Each fuel step appends at most one handle: the final table has length ≤ initial + fuel. -/
theorem runTableShoup_length_le (ans : AnswerFn p) (strat : ShoupStrat p) :
    ∀ (fuel : ℕ) (st : ShSt p),
      (runTableShoup ans strat fuel st).length ≤ st.table.length + fuel := by
  intro fuel
  induction fuel with
  | zero => intro st; simp only [runTableShoup]; omega
  | succ fuel ih =>
    intro st
    rcases hdec : strat (st.phist ++ [eqPattern ans st.table]) with m | out
    · cases m with
      | lin spec =>
        have e : runTableShoup ans strat (fuel + 1) st
            = runTableShoup ans strat fuel
                ⟨st.table ++ [combine spec st.table], st.phist ++ [eqPattern ans st.table]⟩ := by
          simp only [runTableShoup, hdec]
        rw [e]
        have := ih ⟨st.table ++ [combine spec st.table], st.phist ++ [eqPattern ans st.table]⟩
        simp only [List.length_append, List.length_cons, List.length_nil] at this
        omega
    · have e : runTableShoup ans strat (fuel + 1) st = st.table := by
        simp only [runTableShoup, hdec]
      rw [e]; omega

/-- **The handle-set size bound, a THEOREM.** The symbolic handle set has card ≤ (seed count) +
fuel + 1: one appended handle per fuel step, plus the zero/identity handle. -/
theorem card_handleSetShoup_le (strat : ShoupStrat p) (st₀ : ShSt p) (fuel : ℕ) :
    (handleSetShoup strat st₀ fuel).card ≤ st₀.table.length + fuel + 1 := by
  refine (Finset.card_insert_le _ _).trans ?_
  have h := (List.toFinset_card_le (runTableShoup symAns strat fuel st₀)).trans
    (runTableShoup_length_le symAns strat fuel st₀)
  omega

/-! ## § Degree — the Shoup handle table and output stay degree-bounded

The oracle is purely LINEAR (`lin` only): a `combine` over a degree-≤D table stays ≤ D
(`GgmDegreeDischarge.natDegree_combine_le`, REUSED). By induction on fuel, so is the whole final
table, and the committed output (a defaulted table read). -/

/-- **The degree invariant of the Shoup handle table.** If every seed polynomial has natDegree ≤ D,
so does every polynomial in the run's final table — for ANY answer function. -/
theorem runTableShoup_natDegree_le (ans : AnswerFn p) (strat : ShoupStrat p) {D : ℕ} :
    ∀ (fuel : ℕ) (st : ShSt p), (∀ q ∈ st.table, q.natDegree ≤ D) →
      ∀ q ∈ runTableShoup ans strat fuel st, q.natDegree ≤ D := by
  intro fuel
  induction fuel with
  | zero => intro st hst q hq; simp only [runTableShoup] at hq; exact hst q hq
  | succ fuel ih =>
    intro st hst q hq
    rcases hdec : strat (st.phist ++ [eqPattern ans st.table]) with m | out
    · cases m with
      | lin spec =>
        have e : runTableShoup ans strat (fuel + 1) st
            = runTableShoup ans strat fuel
                ⟨st.table ++ [combine spec st.table], st.phist ++ [eqPattern ans st.table]⟩ := by
          simp only [runTableShoup, hdec]
        rw [e] at hq
        refine ih _ ?_ q hq
        intro r hr
        rcases List.mem_append.mp hr with h | h
        · exact hst r h
        · rw [List.mem_singleton.mp h]; exact natDegree_combine_le hst spec
    · have e : runTableShoup ans strat (fuel + 1) st = st.table := by
        simp only [runTableShoup, hdec]
      rw [e] at hq; exact hst q hq

/-- **The handle-set degree invariant** — the zero/identity handle has degree 0. -/
theorem handleSetShoup_natDegree_le (strat : ShoupStrat p) (st₀ : ShSt p) (fuel : ℕ) {D : ℕ}
    (hseed : ∀ q ∈ st₀.table, q.natDegree ≤ D) :
    ∀ q ∈ handleSetShoup strat st₀ fuel, q.natDegree ≤ D := by
  intro q hq
  unfold handleSetShoup at hq
  rcases Finset.mem_insert.mp hq with h | h
  · rw [h]; simp
  · exact runTableShoup_natDegree_le symAns strat fuel st₀ hseed q (List.mem_toFinset.mp h)

/-- **The committed output has degree ≤ D** — a defaulted table read at commit time (or `0` on
fuel exhaustion); every intermediate table is bounded. Induction on fuel, for ANY answer
function. -/
theorem runShoup_output_natDegree_le (ans : AnswerFn p) (strat : ShoupStrat p) {D : ℕ} :
    ∀ (fuel : ℕ) (st : ShSt p), (∀ q ∈ st.table, q.natDegree ≤ D) →
      (runShoup ans strat fuel st).2.natDegree ≤ D := by
  intro fuel
  induction fuel with
  | zero => intro st _; simp [runShoup]
  | succ fuel ih =>
    intro st hst
    rcases hdec : strat (st.phist ++ [eqPattern ans st.table]) with m | out
    · cases m with
      | lin spec =>
        have e : runShoup ans strat (fuel + 1) st
            = runShoup ans strat fuel
                ⟨st.table ++ [combine spec st.table], st.phist ++ [eqPattern ans st.table]⟩ := by
          simp only [runShoup, hdec]
        rw [e]
        refine ih _ ?_
        intro r hr
        rcases List.mem_append.mp hr with h | h
        · exact hst r h
        · rw [List.mem_singleton.mp h]; exact natDegree_combine_le hst spec
    · have e : runShoup ans strat (fuel + 1) st = (out.1, st.table.getD out.2 0) := by
        simp only [runShoup, hdec]
      rw [e]; exact natDegree_getD_le hst out.2

/-! ## § Hybrid — the matrix-valued identical-until-collision (the crux, S4)

Shoup's identical-until-bad for the free-comparison model. Where Maurer's `runAux_congr_of_agree`
threads a per-query boolean agreement, here the branching input is a WHOLE equality matrix, and the
single global hypothesis `τ ∉ pairRootUnion(handleSet)` discharges every step's full-pattern
agreement — which is exactly WHY the bad event is all-pairs. -/

/-- Two answer functions agreeing entrywise on a table produce the SAME `eqPattern`
(same dimension by construction; the matrices coincide by `funext`). -/
lemma eqPattern_congr {ans1 ans2 : AnswerFn p} {tbl : List ((ZMod p)[X])}
    (h : ∀ i j : Fin tbl.length, ans1 (tbl.get i) (tbl.get j) = ans2 (tbl.get i) (tbl.get j)) :
    eqPattern ans1 tbl = eqPattern ans2 tbl := by
  unfold eqPattern
  refine Sigma.ext rfl ?_
  refine heq_of_eq (funext fun i => funext fun j => ?_)
  exact h i j

/-- `pairRootUnion` is monotone: a larger handle set has a larger all-pairs collision set. -/
lemma pairRootUnion_mono {s t : Finset ((ZMod p)[X])} (h : s ⊆ t) :
    pairRootUnion s ⊆ pairRootUnion t := by
  intro τ hτ
  rw [mem_pairRootUnion] at hτ ⊢
  obtain ⟨q₁, q₂, h1, h2, hne, hr⟩ := hτ
  exact ⟨q₁, q₂, h h1, h h2, hne, hr⟩

/-- **Pattern agreement off the all-pairs bad set.** For a table all of whose entries lie in a
handle set with `τ ∉ pairRootUnion`, the real (eval-at-τ) equality pattern equals the symbolic
(formal-equality) one: distinct entries do not collide at τ (τ not a root of their difference),
and equal ones agree trivially. -/
lemma eqPattern_realAns_eq_symAns {τ : ZMod p} {tbl : List ((ZMod p)[X])}
    (hτ : τ ∉ pairRootUnion tbl.toFinset) :
    eqPattern (realAns τ) tbl = eqPattern symAns tbl := by
  refine eqPattern_congr fun i j => ?_
  by_cases hfg : tbl.get i = tbl.get j
  · simp only [realAns, symAns, hfg]
  · have hne : tbl.get i - tbl.get j ≠ 0 := sub_ne_zero.mpr hfg
    have hmem_i : tbl.get i ∈ tbl.toFinset := List.mem_toFinset.mpr (List.get_mem _ _)
    have hmem_j : tbl.get j ∈ tbl.toFinset := List.mem_toFinset.mpr (List.get_mem _ _)
    have hnotroot : τ ∉ (tbl.get i - tbl.get j).roots.toFinset := fun hc =>
      hτ (mem_pairRootUnion.mpr ⟨_, _, hmem_i, hmem_j, hfg, hc⟩)
    have hevalne : (tbl.get i).eval τ ≠ (tbl.get j).eval τ := by
      intro hE
      apply hnotroot
      rw [Multiset.mem_toFinset, mem_roots hne]
      simp only [IsRoot.def, eval_sub, hE, sub_self]
    simp only [realAns, symAns, decide_eq_decide]
    exact ⟨fun h => absurd h hevalne, fun h => absurd h hfg⟩

/-- **IDENTICAL-UNTIL-BAD, the crux (matrix-valued), PROVEN not assumed.** If
`τ ∉ pairRootUnion(handleSet)` (the all-pairs collision set of the final SYMBOLIC handle table),
the real run and the symbolic run COINCIDE. Induction on fuel: at each step the two runs are in
lockstep so observe the same table; by `eqPattern_realAns_eq_symAns` the two FULL patterns are equal
(the current table is a prefix of the final handle set, and `pairRootUnion` is monotone), so `strat`
makes the same decision and the recursion continues in lockstep. The single global non-collision
hypothesis discharges every step's full-pattern agreement — the free-comparison analogue of
`GgmAdaptive.runAux_congr_of_agree`. -/
theorem runShoup_congr_off_bad (strat : ShoupStrat p) {τ : ZMod p} :
    ∀ (fuel : ℕ) (st : ShSt p),
      τ ∉ pairRootUnion (insert 0 (runTableShoup symAns strat fuel st).toFinset) →
      runShoup (realAns τ) strat fuel st = runShoup symAns strat fuel st := by
  intro fuel
  induction fuel with
  | zero => intro st _; rfl
  | succ fuel ih =>
    intro st hτ
    -- The current table's entries all lie in the final symbolic handle set.
    have hsub : st.table.toFinset
        ⊆ insert 0 (runTableShoup symAns strat (fuel + 1) st).toFinset := by
      have hpre : st.table <+: runTableShoup symAns strat (fuel + 1) st :=
        table_prefix_runTableShoup symAns strat (fuel + 1) st
      intro x hx
      exact Finset.mem_insert_of_mem (List.mem_toFinset.mpr (hpre.subset (List.mem_toFinset.mp hx)))
    -- Hence the real and symbolic observations of the current table agree.
    have hobs : eqPattern (realAns τ) st.table = eqPattern symAns st.table :=
      eqPattern_realAns_eq_symAns (fun hc => hτ (pairRootUnion_mono hsub hc))
    rcases hdec : strat (st.phist ++ [eqPattern symAns st.table]) with m | out
    · cases m with
      | lin spec =>
        have eR : runShoup (realAns τ) strat (fuel + 1) st
            = runShoup (realAns τ) strat fuel
                ⟨st.table ++ [combine spec st.table], st.phist ++ [eqPattern symAns st.table]⟩ := by
          simp only [runShoup, hobs, hdec]
        have eS : runShoup symAns strat (fuel + 1) st
            = runShoup symAns strat fuel
                ⟨st.table ++ [combine spec st.table], st.phist ++ [eqPattern symAns st.table]⟩ := by
          simp only [runShoup, hdec]
        have eT : runTableShoup symAns strat (fuel + 1) st
            = runTableShoup symAns strat fuel
                ⟨st.table ++ [combine spec st.table], st.phist ++ [eqPattern symAns st.table]⟩ := by
          simp only [runTableShoup, hdec]
        rw [eR, eS]
        exact ih _ (by rw [← eT]; exact hτ)
    · have eR : runShoup (realAns τ) strat (fuel + 1) st = (out.1, st.table.getD out.2 0) := by
        simp only [runShoup, hobs, hdec]
      have eS : runShoup symAns strat (fuel + 1) st = (out.1, st.table.getD out.2 0) := by
        simp only [runShoup, hdec]
      rw [eR, eS]

/-- **Identical-until-bad, at the set level** (S5). Every real winning trapdoor either triggers the
all-pairs collision event or is a static win of the τ-independent symbolic output — Shoup's
`W₀ ⊆ pairRootUnion(handleSet) ∪ F`, with the bad set already EQUAL to `pairRootUnion(handleSet)`
(no `badSet` indirection: free comparison makes the all-pairs union primitive). -/
theorem realWinSetShoup_subset (strat : ShoupStrat p) (st₀ : ShSt p) (fuel D : ℕ)
    (hdeg_out : (runShoup symAns strat fuel st₀).2.natDegree ≤ D) :
    realWinSetShoup strat st₀ fuel ⊆
      pairRootUnion (handleSetShoup strat st₀ fuel) ∪
        GgmCandidate.winningPoints
          (⟨(runShoup symAns strat fuel st₀).1, (runShoup symAns strat fuel st₀).2, hdeg_out⟩ :
            GenericAdversary D p) := by
  classical
  intro τ hτ
  rw [realWinSetShoup, Finset.mem_filter] at hτ
  obtain ⟨hnz, hcond1, hcond2⟩ := hτ
  by_cases hbad : τ ∈ pairRootUnion (handleSetShoup strat st₀ fuel)
  · exact Finset.mem_union_left _ hbad
  · refine Finset.mem_union_right _ ?_
    have heq := runShoup_congr_off_bad strat fuel st₀ hbad
    rw [heq] at hcond1 hcond2
    rw [GgmCandidate.winningPoints, Finset.mem_filter]
    exact ⟨hnz, hcond1, hcond2⟩

/-! ## § Bound — compose the REUSED all-pairs SZ core with the static root event

`Pr[win] ≤ Pr[bad] + Pr[sym win]`. `Pr[bad]` consumes `card_pairRootUnion_le_D` DIRECTLY (tight —
no `badSet` step); `Pr[sym win]` consumes `card_winningPoints_le`. Both REUSED verbatim. The degree
hypotheses are DISCHARGED via `handleSetShoup_natDegree_le` / `runShoup_output_natDegree_le`. -/

/-- **The all-pairs counting bound.** With the handle-set and output degree invariants (both
DISCHARGED below at the SRS seeding), the free-comparison adversary wins on ≤ `C(#handles, 2)·D +
(D+1)` trapdoors. Reuses `card_pairRootUnion_le_D` and `card_winningPoints_le`. -/
theorem card_realWinSetShoup_le_allPairs (strat : ShoupStrat p) (st₀ : ShSt p) (fuel D : ℕ)
    (hdeg_out : (runShoup symAns strat fuel st₀).2.natDegree ≤ D)
    (hdeg_handles : ∀ q ∈ handleSetShoup strat st₀ fuel, q.natDegree ≤ D) :
    (realWinSetShoup strat st₀ fuel).card ≤
      (handleSetShoup strat st₀ fuel).card.choose 2 * D + (D + 1) := by
  classical
  refine (Finset.card_le_card (realWinSetShoup_subset strat st₀ fuel D hdeg_out)).trans ?_
  refine (Finset.card_union_le _ _).trans ?_
  have hbad : (pairRootUnion (handleSetShoup strat st₀ fuel)).card ≤
      (handleSetShoup strat st₀ fuel).card.choose 2 * D :=
    card_pairRootUnion_le_D hdeg_handles
  exact Nat.add_le_add hbad (card_winningPoints_le _)

/-- The counting bound at an abstract table-size bound `n` (`C(·, 2)` monotone). -/
theorem card_realWinSetShoup_le_encoding (strat : ShoupStrat p) (st₀ : ShSt p) (fuel D n : ℕ)
    (hdeg_out : (runShoup symAns strat fuel st₀).2.natDegree ≤ D)
    (hdeg_handles : ∀ q ∈ handleSetShoup strat st₀ fuel, q.natDegree ≤ D)
    (hn : st₀.table.length + fuel + 1 ≤ n) :
    (realWinSetShoup strat st₀ fuel).card ≤ n.choose 2 * D + (D + 1) := by
  refine (card_realWinSetShoup_le_allPairs strat st₀ fuel D hdeg_out hdeg_handles).trans ?_
  have hcard : (handleSetShoup strat st₀ fuel).card ≤ n :=
    (card_handleSetShoup_le strat st₀ fuel).trans hn
  exact Nat.add_le_add_right (Nat.mul_le_mul_right _ (Nat.choose_le_choose 2 hcard)) _

/-! ## § SRS — the seeded instantiation, `n = fuel + D + 4`

REUSE `GgmRandomEncoding.srsSt`'s table (`1, X, …, X^D, 1, X`, seed count D+3) as the Shoup seed;
its length and degree lemmas apply verbatim. -/

/-- The SRS-seeded Shoup initial state: same seed table as the Maurer/all-pairs files, empty
pattern-history. -/
noncomputable def srsStShoup (D : ℕ) : ShSt p := ⟨(srsSt (p := p) D).table, []⟩

@[simp] lemma srsStShoup_table (D : ℕ) : (srsStShoup (p := p) D).table = (srsSt (p := p) D).table :=
  rfl

/-- **THE RANDOM-ENCODING (SHOUP) GGM t-SDH BOUND (sorry-free; Tier 1).**
Every free-comparison generic strategy — one that observes, at each step and FOR FREE, the full
equality pattern of all its held encodings — wins t-SDH against the real encoding oracle on at
most a `(C(fuel+D+4, 2)·D + (D+1))/(p−1)` fraction of trapdoors: the all-pairs collision event
(now TIGHT,
because comparison is free) plus the static Boneh–Boyen root event. SAME NUMERATOR as
`GgmRandomEncoding.rand_encoding_bound_srs_D`; the difference is the MODEL in which it is proved
(random-encoding free-comparison, not Maurer explicit-equality). The degree invariants are
DISCHARGED here (not assumed), and the identical-until-bad hybrid `runShoup_congr_off_bad` is
PROVEN. -/
theorem shoup_ggm_sound (strat : ShoupStrat p) (fuel D : ℕ) (hD : 1 ≤ D) (hp : 2 ≤ p) :
    shoupExperiment strat (srsStShoup D) fuel
      ≤ (((fuel + D + 4).choose 2 * D + (D + 1) : ℕ) : ℚ) / (p - 1) := by
  unfold shoupExperiment
  have hseed : ∀ q ∈ (srsStShoup (p := p) D).table, q.natDegree ≤ D := by
    rw [srsStShoup_table]; exact srsSt_table_natDegree_le D hD
  have hlen : (srsStShoup (p := p) D).table.length + fuel + 1 ≤ fuel + D + 4 := by
    rw [srsStShoup_table, srsSt_table_length]; omega
  have hcard := card_realWinSetShoup_le_encoding strat (srsStShoup D) fuel D (fuel + D + 4)
    (runShoup_output_natDegree_le symAns strat fuel (srsStShoup D) hseed)
    (handleSetShoup_natDegree_le strat (srsStShoup D) fuel hseed) hlen
  have hnum : ((realWinSetShoup strat (srsStShoup D) fuel).card : ℚ)
      ≤ (((fuel + D + 4).choose 2 * D + (D + 1) : ℕ) : ℚ) := by exact_mod_cast hcard
  have hden : (0 : ℚ) < (p : ℚ) - 1 := by
    have : (2 : ℚ) ≤ (p : ℚ) := by exact_mod_cast hp
    linarith
  gcongr

omit [Fact (Nat.Prime p)] in
/-- **Non-vacuity of the Shoup bound.** Whenever `C(fuel+D+4, 2)·D + (D+1) < p − 1` the bound is a
genuine rational `< 1` — at cryptographic parameters (`p ≈ 2²⁵⁴`, `D ≈ 2²⁰`, `fuel ≈ 2⁶⁰`) it is
`≈ 2⁻¹¹⁴`. Same non-vacuity shape as `rand_encoding_bound_lt_one`. -/
theorem shoup_ggm_sound_lt_one (fuel D : ℕ)
    (hreg : (fuel + D + 4).choose 2 * D + (D + 1) < p - 1) (hp : 2 ≤ p) :
    (((fuel + D + 4).choose 2 * D + (D + 1) : ℕ) : ℚ) / (p - 1) < 1 := by
  have hden : (0 : ℚ) < (p : ℚ) - 1 := by
    have : (2 : ℚ) ≤ (p : ℚ) := by exact_mod_cast hp
    linarith
  rw [div_lt_one hden]
  have h1 : (((fuel + D + 4).choose 2 * D + (D + 1) : ℕ) : ℚ) < ((p - 1 : ℕ) : ℚ) := by
    exact_mod_cast hreg
  have h2 : ((p - 1 : ℕ) : ℚ) = (p : ℚ) - 1 := by
    have : (1 : ℕ) ≤ p := by omega
    push_cast [Nat.cast_sub this]; ring
  rw [h2] at h1; exact h1

end GgmShoup

-- Axiom receipts: every headline theorem is sorry-free on the standard three axioms.
#print axioms GgmShoup.runShoup_congr_off_bad
#print axioms GgmShoup.realWinSetShoup_subset
#print axioms GgmShoup.card_realWinSetShoup_le_allPairs
#print axioms GgmShoup.shoup_ggm_sound
#print axioms GgmShoup.shoup_ggm_sound_lt_one

/-
Copyright (c) 2026 Ember Arlynx. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ember Arlynx
-/
import ArkLib.Scratch.KzgVacuity.GgmAdaptive
import Mathlib.Data.Sym.Card

/-!
# All-pairs (random-encoding) collision bound for the generic-group t-SDH game

This file strengthens the per-query adaptive generic-group-model bound of `GgmAdaptive` into an
all-pairs / global bad-event bound, in the style of the random-encoding analyses of the generic
group model [Sho97].

`GgmAdaptive` bounds the bad event *per explicit equality query*: `fuel` queries, each contributing
$\le \Delta$ collision trapdoors. Here that same explicit-query bad set is upper-bounded by the
global all-pairs collision set: some two formally-distinct table polynomials collide at the
trapdoor $\tau$. The resulting count is the conservative all-pairs number.

The operational semantics remains `GgmAdaptive.Strat`, where comparisons must be requested with
`Move.query`. This file does not define a free-comparison random-encoding semantics or prove a
simulation theorem for one; it proves a sound, looser bound for the explicit-query embedded
strategies. The bound is parameterized by a per-handle degree $\Delta$ and instantiated at two
degrees:

* $\Delta = D$ — the linear-oracle instantiation. The Boneh–Boyen t-SDH adversary [BB04] receives
  `Vector G₁ (D+1) × Vector G₂ 2`, must output a `G₁` element, and is granted no pairing map
  `e : G₁ × G₂ → Gₜ`. So every handle it can form is a `ZMod p`-linear combination of the seed
  $\{1, X, \dots, X^D\}$, of degree $\le D$, and a difference of two such handles again has degree
  $\le D$ (`natDegree_sub_le` — the max, not the sum). This is the $\sim (q+D)^2 D / p$ bound, with
  the degree invariant discharged (not assumed) downstream.

* $\Delta = 2D$ — an algebraic specialization (`rand_encoding_bound`, `rand_encoding_bound_srs`),
  valid when the caller supplies a $\le 2D$ invariant for the same linear `runAux` semantics. It
  does not model a pairing move; a genuine pairing-capable oracle would need a separate two-sorted
  operational semantics and transport.

Both instantiations are one-line specializations of the same general-$\Delta$ all-pairs lemma, so
the file has a single mathematical core; the two degrees differ only in the supplied handle-degree
hypothesis.

## All-pairs Schwartz–Zippel

For a finite set `ps` of polynomials of degree $\le \Delta$, the union over unordered pairs
$q_1 \ne q_2 \in$ `ps` of `roots (q₁ - q₂)` has card $\le \binom{\#ps}{2} \cdot \Delta$
(`card_pairRootUnion_le`) [Sch80], [Zip79]. The unordered count is exact:
`roots (q₁ - q₂) = roots (q₂ - q₁)` as sets, so the ordered `offDiag` union is re-indexed through
`Sym2` (`Sym2.card_image_offDiag`), paying $\binom{n}{2}$, not $n(n-1)$. Degree bookkeeping:
`natDegree (q₁ - q₂) ≤ max (deg q₁) (deg q₂) ≤ Δ` (`natDegree_sub_le` — the max, not the sum:
differences of two degree-$\le \Delta$ handles stay $\le \Delta$, they do not compound to
$2\Delta$).

## The handle table, structurally

`runTable` is the final handle table of a run; every polynomial the adversary ever queried is in it
(or is the zero polynomial — the out-of-range handle default, i.e. the group identity), proven by
induction (`runAux_pairs_mem_runTable`), and its length is $\le$ (seed count) $+$ fuel, proven by
induction (`runTable_length_le`). With the SRS seeding (G₁: `1, X, …, X^D` = D+1 handles; G₂: `1, X`
= 2 handles; seed count D+3) the handle-set card is $\le$ fuel $+ D + 4$ — the $+4$ is the $D+3$
seeds plus the zero/identity handle. The table size is therefore a theorem here
(`card_handlePolys_le`), not a hypothesis.

## The all-pairs bound

Every deterministic `Strat` in the explicit-query model wins t-SDH on at most a
$(\binom{n}{2} \cdot \Delta + (D+1))/(p-1)$ fraction of trapdoors, for `n` any bound on the
handle-set size (`n = fuel + D + 4` at the SRS seeding), under the handle-degree invariant
$\le \Delta$. This is Shoup's $(q+d)^2 \Delta / p$ shape [Sho97] with the global bad event.

The pieces reused from `GgmAdaptive` / `GgmCandidate` (not reproved): `realWinSet_subset`
(identical-until-bad at the set level), `card_winningPoints_le` (the static Boneh–Boyen root event
[BB04], behind which sit `winPoly_ne_zero`, `winPoly_natDegree_le`, `card_roots_winPoly_le`),
`badSet`/`badPolys`/`symPairs`, `adaptiveExperiment`. New here: the all-pairs union lemma, the
structural table lemmas, and the composition.

## References

* [Boneh, D., and Boyen, X., *Short Signatures Without Random Oracles*][BB04]
* [Shoup, V., *Lower Bounds for Discrete Logarithms and Related Problems*][Sho97]
* [Schwartz, J. T., *Fast Probabilistic Algorithms for Verification of Polynomial
    Identities*][Sch80]
* [Zippel, R., *Probabilistic Algorithms for Sparse Polynomials*][Zip79]
-/

open Polynomial

namespace GgmRandomEncoding

open GgmCandidate GgmAdaptive

variable {p : ℕ} [Fact (Nat.Prime p)]

/-! ## § PairUnion — the all-pairs root-union bound

The union, over all unordered pairs of distinct polynomials from a finite set, of the roots of the
pair's difference. Counting through `Sym2` pays `C(n,2)` — the ordered `offDiag` index would pay
`n(n−1)`, double, because `roots (q₁ − q₂)` and `roots (q₂ − q₁)` coincide as sets. -/

/-- The union of `roots (q₁ − q₂)` over all ordered pairs `q₁ ≠ q₂` of `ps` — which equals the
union over unordered pairs, since the two orders of a pair contribute the same root set. -/
noncomputable def pairRootUnion (ps : Finset ((ZMod p)[X])) : Finset (ZMod p) :=
  ps.offDiag.biUnion fun q => (q.1 - q.2).roots.toFinset

/-- Membership characterization of `pairRootUnion`: exactly the τ that are a root of the
difference of SOME pair of distinct polynomials from `ps`. -/
theorem mem_pairRootUnion {ps : Finset ((ZMod p)[X])} {τ : ZMod p} :
    τ ∈ pairRootUnion ps ↔
      ∃ q₁ q₂, q₁ ∈ ps ∧ q₂ ∈ ps ∧ q₁ ≠ q₂ ∧ τ ∈ (q₁ - q₂).roots.toFinset := by
  unfold pairRootUnion
  constructor
  · intro h
    obtain ⟨q, hq, hτ⟩ := Finset.mem_biUnion.mp h
    obtain ⟨h1, h2, hne⟩ := Finset.mem_offDiag.mp hq
    exact ⟨q.1, q.2, h1, h2, hne, hτ⟩
  · rintro ⟨q₁, q₂, h1, h2, hne, hτ⟩
    exact Finset.mem_biUnion.mpr ⟨(q₁, q₂), Finset.mem_offDiag.mpr ⟨h1, h2, hne⟩, hτ⟩

/-- The root set of the difference of an UNORDERED pair of polynomials — well-defined on `Sym2`
because `a − b` and `b − a` have the same roots (`a−b ≠ 0 ↔ b−a ≠ 0`, and the evaluations vanish
together). -/
noncomputable def sym2DiffRoots : Sym2 ((ZMod p)[X]) → Finset (ZMod p) :=
  Sym2.lift ⟨fun a b => (a - b).roots.toFinset, by
    intro a b
    ext τ
    simp only [Multiset.mem_toFinset, mem_roots', ne_eq, IsRoot.def, eval_sub, sub_eq_zero]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨fun e => h1 e.symm, h2.symm⟩
    · rintro ⟨h1, h2⟩
      exact ⟨fun e => h1 e.symm, h2.symm⟩⟩

/-- `sym2DiffRoots` on a constructed pair is the difference's root set. -/
lemma sym2DiffRoots_mk (a b : (ZMod p)[X]) :
    sym2DiffRoots s(a, b) = (a - b).roots.toFinset := rfl

/-- **ALL-PAIRS UNION SCHWARTZ–ZIPPEL.** If every polynomial in `ps` has degree ≤ Δ, the union of
the root sets of all pairwise differences has card ≤ `C(#ps, 2) · Δ`. The count is over UNORDERED
pairs (`Sym2.card_image_offDiag`); the degree of each difference is bounded by the MAX of the two
degrees (`natDegree_sub_le`), so a family of degree-≤Δ handles pays Δ per pair — never 2Δ. -/
theorem card_pairRootUnion_le {ps : Finset ((ZMod p)[X])} {Δ : ℕ}
    (hdeg : ∀ q ∈ ps, q.natDegree ≤ Δ) :
    (pairRootUnion ps).card ≤ ps.card.choose 2 * Δ := by
  classical
  -- Re-index the ordered `offDiag` union through unordered pairs: same union, `C(n,2)` indices.
  have hrw : pairRootUnion ps = (ps.offDiag.image Sym2.mk.uncurry).biUnion sym2DiffRoots := by
    unfold pairRootUnion
    rw [Finset.image_biUnion]
    refine Finset.biUnion_congr rfl fun q _ => ?_
    obtain ⟨a, b⟩ := q
    exact (sym2DiffRoots_mk a b).symm
  rw [hrw]
  refine Finset.card_biUnion_le.trans ?_
  calc ∑ s ∈ ps.offDiag.image Sym2.mk.uncurry, (sym2DiffRoots s).card
      ≤ ∑ _s ∈ ps.offDiag.image Sym2.mk.uncurry, Δ := by
        refine Finset.sum_le_sum fun s hs => ?_
        obtain ⟨⟨a, b⟩, hab, rfl⟩ := Finset.mem_image.mp hs
        obtain ⟨ha, hb, -⟩ := Finset.mem_offDiag.mp hab
        show ((a - b).roots.toFinset).card ≤ Δ
        refine (Multiset.toFinset_card_le _).trans ((card_roots' _).trans ?_)
        exact (natDegree_sub_le a b).trans (max_le (hdeg a ha) (hdeg b hb))
    _ = (ps.offDiag.image Sym2.mk.uncurry).card * Δ := by rw [Finset.sum_const, smul_eq_mul]
    _ = ps.card.choose 2 * Δ := by rw [Sym2.card_image_offDiag]

/-- The δ = 2D specialization: a set of degree-≤2D handle polynomials has all-pairs collision set of
card ≤ `C(n,2) · 2D`. Feeds the off-path conservative chain (PAPER §9.2). -/
theorem card_pairRootUnion_le_two_mul {ps : Finset ((ZMod p)[X])} {D : ℕ}
    (hdeg : ∀ q ∈ ps, q.natDegree ≤ 2 * D) :
    (pairRootUnion ps).card ≤ ps.card.choose 2 * (2 * D) :=
  card_pairRootUnion_le hdeg

/-! ## § Table — the run's handle table, structurally

`runTable` mirrors `runAux`'s recursion on the table component and returns the FINAL handle table.
Three facts, each by induction on fuel: the initial table is a prefix of the final one; every
polynomial behind a queried handle is in the final table or is `0` (the out-of-range `getD`
default — the group identity's polynomial); and the final table grows by at most one entry per
fuel step. -/

/-- The final handle table of a run (the table component of `runAux`'s final state). -/
noncomputable def runTable (ans : AnswerFn p) (strat : Strat p) :
    ℕ → St p → List ((ZMod p)[X])
  | 0, st => st.table
  | fuel + 1, st =>
    match strat st.hist with
    | Sum.inr _ => st.table
    | Sum.inl (Move.lin spec) =>
        runTable ans strat fuel ⟨st.table ++ [combine spec st.table], st.hist⟩
    | Sum.inl (Move.query i j) =>
        runTable ans strat fuel
          ⟨st.table, st.hist ++ [ans (st.table.getD i 0) (st.table.getD j 0)]⟩

/-- The table only ever grows: the current table is a prefix of the final one. -/
theorem table_prefix_runTable (ans : AnswerFn p) (strat : Strat p) :
    ∀ (fuel : ℕ) (st : St p), st.table <+: runTable ans strat fuel st := by
  intro fuel
  induction fuel with
  | zero => intro st; simp only [runTable]; exact List.prefix_rfl
  | succ fuel ih =>
    intro st
    rcases hdec : strat st.hist with m | out
    · cases m with
      | lin spec =>
        have e : runTable ans strat (fuel + 1) st
            = runTable ans strat fuel ⟨st.table ++ [combine spec st.table], st.hist⟩ := by
          simp only [runTable, hdec]
        rw [e]
        exact (List.prefix_append _ _).trans (ih ⟨st.table ++ [combine spec st.table], st.hist⟩)
      | query i j =>
        have e : runTable ans strat (fuel + 1) st
            = runTable ans strat fuel
                ⟨st.table, st.hist ++ [ans (st.table.getD i 0) (st.table.getD j 0)]⟩ := by
          simp only [runTable, hdec]
        rw [e]
        exact ih ⟨st.table, st.hist ++ [ans (st.table.getD i 0) (st.table.getD j 0)]⟩
    · have e : runTable ans strat (fuel + 1) st = st.table := by
        simp only [runTable, hdec]
      rw [e]

/-- Each fuel step appends at most one handle: the final table has length ≤ initial + fuel. -/
theorem runTable_length_le (ans : AnswerFn p) (strat : Strat p) :
    ∀ (fuel : ℕ) (st : St p),
      (runTable ans strat fuel st).length ≤ st.table.length + fuel := by
  intro fuel
  induction fuel with
  | zero => intro st; simp only [runTable]; omega
  | succ fuel ih =>
    intro st
    rcases hdec : strat st.hist with m | out
    · cases m with
      | lin spec =>
        have e : runTable ans strat (fuel + 1) st
            = runTable ans strat fuel ⟨st.table ++ [combine spec st.table], st.hist⟩ := by
          simp only [runTable, hdec]
        rw [e]
        have := ih ⟨st.table ++ [combine spec st.table], st.hist⟩
        simp only [List.length_append, List.length_cons, List.length_nil] at this
        omega
      | query i j =>
        have e : runTable ans strat (fuel + 1) st
            = runTable ans strat fuel
                ⟨st.table, st.hist ++ [ans (st.table.getD i 0) (st.table.getD j 0)]⟩ := by
          simp only [runTable, hdec]
        rw [e]
        have := ih ⟨st.table, st.hist ++ [ans (st.table.getD i 0) (st.table.getD j 0)]⟩
        simp only at this
        omega
    · have e : runTable ans strat (fuel + 1) st = st.table := by
        simp only [runTable, hdec]
      rw [e]
      omega

/-- A defaulted list lookup is either a genuine element or the default. -/
lemma getD_mem_or_eq_zero (l : List ((ZMod p)[X])) (i : ℕ) :
    l.getD i 0 ∈ l ∨ l.getD i 0 = (0 : (ZMod p)[X]) := by
  rw [List.getD_eq_getElem?_getD]
  cases h : l[i]? with
  | none => right; rfl
  | some a =>
    left
    have ha := List.mem_of_getElem? h
    simpa using ha

/-- **Every queried handle polynomial is in the final table (or is `0`).** By induction on fuel:
a query's two components are defaulted lookups into the CURRENT table, which is a prefix of the
final one; the tail pairs come from the recursive run over the same final table. -/
theorem runAux_pairs_mem_runTable (ans : AnswerFn p) (strat : Strat p) :
    ∀ (fuel : ℕ) (st : St p), ∀ ab ∈ (runAux ans strat fuel st).2,
      (ab.1 ∈ runTable ans strat fuel st ∨ ab.1 = 0) ∧
        (ab.2 ∈ runTable ans strat fuel st ∨ ab.2 = 0) := by
  intro fuel
  induction fuel with
  | zero => intro st ab hab; simp [runAux] at hab
  | succ fuel ih =>
    intro st ab hab
    rcases hdec : strat st.hist with m | out
    · cases m with
      | lin spec =>
        have e : runAux ans strat (fuel + 1) st
            = runAux ans strat fuel ⟨st.table ++ [combine spec st.table], st.hist⟩ := by
          simp only [runAux, hdec]
        have eT : runTable ans strat (fuel + 1) st
            = runTable ans strat fuel ⟨st.table ++ [combine spec st.table], st.hist⟩ := by
          simp only [runTable, hdec]
        rw [e] at hab
        rw [eT]
        exact ih ⟨st.table ++ [combine spec st.table], st.hist⟩ ab hab
      | query i j =>
        have e : runAux ans strat (fuel + 1) st
            = ((runAux ans strat fuel
                  ⟨st.table, st.hist ++ [ans (st.table.getD i 0) (st.table.getD j 0)]⟩).1,
                (st.table.getD i 0, st.table.getD j 0) ::
                  (runAux ans strat fuel
                    ⟨st.table, st.hist ++ [ans (st.table.getD i 0) (st.table.getD j 0)]⟩).2) := by
          simp only [runAux, hdec]
        have eT : runTable ans strat (fuel + 1) st
            = runTable ans strat fuel
                ⟨st.table, st.hist ++ [ans (st.table.getD i 0) (st.table.getD j 0)]⟩ := by
          simp only [runTable, hdec]
        rw [e] at hab
        rw [eT]
        -- the recursive state: same table, extended history
        set st' : St p :=
          ⟨st.table, st.hist ++ [ans (st.table.getD i 0) (st.table.getD j 0)]⟩ with hst'
        rcases List.mem_cons.mp hab with hhd | htl
        · -- the head pair: current-table lookups; current table is a prefix of the final one.
          have hpre : st.table ⊆ runTable ans strat fuel st' :=
            (table_prefix_runTable ans strat fuel st').subset
          constructor
          · rcases getD_mem_or_eq_zero st.table i with h | h
            · left; rw [hhd]; exact hpre h
            · right; rw [hhd]; exact h
          · rcases getD_mem_or_eq_zero st.table j with h | h
            · left; rw [hhd]; exact hpre h
            · right; rw [hhd]; exact h
        · exact ih st' ab htl
    · have e : runAux ans strat (fuel + 1) st = ((out.1, st.table.getD out.2 0), []) := by
        simp only [runAux, hdec]
      rw [e] at hab
      simp at hab

/-- The finite set of handle polynomials a run can ever compare: the final table plus the zero
polynomial (the identity handle backing out-of-range lookups). -/
noncomputable def handlePolys (ans : AnswerFn p) (strat : Strat p) (fuel : ℕ) (st : St p) :
    Finset ((ZMod p)[X]) :=
  insert 0 (runTable ans strat fuel st).toFinset

/-- Membership in `handlePolys` from the disjunction `runAux_pairs_mem_runTable` produces. -/
lemma mem_handlePolys_of {ans : AnswerFn p} {strat : Strat p} {fuel : ℕ} {st : St p}
    {f : (ZMod p)[X]} (h : f ∈ runTable ans strat fuel st ∨ f = 0) :
    f ∈ handlePolys ans strat fuel st := by
  unfold handlePolys
  rcases h with h | h
  · exact Finset.mem_insert_of_mem (List.mem_toFinset.mpr h)
  · rw [h]; exact Finset.mem_insert_self _ _

/-- **The table-size bound, a THEOREM.** The handle set has card ≤ (seed count) + fuel + 1:
one appended handle per fuel step, plus the zero/identity handle. -/
theorem card_handlePolys_le (ans : AnswerFn p) (strat : Strat p) (fuel : ℕ) (st : St p) :
    (handlePolys ans strat fuel st).card ≤ st.table.length + fuel + 1 := by
  refine (Finset.card_insert_le _ _).trans ?_
  have h := (List.toFinset_card_le (runTable ans strat fuel st)).trans
    (runTable_length_le ans strat fuel st)
  omega

/-! ## § Bound — the all-pairs adaptive bound at δ = 2D (OFF-PATH specialization)

The Shoup bad set of the adaptive file collects roots of differences of QUERIED pairs; every
queried pair lives in `handlePolys`, so the bad set is inside the all-pairs collision set of the
handle table — a conservative global collision event. Composing with the reused
`realWinSet_subset` and the reused static bound `card_winningPoints_le` gives
`C(n,2)·2D + (D+1)` winning trapdoors.

This δ = 2D chain is a specialization of the general degree bound for the same linear `runAux`
semantics. It does not add a pairing move. ArkLib's `tSdhAdversary` is granted no pairing map, so
the critical-path bound is the δ = D sibling below. -/

/-- The per-query bad set is contained in the all-pairs collision set of the handle table. -/
theorem badSet_subset_pairRootUnion (strat : Strat p) (st₀ : St p) (fuel : ℕ) :
    badSet strat st₀ fuel ⊆ pairRootUnion (handlePolys symAns strat fuel st₀) := by
  intro τ hτ
  unfold badSet rootUnion at hτ
  obtain ⟨q, hq, hroot⟩ := Finset.mem_biUnion.mp hτ
  unfold badPolys at hq
  rw [List.mem_toFinset, List.mem_map] at hq
  obtain ⟨ab, habf, rfl⟩ := hq
  rw [List.mem_filter] at habf
  obtain ⟨hab, hne'⟩ := habf
  have hne : ab.1 ≠ ab.2 := of_decide_eq_true hne'
  have hab' : ab ∈ (runAux symAns strat fuel st₀).2 := hab
  have hmem := runAux_pairs_mem_runTable symAns strat fuel st₀ ab hab'
  exact mem_pairRootUnion.mpr
    ⟨ab.1, ab.2, mem_handlePolys_of hmem.1, mem_handlePolys_of hmem.2, hne, hroot⟩

/-- **The all-pairs counting bound.** Assuming every handle polynomial in the linear run has
degree ≤ 2D and the output-degree
invariant, the adaptive adversary wins on ≤ `C(#handles, 2)·2D + (D+1)` trapdoors.
Reuses `realWinSet_subset` and `card_winningPoints_le`; only the bad-set half is new. -/
theorem card_realWinSet_le_allPairs (strat : Strat p) (st₀ : St p) (fuel : ℕ) (D : ℕ)
    (hdeg_out : (symOutput strat st₀ fuel).2.natDegree ≤ D)
    (hdeg_handles : ∀ q ∈ handlePolys symAns strat fuel st₀, q.natDegree ≤ 2 * D) :
    (realWinSet strat st₀ fuel).card ≤
      (handlePolys symAns strat fuel st₀).card.choose 2 * (2 * D) + (D + 1) := by
  classical
  refine (Finset.card_le_card (realWinSet_subset strat st₀ fuel D hdeg_out)).trans ?_
  refine (Finset.card_union_le _ _).trans ?_
  have hbad : (badSet strat st₀ fuel).card ≤
      (handlePolys symAns strat fuel st₀).card.choose 2 * (2 * D) :=
    (Finset.card_le_card (badSet_subset_pairRootUnion strat st₀ fuel)).trans
      (card_pairRootUnion_le_two_mul hdeg_handles)
  exact Nat.add_le_add hbad (card_winningPoints_le _)

/-- The counting bound at an abstract table-size bound `n`: any `n ≥ (seed count) + fuel + 1`
works, by monotonicity of `C(·, 2)`. -/
theorem card_realWinSet_le_encoding (strat : Strat p) (st₀ : St p) (fuel : ℕ) (D n : ℕ)
    (hdeg_out : (symOutput strat st₀ fuel).2.natDegree ≤ D)
    (hdeg_handles : ∀ q ∈ handlePolys symAns strat fuel st₀, q.natDegree ≤ 2 * D)
    (hn : st₀.table.length + fuel + 1 ≤ n) :
    (realWinSet strat st₀ fuel).card ≤ n.choose 2 * (2 * D) + (D + 1) := by
  refine (card_realWinSet_le_allPairs strat st₀ fuel D hdeg_out hdeg_handles).trans ?_
  have hcard : (handlePolys symAns strat fuel st₀).card ≤ n :=
    (card_handlePolys_le symAns strat fuel st₀).trans hn
  exact Nat.add_le_add_right (Nat.mul_le_mul_right _ (Nat.choose_le_choose 2 hcard)) _

/-- **THE ALL-PAIRS SECURITY BOUND at δ = 2D (sorry-free; OFF-PATH specialization).**
Every deterministic strategy in the explicit-query model whose handle table stays within `n`
polynomials (a THEOREM at
`n = seeds + fuel + 1`, `card_handlePolys_le`) wins on at most a
`(C(n,2)·2D + (D+1))/(p−1)` fraction
of trapdoors — the global all-pairs collision event plus the static root event. This theorem assumes
the `≤ 2D` invariant; it does not provide pairing-capable semantics. -/
theorem rand_encoding_bound (strat : Strat p) (st₀ : St p) (fuel : ℕ) (D n : ℕ) (hp : 2 ≤ p)
    (hdeg_out : (symOutput strat st₀ fuel).2.natDegree ≤ D)
    (hdeg_handles : ∀ q ∈ handlePolys symAns strat fuel st₀, q.natDegree ≤ 2 * D)
    (hn : st₀.table.length + fuel + 1 ≤ n) :
    adaptiveExperiment strat st₀ fuel ≤
      ((n.choose 2 * (2 * D) + (D + 1) : ℕ) : ℚ) / (p - 1) := by
  unfold adaptiveExperiment
  have hnum : ((realWinSet strat st₀ fuel).card : ℚ)
      ≤ ((n.choose 2 * (2 * D) + (D + 1) : ℕ) : ℚ) := by
    exact_mod_cast card_realWinSet_le_encoding strat st₀ fuel D n hdeg_out hdeg_handles hn
  have hden : (0 : ℚ) < (p : ℚ) - 1 := by
    have : (2 : ℚ) ≤ (p : ℚ) := by exact_mod_cast hp
    linarith
  gcongr

omit [Fact (Nat.Prime p)] in
/-- **Strictness of the all-pairs bound.** Whenever `C(n,2)·2D + (D+1) < p − 1` the bound
is a genuine rational `< 1`: at cryptographic parameters (`p ≈ 2²⁵⁴`, `D ≈ 2²⁰`, `n ≈ 2⁶⁰`)
`C(n,2)·2D ≈ 2¹⁴⁰ ≪ p`, so the bound is `≈ 2⁻¹¹⁴`. -/
theorem rand_encoding_bound_lt_one (D n : ℕ)
    (hlt : n.choose 2 * (2 * D) + (D + 1) < p - 1) (hp : 2 ≤ p) :
    ((n.choose 2 * (2 * D) + (D + 1) : ℕ) : ℚ) / (p - 1) < 1 := by
  have hden : (0 : ℚ) < (p : ℚ) - 1 := by
    have : (2 : ℚ) ≤ (p : ℚ) := by exact_mod_cast hp
    linarith
  rw [div_lt_one hden]
  have h1 : ((n.choose 2 * (2 * D) + (D + 1) : ℕ) : ℚ) < ((p - 1 : ℕ) : ℚ) := by
    exact_mod_cast hlt
  have h2 : ((p - 1 : ℕ) : ℚ) = (p : ℚ) - 1 := by
    have : (1 : ℕ) ≤ p := by omega
    push_cast [Nat.cast_sub this]; ring
  rw [h2] at h1; exact h1

/-! ## § SRS — the seeded instantiation, `n = fuel + D + 4`

The adaptive file's SRS seeding: G₁ handles `1, X, …, X^D` (D+1 polynomials), G₂ handles `1, X`
(2 polynomials) — seed count D+3. With the zero/identity handle, the handle set has card
≤ fuel + D + 4, so the concrete numerator is `C(fuel + D + 4, 2)·2D + (D+1)`. -/

/-- The SRS-seeded initial state: table `1, X, …, X^D, 1, X`, empty history. -/
noncomputable def srsSt (D : ℕ) : St p :=
  ⟨((List.range (D + 1)).map fun i => (X : (ZMod p)[X]) ^ i) ++ [1, X], []⟩

/-- The SRS seed count: `(D+1) + 2 = D + 3` handles. -/
theorem srsSt_table_length (D : ℕ) : (srsSt (p := p) D).table.length = D + 3 := by
  simp only [srsSt, List.length_append, List.length_map, List.length_range,
    List.length_cons, List.length_nil]

/-- **The strengthened bound at the SRS seeding**: table size `n = fuel + D + 4` (the D+3 SRS
seeds, one appended handle per fuel step, and the zero/identity handle), giving the concrete
`(C(fuel+D+4, 2)·2D + (D+1))/(p−1)` — the `(q+d)²·δ/p` Shoup shape for t-SDH. -/
theorem rand_encoding_bound_srs (strat : Strat p) (fuel : ℕ) (D : ℕ) (hp : 2 ≤ p)
    (hdeg_out : (symOutput strat (srsSt D) fuel).2.natDegree ≤ D)
    (hdeg_handles : ∀ q ∈ handlePolys symAns strat fuel (srsSt D), q.natDegree ≤ 2 * D) :
    adaptiveExperiment strat (srsSt D) fuel ≤
      (((fuel + D + 4).choose 2 * (2 * D) + (D + 1) : ℕ) : ℚ) / (p - 1) := by
  refine rand_encoding_bound strat (srsSt D) fuel D (fuel + D + 4) hp hdeg_out hdeg_handles ?_
  rw [srsSt_table_length]
  omega

/-! ## § Bound at δ = D — the linear-oracle instantiation (THE ARKLIB CRITICAL PATH)

This is the chain the end-to-end capstone consumes. The embedded adversary receives
`Vector G₁ (D+1) × Vector G₂ 2`, must output a `G₁` element, and is granted **no pairing map**
`e : G₁ × G₂ → Gₜ`. So — matching `GgmAdaptive`'s pairing-free `Move` — every handle it can form
is a `ZMod p`-linear combination of the seed `{1, X, …, X^D}`, degree ≤ D (never a product). The
honest collision degree is therefore **δ = D**, not 2D: a difference of two degree-≤D handles has
degree ≤ D (`natDegree_sub_le` — the max, not the sum). This section re-parametrizes the
*general-Δ* `card_pairRootUnion_le` at Δ = D. It is the exact `~(q+D)²·D/p` Shoup socket the
end-to-end theorem consumes (`rand_encoding_bound_srs_D` → `GgmDegreeDischarge` →
`GgmEndToEnd.tSdh_ggm_sound`), with the handle-degree invariant DISCHARGED there, not assumed. The
δ = 2D chain above is only the off-path
degree specialization. -/

/-- The δ = D instance of the all-pairs root-union bound: a set of degree-≤D handle polynomials has
all-pairs collision set of card ≤ `C(n,2) · D`. Direct from the general-Δ
`card_pairRootUnion_le`. -/
theorem card_pairRootUnion_le_D {ps : Finset ((ZMod p)[X])} {D : ℕ}
    (hdeg : ∀ q ∈ ps, q.natDegree ≤ D) :
    (pairRootUnion ps).card ≤ ps.card.choose 2 * D :=
  card_pairRootUnion_le hdeg

/-- **The all-pairs counting bound at δ = D.** Under the linear-oracle degree invariant (every
handle polynomial has degree ≤ D — no pairing, so no product term) and the output-degree invariant,
the adaptive adversary wins on ≤ `C(#handles, 2)·D + (D + 1)` trapdoors. δ = D sibling of
`card_realWinSet_le_allPairs`. -/
theorem card_realWinSet_le_allPairs_D (strat : Strat p) (st₀ : St p) (fuel : ℕ) (D : ℕ)
    (hdeg_out : (symOutput strat st₀ fuel).2.natDegree ≤ D)
    (hdeg_handles : ∀ q ∈ handlePolys symAns strat fuel st₀, q.natDegree ≤ D) :
    (realWinSet strat st₀ fuel).card ≤
      (handlePolys symAns strat fuel st₀).card.choose 2 * D + (D + 1) := by
  classical
  refine (Finset.card_le_card (realWinSet_subset strat st₀ fuel D hdeg_out)).trans ?_
  refine (Finset.card_union_le _ _).trans ?_
  have hbad : (badSet strat st₀ fuel).card ≤
      (handlePolys symAns strat fuel st₀).card.choose 2 * D :=
    (Finset.card_le_card (badSet_subset_pairRootUnion strat st₀ fuel)).trans
      (card_pairRootUnion_le_D hdeg_handles)
  exact Nat.add_le_add hbad (card_winningPoints_le _)

/-- The δ = D counting bound at an abstract table-size bound `n`. δ = D sibling of
`card_realWinSet_le_encoding`. -/
theorem card_realWinSet_le_encoding_D (strat : Strat p) (st₀ : St p) (fuel : ℕ) (D n : ℕ)
    (hdeg_out : (symOutput strat st₀ fuel).2.natDegree ≤ D)
    (hdeg_handles : ∀ q ∈ handlePolys symAns strat fuel st₀, q.natDegree ≤ D)
    (hn : st₀.table.length + fuel + 1 ≤ n) :
    (realWinSet strat st₀ fuel).card ≤ n.choose 2 * D + (D + 1) := by
  refine (card_realWinSet_le_allPairs_D strat st₀ fuel D hdeg_out hdeg_handles).trans ?_
  have hcard : (handlePolys symAns strat fuel st₀).card ≤ n :=
    (card_handlePolys_le symAns strat fuel st₀).trans hn
  exact Nat.add_le_add_right (Nat.mul_le_mul_right _ (Nat.choose_le_choose 2 hcard)) _

/-- **THE ALL-PAIRS GGM SECURITY BOUND AT δ = D (sorry-free; THE ARKLIB CRITICAL PATH).**
Every adaptive generic t-SDH adversary in the linear (pairing-free) oracle model whose handle table
stays within `n` polynomials wins on at most a `(C(n,2)·D + (D + 1))/(p − 1)` fraction of
trapdoors — the exact `~(q+D)²·D/p` Shoup socket for ArkLib's `tSdhExperiment`, whose adversary
cannot pair. This is the bound the end-to-end capstone consumes (via `GgmDegreeDischarge`); the
δ = 2D `rand_encoding_bound` is the off-path `≤ 2D` specialization. -/
theorem rand_encoding_bound_D (strat : Strat p) (st₀ : St p) (fuel : ℕ) (D n : ℕ) (hp : 2 ≤ p)
    (hdeg_out : (symOutput strat st₀ fuel).2.natDegree ≤ D)
    (hdeg_handles : ∀ q ∈ handlePolys symAns strat fuel st₀, q.natDegree ≤ D)
    (hn : st₀.table.length + fuel + 1 ≤ n) :
    adaptiveExperiment strat st₀ fuel ≤
      ((n.choose 2 * D + (D + 1) : ℕ) : ℚ) / (p - 1) := by
  unfold adaptiveExperiment
  have hnum : ((realWinSet strat st₀ fuel).card : ℚ)
      ≤ ((n.choose 2 * D + (D + 1) : ℕ) : ℚ) := by
    exact_mod_cast card_realWinSet_le_encoding_D strat st₀ fuel D n hdeg_out hdeg_handles hn
  have hden : (0 : ℚ) < (p : ℚ) - 1 := by
    have : (2 : ℚ) ≤ (p : ℚ) := by exact_mod_cast hp
    linarith
  gcongr

/-- **The δ = D bound at the SRS seeding**: table size `n = fuel + D + 4`, giving the concrete
`(C(fuel+D+4, 2)·D + (D + 1))/(p − 1)`. δ = D sibling of `rand_encoding_bound_srs`. -/
theorem rand_encoding_bound_srs_D (strat : Strat p) (fuel : ℕ) (D : ℕ) (hp : 2 ≤ p)
    (hdeg_out : (symOutput strat (srsSt D) fuel).2.natDegree ≤ D)
    (hdeg_handles : ∀ q ∈ handlePolys symAns strat fuel (srsSt D), q.natDegree ≤ D) :
    adaptiveExperiment strat (srsSt D) fuel ≤
      (((fuel + D + 4).choose 2 * D + (D + 1) : ℕ) : ℚ) / (p - 1) := by
  refine rand_encoding_bound_D strat (srsSt D) fuel D (fuel + D + 4) hp hdeg_out hdeg_handles ?_
  rw [srsSt_table_length]
  omega

end GgmRandomEncoding

-- Axiom receipts: every headline theorem is sorry-free on the standard three axioms.
#print axioms GgmRandomEncoding.card_pairRootUnion_le
#print axioms GgmRandomEncoding.card_pairRootUnion_le_two_mul
#print axioms GgmRandomEncoding.runAux_pairs_mem_runTable
#print axioms GgmRandomEncoding.card_handlePolys_le
#print axioms GgmRandomEncoding.badSet_subset_pairRootUnion
#print axioms GgmRandomEncoding.card_realWinSet_le_allPairs
#print axioms GgmRandomEncoding.card_realWinSet_le_encoding
#print axioms GgmRandomEncoding.rand_encoding_bound
#print axioms GgmRandomEncoding.rand_encoding_bound_lt_one
#print axioms GgmRandomEncoding.rand_encoding_bound_srs
#print axioms GgmRandomEncoding.card_pairRootUnion_le_D
#print axioms GgmRandomEncoding.card_realWinSet_le_allPairs_D
#print axioms GgmRandomEncoding.card_realWinSet_le_encoding_D
#print axioms GgmRandomEncoding.rand_encoding_bound_D
#print axioms GgmRandomEncoding.rand_encoding_bound_srs_D

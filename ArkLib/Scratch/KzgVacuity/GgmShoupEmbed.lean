/-
Copyright (c) 2026 Ember Arlynx. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ember Arlynx
-/
import ArkLib.Scratch.KzgVacuity.GgmShoup
import ArkLib.Scratch.KzgVacuity.GgmEndToEnd

/-!
# The random-encoding (Shoup) GGM capstone for ArkLib's t-SDH experiment

This file wires the random-encoding (Shoup) free-comparison strategy model
(`GgmShoup.ShoupStrat` / `runShoup`) into ArkLib's real `tSdhAdversary` /
`tSdhExperiment`, exactly as the Maurer explicit-equality track is wired via
`GgmEmbed.embed`. With both tracks in place, the two standard GGM formulations
bound ArkLib's actual $t$-SDH experiment; the Shoup track is no longer
standalone. The headline theorem is `shoup_tSdh_ggm_sound` (with its genuine
`< 1` corollary `shoup_tSdh_ggm_sound_lt_one`): for every free-comparison
strategy it bounds the winning probability of the embedded adversary
`embedShoup strat` against the real experiment, composed through one socket
exactly as the Maurer capstone `tSdh_ggm_sound`, via an `embedShoup` into
ArkLib's adversary type.

## Faithfulness — free comparison realized in the concrete group

The strategy model is the Shoup random-encoding one [Sho97], in which equality
of handles is observed for free. A real `tSdhAdversary` holds actual $G_1$
elements and can test equality of any two it holds for free (`DecidableEq G₁`,
classically). In a prime-order group the exponent encoding $a \mapsto
g_1^{a.\mathrm{val}}$ is injective (`GgmArkLibTransport.gpow_val_inj_iff`), so
real group equality of two realized handles
$g_1^{(f\,\tau).\mathrm{val}} =? g_1^{(h\,\tau).\mathrm{val}}$ equals eval-at-$\tau$
equality $f.\mathrm{eval}\,\tau =? h.\mathrm{eval}\,\tau$, i.e.
`GgmAdaptive.realAns τ`. Therefore the full pairwise-equality matrix of the
adversary's realized handles equals the symbolic `GgmShoup.eqPattern (realAns τ)`
— the free-comparison observation the strategy branches on. The injective
encoding genuinely realizes `eqPattern` off the bad event; free comparison is
not assumed, it is discharged by injectivity (`groupEqPattern_eq`).

## The construction (matrix-valued analogue of `GgmEmbed`)

* `groupEqPattern tableG` — the $|tableG| \times |tableG|$ real-group equality
  matrix (the free-comparison observation a `tSdhAdversary` computes at zero cost
  via `DecidableEq G₁`).
* `runEmbedAuxShoup` / `runEmbedShoup` / `embedShoup` — mirror `runEmbedAux` /
  `runEmbed` / `embed` but thread the matrix pattern-history
  (`GgmShoup.ShoupStrat`'s input), interpreting `lin` by real group products
  (`GgmEmbed.combineG`) and observing `groupEqPattern` (no `query` move —
  equality is ambient, as in the Shoup model).
* `groupEqPattern_eq` (the crux, one dimension richer than `GgmEmbed`'s
  single-bool `hans`) — under the table↔polynomial invariant `IsEncoding`, the
  group matrix equals `eqPattern (realAns τ)`, entrywise via `gpow_val_inj_iff`.
* `embedShoup_run_correspondence` — `runEmbedShoup` on the real SRS reproduces
  `runShoup (realAns τ)` realized in the group ($g_1^{(output\,\tau).\mathrm{val}}$).
  Mirrors `GgmEmbed.embed_run_correspondence`, reusing `isEncoding_append` /
  `seedG_isEncoding`.

## The capstone

`shoup_tSdh_ggm_sound` composes exactly as the Maurer capstone `tSdh_ggm_sound`,
whose explicit-equality strategy model is Maurer's [Mau05]:

* `Ggm.ProbThreading.experiment_eq_count` (adversary-agnostic) collapses ArkLib's
  `tSdhExperiment` to a $\mathrm{Fin}\,(p-1)$ count, its determinism discharged by
  `embedShoup_det`;
* `winIndexShoup_card_le` (reindex $i \mapsto i+1$, transported by
  `GgmArkLibTransport.tSdhCondition_iff_field`) bounds that count by
  `GgmShoup.realWinSetShoup.card`;
* `GgmShoup.card_realWinSetShoup_le_encoding` (the all-pairs Schwartz–Zippel
  bound) bounds that by $\binom{fuel+D+4}{2} \cdot D + (D+1)$.

The RHS is byte-identical to `tSdh_ggm_sound`'s: both embedded classes realize
the same $g_1^{(f\,\tau)}$ outputs and the same $t$-SDH win set (the Boneh–Boyen
$t$-SDH problem [BB04]); the two models differ only in how comparison is priced.
The bound quantifies over the image of `embedShoup`, not the full `tSdhAdversary`
type (over which it is false).

## References

* [Boneh, D., and Boyen, X., *Short Signatures Without Random Oracles*][BB04]
* [Shoup, V., *Lower Bounds for Discrete Logarithms and Related Problems*][Sho97]
* [Maurer, U., *Abstract Models of Computation in Cryptography*][Mau05]
-/

open Polynomial Groups OracleSpec OracleComp
open scoped Classical NNReal ENNReal

namespace GgmShoupEmbed

open GgmCandidate GgmAdaptive GgmRandomEncoding GgmArkLibTransport GgmEmbed Ggm.ProbThreading
open GgmDegreeDischarge GgmShoup GgmEndToEnd

variable {p : ℕ} [Fact (Nat.Prime p)]
  [∀ i, SampleableType (unifSpec.Range i)]
  {G₁ : Type} [Group G₁] [PrimeOrderWith G₁ p] {g₁ : G₁}
  {G₂ : Type} [Group G₂] [PrimeOrderWith G₂ p] {g₂ : G₂}
  {D : ℕ}

/-! ## 0. Sigma-matrix extensionality — two equality matrices over lists of equal length agree. -/

omit [∀ i, SampleableType (unifSpec.Range i)] in
/-- Two `Σ n, Fin n → Fin n → Bool`-packaged matrices are equal when their dimensions are equal and
the matrices agree entrywise (through the dimension cast). The dimension mismatch is discharged by
`subst`, so no `HEq`/`Fin` bookkeeping leaks into the callers. -/
lemma sigma_matrix_ext {n m : ℕ} (h : n = m)
    {f : Fin n → Fin n → Bool} {g' : Fin m → Fin m → Bool}
    (hfg : ∀ (i j : Fin n), f i j = g' (Fin.cast h i) (Fin.cast h j)) :
    (⟨n, f⟩ : Σ k : ℕ, Fin k → Fin k → Bool) = ⟨m, g'⟩ := by
  subst h
  refine Sigma.ext rfl (heq_of_eq (funext fun i => funext fun j => ?_))
  simpa using hfg i j

/-! ## 1. The free-comparison observation in the real group, and its agreement with `eqPattern`.

`groupEqPattern` is the `|tableG|×|tableG|` real-group equality matrix — exactly what a concrete
`tSdhAdversary` observes for free via `DecidableEq G₁`. Under `GgmEmbed.IsEncoding`, injectivity of
the
encoding folds it onto the symbolic `eqPattern (realAns τ)`. This is the free-comparison analogue of
`GgmEmbed.runEmbedAux_correspondence`'s single-bool `hans`, one dimension richer. -/

/-- The real-group free-comparison observation: the full pairwise `groupEq` matrix of the handle
table, packaged with its dimension (mirrors `GgmShoup.eqPattern`, over group elements). -/
noncomputable def groupEqPattern (tableG : List G₁) : Σ n : ℕ, Fin n → Fin n → Bool :=
  ⟨tableG.length, fun i j => groupEq (tableG.get i) (tableG.get j)⟩

/-- **The free-comparison realization is FAITHFUL.** Under the table↔polynomial invariant, the
real-group equality matrix `groupEqPattern tableG` equals the symbolic eval-at-τ matrix
`eqPattern (realAns τ) table`: entrywise, real group equality of realized handles
`g^(fᵢ τ).val =? g^(fⱼ τ).val` folds to `fᵢ τ =? fⱼ τ` by injectivity (`gpow_val_inj_iff`). -/
lemma groupEqPattern_eq {g : G₁} (hord : orderOf g = p) {τ : ZMod p}
    {tableG : List G₁} {table : List ((ZMod p)[X])} (hInv : IsEncoding g τ tableG table) :
    groupEqPattern tableG = eqPattern (realAns τ) table := by
  obtain ⟨hlen, hpt⟩ := hInv
  unfold groupEqPattern eqPattern
  refine sigma_matrix_ext hlen ?_
  intro i j
  have key : ∀ k : Fin tableG.length,
      tableG.get k = g ^ ((table.get (Fin.cast hlen k)).eval τ).val := by
    intro k
    have hk := hpt (k : ℕ)
    rw [List.getD_eq_getElem tableG 1 k.isLt, List.getD_eq_getElem table 0 (hlen ▸ k.isLt)] at hk
    rw [List.get_eq_getElem, List.get_eq_getElem]
    simpa using hk
  simp only [groupEq, realAns]
  exact decide_eq_decide.mpr (by rw [key i, key j]; exact gpow_val_inj_iff hord)

/-! ## 2. `runEmbedShoup` — the matrix-threaded real-group run — and `embedShoup`. -/

/-- **The real-group Shoup run.** A `List G₁` handle table (no polynomials, no τ), evolved by
`strat`'s `lin` moves interpreted as REAL group products (`GgmEmbed.combineG`, REUSED). At every
step
it observes the FULL real-group equality matrix `groupEqPattern` for free — the random-encoding
free-comparison discipline — and appends it to the pattern-history the strategy branches on. There
is
no `query` branch (equality is ambient). Mirrors `GgmEmbed.runEmbedAux`, matrix-valued. -/
noncomputable def runEmbedAuxShoup (g : G₁) (strat : ShoupStrat p) :
    ℕ → (List G₁ × List (Σ n : ℕ, Fin n → Fin n → Bool)) → Option (ZMod p × G₁)
  | 0, _ => some (0, 1)
  | fuel + 1, (tableG, phist) =>
    match strat (phist ++ [groupEqPattern tableG]) with
    | Sum.inr (c, k) => some (c, tableG.getD k 1)
    | Sum.inl (ShoupMove.lin spec) =>
        runEmbedAuxShoup g strat fuel
          (tableG ++ [combineG spec tableG], phist ++ [groupEqPattern tableG])

/-- **`runEmbedShoup`** — run the free-comparison strategy against the real-group SRS. Reads only
the
G₁ tower (`srs.1`); being pairing-free it needs neither the G₂ generator nor τ. Mirrors
`GgmEmbed.runEmbed`. -/
noncomputable def runEmbedShoup (g₁ : G₁) (D fuel : ℕ) (strat : ShoupStrat p)
    (srs : Vector G₁ (D + 1) × Vector G₂ 2) : Option (ZMod p × G₁) :=
  runEmbedAuxShoup g₁ strat fuel (seedG srs.1.toList D, [])

/-- **`embedShoup : ShoupStrat p → tSdhAdversary D`** — the concrete adversary that realizes free
comparison. It holds real `G₁` elements and, at each step, computes the full `groupEqPattern` of
them
(free `DecidableEq G₁`), feeding the strategy the REAL equality matrix — which off the bad event IS
the symbolic `eqPattern (realAns τ)` (`groupEqPattern_eq`). Deterministic, empty-cache; its IMAGE is
the free-comparison adversary class `shoup_tSdh_ggm_sound` quantifies over. Mirrors
`GgmEmbed.embed`. -/
noncomputable def embedShoup (g₁ : G₁) (D fuel : ℕ) (strat : ShoupStrat p) :
    Groups.tSdhAdversary D (G₁ := G₁) (G₂ := G₂) (p := p) :=
  fun srs => pure (runEmbedShoup g₁ D fuel strat srs)

/-! ## 3. The correspondence: `runEmbedShoup` steps in lockstep with `runShoup (realAns τ)`. -/

/-- **THE CORRESPONDENCE (induction core).** Under the invariant, `runEmbedAuxShoup` on the group
table returns exactly the committed offset of `runShoup (realAns τ)` and the real-group encoding of
its committed output polynomial. The two runs step in lockstep because at each step the group's FREE
equality matrix equals the symbolic one (`groupEqPattern_eq`), so the strategy makes the same
decision. Mirrors `GgmEmbed.runEmbedAux_correspondence`, matrix-valued (and simpler — Shoup has no
query log to thread). -/
lemma runEmbedAuxShoup_correspondence {g : G₁} (hord : orderOf g = p) (τ : ZMod p)
    (strat : ShoupStrat p) :
    ∀ (fuel : ℕ) (tableG : List G₁) (table : List ((ZMod p)[X]))
      (phist : List (Σ n : ℕ, Fin n → Fin n → Bool)),
      IsEncoding g τ tableG table →
      runEmbedAuxShoup g strat fuel (tableG, phist)
        = some ((runShoup (realAns τ) strat fuel ⟨table, phist⟩).1,
                g ^ ((runShoup (realAns τ) strat fuel ⟨table, phist⟩).2.eval τ).val) := by
  intro fuel
  induction fuel with
  | zero =>
    intro tableG table phist hInv
    simp only [runEmbedAuxShoup, runShoup, eval_zero, encode_zero]
  | succ fuel ih =>
    intro tableG table phist hInv
    have hpat : groupEqPattern tableG = eqPattern (realAns τ) table := groupEqPattern_eq hord hInv
    rcases hdec : strat (phist ++ [eqPattern (realAns τ) table]) with m | out
    · cases m with
      | lin spec =>
        have eG : runEmbedAuxShoup g strat (fuel + 1) (tableG, phist)
            = runEmbedAuxShoup g strat fuel
                (tableG ++ [combineG spec tableG], phist ++ [eqPattern (realAns τ) table]) := by
          simp only [runEmbedAuxShoup, hpat, hdec]
        have eS : runShoup (realAns τ) strat (fuel + 1) ⟨table, phist⟩
            = runShoup (realAns τ) strat fuel
                ⟨table ++ [combine spec table], phist ++ [eqPattern (realAns τ) table]⟩ := by
          simp only [runShoup, hdec]
        rw [eG, eS]
        exact ih _ _ _ (isEncoding_append hord spec hInv)
    · have eG : runEmbedAuxShoup g strat (fuel + 1) (tableG, phist)
          = some (out.1, tableG.getD out.2 1) := by
        simp only [runEmbedAuxShoup, hpat, hdec]
      have eS : runShoup (realAns τ) strat (fuel + 1) ⟨table, phist⟩
          = (out.1, table.getD out.2 0) := by
        simp only [runShoup, hdec]
      rw [eG, eS, hInv.2 out.2]

omit [∀ i, SampleableType (unifSpec.Range i)] [PrimeOrderWith G₂ p] in
/-- **THE DELIVERABLE.** `runEmbedShoup` on the real SRS `PowerSrs.generate D τ` returns the
committed
offset of the SYMBOLIC free-comparison run `runShoup (realAns τ) strat fuel (srsStShoup D)` and the
real-group encoding `g₁ ^ (output.eval τ).val` of its committed output polynomial. This certifies
`embedShoup strat` is genuinely generic (it reproduces the symbolic Shoup run realized in the group,
never inverting the encoding), and is the socket the capstone consumes. Mirrors
`GgmEmbed.embed_run_correspondence`. -/
theorem embedShoup_run_correspondence (hord : orderOf g₁ = p)
    (D : ℕ) (hD : 1 ≤ D) (τ : ZMod p) (strat : ShoupStrat p) (fuel : ℕ) :
    runEmbedShoup g₁ D fuel strat (PowerSrs.generate (g₁ := g₁) (g₂ := g₂) D τ)
      = some ((runShoup (realAns τ) strat fuel (srsStShoup D)).1,
              g₁ ^ ((runShoup (realAns τ) strat fuel (srsStShoup D)).2.eval τ).val) := by
  have hsrs1 : (PowerSrs.generate (g₁ := g₁) (g₂ := g₂) D τ).1 = PowerSrs.tower g₁ τ D := rfl
  rw [runEmbedShoup, hsrs1,
    runEmbedAuxShoup_correspondence hord τ strat fuel
      (seedG (PowerSrs.tower g₁ τ D).toList D) (srsSt (p := p) D).table []
      (seedG_isEncoding g₁ hord τ D hD)]
  rfl

/-! ## 4. The deterministic output of `embedShoup`, and `embedShoup`'s determinism. -/

/-- The deterministic-given-τ `Option`-output of `embedShoup strat` on the SRS generated from `τ`:
the committed offset of the symbolic Shoup run realized in the group. This is the RHS of
`embedShoup_run_correspondence`, packaged as the `resultOf` that `experiment_eq_count` consumes.
Mirrors `GgmEndToEnd.stratResult`. -/
noncomputable def stratResultShoup (g₁ : G₁) (D fuel : ℕ) (strat : ShoupStrat p) :
    ZMod p → Option (ZMod p × G₁) :=
  fun τ => some ((runShoup (realAns τ) strat fuel (srsStShoup D)).1,
    g₁ ^ ((runShoup (realAns τ) strat fuel (srsStShoup D)).2.eval τ).val)

omit [∀ i, SampleableType (unifSpec.Range i)] [PrimeOrderWith G₂ p] in
/-- **`embedShoup strat` is deterministic-given-τ from the empty cache**, with output
`stratResultShoup`. `embedShoup strat srs = pure (runEmbedShoup … srs)`, and
`embedShoup_run_correspondence` identifies `runEmbedShoup …` on `PowerSrs.generate D τ` with
`stratResultShoup τ`. This is the exact `hdet` hypothesis of `experiment_eq_count`. Mirrors
`GgmEndToEnd.embed_det`. -/
theorem embedShoup_det (hord₁ : orderOf g₁ = p) (hD : 1 ≤ D) (strat : ShoupStrat p) (fuel : ℕ) :
    ∀ τ, (embedShoup g₁ D fuel strat
        (PowerSrs.generate (g₁ := g₁) (g₂ := g₂) D τ)).run' ∅
      = pure (stratResultShoup g₁ D fuel strat τ) := by
  intro τ
  simp only [embedShoup, StateT.run'_pure', stratResultShoup]
  rw [embedShoup_run_correspondence hord₁ D hD τ strat fuel]

/-! ## 5. The reindex `Fin (p−1) ↪ realWinSetShoup`: winning-index count ≤ winning-set card. -/

omit [∀ i, SampleableType (unifSpec.Range i)] in
/-- **The reindex bound.** The number of winning nonzero-trapdoor indices `i : Fin (p−1)` (those on
which `embedShoup strat`'s deterministic output `stratResultShoup` wins ArkLib's `tSdhCondition`) is
at most the cardinality of the field-level free-comparison winning set `realWinSetShoup`. Proved by
the injection `i ↦ (i+1 : ZMod p)` into `realWinSetShoup`, transporting each winning index through
`tSdhCondition_iff_field`. Mirrors `GgmEndToEnd.winIndex_card_le`, targeting `realWinSetShoup`. -/
theorem winIndexShoup_card_le (hord₁ : orderOf g₁ = p) (hp : 2 ≤ p)
    (strat : ShoupStrat p) (fuel : ℕ) :
    (Finset.univ.filter (winPred (stratResultShoup g₁ D fuel strat) g₁)).card
      ≤ (realWinSetShoup strat (srsStShoup D) fuel).card := by
  refine Finset.card_le_card_of_injOn (fun i => ((i : ℕ) + 1 : ZMod p)) ?_ ?_
  · -- maps winning indices into `realWinSetShoup`
    intro i hi
    rw [Finset.mem_coe, Finset.mem_filter] at hi
    have hw := hi.2
    simp only [winPred] at hw
    obtain ⟨ch, hres, hcond⟩ := hw
    rw [stratResultShoup, Option.some.injEq] at hres
    rw [← hres] at hcond
    rw [Finset.mem_coe, realWinSetShoup, Finset.mem_filter]
    refine ⟨?_, (tSdhCondition_iff_field hord₁ _ _ _).mp hcond⟩
    rw [nonzeroPoints, Finset.mem_erase]
    exact ⟨index_ne_zero hp i, Finset.mem_univ _⟩
  · -- `i ↦ (i+1 : ZMod p)` is injective on `Fin (p−1)`
    intro i _ j _ hij
    simp only at hij
    have hi : (i : ℕ) + 1 < p := by have := i.isLt; omega
    have hj : (j : ℕ) + 1 < p := by have := j.isLt; omega
    have hci : ((i : ℕ) + 1 : ZMod p) = (((i : ℕ) + 1 : ℕ) : ZMod p) := by push_cast; ring
    have hcj : ((j : ℕ) + 1 : ZMod p) = (((j : ℕ) + 1 : ℕ) : ZMod p) := by push_cast; ring
    rw [hci, hcj] at hij
    have := congrArg ZMod.val hij
    rw [ZMod.val_natCast_of_lt hi, ZMod.val_natCast_of_lt hj] at this
    exact Fin.ext (by omega)

/-! ## 6. ⚑ THE CAPSTONE — the Shoup track wired to ArkLib's REAL `tSdhExperiment`. -/

omit [PrimeOrderWith G₂ p] in
/-- **`shoup_tSdh_ggm_sound` — the random-encoding (Shoup) GGM t-SDH bound about ArkLib's REAL
experiment.** For every free-comparison strategy `strat : ShoupStrat p`, the embedded ArkLib
adversary
`embedShoup strat` wins ArkLib's REAL t-SDH experiment with probability at most
`(C(fuel+D+4, 2)·D + (D+1)) / (p − 1)` — the all-pairs collision number (TIGHT under free
comparison)
plus the static Boneh–Boyen root event. Composed through ONE socket, EXACTLY as the Maurer capstone
`GgmEndToEnd.tSdh_ggm_sound`:

* `experiment_eq_count` (adversary-agnostic) turns `tSdhExperiment` into a `Fin (p−1)` count, its
  determinism discharged by `embedShoup_det` (resting on `embedShoup_run_correspondence`);
* the count is bounded by `realWinSetShoup.card` via `winIndexShoup_card_le` +
  `tSdhCondition_iff_field`;
* `realWinSetShoup.card` is bounded by `GgmShoup.card_realWinSetShoup_le_encoding` (the all-pairs
  Schwartz–Zippel bound, whose hybrid `runShoup_congr_off_bad` is PROVEN in Tier 1), with both
  degree
  invariants discharged.

RHS byte-identical to `tSdh_ggm_sound`: BOTH standard GGM models now bound the SAME real experiment.
Quantifies over the IMAGE of `embedShoup` — NOT the full `tSdhAdversary` type (over which it is
false). -/
theorem shoup_tSdh_ggm_sound
    (hord₁ : orderOf g₁ = p)
    (hD : 1 ≤ D) (strat : ShoupStrat p) (fuel : ℕ) :
    tSdhExperiment (g₁ := g₁) (g₂ := g₂) D (embedShoup g₁ D fuel strat)
      ≤ (((fuel + D + 4).choose 2 * D + (D + 1) : ℕ) : ℝ≥0∞) / ((p - 1 : ℕ) : ℝ≥0∞) := by
  have hp : 2 ≤ p := (Fact.out : Nat.Prime p).two_le
  have hseed : ∀ q ∈ (srsStShoup (p := p) D).table, q.natDegree ≤ D := by
    rw [srsStShoup_table]; exact srsSt_table_natDegree_le D hD
  -- (C) collapse the experiment to a count over `Fin (p−1)`
  rw [experiment_eq_count D (embedShoup g₁ D fuel strat) (stratResultShoup g₁ D fuel strat)
    (embedShoup_det hord₁ hD strat fuel)]
  -- the numerator is bounded, in ℕ, by the Shoup all-pairs number
  have hcard : (Finset.univ.filter (winPred (stratResultShoup g₁ D fuel strat) g₁)).card
      ≤ (fuel + D + 4).choose 2 * D + (D + 1) := by
    refine (winIndexShoup_card_le hord₁ hp strat fuel).trans ?_
    exact card_realWinSetShoup_le_encoding strat (srsStShoup D) fuel D (fuel + D + 4)
      (runShoup_output_natDegree_le symAns strat fuel (srsStShoup D) hseed)
      (handleSetShoup_natDegree_le strat (srsStShoup D) fuel hseed)
      (by rw [srsStShoup_table, srsSt_table_length]; omega)
  -- lift the ℕ count bound through the ℝ≥0∞ division
  exact ENNReal.div_le_div_right (by exact_mod_cast hcard) _

omit [PrimeOrderWith G₂ p] in
/-- **`shoup_tSdh_ggm_sound_lt_one`.** Under the standard security regime
`C(fuel+D+4, 2)·D + (D+1) < p − 1`, the t-SDH advantage of `embedShoup strat` against ArkLib's REAL
experiment is a genuine `< 1` — real content, not a restated `≤ 1`. Mirrors
`GgmEndToEnd.tSdh_ggm_sound_lt_one`. -/
theorem shoup_tSdh_ggm_sound_lt_one
    (hord₁ : orderOf g₁ = p)
    (hD : 1 ≤ D) (strat : ShoupStrat p) (fuel : ℕ)
    (hreg : (fuel + D + 4).choose 2 * D + (D + 1) < p - 1) :
    tSdhExperiment (g₁ := g₁) (g₂ := g₂) D (embedShoup g₁ D fuel strat) < 1 := by
  refine lt_of_le_of_lt (shoup_tSdh_ggm_sound hord₁ hD strat fuel) ?_
  have hb0 : ((p - 1 : ℕ) : ℝ≥0∞) ≠ 0 := by
    rw [Ne, Nat.cast_eq_zero]; omega
  have hbtop : ((p - 1 : ℕ) : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  rw [ENNReal.div_lt_iff (Or.inl hb0) (Or.inl hbtop), one_mul]
  exact_mod_cast hreg

/-! ## 7. Non-collapse: the embedded free-comparison class is a genuine non-singleton.

`shoup_tSdh_ggm_sound` quantifies over the IMAGE of `embedShoup`, NOT over all `tSdhAdversary` (over
which the bound is FALSE — a `Classical.choice`-definable adversary inverts the encoding and wins
with
probability 1). `embedShoup_noncollapsing` certifies distinct strategies give distinct real
adversaries, so the class is not degenerate. Mirrors `GgmEmbed.embed_noncollapsing`. -/

/-- The constant Shoup strategy: immediately commit offset `c`, read handle `0`, ignoring the
pattern
history. `stratOffsetShoup 0` / `stratOffsetShoup 1` are the non-collapse witnesses. -/
private def stratOffsetShoup (c : ZMod p) : ShoupStrat p := fun _ => Sum.inr (c, 0)

omit [∀ i, SampleableType (unifSpec.Range i)] [Group G₂] [PrimeOrderWith G₂ p] in
/-- A `stratOffsetShoup c` run (≥ 1 fuel) commits `c` and the `0`-th seed handle — the SRS's `0`-th
G₁ element — on ANY SRS. Reuses `GgmEmbed.seedG_getD_zero`. -/
lemma runEmbedShoup_stratOffsetShoup (D f : ℕ) (c : ZMod p)
    (srs : Vector G₁ (D + 1) × Vector G₂ 2) :
    runEmbedShoup g₁ D (f + 1) (stratOffsetShoup c) srs
      = some (c, srs.1.toList.getD 0 1) := by
  simp only [runEmbedShoup, runEmbedAuxShoup, stratOffsetShoup, seedG_getD_zero]

omit [∀ i, SampleableType (unifSpec.Range i)] [PrimeOrderWith G₂ p] in
/-- **`embedShoup_noncollapsing` — distinct strategies → distinct real adversaries.** There are two
free-comparison strategies whose `embedShoup`-outputs (deterministic `runEmbedShoup` values) are
distinct, so the IMAGE of `embedShoup` is a genuine non-singleton:

* (i) On EVERY SRS, `stratOffsetShoup 0` and `stratOffsetShoup 1` commit distinct offsets (`0 ≠ 1`).
* (ii) On the real KZG SRS, `stratOffsetShoup 0`'s committed GROUP element is the base generator
  `g₁`
  (`≠ 1` by `hg₁`), so the image really exercises the group.

Honest non-claim: `embedShoup` is not injective (off-branch pattern disagreement is invisible); this
asserts only that the image is not a singleton — what a meaningful quantifier requires. -/
theorem embedShoup_noncollapsing (hg₁ : g₁ ≠ 1) (D f : ℕ) :
    ∃ s₀ s₁ : ShoupStrat p,
      (∀ srs : Vector G₁ (D + 1) × Vector G₂ 2,
          runEmbedShoup g₁ D (f + 1) s₀ srs ≠ runEmbedShoup g₁ D (f + 1) s₁ srs) ∧
      (∀ τ : ZMod p,
          runEmbedShoup g₁ D (f + 1) s₀ (PowerSrs.generate (g₁ := g₁) (g₂ := g₂) D τ)
            ≠ some (0, 1)) := by
  have h01 : (0 : ZMod p) ≠ 1 := zero_ne_one
  refine ⟨stratOffsetShoup 0, stratOffsetShoup 1, ?_, ?_⟩
  · intro srs h
    rw [runEmbedShoup_stratOffsetShoup D f 0 srs, runEmbedShoup_stratOffsetShoup D f 1 srs,
        Option.some.injEq, Prod.mk.injEq] at h
    exact h01 h.1
  · intro τ h
    have hval : (PowerSrs.generate (g₁ := g₁) (g₂ := g₂) D τ).1.toList.getD 0 1 = g₁ := by
      have hsrs1 : (PowerSrs.generate (g₁ := g₁) (g₂ := g₂) D τ).1 = PowerSrs.tower g₁ τ D := rfl
      rw [hsrs1, tower_toList_getD τ D 0 (Nat.succ_pos D), pow_zero, pow_one]
    rw [runEmbedShoup_stratOffsetShoup D f 0 (PowerSrs.generate (g₁ := g₁) (g₂ := g₂) D τ), hval,
        Option.some.injEq, Prod.mk.injEq] at h
    exact hg₁ h.2

/-! ## Axiom hygiene — the wiring rests on exactly `[propext, Classical.choice, Quot.sound]`. -/

#print axioms embedShoup_run_correspondence
#print axioms embedShoup_det
#print axioms winIndexShoup_card_le
#print axioms shoup_tSdh_ggm_sound
#print axioms shoup_tSdh_ggm_sound_lt_one
#print axioms embedShoup_noncollapsing

end GgmShoupEmbed

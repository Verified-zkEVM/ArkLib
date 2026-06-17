# CWSS => KS via seeded exhaustive replay

Status: design reviewed and reduced. The route is feasible, but it is not implementation-ready until
the concrete seeded transport theorem for the whole KS experiment (R1) is proved and the pinned-state
stability decision in §6 is settled. Land this in milestones, with a one-challenge-round theorem
before the full multi-round telescope.

Goal:

```lean
verifier.coordinateWiseSpecialSound init impl D relIn relOut.language
  → verifier.knowledgeSoundnessRewindingWithError init impl (D.forkOracleVal StmtOut)
       (D.cwssForkSeededImpl impl verifier) relIn relOut D.knowledgeError
```

Here `D.knowledgeError = sum_i l_i * (k_i - 1) / |S_i|`, so the final lower bound is the additive
`epsilon - D.knowledgeError`.

Path abbreviations: `CWSS/` means
`ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/`; `Implications/CWSSRewinding.lean`
means `ArkLib/OracleReduction/Security/Implications/CoordinateWiseSpecialSoundnessRewinding.lean`.

## 1. Invariants

Keep these events distinct.

* `A`: `(stmtOut, witOut) in relOut`, the KS acceptance event. Its probability is `epsilon`.
* `L`: `stmtOut in relOut.language`, the output-statement language event.
* `S`: the seeded rewinding extractor succeeds: the exhaustive collector returns a `RunForest` and
  the pure tree extractor is applied.

`SiblingRun` stores only `(transcript, stmtOut)`, not `witOut`. Therefore every collector,
heavy-line, and telescope statement must be about `L`, never `A`. The only bridge is
`A → L`, by `relOut.language = Prod.fst '' relOut`.

The extractor does not receive the central `stmtOut`. Consequently, the collector cannot check the
central leaf's language event. Use two notions:

* `collectForestExhaustive`: executable extractor code. At a leaf it returns `.leaf`
  unconditionally; for sibling forks it discards `none` and `stmtOut ∉ relOut.language`.
* `Good_m`: proof-only extractability for a concrete run/continuation. At a leaf it requires that
  the current run's output statement is in `relOut.language`.

Then prove:

* witness branch: in the live KS experiment, `A and S` implies the assembled tree is accepting, so
  the tree extractor returns a valid input witness;
* probability branch: `Pr[L and not S] <= D.knowledgeError`.

The final arithmetic is:

```text
Pr[valid and A] >= Pr[A and S]
               = Pr[A] - Pr[A and not S]
               >= epsilon - D.knowledgeError.
```

## 2. Target theorem interface

The theorem should extend the deprecated single-shot theorem by adding a lawful seed and the
decidability needed by the exhaustive collector:

```lean
theorem coordinateWiseSpecialSound_implies_knowledgeSoundnessRewindingWithError
    (D : CWSSStructure pSpec)
    [∀ i, SampleableType (pSpec.Challenge i)]
    [∀ i, Fintype (D.alphabet i)]
    [∀ i, SampleableType (D.alphabet i)]
    [∀ i, DecidableEq (D.alphabet i)]
    (hSound : ∀ i, 1 ≤ D.soundnessParam i)
    (relIn : Set (StmtIn × WitIn)) (relOut : Set (StmtOut × WitOut))
    [DecidablePred (· ∈ relOut.language)]
    (verifier : Verifier oSpec StmtIn StmtOut pSpec)
    (hImpl : impl.ReplayConsistent)
    (hVer : verifier.DeterminateAcceptance init impl relOut.language)
    (seed : impl.SeededReplay init) [LawfulSeededReplay seed] :
    verifier.coordinateWiseSpecialSound init impl D relIn relOut.language →
      verifier.knowledgeSoundnessRewindingWithError init impl (D.forkOracleVal StmtOut)
        (D.cwssForkSeededImpl impl verifier) relIn relOut D.knowledgeError
```

Notes to pin down before proving:

* Keep `hImpl` and `hVer` on the live `impl`; they are used only in the witness branch. The
  probability branch uses each pinned implementation `seed.pin t`, plus
  `LawfulSeededReplay.det t` and `LawfulSeededReplay.consistent seed t`.
* If `SampleableType` already supplies nonempty finite support, prove helper instances from it.
  Otherwise add `[∀ i, Nonempty (D.alphabet i)]`; the heavy-lines denominator must never be
  the empty-cardinality case.
* `hSound` rules out the meaningless `k_i = 0` interpretation hidden by truncated subtraction.
  The `k_i = 1` case is allowed: it means no siblings are needed at that round.
* The coordinate sampling bridge needs finite challenge types and product sampling:
  `[∀ i, Finite (pSpec.Challenge i)]` and
  `[SampleableType (Fin (D.coordIndex i) → D.alphabet i)]`. Prefer deriving these from
  `D.decompose` and the alphabet instances, then record exact instance lemmas near heavy-lines.

## 3. Existing pieces to reuse

Do not rebuild these.

* `Rewinding/Basic.lean`: `Extractor.Rewinding`, `QueryImpl.Reachable`,
  `QueryImpl.ReplayConsistent`, `Verifier.DeterminateAcceptance`,
  `knowledgeSoundnessRewindingWithError`.
* `Rewinding/Coupling.lean`: `SiblingRun`, `FullTranscript.pinnedChallengeImpl`,
  `Prover.Realizes`, `QueryImpl.IsDeterministic`, closure lemmas, and run-coupling lemmas.
* `Rewinding/ReplayFork.lean`: `ReplaySuffix`, `replayChallenge`, `replayForkImpl`, G1-G7, and
  `replayForkImpl_replay_deterministic`.
* `Rewinding/SeededReplay.lean`: `SeededReplay`, `LawfulSeededReplay`, `consistent`,
  `ofDeterministic`, `lawful_ofDeterministic`. R1 below is still missing.
* `CWSS/ForkOracle.lean`: `ForkQueryVal`, `forkOracleVal`, `cwssForkSeededImpl`,
  `cwssForkSeededImpl_coordEq`.
* `CWSS/Basic.lean`: `CoordEq`, `IsSpecialSoundFamily`, `CWSSStructure`, `arity`,
  `ofSpecialSound`, `knowledgeError`, `IsStructured`, `coordinateWiseSpecialSound`.
* `CWSS/CoordinateOracle.lean`: keep `challenge_uniform_eq_bundle_coords`; the coordinate-oracle
  substrate is not part of the seeded additive route unless another client still needs it.
* `Implications/CWSSRewinding.lean`: `gatherFin`, `RunForest`, `runs`, `toTree`, `WellFormed`,
  `WellFormed.toTree_isStructured`, `WellFormed.mem_toTree_fullTranscripts`, `agree_snoc`,
  `aux_mem_transcripts`, and the old support-inversion proof patterns.

After the seeded collector lands, delete the deprecated single-shot collector/implication blocks and
update docstrings that still say bounded extractors cannot achieve the additive error. The corrected
statement is: single-shot bounded forks only give forking-style losses; exhaustive seeded replay can
give the additive bound when the ambient `oSpec` randomness admits a lawful tape.

## 4. Extractor and witness branch

The extractor is bounded but exhaustive: it queries every `v : D.alphabet i` at each coordinate line.
This can be exponential, but `knowledgeSoundnessRewinding` has no efficiency bound.

Use `SiblingRun pSpec StmtOut` as the proof-side "scored run" type for both central and sibling runs.
The measured central run supplies `⟨transcript, stmtOut⟩`; the executable extractor still receives
only `transcript`, but all `Good`/probability lemmas should carry the scored central run so leaf
language checks are available.

Define:

* `tryCollectOneExhaustive`: query one value `v : D.alphabet i` in plain `OracleComp`, not
  `OptionT`. It returns `none` for the guarded center value, failed fork, language failure, or
  recursive subcollection failure; it returns `some (sib, subforest)` otherwise. Running the
  recursive collector's `.run` here is deliberate: a bad value must not abort the whole sweep.
* `alphabetValues`: a local list containing every `v : D.alphabet i` exactly once, derived from
  `Finset.univ` with `nodup` and membership lemmas. Avoid proving list-order facts inline.
* `collectSiblingsExhaustive`: iterate `tryCollectOneExhaustive` over `alphabetValues`. Keep the
  successful candidates in a list, fail if its length is `< k_i - 1`, and convert
  `List.take (k_i - 1)` into the `Fin (k_i - 1)` sibling/subforest family.
* `collectForestExhaustive`: reverse-induction over rounds. Message rounds recurse on the center.
  Challenge rounds recurse on the center, then collect sibling subforests coordinatewise.
* `rewindingExtractorSeeded`: collect from the measured transcript, assemble `RunForest.toTree`, and
  apply the tree extractor supplied by `coordinateWiseSpecialSound`.

Implement these in small pieces:

1. `tryCollectOneExhaustive_unfold_center`: the center value returns `none` without querying.
2. `tryCollectOneExhaustive_support_some`: a successful value query gives the fork support fact,
   `stmtOut ∈ relOut.language`, recursive collection support, and the returned candidate.
3. `alphabetValues_mem` and `alphabetValues_nodup`: finite enumeration facts used by the collector
   and heavy-to-collector bridge.
4. `collectAllExhaustive_support_mem`: every list member returned by the exhaustive pass satisfies
   the `tryCollectOne` success predicate.
5. `collectAllExhaustive_length_ge_of_heavy`: if at least `k_i - 1` non-center values satisfy the
   success predicate, the list has enough entries.
6. `take_to_fin_family_spec`: the first `k_i - 1` entries of a list with sufficient length form a
   `Fin (k_i - 1)` family, and every family entry came from the list.

Witness branch obligations then become:

* Derive `cwssForkSeededImpl_prefix_eq`, `_realizes`, `_accepts`, and `_reachable` from general
  G3-G6 by unfolding the center guard as in `cwssForkSeededImpl_coordEq`.
* Add a right-summand simplification for `forkOracleVal`, analogous to the old
  `simulateQ_addLift_fork`.
* Port the old monadic correctness proof in layers, not as one theorem:
  `tryCollectOneExhaustive_spec`, `collectSiblingsExhaustive_spec`, `gatherFinExhaustive_spec`,
  `aux_collectForestExhaustive_wellFormed`, then the public
  `collectForestExhaustive_wellFormed`.
* Central acceptance is external to `WellFormed`: on event `A`, the measured central output gives
  `L`; apply `hVer` to the realized central run to get the `ChallengeTree.IsAccepting` certificate
  for the central path.

Then `WellFormed.toTree_isStructured`, `WellFormed.mem_toTree_fullTranscripts`, the central
acceptance certificate, and `coordinateWiseSpecialSound` prove `(stmtIn, extracted) in relIn`.

## 5. Heavy lines

Add a protocol-free file, probably `CWSS/HeavyLines.lean`, with:

```lean
theorem card_light_accepting_le {S} [Fintype S] [DecidableEq S] [Nonempty S]
    (ℓ k : ℕ) (acc : (Fin ℓ → S) → Prop) [DecidablePred acc] :
    (Finset.univ.filter fun c =>
      acc c ∧ ∃ j, (Finset.univ.filter fun w => acc (Function.update c j w)).card < k).card
      ≤ ℓ * (k - 1) * Fintype.card S ^ (ℓ - 1)

theorem prob_lines_light_le {S} [Fintype S] [DecidableEq S] [Nonempty S]
    (ℓ k : ℕ) [SampleableType (Fin ℓ → S)]
    (acc : (Fin ℓ → S) → Prop) [DecidablePred acc] :
    Pr[fun c => acc c ∧
      ∃ j, (Finset.univ.filter fun w => acc (Function.update c j w)).card < k
      | $ᵗ (Fin ℓ → S)]
      ≤ (ℓ * (k - 1) : ℝ≥0∞) / Fintype.card S
```

The exact notation/types will follow local `ProbComp` conventions; the statement above is only the
shape. Build this in three layers:

1. `line_fiber_card_le`: for fixed `j` and fixed off-`j` coordinates, a light accepting fiber has
   cardinality at most `k - 1`.
2. `card_light_at_coord_le`: sum the fiber bound over off-`j` assignments.
3. `card_light_accepting_le`: union-bound over `j : Fin ℓ`.
4. `prob_lines_light_le`: divide by the uniform sample space cardinality.

Then add `prob_lines_light_le_challenge`, transported along `D.decompose i` using
`challenge_uniform_eq_bundle_coords`.

## 6. Proof-only extractability

Define proof-only extractability in a separate namespace, e.g. `SeededAnalysis`, so it never pollutes
the executable extractor API.

For fixed tape `t`, parent scored run `centerRun : SiblingRun pSpec StmtOut`, round `m`, coordinate
`j`, and replacement value `v`, define `acc(v)` to mean:

* full replay with `replayForkImpl (seed.pin t) ... parent m replacement .replay` returns
  `some sib`; uniqueness of this outcome comes from `LawfulSeededReplay.det t` and
  `replayForkImpl_replay_deterministic`, not from any totality claim; and
* that sibling is `Good_{m+1}`.

At a leaf, `Good` requires the current run's output statement to be in `relOut.language`. This is
proof-only data: for the measured central run it comes from event `L`; for forked siblings it is
available from `SiblingRun.stmtOut` and the collector's language filter.

Two endpoint facts are load-bearing:

* For `v = center`, the CWSS oracle guard returns `none`, but the proof does not query it. G7 for the
  general fork says full replay to the parent's own challenge reproduces the parent, so `acc(center)`
  is the center-continuation term in `Good_m`.
* For `v ≠ center`, `cwssForkSeededImpl` is the general full-replay fork at the coordinate-updated
  replacement. G1 gives `CoordEq`, and successful exhaustive candidates are exactly non-center values
  whose sibling output is in `relOut.language` and whose recursive subcollection succeeds.

Before implementing Branch B, settle the pinned-state stability issue. The exhaustive sweep is
sequential: trial forks for earlier values thread the `StateT` state before later values are tried.
The heavy-lines predicate is clean only if the output of a pinned full replay is independent of those
intermediate states.

Decision point:

* Preferred route: strengthen or derive from `LawfulSeededReplay` a reusable output-stability lemma
  for pinned implementations, sufficient to show that `replayForkImpl (seed.pin t) ... .replay`
  has the same `Option SiblingRun` support from any reachable sweep state. A possible shape is:

  ```lean
  theorem pinned_replayFork_output_stable
      (hReach₁ : (seed.pin t).Reachable s₀ s₁)
      (hReach₂ : (seed.pin t).Reachable s₀ s₂) :
      support (((replayForkImpl (seed.pin t) ... replacement .replay).run s₁).map Prod.fst)
        = support (((replayForkImpl (seed.pin t) ... replacement .replay).run s₂).map Prod.fst)
  ```

* Fallback route: make `Good` and the heavy-line predicate state-sequential, scoring each value from
  the actual state reached before that value in the enumeration. This avoids strengthening
  `LawfulSeededReplay`, but it makes the heavy-lines argument enumeration-dependent and is probably
  much harder to telescope.

Break `Good` into small lemmas after that decision:

1. `good_leaf_iff_lang`: terminal `Good` is exactly `centerRun.stmtOut ∈ relOut.language`.
2. `good_center_replay`: G7 identifies `acc(center)` with the center continuation.
3. `heavy_line_noncenter_count`: if the center value is good and the line has at least `k_i` good
   values, then at least `k_i - 1` non-center values are good.
4. `good_heavy_to_tryCollectOne`: a non-center value counted by a heavy line gives a successful
   `tryCollectOneExhaustive`.
5. `good_heavy_to_collectSiblings`: heaviness gives enough successful values for one coordinate.
6. `good_implies_collectForest`: `Good_m` implies the executable collector succeeds from round `m`.
7. `collectForest_success_implies_wellFormed`: the live-implementation direction for the witness
   branch.

Avoid a global biconditional unless a later proof truly needs it.

## 7. Additive probability bound

Per tape, prove:

```text
Pr[L and not S | seed.pin t, seed.pinInit t] <= D.knowledgeError.
```

Then average over `seed.genTape` using R1 and use `A → L`.

### One-round milestone

First prove a one-challenge-round theorem with an explicit one-round protocol hypothesis. This is a
de-risking theorem, not the final result.

* `acc(v)` is "the replayed run with replacement value `v` lands in `relOut.language`."
* G7 identifies `acc(center)` with the pinned language event `L`.
* `L and not S` is contained in `L and exists light coordinate line`.
* `prob_lines_light_le_challenge` gives the loss `l * (k - 1) / |S|`.
* R1 transports the pinned failure event to the live KS experiment.

### Multi-round telescope

Use Lean-friendly indices over `Fin (n + 1)`; avoid paper-style `T_1`/`T_{mu+1}` off-by-one
ambiguity. Define `Good_m^t` recursively for continuations starting at round index `m`:

* leaf: current output statement is in `relOut.language`;
* message node: `Good` of the child;
* challenge node: center continuation is good and every coordinate line is heavy, where heaviness
  counts values whose full-replay sibling is good from `m.succ`.

Let `T_m^t` be the probability, under `seed.pin t` and `seed.pinInit t`, that `Good_m^t` holds for
the sampled continuation. Then:

* at the terminal index, `T_last^t = Pr[L | seed.pin t, seed.pinInit t]`;
* `Good_0^t` implies `L and S`, hence `Pr[L and S | seed.pin t] >= T_0^t`;
* for each challenge round `m`,
  `T_m^t >= T_{m.succ}^t - l_m * (k_m - 1) / |S_m|`;
* message rounds have equality or a pure reindexing step.

Telescoping yields `T_0^t >= Pr[L | seed.pin t] - D.knowledgeError`, hence
`Pr[L and not S | seed.pin t] <= D.knowledgeError`.

Required sublemmas, in an implementation order that keeps each proof small:

1. `run_peel_round`: expose the round-`m` challenge as a uniform bind using `runToRound_succ` and
   `probOutput_bind_eq_tsum`.
2. `good_unfold_msg`, `good_unfold_chal`, `good_unfold_leaf`: simp-facing unfold lemmas for `Good`.
3. `bad_chal_subset_light_line`: at one challenge node, `Good_{m.succ}` and not `Good_m` imply some
   coordinate line is light.
4. `bad_chal_prob_le`: apply `prob_lines_light_le_challenge` to that round-local `acc`.
5. `round_step_msg` and `round_step_chal`: prove the `T_m` step separately for message and challenge
   rounds.
6. `telescope_round_steps`: a pure finite-sum lemma over `Fin (n + 1)` that accumulates only
   challenge-round losses.
7. `extract_prob_ge_pinned`: fixed-tape language-failure bound.
8. `extract_prob_ge_live`: R1 transports the fixed-tape bound to the live KS experiment.

## 8. R1: seeded transport

`LawfulSeededReplay.faithful` transports only a single `simulateQ impl oa` where
`oa : OracleComp oSpec alpha`. The KS experiment is larger: it adds the challenge oracle, logs the
measured run, then runs an extractor whose fork answers contain nested replays through the same
ambient `impl`. Do not state transport for an arbitrary experiment functional; that would hide the
real side condition.

Define a concrete `ksExperiment` matching `knowledgeSoundnessRewinding`'s `exec`:

1. draw the initial state;
2. run the reduction with `impl.addLift challengeQueryImpl`, logging the measured run;
3. continue from the resulting state;
4. run the extractor with `impl.addLift forkImpl`, where each fork answer is interpreted by
   `D.cwssForkSeededImpl impl verifier`.

Then prove:

```lean
evalDist (do
  let t <- seed.genTape
  ksExperiment (seed.pin t) (seed.pinInit t)
    (D.cwssForkSeededImpl (seed.pin t) verifier) E)
=
evalDist (ksExperiment impl init
    (D.cwssForkSeededImpl impl verifier) E)
```

The proof needs a flattening lemma, probably in `Rewinding/Coupling.lean`, that inlines fork answers
whose body is itself `simulateQ impl ...` into the host simulation while threading the same state.
The existing `simulateQ_addLift_left` and `simulateQ_addLift_getChallenge` are enough for
oSpec-free challenge oracles, but not for nested replay forks.

Break R1 into checkpoints:

1. `ksExperiment_noExtractor_transport`: transport the measured run with logging, before extractor
   execution.
2. `forkAnswer_transport`: transport one `D.cwssForkSeededImpl` answer. This is the first lemma that
   needs nested-replay flattening.
3. `simulateQ_ext_fork_transport`: induction on the extractor `OracleComp`, using
   `forkAnswer_transport` for right-summand queries and `LawfulSeededReplay.faithful` for left
   `oSpec` queries.
4. `ksExperiment_transport`: combine measured-run transport with extractor transport.
5. `event_prob_transport`: convert `evalDist` equality into the probability equalities needed by
   Branch B.

De-risk R1 first for empty `oSpec` / deterministic `impl`, where
`SeededReplay.ofDeterministic` collapses most of the statement by `rfl` or `simp`.

## 9. Build order and risks

Recommended order:

1. Seeded fork corollaries for `cwssForkSeededImpl`, plus `simulateQ_addLift_forkVal`.
2. `CWSS/HeavyLines.lean`, proving the pure cardinality lemmas before probability lemmas.
3. Exhaustive collector definitions and support lemmas through `take_to_fin_family_spec`.
4. Live witness branch through `collectForestExhaustive_wellFormed`.
5. Settle and prove the pinned-state stability lemma, or explicitly choose the state-sequential
   fallback.
6. Proof-only `Good` predicates and `good_implies_collectForest`.
7. One-round additive theorem, initially for deterministic/empty `oSpec`.
8. R1 transport for the concrete `ksExperiment`, first in the deterministic/empty-`oSpec` case, then
   for arbitrary lawful seeded replay.
9. Multi-round `run_peel_round`, round-step lemmas, telescope, and `extract_prob_ge`.
10. Final theorem, special-soundness corollary via `D = CWSSStructure.ofSpecialSound k`, docstring
   cleanup, and deletion of deprecated single-shot blocks.

Ranked risks:

1. **Pinned-state output stability for sequential exhaustive sweeps.** Blocking for the additive
   theorem as currently planned. The preferred route is still feasible, but it must be proved or
   adopted as a strengthened seeded-replay law before Branch B can be implementation-ready. The
   state-sequential fallback is possible but likely much harder.
2. **R1 flattening/transport for the nested fork experiment.** Blocking for the final live
   `knowledgeSoundnessRewindingWithError` theorem, but not for pinned one-round or pinned multi-round
   milestones. This is a proof-engineering risk, not a conceptual blocker, because the experiment
   shape is concrete.
3. **Multi-round round-step/telescope proof with prefix/suffix averaging.** Not a feasibility
   blocker if the one-round theorem and pinned-state stability are in place. It is the largest
   remaining Lean proof, so keep the message/challenge round steps and pure telescope separate.
4. **Inverting the exhaustive query/filter/take collector support.** Not a feasibility blocker.
   This is tedious `OptionT`/list/Fin bookkeeping; the plan isolates it before probability work.
5. **Protocol-free heavy-lines counting and challenge-coordinate sampling bridge.** Low conceptual
   risk. It can be built and validated independently, and failure here would be local to
   cardinality/probability lemmas rather than the replay architecture.

Feasibility assessment: the design is feasible as a staged implementation, but not yet
implementation-ready for the final theorem. The only issue that could force a design choice is risk
1. Risks 2-5 should not change the architecture; they affect proof effort and milestone ordering.

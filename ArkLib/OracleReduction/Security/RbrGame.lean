/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

import ArkLib.OracleReduction.ProtocolSpec.Basic
import ArkLib.Data.Probability.Instances
import ArkLib.ToVCVio.OracleComp.QueryTracking.LoggingOracle

/-!
# `ProtocolSpec` glue for the round-by-round (knowledge) soundness games

ArkLib's round-by-round soundness games (`Verifier.rbrSoundness`,
`Verifier.rbrKnowledgeSoundness` in `ArkLib/OracleReduction/Security/RoundByRound.lean`) all
compute, per challenge round `i`, a probability of the shape

```
Pr[ event | do
  (simulateQ (impl.addLift challengeQueryImpl : QueryImpl _ (StateT σ ProbComp))
    (do
      let tr ← proverRun                                -- adversarial, arbitrary
      let challenge ← liftComp (pSpec.getChallenge i) _
      return (… tr … challenge …))).run' (← init)]
```

This file provides the generic ArkLib-local glue to bound such probabilities from
per-fixed-transcript bounds `∀ tr, Pr[ event tr · | $ᵗ (pSpec.Challenge i)] ≤ ε`:

* `ProtocolSpec.simulateQ_addLift_challengeQueryImpl_getChallenge` resolves the simulated
  challenge query into an explicit uniform draw `liftM ($ᵗ (pSpec.Challenge i))`;
* `ProtocolSpec.probEvent_simulateQ_addLift_getChallenge_bind_le` is the master mixture bound
  for the full game shape (built on VCV-io's `probEvent_bind_le_of_forall_le`);
* `probEvent_uniformSample_eq_prob_uniformOfFintype` bridges VCV-io's `$ᵗ` (the
  `SampleableType` uniform sampler used by `challengeQueryImpl`) to the PMF-level
  `Pr_{ let x ←$ᵖ α }[…]` notation in which per-transcript bounds are usually proven.

These statements are `ProtocolSpec`-specific and so live in ArkLib core, but their *content* is
not: `challengeQueryImpl` is only `fun q => $ᵗ _`, i.e. "answer each query with a uniform sample of
its answer type", and `QueryImpl.addLift` is already VCV-io's. No notion of protocol, transcript or
round enters any proof below — they are `probEvent_bind_le_of_forall_le` plus a `simulateQ`
normalisation. Generalising the challenge oracle to an arbitrary uniform-answer `QueryImpl` would
let the mixture bounds move upstream, leaving thin specialisations here. The `loggingOracle` lemmas
they build on already sit in `ArkLib/ToVCVio/OracleComp/QueryTracking/LoggingOracle.lean` for
exactly that reason; `probEvent_uniformSample_eq_prob_uniformOfFintype` stays here only because it
mentions ArkLib's `Pr_{…}` notation.

Cf. VCVio PR #475, which adds a protocol-agnostic round-by-round layer. Its generic
`KnowledgeTransitionFamily.IsBounded` packages exactly the inner worst-case obligation of
`Verifier.rbrKnowledgeSoundnessWorstCase`, but it has no averaged, prover-sampled notion, so the
worst-case ⇒ averaged bridges in `Security/RoundByRound.lean` are not subsumed by it; and its
transition family is law-free data, so ArkLib's `KnowledgeStateFunction` obligations do not
transfer. Its source-shaped `ExtractionCondition` is a *different* notion from ArkLib's
`rbrKnowledgeSoundnessOneShot`, which samples the prefix by running a prover and feeds the prover's
query log to the extractor.

Beyond the three lemmas above, this file also carries the `OptionT` challenge-first master
bounds (`ProtocolSpec.probEvent_optionT_simulateQ_addLift_*`). Those serve the *plain* (non-rbr)
knowledge-soundness game, whose computation is `Option`-valued and draws its challenge first;
see the section header preceding them for why the rbr master bound does not apply there. The two
generic `loggingOracle` lemmas used by later reductions live separately in
`ArkLib/ToVCVio/OracleComp/QueryTracking/LoggingOracle.lean`, from where they can move upstream
without importing ArkLib core.
-/

open OracleComp OracleSpec ProtocolSpec ProbabilityTheory
open scoped ENNReal
open Probability

namespace ProtocolSpec

variable {n : ℕ} {pSpec : ProtocolSpec n} [∀ j, SampleableType (pSpec.Challenge j)]
  {ι : Type} {oSpec : OracleSpec ι} {σ : Type}

/-- **Challenge-query resolution for the rbr games.** Simulating the lifted challenge query
`liftComp (pSpec.getChallenge i) _` under the game's combined implementation
`impl.addLift challengeQueryImpl` is exactly the uniform draw `$ᵗ (pSpec.Challenge i)` lifted
into `StateT σ ProbComp` (the oracle state is untouched).

The proof routes the lifted computation to the right summand of the `addLift`
(`QueryImpl.simulateQ_add_liftComp_right`), then resolves the single query
(`simulateQ_spec_query`); `challengeQueryImpl ⟨i, ()⟩ = $ᵗ (pSpec.Challenge i)` holds by
definition. -/
lemma simulateQ_addLift_challengeQueryImpl_getChallenge
    (impl : QueryImpl oSpec (StateT σ ProbComp)) (i : pSpec.ChallengeIdx) :
    simulateQ (impl.addLift challengeQueryImpl : QueryImpl _ (StateT σ ProbComp))
      (liftComp (pSpec.getChallenge i) (oSpec + [pSpec.Challenge]ₒ)) =
      (liftM ($ᵗ (pSpec.Challenge i)) : StateT σ ProbComp (pSpec.Challenge i)) := by
  rw [QueryImpl.addLift_def, QueryImpl.simulateQ_add_liftComp_right]
  -- `pSpec.getChallenge i` is reducibly `liftM ([pSpec.Challenge]ₒ.query ⟨i, ()⟩)`, and
  -- `(challengeQueryImpl.liftTarget _) ⟨i, ()⟩` is definitionally `liftM ($ᵗ _)`.
  exact (simulateQ_spec_query (challengeQueryImpl.liftTarget (StateT σ ProbComp))
    ⟨i, ()⟩).trans rfl

/-- **Master mixture bound for the rbr game shape.** If, for every *fixed* output `tr` of the
(adversarial, arbitrary) simulated prover run `oa`, the event holds over a fresh uniform
challenge with probability at most `ε`, then the whole game probability — initial state
sampled from `init`, prover run simulated under `impl.addLift challengeQueryImpl`, challenge
obtained via `liftComp (pSpec.getChallenge i) _` — is at most `ε`.

`f` packages the game's `return` expression (e.g. `fun tr c ↦ (tr.1.1, c, tr.2)` for
`rbrKnowledgeSoundness`); when applying this lemma to a game whose `do`-block destructures
the prover output, pass `f` explicitly and use `exact` (the match-lambdas agree only up to
definitional structure eta). -/
theorem probEvent_simulateQ_addLift_getChallenge_bind_le
    {T β : Type}
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (oa : OracleComp (oSpec + [pSpec.Challenge]ₒ) T) (i : pSpec.ChallengeIdx)
    (f : T → pSpec.Challenge i → β) (E : β → Prop) {ε : ℝ≥0∞}
    (h : ∀ tr : T, Pr[ fun c ↦ E (f tr c) | $ᵗ (pSpec.Challenge i)] ≤ ε) :
    Pr[ E | do
      (simulateQ (impl.addLift challengeQueryImpl : QueryImpl _ (StateT σ ProbComp))
        (do
          let tr ← oa
          let challenge ← liftComp (pSpec.getChallenge i) (oSpec + [pSpec.Challenge]ₒ)
          return f tr challenge)).run' (← init)] ≤ ε := by
  refine probEvent_bind_le_of_forall_le fun s _ ↦ ?_
  have hbody : (simulateQ (impl.addLift challengeQueryImpl : QueryImpl _ (StateT σ ProbComp))
      (do
        let tr ← oa
        let challenge ← liftComp (pSpec.getChallenge i) (oSpec + [pSpec.Challenge]ₒ)
        return f tr challenge)).run' s
      = (simulateQ (impl.addLift challengeQueryImpl : QueryImpl _ (StateT σ ProbComp)) oa).run s
          >>= fun x ↦ f x.1 <$> ($ᵗ (pSpec.Challenge i)) := by
    rw [simulateQ_bind, StateT.run'_eq, StateT.run_bind, map_bind]
    refine bind_congr fun x ↦ ?_
    rw [simulateQ_bind, simulateQ_addLift_challengeQueryImpl_getChallenge, StateT.run_bind]
    simp only [simulateQ_pure, StateT.run_monadLift, StateT.run_pure, bind_pure_comp,
      Functor.map_map, monadLift_self]
  rw [hbody]
  refine probEvent_bind_le_of_forall_le fun x _ ↦ ?_
  rw [probEvent_map]
  exact h x.1

end ProtocolSpec

/-- **`$ᵗ` ↔ `$ᵖ` bridge.** The probability of an event under VCV-io's canonical uniform
sampler `$ᵗ α` (the `SampleableType.selectElem` used by `challengeQueryImpl`) coincides with
the PMF-level probability `Pr_{ let x ←$ᵖ α }[…]` under `PMF.uniformOfFintype`. Use it to
discharge the per-transcript hypothesis of
`ProtocolSpec.probEvent_simulateQ_addLift_getChallenge_bind_le` from a PMF-level bound. -/
lemma probEvent_uniformSample_eq_prob_uniformOfFintype {α : Type} [SampleableType α]
    [Fintype α] [Nonempty α] (p : α → Prop) :
    Pr[ p | $ᵗ α] = Pr_{ let x ←$ᵖ α }[ p x ] := by
  classical
  rw [probEvent_uniformSample, prob_uniform_eq_card_filter_div_card]
  simp only [ENNReal.coe_natCast]

section ExecutableDocumentation

open ProtocolSpec

variable {n : ℕ} {pSpec : ProtocolSpec n} [∀ j, SampleableType (pSpec.Challenge j)]
  {ι : Type} {oSpec : OracleSpec ι} {σ : Type}

/-- Executable documentation: the master lemma engages the exact `rbrKnowledgeSoundness` game
shape — destructuring prover-output bind, challenge via `liftComp (pSpec.getChallenge i) _`,
`return` of the `(transcript, challenge, log)` triple — with `f` passed explicitly. -/
example {T₁ T₂ L : Type}
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (oa : OracleComp (oSpec + [pSpec.Challenge]ₒ) ((T₁ × T₂) × L)) (i : pSpec.ChallengeIdx)
    (E : T₁ × pSpec.Challenge i × L → Prop) {ε : ℝ≥0∞}
    (h : ∀ (t₁ : T₁) (log : L),
      Pr[ fun c ↦ E (t₁, c, log) | $ᵗ (pSpec.Challenge i)] ≤ ε) :
    Pr[ E | do
      (simulateQ (impl.addLift challengeQueryImpl : QueryImpl _ (StateT σ ProbComp))
        (do
          let ⟨⟨t₁, _⟩, log⟩ ← oa
          let challenge ← liftComp (pSpec.getChallenge i) (oSpec + [pSpec.Challenge]ₒ)
          return (t₁, challenge, log))).run' (← init)] ≤ ε :=
  probEvent_simulateQ_addLift_getChallenge_bind_le init impl oa i
    (fun x c ↦ (x.1.1, c, x.2)) E (fun x ↦ h x.1.1 x.2)

end ExecutableDocumentation

/-! ## Knowledge-soundness game glue

The plain (non-rbr) knowledge-soundness game (`Verifier.knowledgeSoundness`,
`ArkLib/OracleReduction/Security/Basic.lean`) differs from the rbr games in two ways that
make the master lemma above inapplicable:

* the game is `Option`-valued (`OptionT.mk` of the simulated run — the reduction execution
  may fail), and
* for a verifier-first protocol the challenge is drawn *first*, with the adversarial tail
  (the prover's remaining moves plus the pure verifier/extractor projections) *after* it
  inside the same computation.

The underlying probabilistic steps — the "zero off the challenge event" monotonicity step and
its additive and convex prefix-split sharpenings (`probEvent_bind_le_probEvent`,
`probEvent_bind_le_probEvent_add`, `probEvent_bind_le_probEvent_convex`) — live upstream in
VCVio (`VCVio/EvalDist/Monad/Basic.lean`). What follows is the ArkLib-specific `ProtocolSpec`
glue built on top of them.

The master bound for this shape is
`ProtocolSpec.probEvent_optionT_simulateQ_addLift_getChallenge_bind_some_le`. It consumes a
challenge-only probability bound `Pr[fun c ↦ ∃ t, E (f c t) | $ᵗ _] ≤ ε`, where the `∃ t`
ranges over *all* possible tail outputs — the worst-case form in which per-round soundness
bounds are normally stated, so no reasoning about the tail's distribution is needed. -/
namespace ProtocolSpec

variable {n : ℕ} {pSpec : ProtocolSpec n} [∀ j, SampleableType (pSpec.Challenge j)]
  {ι : Type} {oSpec : OracleSpec ι} {σ : Type}

/-- **Master mixture bound for the challenge-first knowledge-soundness game shape.** If the
game's `Option`-valued computation `oa` is a fresh challenge draw followed by an arbitrary
(adversarial) tail whose final value is `some (f c t)`, then the whole game probability —
initial state sampled from `init`, simulation under `impl.addLift challengeQueryImpl`,
`OptionT`-wrapped — is bounded by the challenge-only probability of `∃ t, E (f c t)` over a
uniform challenge.

`oa` is taken as an argument together with the equation `hoa` (rather than inlined in the
conclusion) so that applying the lemma to a concrete game by `refine` assigns `oa` to the
game's computation by *definitional* unification; the caller then proves `hoa` by genuine
rewriting (log-discarding, prover-run unfolding) without having to respell the game term. -/
theorem probEvent_optionT_simulateQ_addLift_getChallenge_bind_some_le
    {T β : Type}
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (oa : OracleComp (oSpec + [pSpec.Challenge]ₒ) (Option β)) (i : pSpec.ChallengeIdx)
    (tail : pSpec.Challenge i → OracleComp (oSpec + [pSpec.Challenge]ₒ) T)
    (f : pSpec.Challenge i → T → β) (E : β → Prop) {ε : ℝ≥0∞}
    (hoa : oa = do
      let c ← liftComp (pSpec.getChallenge i) (oSpec + [pSpec.Challenge]ₒ)
      (fun t ↦ some (f c t)) <$> tail c)
    (h : Pr[ fun c ↦ ∃ t, E (f c t) | $ᵗ (pSpec.Challenge i)] ≤ ε) :
    Pr[ E | OptionT.mk (do
      (simulateQ (impl.addLift challengeQueryImpl : QueryImpl _ (StateT σ ProbComp))
        oa).run' (← init))] ≤ ε := by
  subst hoa
  -- Resolve the simulated challenge query into a top-level uniform draw, per initial state.
  have hbody : ∀ s : σ,
      (simulateQ (impl.addLift challengeQueryImpl : QueryImpl _ (StateT σ ProbComp))
        (do
          let c ← liftComp (pSpec.getChallenge i) (oSpec + [pSpec.Challenge]ₒ)
          (fun t ↦ some (f c t)) <$> tail c)).run' s
      = ($ᵗ (pSpec.Challenge i)) >>= fun c ↦
          (fun t ↦ some (f c t)) <$>
            ((simulateQ (impl.addLift challengeQueryImpl : QueryImpl _ (StateT σ ProbComp))
              (tail c)).run' s) := by
    intro s
    rw [simulateQ_bind, simulateQ_addLift_challengeQueryImpl_getChallenge,
      StateT.run'_bind']
    simp only [StateT.run_liftM, bind_assoc, pure_bind, simulateQ_map, StateT.run'_map']
  rw [OptionT.mk_bind]
  refine probEvent_bind_le_of_forall_le fun s _ ↦ ?_
  rw [hbody s, OptionT.mk_bind]
  refine le_trans (probEvent_bind_le_probEvent (p := fun c ↦ ∃ t, E (f c t)) ?_)
    (le_trans (le_of_eq (OptionT.probEvent_liftM _ _)) h)
  intro c _ hc
  refine probEvent_eq_zero fun z hz hE ↦ hc ?_
  rw [OptionT.mem_support_iff, OptionT.run_mk, support_map, Set.mem_image] at hz
  obtain ⟨t, _, ht⟩ := hz
  exact ⟨t, by rw [Option.some_inj] at ht; rw [ht]; exact hE⟩

/-- **Prefix-extended, `Option`-valued master mixture bound for the knowledge-soundness game
shape.** Generalizes `probEvent_optionT_simulateQ_addLift_getChallenge_bind_some_le` in two
directions needed by multi-round games: an arbitrary (adversarial) prefix `mid` runs *before*
the challenge draw, and the post-challenge value `f pre c t` is `Option`-valued (the verifier
may reject, producing `none`). The challenge-only hypothesis accordingly asks for the
probability that *some* tail output produces a `some` value satisfying the event.

`oa` is taken as an argument together with the equation `hoa` (rather than inlined in the
conclusion) so that applying the lemma to a concrete game by `refine` assigns `oa` to the
game's computation by *definitional* unification; the caller then proves `hoa` by genuine
rewriting without having to respell the game term. The conclusion fixes the oracle state `s`
(rather than sampling it from an `init`) because the intended use is *inside* an outer game
bound (e.g. the tail hypothesis of
`probEvent_optionT_simulateQ_addLift_getChallenge_first_bind_le_convex`), where the state has
already been fixed; recover the `init`-sampled form with `probEvent_bind_le_of_forall_le`.

(Intended outer bound: the tail hypothesis of
`probEvent_optionT_simulateQ_addLift_getChallenge_first_bind_le_convex`.) -/
theorem probEvent_optionT_simulateQ_addLift_prefix_getChallenge_bind_le
    {P T β : Type}
    (s : σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (oa : OracleComp (oSpec + [pSpec.Challenge]ₒ) (Option β)) (i : pSpec.ChallengeIdx)
    (mid : OracleComp (oSpec + [pSpec.Challenge]ₒ) P)
    (tail : P → pSpec.Challenge i → OracleComp (oSpec + [pSpec.Challenge]ₒ) T)
    (f : P → pSpec.Challenge i → T → Option β) (E : β → Prop) {ε : ℝ≥0∞}
    (hoa : oa = do
      let pre ← mid
      let c ← liftComp (pSpec.getChallenge i) (oSpec + [pSpec.Challenge]ₒ)
      (f pre c) <$> tail pre c)
    (h : ∀ pre : P,
      Pr[ fun c ↦ ∃ t b, f pre c t = some b ∧ E b | $ᵗ (pSpec.Challenge i)] ≤ ε) :
    Pr[ E | OptionT.mk
      ((simulateQ (impl.addLift challengeQueryImpl : QueryImpl _ (StateT σ ProbComp))
        oa).run' s)] ≤ ε := by
  subst hoa
  -- Split off the simulated prefix, then resolve the challenge query, per initial state.
  have hbody : ∀ s : σ,
      (simulateQ (impl.addLift challengeQueryImpl : QueryImpl _ (StateT σ ProbComp))
        (do
          let pre ← mid
          let c ← liftComp (pSpec.getChallenge i) (oSpec + [pSpec.Challenge]ₒ)
          (f pre c) <$> tail pre c)).run' s
      = (simulateQ (impl.addLift challengeQueryImpl : QueryImpl _ (StateT σ ProbComp))
          mid).run s >>= fun x ↦
          ($ᵗ (pSpec.Challenge i)) >>= fun c ↦
            (f x.1 c) <$>
              ((simulateQ (impl.addLift challengeQueryImpl : QueryImpl _ (StateT σ ProbComp))
                (tail x.1 c)).run' x.2) := by
    intro s
    rw [simulateQ_bind, StateT.run'_bind']
    refine bind_congr fun x ↦ ?_
    -- The per-prefix equality, with the prefix value and state as plain variables (the
    -- `StateT.run'_bind'` match-lambda is defeq to its projection spelling but not
    -- `rw`-matchable; `exact … x.1 x.2` bridges by definitional unification).
    have hx : ∀ (pre : P) (s' : σ),
        (simulateQ (impl.addLift challengeQueryImpl : QueryImpl _ (StateT σ ProbComp))
          (do
            let c ← liftComp (pSpec.getChallenge i) (oSpec + [pSpec.Challenge]ₒ)
            (f pre c) <$> tail pre c)).run' s'
        = ($ᵗ (pSpec.Challenge i)) >>= fun c ↦
            (f pre c) <$>
              ((simulateQ (impl.addLift challengeQueryImpl : QueryImpl _ (StateT σ ProbComp))
                (tail pre c)).run' s') := by
      intro pre s'
      rw [simulateQ_bind, simulateQ_addLift_challengeQueryImpl_getChallenge,
        StateT.run'_bind']
      simp only [StateT.run_liftM, bind_assoc, pure_bind, simulateQ_map, StateT.run'_map']
    exact hx x.1 x.2
  rw [hbody s, OptionT.mk_bind]
  refine probEvent_bind_le_of_forall_le fun x _ ↦ ?_
  rw [OptionT.mk_bind]
  refine le_trans (probEvent_bind_le_probEvent
    (p := fun c ↦ ∃ t b, f x.1 c t = some b ∧ E b) ?_)
    (le_trans (le_of_eq (OptionT.probEvent_liftM _ _)) (h x.1))
  intro c _ hc
  refine probEvent_eq_zero fun z hz hE ↦ hc ?_
  rw [OptionT.mem_support_iff, OptionT.run_mk, support_map, Set.mem_image] at hz
  obtain ⟨t, _, htz⟩ := hz
  exact ⟨t, z, htz, hE⟩

/-- The two algebraically-equal spellings of a convex combination `λ·1 + (1−λ)·ε` in `ℝ≥0∞`,
for `λ, ε ≤ 1`. Used to turn the `λ + (1−λ)·ε` shape produced by
`probEvent_bind_le_probEvent_convex` into the monotone-in-`λ` shape `ε + λ·(1−ε)`. -/
private lemma enn_convex_symm (a ε : ℝ≥0∞) (ha : a ≤ 1) (hε : ε ≤ 1) :
    a + (1 - a) * ε = ε + a * (1 - ε) := by
  have ha' : a ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top ha
  have hε' : ε ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hε
  have hsub_a : (1 : ℝ≥0∞) - a ≠ ⊤ := ENNReal.sub_ne_top ENNReal.one_ne_top
  have hsub_ε : (1 : ℝ≥0∞) - ε ≠ ⊤ := ENNReal.sub_ne_top ENNReal.one_ne_top
  rw [← ENNReal.toReal_eq_toReal_iff'
        (ENNReal.add_ne_top.mpr ⟨ha', ENNReal.mul_ne_top hsub_a hε'⟩)
        (ENNReal.add_ne_top.mpr ⟨hε', ENNReal.mul_ne_top ha' hsub_ε⟩),
    ENNReal.toReal_add ha' (ENNReal.mul_ne_top hsub_a hε'),
    ENNReal.toReal_add hε' (ENNReal.mul_ne_top ha' hsub_ε),
    ENNReal.toReal_mul, ENNReal.toReal_mul,
    ENNReal.toReal_sub_of_le ha ENNReal.one_ne_top,
    ENNReal.toReal_sub_of_le hε ENNReal.one_ne_top, ENNReal.toReal_one]
  ring

/-- **Convex master bound for a challenge-first game.** For a game whose `Option`-valued
computation starts with a fresh challenge draw and continues with an arbitrary (adversarial,
possibly further-sampling) tail, the game probability is at most the convex combination
`ε₂ + ε₁·(1 − ε₂)`, where `ε₁` bounds a challenge-only prefix event `p` and `ε₂` bounds the
tail game on every challenge *off* `p` — the off-prefix tail bound `ε₂` is charged on the full
mass, and the prefix bound `ε₁` only on the remaining `(1 − ε₂)` fraction. Requires `ε₂ ≤ 1`.
Dropping the `(1 − ε₂) ≤ 1` factor recovers the additive bound `ε₂ + ε₁`, so this is sharper
by exactly `ε₁·ε₂`. Engine of *convex-form* knowledge-soundness errors. -/
theorem probEvent_optionT_simulateQ_addLift_getChallenge_first_bind_le_convex
    {β : Type}
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (oa : OracleComp (oSpec + [pSpec.Challenge]ₒ) (Option β)) (i : pSpec.ChallengeIdx)
    (tail : pSpec.Challenge i → OracleComp (oSpec + [pSpec.Challenge]ₒ) (Option β))
    (E : β → Prop) (p : pSpec.Challenge i → Prop) {ε₁ ε₂ : ℝ≥0∞}
    (hε₂ : ε₂ ≤ 1)
    (hoa : oa = do
      let c ← liftComp (pSpec.getChallenge i) (oSpec + [pSpec.Challenge]ₒ)
      tail c)
    (h₁ : Pr[ p | $ᵗ (pSpec.Challenge i)] ≤ ε₁)
    (h₂ : ∀ c, ¬ p c → ∀ s : σ,
      Pr[ E | OptionT.mk
        ((simulateQ (impl.addLift challengeQueryImpl : QueryImpl _ (StateT σ ProbComp))
          (tail c)).run' s)] ≤ ε₂) :
    Pr[ E | OptionT.mk (do
      (simulateQ (impl.addLift challengeQueryImpl : QueryImpl _ (StateT σ ProbComp))
        oa).run' (← init))] ≤ ε₂ + ε₁ * (1 - ε₂) := by
  subst hoa
  have hbody : ∀ s : σ,
      (simulateQ (impl.addLift challengeQueryImpl : QueryImpl _ (StateT σ ProbComp))
        (do
          let c ← liftComp (pSpec.getChallenge i) (oSpec + [pSpec.Challenge]ₒ)
          tail c)).run' s
      = ($ᵗ (pSpec.Challenge i)) >>= fun c ↦
          (simulateQ (impl.addLift challengeQueryImpl : QueryImpl _ (StateT σ ProbComp))
            (tail c)).run' s := by
    intro s
    rw [simulateQ_bind, simulateQ_addLift_challengeQueryImpl_getChallenge,
      StateT.run'_bind']
    simp only [StateT.run_liftM, bind_assoc, pure_bind]
  rw [OptionT.mk_bind]
  refine probEvent_bind_le_of_forall_le fun s _ ↦ ?_
  rw [hbody s, OptionT.mk_bind]
  -- Convex per-challenge split, then bound `Pr[p]` by `ε₁` inside the monotone-in-`Pr[p]` shape.
  refine le_trans (probEvent_bind_le_probEvent_convex (p := p) fun c _ hc ↦ h₂ c hc s) ?_
  rw [enn_convex_symm _ _ probEvent_le_one hε₂]
  exact add_le_add le_rfl (mul_le_mul' (le_trans (le_of_eq (OptionT.probEvent_liftM _ _)) h₁)
    le_rfl)

end ProtocolSpec

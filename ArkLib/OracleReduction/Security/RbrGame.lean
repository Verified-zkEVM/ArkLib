/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/
module

public import ArkLib.OracleReduction.ProtocolSpec.Basic
public import ArkLib.Data.Probability.Instances
public import VCVio.OracleComp.QueryTracking.LoggingOracle.Core
public import VCVio.EvalDist.Monad.Branch
public import VCVio.OracleComp.Constructions.SampleableType.Measure

/-!
# `ProtocolSpec` glue for security games

This file resolves simulated challenge queries into uniform draws and provides bounds for the
`OptionT` knowledge-soundness game. The latter draws a challenge before an arbitrary adversarial
continuation, possibly after an earlier prefix. The probabilistic bind-event inequalities live
upstream in VCVio; these lemmas provide their `ProtocolSpec` specializations.
-/

@[expose] public section

open OracleComp OracleSpec ProtocolSpec ProbabilityTheory
open scoped ENNReal
open Probability

namespace ProtocolSpec

variable {n : ℕ} {pSpec : ProtocolSpec n} [∀ j, SampleableType (pSpec.Challenge j)]
  {ι : Type} {oSpec : OracleSpec ι} {σ : Type}

/-- **Challenge-query resolution for security games.** Simulating the lifted challenge query
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

end ProtocolSpec

/-! ## Knowledge-soundness game glue

The knowledge-soundness game (`Verifier.knowledgeSoundness`,
`ArkLib/OracleReduction/Security/Basic.lean`) is `Option`-valued because reduction execution may
fail. For a verifier-first protocol the challenge is drawn before the adversarial continuation,
which comprises the prover's remaining moves and the verifier/extractor projections.

The underlying probabilistic steps — the "zero off the challenge event" monotonicity step and
its additive and convex prefix-split sharpenings (`prEvent_bind_le_prEvent_of_forall_eq_zero`,
`prEvent_bind_le_prEvent_add`, `prEvent_bind_le_prEvent_add_mul_prEvent_not`) — live upstream in
VCVio (`VCVio/EvalDist/Monad/Basic.lean`). What follows is the ArkLib-specific `ProtocolSpec`
glue built on top of them.

The master bound for this shape is
`ProtocolSpec.prEvent_optionT_simulateQ_addLift_getChallenge_bind_some_le`. It consumes a
challenge-only probability bound `Pr{let c ← $ᵗ _}[∃ t, E (f c t)] ≤ ε`, where the `∃ t`
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
theorem prEvent_optionT_simulateQ_addLift_getChallenge_bind_some_le
    {T β : Type}
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (oa : OracleComp (oSpec + [pSpec.Challenge]ₒ) (Option β)) (i : pSpec.ChallengeIdx)
    (tail : pSpec.Challenge i → OracleComp (oSpec + [pSpec.Challenge]ₒ) T)
    (f : pSpec.Challenge i → T → β) (E : β → Prop) {ε : ℝ≥0∞}
    (hoa : oa = do
      let c ← liftComp (pSpec.getChallenge i) (oSpec + [pSpec.Challenge]ₒ)
      (fun t ↦ some (f c t)) <$> tail c)
    (h : Pr{let c ← $ᵗ (pSpec.Challenge i)}[∃ t, E (f c t)] ≤ ε) :
    Pr{let x ← (OptionT.mk (do
      (simulateQ (impl.addLift challengeQueryImpl : QueryImpl _ (StateT σ ProbComp))
        oa).run' (← init)))}[E x] ≤ ε := by
  subst hoa
  rw [OptionT.mk_bind]
  refine prEvent_bind_le_of_forall_le _ _ E fun s ↦ ?_
  simp only [simulateQ_bind, simulateQ_addLift_challengeQueryImpl_getChallenge, StateT.run'_bind',
    StateT.run_liftM, bind_assoc, pure_bind, simulateQ_map, StateT.run'_map']
  rw [OptionT.mk_bind]
  refine (prEvent_bind_le_prEvent_of_support _ _ (fun c ↦ ∃ t, E (f c t)) E fun c _ hc ↦ ?_).trans
    ((OptionT.prEvent_lift _ _).trans_le h)
  rw [OptionT.prEvent_mk_eq_zero_iff]
  simp only [support_map, Set.mem_image, Option.some_inj]
  rintro _ ⟨t, _, rfl⟩ hE
  exact hc ⟨t, hE⟩

/-- **Prefix-extended, `Option`-valued master mixture bound for the knowledge-soundness game
shape.** Generalizes `prEvent_optionT_simulateQ_addLift_getChallenge_bind_some_le` in two
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
`prEvent_optionT_simulateQ_addLift_getChallenge_first_bind_le_convex`), where the state has
already been fixed; recover the `init`-sampled form with `prEvent_bind_le_of_forall_le`.

(Intended outer bound: the tail hypothesis of
`prEvent_optionT_simulateQ_addLift_getChallenge_first_bind_le_convex`.) -/
theorem prEvent_optionT_simulateQ_addLift_prefix_getChallenge_bind_le
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
      Pr{let c ← $ᵗ (pSpec.Challenge i)}[∃ t b, f pre c t = some b ∧ E b] ≤ ε) :
    Pr{let x ← (OptionT.mk
      ((simulateQ (impl.addLift challengeQueryImpl : QueryImpl _ (StateT σ ProbComp))
        oa).run' s))}[E x] ≤ ε := by
  subst hoa
  rw [simulateQ_bind, StateT.run'_bind', OptionT.mk_bind]
  refine prEvent_bind_le_of_forall_le _ _ E fun ⟨pre, s'⟩ ↦ ?_
  simp only [simulateQ_bind, simulateQ_addLift_challengeQueryImpl_getChallenge, StateT.run'_bind',
    StateT.run_liftM, bind_assoc, pure_bind, simulateQ_map, StateT.run'_map']
  rw [OptionT.mk_bind]
  refine (prEvent_bind_le_prEvent_of_support _ _ (fun c ↦ ∃ t b, f pre c t = some b ∧ E b) E
    fun c _ hc ↦ ?_).trans ((OptionT.prEvent_lift _ _).trans_le (h pre))
  rw [OptionT.prEvent_mk_eq_zero_iff]
  simp only [support_map, Set.mem_image]
  rintro z ⟨t, _, htz⟩ hE
  exact hc ⟨t, z, htz, hE⟩

/-- The two algebraically-equal spellings of a convex combination `λ·1 + (1−λ)·ε` in `ℝ≥0∞`,
for `λ, ε ≤ 1`. Used to turn the `λ + (1−λ)·ε` shape produced by
`prEvent_bind_le_prEvent_add_mul_prEvent_not` into the monotone-in-`λ` shape
`ε + λ·(1−ε)`. -/
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
theorem prEvent_optionT_simulateQ_addLift_getChallenge_first_bind_le_convex
    {β : Type}
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (oa : OracleComp (oSpec + [pSpec.Challenge]ₒ) (Option β)) (i : pSpec.ChallengeIdx)
    (tail : pSpec.Challenge i → OracleComp (oSpec + [pSpec.Challenge]ₒ) (Option β))
    (E : β → Prop) (p : pSpec.Challenge i → Prop) {ε₁ ε₂ : ℝ≥0∞}
    (hε₂ : ε₂ ≤ 1)
    (hoa : oa = do
      let c ← liftComp (pSpec.getChallenge i) (oSpec + [pSpec.Challenge]ₒ)
      tail c)
    (h₁ : Pr{let c ← $ᵗ (pSpec.Challenge i)}[p c] ≤ ε₁)
    (h₂ : ∀ c, ¬ p c → ∀ s : σ,
      Pr{let x ← (OptionT.mk
        ((simulateQ (impl.addLift challengeQueryImpl : QueryImpl _ (StateT σ ProbComp))
          (tail c)).run' s))}[E x] ≤ ε₂) :
    Pr{let x ← (OptionT.mk (do
      (simulateQ (impl.addLift challengeQueryImpl : QueryImpl _ (StateT σ ProbComp))
        oa).run' (← init)))}[E x] ≤ ε₂ + ε₁ * (1 - ε₂) := by
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
  refine prEvent_bind_le_of_forall_le _ _ E fun s ↦ ?_
  rw [hbody s, OptionT.mk_bind]
  refine (prEvent_bind_le_prEvent_add_mul_prEvent_not _ _ p E fun c hc ↦ h₂ c hc s).trans ?_
  change Pr{let c ← OptionT.lift ($ᵗ (pSpec.Challenge i))}[p c] + ε₂ *
      Pr{let c ← OptionT.lift ($ᵗ (pSpec.Challenge i))}[¬ p c] ≤ ε₂ + ε₁ * (1 - ε₂)
  simp only [OptionT.prEvent_lift]
  have hnot : Pr{let c ← $ᵗ (pSpec.Challenge i)}[¬ p c] =
      1 - Pr{let c ← $ᵗ (pSpec.Challenge i)}[p c] := by
    let _ : MeasurableSpace (pSpec.Challenge i) := ⊤
    refine ENNReal.eq_sub_of_add_eq' ENNReal.one_ne_top ((add_comm _ _).trans ?_)
    rw [prEvent_add_prEvent_not, evalDist_map_apply_univ _ Measurable.of_discrete,
      SampleableType.evalDist_uniformSample, MeasureTheory.measure_univ]
  rw [hnot, mul_comm ε₂, enn_convex_symm _ _ (prEvent_le_one _) hε₂]
  exact add_le_add le_rfl (mul_le_mul' h₁ le_rfl)

end ProtocolSpec

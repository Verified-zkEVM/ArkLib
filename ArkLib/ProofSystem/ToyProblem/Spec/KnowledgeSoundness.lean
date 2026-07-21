/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

import ArkLib.ProofSystem.ToyProblem.Spec.General

/-!
# Knowledge soundness of the toy-problem IOR (ABF26 Lemma 6.6, corrected)

Plain (straightline) knowledge soundness of Construction 6.2
(`protocol62_knowledgeSound`), against the relaxed relation `R̃²_{C,δ}`.

## The error term: the paper's sum, tightened to a convex combination

[ABF26] Lemma 6.6 (current `.tex` @ `53a5055`, the `lem:toysoudness` statement at
L2259–2264) states the knowledge error as the **sum**

  `ε_mca(C,δ) + |Λ(C^{≡2},δ)|/|F| + (1−δ)^t`.

Writing `ε₀ := ε_mca(C,δ) + |Λ(C^{≡2},δ)|/|F|`, this file proves the slightly
tighter **convex/union combination**

  `(1−δ)^t + ε₀·(1 − (1−δ)^t)`,

which is `≤` the paper's sum (smaller by `ε₀·(1−δ)^t`), so it is at least as
strong as Lemma 6.6 and matches what the generic round-by-round → plain
implication yields from the L6.8 round errors `(ε₀, (1−δ)^t)`.

Historical note: an earlier draft instead printed `max{ε₀, (1−δ)^t}`, which is
unsound — its proof drops the conditioning on `Δ ≤ δ`, and exact codewords with
off-by-one linear targets give a bad event of probability `≥ 1/|F|` that the
`max` undershoots once `ε₀, (1−δ)^t < 1/|F|`. This was independently verified,
author-confirmed, and corrected to the sum above; we record it so the deviation
from older copies of the paper is not mistaken for a formalization gap.

## Proof structure

The proof is a two-level prefix split over the 3-round game, using the
generic machinery of `ArkLib/ToVCVio/OracleComp/RbrGame.lean`:

* The straightline extractor is the always-`some` classical choice
  `Spec.extractZero` (shared with L6.8/L6.10) — under the post-PR-#569
  game, extraction failure scores against the prover, and the choice
  extractor succeeds whenever *any* relaxed witness exists, so the game
  event forces "no witness exists".
* `verifier_run_loggingOracle_eq` collapses the (logged) oracle verifier on
  an arbitrary transcript to a `pure` `if accepts … then … else none`
  (via `verifierBody_simulateQ_eq_pure_ite`).
* The game then has the challenge-first shape consumed by
  `ProtocolSpec.probEvent_optionT_simulateQ_addLift_getChallenge_first_bind_le_add`
  (round-0 challenge `γ`), with prefix event "some message satisfies the
  post-γ state `gammaState` while extraction fails", bounded by
  `gamma_round_game_bound` (the MCA + list-decoding term).
* Off the prefix event, the remaining 2-round tail is bounded via
  `ProtocolSpec.probEvent_optionT_simulateQ_addLift_prefix_getChallenge_bind_le`
  (round-2 challenge `xs`), per-prefix bound `spotcheck_round_game_bound`
  (the `(1−δ)^t` term).

## References

* [Arnon, G., Boneh, D., Fenzi, G., *Open Problems in List Decoding and
  Correlated Agreement*][ABF26] (§6.2, Lemma 6.6 — error term corrected,
  see above).
-/

namespace ToyProblem

namespace Spec

open OracleSpec OracleComp ProtocolSpec
open Code InterleavedCode ListDecodable ProximityGap
open scoped NNReal ENNReal

-- The code-theoretic terms (`epsMCA`, `interleavedCodeSet`) use `[Fintype A]`/`[DecidableEq A]`
-- in their bodies but not in the alphabet-generic lemma types; suppress the `unused…InType`
-- linter file-wide (the same toy idiom as `SoundnessBounds.lean` / `Spec/General.lean`).
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

variable {ι F A : Type} [Fintype ι] [Field F] [Fintype F] [DecidableEq F]
variable [AddCommGroup A] [Module F A] [Fintype A] [DecidableEq A]
variable (k t : ℕ)

section Protocol

omit [Fintype ι] [Fintype F] [Fintype A] in
/-- The (logged) run of the C6.2 oracle verifier on an arbitrary transcript collapses to the
deterministic `pure` of "`some` output iff the §6.1 acceptance predicate holds", with an empty
verifier query log. Packages `verifierBody_simulateQ_eq_pure_ite` together with the
`toVerifier` output wrapper and the logging layer, so the L6.6 game reduction can rewrite the
verifier away in one step (under the prover-run binders, where the transcript is abstract). -/
private lemma verifier_run_loggingOracle_eq
    (encode : (Fin k → F) → (ι → A))
    (stmt : Statement (F := F) k) (oStmt : ∀ i, OracleStatement ι A i)
    (tr : (pSpec (ι := ι) (F := F) k t).FullTranscript) :
    (simulateQ loggingOracle
        ((oracleVerifier (k := k) (t := t) encode).toVerifier.run (stmt, oStmt) tr)).run
      = pure ((if accepts (k := k) (t := t) encode stmt oStmt
            (tr.challenges ⟨0, rfl⟩) (tr.messages ⟨1, rfl⟩)
            (tr.challenges ⟨2, rfl⟩)
          then some (((), nofun) :
            OutputStatement × ∀ i, OutputOracleStatement i) else none), ∅) := by
  classical
  simp only [Verifier.run, OracleVerifier.toVerifier, oracleVerifier]
  simp only [bind_pure_comp]
  rw [verifierBody_simulateQ_eq_pure_ite (k := k) (t := t) encode oStmt tr.messages
    stmt.1 stmt.2.1 stmt.2.2 (tr.challenges ⟨⟨0, by norm_num⟩, rfl⟩)
    (tr.challenges ⟨⟨2, by norm_num⟩, rfl⟩)]
  -- The `OptionT`-mapped output wrapper over a `pure` body, logged, is a `pure` with empty
  -- log — with the wrapper function abstract, so the `embed`-match term need not be spelled.
  have hmap : ∀ (fn : Unit → OutputStatement × ∀ i, OutputOracleStatement i)
      (o : Option Unit),
      (simulateQ loggingOracle
        ((fn <$> (show OptionT (OracleComp []ₒ) Unit from
            (pure o : OracleComp []ₒ (Option Unit))) :
          OptionT (OracleComp []ₒ) (OutputStatement × ∀ i, OutputOracleStatement i)) :
          OracleComp []ₒ (Option (OutputStatement × ∀ i, OutputOracleStatement i)))).run
        = pure (o.map fn, ∅) := by
    intro fn o
    cases o with
    | none =>
        rw [show ((fn <$> (show OptionT (OracleComp []ₒ) Unit from
            (pure none : OracleComp []ₒ (Option Unit))) :
            OptionT (OracleComp []ₒ) (OutputStatement × ∀ i, OutputOracleStatement i)) :
            OracleComp []ₒ (Option (OutputStatement × ∀ i, OutputOracleStatement i)))
          = (pure none : OracleComp []ₒ
              (Option (OutputStatement × ∀ i, OutputOracleStatement i))) from rfl,
          simulateQ_pure]
        rfl
    | some u =>
        rw [show ((fn <$> (show OptionT (OracleComp []ₒ) Unit from
            (pure (some u) : OracleComp []ₒ (Option Unit))) :
            OptionT (OracleComp []ₒ) (OutputStatement × ∀ i, OutputOracleStatement i)) :
            OracleComp []ₒ (Option (OutputStatement × ∀ i, OutputOracleStatement i)))
          = (pure (some (fn u)) : OracleComp []ₒ
              (Option (OutputStatement × ∀ i, OutputOracleStatement i))) from rfl,
          simulateQ_pure]
        rfl
  rw [hmap]
  split <;> rename_i h
  · rw [if_pos (show accepts (k := k) (t := t) encode stmt oStmt (tr.challenges ⟨0, rfl⟩)
      (tr.messages ⟨1, rfl⟩) (tr.challenges ⟨2, rfl⟩) from h)]
    rw [Option.map_some]
    refine congrArg pure (congrArg (·, ∅) (congrArg some (congrArg (Prod.mk ()) ?_)))
    funext i
    exact i.elim0
  · rw [if_neg (fun hacc : accepts (k := k) (t := t) encode stmt oStmt
        (tr.challenges ⟨0, rfl⟩) (tr.messages ⟨1, rfl⟩) (tr.challenges ⟨2, rfl⟩) ↦ h hacc),
      Option.map_none]

omit [Fintype ι] [Field F] [Fintype F] [DecidableEq F]
  [AddCommGroup A] [Module F A] [Fintype A] [DecidableEq A] in
/-- **Challenge-first normal form of the (mapped) toy 3-round prover run.** For the
verifier-first (`V_to_P` / `P_to_V` / `V_to_P`) `pSpec`, post-composing `Prover.run` with any
`post` that reads the transcript only through its round-0/2 challenges and round-1 message
equals the explicit challenge-first `do`-block: draw `γ`, receive it, send the round-1 message,
draw the spot checks `xs`, receive them, output, and apply `post` to `(γ, msg, xs, out)`.

This isolates two purely definitional facts bundled together: (i) the monad-law flattening of
the `Fin.induction`/`processRound` bind tree — whose leading `pure (default, prover.input …)`
base resists `simp [pure_bind]` due to the dependent `Fin`-index types on the prover state —
and (ii) the reduction of the assembled `Transcript.concat`/`Fin.snoc` accessors
(`.challenges ⟨0⟩ = γ`, `.messages ⟨1⟩ = msg`, `.challenges ⟨2⟩ = xs`). With it, the L6.6
game-shape equation (`case hC` of `protocol62_knowledgeSound`'s `hoa`) is a one-line
instantiation. Reusable across any soundness/completeness argument over this `pSpec`. -/
private lemma prover_run_map_eq {β : Type}
    (prover : Prover []ₒ
      (Statement (F := F) k × (∀ i, OracleStatement ι A i)) (Witness (F := F) k)
      (OutputStatement × ∀ i, OutputOracleStatement i) OutputWitness
      (pSpec (ι := ι) (F := F) k t))
    (stmt : Statement (F := F) k × (∀ i, OracleStatement ι A i)) (witIn : Witness (F := F) k)
    (post : F → (Fin k → F) → (Fin t → ι) →
      ((OutputStatement × ∀ i, OutputOracleStatement i) × OutputWitness) → β) :
    (fun r ↦ post (r.1.challenges ⟨0, rfl⟩) (r.1.messages ⟨1, rfl⟩) (r.1.challenges ⟨2, rfl⟩) r.2)
        <$> Prover.run stmt witIn prover
      = (do
      let c ← liftComp ((pSpec (ι := ι) (F := F) k t).getChallenge ⟨0, rfl⟩)
        ([]ₒ + [(pSpec (ι := ι) (F := F) k t).Challenge]ₒ)
      let f0 ← liftComp (prover.receiveChallenge ⟨0, rfl⟩ (prover.input (stmt, witIn)))
        ([]ₒ + [(pSpec (ι := ι) (F := F) k t).Challenge]ₒ)
      let pre ← liftComp (prover.sendMessage ⟨1, rfl⟩ (f0 c))
        ([]ₒ + [(pSpec (ι := ι) (F := F) k t).Challenge]ₒ)
      let xs ← liftComp ((pSpec (ι := ι) (F := F) k t).getChallenge ⟨2, rfl⟩)
        ([]ₒ + [(pSpec (ι := ι) (F := F) k t).Challenge]ₒ)
      let f2 ← liftComp (prover.receiveChallenge ⟨2, rfl⟩ pre.2)
        ([]ₒ + [(pSpec (ι := ι) (F := F) k t).Challenge]ₒ)
      let out ← liftComp (prover.output (f2 xs))
        ([]ₒ + [(pSpec (ι := ι) (F := F) k t).Challenge]ₒ)
      pure (post c pre.1 xs out)) := by
  -- Resolve the three round directions *once* via the framework-level per-direction unfolds of
  -- `Prover.processRound` (`processRound_of_dir_eq_{V_to_P,P_to_V}`), instead of re-deriving the
  -- dependent `match`/index split by hand. With the direction `match`es gone, `Fin.induction_three`
  -- exposes the run as the three challenge-first `do`-blocks directly.
  have h0 : (pSpec (ι := ι) (F := F) k t).dir 0 = .V_to_P := rfl
  have h1 : (pSpec (ι := ι) (F := F) k t).dir 1 = .P_to_V := rfl
  have h2 : (pSpec (ι := ι) (F := F) k t).dir 2 = .V_to_P := rfl
  -- Unfold the run and resolve all three round directions in one shot via the framework-level
  -- per-direction `processRound` unfolds, then flatten the resulting `do`-blocks to the
  -- challenge-first form. Note: because each `processRound` already emits a concrete `do`-block,
  -- the cross-round `Fin`-index alignment (`(0).succ` vs `(1).castSucc`, …) collapses under a
  -- single `dsimp` of the `Fin`-operation heads — none of the old per-index `show … = … from rfl`
  -- casts are needed any more.
  simp only [Prover.run, Prover.runToRound, Fin.induction_three,
    Prover.processRound_of_dir_eq_V_to_P 0 h0, Prover.processRound_of_dir_eq_P_to_V 1 h1,
    Prover.processRound_of_dir_eq_V_to_P 2 h2,
    map_eq_bind_pure_comp, bind_assoc, liftComp_eq_liftM, pure_bind, Function.comp,
    Fin.castSucc_zero', Fin.isValue]
  dsimp only [Fin.succ, Fin.castSucc, Fin.castAdd, Fin.castLE, Fin.castLT, Fin.last]
  -- Expose canonical `OracleComp` binds (unfold the `monadLift`/`liftM` internals), finish
  -- flattening, and reduce the assembled `Fin.snoc` transcript read-backs (`challenge[0] = c`,
  -- `message[1] = pre.1`, `challenge[2] = xs`). The residual identity `cast`s from `Fin.snoc`'s
  -- dependent eliminator are defeq, closed by `rfl`.
  simp only [MonadLift.monadLift, liftM, monadLift, MonadLiftT.monadLift, pure_bind, bind_assoc,
    FullTranscript.challenges, FullTranscript.messages, Transcript.concat, Fin.snoc,
    Fin.val_zero, Fin.val_one, Fin.val_two, lt_self_iff_false, Fin.val_castLT,
    Fin.castSucc_castLT, show (0 : ℕ) < 2 from by norm_num, show (0 : ℕ) < 1 from by norm_num,
    show (1 : ℕ) < 2 from by norm_num, show ¬ ((2 : ℕ) < 0) from by norm_num,
    dif_pos, cast_eq, dite_false]
  rfl

/-- **Lemma 6.6 of [ABF26], corrected** (knowledge soundness of Construction 6.2).

For any `δ ∈ (0, δ_min(C))` and fixed injective linear encoder with
range `C` (injectivity is implicit in the paper's encoding map and
load-bearing for the extractor's per-list-pair counting),
the toy-problem IOR has knowledge soundness against the relaxed relation
`R̃_{C,δ}^2` with the **convex-combination** error

  `(1 − δ)^t + ε₀ · (1 − (1 − δ)^t)`,    where `ε₀ := ε_mca(C, δ) + |Λ(C^{≡2}, δ)| / |F|`.

This is `≤` the sum `ε₀ + (1 − δ)^t` stated in [ABF26] Lemma 6.6 (current
`.tex` @ `53a5055`, `lem:toysoudness` L2259–2264), so it is at least as strong as
the paper's bound. (An
earlier draft printed the unsound `max{ε₀, (1 − δ)^t}`; it was author-confirmed
and corrected to the sum. See this file's module docstring for the full
analysis.)

**Why the convex form, and how it relates to the natural sum.** The honest
total-probability accounting over the combination randomness `γ` is
`Pr_γ[p]·1 + (1 − Pr_γ[p])·(1 − δ)^t` where `p` is the bad-`γ` prefix event
(`Pr_γ[p] ≤ ε₀`): on `p` (mass `≤ ε₀`) the prover can pass every spot-check
with probability up to `1`, so that branch is paid in full; off `p` the fold
is `δ`-far, so spot-checks pass with probability `≤ (1 − δ)^t`. Monotonicity
in `Pr_γ[p]` (since `(1 − δ)^t ≤ 1`) gives the closed form above. Dropping
the `(1 − (1 − δ)^t) ≤ 1` factor yields the *natural sum form*
`ε₀ + (1 − δ)^t` — the L6.8 round-error sum — at additive cost exactly
`ε₀·(1 − δ)^t` (a second-order term; negligible in the prize regime).

The `(Lambda …).toNat` in `ε₀` is faithful: `Lambda` is never `⊤` over a
finite alphabet (`ListDecodable.Lambda_ne_top`), so `toNat` loses nothing.

Stated against ArkLib's `OracleVerifier.knowledgeSoundness` (cf.
`OracleReduction/Security/Basic.lean :: OracleVerifier.knowledgeSoundness`,
definitionally `toVerifier.knowledgeSoundness`) — the faithful object
for an IOPP whose inputs `f₁, f₂` are oracles.

**Naming convention — paper vs API.** The ArkLib API's
`OracleVerifier.knowledgeSoundness` takes `(relIn, relOut)` where `relIn`
is the relation the extracted witness satisfies and `relOut` is the
relation the verifier's output must satisfy. In this file `relIn` is
*our* `outputRelationFor` (paper's `R̃²_{C,δ}`, checked against the
messages returned by the extractor) and `relOut` is `Set.univ` (paper's
C6.2 has trivial output `Unit`). The name `outputRelationFor` reflects
the **paper's** "this is the protocol's output relation" perspective; do
not be misled by the API parameter named `relIn`.

The straightline extractor is the always-`some` classical choice
`extractZero` (stmtIn-only; shared with L6.8/L6.10): under the
post-PR-#569 game extraction failure scores against the prover, and the
choice extractor succeeds whenever *any* relaxed witness exists, so the
game event forces "no relaxed witness exists" and the bound reduces to
the two-round prefix split described in the module docstring.

The paper's extraction-time claim (`O(enc + ecor)`) is not modeled:
ArkLib has no cost semantics, so this theorem carries only the error
bound. -/
theorem protocol62_knowledgeSound
    [SampleableType F] [SampleableType ι] [Nonempty ι]
    {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl []ₒ (StateT σ ProbComp))
    (C : Set (ι → A)) (δ : ℝ≥0)
    (encode : (Fin k → F) →ₗ[F] (ι → A))
    (hinj : Function.Injective encode)
    (hC : Set.range encode = C)
    (hδ_pos : 0 < δ)
    (hδ_lt_min : δ < (minRelHammingDistCode C : ℝ≥0)) :
      (oracleVerifier (k := k) (t := t) (encode : (Fin k → F) → (ι → A))).knowledgeSoundness
        (WitOut := OutputWitness)
        init impl (outputRelationFor k (encode : (Fin k → F) → (ι → A)) δ)
        (Set.univ : Set ((OutputStatement × ∀ i, OutputOracleStatement i) ×
          OutputWitness))
        ((1 - δ) ^ t +
          ((epsMCA (F := F) (A := A) C δ).toNNReal +
              ((Lambda (interleavedCodeSet (κ := Fin 2) C) (δ : ℝ)).toNat : ℝ≥0)
                / (Fintype.card F : ℝ≥0))
            * (1 - (1 - δ) ^ t)) := by
  classical
  unfold OracleVerifier.knowledgeSoundness Verifier.knowledgeSoundness
  -- The straightline extractor: classical choice of any `R̃²` witness, from the input
  -- statement alone (always-`some`; cf. `Spec.extractZero`).
  refine ⟨fun stmtIn _ _ _ _ ↦
    pure (extractZero k ((encode : (Fin k → F) → (ι → A))) δ stmtIn), ?_⟩
  rintro ⟨stmt, oStmt⟩ witIn prover
  -- Push the `ℝ≥0 → ℝ≥0∞` coercion through the convex combination so it matches the
  -- `ε₂ + ε₁·(1 − ε₂)` shape produced by the convex master lemma (ε₂ = (1−δ)^t, ε₁ = ε₀).
  rw [ENNReal.coe_add, ENNReal.coe_mul, ENNReal.coe_sub, ENNReal.coe_one]
  -- Outer split at the leading γ-draw (C6.2 is verifier-first): prefix event = "extraction
  -- fails yet some message satisfies the post-γ state", tail = the remaining two rounds.
  refine ProtocolSpec.probEvent_optionT_simulateQ_addLift_getChallenge_first_bind_le_convex
    (ε₂ := (((1 - δ) ^ t : ℝ≥0) : ℝ≥0∞))
    init impl _ ⟨0, rfl⟩
    (fun γ ↦ do
      let pre ← (liftComp (prover.receiveChallenge ⟨0, rfl⟩
            (prover.input ((stmt, oStmt), witIn)))
            ([]ₒ + [(pSpec (ι := ι) (F := F) k t).Challenge]ₒ)) >>= fun fc ↦
          liftComp (prover.sendMessage ⟨1, rfl⟩ (fc γ))
            ([]ₒ + [(pSpec (ι := ι) (F := F) k t).Challenge]ₒ)
      let xs ← liftComp ((pSpec (ι := ι) (F := F) k t).getChallenge ⟨2, rfl⟩)
          ([]ₒ + [(pSpec (ι := ι) (F := F) k t).Challenge]ₒ)
      (fun out : (OutputStatement × ∀ i, OutputOracleStatement i) × OutputWitness ↦
        if accepts (k := k) (t := t) ((encode : (Fin k → F) → (ι → A)))
            stmt oStmt γ pre.1 xs
        then some ((stmt, oStmt),
          some (extractZero k ((encode : (Fin k → F) → (ι → A))) δ (stmt, oStmt)),
          (((), nofun) : OutputStatement × ∀ i, OutputOracleStatement i), out.2)
        else none) <$>
        ((liftComp (prover.receiveChallenge
            (⟨2, by rfl⟩ : (pSpec (ι := ι) (F := F) k t).ChallengeIdx) pre.2)
            ([]ₒ + [(pSpec (ι := ι) (F := F) k t).Challenge]ₒ)) >>= fun fc2 ↦
          liftComp (prover.output (fc2 xs))
            ([]ₒ + [(pSpec (ι := ι) (F := F) k t).Challenge]ₒ)))
    _
    (fun γ ↦ ∃ w : Fin k → F,
      ((stmt, oStmt), extractZero k ((encode : (Fin k → F) → (ι → A))) δ (stmt, oStmt)) ∉
          outputRelationFor k ((encode : (Fin k → F) → (ι → A))) δ ∧
        gammaState k ((encode : (Fin k → F) → (ι → A))) δ stmt.1 stmt.2.1 stmt.2.2
          (oStmt 0) (oStmt 1) γ w)
    ?hε₂ ?hoa ?h₁ ?h₂
  case hε₂ =>
    -- `(1−δ)^t ≤ 1`: the spot-check term is a probability.
    exact ENNReal.coe_le_one_iff.mpr (pow_le_one' tsub_le_self t)
  case h₁ =>
    exact gamma_round_game_bound k C δ encode hinj hC hδ_pos hδ_lt_min (stmt, oStmt)
  case h₂ =>
    intro γ hγ s
    -- Inner split at the spot-check draw, per fixed prefix `(γ, g)`.
    refine ProtocolSpec.probEvent_optionT_simulateQ_addLift_prefix_getChallenge_bind_le
      s impl _ ⟨2, rfl⟩ _ _ _ _ rfl (fun pre ↦ ?_)
    refine le_trans (probEvent_mono ?_) (spotcheck_round_game_bound k t
        ((encode : (Fin k → F) → (ι → A))) δ (stmt, oStmt) γ pre.1)
    rintro xs - ⟨out, b, hfb, hE⟩
    by_cases hacc : accepts (k := k) (t := t) ((encode : (Fin k → F) → (ι → A)))
        stmt oStmt γ pre.1 xs
    · rw [if_pos hacc, Option.some_inj] at hfb
      subst hfb
      refine ⟨PUnit.unit.{1}, fun hgs ↦ hγ ⟨pre.1, hE.1 _ rfl, hgs⟩, hacc⟩
    · rw [if_neg hacc] at hfb
      exact absurd hfb (by simp)
  case hoa =>
    -- GOAL: exec.run = liftComp (getChallenge 0) ... >>= tail
    -- Strategy: collapse exec via verifier_run_loggingOracle_eq + logging glue to
    -- `g <$> Prover.run`, then unfold Prover.run to the challenge-first shape.
    let g : ((pSpec (ι := ι) (F := F) k t).FullTranscript ×
        (OutputStatement × ∀ i, OutputOracleStatement i) × OutputWitness) →
      Option ((Statement (F := F) k × (∀ i, OracleStatement ι A i)) ×
        Option (Witness (F := F) k) ×
        (OutputStatement × ∀ i, OutputOracleStatement i) ×
        OutputWitness) :=
      fun r ↦
        if accepts (k := k) (t := t) (encode : (Fin k → F) → (ι → A))
              stmt oStmt (r.1.challenges ⟨0, rfl⟩) (r.1.messages ⟨1, rfl⟩)
              (r.1.challenges ⟨2, rfl⟩)
        then some ((stmt, oStmt),
              some (extractZero k (encode : (Fin k → F) → (ι → A)) δ (stmt, oStmt)),
              (((), nofun) : OutputStatement × ∀ i, OutputOracleStatement i),
              r.2.2)
        else none
    refine Eq.trans ?hA (Eq.trans (loggingOracle.map_fst_run_simulateQ
      (Prover.run (stmt, oStmt) witIn prover) g) ?hC)
    case hA =>
      -- Unfold exec.run via Reduction.runWithLog (do-notation in OptionT), collapsing the
      -- verifier's logged run and the always-succeeding extractor.
      -- Step 1: Unfold the reduction's runWithLog and prover's runWithLog. Use OptionT.run_pure
      -- (not run_bind) to avoid Option.elimM form; bind_assoc/pure_bind handle the OptionT
      -- do-notation bind rewrites at the OptionT level.
      simp only [Reduction.runWithLog, Prover.runWithLog, OptionT.run_pure,
        liftM_pure, pure_bind, bind_assoc]
      -- Step 2: Collapse the verifier's logged run under the prover-run binder.
      -- verifier_run_loggingOracle_eq rewrites
      -- (simulateQ loggingOracle (toVerifier.run (stmt,oStmt) tr)).run to
      -- pure ((if accepts... then some (...) else none), ∅).
      simp_rw [verifier_run_loggingOracle_eq (encode := (encode : (Fin k → F) → (ι → A)))]
      -- Step 3: Collapse liftM (pure ...) and Option.getM.
      simp only [liftM_pure, pure_bind, Option.getM_some, Option.getM_none]
      -- Step 4: Collapse the extractor (always pure (some (extractZero ...))),
      -- then unfold the OptionT.lift wrapper and .run to OracleComp level.
      simp only [OptionT.liftM_def, bind_pure_comp]
      simp only [OptionT.run_bind, OptionT.run_lift, OptionT.run_map, OptionT.run_pure,
        bind_pure_comp, Functor.map_map, Option.map_some, pure_bind, bind_assoc]
      -- Collapse Option.getM on (if accepts... then some ... else none):
      -- for some branch: (some x).getM.run = pure (some x); for none: none.getM.run = pure none.
      -- The OptionT.run_bind and if-case steps reduce the remaining bind.
      simp only [Option.getM, Option.elimM, Option.elim_none, Option.elim_some,
        pure_bind, bind_pure_comp]
      -- Collapse `some <$> oa >>= fun o => o.elim (pure none) f` to `oa >>= f` via bind_map_left.
      simp only [bind_map_left, Option.elim_some]
      -- The goal is now `oa >>= fun x => ... = (fun x => g x.1) <$> oa`.
      -- Rewrite RHS as `oa >>= fun x => pure (g x.1)` via map_eq_bind_pure_comp.
      rw [map_eq_bind_pure_comp]
      apply bind_congr; intro x
      -- Now show the `match (if accepts... then some ... else none)` step equals `pure (g x.1)`.
      -- Split the `accepts` condition to handle both branches.
      simp only [Function.comp]
      split_ifs with h
      · -- accepts case: (pure ((),nofun)).run = pure (some ((),nofun))
        simp only [OptionT.run_pure, map_pure, Option.map_some]
        -- g x.1 = some (...) since h holds; unify by unfolding g
        congr 1; simp only [g, h, if_true]
      · -- ¬accepts case: OptionT.run (pure none) = pure none, then Option.map f none = none
        simp only [Alternative.failure, OptionT.fail, OptionT.mk, OptionT.run, map_pure,
          Option.map_none]
        simp only [g, h, if_false]
    case hC =>
      -- `g <$> Prover.run = challenge-first tail`. `g r` reads the transcript only through
      -- `.challenges ⟨0⟩` / `.messages ⟨1⟩` / `.challenges ⟨2⟩`, so it is the `post`-instance of
      -- `prover_run_map_eq`; rewriting by it leaves a flat challenge-first `do`-block to align
      -- with the (regrouped) `tail` via monad laws.
      refine (prover_run_map_eq k t prover (stmt, oStmt) witIn
        (fun c m xs out ↦
          if accepts (k := k) (t := t) ((encode : (Fin k → F) → (ι → A))) stmt oStmt c m xs
          then some ((stmt, oStmt),
            some (extractZero k ((encode : (Fin k → F) → (ι → A))) δ (stmt, oStmt)),
            (((), nofun) : OutputStatement × ∀ i, OutputOracleStatement i), out.2)
          else none)).trans ?_
      simp only [bind_assoc, map_eq_bind_pure_comp, Function.comp_def]


end Protocol

end Spec

end ToyProblem

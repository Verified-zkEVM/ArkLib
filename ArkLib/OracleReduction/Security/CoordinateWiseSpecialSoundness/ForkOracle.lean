/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tobias Rothmann
-/

import ArkLib.OracleReduction.Security.CoordinateWiseSpecialSoundness.Basic
import ArkLib.OracleReduction.Security.Rewinding

/-!
  # The CWSS seeded fork oracle (client of the general replay fork)

  The interface through which a rewinding extractor (`Extractor.Rewinding`) obtains *sibling runs*
  of the prover for coordinate-wise special soundness. It is a thin CWSS client of the
  protocol-generic `ProtocolSpec.replayForkImpl` (`Rewinding.ReplayFork`): a fork query carries the
  parent transcript and a `(round, coord, value)` edit (`ForkQueryVal`), and `cwssForkSeededImpl`
  feeds the coordinate-override replacement
  `(decompose round).symm (Function.update (decompose round (parent round)) coord value)` to
  `replayForkImpl` with the full-replay (`.replay`) suffix — the additive `ε − κ` route.

  Black-boxness, statelessness, and nested forking are inherited from the general fork (siblings
  carry their own transcripts, so they re-fork for free). The CWSS-specific guarantee
  `cwssForkSeededImpl_coordEq` — the round-`coord` challenge differs from the parent's exactly at
  `coord` — is a one-line corollary of the general `(G1)` `replayForkImpl_forkRound`; prefix
  agreement, realizedness, acceptance, and reachability are reused directly from `Rewinding.ReplayFork`
  (G2–G7).

  The deprecated single-shot *sampling* fork (`cwssForkImpl`/`ForkQuery`, the multiplicative
  Bellare–Neven regime with the without-replacement `avoid` set) has been removed: it is subsumed by
  `replayForkImpl` at the `.resample` suffix, recoverable as another thin client if that route is
  revived.

  ## References

  * [Fenzi, G., Moghaddas, H., and Nguyen, N. K., *Lattice-Based Polynomial Commitments: Towards
      Asymptotic and Concrete Efficiency*][FMN24]
  * [Nguyen, N. K., O'Rourke, G., and Zhang, J., *Hachi: Efficient Lattice-Based Multilinear
      Polynomial Commitments over Extension Fields*][NOZ26]
-/

noncomputable section

open OracleComp OracleSpec ProtocolSpec

-- `ProtocolSpec.SiblingRun`, `FullTranscript.pinnedChallengeImpl`, and `Prover.Realizes` have moved
-- to `Rewinding.Coupling` (CWSS-free; shared with the general replay fork). They
-- remain in scope here via the `…Rewinding` import.

namespace CWSSStructure

variable {n : ℕ} {pSpec : ProtocolSpec n}

/-- A **value-indexed** fork query for the seeded (full-replay) route: re-run the prover, replaying
  the challenges of `parent` strictly before `round`, and at `round` overriding coordinate `coord`
  to the *given* `value` (no sampling, no `avoid`). Deterministic in `value`. -/
structure ForkQueryVal (D : CWSSStructure pSpec) where
  /-- The transcript of the (parent) run being forked. -/
  parent : FullTranscript pSpec
  /-- The challenge round at which to fork. -/
  round : pSpec.ChallengeIdx
  /-- The coordinate of round `round` to override. -/
  coord : Fin (D.coordIndex round)
  /-- The replacement value at `(round, coord)`. -/
  value : D.alphabet round

/-- The seeded fork oracle: each query forks a parent run at one coordinate to a fixed value; the
  answer is the resulting sibling run, or `none`. This is the interface `F` for the seeded route. -/
@[reducible]
def forkOracleVal (D : CWSSStructure pSpec) (StmtOut : Type) : OracleSpec D.ForkQueryVal :=
  fun _ => Option (SiblingRun pSpec StmtOut)

variable {ι : Type} {oSpec : OracleSpec ι} {StmtIn WitIn StmtOut WitOut : Type}
  {σ : Type}

/-- The **seeded** CWSS fork implementation (full-replay route): a thin wrapper over the general
  `ProtocolSpec.replayForkImpl`. On a query `⟨parent, round, coord, value⟩`, if `value` is the
  parent's own coordinate value the fork is a no-op (`none`); otherwise rerun the reduction with the
  round-`round` challenge overridden at coordinate `coord` to `value` (via `decompose`), replaying
  the prefix *and* suffix from `parent` (`.replay`). Deterministic in `value` (`§2.4`). -/
def cwssForkSeededImpl (D : CWSSStructure pSpec)
    [∀ i, SampleableType (pSpec.Challenge i)] [∀ i, DecidableEq (D.alphabet i)]
    (impl : QueryImpl oSpec (StateT σ ProbComp))
    (verifier : Verifier oSpec StmtIn StmtOut pSpec) :
    StmtIn → WitIn → Prover oSpec StmtIn WitIn StmtOut WitOut pSpec →
      QueryImpl (D.forkOracleVal StmtOut) (StateT σ ProbComp) :=
  fun stmtIn witIn prover q =>
    if q.value = D.decompose q.round (q.parent.challenges q.round) q.coord then
      return none
    else
      replayForkImpl impl verifier stmtIn witIn prover q.parent q.round
        ((D.decompose q.round).symm
          (Function.update (D.decompose q.round (q.parent.challenges q.round)) q.coord q.value))
        .replay

/-! ## Structural guarantee (CWSS corollary of the general fork)

The general fork's guarantees `(G1)`–`(G7)` live in `Rewinding.ReplayFork`; only the CWSS-specific
`CoordEq` corollary is derived here, from `(G1)`. -/

variable {D : CWSSStructure pSpec}
  [∀ i, SampleableType (pSpec.Challenge i)] [∀ i, SampleableType (D.alphabet i)]
  [∀ i, DecidableEq (D.alphabet i)]
  {impl : QueryImpl oSpec (StateT σ ProbComp)}
  {verifier : Verifier oSpec StmtIn StmtOut pSpec}
  {stmtIn : StmtIn} {witIn : WitIn}
  {prover : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec}

/-- **CWSS corollary of `(G1)`** (`ProtocolSpec.replayForkImpl_forkRound`): a successful seeded fork
  produces a round-`q.round` challenge that is `CoordEq q.coord` to the parent's — it differs exactly
  at the forked coordinate. Obtained by substituting the `decompose`-update replacement into `(G1)`
  and pushing through `Function.update_self`/`update_of_ne`. -/
theorem cwssForkSeededImpl_coordEq
    {q : D.ForkQueryVal} {s s' : σ} {sib : SiblingRun pSpec StmtOut}
    (h : (some sib, s') ∈ support
      ((D.cwssForkSeededImpl impl verifier stmtIn witIn prover q).run s)) :
    CoordinateWise.CoordEq q.coord
      (D.decompose q.round (q.parent.challenges q.round))
      (D.decompose q.round (sib.transcript.challenges q.round)) := by
  unfold cwssForkSeededImpl at h
  split at h
  · -- guard hit (`value` is the parent's own): the fork returns `none`, contradicting `some sib`
    rw [show ((return none : StateT σ ProbComp (Option (SiblingRun pSpec StmtOut))).run s)
          = pure (none, s) from rfl, support_pure, Set.mem_singleton_iff] at h
    simp at h
  · rename_i hguard
    -- otherwise `sib` is a `.replay` fork at the `decompose`-update replacement; apply (G1)
    have hfork := replayForkImpl_forkRound h
    have hdecomp : D.decompose q.round (sib.transcript.challenges q.round)
        = Function.update (D.decompose q.round (q.parent.challenges q.round)) q.coord q.value := by
      rw [hfork, Equiv.apply_symm_apply]
    refine ⟨?_, ?_⟩
    · rw [hdecomp, Function.update_self]
      exact fun heq => hguard heq.symm
    · intro j hj
      rw [hdecomp, Function.update_of_ne hj]

end CWSSStructure

/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tobias Rothmann
-/

import ArkLib.OracleReduction.Security.Rewinding.Coupling

/-!
  # The general round-indexed replay fork

  A protocol-generic forking method for rewinding extractors: rerun the prover+verifier with the
  round-`r` challenge edited to a given `replacement`, replaying the prefix from a parent transcript
  and governing the suffix by a `ReplaySuffix` mode (`replay` → full replay, additive `ε − κ`;
  `resample` → live, multiplicative). Coordinate structure never appears — the CWSS coordinate edit
  is computed by the client and passed in as `replacement`.

  This is the ArkLib analog of VCVio's `ReplayFork`. See `docs/general-replay-fork-design.md` §2.

  The structural guarantees `(G1)`–`(G7)` generalize the existing `cwssForkImpl_*` lemmas
  (mode-agnostic) via the run-coupling lemmas in `Rewinding.Coupling`; the determinism lemma
  `replayForkImpl_replay_deterministic` consumes `QueryImpl.IsDeterministic`'s closure lemmas.
-/

noncomputable section

open OracleComp OracleSpec ProtocolSpec

/-- How a replay fork answers challenge rounds strictly *after* the fork round. -/
inductive ReplaySuffix
  | replay
  | resample
  deriving DecidableEq, Repr

namespace ProtocolSpec

variable {ι : Type} {oSpec : OracleSpec ι} {StmtIn WitIn StmtOut WitOut : Type} {σ : Type}
  {n : ℕ} {pSpec : ProtocolSpec n}

/-- Round-indexed challenge oracle for one fork: replay rounds `< r` from `parent`, answer round `r`
  with `replacement`, and handle rounds `> r` per `mode` (`replay` → from `parent` deterministically;
  `resample` → fresh uniform). No `decompose`, no coordinates. -/
def replayChallenge [∀ i, SampleableType (pSpec.Challenge i)]
    (parent : FullTranscript pSpec) (r : pSpec.ChallengeIdx)
    (replacement : pSpec.Challenge r) (mode : ReplaySuffix) :
    QueryImpl [pSpec.Challenge]ₒ ProbComp := fun q =>
  if h : q.1 = r then
    pure (cast (congrArg pSpec.Challenge h.symm) replacement)
  else if q.1.1 < r.1 then
    pure (parent.challenges q.1)
  else
    match mode with
    | .replay => pure (parent.challenges q.1)
    | .resample => $ᵗ (pSpec.Challenge q.1)

/-- The `.replay` challenge oracle is pure-valued, so every query has subsingleton support — this
  discharges the `hC` hypothesis of `QueryImpl.IsDeterministic.addLift`. -/
theorem replayChallenge_replay_subsingleton [∀ i, SampleableType (pSpec.Challenge i)]
    (parent : FullTranscript pSpec) (r : pSpec.ChallengeIdx) (replacement : pSpec.Challenge r) :
    ∀ q, (support (replayChallenge parent r replacement .replay q)).Subsingleton := by
  intro q
  -- every branch of `.replay` is `pure _`, hence singleton (so subsingleton) support
  have hpure : ∃ x, replayChallenge parent r replacement .replay q = pure x := by
    unfold replayChallenge
    split
    · exact ⟨_, rfl⟩
    · split <;> exact ⟨_, rfl⟩
  obtain ⟨x, hx⟩ := hpure
  rw [hx, support_pure]
  exact Set.subsingleton_singleton

/-- Rerun the reduction with the round-`r` challenge edited to `replacement`, the prefix replayed
  from `parent`, and the suffix governed by `mode`; return the resulting sibling run (`none` if the
  rerun failed). Shares the ambient oracle state `σ` with the measured run via `impl`. A plain
  `StateT σ ProbComp` value — the KS fork-oracle spec and its `QueryImpl` wrapper stay client-side. -/
def replayForkImpl [∀ i, SampleableType (pSpec.Challenge i)]
    (impl : QueryImpl oSpec (StateT σ ProbComp))
    (verifier : Verifier oSpec StmtIn StmtOut pSpec)
    (stmtIn : StmtIn) (witIn : WitIn)
    (prover : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (parent : FullTranscript pSpec) (r : pSpec.ChallengeIdx)
    (replacement : pSpec.Challenge r) (mode : ReplaySuffix) :
    StateT σ ProbComp (Option (SiblingRun pSpec StmtOut)) := do
  let result ← simulateQ (impl.addLift (replayChallenge parent r replacement mode))
    ((Reduction.mk prover verifier).run stmtIn witIn).run
  match result with
  | none => return none
  | some ⟨⟨transcript, _, _⟩, stmtOut⟩ => return some ⟨transcript, stmtOut⟩

/-! ## Structural guarantees of a successful fork (suffix-mode-generic).

These generalize `cwssForkImpl_{coordEq,prefix_eq,realizes,reachable,accepts}` by swapping the
challenge oracle; each proof goes through the (relocated) run-coupling lemmas, which are edit- and
mode-agnostic. `(G7)` is `runToRound_couple` at `bound = n`. -/

variable [∀ i, SampleableType (pSpec.Challenge i)]
  {impl : QueryImpl oSpec (StateT σ ProbComp)}
  {verifier : Verifier oSpec StmtIn StmtOut pSpec}
  {stmtIn : StmtIn} {witIn : WitIn}
  {prover : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec}
  {parent : FullTranscript pSpec} {r : pSpec.ChallengeIdx}
  {replacement : pSpec.Challenge r} {mode : ReplaySuffix}
  {s s' : σ} {sib : SiblingRun pSpec StmtOut}

/-- **Shared support-extraction for a successful fork**: from a successful `replayForkImpl` query,
  recover a prover run under the indexed-replay challenge oracle producing `sib.transcript`, plus the
  reachability of the end state. Simpler than `cwssForkImpl_run_aux` (no sampling/guard layer). -/
private lemma replayForkImpl_run_aux
    (h : (some sib, s') ∈ support
      ((replayForkImpl impl verifier stmtIn witIn prover parent r replacement mode).run s)) :
    ∃ (out : StmtOut × WitOut) (sp : σ),
      ((sib.transcript, out), sp) ∈ support
        ((simulateQ (impl.addLift (replayChallenge parent r replacement mode) :
            QueryImpl (oSpec + [pSpec.Challenge]ₒ) (StateT σ ProbComp))
          (prover.run stmtIn witIn)).run s) ∧
      impl.Reachable sp s' := by
  unfold replayForkImpl at h
  simp only [StateT.run_bind, support_bind, Set.mem_iUnion] at h
  obtain ⟨⟨result, smid⟩, hresult, hmatch⟩ := h
  rcases result with _ | ⟨⟨transcript, fst, snd⟩, stmtOut⟩
  · simp at hmatch
  · unfold Reduction.run at hresult
    simp only [OptionT.run_bind, OptionT.run_monadLift, Option.elimM, simulateQ_bind,
      simulateQ_map, monadLift_eq_self, StateT.run_bind, StateT.run_map, support_bind,
      support_map, Set.mem_iUnion, Set.mem_image, Option.elim] at hresult
    obtain ⟨⟨po, sp⟩, hpo, hver⟩ := hresult
    obtain ⟨x, hx, heq⟩ := hpo
    rw [Prod.mk.injEq] at heq
    obtain ⟨rfl, rfl⟩ := heq
    simp only [OptionT.run_pure, Option.elimM, Option.elim, simulateQ_bind, simulateQ_map,
      simulateQ_pure, StateT.run_bind, StateT.run_map, support_bind, support_map, support_pure,
      Set.mem_iUnion, Set.mem_image, Set.mem_singleton_iff] at hver
    obtain ⟨⟨vo, vs⟩, hvo, hver2⟩ := hver
    rcases vo with _ | vS
    · simp at hver2
    · rcases vS with _ | vSS
      · simp at hver2
      · simp only [Option.getM, OptionT.run_pure, simulateQ_bind, simulateQ_pure, pure_bind,
          StateT.run_bind, StateT.run_pure, support_bind, support_pure, Set.mem_iUnion,
          Set.mem_singleton_iff, Prod.mk.injEq, Option.some.injEq] at hver2
        simp only [Set.mem_singleton_iff, Prod.mk.injEq, StateT.run_pure,
          support_pure] at hmatch
        obtain ⟨⟨hx1, -⟩, hsmid_vs⟩ := hver2
        obtain ⟨hr, hs'_smid⟩ := hmatch
        rw [Option.some.injEq] at hr
        refine ⟨x.1.2, x.2, ?_, ?_⟩
        · have hrt : sib.transcript = transcript := by rw [hr]
          rw [hrt, show transcript = x.1.1 from congrArg Prod.fst hx1]
          exact hx
        · rw [hs'_smid, hsmid_vs]
          exact simulateQ_reachable impl _ _ hvo

/-- (G1) The sibling's round-`r` challenge IS the replacement. -/
theorem replayForkImpl_forkRound
    (h : (some sib, s') ∈ support
      ((replayForkImpl impl verifier stmtIn witIn prover parent r replacement mode).run s)) :
    sib.transcript.challenges r = replacement := by
  obtain ⟨out, sp, hmem, -⟩ := replayForkImpl_run_aux h
  have key := run_transcript_challenge_mem impl (replayChallenge parent r replacement mode)
    prover stmtIn witIn hmem r
  unfold replayChallenge at key
  simp only [↓reduceDIte, cast_eq, support_pure, Set.mem_singleton_iff] at key
  exact key

/-- (G2) Challenges of rounds `< r` are the parent's (by construction). -/
theorem replayForkImpl_prefix_replayed
    (h : (some sib, s') ∈ support
      ((replayForkImpl impl verifier stmtIn witIn prover parent r replacement mode).run s)) :
    ∀ i' : pSpec.ChallengeIdx, i'.1 < r.1 →
      sib.transcript.challenges i' = parent.challenges i' := by
  obtain ⟨out, sp, hmem, -⟩ := replayForkImpl_run_aux h
  intro i' hi'
  have key := run_transcript_challenge_mem impl (replayChallenge parent r replacement mode)
    prover stmtIn witIn hmem i'
  unfold replayChallenge at key
  rw [dif_neg (fun he => lt_irrefl _ (he ▸ hi')), if_pos hi', support_pure] at key
  exact key

/-- (G3) Under a replay-consistent `impl` and a realized parent, the whole transcript agrees before
  the fork round. -/
theorem replayForkImpl_prefix_eq (hImpl : impl.ReplayConsistent)
    (hParent : ∃ s₀ s₁, prover.Realizes impl stmtIn witIn parent s₀ s₁ ∧ impl.Reachable s₁ s)
    (h : (some sib, s') ∈ support
      ((replayForkImpl impl verifier stmtIn witIn prover parent r replacement mode).run s)) :
    ∀ m : Fin n, m < r.1 → sib.transcript m = parent m := by
  -- decompose the realized parent run
  obtain ⟨sP0, sP1, ⟨outP, hRunP⟩, hReach1s⟩ := hParent
  rw [Prover.run] at hRunP
  simp only [simulateQ_bind, simulateQ_addLift_left, StateT.run_bind, support_bind,
    Set.mem_iUnion] at hRunP
  obtain ⟨⟨⟨trLP, stLP⟩, smidP⟩, hrrP, hrestP⟩ := hRunP
  obtain ⟨⟨oP, soP⟩, hoP, hfinP⟩ := hrestP
  change ((parent, outP), sP1) ∈ support (pure ((trLP, oP), soP)) at hfinP
  rw [support_pure] at hfinP
  have htrP : parent = trLP := congrArg (fun x => x.1.1) (Set.mem_singleton_iff.mp hfinP)
  have hsP1 : sP1 = soP := congrArg (fun x => x.2) (Set.mem_singleton_iff.mp hfinP)
  have hReachP : impl.Reachable smidP s :=
    reachable_trans (reachable_run impl (prover.output stLP) hoP) (hsP1 ▸ hReach1s)
  -- decompose the fork run
  obtain ⟨outF, sp, hForkRun, -⟩ := replayForkImpl_run_aux h
  rw [Prover.run] at hForkRun
  simp only [simulateQ_bind, simulateQ_addLift_left, StateT.run_bind, support_bind,
    Set.mem_iUnion] at hForkRun
  obtain ⟨⟨⟨trLF, stLF⟩, smidF⟩, hrrF, hrestF⟩ := hForkRun
  obtain ⟨⟨oF, soF⟩, -, hfinF⟩ := hrestF
  change ((sib.transcript, outF), sp) ∈ support (pure ((trLF, oF), soF)) at hfinF
  rw [support_pure] at hfinF
  have htrF : sib.transcript = trLF := congrArg (fun x => x.1.1) (Set.mem_singleton_iff.mp hfinF)
  -- pinned and replay challenge oracles agree (deterministically) on rounds before the fork
  have hChAgree : ∀ (cidx : pSpec.ChallengeIdx), cidx.1.1 < r.1.1 →
      ∀ x ∈ support (parent.pinnedChallengeImpl ⟨cidx, ()⟩),
      ∀ y ∈ support (replayChallenge parent r replacement mode ⟨cidx, ()⟩), x = y := by
    intro cidx hlt x hx y hy
    simp only [FullTranscript.pinnedChallengeImpl, support_pure, Set.mem_singleton_iff] at hx
    have hne : ¬ (cidx = r) := fun hc => by subst hc; exact absurd hlt (lt_irrefl _)
    have hyf : replayChallenge parent r replacement mode ⟨cidx, ()⟩
        = pure (parent.challenges cidx) := by
      unfold replayChallenge
      rw [dif_neg hne]
      exact if_pos hlt
    rw [hyf] at hy
    have hyeq : y = parent.challenges cidx := by simpa using hy
    rw [hx, hyeq]
  -- couple the two runs; transcripts agree on rounds before the fork
  obtain ⟨hEntry, -⟩ := runToRound_couple impl hImpl parent.pinnedChallengeImpl
    (replayChallenge parent r replacement mode) prover stmtIn witIn r.1.1 hChAgree
    (Fin.last n) hrrP hrrF hReachP
  intro m hm
  rw [htrF, htrP]
  exact (hEntry m.1 m.2 hm).symm

/-- (G4) The sibling is itself realized (so it is re-forkable). -/
theorem replayForkImpl_realizes
    (h : (some sib, s') ∈ support
      ((replayForkImpl impl verifier stmtIn witIn prover parent r replacement mode).run s)) :
    ∃ s₁, prover.Realizes impl stmtIn witIn sib.transcript s s₁ ∧ impl.Reachable s₁ s' := by
  obtain ⟨out, sp, hmem, hreach⟩ := replayForkImpl_run_aux h
  exact ⟨sp, ⟨out, run_pin impl _ prover stmtIn witIn hmem⟩, hreach⟩

/-- (G5) The sibling's transcript was accepted by the verifier. -/
theorem replayForkImpl_accepts
    (h : (some sib, s') ∈ support
      ((replayForkImpl impl verifier stmtIn witIn prover parent r replacement mode).run s)) :
    ∃ ss ss' : σ, (some sib.stmtOut, ss') ∈
      support ((simulateQ impl (verifier.run stmtIn sib.transcript).run).run ss) := by
  unfold replayForkImpl at h
  simp only [StateT.run_bind, support_bind, Set.mem_iUnion] at h
  obtain ⟨⟨result, smid⟩, hresult, hmatch⟩ := h
  rcases result with _ | ⟨⟨transcript, fst, snd⟩, stmtOut⟩
  · simp at hmatch
  · unfold Reduction.run at hresult
    simp only [OptionT.run_bind, OptionT.run_monadLift, Option.elimM, simulateQ_bind,
      simulateQ_map, monadLift_eq_self, StateT.run_bind, StateT.run_map, support_bind,
      support_map, Set.mem_iUnion, Set.mem_image, Option.elim] at hresult
    obtain ⟨⟨po, sp⟩, hpo, hver⟩ := hresult
    obtain ⟨x, hx, heq⟩ := hpo
    rw [Prod.mk.injEq] at heq
    obtain ⟨rfl, rfl⟩ := heq
    simp only [OptionT.run_pure, Option.elimM, Option.elim, simulateQ_bind, simulateQ_map,
      simulateQ_pure, StateT.run_bind, StateT.run_map, support_bind, support_map, support_pure,
      Set.mem_iUnion, Set.mem_image, Set.mem_singleton_iff] at hver
    obtain ⟨⟨vo, vs⟩, hvo, hver2⟩ := hver
    rcases vo with _ | vS
    · simp at hver2
    · rcases vS with _ | vSS
      · simp at hver2
      · simp only [Option.getM, OptionT.run_pure, simulateQ_bind, simulateQ_pure, pure_bind,
          StateT.run_bind, StateT.run_pure, support_bind, support_pure, Set.mem_iUnion,
          Set.mem_singleton_iff, Prod.mk.injEq, Option.some.injEq] at hver2
        simp only [Set.mem_singleton_iff, Prod.mk.injEq, StateT.run_pure,
          support_pure] at hmatch
        obtain ⟨⟨hx1, hstmt⟩, -⟩ := hver2
        obtain ⟨hr, -⟩ := hmatch
        rw [Option.some.injEq] at hr
        refine ⟨x.2, vs, ?_⟩
        have hrtr : sib.transcript = x.1.1 := by rw [hr]; exact congrArg Prod.fst hx1
        have hrstmt : sib.stmtOut = vSS := by rw [hr]; exact hstmt
        rw [hrtr, hrstmt]
        rw [show (liftM (Verifier.run stmtIn x.1.1 verifier).run :
              OptionT (OracleComp (oSpec + [pSpec.Challenge]ₒ)) (Option StmtOut)).run
            = (liftM (Option.some <$> (Verifier.run stmtIn x.1.1 verifier).run) :
              OracleComp (oSpec + [pSpec.Challenge]ₒ) (Option (Option StmtOut))) from rfl,
          simulateQ_addLift_left, simulateQ_map, StateT.run_map, support_map,
          Set.mem_image] at hvo
        obtain ⟨⟨vo', vs'⟩, hvo', hvoeq⟩ := hvo
        rw [Prod.mk.injEq, Option.some.injEq] at hvoeq
        obtain ⟨rfl, rfl⟩ := hvoeq
        exact hvo'

/-- (G6) The end state is reachable from the start. -/
theorem replayForkImpl_reachable
    (h : (some sib, s') ∈ support
      ((replayForkImpl impl verifier stmtIn witIn prover parent r replacement mode).run s)) :
    impl.Reachable s s' := by
  obtain ⟨out, sp, hmem, hreach⟩ := replayForkImpl_run_aux h
  exact reachable_trans (simulateQ_reachable impl _ _ hmem) hreach

/-- (G7) Forking to the parent's OWN round-`r` value (`.replay`) reproduces the parent run: the
  sibling transcript IS the parent's. Lets the measured center and forked siblings be scored by one
  accept predicate in the heavy-lines step. -/
theorem replayForkImpl_self_reproduces (hImpl : impl.ReplayConsistent)
    (hParent : ∃ s₀ s₁, prover.Realizes impl stmtIn witIn parent s₀ s₁ ∧ impl.Reachable s₁ s)
    (h : (some sib, s') ∈ support
      ((replayForkImpl impl verifier stmtIn witIn prover parent r (parent.challenges r) .replay).run s)) :
    sib.transcript = parent := by
  -- forking to the parent's own value replays *every* challenge from the parent
  have hreplay : ∀ cidx : pSpec.ChallengeIdx,
      replayChallenge parent r (parent.challenges r) .replay ⟨cidx, ()⟩
        = pure (parent.challenges cidx) := by
    intro cidx
    by_cases hc : cidx = r
    · subst hc
      simp only [replayChallenge, ↓reduceDIte]
      congr 1
    · unfold replayChallenge
      rw [dif_neg hc]
      split <;> rfl
  -- decompose the realized parent run
  obtain ⟨sP0, sP1, ⟨outP, hRunP⟩, hReach1s⟩ := hParent
  rw [Prover.run] at hRunP
  simp only [simulateQ_bind, simulateQ_addLift_left, StateT.run_bind, support_bind,
    Set.mem_iUnion] at hRunP
  obtain ⟨⟨⟨trLP, stLP⟩, smidP⟩, hrrP, hrestP⟩ := hRunP
  obtain ⟨⟨oP, soP⟩, hoP, hfinP⟩ := hrestP
  change ((parent, outP), sP1) ∈ support (pure ((trLP, oP), soP)) at hfinP
  rw [support_pure] at hfinP
  have htrP : parent = trLP := congrArg (fun x => x.1.1) (Set.mem_singleton_iff.mp hfinP)
  have hsP1 : sP1 = soP := congrArg (fun x => x.2) (Set.mem_singleton_iff.mp hfinP)
  have hReachP : impl.Reachable smidP s :=
    reachable_trans (reachable_run impl (prover.output stLP) hoP) (hsP1 ▸ hReach1s)
  -- decompose the fork run
  obtain ⟨outF, sp, hForkRun, -⟩ := replayForkImpl_run_aux h
  rw [Prover.run] at hForkRun
  simp only [simulateQ_bind, simulateQ_addLift_left, StateT.run_bind, support_bind,
    Set.mem_iUnion] at hForkRun
  obtain ⟨⟨⟨trLF, stLF⟩, smidF⟩, hrrF, hrestF⟩ := hForkRun
  obtain ⟨⟨oF, soF⟩, -, hfinF⟩ := hrestF
  change ((sib.transcript, outF), sp) ∈ support (pure ((trLF, oF), soF)) at hfinF
  rw [support_pure] at hfinF
  have htrF : sib.transcript = trLF := congrArg (fun x => x.1.1) (Set.mem_singleton_iff.mp hfinF)
  -- the two challenge oracles agree on *all* rounds
  have hChAgree : ∀ (cidx : pSpec.ChallengeIdx), cidx.1.1 < n →
      ∀ x ∈ support (parent.pinnedChallengeImpl ⟨cidx, ()⟩),
      ∀ y ∈ support (replayChallenge parent r (parent.challenges r) .replay ⟨cidx, ()⟩), x = y := by
    intro cidx _ x hx y hy
    simp only [FullTranscript.pinnedChallengeImpl, support_pure, Set.mem_singleton_iff] at hx
    rw [hreplay cidx] at hy
    have hyeq : y = parent.challenges cidx := by simpa using hy
    rw [hx, hyeq]
  -- couple at `bound = n`: the whole transcript agrees
  obtain ⟨hEntry, -⟩ := runToRound_couple impl hImpl parent.pinnedChallengeImpl
    (replayChallenge parent r (parent.challenges r) .replay) prover stmtIn witIn n hChAgree
    (Fin.last n) hrrP hrrF hReachP
  funext m
  rw [htrF, htrP]
  exact (hEntry m.1 m.2 m.2).symm

/-- **Determinism of a full-replay fork.** Under a deterministic ambient impl, the `.replay` fork's
  result has subsingleton support — a deterministic function of `replacement`. -/
theorem replayForkImpl_replay_deterministic (hImpl : impl.IsDeterministic) :
    (support ((replayForkImpl impl verifier stmtIn witIn prover
      parent r replacement .replay).run s)).Subsingleton := by
  -- the combined oracle is deterministic, so the rerun's support is subsingleton; the trailing
  -- `match`/`pure` continuation preserves it.
  have hdet : (impl.addLift (replayChallenge parent r replacement .replay)).IsDeterministic :=
    hImpl.addLift (replayChallenge_replay_subsingleton parent r replacement)
  unfold replayForkImpl
  rw [StateT.run_bind, support_bind]
  rintro x hx y hy
  simp only [Set.mem_iUnion, exists_prop] at hx hy
  obtain ⟨p, hpS, hxT⟩ := hx
  obtain ⟨p', hp'S, hyT⟩ := hy
  obtain rfl : p = p' := hdet.simulateQ _ s hpS hp'S
  rcases hp1 : p.1 with _ | ⟨⟨tr, w⟩, o⟩
  all_goals
    rw [hp1] at hxT hyT
    simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hxT hyT
    rw [hxT, hyT]

end ProtocolSpec

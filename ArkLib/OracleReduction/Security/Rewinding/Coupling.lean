/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tobias Rothmann
-/

import ArkLib.OracleReduction.Security.Rewinding.Basic

/-!
  # Execution-semantics / run-coupling layer (shared by every replay fork)

  CWSS-free infrastructure for reasoning about prover-driven runs under a chosen challenge oracle,
  factored out of `CoordinateWiseSpecialSoundness.ForkOracle`. It is stated over an *arbitrary*
  challenge oracle `C : QueryImpl [pSpec.Challenge]ₒ ProbComp`, so it serves the general
  `Rewinding.ReplayFork` and any client.

  Contents:
  * `ProtocolSpec.SiblingRun` — a completed prover-driven run (transcript + output statement).
  * `FullTranscript.pinnedChallengeImpl`, `Prover.Realizes` — transcript self-consistency.
  * `QueryImpl.IsDeterministic` — per-state subsingleton support, closed under `simulateQ` and
    `addLift` (the additive-route determinism predicate; shared with `LawfulSeededReplay.det`).
  * (TODO, relocation) the run-coupling lemmas (`runToRound_couple`, `oracleComp_replay`, `run_pin`,
    `runToRound_pin`, `simulateQ_reachable`, `reachable_run`, `runToRound_transcript_challenge_mem`,
    `run_transcript_challenge_mem`, `simulateQ_addLift_left`/`_getChallenge`, `runToRound_succ`) are
    still `private` in `ForkOracle.lean`; they move here (public) when the `ReplayFork` proofs that
    consume them are filled in. See `docs/general-replay-fork-design.md` §1.

  See `docs/general-replay-fork-design.md`.
-/

noncomputable section

open OracleComp OracleSpec ProtocolSpec

namespace ProtocolSpec

variable {n : ℕ}

/-- A completed prover-driven run, as returned by a replay fork: the run's full transcript (from
  which all challenge coordinates can be read off, so the run can itself be re-forked) and the
  verifier's output statement (from which acceptance is decided). -/
structure SiblingRun (pSpec : ProtocolSpec n) (StmtOut : Type) where
  /-- The full transcript of the sibling run. -/
  transcript : FullTranscript pSpec
  /-- The verifier's output statement on the sibling run. -/
  stmtOut : StmtOut

/-- The challenge implementation that answers every challenge query with the value recorded in the
  transcript `tr`. Used to express *self-consistency* of a transcript with a prover
  (`Prover.Realizes`), abstracting over the mechanism (uniform sampling, indexed replay, …) that
  actually produced the challenges. -/
def FullTranscript.pinnedChallengeImpl {pSpec : ProtocolSpec n} (tr : FullTranscript pSpec) :
    QueryImpl [pSpec.Challenge]ₒ ProbComp :=
  fun q => pure (tr.challenges q.1)

end ProtocolSpec

namespace Prover

variable {ι : Type} {oSpec : OracleSpec ι} {StmtIn WitIn StmtOut WitOut : Type}
  {n : ℕ} {pSpec : ProtocolSpec n} {σ : Type}

/-- `prover.Realizes impl stmtIn witIn tr s₀ s₁`: the transcript `tr` is **realized** by `prover`
  from ambient oracle state `s₀` (ending in state `s₁`): running the prover with every challenge
  pinned to the value recorded in `tr` (`FullTranscript.pinnedChallengeImpl`), and `oSpec`
  answered through `impl`, can output exactly `tr`. In other words, `tr`'s messages are messages
  the prover itself can produce on `tr`'s challenges in that oracle world. -/
def Realizes (prover : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (impl : QueryImpl oSpec (StateT σ ProbComp)) (stmtIn : StmtIn) (witIn : WitIn)
    (tr : FullTranscript pSpec) (s₀ s₁ : σ) : Prop :=
  ∃ out : StmtOut × WitOut,
    ((tr, out), s₁) ∈ support
      ((simulateQ
        (impl.addLift tr.pinnedChallengeImpl :
          QueryImpl (oSpec + [pSpec.Challenge]ₒ) (StateT σ ProbComp))
        (prover.run stmtIn witIn)).run s₀)

end Prover

namespace QueryImpl

/-- A `StateT σ ProbComp` query implementation is **deterministic** if every query has subsingleton
  support per state: the answer–next-state pair is unique (if any). This is the predicate the
  additive-route heavy-lines argument needs — it makes a `.replay` fork's acceptance a deterministic
  function of the edited challenge — and is exactly `LawfulSeededReplay.det`.

  Subsingleton (not singleton) suffices: heavy-lines only couples the realized run's outcome to the
  unique support element. VCVio has no general `support`-nonemptiness lemma. -/
def IsDeterministic {ι : Type} {spec : OracleSpec ι} {σ : Type}
    (impl : QueryImpl spec (StateT σ ProbComp)) : Prop :=
  ∀ (t : ι) (st : σ), (support ((impl t).run st)).Subsingleton

/-- Determinism is closed under `simulateQ`: a deterministic impl gives every `OracleComp` program
  subsingleton support per state. Proof by induction on `oa` via `simulateQ_pure/_bind/_spec_query`
  and `support_pure/_bind` (cf. `simulateQ_reachable`). -/
theorem IsDeterministic.simulateQ {ι : Type} {spec : OracleSpec ι} {σ α : Type}
    {impl : QueryImpl spec (StateT σ ProbComp)} (h : impl.IsDeterministic)
    (oa : OracleComp spec α) :
    ∀ st : σ, (support ((simulateQ impl oa).run st)).Subsingleton := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro st
    rw [simulateQ_pure, StateT.run_pure, support_pure]
    exact Set.subsingleton_singleton
  | query_bind t k ih =>
    intro st
    rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, support_bind]
    rintro x hx y hy
    simp only [Set.mem_iUnion, exists_prop] at hx hy
    obtain ⟨p, hpS, hxT⟩ := hx
    obtain ⟨p', hp'S, hyT⟩ := hy
    have hpp' : p = p' := h t st hpS hp'S
    subst hpp'
    exact ih p.1 p.2 hxT hyT

/-- Determinism is closed under `addLift` of a (pure-valued) challenge-side impl: if `impl` is
  deterministic and every `C t` has subsingleton support, so does the combined oracle. -/
theorem IsDeterministic.addLift {ι ι₂ : Type} {spec : OracleSpec ι} {spec₂ : OracleSpec ι₂}
    {σ : Type} {impl : QueryImpl spec (StateT σ ProbComp)} {C : QueryImpl spec₂ ProbComp}
    (hImpl : impl.IsDeterministic) (hC : ∀ t, (support (C t)).Subsingleton) :
    (impl.addLift C : QueryImpl (spec + spec₂) (StateT σ ProbComp)).IsDeterministic := by
  intro t st
  rw [QueryImpl.addLift_def]
  cases t with
  | inl t₁ =>
    rw [QueryImpl.add_apply_inl, QueryImpl.liftTarget_self]
    exact hImpl t₁ st
  | inr t₂ =>
    rw [QueryImpl.add_apply_inr, QueryImpl.liftTarget_apply]
    -- `StateT.run_liftM` is `rfl`: `(liftM (C t₂)).run st = C t₂ >>= fun a => pure (a, st)`.
    show (support (C t₂ >>= fun a => pure (a, st))).Subsingleton
    rw [support_bind]
    rintro x hx y hy
    simp only [Set.mem_iUnion, exists_prop, support_pure, Set.mem_singleton_iff] at hx hy
    obtain ⟨a, ha, rfl⟩ := hx
    obtain ⟨b, hb, rfl⟩ := hy
    rw [hC t₂ ha hb]

end QueryImpl

/-! ## Run-coupling lemmas (relocated from `CoordinateWiseSpecialSoundness.ForkOracle`)

  Stated over an *arbitrary* challenge oracle `C : QueryImpl [pSpec.Challenge]ₒ ProbComp`; consumed
  by the general replay fork (`Rewinding.ReplayFork`) and the CWSS client. -/

section ExecutionSemantics

variable {ι : Type} {oSpec : OracleSpec ι} {StmtIn WitIn StmtOut WitOut : Type} {σ : Type}

/-- One step of `runToRound`: running up to round `i + 1` is processing round `i` on the run up to
  round `i`. -/
lemma Prover.runToRound_succ {n : ℕ} {pSpec : ProtocolSpec n}
    (prover : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (stmt : StmtIn) (wit : WitIn) (i : Fin n) :
    prover.runToRound i.succ stmt wit =
      prover.processRound i (prover.runToRound i.castSucc stmt wit) := by
  simp only [Prover.runToRound, Fin.induction_succ]

/-- Under `impl.addLift C`, a (lifted) challenge query of round `i` is answered by `C`. -/
lemma simulateQ_addLift_getChallenge {n : ℕ} {pSpec : ProtocolSpec n}
    [∀ i, SampleableType (pSpec.Challenge i)]
    (impl : QueryImpl oSpec (StateT σ ProbComp))
    (C : QueryImpl [pSpec.Challenge]ₒ ProbComp) (i : pSpec.ChallengeIdx) :
    simulateQ (impl.addLift C : QueryImpl (oSpec + [pSpec.Challenge]ₒ) (StateT σ ProbComp))
      (liftM (pSpec.getChallenge i)) = (liftM (C ⟨i, ()⟩) : StateT σ ProbComp _) := by
  change simulateQ (_ + _) (OracleComp.liftComp (pSpec.getChallenge i) _) = _
  rw [QueryImpl.simulateQ_add_liftComp_right]
  change simulateQ (C.liftTarget (StateT σ ProbComp))
    (liftM (OracleSpec.query (spec := [pSpec.Challenge]ₒ) ⟨i, ()⟩)) = _
  rw [simulateQ_spec_query, QueryImpl.liftTarget_apply]

/-- Under `impl.addLift C`, an `oSpec` computation is answered by `impl`, independent of `C`. -/
lemma simulateQ_addLift_left {n : ℕ} {pSpec : ProtocolSpec n} {α : Type}
    (impl : QueryImpl oSpec (StateT σ ProbComp)) (C : QueryImpl [pSpec.Challenge]ₒ ProbComp)
    (oa : OracleComp oSpec α) :
    simulateQ (impl.addLift C : QueryImpl (oSpec + [pSpec.Challenge]ₒ) (StateT σ ProbComp))
      (liftM oa) = simulateQ impl oa := by
  change simulateQ (_ + _) (OracleComp.liftComp oa _) = _
  rw [QueryImpl.simulateQ_add_liftComp_left, QueryImpl.liftTarget_self]

lemma runToRound_transcript_challenge_mem {n : ℕ} {pSpec : ProtocolSpec n}
    [∀ i, SampleableType (pSpec.Challenge i)]
    (impl : QueryImpl oSpec (StateT σ ProbComp))
    (C : QueryImpl [pSpec.Challenge]ₒ ProbComp)
    (prover : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (stmt : StmtIn) (wit : WitIn) :
    ∀ (i : Fin (n + 1)) {tr : pSpec.Transcript i} {st : prover.PrvState i} {s s' : σ},
      ((tr, st), s') ∈ support
        ((simulateQ (impl.addLift C : QueryImpl (oSpec + [pSpec.Challenge]ₒ) (StateT σ ProbComp))
          (prover.runToRound i stmt wit)).run s) →
      ∀ (j : Fin n) (hji : j.1 < i.1) (hd : pSpec.dir j = .V_to_P),
        tr ⟨j.1, hji⟩ ∈ support (C ⟨⟨j, hd⟩, ()⟩) := by
  intro i
  induction i using Fin.induction with
  | zero => intro tr st s s' _ j hji _; exact absurd hji (Nat.not_lt_zero _)
  | succ i ih =>
    intro tr st s s' h j hji hd
    rw [Prover.runToRound_succ] at h
    unfold Prover.processRound at h
    simp only [simulateQ_bind, StateT.run_bind, support_bind, Set.mem_iUnion] at h
    obtain ⟨⟨⟨trP, stP⟩, sM⟩, hPrev, hRound⟩ := h
    split at hRound
    · -- round `i` is a challenge round; the recorded challenge is an answer of `C`.
      rename_i hDi
      simp only [simulateQ_bind, simulateQ_addLift_getChallenge, simulateQ_pure,
        StateT.run_bind, support_bind, Set.mem_iUnion] at hRound
      obtain ⟨⟨c, sc⟩, hc, ⟨f, sf⟩, -, hlast⟩ := hRound
      change (c, sc) ∈ support (C ⟨⟨i, hDi⟩, ()⟩ >>= fun a => pure (a, sM)) at hc
      rw [support_bind] at hc
      have hc' : c ∈ support (C ⟨⟨i, hDi⟩, ()⟩) := by
        obtain ⟨x, hx, hmem⟩ := Set.mem_iUnion₂.mp hc
        rw [support_pure] at hmem
        have heq : (c, sc) = (x, sM) := hmem
        rw [show c = x from congrArg Prod.fst heq]
        exact hx
      change ((tr, st), s') ∈ support (pure ((Transcript.concat c trP, f c), sf)) at hlast
      simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hlast
      have htr : tr = Transcript.concat c trP := hlast.1.1
      rcases Nat.lt_or_ge j.1 i.1 with hlt | hge
      · -- earlier round: the new entry doesn't affect round `j`.
        have hentry : (Transcript.concat c trP) ⟨j.1, hji⟩ = trP ⟨j.1, hlt⟩ :=
          @Fin.snoc_castSucc i.1 (fun k => pSpec.«Type» (Fin.castLE i.succ.is_le k))
            c trP ⟨j.1, hlt⟩
        rw [htr, hentry]
        exact ih hPrev j (by simpa using hlt) hd
      · -- round `i` itself: the recorded challenge `c` is in `C`'s support.
        have hj_eq : j = i := Fin.ext (by
          have : j.1 < i.1 + 1 := by simpa [Fin.val_succ] using hji
          omega)
        subst hj_eq
        have hentry : (Transcript.concat c trP) ⟨j.1, hji⟩ = c :=
          @Fin.snoc_last j.1 (fun k => pSpec.«Type» (Fin.castLE j.succ.is_le k)) c trP
        rw [htr, hentry]
        exact hc'
    · -- round `i` is a message round; the recorded entry is a prover message.
      rename_i hDi
      simp only [simulateQ_bind, simulateQ_pure, StateT.run_bind,
        support_bind, Set.mem_iUnion] at hRound
      obtain ⟨⟨d, sd⟩, -, hlast⟩ := hRound
      change ((tr, st), s') ∈ support (pure ((Transcript.concat d.1 trP, d.2), sd)) at hlast
      simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hlast
      obtain ⟨⟨htr, -⟩, -⟩ := hlast
      rcases Nat.lt_or_ge j.1 i.1 with hlt | hge
      · -- earlier round: use the induction hypothesis.
        have hentry : (Transcript.concat d.1 trP) ⟨j.1, hji⟩ = trP ⟨j.1, hlt⟩ :=
          @Fin.snoc_castSucc i.1 (fun k => pSpec.«Type» (Fin.castLE i.succ.is_le k))
            d.1 trP ⟨j.1, hlt⟩
        rw [htr, hentry]
        exact ih hPrev j (by simpa using hlt) hd
      · -- round `i = j` would be `V_to_P` (by `hd`) yet is `P_to_V` here: contradiction.
        have hj_eq : j = i := Fin.ext (by
          have : j.1 < i.1 + 1 := by simpa [Fin.val_succ] using hji
          omega)
        subst hj_eq
        rw [hd] at hDi
        exact absurd hDi (by simp)

/-- The `Prover.run` counterpart of `runToRound_transcript_challenge_mem`: the full prover run's
  transcript records the challenge oracle's answers at every round. -/
lemma run_transcript_challenge_mem {n : ℕ} {pSpec : ProtocolSpec n}
    [∀ i, SampleableType (pSpec.Challenge i)]
    (impl : QueryImpl oSpec (StateT σ ProbComp))
    (C : QueryImpl [pSpec.Challenge]ₒ ProbComp)
    (prover : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (stmt : StmtIn) (wit : WitIn)
    {tr : FullTranscript pSpec} {out : StmtOut × WitOut} {s s' : σ}
    (h : ((tr, out), s') ∈ support
      ((simulateQ (impl.addLift C : QueryImpl (oSpec + [pSpec.Challenge]ₒ) (StateT σ ProbComp))
        (prover.run stmt wit)).run s))
    (i' : pSpec.ChallengeIdx) :
    tr.challenges i' ∈ support (C ⟨i', ()⟩) := by
  rw [Prover.run] at h
  simp only [simulateQ_bind, StateT.run_bind, support_bind, Set.mem_iUnion] at h
  obtain ⟨⟨rr, smid⟩, hrr, hrest⟩ := h
  obtain ⟨⟨o, s''⟩, -, hfin⟩ := hrest
  simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff,
    Prod.mk.injEq] at hfin
  obtain ⟨⟨htr, -⟩, -⟩ := hfin
  rw [htr]
  exact runToRound_transcript_challenge_mem impl C prover stmt wit (Fin.last n) hrr i'.1
    i'.1.isLt i'.2

/-- Transitivity of reachability. -/
lemma reachable_trans {impl : QueryImpl oSpec (StateT σ ProbComp)} {s a b : σ}
    (h1 : impl.Reachable s a) (h2 : impl.Reachable a b) : impl.Reachable s b := by
  induction h2 with
  | refl => exact h1
  | step _ hmem ih => exact QueryImpl.Reachable.step ih hmem

/-- Any state reached by running a computation through `impl.addLift C` is reachable from the
  start through `impl` alone: the challenge oracle `C` is stateless. -/
lemma simulateQ_reachable {n : ℕ} {pSpec : ProtocolSpec n}
    (impl : QueryImpl oSpec (StateT σ ProbComp)) (C : QueryImpl [pSpec.Challenge]ₒ ProbComp) :
    ∀ {α : Type} (oa : OracleComp (oSpec + [pSpec.Challenge]ₒ) α) {a : α} {s s' : σ},
      (a, s') ∈ support ((simulateQ (impl.addLift C :
          QueryImpl (oSpec + [pSpec.Challenge]ₒ) (StateT σ ProbComp)) oa).run s) →
      impl.Reachable s s' := by
  intro α oa
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro a' s s' h
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff,
      Prod.mk.injEq] at h
    rw [h.2]
    exact QueryImpl.Reachable.refl s
  | query_bind t k ih =>
    intro a' s s' h
    rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, support_bind] at h
    simp only [Set.mem_iUnion] at h
    obtain ⟨⟨u, s_mid⟩, hu, hk⟩ := h
    refine reachable_trans ?_ (ih u hk)
    rw [QueryImpl.addLift_def] at hu
    cases t with
    | inl t₁ =>
      simp only [QueryImpl.add_apply_inl, QueryImpl.liftTarget_self] at hu
      exact QueryImpl.Reachable.step (QueryImpl.Reachable.refl s) hu
    | inr t₂ =>
      simp only [QueryImpl.add_apply_inr, QueryImpl.liftTarget_apply] at hu
      change (u, s_mid) ∈ support (C t₂ >>= fun a => pure (a, s)) at hu
      rw [support_bind] at hu
      obtain ⟨c, -, hcs⟩ := Set.mem_iUnion₂.mp hu
      rw [support_pure] at hcs
      rw [show s_mid = s from congrArg Prod.snd (hcs : (u, s_mid) = (c, s))]
      exact QueryImpl.Reachable.refl s

/-- States reached by an `oSpec` computation through `impl` are reachable through `impl`. -/
lemma reachable_run {α : Type} (impl : QueryImpl oSpec (StateT σ ProbComp)) :
    ∀ (oa : OracleComp oSpec α) {a : α} {s s' : σ},
      (a, s') ∈ support ((simulateQ impl oa).run s) → impl.Reachable s s' := by
  intro oa
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro a' s s' h
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff,
      Prod.mk.injEq] at h
    rw [h.2]; exact QueryImpl.Reachable.refl s
  | query_bind t k ih =>
    intro a' s s' h
    rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, support_bind] at h
    simp only [Set.mem_iUnion] at h
    obtain ⟨⟨u, smid⟩, hu, hk⟩ := h
    exact reachable_trans (QueryImpl.Reachable.step (QueryImpl.Reachable.refl s) hu) (ih u hk)

/-- **Replay coupling**: under a replay-consistent `impl`, two runs of the same `oSpec` computation
  produce the same value, provided the second starts from a state reachable from the first's end.
  This is what makes a forked run reproduce the parent's prover messages. -/
lemma oracleComp_replay {α : Type} {impl : QueryImpl oSpec (StateT σ ProbComp)}
    (hImpl : impl.ReplayConsistent) :
    ∀ (oa : OracleComp oSpec α) {a b : α} {sRef sRef' sFork sFork' : σ},
      (a, sRef') ∈ support ((simulateQ impl oa).run sRef) →
      impl.Reachable sRef' sFork →
      (b, sFork') ∈ support ((simulateQ impl oa).run sFork) →
      b = a := by
  intro oa
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro a' b sRef sRef' sFork sFork' hRef _ hFork
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff,
      Prod.mk.injEq] at hRef hFork
    exact hFork.1.trans hRef.1.symm
  | query_bind t k ih =>
    intro a' b sRef sRef' sFork sFork' hRef hreach hFork
    rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, support_bind] at hRef hFork
    simp only [Set.mem_iUnion] at hRef hFork
    obtain ⟨pRef, huRef, hkRef⟩ := hRef
    obtain ⟨pFork, huFork, hkFork⟩ := hFork
    have hreach1 : impl.Reachable pRef.2 sFork :=
      reachable_trans (reachable_run impl (k pRef.1) hkRef) hreach
    have hueq : pFork.1 = pRef.1 := hImpl huRef hreach1 huFork
    have hreach2 : impl.Reachable sRef' pFork.2 :=
      reachable_trans hreach (QueryImpl.Reachable.step (QueryImpl.Reachable.refl sFork) huFork)
    exact ih pFork.1 (hueq.symm ▸ hkRef) hreach2 hkFork

/-- **Challenge-pinning swap**: a run under any challenge oracle `C` whose recorded challenges agree
  with a transcript `T` is also a run under the oracle that pins every challenge to `T`. The hypothesis
  `hT` says the produced transcript's challenges (at rounds `< i`) are `T`'s. -/
lemma runToRound_pin {n : ℕ} {pSpec : ProtocolSpec n}
    [∀ i, SampleableType (pSpec.Challenge i)]
    (impl : QueryImpl oSpec (StateT σ ProbComp)) (C : QueryImpl [pSpec.Challenge]ₒ ProbComp)
    (T : FullTranscript pSpec)
    (prover : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec) (stmt : StmtIn) (wit : WitIn) :
    ∀ (i : Fin (n + 1)) {tr : pSpec.Transcript i} {st : prover.PrvState i} {sp s : σ},
      (∀ (j : Fin n) (hj : j.1 < i.1) (hd : pSpec.dir j = .V_to_P),
        tr ⟨j.1, hj⟩ = T.challenges ⟨j, hd⟩) →
      ((tr, st), sp) ∈ support ((simulateQ (impl.addLift C :
          QueryImpl (oSpec + [pSpec.Challenge]ₒ) (StateT σ ProbComp))
        (prover.runToRound i stmt wit)).run s) →
      ((tr, st), sp) ∈ support ((simulateQ (impl.addLift T.pinnedChallengeImpl :
          QueryImpl (oSpec + [pSpec.Challenge]ₒ) (StateT σ ProbComp))
        (prover.runToRound i stmt wit)).run s) := by
  intro i
  induction i using Fin.induction with
  | zero =>
    intro tr st sp s _ h
    rw [Prover.runToRound_zero_of_prover_first, simulateQ_pure] at h ⊢
    exact h
  | succ i ih =>
    intro tr st sp s hT h
    rw [Prover.runToRound_succ] at h ⊢
    unfold Prover.processRound at h ⊢
    simp only [simulateQ_bind, StateT.run_bind, support_bind, Set.mem_iUnion] at h ⊢
    obtain ⟨⟨⟨trP, stP⟩, s_mid⟩, hPrev, hRound⟩ := h
    have hjs : ∀ (j : Fin n), j.1 < i.castSucc.1 → j.1 < i.succ.1 := fun j hj => by
      simp only [Fin.val_castSucc] at hj; simp only [Fin.val_succ]; omega
    split at hRound
    · -- challenge round
      rename_i hDi
      simp only [simulateQ_bind, simulateQ_addLift_getChallenge, simulateQ_addLift_left,
        simulateQ_pure, StateT.run_bind, support_bind, Set.mem_iUnion] at hRound
      obtain ⟨⟨c, sc⟩, hc, ⟨f, sf⟩, hf, hlast⟩ := hRound
      change ((tr, st), sp) ∈ support (pure ((Transcript.concat c trP, f c), sf)) at hlast
      simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hlast
      have htrsnoc : tr = Fin.snoc trP c := hlast.1.1
      have hsc : sc = s_mid := by
        change (c, sc) ∈ support ((C ⟨⟨i, hDi⟩, ()⟩ : ProbComp _) >>= fun a => pure (a, s_mid)) at hc
        rw [support_bind] at hc
        obtain ⟨c', -, hc'⟩ := Set.mem_iUnion₂.mp hc
        rw [support_pure] at hc'
        exact congrArg Prod.snd (hc' : (c, sc) = (c', s_mid))
      have hci : c = T.challenges ⟨i, hDi⟩ := by
        have hb : i.1 < i.succ.1 := by simp only [Fin.val_succ]; omega
        have h1 : tr ⟨i.1, hb⟩ = T.challenges ⟨i, hDi⟩ := hT i hb hDi
        rw [htrsnoc] at h1
        exact (@Fin.snoc_last i.1 (fun k => pSpec.«Type» (Fin.castLE i.succ.is_le k))
          c trP).symm.trans h1
      refine ⟨((trP, stP), s_mid), ?_, ?_⟩
      · apply ih (fun j hj hd => ?_) hPrev
        rw [← hT j (hjs j hj) hd, htrsnoc]
        exact (@Fin.snoc_castSucc i.1 (fun k => pSpec.«Type» (Fin.castLE i.succ.is_le k))
          c trP ⟨j.1, hj⟩).symm
      · simp only [hDi, simulateQ_bind, simulateQ_addLift_getChallenge, simulateQ_addLift_left,
          simulateQ_pure, StateT.run_bind, support_bind, Set.mem_iUnion]
        refine ⟨(c, sc), ?_, (f, sf), hf, ?_⟩
        · change (c, sc) ∈ support ((FullTranscript.pinnedChallengeImpl T ⟨⟨i, hDi⟩, ()⟩ : ProbComp _)
            >>= fun a => pure (a, s_mid))
          rw [FullTranscript.pinnedChallengeImpl, pure_bind, support_pure]
          exact show (c, sc) = (T.challenges ⟨i, hDi⟩, s_mid) from Prod.ext hci hsc
        · change ((tr, st), sp) ∈ support (pure ((Transcript.concat c trP, f c), sf))
          rw [support_pure]
          exact show ((tr, st), sp) = ((Transcript.concat c trP, f c), sf) from
            Prod.ext (Prod.ext hlast.1.1 hlast.1.2) hlast.2
    · -- message round
      rename_i hDi
      simp only [simulateQ_bind, simulateQ_addLift_left, simulateQ_pure, StateT.run_bind,
        support_bind, Set.mem_iUnion] at hRound ⊢
      obtain ⟨⟨d, sd⟩, hd_mem, hlast⟩ := hRound
      change ((tr, st), sp) ∈ support (pure ((Transcript.concat d.1 trP, d.2), sd)) at hlast
      simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hlast
      refine ⟨((trP, stP), s_mid), ?_, ?_⟩
      · apply ih (fun j hj hd => ?_) hPrev
        rw [← hT j (hjs j hj) hd, hlast.1.1]
        exact (@Fin.snoc_castSucc i.1 (fun k => pSpec.«Type» (Fin.castLE i.succ.is_le k))
          d.1 trP ⟨j.1, hj⟩).symm
      · refine ⟨(d, sd), hd_mem, ?_⟩
        change ((tr, st), sp) ∈ support (pure ((Transcript.concat d.1 trP, d.2), sd))
        rw [support_pure]
        exact show ((tr, st), sp) = ((Transcript.concat d.1 trP, d.2), sd) from
          Prod.ext (Prod.ext hlast.1.1 hlast.1.2) hlast.2

/-- The `Prover.run` counterpart of `runToRound_pin`: a full run is also a run under the oracle that
  pins every challenge to the produced transcript. This realizes the transcript. -/
lemma run_pin {n : ℕ} {pSpec : ProtocolSpec n} [∀ i, SampleableType (pSpec.Challenge i)]
    (impl : QueryImpl oSpec (StateT σ ProbComp)) (C : QueryImpl [pSpec.Challenge]ₒ ProbComp)
    (prover : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec) (stmt : StmtIn) (wit : WitIn)
    {tr : FullTranscript pSpec} {out : StmtOut × WitOut} {s s' : σ}
    (h : ((tr, out), s') ∈ support
      ((simulateQ (impl.addLift C : QueryImpl (oSpec + [pSpec.Challenge]ₒ) (StateT σ ProbComp))
        (prover.run stmt wit)).run s)) :
    ((tr, out), s') ∈ support
      ((simulateQ (impl.addLift tr.pinnedChallengeImpl :
          QueryImpl (oSpec + [pSpec.Challenge]ₒ) (StateT σ ProbComp))
        (prover.run stmt wit)).run s) := by
  rw [Prover.run] at h ⊢
  simp only [simulateQ_bind, simulateQ_addLift_left, StateT.run_bind, support_bind,
    Set.mem_iUnion] at h ⊢
  obtain ⟨⟨rr, smid⟩, hrr, hrest⟩ := h
  have htr : tr = rr.1 := by
    obtain ⟨⟨o, s''⟩, -, hfin⟩ := hrest
    change ((tr, out), s') ∈ support (pure ((rr.1, o), s'')) at hfin
    rw [support_pure] at hfin
    exact congrArg (fun x => x.1.1) (hfin : ((tr, out), s') = ((rr.1, o), s''))
  refine ⟨(rr, smid), ?_, hrest⟩
  apply runToRound_pin impl C tr prover stmt wit (Fin.last n) (fun j hj hd => ?_) hrr
  rw [htr]; rfl

/-- **Replay coupling of two prover runs**: under a replay-consistent `impl`, two runs of the same
  prover (same inputs) whose challenge oracles `C_P`, `C_F` agree (deterministically) on every
  challenge round before `bound`, and whose fork-start state is reachable from the parent's run
  state, produce transcripts that agree on every round before `bound` and prover states that agree
  up to round `bound`. The key step at each round is `oracleComp_replay`, applied to the prover's
  `sendMessage`/`receiveChallenge` `oSpec` sub-computation. -/
lemma runToRound_couple {n : ℕ} {pSpec : ProtocolSpec n}
    [∀ i, SampleableType (pSpec.Challenge i)]
    (impl : QueryImpl oSpec (StateT σ ProbComp)) (hImpl : impl.ReplayConsistent)
    (C_P C_F : QueryImpl [pSpec.Challenge]ₒ ProbComp)
    (prover : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec) (stmt : StmtIn) (wit : WitIn)
    (bound : ℕ)
    (hChAgree : ∀ (cidx : pSpec.ChallengeIdx), cidx.1.1 < bound →
      ∀ x ∈ support (C_P ⟨cidx, ()⟩), ∀ y ∈ support (C_F ⟨cidx, ()⟩), x = y)
    {s₀ sF0 : σ} :
    ∀ (i : Fin (n + 1)) {trP : pSpec.Transcript i} {stP : prover.PrvState i} {sP : σ}
      {trF : pSpec.Transcript i} {stF : prover.PrvState i} {sF : σ},
      ((trP, stP), sP) ∈ support
        ((simulateQ (impl.addLift C_P : QueryImpl (oSpec + [pSpec.Challenge]ₒ) (StateT σ ProbComp))
          (prover.runToRound i stmt wit)).run s₀) →
      ((trF, stF), sF) ∈ support
        ((simulateQ (impl.addLift C_F : QueryImpl (oSpec + [pSpec.Challenge]ₒ) (StateT σ ProbComp))
          (prover.runToRound i stmt wit)).run sF0) →
      impl.Reachable sP sF0 →
      (∀ (m : ℕ) (hmi : m < i.1), m < bound → trP ⟨m, hmi⟩ = trF ⟨m, hmi⟩) ∧
        (i.1 ≤ bound → stP = stF) := by
  intro i
  induction i using Fin.induction with
  | zero =>
    intro trP stP sP trF stF sF hP hF _
    simp only [Prover.runToRound_zero_of_prover_first, simulateQ_pure, StateT.run_pure,
      support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hP hF
    obtain ⟨⟨_, hstP⟩, _⟩ := hP
    obtain ⟨⟨_, hstF⟩, _⟩ := hF
    exact ⟨fun m hmi _ => absurd hmi (Nat.not_lt_zero m), fun _ => by rw [hstP, hstF]⟩
  | succ i ih =>
    intro trP stP sP trF stF sF hP hF hreach
    rw [Prover.runToRound_succ] at hP hF
    unfold Prover.processRound at hP hF
    simp only [simulateQ_bind, StateT.run_bind, support_bind, Set.mem_iUnion] at hP hF
    obtain ⟨⟨⟨trP', stP'⟩, sMP⟩, hPrevP, hRoundP⟩ := hP
    obtain ⟨⟨⟨trF', stF'⟩, sMF⟩, hPrevF, hRoundF⟩ := hF
    have hReachMP_sP : impl.Reachable sMP sP := simulateQ_reachable impl C_P _ hRoundP
    have hreach_prev : impl.Reachable sMP sF0 := reachable_trans hReachMP_sP hreach
    obtain ⟨ihEntry, ihState⟩ := ih hPrevP hPrevF hreach_prev
    have hReachP_MF : impl.Reachable sP sMF :=
      reachable_trans hreach (simulateQ_reachable impl C_F _ hPrevF)
    have hsucc : i.succ.1 = i.1 + 1 := rfl
    split at hRoundP
    · -- challenge round
      rename_i hDi
      split at hRoundF
      swap
      · rename_i hDiF; rw [hDi] at hDiF; exact absurd hDiF (by decide)
      rename_i hDiF
      simp only [simulateQ_bind, simulateQ_addLift_getChallenge, simulateQ_addLift_left,
        simulateQ_pure, StateT.run_bind, support_bind, Set.mem_iUnion] at hRoundP hRoundF
      obtain ⟨⟨cP, scP⟩, hcP, ⟨fP, sfP⟩, hfP, hlastP⟩ := hRoundP
      obtain ⟨⟨cF, scF⟩, hcF, ⟨fF, sfF⟩, hfF, hlastF⟩ := hRoundF
      have htrP : trP = Transcript.concat cP trP' := congrArg (fun x => x.1.1) hlastP
      have hstP : stP = fP cP := congrArg (fun x => x.1.2) hlastP
      have hsP : sP = sfP := congrArg (fun x => x.2) hlastP
      have htrF : trF = Transcript.concat cF trF' := congrArg (fun x => x.1.1) hlastF
      have hstF : stF = fF cF := congrArg (fun x => x.1.2) hlastF
      change (cP, scP) ∈ support ((C_P ⟨⟨i, hDi⟩, ()⟩ : ProbComp _) >>= fun a => pure (a, sMP))
        at hcP
      change (cF, scF) ∈ support ((C_F ⟨⟨i, hDi⟩, ()⟩ : ProbComp _) >>= fun a => pure (a, sMF))
        at hcF
      rw [support_bind] at hcP hcF
      obtain ⟨cP', hcP'mem, hcP'⟩ := Set.mem_iUnion₂.mp hcP
      obtain ⟨cF', hcF'mem, hcF'⟩ := Set.mem_iUnion₂.mp hcF
      rw [support_pure] at hcP' hcF'
      have hscP : scP = sMP := congrArg Prod.snd (Set.mem_singleton_iff.mp hcP')
      have hscF : scF = sMF := congrArg Prod.snd (Set.mem_singleton_iff.mp hcF')
      have hcPmem : cP ∈ support (C_P ⟨⟨i, hDi⟩, ()⟩) := by
        rw [show cP = cP' from congrArg Prod.fst (Set.mem_singleton_iff.mp hcP')]; exact hcP'mem
      have hcFmem : cF ∈ support (C_F ⟨⟨i, hDi⟩, ()⟩) := by
        rw [show cF = cF' from congrArg Prod.fst (Set.mem_singleton_iff.mp hcF')]; exact hcF'mem
      rw [hscP] at hfP
      rw [hscF] at hfF
      rcases lt_or_ge i.1 bound with hin | hout
      · have hstEq : stP' = stF' := ihState (le_of_lt hin)
        have hcEq : cP = cF := hChAgree ⟨i, hDi⟩ hin cP hcPmem cF hcFmem
        rw [← hstEq] at hfF
        have hfEq : fF = fP := oracleComp_replay hImpl (prover.receiveChallenge ⟨i, hDi⟩ stP')
          hfP (hsP ▸ hReachP_MF) hfF
        refine ⟨fun m hm' hb => ?_, fun _ => ?_⟩
        · rcases Nat.lt_or_ge m i.1 with hmlt | hmge
          · rw [htrP, htrF,
              show (Transcript.concat cP trP') ⟨m, hm'⟩ = trP' ⟨m, hmlt⟩ from
                @Fin.snoc_castSucc i.1 (fun k => pSpec.«Type» (Fin.castLE i.succ.is_le k))
                  cP trP' ⟨m, hmlt⟩,
              show (Transcript.concat cF trF') ⟨m, hm'⟩ = trF' ⟨m, hmlt⟩ from
                @Fin.snoc_castSucc i.1 (fun k => pSpec.«Type» (Fin.castLE i.succ.is_le k))
                  cF trF' ⟨m, hmlt⟩]
            exact ihEntry m hmlt hb
          · have hm_eq : m = i.1 := by omega
            subst hm_eq
            rw [htrP, htrF,
              show (Transcript.concat cP trP') ⟨i.1, hm'⟩ = cP from
                @Fin.snoc_last i.1 (fun k => pSpec.«Type» (Fin.castLE i.succ.is_le k))
                  cP trP',
              show (Transcript.concat cF trF') ⟨i.1, hm'⟩ = cF from
                @Fin.snoc_last i.1 (fun k => pSpec.«Type» (Fin.castLE i.succ.is_le k))
                  cF trF']
            exact hcEq
        · rw [hstP, hstF, hfEq, hcEq]
      · refine ⟨fun m hm' hb => ?_, fun hle => ?_⟩
        · have hmlt : m < i.1 := by omega
          rw [htrP, htrF,
            show (Transcript.concat cP trP') ⟨m, hm'⟩ = trP' ⟨m, hmlt⟩ from
              @Fin.snoc_castSucc i.1 (fun k => pSpec.«Type» (Fin.castLE i.succ.is_le k))
                cP trP' ⟨m, hmlt⟩,
            show (Transcript.concat cF trF') ⟨m, hm'⟩ = trF' ⟨m, hmlt⟩ from
              @Fin.snoc_castSucc i.1 (fun k => pSpec.«Type» (Fin.castLE i.succ.is_le k))
                cF trF' ⟨m, hmlt⟩]
          exact ihEntry m hmlt hb
        · exfalso; simp only [Fin.val_succ] at hle; omega
    · -- message round
      rename_i hDi
      split at hRoundF
      · rename_i hDiF; rw [hDi] at hDiF; exact absurd hDiF (by decide)
      rename_i hDiF
      simp only [simulateQ_bind, simulateQ_addLift_left, simulateQ_pure, StateT.run_bind,
        support_bind, Set.mem_iUnion] at hRoundP hRoundF
      obtain ⟨⟨dP, sdP⟩, hdP, hlastP⟩ := hRoundP
      obtain ⟨⟨dF, sdF⟩, hdF, hlastF⟩ := hRoundF
      change ((trP, stP), sP) ∈ support (pure ((Transcript.concat dP.1 trP', dP.2), sdP)) at hlastP
      change ((trF, stF), sF) ∈ support (pure ((Transcript.concat dF.1 trF', dF.2), sdF)) at hlastF
      rw [support_pure, Set.mem_singleton_iff] at hlastP hlastF
      have htrP : trP = Transcript.concat dP.1 trP' := congrArg (fun x => x.1.1) hlastP
      have hstP : stP = dP.2 := congrArg (fun x => x.1.2) hlastP
      have hsP : sP = sdP := congrArg (fun x => x.2) hlastP
      have htrF : trF = Transcript.concat dF.1 trF' := congrArg (fun x => x.1.1) hlastF
      have hstF : stF = dF.2 := congrArg (fun x => x.1.2) hlastF
      rcases lt_or_ge i.1 bound with hin | hout
      · have hstEq : stP' = stF' := ihState (le_of_lt hin)
        rw [← hstEq] at hdF
        have hdEq : dF = dP := oracleComp_replay hImpl (prover.sendMessage ⟨i, hDi⟩ stP')
          hdP (hsP ▸ hReachP_MF) hdF
        refine ⟨fun m hm' hb => ?_, fun _ => ?_⟩
        · rcases Nat.lt_or_ge m i.1 with hmlt | hmge
          · rw [htrP, htrF,
              show (Transcript.concat dP.1 trP') ⟨m, hm'⟩ = trP' ⟨m, hmlt⟩ from
                @Fin.snoc_castSucc i.1 (fun k => pSpec.«Type» (Fin.castLE i.succ.is_le k))
                  dP.1 trP' ⟨m, hmlt⟩,
              show (Transcript.concat dF.1 trF') ⟨m, hm'⟩ = trF' ⟨m, hmlt⟩ from
                @Fin.snoc_castSucc i.1 (fun k => pSpec.«Type» (Fin.castLE i.succ.is_le k))
                  dF.1 trF' ⟨m, hmlt⟩]
            exact ihEntry m hmlt hb
          · have hm_eq : m = i.1 := by omega
            subst hm_eq
            rw [htrP, htrF,
              show (Transcript.concat dP.1 trP') ⟨i.1, hm'⟩ = dP.1 from
                @Fin.snoc_last i.1 (fun k => pSpec.«Type» (Fin.castLE i.succ.is_le k))
                  dP.1 trP',
              show (Transcript.concat dF.1 trF') ⟨i.1, hm'⟩ = dF.1 from
                @Fin.snoc_last i.1 (fun k => pSpec.«Type» (Fin.castLE i.succ.is_le k))
                  dF.1 trF']
            rw [hdEq]
        · rw [hstP, hstF, hdEq]
      · refine ⟨fun m hm' hb => ?_, fun hle => ?_⟩
        · have hmlt : m < i.1 := by omega
          rw [htrP, htrF,
            show (Transcript.concat dP.1 trP') ⟨m, hm'⟩ = trP' ⟨m, hmlt⟩ from
              @Fin.snoc_castSucc i.1 (fun k => pSpec.«Type» (Fin.castLE i.succ.is_le k))
                dP.1 trP' ⟨m, hmlt⟩,
            show (Transcript.concat dF.1 trF') ⟨m, hm'⟩ = trF' ⟨m, hmlt⟩ from
              @Fin.snoc_castSucc i.1 (fun k => pSpec.«Type» (Fin.castLE i.succ.is_le k))
                dF.1 trF' ⟨m, hmlt⟩]
          exact ihEntry m hmlt hb
        · exfalso; simp only [Fin.val_succ] at hle; omega

end ExecutionSemantics

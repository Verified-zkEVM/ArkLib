/-
Copyright (c) 2026 Equation Capital dba Apoth3osis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Institute for Ontological Mathematics (IAOM)
-/

import ArkLib.OracleReduction.Composition.Sequential.Append

/-!
# Append perfect completeness at 1-message ++ 1-message

The commit-then-reveal shape (#627): for single-message protocols with pure
verifiers, perfect completeness composes across `Reduction.append`
**unconditionally** — the prover-level factorization hypothesis of
`Reduction.append_perfectCompleteness_of_proverFactorization` is proven here
(`hfact_oneMsg`) through `Prover.append`'s definition, via per-field equation
lemmas at the embedded indices, a characterization of the appended prover's
run in component operations, and simulated-level bridge lemmas showing the
direct challenge-sum lifts wash out under any `QueryImpl`.

Main results: `AppendOneMsg.append_run_components`, `AppendOneMsg.hfact_oneMsg`,
`AppendOneMsg.append_perfectCompleteness_oneMsg`.
-/

open ProtocolSpec OracleSpec OracleComp

namespace AppendOneMsg


variable {ι : Type} {oSpec : OracleSpec ι} {S₁ W₁ S₂ W₂ S₃ W₃ M₁ M₂ : Type}

@[reducible] def spec₁ (M₁ : Type) : ProtocolSpec 1 := ⟨!v[.P_to_V], !v[M₁]⟩
@[reducible] def spec₂ (M₂ : Type) : ProtocolSpec 1 := ⟨!v[.P_to_V], !v[M₂]⟩

variable (P₁ : Prover oSpec S₁ W₁ S₂ W₂ (spec₁ M₁))
  (P₂ : Prover oSpec S₂ W₂ S₃ W₃ (spec₂ M₂))

/-- **L1**: the appended prover's round-0 message is P₁'s (left region). -/
theorem append_sendMessage_left (st : (P₁.append P₂).PrvState (Fin.castSucc 0)) :
    (P₁.append P₂).sendMessage ⟨0, rfl⟩ st =
      (liftM (P₁.sendMessage ⟨0, rfl⟩ st) : OracleComp oSpec _) := by
  simp only [Prover.append, eq_mpr_eq_cast, eq_mp_eq_cast]
  rw [dif_pos (by norm_num : ((0 : Fin (1 + 1)) : ℕ) < 1)]
  refine eq_of_heq ((cast_heq _ _).trans ?_)
  congr 1

/-- **L2**: the appended prover's round-1 message is the boundary composite —
P₁'s output feeding P₂'s input and first message. -/
theorem append_sendMessage_boundary (st : (P₁.append P₂).PrvState (Fin.castSucc 1)) :
    (P₁.append P₂).sendMessage ⟨1, rfl⟩ st =
      ((do
        let ctx₂ ← P₁.output st
        P₂.sendMessage ⟨0, rfl⟩ (P₂.input ctx₂)) : OracleComp oSpec _) := by
  simp only [Prover.append, eq_mpr_eq_cast, eq_mp_eq_cast]
  rw [dif_neg (by norm_num : ¬ ((1 : Fin (1 + 1)) : ℕ) < 1),
    dif_pos (by norm_num : ((1 : Fin (1 + 1)) : ℕ) = 1)]
  refine eq_of_heq ((cast_heq _ _).trans ?_)
  congr 1

/-- **L3**: the appended prover's input is P₁'s. -/
theorem append_input (ctx : S₁ × W₁) :
    (P₁.append P₂).input ctx = (P₁.input ctx : (P₁.append P₂).PrvState 0) := by
  simp only [Prover.append, eq_mpr_eq_cast, eq_mp_eq_cast]
  refine eq_of_heq ((cast_heq _ _).trans ?_)
  congr 1

/-- **L4**: the appended prover's output (n = 1 ≠ 0 branch) is P₂'s. -/
theorem append_output (st : (P₁.append P₂).PrvState (Fin.last (1 + 1))) :
    (P₁.append P₂).output st = (P₂.output st : OracleComp oSpec _) := by
  simp only [Prover.append, eq_mpr_eq_cast, eq_mp_eq_cast]
  rw [dif_neg (by norm_num : ¬ (1 : ℕ) = 0)]
  congr 1

instance {M₁ M₂ : Type} : ∀ i, OracleInterface ((spec₁ M₁ ++ₚ spec₂ M₂).Challenge i) :=
  fun i => ProtocolSpec.challengeOracleInterface i

/-- The DIRECT lift into the composed challenge-sum — pins the exact instance
chain `processRound` elaborates (L5's wall was my restated `liftM` electing the
two-hop route through a component's challenge-sum, opened by the #633
instances; the routes are semantically but not definitionally equal). -/
@[reducible] def liftc {M₁ M₂ α : Type} (x : OracleComp oSpec α) :
    OracleComp (oSpec + [(spec₁ M₁ ++ₚ spec₂ M₂).Challenge]ₒ) α :=
  @liftM _ _ (instMonadLiftTOfMonadLift (OracleComp oSpec) (OracleComp oSpec)
    (OracleComp (oSpec + [(spec₁ M₁ ++ₚ spec₂ M₂).Challenge]ₒ))) _ x

variable (stmt : S₁) (wit : W₁)

/-- **L5a**: composed run to round 1 — P₁'s message under the direct lift. -/
theorem append_runToRound_one :
    (P₁.append P₂).runToRound 1 stmt wit =
      (liftc (oSpec := oSpec) (M₁ := M₁) (M₂ := M₂)
          ((P₁.append P₂).sendMessage ⟨0, rfl⟩
            ((P₁.append P₂).input (stmt, wit))) >>= fun y =>
        pure (ProtocolSpec.Transcript.concat
          (pSpec := spec₁ M₁ ++ₚ spec₂ M₂) (m := 0) y.1
          (default : (spec₁ M₁ ++ₚ spec₂ M₂).Transcript 0), y.2)) :=
  (Prover.runToRound_succ 0 stmt wit (P₁.append P₂)).trans (by
    show Prover.processRound 0 (P₁.append P₂)
      (pure ((default : (spec₁ M₁ ++ₚ spec₂ M₂).Transcript 0),
        (P₁.append P₂).input (stmt, wit))) = _
    simp only [Prover.processRound, pure_bind]
    split
    · rename_i hDir; exact absurd hDir (by decide)
    · rfl)

/-- **L5b**: `processRound 1` as an explicit bind (the boundary-round step). -/
theorem processRound_one_eq
    (c : OracleComp (oSpec + [(spec₁ M₁ ++ₚ spec₂ M₂).Challenge]ₒ)

         ((spec₁ M₁ ++ₚ spec₂ M₂).Transcript (Fin.castSucc 1) × (P₁.append P₂).PrvState (Fin.castSucc 1))) :
    Prover.processRound 1 (P₁.append P₂) c =
      c >>= fun pr =>
        liftc (M₁ := M₁) (M₂ := M₂) ((P₁.append P₂).sendMessage ⟨1, rfl⟩ pr.2) >>= fun w =>
        pure (ProtocolSpec.Transcript.concat
          (pSpec := spec₁ M₁ ++ₚ spec₂ M₂) (m := 1) w.1 pr.1, w.2) := by
  simp only [Prover.processRound]
  refine bind_congr fun pr => ?_
  split
  · rename_i hDir; exact absurd hDir (by decide)
  · rfl

/-- **L5c**: the full composed run, in its natural nesting — the three
directly-lifted stages (P₁'s message; the boundary message; P₂'s output). -/
theorem append_run_raw :
    (P₁.append P₂).run stmt wit =
      (((liftc (oSpec := oSpec) (M₁ := M₁) (M₂ := M₂)
          ((P₁.append P₂).sendMessage ⟨0, rfl⟩
            ((P₁.append P₂).input (stmt, wit))) >>= fun y =>
        pure (ProtocolSpec.Transcript.concat
          (pSpec := spec₁ M₁ ++ₚ spec₂ M₂) (m := 0) y.1
          (default : (spec₁ M₁ ++ₚ spec₂ M₂).Transcript 0), y.2)) >>= fun pr =>
        liftc (M₁ := M₁) (M₂ := M₂)
          ((P₁.append P₂).sendMessage ⟨1, rfl⟩ pr.2) >>= fun w =>
        pure (ProtocolSpec.Transcript.concat
          (pSpec := spec₁ M₁ ++ₚ spec₂ M₂) (m := 1) w.1 pr.1, w.2)) >>= fun x =>
        liftc (M₁ := M₁) (M₂ := M₂) ((P₁.append P₂).output x.2) >>= fun o =>
        pure (x.1, o)) := by
  show ((P₁.append P₂).runToRound (Fin.last 2) stmt wit >>= fun x =>
    liftc (M₁ := M₁) (M₂ := M₂) ((P₁.append P₂).output x.2) >>= fun o =>
      pure (x.1, o)) = _
  rw [show (P₁.append P₂).runToRound (Fin.last 2) stmt wit
      = Prover.processRound 1 (P₁.append P₂) ((P₁.append P₂).runToRound 1 stmt wit)
    from Prover.runToRound_succ 1 stmt wit (P₁.append P₂),
    append_runToRound_one, processRound_one_eq]
  rfl

/-- **L5d (the keystone corollary)**: the composed run written entirely in
COMPONENT operations — P₁'s message, then the boundary handoff
(P₁'s output ⨟ P₂'s input ⨟ P₂'s message), then P₂'s output — each under the
direct lift. This is the fully-opened left side of the BCS `hfact`. -/
theorem append_run_components :
    (P₁.append P₂).run stmt wit =
      (((liftc (oSpec := oSpec) (M₁ := M₁) (M₂ := M₂)
          (P₁.sendMessage ⟨0, rfl⟩ (P₁.input (stmt, wit))) >>= fun y =>
        pure (ProtocolSpec.Transcript.concat
          (pSpec := spec₁ M₁ ++ₚ spec₂ M₂) (m := 0) y.1
          (default : (spec₁ M₁ ++ₚ spec₂ M₂).Transcript 0), y.2)) >>= fun pr =>
        liftc (M₁ := M₁) (M₂ := M₂)
          (do
            let ctx₂ ← P₁.output pr.2
            P₂.sendMessage ⟨0, rfl⟩ (P₂.input ctx₂)) >>= fun w =>
        pure (ProtocolSpec.Transcript.concat
          (pSpec := spec₁ M₁ ++ₚ spec₂ M₂) (m := 1) w.1 pr.1, w.2)) >>= fun x =>
        liftc (M₁ := M₁) (M₂ := M₂) (P₂.output x.2) >>= fun o =>
        pure (x.1, o)) := by
  rw [append_run_raw]
  simp only [append_sendMessage_left, append_sendMessage_boundary, append_input,
    append_output]
  rfl

/-! ## Component-run characterizations + transcript alignment (hfact inputs) -/

instance {M : Type} : ∀ i, OracleInterface ((spec₁ M).Challenge i) :=
  fun i => ProtocolSpec.challengeOracleInterface i

/-- The direct lift into a component's challenge-sum (same pin as `liftc`). -/
@[reducible] def liftd {M α : Type} (x : OracleComp oSpec α) :
    OracleComp (oSpec + [(spec₁ M).Challenge]ₒ) α :=
  @liftM _ _ (instMonadLiftTOfMonadLift (OracleComp oSpec) (OracleComp oSpec)
    (OracleComp (oSpec + [(spec₁ M).Challenge]ₒ))) _ x

/-- The run of an abstract 1-message prover, in natural nesting. -/
theorem oneMsg_run_raw {S W S' W' M : Type}
    (P : Prover oSpec S W S' W' (spec₁ M)) (stmt : S) (wit : W) :
    P.run stmt wit =
      ((liftd (oSpec := oSpec) (M := M)
          (P.sendMessage ⟨0, rfl⟩ (P.input (stmt, wit))) >>= fun y =>
        pure (ProtocolSpec.Transcript.concat (pSpec := spec₁ M) (m := 0) y.1
          (default : (spec₁ M).Transcript 0), y.2)) >>= fun x =>
        liftd (M := M) (P.output x.2) >>= fun o =>
        pure (x.1, o)) := by
  show (P.runToRound (Fin.last 1) stmt wit >>= fun x =>
    liftd (M := M) (P.output x.2) >>= fun o => pure (x.1, o)) = _
  rw [show P.runToRound (Fin.last 1) stmt wit
      = Prover.processRound 0 P (P.runToRound 0 stmt wit)
    from Prover.runToRound_succ 0 stmt wit P]
  show Prover.processRound 0 P
    (pure ((default : (spec₁ M).Transcript 0), P.input (stmt, wit))) >>= _ = _
  simp only [Prover.processRound, pure_bind]
  split
  · rename_i hDir; exact absurd hDir (by decide)
  · rfl

/-- **L6**: the nested composed-transcript concat is the `++ₜ` of the two
single-message transcripts. -/
theorem transcript_align (y₁ : M₁) (y₂ : M₂) :
    ProtocolSpec.Transcript.concat (pSpec := spec₁ M₁ ++ₚ spec₂ M₂) (m := 1) y₂
      (ProtocolSpec.Transcript.concat (pSpec := spec₁ M₁ ++ₚ spec₂ M₂) (m := 0) y₁
        (default : (spec₁ M₁ ++ₚ spec₂ M₂).Transcript 0)) =
    ((ProtocolSpec.Transcript.concat (pSpec := spec₁ M₁) (m := 0) y₁
        (default : (spec₁ M₁).Transcript 0) : FullTranscript (spec₁ M₁)) ++ₜ
      (ProtocolSpec.Transcript.concat (pSpec := spec₂ M₂) (m := 0) y₂
        (default : (spec₂ M₂).Transcript 0) : FullTranscript (spec₂ M₂))) := by
  funext i
  match i with
  | ⟨0, _⟩ => rfl
  | ⟨1, _⟩ => rfl

/-! ## Simulated bridges: direct lifts wash out under simulation -/

instance {M₁ M₂ : Type} : ∀ i, SampleableType ((spec₁ M₁ ++ₚ spec₂ M₂).Challenge i)
  | ⟨0, h⟩ => nomatch h
  | ⟨1, h⟩ => nomatch h

variable {σ : Type} (impl : QueryImpl oSpec (StateT σ ProbComp))

/-- Simulating a directly-lifted `oSpec` computation through the composed
implementation equals simulating it through the lifted base implementation. -/
theorem bridge_c {α : Type} (X : OracleComp oSpec α) :
    simulateQ (QueryImpl.addLift impl challengeQueryImpl :
        QueryImpl _ (StateT σ ProbComp))
      (liftc (oSpec := oSpec) (M₁ := M₁) (M₂ := M₂) X) =
    simulateQ (impl.liftTarget (StateT σ ProbComp)) X := by
  show simulateQ _ (@liftM _ _ (instMonadLiftTOfMonadLift (OracleComp oSpec)
    (OracleComp oSpec)
    (OracleComp (oSpec + [(spec₁ M₁ ++ₚ spec₂ M₂).Challenge]ₒ))) _ X) = _
  exact @QueryImpl.simulateQ_liftM_eq_of_query _ _ oSpec _ _ _ _ _
    (instMonadLiftTOfMonadLift (OracleComp oSpec) (OracleComp oSpec)
      (OracleComp (oSpec + [(spec₁ M₁ ++ₚ spec₂ M₂).Challenge]ₒ)))
    (by infer_instance)
    (QueryImpl.addLift impl challengeQueryImpl)
    (impl.liftTarget (StateT σ ProbComp))
    (fun t => by
      show simulateQ _ (OracleComp.liftComp (liftM (OracleSpec.query t) :
        OracleComp oSpec _) _) = _
      simp [QueryImpl.addLift_def, OracleComp.liftComp_query,
        OracleSpec.query_def, simulateQ_spec_query]
      show simulateQ (impl + QueryImpl.liftTarget (StateT σ ProbComp) challengeQueryImpl)
        ((liftM (OracleQuery.mk
            (spec := oSpec + [(spec₁ M₁ ++ₚ spec₂ M₂).Challenge]ₒ)
            (Sum.inl t) id) :
          OracleComp (oSpec + [(spec₁ M₁ ++ₚ spec₂ M₂).Challenge]ₒ)
            (oSpec.Range t))) = impl t
      rw [simulateQ_query]
      show id <$> (impl + QueryImpl.liftTarget (StateT σ ProbComp)
        challengeQueryImpl) (Sum.inl t) = impl t
      rw [id_map]
      exact QueryImpl.add_apply_inl _ _ _) X

/-- The component-spec simulated bridge (same skeleton as `bridge_c`). -/
theorem bridge_d {M α : Type} (X : OracleComp oSpec α) :
    simulateQ (QueryImpl.addLift impl challengeQueryImpl :
        QueryImpl _ (StateT σ ProbComp))
      (liftd (oSpec := oSpec) (M := M) X) =
    simulateQ (impl.liftTarget (StateT σ ProbComp)) X := by
  show simulateQ _ (@liftM _ _ (instMonadLiftTOfMonadLift (OracleComp oSpec)
    (OracleComp oSpec)
    (OracleComp (oSpec + [(spec₁ M).Challenge]ₒ))) _ X) = _
  exact @QueryImpl.simulateQ_liftM_eq_of_query _ _ oSpec _ _ _ _ _
    (instMonadLiftTOfMonadLift (OracleComp oSpec) (OracleComp oSpec)
      (OracleComp (oSpec + [(spec₁ M).Challenge]ₒ)))
    (by infer_instance)
    (QueryImpl.addLift impl challengeQueryImpl)
    (impl.liftTarget (StateT σ ProbComp))
    (fun t => by
      simp [QueryImpl.addLift_def, OracleComp.liftComp_query,
        OracleSpec.query_def, simulateQ_spec_query]
      show simulateQ (impl + QueryImpl.liftTarget (StateT σ ProbComp)
        challengeQueryImpl)
        ((liftM (OracleQuery.mk (spec := oSpec + [(spec₁ M).Challenge]ₒ)
            (Sum.inl t) id) :
          OracleComp (oSpec + [(spec₁ M).Challenge]ₒ) (oSpec.Range t))) = impl t
      rw [simulateQ_query]
      show id <$> (impl + QueryImpl.liftTarget (StateT σ ProbComp)
        challengeQueryImpl) (Sum.inl t) = impl t
      rw [id_map]
      exact QueryImpl.add_apply_inl _ _ _) X

/-! ## hfact: the prover-level simulated factorization at 1+1 -/

theorem hfact_oneMsg
    (R₁ : Reduction oSpec S₁ W₁ S₂ W₂ (spec₁ M₁))
    (R₂ : Reduction oSpec S₂ W₂ S₃ W₃ (spec₂ M₂))
    (stmt : S₁) (wit : W₁) (s : σ) :
    StateT.run (simulateQ (QueryImpl.addLift impl challengeQueryImpl :
        QueryImpl _ (StateT σ ProbComp))
      (liftM ((R₁.append R₂).prover.run stmt wit) :
        OracleComp (oSpec + [(spec₁ M₁ ++ₚ spec₂ M₂).Challenge]ₒ) _)) s =
    (do
      let (r₁, s₁) ← StateT.run (simulateQ (QueryImpl.addLift impl challengeQueryImpl :
          QueryImpl _ (StateT σ ProbComp))
        (liftM (R₁.prover.run stmt wit) :
          OracleComp (oSpec + [(spec₁ M₁).Challenge]ₒ) _)) s
      let (r₂, s₂) ← StateT.run (simulateQ (QueryImpl.addLift impl challengeQueryImpl :
          QueryImpl _ (StateT σ ProbComp))
        (liftM (R₂.prover.run r₁.2.1 r₁.2.2) :
          OracleComp (oSpec + [(spec₂ M₂).Challenge]ₒ) _)) s₁
      pure ((r₁.1 ++ₜ r₂.1, r₂.2), s₂)) := by
  show StateT.run (simulateQ _ ((R₁.prover.append R₂.prover).run stmt wit)) s = _
  rw [append_run_components]
  conv_rhs =>
    rw [show (liftM (R₁.prover.run stmt wit) :
        OracleComp (oSpec + [(spec₁ M₁).Challenge]ₒ) _)
      = R₁.prover.run stmt wit from rfl,
      oneMsg_run_raw R₁.prover stmt wit]
  have simQb : ∀ {ι' : Type} {spec' : OracleSpec ι'} {γ β : Type}
      (impl' : QueryImpl spec' (StateT σ ProbComp))
      (mx : OracleComp spec' γ) (my : γ → OracleComp spec' β),
      simulateQ impl' (@bind _ _ _ _ mx my)
        = @bind _ _ _ _ (simulateQ impl' mx) (fun x => simulateQ impl' (my x)) :=
    fun impl' mx my => simulateQ_bind _ mx my
  have runb : ∀ {γ β : Type} (mx : StateT σ ProbComp γ) (my : γ → StateT σ ProbComp β)
      (s' : σ), StateT.run (bind mx my) s'
        = bind (StateT.run mx s') (fun p => StateT.run (my p.1) p.2) :=
    fun mx my s' => rfl
  -- VALIDATED (fires): term-level distribution — congrArg + Eq.trans checks by
  -- defeq where rw/simp/conv matching refuses (see WIP note for the root-cause
  -- forensics and the full remaining chain).
  erw [simulateQ_bind, simulateQ_bind, simulateQ_bind]
  erw [simulateQ_bind, simulateQ_bind, bridge_c]
  erw [bridge_d]
  erw [StateT.run_bind]
  erw [StateT.run_bind, StateT.run_bind]
  erw [StateT.run_bind, StateT.run_bind]
  erw [bind_assoc, bind_assoc, bind_assoc, bind_assoc]
  refine bind_congr (m := ProbComp) fun x => ?_
  erw [simulateQ_pure, simulateQ_pure, StateT.run_pure, StateT.run_pure,
    pure_bind, pure_bind]
  erw [simulateQ_bind, bridge_c, simulateQ_bind, simulateQ_bind, bridge_d]
  erw [StateT.run_bind, StateT.run_bind, StateT.run_bind]
  erw [bind_assoc]
  erw [bind_assoc]
  erw [bind_assoc]
  refine bind_congr (m := ProbComp) fun y => ?_
  erw [simulateQ_pure, StateT.run_pure, pure_bind]
  simp only []
  erw [oneMsg_run_raw]
  erw [simulateQ_bind, simulateQ_bind, bridge_d]
  erw [StateT.run_bind, StateT.run_bind, bind_assoc, bind_assoc]
  refine bind_congr (m := ProbComp) fun z => ?_
  erw [simulateQ_pure, StateT.run_pure, pure_bind,
    simulateQ_pure, StateT.run_pure, pure_bind]
  erw [simulateQ_bind, bridge_c, simulateQ_bind, bridge_d]
  erw [StateT.run_bind, StateT.run_bind]
  erw [bind_assoc]
  refine bind_congr (m := ProbComp) fun o => ?_
  erw [simulateQ_pure, StateT.run_pure, simulateQ_pure, StateT.run_pure, pure_bind]
  erw [transcript_align]
  rfl

/-! ## Instance pins for the crown -/

section CompositionLocal
/- Local restatement of `Reduction.append_perfectCompleteness_of_proverFactorization`
(and its `run_pure_verifier` helper) elaborated in THIS file's instance context:
applying the `Append.lean` version at these concrete reducible specs runs into a
pinned-vs-generic `OracleInterface` unification storm (whnf heartbeat divergence);
elaborating the theorem here sidesteps it. Semantically identical to the upstream
statements. -/

variable {ι : Type} {oSpec : OracleSpec ι} {Stmt₁ Wit₁ Stmt₂ Wit₂ Stmt₃ Wit₃ : Type}
  {m n : ℕ} {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n}

/-- **Run of a reduction with a pure verifier** (abstract prover): the `OptionT`
plumbing collapses onto the prover's run. Reusable for any reduction whose verifier
is a pure function of statement and transcript (their `support_run_pure_verifier`
premise pattern). -/
theorem run_pure_verifier
    (R : Reduction oSpec Stmt₁ Wit₁ Stmt₂ Wit₂ pSpec₁)
    (f : Stmt₁ → FullTranscript pSpec₁ → Stmt₂)
    (hf : ∀ stmt td, R.verifier.verify stmt td =
      (pure (f stmt td) : OptionT (OracleComp oSpec) Stmt₂))
    (stmt : Stmt₁) (wit : Wit₁) :
    (R.run stmt wit).run =
      ((liftM (R.prover.run stmt wit) : OracleComp _ _) >>= fun r =>
        pure (some ((r.1, r.2), f stmt r.1))) := by
  unfold Reduction.run
  simp only [OptionT.run_bind, Option.elimM]
  rw [show ((liftM (R.prover.run stmt wit) : OptionT (OracleComp _) _)).run
    = (liftM (R.prover.run stmt wit) : OracleComp _ _) >>= fun r => pure (some r) from rfl]
  rw [bind_assoc]
  refine bind_congr fun r => ?_
  rw [pure_bind]
  simp only [Option.elim_some, Verifier.run, hf]
  rfl

variable {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
  {rel₁ : Set (Stmt₁ × Wit₁)} {rel₂ : Set (Stmt₂ × Wit₂)} {rel₃ : Set (Stmt₃ × Wit₃)}
  [∀ i, SampleableType (pSpec₁.Challenge i)] [∀ i, SampleableType (pSpec₂.Challenge i)]
  [∀ i, SampleableType ((pSpec₁ ++ₚ pSpec₂).Challenge i)]

/-- **Perfect completeness composes across `Reduction.append`** under:
pure verifiers (`hf₁`, `hf₂`), the prover-level simulated factorization `hfact`
(the distributional shadow of `Prover.append_run` — the sole remaining upstream
obligation), and — the side condition answering the upstream TODO — R₂ complete
**uniformly in the initial state** (`h₂` quantifies over `init'`; the appended run
hands R₂ whatever state R₁'s prover left, so a fixed-`init` premise cannot apply). -/
theorem append_perfectCompleteness_of_proverFactorization
    (R₁ : Reduction oSpec Stmt₁ Wit₁ Stmt₂ Wit₂ pSpec₁)
    (R₂ : Reduction oSpec Stmt₂ Wit₂ Stmt₃ Wit₃ pSpec₂)
    (f₁ : Stmt₁ → FullTranscript pSpec₁ → Stmt₂)
    (f₂ : Stmt₂ → FullTranscript pSpec₂ → Stmt₃)
    (hf₁ : ∀ stmt td, R₁.verifier.verify stmt td =
      (pure (f₁ stmt td) : OptionT (OracleComp oSpec) Stmt₂))
    (hf₂ : ∀ stmt td, R₂.verifier.verify stmt td =
      (pure (f₂ stmt td) : OptionT (OracleComp oSpec) Stmt₃))
    (hfact : ∀ (stmt : Stmt₁) (wit : Wit₁) (s : σ),
      StateT.run (simulateQ (QueryImpl.addLift impl challengeQueryImpl :
          QueryImpl _ (StateT σ ProbComp))
        (liftM ((R₁.append R₂).prover.run stmt wit) :
          OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) _)) s =
      (do
        let (r₁, s₁) ← StateT.run (simulateQ (QueryImpl.addLift impl challengeQueryImpl :
            QueryImpl _ (StateT σ ProbComp))
          (liftM (R₁.prover.run stmt wit) :
            OracleComp (oSpec + [pSpec₁.Challenge]ₒ) _)) s
        let (r₂, s₂) ← StateT.run (simulateQ (QueryImpl.addLift impl challengeQueryImpl :
            QueryImpl _ (StateT σ ProbComp))
          (liftM (R₂.prover.run r₁.2.1 r₁.2.2) :
            OracleComp (oSpec + [pSpec₂.Challenge]ₒ) _)) s₁
        pure ((r₁.1 ++ₜ r₂.1, r₂.2), s₂)))
    (h₁ : R₁.perfectCompleteness init impl rel₁ rel₂)
    (h₂ : ∀ init' : ProbComp σ, R₂.perfectCompleteness init' impl rel₂ rel₃) :
    (R₁.append R₂).perfectCompleteness init impl rel₁ rel₃ := by
  simp only [Reduction.perfectCompleteness, Reduction.completeness,
    ENNReal.coe_zero, tsub_zero] at h₁ h₂ ⊢
  intro stmtIn witIn hIn
  -- The appended verifier of pure verifiers is the pure composite.
  have hfA : ∀ stmt td, (R₁.append R₂).verifier.verify stmt td =
      (pure (f₂ (f₁ stmt td.fst) td.snd) : OptionT (OracleComp oSpec) Stmt₃) := by
    intro stmt td
    show (do
      let stmt₂ ← R₁.verifier.verify stmt td.fst
      let r ← R₂.verifier.verify stmt₂ td.snd
      pure r : OptionT (OracleComp oSpec) Stmt₃) = _
    rw [hf₁, pure_bind, hf₂]
    simp only [bind_pure]
  -- Composed-run characterization through the appended prover.
  have hcomp := run_pure_verifier (R₁.append R₂)
    (fun stmt td => f₂ (f₁ stmt td.fst) td.snd) hfA stmtIn witIn
  simp only [hcomp]
  rw [ge_iff_le, one_le_probEvent_iff, probEvent_eq_one_iff]
  -- Extract stage facts from h₁ at init.
  have h₁' := h₁ stmtIn witIn hIn
  rw [ge_iff_le, one_le_probEvent_iff, probEvent_eq_one_iff] at h₁'
  simp only [run_pure_verifier R₁ f₁ hf₁] at h₁'
  obtain ⟨-, h₁supp⟩ := h₁'
  -- Per-state stage-1 prover facts (constructive membership into h₁supp's support).
  have h₁supp' : ∀ s ∈ _root_.support init,
      ∀ q ∈ _root_.support (StateT.run (simulateQ (QueryImpl.addLift impl challengeQueryImpl :
          QueryImpl _ (StateT σ ProbComp))
        (liftM (R₁.prover.run stmtIn witIn) :
          OracleComp (oSpec + [pSpec₁.Challenge]ₒ) _)) s),
      (f₁ stmtIn q.1.1, q.1.2.2) ∈ rel₂ ∧ q.1.2.1 = f₁ stmtIn q.1.1 := by
    intro s hs q hq
    exact h₁supp ((q.1.1, q.1.2), f₁ stmtIn q.1.1) (by
      rw [OptionT.mem_support_iff]
      simp only [OptionT.run_mk, support_bind, Set.mem_iUnion]
      refine ⟨s, hs, ?_⟩
      simp only [simulateQ_bind, StateT.run'_eq, StateT.run_bind, support_map, support_bind,
        Set.mem_image, Set.mem_iUnion, exists_prop]
      exact ⟨(some ((q.1.1, q.1.2), f₁ stmtIn q.1.1), q.2),
        ⟨q, hq, by simp [simulateQ_pure, StateT.run_pure]⟩, rfl⟩)
  constructor
  · -- No failure: the composed value is unconditionally `some`.
    rw [OptionT.probFailure_eq, OptionT.run_mk]
    simp only [probFailure_eq_zero, zero_add]
    apply probOutput_eq_zero_of_not_mem_support
    simp only [support_bind, Set.mem_iUnion, not_exists]
    intro s _ h
    simp only [simulateQ_bind, StateT.run'_eq, StateT.run_bind, support_map,
      support_bind] at h
    simp only [Set.mem_image, Set.mem_iUnion, exists_prop] at h
    obtain ⟨p, ⟨r, _, hp⟩, hnone⟩ := h
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hp
    rw [hp] at hnone
    exact Option.some_ne_none _ hnone
  · -- Support ⊆ event: decompose through hfact, compose event₁ and event₂.
    intro x hx
    rw [OptionT.mem_support_iff] at hx
    simp only [OptionT.run_mk, support_bind, Set.mem_iUnion] at hx
    obtain ⟨s, hs, hx⟩ := hx
    simp only [simulateQ_bind, StateT.run'_eq, StateT.run_bind, support_map,
      support_bind] at hx
    simp only [Set.mem_image, Set.mem_iUnion, exists_prop] at hx
    obtain ⟨p, ⟨r, hr, hp⟩, hsome⟩ := hx
    rw [hfact stmtIn witIn s] at hr
    simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff,
      exists_prop] at hr
    obtain ⟨q₁, hq₁, q₂, hq₂, hr_eq⟩ := hr
    obtain ⟨hrel₂, hstmt₂⟩ := h₁supp' s hs q₁ hq₁
    -- Stage-2 facts from h₂ at the deterministic mid state.
    have h₂' := h₂ (pure q₁.2) q₁.1.2.1 q₁.1.2.2 (by rw [hstmt₂]; exact hrel₂)
    rw [ge_iff_le, one_le_probEvent_iff, probEvent_eq_one_iff] at h₂'
    simp only [run_pure_verifier R₂ f₂ hf₂] at h₂'
    obtain ⟨-, h₂supp⟩ := h₂'
    have hev₂ := h₂supp ((q₂.1.1, q₂.1.2), f₂ q₁.1.2.1 q₂.1.1) (by
      rw [OptionT.mem_support_iff]
      simp only [OptionT.run_mk, support_bind, Set.mem_iUnion]
      refine ⟨q₁.2, by simp, ?_⟩
      simp only [simulateQ_bind, StateT.run'_eq, StateT.run_bind, support_map, support_bind,
        Set.mem_image, Set.mem_iUnion, exists_prop]
      exact ⟨(some ((q₂.1.1, q₂.1.2), f₂ q₁.1.2.1 q₂.1.1), q₂.2),
        ⟨q₂, hq₂, by simp [simulateQ_pure, StateT.run_pure]⟩, rfl⟩)
    obtain ⟨hrel₃, hstmt₃⟩ := hev₂
    -- Assemble the composed event.
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hp
    rw [hp] at hsome
    cases Option.some.inj hsome
    rw [hr_eq]
    refine ⟨?_, ?_⟩
    · show (f₂ (f₁ stmtIn (q₁.1.1 ++ₜ q₂.1.1).fst) (q₁.1.1 ++ₜ q₂.1.1).snd, q₂.1.2.2) ∈ rel₃
      rw [FullTranscript.append_fst, FullTranscript.append_snd, ← hstmt₂]
      exact hrel₃
    · show q₂.1.2.1 = f₂ (f₁ stmtIn (q₁.1.1 ++ₜ q₂.1.1).fst) (q₁.1.1 ++ₜ q₂.1.1).snd
      rw [FullTranscript.append_fst, FullTranscript.append_snd, ← hstmt₂]
      exact hstmt₃

end CompositionLocal


instance {M : Type} : ∀ i, SampleableType ((spec₁ M).Challenge i)
  | ⟨0, h⟩ => nomatch h

instance {M : Type} : ∀ i, SampleableType ((spec₂ M).Challenge i)
  | ⟨0, h⟩ => nomatch h

instance {M : Type} : ∀ i, OracleInterface ((spec₂ M).Challenge i) :=
  fun i => ProtocolSpec.challengeOracleInterface i


variable {rel₁ : Set (S₁ × W₁)} {rel₂ : Set (S₂ × W₂)} {rel₃ : Set (S₃ × W₃)}

set_option maxHeartbeats 4000000 in
/-- **1-message append perfect completeness, unconditional**: for
1-message protocols with pure verifiers, perfect completeness composes across
`Reduction.append` — no factorization hypothesis left (it is `hfact_oneMsg`),
only the honest side conditions: pure verifiers and R₂ complete uniformly in
the initial state. -/
theorem append_perfectCompleteness_oneMsg
    (R₁ : Reduction oSpec S₁ W₁ S₂ W₂ (spec₁ M₁))
    (R₂ : Reduction oSpec S₂ W₂ S₃ W₃ (spec₂ M₂))
    (f₁ : S₁ → FullTranscript (spec₁ M₁) → S₂)
    (f₂ : S₂ → FullTranscript (spec₂ M₂) → S₃)
    (hf₁ : ∀ stmt td, R₁.verifier.verify stmt td =
      (pure (f₁ stmt td) : OptionT (OracleComp oSpec) S₂))
    (hf₂ : ∀ stmt td, R₂.verifier.verify stmt td =
      (pure (f₂ stmt td) : OptionT (OracleComp oSpec) S₃))
    (init : ProbComp σ)
    (h₁ : R₁.perfectCompleteness init impl rel₁ rel₂)
    (h₂ : ∀ init' : ProbComp σ, R₂.perfectCompleteness init' impl rel₂ rel₃) :
    (R₁.append R₂).perfectCompleteness init impl rel₁ rel₃ :=
  append_perfectCompleteness_of_proverFactorization R₁ R₂ f₁ f₂ hf₁ hf₂
    (fun stmt wit s => hfact_oneMsg impl R₁ R₂ stmt wit s) h₁ h₂



end AppendOneMsg

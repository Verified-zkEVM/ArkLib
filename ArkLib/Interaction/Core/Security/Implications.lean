/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Interaction.Core.Security.RoundByRound
public import ArkLib.Interaction.Core.Security.Soundness
public import VCVio.EvalDist.ProbabilityBounds

/-!
# Round-by-round soundness implies soundness

A false statement can be accepted only if some challenge node on the run's path turns the
round-by-round state from false to true. Each such flip has probability at most its node's error,
also when the prefix before the node is random. The union bound over the challenge nodes of a path
therefore bounds soundness by the supremum, over shape paths, of the sum of the node errors along
the path.
-/

@[expose] public section

namespace Interaction.Core
open PFunctor FreeM TwoParty.Lens OracleComp Oracle MeasureTheory
open scoped ENNReal

section Escape

variable {P : PFunctor.{1, 0}} (l : PFunctor.Lens P rolePoly)

/-- The challenge nodes met along a shape path. -/
def challengeNodesOn : (s : FreeM P PUnit) → Path s → Finset (ChallengeNode l s)
  | .pure _, _ => ∅
  | .liftBind a next, ⟨b, p⟩ =>
    let rest := (challengeNodesOn (next b) p).map
      ⟨fun c => ⟨.inr ⟨b, c.val⟩, c.property⟩, fun c c' h => Subtype.ext (by
        have h' := congrArg Subtype.val h
        dsimp only at h'
        injection h' with h'
        injection h' with _ h')⟩
    match h : owner l a with
    | .receiver => .cons ⟨.inl ⟨⟩, h⟩ rest (by
        rw [Finset.mem_map]
        rintro ⟨c, -, hc⟩
        exact Sum.inr_ne_inl (congrArg Subtype.val hc))
    | .sender => rest

/-- Some receiver node on the transcript turns the state from false to true. -/
def EscapeAlong : (s : FreeM P PUnit) →
    (∀ {t : FreeM P PUnit}, (sp : Cursor.Spine s t) → PrefixMoves l sp → Prop) →
    PathAlong l s → Prop
  | .pure _, _, _ => False
  | .liftBind a next, G, ⟨x, tr⟩ =>
    (owner l a = .receiver ∧ ¬ G (.root _) ⟨⟩ ∧
      G (.down (l.toFunB a x) (.root _)) ⟨⟨x, rfl⟩, ⟨⟩⟩) ∨
    EscapeAlong (next (l.toFunB a x))
      (fun sp history => G (.down (l.toFunB a x) sp) ⟨⟨x, rfl⟩, history⟩) tr

/-- A family false at the root, kept false by sender moves and false only at rejected leaves,
escapes along every accepted transcript. -/
theorem escapeAlong_of_accepts (s : FreeM P PUnit) :
    ∀ (G : ∀ {t : FreeM P PUnit}, (sp : Cursor.Spine s t) → PrefixMoves l sp → Prop)
      (accepts : PathAlong l s → Prop),
      (∀ {a next} (sp : Cursor.Spine s (.liftBind a next)) history, owner l a = .sender →
        ¬ G sp history → ∀ x,
          ¬ G (sp.comp (.down (l.toFunB a x) (.root _))) (PrefixMoves.snoc l sp history x)) →
      (∀ (sp : Cursor.Spine s (.pure ⟨⟩)) history,
        ¬ G sp history → ¬ accepts (PrefixMoves.complete l sp history)) →
      ¬ G (.root s) ⟨⟩ → ∀ tr, accepts tr → EscapeAlong l s G tr := by
  induction s using FreeM.rec with
  | pure u =>
    cases u
    intro G accepts _ hleaf hroot tr hacc
    exact hleaf (.root _) ⟨⟩ hroot hacc
  | liftBind a next ih =>
    intro G accepts hsend hleaf hroot tr hacc
    rcases tr with ⟨x, tr⟩
    by_cases hx : G (.down (l.toFunB a x) (.root _)) ⟨⟨x, rfl⟩, ⟨⟩⟩
    · left
      refine ⟨?_, hroot, hx⟩
      cases hown : owner l a with
      | sender => exact absurd hx (hsend (.root _) ⟨⟩ hown hroot x)
      | receiver => rfl
    · right
      exact ih (l.toFunB a x) (fun sp history => G (.down (l.toFunB a x) sp) ⟨⟨x, rfl⟩, history⟩)
        (fun tr => accepts ⟨x, tr⟩)
        (fun sp history hown hG y => hsend (.down _ sp) ⟨⟨x, rfl⟩, history⟩ hown hG y)
        (fun sp history hG => hleaf (.down _ sp) ⟨⟨x, rfl⟩, history⟩ hG) hx tr hacc

/-- On an accepted transcript of a false admissible statement, some challenge node on the path
turns the state from false to true. -/
theorem StateFunction.escapeAlong {s : FreeM P PUnit} {S : Type}
    {admissible language : S → Prop} {accepts : S → PathAlong l s → Prop}
    (F : StateFunction l s S admissible language accepts) {stmt : S}
    (hadm : admissible stmt) (hlang : ¬ language stmt) {tr : PathAlong l s}
    (hacc : accepts stmt tr) :
    EscapeAlong l s (fun sp history => F.toFun sp history stmt) tr :=
  escapeAlong_of_accepts l s (fun sp history => F.toFun sp history stmt) (accepts stmt)
    (fun sp history hown hG x => F.send sp history stmt hown hG x)
    (fun sp history hG => F.leaf sp history stmt hG) (fun h => hlang (F.root stmt hadm h)) tr hacc

/-- A flip at a challenge node, averaged over a random prefix before the node, has probability at
most the node's error. -/
theorem flip_random_prefix_le {α : Type} {s : FreeM P PUnit}
    (G : ∀ {t : FreeM P PUnit}, (sp : Cursor.Spine s t) → PrefixMoves l sp → Prop)
    (draw : QueryImpl (challengeSpec l s) ProbComp) {a : P.A} {next : P.B a → FreeM P PUnit}
    (sp : Cursor.Spine s (.liftBind a next)) (h : owner l a = .receiver) {e : ℝ≥0∞}
    (hlocal : ∀ history : PrefixMoves l sp,
      letI : MeasurableSpace (Move l a) := ⊤
      𝒟[sampleAt l draw sp h] {x | ¬ G sp history ∧
        G (sp.comp (.down (l.toFunB a x) (.root _))) (PrefixMoves.snoc l sp history x)} ≤ e)
    (author : ProbComp α) (prefixOf : α → PrefixMoves l sp) :
    Pr{let y ← author; let x ← sampleAt l draw sp h}[¬ G sp (prefixOf y) ∧
      G (sp.comp (.down (l.toFunB a x) (.root _))) (PrefixMoves.snoc l sp (prefixOf y) x)] ≤ e := by
  let : MeasurableSpace (Move l a) := ⊤
  have bound := prEvent_bind_le_of_forall_le author (fun y => (fun x => ¬ G sp (prefixOf y) ∧
    G (sp.comp (.down (l.toFunB a x) (.root _))) (PrefixMoves.snoc l sp (prefixOf y) x)) <$>
      sampleAt l draw sp h) (fun z => z) (ε := e) fun y => by
    rw [prEvent_map, prEvent_eq_evalDist (α := Move l a) _ _ measurable_from_top]
    exact hlocal (prefixOf y)
  rwa [id_map'] at bound

end Escape

section Plain

variable {m : Type → Type} [Monad m] [LawfulMonad m]

/-- The sampler passes over a message node. -/
private theorem sampler_message {X : Type} {next : X → Protocol}
    (d : (c : ChallengeNode plainSig (.liftBind (.message X) next)) →
      m (challengeSpec plainSig (.liftBind (.message X) next) c)) :
    sampler plainSig (.liftBind (.message X) next) d =
      pure fun x => sampler plainSig (next x) fun c => d ⟨.inr ⟨x, c.val⟩, c.property⟩ := by
  exact map_pure _ _

/-- The sampler draws at a challenge node, then samples the rest of the protocol. -/
private theorem sampler_challenge {C : Type} {next : PUnit → Protocol}
    (d : (c : ChallengeNode plainSig (.liftBind (.challenge C) next)) →
      m (challengeSpec plainSig (.liftBind (.challenge C) next) c)) :
    sampler plainSig (.liftBind (.challenge C) next) d =
      (fun x => ⟨x, sampler plainSig (next ⟨⟩) fun c => d ⟨.inr ⟨⟨⟩, c.val⟩, c.property⟩⟩) <$>
        d ⟨.inl ⟨⟩, rfl⟩ := by
  exact Functor.map_map _ _ _

/-- At a message node the prover sends a move, then the rest of the protocol runs. -/
private theorem run_sampler_message {β X : Type} {next : X → Protocol}
    {Out : PathAlong plainSig (.liftBind (.message X) next) → Type}
    (p : Focal plainSig m (.liftBind (.message X) next) Out)
    (d : (c : ChallengeNode plainSig (.liftBind (.message X) next)) →
      m (challengeSpec plainSig (.liftBind (.message X) next) c))
    (g : ((tr : PathAlong plainSig (.liftBind (.message X) next)) × Out tr × PUnit) → m β) :
    (TwoParty.Lens.run (.liftBind (PlainPos.message X) next : Protocol) p
        (sampler plainSig _ d) >>= g) =
      ((p : m ((x : X) × Focal plainSig m (next x) (fun tr => Out ⟨x, tr⟩))) >>= fun v =>
        TwoParty.Lens.run (next v.1) v.2
          (sampler plainSig (next v.1) fun c => d ⟨.inr ⟨v.1, c.val⟩, c.property⟩) >>= fun r =>
            g ⟨⟨v.1, r.1⟩, r.2.1, r.2.2⟩) := by
  rw [run_node, step_bind]
  refine (step_sender (owner plainSig (PlainPos.message X)) rfl _ _ _).trans ?_
  refine bind_congr fun v => ?_
  refine (congrArg (· >>= _) (sampler_message d)).trans ?_
  simp only [bind_assoc]
  exact (LawfulMonad.pure_bind (m := m) _ _).trans
    (bind_congr fun _ => LawfulMonad.pure_bind (m := m) _ _)

/-- At a challenge node the prover fixes a reply to each challenge, the challenge is drawn,
then the rest of the protocol runs. -/
private theorem run_sampler_challenge {β C : Type} {next : PUnit → Protocol}
    {Out : PathAlong plainSig (.liftBind (.challenge C) next) → Type}
    (p : Focal plainSig m (.liftBind (.challenge C) next) Out)
    (d : (c : ChallengeNode plainSig (.liftBind (.challenge C) next)) →
      m (challengeSpec plainSig (.liftBind (.challenge C) next) c))
    (g : ((tr : PathAlong plainSig (.liftBind (.challenge C) next)) × Out tr × PUnit) → m β) :
    (TwoParty.Lens.run (.liftBind (PlainPos.challenge C) next : Protocol) p
        (sampler plainSig _ d) >>= g) =
      ((p : m ((x : C) → Focal plainSig m (next ⟨⟩) (fun tr => Out ⟨x, tr⟩))) >>= fun f =>
        (d ⟨.inl ⟨⟩, rfl⟩ : m C) >>= fun x =>
        TwoParty.Lens.run (next ⟨⟩) (f x)
          (sampler plainSig (next ⟨⟩) fun c => d ⟨.inr ⟨⟨⟩, c.val⟩, c.property⟩) >>= fun r =>
            g ⟨⟨x, r.1⟩, r.2.1, r.2.2⟩) := by
  rw [run_node, step_bind]
  refine (step_receiver (owner plainSig (PlainPos.challenge C)) rfl _ _ _).trans ?_
  refine bind_congr fun f => ?_
  refine (congrArg (· >>= _) (sampler_challenge d)).trans ?_
  simp only [bind_assoc]
  exact (bind_map_left (m := m) _ _ _).trans
    (bind_congr fun _ => bind_congr fun _ => LawfulMonad.pure_bind (m := m) _ _)

/-- Simulating a bind threads the handler state from the first part to the second. -/
private theorem run'_simulateQ_bind {ι σ α β : Type} {spec : OracleSpec ι}
    (H : QueryImpl spec (StateT σ ProbComp)) (A : OracleComp spec α)
    (f : α → OracleComp spec β) (st : σ) :
    (simulateQ H (A >>= f)).run' st =
      (simulateQ H A).run st >>= fun z => (simulateQ H (f z.1)).run' z.2 := by
  simp only [simulateQ_bind, StateT.run'_eq, StateT.run_bind, _root_.map_bind]

/-- The node errors along a path through a message node are those of the subpath. -/
private theorem sum_challengeNodesOn_message {X : Type} {next : X → Protocol}
    (ε : ChallengeNode plainSig (.liftBind (PlainPos.message X) next) → ℝ≥0∞) (x : X)
    (path : Path (next x)) :
    ∑ c ∈ challengeNodesOn plainSig (.liftBind (PlainPos.message X) next) ⟨x, path⟩, ε c =
      ∑ c ∈ challengeNodesOn plainSig (next x) path, ε ⟨.inr ⟨x, c.val⟩, c.property⟩ :=
  Finset.sum_map _ _ _

/-- The node errors along a path through a challenge node are the node's error plus those of
the subpath. -/
private theorem sum_challengeNodesOn_challenge {C : Type} {next : PUnit → Protocol}
    (ε : ChallengeNode plainSig (.liftBind (PlainPos.challenge C) next) → ℝ≥0∞)
    (path : Path (next ⟨⟩)) :
    ∑ c ∈ challengeNodesOn plainSig (.liftBind (PlainPos.challenge C) next) ⟨⟨⟩, path⟩, ε c =
      ε ⟨.inl ⟨⟩, rfl⟩ +
        ∑ c ∈ challengeNodesOn plainSig (next ⟨⟩) path,
          ε ⟨.inr ⟨⟨⟩, c.val⟩, c.property⟩ := by
  change ∑ c ∈ Finset.cons _ _ ?h, ε c = _
  · rw [Finset.sum_cons, Finset.sum_map]
    rfl
  · rw [Finset.mem_map]
    rintro ⟨c, -, hc⟩
    exact Sum.inr_ne_inl (congrArg Subtype.val hc)

/-- Union bound over a second draw: if the event has probability at most `e` after every draw
outside `flip`, then it has probability at most the flip probability plus `e`. -/
private theorem prEvent_bind_bind_le_add {α γ β : Type} (mx : ProbComp α) (my : ProbComp γ)
    (F : α → γ → ProbComp β) (flip : γ → Prop) (ev : β → Prop) {e : ℝ≥0∞}
    (h : ∀ z x, ¬ flip x → Pr{let y ← F z x}[ev y] ≤ e) :
    Pr{let y ← mx >>= fun z => my >>= fun x => F z x}[ev y] ≤
      Pr{let _z ← mx; let x ← my}[flip x] + e := by
  have bound := prEvent_bind_le_prEvent_add (mx >>= fun z => (fun x => (z, x)) <$> my)
    (fun w => F w.1 w.2) (fun w => flip w.2) ev fun w hw => h w.1 w.2 hw
  simpa only [prEvent_norm] using bound

/-- Sampling at the root challenge node is the root draw. -/
private theorem sampleAt_root_challenge {C : Type} {next : PUnit → Protocol}
    (draw : QueryImpl (challengeSpec plainSig (.liftBind (PlainPos.challenge C) next)) ProbComp) :
    sampleAt plainSig draw (.root _) rfl = draw ⟨.inl ⟨⟩, rfl⟩ :=
  LawfulFunctor.id_map _

/-- A run whose continuation accepts only after an escape accepts with probability at most the
supremum, over shape paths, of the summed node errors along the path. -/
private theorem prEvent_run_le {ι σ β : Type} {spec : OracleSpec ι}
    (H : QueryImpl spec (StateT σ ProbComp)) (ev : β → Prop) (t : Protocol) :
    ∀ {Out : PathAlong plainSig t → Type}
      (G : ∀ {t' : Protocol}, (sp : Cursor.Spine t t') → PrefixMoves plainSig sp → Prop)
      (draw : QueryImpl (challengeSpec plainSig t) ProbComp)
      (ε : ChallengeNode plainSig t → ℝ≥0∞)
      (d : (c : ChallengeNode plainSig t) → OracleComp spec (challengeSpec plainSig t c))
      (k : (tr : PathAlong plainSig t) → Out tr → OracleComp spec β),
      (∀ c st, (simulateQ H (d c)).run st = (fun x => (x, st)) <$> draw c) →
      (∀ (a : PlainPos) (next : PlainPoly.B a → Protocol)
        (sp : Cursor.Spine t (.liftBind a next)) (h : owner plainSig a = .receiver)
        (history : PrefixMoves plainSig sp),
        letI : MeasurableSpace (Move plainSig a) := ⊤
        𝒟[sampleAt plainSig draw sp h] {x | ¬ G sp history ∧
          G (sp.comp (.down (plainSig.toFunB a x) (.root _)))
            (PrefixMoves.snoc plainSig sp history x)} ≤ ε (spineChallenge plainSig sp h)) →
      (∀ tr out st, ¬ EscapeAlong plainSig t G tr →
        Pr{let y ← (simulateQ H (k tr out)).run' st}[ev y] = 0) →
      ∀ (p : Focal plainSig (OracleComp spec) t Out) (st : σ),
      Pr{let y ← (simulateQ H (TwoParty.Lens.run t p (sampler plainSig t d) >>=
          fun r => k r.1 r.2.1)).run' st}[ev y] ≤
        ⨆ path : Path t, ∑ c ∈ challengeNodesOn plainSig t path, ε c := by
  induction t using FreeM.rec with
  | pure u =>
    cases u
    intro Out G draw ε d k hd hlocal hk p st
    refine le_trans ?_ zero_le
    have hrun : (TwoParty.Lens.run (.pure ⟨⟩ : Protocol) p (sampler plainSig _ d) >>=
        fun r => k r.1 r.2.1) = p >>= k ⟨⟩ := by
      refine (congrArg (fun x => x >>= fun r => k r.1 r.2.1)
        (run_done (l := plainSig) (OutC := fun _ => PUnit) p
        (sampler plainSig (.pure ⟨⟩) d : OracleComp spec PUnit))).trans ?_
      refine (bind_assoc _ _ _).trans (bind_congr fun out => ?_)
      exact LawfulMonad.pure_bind _ _
    rw [hrun, run'_simulateQ_bind]
    exact prEvent_bind_le_of_forall_le _ _ _ fun z => (hk ⟨⟩ z.1 z.2 id).le
  | liftBind a next ih =>
    cases a with
    | message X =>
      intro Out G draw ε d k hd hlocal hk p st
      rw [run_sampler_message, run'_simulateQ_bind]
      refine prEvent_bind_le_of_forall_le _ _ _ fun z => ?_
      refine (ih z.1.1 (fun sp history => G (.down z.1.1 sp) ⟨⟨z.1.1, rfl⟩, history⟩)
        (fun c => draw ⟨.inr ⟨z.1.1, c.val⟩, c.property⟩)
        (fun c => ε ⟨.inr ⟨z.1.1, c.val⟩, c.property⟩)
        (fun c => d ⟨.inr ⟨z.1.1, c.val⟩, c.property⟩) (fun tr out => k ⟨z.1.1, tr⟩ out)
        (fun c st => hd _ st)
        (fun a' next' sp h history => hlocal a' next' (.down z.1.1 sp) h ⟨⟨z.1.1, rfl⟩, history⟩)
        (fun tr out st hne => hk ⟨z.1.1, tr⟩ out st fun hesc =>
          hesc.elim (fun h => nomatch h.1) hne) z.1.2 z.2).trans ?_
      refine iSup_le fun path => le_iSup_of_le ⟨z.1.1, path⟩ ?_
      rw [sum_challengeNodesOn_message]
    | challenge C =>
      intro Out G draw ε d k hd hlocal hk p st
      rw [run_sampler_challenge, run'_simulateQ_bind]
      simp only [run'_simulateQ_bind H (d ⟨.inl ⟨⟩, rfl⟩), hd, bind_map_left]
      have hcont := fun (x : C) hk'
          (f : (x : C) → Focal plainSig (OracleComp spec) (next ⟨⟩) (fun tr => Out ⟨x, tr⟩))
          (st' : σ) => ih ⟨⟩
        (fun sp history => G (.down ⟨⟩ sp) ⟨⟨x, rfl⟩, history⟩)
        (fun c => draw ⟨.inr ⟨⟨⟩, c.val⟩, c.property⟩)
        (fun c => ε ⟨.inr ⟨⟨⟩, c.val⟩, c.property⟩)
        (fun c => d ⟨.inr ⟨⟨⟩, c.val⟩, c.property⟩) (fun tr out => k ⟨x, tr⟩ out)
        (fun c st => hd _ st)
        (fun a' next' sp h history => hlocal a' next' (.down ⟨⟩ sp) h ⟨⟨x, rfl⟩, history⟩)
        hk' (f x) st'
      rcases isEmpty_or_nonempty (Path (next ⟨⟩)) with hempty | hne
      · have : IsEmpty (PathAlong plainSig (next ⟨⟩)) :=
          ⟨fun tr => isEmptyElim (projectPathAlong plainSig _ tr)⟩
        refine le_trans ?_ zero_le
        refine prEvent_bind_le_of_forall_le _ _ _ fun z =>
          prEvent_bind_le_of_forall_le _ _ _ fun x => ?_
        refine (hcont x (fun tr => isEmptyElim tr) z.1 z.2).trans ?_
        rw [iSup_of_empty]
        exact bot_le
      · refine (prEvent_bind_bind_le_add ((simulateQ H p).run st) (draw ⟨.inl ⟨⟩, rfl⟩)
          (fun z (x : C) => (simulateQ H (TwoParty.Lens.run (next ⟨⟩) (z.1 x)
            (sampler plainSig (next ⟨⟩) fun c => d ⟨.inr ⟨⟨⟩, c.val⟩, c.property⟩) >>=
              fun r => k ⟨x, r.1⟩ r.2.1)).run' z.2)
          (fun x : C => ¬ G (.root _) ⟨⟩ ∧ G (.down ⟨⟩ (.root _)) ⟨⟨x, rfl⟩, ⟨⟩⟩) ev
          fun z x hx => hcont x (fun tr out st hne => hk ⟨x, tr⟩ out st fun hesc =>
            hesc.elim (fun h => hx ⟨h.2.1, h.2.2⟩) hne) z.1 z.2).trans ?_
        have hflip := flip_random_prefix_le plainSig G draw (.root _) rfl
          (fun history => hlocal _ _ (.root _) rfl history) ((simulateQ H p).run st) fun _ => ⟨⟩
        rw [sampleAt_root_challenge] at hflip
        refine (add_le_add hflip le_rfl).trans ?_
        rw [ENNReal.add_iSup]
        exact iSup_le fun path => le_iSup_of_le ⟨⟨⟩, path⟩
          (le_of_eq (sum_challengeNodesOn_challenge ε path).symm)

end Plain

/-- Round-by-round soundness implies soundness for every initial state distribution. The error is
the supremum, over shape paths, of the sum of the node errors along the path. -/
theorem Verifier.soundness_of_rbrSoundness {ι σ S T : Type} {ambient : OracleSpec ι}
    {s : Protocol} {V : Verifier ambient s S T} {init : ProbComp σ}
    {impl : QueryImpl ambient (StateT σ ProbComp)}
    {input : StatementProblem S} {output : StatementProblem T}
    {draw : QueryImpl (challengeSpec plainSig s) ProbComp}
    {ε : ChallengeNode plainSig s → ℝ≥0∞}
    (h : V.rbrSoundness impl input output draw ε) :
    V.soundness init impl draw input output
      (⨆ path : Path s, ∑ c ∈ challengeNodesOn plainSig s path, ε c) := by
  obtain ⟨F, hF⟩ := h
  intro Out stmt hadm hlang (p : Prover plainSig ambient s Out)
  let : MeasurableSpace (Observation plainSig s Out T) := ⊤
  change 𝒟[experiment init impl draw (V.run stmt p)] _ ≤ _
  rw [← prEvent_eq_evalDist _ _ measurable_from_top]
  unfold experiment
  refine prEvent_bind_le_of_forall_le _ _ _ fun st => ?_
  let k : (tr : PathAlong plainSig s) → Out tr →
      OracleComp (ambient + challengeSpec plainSig s) (Observation plainSig s Out T) :=
    fun tr out => (fun v => (⟨tr, out, v⟩ : Observation plainSig s Out T)) <$>
      OracleComp.liftComp
        (V.decide stmt (projectPathAlong plainSig s tr) (toPlainView s tr)).run
        (ambient + challengeSpec plainSig s)
  have hrun : V.run stmt p = TwoParty.Lens.run s
      (Prover.simulate (fun q => liftM ((ambient + challengeSpec plainSig s).query (.inl q))) p)
      (sampler plainSig s fun c => liftM ((ambient + challengeSpec plainSig s).query (.inr c)))
        >>= fun r => k r.1 r.2.1 := by
    unfold Verifier.run
    refine bind_congr fun r => ?_
    exact LawfulMonad.bind_pure_comp _ _
  rw [hrun]
  refine prEvent_run_le (impl.addLift draw) _ s (fun sp history => F.toFun sp history stmt) draw ε
    _ k ?_ (hF stmt hadm hlang) ?_ _ st
  · intro c st
    rw [QueryImpl.addLift_def, QueryImpl.simulateQ_add_query_right, QueryImpl.liftTarget_apply,
      StateT.run_liftM]
    exact LawfulMonad.bind_pure_comp _ _
  · intro tr out st hne
    by_contra hpos
    refine hne (StateFunction.escapeAlong plainSig F hadm hlang (tr := tr) ⟨st, ?_⟩)
    let : MeasurableSpace (Option T) := ⊤
    rw [← prEvent_eq_evalDist _ _ measurable_from_top]
    simp only [k, QueryImpl.addLift_def, simulateQ_map, QueryImpl.simulateQ_add_liftComp_left,
      QueryImpl.liftTarget_self, StateT.run'_eq, StateT.run_map, Functor.map_map] at hpos
    rw [StateT.run'_eq, prEvent_map]
    exact pos_iff_ne_zero.2 hpos

/-- Round-by-round soundness implies soundness with the sum of all node errors. -/
theorem Verifier.soundness_of_rbrSoundness_tsum {ι σ S T : Type} {ambient : OracleSpec ι}
    {s : Protocol} {V : Verifier ambient s S T} {init : ProbComp σ}
    {impl : QueryImpl ambient (StateT σ ProbComp)}
    {input : StatementProblem S} {output : StatementProblem T}
    {draw : QueryImpl (challengeSpec plainSig s) ProbComp}
    {ε : ChallengeNode plainSig s → ℝ≥0∞}
    (h : V.rbrSoundness impl input output draw ε) :
    V.soundness init impl draw input output (∑' c, ε c) := fun Out stmt hadm hlang p =>
  (soundness_of_rbrSoundness (init := init) h Out stmt hadm hlang p).trans
    (iSup_le fun _ => ENNReal.sum_le_tsum _)

/-- If every node error is at most `e` and every shape path meets at most `k` challenge nodes,
round-by-round soundness implies soundness with error `k • e`. -/
theorem Verifier.soundness_of_rbrSoundness_uniform {ι σ S T : Type} {ambient : OracleSpec ι}
    {s : Protocol} {V : Verifier ambient s S T} {init : ProbComp σ}
    {impl : QueryImpl ambient (StateT σ ProbComp)}
    {input : StatementProblem S} {output : StatementProblem T}
    {draw : QueryImpl (challengeSpec plainSig s) ProbComp}
    {ε : ChallengeNode plainSig s → ℝ≥0∞} {e : ℝ≥0∞} {k : ℕ}
    (h : V.rbrSoundness impl input output draw ε) (hε : ∀ c, ε c ≤ e)
    (hcount : ∀ path, (challengeNodesOn plainSig s path).card ≤ k) :
    V.soundness init impl draw input output (k • e) := fun Out stmt hadm hlang p =>
  (soundness_of_rbrSoundness (init := init) h Out stmt hadm hlang p).trans <| iSup_le fun path =>
    (Finset.sum_le_sum fun c _ => hε c).trans <| by
      rw [Finset.sum_const]
      exact nsmul_le_nsmul_left zero_le (hcount path)

end Interaction.Core

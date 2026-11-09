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
also when the prefix before the node is random, and also when a possibly failing author selects
the node together with its prefix. The union bound over the challenge nodes of a path therefore
bounds soundness by the supremum, over shape paths, of the sum of the node errors along the path.

One induction over the protocol tree, for any signature lens, gives this bound for plain and
oracle verifiers in the classical model. An oracle verifier's acceptance is its decision on the
input data and the run's payloads, with the output read through its output oracle map.
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

/-- At a fixed receiver node, a flip averaged over a random full prefix before the node has
probability at most any bound on the flip probability at each prefix. -/
theorem flip_random_history_le {α : Type} {s : FreeM P PUnit}
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

/-- A receiver node reached by a structural cursor, with the full moves before it. -/
structure ReceiverPrefix (s : FreeM P PUnit) where
  /-- The position at the node. -/
  pos : P.A
  /-- The subtrees after the node. -/
  next : P.B pos → FreeM P PUnit
  /-- The structural cursor from the root to the node. -/
  spine : Cursor.Spine s (.liftBind pos next)
  /-- The receiver owns the node. -/
  receiver : owner l pos = .receiver
  /-- The full moves before the node, including erased payloads. -/
  history : PrefixMoves l spine

/-- The challenge node at which a receiver prefix ends. -/
abbrev ReceiverPrefix.node {s : FreeM P PUnit} (pfx : ReceiverPrefix l s) : ChallengeNode l s :=
  spineChallenge l pfx.spine pfx.receiver

/-- A fresh move at the end of a receiver prefix turns the state from false to true. -/
abbrev ReceiverPrefix.Flips {s : FreeM P PUnit}
    (G : ∀ {t : FreeM P PUnit}, (sp : Cursor.Spine s t) → PrefixMoves l sp → Prop)
    (pfx : ReceiverPrefix l s) (x : Move l pfx.pos) : Prop :=
  ¬ G pfx.spine pfx.history ∧
    G (pfx.spine.comp (.down (l.toFunB pfx.pos x) (.root _)))
      (PrefixMoves.snoc l pfx.spine pfx.history x)

/-- A possibly failing author selects a receiver node and a full prefix before it, then a fresh
move is drawn at the selected node. If every node bounds the flip probability at each of its
prefixes by its error, and each selectable node has error at most `e`, the flip has probability at
most `e`. Author failure contributes no mass. -/
theorem flip_random_prefix_le {α : Type} {s : FreeM P PUnit}
    (G : ∀ {t : FreeM P PUnit}, (sp : Cursor.Spine s t) → PrefixMoves l sp → Prop)
    (draw : QueryImpl (challengeSpec l s) ProbComp) (ε : ChallengeNode l s → ℝ≥0∞)
    (hlocal : ∀ (a : P.A) (next : P.B a → FreeM P PUnit)
      (sp : Cursor.Spine s (.liftBind a next)) (h : owner l a = .receiver)
      (history : PrefixMoves l sp),
      letI : MeasurableSpace (Move l a) := ⊤
      𝒟[sampleAt l draw sp h] {x | ¬ G sp history ∧
        G (sp.comp (.down (l.toFunB a x) (.root _)))
          (PrefixMoves.snoc l sp history x)} ≤ ε (spineChallenge l sp h))
    (author : OptionT ProbComp α) (select : α → ReceiverPrefix l s) {e : ℝ≥0∞}
    (hselect : ∀ y, ε (select y).node ≤ e) :
    Pr{let flip ← (author >>= fun y => (select y).Flips l G <$>
      OptionT.lift (sampleAt l draw (select y).spine (select y).receiver))}[flip] ≤ e := by
  have bound := prEvent_bind_le_of_forall_le author (fun y => (select y).Flips l G <$>
    OptionT.lift (sampleAt l draw (select y).spine (select y).receiver)) id (ε := e) fun y => by
      let : MeasurableSpace (Move l (select y).pos) := ⊤
      rw [prEvent_map, OptionT.prEvent_lift,
        prEvent_eq_evalDist (α := Move l (select y).pos) _ _ measurable_from_top]
      exact (hlocal _ _ (select y).spine (select y).receiver (select y).history).trans
        (hselect y)
  simpa only [prEvent_norm, id_eq] using bound

end Escape

section Run

variable {P : PFunctor.{1, 0}} {l : PFunctor.Lens P rolePoly}

section Sampler

variable {m : Type → Type} [Monad m] [LawfulMonad m]

/-- A sender slot built by rewriting with an ownership equation is its pure payload. -/
private theorem cast_map_pure_sender {X : Type} {B B' : X → Type} {r : TwoParty.Role}
    (h : r = .sender) (e : Choice .counterpart r X B = ((x : X) → B x)) (G : (x : X) → B x)
    (Φ : ∀ x, B x → B' x) :
    cast (congrArg (fun r => m (Choice .counterpart r X B')) h)
      (Choice.map .counterpart r Φ <$> (pure (Eq.mpr e G) : m _)) = pure fun x => Φ x (G x) := by
  subst h
  exact map_pure _ _

/-- A receiver slot built by rewriting with an ownership equation maps its draw. -/
private theorem cast_map_map_receiver {X : Type} {B B' : X → Type} {r : TwoParty.Role}
    (h : r = .receiver) (e : Choice .counterpart r X B = ((x : X) × B x))
    (G : X → (x : X) × B x) (mx : m X) (Φ : ∀ x, B x → B' x) :
    cast (congrArg (fun r => m (Choice .counterpart r X B')) h)
      (Choice.map .counterpart r Φ <$> ((fun x => Eq.mpr e (G x)) <$> mx)) =
        (fun x => ⟨(G x).1, Φ _ (G x).2⟩) <$> mx := by
  subst h
  exact Functor.map_map _ _ _

/-- The sampler passes over a sender node. -/
private theorem sampler_sender {a : P.A} {next : P.B a → FreeM P PUnit} (h : owner l a = .sender)
    (d : (c : ChallengeNode l (.liftBind a next)) → m (challengeSpec l (.liftBind a next) c)) :
    cast (congrArg (fun r => m (Choice .counterpart r (Move l a)
      (fun x => Counterpart l m (next (l.toFunB a x)) (fun _ => PUnit)))) h)
      (sampler l (.liftBind a next) d) =
    pure fun x => sampler l (next (l.toFunB a x))
      fun c => d ⟨.inr ⟨l.toFunB a x, c.val⟩, c.property⟩ := by
  simp only [sampler, PureEnd.toStrategy, PureEnd.mapOutput, samplerEnd]
  split
  · exact cast_map_pure_sender h _ _ _
  · rename_i h'
    cases h.symm.trans h'

/-- The sampler draws at a receiver node, then samples the rest of the protocol. -/
private theorem sampler_receiver {a : P.A} {next : P.B a → FreeM P PUnit}
    (h : owner l a = .receiver)
    (d : (c : ChallengeNode l (.liftBind a next)) → m (challengeSpec l (.liftBind a next) c)) :
    cast (congrArg (fun r => m (Choice .counterpart r (Move l a)
      (fun x => Counterpart l m (next (l.toFunB a x)) (fun _ => PUnit)))) h)
      (sampler l (.liftBind a next) d) =
    (fun x => ⟨x, sampler l (next (l.toFunB a x))
      fun c => d ⟨.inr ⟨l.toFunB a x, c.val⟩, c.property⟩⟩) <$> d ⟨.inl ⟨⟩, h⟩ := by
  simp only [sampler, PureEnd.toStrategy, PureEnd.mapOutput, samplerEnd]
  split
  · rename_i h'
    cases h.symm.trans h'
  · exact cast_map_map_receiver h _ (fun x => ⟨x, _⟩) _ _

/-- At a sender node the prover sends a move, then the rest of the protocol runs. -/
private theorem run_sampler_sender {β : Type} {a : P.A} {next : P.B a → FreeM P PUnit}
    (h : owner l a = .sender) {Out : PathAlong l (.liftBind a next) → Type}
    (p : Focal l m (.liftBind a next) Out)
    (d : (c : ChallengeNode l (.liftBind a next)) → m (challengeSpec l (.liftBind a next) c))
    (g : ((tr : PathAlong l (.liftBind a next)) × Out tr × PUnit) → m β) :
    (TwoParty.Lens.run (.liftBind a next) p (sampler l _ d) >>= g) =
      (cast (congrArg (fun r => m (Choice .focal r (Move l a)
          (fun x => Focal l m (next (l.toFunB a x)) (fun tr => Out ⟨x, tr⟩)))) h) p >>= fun v =>
        TwoParty.Lens.run (next (l.toFunB a v.1)) v.2
          (sampler l _ fun c => d ⟨.inr ⟨l.toFunB a v.1, c.val⟩, c.property⟩) >>= fun r =>
            g ⟨⟨v.1, r.1⟩, r.2.1, r.2.2⟩) := by
  rw [run_node, step_bind]
  refine (step_sender (owner l a) h _ _ _).trans ?_
  refine bind_congr fun v => ?_
  refine (congrArg (· >>= _) (sampler_sender h d)).trans ?_
  simp only [bind_assoc]
  exact (LawfulMonad.pure_bind (m := m) _ _).trans
    (bind_congr fun _ => LawfulMonad.pure_bind (m := m) _ _)

/-- At a receiver node the prover fixes a reply to each move, the move is drawn, then the rest of
the protocol runs. -/
private theorem run_sampler_receiver {β : Type} {a : P.A} {next : P.B a → FreeM P PUnit}
    (h : owner l a = .receiver) {Out : PathAlong l (.liftBind a next) → Type}
    (p : Focal l m (.liftBind a next) Out)
    (d : (c : ChallengeNode l (.liftBind a next)) → m (challengeSpec l (.liftBind a next) c))
    (g : ((tr : PathAlong l (.liftBind a next)) × Out tr × PUnit) → m β) :
    (TwoParty.Lens.run (.liftBind a next) p (sampler l _ d) >>= g) =
      (cast (congrArg (fun r => m (Choice .focal r (Move l a)
          (fun x => Focal l m (next (l.toFunB a x)) (fun tr => Out ⟨x, tr⟩)))) h) p >>= fun f =>
        (d ⟨.inl ⟨⟩, h⟩ : m (Move l a)) >>= fun x =>
        TwoParty.Lens.run (next (l.toFunB a x)) (f x)
          (sampler l _ fun c => d ⟨.inr ⟨l.toFunB a x, c.val⟩, c.property⟩) >>= fun r =>
            g ⟨⟨x, r.1⟩, r.2.1, r.2.2⟩) := by
  rw [run_node, step_bind]
  refine (step_receiver (owner l a) h _ _ _).trans ?_
  refine bind_congr fun f => ?_
  refine (congrArg (· >>= _) (sampler_receiver h d)).trans ?_
  simp only [bind_assoc]
  exact (bind_map_left (m := m) _ _ _).trans
    (bind_congr fun _ => bind_congr fun _ => LawfulMonad.pure_bind (m := m) _ _)

end Sampler

/-- The node errors along a path through a sender node are those of the subpath. -/
private theorem sum_challengeNodesOn_sender {a : P.A} {next : P.B a → FreeM P PUnit}
    (h : owner l a = .sender) (ε : ChallengeNode l (.liftBind a next) → ℝ≥0∞) (b : P.B a)
    (path : Path (next b)) :
    ∑ c ∈ challengeNodesOn l (.liftBind a next) ⟨b, path⟩, ε c =
      ∑ c ∈ challengeNodesOn l (next b) path, ε ⟨.inr ⟨b, c.val⟩, c.property⟩ := by
  simp only [challengeNodesOn]
  split
  · rename_i h'
    cases h.symm.trans h'
  · exact Finset.sum_map _ _ _

/-- The node errors along a path through a receiver node are the node's error plus those of
the subpath. -/
private theorem sum_challengeNodesOn_receiver {a : P.A} {next : P.B a → FreeM P PUnit}
    (h : owner l a = .receiver) (ε : ChallengeNode l (.liftBind a next) → ℝ≥0∞) (b : P.B a)
    (path : Path (next b)) :
    ∑ c ∈ challengeNodesOn l (.liftBind a next) ⟨b, path⟩, ε c =
      ε ⟨.inl ⟨⟩, h⟩ + ∑ c ∈ challengeNodesOn l (next b) path, ε ⟨.inr ⟨b, c.val⟩, c.property⟩ := by
  simp only [challengeNodesOn]
  split
  · rw [Finset.sum_cons, Finset.sum_map]
    rfl
  · rename_i h'
    cases h.symm.trans h'

/-- Simulating a bind threads the handler state from the first part to the second. -/
private theorem run'_simulateQ_bind {ι σ α β : Type} {spec : OracleSpec ι}
    (H : QueryImpl spec (StateT σ ProbComp)) (A : OracleComp spec α)
    (f : α → OracleComp spec β) (st : σ) :
    (simulateQ H (A >>= f)).run' st =
      (simulateQ H A).run st >>= fun z => (simulateQ H (f z.1)).run' z.2 := by
  simp only [simulateQ_bind, StateT.run'_eq, StateT.run_bind, _root_.map_bind]

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

/-- Sampling at the root receiver node is the root draw. -/
private theorem sampleAt_root {a : P.A} {next : P.B a → FreeM P PUnit}
    (draw : QueryImpl (challengeSpec l (.liftBind a next)) ProbComp)
    (h : owner l a = .receiver) :
    sampleAt l draw (.root _) h = (draw ⟨.inl ⟨⟩, h⟩ : ProbComp (Move l a)) :=
  LawfulFunctor.id_map _

/-- A run whose continuation accepts only after an escape accepts with probability at most the
supremum, over shape paths, of the summed node errors along the path. -/
private theorem prEvent_run_le {ι σ β : Type} {spec : OracleSpec ι}
    (H : QueryImpl spec (StateT σ ProbComp)) (ev : β → Prop) (t : FreeM P PUnit) :
    ∀ {Out : PathAlong l t → Type}
      (G : ∀ {t' : FreeM P PUnit}, (sp : Cursor.Spine t t') → PrefixMoves l sp → Prop)
      (draw : QueryImpl (challengeSpec l t) ProbComp)
      (ε : ChallengeNode l t → ℝ≥0∞)
      (d : (c : ChallengeNode l t) → OracleComp spec (challengeSpec l t c))
      (k : (tr : PathAlong l t) → Out tr → OracleComp spec β),
      (∀ c st, (simulateQ H (d c)).run st = (fun x => (x, st)) <$> draw c) →
      (∀ (a : P.A) (next : P.B a → FreeM P PUnit)
        (sp : Cursor.Spine t (.liftBind a next)) (h : owner l a = .receiver)
        (history : PrefixMoves l sp),
        letI : MeasurableSpace (Move l a) := ⊤
        𝒟[sampleAt l draw sp h] {x | ¬ G sp history ∧
          G (sp.comp (.down (l.toFunB a x) (.root _)))
            (PrefixMoves.snoc l sp history x)} ≤ ε (spineChallenge l sp h)) →
      (∀ tr out st, ¬ EscapeAlong l t G tr →
        Pr{let y ← (simulateQ H (k tr out)).run' st}[ev y] = 0) →
      ∀ (p : Focal l (OracleComp spec) t Out) (st : σ),
      Pr{let y ← (simulateQ H (TwoParty.Lens.run t p (sampler l t d) >>=
          fun r => k r.1 r.2.1)).run' st}[ev y] ≤
        ⨆ path : Path t, ∑ c ∈ challengeNodesOn l t path, ε c := by
  induction t using FreeM.rec with
  | pure u =>
    cases u
    intro Out G draw ε d k hd hlocal hk p st
    refine le_trans ?_ zero_le
    have hrun : (TwoParty.Lens.run (.pure ⟨⟩ : FreeM P PUnit) p (sampler l _ d) >>=
        fun r => k r.1 r.2.1) = p >>= k ⟨⟩ := by
      refine (congrArg (fun x => x >>= fun r => k r.1 r.2.1)
        (run_done (l := l) (OutC := fun _ => PUnit) p
        (sampler l (.pure ⟨⟩) d : OracleComp spec PUnit))).trans ?_
      refine (bind_assoc _ _ _).trans (bind_congr fun out => ?_)
      exact LawfulMonad.pure_bind _ _
    rw [hrun, run'_simulateQ_bind]
    exact prEvent_bind_le_of_forall_le _ _ _ fun z => (hk ⟨⟩ z.1 z.2 id).le
  | liftBind a next ih =>
    intro Out G draw ε d k hd hlocal hk p st
    -- The induction hypothesis below the move `x`, with every index shifted past the node.
    have hsub := fun (x : Move l a) hk'
        (q : Focal l (OracleComp spec) (next (l.toFunB a x)) (fun tr => Out ⟨x, tr⟩))
        (st' : σ) => ih (l.toFunB a x)
      (fun sp history => G (.down (l.toFunB a x) sp) ⟨⟨x, rfl⟩, history⟩)
      (fun c => draw ⟨.inr ⟨l.toFunB a x, c.val⟩, c.property⟩)
      (fun c => ε ⟨.inr ⟨l.toFunB a x, c.val⟩, c.property⟩)
      (fun c => d ⟨.inr ⟨l.toFunB a x, c.val⟩, c.property⟩) (fun tr out => k ⟨x, tr⟩ out)
      (fun c st => hd _ st)
      (fun a' next' sp h history => hlocal a' next' (.down _ sp) h ⟨⟨x, rfl⟩, history⟩)
      hk' q st'
    rcases (show owner l a = .sender ∨ owner l a = .receiver by
      cases owner l a <;> simp) with hown | hown
    · rw [run_sampler_sender hown, run'_simulateQ_bind]
      refine prEvent_bind_le_of_forall_le _ _ _ fun z => ?_
      refine (hsub z.1.1 (fun tr out st hne => hk ⟨z.1.1, tr⟩ out st fun hesc =>
          hesc.elim (fun h => nomatch h.1.symm.trans hown) hne) z.1.2 z.2).trans ?_
      refine iSup_le fun path => le_iSup_of_le ⟨l.toFunB a z.1.1, path⟩ ?_
      rw [sum_challengeNodesOn_sender hown]
    · obtain ⟨q, hq⟩ : ∃ q : OracleComp spec ((x : Move l a) →
          Focal l (OracleComp spec) (next (l.toFunB a x)) (fun tr => Out ⟨x, tr⟩)),
          cast (congrArg (fun r => OracleComp spec (Choice .focal r (Move l a)
            (fun x => Focal l (OracleComp spec) (next (l.toFunB a x))
              (fun tr => Out ⟨x, tr⟩)))) hown) p = q := ⟨_, rfl⟩
      rw [run_sampler_receiver hown, hq, run'_simulateQ_bind]
      simp only [run'_simulateQ_bind H (d ⟨.inl ⟨⟩, hown⟩), hd, bind_map_left]
      rcases isEmpty_or_nonempty (Path (FreeM.liftBind a next)) with hempty | hne
      · refine le_trans ?_ zero_le
        refine prEvent_bind_le_of_forall_le _ _ _ fun z =>
          prEvent_bind_le_of_forall_le _ _ _ fun x => ?_
        have : IsEmpty (PathAlong l (next (l.toFunB a x))) :=
          ⟨fun tr => hempty.false ⟨_, projectPathAlong l _ tr⟩⟩
        refine (hsub x (fun tr => isEmptyElim tr) _ z.2).trans ?_
        have : IsEmpty (Path (next (l.toFunB a x))) := ⟨fun path => hempty.false ⟨_, path⟩⟩
        rw [iSup_of_empty]
        exact bot_le
      · refine (prEvent_bind_bind_le_add ((simulateQ H q).run st)
          (draw ⟨.inl ⟨⟩, hown⟩ : ProbComp (Move l a))
          (fun z (x : Move l a) => (simulateQ H (TwoParty.Lens.run (next (l.toFunB a x))
            (z.1 x) (sampler l _ fun c => d ⟨.inr ⟨l.toFunB a x, c.val⟩, c.property⟩) >>=
              fun r => k ⟨x, r.1⟩ r.2.1)).run' z.2)
          (fun x : Move l a => ¬ G (.root _) ⟨⟩ ∧
            G (.down (l.toFunB a x) (.root _)) ⟨⟨x, rfl⟩, ⟨⟩⟩) ev
          (e := ⨆ path : Path (FreeM.liftBind a next), ∑ c ∈ challengeNodesOn l (next path.1)
            path.2, ε ⟨.inr ⟨path.1, c.val⟩, c.property⟩)
          fun z x hx => (hsub x (fun tr out st hne => hk ⟨x, tr⟩ out st fun hesc =>
            hesc.elim (fun h => hx ⟨h.2.1, h.2.2⟩) hne) _ z.2).trans
            (iSup_le fun path => le_iSup_of_le ⟨l.toFunB a x, path⟩ le_rfl)).trans ?_
        have hflip := flip_random_history_le l G draw (.root _) hown
          (fun history => hlocal _ _ (.root _) hown history) ((simulateQ H q).run st) fun _ => ⟨⟩
        rw [sampleAt_root] at hflip
        refine (add_le_add hflip le_rfl).trans ?_
        rw [ENNReal.add_iSup]
        exact iSup_le fun path => le_iSup_of_le path
          (le_of_eq (sum_challengeNodesOn_receiver hown ε path.1 path.2).symm)

end Run

section Experiment

variable {ι κ ρ σ α : Type} {ambient : OracleSpec ι} {chal : OracleSpec κ}
  {resources : OracleSpec ρ}

/-- A challenge query, interpreted beside the ambient handler, is a fresh draw that keeps the
ambient state. -/
private theorem run_simulateQ_addLift_challenge (impl : QueryImpl ambient (StateT σ ProbComp))
    (draw : QueryImpl chal ProbComp) (c : κ) (st : σ) :
    (simulateQ (impl.addLift draw : QueryImpl (ambient + chal) (StateT σ ProbComp))
      (liftM ((ambient + chal).query (.inr c)))).run st = (fun x => (x, st)) <$> draw c := by
  rw [QueryImpl.addLift_def, QueryImpl.simulateQ_add_query_right, QueryImpl.liftTarget_apply,
    StateT.run_liftM]
  exact LawfulMonad.bind_pure_comp _ _

/-- Answering resource queries inside a program, then interpreting the program's ambient and
challenge queries, is interpreting ambient queries beside the resource answers. -/
theorem simulateQ_addLift_resources (impl : QueryImpl ambient (StateT σ ProbComp))
    (draw : QueryImpl chal ProbComp) (answer : QueryImpl resources Id)
    (program : OracleComp (ambient + resources) α) :
    simulateQ (impl.addLift draw : QueryImpl (ambient + chal) (StateT σ ProbComp))
      (simulateQ (QueryImpl.addLift
        ((fun q => liftM ((ambient + chal).query (.inl q))) :
          QueryImpl ambient (OracleComp (ambient + chal))) answer) program) =
      simulateQ (impl.addLift answer : QueryImpl (ambient + resources) (StateT σ ProbComp))
        program := by
  refine QueryImpl.simulateQ_simulateQ_eq_of_apply (fun q => ?_) program
  rcases q with q | q
  · simp
  · exact simulateQ_pure _ _

/-- An accepted output, read through a map, is an accepted result read through that map. -/
private theorem exists_map_some_iff {T U : Type} (f : T → U) (L : U → Prop) (v : Option T) :
    (∃ u, v.map f = some u ∧ L u) ↔ ∃ t, v = some t ∧ L (f t) := by
  cases v <;> simp

end Experiment

section PathBounds

variable {P : PFunctor.{1, 0}} {l : PFunctor.Lens P rolePoly} {s : FreeM P PUnit}

/-- The path supremum of summed node errors is at most the sum of all node errors. -/
theorem iSup_sum_challengeNodesOn_le_tsum (ε : ChallengeNode l s → ℝ≥0∞) :
    ⨆ path : Path s, ∑ c ∈ challengeNodesOn l s path, ε c ≤ ∑' c, ε c :=
  iSup_le fun _ => ENNReal.sum_le_tsum _

/-- If every node error is at most `e` and every shape path meets at most `k` challenge nodes,
the path supremum of summed node errors is at most `k • e`. -/
theorem iSup_sum_challengeNodesOn_le_nsmul {ε : ChallengeNode l s → ℝ≥0∞} {e : ℝ≥0∞} {k : ℕ}
    (hε : ∀ c, ε c ≤ e) (hcount : ∀ path, (challengeNodesOn l s path).card ≤ k) :
    ⨆ path : Path s, ∑ c ∈ challengeNodesOn l s path, ε c ≤ k • e :=
  iSup_le fun path => (Finset.sum_le_sum fun c _ => hε c).trans <| by
    rw [Finset.sum_const]
    exact nsmul_le_nsmul_left zero_le (hcount path)

end PathBounds

section Plain

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
  · exact fun c => run_simulateQ_addLift_challenge impl draw c
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
    (iSup_sum_challengeNodesOn_le_tsum ε)

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
  (soundness_of_rbrSoundness (init := init) h Out stmt hadm hlang p).trans
    (iSup_sum_challengeNodesOn_le_nsmul hε hcount)

end Plain

section OracleVerifier

variable {ι I J σ S T : Type} {ambient : OracleSpec ι} {s : OracleProtocol} {A : I → Type}
  {B : J → Type} {inputs : OracleFamily I A} {outputs : OracleFamily J B}
  {V : OracleVerifier ambient s S T inputs outputs} {init : ProbComp σ}
  {impl : QueryImpl ambient (StateT σ ProbComp)}
  {input : StatementProblem (S × (∀ i, A i))} {output : StatementProblem (T × (∀ j, B j))}
  {draw : QueryImpl (challengeSpec oracleSig s) ProbComp}
  {ε : ChallengeNode oracleSig s → ℝ≥0∞}

/-- Round-by-round soundness of an oracle verifier implies its soundness for every initial state
distribution. The error is the supremum, over shape paths, of the sum of the node errors along the
path. Acceptance is the verifier's decision on the input data and the run's payloads, with its
output read through the verifier's output oracle map. -/
theorem OracleVerifier.soundness_of_rbrSoundness
    (h : V.rbrSoundness impl input output draw ε) :
    V.soundness init impl draw input output
      (⨆ path : Path s, ∑ c ∈ challengeNodesOn oracleSig s path, ε c) := by
  obtain ⟨F, hF⟩ := h
  intro Out stmt hadm hlang (p : Prover oracleSig ambient s Out)
  let : MeasurableSpace (Observation oracleSig s Out (T × (∀ j, B j))) := ⊤
  change 𝒟[experiment init impl draw (V.run stmt.1 stmt.2 p)] _ ≤ _
  rw [← prEvent_eq_evalDist _ _ measurable_from_top]
  unfold experiment
  refine prEvent_bind_le_of_forall_le _ _ _ fun st => ?_
  let liftAmbient : QueryImpl ambient (OracleComp (ambient + challengeSpec oracleSig s)) :=
    fun q => liftM ((ambient + challengeSpec oracleSig s).query (.inl q))
  let k : (tr : PathAlong oracleSig s) → Out tr →
      OracleComp (ambient + challengeSpec oracleSig s)
        (Observation oracleSig s Out (T × (∀ j, B j))) := fun tr out =>
    (fun v => (⟨tr, out, v.map fun t => (t, (V.outputMap stmt.1 (projectPathAlong oracleSig s tr)
        (toView s tr)).f (sumData stmt.2 (payloads s tr)))⟩ :
        Observation oracleSig s Out (T × (∀ j, B j)))) <$>
      simulateQ (QueryImpl.addLift liftAmbient ((sumFamily inputs
        (pathFamily s (projectPathAlong oracleSig s tr))).behaviorOfRealizations
          (sumData stmt.2 (payloads s tr))))
        (V.decide stmt.1 (projectPathAlong oracleSig s tr) (toView s tr)).run
  have hrun : V.run stmt.1 stmt.2 p = TwoParty.Lens.run s (Prover.simulate liftAmbient p)
      (sampler oracleSig s fun c => liftM ((ambient + challengeSpec oracleSig s).query (.inr c)))
        >>= fun r => k r.1 r.2.1 := by
    unfold OracleVerifier.run
    refine bind_congr fun r => ?_
    exact LawfulMonad.bind_pure_comp _ _
  rw [hrun]
  refine prEvent_run_le (impl.addLift draw) _ s (fun sp history => F.toFun sp history stmt) draw ε
    _ k ?_ (hF stmt hadm hlang) ?_ _ st
  · exact fun c => run_simulateQ_addLift_challenge impl draw c
  · intro tr out st hne
    by_contra hpos
    refine hne (StateFunction.escapeAlong oracleSig F hadm hlang (tr := tr) ⟨st, ?_⟩)
    let : MeasurableSpace (Option T) := ⊤
    rw [← prEvent_eq_evalDist _ _ measurable_from_top]
    simp only [k, liftAmbient, simulateQ_map, simulateQ_addLift_resources, StateT.run'_eq,
      StateT.run_map, Functor.map_map, exists_map_some_iff] at hpos
    rw [StateT.run'_eq, prEvent_map]
    exact pos_iff_ne_zero.2 hpos

/-- Round-by-round soundness of an oracle verifier implies its soundness with the sum of all node
errors. -/
theorem OracleVerifier.soundness_of_rbrSoundness_tsum
    (h : V.rbrSoundness impl input output draw ε) :
    V.soundness init impl draw input output (∑' c, ε c) := fun Out stmt hadm hlang p =>
  (soundness_of_rbrSoundness (init := init) h Out stmt hadm hlang p).trans
    (iSup_sum_challengeNodesOn_le_tsum ε)

/-- If every node error is at most `e` and every shape path meets at most `k` challenge nodes,
round-by-round soundness of an oracle verifier implies its soundness with error `k • e`. -/
theorem OracleVerifier.soundness_of_rbrSoundness_uniform {e : ℝ≥0∞} {k : ℕ}
    (h : V.rbrSoundness impl input output draw ε) (hε : ∀ c, ε c ≤ e)
    (hcount : ∀ path, (challengeNodesOn oracleSig s path).card ≤ k) :
    V.soundness init impl draw input output (k • e) := fun Out stmt hadm hlang p =>
  (soundness_of_rbrSoundness (init := init) h Out stmt hadm hlang p).trans
    (iSup_sum_challengeNodesOn_le_nsmul hε hcount)

end OracleVerifier

end Interaction.Core

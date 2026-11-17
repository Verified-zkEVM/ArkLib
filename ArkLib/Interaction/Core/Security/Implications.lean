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

The protocol-tree bounds apply to any signature lens and any lawful monad with distribution
semantics. Challenges may depend on the full prefix; node-indexed fresh draws are a specialization.
The classical stateful wrappers use the same bound. An oracle verifier's acceptance is its decision
on the input data and the run's payloads, with its output read through its output oracle map.
-/

@[expose] public section

universe v uS uI wI wJ uι uκ uA u

namespace Interaction.Core
open PFunctor FreeM TwoParty.Lens OracleComp Oracle MeasureTheory
open scoped ENNReal

section Escape

variable {P : PFunctor.{uA, u}} (l : PFunctor.Lens P rolePoly.{u})

/-- The challenge nodes met along a shape path. -/
def challengeNodesOn : (s : FreeM P PUnit.{u + 1}) → Path s → Finset (ChallengeNode l s)
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
def EscapeAlong : (s : FreeM P PUnit.{u + 1}) →
    (∀ {t : FreeM P PUnit.{u + 1}}, (sp : Cursor.Spine s t) → PrefixMoves l sp → Prop) →
    PathAlong l s → Prop
  | .pure _, _, _ => False
  | .liftBind a next, G, ⟨x, tr⟩ =>
    (owner l a = .receiver ∧ ¬ G (.root _) ⟨⟩ ∧
      G (.down (l.toFunB a x) (.root _)) ⟨⟨x, rfl⟩, ⟨⟩⟩) ∨
    EscapeAlong (next (l.toFunB a x))
      (fun sp history => G (.down (l.toFunB a x) sp) ⟨⟨x, rfl⟩, history⟩) tr

/-- A family false at the root, kept false by sender moves and false only at rejected leaves,
escapes along every accepted transcript. -/
theorem escapeAlong_of_accepts (s : FreeM P PUnit.{u + 1}) :
    ∀ (G : ∀ {t : FreeM P PUnit.{u + 1}}, (sp : Cursor.Spine s t) → PrefixMoves l sp → Prop)
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
theorem StateFunction.escapeAlong {s : FreeM P PUnit.{u + 1}} {S : Type uS}
    {admissible language : S → Prop} {accepts : S → PathAlong l s → Prop}
    (F : StateFunction l s S admissible language accepts) {stmt : S}
    (hadm : admissible stmt) (hlang : ¬ language stmt) {tr : PathAlong l s}
    (hacc : accepts stmt tr) :
    EscapeAlong l s (fun sp history => F.toFun sp history stmt) tr :=
  escapeAlong_of_accepts l s (fun sp history => F.toFun sp history stmt) (accepts stmt)
    (fun sp history hown hG x => F.send sp history stmt hown hG x)
    (fun sp history hG => F.leaf sp history stmt hG) (fun h => hlang (F.root stmt hadm h)) tr hacc

/-- A receiver node reached by a structural cursor, with the full moves before it. -/
structure ReceiverPrefix (s : FreeM P PUnit.{u + 1}) where
  /-- The position at the node. -/
  pos : P.A
  /-- The subtrees after the node. -/
  next : P.B pos → FreeM P PUnit.{u + 1}
  /-- The structural cursor from the root to the node. -/
  spine : Cursor.Spine s (.liftBind pos next)
  /-- The receiver owns the node. -/
  receiver : owner l pos = .receiver
  /-- The full moves before the node, including erased payloads. -/
  history : PrefixMoves l spine

/-- The challenge node at which a receiver prefix ends. -/
abbrev ReceiverPrefix.node {s : FreeM P PUnit.{u + 1}} (pfx : ReceiverPrefix l s) :
    ChallengeNode l s :=
  spineChallenge l pfx.spine pfx.receiver

/-- A fresh move at the end of a receiver prefix turns the state from false to true. -/
abbrev ReceiverPrefix.Flips {s : FreeM P PUnit.{u + 1}}
    (G : ∀ {t : FreeM P PUnit.{u + 1}}, (sp : Cursor.Spine s t) → PrefixMoves l sp → Prop)
    (pfx : ReceiverPrefix l s) (x : Move l pfx.pos) : Prop :=
  ¬ G pfx.spine pfx.history ∧
    G (pfx.spine.comp (.down (l.toFunB pfx.pos x) (.root _)))
      (PrefixMoves.snoc l pfx.spine pfx.history x)

variable {P : PFunctor.{uA, 0}} (l : PFunctor.Lens P rolePoly)

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

/-- Encoded event marginals transport a full-prefix model's local bound to the actual move.
The model's sample and encoding may both depend on the full prefix. -/
theorem ReceiverPrefix.flip_le_of_encoded_marginals
    {m : Type → Type v} [Monad m] [EvalDistSemantics m] {s : FreeM P PUnit}
    (G : ∀ {t : FreeM P PUnit}, (sp : Cursor.Spine s t) → PrefixMoves l sp → Prop)
    (pfx : ReceiverPrefix l s) (action : m (Move l pfx.pos))
    {Result : Type} (sample : ProbComp Result) (encode : Move l pfx.pos → Result)
    (modelEvent : Result → Prop) {e : ℝ≥0∞}
    (marginals : ∀ event : Result → Prop,
      Pr{let x ← action}[event (encode x)] =
        Pr{let r ← sample}[event r])
    (extension : ∀ x, pfx.Flips l G x ↔ modelEvent (encode x))
    (localBound : Pr{let r ← sample}[modelEvent r] ≤ e) :
    Pr{let x ← action}[pfx.Flips l G x] ≤ e := by
  have events : pfx.Flips l G = fun x => modelEvent (encode x) :=
    funext fun x => propext (extension x)
  rw [events, marginals]
  exact localBound

/-- A possibly failing author may select a prefix-dependent model and flip event.
The local bound is averaged after the author, without requiring a node-indexed sampler. -/
theorem flip_random_model_le {α : Type} (author : OptionT ProbComp α)
    {Result : α → Type} (sample : (a : α) → ProbComp (Result a))
    (event : (a : α) → Result a → Prop) (error : α → ℝ≥0∞) {e : ℝ≥0∞}
    (hlocal : ∀ a, Pr{let x ← sample a}[event a x] ≤ error a)
    (herror : ∀ a, error a ≤ e) :
    Pr{let flip ← (author >>= fun a => event a <$> OptionT.lift (sample a))}[flip] ≤ e := by
  have bound := prEvent_bind_le_of_forall_le author
    (fun a => event a <$> OptionT.lift (sample a)) id (ε := e) fun a => by
      rw [prEvent_map, OptionT.prEvent_lift]
      exact (hlocal a).trans (herror a)
  simpa only [prEvent_norm, id_eq] using bound

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

variable {P : PFunctor.{uA, u}} {l : PFunctor.Lens P rolePoly.{u}}

/-- The node errors along a path through a sender node are those of the subpath. -/
private theorem sum_challengeNodesOn_sender {a : P.A} {next : P.B a → FreeM P PUnit.{u + 1}}
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
private theorem sum_challengeNodesOn_receiver {a : P.A} {next : P.B a → FreeM P PUnit.{u + 1}}
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

variable {P : PFunctor.{uA, 0}} {l : PFunctor.Lens P rolePoly}

/-- Sampling at the root receiver node is the root draw. -/
private theorem sampleAt_root {a : P.A} {next : P.B a → FreeM P PUnit}
    (draw : QueryImpl (challengeSpec l (.liftBind a next)) ProbComp)
    (h : owner l a = .receiver) :
    sampleAt l draw (.root _) h = (draw ⟨.inl ⟨⟩, h⟩ : ProbComp (Move l a)) :=
  LawfulFunctor.id_map _

private theorem prEvent_state_map {m : Type → Type v} [Monad m] [LawfulMonad m]
    [EvalDistSemantics m] [LawfulEvalDistSemantics m] {α β σ : Type}
    (c : StateT σ m α) (f : α → β) (st : σ) (event : β → Prop) :
    Pr{let x ← (f <$> c).run' st}[event x] =
      Pr{let x ← c.run' st}[event (f x)] := by
  rw [StateT.run'_map', prEvent_map]

private theorem prEvent_state_run' {m : Type → Type v} [Monad m] [LawfulMonad m]
    [EvalDistSemantics m] [LawfulEvalDistSemantics m] {α σ : Type}
    (c : StateT σ m α) (st : σ) (event : α → Prop) :
    Pr{let x ← c.run' st}[event x] = Pr{let x ← c.run st}[event x.1] := by
  rw [StateT.run'_eq, prEvent_map]

/-- Interpret a challenge at a cursor and transport its move to the cursor's position. -/
def challengeActionAt {m : Type → Type v} [Monad m] {ι : Type} {spec : OracleSpec ι}
    {σ : Type} {t : FreeM P PUnit} (H : QueryImpl spec (StateT σ m))
    (d : (c : ChallengeNode l t) → OracleComp spec (challengeSpec l t c))
    {a : P.A} {next : P.B a → FreeM P PUnit}
    (sp : Cursor.Spine t (.liftBind a next)) (h : owner l a = .receiver) :
    StateT σ m (Move l a) :=
  (fun x => Eq.mp (congrArg (Move l) (spineNode_position sp)) x) <$>
    simulateQ H (d (spineChallenge l sp h))

/-- Raw event marginals are preserved by transporting the move to a cursor. -/
theorem challengeActionAt_marginals {m : Type → Type v} [Monad m] [LawfulMonad m]
    [EvalDistSemantics m] [LawfulEvalDistSemantics m]
    {ι σ : Type} {spec : OracleSpec ι} {t : FreeM P PUnit}
    (H : QueryImpl spec (StateT σ m))
    (d : (c : ChallengeNode l t) → OracleComp spec (challengeSpec l t c))
    (draw : QueryImpl (challengeSpec l t) ProbComp)
    (marginals : ∀ c st (event : challengeSpec l t c → Prop),
      Pr{let x ← (simulateQ H (d c)).run' st}[event x] = Pr{let x ← draw c}[event x])
    {a : P.A} {next : P.B a → FreeM P PUnit}
    (sp : Cursor.Spine t (.liftBind a next)) (h : owner l a = .receiver)
    (st : σ) (event : Move l a → Prop) :
    Pr{let x ← (challengeActionAt H d sp h).run' st}[event x] =
      Pr{let x ← sampleAt l draw sp h}[event x] :=
  (prEvent_state_map (simulateQ H (d (spineChallenge l sp h))) _ st _).trans
    ((marginals (spineChallenge l sp h) st _).trans
      (prEvent_map (draw (spineChallenge l sp h)) _ event).symm)

/-- The root cursor does not change the type of the interpreted move. -/
private theorem challengeActionAt_root {m : Type → Type v} [Monad m] [LawfulMonad m]
    {ι σ : Type} {spec : OracleSpec ι} {a : P.A} {next : P.B a → FreeM P PUnit}
    (H : QueryImpl spec (StateT σ m))
    (d : (c : ChallengeNode l (.liftBind a next)) →
      OracleComp spec (challengeSpec l (.liftBind a next) c)) (h : owner l a = .receiver) :
    challengeActionAt H d (.root (.liftBind a next)) h = simulateQ H (d ⟨.inl ⟨⟩, h⟩) :=
  LawfulFunctor.id_map _

/-- A run whose continuation accepts only after an escape accepts with probability at most the
supremum, over shape paths, of the summed node errors along the path. -/
theorem prEvent_run_state_le_of_local {m : Type → Type v} [Monad m] [LawfulMonad m]
    [EvalDistSemantics m] [LawfulEvalDistSemantics m]
    {ι σ β : Type} {spec : OracleSpec ι}
    (H : QueryImpl spec (StateT σ m)) (ev : β → Prop) (t : FreeM P PUnit) :
    ∀ {Out : PathAlong l t → Type}
      (G : ∀ {t' : FreeM P PUnit}, (sp : Cursor.Spine t t') → PrefixMoves l sp → Prop)
      (ε : ChallengeNode l t → ℝ≥0∞)
      (d : (c : ChallengeNode l t) → OracleComp spec (challengeSpec l t c))
      (k : (tr : PathAlong l t) → Out tr → OracleComp spec β),
      (∀ (a : P.A) (next : P.B a → FreeM P PUnit)
        (sp : Cursor.Spine t (.liftBind a next)) (h : owner l a = .receiver)
        (history : PrefixMoves l sp) (st : σ),
        Pr{let x ← (challengeActionAt H d sp h).run' st}[¬ G sp history ∧
          G (sp.comp (.down (l.toFunB a x) (.root _)))
            (PrefixMoves.snoc l sp history x)] ≤ ε (spineChallenge l sp h)) →
      (∀ tr out st, ¬ EscapeAlong l t G tr →
        Pr{let y ← (simulateQ H (k tr out)).run' st}[ev y] = 0) →
      ∀ (p : Focal l (OracleComp spec) t Out) (st : σ),
      Pr{let y ← (simulateQ H (TwoParty.Lens.run t p (sampler l t d) >>=
          fun r => k r.1 r.2.1)).run' st}[ev y] ≤
        ⨆ path : Path t, ∑ c ∈ challengeNodesOn l t path, ε c := by
  induction t using FreeM.rec with
  | pure u =>
    cases u
    intro Out G ε d k hlocal hk p st
    refine le_trans ?_ zero_le
    have hrun : (TwoParty.Lens.run (.pure ⟨⟩ : FreeM P PUnit) p (sampler l _ d) >>=
        fun r => k r.1 r.2.1) = p >>= k ⟨⟩ := by
      refine (congrArg (fun x => x >>= fun r => k r.1 r.2.1)
        (run_done (l := l) (OutC := fun _ => PUnit) p
        (sampler l (.pure ⟨⟩) d : OracleComp spec PUnit))).trans ?_
      refine (bind_assoc _ _ _).trans (bind_congr fun out => ?_)
      exact LawfulMonad.pure_bind _ _
    rw [hrun, simulateQ_bind, StateT.run'_bind']
    exact prEvent_bind_le_of_forall_le _ _ _ fun z => (hk ⟨⟩ z.1 z.2 id).le
  | liftBind a next ih =>
    intro Out G ε d k hlocal hk p st
    -- The induction hypothesis below the move `x`, with every index shifted past the node.
    have hsub := fun (x : Move l a) hk'
        (q : Focal l (OracleComp spec) (next (l.toFunB a x)) (fun tr => Out ⟨x, tr⟩))
        (st' : σ) => ih (l.toFunB a x)
      (fun sp history => G (.down (l.toFunB a x) sp) ⟨⟨x, rfl⟩, history⟩)
      (fun c => ε ⟨.inr ⟨l.toFunB a x, c.val⟩, c.property⟩)
      (fun c => d ⟨.inr ⟨l.toFunB a x, c.val⟩, c.property⟩) (fun tr out => k ⟨x, tr⟩ out)
      (fun a' next' sp h history st => hlocal a' next' (.down _ sp) h ⟨⟨x, rfl⟩, history⟩ st)
      hk' q st'
    rcases (show owner l a = .sender ∨ owner l a = .receiver by
      cases owner l a <;> simp) with hown | hown
    · rw [run_sampler_sender hown, simulateQ_bind, StateT.run'_bind']
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
      rw [run_sampler_receiver hown, hq, simulateQ_bind, StateT.run'_bind']
      simp only [simulateQ_bind H (d ⟨.inl ⟨⟩, hown⟩),
        StateT.run'_bind' (simulateQ H (d ⟨.inl ⟨⟩, hown⟩))]
      rcases isEmpty_or_nonempty (Path (FreeM.liftBind a next)) with hempty | hne
      · refine le_trans ?_ zero_le
        refine prEvent_bind_le_of_forall_le _ _ _ fun z =>
          prEvent_bind_le_of_forall_le _ _ _ fun w => ?_
        let x := w.1
        have : IsEmpty (PathAlong l (next (l.toFunB a x))) :=
          ⟨fun tr => hempty.false ⟨_, projectPathAlong l _ tr⟩⟩
        refine (hsub x (fun tr => isEmptyElim tr) _ w.2).trans ?_
        have : IsEmpty (Path (next (l.toFunB a x))) := ⟨fun path => hempty.false ⟨_, path⟩⟩
        rw [iSup_of_empty]
        exact bot_le
      · refine prEvent_bind_le_of_forall_le _ _ _ fun z => ?_
        refine (prEvent_bind_le_prEvent_add
          ((simulateQ H (d ⟨.inl ⟨⟩, hown⟩)).run z.2)
          (fun w => (simulateQ H (TwoParty.Lens.run (next (l.toFunB a w.1))
            (z.1 w.1) (sampler l _ fun c => d ⟨.inr ⟨l.toFunB a w.1, c.val⟩, c.property⟩) >>=
              fun r => k ⟨w.1, r.1⟩ r.2.1)).run' w.2)
          (fun w => ¬ G (.root _) ⟨⟩ ∧
            G (.down (l.toFunB a w.1) (.root _)) ⟨⟨w.1, rfl⟩, ⟨⟩⟩) ev
          (ε := ⨆ path : Path (FreeM.liftBind a next),
            ∑ c ∈ challengeNodesOn l (next path.1) path.2,
              ε ⟨.inr ⟨path.1, c.val⟩, c.property⟩)
          fun w hx => (hsub w.1 (fun tr out st hne => hk ⟨w.1, tr⟩ out st fun hesc =>
            hesc.elim (fun h => hx ⟨h.2.1, h.2.2⟩) hne) _ w.2).trans
            (iSup_le fun path => le_iSup_of_le ⟨l.toFunB a w.1, path⟩ le_rfl)).trans ?_
        have hflip := hlocal a next (.root _) hown ⟨⟩ z.2
        rw [challengeActionAt_root] at hflip
        have hflip' : Pr{let w ← (simulateQ H (d ⟨.inl ⟨⟩, hown⟩)).run z.2}[
            ¬ G (.root _) ⟨⟩ ∧ G (.down (l.toFunB a w.1) (.root _))
              ⟨⟨w.1, rfl⟩, ⟨⟩⟩] ≤ ε ⟨.inl ⟨⟩, hown⟩ := by
          exact (prEvent_state_run' (simulateQ H (d ⟨.inl ⟨⟩, hown⟩)) z.2 _).symm.le.trans hflip
        refine (add_le_add hflip' le_rfl).trans ?_
        rw [ENNReal.add_iSup]
        exact iSup_le fun path => le_iSup_of_le path
          (le_of_eq (sum_challengeNodesOn_receiver hown ε path.1 path.2).symm)

/-- Fresh raw challenge marginals and local model bounds give the actual flip bound. -/
theorem prEvent_run_state_le {m : Type → Type v} [Monad m] [LawfulMonad m]
    [EvalDistSemantics m] [LawfulEvalDistSemantics m]
    {ι σ β : Type} {spec : OracleSpec ι}
    (H : QueryImpl spec (StateT σ m)) (ev : β → Prop) (t : FreeM P PUnit) :
    ∀ {Out : PathAlong l t → Type}
      (G : ∀ {t' : FreeM P PUnit}, (sp : Cursor.Spine t t') → PrefixMoves l sp → Prop)
      (draw : QueryImpl (challengeSpec l t) ProbComp)
      (ε : ChallengeNode l t → ℝ≥0∞)
      (d : (c : ChallengeNode l t) → OracleComp spec (challengeSpec l t c))
      (k : (tr : PathAlong l t) → Out tr → OracleComp spec β),
      (∀ c st (event : challengeSpec l t c → Prop),
        Pr{let x ← (simulateQ H (d c)).run' st}[event x] =
          Pr{let x ← draw c}[event x]) →
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
  intro Out G draw ε d k hd hlocal hk p st
  apply prEvent_run_state_le_of_local H ev t G ε d k _ hk p st
  intro a next sp h history st
  let event : Move l a → Prop := fun x => ¬ G sp history ∧
    G (sp.comp (.down (l.toFunB a x) (.root _))) (PrefixMoves.snoc l sp history x)
  let : MeasurableSpace (Move l a) := ⊤
  calc
    _ = Pr{let x ← sampleAt l draw sp h}[event x] :=
      challengeActionAt_marginals H d draw hd sp h st event
    _ ≤ _ := by
      rw [prEvent_eq_evalDist_of_discrete]
      exact hlocal a next sp h history

/-- For any lawful monad with distribution semantics, fresh challenge marginals and local flip
bounds bound acceptance by the supremum of the sums of node errors along shape paths.
The author and terminal continuation may fail. No attachment or losslessness is required. -/
theorem prEvent_run_le {m : Type → Type v} [Monad m] [LawfulMonad m]
    [EvalDistSemantics m] [LawfulEvalDistSemantics m]
    {ι β : Type} {spec : OracleSpec ι}
    (H : QueryImpl spec m) (ev : β → Prop) (t : FreeM P PUnit)
    {Out : PathAlong l t → Type}
    (G : ∀ {t' : FreeM P PUnit}, (sp : Cursor.Spine t t') → PrefixMoves l sp → Prop)
    (draw : QueryImpl (challengeSpec l t) ProbComp)
    (ε : ChallengeNode l t → ℝ≥0∞)
    (d : (c : ChallengeNode l t) → OracleComp spec (challengeSpec l t c))
    (k : (tr : PathAlong l t) → Out tr → OracleComp spec β)
    (hd : ∀ c (event : challengeSpec l t c → Prop),
      Pr{let x ← simulateQ H (d c)}[event x] = Pr{let x ← draw c}[event x])
    (hlocal : ∀ (a : P.A) (next : P.B a → FreeM P PUnit)
      (sp : Cursor.Spine t (.liftBind a next)) (h : owner l a = .receiver)
      (history : PrefixMoves l sp),
      letI : MeasurableSpace (Move l a) := ⊤
      𝒟[sampleAt l draw sp h] {x | ¬ G sp history ∧
        G (sp.comp (.down (l.toFunB a x) (.root _)))
          (PrefixMoves.snoc l sp history x)} ≤ ε (spineChallenge l sp h))
    (hk : ∀ tr out, ¬ EscapeAlong l t G tr →
      Pr{let y ← simulateQ H (k tr out)}[ev y] = 0)
    (p : Focal l (OracleComp spec) t Out) :
    Pr{let y ← simulateQ H (TwoParty.Lens.run t p (sampler l t d) >>=
      fun r => k r.1 r.2.1)}[ev y] ≤
        ⨆ path : Path t, ∑ c ∈ challengeNodesOn l t path, ε c := by
  have hlift {α : Type} (program : OracleComp spec α) (st : Unit) :
      (simulateQ (H.liftTarget (StateT Unit m)) program).run' st =
        simulateQ H program := by
    rw [simulateQ_liftTarget, StateT.liftM_def, StateT.run'_lift']
  simpa only [hlift] using prEvent_run_state_le (H.liftTarget (StateT Unit m)) ev t G
    draw ε d k (fun c st event => by rw [hlift]; exact hd c event) hlocal
    (fun tr out st hne => by rw [hlift]; exact hk tr out hne) p ()

end Run

section Experiment

/-- An accepted output, read through a map, is an accepted result read through that map. -/
private theorem exists_map_some_iff {T U : Type} (f : T → U) (L : U → Prop) (v : Option T) :
    (∃ u, v.map f = some u ∧ L u) ↔ ∃ t, v = some t ∧ L (f t) := by
  cases v <;> simp

/-- Lifting an ambient handler threads an unused state through the entire computation. -/
private theorem simulateQ_stateLift_run' {m : Type → Type v} [Monad m] [LawfulMonad m]
    {ι : Type uι} {σ α : Type} {spec : OracleSpec.{uι, 0} ι} (H : QueryImpl spec m)
    (c : OracleComp spec α) (st : σ) :
    (simulateQ (H.liftTarget (StateT σ m)) c).run' st = simulateQ H c := by
  rw [simulateQ_liftTarget, StateT.liftM_def, StateT.run'_lift']

/-- Deterministic resource answers commute with an unused state lift. -/
private theorem stateLift_addLift {m : Type → Type v} [Monad m] [LawfulMonad m]
    {ι : Type uι} {κ : Type uκ} {σ : Type}
    {spec : OracleSpec.{uι, 0} ι} {resources : OracleSpec.{uκ, 0} κ}
    (H : QueryImpl spec m) (answer : QueryImpl resources Id) :
    ((H.liftTarget (StateT σ m)).addLift answer : QueryImpl (spec + resources) (StateT σ m)) =
      (H.addLift answer : QueryImpl (spec + resources) m).liftTarget (StateT σ m) := by
  funext q
  rcases q with q | q
  · rfl
  · change (pure (answer q).run : StateT σ m _) = StateT.lift (pure (answer q).run)
    funext st
    change (pure ((answer q).run, st) : m _) =
      (pure (answer q).run >>= fun a => pure (a, st))
    rw [LawfulMonad.pure_bind]

end Experiment

section PrefixExecution

variable {P : PFunctor.{uA, 0}} (l : PFunctor.Lens P rolePoly)

/-- Actual prefix-dependent flip bounds control the full passive execution in any lawful
subprobability monad. Each draw is evaluated at its matching history. -/
theorem prEvent_runPrefixChallenges_le {m : Type → Type v} [Monad m] [LawfulMonad m]
    [EvalDistSemantics m] [LawfulEvalDistSemantics m] {ι β : Type} {spec : OracleSpec ι}
    (H : QueryImpl spec m) (ev : β → Prop) (s : FreeM P PUnit) :
    ∀ {Out : PathAlong l s → Type}
      (G : ∀ {t}, (sp : Cursor.Spine s t) → PrefixMoves l sp → Prop)
      (ε : ChallengeNode l s → ℝ≥0∞) (d : PrefixChallengePrograms l spec s)
      (k : (tr : PathAlong l s) → Out tr → OracleComp spec β),
      (∀ a next (sp : Cursor.Spine s (.liftBind a next)) (h : owner l a = .receiver) history,
        Pr{let x ← simulateQ H (d sp h history)}[¬ G sp history ∧
          G (sp.comp (.down (l.toFunB a x) (.root _)))
            (PrefixMoves.snoc l sp history x)] ≤ ε (spineChallenge l sp h)) →
      (∀ tr out, ¬ EscapeAlong l s G tr → Pr{let y ← simulateQ H (k tr out)}[ev y] = 0) →
      ∀ p : Focal l (OracleComp spec) s Out,
      Pr{let y ← simulateQ H (runPrefixChallenges l s p d >>= fun r => k r.1 r.2.1)}[ev y] ≤
        ⨆ path : Path s, ∑ c ∈ challengeNodesOn l s path, ε c := by
  induction s using FreeM.rec with
  | pure u =>
    cases u
    intro Out G ε d k hlocal hk p
    simp only [runPrefixChallenges_done, bind_assoc, LawfulMonad.pure_bind, simulateQ_bind]
    exact (prEvent_bind_le_of_forall_le _ _ _ fun out => (hk ⟨⟩ out id).le).trans zero_le
  | liftBind a next ih =>
    intro Out G ε d k hlocal hk p
    have hsub := fun (x : Move l a) hk'
        (q : Focal l (OracleComp spec) (next (l.toFunB a x)) (fun tr => Out ⟨x, tr⟩)) =>
      ih (l.toFunB a x)
        (fun sp history => G (.down (l.toFunB a x) sp) ⟨⟨x, rfl⟩, history⟩)
        (fun c => ε ⟨.inr ⟨l.toFunB a x, c.val⟩, c.property⟩)
        (fun sp h history => d (.down (l.toFunB a x) sp) h ⟨⟨x, rfl⟩, history⟩)
        (fun tr out => k ⟨x, tr⟩ out)
        (fun a' next' sp h history => hlocal a' next' (.down _ sp) h ⟨⟨x, rfl⟩, history⟩)
        hk' q
    simp only [simulateQ_bind] at hsub
    cases hown : owner l a with
    | sender =>
      rw [runPrefixChallenges_sender l hown]
      simp only [simulateQ_bind, bind_assoc, LawfulMonad.pure_bind]
      refine prEvent_bind_le_of_forall_le _ _ _ fun v => ?_
      refine (hsub v.1 (fun tr out hne => hk ⟨v.1, tr⟩ out fun hesc =>
        hesc.elim (fun h => nomatch h.1.symm.trans hown) hne) v.2).trans ?_
      refine iSup_le fun path => le_iSup_of_le ⟨l.toFunB a v.1, path⟩ ?_
      rw [sum_challengeNodesOn_sender hown]
    | receiver =>
      rw [runPrefixChallenges_receiver l hown]
      simp only [simulateQ_bind, bind_assoc, LawfulMonad.pure_bind]
      refine prEvent_bind_le_of_forall_le _ _ _ fun f => ?_
      rcases isEmpty_or_nonempty (Path (FreeM.liftBind a next)) with hempty | hne
      · refine le_trans ?_ zero_le
        refine prEvent_bind_le_of_forall_le _ _ _ fun x => ?_
        let : IsEmpty (PathAlong l (next (l.toFunB a x))) :=
          ⟨fun tr => hempty.false ⟨_, projectPathAlong l _ tr⟩⟩
        refine (hsub x (fun tr => isEmptyElim tr) (f x)).trans ?_
        let : IsEmpty (Path (next (l.toFunB a x))) := ⟨fun path => hempty.false ⟨_, path⟩⟩
        rw [iSup_of_empty]
        exact bot_le
      · refine (prEvent_bind_le_prEvent_add _ _
          (fun x => ¬ G (.root _) ⟨⟩ ∧
            G (.down (l.toFunB a x) (.root _)) ⟨⟨x, rfl⟩, ⟨⟩⟩) ev
          (ε := ⨆ path : Path (FreeM.liftBind a next),
            ∑ c ∈ challengeNodesOn l (next path.1) path.2,
              ε ⟨.inr ⟨path.1, c.val⟩, c.property⟩)
          fun x hx => (hsub x (fun tr out hne => hk ⟨x, tr⟩ out fun hesc =>
            hesc.elim (fun h => hx ⟨h.2.1, h.2.2⟩) hne) (f x)).trans
            (iSup_le fun path => le_iSup_of_le ⟨l.toFunB a x, path⟩ le_rfl)).trans ?_
        refine (add_le_add (hlocal a next (.root _) hown ⟨⟩) le_rfl).trans ?_
        rw [ENNReal.add_iSup]
        exact iSup_le fun path => le_iSup_of_le path
          (le_of_eq (sum_challengeNodesOn_receiver hown ε path.1 path.2).symm)

/-- A full-prefix state certificate bounds soundness with prefix-dependent public challenges.
The terminal continuation may fail; valid acceptance is required only when its event has mass. -/
theorem prEvent_runPrefixChallenges_soundness {m : Type → Type v}
    [Monad m] [LawfulMonad m] [EvalDistSemantics m] [LawfulEvalDistSemantics m]
    {ι β : Type} {spec : OracleSpec ι} {s : FreeM P PUnit} {S : Type uS}
    {admissible language : S → Prop} {accepts : S → PathAlong l s → Prop}
    (F : StateFunction l s S admissible language accepts)
    (H : QueryImpl spec m) (ev : β → Prop) (ε : ChallengeNode l s → ℝ≥0∞)
    (d : PrefixChallengePrograms l spec s) {Out : PathAlong l s → Type}
    (k : (tr : PathAlong l s) → Out tr → OracleComp spec β)
    (stmt : S) (hadm : admissible stmt) (hlang : ¬ language stmt)
    (hlocal : ∀ a next (sp : Cursor.Spine s (.liftBind a next))
      (h : owner l a = .receiver) history,
      Pr{let x ← simulateQ H (d sp h history)}[¬ F.toFun sp history stmt ∧
        F.toFun (sp.comp (.down (l.toFunB a x) (.root _)))
          (PrefixMoves.snoc l sp history x) stmt] ≤ ε (spineChallenge l sp h))
    (terminal : ∀ tr out, 0 < Pr{let y ← simulateQ H (k tr out)}[ev y] → accepts stmt tr)
    (p : Focal l (OracleComp spec) s Out) :
    Pr{let y ← simulateQ H (runPrefixChallenges l s p d >>= fun r => k r.1 r.2.1)}[ev y] ≤
      ⨆ path : Path s, ∑ c ∈ challengeNodesOn l s path, ε c := by
  apply prEvent_runPrefixChallenges_le l H ev s (fun sp history => F.toFun sp history stmt)
    ε d k hlocal _ p
  intro tr out hne
  by_contra hpos
  exact hne (F.escapeAlong l hadm hlang (terminal tr out (pos_iff_ne_zero.2 hpos)))

end PrefixExecution

section PathBounds

variable {P : PFunctor.{uA, u}} {l : PFunctor.Lens P rolePoly.{u}}
  {s : FreeM P PUnit.{u + 1}}

/-- The path supremum of summed node errors is at most the sum of all node errors. -/
theorem iSup_sum_challengeNodesOn_le_tsum (ε : ChallengeNode l s → ℝ≥0∞) :
    ⨆ path : Path s, ∑ c ∈ challengeNodesOn l s path, ε c ≤ ∑' c, ε c :=
  iSup_le fun _ => ENNReal.sum_le_tsum _

/-- Distinct challenge ranks along each path bound the path error by the finite rank sum.
The ranks need not be consecutive, and errors may vary arbitrarily with the rank. -/
theorem iSup_sum_challengeNodesOn_le_rank_sum (ε : ChallengeNode l s → ℝ≥0∞)
    (rank : ChallengeNode l s → ℕ) (error : ℕ → ℝ≥0∞) (first count : ℕ)
    (hinj : ∀ path, Set.InjOn rank (challengeNodesOn l s path))
    (hrange : ∀ path c, c ∈ challengeNodesOn l s path → rank c ∈ Finset.Ico first count)
    (hε : ∀ c, ε c ≤ error (rank c)) :
    ⨆ path : Path s, ∑ c ∈ challengeNodesOn l s path, ε c ≤
      ∑ j ∈ Finset.Ico first count, error j := by
  classical
  refine iSup_le fun path => ?_
  calc
    ∑ c ∈ challengeNodesOn l s path, ε c ≤
        ∑ c ∈ challengeNodesOn l s path, error (rank c) :=
      Finset.sum_le_sum fun c _ => hε c
    _ = ∑ j ∈ (challengeNodesOn l s path).image rank, error j :=
      (Finset.sum_image (hinj path)).symm
    _ ≤ ∑ j ∈ Finset.Ico first count, error j :=
      Finset.sum_le_sum_of_subset (by
        intro j hj
        obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hj
        exact hrange path c hc)

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

/-- Stateful interpretation preserves the initial distribution and all possible terminal states. -/
theorem Verifier.soundnessUsing_of_localSoundness
    {m : Type → Type v} [Monad m] [LawfulMonad m]
    [EvalDistSemantics m] [LawfulEvalDistSemantics m]
    {ι σ : Type} {S : Type uS} {ambient : OracleSpec ι}
    {s : Protocol} {T : Path s → Type} {V : Verifier ambient s S T} {init : m σ}
    {H : QueryImpl (ambient + challengeSpec plainSig s) (StateT σ m)}
    {input : StatementProblem S} {output : PathProblem s T}
    {ε : ChallengeNode plainSig s → ℝ≥0∞}
    (F : StateFunction plainSig s _ (input.admissible ()) (input.language ())
      (fun stmt tr => ∃ st, V.validAcceptanceUsing (fun q => H (.inl q))
        (fun x => x.run' st) output.language stmt tr))
    (localBound : ∀ stmt, input.admissible () stmt → ¬ input.language () stmt →
      ∀ a next (sp : Cursor.Spine s (.liftBind a next)) (h : owner plainSig a = .receiver)
        (history : PrefixMoves plainSig sp) st,
        Pr{let x ← (challengeActionAt H
          (fun c => liftM ((ambient + challengeSpec plainSig s).query (.inr c)))
            sp h).run' st}[¬ F.toFun sp history stmt ∧
              F.toFun (sp.comp (.down (plainSig.toFunB a x) (.root _)))
                (PrefixMoves.snoc plainSig sp history x) stmt] ≤ ε (spineChallenge plainSig sp h)) :
    V.soundnessUsing (fun c => do (simulateQ H c).run' (← init)) input output
      (⨆ path : Path s, ∑ c ∈ challengeNodesOn plainSig s path, ε c) := by
  intro Out stmt hadm hlang (p : Prover plainSig ambient s Out)
  change Pr{let obs ← (do (simulateQ H (V.run stmt p)).run' (← init))}[_] ≤ _
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
  refine prEvent_run_state_le_of_local H _ s
    (fun sp history => F.toFun sp history stmt) ε _ k
    (localBound stmt hadm hlang) ?_ _ st
  intro tr out st hne
  by_contra hpos
  apply hne
  apply StateFunction.escapeAlong plainSig F hadm hlang
  refine ⟨st, pos_iff_ne_zero.2 ?_⟩
  have hdec := QueryImpl.simulateQ_liftComp_left_eq_of_apply H
    (fun q => H (.inl q)) (fun _ => rfl)
    (V.decide stmt (projectPathAlong plainSig s tr) (toPlainView s tr)).run
  simpa only [Verifier.validAcceptanceUsing, k, simulateQ_map, hdec,
    StateT.run'_eq, StateT.run_map, prEvent_map] using hpos

/-- Fresh challenge marginals specialize the bound on actual flip events. -/
theorem Verifier.soundnessUsing_of_rbrSoundness
    {m : Type → Type v} [Monad m] [LawfulMonad m]
    [EvalDistSemantics m] [LawfulEvalDistSemantics m]
    {ι σ : Type} {S : Type uS} {ambient : OracleSpec ι}
    {s : Protocol} {T : Path s → Type} {V : Verifier ambient s S T} {init : m σ}
    {H : QueryImpl (ambient + challengeSpec plainSig s) (StateT σ m)}
    {input : StatementProblem S} {output : PathProblem s T}
    {draw : QueryImpl (challengeSpec plainSig s) ProbComp}
    {ε : ChallengeNode plainSig s → ℝ≥0∞}
    (fresh : FreshChallengesAt H draw)
    (h : Core.rbrSoundness plainSig s (input.admissible ()) (input.language ())
      (fun stmt tr => ∃ st, V.validAcceptanceUsing (fun q => H (.inl q))
        (fun x => x.run' st) output.language stmt tr) draw ε) :
    V.soundnessUsing (fun c => do (simulateQ H c).run' (← init)) input output
      (⨆ path : Path s, ∑ c ∈ challengeNodesOn plainSig s path, ε c) := by
  obtain ⟨F, hF⟩ := h
  apply Verifier.soundnessUsing_of_localSoundness F
  intro stmt hadm hlang a next sp h history st
  let event : Move plainSig a → Prop := fun x => ¬ F.toFun sp history stmt ∧
    F.toFun (sp.comp (.down (plainSig.toFunB a x) (.root _)))
      (PrefixMoves.snoc plainSig sp history x) stmt
  let : MeasurableSpace (Move plainSig a) := ⊤
  calc
    _ = Pr{let x ← sampleAt plainSig draw sp h}[event x] :=
      challengeActionAt_marginals H _ draw (fun c st event => by
        rw [simulateQ_spec_query]
        exact fresh st c event) sp h st event
    _ ≤ _ := by
      rw [prEvent_eq_evalDist_of_discrete]
      exact hF stmt hadm hlang a next sp h history

/-- Fresh challenge marginals turn round-by-round soundness into soundness of the plain run
in any lawful distribution monad, including monads with missing probability mass. -/
theorem Verifier.soundnessWith_of_rbrSoundness {m : Type → Type v} [Monad m] [LawfulMonad m]
    [EvalDistSemantics m] [LawfulEvalDistSemantics m]
    {ι : Type} {S : Type uS} {ambient : OracleSpec ι} {s : Protocol}
    {T : Path s → Type} {V : Verifier ambient s S T}
    {H : QueryImpl (ambient + challengeSpec plainSig s) m}
    {input : StatementProblem S} {output : PathProblem s T}
    {draw : QueryImpl (challengeSpec plainSig s) ProbComp}
    {ε : ChallengeNode plainSig s → ℝ≥0∞}
    (fresh : FreshChallenges H draw)
    (h : Core.rbrSoundness plainSig s (input.admissible ()) (input.language ())
      (V.validAcceptanceWith (fun q => H (.inl q)) (output.language)) draw ε) :
    V.soundnessWith H input output
      (⨆ path : Path s, ∑ c ∈ challengeNodesOn plainSig s path, ε c) := by
  let H' := H.liftTarget (StateT Unit m)
  have hlift {α : Type} (c : OracleComp (ambient + challengeSpec plainSig s) α)
      (st : Unit) : (simulateQ H' c).run' st = simulateQ H c := by
    rw [simulateQ_liftTarget, StateT.liftM_def, StateT.run'_lift']
  have hfresh : FreshChallengesAt H' draw := by
    intro st c event
    simpa only [H', QueryImpl.liftTarget_apply, StateT.liftM_def, StateT.run'_lift']
      using fresh c event
  have hacc : ∀ stmt tr,
      (∃ st : Unit, V.validAcceptanceUsing (fun q => H' (.inl q))
        (fun x => x.run' st) output.language stmt tr) ↔
      V.validAcceptanceWith (fun q => H (.inl q)) output.language stmt tr := by
    intro stmt tr
    change (∃ st : Unit, 0 < Pr{let v ←
      (simulateQ (QueryImpl.liftTarget (StateT Unit m) (fun q => H (.inl q) : QueryImpl ambient m))
        (V.decide stmt (projectPathAlong plainSig s tr) (toPlainView s tr)).run).run' st}[
          ∃ t, v = some t ∧ output.language (projectPathAlong plainSig s tr) t]) ↔ _
    simp only [simulateQ_stateLift_run', exists_const]
    rfl
  have h' : Core.rbrSoundness plainSig s (input.admissible ()) (input.language ())
      (fun stmt tr => ∃ st : Unit, V.validAcceptanceUsing (fun q => H' (.inl q))
        (fun x => x.run' st) output.language stmt tr) draw ε := by
    simpa only [hacc] using h
  have bound := Verifier.soundnessUsing_of_rbrSoundness (init := pure ()) hfresh h'
  simpa only [hlift, LawfulMonad.pure_bind] using bound

/-- Fresh round-by-round soundness bounds soundness by the sum of all node errors. -/
theorem Verifier.soundnessWith_of_rbrSoundness_tsum {m : Type → Type v} [Monad m] [LawfulMonad m]
    [EvalDistSemantics m] [LawfulEvalDistSemantics m]
    {ι : Type} {S : Type uS} {ambient : OracleSpec ι} {s : Protocol}
    {T : Path s → Type} {V : Verifier ambient s S T}
    {H : QueryImpl (ambient + challengeSpec plainSig s) m}
    {input : StatementProblem S} {output : PathProblem s T}
    {draw : QueryImpl (challengeSpec plainSig s) ProbComp}
    {ε : ChallengeNode plainSig s → ℝ≥0∞}
    (fresh : FreshChallenges H draw)
    (h : Core.rbrSoundness plainSig s (input.admissible ()) (input.language ())
      (V.validAcceptanceWith (fun q => H (.inl q)) (output.language)) draw ε) :
    V.soundnessWith H input output (∑' c, ε c) := fun Out stmt hadm hlang p =>
  (soundnessWith_of_rbrSoundness fresh h Out stmt hadm hlang p).trans
    (iSup_sum_challengeNodesOn_le_tsum ε)

/-- Uniform local errors and a path length bound give soundness error `k • e`. -/
theorem Verifier.soundnessWith_of_rbrSoundness_uniform {m : Type → Type v} [Monad m] [LawfulMonad m]
    [EvalDistSemantics m] [LawfulEvalDistSemantics m]
    {ι : Type} {S : Type uS} {ambient : OracleSpec ι} {s : Protocol}
    {T : Path s → Type} {V : Verifier ambient s S T}
    {H : QueryImpl (ambient + challengeSpec plainSig s) m}
    {input : StatementProblem S} {output : PathProblem s T}
    {draw : QueryImpl (challengeSpec plainSig s) ProbComp}
    {ε : ChallengeNode plainSig s → ℝ≥0∞}
    {e : ℝ≥0∞} {k : ℕ}
    (fresh : FreshChallenges H draw)
    (h : Core.rbrSoundness plainSig s (input.admissible ()) (input.language ())
      (V.validAcceptanceWith (fun q => H (.inl q)) (output.language)) draw ε)
    (hε : ∀ c, ε c ≤ e)
    (hcount : ∀ path, (challengeNodesOn plainSig s path).card ≤ k) :
    V.soundnessWith H input output (k • e) := fun Out stmt hadm hlang p =>
  (soundnessWith_of_rbrSoundness fresh h Out stmt hadm hlang p).trans
    (iSup_sum_challengeNodesOn_le_nsmul hε hcount)

/-- Round-by-round soundness implies soundness for every initial state distribution. The error is
the supremum, over shape paths, of the sum of the node errors along the path. -/
theorem Verifier.soundness_of_rbrSoundness {ι σ : Type} {S : Type uS} {ambient : OracleSpec ι}
    {s : Protocol} {T : Path s → Type} {V : Verifier ambient s S T} {init : ProbComp σ}
    {impl : QueryImpl ambient (StateT σ ProbComp)}
    {input : StatementProblem S} {output : PathProblem s T}
    {draw : QueryImpl (challengeSpec plainSig s) ProbComp}
    {ε : ChallengeNode plainSig s → ℝ≥0∞}
    (h : V.rbrSoundness impl input output draw ε) :
    V.soundness init impl draw input output
      (⨆ path : Path s, ∑ c ∈ challengeNodesOn plainSig s path, ε c) := by
  apply (V.soundness_iff_soundnessUsing init impl draw input output _).mpr
  apply Verifier.soundnessUsing_of_rbrSoundness (freshChallengesAt_addLift impl draw)
  simpa only [Verifier.rbrSoundness,
    Verifier.validAcceptance_iff_validAcceptanceUsing, QueryImpl.addLift_def,
    QueryImpl.add_apply_inl, QueryImpl.liftTarget_self] using h

/-- Round-by-round soundness implies soundness with the sum of all node errors. -/
theorem Verifier.soundness_of_rbrSoundness_tsum {ι σ : Type} {S : Type uS} {ambient : OracleSpec ι}
    {s : Protocol} {T : Path s → Type} {V : Verifier ambient s S T} {init : ProbComp σ}
    {impl : QueryImpl ambient (StateT σ ProbComp)}
    {input : StatementProblem S} {output : PathProblem s T}
    {draw : QueryImpl (challengeSpec plainSig s) ProbComp}
    {ε : ChallengeNode plainSig s → ℝ≥0∞}
    (h : V.rbrSoundness impl input output draw ε) :
    V.soundness init impl draw input output (∑' c, ε c) := fun Out stmt hadm hlang p =>
  (soundness_of_rbrSoundness (init := init) h Out stmt hadm hlang p).trans
    (iSup_sum_challengeNodesOn_le_tsum ε)

/-- If every node error is at most `e` and every shape path meets at most `k` challenge nodes,
round-by-round soundness implies soundness with error `k • e`. -/
theorem Verifier.soundness_of_rbrSoundness_uniform {ι σ : Type} {S : Type uS}
    {ambient : OracleSpec ι}
    {s : Protocol} {T : Path s → Type} {V : Verifier ambient s S T} {init : ProbComp σ}
    {impl : QueryImpl ambient (StateT σ ProbComp)}
    {input : StatementProblem S} {output : PathProblem s T}
    {draw : QueryImpl (challengeSpec plainSig s) ProbComp}
    {ε : ChallengeNode plainSig s → ℝ≥0∞} {e : ℝ≥0∞} {k : ℕ}
    (h : V.rbrSoundness impl input output draw ε) (hε : ∀ c, ε c ≤ e)
    (hcount : ∀ path, (challengeNodesOn plainSig s path).card ≤ k) :
    V.soundness init impl draw input output (k • e) := fun Out stmt hadm hlang p =>
  (soundness_of_rbrSoundness (init := init) h Out stmt hadm hlang p).trans
    (iSup_sum_challengeNodesOn_le_nsmul hε hcount)

end Plain

/-- Stateful interpretation preserves the initial distribution and all possible terminal states. -/
theorem OracleVerifier.soundnessUsing_of_localSoundness
    {m : Type → Type v} [Monad m] [LawfulMonad m]
    [EvalDistSemantics m] [LawfulEvalDistSemantics m]
    {ι σ : Type} {I : Type uI} {S : Type uS} {ambient : OracleSpec ι}
  {s : OracleProtocol} {T : Path s → Type} {A : I → Type} {J : Path s → Type}
  {B : (p : Path s) → J p → Type} {inputs : OracleFamily.{uI, 0, wI} I A}
  {outputs : (p : Path s) → OracleFamily.{0, 0, wJ} (J p) (B p)}
  {V : OracleVerifier ambient s S T inputs outputs} {init : m σ}
  {H : QueryImpl (ambient + challengeSpec oracleSig s) (StateT σ m)}
  {input : StatementProblem (S × (∀ i, A i))} {output : PathProblem s (OracleVerifier.Output T B)}
  {ε : ChallengeNode oracleSig s → ℝ≥0∞}
    (F : StateFunction oracleSig s _ (input.admissible ()) (input.language ())
      (fun stmt tr => ∃ st, V.validAcceptanceUsing (fun q => H (.inl q))
        (fun x => x.run' st) output.language stmt tr))
    (localBound : ∀ stmt, input.admissible () stmt → ¬ input.language () stmt →
      ∀ a next (sp : Cursor.Spine s (.liftBind a next)) (h : owner oracleSig a = .receiver)
        (history : PrefixMoves oracleSig sp) st,
        Pr{let x ← (challengeActionAt H
          (fun c => liftM ((ambient + challengeSpec oracleSig s).query (.inr c)))
            sp h).run' st}[¬ F.toFun sp history stmt ∧
              F.toFun (sp.comp (.down (oracleSig.toFunB a x) (.root _)))
                (PrefixMoves.snoc oracleSig sp history x) stmt] ≤
                  ε (spineChallenge oracleSig sp h)) :
    V.soundnessUsing (fun c => do (simulateQ H c).run' (← init)) input output
      (⨆ path : Path s, ∑ c ∈ challengeNodesOn oracleSig s path, ε c) := by
  intro Out stmt hadm hlang (p : Prover oracleSig ambient s Out)
  change Pr{let obs ← (do (simulateQ H (V.run stmt.1 stmt.2 p)).run' (← init))}[_] ≤ _
  refine prEvent_bind_le_of_forall_le _ _ _ fun st => ?_
  let liftAmbient : QueryImpl ambient (OracleComp (ambient + challengeSpec oracleSig s)) :=
    (QueryImpl.id' (ambient + challengeSpec oracleSig s)).restrictLeft
  let k : (tr : PathAlong oracleSig s) → Out tr →
      OracleComp (ambient + challengeSpec oracleSig s)
        (Observation oracleSig s Out (OracleVerifier.Output T B)) := fun tr out =>
    (fun v => (⟨tr, out, v.map fun t => (t, (V.outputMap stmt.1 (projectPathAlong oracleSig s tr)
        (toView s tr)).f (stmt.2, payloads s tr))⟩ :
        Observation oracleSig s Out (OracleVerifier.Output T B))) <$>
      simulateQ (QueryImpl.addLift liftAmbient
        ((pathResources inputs s (projectPathAlong oracleSig s tr)).answer
          (stmt.2, payloads s tr)))
        (V.decide stmt.1 (projectPathAlong oracleSig s tr) (toView s tr)).run
  have hrun : V.run stmt.1 stmt.2 p = TwoParty.Lens.run s (Prover.simulate liftAmbient p)
      (sampler oracleSig s fun c => liftM ((ambient + challengeSpec oracleSig s).query (.inr c)))
        >>= fun r => k r.1 r.2.1 := by
    rw [OracleVerifier.run_eq]
    refine bind_congr fun r => ?_
    exact LawfulMonad.bind_pure_comp _ _
  rw [hrun]
  refine prEvent_run_state_le_of_local H _ s
    (fun sp history => F.toFun sp history stmt) ε _ k
    (localBound stmt hadm hlang) ?_ _ st
  intro tr out st hne
  by_contra hpos
  apply hne
  apply StateFunction.escapeAlong oracleSig F hadm hlang
  refine ⟨st, pos_iff_ne_zero.2 ?_⟩
  unfold k liftAmbient QueryImpl.restrictLeft at hpos
  simpa only [OracleVerifier.validAcceptanceUsing, QueryImpl.id'_apply, simulateQ_map,
    simulateQ_resources, StateT.run'_eq, StateT.run_map, prEvent_map,
    exists_map_some_iff] using hpos

/-- Fresh challenge marginals specialize the bound on actual flip events. -/
theorem OracleVerifier.soundnessUsing_of_rbrSoundness
    {m : Type → Type v} [Monad m] [LawfulMonad m]
    [EvalDistSemantics m] [LawfulEvalDistSemantics m]
    {ι σ : Type} {I : Type uI} {S : Type uS} {ambient : OracleSpec ι}
  {s : OracleProtocol} {T : Path s → Type} {A : I → Type} {J : Path s → Type}
  {B : (p : Path s) → J p → Type} {inputs : OracleFamily.{uI, 0, wI} I A}
  {outputs : (p : Path s) → OracleFamily.{0, 0, wJ} (J p) (B p)}
  {V : OracleVerifier ambient s S T inputs outputs} {init : m σ}
  {H : QueryImpl (ambient + challengeSpec oracleSig s) (StateT σ m)}
  {input : StatementProblem (S × (∀ i, A i))} {output : PathProblem s (OracleVerifier.Output T B)}
  {draw : QueryImpl (challengeSpec oracleSig s) ProbComp}
  {ε : ChallengeNode oracleSig s → ℝ≥0∞}
    (fresh : FreshChallengesAt H draw)
    (h : Core.rbrSoundness oracleSig s (input.admissible ()) (input.language ())
      (fun stmt tr => ∃ st, V.validAcceptanceUsing (fun q => H (.inl q))
        (fun x => x.run' st) output.language stmt tr) draw ε) :
    V.soundnessUsing (fun c => do (simulateQ H c).run' (← init)) input output
      (⨆ path : Path s, ∑ c ∈ challengeNodesOn oracleSig s path, ε c) := by
  obtain ⟨F, hF⟩ := h
  apply OracleVerifier.soundnessUsing_of_localSoundness F
  intro stmt hadm hlang a next sp h history st
  let event : Move oracleSig a → Prop := fun x => ¬ F.toFun sp history stmt ∧
    F.toFun (sp.comp (.down (oracleSig.toFunB a x) (.root _)))
      (PrefixMoves.snoc oracleSig sp history x) stmt
  let : MeasurableSpace (Move oracleSig a) := ⊤
  calc
    _ = Pr{let x ← sampleAt oracleSig draw sp h}[event x] :=
      challengeActionAt_marginals H _ draw (fun c st event => by
        rw [simulateQ_spec_query]
        exact fresh st c event) sp h st event
    _ ≤ _ := by
      rw [prEvent_eq_evalDist_of_discrete]
      exact hF stmt hadm hlang a next sp h history

/-- Fresh challenge marginals turn round-by-round soundness into soundness of the oracle run
in any lawful distribution monad, with its actual resource answers and output oracle map. -/
theorem OracleVerifier.soundnessWith_of_rbrSoundness {m : Type → Type v}
    [Monad m] [LawfulMonad m] [EvalDistSemantics m] [LawfulEvalDistSemantics m]
    {ι : Type} {I : Type uI} {S : Type uS} {ambient : OracleSpec ι} {s : OracleProtocol}
    {T : Path s → Type} {A : I → Type} {J : Path s → Type}
    {B : (p : Path s) → J p → Type} {inputs : OracleFamily.{uI, 0, wI} I A}
    {outputs : (p : Path s) → OracleFamily.{0, 0, wJ} (J p) (B p)}
    {V : OracleVerifier ambient s S T inputs outputs}
    {H : QueryImpl (ambient + challengeSpec oracleSig s) m}
    {input : StatementProblem (S × (∀ i, A i))}
    {output : PathProblem s (OracleVerifier.Output T B)}
    {draw : QueryImpl (challengeSpec oracleSig s) ProbComp}
    {ε : ChallengeNode oracleSig s → ℝ≥0∞}
    (fresh : FreshChallenges H draw)
    (h : Core.rbrSoundness oracleSig s (input.admissible ()) (input.language ())
      (V.validAcceptanceWith (fun q => H (.inl q)) (output.language)) draw ε) :
    V.soundnessWith H input output
      (⨆ path : Path s, ∑ c ∈ challengeNodesOn oracleSig s path, ε c) := by
  let H' := H.liftTarget (StateT Unit m)
  have hlift {α : Type} (c : OracleComp (ambient + challengeSpec oracleSig s) α)
      (st : Unit) : (simulateQ H' c).run' st = simulateQ H c := by
    rw [simulateQ_liftTarget, StateT.liftM_def, StateT.run'_lift']
  have hfresh : FreshChallengesAt H' draw := by
    intro st c event
    simpa only [H', QueryImpl.liftTarget_apply, StateT.liftM_def, StateT.run'_lift']
      using fresh c event
  have hacc : ∀ stmt tr,
      (∃ st : Unit, V.validAcceptanceUsing (fun q => H' (.inl q))
        (fun x => x.run' st) output.language stmt tr) ↔
      V.validAcceptanceWith (fun q => H (.inl q)) output.language stmt tr := by
    intro stmt tr
    dsimp only [OracleVerifier.validAcceptanceUsing, OracleVerifier.validAcceptanceWith]
    change (∃ st : Unit, 0 < Pr{let v ←
      (simulateQ ((QueryImpl.liftTarget (StateT Unit m)
        (fun q => H (.inl q) : QueryImpl ambient m)).addLift
        ((pathResources inputs s (projectPathAlong oracleSig s tr)).answer
          (stmt.2, payloads s tr)) : QueryImpl
            (ambient + (pathResources inputs s (projectPathAlong oracleSig s tr)).spec)
            (StateT Unit m))
        (V.decide stmt.1 (projectPathAlong oracleSig s tr) (toView s tr)).run).run' st}[
          ∃ t, v = some t ∧ output.language (projectPathAlong oracleSig s tr)
            (t, (V.outputMap stmt.1 (projectPathAlong oracleSig s tr) (toView s tr)).f
              (stmt.2, payloads s tr))]) ↔ _
    simp only [stateLift_addLift, simulateQ_stateLift_run', exists_const]
  have h' : Core.rbrSoundness oracleSig s (input.admissible ()) (input.language ())
      (fun stmt tr => ∃ st : Unit, V.validAcceptanceUsing (fun q => H' (.inl q))
        (fun x => x.run' st) output.language stmt tr) draw ε := by
    simpa only [hacc] using h
  have bound := OracleVerifier.soundnessUsing_of_rbrSoundness (init := pure ()) hfresh h'
  simpa only [hlift, LawfulMonad.pure_bind] using bound

/-- Fresh round-by-round soundness bounds soundness by the sum of all node errors. -/
theorem OracleVerifier.soundnessWith_of_rbrSoundness_tsum {m : Type → Type v}
    [Monad m] [LawfulMonad m] [EvalDistSemantics m] [LawfulEvalDistSemantics m]
    {ι : Type} {I : Type uI} {S : Type uS} {ambient : OracleSpec ι} {s : OracleProtocol}
    {T : Path s → Type} {A : I → Type} {J : Path s → Type}
    {B : (p : Path s) → J p → Type} {inputs : OracleFamily.{uI, 0, wI} I A}
    {outputs : (p : Path s) → OracleFamily.{0, 0, wJ} (J p) (B p)}
    {V : OracleVerifier ambient s S T inputs outputs}
    {H : QueryImpl (ambient + challengeSpec oracleSig s) m}
    {input : StatementProblem (S × (∀ i, A i))}
    {output : PathProblem s (OracleVerifier.Output T B)}
    {draw : QueryImpl (challengeSpec oracleSig s) ProbComp}
    {ε : ChallengeNode oracleSig s → ℝ≥0∞}
    (fresh : FreshChallenges H draw)
    (h : Core.rbrSoundness oracleSig s (input.admissible ()) (input.language ())
      (V.validAcceptanceWith (fun q => H (.inl q)) (output.language)) draw ε) :
    V.soundnessWith H input output (∑' c, ε c) := fun Out stmt hadm hlang p =>
  (soundnessWith_of_rbrSoundness fresh h Out stmt hadm hlang p).trans
    (iSup_sum_challengeNodesOn_le_tsum ε)

/-- Uniform local errors and a path length bound give soundness error `k • e`. -/
theorem OracleVerifier.soundnessWith_of_rbrSoundness_uniform {m : Type → Type v}
    [Monad m] [LawfulMonad m] [EvalDistSemantics m] [LawfulEvalDistSemantics m]
    {ι : Type} {I : Type uI} {S : Type uS} {ambient : OracleSpec ι} {s : OracleProtocol}
    {T : Path s → Type} {A : I → Type} {J : Path s → Type}
    {B : (p : Path s) → J p → Type} {inputs : OracleFamily.{uI, 0, wI} I A}
    {outputs : (p : Path s) → OracleFamily.{0, 0, wJ} (J p) (B p)}
    {V : OracleVerifier ambient s S T inputs outputs}
    {H : QueryImpl (ambient + challengeSpec oracleSig s) m}
    {input : StatementProblem (S × (∀ i, A i))}
    {output : PathProblem s (OracleVerifier.Output T B)}
    {draw : QueryImpl (challengeSpec oracleSig s) ProbComp}
    {ε : ChallengeNode oracleSig s → ℝ≥0∞}
    {e : ℝ≥0∞} {k : ℕ}
    (fresh : FreshChallenges H draw)
    (h : Core.rbrSoundness oracleSig s (input.admissible ()) (input.language ())
      (V.validAcceptanceWith (fun q => H (.inl q)) (output.language)) draw ε)
    (hε : ∀ c, ε c ≤ e)
    (hcount : ∀ path, (challengeNodesOn oracleSig s path).card ≤ k) :
    V.soundnessWith H input output (k • e) := fun Out stmt hadm hlang p =>
  (soundnessWith_of_rbrSoundness fresh h Out stmt hadm hlang p).trans
    (iSup_sum_challengeNodesOn_le_nsmul hε hcount)

section OracleVerifier

variable {ι σ : Type} {I : Type uI} {S : Type uS} {ambient : OracleSpec ι}
  {s : OracleProtocol} {T : Path s → Type} {A : I → Type} {J : Path s → Type}
  {B : (p : Path s) → J p → Type} {inputs : OracleFamily.{uI, 0, wI} I A}
  {outputs : (p : Path s) → OracleFamily.{0, 0, wJ} (J p) (B p)}
  {V : OracleVerifier ambient s S T inputs outputs} {init : ProbComp σ}
  {impl : QueryImpl ambient (StateT σ ProbComp)}
  {input : StatementProblem (S × (∀ i, A i))} {output : PathProblem s (OracleVerifier.Output T B)}
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
  apply (V.soundness_iff_soundnessUsing init impl draw input output _).mpr
  apply OracleVerifier.soundnessUsing_of_rbrSoundness (freshChallengesAt_addLift impl draw)
  simpa only [OracleVerifier.rbrSoundness,
    OracleVerifier.validAcceptance_iff_validAcceptanceUsing, QueryImpl.addLift_def,
    QueryImpl.add_apply_inl, QueryImpl.liftTarget_self] using h

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

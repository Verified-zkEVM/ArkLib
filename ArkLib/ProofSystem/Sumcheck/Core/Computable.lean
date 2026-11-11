/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.ProofSystem.Sumcheck.Core.Completeness
public import ArkLib.ProofSystem.Sumcheck.Core.LegacySoundness
public import ArkLib.ProofSystem.Sumcheck.Core.ComputableSoundness
public import ArkLib.ProofSystem.Sumcheck.Impl.Projection

/-!
# Computable Sumcheck

The interaction-layer Sumcheck at an executable message carrier, with its security transported
from `Sumcheck.Core`.

The protocol, the verifier and the honest prover of `Sumcheck.Core` are generic in the message
carrier `M` and its evaluation `eval : M → R → R` (`protocolOn`, `verifierOn`). This file
instantiates them at the CompPoly coefficient arrays `Sumcheck.Impl.Representation.Message`,
whose evaluation queries are answered by Horner evaluation, and at CompPoly multivariate inputs.

* `Computable.protocol`, `Computable.verifier` and `Computable.observe` are the executable
  protocol, verifier and verdict reader. `Computable.honestProver` computes each round message
  with `Sumcheck.Impl.Computable.projectedMessage`. Everything a runtime evaluates is computable;
  `scripts/SumcheckRuntime.lean` runs them.
* `run_eq_interpret` relates the run over any carrier `M` to the run at the polynomial carrier:
  after renaming the challenge queries (`renameQueries`) and mapping the observation, it is the
  run of the interpreted prover `interpretFocal f n g P`, whose messages are read through
  `f : M → R⦃≤ deg⦄[X]`. `Computable.interpretProver` is this interpretation through
  `toMessage`; it is used only in proofs.
* `Computable.interpretProver_honestProver` identifies the interpreted computable honest prover
  with `Sumcheck.Core.honestProver` on the interpreted input.
* `Computable.support_completeness` transports the mathematical honest verdict on every
  supported run; `Computable.perfectCompleteness` follows for every challenge implementation.
  `Computable.soundness` transports `Sumcheck.Core.verifier_soundness`. Challenge implementations
  move between carriers by `transportDraw`, which keeps uniform sampling.
-/

@[expose] public section

namespace Sumcheck.Core
open Polynomial PFunctor FreeM Interaction.Core Interaction.TwoParty.Lens Interaction.Oracle
  OracleComp OracleSpec ProtocolSpec MeasureTheory
open scoped ENNReal NNReal

/-! ## Changing the message carrier -/

section Transport

variable {R : Type} {M M' : Type} {eval : M → R → R} {eval' : M' → R → R}



/-- The challenge node of the first round of `protocolOn`, named by shape branches alone. -/
def headNodeOn (k : ℕ) : ChallengeNode oracleSig (protocolOn R M eval (k + 1)) :=
  ⟨.inr ⟨⟨⟩, .inl ⟨⟩⟩, rfl⟩

/-- Restrict a challenge implementation of `protocolOn` to the remaining rounds. -/
def tailDrawOn {m : Type → Type} {k : ℕ}
    (draw : (c : ChallengeNode oracleSig (protocolOn R M eval (k + 1))) →
      m (challengeSpec oracleSig _ c)) :
    (c : ChallengeNode oracleSig (protocolOn R M eval k)) → m (challengeSpec oracleSig _ c) :=
  fun c => draw ⟨.inr ⟨⟨⟩, .inr ⟨⟨⟩, c.val⟩⟩, c.property⟩

/-- Move a challenge implementation between message carriers. The challenge nodes of
`protocolOn` do not depend on the carrier, and every challenge is a ring element. -/
def transportDraw {m : Type → Type} : (k : ℕ) →
    ((c : ChallengeNode oracleSig (protocolOn R M' eval' k)) →
      m (challengeSpec oracleSig _ c)) →
    (c : ChallengeNode oracleSig (protocolOn R M eval k)) → m (challengeSpec oracleSig _ c)
  | 0, _, ⟨n, _⟩ => nomatch n
  | _ + 1, _, ⟨.inl _, h⟩ => nomatch h
  | k + 1, draw, ⟨.inr ⟨_, .inl _⟩, _⟩ => draw (headNodeOn k)
  | k + 1, draw, ⟨.inr ⟨_, .inr ⟨_, c⟩⟩, h⟩ => transportDraw k (tailDrawOn draw) ⟨c, h⟩

/-- Transporting a challenge implementation there and back returns it. -/
theorem transportDraw_transportDraw_apply {m : Type → Type} : (k : ℕ) →
    (draw : (c : ChallengeNode oracleSig (protocolOn R M eval k)) →
      m (challengeSpec oracleSig _ c)) →
    (c : ChallengeNode oracleSig (protocolOn R M eval k)) →
    transportDraw (M' := M') (eval' := eval') k (transportDraw k draw) c = draw c
  | 0, _, ⟨n, _⟩ => nomatch n
  | _ + 1, _, ⟨.inl _, h⟩ => nomatch h
  | _ + 1, _, ⟨.inr ⟨_, .inl _⟩, _⟩ => rfl
  | k + 1, draw, ⟨.inr ⟨_, .inr ⟨_, c⟩⟩, h⟩ =>
    transportDraw_transportDraw_apply k (tailDrawOn draw) ⟨c, h⟩

/-- Transporting a challenge implementation there and back returns it. -/
theorem transportDraw_transportDraw {m : Type → Type} (k : ℕ)
    (draw : (c : ChallengeNode oracleSig (protocolOn R M eval k)) →
      m (challengeSpec oracleSig _ c)) :
    transportDraw (M' := M') (eval' := eval') k (transportDraw k draw) = draw :=
  funext (transportDraw_transportDraw_apply k draw)

/-- Transport commutes with a natural map applied to every draw. -/
theorem transportDraw_natural {m n : Type → Type} (φ : (α : Type) → m α → n α) : (k : ℕ) →
    (draw : (c : ChallengeNode oracleSig (protocolOn R M' eval' k)) →
      m (challengeSpec oracleSig (protocolOn R M' eval' k) c)) →
    (c : ChallengeNode oracleSig (protocolOn R M eval k)) →
    transportDraw k (fun c => φ _ (draw c)) c = φ _ (transportDraw k draw c)
  | 0, _, ⟨n, _⟩ => nomatch n
  | _ + 1, _, ⟨.inl _, h⟩ => nomatch h
  | _ + 1, _, ⟨.inr ⟨_, .inl _⟩, _⟩ => rfl
  | k + 1, draw, ⟨.inr ⟨_, .inr ⟨_, c⟩⟩, h⟩ => by
    have e := transportDraw_natural φ k (tailDrawOn draw) ⟨c, h⟩
    exact e

/-- Map the messages of a transcript of `protocolOn`, keeping every challenge. -/
abbrev mapTranscript (f : M → M') (k : ℕ) :
    PathAlong oracleSig (protocolOn R M eval k) →
      PathAlong oracleSig (protocolOn R M' eval' k) :=
  Interpreted.mapTranscript f k

/-- Interpret a prover of `protocolOn` at another message carrier: every sent message is mapped
by `f`, every slot keeps its effects, and the output is mapped by `g`. -/
def interpretFocal {m : Type → Type} [Functor m] (f : M → M') : (k : ℕ) →
    {Out : PathAlong oracleSig (protocolOn R M eval k) → Type} →
    {Out' : PathAlong oracleSig (protocolOn R M' eval' k) → Type} →
    (∀ tr, Out tr → Out' (mapTranscript f k tr)) →
    Focal oracleSig m (protocolOn R M eval k) Out →
    Focal oracleSig m (protocolOn R M' eval' k) Out'
  | 0, _, _, g, P => (g ⟨⟩ <$> P : m _)
  | k + 1, _, _, g, P => (fun r => ⟨f r.1, (fun h chal => interpretFocal f k
      (fun tail => g ⟨r.1, ⟨chal, tail⟩⟩) (h chal)) <$> r.2⟩) <$> P

/-- The sampler of one more round has a pure message slot and draws at the challenge node. -/
theorem samplerEnd_protocolOn_succ {m : Type → Type} [Monad m] (k : ℕ)
    (draw : (c : ChallengeNode oracleSig (protocolOn R M eval (k + 1))) →
      m (challengeSpec oracleSig _ c)) :
    samplerEnd oracleSig (protocolOn R M eval (k + 1)) draw =
      (pure fun _ => (fun chal =>
          ⟨chal, samplerEnd oracleSig (protocolOn R M eval k) (tailDrawOn draw)⟩) <$>
        draw (headNodeOn k) :
        m ((_ : M) → m ((_ : R) ×
          PureEnd oracleSig m .counterpart (protocolOn R M eval k) (fun _ => PUnit)))) := rfl

/-- Running one round of `protocolOn` against the sampler: the prover's message slot, its
challenge slot, the draw, then the remaining rounds. -/
theorem run_protocolOn_succ {m : Type → Type} [Monad m] [LawfulMonad m] (k : ℕ)
    {Out : PathAlong oracleSig (protocolOn R M eval (k + 1)) → Type}
    (P : Focal oracleSig m (protocolOn R M eval (k + 1)) Out)
    (draw : (c : ChallengeNode oracleSig (protocolOn R M eval (k + 1))) →
      m (challengeSpec oracleSig _ c)) :
    Interaction.TwoParty.Lens.run (protocolOn R M eval (k + 1)) P
        (sampler oracleSig (protocolOn R M eval (k + 1)) draw) = (do
      let r ← P
      let h ← r.2
      let chal ← draw (headNodeOn k)
      let x ← Interaction.TwoParty.Lens.run (protocolOn R M eval k) (h chal)
        (sampler oracleSig (protocolOn R M eval k) (tailDrawOn draw))
      pure ⟨⟨r.1, ⟨chal, x.1⟩⟩, x.2.1, x.2.2⟩) := by
  rw [← bind_pure (Interaction.TwoParty.Lens.run _ P (sampler oracleSig _ draw))]
  erw [run_sampler_sender rfl]
  refine bind_congr fun chosen => ?_
  erw [run_sampler_receiver rfl]
  rfl

/-- Simulating a prover of one more round simulates its message slot, its challenge slot and
the remaining rounds. -/
theorem simulate_protocolOn_succ {ι κ : Type} {spec : OracleSpec ι} {spec' : OracleSpec κ}
    (F : QueryImpl spec (OracleComp spec')) (k : ℕ)
    {Out : PathAlong oracleSig (protocolOn R M eval (k + 1)) → Type}
    (P : Prover oracleSig spec (protocolOn R M eval (k + 1)) Out) :
    Prover.simulate F P = ((fun r => ⟨r.1, (fun h chal => Prover.simulate F (h chal)) <$>
      simulateQ F r.2⟩) <$> simulateQ F P :
        OracleComp spec' ((x : M) × OracleComp spec' ((chal : R) →
          Focal oracleSig (OracleComp spec') (protocolOn R M eval k)
            (fun tail => Out ⟨x, ⟨chal, tail⟩⟩)))) := rfl

/-- Simulating the ambient oracle commutes with interpreting the messages. -/
theorem simulate_interpretFocal {ι κ : Type} {spec : OracleSpec ι} {spec' : OracleSpec κ}
    (F : QueryImpl spec (OracleComp spec')) (f : M → M') : (k : ℕ) →
    {Out : PathAlong oracleSig (protocolOn R M eval k) → Type} →
    {Out' : PathAlong oracleSig (protocolOn R M' eval' k) → Type} →
    (g : ∀ tr, Out tr → Out' (mapTranscript f k tr)) →
    (P : Prover oracleSig spec (protocolOn R M eval k) Out) →
    Prover.simulate F (interpretFocal f k g P) = interpretFocal f k g (Prover.simulate F P)
  | 0, _, _, g, P => by
    change simulateQ F (g ⟨⟩ <$> P) = g ⟨⟩ <$> simulateQ F P
    rw [simulateQ_map]
  | k + 1, _, _, g, P => by
    rw [simulate_protocolOn_succ, simulate_protocolOn_succ]
    change _ <$> simulateQ F (_ <$> P) = _ <$> (_ <$> simulateQ F P)
    erw [simulateQ_map, Functor.map_map, Functor.map_map]
    refine congrArg (· <$> simulateQ F P) (funext fun r => ?_)
    refine congrArg (Sigma.mk (f r.1)) ?_
    change _ <$> simulateQ F (_ <$> r.2) = _ <$> (_ <$> simulateQ F r.2)
    erw [simulateQ_map, Functor.map_map, Functor.map_map]
    exact congrArg (· <$> simulateQ F r.2) (funext fun h => funext fun chal =>
      simulate_interpretFocal F f k _ (h chal))

/-- Running an interpreted prover against the sampler runs the original prover against the
transported sampler, and maps its transcript and output. -/
theorem run_interpretFocal {m : Type → Type} [Monad m] [LawfulMonad m] (f : M → M') :
    (k : ℕ) → {Out : PathAlong oracleSig (protocolOn R M eval k) → Type} →
    {Out' : PathAlong oracleSig (protocolOn R M' eval' k) → Type} →
    (g : ∀ tr, Out tr → Out' (mapTranscript f k tr)) →
    (P : Focal oracleSig m (protocolOn R M eval k) Out) →
    (draw : (c : ChallengeNode oracleSig (protocolOn R M' eval' k)) →
      m (challengeSpec oracleSig _ c)) →
    Interaction.TwoParty.Lens.run (protocolOn R M' eval' k) (interpretFocal f k g P)
        (sampler oracleSig (protocolOn R M' eval' k) draw) =
      (fun x => ⟨mapTranscript f k x.1, g x.1 x.2.1, x.2.2⟩) <$>
        Interaction.TwoParty.Lens.run (protocolOn R M eval k) P
          (sampler oracleSig (protocolOn R M eval k) (transportDraw k draw))
  | 0, Out, Out', g, P, draw => by
    refine (run_done (l := oracleSig) (OutP := Out') (OutC := fun _ => PUnit)
      (g ⟨⟩ <$> P) (pure ⟨⟩)).trans ?_
    refine Eq.trans ?_ (congrArg (_ <$> ·) (run_done (l := oracleSig) (OutP := Out)
      (OutC := fun _ => PUnit) P (pure ⟨⟩))).symm
    simp only [bind_map_left, _root_.map_bind, LawfulMonad.pure_bind,
      LawfulApplicative.map_pure]
    rfl
  | k + 1, Out, Out', g, P, draw => by
    rw [run_protocolOn_succ, run_protocolOn_succ]
    dsimp only [interpretFocal]
    erw [bind_map_left]
    simp only [_root_.map_bind, LawfulApplicative.map_pure]
    refine bind_congr (m := m) fun r => ?_
    erw [bind_map_left]
    refine bind_congr (m := m) fun h => bind_congr (m := m) fun chal => ?_
    rw [run_interpretFocal f k
      (Out' := fun tail => Out' ⟨f r.1, ⟨chal, tail⟩⟩) (fun tail => g ⟨r.1, ⟨chal, tail⟩⟩)
      (h chal) (tailDrawOn draw)]
    simp only [bind_map_left]
    rfl

/-- Mapping by the identity keeps a transcript. -/
theorem mapTranscript_id : (k : ℕ) → (tr : PathAlong oracleSig (protocolOn R M eval k)) →
    mapTranscript (eval' := eval) id k tr = tr
  | 0, _ => rfl
  | k + 1, ⟨x, ⟨c, tr⟩⟩ => by
    change (⟨x, ⟨c, mapTranscript (eval' := eval) id k tr⟩⟩ :
      PathAlong oracleSig (protocolOn R M eval (k + 1))) = ⟨x, ⟨c, tr⟩⟩
    rw [mapTranscript_id k tr]

/-- Rename the queries of a run of `protocolOn` to the queries of a run at another carrier:
ambient queries are kept and each challenge query asks the corresponding challenge node. -/
def renameQueries {ι : Type} (ambient : OracleSpec ι) (k : ℕ) :
    QueryImpl (ambient + challengeSpec oracleSig (protocolOn R M eval k))
      (OracleComp (ambient + challengeSpec oracleSig (protocolOn R M' eval' k))) :=
  QueryImpl.add
    (fun q => liftM ((ambient + challengeSpec oracleSig (protocolOn R M' eval' k)).query (.inl q)))
    (transportDraw k fun c =>
      liftM ((ambient + challengeSpec oracleSig (protocolOn R M' eval' k)).query (.inr c)))

/-- Renaming challenge nodes preserves every supported result. -/
private theorem support_renameQueries {ι α : Type} (ambient : OracleSpec ι) (k : ℕ)
    (program : OracleComp (ambient + challengeSpec oracleSig (protocolOn R M eval k)) α) :
    support (simulateQ (renameQueries (M' := M') (eval' := eval') ambient k) program) =
      support program := by
  have full : ∀ j (draw : (c : ChallengeNode oracleSig (protocolOn R M' eval' j)) →
      OracleComp (ambient + challengeSpec oracleSig (protocolOn R M' eval' k))
        (challengeSpec oracleSig _ c)),
      (∀ c, support (draw c) = Set.univ) →
      ∀ c : ChallengeNode oracleSig (protocolOn R M eval j),
        support (transportDraw j draw c) = Set.univ := by
    intro j
    induction j with
    | zero => intro draw h ⟨c, _⟩; exact nomatch c
    | succ k ih =>
      intro draw h ⟨c, hc⟩
      rcases c with c | ⟨_, c | ⟨_, c⟩⟩
      · exact nomatch hc
      · exact h (headNodeOn k)
      · exact ih (tailDrawOn draw) (fun c => h _) ⟨c, hc⟩
  have hquery : ∀ q : (ambient + challengeSpec oracleSig (protocolOn R M eval k)).Domain,
      support (renameQueries (M' := M') (eval' := eval') ambient k q) =
      Set.univ := by
    intro q
    rcases q with q | c
    · exact support_query _
    · exact full k _ (fun c => support_query _) c
  induction program using OracleComp.inductionOn with
  | pure x => simp
  | query_bind q next ih =>
    simp [hquery, ih]

/-- Map an observation of `protocolOn` to another carrier: the transcript by `f`, the prover
output by `g`, and the oracle part of the verdict by `dmap`. -/
def mapObservation (f : M → M') (k : ℕ) {Out : PathAlong oracleSig (protocolOn R M eval k) → Type}
    {Out' : PathAlong oracleSig (protocolOn R M' eval' k) → Type}
    (g : ∀ tr, Out tr → Out' (mapTranscript f k tr)) {T B B' : Type} (dmap : B → B')
    (obs : Observation oracleSig (protocolOn R M eval k) Out (fun _ => T × B)) :
    Observation oracleSig (protocolOn R M' eval' k) Out' (fun _ => T × B') :=
  ⟨mapTranscript f k obs.1, g obs.1 obs.2.1, obs.2.2.map fun v => (v.1, dmap v.2)⟩

/-- An experiment on a renamed program is the experiment on the original program with the
transported challenge implementation. -/
theorem experiment_renameQueries {ι σ α : Type} {ambient : OracleSpec ι} (k : ℕ)
    (init : ProbComp σ) (impl : QueryImpl ambient (StateT σ ProbComp))
    (challenges : QueryImpl (challengeSpec oracleSig (protocolOn R M' eval' k)) ProbComp)
    (program : OracleComp (ambient + challengeSpec oracleSig (protocolOn R M eval k)) α) :
    experiment init impl challenges (simulateQ (renameQueries ambient k) program) =
      experiment init impl (transportDraw k challenges) program := by
  simp only [experiment]
  refine bind_congr fun st => congrArg (StateT.run' · st) ?_
  refine QueryImpl.simulateQ_simulateQ_eq_of_apply (fun t => ?_) program
  rcases t with q | c
  · exact simulateQ_spec_query _ _
  · change simulateQ _ (transportDraw k _ c) = _
    have e := transportDraw_natural (M := M) (eval := eval)
      (m := OracleComp (ambient + challengeSpec oracleSig (protocolOn R M' eval' k)))
      (n := StateT σ ProbComp)
      (fun _ x => simulateQ (QueryImpl.addLift (r := StateT σ ProbComp) impl challenges) x) k
      (fun c => liftM ((ambient + challengeSpec oracleSig (protocolOn R M' eval' k)).query
        (.inr c))) c
    refine e.symm.trans ?_
    simp only [simulateQ_spec_query, QueryImpl.addLift_def, QueryImpl.add_apply_inr,
      QueryImpl.liftTarget_apply]
    exact transportDraw_natural (n := StateT σ ProbComp) (fun _ x => liftM x) k challenges c

end Transport

/-! ## Folding pure rounds at any carrier -/

section FoldOn

variable {R : Type} {M M' : Type} {eval : M → R → R} {eval' : M' → R → R}
  {m : Type → Type} [Monad m] {State State' : ℕ → Type} {Out Out' : Type}

/-- A dependent fold of pure rounds over the carrier `M`, as `foldRounds`. -/
def foldRoundsOn (msg : (k : ℕ) → State (k + 1) → M)
    (next : (k : ℕ) → State (k + 1) → R → State k) (finish : State 0 → Out) :
    (k : ℕ) → State k → Focal oracleSig m (protocolOn R M eval k) (fun _ => Out)
  | 0, st => (pure (finish st) : m Out)
  | k + 1, st => (pure ⟨msg k st, pure fun chal => foldRoundsOn msg next finish k
      (next k st chal)⟩ : m ((_ : M) × m ((_ : R) → _)))

/-- Folds whose states correspond under `φ`, with the same messages, transitions and outputs,
are the same prover. -/
theorem foldRoundsOn_map (msg : (k : ℕ) → State (k + 1) → M)
    (next : (k : ℕ) → State (k + 1) → R → State k) (finish : State 0 → Out)
    (msg' : (k : ℕ) → State' (k + 1) → M) (next' : (k : ℕ) → State' (k + 1) → R → State' k)
    (finish' : State' 0 → Out) (φ : (k : ℕ) → State k → State' k)
    (hmsg : ∀ k st, msg' k (φ (k + 1) st) = msg k st)
    (hnext : ∀ k st chal, next' k (φ (k + 1) st) chal = φ k (next k st chal))
    (hfinish : ∀ st, finish' (φ 0 st) = finish st) :
    (k : ℕ) → (st : State k) →
    foldRoundsOn (m := m) (eval := eval) msg' next' finish' k (φ k st) =
      foldRoundsOn msg next finish k st
  | 0, st => congrArg (pure (f := m)) (hfinish st)
  | k + 1, st => by
    change (pure ⟨msg' k (φ (k + 1) st), pure fun chal => foldRoundsOn (m := m) (eval := eval)
        msg' next' finish' k (next' k (φ (k + 1) st) chal)⟩ : m ((_ : M) × m ((_ : R) → _))) =
      pure ⟨msg k st, pure fun chal => foldRoundsOn msg next finish k (next k st chal)⟩
    simp only [hmsg, hnext, foldRoundsOn_map msg next finish msg' next' finish' φ hmsg hnext
      hfinish k]

variable [LawfulMonad m]

/-- Interpreting a fold of pure rounds maps its messages and its output. -/
theorem interpretFocal_foldRoundsOn (f : M → M') (o : Out → Out')
    (msg : (k : ℕ) → State (k + 1) → M)
    (next : (k : ℕ) → State (k + 1) → R → State k) (finish : State 0 → Out) :
    (k : ℕ) → (st : State k) →
    interpretFocal (eval' := eval') f k (fun _ => o)
        (foldRoundsOn (m := m) (eval := eval) msg next finish k st) =
      foldRoundsOn (fun k st => f (msg k st)) next (fun st => o (finish st)) k st
  | 0, st => LawfulApplicative.map_pure (f := m) o (finish st)
  | k + 1, st => by
    refine (LawfulApplicative.map_pure _ _).trans ?_
    refine congrArg (pure (f := m)) (congrArg (Sigma.mk (f (msg k st))) ?_)
    refine (LawfulApplicative.map_pure _ _).trans ?_
    exact congrArg (pure (f := m)) (funext fun chal =>
      interpretFocal_foldRoundsOn f o msg next finish k _)

end FoldOn

/-- The polynomial-carrier fold of pure rounds is `foldRoundsOn` specialized to polynomial
evaluation. -/
theorem foldRounds_eq_foldRoundsOn {R : Type} [CommSemiring R] {deg : ℕ} {m : Type → Type}
    [Monad m] {State : ℕ → Type} {Out : Type} (msg : (k : ℕ) → State (k + 1) → R⦃≤ deg⦄[X])
    (next : (k : ℕ) → State (k + 1) → R → State k) (finish : State 0 → Out) :
    (k : ℕ) → (st : State k) →
    foldRounds (m := m) msg next finish k st =
      foldRoundsOn (m := m) (eval := fun p x => p.val.eval x) msg next finish k st
  | 0, _ => rfl
  | k + 1, st => by
    change (pure ⟨msg k st, pure fun chal => foldRounds msg next finish k (next k st chal)⟩ :
      m ((_ : R⦃≤ deg⦄[X]) × m ((_ : R) → _))) = pure ⟨msg k st, pure fun chal =>
        foldRoundsOn (m := m) (eval := fun p x => p.val.eval x) msg next finish k
          (next k st chal)⟩
    simp only [foldRounds_eq_foldRoundsOn msg next finish k]

/-! ## The decision at another message carrier -/

section Decision

variable {R : Type} [CommSemiring R] {deg : ℕ} {M : Type} {eval : M → R → R}



/-- Read a transcript of `protocolOn` as a transcript of `protocol` through `f`. -/
abbrev polyTranscript (f : M → R⦃≤ deg⦄[X]) (k : ℕ)
    (tr : PathAlong oracleSig (protocolOn R M eval k)) : PathAlong oracleSig (protocol R deg k) :=
  mapTranscript (eval' := fun (p : R⦃≤ deg⦄[X]) (x : R) => p.val.eval x) f k tr

/-- A routed query of a replicated protocol with one more round splits by its legacy half. -/
theorem routeOn_succ_sumEquiv (k : ℕ) (p : Path (protocolOn R M eval k))
    (s : (Spec.SingleRound.pSpec R deg).MessageIdx ⊕ (Spec.pSpec R deg k).MessageIdx)
    (q : OracleInterface.Query
      ((Spec.SingleRound.pSpec R deg ++ₚ Spec.pSpec R deg k).Message (MessageIdx.sumEquiv s))) :
    routeOn R deg M eval (k + 1) ⟨⟨⟩, ⟨⟨⟩, p⟩⟩ ⟨MessageIdx.sumEquiv s, q⟩ =
      Legacy.routePart (roundRouteOn R deg M eval k p)
        (fun q => simulateQ (tailLiftOn R M eval k p) (routeOn R deg M eval k p q))
        s q :=
  Legacy.appendRoute_sumEquiv _ _ s q

/-- If `eval` answers as `f` followed by polynomial evaluation, then answering routed queries
from the run's payloads answers the legacy message queries from the decoded transcript of the
mapped run. -/
theorem simulateQ_routeOn {f : M → R⦃≤ deg⦄[X]} (hf : ∀ x r, eval x r = (f x).val.eval r) :
    (k : ℕ) → (tr : PathAlong oracleSig (protocolOn R M eval k)) →
    (q : [(Spec.pSpec R deg k).Message]ₒ.Domain) →
    simulateQ (payloadImpl (protocolOn R M eval k) tr)
        (routeOn R deg M eval k (projectPathAlong oracleSig _ tr) q) =
      OracleInterface.simOracle0 (Spec.pSpec R deg k).Message
        (decodeTranscript k (polyTranscript f k tr)).messages q
  | 0, _, q => q.1.1.elim0
  | k + 1, ⟨msg, ⟨chal, tail⟩⟩, ⟨j, q⟩ => by
    obtain ⟨s, rfl⟩ := (MessageIdx.sumEquiv (pSpec₁ := Spec.SingleRound.pSpec R deg)
      (pSpec₂ := Spec.pSpec R deg k)).surjective j
    refine (congrArg (simulateQ _)
      (routeOn_succ_sumEquiv k (projectPathAlong oracleSig _ tail) s q)).trans ?_
    rcases s with i | i
    · refine Legacy.simulateQ_queryAlongHEq _ _ _ _ _ _ _ (roundFullTranscript (f msg) chal i.1)
        ?_ ?_ q
      · exact (FullTranscript.fst_apply_heq _ _).symm.trans
          (heq_of_eq (congrFun (FullTranscript.append_fst _ _) _))
      · intro q'
        obtain rfl := Unique.eq_default i
        exact (simulateQ_spec_query _ _).trans (hf msg q')
    · refine Legacy.simulateQ_queryAlongHEq _ _ _ _ _ _ _
        ((decodeTranscript k (polyTranscript f k tail)).messages i) ?_ ?_ q
      · exact (FullTranscript.snd_apply_heq _ _).symm.trans
          (heq_of_eq (congrFun (FullTranscript.append_snd _ _) _))
      · intro q'
        refine (QueryImpl.simulateQ_simulateQ_eq_of_apply
          (impl := payloadImpl (protocolOn R M eval k) tail) (fun t => ?_) _).trans
          (simulateQ_routeOn hf k tail ⟨i, q'⟩)
        exact simulateQ_spec_query _ _

/-- Erasing the messages keeps every challenge, whatever the message carrier. -/
theorem viewChallengeListOn_toView (f : M → R⦃≤ deg⦄[X]) :
    (k : ℕ) → (tr : PathAlong oracleSig (protocolOn R M eval k)) →
    viewChallengeListOn k (toView (protocolOn R M eval k) tr).1 =
      transcriptChallenges k (polyTranscript f k tr)
  | 0, _ => rfl
  | k + 1, ⟨_, ⟨chal, tail⟩⟩ => by
    change (Fin.cons chal (viewChallengeListOn k (toView (protocolOn R M eval k) tail).1) :
        Fin (k + 1) → R) =
      Fin.cons chal (transcriptChallenges k (polyTranscript f k tail))
    rw [viewChallengeListOn_toView f k tail]

/-- The view of a run has the challenges of the decoded transcript of the mapped run. -/
theorem viewChallengesOn_toView (f : M → R⦃≤ deg⦄[X]) (k : ℕ)
    (tr : PathAlong oracleSig (protocolOn R M eval k)) :
    viewChallengesOn (deg := deg) (toView (protocolOn R M eval k) tr) =
      (decodeTranscript k (polyTranscript f k tr)).challenges := by
  funext j
  unfold viewChallengesOn
  rw [viewChallengeListOn_toView f]
  exact (legacyTranscript_apply_challenge k _ _ j.1 j.2).symm

end Decision

/-! ## The verifier at another message carrier -/

section VerifierOn

variable {R : Type} [CommSemiring R] [DecidableEq R] [SampleableType R] {deg n : ℕ} {d : ℕ}
  (D : Fin d ↪ R) {ι : Type} {ambient : OracleSpec ι} {M : Type} {eval : M → R → R} {I : Type}
  {A : I → Type} (inputs : OracleFamily I A)



variable {f : M → R⦃≤ deg⦄[X]} (hf : ∀ x r, eval x r = (f x).val.eval r)
include hf

/-- On any completed run, the decision over the carrier `M` returns the legacy verdict of the
decoded transcript of the mapped run. -/
theorem simulateQ_decideOn {κ : Type} {spec' : OracleSpec κ}
    (amb : QueryImpl ambient (OracleComp spec')) (stmt : Spec.StatementRound R n 0)
    (data : ∀ i, A i) (tr : PathAlong oracleSig (protocolOn R M eval n)) :
    simulateQ (QueryImpl.addLift amb ((pathResources inputs (protocolOn R M eval n)
        (projectPathAlong oracleSig _ tr)).answer (data, payloads _ tr)))
      ((verifierOn R deg n D ambient M eval inputs).decide stmt _ (toView _ tr)).run =
      (pure (legacyVerdict R deg n D ambient stmt (decodeTranscript n (polyTranscript f n tr))) :
        OracleComp spec' _) := by
  change simulateQ _ (simulateQ (pathLift ambient inputs _)
    (simulateQ (routeOn R deg M eval n _)
      (legacyProgram R deg n D ambient stmt (viewChallengesOn (toView _ tr))))) = _
  rw [simulateQ_pathLift, viewChallengesOn_toView f]
  congr 1
  exact QueryImpl.simulateQ_simulateQ_eq_of_apply (simulateQ_routeOn hf n tr) _

/-- Closed form of the execution over the carrier `M` against any prover: run the prover against
the sampler, then return the legacy verdict of the decoded transcript of the mapped run, with
the input data as output oracle. -/
theorem run_verifierOn (stmt : Spec.StatementRound R n 0) (data : ∀ i, A i)
    {Out : PathAlong oracleSig (protocolOn R M eval n) → Type}
    (P : Prover oracleSig ambient (protocolOn R M eval n) Out) :
    (verifierOn R deg n D ambient M eval inputs).run stmt data P =
      (fun x => (⟨x.1, x.2.1, (legacyVerdict R deg n D ambient stmt
          (decodeTranscript n (polyTranscript f n x.1))).map fun t => (t, data)⟩ :
          Observation oracleSig (protocolOn R M eval n) Out
            (fun _ => Spec.StatementRound R n (Fin.last n) × ∀ i, A i))) <$>
        Interaction.TwoParty.Lens.run (protocolOn R M eval n)
          (P.simulate fun q => liftM
            ((ambient + challengeSpec oracleSig (protocolOn R M eval n)).query (.inl q)))
          (sampler oracleSig _ fun c => liftM
            ((ambient + challengeSpec oracleSig (protocolOn R M eval n)).query (.inr c))) := by
  unfold Interaction.Core.OracleVerifier.run
  rw [map_eq_bind_pure_comp]
  refine bind_congr fun x => ?_
  obtain ⟨tr, out, u⟩ := x
  simp only [simulateQ_decideOn D inputs hf]
  rfl

/-- A run over the carrier `M`, with its queries renamed and its observation mapped, is the run
of the interpreted prover against the verifier at the polynomial carrier. Messages are mapped by
`f`, the prover output by `g` and the output oracle data by `dmap`. -/
theorem run_eq_interpret {A' : I → Type} (inputs' : OracleFamily I A')
    (dmap : (∀ i, A i) → ∀ i, A' i) (stmt : Spec.StatementRound R n 0) (data : ∀ i, A i)
    {Out : PathAlong oracleSig (protocolOn R M eval n) → Type}
    {Out' : PathAlong oracleSig (protocol R deg n) → Type}
    (g : ∀ tr, Out tr → Out' (polyTranscript f n tr))
    (P : Prover oracleSig ambient (protocolOn R M eval n) Out) :
    simulateQ (renameQueries (M' := R⦃≤ deg⦄[X]) (eval' := fun p x => p.val.eval x) ambient n)
        (mapObservation f n g dmap <$>
          (verifierOn R deg n D ambient M eval inputs).run stmt data P) =
      (verifierOn R deg n D ambient _ (fun p x => p.val.eval x) inputs').run stmt (dmap data)
        (interpretFocal f n g P) := by
  rw [run_verifierOn D inputs hf, run_verifierOn (f := id)
      (eval := fun (p : R⦃≤ deg⦄[X]) x => p.val.eval x) D inputs' (fun _ _ => rfl),
    simulate_interpretFocal, run_interpretFocal, simulateQ_map, simulateQ_map, Functor.map_map,
    Functor.map_map, Interaction.TwoParty.Lens.run, simulateQ_runWith_sampler,
    Prover.simulate_simulate]
  have hP : (fun q => simulateQ (renameQueries (M' := R⦃≤ deg⦄[X])
      (eval' := fun p x => p.val.eval x) ambient n)
        (liftM ((ambient + challengeSpec oracleSig (protocolOn R M eval n)).query (.inl q)))) =
      fun q => liftM ((ambient + challengeSpec oracleSig
        (protocolOn R (R⦃≤ deg⦄[X]) (fun p x => p.val.eval x) n)).query (.inl q)) :=
    funext fun q => simulateQ_spec_query _ _
  have hd : (fun c => simulateQ (renameQueries (M' := R⦃≤ deg⦄[X])
      (eval' := fun p x => p.val.eval x) ambient n)
        (liftM ((ambient + challengeSpec oracleSig (protocolOn R M eval n)).query (.inr c)))) =
      transportDraw n fun c =>
        liftM ((ambient + challengeSpec oracleSig
          (protocolOn R (R⦃≤ deg⦄[X]) (fun p x => p.val.eval x) n)).query (.inr c)) :=
    funext fun c => simulateQ_spec_query _ _
  rw [hP, hd]
  refine congrArg (· <$> _) (funext fun x => ?_)
  simp only [mapObservation, mapTranscript_id, Option.map_map]
  rfl

end VerifierOn

/-! ## Uniform challenges at any carrier -/

section Uniform



/-- Every challenge of `protocolOn` is a ring element, so it can be sampled uniformly. -/
@[instance_reducible]
def challengeSampleableOn (R : Type) [SampleableType R] (M : Type) (eval : M → R → R) :
    (k : ℕ) → (c : ChallengeNode oracleSig (protocolOn R M eval k)) →
      SampleableType (challengeSpec oracleSig (protocolOn R M eval k) c)
  | 0, ⟨n, _⟩ => nomatch n
  | _ + 1, ⟨.inl _, h⟩ => nomatch h
  | _ + 1, ⟨.inr ⟨_, .inl _⟩, _⟩ => inferInstanceAs (SampleableType R)
  | k + 1, ⟨.inr ⟨_, .inr ⟨_, c⟩⟩, h⟩ => challengeSampleableOn R M eval k ⟨c, h⟩

/-- Transporting uniform challenges of `protocol` gives uniform challenges of `protocolOn`. -/
theorem transportDraw_challengeQueryImpl (R : Type) [CommSemiring R] [SampleableType R]
    (deg : ℕ) (M : Type) (eval : M → R → R) : (k : ℕ) →
    (c : ChallengeNode oracleSig (protocolOn R M eval k)) →
    transportDraw (M' := R⦃≤ deg⦄[X]) (eval' := fun p x => p.val.eval x) k
        (challengeQueryImpl oracleSig (protocol R deg k)) c =
      @challengeQueryImpl _ oracleSig (protocolOn R M eval k) (challengeSampleableOn R M eval k) c
  | 0, ⟨n, _⟩ => nomatch n
  | _ + 1, ⟨.inl _, h⟩ => nomatch h
  | _ + 1, ⟨.inr ⟨_, .inl _⟩, _⟩ => rfl
  | k + 1, ⟨.inr ⟨_, .inr ⟨_, c⟩⟩, h⟩ => by
    have e := transportDraw_challengeQueryImpl R deg M eval k ⟨c, h⟩
    exact e

end Uniform

section InterpretedTransport

variable {R M N : Type} {eval : M → R → R} {evalN : N → R → R}
  {ι I : Type} {ambient : OracleSpec ι} {A B : I → Type}
  (inputs : OracleFamily I A) (outputs : OracleFamily I B)
  {State : ℕ → Type} {T : Type} (checks : RoundChecks R State) (finish : State 0 → T)
  (f : M → N) (hf : ∀ msg r, evalN (f msg) r = eval msg r)

/-- The passive interpreted verifier is a map of the prover-sampler run. -/
theorem run_interpreted (k : ℕ) (st : State k) (data : ∀ i, A i)
    {Out : PathAlong oracleSig (protocolOn R M eval k) → Type}
    (P : Prover oracleSig ambient (protocolOn R M eval k) Out) :
    (Interpreted.verifier ambient inputs checks finish k).run st data P =
      (fun x => (⟨x.1, x.2.1,
        (Interpreted.verdict eval checks finish k st x.1).map (fun t => (t, data))⟩ :
        Observation oracleSig _ Out (fun _ => T × (∀ i, A i)))) <$>
        Interaction.TwoParty.Lens.run (protocolOn R M eval k)
          (P.simulate fun q => liftM
            ((ambient + challengeSpec oracleSig (protocolOn R M eval k)).query (.inl q)))
          (sampler oracleSig _ fun c => liftM
            ((ambient + challengeSpec oracleSig (protocolOn R M eval k)).query (.inr c))) := by
  rw [Interpreted.verifier_run, map_eq_bind_pure_comp]
  refine bind_congr fun x => ?_
  rcases x with ⟨tr, out, u⟩
  rfl

include hf in
/-- Interpreting messages and retained data preserves the whole passive verifier run,
including every private effect and dependent prover output. -/
theorem run_interpreted_eq (k : ℕ) (st : State k) (dmap : (∀ i, A i) → ∀ i, B i)
    (data : ∀ i, A i) {Out : PathAlong oracleSig (protocolOn R M eval k) → Type}
    {Out' : PathAlong oracleSig (protocolOn R N evalN k) → Type}
    (g : ∀ tr, Out tr → Out' (mapTranscript f k tr))
    (P : Prover oracleSig ambient (protocolOn R M eval k) Out) :
    simulateQ (renameQueries (M' := N) (eval' := evalN) ambient k)
      (mapObservation f k g dmap <$>
        (Interpreted.verifier ambient inputs checks finish k).run st data P) =
      (Interpreted.verifier ambient outputs checks finish k).run st (dmap data)
        (interpretFocal f k g P) := by
  rw [run_interpreted, run_interpreted]
  rw [simulate_interpretFocal, run_interpretFocal, simulateQ_map, simulateQ_map,
    Functor.map_map, Functor.map_map, Interaction.TwoParty.Lens.run,
    simulateQ_runWith_sampler, Prover.simulate_simulate]
  have hP : (fun q => simulateQ (renameQueries (M' := N) (eval' := evalN) ambient k)
      (liftM ((ambient + challengeSpec oracleSig (protocolOn R M eval k)).query (.inl q)))) =
      fun q => liftM ((ambient + challengeSpec oracleSig (protocolOn R N evalN k)).query
        (.inl q)) := funext fun q => simulateQ_spec_query _ _
  have hd : (fun c => simulateQ (renameQueries (M' := N) (eval' := evalN) ambient k)
      (liftM ((ambient + challengeSpec oracleSig (protocolOn R M eval k)).query (.inr c)))) =
      transportDraw k fun c => liftM
        ((ambient + challengeSpec oracleSig (protocolOn R N evalN k)).query (.inr c)) :=
    funext fun c => simulateQ_spec_query _ _
  rw [hP, hd]
  refine congrArg (· <$> _) (funext fun x => ?_)
  simp only [mapObservation, Option.map_map, Interpreted.verdict_transport checks finish f hf]
  rfl

/-- For constant terminal types, dependent message interpretation is the native transport. -/
theorem interpretFocal_eq_transport {m : Type → Type} [Monad m] [LawfulMonad m] {Out : Type}
    (k : ℕ) (P : Focal oracleSig m (protocolOn R M eval k) (fun _ => Out)) :
    interpretFocal (eval' := evalN) f k (fun _ => id) P =
      Interpreted.transportProver f k P := by
  induction k with
  | zero => exact id_map P
  | succ k ih =>
    simp only [interpretFocal, Interpreted.transportProver]
    erw [LawfulMonad.bind_pure_comp]
    congr 1
    funext chosen
    congr 1
    erw [LawfulMonad.bind_pure_comp]
    congr 1
    funext respond r
    exact ih (respond r)

/-- Interpreting messages commutes with packing dependent private outputs into a fixed type. -/
theorem transport_interpretFocal {m : Type → Type} [Monad m] [LawfulMonad m]
    {O : Type} (k : ℕ) {Out : PathAlong oracleSig (protocolOn R M eval k) → Type}
    (g : ∀ tr, Out tr → O) (P : Focal oracleSig m (protocolOn R M eval k) Out) :
    Interpreted.transportProver (evaluateN := evalN) f k
      (interpretFocal (eval' := eval) id k g P) = interpretFocal f k g P := by
  induction k with
  | zero => rfl
  | succ k ih =>
    dsimp only [interpretFocal, Interpreted.transportProver]
    erw [bind_map_left, LawfulMonad.bind_pure_comp]
    congr 1
    funext chosen
    congr 1
    erw [bind_map_left, LawfulMonad.bind_pure_comp]
    congr 1
    funext respond r
    exact ih (fun tail => g ⟨chosen.1, r, tail⟩) (respond r)

end InterpretedTransport

/-! ## The computable instance -/

namespace Computable

open Sumcheck.Impl.Representation Sumcheck.Impl.Computable CPoly

section Protocol

variable (R : Type) [CommSemiring R] (deg n : ℕ)

/-- The computable Sumcheck protocol: each round message is a CompPoly coefficient array of
degree at most `deg`, and its evaluation queries are answered by Horner evaluation. -/
abbrev protocol : OracleProtocol.{0} := protocolOn R (Message R deg) (evaluate R deg) n

/-- Every challenge of the computable protocol is a ring element, sampled uniformly. -/
instance [SampleableType R] :
    ∀ c, SampleableType (challengeSpec oracleSig (protocol R deg n) c) :=
  challengeSampleableOn R _ _ n

/-- A computable input polynomial: a CompPoly multivariate polynomial whose individual degrees
are at most `deg`. -/
abbrev Input := {p : CMvPolynomial n R // ∀ j, p.degreeOf j ≤ deg}

/-- The input oracle over computable polynomials, answered by evaluation at a point. -/
def inputFamily : OracleFamily Unit (fun _ => Input R deg n) :=
  ⟨fun _ => { Query := Fin n → R
              toOC.spec := (Fin n → R) →ₒ R
              toOC.impl point := do return (← read).val.eval point }⟩

/-- The mathematical polynomial of a computable input. -/
def interpretInput [BEq R] [LawfulBEq R] (data : ∀ _ : Unit, Input R deg n) :
    ∀ i, Spec.OracleStatement R n deg i :=
  fun _ => toOracleStatement (data ()).val (data ()).property

/-- Reading a computable input as a mathematical polynomial is injective. -/
theorem interpretInput_injective [BEq R] [LawfulBEq R] :
    Function.Injective (interpretInput R deg n) := fun a b h => by
  funext u
  cases u
  exact Subtype.ext (CPoly.fromCMvPolynomial_injective
    (congrArg Subtype.val (congrFun h ())))

end Protocol

section Verifier

variable (R : Type) [CommSemiring R] [DecidableEq R] [SampleableType R] (deg n : ℕ) {d : ℕ}
  (D : Fin d ↪ R) {ι : Type} (ambient : OracleSpec ι)

/-- The computable Sumcheck verifier: `verifierOn` at the CompPoly message carrier and the
computable input family. It runs the legacy decision fold with Horner-evaluated message queries,
and its output oracle is the input polynomial. -/
def verifier : OracleVerifier ambient (protocol R deg n) (Spec.StatementRound R n 0)
    (fun _ => Spec.StatementRound R n (Fin.last n)) (inputFamily R deg n)
    (fun _ => inputFamily R deg n) :=
  verifierOn R deg n D ambient _ _ (inputFamily R deg n)

end Verifier

section Observe

variable (R : Type) [CommSemiring R] (deg n : ℕ)

/-- The observation of a computable Sumcheck run with prover output `Out`. -/
abbrev Obs (Out : PathAlong oracleSig (protocol R deg n) → Type) :=
  Observation oracleSig (protocol R deg n) Out
    (fun _ => Spec.StatementRound R n (Fin.last n) × ∀ _ : Unit, Input R deg n)

variable {R deg n} in
/-- Read a run's verdict: the accepted statement, and the output oracle evaluated at the accepted
challenges, computed from the CompPoly data. -/
def observe {Out : PathAlong oracleSig (protocol R deg n) → Type} (obs : Obs R deg n Out) :
    Option (Spec.StatementRound R n (Fin.last n) × R) :=
  obs.2.2.map fun v => (v.1, (v.2 ()).val.eval v.1.challenges)

end Observe

section Honest

variable (R : Type) [CommSemiring R] (deg n : ℕ)

/-- The computable honest prover's state with `k` rounds remaining: the round index `round`,
with `round + k = n`, and the legacy statement at that round. The input polynomial is a
parameter of the prover, not part of the state. -/
structure RoundState (k : ℕ) where
  /-- The index of the next round, or `n` after the last round. -/
  round : Fin (n + 1)
  /-- The round index and the remaining count add up to the number of variables. -/
  round_add : round.val + k = n
  /-- The legacy statement at the current round. -/
  statement : Spec.StatementRound R n round

/-- The prover output: the output statement, the output oracle data and the unit witness. -/
abbrev HonestOutput :=
  (Spec.StatementRound R n (Fin.last n) × ∀ _ : Unit, Input R deg n) × Unit

variable {R deg n}

/-- The round being played when `k + 1` rounds remain. -/
def RoundState.index {k : ℕ} (st : RoundState R n (k + 1)) : Fin n :=
  ⟨st.round.val, by have := st.round_add; omega⟩

variable [DecidableEq R] [Nontrivial R] {d : ℕ} (D : Fin d ↪ R) (x : Input R deg n)

/-- The honest round message, computed on CompPoly carriers by
`Sumcheck.Impl.Computable.projectedMessage`. -/
def honestMessage (k : ℕ) (st : RoundState R n (k + 1)) : Message R deg :=
  Sumcheck.Impl.Computable.projectedMessage D st.index st.statement.challenges x.val x.property

/-- The statement update: the new target is the round message at the challenge, by Horner
evaluation, and the challenge is appended to the history. -/
def nextState (k : ℕ) (st : RoundState R n (k + 1)) (chal : R) : RoundState R n k where
  round := st.index.succ
  round_add := by
    have := st.round_add
    change st.round.val + 1 + k = n
    omega
  statement := ⟨evaluate R deg (honestMessage D x k st) chal,
    Fin.snoc st.statement.challenges chal⟩

/-- Read the output from the state after the last round; the output oracle is the input. -/
def finishState (st : RoundState R n 0) : HonestOutput R deg n :=
  ((⟨st.statement.target, fun j => st.statement.challenges (Fin.cast (by
      have := st.round_add; simp only [Fin.val_last]; omega) j)⟩, fun _ => x), ())

/-- The computable honest prover from a state with `k` rounds remaining. Every slot is `pure`. -/
def honestFrom {m : Type → Type} [Monad m] (k : ℕ) (st : RoundState R n k) :
    Focal oracleSig m (protocol R deg k) (fun _ => HonestOutput R deg n) :=
  foldRoundsOn (honestMessage D x) (nextState D x) (finishState x) k st

/-- The computable honest Sumcheck prover on the input statement and polynomial. -/
def honestProver {m : Type → Type} [Monad m] (stmt : Spec.StatementRound R n 0)
    (data : ∀ _ : Unit, Input R deg n) :
    Focal oracleSig m (protocol R deg n) (fun _ => HonestOutput R deg n) :=
  honestFrom D (data ()) n ⟨0, Nat.zero_add n, stmt⟩

end Honest

section Interpret

variable {R : Type} [CommSemiring R] [DecidableEq R] {deg n : ℕ}

/-- Read a computable prover output as the output of the interaction-layer honest prover. -/
def honestOutputMap (o : HonestOutput R deg n) : Core.HonestOutput R deg n :=
  ((o.1.1, interpretInput R deg n o.1.2), o.2)

/-- Read a prover of the computable protocol as a prover of `Sumcheck.Core.protocol`: every
message is read through `toMessage`, every effect is kept, and the output is mapped by `g`. It
is used only in proofs. -/
noncomputable def interpretProver {m : Type → Type} [Functor m] {k : ℕ}
    {Out : PathAlong oracleSig (protocol R deg k) → Type}
    {Out' : PathAlong oracleSig (Core.protocol R deg k) → Type}
    (g : ∀ tr, Out tr → Out' (polyTranscript (toMessage R deg) k tr))
    (P : Focal oracleSig m (protocol R deg k) Out) :
    Focal oracleSig m (Core.protocol R deg k) Out' :=
  interpretFocal (toMessage R deg) k g P

variable [Nontrivial R] {d : ℕ} (D : Fin d ↪ R) (x : Input R deg n)

/-- The interaction-layer state of a computable state, with the interpreted input polynomial. -/
def liftState {k : ℕ} (st : RoundState R n k) : Core.RoundState R deg n k :=
  ⟨st.round, st.round_add, st.statement, toOracleStatement x.val x.property⟩

/-- Interpreting the computable honest prover gives the interaction-layer fold of honest rounds
on the interpreted input. -/
theorem interpretProver_honestFrom {m : Type → Type} [Monad m] [LawfulMonad m] (k : ℕ)
    (st : RoundState R n k) :
    interpretProver (fun _ => honestOutputMap) (honestFrom (m := m) D x k st) =
      foldRounds (Core.honestMessage D) (Core.nextState (Core.honestMessage D)) Core.finishState
        k (liftState x st) := by
  rw [foldRounds_eq_foldRoundsOn]
  refine (interpretFocal_foldRoundsOn _ _ _ _ _ k st).trans
    (foldRoundsOn_map (fun k st => toMessage R deg (honestMessage D x k st)) (nextState D x)
      (fun st => honestOutputMap (finishState x st)) (Core.honestMessage D)
      (Core.nextState (Core.honestMessage D)) Core.finishState (fun _ st => liftState x st)
      (fun k st => ?_) (fun k st chal => ?_) (fun st => rfl) k st).symm
  · exact (Sumcheck.Impl.Computable.projectedMessage_toMessage D _ _ x.val x.property).symm
  · change (⟨_, _, ⟨(Core.honestMessage D k (liftState x st)).val.eval chal, _⟩, _⟩ :
        Core.RoundState R deg n k) = ⟨_, _, ⟨evaluate R deg (honestMessage D x k st) chal, _⟩, _⟩
    have h : evaluate R deg (honestMessage D x k st) chal =
        (Core.honestMessage D k (liftState x st)).val.eval chal :=
      Sumcheck.Impl.Computable.projectedMessage_evaluate D _ _ x.val x.property chal
    simp only [h]
    rfl

/-- Interpreting the computable honest prover gives the interaction-layer honest prover on the
interpreted input. -/
theorem interpretProver_honestProver {m : Type → Type} [Monad m] [LawfulMonad m]
    (stmt : Spec.StatementRound R n 0) (data : ∀ _ : Unit, Input R deg n) :
    interpretProver (fun _ => honestOutputMap) (honestProver (m := m) D stmt data) =
      Core.honestProver D stmt (interpretInput R deg n data) :=
  interpretProver_honestFrom D (data ()) n ⟨0, Nat.zero_add n, stmt⟩

end Interpret

/-! ## Completeness -/

section Completeness

variable (R : Type) [CommSemiring R] [DecidableEq R] (deg n : ℕ) {d : ℕ} (D : Fin d ↪ R)

/-- The Sumcheck relation at round `i` on computable inputs: the interpreted input lies in the
legacy relation. The witness is unit and there is no promise. -/
def relationProblem {Ctx : Type} (i : Fin (n + 1)) :
    Problem (⟨fun _ : Ctx => Spec.StatementRound R n i × ∀ _ : Unit, Input R deg n⟩ :
      ClaimFamily Ctx) where
  Witness _ _ := Unit
  admissible _ _ := True
  rel _ x _ := ((x.1, interpretInput R deg n x.2), ()) ∈ Spec.relationRound R n deg D i
  rel_admissible _ _ _ _ := trivial

/-- The observation of a computable Sumcheck run with the honest prover's output type. -/
abbrev HonestObservation := Obs R deg n (fun _ => HonestOutput R deg n)

/-- Judge a computable Sumcheck run by the verifier verdict and the statement in the prover
output. -/
def judgement :
    OutputJudgement (HonestObservation R deg n)
      (relationProblem (Ctx := Path (protocol R deg n)) R deg n D (Fin.last n)) :=
  { context := fun obs => projectPathAlong oracleSig _ obs.1
    verdict := fun obs => obs.2.2
    proverStatement := fun obs => obs.2.1.1
    witness := fun _ _ _ => () }

variable {R deg n} [SampleableType R] [Nontrivial R] {ι : Type} (ambient : OracleSpec ι)

/-- Every supported honest run on a true input accepts the prover's output in the final
relation. This statement needs no probability distribution or normalization assumption. -/
theorem support_completeness (stmt : Spec.StatementRound R n 0)
    (data : ∀ _ : Unit, Input R deg n)
    (hx : (relationProblem R deg n D 0).rel () (stmt, data) ()) :
    ∀ obs ∈ support ((verifier R deg n D ambient).run stmt data (honestProver D stmt data)),
      (judgement R deg n D).honest obs := by
  intro obs hobs
  have hrun := run_eq_interpret D (ambient := ambient) (inputFamily R deg n)
    (evaluate_eq R deg) (Spec.polynomialFamily R n deg) (interpretInput R deg n) stmt data
    (Out' := fun _ => Core.HonestOutput R deg n) (fun _ => honestOutputMap)
    (honestProver D stmt data)
  have hp := interpretProver_honestProver (m := OracleComp ambient) D stmt data
  change interpretFocal (toMessage R deg) n (Out' := fun _ => Core.HonestOutput R deg n)
    (fun _ => honestOutputMap)
    (honestProver D stmt data) = _ at hp
  rw [hp] at hrun
  change _ = (Core.verifier R deg n D ambient).run stmt (interpretInput R deg n data)
    (Core.honestProver D stmt (interpretInput R deg n data)) at hrun
  have hm : mapObservation (toMessage R deg) n (fun _ => honestOutputMap)
      (interpretInput R deg n) obs ∈ support
        ((Core.verifier R deg n D ambient).run stmt (interpretInput R deg n data)
          (Core.honestProver D stmt (interpretInput R deg n data))) := by
    rw [← hrun, support_renameQueries, _root_.support_map]
    exact ⟨obs, hobs, rfl⟩
  rw [Core.run_verifier_honestProver, _root_.support_map] at hm
  obtain ⟨chals, -, heq⟩ := hm
  have hgood : (Core.judgement R deg n D).honest
      (mapObservation (toMessage R deg) n (fun _ => honestOutputMap)
        (interpretInput R deg n) obs) := by
    rw [← heq]
    obtain ⟨hv, hout, hrel⟩ := Core.legacyVerdict_honestTranscript D ambient stmt
      (interpretInput R deg n data) hx chals
    refine ⟨(Core.honestOutput D stmt (interpretInput R deg n data) chals).1, ?_, rfl, hrel⟩
    change Option.map _ (legacyVerdict R deg n D ambient stmt _) = _
    rw [hv, Option.map_some]
    exact congrArg some (Prod.ext rfl hout.symm)
  obtain ⟨t, ht, hprov, hrel⟩ := hgood
  change Option.map _ obs.2.2 = some t at ht
  obtain ⟨v, hv, rfl⟩ := Option.map_eq_some_iff.mp ht
  have hvo : v = obs.2.1.1 := by
    obtain ⟨h1, h2⟩ := Prod.ext_iff.mp hprov
    exact Prod.ext h1.symm (interpretInput_injective R deg n h2.symm)
  exact ⟨v, hv, hvo.symm, hrel⟩

/-- Perfect completeness of the computable Sumcheck.

For every ambient state, ambient oracle implementation and challenge implementation, the
computable honest prover on an input whose interpretation is in the round-`0` relation is
accepted with probability one; the accepted statement is the prover's output statement and lies
in the final relation. This follows from `support_completeness`, since every result supported by
the interpreted experiment is supported by the original run. -/
theorem perfectCompleteness {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl ambient (StateT σ ProbComp))
    (challenges : QueryImpl (challengeSpec oracleSig (protocol R deg n)) ProbComp) :
    letI : MeasurableSpace (HonestObservation R deg n) := ⊤
    completeness ((verifier R deg n D ambient).classicalModel init impl challenges)
      (relationProblem R deg n D 0) (relationProblem R deg n D (Fin.last n))
      (judgement R deg n D) (fun x _ => honestProver D x.1 x.2) 0 := by
  let : MeasurableSpace (HonestObservation R deg n) := ⊤
  refine ⟨MeasurableSpace.measurableSet_top, fun x _ hx => ?_⟩
  change 1 - 0 ≤ 𝒟[experiment init impl challenges
    ((verifier R deg n D ambient).run x.1 x.2 (honestProver D x.1 x.2))] _
  rw [tsub_zero]
  apply le_of_eq
  symm
  apply (OracleComp.evalDist_apply_setOf_eq_one_iff_forall_mem_support _ _).mpr
  intro obs hobs
  simp only [experiment, mem_support_bind_iff] at hobs
  obtain ⟨st, -, hs⟩ := hobs
  exact support_completeness D ambient x.1 x.2 hx obs
    (support_simulateQ_run'_subset _ _ st hs)

end Completeness

/-! ## Soundness -/

section Soundness

variable (R : Type) [CommSemiring R] [DecidableEq R] (deg n : ℕ) {d : ℕ} (D : Fin d ↪ R)

/-- The Sumcheck language at round `i` on computable inputs: the statements whose interpreted
input lies in the legacy language. -/
def language (i : Fin (n + 1)) : Set (Spec.StatementRound R n i × ∀ _ : Unit, Input R deg n) :=
  {x | (x.1, interpretInput R deg n x.2) ∈ (Spec.relationRound R n deg D i).language}

variable [SampleableType R] {ι : Type} (ambient : OracleSpec ι)
  {σ : Type} (init : ProbComp σ) (impl : QueryImpl ambient (StateT σ ProbComp))

/-- Soundness of the computable Sumcheck verifier: a statement outside the round-`0` language is
accepted into the final language with probability at most `deg / |R|` per challenge, for every
prover and every prover output type. Challenges are sampled uniformly. The proof transports
`Sumcheck.Core.verifier_soundness` through `run_eq_interpret`; the transported prover outputs
the computable transcript together with its output. -/
theorem soundness [Fintype R] [IsDomain R] :
    ∀ Out : PathAlong oracleSig (protocol R deg n) → Type,
      letI : MeasurableSpace (Obs R deg n Out) := ⊤
      Interaction.Core.soundness ((verifier R deg n D ambient).classicalModel (Out := Out) init
          impl (challengeQueryImpl oracleSig (protocol R deg n)))
        (Legacy.langProblem (language R deg n D 0))
        (Legacy.langProblem (language R deg n D (Fin.last n)))
        (fun obs => projectPathAlong oracleSig _ obs.1) (fun obs => obs.2.2)
        ((∑ _ : (Spec.pSpec R deg n).ChallengeIdx, (deg : ℝ≥0) / Fintype.card R : ℝ≥0) :
          ℝ≥0∞) := by
  intro Out
  let : MeasurableSpace (Obs R deg n Out) := ⊤
  let Out' : PathAlong oracleSig (Core.protocol R deg n) → Type := fun _ => Σ tr, Out tr
  let : MeasurableSpace (Observation oracleSig (Core.protocol R deg n) Out'
    (fun _ => Spec.StatementRound R n (Fin.last n) × ∀ j, Spec.OracleStatement R n deg j)) := ⊤
  let : MeasurableSpace (Observation oracleSig
    (protocolOn R (R⦃≤ deg⦄[X]) (fun p x => p.val.eval x) n) Out'
    (fun _ => Spec.StatementRound R n (Fin.last n) × ∀ j, Spec.OracleStatement R n deg j)) := ⊤
  rintro ⟨stmt, data⟩ - hnot P
  have hC := Core.legacyVerifier_soundness R deg n D ambient init impl Out'
    (stmt, interpretInput R deg n data) trivial (by
      simpa [Legacy.langProblem_language, language] using hnot)
    (interpretFocal (toMessage R deg) n (Out' := Out') (fun tr o => ⟨tr, o⟩) P)
  have hrun := run_eq_interpret D (ambient := ambient) (inputFamily R deg n)
    (evaluate_eq R deg) (Spec.polynomialFamily R n deg) (interpretInput R deg n) stmt data
    (Out' := Out') (fun tr o => ⟨tr, o⟩) P
  change 𝒟[experiment init impl _ ((verifierOn R deg n D ambient _ _
    (Spec.polynomialFamily R n deg)).run stmt (interpretInput R deg n data)
      (interpretFocal (toMessage R deg) n _ P))] _ ≤ _ at hC
  have hch : transportDraw (M' := R⦃≤ deg⦄[X]) (eval' := fun p x => p.val.eval x) n
      (challengeQueryImpl oracleSig (Core.protocol R deg n)) =
      challengeQueryImpl oracleSig (protocol R deg n) :=
    funext (transportDraw_challengeQueryImpl R deg _ _ n)
  rw [← hrun, experiment_renameQueries, hch, experiment_map, evalDist_map _ measurable_from_top,
    Measure.map_apply measurable_from_top MeasurableSpace.measurableSet_top] at hC
  refine le_trans (measure_mono fun obs hobs => ?_) hC
  obtain ⟨t, ht, hlang⟩ := hobs
  refine ⟨(t.1, interpretInput R deg n t.2), ?_, ?_⟩
  · change Option.map _ obs.2.2 = _
    change obs.2.2 = some t at ht
    rw [ht]
    rfl
  · simpa [Legacy.langProblem_language, language] using hlang

end Soundness

/-! ## Indexed intervals on computational inputs -/

section Intervals

variable {R : Type} [CommSemiring R] [DecidableEq R] {deg n d : ℕ}
  (D : Fin d → R) {ι : Type} (ambient : OracleSpec ι)

/-- Execute a bounded interval with coefficient-array messages and retain its original
computational polynomial as the output oracle. -/
@[macro_inline]
def intervalVerifier (start count : ℕ) (bound : start + count ≤ n) :
    OracleVerifier ambient (protocol R deg count) (RoundStatement R n ⟨start, by omega⟩)
      (fun _ => RoundStatement R n ⟨count + start, by omega⟩) (inputFamily R deg n)
      (fun _ => inputFamily R deg n) where
  decide stmt := (Interpreted.verifier ambient (inputFamily R deg n) (intervalCheck D)
    IntervalClaim.finish count).decide (intervalInitial start count bound stmt)
  outputMap _ _ _ := OracleMap.fst _ _

/-- Reading computational messages and inputs gives the parent's actual interval run. -/
theorem interval_run_eq_interpret [BEq R] [LawfulBEq R]
    (start count : ℕ) (bound : start + count ≤ n)
    (stmt : RoundStatement R n ⟨start, by omega⟩) (data : ∀ _ : Unit, Input R deg n)
    {Out : PathAlong oracleSig (protocol R deg count) → Type}
    {Out' : PathAlong oracleSig (Core.protocol R deg count) → Type}
    (g : ∀ tr, Out tr → Out' (polyTranscript (toMessage R deg) count tr))
    (P : Prover oracleSig ambient (protocol R deg count) Out) :
    simulateQ (renameQueries (M' := R⦃≤ deg⦄[X])
      (eval' := fun p x => p.val.eval x) ambient count)
      (mapObservation (toMessage R deg) count g (interpretInput R deg n) <$>
        (intervalVerifier D ambient start count bound).run stmt data P) =
      (Core.intervalVerifier R deg n D ambient start count bound).run stmt
        (interpretInput R deg n data) (interpretFocal (toMessage R deg) count g P) := by
  have h := run_interpreted_eq (inputFamily R deg n) (polynomialFamily R n deg)
    (intervalCheck D) IntervalClaim.finish (toMessage R deg)
    (fun q r => (evaluate_eq R deg q r).symm) count
    (intervalInitial start count bound stmt) (interpretInput R deg n) data g P
  rw [Interpreted.verifier_polynomial] at h
  exact h

variable [BEq R] [LawfulBEq R] [Nontrivial R]

/-- Every supported honest interval accepts a true endpoint, with no distribution chosen. -/
theorem interval_support_completeness (start count : ℕ) (bound : start + count ≤ n)
    (stmt : RoundStatement R n ⟨start, by omega⟩) (data : ∀ _ : Unit, Input R deg n)
    (htrue : indexedRelation D _ stmt (toPolynomial (data ()).val (data ()).property)) :
    ∀ obs ∈ support ((intervalVerifier D ambient start count bound).run stmt data
      (intervalHonestProver D (data ()).val (data ()).property count
        (intervalInitial start count bound stmt))),
      ∃ t, obs.2.2 = some (t, data) ∧
        indexedRelation D _ t (toPolynomial (data ()).val (data ()).property) := by
  intro obs hobs
  have hrun := interval_run_eq_interpret D ambient start count bound stmt data
    (Out' := fun _ => RoundStatement R n ⟨count + start, by omega⟩) (fun _ => id)
    (intervalHonestProver D (data ()).val (data ()).property count
      (intervalInitial start count bound stmt))
  change _ = (Core.intervalVerifier R deg n D ambient start count bound).run stmt
    (interpretInput R deg n data) (interpretFocal (toMessage R deg) count (fun _ => id) _) at hrun
  rw [interpretFocal_eq_transport, interpret_intervalHonestProver] at hrun
  have hd : interpretInput R deg n data =
      fun _ => toPolynomial (data ()).val (data ()).property := rfl
  rw [hd] at hrun
  have hm : mapObservation (toMessage R deg) count (fun _ => id)
      (interpretInput R deg n) obs ∈ support
      ((Core.intervalVerifier R deg n D ambient start count bound).run stmt
        (fun _ => toPolynomial (data ()).val (data ()).property)
        (intervalProver D (toPolynomial (data ()).val (data ()).property) count
          (intervalInitial start count bound stmt))) := by
    rw [← hrun, support_renameQueries, _root_.support_map]
    exact ⟨obs, hobs, rfl⟩
  rw [intervalVerifier_honest_run D _ ambient start count bound stmt htrue,
    _root_.support_map] at hm
  obtain ⟨chals, -, heq⟩ := hm
  have hv := congrArg (fun (x : Observation oracleSig (Core.protocol R deg count)
      (fun _ => RoundStatement R n ⟨count + start, by omega⟩)
      (fun _ => RoundStatement R n ⟨count + start, by omega⟩ ×
        (∀ j, PolynomialData R n deg j))) => x.2.2) heq.symm
  obtain ⟨v, hv, he⟩ := Option.map_eq_some_iff.mp hv
  have hdata : v.2 = data := interpretInput_injective R deg n ((congrArg Prod.snd he).trans hd.symm)
  refine ⟨v.1, ?_, ?_⟩
  · exact hv.trans (congrArg some (Prod.ext rfl hdata))
  · have ht := (intervalVerdict_honest D (toPolynomial (data ()).val (data ()).property)
      count (intervalInitial start count bound stmt) htrue chals).2
    have hstmt : v.1 = (foldState (intervalNext D
      (toPolynomial (data ()).val (data ()).property)) count
        (intervalInitial start count bound stmt) chals).finish := congrArg Prod.fst he
    rw [hstmt]
    exact ht

/-- Honest intervals accept a true endpoint with probability one under any shared-state
handler, including adaptive challenge handlers. -/
theorem interval_perfectCompleteness {σ : Type} (init : ProbComp σ)
    (start count : ℕ) (bound : start + count ≤ n)
    (impl : QueryImpl (ambient + challengeSpec oracleSig (protocol R deg count))
      (StateT σ ProbComp))
    (stmt : RoundStatement R n ⟨start, by omega⟩) (data : ∀ _ : Unit, Input R deg n)
    (htrue : indexedRelation D _ stmt (toPolynomial (data ()).val (data ()).property)) :
    Pr{let obs ← (intervalExperiment init impl
      ((intervalVerifier D ambient start count bound).run stmt data
        (intervalHonestProver D (data ()).val (data ()).property count
          (intervalInitial start count bound stmt))))}[
      ∃ t, obs.2.2 = some (t, data) ∧
        indexedRelation D _ t (toPolynomial (data ()).val (data ()).property)] = 1 := by
  apply prEvent_eq_one_of_forall_mem_support
  intro obs hobs
  simp only [intervalExperiment, mem_support_bind_iff] at hobs
  obtain ⟨st, -, hs⟩ := hobs
  exact interval_support_completeness D ambient start count bound stmt data htrue obs
    (support_simulateQ_run'_subset _ _ st hs)

/-- The measure of valid honest interval acceptance is one for every bounded endpoint. -/
theorem interval_measureCompleteness {σ : Type} (init : ProbComp σ)
    (start count : ℕ) (bound : start + count ≤ n)
    (impl : QueryImpl (ambient + challengeSpec oracleSig (protocol R deg count))
      (StateT σ ProbComp))
    (stmt : RoundStatement R n ⟨start, by omega⟩) (data : ∀ _ : Unit, Input R deg n)
    (htrue : indexedRelation D _ stmt (toPolynomial (data ()).val (data ()).property)) :
    𝒟[(fun obs => ∃ t, obs.2.2 = some (t, data) ∧
      indexedRelation D _ t (toPolynomial (data ()).val (data ()).property)) <$>
      intervalExperiment init impl ((intervalVerifier D ambient start count bound).run stmt data
        (intervalHonestProver D (data ()).val (data ()).property count
          (intervalInitial start count bound stmt)))] {True} = 1 := by
  rw [← prEvent_eq_evalDist_map]
  exact interval_perfectCompleteness D ambient init start count bound impl stmt data htrue

omit [Nontrivial R] in
/-- A false computational input reaches a true suffix output with probability at most
`count * (deg / |R|)`, for every dependent private output and arbitrary prover. -/
theorem interval_soundness [SampleableType R] [Fintype R] [IsDomain R]
    {σ : Type} (init : ProbComp σ) (impl : QueryImpl ambient (StateT σ ProbComp))
    (start count : ℕ) (finish : start + count = n)
    (stmt : RoundStatement R n ⟨start, by omega⟩) (data : ∀ _ : Unit, Input R deg n)
    {Out : PathAlong oracleSig (protocol R deg count) → Type}
    (P : Prover oracleSig ambient (protocol R deg count) Out)
    (hfalse : ¬ indexedRelation D _ stmt (toPolynomial (data ()).val (data ()).property)) :
    Pr{let obs ← (experiment init impl
      (challengeQueryImpl oracleSig (protocol R deg count))
      ((intervalVerifier D ambient start count finish.le).run stmt data P))}[
        ∃ t, obs.2.2 = some t ∧
          indexedRelation D _ t.1 (toPolynomial (t.2 ()).val (t.2 ()).property)] ≤
      (count : ℝ≥0∞) * (((deg : ℝ≥0) / Fintype.card R : ℝ≥0) : ℝ≥0∞) := by
  let Out' : PathAlong oracleSig (Core.protocol R deg count) → Type := fun _ => Σ tr, Out tr
  have hb := execute_soundness D ambient init impl start count finish stmt
    (interpretInput R deg n data)
    (interpretFocal (eval' := evaluate R deg) id count (Out' := fun _ => Σ tr, Out tr)
      (fun tr o => ⟨tr, o⟩) P)
    (by simpa [interpretInput, toPolynomial, Sumcheck.Impl.Computable.toOracleStatement]
      using hfalse)
  rw [executeExperiment_eq_native, prEvent_map, transport_interpretFocal] at hb
  have hrun := interval_run_eq_interpret D ambient start count finish.le stmt data
    (Out' := Out') (fun tr o => ⟨tr, o⟩) P
  have hch : transportDraw (M' := R⦃≤ deg⦄[X]) (eval' := fun p x => p.val.eval x) count
      (indexedDraw (R := R) (deg := deg) count) =
      challengeQueryImpl oracleSig (protocol R deg count) :=
    funext (transportDraw_challengeQueryImpl R deg _ _ count)
  rw [← hrun] at hb
  have he := experiment_renameQueries (M := Message R deg) (eval := evaluate R deg)
    (M' := R⦃≤ deg⦄[X]) (eval' := fun p x => p.val.eval x) count init impl
    (indexedDraw (R := R) (deg := deg) count)
    (mapObservation (toMessage R deg) count (Out' := Out') (fun tr o => ⟨tr, o⟩)
      (interpretInput R deg n) <$>
        (intervalVerifier D ambient start count finish.le).run stmt data P)
  rw [he, hch, experiment_map, prEvent_map] at hb
  refine le_trans (prEvent_mono _ _ _ fun obs hobs => ?_) hb
  obtain ⟨v, hv, hrel⟩ := hobs
  refine ⟨(v.1, interpretInput R deg n v.2), ?_, ?_⟩
  · change Option.map _ obs.2.2 = _
    rw [hv]
    rfl
  · simpa [intervalOutputProblem, Problem.language, interpretInput,
      toPolynomial, Sumcheck.Impl.Computable.toOracleStatement] using hrel

/-- A list domain retains every repeated point. -/
theorem interval_perfectCompleteness_list (domain : List R) {σ : Type} (init : ProbComp σ)
    (start count : ℕ) (bound : start + count ≤ n)
    (impl : QueryImpl (ambient + challengeSpec oracleSig (protocol R deg count))
      (StateT σ ProbComp))
    (stmt : RoundStatement R n ⟨start, by omega⟩) (data : ∀ _ : Unit, Input R deg n)
    (htrue : indexedRelation domain.get _ stmt (toPolynomial (data ()).val (data ()).property)) :
    Pr{let obs ← (intervalExperiment init impl
      ((intervalVerifier domain.get ambient start count bound).run stmt data
        (intervalHonestProver domain.get (data ()).val (data ()).property count
          (intervalInitial start count bound stmt))))}[
      ∃ t, obs.2.2 = some (t, data) ∧
        indexedRelation domain.get _ t (toPolynomial (data ()).val (data ()).property)] = 1 :=
  interval_perfectCompleteness domain.get ambient init start count bound impl stmt data htrue

/-- An injective domain specializes the indexed result. -/
theorem interval_perfectCompleteness_injective (embedding : Fin d ↪ R)
    {σ : Type} (init : ProbComp σ)
    (start count : ℕ) (bound : start + count ≤ n)
    (impl : QueryImpl (ambient + challengeSpec oracleSig (protocol R deg count))
      (StateT σ ProbComp))
    (stmt : RoundStatement R n ⟨start, by omega⟩) (data : ∀ _ : Unit, Input R deg n)
    (htrue : indexedRelation (⇑embedding) _ stmt (toPolynomial (data ()).val (data ()).property)) :
    Pr{let obs ← (intervalExperiment init impl
      ((intervalVerifier (⇑embedding) ambient start count bound).run stmt data
        (intervalHonestProver (⇑embedding) (data ()).val (data ()).property count
          (intervalInitial start count bound stmt))))}[
      ∃ t, obs.2.2 = some (t, data) ∧
        indexedRelation (⇑embedding) _ t (toPolynomial (data ()).val (data ()).property)] = 1 :=
  interval_perfectCompleteness (⇑embedding) ambient init start count bound impl stmt data htrue

omit [Nontrivial R] in
/-- A list domain retains every repeated point. -/
theorem interval_soundness_list (domain : List R) [SampleableType R] [Fintype R] [IsDomain R]
    {σ : Type} (init : ProbComp σ) (impl : QueryImpl ambient (StateT σ ProbComp))
    (start count : ℕ) (finish : start + count = n)
    (stmt : RoundStatement R n ⟨start, by omega⟩) (data : ∀ _ : Unit, Input R deg n)
    {Out : PathAlong oracleSig (protocol R deg count) → Type}
    (P : Prover oracleSig ambient (protocol R deg count) Out)
    (hfalse : ¬ indexedRelation domain.get _ stmt (toPolynomial (data ()).val (data ()).property)) :
    Pr{let obs ← (experiment init impl
      (challengeQueryImpl oracleSig (protocol R deg count))
      ((intervalVerifier domain.get ambient start count finish.le).run stmt data P))}[
        ∃ t, obs.2.2 = some t ∧
          indexedRelation domain.get _ t.1 (toPolynomial (t.2 ()).val (t.2 ()).property)] ≤
      (count : ℝ≥0∞) * (((deg : ℝ≥0) / Fintype.card R : ℝ≥0) : ℝ≥0∞) :=
  interval_soundness domain.get ambient init impl start count finish stmt data P hfalse

omit [Nontrivial R] in
/-- An injective domain specializes the indexed result. -/
theorem interval_soundness_injective (embedding : Fin d ↪ R)
    [SampleableType R] [Fintype R] [IsDomain R]
    {σ : Type} (init : ProbComp σ) (impl : QueryImpl ambient (StateT σ ProbComp))
    (start count : ℕ) (finish : start + count = n)
    (stmt : RoundStatement R n ⟨start, by omega⟩) (data : ∀ _ : Unit, Input R deg n)
    {Out : PathAlong oracleSig (protocol R deg count) → Type}
    (P : Prover oracleSig ambient (protocol R deg count) Out)
    (hfalse : ¬ indexedRelation (⇑embedding) _ stmt
      (toPolynomial (data ()).val (data ()).property)) :
    Pr{let obs ← (experiment init impl
      (challengeQueryImpl oracleSig (protocol R deg count))
      ((intervalVerifier (⇑embedding) ambient start count finish.le).run stmt data P))}[
        ∃ t, obs.2.2 = some t ∧
          indexedRelation (⇑embedding) _ t.1 (toPolynomial (t.2 ()).val (t.2 ()).property)] ≤
      (count : ℝ≥0∞) * (((deg : ℝ≥0) / Fintype.card R : ℝ≥0) : ℝ≥0∞) :=
  interval_soundness (⇑embedding) ambient init impl start count finish stmt data P hfalse

end Intervals


end Computable

end Sumcheck.Core

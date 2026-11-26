/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import Specs.Kit.Iteration

/-!
# The passive verifier of an iteration

This module builds an oracle verifier for an iteration `pre.then s`, where `s` is certified as `n`
rounds followed by a suffix, from three query programs:

* `start`: from the input statement and the verifier's view of the prefix block, the initial
  state, with query access to the input oracles and the prefix's oracle messages;
* `check i`: from the state before round `i`, the view of round `i`'s block and its challenge,
  the state after round `i`, with query access to the input oracles and the block's oracle
  messages;
* `finish`: from the final state and the view of the suffix block, the output statement, with
  query access to the input oracles and the suffix's oracle messages.

Each program may reject. The verifier keeps the input oracles as its output oracles.

* `Rounds.verifier`: the verifier.
* `Rounds.simulate_verifier`: answered from a transcript, the verifier's decision is the kit's
  verdict of the programs' pure semantics (`Block.run`), followed by `finish`.
* `Rounds.verifier_rbrSoundness` and `Rounds.verifier_soundness`: the iteration theorem for this
  verifier, with error `ε i` at round `i`'s challenge and `∑ i, ε i` overall.

## Design choices

* **Each program sees only its own block.** A round's check queries the input bundle and
  `Block.bundle` of its block, never a path-indexed bundle. The verifier routes the oracle
  messages of a path once, with `Block.route` and `Rounds.route`, into one bundle whose type does
  not depend on the path, and `Rounds.route_f` computes the routed data from the transcript. The
  author of a check therefore never sees a path or a cast.
* **The programs read the view, not the path.** The verifier reads the plain messages and the
  challenges from the view transcript with `Block.splitView`, so the decision depends on the path
  only through the routing of queries.
* **The pure semantics is the kit's `Step`.** `Check.step` answers a check's queries from the
  input data and the block's values. The iteration theorem then applies with the input data as
  part of the statement.
-/

namespace Specs.Kit

open scoped ENNReal NNReal
open PFunctor FreeM Interaction Interaction.TwoParty Interaction.TwoParty.Lens Interaction.Oracle
  OracleComp OracleSpec MeasureTheory

namespace Chal

variable {C : Type} {rest : OracleProtocol}

/-- Split a view transcript of a challenge followed by `rest`. -/
def splitView (tr : Transcript viewSig (chalThen C rest)) : C × Transcript viewSig rest :=
  (tr.1, tr.2)

/-- Route the oracle messages of a path through a challenge followed by `rest` as `R` routes
those of `rest`. A challenge adds no oracle message. -/
def route {F : OracleBundle} (R : (p : Path rest) → OracleMap (oracleMessageBundle rest p) F) :
    (p : Path (chalThen C rest)) → OracleMap (oracleMessageBundle (chalThen C rest) p) F
  | ⟨_, p⟩ => R p

/-- The route on a transcript. -/
theorem route_f {F : OracleBundle}
    (R : (p : Path rest) → OracleMap (oracleMessageBundle rest p) F) :
    ∀ tr : Transcript oracleSig (chalThen C rest),
    (route R (Transcript.path tr)).f (oracleMessages _ tr) =
      (R (Transcript.path (split tr).2)).f (oracleMessages rest (split tr).2)
  | ⟨_, _⟩ => rfl

end Chal

/-! ## Programs on a block -/

/-- Keep the first bundle after the inputs. -/
def liftLeft (inputs B R : OracleBundle) : OracleMap (inputs.sum (B.sum R)) (inputs.sum B) :=
  (OracleMap.id inputs).par (OracleMap.fst B R)

/-- Keep the second bundle after the inputs. -/
def liftRight (inputs B R : OracleBundle) : OracleMap (inputs.sum (B.sum R)) (inputs.sum R) :=
  (OracleMap.id inputs).par (OracleMap.snd B R)

/-- A program with query access to the input bundle and the oracle messages of the block `ms`. -/
abbrev Block.Program (inputs : OracleBundle) (ms : Block) (α : Type) : Type :=
  OptionT (OracleComp (inputs.sum (Block.bundle ms)).spec) α

/-- The pure semantics of a block program: its queries answered by the input data and the
block's values. -/
def Block.run (inputs : OracleBundle) (ms : Block) {α : Type} (data : inputs.Data)
    (vals : ms.Values) (prog : Block.Program inputs ms α) : Option α :=
  simulateQ (r := Id) ((inputs.sum (Block.bundle ms)).answer (data, Block.data ms vals)) prog.run

variable {n : ℕ}

/-- A round check for every round: from the state before round `i`, the view of round `i`'s
block and its challenge, a program for the state after round `i`. -/
abbrev Check (inputs : OracleBundle) (rs : Fin n → Round) (S : Fin (n + 1) → Type) : Type :=
  ∀ i : Fin n, S i.castSucc → (rs i).msgs.ViewValues → (rs i).Chal →
    Block.Program inputs (rs i).msgs (S i.succ)

/-- The pure update of a check, with its queries answered by the input data `data` and the
values of the round's block. -/
def Check.step {inputs : OracleBundle} {rs : Fin n → Round} {S : Fin (n + 1) → Type}
    (check : Check inputs rs S) (data : inputs.Data) : Step rs S := fun i st vals c =>
  Block.run inputs (rs i).msgs data vals (check i st (Block.erase _ vals) c)

/-! ## Routing the oracle messages of an iteration -/

namespace Rounds

variable {rs : Fin n → Round} {suf : Block} {S : Fin (n + 1) → Type} (inputs : OracleBundle)

/-- The bundle of the oracle messages of the rounds from `j` on and of the suffix, in order. -/
@[reducible]
def bundle : {j k : ℕ} → {h : j + k = n} → {s : OracleProtocol} → Rounds rs suf j k h s →
    OracleBundle
  | _, _, _, _, .done => (Block.bundle suf).sum .empty
  | _, _, _, _, .round j _ _ w => (Block.bundle (rs ⟨j, by omega⟩).msgs).sum w.bundle

/-- Route the oracle messages of a path through `s` into `w.bundle`. -/
def route : {j k : ℕ} → {h : j + k = n} → {s : OracleProtocol} → (w : Rounds rs suf j k h s) →
    (p : Path s) → OracleMap (oracleMessageBundle s p) w.bundle
  | _, _, _, _, .done, p =>
      @Block.route (.pure PUnit.unit) suf OracleBundle.empty (fun _ => OracleMap.id _) p
  | _, _, _, _, .round j _ _ w, p => Block.route (rs ⟨j, by omega⟩).msgs (Chal.route w.route) p

/-- The data of `w.bundle` on a transcript. It does not depend on the path. -/
def data : {j k : ℕ} → {h : j + k = n} → {s : OracleProtocol} → (w : Rounds rs suf j k h s) →
    Transcript oracleSig s → w.bundle.Data
  | _, _, _, _, .done, tr => (Block.data suf (Block.split suf tr).1, ())
  | _, _, _, _, .round j _ _ w, tr =>
      (Block.data _ (Block.split (rs ⟨j, by omega⟩).msgs tr).1,
        w.data (Chal.split (Block.split (rs ⟨j, by omega⟩).msgs tr).2).2)

/-- **The route on a transcript.** Routing the oracle messages of a transcript gives `w.data`. -/
theorem route_f : ∀ {j k : ℕ} {h : j + k = n} {s : OracleProtocol}
    (w : Rounds rs suf j k h s) (tr : Transcript oracleSig s),
    (w.route (Transcript.path tr)).f (oracleMessages s tr) = w.data tr
  | _, _, _, _, .done, tr => Block.route_f suf _ tr
  | _, _, _, _, .round j _ _ w, tr => by
    refine (Block.route_f _ _ tr).trans ?_
    rw [Chal.route_f, route_f w]
    rfl

/-! ## The decision -/

variable {T : Type} (check : Check inputs rs S)
  (finish : S (Fin.last n) → suf.ViewValues → Block.Program inputs suf T)

/-- The decision after round `j`: run the checks of the remaining rounds in order, then
`finish`. A rejection skips the remaining programs. -/
def decision : {j k : ℕ} → {h : j + k = n} → {s : OracleProtocol} → (w : Rounds rs suf j k h s) →
    S ⟨j, by omega⟩ → Transcript viewSig s → OracleComp (inputs.sum w.bundle).spec (Option T)
  | _, _, _, _, .done, st, v =>
      simulateQ (liftLeft inputs _ _).impl (finish st (Block.splitView suf v).1).run
  | _, _, _, _, .round j _ _ w, st, v =>
      simulateQ (liftLeft inputs _ _).impl (check ⟨j, by omega⟩ st
        (Block.splitView (rs ⟨j, by omega⟩).msgs v).1
        (Chal.splitView (Block.splitView (rs ⟨j, by omega⟩).msgs v).2).1).run >>= fun res =>
        res.elim (pure none) fun mid => simulateQ (liftRight inputs _ _).impl
          (w.decision mid (Chal.splitView (Block.splitView (rs ⟨j, by omega⟩).msgs v).2).2)

/-- **The decision on a transcript.** Answered from the input data and the transcript, the
decision is the kit's verdict of the checks' pure updates, followed by `finish`. -/
theorem simulate_decision (d : inputs.Data) : ∀ {j k : ℕ} {h : j + k = n} {s : OracleProtocol}
    (w : Rounds rs suf j k h s) (st : S ⟨j, by omega⟩) (tr : Transcript oracleSig s),
    simulateQ (r := Id) ((inputs.sum w.bundle).answer (d, w.data tr))
      (w.decision inputs check finish st (Transcript.mapMoves eraseOracle tr)) =
      (w.verdict (check.step d) (some st) tr).bind fun p =>
        Block.run inputs suf d p.2 (finish p.1 (Block.erase suf p.2))
  | _, _, _, _, .done, st, tr => by
    refine (OracleMap.simulate_eq _ _ _).trans ?_
    rw [Block.splitView_erase]
    rfl
  | _, _, _, _, .round j _ _ w, st, tr => by
    change simulateQ _ (simulateQ (liftLeft inputs _ _).impl _ >>= _) = _
    rw [simulateQ_bind, OracleMap.simulate_eq, Block.splitView_erase]
    change (check.step d ⟨j, by omega⟩ st (Block.split _ tr).1
      (Chal.split (Block.split _ tr).2).1 >>= _ : Id _) = _
    cases hs : check.step d ⟨j, by omega⟩ st (Block.split _ tr).1
      (Chal.split (Block.split _ tr).2).1 with
    | none =>
      change _ = Option.bind (w.verdict (check.step d)
        (Option.bind (some st) fun x => check.step d ⟨j, by omega⟩ x (Block.split _ tr).1
          (Chal.split (Block.split _ tr).2).1) _) _
      simp only [Option.bind_some, hs, verdict_none]
      rfl
    | some mid =>
      change simulateQ _ (simulateQ (liftRight inputs _ _).impl _) = _
      rw [OracleMap.simulate_eq]
      refine (simulate_decision d w mid _).trans ?_
      change _ = Option.bind (w.verdict (check.step d)
        (Option.bind (some st) fun x => check.step d ⟨j, by omega⟩ x (Block.split _ tr).1
          (Chal.split (Block.split _ tr).2).1) _) _
      simp only [Option.bind_some, hs]

end Rounds

/-! ## The verifier -/

/-- Lift the queries of a bundle into the ambient oracles and that bundle. -/
def inrLift {ι : Type} (ambient : OracleSpec ι) (B : OracleBundle) :
    QueryImpl B.spec (OracleComp (ambient + B.spec)) :=
  fun q => liftM ((ambient + B.spec).query (.inr q))

/-- Lifted bundle queries, answered from the bundle's data with ambient queries answered in any
lawful monad, are a pure computation. -/
theorem simulateQ_inrLift {ι : Type} {ambient : OracleSpec ι} {B : OracleBundle}
    {m : Type → Type} [Monad m] [LawfulMonad m] (amb : QueryImpl ambient m) (x : B.Data)
    {α : Type} (oa : OracleComp B.spec α) :
    simulateQ (QueryImpl.addLift amb (B.answer x)) (simulateQ (inrLift ambient B) oa) =
      (pure (simulateQ (B.answer x) oa) : m α) := by
  refine (QueryImpl.simulateQ_simulateQ_eq_of_apply
    (impl := (B.answer x).liftTarget m) (fun t => ?_) oa).trans ?_
  · simp only [QueryImpl.addLift_def]
    exact QueryImpl.simulateQ_add_query_right _ _ _
  · rw [simulateQ_liftTarget]
    rfl

namespace Rounds

variable {rs : Fin n → Round} {suf : Block} {S : Fin (n + 1) → Type} (inputs : OracleBundle)
  {pre : Block} {s : OracleProtocol} {Stmt T : Type}
  (start : Stmt → pre.ViewValues → Block.Program inputs pre (S 0))
  (check : Check inputs rs S)
  (finish : S (Fin.last n) → suf.ViewValues → Block.Program inputs suf T)

/-- Route the input oracles and the oracle messages of a path through an iteration into one
bundle whose type does not depend on the path. -/
def iterMap (w : Rounds rs suf 0 n (Nat.zero_add n) s) (p : Path (pre.then s)) :
    OracleMap (pathBundle inputs (pre.then s) p) (inputs.sum ((Block.bundle pre).sum w.bundle)) :=
  (OracleMap.id inputs).par (Block.route pre w.route p)

theorem iterMap_f (w : Rounds rs suf 0 n (Nat.zero_add n) s) (d : inputs.Data)
    (tr : Transcript oracleSig (pre.then s)) :
    (w.iterMap inputs (Transcript.path tr)).f (d, oracleMessages _ tr) =
      (d, (Block.data pre (Block.split pre tr).1, w.data (Block.split pre tr).2)) := by
  change (d, (Block.route pre w.route (Transcript.path tr)).f (oracleMessages _ tr)) = _
  rw [Block.route_f, route_f]

/-- The decision of an iteration as one program on the routed bundle: `start`, the checks of the
rounds, then `finish`. -/
def program (w : Rounds rs suf 0 n (Nat.zero_add n) s) (stmt : Stmt)
    (v : Transcript viewSig (pre.then s)) :
    OracleComp (inputs.sum ((Block.bundle pre).sum w.bundle)).spec (Option T) :=
  simulateQ (liftLeft inputs _ _).impl (start stmt (Block.splitView pre v).1).run >>= fun res =>
    res.elim (pure none) fun st => simulateQ (liftRight inputs _ _).impl
      (w.decision inputs check finish st (Block.splitView pre v).2)

variable {ι : Type} (ambient : OracleSpec ι)

/-- **The passive verifier of an iteration.** It runs `start`, the round checks and `finish`
against the routed oracle messages and keeps the input oracles. -/
def verifier (w : Rounds rs suf 0 n (Nat.zero_add n) s) :
    OracleVerifier ambient (pre.then s) Stmt (fun _ => T) inputs (fun _ => inputs) where
  decide stmt p v := OptionT.mk (simulateQ (inrLift ambient _)
    (simulateQ (w.iterMap inputs p).impl (w.program inputs start check finish stmt v.1)))
  outputMap _ _ _ := OracleMap.fst _ _

/-- The pure semantics of `start`. -/
def startRun (x : Stmt × inputs.Data) (vals : pre.Values) : Option (S 0) :=
  Block.run inputs pre x.2 vals (start x.1 (Block.erase pre vals))

/-- The pure semantics of `finish`. -/
def finishRun (d : inputs.Data) (p : S (Fin.last n) × suf.Values) : Option T :=
  Block.run inputs suf d p.2 (finish p.1 (Block.erase suf p.2))

/-- **The verifier on a transcript.** With its queries answered, the verifier's decision is the
kit's verdict of the programs' pure semantics, followed by `finish`. -/
theorem simulate_verifier (w : Rounds rs suf 0 n (Nat.zero_add n) s)
    {m : Type → Type} [Monad m] [LawfulMonad m] (impl : QueryImpl ambient m)
    (x : Stmt × inputs.Data) (tr : Transcript oracleSig (pre.then s)) :
    simulateQ (QueryImpl.addLift impl
      ((pathBundle inputs (pre.then s) (Transcript.path tr)).answer (x.2, oracleMessages _ tr)))
      ((w.verifier inputs start check finish ambient).decide x.1 _ (toView _ tr)).run =
      (pure ((w.iterVerdict (startRun inputs start) (fun x => check.step x.2) x tr).bind
        (finishRun inputs finish x.2)) : m _) := by
  change simulateQ _ (simulateQ (inrLift ambient _) _) = _
  rw [simulateQ_inrLift]
  congr 1
  rw [OracleMap.simulate_eq, iterMap_f]
  change simulateQ _ (w.program inputs start check finish x.1
    (Transcript.mapMoves eraseOracle tr)) = _
  unfold program
  rw [Block.splitView_erase, simulateQ_bind, OracleMap.simulate_eq]
  change (startRun inputs start x (Block.split pre tr).1 >>= _ : Id _) = _
  unfold iterVerdict
  cases startRun inputs start x (Block.split pre tr).1 with
  | none =>
    exact (congrArg (fun o => Option.bind o (finishRun inputs finish x.2))
      (verdict_none (check.step x.2) w (Block.split pre tr).2)).symm
  | some st =>
    change simulateQ _ (simulateQ (liftRight inputs _ _).impl _) = _
    rw [OracleMap.simulate_eq]
    exact simulate_decision inputs check finish x.2 w st (Block.split pre tr).2

/-- Valid acceptance by the verifier means an unrejected final state and suffix whose output is
in the event. -/
theorem verifier_validAcceptance (w : Rounds rs suf 0 n (Nat.zero_add n) s) {σ : Type}
    (impl : QueryImpl ambient (StateT σ ProbComp)) (x : Stmt × inputs.Data)
    (tr : Transcript oracleSig (pre.then s)) (event : T × inputs.Data → Prop) :
    (w.verifier inputs start check finish ambient).validAcceptance impl x tr event →
      ∃ p, w.iterVerdict (startRun inputs start) (fun x => check.step x.2) x tr = some p ∧
        ∃ t, finishRun inputs finish x.2 p = some t ∧ event (t, x.2) := by
  unfold OracleVerifier.validAcceptance
  dsimp only
  rw [simulate_verifier]
  intro h
  obtain ⟨state, hs⟩ := h
  classical
  by_contra hf
  cases hv : (w.iterVerdict (startRun inputs start) (fun x => check.step x.2) x tr).bind
      (finishRun inputs finish x.2) with
  | none => simp [hv] at hs
  | some t =>
    obtain ⟨p, hp, ht⟩ := Option.bind_eq_some_iff.mp hv
    have hne : ¬ event (t, x.2) := fun he => hf ⟨p, hp, t, ht, he⟩
    simp [hv, verifier, OracleMap.fst, hne] at hs

/-- **The iteration theorem for the passive verifier.** Besides the per-round obligation for the
checks' pure updates, the author proves the root law for `start` (`hroot`) and that an accepted
output of `finish` makes the final claim true (`hfinish`). -/
theorem verifier_rbrSoundness (w : Rounds rs suf 0 n (Nat.zero_add n) s) {σ : Type}
    (impl : QueryImpl ambient (StateT σ ProbComp))
    (input : StatementProblem (Stmt × inputs.Data))
    (output : PathProblem (pre.then s) (fun _ => T × inputs.Data))
    (good : Stmt × inputs.Data → ∀ i, S i → Prop)
    (draw : QueryImpl (challengeSpec oracleSig (pre.then s)) ProbComp)
    (chal : ∀ i, ProbComp (rs i).Chal) (ε : Fin n → ℝ≥0∞)
    (hdraw : ∀ vals, w.DrawIs chal (Block.restrictDraw pre vals draw))
    (hroot : ∀ x vals st, input.admissible () x → startRun inputs start x vals = some st →
      good x 0 st → input.language () x)
    (hfinish : ∀ x p q t, finishRun inputs finish x.2 q = some t →
      output.language p (t, x.2) → good x (Fin.last n) q.1)
    (hround : ∀ x, RoundSound chal (check.step x.2) (good x) ε) :
    (w.verifier inputs start check finish ambient).rbrSoundness impl input output draw
      (fun c => ε (w.iterRoundOf c)) := by
  refine w.rbrSoundness (admissible := input.admissible ()) (language := input.language ())
    (startRun inputs start) (fun x => check.step x.2) good draw chal ε hdraw hroot
    (fun x tr hacc => ?_) hround
  obtain ⟨p, hp, t, ht, hl⟩ :=
    verifier_validAcceptance inputs start check finish ambient w impl x tr _ hacc
  exact ⟨p, hp, hfinish x _ p t ht hl⟩

/-- **The iteration theorem for the passive verifier, soundness form.** The verifier is sound
with error `∑ i, ε i`. -/
theorem verifier_soundness (w : Rounds rs suf 0 n (Nat.zero_add n) s) {σ : Type}
    (init : ProbComp σ) (impl : QueryImpl ambient (StateT σ ProbComp))
    (input : StatementProblem (Stmt × inputs.Data))
    (output : PathProblem (pre.then s) (fun _ => T × inputs.Data))
    (good : Stmt × inputs.Data → ∀ i, S i → Prop)
    (draw : QueryImpl (challengeSpec oracleSig (pre.then s)) ProbComp)
    (chal : ∀ i, ProbComp (rs i).Chal) (ε : Fin n → ℝ≥0∞)
    (hdraw : ∀ vals, w.DrawIs chal (Block.restrictDraw pre vals draw))
    (hroot : ∀ x vals st, input.admissible () x → startRun inputs start x vals = some st →
      good x 0 st → input.language () x)
    (hfinish : ∀ x p q t, finishRun inputs finish x.2 q = some t →
      output.language p (t, x.2) → good x (Fin.last n) q.1)
    (hround : ∀ x, RoundSound chal (check.step x.2) (good x) ε) :
    (w.verifier inputs start check finish ambient).soundness init impl draw input output
      (∑ i, ε i) :=
  w.soundness_of_rbrSoundness (init := init)
    (verifier_rbrSoundness inputs start check finish ambient w impl input output good draw chal ε
      hdraw hroot hfinish hround)

end Rounds

end Specs.Kit

/-! ## Axioms -/

#print axioms Specs.Kit.Rounds.route_f
#print axioms Specs.Kit.Rounds.simulate_decision
#print axioms Specs.Kit.Rounds.simulate_verifier
#print axioms Specs.Kit.Rounds.verifier_validAcceptance
#print axioms Specs.Kit.Rounds.verifier_rbrSoundness
#print axioms Specs.Kit.Rounds.verifier_soundness

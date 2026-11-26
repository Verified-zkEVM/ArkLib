/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import Specs.Security
import Specs.Kit.Iteration
import Specs.Kit.Verifier
import ArkLib.Interaction.Security.Agreement

/-!
# From a `rounds` block to the kit's iteration theorem

This module connects a specification's `rounds` block to the iteration kit of
`Specs.Kit.Iteration`, and concludes the specification's soundness from the kit's per-round
obligation.

* `Bridge.cert`: a tree family that satisfies the `rounds` equations with round shape
  `(rsN i).then` is certified as the kit's rounds (`Kit.Rounds`). Each case is a cast along the
  tree equation, so with `rfl` equations, as `rounds` uses by default, the certificate computes.
* `Bridge.verdict_roundsGo` (**the bridge theorem**): the verdict of the rounds `j, …, j + k - 1`
  of a `rounds` block (`roundsFrom`) is the kit's verdict `Kit.Rounds.verdict` on the
  certificate, followed by the continuation's verdict. The hypotheses are one round (`hbody`) and
  the continuation (`hnext`), each for an arbitrary transcript.
* `Bridge.decide_eq_iterVerdict` and `Bridge.agrees_of_kit`: when the verdict factors through the
  kit (`hverdict`), the specification's derived verifier decides as the kit's `iterVerdict` on every
  transcript, and it agrees (ArkLib's `OracleVerifier.Agrees`) with the kit's iteration verifier
  `Kit.Rounds.verifier` whose check programs have that step as their pure semantics.
* `Bridge.rbrSound_of_kit` and `Bridge.sound_of_kit`: a specification whose verdict factors
  through the kit's `iterVerdict` is round-by-round sound and sound, from the per-round obligation
  `Kit.RoundSound`. They apply `Kit.Rounds.rbrSoundness` to the specification's own verifier, so
  the conclusion is `Spec.RBRSound` and `Spec.Sound` of the specification.

## Design choices

* **The round state is the `rounds` block's own state.** The kit's state at round `i : Fin (n+1)`
  is `State i.val`, and the kit's round family is `fun i => rsN i.val`. *Why:* the description's
  round body already maps `State i` to `State (i + 1)`, so the kit's step is the body's pure
  meaning and needs no translation.
* **The round shape is a hypothesis `hF : F i t = (rsN i).then t`.** The `rounds` combinator
  infers its round shape `F` from the body's type. *Why:* stating the theorem for an arbitrary
  `F` lets it apply to the description as elaborated, with no unfolding at the use site. A use
  site proves `hF` by `rfl`.
* **One round is a hypothesis about the body on an arbitrary transcript.** `hbody` says that the
  body's verdict is the kit step, then the continuation on the rest of the transcript with some
  handler table. *Why:* the round body is an arbitrary description, so its meaning must be given
  once; every other step of the induction is generic. The invariant `Inv` on handler tables lets a
  round body rely on what the earlier rounds and the input reads put in the table.
* **The continuation's verdict reads only the final state and the suffix values** (`hnext`).
  *Why:* the kit's verdict returns exactly these. A continuation that needs another value carries
  it in the state.
* **Soundness takes the factorisation `hverdict` as a hypothesis.** *Why:* the steps before the
  `rounds` block (input reads, stage markers) differ between specifications, and each instance
  proves the factorisation from `verdict_roundsGo` in one or two lines.
-/

set_option linter.hashCommand false

namespace Specs
open Interaction PFunctor FreeM OracleComp OracleSpec Interaction.TwoParty.Lens
open Specs.Kit
open scoped ENNReal

variable {In : OracleBundle} {W T : Type}

/-- The verdict of a description moved to an equal tree is its verdict on the moved
transcript. -/
theorem Desc.verdict_retree {t t' : OracleProtocol} {ks : Skel} (e : t = t')
    (d : Desc In W T t ks) (ans : QueryImpl In.spec Id) (tr : Transcript oracleSig t')
    (env : Handlers Id) (ℓ : ℕ) :
    (d.retree e).verdict ans tr env ℓ =
      d.verdict ans (cast (congrArg (Transcript oracleSig) e.symm) tr) env ℓ := by
  subst e
  rfl

/-- Moving a description to an equal skeleton keeps its verdict. -/
theorem Desc.verdict_reskel {t : OracleProtocol} {ks ks' : Skel} (e : ks = ks')
    (d : Desc In W T t ks) (ans : QueryImpl In.spec Id) (tr : Transcript oracleSig t)
    (env : Handlers Id) (ℓ : ℕ) : (d.reskel e).verdict ans tr env ℓ = d.verdict ans tr env ℓ := by
  subst e
  rfl

namespace Bridge

variable {n : ℕ} {rsN : ℕ → Round} {suf : Block}

/-- The kit's round family of a `rounds` block with round shapes `rsN`. -/
abbrev fam (n : ℕ) (rsN : ℕ → Round) : Fin n → Round := fun i => rsN i.val

/-- The kit's verdict on a certificate moved to an equal tree is its verdict on the moved
transcript. -/
theorem verdict_cast {S : Fin (n + 1) → Type} (step : Step (fam n rsN) S) {j k : ℕ}
    {h : j + k = n} {s s' : OracleProtocol} (e : s = s')
    (w : Rounds (fam n rsN) suf j k h s) (st : Option (S ⟨j, by omega⟩))
    (tr : Transcript oracleSig s') :
    (cast (congrArg (Rounds (fam n rsN) suf j k h) e) w).verdict step st tr =
      w.verdict step st (cast (congrArg (Transcript oracleSig) e.symm) tr) := by
  subst e
  rfl

/-- **The certificate of a `rounds` block.** A tree family `τ` with the equations of `rounds`,
whose round shape is `(rsN j).then`, is the kit's rounds `j, …, j + k - 1` followed by the suffix
`suf`. -/
def cert (τ : ℕ → ℕ → OracleProtocol) (h0 : ∀ j, τ j 0 = suf.then (.pure PUnit.unit))
    (hS : ∀ j k, τ j (k + 1) = (rsN j).then (τ (j + 1) k)) :
    (k j : ℕ) → (h : j + k = n) → Rounds (fam n rsN) suf j k h (τ j k)
  | 0, j, h => cast (congrArg (Rounds (fam n rsN) suf j 0 h) (h0 j).symm)
      (by subst h; exact .done)
  | k + 1, j, h => cast (congrArg (Rounds (fam n rsN) suf j (k + 1) h) (hS j k).symm)
      (.round j k h (cert τ h0 hS k (j + 1) (by omega)))

variable {State : ℕ → Type} {F : ℕ → OracleProtocol → OracleProtocol} {G : Skel → Skel}

/-- **The bridge theorem.** The verdict of the rounds `j, …, j + k - 1` of a `rounds` block is
the kit's verdict on the certificate `cert`, followed by the continuation's verdict `fin`, when

* `hbody`: one round's verdict is the kit step `step`, then the continuation's verdict on the
  rest of the transcript with some handler table that keeps the invariant `Inv`;
* `hnext`: the continuation's verdict is `fin` of the final state and the suffix values. -/
theorem verdict_roundsGo (ans : QueryImpl In.spec Id) (l : Loop)
    (body : ∀ {t : OracleProtocol} {ks : Skel}, (i : ℕ) → i < n → State i →
      (State (i + 1) → Desc In W T t ks) → Desc In W T (F i t) (G ks))
    {ks : Skel} (next : State n → Desc In W T (suf.then (.pure PUnit.unit)) ks)
    (τ : ℕ → ℕ → OracleProtocol) (h0 : ∀ j, τ j 0 = suf.then (.pure PUnit.unit))
    (hS : ∀ j k, τ j (k + 1) = F j (τ (j + 1) k)) (hG : ∀ ks, G ks = (G .done).seq ks)
    (hF : ∀ i t, F i t = (rsN i).then t)
    (step : Step (fam n rsN) (fun i => State i.val)) (fin : State n → suf.Values → Option T)
    (Inv : Handlers Id → ℕ → Prop)
    (hbody : ∀ {t : OracleProtocol} {ks : Skel} (i : ℕ) (hi : i < n) (st : State i)
      (nx : State (i + 1) → Desc In W T t ks) (tr : Transcript oracleSig (F i t))
      (env : Handlers Id) (ℓ : ℕ), Inv env ℓ →
      ∃ env' ℓ', Inv env' ℓ' ∧ (body i hi st nx).verdict ans tr env ℓ =
        (step ⟨i, hi⟩ st
          (Block.split (rsN i).msgs (cast (congrArg (Transcript oracleSig) (hF i t)) tr)).1
          (Chal.split (Block.split (rsN i).msgs
            (cast (congrArg (Transcript oracleSig) (hF i t)) tr)).2).1).bind fun st' =>
          (nx st').verdict ans (Chal.split (Block.split (rsN i).msgs
            (cast (congrArg (Transcript oracleSig) (hF i t)) tr)).2).2 env' ℓ')
    (hnext : ∀ st tr env ℓ, Inv env ℓ →
      (next st).verdict ans tr env ℓ = fin st (Block.split suf tr).1) :
    ∀ (k j : ℕ) (h : j + k = n) (st : State j) (tr : Transcript oracleSig (τ j k))
      (env : Handlers Id) (ℓ : ℕ), Inv env ℓ →
      (roundsFrom l n body next τ h0 hS hG k j h st).verdict ans tr env ℓ =
        ((cert τ h0 (fun j k => (hS j k).trans (hF j _)) k j h).verdict step (some st)
          tr).bind fun p => fin p.1 p.2 := by
  intro k
  induction k with
  | zero =>
    intro j h st tr env ℓ hinv
    subst h
    dsimp only [roundsFrom]
    rw [roundsGo, Desc.verdict_retree, hnext _ _ _ _ hinv, cert,
      verdict_cast (e := (h0 _).symm)]
    rfl
  | succ k ih =>
    intro j h st tr env ℓ hinv
    dsimp only [roundsFrom]
    rw [roundsGo, Desc.verdict_retree]
    erw [Desc.verdict.eq_11, Desc.verdict_reskel]
    obtain ⟨env', ℓ', hinv', hb⟩ := hbody j (by omega) st
      (fun st' => .mark .endRound (roundsFrom l n body next τ h0 hS hG k (j + 1) (by omega) st'))
      _ env ℓ hinv
    rw [hb, cert, verdict_cast (e := ((hS j k).trans (hF j _)).symm), Rounds.verdict, cast_cast]
    simp only [Option.bind_some]
    generalize hc : cast _ tr = tr'
    cases hs : step ⟨j, by omega⟩ st (Block.split (rsN j).msgs tr').1
        (Chal.split (Block.split (rsN j).msgs tr').2).1 with
    | none => simp
    | some st' =>
      simp only [Option.bind_some]
      erw [Desc.verdict.eq_11]
      exact ih (j + 1) (by omega) st' _ env' ℓ' hinv'

end Bridge

/-! ## Soundness of a specification through the kit -/

namespace Bridge

variable {n : ℕ} {S : Type} {ks : Skel} {pre suf : Block} {s : OracleProtocol}
  {rs : Fin n → Round} {K : Fin (n + 1) → Type}

/-- **The derived verifier decides as the kit.** If the verdict factors through the kit's
`iterVerdict`, the specification's verifier, with its queries answered from the input data and the
transcript, returns that verdict. -/
theorem decide_eq_iterVerdict (sp : Spec In S W T (pre.then s) ks) {ι : Type}
    (ambient : OracleSpec ι) {m : Type → Type} [Monad m] [LawfulMonad m]
    (amb : QueryImpl ambient m) (w : Rounds rs suf 0 n (Nat.zero_add n) s)
    (start : S × In.Data → pre.Values → Option (K 0)) (step : S × In.Data → Step rs K)
    (finish : S × In.Data → K (Fin.last n) × suf.Values → Option T)
    (hverdict : ∀ x tr, sp.verdict x.1 x.2 tr = (w.iterVerdict start step x tr).bind (finish x))
    (x : S × In.Data) (tr : Transcript oracleSig (pre.then s)) :
    simulateQ (QueryImpl.addLift (r := m) amb ((pathBundle In (pre.then s) tr.path).answer
        (x.2, oracleMessages _ tr))) ((sp.verifier ambient).decide x.1 _ (toView _ tr)).run =
      pure ((w.iterVerdict start step x tr).bind (finish x)) := by
  rw [Spec.decide_eq_verdict, hverdict]

/-- **The derived verifier agrees with the kit's iteration verifier.** If the verdict factors
through the kit with the pure semantics of the kit's programs `start`, `check` and `finish`, the
specification's verifier and `Kit.Rounds.verifier` agree in ArkLib's sense, so every security
notion transfers between them (`OracleVerifier.Agrees.soundness_iff` and its siblings). -/
theorem agrees_of_kit (sp : Spec In S W T (pre.then s) ks) {ι : Type} (ambient : OracleSpec ι)
    (w : Rounds rs suf 0 n (Nat.zero_add n) s)
    (start : S → pre.ViewValues → Block.Program In pre (K 0)) (check : Check In rs K)
    (finish : K (Fin.last n) → suf.ViewValues → Block.Program In suf T)
    (hverdict : ∀ x tr, sp.verdict x.1 x.2 tr =
      (w.iterVerdict (Rounds.startRun In start) (fun x => check.step x.2) x tr).bind
        (Rounds.finishRun In finish x.2)) :
    OracleVerifier.Agrees (sp.verifier ambient) (w.verifier In start check finish ambient) :=
  fun stmt data tr =>
    ⟨fun _ _ _ amb => by
      rw [Spec.decide_eq_verdict]
      exact (congrArg pure (hverdict (stmt, data) tr)).trans
        (Rounds.simulate_verifier In start check finish ambient w amb (stmt, data) tr).symm, rfl⟩

/-- **Round-by-round soundness of a specification through the kit.** A specification on the tree
`pre.then s`, where `s` is certified as `n` rounds followed by the suffix `suf`, is round-by-round
sound with error `ε i` at the challenge of round `i`, given:

* `hverdict`: the specification's verdict is the kit's `iterVerdict`, then `finish`;
* `hdraw`: the challenge of round `i` is drawn by `chal i`;
* `hroot`: an admissible input whose initial state holds is in the input language;
* `hfinish`: an output in the output language comes from a final state whose claim holds;
* `hround`: the per-round obligation `Kit.RoundSound`. -/
theorem rbrSound_of_kit (sp : Spec In S W T (pre.then s) ks) {ι σ : Type}
    (ambient : OracleSpec ι) (impl : QueryImpl ambient (StateT σ ProbComp))
    (input : StatementProblem (S × In.Data))
    (output : PathProblem (pre.then s) (fun _ => T × In.Data))
    (draw : QueryImpl (challengeSpec oracleSig (pre.then s)) ProbComp)
    (w : Rounds rs suf 0 n (Nat.zero_add n) s)
    (start : S × In.Data → pre.Values → Option (K 0)) (step : S × In.Data → Step rs K)
    (finish : S × In.Data → K (Fin.last n) × suf.Values → Option T)
    (good : S × In.Data → ∀ i, K i → Prop) (chal : ∀ i, ProbComp (rs i).Chal)
    (ε : Fin n → ℝ≥0∞)
    (hverdict : ∀ x tr, sp.verdict x.1 x.2 tr = (w.iterVerdict start step x tr).bind (finish x))
    (hdraw : ∀ vals, w.DrawIs chal (Block.restrictDraw pre vals draw))
    (hroot : ∀ x vals st, input.admissible () x → start x vals = some st → good x 0 st →
      input.language () x)
    (hfinish : ∀ x p q o, finish x q = some o → output.language p (o, x.2) →
      good x (Fin.last n) q.1)
    (hround : ∀ x, RoundSound chal (step x) (good x) ε) :
    sp.RBRSound ambient impl input output draw (fun c => ε (w.iterRoundOf c)) := by
  refine w.rbrSoundness start step good draw chal ε hdraw hroot (fun x tr hacc => ?_) hround
  obtain ⟨o, hv, hl⟩ := sp.verdict_of_validAcceptance ambient impl x tr _ hacc
  rw [hverdict, Option.bind_eq_some_iff] at hv
  obtain ⟨q, hq, hf⟩ := hv
  exact ⟨q, hq, hfinish x _ q o hf hl⟩

/-- **Soundness of a specification through the kit**, with error `∑ i, ε i`. -/
theorem sound_of_kit (sp : Spec In S W T (pre.then s) ks) {ι σ : Type}
    (ambient : OracleSpec ι) (init : ProbComp σ) (impl : QueryImpl ambient (StateT σ ProbComp))
    (input : StatementProblem (S × In.Data))
    (output : PathProblem (pre.then s) (fun _ => T × In.Data))
    (draw : QueryImpl (challengeSpec oracleSig (pre.then s)) ProbComp)
    (w : Rounds rs suf 0 n (Nat.zero_add n) s)
    (start : S × In.Data → pre.Values → Option (K 0)) (step : S × In.Data → Step rs K)
    (finish : S × In.Data → K (Fin.last n) × suf.Values → Option T)
    (good : S × In.Data → ∀ i, K i → Prop) (chal : ∀ i, ProbComp (rs i).Chal)
    (ε : Fin n → ℝ≥0∞)
    (hverdict : ∀ x tr, sp.verdict x.1 x.2 tr = (w.iterVerdict start step x tr).bind (finish x))
    (hdraw : ∀ vals, w.DrawIs chal (Block.restrictDraw pre vals draw))
    (hroot : ∀ x vals st, input.admissible () x → start x vals = some st → good x 0 st →
      input.language () x)
    (hfinish : ∀ x p q o, finish x q = some o → output.language p (o, x.2) →
      good x (Fin.last n) q.1)
    (hround : ∀ x, RoundSound chal (step x) (good x) ε) :
    sp.Sound ambient init impl draw input output (∑ i, ε i) :=
  w.soundness_of_rbrSoundness (V := sp.verifier ambient) (init := init)
    (rbrSound_of_kit sp ambient impl input output draw w start step finish good chal ε hverdict
      hdraw hroot hfinish hround)

end Bridge

end Specs

#print axioms Specs.Bridge.verdict_roundsGo
#print axioms Specs.Bridge.decide_eq_iterVerdict
#print axioms Specs.Bridge.agrees_of_kit
#print axioms Specs.Bridge.rbrSound_of_kit
#print axioms Specs.Bridge.sound_of_kit

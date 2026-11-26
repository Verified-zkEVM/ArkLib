/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import Specs.Kit.Block

/-!
# The iteration theorem of the proof kit

This module provides the kit's round, its certificate and the iteration theorem. A round `i` is a
block of prover messages followed by one verifier challenge. An iteration of `n` rounds has a
prefix block before round `0` and a suffix block after the last challenge. The iteration theorem
proves round-by-round soundness of every protocol certified as an iteration from one per-round
obligation, `RoundSound`, and three local laws. None of its hypotheses mentions a cursor, a spine
or a partial transcript.

## The tree shape of an instance

A protocol `t : OracleProtocol` is an instance with prefix `pre`, rounds `rs : Fin n → Round` and
suffix `suf` when `t` is `pre.then s` and `w : Rounds rs suf 0 n _ s` certifies `s`. The
certificate has two constructors, and each fixes the tree up to definitional unfolding:

* `Rounds.done : Rounds rs suf n 0 rfl (suf.then (.pure PUnit.unit))`: after the last round, the
  prover sends the suffix block and the protocol ends;
* `Rounds.round j k h w : Rounds rs suf j (k + 1) h ((rs ⟨j, _⟩).then rest)`, where
  `w : Rounds rs suf (j + 1) k _ rest`: round `j` is the tree

  ```
  (rs j).msgs.then (.liftBind (.challenge (rs j).Chal) fun _ => rest)
  ```

  that is, one `.liftBind` node per message of the block (`.message X` for `Msg.plain X`,
  `.oracle X I` for `Msg.oracle X I`, each continuing with a constant function), then one
  challenge node continuing with the constant function `fun _ => rest`.

A block `[m₁, …, mₖ]` followed by `rest` is the tree
`.liftBind m₁.pos fun _ => … .liftBind mₖ.pos fun _ => rest`. With an empty prefix, `[].then s`
is `s` by definition, and with an empty suffix the last subtree is `.pure PUnit.unit`.

A protocol that a recursion defines in exactly this shape, such as sum-check's
`Sumcheck.protocol R deg n`, is an instance through a certificate that the same recursion
builds: every constructor's index agrees with the protocol by definition, so statements keep the
protocol's own name and need no casts. `Rounds.ofIter` builds the certificate of the kit's own
tree `iterFrom`.

## Main results

* `RoundSound chal step good ε`: from a state whose claim is false, every value of round `i`'s
  block passes round `i` into a state whose claim is true with probability at most `ε i` over
  `chal i`.
* `Rounds.rbrSoundness`: the iteration theorem, round-by-round form, with error `ε i` at the
  challenge of round `i`.
* `Rounds.soundness_of_rbrSoundness`: an oracle verifier with that round-by-round error is sound
  with error `∑ i, ε i`.
* `Rounds.challengeDraw chal`: the draw that draws round `i`'s challenge by `chal i`, and
  `Rounds.drawIs_challengeDraw`, which discharges the iteration theorem's `hdraw` for it.

The passive verifier of an iteration, built from per-round query programs, is in
`Specs.Kit.Verifier`.

## Design choices

* **The round has one challenge.** Every interactive proof in ArkLib that the kit targets
  alternates prover blocks and single challenges. Two consecutive challenges are one challenge of
  the product type, so this costs no generality for round-by-round soundness.
* **States may be rejected.** The analysis state before round `i` has type `Option (S i)`. A round
  update `Step` returns `none` when its check rejects, and the state function holds only for an
  unrejected state whose claim holds (`holds`). The prefix block gives the initial state
  (`start`), so a protocol whose first claim depends on prefix messages is an instance.
* **Statements may vary every parameter.** The update, the claim and the initial state take the
  input statement, because a claim usually mentions the input (sum-check's polynomial, FRI's
  input word).
* **The state function is built from the walks of `Specs.Kit.Block`.** A block keeps the state
  until it is complete, then the challenge applies the round update. The two lemmas `Block.Flips`
  and `Block.LeafOK` compose block by block, so the proofs here are short inductions on the
  certificate.
-/

namespace Specs.Kit

open scoped ENNReal NNReal
open PFunctor FreeM Interaction Interaction.TwoParty Interaction.TwoParty.Lens Interaction.Oracle
  OracleComp OracleSpec MeasureTheory

/-! ## Challenges -/

namespace Chal

variable {C : Type} {rest : OracleProtocol}

/-- Split a transcript of a challenge followed by `rest`. -/
def split (tr : Transcript oracleSig (chalThen C rest)) : C × Transcript oracleSig rest :=
  (tr.1, tr.2)

/-- A function on the challenge nodes of a challenge followed by `rest`: `here` at the
challenge, `there` below it. -/
def onNode {α : Type} (here : α) (there : ChallengeNode oracleSig rest → α) :
    ChallengeNode oracleSig (chalThen C rest) → α
  | ⟨.inl _, _⟩ => here
  | ⟨.inr ⟨_, c⟩, h⟩ => there ⟨c, h⟩

/-- The challenge nodes along a path through a challenge followed by `rest`: the challenge and
the challenge nodes of `rest`. -/
theorem sum_challengeNodesOn (g : ChallengeNode oracleSig (chalThen C rest) → ℝ≥0∞)
    (p : Path rest) :
    ∑ c ∈ challengeNodesOn oracleSig (chalThen C rest) ⟨⟨⟩, p⟩, g c =
      g node + ∑ c ∈ challengeNodesOn oracleSig rest p, g ⟨.inr ⟨⟨⟩, c.1⟩, c.2⟩ := by
  simp only [challengeNodesOn, owner, oracleSig]
  refine (Finset.sum_cons _).trans ?_
  exact congrArg _ (Finset.sum_map _ _ _)

end Chal

/-! ## Rounds and their certificate -/

/-- One round of an iteration: a block of prover messages, then one verifier challenge. -/
structure Round : Type 1 where
  /-- The prover's messages, in order. -/
  msgs : Block
  /-- The verifier's challenge. -/
  Chal : Type

/-- One round followed by the protocol `rest`. -/
@[reducible]
def Round.then (r : Round) (rest : OracleProtocol) : OracleProtocol :=
  r.msgs.then (chalThen r.Chal rest)

variable {n : ℕ}

/-- Rounds `j, …, n - 1` of the family `rs` followed by the suffix block, where `j + k = n`. -/
def iterFrom (rs : Fin n → Round) (suf : Block) : (j k : ℕ) → j + k = n → OracleProtocol
  | _, 0, _ => suf.then (.pure PUnit.unit)
  | j, k + 1, h => (rs ⟨j, by omega⟩).then (iterFrom rs suf (j + 1) k (by omega))

/-- The kit's own tree of an iteration: the prefix, the `n` rounds and the suffix. -/
abbrev iterate (pre : Block) (rs : Fin n → Round) (suf : Block) : OracleProtocol :=
  pre.then (iterFrom rs suf 0 n (Nat.zero_add n))

/-- `Rounds rs suf j k h s` certifies that `s` is rounds `j, …, j + k - 1` of the family `rs`
followed by the suffix block `suf`, where `j + k = n`.

A protocol defined by its own recursion is an instance through a recursion whose cases hold by
definition, so the protocol keeps its own name in every statement. -/
inductive Rounds (rs : Fin n → Round) (suf : Block) :
    (j k : ℕ) → j + k = n → OracleProtocol → Type 1
  /-- After the last round, the suffix block and the end of the protocol. -/
  | done : Rounds rs suf n 0 rfl (suf.then (.pure PUnit.unit))
  /-- Round `j`, then the rounds after it. -/
  | round (j k : ℕ) (h : j + (k + 1) = n) {rest : OracleProtocol} :
      Rounds rs suf (j + 1) k (by omega) rest →
        Rounds rs suf j (k + 1) h ((rs ⟨j, by omega⟩).then rest)

/-- The kit's own tree is an instance. -/
def Rounds.ofIter (rs : Fin n → Round) (suf : Block) : (j k : ℕ) → (h : j + k = n) →
    Rounds rs suf j k h (iterFrom rs suf j k h)
  | j, 0, h => by subst h; exact .done
  | j, k + 1, h => .round j k h (Rounds.ofIter rs suf (j + 1) k (by omega))

section Generic

variable {rs : Fin n → Round} {suf : Block} {S : Fin (n + 1) → Type}

/-- A pure state update for every round: the state before round `i`, the values of the round's
block and its challenge give the state after it, or `none` if the round's check rejects. -/
abbrev Step (rs : Fin n → Round) (S : Fin (n + 1) → Type) : Type :=
  ∀ i : Fin n, S i.castSucc → (rs i).msgs.Values → (rs i).Chal → Option (S i.succ)

/-- A possibly rejected state holds when it was not rejected and its claim is true. -/
def holds (good : ∀ i, S i → Prop) {i : Fin (n + 1)} : Option (S i) → Prop
  | none => False
  | some x => good i x

@[simp] theorem holds_none (good : ∀ i, S i → Prop) {i : Fin (n + 1)} :
    holds good (none : Option (S i)) ↔ False := Iff.rfl

@[simp] theorem holds_some (good : ∀ i, S i → Prop) {i : Fin (n + 1)} (x : S i) :
    holds good (some x) ↔ good i x := Iff.rfl

/-- **The per-round obligation.** From a state whose claim is false, every value of round `i`'s
block passes round `i` into a state whose claim is true with probability at most `ε i` over the
round's challenge. -/
def RoundSound (chal : ∀ i, ProbComp (rs i).Chal) (step : Step rs S)
    (good : ∀ i, S i → Prop) (ε : Fin n → ℝ≥0∞) : Prop :=
  ∀ (i : Fin n) (st : S i.castSucc) (vals : (rs i).msgs.Values), ¬ good i.castSucc st →
    Pr{let c ← chal i}[∃ st', step i st vals c = some st' ∧ good i.succ st'] ≤ ε i

namespace Rounds

/-- The final state and the suffix values after a completed transcript, or `none` if some
round's check rejects. -/
def verdict (step : Step rs S) : {j k : ℕ} → {h : j + k = n} → {s : OracleProtocol} →
    Rounds rs suf j k h s → Option (S ⟨j, by omega⟩) → Transcript oracleSig s →
    Option (S (Fin.last n) × suf.Values)
  | _, _, _, _, .done, st, tr => st.map fun x => (x, (Block.split suf tr).1)
  | _, _, _, _, .round j k h w, st, tr =>
      w.verdict step
        (st.bind fun x => step ⟨j, by omega⟩ x (Block.split (rs ⟨j, by omega⟩).msgs tr).1
          (Chal.split (Block.split (rs ⟨j, by omega⟩).msgs tr).2).1)
        (Chal.split (Block.split (rs ⟨j, by omega⟩).msgs tr).2).2

/-- A rejected state stays rejected. -/
@[simp]
theorem verdict_none (step : Step rs S) : ∀ {j k : ℕ} {h : j + k = n} {s : OracleProtocol}
    (w : Rounds rs suf j k h s) (tr : Transcript oracleSig s), w.verdict step none tr = none
  | _, _, _, _, .done, _ => rfl
  | _, _, _, _, .round _ _ _ w, _ => verdict_none step w _

/-- The round of each challenge node. -/
def roundOf : {j k : ℕ} → {h : j + k = n} → {s : OracleProtocol} →
    Rounds rs suf j k h s → ChallengeNode oracleSig s → Fin n
  | _, _, _, _, .done, c => (Block.noChallenge suf c).elim
  | _, _, _, _, .round j k h w, c =>
      Chal.onNode ⟨j, by omega⟩ w.roundOf (Block.tailNode (rs ⟨j, by omega⟩).msgs c)

/-- The challenge of round `i` is drawn by `chal i`, whatever the values of the earlier
blocks. -/
def DrawIs (chal : ∀ i, ProbComp (rs i).Chal) : {j k : ℕ} → {h : j + k = n} →
    {s : OracleProtocol} → Rounds rs suf j k h s →
    QueryImpl (challengeSpec oracleSig s) ProbComp → Prop
  | _, _, _, _, .done, _ => True
  | _, _, _, _, .round j k h w, draw => ∀ vals : (rs ⟨j, by omega⟩).msgs.Values,
      Chal.headDraw (Block.restrictDraw (rs ⟨j, by omega⟩).msgs vals draw) = chal ⟨j, by omega⟩ ∧
        w.DrawIs chal (Chal.restDraw (Block.restrictDraw (rs ⟨j, by omega⟩).msgs vals draw))

/-- The draw that draws the challenge of round `i` by `chal i`. -/
def challengeDraw (chal : ∀ i, ProbComp (rs i).Chal) : {j k : ℕ} → {h : j + k = n} →
    {s : OracleProtocol} → Rounds rs suf j k h s →
    QueryImpl (challengeSpec oracleSig s) ProbComp
  | _, _, _, _, .done => fun c => (Block.noChallenge suf c).elim
  | _, _, _, _, .round j k h w =>
      Block.lift (rs ⟨j, by omega⟩).msgs (Chal.lift (chal ⟨j, by omega⟩) (w.challengeDraw chal))

/-- The draw `challengeDraw chal` draws the challenge of round `i` by `chal i`. -/
theorem drawIs_challengeDraw (chal : ∀ i, ProbComp (rs i).Chal) :
    ∀ {j k : ℕ} {h : j + k = n} {s : OracleProtocol} (w : Rounds rs suf j k h s),
    w.DrawIs chal (w.challengeDraw chal)
  | _, _, _, _, .done => True.intro
  | _, _, _, _, .round j k h w => fun vals => by
    simp only [challengeDraw, Block.restrictDraw_lift]
    exact ⟨rfl, drawIs_challengeDraw chal w⟩

/-- The state function: run the round updates over the completed rounds of a prefix and ask
whether the current state holds. Messages and incomplete blocks do not change it. -/
def stateFn (step : Step rs S) (good : ∀ i, S i → Prop) : {j k : ℕ} → {h : j + k = n} →
    {s : OracleProtocol} → Rounds rs suf j k h s → Option (S ⟨j, by omega⟩) →
    Block.SpineProp s
  | _, _, _, _, .done, st => fun _ _ => holds good st
  | _, _, _, _, .round j k h w, st =>
      Block.walk (rs ⟨j, by omega⟩).msgs (holds good st) fun vals =>
        Chal.walk (holds good st) fun c =>
          w.stateFn step good (st.bind fun x => step ⟨j, by omega⟩ x vals c)

variable {step : Step rs S} {good : ∀ i, S i → Prop}

/-- At the start of a protocol the state function is the current state. -/
theorem stateFn_root {j k : ℕ} {h : j + k = n} {s : OracleProtocol}
    (w : Rounds rs suf j k h s) (st : Option (S ⟨j, by omega⟩)) :
    w.stateFn step good st (.root s) ⟨⟩ = holds good st := by
  cases w with
  | done => rfl
  | round j k h w => exact Block.walk_root_eq _ fun _ => rfl

/-- One round's flip bound in terms of possibly rejected states. -/
theorem holds_flip_le {chal : ∀ i, ProbComp (rs i).Chal} {ε : Fin n → ℝ≥0∞}
    (hround : RoundSound chal step good ε) (i : Fin n) (st : Option (S i.castSucc))
    (vals : (rs i).msgs.Values) :
    Pr{let c ← chal i}[¬ holds good st ∧
      holds good (st.bind fun x => step i x vals c)] ≤ ε i := by
  cases st with
  | none =>
    rw [prEvent_eq_zero_of_forall_not _ _ fun _ h => h.2]
    exact zero_le
  | some st =>
    by_cases hg : good i.castSucc st
    · rw [prEvent_eq_zero_of_forall_not _ _ fun _ h => h.1 hg]
      exact zero_le
    · refine (prEvent_mono _ _ _ fun c hc => ?_).trans (hround i st vals hg)
      obtain ⟨-, hc⟩ := hc
      simp only [Option.bind_some] at hc
      cases hs : step i st vals c with
      | none => rw [hs] at hc; exact hc.elim
      | some st' => rw [hs] at hc; exact ⟨st', rfl, hc⟩

/-- **The probability bounds, done once.** At every challenge, the state function flips from
false to true with probability at most the error of the challenge's round, and no prover message
flips it. -/
theorem flips {chal : ∀ i, ProbComp (rs i).Chal} {ε : Fin n → ℝ≥0∞}
    (hround : RoundSound chal step good ε) :
    ∀ {j k : ℕ} {h : j + k = n} {s : OracleProtocol} (w : Rounds rs suf j k h s)
      (draw : QueryImpl (challengeSpec oracleSig s) ProbComp), w.DrawIs chal draw →
      ∀ st : Option (S ⟨j, by omega⟩),
      Block.Flips s (w.stateFn step good st) draw (fun c => ε (w.roundOf c))
  | _, _, _, _, .done, draw, _, _ => Block.flips_const _ suf draw _
  | _, _, _, _, .round j k h w, draw, hdraw, st => by
    unfold DrawIs at hdraw
    refine Block.walk_flips_tail _
      (E' := fun c => ε (Chal.onNode ⟨j, by omega⟩ w.roundOf c)) (fun _ hn => hn)
      fun vals => Chal.walk_flips ?_ fun c =>
        flips hround w _ (hdraw vals).2 (st.bind fun x => step ⟨j, by omega⟩ x vals c)
    rw [(hdraw vals).1]
    simp only [stateFn_root]
    let : MeasurableSpace (rs ⟨j, by omega⟩).Chal := ⊤
    rw [← prEvent_eq_evalDist_of_discrete]
    exact holds_flip_le hround ⟨j, by omega⟩ st vals

/-- At a leaf the state function holds when the verdict is an unrejected final state whose claim
holds. -/
theorem leaf : ∀ {j k : ℕ} {h : j + k = n} {s : OracleProtocol}
    (w : Rounds rs suf j k h s) (st : Option (S ⟨j, by omega⟩)),
    Block.LeafOK s (w.stateFn step good st)
      (fun tr => ∃ p, w.verdict step st tr = some p ∧ good (Fin.last n) p.1)
  | _, _, _, _, .done, st => fun _ _ ⟨p, hp, hg⟩ => by
    cases st with
    | none => cases hp
    | some x =>
      obtain rfl := Option.some.inj hp
      exact hg
  | _, _, _, _, .round j k h w, st =>
    Block.walk_leaf _ fun vals => Chal.walk_leaf fun c sp history hG =>
      leaf w _ sp history (by simpa only [verdict, Block.split_join, Chal.split] using hG)

end Rounds

/-! ## The iteration theorem -/

namespace Rounds

variable {pre : Block} {s : OracleProtocol}

/-- The final state and the suffix values of an iteration's transcript, from the initial state
that the prefix values give. -/
def iterVerdict (w : Rounds rs suf 0 n (Nat.zero_add n) s) {Stmt : Type}
    (start : Stmt → pre.Values → Option (S 0)) (step : Stmt → Step rs S) (x : Stmt)
    (tr : Transcript oracleSig (pre.then s)) : Option (S (Fin.last n) × suf.Values) :=
  w.verdict (step x) (start x (Block.split pre tr).1) (Block.split pre tr).2

/-- The round of each challenge node of an iteration. -/
def iterRoundOf (w : Rounds rs suf 0 n (Nat.zero_add n) s)
    (c : ChallengeNode oracleSig (pre.then s)) : Fin n :=
  w.roundOf (Block.tailNode pre c)

/-- **The iteration theorem, round-by-round form.** A protocol `pre.then s`, where `s` is
certified as `n` rounds followed by a suffix, is round-by-round sound with error `ε i` at the
challenge of round `i`, given:

* `hdraw`: the challenge of round `i` is drawn by `chal i`;
* `hroot`: an admissible statement whose initial state holds is in the language;
* `hleaf`: an accepted transcript has an unrejected final state whose claim holds;
* `hround`: the per-round obligation `RoundSound`, for each statement.

None of the hypotheses mentions a spine, a cursor or a partial transcript. -/
theorem rbrSoundness (w : Rounds rs suf 0 n (Nat.zero_add n) s)
    {Stmt : Type} {admissible language : Stmt → Prop}
    {accepts : Stmt → Transcript oracleSig (pre.then s) → Prop}
    (start : Stmt → pre.Values → Option (S 0)) (step : Stmt → Step rs S)
    (good : Stmt → ∀ i, S i → Prop)
    (draw : QueryImpl (challengeSpec oracleSig (pre.then s)) ProbComp)
    (chal : ∀ i, ProbComp (rs i).Chal) (ε : Fin n → ℝ≥0∞)
    (hdraw : ∀ vals, w.DrawIs chal (Block.restrictDraw pre vals draw))
    (hroot : ∀ x vals st, admissible x → start x vals = some st → good x 0 st → language x)
    (hleaf : ∀ x tr, accepts x tr →
      ∃ p, w.iterVerdict start step x tr = some p ∧ good x (Fin.last n) p.1)
    (hround : ∀ x, RoundSound chal (step x) (good x) ε) :
    Interaction.rbrSoundness oracleSig (pre.then s) admissible language accepts draw
      (fun c => ε (w.iterRoundOf c)) := by
  have hstart : ∀ x vals, ¬ (admissible x → language x) →
      ¬ w.stateFn (step x) (good x) (start x vals) (.root s) ⟨⟩ := by
    intro x vals hn hst
    replace hst : holds (good x) (start x vals) := Eq.mp (stateFn_root w _) hst
    cases hs : start x vals with
    | none => rw [hs] at hst; exact hst
    | some st =>
      rw [hs] at hst
      exact hn fun hadm => hroot x vals st hadm hs hst
  have hF : ∀ x, Block.Flips (pre.then s)
      (Block.walk pre (admissible x → language x)
        fun vals => w.stateFn (step x) (good x) (start x vals))
      draw (fun c => ε (w.iterRoundOf c)) := fun x =>
    Block.walk_flips_tail pre (E' := fun c => ε (w.roundOf c)) (hstart x)
      fun vals => flips (hround x) w _ (hdraw vals) _
  refine ⟨{ toFun := fun sp history x => Block.walk pre (admissible x → language x)
              (fun vals => w.stateFn (step x) (good x) (start x vals)) sp history
            root := fun x hadm hroot' => ?_
            send := fun sp history x hown hfalse y => (hF x).send sp history hown hfalse y
            leaf := fun sp history x hfalse hacc => hfalse ?_ }, ?_⟩
  · rcases Block.walk_root pre hroot' with h | ⟨vals, h⟩
    · exact h hadm
    · by_contra hl
      exact hstart x vals (fun h' => hl (h' hadm)) h
  · refine Block.walk_leaf pre (G := fun tr => ∃ p, w.iterVerdict start step x tr = some p ∧
      good x (Fin.last n) p.1) (fun vals sp' history' hG => ?_) sp history (hleaf x _ hacc)
    refine leaf w _ sp' history' ?_
    simpa only [iterVerdict, Block.split_join] using hG
  · intro x _ _ a next sp hrecv history
    exact (hF x).flip sp hrecv history

/-- Along every path, the round errors of the challenges sum to the errors of the rounds from
`j` on. -/
theorem sum_challengeNodesOn (f : Fin n → ℝ≥0∞) : ∀ {j k : ℕ} {h : j + k = n}
    {s : OracleProtocol} (w : Rounds rs suf j k h s) (p : Path s),
    ∑ c ∈ challengeNodesOn oracleSig s p, f (w.roundOf c) =
      ∑ i : Fin n, if j ≤ i.val then f i else 0
  | _, _, _, _, .done, _ => by
    rw [Finset.sum_eq_zero fun c _ => (Block.noChallenge suf c).elim]
    refine (Finset.sum_eq_zero fun i _ => ?_).symm
    have := i.isLt
    exact ite_eq_right_iff.mpr fun h' => absurd h' (by omega)
  | _, _, _, _, .round j k h w, p => by
    refine (Block.sum_challengeNodesOn
      (fun c => f (Chal.onNode ⟨j, by omega⟩ w.roundOf c)) _ p).trans ?_
    generalize Block.tailPath _ p = q
    obtain ⟨⟨⟩, q⟩ := q
    rw [Chal.sum_challengeNodesOn]
    change f ⟨j, by omega⟩ + ∑ c ∈ challengeNodesOn oracleSig _ q, f (w.roundOf c) = _
    rw [sum_challengeNodesOn f w q]
    have hj : j < n := by omega
    have hsplit : ∀ i : Fin n, (if j ≤ i.val then f i else 0) =
        (if (⟨j, hj⟩ : Fin n) = i then f i else 0) + (if j + 1 ≤ i.val then f i else 0) := by
      intro i
      by_cases h1 : i.val = j
      · have h2 : (⟨j, hj⟩ : Fin n) = i := Fin.ext h1.symm
        subst h2
        simp
      · have h2 : (⟨j, hj⟩ : Fin n) ≠ i := fun e => h1 (congrArg Fin.val e).symm
        by_cases h3 : j + 1 ≤ i.val
        · simp [h2, h3, show j ≤ i.val by omega]
        · simp [h2, h3, show ¬ j ≤ i.val by omega]
    rw [Finset.sum_congr rfl fun i _ => hsplit i, Finset.sum_add_distrib, Finset.sum_ite_eq]
    simp

/-- Along every path of an iteration, the round errors of the challenges sum to `∑ i, f i`. -/
theorem sum_iterRoundOf (f : Fin n → ℝ≥0∞) (w : Rounds rs suf 0 n (Nat.zero_add n) s)
    (p : Path (pre.then s)) :
    ∑ c ∈ challengeNodesOn oracleSig (pre.then s) p, f (w.iterRoundOf c) = ∑ i, f i := by
  refine (Block.sum_challengeNodesOn (fun c => f (w.roundOf c)) pre p).trans ?_
  rw [sum_challengeNodesOn f w]
  simp

/-- **The iteration theorem, soundness form.** An oracle verifier on an iteration that is
round-by-round sound with error `ε i` at the challenge of round `i` is sound with error
`∑ i, ε i`, through the existing implication `OracleVerifier.soundness_of_rbrSoundness`. -/
theorem soundness_of_rbrSoundness (w : Rounds rs suf 0 n (Nat.zero_add n) s)
    {ι σ Stmt : Type} {ambient : OracleSpec ι} {T : Path (pre.then s) → Type}
    {inputs : OracleBundle} {outputs : Path (pre.then s) → OracleBundle}
    {V : OracleVerifier ambient (pre.then s) Stmt T inputs outputs}
    {init : ProbComp σ} {impl : QueryImpl ambient (StateT σ ProbComp)}
    {input : StatementProblem (Stmt × inputs.Data)}
    {output : PathProblem (pre.then s) (OracleVerifier.Output T outputs)}
    {draw : QueryImpl (challengeSpec oracleSig (pre.then s)) ProbComp} {ε : Fin n → ℝ≥0∞}
    (h : V.rbrSoundness impl input output draw (fun c => ε (w.iterRoundOf c))) :
    V.soundness init impl draw input output (∑ i, ε i) := fun Out stmt hadm hlang p =>
  (OracleVerifier.soundness_of_rbrSoundness (init := init) h Out stmt hadm hlang p).trans
    (iSup_le fun path => (sum_iterRoundOf ε w path).le)

end Rounds

end Generic

end Specs.Kit

/-! ## Axioms -/

#print axioms Specs.Kit.Rounds.rbrSoundness
#print axioms Specs.Kit.Rounds.soundness_of_rbrSoundness
#print axioms Specs.Kit.Rounds.drawIs_challengeDraw

/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.ProofSystem.Sumcheck.Indexed

/-!
# Prototype: round iteration with a per-round soundness theorem

This prototype is item 1 of the proof kit in the protocol-specs proposal. It has four parts.

1. **The iteration combinator.** A `Round` is one oracle message followed by one challenge. A
   family `rs : Fin n → Round` iterates to the `n`-round protocol `iterate rs`. The certificate
   `Rounds rs j k h s` says that `s` is rounds `j, …, j + k - 1` of `rs`. A protocol that is
   defined by its own recursion, such as sum-check's tree, is an instance by a recursion whose
   cases hold by definition (`scRounds`), so no statement about it needs a cast. The verifier
   state `S i` is indexed by the absolute round number `i : Fin (n + 1)`, and each round's check
   is a query program against that round's oracle message (`Rounds.verifier`).
2. **The iteration theorem** (`Rounds.rbrSoundness`, `Rounds.verifier_rbrSoundness`,
   `Rounds.verifier_soundness`). The author supplies one per-round obligation, `RoundSound`: from
   a state whose claim is false, every message passes the round into a true claim with
   probability at most `ε i` over the round's challenge. The theorem builds the state function
   and proves round-by-round soundness with error `ε i` at the challenge of round `i`, and
   soundness with error `∑ i, ε i`. The recursion over cursor spines and partial transcripts
   happens once, in this file.
3. **The claim-reduction step** (`agreement_le`, `claimReduction_le`) and its sum-check instance
   (`sumcheck_roundSound`).
4. **Sum-check through the kit.** `indexedVerifier_soundness_viaKit` proves the statement of
   `Sumcheck.indexedVerifier_soundness` from the iteration theorem, the round instance of the
   claim-reduction step and one verdict lemma. `kitVerifier_soundness` proves the same bound for
   the verifier that the kit builds from sum-check's round check.

Section 5 proves the per-round obligation once for a second family: polynomial rounds whose
degree bound, and so whose message type and error, change with the round. It is not a FRI
instance. The section "Open problems" at the end lists what is missing.

Check with `lake env lean` from a built ArkLib worktree.
-/

namespace RoundIteration

open scoped ENNReal NNReal
open PFunctor FreeM Interaction Interaction.TwoParty.Lens Interaction.Oracle OracleComp
  OracleSpec MeasureTheory

/-! ## 1. The iteration combinator -/

/-- One round of an iterated protocol: the prover sends an oracle message with a query interface,
then the verifier sends a challenge. -/
structure Round : Type 1 where
  /-- The prover's message. -/
  Msg : Type
  /-- The queries the verifier may ask about the message. -/
  iface : OracleInterface Msg
  /-- The verifier's challenge. -/
  Chal : Type

/-- One round followed by the protocol `rest`. -/
@[reducible]
def Round.then (r : Round) (rest : OracleProtocol) : OracleProtocol :=
  .liftBind (.oracle r.Msg r.iface) fun _ => .liftBind (.challenge r.Chal) fun _ => rest

variable {n : ℕ}

/-- Rounds `j, …, j + k - 1` of the family `rs`, where `j + k = n`. -/
def iterFrom (rs : Fin n → Round) : (j k : ℕ) → j + k = n → OracleProtocol
  | _, 0, _ => .pure PUnit.unit
  | j, k + 1, h => (rs ⟨j, by omega⟩).then (iterFrom rs (j + 1) k (by omega))

/-- The `n`-round protocol of a round family. -/
abbrev iterate (rs : Fin n → Round) : OracleProtocol :=
  iterFrom rs 0 n (Nat.zero_add n)

/-- `Rounds rs j k h s` certifies that `s` is rounds `j, …, j + k - 1` of the family `rs`.

A protocol defined by its own recursion is an instance through a recursion whose cases hold by
definition, so the protocol keeps its own name in every statement. -/
inductive Rounds (rs : Fin n → Round) : (j k : ℕ) → j + k = n → OracleProtocol → Type 1
  | done : Rounds rs n 0 rfl (.pure PUnit.unit)
  | round (j k : ℕ) (h : j + (k + 1) = n) {rest : OracleProtocol} :
      Rounds rs (j + 1) k (by omega) rest →
        Rounds rs j (k + 1) h ((rs ⟨j, by omega⟩).then rest)

/-- The combinator's own protocol is an instance. -/
def Rounds.ofIter (rs : Fin n → Round) : (j k : ℕ) → (h : j + k = n) →
    Rounds rs j k h (iterFrom rs j k h)
  | j, 0, h => by subst h; exact .done
  | j, k + 1, h => .round j k h (Rounds.ofIter rs (j + 1) k (by omega))

/-- The full iteration as a certificate. -/
abbrev Rounds.iterate (rs : Fin n → Round) : Rounds rs 0 n (Nat.zero_add n) (iterate rs) :=
  Rounds.ofIter rs 0 n (Nat.zero_add n)

section Generic

variable {rs : Fin n → Round} {S : Fin (n + 1) → Type}

/-- A pure state update for every round: the state before round `i`, the round's message and
challenge give the state after it, or `none` if the round's check rejects. -/
abbrev Step (rs : Fin n → Round) (S : Fin (n + 1) → Type) : Type :=
  ∀ i : Fin n, S i.castSucc → (rs i).Msg → (rs i).Chal → Option (S i.succ)

/-- A round check as the verifier runs it: a query program against the round's message. -/
abbrev Check (rs : Fin n → Round) (S : Fin (n + 1) → Type) : Type :=
  ∀ i : Fin n, S i.castSucc → (rs i).Chal →
    OptionT (OracleComp (rs i).iface.spec) (S i.succ)

/-- The pure update of a check: its queries answered by the round's message. -/
def Check.step (check : Check rs S) : Step rs S := fun i st msg c =>
  simulateQ (r := Id) (fun q => ((rs i).iface.answer msg q : Id _)) (check i st c).run

/-- A possibly rejected state holds when it was not rejected and its claim is true. -/
def holds (good : ∀ i, S i → Prop) {i : Fin (n + 1)} : Option (S i) → Prop
  | none => False
  | some x => good i x

@[simp] theorem holds_none (good : ∀ i, S i → Prop) {i : Fin (n + 1)} :
    holds good (none : Option (S i)) ↔ False := Iff.rfl

@[simp] theorem holds_some (good : ∀ i, S i → Prop) {i : Fin (n + 1)} (x : S i) :
    holds good (some x) ↔ good i x := Iff.rfl

namespace Rounds

/-- The final state after a completed transcript, or `none` if some round's check rejects. -/
def verdict (step : Step rs S) : {j k : ℕ} → {h : j + k = n} → {s : OracleProtocol} →
    Rounds rs j k h s → S ⟨j, by omega⟩ → Transcript oracleSig s → Option (S (Fin.last n))
  | _, _, _, _, .done, st, _ => some st
  | _, _, _, _, .round j _ _ w, st, tr =>
      (step ⟨j, by omega⟩ st tr.1 tr.2.1).bind fun mid => w.verdict step mid tr.2.2

/-- The round of each challenge node. -/
def roundOf : {j k : ℕ} → {h : j + k = n} → {s : OracleProtocol} →
    Rounds rs j k h s → ChallengeNode oracleSig s → Fin n
  | _, _, _, _, .done, ⟨c, _⟩ => nomatch c
  | _, _, _, _, .round _ _ _ w, ⟨.inr ⟨_, .inr ⟨_, c⟩⟩, hc⟩ => w.roundOf ⟨c, hc⟩
  | _, _, _, _, .round j _ _ _, _ => ⟨j, by omega⟩

/-- The challenge draw at round `i` is `chal i`. -/
def DrawIs (chal : ∀ i, ProbComp (rs i).Chal) : {j k : ℕ} → {h : j + k = n} →
    {s : OracleProtocol} → Rounds rs j k h s → QueryImpl (challengeSpec oracleSig s) ProbComp →
    Prop
  | _, _, _, _, .done, _ => True
  | _, _, _, _, .round j _ _ w, draw =>
      draw ⟨.inr ⟨⟨⟩, .inl ⟨⟩⟩, rfl⟩ = chal ⟨j, by omega⟩ ∧
        w.DrawIs chal (fun c => draw ⟨.inr ⟨⟨⟩, .inr ⟨⟨⟩, c.1⟩⟩, c.2⟩)

/-- The state function: run the round updates over the completed rounds of a prefix and ask
whether the current claim holds. A message alone does not change it. -/
def prefixGood (step : Step rs S) (good : ∀ i, S i → Prop) :
    {j k : ℕ} → {h : j + k = n} → {s : OracleProtocol} → Rounds rs j k h s →
    Option (S ⟨j, by omega⟩) → {t : OracleProtocol} → (sp : Cursor.Spine s t) →
    PartialTranscriptAt oracleSig sp → Prop
  | _, _, _, _, .done, st, _, _, _ => holds good st
  | _, _, _, _, .round j _ _ w, st, _, sp, history => by
      cases sp with
      | root => exact holds good st
      | down b tail =>
        cases tail with
        | root => exact holds good st
        | down b' tail =>
          exact w.prefixGood step good
            (st.bind fun x => step ⟨j, by omega⟩ x history.1.1 history.2.1.1) tail history.2.2

end Rounds

/-- **The per-round obligation.** From a state whose claim is false, every message passes round
`i` into a state whose claim is true with probability at most `ε i` over the round's
challenge. -/
def RoundSound (chal : ∀ i, ProbComp (rs i).Chal) (step : Step rs S)
    (good : ∀ i, S i → Prop) (ε : Fin n → ℝ≥0∞) : Prop :=
  ∀ (i : Fin n) (st : S i.castSucc) (msg : (rs i).Msg), ¬ good i.castSucc st →
    Pr{let c ← chal i}[∃ st', step i st msg c = some st' ∧ good i.succ st'] ≤ ε i

/-! ## 2. The iteration theorem -/

namespace Rounds

variable (step : Step rs S) (good : ∀ i, S i → Prop)

/-- At the start of a protocol the state function is the claim of the current state. -/
theorem prefixGood_root {j k : ℕ} {h : j + k = n} {s : OracleProtocol} (w : Rounds rs j k h s)
    (st : Option (S ⟨j, by omega⟩)) :
    w.prefixGood step good st (.root s) PUnit.unit = holds good st := by
  cases w <;> rfl

/-- A prover message does not change the state function. -/
theorem prefixGood_send : ∀ {j k : ℕ} {h : j + k = n} {s : OracleProtocol}
    (w : Rounds rs j k h s) (st : Option (S ⟨j, by omega⟩)) {a : OraclePos}
    {next : OraclePoly.B a → OracleProtocol} (sp : Cursor.Spine s (.liftBind a next))
    (history : PartialTranscriptAt oracleSig sp), owner oracleSig a = .sender →
    ∀ x : Move oracleSig a,
    w.prefixGood step good st (sp.comp (.down (oracleSig.toFunB a x) (.root _)))
      (PartialTranscriptAt.snoc oracleSig sp history x) =
      w.prefixGood step good st sp history
  | _, _, _, _, .done, _, _, _, sp, _, _, _ => by cases sp
  | _, _, _, _, .round j k h w, st, _, _, sp, history, hown, x => by
    cases sp with
    | root => rfl
    | down b tail =>
      cases tail with
      | root => cases hown
      | down b' tail =>
        obtain ⟨⟨y, hy⟩, ⟨⟨z, hz⟩, rest⟩⟩ := history
        exact prefixGood_send w (st.bind fun u => step ⟨j, by omega⟩ u y z) tail rest hown x

/-- At a leaf the state function is the claim of the verdict's final state. -/
theorem prefixGood_leaf : ∀ {j k : ℕ} {h : j + k = n} {s : OracleProtocol}
    (w : Rounds rs j k h s) (st : Option (S ⟨j, by omega⟩))
    (sp : Cursor.Spine s (.pure PUnit.unit)) (history : PartialTranscriptAt oracleSig sp),
    w.prefixGood step good st sp history ↔
      holds good (st.bind fun x =>
        w.verdict step x (PartialTranscriptAt.complete oracleSig sp history))
  | _, _, _, _, .done, st, sp, _ => by
    cases sp
    cases st <;> exact Iff.rfl
  | _, _, _, _, .round j k h w, st, sp, history => by
    cases sp with
    | down b tail =>
      cases tail with
      | down b' tail =>
        refine (prefixGood_leaf w _ tail history.2.2).trans ?_
        rw [Option.bind_assoc]
        exact Iff.rfl

variable {step good}

/-- One round's flip bound in terms of possibly rejected states. -/
theorem holds_flip_le {chal : ∀ i, ProbComp (rs i).Chal} {ε : Fin n → ℝ≥0∞}
    (hround : RoundSound chal step good ε) (i : Fin n) (st : Option (S i.castSucc))
    (msg : (rs i).Msg) :
    Pr{let c ← chal i}[¬ holds good st ∧
      holds good (st.bind fun x => step i x msg c)] ≤ ε i := by
  cases st with
  | none =>
    simp only [holds_none, not_false_eq_true, Option.bind_none, true_and]
    rw [prEvent_eq_zero_of_forall_not _ _ fun _ h => h]
    exact zero_le
  | some st =>
    by_cases hg : good i.castSucc st
    · rw [prEvent_eq_zero_of_forall_not _ _ fun _ h => h.1 hg]
      exact zero_le
    · refine (prEvent_mono _ _ _ fun c hc => ?_).trans (hround i st msg hg)
      obtain ⟨-, hc⟩ := hc
      simp only [Option.bind_some] at hc
      cases hs : step i st msg c with
      | none => rw [hs] at hc; exact hc.elim
      | some st' => rw [hs] at hc; exact ⟨st', rfl, hc⟩

/-- **The spine recursion, done once.** At every challenge prefix, the challenge turns a false
state function true with probability at most the error of the challenge's round. -/
theorem prefixGood_flip_le {chal : ∀ i, ProbComp (rs i).Chal} {ε : Fin n → ℝ≥0∞}
    (hround : RoundSound chal step good ε) :
    ∀ {j k : ℕ} {h : j + k = n} {s : OracleProtocol} (w : Rounds rs j k h s)
      (draw : QueryImpl (challengeSpec oracleSig s) ProbComp), w.DrawIs chal draw →
      ∀ (st : Option (S ⟨j, by omega⟩)) {a : OraclePos} {next : OraclePoly.B a → OracleProtocol}
      (sp : Cursor.Spine s (.liftBind a next)) (hrecv : owner oracleSig a = .receiver)
      (history : PartialTranscriptAt oracleSig sp),
      letI : MeasurableSpace (Move oracleSig a) := ⊤
      𝒟[sampleAt oracleSig draw sp hrecv]
        {x | ¬ w.prefixGood step good st sp history ∧
          w.prefixGood step good st (sp.comp (.down (oracleSig.toFunB a x) (.root _)))
            (PartialTranscriptAt.snoc oracleSig sp history x)} ≤
        ε (w.roundOf (spineChallenge oracleSig sp hrecv))
  | _, _, _, _, .done, _, _, _, _, _, sp, _, _ => by cases sp
  | _, _, _, _, .round j k h w, draw, hdraw, st, _, _, sp, hrecv, history => by
    cases sp with
    | root => cases hrecv
    | down b tail =>
      cases b
      cases tail with
      | root =>
        have hs : sampleAt oracleSig draw (.down ⟨⟩ (.root _)) hrecv =
            draw ⟨.inr ⟨⟨⟩, .inl ⟨⟩⟩, rfl⟩ := LawfulFunctor.id_map _
        rw [hs, hdraw.1]
        let : MeasurableSpace (Move oracleSig (.challenge (rs ⟨j, by omega⟩).Chal)) := ⊤
        rw [← prEvent_eq_evalDist_of_discrete]
        obtain ⟨⟨y, hy⟩, ⟨⟩⟩ := history
        change Pr{let x ← chal ⟨j, by omega⟩}[¬ holds good st ∧
          w.prefixGood step good (st.bind fun u => step ⟨j, by omega⟩ u y x)
            (.root _) PUnit.unit] ≤ ε ⟨j, by omega⟩
        simp only [prefixGood_root]
        exact holds_flip_le hround ⟨j, by omega⟩ st y
      | down b' tail =>
        cases b'
        obtain ⟨⟨y, hy⟩, ⟨⟨z, hz⟩, rest⟩⟩ := history
        exact prefixGood_flip_le hround w _ hdraw.2
          (st.bind fun u => step ⟨j, by omega⟩ u y z) tail hrecv rest

/-- **The iteration theorem, round-by-round form.** A protocol certified as `n` rounds is
round-by-round sound with error `ε i` at the challenge of round `i`, given:

* `hdraw`: the challenge of round `i` is drawn by `chal i`;
* `hroot`: an admissible statement whose initial claim holds is in the language;
* `hleaf`: an accepted transcript has an unrejected final state whose claim holds;
* `hround`: the per-round obligation `RoundSound`, for each statement.

None of the hypotheses mentions a spine, a cursor or a partial transcript. -/
theorem rbrSoundness {s : OracleProtocol} (w : Rounds rs 0 n (Nat.zero_add n) s)
    {Stmt : Type} {admissible language : Stmt → Prop}
    {accepts : Stmt → Transcript oracleSig s → Prop}
    (step : Step rs S) (init : Stmt → S 0) (good : Stmt → ∀ i, S i → Prop)
    (draw : QueryImpl (challengeSpec oracleSig s) ProbComp) (chal : ∀ i, ProbComp (rs i).Chal)
    (ε : Fin n → ℝ≥0∞) (hdraw : w.DrawIs chal draw)
    (hroot : ∀ x, admissible x → good x 0 (init x) → language x)
    (hleaf : ∀ x tr, accepts x tr →
      ∃ t, w.verdict step (init x) tr = some t ∧ good x (Fin.last n) t)
    (hround : ∀ x, RoundSound chal step (good x) ε) :
    Interaction.rbrSoundness oracleSig s admissible language accepts draw
      (fun c => ε (w.roundOf c)) := by
  refine ⟨{ toFun := fun sp history x => w.prefixGood step (good x) (some (init x)) sp history
            root := fun x hadm hg => hroot x hadm (by
              rw [prefixGood_root] at hg
              exact hg)
            send := fun sp history x hown hfalse y => by
              rwa [prefixGood_send _ _ w _ sp history hown y]
            leaf := fun sp history x hfalse hacc => hfalse (by
              rw [prefixGood_leaf]
              obtain ⟨t, ht, hg⟩ := hleaf x _ hacc
              change holds (good x) (w.verdict step (init x) _)
              rw [ht]
              exact hg) }, ?_⟩
  intro x _ _ a next sp hrecv history
  exact prefixGood_flip_le (hround x) w draw hdraw _ sp hrecv history

/-- The challenge nodes along a path through one more round. -/
theorem sum_challengeNodesOn_then (r : Round) (rest : OracleProtocol) (p : Path rest)
    (g : ChallengeNode oracleSig (r.then rest) → ℝ≥0∞) :
    ∑ c ∈ challengeNodesOn oracleSig (r.then rest) ⟨⟨⟩, ⟨⟨⟩, p⟩⟩, g c =
      g ⟨.inr ⟨⟨⟩, .inl ⟨⟩⟩, rfl⟩ +
        ∑ c ∈ challengeNodesOn oracleSig rest p, g ⟨.inr ⟨⟨⟩, .inr ⟨⟨⟩, c.1⟩⟩, c.2⟩ := by
  simp only [challengeNodesOn, owner, oracleSig]
  refine (Finset.sum_map _ _ _).trans ?_
  refine (Finset.sum_cons _).trans ?_
  exact congrArg _ (Finset.sum_map _ _ _)

/-- Along every path, the round errors of the challenges sum to the errors of the rounds from
`j` on. -/
theorem sum_challengeNodesOn (f : Fin n → ℝ≥0∞) : ∀ {j k : ℕ} {h : j + k = n}
    {s : OracleProtocol} (w : Rounds rs j k h s) (p : Path s),
    ∑ c ∈ challengeNodesOn oracleSig s p, f (w.roundOf c) =
      ∑ i : Fin n, if j ≤ i.val then f i else 0
  | _, _, _, _, .done, _ => by
    simp only [challengeNodesOn, Finset.sum_empty]
    refine (Finset.sum_eq_zero fun i _ => ?_).symm
    have := i.isLt
    exact ite_eq_right_iff.mpr fun h' => absurd h' (by omega)
  | _, _, _, _, .round j k h w, ⟨⟨⟩, ⟨⟨⟩, p⟩⟩ => by
    rw [sum_challengeNodesOn_then]
    change f ⟨j, by omega⟩ + ∑ c ∈ challengeNodesOn oracleSig _ p, f (w.roundOf c) = _
    rw [sum_challengeNodesOn f w p]
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

/-- **From round errors to soundness.** An oracle verifier on an `n`-round protocol that is
round-by-round sound with error `ε i` at the challenge of round `i` is sound with error
`∑ i, ε i`, through the existing implication `OracleVerifier.soundness_of_rbrSoundness`. -/
theorem soundness_of_rbrSoundness {s : OracleProtocol} (w : Rounds rs 0 n (Nat.zero_add n) s)
    {ι σ Stmt : Type} {ambient : OracleSpec ι} {T : Path s → Type} {inputs : OracleBundle}
    {outputs : Path s → OracleBundle} {V : OracleVerifier ambient s Stmt T inputs outputs}
    {init : ProbComp σ} {impl : QueryImpl ambient (StateT σ ProbComp)}
    {input : StatementProblem (Stmt × inputs.Data)}
    {output : PathProblem s (OracleVerifier.Output T outputs)}
    {draw : QueryImpl (challengeSpec oracleSig s) ProbComp} {ε : Fin n → ℝ≥0∞}
    (h : V.rbrSoundness impl input output draw (fun c => ε (w.roundOf c))) :
    V.soundness init impl draw input output (∑ i, ε i) := fun Out stmt hadm hlang p =>
  (OracleVerifier.soundness_of_rbrSoundness (init := init) h Out stmt hadm hlang p).trans
    (iSup_le fun path => by simp [sum_challengeNodesOn ε w path])

end Rounds

/-! ### The passive verifier of an iteration -/

namespace Rounds

variable (check : Check rs S)

/-- A query to the first oracle message of `r.then rest`. -/
def headQuery (r : Round) {rest : OracleProtocol} : (p : Path (r.then rest)) →
    QueryImpl r.iface.spec (OracleComp (oracleMessageSpec (r.then rest) p))
  | ⟨⟨⟩, ⟨⟨⟩, p⟩⟩ => fun q => liftM ((oracleMessageSpec (r.then rest) ⟨⟨⟩, ⟨⟨⟩, p⟩⟩).query (.inl q))

/-- The path of the rounds after the first. -/
def tailPath (r : Round) {rest : OracleProtocol} : Path (r.then rest) → Path rest
  | ⟨⟨⟩, ⟨⟨⟩, p⟩⟩ => p

/-- A query to the oracle messages of the rounds after the first. -/
def tailLift (r : Round) {rest : OracleProtocol} : (p : Path (r.then rest)) →
    QueryImpl (oracleMessageSpec rest (tailPath r p))
      (OracleComp (oracleMessageSpec (r.then rest) p))
  | ⟨⟨⟩, ⟨⟨⟩, p⟩⟩ => fun q => liftM ((oracleMessageSpec (r.then rest) ⟨⟨⟩, ⟨⟨⟩, p⟩⟩).query (.inr q))

/-- The verifier view of the rounds after the first. -/
def tailView (r : Round) {rest : OracleProtocol} {p : Path (r.then rest)}
    (v : View (r.then rest) p) : View rest (tailPath r p) :=
  ⟨v.1.2.2, congrArg (tailPath r) v.2⟩

/-- Answering lifted queries of the remaining rounds uses exactly their oracle messages. -/
theorem simulate_tail (r : Round) {rest : OracleProtocol} (msg : r.Msg) (c : r.Chal)
    (tr : Transcript oracleSig rest) {α : Type}
    (prog : OracleComp (oracleMessageSpec rest tr.path) α) :
    simulateQ (oracleMessageImpl (r.then rest) ⟨msg, c, tr⟩)
      (simulateQ (tailLift r (Transcript.path (l := oracleSig) (s := r.then rest) ⟨msg, c, tr⟩))
        prog) = simulateQ (oracleMessageImpl rest tr) prog :=
  QueryImpl.simulateQ_simulateQ_eq_of_apply (fun _ => rfl) prog

/-- The final decision: run each round's check against that round's oracle message, in order,
after the interaction. A rejection skips the remaining checks. -/
def decision : {j k : ℕ} → {h : j + k = n} → {s : OracleProtocol} → Rounds rs j k h s →
    S ⟨j, by omega⟩ → (p : Path s) → View s p →
    OracleComp (oracleMessageSpec s p) (Option (S (Fin.last n)))
  | _, _, _, _, .done, st, _, _ => pure (some st)
  | _, _, _, _, .round j _ _ w, st, p, v =>
      simulateQ (headQuery _ p) (check ⟨j, by omega⟩ st v.1.2.1).run >>= fun res =>
        res.elim (pure none) fun mid =>
          simulateQ (tailLift _ p) (w.decision mid (tailPath _ p) (tailView _ v))

/-- Answering the decision's queries from a transcript computes the verdict of the checks' pure
updates. -/
theorem simulate_decision : ∀ {j k : ℕ} {h : j + k = n} {s : OracleProtocol}
    (w : Rounds rs j k h s) (st : S ⟨j, by omega⟩) (tr : Transcript oracleSig s),
    simulateQ (oracleMessageImpl s tr) (w.decision check st tr.path (toView s tr)) =
      w.verdict check.step st tr
  | _, _, _, _, .done, _, _ => rfl
  | _, _, _, _, .round j k h w, st, ⟨msg, c, tr⟩ => by
    change simulateQ _ (simulateQ _ (check ⟨j, by omega⟩ st c).run >>= _) = _
    rw [simulateQ_bind]
    have hh : simulateQ (oracleMessageImpl ((rs ⟨j, by omega⟩).then _) ⟨msg, c, tr⟩)
        (simulateQ (headQuery _ (Transcript.path (l := oracleSig)
          (s := (rs ⟨j, by omega⟩).then _) ⟨msg, c, tr⟩))
          (check ⟨j, by omega⟩ st c).run) = check.step ⟨j, by omega⟩ st msg c :=
      QueryImpl.simulateQ_simulateQ_eq_of_apply (fun _ => rfl) _
    rw [hh]
    cases hs : check.step ⟨j, by omega⟩ st msg c with
    | none =>
      change _ = Option.bind (check.step ⟨j, by omega⟩ st msg c) _
      rw [hs]
      rfl
    | some mid =>
      refine (simulate_tail (rs ⟨j, by omega⟩) msg c tr
        (w.decision check mid (Transcript.path tr) (toView _ tr))).trans ?_
      rw [simulate_decision w mid tr]
      change _ = Option.bind (check.step ⟨j, by omega⟩ st msg c) _
      rw [hs]
      rfl

variable {ι : Type} (ambient : OracleSpec ι) (inputs : OracleBundle) {Stmt T : Type}
  (init : Stmt → S 0) (finish : S (Fin.last n) → T)

/-- **The iterated passive verifier.** It runs the round checks from the initial state of the
input statement, maps the final state to the output statement and keeps the input oracle. -/
def verifier {s : OracleProtocol} (w : Rounds rs 0 n (Nat.zero_add n) s) :
    OracleVerifier ambient s Stmt (fun _ => T) inputs (fun _ => inputs) where
  decide stmt p v := OptionT.mk (simulateQ (pathLift ambient inputs p)
    (Option.map finish <$> w.decision check (init stmt) p v))
  outputMap _ _ _ := OracleMap.fst _ _

/-- With its queries answered, the iterated verifier's decision is the verdict. -/
theorem simulate_verifier {s : OracleProtocol} (w : Rounds rs 0 n (Nat.zero_add n) s)
    {m : Type → Type} [Monad m] [LawfulMonad m] (impl : QueryImpl ambient m) (stmt : Stmt)
    (data : inputs.Data) (tr : Transcript oracleSig s) :
    simulateQ (QueryImpl.addLift impl
      ((pathBundle inputs s tr.path).answer (data, oracleMessages s tr)))
      ((w.verifier check ambient inputs init finish).decide stmt _ (toView s tr)).run =
      (pure ((w.verdict check.step (init stmt) tr).map finish) : m _) := by
  change simulateQ _ (simulateQ (pathLift ambient inputs _) _) = _
  rw [simulateQ_pathLift]
  congr 1
  rw [simulateQ_map]
  exact congrArg (Option.map finish) (simulate_decision check w (init stmt) tr)

/-- Valid acceptance by the iterated verifier means an unrejected final state whose output is in
the event. -/
theorem verifier_validAcceptance {s : OracleProtocol} (w : Rounds rs 0 n (Nat.zero_add n) s)
    {σ : Type} (impl : QueryImpl ambient (StateT σ ProbComp)) (x : Stmt × inputs.Data)
    (tr : Transcript oracleSig s) (event : T × inputs.Data → Prop) :
    (w.verifier check ambient inputs init finish).validAcceptance impl x tr event →
      ∃ t, w.verdict check.step (init x.1) tr = some t ∧ event (finish t, x.2) := by
  unfold OracleVerifier.validAcceptance
  dsimp only
  rw [simulate_verifier]
  intro h
  obtain ⟨state, hs⟩ := h
  classical
  by_contra hf
  cases hv : w.verdict check.step (init x.1) tr with
  | none => simp [hv] at hs
  | some t =>
    have hne : ¬ event (finish t, x.2) := fun he => hf ⟨t, hv, he⟩
    simp [hv, verifier, OracleMap.fst, hne] at hs

/-- **The iteration theorem for the iterated verifier.** Besides the per-round obligation, the
author proves that each check's queries compute the pure update (`hcheck`), the root law
(`hroot`) and that an accepted output claim is the final round's claim (`hfinish`). -/
theorem verifier_rbrSoundness {s : OracleProtocol} (w : Rounds rs 0 n (Nat.zero_add n) s)
    {σ : Type} (impl : QueryImpl ambient (StateT σ ProbComp))
    (input : StatementProblem (Stmt × inputs.Data))
    (output : PathProblem s (fun _ => T × inputs.Data))
    (step : Step rs S) (good : Stmt × inputs.Data → ∀ i, S i → Prop)
    (draw : QueryImpl (challengeSpec oracleSig s) ProbComp) (chal : ∀ i, ProbComp (rs i).Chal)
    (ε : Fin n → ℝ≥0∞) (hdraw : w.DrawIs chal draw)
    (hcheck : ∀ i st msg c, check.step i st msg c = step i st msg c)
    (hroot : ∀ x, input.admissible () x → good x 0 (init x.1) → input.language () x)
    (hfinish : ∀ x p t, output.language p (finish t, x.2) → good x (Fin.last n) t)
    (hround : ∀ x, RoundSound chal step (good x) ε) :
    (w.verifier check ambient inputs init finish).rbrSoundness impl input output draw
      (fun c => ε (w.roundOf c)) := by
  obtain rfl : check.step = step := funext fun i => funext fun st => funext fun msg =>
    funext fun c => hcheck i st msg c
  refine w.rbrSoundness check.step (fun x => init x.1) good draw chal ε hdraw hroot
    (fun x tr hacc => ?_) hround
  obtain ⟨t, ht, hl⟩ := verifier_validAcceptance check ambient inputs init finish w impl x tr _ hacc
  exact ⟨t, ht, hfinish x _ t hl⟩

/-- **The iteration theorem, soundness form.** The iterated verifier is sound with error
`∑ i, ε i`, through the existing implication `OracleVerifier.soundness_of_rbrSoundness`. -/
theorem verifier_soundness {s : OracleProtocol} (w : Rounds rs 0 n (Nat.zero_add n) s)
    {σ : Type} (initState : ProbComp σ) (impl : QueryImpl ambient (StateT σ ProbComp))
    (input : StatementProblem (Stmt × inputs.Data))
    (output : PathProblem s (fun _ => T × inputs.Data))
    (step : Step rs S) (good : Stmt × inputs.Data → ∀ i, S i → Prop)
    (draw : QueryImpl (challengeSpec oracleSig s) ProbComp) (chal : ∀ i, ProbComp (rs i).Chal)
    (ε : Fin n → ℝ≥0∞) (hdraw : w.DrawIs chal draw)
    (hcheck : ∀ i st msg c, check.step i st msg c = step i st msg c)
    (hroot : ∀ x, input.admissible () x → good x 0 (init x.1) → input.language () x)
    (hfinish : ∀ x p t, output.language p (finish t, x.2) → good x (Fin.last n) t)
    (hround : ∀ x, RoundSound chal step (good x) ε) :
    (w.verifier check ambient inputs init finish).soundness initState impl draw input output
      (∑ i, ε i) :=
  w.soundness_of_rbrSoundness
    (verifier_rbrSoundness check ambient inputs init finish w impl input output step good draw
      chal ε hdraw hcheck hroot hfinish hround)

end Rounds

end Generic

/-! ## 3. The claim-reduction step -/

section ClaimReduction

open Polynomial

variable {R : Type} [CommSemiring R] [IsDomain R] [Fintype R] [SampleableType R] {d : ℕ}

/-- **Polynomial agreement.** A degree-`≤ d` message `g` that differs from a claimed honest
polynomial `h` at some point agrees with it at a uniform challenge with probability at most
`d / |R|`. The hypothesis is pointwise because over a finite semiring two distinct polynomials
can agree everywhere; over a field `agreement_le_field` takes `g ≠ h`. -/
theorem agreement_le (g h : R⦃≤ d⦄[X]) (hne : ∃ a, g.val.eval a ≠ h.val.eval a) :
    Pr{let r ← $ᵗ R}[g.val.eval r = h.val.eval r] ≤
      (((d : ℝ≥0) / Fintype.card R : ℝ≥0) : ℝ≥0∞) := by
  obtain ⟨a, ha⟩ := hne
  exact Probability.prob_agreement_of_sum_ne {a} g h (by simpa using ha)

/-- Polynomial agreement over a field: distinct degree-`≤ d` polynomials agree at a uniform
challenge with probability at most `d / |R|`. -/
theorem agreement_le_field {F : Type} [Field F] [Fintype F] [SampleableType F]
    (g h : F⦃≤ d⦄[X]) (hne : g ≠ h) :
    Pr{let r ← $ᵗ F}[g.val.eval r = h.val.eval r] ≤
      (((d : ℝ≥0) / Fintype.card F : ℝ≥0) : ℝ≥0∞) :=
  Probability.prob_degreeLE_eval_eq_le hne

/-- **The claim-reduction step.** Suppose a round reduces the input claim `claimIn` to the output
claim `claimOut r` at the challenge `r`, with message `g` and honest polynomial `h`, such that

* `hhonest`: if the check passes and the input claim is false, then `g` differs from `h` at some
  point;
* `hout`: if the check passes, a true output claim at `r` means `g` and `h` agree at `r`.

Then from a false input claim, the check passes and the output claim is true with probability
at most `d / |R|`. -/
theorem claimReduction_le (claimIn check : Prop) (claimOut : R → Prop) (g h : R⦃≤ d⦄[X])
    (hhonest : check → ¬ claimIn → ∃ a, g.val.eval a ≠ h.val.eval a)
    (hout : ∀ r, check → claimOut r → g.val.eval r = h.val.eval r) (hfalse : ¬ claimIn) :
    Pr{let r ← $ᵗ R}[check ∧ claimOut r] ≤ (((d : ℝ≥0) / Fintype.card R : ℝ≥0) : ℝ≥0∞) := by
  by_cases hc : check
  · exact (prEvent_mono _ _ _ fun r hr => hout r hc hr.2).trans
      (agreement_le g h (hhonest hc hfalse))
  · rw [prEvent_eq_zero_of_forall_not _ _ fun _ hr => hc hr.1]
    exact zero_le

end ClaimReduction

/-! ## 4. Sum-check through the kit -/

section Sumcheck

open Sumcheck Polynomial MvPolynomial

variable (R : Type) [CommSemiring R] (deg : ℕ)

/-- One sum-check round: the round polynomial as an evaluation oracle, then a ring challenge. -/
@[reducible]
def scRound : Round :=
  ⟨R⦃≤ deg⦄[X], Interpreted.messageInterface (fun (q : R⦃≤ deg⦄[X]) r => q.val.eval r), R⟩

/-- **Sum-check's existing tree is an instance.** Each case holds by definition of
`Sumcheck.protocol`. -/
def scRounds : (k j : ℕ) → (h : j + k = n) →
    Rounds (fun _ : Fin n => scRound R deg) j k h (protocol R deg k)
  | 0, j, h => by subst h; exact .done
  | k + 1, j, h => .round j k h (scRounds k (j + 1) (by omega))

/-- The combinator's protocol is sum-check's tree. -/
theorem iterFrom_scRound : ∀ (k j : ℕ) (h : j + k = n),
    iterFrom (fun _ : Fin n => scRound R deg) j k h = protocol R deg k
  | 0, _, _ => rfl
  | k + 1, j, h => by
    rw [iterFrom, iterFrom_scRound k (j + 1) (by omega)]

variable {R deg} [DecidableEq R] {d : ℕ} (D : Fin d → R)

/-- The sum-check round update: check the indexed sum of the message, then move the claim to the
message's value at the challenge. -/
noncomputable def scStep : Step (fun _ : Fin n => scRound R deg) (RoundStatement R n) :=
  fun i (st : RoundStatement R n i.castSucc) (msg : R⦃≤ deg⦄[X]) (r : R) =>
    if (∑ a, msg.val.eval (D a)) = st.target then
      some ⟨msg.val.eval r, Fin.snoc st.challenges r⟩ else none

/-- The sum-check round check as queries to the round polynomial. -/
def scCheck : Check (fun _ : Fin n => scRound R deg) (RoundStatement R n) :=
  fun i (st : RoundStatement R n i.castSucc) (r : R) => OptionT.mk do
    let values ← (List.finRange d).mapM fun a => liftM ((R →ₒ R).query (D a))
    if values.sum = st.target then
      let value ← liftM ((R →ₒ R).query r)
      return some ⟨value, Fin.snoc st.challenges r⟩
    else return none

/-- The check's queries compute the round update. -/
theorem scCheck_step (i : Fin n) (st : RoundStatement R n i.castSucc) (msg : R⦃≤ deg⦄[X])
    (r : R) : (scCheck (deg := deg) D).step i st msg r = scStep D i st msg r := by
  unfold Check.step scCheck scStep
  change simulateQ _ ((List.finRange d).mapM (fun a => liftM ((R →ₒ R).query (D a))) >>= _) = _
  simp only [simulateQ_bind, simulateQ_list_mapM]
  change ((List.finRange d).mapM (fun a => (pure (msg.val.eval (D a)) : Id R)) >>= _) = _
  simp only [List.mapM_pure, LawfulMonad.pure_bind]
  rw [← List.ofFn_eq_map, List.sum_ofFn]
  split <;> rfl

/-- **The sum-check round instance of the claim-reduction step.** If the round's input claim is
false, the check passes and the output claim is true with probability at most `deg / |R|`. -/
theorem sumcheck_roundSound [IsDomain R] [Fintype R] [SampleableType R]
    (p : R⦃≤ deg⦄[X Fin n]) :
    RoundSound (fun _ => $ᵗ R) (scStep (deg := deg) D) (fun i st => indexedRelation D i st p)
      (fun _ => (((deg : ℝ≥0) / Fintype.card R : ℝ≥0) : ℝ≥0∞)) := by
  intro i st msg hfalse
  have hevent : (fun r => ∃ st', scStep D i st msg r = some st' ∧ indexedRelation D i.succ st' p) =
      (fun r => (∑ a, msg.val.eval (D a)) = st.target ∧
        indexedRelation D i.succ ⟨msg.val.eval r, Fin.snoc st.challenges r⟩ p) := by
    funext r
    by_cases hs : (∑ a, msg.val.eval (D a)) = st.target <;> simp [scStep, hs]
  simp only [hevent]
  let honest := projectedRoundPolynomial D i st.challenges p
  refine claimReduction_le _ _ _ msg honest (fun hs hf => ?_) (fun r _ hr => ?_) hfalse
  · by_contra! h
    exact hf (((sum_projectedRoundPolynomial D i st.challenges p).symm.trans
      (Finset.sum_congr rfl fun a _ => (h (D a)).symm)).trans hs)
  · exact hr.symm.trans (roundSum_succ D i st.challenges p r)

omit [DecidableEq R] in
/-- The challenge draw of sum-check's tree is uniform in every round. -/
theorem scDrawIs [SampleableType R] : ∀ (k j : ℕ) (h : j + k = n),
    (scRounds R deg k j h).DrawIs (fun _ => $ᵗ R) (indexedDraw (R := R) (deg := deg) k)
  | 0, j, h => by subst h; exact True.intro
  | k + 1, j, h => And.intro rfl (scDrawIs k (j + 1) (by omega))

variable (R deg) in
/-- **Sum-check's verifier, built by the kit.** It has the type of
`Sumcheck.indexedVerifier`. -/
noncomputable def kitVerifier {ι : Type} (ambient : OracleSpec ι) :
    OracleVerifier ambient (protocol R deg n) (RoundStatement R n 0)
      (fun _ => RoundStatement R n (Fin.last n)) (polynomialFamily R n deg)
      (fun _ => polynomialFamily R n deg) :=
  (scRounds R deg n 0 (Nat.zero_add n)).verifier (scCheck D) ambient _ id id

/-- **Sum-check soundness through the kit**: the statement of
`Sumcheck.indexedVerifier_soundness` for the kit-built verifier. The proof uses only the
iteration theorem, the round instance of the claim-reduction step and the round's own algebra. -/
theorem kitVerifier_soundness [IsDomain R] [Fintype R] [SampleableType R]
    {ι σ : Type} (ambient : OracleSpec ι) (init : ProbComp σ)
    (impl : QueryImpl ambient (StateT σ ProbComp)) :
    (kitVerifier R deg D ambient (n := n)).soundness init impl
      (indexedDraw (R := R) (deg := deg) n)
      (indexedInputProblem D) (indexedOutputProblem (R := R) (deg := deg) (n := n))
      ((n : ℝ≥0∞) * (((deg : ℝ≥0) / Fintype.card R : ℝ≥0) : ℝ≥0∞)) := by
  have h := Rounds.verifier_soundness (scCheck D) ambient (polynomialFamily R n deg) id id
    (scRounds R deg n 0 (Nat.zero_add n)) init impl
    (indexedInputProblem D) (indexedOutputProblem (R := R) (deg := deg) (n := n)) (scStep D)
    (fun x i st => indexedRelation D i st (x.2 ())) _ (fun _ => $ᵗ R) _
    (scDrawIs n 0 (Nat.zero_add n)) (scCheck_step D)
    (fun x _ h => ⟨(), h⟩) (fun x _ t ⟨_, h⟩ => (indexedRelation_last D t (x.2 ())).mpr h)
    (fun x => sumcheck_roundSound D (x.2 ()))
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h
  exact h

/-! ### The same theorem for today's verifier

The kit also proves `Sumcheck.indexedVerifier_soundness` itself. The only new fact is that the
kit's round update, iterated over sum-check's tree, computes today's verdict. -/

/-- The kit's verdict is `Sumcheck.indexedVerdict`. -/
theorem scVerdict_eq : ∀ (k j : ℕ) (h : j + k = n) (st : RoundStatement R n ⟨j, by omega⟩)
    (tr : Transcript oracleSig (protocol R deg k)),
    (scRounds R deg k j h).verdict (scStep D) st tr =
      indexedVerdict D k (some ⟨⟨j, by omega⟩, by simpa using h, st⟩) tr
  | 0, j, h, st, tr => by subst h; rfl
  | k + 1, j, h, st, ⟨msg, r, tail⟩ => by
    rw [indexedVerdict_succ]
    change (scStep D ⟨j, by omega⟩ st msg r).bind
      (fun mid => (scRounds R deg k (j + 1) (by omega)).verdict (scStep D) mid tail) = _
    unfold scStep indexedNext
    simp only [Interpreted.message, Interpreted.challenge, Interpreted.tail, Option.bind_some]
    by_cases hs : (∑ a, msg.val.eval (D a)) = st.target
    · simp only [hs, ↓reduceIte, Option.bind_some]
      exact scVerdict_eq k (j + 1) (by omega) ⟨msg.val.eval r, Fin.snoc st.challenges r⟩ tail
    · simp only [hs, ↓reduceIte, Option.bind_none, indexedVerdict_none]

/-- Round-by-round soundness of today's `Sumcheck.indexedVerifier`, from the kit. -/
theorem indexedVerifier_rbrSoundness_viaKit [IsDomain R] [Fintype R] [SampleableType R]
    {ι σ : Type} (ambient : OracleSpec ι) (impl : QueryImpl ambient (StateT σ ProbComp)) :
    (indexedVerifier R deg n D ambient).rbrSoundness impl
      (indexedInputProblem D) (indexedOutputProblem (R := R) (deg := deg) (n := n))
      (indexedDraw (R := R) (deg := deg) n)
      (fun c => (fun _ => (((deg : ℝ≥0) / Fintype.card R : ℝ≥0) : ℝ≥0∞))
        ((scRounds R deg n 0 (Nat.zero_add n)).roundOf c)) := by
  refine (scRounds R deg n 0 (Nat.zero_add n)).rbrSoundness (S := RoundStatement R n)
    (Stmt := RoundStatement R n 0 × (∀ i, PolynomialData R n deg i))
    (admissible := (indexedInputProblem D).admissible ())
    (language := (indexedInputProblem D).language ())
    (accepts := fun stmt tr => (indexedVerifier R deg n D ambient).validAcceptance impl stmt tr
      ((indexedOutputProblem (R := R) (deg := deg) (n := n)).language tr.path))
    (scStep D) (fun x => x.1) (fun x i st => indexedRelation D i st (x.2 ()))
    (indexedDraw (R := R) (deg := deg) n) (fun _ => $ᵗ R)
    (fun _ => (((deg : ℝ≥0) / Fintype.card R : ℝ≥0) : ℝ≥0∞))
    (scDrawIs n 0 (Nat.zero_add n)) (fun x _ h => ⟨(), h⟩) (fun x tr hacc => ?_)
    (fun x => sumcheck_roundSound D (x.2 ()))
  obtain ⟨t, ht, hl⟩ := indexed_validAcceptance D impl x tr hacc
  exact ⟨t, (scVerdict_eq D n 0 (Nat.zero_add n) x.1 tr).trans ht,
    (indexedRelation_last D t (x.2 ())).mpr hl⟩

/-- **Sum-check soundness through the kit**, with exactly the statement of
`Sumcheck.indexedVerifier_soundness`. -/
theorem indexedVerifier_soundness_viaKit [IsDomain R] [Fintype R] [SampleableType R]
    {ι σ : Type} (ambient : OracleSpec ι) (init : ProbComp σ)
    (impl : QueryImpl ambient (StateT σ ProbComp)) :
    (indexedVerifier R deg n D ambient).soundness init impl
      (indexedDraw (R := R) (deg := deg) n)
      (indexedInputProblem D) (indexedOutputProblem (R := R) (deg := deg) (n := n))
      ((n : ℝ≥0∞) * (((deg : ℝ≥0) / Fintype.card R : ℝ≥0) : ℝ≥0∞)) := by
  have h := (scRounds R deg n 0 (Nat.zero_add n)).soundness_of_rbrSoundness (init := init)
    (ε := fun _ => (((deg : ℝ≥0) / Fintype.card R : ℝ≥0) : ℝ≥0∞))
    (indexedVerifier_rbrSoundness_viaKit D ambient impl)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h
  exact h

end Sumcheck

/-! ## 5. A second family: polynomial rounds of varying degree

Sum-check's rounds all have the same message type and the same error. Here round `i` sends a
polynomial of degree at most `degs i`, so the message type and the error `degs i / |R|` change
with the round. Any claim reduction of this shape (sum-check over a non-uniform degree bound,
or a chain of univariate evaluation-claim reductions) gets its per-round obligation from one
algebraic fact per round: from a false claim, some honest polynomial differs from the message
whenever the round can pass into a true claim, and agrees with it at the challenge. -/

section PolyRounds

open Polynomial

variable (R : Type) [CommSemiring R]

/-- A round whose message is a univariate polynomial of degree at most `d`, read through its
evaluations. -/
@[reducible]
def polyRound (d : ℕ) : Round :=
  ⟨R⦃≤ d⦄[X], Sumcheck.Interpreted.messageInterface (fun (q : R⦃≤ d⦄[X]) r => q.val.eval r), R⟩

variable {R} [IsDomain R] [Fintype R] [SampleableType R] {degs : Fin n → ℕ}
  {S : Fin (n + 1) → Type}

/-- **The per-round obligation for varying-degree polynomial rounds**, from one algebraic fact:
from a false claim there is an honest polynomial `h` such that whenever the round passes into a
true claim at `r`, the message differs from `h` somewhere and agrees with it at `r`. -/
theorem polyRounds_roundSound (step : Step (fun i => polyRound R (degs i)) S)
    (good : ∀ i, S i → Prop)
    (hreduce : ∀ i st (msg : R⦃≤ degs i⦄[X]), ¬ good i.castSucc st →
      ∃ h : R⦃≤ degs i⦄[X], ∀ r st', step i st msg r = some st' → good i.succ st' →
        (∃ a, msg.val.eval a ≠ h.val.eval a) ∧ msg.val.eval r = h.val.eval r) :
    RoundSound (fun _ => $ᵗ R) step good
      (fun i => (((degs i : ℝ≥0) / Fintype.card R : ℝ≥0) : ℝ≥0∞)) := by
  intro i st msg hfalse
  obtain ⟨h, hh⟩ := hreduce i st msg hfalse
  by_cases hne : ∃ a, msg.val.eval a ≠ h.val.eval a
  · exact (prEvent_mono _ _ _ fun r ⟨st', hs, hg⟩ => (hh r st' hs hg).2).trans
      (agreement_le msg h hne)
  · rw [prEvent_eq_zero_of_forall_not _ _ fun r ⟨st', hs, hg⟩ => hne (hh r st' hs hg).1]
    exact zero_le

end PolyRounds

/-! ## Axioms -/

#print axioms Rounds.rbrSoundness
#print axioms Rounds.soundness_of_rbrSoundness
#print axioms Rounds.verifier_rbrSoundness
#print axioms Rounds.verifier_soundness
#print axioms claimReduction_le
#print axioms agreement_le_field
#print axioms sumcheck_roundSound
#print axioms kitVerifier_soundness
#print axioms indexedVerifier_soundness_viaKit
#print axioms polyRounds_roundSound

/-! ## Open problems

1. **Round shape.** A `Round` is exactly one oracle message followed by one challenge. Plain
   (non-oracle) messages, several messages or challenges per round, and a final message after the
   last challenge (FRI's final constant, for example) are not covered. The natural extension
   makes a round a small protocol with one challenge, and replaces the two-step spine recursion in
   `prefixGood` and `prefixGood_flip_le` by a recursion over that protocol.
2. **No FRI instance.** Section 5 proves the per-round obligation for polynomial rounds of varying
   degree, but no existing one-round protocol other than sum-check is iterated here. A FRI-shaped
   family needs item 1 (the final message), a folding state and its own distance argument for
   the per-round obligation.
3. **Failed attempt: a term-mode state function.** The first `prefixGood` matched the spine in
   term mode, with the patterns `.root _`, `.down _ (.root _)` and `.down _ (.down _ sp)`. Its
   recursive case did not reduce by definition when the partial transcript was a variable, so
   `prefixGood_send` failed with

       error: Type mismatch
         prefixGood_send w (st.bind fun u => step ⟨j, ⋯⟩ u y z) tail rest hown x
       has type
         prefixGood step good w (st.bind fun u => step ⟨j, ⋯⟩ u y z)
             (tail.comp (Cursor.Spine.down (oracleSig.toFunB x✝¹ x) ...))
             (PartialTranscriptAt.snoc oracleSig tail rest x) = ...
       but is expected to have type
         prefixGood step good (round j k h w) st
             ((Cursor.Spine.down b (Cursor.Spine.down b' tail)).comp ...) ... = ...

   The same equation also failed as a standalone `rfl` test. Defining the spine cases with the
   `cases` tactic, as `Sumcheck.foldPrefix` does, fixed it. The current definition does that.
4. **Failed attempt: rewriting the decision's tail.** In `simulate_decision`, a `change` to a goal
   that names the tail view as `toView _ tr` and then `rw [simulate_tail]` failed, because the
   view's type is `View rest tr.path` only after unfolding `tailPath`:

       error: Tactic `rewrite` failed: Did not find an occurrence of the pattern
         simulateQ (oracleMessageImpl (Round.then ?r ?rest) ⟨?msg, ⟨?c, ?tr⟩⟩)
           (simulateQ (tailLift ?r (Transcript.path ⟨?msg, ⟨?c, ?tr⟩⟩)) ?prog)
       ...
       Note: The target expression is not type-correct under the `implicit` transparency level

   Applying `(simulate_tail ..).trans` with `refine`, which unifies up to definitional
   unfolding, fixed it.
-/

end RoundIteration

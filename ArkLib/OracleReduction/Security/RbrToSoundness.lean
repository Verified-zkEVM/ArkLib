/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Calgooon
-/
module

public import ArkLib.OracleReduction.Security.RoundByRound

/-!
# The union step: round-by-round soundness implies soundness

`Verifier.rbrSoundness_implies_soundness` is unprovable as stated (`Counterexample.lean`):
`StateFunction.toFun_full` speaks of the verifier run from a fresh draw of `init`, while the
soundness game runs it from the oracle state the prover's queries left behind. This file proves
the implication under the full-transcript clause FROM EVERY oracle state
(`rbrSoundnessWith_implies_soundness_of_full`) and hence for every stateless simulation
(`rbrSoundness_implies_soundness_proved`, the original statement plus `[Subsingleton σ]`).

PORT NOTE: written at the fork pin `quangvdao/ArkLib` @ a5aa2677 (Lean v4.33.1, VCVio eb22883)
in VCVio's retired event-probability API and ported to the native measure semantics of VCVio
d7089e46 (`Pr{let x ← mx}[E x]`, the successful-output measure of a `Prop`-valued run at
`{True}`): the conditional decomposition of a bind is
`OracleComp.evalDist_bind_apply_le_add_of_support`, the zero and one facts go through the structural
support, and the optional layer through `OptionT.prEvent_mk` and
`OracleComp.OptionT.prEvent_mk_eq_zero_iff`. Elaborated on Modal against main @ 40c6adef on
2026-09-27: the three modules build and the six theorems here, in `Counterexample.lean` and in
`Implications.lean` print `[propext, Classical.choice, Quot.sound]`.

## The shape of the proof

Fix `stmtIn ∉ langIn`, a prover and its witness; write `sim := impl.addLift challengeQueryImpl`.
For each round `m : Fin (n + 1)` the prefix run `R m` is the prover run to round `m` under the
simulated oracles, the joint law of (transcript, prover state) and the oracle state
(`prefixRun`); `A m` is the probability that the state function is TRUE after round `m`
(`stateTrue`).

1. `A 0 = 0`: the transcript at round 0 is the empty one and `toFun_empty` says the state
   function is false there exactly because `stmtIn ∉ langIn` (`stateTrue_zero`).
2. A message round cannot turn the state function true (`toFun_next`):
   `A j.succ ≤ A j.castSucc` (`stateTrue_succ_of_P_to_V`).
3. A challenge round turns it true only through the bad transition, and the joint law of
   (prefix transcript, fresh challenge) inside the whole execution IS the round-`j` game of
   `rbrSoundness` for THE SAME prover (no per-round adversary is built; `rbrSoundness`
   quantifies over every prover and this one is one of them):
   `A j.succ ≤ A j.castSucc + Pr{let x ← rbrGame j}[bad_j x]` (`stateTrue_succ_of_V_to_P`). The
   engine of 2 and 3 is a conditional decomposition: from a pointwise inequality at every reachable
   outcome of the prefix, `Pr{y ← R >>= f}[q y] ≤ Pr{z ← R >>= g}[p z] + Pr{w ← R >>= h}[r w]`
   (`prEvent_bind_le_bind_add`).
4. By induction on the round (`Fin.induction`): `A (last n) ≤ ∑ i, ε i` over the challenge
   rounds (`stateTrue_last_le_sum`); the finite union bound is this telescoping sum.
5. The soundness game is the prover run to the last round, its output step, then the verifier
   run FROM THE ORACLE STATE THE PROVER LEFT BEHIND; where the state function is false at the
   full transcript the verifier accepts with probability zero from every state (the hypothesis
   `hfull`, the ∀-state form of `toFun_full`), so the acceptance probability is at most `A (last n)`
   (`soundGame_le_stateTrue_last`).
6. Chain 1 to 5: the acceptance probability is at most `∑ i, ε i`.

The delicate step is the quantification of step 5, and it is where the original statement
breaks: `toFun_full` speaks of the verifier run from a FRESH draw of `init`; the soundness game
runs it from the state the prover's own queries left. With a stateful `impl` the prover sets the
state and the verifier reads it, and the state function has nothing to say
(`Counterexample.lean`). The theorem holds with `hfull` in the ∀-state form and therefore
whenever `σ` is a subsingleton.
-/

@[expose] public section

namespace ArkLib.RbrToSoundness

open OracleComp OracleSpec ProtocolSpec
open scoped NNReal ENNReal ProbabilityTheory

/-! ### §1: the conditional decomposition of a bind, over `ProbComp`

`OracleComp.evalDist_bind_apply_le_add_of_support` lifts an additive bound on the continuations'
event masses, needed only at the structurally reachable prefix outcomes, through the common
prefix. Applied at the event `{True}` of a `Prop`-valued run it is the conditional
decomposition of `Pr{…}[…]` after a bind. -/
section generic

variable {α β γ δ : Type}

/-- a bind into `pure` re-indexes the event -/
lemma prEvent_bind_pure_fun (mx : ProbComp α) (f : α → β) (q : β → Prop) :
    Pr{let y ← mx >>= fun x => pure (f x)}[q y] = Pr{let x ← mx}[q (f x)] := by
  simp only [bind_assoc, pure_bind]

/-- the conditional decomposition with two terms on the right -/
lemma prEvent_bind_le_bind_add (mx : ProbComp α) (f : α → ProbComp β)
    (g : α → ProbComp γ) (h : α → ProbComp δ) (q : β → Prop) (p : γ → Prop) (r : δ → Prop)
    (hpt : ∀ x ∈ support mx,
      Pr{let y ← f x}[q y] ≤ Pr{let z ← g x}[p z] + Pr{let w ← h x}[r w]) :
    Pr{let y ← mx >>= f}[q y] ≤ Pr{let z ← mx >>= g}[p z] + Pr{let w ← mx >>= h}[r w] := by
  simp only [bind_assoc]
  exact evalDist_bind_apply_le_add_of_support mx _ _ _ (measurableSet_singleton True) hpt

/-- the conditional decomposition with one term on the right -/
lemma prEvent_bind_le_bind (mx : ProbComp α) (f : α → ProbComp β) (g : α → ProbComp γ)
    (q : β → Prop) (p : γ → Prop)
    (hpt : ∀ x ∈ support mx, Pr{let y ← f x}[q y] ≤ Pr{let z ← g x}[p z]) :
    Pr{let y ← mx >>= f}[q y] ≤ Pr{let z ← mx >>= g}[p z] := by
  simp only [bind_assoc]
  exact evalDist_bind_apply_mono_of_support mx _ _ (measurableSet_singleton True) hpt

/-- every outcome of a bind into `pure` is an image of a prefix outcome -/
lemma exists_of_mem_support_bind_pure (mx : ProbComp α) (f : α → β) {y : β}
    (hy : y ∈ support (mx >>= fun x => pure (f x))) : ∃ x ∈ support mx, y = f x := by
  obtain ⟨x, hx, hy⟩ := (mem_support_bind_iff mx _ y).mp hy
  exact ⟨x, hx, (mem_support_pure_iff y (f x)).mp hy⟩

/-- the event of a `pure` prefix is one when it holds at the value -/
lemma prEvent_pure_eq_one (x : α) (p : α → Prop) (hp : p x) :
    Pr{let y ← (pure x : ProbComp α)}[p y] = 1 :=
  prEvent_eq_one_of_forall_mem_support _ _ fun y hy => by
    rw [mem_support_pure_iff] at hy
    subst hy
    exact hp

/-- the event of a `pure` prefix is zero when it fails at the value -/
lemma prEvent_pure_eq_zero (x : α) (p : α → Prop) (hp : ¬ p x) :
    Pr{let y ← (pure x : ProbComp α)}[p y] = 0 :=
  prEvent_eq_zero_of_forall_mem_support _ _ fun y hy => by
    rw [mem_support_pure_iff] at hy
    subst hy
    exact hp

end generic

/-! ### §2: the games: the prefix runs of one prover, the round game, the whole run -/
section games

variable {ι : Type} {oSpec : OracleSpec ι} {StmtIn WitIn StmtOut WitOut : Type} {n : ℕ}
  {pSpec : ProtocolSpec n} [∀ i, SampleableType (pSpec.Challenge i)]
  {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
  (stmtIn : StmtIn) (witIn : WitIn) (prover : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec)

/-- the simulated oracles of every game: `impl` for the shared oracle, a uniform draw for each
challenge -/
local notation "sim" =>
  (impl.addLift challengeQueryImpl : QueryImpl (oSpec + [pSpec.Challenge]ₒ) (StateT σ ProbComp))

/-- the prover run to round `m` under the simulated oracles: the joint law of (transcript,
prover state) and the oracle state -/
def prefixRun (m : Fin (n + 1)) : ProbComp ((pSpec.Transcript m × prover.PrvState m) × σ) :=
  init >>= fun s => (simulateQ sim (prover.runToRound m stmtIn witIn)).run s

/-- the round-`i` game of `Verifier.rbrSoundness`, token for token -/
def rbrGame (i : pSpec.ChallengeIdx) :
    ProbComp (pSpec.Transcript i.1.castSucc × pSpec.Challenge i) :=
  do (simulateQ (impl.addLift challengeQueryImpl : QueryImpl _ (StateT σ ProbComp))
      (do
        let ⟨transcript, _⟩ ← prover.runToRound i.1.castSucc stmtIn witIn
        let challenge ← liftComp (pSpec.getChallenge i) _
        return (transcript, challenge))).run' (← init)

/-- the prover's whole run (to the last round, then its output step) with the oracle state -/
def fullRun : ProbComp ((pSpec.FullTranscript × StmtOut × WitOut) × σ) :=
  init >>= fun s => (simulateQ sim (prover.run stmtIn witIn)).run s

lemma rbrGame_eq (i : pSpec.ChallengeIdx) :
    rbrGame init impl stmtIn witIn prover i =
      prefixRun init impl stmtIn witIn prover i.1.castSucc >>= fun y =>
        (simulateQ sim (liftM (pSpec.getChallenge i) :
            OracleComp (oSpec + [pSpec.Challenge]ₒ) _)).run y.2
          >>= fun z => pure (y.1.1, z.1) := by
  simp only [rbrGame, prefixRun, bind_assoc]
  refine bind_congr fun s => ?_
  rw [simulateQ_bind, StateT.run'_bind']
  refine bind_congr fun ⟨⟨tr, st⟩, s'⟩ => ?_
  simp only [simulateQ_bind, simulateQ_pure, StateT.run'_bind', StateT.run'_pure',
    liftComp_eq_liftM]

lemma prefixRun_succ_of_V_to_P (j : Fin n) (hj : pSpec.dir j = .V_to_P) :
    prefixRun init impl stmtIn witIn prover j.succ =
      prefixRun init impl stmtIn witIn prover j.castSucc >>= fun y =>
        (simulateQ sim (liftM (pSpec.getChallenge ⟨j, hj⟩) :
            OracleComp (oSpec + [pSpec.Challenge]ₒ) _)).run y.2
          >>= fun z =>
        (simulateQ sim (liftM (prover.receiveChallenge ⟨j, hj⟩ y.1.2) :
            OracleComp (oSpec + [pSpec.Challenge]ₒ) _)).run z.2 >>= fun w =>
        pure ((y.1.1.concat z.1, w.1 z.1), w.2) := by
  simp only [prefixRun, Prover.runToRound_succ, Prover.processRound_of_dir_eq_V_to_P j hj,
    bind_assoc]
  refine bind_congr fun s => ?_
  rw [simulateQ_bind, StateT.run_bind]
  refine bind_congr fun ⟨⟨tr, st⟩, s'⟩ => ?_
  simp only [simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure]

lemma prefixRun_succ_of_P_to_V (j : Fin n) (hj : pSpec.dir j = .P_to_V) :
    prefixRun init impl stmtIn witIn prover j.succ =
      prefixRun init impl stmtIn witIn prover j.castSucc >>= fun y =>
        (simulateQ sim (liftM (prover.sendMessage ⟨j, hj⟩ y.1.2) :
            OracleComp (oSpec + [pSpec.Challenge]ₒ) _)).run y.2 >>= fun z =>
        pure ((y.1.1.concat z.1.1, z.1.2), z.2) := by
  simp only [prefixRun, Prover.runToRound_succ, Prover.processRound_of_dir_eq_P_to_V j hj,
    bind_assoc]
  refine bind_congr fun s => ?_
  rw [simulateQ_bind, StateT.run_bind]
  refine bind_congr fun ⟨⟨tr, st⟩, s'⟩ => ?_
  simp only [simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure]

lemma fullRun_eq :
    fullRun init impl stmtIn witIn prover =
      prefixRun init impl stmtIn witIn prover (Fin.last n) >>= fun y =>
        (simulateQ sim (liftM (prover.output y.1.2) :
            OracleComp (oSpec + [pSpec.Challenge]ₒ) _)).run y.2
          >>= fun z => pure ((y.1.1, z.1), z.2) := by
  simp only [fullRun, prefixRun, Prover.run, bind_assoc]
  refine bind_congr fun s => ?_
  rw [simulateQ_bind, StateT.run_bind]
  refine bind_congr fun ⟨⟨tr, st⟩, s'⟩ => ?_
  simp only [simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure]
  rfl

/-! ### §3: the state function along the execution -/

variable {langIn : Set StmtIn} {langOut : Set StmtOut}
  {verifier : Verifier oSpec StmtIn StmtOut pSpec}
  (sF : verifier.StateFunction init impl langIn langOut)

/-- the probability that the state function is TRUE after round `m` of the whole execution -/
noncomputable def stateTrue (m : Fin (n + 1)) : ℝ≥0∞ :=
  Pr{let y ← prefixRun init impl stmtIn witIn prover m}[sF m stmtIn y.1.1]

/-- the bad transition at challenge round `i`: the event of `rbrSoundness` -/
def badEvent (i : pSpec.ChallengeIdx) :
    pSpec.Transcript i.1.castSucc × pSpec.Challenge i → Prop :=
  fun x => ¬ sF i.1.castSucc stmtIn x.1 ∧ sF i.1.succ stmtIn (x.1.concat x.2)

/-- at round 0 the state function is false: the transcript is empty and `stmtIn ∉ langIn`
(`toFun_empty`) -/
lemma stateTrue_zero (hstmt : stmtIn ∉ langIn) :
    stateTrue init impl stmtIn witIn prover sF 0 = 0 := by
  unfold stateTrue
  refine prEvent_eq_zero_of_forall_mem_support _ _ fun y _ hy => hstmt ?_
  have h0 : y.1.1 = default := Unique.eq_default _
  rw [h0] at hy
  exact (sF.toFun_empty stmtIn).mpr hy

/-- a message round never turns the state function true (`toFun_next`) -/
lemma stateTrue_succ_of_P_to_V (j : Fin n) (hj : pSpec.dir j = .P_to_V) :
    stateTrue init impl stmtIn witIn prover sF j.succ ≤
      stateTrue init impl stmtIn witIn prover sF j.castSucc := by
  unfold stateTrue
  rw [prefixRun_succ_of_P_to_V init impl stmtIn witIn prover j hj]
  refine prEvent_bind_le_prEvent_of_support _ _ _ _ fun y _ hy => ?_
  refine prEvent_eq_zero_of_forall_mem_support _ _ fun x hx => ?_
  obtain ⟨z, _, rfl⟩ := exists_of_mem_support_bind_pure _ _ hx
  exact sF.toFun_next j hj stmtIn y.1.1 hy z.1.1

/-- a challenge round turns the state function true only through the bad transition, whose law
inside the whole execution is the round game for the same prover -/
lemma stateTrue_succ_of_V_to_P (j : Fin n) (hj : pSpec.dir j = .V_to_P) :
    stateTrue init impl stmtIn witIn prover sF j.succ ≤
      stateTrue init impl stmtIn witIn prover sF j.castSucc +
        Pr{let x ← rbrGame init impl stmtIn witIn prover ⟨j, hj⟩}[
          badEvent init impl stmtIn sF ⟨j, hj⟩ x] := by
  classical
  unfold stateTrue
  rw [prefixRun_succ_of_V_to_P init impl stmtIn witIn prover j hj, rbrGame_eq]
  have hR : Pr{let y ← prefixRun init impl stmtIn witIn prover j.castSucc}[
        sF j.castSucc stmtIn y.1.1]
      = Pr{let y ← prefixRun init impl stmtIn witIn prover j.castSucc >>= fun y => pure y}[
        sF j.castSucc stmtIn y.1.1] := by
    rw [bind_pure]
  rw [hR]
  refine prEvent_bind_le_bind_add _ _ _ _ _ _ _ fun y _ => ?_
  by_cases hy : sF j.castSucc stmtIn y.1.1
  · rw [prEvent_pure_eq_one y (fun z => sF j.castSucc stmtIn z.1.1) hy]
    exact le_add_right (prEvent_le_one _ _)
  · rw [prEvent_pure_eq_zero y (fun z => sF j.castSucc stmtIn z.1.1) hy, zero_add,
      prEvent_bind_pure_fun]
    refine prEvent_bind_le_prEvent_of_support _ _ _ _ fun z _ hz => ?_
    refine prEvent_eq_zero_of_forall_mem_support _ _ fun x hx => ?_
    obtain ⟨w, _, rfl⟩ := exists_of_mem_support_bind_pure _ _ hx
    exact fun h => hz ⟨hy, h⟩

/-- the round errors as a function of the round index: `ε i` at a challenge round, `0`
elsewhere -/
noncomputable def roundError (ε : pSpec.ChallengeIdx → ℝ≥0) (j : Fin n) : ℝ≥0∞ :=
  if h : pSpec.dir j = .V_to_P then (ε ⟨j, h⟩ : ℝ≥0∞) else 0

omit [∀ i, SampleableType (pSpec.Challenge i)] in
lemma sum_roundError (ε : pSpec.ChallengeIdx → ℝ≥0) :
    ∑ j : Fin n, roundError (pSpec := pSpec) ε j = ∑ i : pSpec.ChallengeIdx, (ε i : ℝ≥0∞) := by
  classical
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ
    (fun j : Fin n => pSpec.dir j = .V_to_P)]
  rw [Finset.sum_eq_zero (s := Finset.univ.filter (fun j : Fin n => ¬ pSpec.dir j = .V_to_P))
    (fun j hj => by simp only [Finset.mem_filter] at hj; simp [roundError, hj.2]), add_zero]
  rw [Finset.sum_subtype (Finset.univ.filter (fun j : Fin n => pSpec.dir j = .V_to_P))
    (p := fun j : Fin n => pSpec.dir j = .V_to_P) (fun j => by simp)]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [roundError, i.2]

/-- the telescoping sum: after round `m` the state function is true with probability at most
the sum of the round errors of the challenge rounds before `m` -/
lemma stateTrue_le_sum (hstmt : stmtIn ∉ langIn) (ε : pSpec.ChallengeIdx → ℝ≥0)
    (hrbr : ∀ i : pSpec.ChallengeIdx,
      Pr{let x ← rbrGame init impl stmtIn witIn prover i}[badEvent init impl stmtIn sF i x] ≤
        (ε i : ℝ≥0∞)) :
    ∀ m : Fin (n + 1), stateTrue init impl stmtIn witIn prover sF m ≤
      ∑ j ∈ Finset.univ.filter (fun j : Fin n => j.val < m.val), roundError ε j := by
  classical
  intro m
  induction m using Fin.induction with
  | zero => rw [stateTrue_zero init impl stmtIn witIn prover sF hstmt]; exact zero_le
  | succ j ih =>
    have h1 : roundError ε j = ∑ k : Fin n, if k = j then roundError ε k else 0 := by
      rw [Finset.sum_ite_eq']; simp
    have hsplit :
        ∑ k ∈ Finset.univ.filter (fun k : Fin n => k.val < j.succ.val), roundError ε k
          = ∑ k ∈ Finset.univ.filter (fun k : Fin n => k.val < j.castSucc.val), roundError ε k
            + roundError ε j := by
      rw [Finset.sum_filter, Finset.sum_filter, h1, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp only [Fin.val_succ, Fin.val_castSucc]
      by_cases hk : k = j
      · subst hk; simp
      · have hne : k.val ≠ j.val := fun h => hk (Fin.ext h)
        by_cases hlt : k.val < j.val
        · rw [ite_eq_left (by omega), ite_eq_left hlt, ite_eq_right hk, add_zero]
        · rw [ite_eq_right (by omega), ite_eq_right hlt, ite_eq_right hk, add_zero]
    rw [hsplit]
    by_cases hj : pSpec.dir j = .V_to_P
    · calc stateTrue init impl stmtIn witIn prover sF j.succ
          ≤ stateTrue init impl stmtIn witIn prover sF j.castSucc +
            Pr{let x ← rbrGame init impl stmtIn witIn prover ⟨j, hj⟩}[
              badEvent init impl stmtIn sF ⟨j, hj⟩ x] :=
            stateTrue_succ_of_V_to_P init impl stmtIn witIn prover sF j hj
        _ ≤ _ + roundError ε j := by
            gcongr
            rw [roundError, dite_eq_left hj]
            exact hrbr ⟨j, hj⟩
        _ ≤ _ := by gcongr
    · have hj' : pSpec.dir j = .P_to_V := by
        cases h : pSpec.dir j
        · rfl
        · exact absurd h hj
      calc stateTrue init impl stmtIn witIn prover sF j.succ
          ≤ stateTrue init impl stmtIn witIn prover sF j.castSucc :=
            stateTrue_succ_of_P_to_V init impl stmtIn witIn prover sF j hj'
        _ ≤ _ := le_add_right ih

/-- the union bound: after the last round, at most the sum of all the round errors -/
lemma stateTrue_last_le_sum (hstmt : stmtIn ∉ langIn) (ε : pSpec.ChallengeIdx → ℝ≥0)
    (hrbr : ∀ i : pSpec.ChallengeIdx,
      Pr{let x ← rbrGame init impl stmtIn witIn prover i}[badEvent init impl stmtIn sF i x] ≤
        (ε i : ℝ≥0∞)) :
    stateTrue init impl stmtIn witIn prover sF (Fin.last n) ≤
      ∑ i : pSpec.ChallengeIdx, (ε i : ℝ≥0∞) := by
  classical
  refine (stateTrue_le_sum init impl stmtIn witIn prover sF hstmt ε hrbr (Fin.last n)).trans
    ?_
  rw [Finset.filter_true_of_mem (fun k _ => by simp [Fin.val_last, k.isLt]), sum_roundError]

/-! ### §4: the soundness game: the verifier runs from the oracle state the prover leaves -/

variable (verifier)

/-- the soundness game (`Verifier.soundness` after its `let`s), token for token -/
def soundGame : OptionT ProbComp ((pSpec.FullTranscript × StmtOut × WitOut) × StmtOut) :=
  OptionT.mk do
    (simulateQ (impl.addLift challengeQueryImpl : QueryImpl _ (StateT σ ProbComp))
      (Reduction.run stmtIn witIn (Reduction.mk prover verifier)).run).run' (← init)

omit [∀ i, SampleableType (pSpec.Challenge i)] in
/-- the reduction's run, the `OptionT` layer resolved: the prover's run, the verifier's run
lifted, the verdict -/
lemma reductionRun_run :
    (Reduction.run stmtIn witIn (Reduction.mk prover verifier)).run =
      prover.run stmtIn witIn >>= fun pr =>
        (liftM (verifier.run stmtIn pr.1).run : OracleComp (oSpec + [pSpec.Challenge]ₒ) _)
          >>= fun so =>
        pure (so.map fun o => (pr, o)) := by
  simp only [Reduction.run, ← monadLift_liftM_OptionT, OptionT.run_bind, OptionT.run_monadLift,
    monadLift_self, bind_map_left, Option.elimM, Option.elim]
  refine bind_congr fun pr => bind_congr fun so => ?_
  cases so <;> simp [Option.getM]

lemma soundGame_eq :
    soundGame init impl stmtIn witIn prover verifier =
      OptionT.mk (fullRun init impl stmtIn witIn prover >>= fun y =>
        (simulateQ impl (verifier.run stmtIn y.1.1)).run y.2 >>= fun z =>
        pure (z.1.map fun o => (y.1, o))) := by
  simp only [soundGame, fullRun, reductionRun_run, bind_assoc]
  congr 1
  refine bind_congr fun s => ?_
  rw [simulateQ_bind, StateT.run'_bind']
  refine bind_congr fun ⟨pr, s'⟩ => ?_
  dsimp only
  rw [simulateQ_bind, QueryImpl.addLift_def, QueryImpl.simulateQ_add_liftM_left,
    QueryImpl.liftTarget_self, StateT.run'_bind']
  refine bind_congr fun ⟨so, s''⟩ => ?_
  simp only [simulateQ_pure, StateT.run'_pure']

/-- **the verifier step.** Where the state function is false at the full transcript and the
verifier accepts with probability zero FROM EVERY ORACLE STATE, the soundness game accepts with
probability at most the probability that the state function is true after the last round. -/
lemma soundGame_le_stateTrue_last
    (hfull : ∀ stmt tr, ¬ sF (.last n) stmt tr → ∀ s : σ,
      Pr{let stmtOut ← OptionT.mk ((simulateQ impl (verifier.run stmt tr)).run' s)}[
        stmtOut ∈ langOut] = 0) :
    Pr{let x ← soundGame init impl stmtIn witIn prover verifier}[x.2 ∈ langOut] ≤
      stateTrue init impl stmtIn witIn prover sF (Fin.last n) := by
  rw [soundGame_eq, OptionT.prEvent_mk]
  refine (prEvent_bind_le_prEvent_of_support _ _ (fun y => sF (Fin.last n) stmtIn y.1.1) _
    fun y _ hy => ?_).trans ?_
  · have hz := (OptionT.prEvent_mk_eq_zero_iff _ _).mp (hfull stmtIn y.1.1 hy y.2)
    refine prEvent_eq_zero_of_forall_mem_support _ _ fun o ho hbad => ?_
    obtain ⟨z, hzmem, rfl⟩ := exists_of_mem_support_bind_pure _ _ ho
    rcases h : z.1 with _ | v
    · simp [h] at hbad
    · rw [h] at hbad
      refine hz v ?_ (by simpa using hbad)
      rw [StateT.run'_eq, support_map]
      exact ⟨z, hzmem, h⟩
  · unfold stateTrue
    rw [fullRun_eq]
    refine prEvent_bind_le_prEvent_of_support _ _ _ _ fun y _ hy => ?_
    refine prEvent_eq_zero_of_forall_mem_support _ _ fun x hx => ?_
    obtain ⟨z, _, rfl⟩ := exists_of_mem_support_bind_pure _ _ hx
    exact hy

end games

end ArkLib.RbrToSoundness

/-! ### §5: the theorems -/

namespace Verifier

open OracleComp OracleSpec ProtocolSpec ArkLib.RbrToSoundness
open scoped NNReal ENNReal ProbabilityTheory

variable {ι : Type} {oSpec : OracleSpec ι} {StmtIn StmtOut : Type} {n : ℕ}
  {pSpec : ProtocolSpec n} [∀ i, SampleableType (pSpec.Challenge i)] {σ : Type}
  (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))

/-- **The union step, With-form.** Round-by-round soundness witnessed by a state function `sF`
(the body of `rbrSoundness` for that `sF`), together with `sF`'s full-transcript clause FROM
EVERY ORACLE STATE (`hfull`, the ∀-state form of `toFun_full`), gives soundness with error
`∑ i, ε i`. This is the statement that is true in general; `Counterexample.lean` shows the
clause from a fresh `init` alone does not suffice. -/
theorem rbrSoundnessWith_implies_soundness_of_full (langIn : Set StmtIn)
    (langOut : Set StmtOut) (verifier : Verifier oSpec StmtIn StmtOut pSpec)
    (rbrSoundnessError : pSpec.ChallengeIdx → ℝ≥0)
    (sF : verifier.StateFunction init impl langIn langOut)
    (hrbr : ∀ stmtIn ∉ langIn,
      ∀ WitIn WitOut : Type,
      ∀ witIn : WitIn,
      ∀ prover : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec,
      ∀ i : pSpec.ChallengeIdx,
        Pr{let ⟨transcript, challenge⟩ ← do
          (simulateQ (impl.addLift challengeQueryImpl : QueryImpl _ (StateT σ ProbComp))
            (do
              let ⟨transcript, _⟩ ← prover.runToRound i.1.castSucc stmtIn witIn
              let challenge ← liftComp (pSpec.getChallenge i) _
              return (transcript, challenge))).run' (← init)}[
          ¬ sF i.1.castSucc stmtIn transcript ∧
            sF i.1.succ stmtIn (transcript.concat challenge)] ≤
          rbrSoundnessError i)
    (hfull : ∀ stmt tr, ¬ sF (.last n) stmt tr → ∀ s : σ,
      Pr{let stmtOut ← OptionT.mk ((simulateQ impl (verifier.run stmt tr)).run' s)}[
        stmtOut ∈ langOut] = 0) :
    soundness init impl langIn langOut verifier (∑ i, rbrSoundnessError i) := by
  intro WitIn WitOut witIn prover stmtIn hstmt
  change Pr{let x ← soundGame init impl stmtIn witIn prover verifier}[x.2 ∈ langOut] ≤ _
  rw [ENNReal.ofNNReal_finsetSum]
  refine (soundGame_le_stateTrue_last init impl stmtIn witIn prover verifier sF hfull).trans ?_
  refine stateTrue_last_le_sum init impl stmtIn witIn prover sF hstmt rbrSoundnessError fun i => ?_
  -- the round game of `rbrSoundness` is `rbrGame` with its binds re-associated (the nested
  -- `(← init)` lifts out of the single-element `do`) and the bad event destructured; after
  -- unfolding, `bind_assoc` makes the two sides one term
  have h := hrbr stmtIn hstmt WitIn WitOut witIn prover i
  refine le_of_eq_of_le ?_ h
  unfold rbrGame badEvent
  simp only [bind_assoc]

/-- **The union step at the original statement plus `[Subsingleton σ]`.** When the oracle
simulation carries no state (the `init := pure ()`, `impl := isEmptyElim` convention of
`VectorIOR`), the state the prover leaves behind IS the fresh one, so `toFun_full` from a fresh
`init` is `toFun_full` from every reachable state and the With-form applies. Without
`[Subsingleton σ]` the statement is false (`Counterexample.lean`). -/
theorem rbrSoundness_implies_soundness_proved [Subsingleton σ] (langIn : Set StmtIn)
    (langOut : Set StmtOut) (verifier : Verifier oSpec StmtIn StmtOut pSpec)
    (rbrSoundnessError : pSpec.ChallengeIdx → ℝ≥0) :
      rbrSoundness init impl langIn langOut verifier rbrSoundnessError →
        soundness init impl langIn langOut verifier (∑ i, rbrSoundnessError i) := by
  rintro ⟨sF, hsF⟩
  by_cases hne : ∃ s₀, s₀ ∈ support init
  · obtain ⟨s₀, hs₀⟩ := hne
    refine rbrSoundnessWith_implies_soundness_of_full init impl langIn langOut verifier _ sF hsF
      ?_
    intro stmt tr htr s
    have h := (OptionT.prEvent_mk_eq_zero_iff _ _).mp (sF.toFun_full stmt tr htr)
    refine (OptionT.prEvent_mk_eq_zero_iff _ _).mpr fun x hx => h x ?_
    obtain rfl := Subsingleton.elim s₀ s
    exact (mem_support_bind_iff _ _ _).mpr ⟨_, hs₀, hx⟩
  · intro WitIn WitOut witIn prover stmtIn hstmt
    change Pr{let x ← soundGame init impl stmtIn witIn prover verifier}[x.2 ∈ langOut] ≤ _
    unfold soundGame
    rw [OptionT.prEvent_mk]
    refine (prEvent_eq_zero_of_forall_mem_support _ _ fun o ho _ => ?_).trans_le zero_le
    obtain ⟨s, hs, -⟩ := (mem_support_bind_iff _ _ _).mp ho
    exact hne ⟨s, hs⟩

end Verifier

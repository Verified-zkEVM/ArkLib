/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Interaction.Core.OracleVerifier
public import VCVio.OracleComp.EvalDist

/-!
# Finite heterogeneous stage composition

A finite family of stages runs across boundary types `State 0, …, State n` that may all differ.
Each stage maps an accepted boundary value to an optional next one, and a rejection stops the
fold: later stages do not run. `foldStages` is this fold in an arbitrary monad, with its zero,
successor, rejection, last-step and split laws, and the propagation of an invariant
deterministically, over the support, and almost surely.

A closed stage of oracle reductions pairs a protocol, an honest prover, a challenge
implementation and a passive oracle verifier between two declared interfaces. Its run is the
core run `OracleVerifier.run`, whose challenge queries are answered by the stage's draws, and it
hands the accepted output claim and the next private state to the following stage.
`ClosedStage.runStages` folds a family of closed stages.

Unlike `OracleVerifier.append`, which runs every interaction and decides at the end, a fold of
closed stages decides at each boundary. The two programs differ in the order of their effects,
and a rejecting stage skips the interactions of the later stages, which an append still runs.
-/

@[expose] public section

universe u v w uQ uQ'

namespace Interaction.Core
open PFunctor FreeM TwoParty.Lens OracleComp Oracle

section Fold

variable {m : Type u → Type v} [Monad m]

/-- Run `n` optional steps in order across the boundary types `State 0, …, State n`. A step that
returns `none` rejects, and no later step runs. -/
def foldStages : (n : Nat) → (State : Fin (n + 1) → Type u) →
    ((i : Fin n) → State i.castSucc → m (Option (State i.succ))) →
    State ⟨0, Nat.zero_lt_succ n⟩ → m (Option (State (Fin.last n)))
  | 0, _, _, x => pure (some x)
  | n + 1, State, step, x => step ⟨0, Nat.zero_lt_succ n⟩ x >>= fun r =>
    r.elim (pure none) (foldStages n (fun i => State i.succ) (fun i => step i.succ))

/-- With no stages, the fold accepts its input unchanged. -/
@[simp]
theorem foldStages_zero (State : Fin 1 → Type u)
    (step : (i : Fin 0) → State i.castSucc → m (Option (State i.succ)))
    (x : State ⟨0, Nat.zero_lt_succ 0⟩) : foldStages 0 State step x = pure (some x) := rfl

/-- The fold runs the first stage, then either rejects or folds the remaining stages from the
accepted value. -/
theorem foldStages_succ (n : Nat) (State : Fin (n + 2) → Type u)
    (step : (i : Fin (n + 1)) → State i.castSucc → m (Option (State i.succ)))
    (x : State ⟨0, Nat.zero_lt_succ _⟩) :
    foldStages (n + 1) State step x = (step ⟨0, Nat.zero_lt_succ n⟩ x >>= fun r =>
      r.elim (pure none) (foldStages n (fun i => State i.succ) (fun i => step i.succ))) := rfl

/-- A rejecting first stage skips every later stage. -/
theorem foldStages_succ_of_reject [LawfulMonad m] (n : Nat) (State : Fin (n + 2) → Type u)
    (step : (i : Fin (n + 1)) → State i.castSucc → m (Option (State i.succ)))
    (x : State ⟨0, Nat.zero_lt_succ _⟩) (h : step ⟨0, Nat.zero_lt_succ n⟩ x = pure none) :
    foldStages (n + 1) State step x = pure none := by
  rw [foldStages_succ, h, LawfulMonad.pure_bind]
  rfl

/-- The fold of one stage is that stage. -/
theorem foldStages_one [LawfulMonad m] (State : Fin 2 → Type u)
    (step : (i : Fin 1) → State i.castSucc → m (Option (State i.succ)))
    (x : State ⟨0, Nat.zero_lt_succ _⟩) :
    foldStages 1 State step x = step ⟨0, Nat.zero_lt_succ 0⟩ x := by
  rw [foldStages_succ]
  exact (bind_congr fun r => by cases r <;> rfl).trans (bind_pure _)

/-- The fold of `n + 1` stages folds the first `n` stages and then, after acceptance only, runs
the last stage. -/
theorem foldStages_succ_last [LawfulMonad m] : (n : Nat) → (State : Fin (n + 2) → Type u) →
    (step : (i : Fin (n + 1)) → State i.castSucc → m (Option (State i.succ))) →
    (x : State ⟨0, Nat.zero_lt_succ _⟩) →
    foldStages (n + 1) State step x =
      (foldStages n (fun i => State i.castSucc) (fun i => step i.castSucc) x >>= fun r =>
        r.elim (pure none) (step (Fin.last n)))
  | 0, State, step, x => by
    rw [foldStages_succ, foldStages_zero, LawfulMonad.pure_bind]
    refine (bind_congr fun r => ?_).trans (bind_pure _)
    cases r <;> rfl
  | n + 1, State, step, x => by
    rw [foldStages_succ, foldStages_succ, bind_assoc]
    refine bind_congr fun r => ?_
    cases r with
    | none =>
      exact (LawfulMonad.pure_bind none fun r => r.elim (pure none) (step (Fin.last (n + 1)))).symm
    | some y => exact foldStages_succ_last n (fun i => State i.succ) (fun i => step i.succ) y

/-- Splitting `a + b` stages after the first `a`: the suffix starts from the boundary value that
the prefix accepted, and does not run after a rejection. Effects keep their order. -/
theorem foldStages_add [LawfulMonad m] (a : Nat) : (b : Nat) →
    (State : Fin (a + b + 1) → Type u) →
    (step : (i : Fin (a + b)) → State i.castSucc → m (Option (State i.succ))) →
    (x : State ⟨0, Nat.zero_lt_succ _⟩) →
    foldStages (a + b) State step x =
      (foldStages a (fun i => State ⟨i, by omega⟩) (fun i => step ⟨i, by omega⟩) x >>= fun r =>
        r.elim (pure none) fun (y : State ⟨a, by omega⟩) =>
          foldStages b (fun i => State ⟨a + i, by omega⟩) (fun i => step ⟨a + i, by omega⟩) y)
  | 0, State, step, x =>
    ((bind_congr fun r => by cases r <;> rfl).trans (bind_pure _)).symm
  | b + 1, State, step, x => by
    refine (foldStages_succ_last (a + b) State step x).trans ?_
    rw [foldStages_add a b (fun i => State i.castSucc) (fun i => step i.castSucc), bind_assoc]
    refine bind_congr fun r => ?_
    cases r with
    | none => exact LawfulMonad.pure_bind _ _
    | some y =>
      exact (foldStages_succ_last b (fun i => State ⟨a + i, by omega⟩)
        (fun i => step ⟨a + i, by omega⟩) y).symm

/-- Splitting `k` stages at any `a` with `a + b = k`. The suffix's last boundary is the fold's
last boundary up to the equation `a + b = k`, along which its program is cast. -/
theorem foldStages_split [LawfulMonad m] (a b k : Nat) (h : a + b = k)
    (State : Fin (k + 1) → Type u)
    (step : (i : Fin k) → State i.castSucc → m (Option (State i.succ)))
    (x : State ⟨0, Nat.zero_lt_succ _⟩) :
    foldStages k State step x =
      (foldStages a (fun i => State ⟨i, by omega⟩) (fun i => step ⟨i, by omega⟩) x >>= fun r =>
        r.elim (pure none) fun (y : State ⟨a, by omega⟩) =>
          cast (congrArg (fun j : Fin (k + 1) => m (Option (State j)))
            (Fin.ext h : (⟨a + b, by omega⟩ : Fin (k + 1)) = Fin.last k))
            (foldStages b (fun i => State ⟨a + i, by omega⟩)
              (fun i => step ⟨a + i, by omega⟩) y)) := by
  subst h
  exact foldStages_add a b State step x

/-- Interpreting a fold of oracle computations is the fold of the interpreted stages. -/
theorem simulateQ_foldStages {ι : Type w} {spec : OracleSpec.{w, u} ι} [LawfulMonad m]
    (impl : QueryImpl spec m) : (n : Nat) → (State : Fin (n + 1) → Type u) →
    (step : (i : Fin n) → State i.castSucc → OracleComp spec (Option (State i.succ))) →
    (x : State ⟨0, Nat.zero_lt_succ _⟩) →
    simulateQ impl (foldStages n State step x) =
      foldStages n State (fun i y => simulateQ impl (step i y)) x
  | 0, _, _, _ => simulateQ_pure _ _
  | n + 1, State, step, x => by
    rw [foldStages_succ, foldStages_succ, simulateQ_bind]
    refine bind_congr fun r => ?_
    cases r with
    | none => exact simulateQ_pure _ _
    | some y => exact simulateQ_foldStages impl n (fun i => State i.succ) (fun i => step i.succ) y

/-- A deterministic acceptance invariant propagates from the initial boundary value through all
stages. One initial invariant and per-stage preservation suffice. -/
theorem foldStages_preserves [LawfulMonad m] (n : Nat) (State : Fin (n + 1) → Type u)
    (step : (i : Fin n) → State i.castSucc → m (Option (State i.succ)))
    (Inv : (i : Fin (n + 1)) → State i → Prop)
    (preserves : ∀ (i : Fin n) (x : State i.castSucc), Inv i.castSucc x →
      ∃ y, step i x = pure (some y) ∧ Inv i.succ y)
    (x : State ⟨0, Nat.zero_lt_succ _⟩) (hx : Inv ⟨0, Nat.zero_lt_succ _⟩ x) :
    ∃ y, foldStages n State step x = pure (some y) ∧ Inv (Fin.last n) y := by
  induction n with
  | zero => exact ⟨x, rfl, hx⟩
  | succ n ih =>
    obtain ⟨mid, hmid, hinv⟩ := preserves ⟨0, Nat.zero_lt_succ _⟩ x hx
    obtain ⟨y, hy, hfinal⟩ := ih (fun i => State i.succ) (fun i => step i.succ)
      (fun i => Inv i.succ) (fun i => preserves i.succ) mid hinv
    refine ⟨y, ?_, hfinal⟩
    rw [foldStages_succ, hmid, LawfulMonad.pure_bind]
    exact hy

/-- Every possible result of the fold is an accepted value satisfying the final invariant,
provided every possible result of each stage is, from an input satisfying its invariant. This
holds in every lawful monad whose support is exact for `pure` and `bind`. -/
theorem foldStages_preserves_support [LawfulMonad m] [MonadAttach m] [ExactMonadAttach m]
    (n : Nat) (State : Fin (n + 1) → Type u)
    (step : (i : Fin n) → State i.castSucc → m (Option (State i.succ)))
    (Inv : (i : Fin (n + 1)) → State i → Prop)
    (preserves : ∀ (i : Fin n) (x : State i.castSucc), Inv i.castSucc x →
      ∀ r ∈ support (step i x), ∃ y, r = some y ∧ Inv i.succ y)
    (x : State ⟨0, Nat.zero_lt_succ _⟩) (hx : Inv ⟨0, Nat.zero_lt_succ _⟩ x) :
    ∀ r ∈ support (foldStages n State step x), ∃ y, r = some y ∧ Inv (Fin.last n) y := by
  induction n with
  | zero =>
    intro r hr
    rw [foldStages_zero, support_pure, Set.mem_singleton_iff] at hr
    exact ⟨x, hr, hx⟩
  | succ n ih =>
    intro r hr
    rw [foldStages_succ, mem_support_bind_iff] at hr
    obtain ⟨mid, hmid, hr⟩ := hr
    obtain ⟨y, rfl, hy⟩ := preserves ⟨0, Nat.zero_lt_succ _⟩ x hx mid hmid
    exact ih (fun i => State i.succ) (fun i => step i.succ) (fun i => Inv i.succ)
      (fun i => preserves i.succ) y hy r hr

/-- Almost-sure acceptance and preservation at every stage give almost-sure acceptance and the
final invariant for the fold. Only the measure interpretation of the oracles is used. -/
theorem foldStages_preserves_measure {ι : Type w} {spec : OracleSpec.{w, u} ι}
    [spec.AnswerMeasure] (n : Nat) (State : Fin (n + 1) → Type u)
    [∀ i, MeasurableSpace (State i)] [∀ i, DiscreteMeasurableSpace (State i)]
    (step : (i : Fin n) → State i.castSucc → OracleComp spec (Option (State i.succ)))
    (Inv : (i : Fin (n + 1)) → State i → Prop)
    (preserves : ∀ (i : Fin n) (x : State i.castSucc), Inv i.castSucc x →
      𝒟[step i x] {r | ∃ y, r = some y ∧ Inv i.succ y} = 1)
    (x : State ⟨0, Nat.zero_lt_succ _⟩) (hx : Inv ⟨0, Nat.zero_lt_succ _⟩ x) :
    𝒟[foldStages n State step x] {r | ∃ y, r = some y ∧ Inv (Fin.last n) y} = 1 := by
  induction n with
  | zero =>
    rw [foldStages_zero, evalDist_pure, MeasureTheory.Measure.dirac_apply_of_mem]
    exact ⟨x, rfl, hx⟩
  | succ n ih =>
    rw [foldStages_succ]
    refine OracleComp.evalDist_bind_apply_eq_one_of_ae _ _ MeasurableSet.of_discrete ?_
    filter_upwards [(MeasureTheory.ae_iff_prob_eq_one Measurable.of_discrete).mpr
      (preserves ⟨0, Nat.zero_lt_succ _⟩ x hx)] with mid hmid
    obtain ⟨y, rfl, hy⟩ := hmid
    exact ih (fun i => State i.succ) (fun i => step i.succ)
      (fun i => Inv i.succ) (fun i => preserves i.succ) y hy

end Fold

/-- A boundary between stages: a public statement with a concrete oracle family, and a separate
private prover state. The query and answer types of the oracle interfaces live in their own
universe `uQ`. -/
structure StageInterface where
  /-- Public statement type. -/
  Stmt : Type u
  /-- Indices of the exported oracles. -/
  Index : Type u
  /-- Concrete data at each exported oracle. -/
  Data : Index → Type u
  /-- The query interfaces of the exported oracles. -/
  oracles : OracleFamily.{u, u, uQ} Index Data
  /-- Private prover state passed between stages. -/
  Private : Type u

/-- The public claim at a boundary: a statement and concrete data for the exported oracles. It is
the accepted output `OracleVerifier.Output` of an oracle verifier that targets the interface. -/
abbrev StageInterface.Claim (I : StageInterface.{u, uQ}) := I.Stmt × ∀ i, I.Data i

/-- The public claim and the separate private state required to run the next stage. -/
abbrev StageInterface.State (I : StageInterface.{u, uQ}) := I.Claim × I.Private

/-- A stage of oracle reductions between two declared interfaces. The protocol and the challenge
implementation are selected by the public statement. The prover additionally sees the claim's
oracle data and the private state, and the verifier has query access to the claim's oracles. -/
structure ClosedStage {ι : Type u} (ambient : OracleSpec.{u, u} ι) (I : StageInterface.{u, uQ})
    (J : StageInterface.{u, uQ'}) where
  /-- The protocol, selected by the public statement. -/
  protocol : I.Stmt → OracleProtocol.{u}
  /-- The challenge implementation of the selected protocol, over the shared oracles. -/
  draw : (stmt : I.Stmt) → (c : ChallengeNode oracleSig (protocol stmt)) →
    OracleComp ambient (challengeSpec oracleSig (protocol stmt) c)
  /-- The prover's private output, which may depend on the full transcript. -/
  Out : (stmt : I.Stmt) → PathAlong oracleSig (protocol stmt) → Type u
  /-- The honest prover, from the public claim and the private state. -/
  prover : (claim : I.Claim) → I.Private → Prover oracleSig ambient (protocol claim.1) (Out claim.1)
  /-- The passive oracle verifier, whose accepted output is a claim of the next interface. -/
  verifier : (stmt : I.Stmt) → OracleVerifier ambient (protocol stmt) I.Stmt (fun _ => J.Stmt)
    I.oracles (fun _ => J.oracles)
  /-- The next private state, from the transcript and the prover's private output. -/
  nextPrivate : (stmt : I.Stmt) → I.Private → (tr : PathAlong oracleSig (protocol stmt)) →
    Out stmt tr → J.Private

namespace ClosedStage

variable {ι : Type u} {ambient : OracleSpec.{u, u} ι} {I : StageInterface.{u, uQ}}
  {J : StageInterface.{u, uQ'}}

/-- The stage's challenge queries answered by its draws; shared queries stay shared. -/
def handler (stage : ClosedStage ambient I J) (stmt : I.Stmt) :
    QueryImpl (ambient + challengeSpec oracleSig (stage.protocol stmt)) (OracleComp ambient) :=
  QueryImpl.id' ambient + stage.draw stmt

/-- Run the stage on an input claim with the core oracle run, and hand over the accepted output
claim with the next private state. A rejection hands over nothing. -/
def run (stage : ClosedStage ambient I J) (input : I.State) :
    OracleComp ambient (Option J.State) := do
  let obs ← simulateQ (stage.handler input.1.1)
    ((stage.verifier input.1.1).run input.1.1 input.1.2 (stage.prover input.1 input.2))
  pure (obs.2.2.map fun claim => (claim, stage.nextPrivate input.1.1 input.2 obs.1 obs.2.1))

/-- The handoff is the verdict of the same core run, paired with the private state computed from
that run's transcript and prover output. -/
theorem run_eq (stage : ClosedStage ambient I J) (input : I.State) :
    stage.run input = (fun obs => obs.2.2.map fun claim =>
        (claim, stage.nextPrivate input.1.1 input.2 obs.1 obs.2.1)) <$>
      simulateQ (stage.handler input.1.1)
        ((stage.verifier input.1.1).run input.1.1 input.1.2 (stage.prover input.1 input.2)) := by
  simp only [run, map_eq_bind_pure_comp, Function.comp_def]

/-- Run a finite family of closed stages across declared interfaces. Each accepted claim is the
next stage's input claim, with the next private state. -/
abbrev runStages (n : Nat) (I : Fin (n + 1) → StageInterface.{u, uQ})
    (stages : (i : Fin n) → ClosedStage ambient (I i.castSucc) (I i.succ)) :
    (I ⟨0, Nat.zero_lt_succ n⟩).State → OracleComp ambient (Option (I (Fin.last n)).State) :=
  foldStages n (fun i => (I i).State) (fun i => (stages i).run)

end ClosedStage

end Interaction.Core

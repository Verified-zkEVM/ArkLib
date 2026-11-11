/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Interaction.Core.Reduction
public import VCVio.EvalDist.ProbabilityNotation
public import ToMathlib.Control.StateT
public import PolyFun.Interaction.TwoParty.Lens.Compose

/-!
# Plain execution

Execution uses PolyFun's focal-first runner, then calls the verifier decision. The observation
retains the transcript and prover output on rejection. Ambient failure remains a failure of the
oracle computation, distinct from a returned rejecting verdict.

Simulating a run against a sampler, under either schedule and into any lawful monad, simulates
every prover slot and every draw (`simulateQ_runWith_sampler`). Simulating a simulated prover
composes the two handlers (`Prover.simulate_simulate`).
-/

@[expose] public section

universe u uA v uS uW uι

namespace Interaction.Core
open PFunctor FreeM TwoParty.Lens OracleComp

/-- A completed interaction, including a possibly rejecting verifier verdict. The verdict's type
is the output statement type at the shape path of the transcript. -/
abbrev Observation {P : PFunctor.{uA, u}} (l : PFunctor.Lens P rolePoly.{u})
    (s : FreeM P PUnit.{u + 1}) (Out : PathAlong l s → Type u) (StmtOut : Path s → Type u) :=
  (tr : PathAlong l s) × Out tr × Option (StmtOut (projectPathAlong l s tr))

/-- Run the interaction against an arbitrary focal strategy, and decide at its end. -/
def Verifier.run {ι : Type u} {ambient : OracleSpec.{u, u} ι}
    {s : Protocol.{u}} {S : Type uS} {T : Path s → Type u} {Out : PathAlong plainSig s → Type u}
    (V : Verifier ambient s S T) (stmt : S) (p : Prover plainSig ambient s Out) :
    OracleComp (ambient + challengeSpec plainSig s) (Observation plainSig s Out T) := do
  let ⟨tr, out, _⟩ ← TwoParty.Lens.run s
    (p.simulate (fun q => liftM ((ambient + challengeSpec plainSig s).query (.inl q))))
    (sampler plainSig s (fun c =>
      liftM ((ambient + challengeSpec plainSig s).query (.inr c))))
  let verdict ← OracleComp.liftComp
    (V.decide stmt (projectPathAlong plainSig s tr) (toPlainView s tr)).run
    (ambient + challengeSpec plainSig s)
  pure ⟨tr, out, verdict⟩

/-- Every challenge action has the prescribed event marginals. By the lawful bind semantics,
these marginals hold after every history, independently of the earlier actions. Missing mass in
ambient actions is permitted; a challenge has exactly the mass of its specified draw. -/
def FreshChallenges {m : Type → Type v} [Monad m] [EvalDistSemantics m]
    {ι : Type uι} {ambient : OracleSpec.{uι, 0} ι} {P : PFunctor.{uA, 0}}
    {l : PFunctor.Lens P rolePoly} {s : FreeM P PUnit}
    (handler : QueryImpl (ambient + challengeSpec l s) m)
    (draw : QueryImpl (challengeSpec l s) ProbComp) : Prop :=
  ∀ c (event : challengeSpec l s c → Prop),
    Pr{let x ← handler (.inr c)}[event x] = Pr{let x ← draw c}[event x]

/-- A stateful challenge has the prescribed event marginals from every current state.
The challenge may change the state; only its move distribution is fixed. -/
def FreshChallengesAt {m : Type → Type v} [Monad m] [EvalDistSemantics m]
    {ι : Type uι} {σ : Type} {ambient : OracleSpec.{uι, 0} ι}
    {P : PFunctor.{uA, 0}}
    {l : PFunctor.Lens P rolePoly} {s : FreeM P PUnit}
    (handler : QueryImpl (ambient + challengeSpec l s) (StateT σ m))
    (draw : QueryImpl (challengeSpec l s) ProbComp) : Prop :=
  ∀ st c (event : challengeSpec l s c → Prop),
    Pr{let x ← (handler (.inr c)).run' st}[event x] = Pr{let x ← draw c}[event x]

/-- Lifting a separate challenge draw into the ambient state gives fresh challenge marginals. -/
theorem freshChallengesAt_addLift {ι : Type uι} {σ : Type}
    {ambient : OracleSpec.{uι, 0} ι} {P : PFunctor.{uA, 0}}
    {l : PFunctor.Lens P rolePoly} {s : FreeM P PUnit}
    (impl : QueryImpl ambient (StateT σ ProbComp))
    (draw : QueryImpl (challengeSpec l s) ProbComp) :
    FreshChallengesAt
      (impl.addLift draw : QueryImpl (ambient + challengeSpec l s) (StateT σ ProbComp)) draw := by
  intro st c event
  simp only [QueryImpl.addLift_def, QueryImpl.add_apply_inr, QueryImpl.liftTarget_apply,
    StateT.liftM_def, StateT.run'_lift']

/-- Every possible verdict of a run is a possible verdict of the decision on its transcript. -/
theorem Verifier.verdict_mem_support_run {ι : Type u} {ambient : OracleSpec.{u, u} ι}
    {s : Protocol.{u}} {S : Type uS} {T : Path s → Type u} {Out : PathAlong plainSig s → Type u}
    (V : Verifier ambient s S T) (stmt : S) (p : Prover plainSig ambient s Out)
    {obs : Observation plainSig s Out T} (h : obs ∈ support (V.run stmt p)) :
    obs.2.2 ∈ support
      (V.decide stmt (projectPathAlong plainSig s obs.1) (toPlainView s obs.1)).run := by
  simp only [Verifier.run, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at h
  obtain ⟨⟨tr, out, _⟩, -, verdict, hv, rfl⟩ := h
  simpa only [mem_support_liftComp_iff] using hv

/-- Execute the honest prover and terminal decision, retaining explicit rejection. -/
def Reduction.observe {ι : Type u} {ambient : OracleSpec.{u, u} ι}
    {s : Protocol.{u}} {S : Type uS} {W : Type uW} {T : Path s → Type u}
    {Out : PathAlong plainSig s → Type u}
    (R : Reduction ambient s S W T Out) (stmt : S) (wit : W) :
    OracleComp (ambient + challengeSpec plainSig s) (Observation plainSig s Out T) :=
  R.verifier.run stmt (R.prover stmt wit)

/-- The accepting-result presentation of the same execution. -/
def Reduction.run {ι : Type u} {ambient : OracleSpec.{u, u} ι}
    {s : Protocol.{u}} {S : Type uS} {W : Type uW} {T : Path s → Type u}
    {Out : PathAlong plainSig s → Type u}
    (R : Reduction ambient s S W T Out) (stmt : S) (wit : W) :
    OptionT (OracleComp (ambient + challengeSpec plainSig s))
      ((tr : PathAlong plainSig s) × Out tr × T (projectPathAlong plainSig s tr)) :=
  OptionT.mk do
    let ⟨tr, out, verdict⟩ ← R.observe stmt wit
    pure (verdict.map fun t => ⟨tr, out, t⟩)

/-! ### Simulating a run -/

section Simulate

variable {κ κ' : Type u} {spec : OracleSpec.{u, u} κ} {spec' : OracleSpec.{u, u} κ'}
  {n : Type u → Type u} [Monad n] [LawfulMonad n]

/-- Simulation interprets both slots and the continuation of a local exchange. -/
theorem simulateQ_step {X : Type u} {A B : X → Type u} {R : Type u}
    (F : QueryImpl spec n) (role : TwoParty.Role) (order : Schedule)
    (p : OracleComp spec (Choice .focal role X A))
    (c : OracleComp spec (Choice .counterpart role X B))
    (k : ∀ x, A x → B x → OracleComp spec R) :
    simulateQ F (step role order p c k) =
      step role order (simulateQ F p) (simulateQ F c)
        (fun x a b => simulateQ F (k x a b)) := by
  cases role <;> cases order <;> simp only [step, Schedule.seq, simulateQ_bind]

/-- Simulating a run against a public-coin sampler, under either schedule, simulates every
    prover slot and every draw for any ownership lens. -/
theorem simulateQ_runWith_sampler {P : PFunctor.{uA, u}}
    {l : PFunctor.Lens P rolePoly.{u}} (F : QueryImpl spec n) (order : Schedule) :
    (s : FreeM P PUnit.{u + 1}) → {Out : PathAlong l s → Type u} →
    (p : Prover l spec s Out) →
    (draw : (c : ChallengeNode l s) → OracleComp spec (challengeSpec l s c)) →
    simulateQ F (runWith order s p (sampler l s draw)) =
      runWith order s (Prover.simulate F p)
        (sampler l s (fun c => simulateQ F (draw c)))
  | .pure ⟨⟩, _, p, _ => by
    erw [runWith_done, runWith_done]
    cases order <;> simp only [Schedule.seq, simulateQ_bind, simulateQ_pure] <;> rfl
  | .liftBind a rest, _, p, draw => by
    rw [TwoParty.Lens.runWith_node, TwoParty.Lens.runWith_node]
    simp only [interaction]
    rw [Prover.simulate_node, sampler_node, sampler_node]
    rw [simulateQ_step, simulateQ_map, simulateQ_samplerSlot, step_map_right, step_map]
    apply congrArg₂ (fun c k => step (owner l a) order (simulateQ F p) c k)
    · rfl
    · funext x pn cn
      rw [simulateQ_bind, simulateQ_runWith_sampler F order]
      simp only [simulateQ_pure]
      rfl

end Simulate

section SplitSimulation

variable {P : PFunctor.{uA, u}} {l : PFunctor.Lens P rolePoly.{u}}
  {ι κ : Type u} {ambient : OracleSpec.{u, u} ι} {spec : OracleSpec.{u, u} κ}
  {n : Type u → Type u}
  [Monad n] [LawfulMonad n]

/-- Interpreting a run against a sampler interprets every prover slot and every draw. -/
theorem simulateQ_run_simulate_sampler (h : QueryImpl spec n)
    (ιm : QueryImpl ambient (OracleComp spec)) (s : FreeM P PUnit.{u + 1})
    {Out : PathAlong l s → Type u} (k : Prover l ambient s Out)
    (draw : (c : ChallengeNode l s) → OracleComp spec (challengeSpec l s c)) :
    simulateQ h (TwoParty.Lens.run s (k.simulate ιm) (sampler l s draw)) =
      TwoParty.Lens.run s (k.simulate fun q => simulateQ h (ιm q))
        (sampler l s fun c => simulateQ h (draw c)) := by
  rw [TwoParty.Lens.run, simulateQ_runWith_sampler, Prover.simulate_simulate]
  rfl

/-- Splitting the first slot of a simulated prover simulates the split slot and then the
returned strategy. -/
theorem splitSlot_simulate (ιm : QueryImpl ambient n) :
    (s : FreeM P PUnit.{u + 1}) → {Out : PathAlong l s → Type u} →
    (prover : Prover l ambient s Out) →
    Strategy.splitSlot (prover.simulate ιm) =
      (fun k => Prover.simulate ιm k) <$> simulateQ ιm (Strategy.splitSlot prover)
  | .pure _, _, prover => by
    simp only [Strategy.splitSlot, Prover.simulate_done, simulateQ_map, Functor.map_map]
    rfl
  | .liftBind a rest, _, prover => by
    simp only [Strategy.splitSlot, Prover.simulate_node, simulateQ_map, Functor.map_map,
      simulateQ_pure]
    exact congrArg (· <$> _) (funext fun v => (LawfulApplicative.map_pure _ _).symm)

/-- Splitting a simulated prover at the seam simulates the split prover and then each
returned continuation. -/
theorem splitPrefix_simulate (ιm : QueryImpl ambient n) :
    (s₁ : FreeM P PUnit.{u + 1}) → (s₂ : Path s₁ → FreeM P PUnit.{u + 1}) →
    {Out : PathAlong l (s₁.append s₂) → Type u} →
    (prover : Prover l ambient (s₁.append s₂) Out) →
    Focal.splitPrefix (prover.simulate ιm) =
      Strategy.mapOutput (fun _ k => Prover.simulate ιm k)
        (Prover.simulate ιm (Focal.splitPrefix prover))
  | .pure ⟨⟩, s₂, _, prover => splitSlot_simulate ιm (s₂ ⟨⟩) prover
  | .liftBind a next, s₂, _, prover => by
    simp only [Focal.splitPrefix, Strategy.mapOutput, PureEnd.mapOutput, Prover.simulate_node,
      simulateQ_map, Functor.map_map]
    refine congrArg (· <$> _) (funext fun v => ?_)
    refine (congrFun (Choice.map_comp _ _ _ _) v).trans ?_
    refine Eq.trans ?_ (congrFun (Choice.map_comp _ _ _ _) _).symm
    refine Eq.trans ?_ (congrFun (Choice.map_comp _ _ _ _) v).symm
    exact congrArg (fun f => Choice.map .focal (owner l a) f v)
      (funext fun x => funext fun r => splitPrefix_simulate ιm (next (l.toFunB a x))
        (fun p => s₂ ⟨l.toFunB a x, p⟩) r)

end SplitSimulation

/-- On an accepted statement, the guarded run is the run. -/
theorem Verifier.onAccept_run_some {ι : Type u} {ambient : OracleSpec.{u, u} ι}
    {s : Protocol.{u}} {T : Type uS} {U : Path s → Type u}
    {Out : PathAlong plainSig s → Type u}
    (V : Verifier ambient s T U) (t : T) (prover : Prover plainSig ambient s Out) :
    V.onAccept.run (some t) prover = V.run t prover := rfl

/-- On a rejected statement, the guarded run interacts and rejects. -/
theorem Verifier.onAccept_run_none {ι : Type u} {ambient : OracleSpec.{u, u} ι}
    {s : Protocol.{u}} {T : Type uS} {U : Path s → Type u}
    {Out : PathAlong plainSig s → Type u}
    (V : Verifier ambient s T U) (prover : Prover plainSig ambient s Out) :
    V.onAccept.run none prover =
      (fun r => ⟨r.1, r.2.1, none⟩) <$> TwoParty.Lens.run s
        (prover.simulate (fun q => liftM ((ambient + challengeSpec plainSig s).query (.inl q))))
        (sampler plainSig s (fun c =>
          liftM ((ambient + challengeSpec plainSig s).query (.inr c)))) := by
  simp only [Verifier.run, Verifier.onAccept, map_eq_bind_pure_comp]
  refine bind_congr fun r => ?_
  simp

end Interaction.Core

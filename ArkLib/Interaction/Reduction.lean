/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import PolyFun.Interaction.TwoParty.Compose

/-!
# Plain dependent reductions

This file packages the smallest ArkLib reduction layer over PolyFun's typed interaction trees.
A reduction pairs:

* a focal prover strategy, constructed monadically from a statement and witness; and
* a counterpart verifier strategy, constructed from the same public statement.

The interaction tree, role decoration, and terminal output families may all depend on the shared
input. `Reduction.execute` is only a transparent wrapper around `TwoParty.run`.

## Sequential composition

`Reduction.comp` appends a second reduction whose tree and roles may depend on the complete first
path. The first prover and verifier outputs become the second reduction's inputs.

There are two distinct execution laws in PolyFun:

* `TwoParty.run_compFlat_appendFlat_pure` factors a pure suffix constructor under `LawfulMonad`;
* `TwoParty.run_comp_append` factors a general effectful suffix constructor under
  `TwoParty.LawfulCommMonad`.

ArkLib's prover setup is effectful in general, so `Reduction.execute_comp` deliberately exposes
the second boundary. Stateful clients without commutative effects must thread state explicitly
rather than use this factorization theorem.
-/

universe u v w x

namespace Interaction

open TwoParty

/-! ## Participants -/

/-- The next statement and witness produced by an honest prover. -/
abbrev HonestProverOutput (StatementOut : Type u) (WitnessOut : Type v) :=
  StatementOut × WitnessOut

namespace HonestProverOutput

/-- The statement component of an honest prover output. -/
abbrev stmt {StatementOut : Type u} {WitnessOut : Type v}
    (out : HonestProverOutput StatementOut WitnessOut) : StatementOut :=
  out.1

/-- The witness component of an honest prover output. -/
abbrev wit {StatementOut : Type u} {WitnessOut : Type v}
    (out : HonestProverOutput StatementOut WitnessOut) : WitnessOut :=
  out.2

/-- Split a lifted honest-prover output into separately lifted statement and witness outputs. -/
def splitLiftAppend
    (ctx₁ : TypeTree) (ctx₂ : TypeTree.Path ctx₁ → TypeTree)
    (StatementOut WitnessOut : (tr₁ : TypeTree.Path ctx₁) → TypeTree.Path (ctx₂ tr₁) → Type u)
    (tr : TypeTree.Path (ctx₁.append ctx₂))
    (out : PFunctor.FreeM.Path.liftAppend ctx₁ ctx₂
      (fun tr₁ tr₂ => HonestProverOutput (StatementOut tr₁ tr₂) (WitnessOut tr₁ tr₂)) tr) :
    HonestProverOutput
      (PFunctor.FreeM.Path.liftAppend ctx₁ ctx₂ StatementOut tr)
      (PFunctor.FreeM.Path.liftAppend ctx₁ ctx₂ WitnessOut tr) :=
  PFunctor.FreeM.Path.liftAppendProd ctx₁ ctx₂ StatementOut WitnessOut tr out

theorem splitLiftAppend_packAppend
    (ctx₁ : TypeTree) (ctx₂ : TypeTree.Path ctx₁ → TypeTree)
    (StatementOut WitnessOut : (tr₁ : TypeTree.Path ctx₁) → TypeTree.Path (ctx₂ tr₁) → Type u)
    (tr₁ : TypeTree.Path ctx₁) (tr₂ : TypeTree.Path (ctx₂ tr₁))
    (out : HonestProverOutput (StatementOut tr₁ tr₂) (WitnessOut tr₁ tr₂)) :
    splitLiftAppend ctx₁ ctx₂ StatementOut WitnessOut
        (PFunctor.FreeM.Path.append ctx₁ ctx₂ tr₁ tr₂)
        (PFunctor.FreeM.Path.packAppend ctx₁ ctx₂
          (fun tr₁ tr₂ => HonestProverOutput (StatementOut tr₁ tr₂) (WitnessOut tr₁ tr₂))
          tr₁ tr₂ out) =
      (PFunctor.FreeM.Path.packAppend ctx₁ ctx₂ StatementOut tr₁ tr₂ out.stmt,
        PFunctor.FreeM.Path.packAppend ctx₁ ctx₂ WitnessOut tr₁ tr₂ out.wit) :=
  PFunctor.FreeM.Path.liftAppendProd_packAppend
    ctx₁ ctx₂ StatementOut WitnessOut tr₁ tr₂ out

/-- Split the honest-prover payload in a complete run of an appended interaction. -/
def splitLiftAppendRun
    (ctx₁ : TypeTree) (ctx₂ : TypeTree.Path ctx₁ → TypeTree)
    (StatementOut WitnessOut : (tr₁ : TypeTree.Path ctx₁) → TypeTree.Path (ctx₂ tr₁) → Type u)
    (run : (tr : TypeTree.Path (ctx₁.append ctx₂)) ×
      PFunctor.FreeM.Path.liftAppend ctx₁ ctx₂
        (fun tr₁ tr₂ => HonestProverOutput (StatementOut tr₁ tr₂) (WitnessOut tr₁ tr₂)) tr ×
      PFunctor.FreeM.Path.liftAppend ctx₁ ctx₂ StatementOut tr) :
    ((tr : TypeTree.Path (ctx₁.append ctx₂)) ×
      HonestProverOutput
        (PFunctor.FreeM.Path.liftAppend ctx₁ ctx₂ StatementOut tr)
        (PFunctor.FreeM.Path.liftAppend ctx₁ ctx₂ WitnessOut tr) ×
      PFunctor.FreeM.Path.liftAppend ctx₁ ctx₂ StatementOut tr) :=
  ⟨run.1, splitLiftAppend ctx₁ ctx₂ StatementOut WitnessOut run.1 run.2.1, run.2.2⟩

end HonestProverOutput

/-- A prover performs monadic setup and returns the focal strategy for the selected input. -/
abbrev Prover (m : Type u → Type u)
    (SharedIn : Type v)
    (Context : SharedIn → TypeTree)
    (Roles : (i : SharedIn) → RoleDecoration (Context i))
    (StatementIn : SharedIn → Type w)
    (WitnessIn : SharedIn → Type x)
    (StatementOut WitnessOut : (i : SharedIn) → TypeTree.Path (Context i) → Type u) :=
  (i : SharedIn) → StatementIn i → WitnessIn i →
    m (StrategyOver (SyntaxOver.TwoParty.pairedTypeTree m) Participant.focal
      (Context i) (Roles i)
      (fun tr => HonestProverOutput (StatementOut i tr) (WitnessOut i tr)))

/-- A verifier returns the counterpart strategy for the selected input and public statement. -/
abbrev Verifier (m : Type u → Type u)
    (SharedIn : Type v)
    (Context : SharedIn → TypeTree)
    (Roles : (i : SharedIn) → RoleDecoration (Context i))
    (StatementIn : SharedIn → Type w)
    (StatementOut : (i : SharedIn) → TypeTree.Path (Context i) → Type u) :=
  (i : SharedIn) → StatementIn i →
    StrategyOver (SyntaxOver.TwoParty.pairedTypeTree m) Participant.counterpart
      (Context i) (Roles i) (StatementOut i)

/-- A plain dependent reduction pairs a prover and verifier for one typed interaction. -/
structure Reduction (m : Type u → Type u)
    (SharedIn : Type v)
    (Context : SharedIn → TypeTree)
    (Roles : (i : SharedIn) → RoleDecoration (Context i))
    (StatementIn : SharedIn → Type w)
    (WitnessIn : SharedIn → Type x)
    (StatementOut WitnessOut : (i : SharedIn) → TypeTree.Path (Context i) → Type u) where
  prover : Prover m SharedIn Context Roles StatementIn WitnessIn StatementOut WitnessOut
  verifier : Verifier m SharedIn Context Roles StatementIn StatementOut

/-! ## Execution -/

/-- Execute a reduction with PolyFun's canonical two-party runner. -/
def Reduction.execute {m : Type u → Type u} [Monad m]
    {SharedIn : Type v}
    {Context : SharedIn → TypeTree}
    {Roles : (i : SharedIn) → RoleDecoration (Context i)}
    {StatementIn : SharedIn → Type w}
    {WitnessIn : SharedIn → Type x}
    {StatementOut WitnessOut : (i : SharedIn) → TypeTree.Path (Context i) → Type u}
    (reduction : Reduction m SharedIn Context Roles StatementIn WitnessIn StatementOut WitnessOut)
    (i : SharedIn) (stmt : StatementIn i) (wit : WitnessIn i) :
    m ((tr : TypeTree.Path (Context i)) ×
      HonestProverOutput (StatementOut i tr) (WitnessOut i tr) × StatementOut i tr) := do
  let strategy ← reduction.prover i stmt wit
  TwoParty.run (Context i) (Roles i) strategy (reduction.verifier i stmt)

/-- Honest execution is definitionally PolyFun's two-party runner after prover setup. -/
theorem Reduction.execute_eq_run {m : Type u → Type u} [Monad m]
    {SharedIn : Type v}
    {Context : SharedIn → TypeTree}
    {Roles : (i : SharedIn) → RoleDecoration (Context i)}
    {StatementIn : SharedIn → Type w}
    {WitnessIn : SharedIn → Type x}
    {StatementOut WitnessOut : (i : SharedIn) → TypeTree.Path (Context i) → Type u}
    (reduction : Reduction m SharedIn Context Roles StatementIn WitnessIn StatementOut WitnessOut)
    (i : SharedIn) (stmt : StatementIn i) (wit : WitnessIn i) :
    reduction.execute i stmt wit = (do
      let strategy ← reduction.prover i stmt wit
      TwoParty.run (Context i) (Roles i) strategy (reduction.verifier i stmt)) := rfl

/-- Run a focal strategy against an input-indexed verifier. -/
def Verifier.run {m : Type u → Type u} [Monad m]
    {SharedIn : Type v}
    {Context : SharedIn → TypeTree}
    {Roles : (i : SharedIn) → RoleDecoration (Context i)}
    {StatementIn : SharedIn → Type w}
    {StatementOut : (i : SharedIn) → TypeTree.Path (Context i) → Type u}
    (verifier : Verifier m SharedIn Context Roles StatementIn StatementOut)
    (i : SharedIn) (stmt : StatementIn i)
    {OutputP : TypeTree.Path (Context i) → Type u}
    (prover : StrategyOver (SyntaxOver.TwoParty.pairedTypeTree m) Participant.focal
      (Context i) (Roles i) OutputP) :
    m ((tr : TypeTree.Path (Context i)) × OutputP tr × StatementOut i tr) :=
  TwoParty.run (Context i) (Roles i) prover (verifier i stmt)

/-! ## Sequential composition -/

/-- Compose a reduction with a continuation reduction indexed by the complete prefix path.

The second shared input remembers the original public statement as well as the realized prefix.
Its statement and witness inputs are exactly the first reduction's outputs. The combined terminal
families use `PFunctor.FreeM.Path.liftAppend`, preserving their dependence on both paths. -/
def Reduction.comp {m : Type u → Type u} [Monad m]
    {SharedIn : Type v}
    {StatementIn : SharedIn → Type w}
    {WitnessIn : SharedIn → Type x}
    {ctx₁ : SharedIn → TypeTree}
    {roles₁ : (i : SharedIn) → RoleDecoration (ctx₁ i)}
    {StmtMid WitMid : (i : SharedIn) → TypeTree.Path (ctx₁ i) → Type u}
    {ctx₂ : (i : SharedIn) → TypeTree.Path (ctx₁ i) → TypeTree}
    {roles₂ : (i : SharedIn) → (tr₁ : TypeTree.Path (ctx₁ i)) → RoleDecoration (ctx₂ i tr₁)}
    {StmtOut WitOut : (i : SharedIn) → (tr₁ : TypeTree.Path (ctx₁ i)) →
      TypeTree.Path (ctx₂ i tr₁) → Type u}
    (reduction₁ : Reduction m SharedIn ctx₁ roles₁ StatementIn WitnessIn StmtMid WitMid)
    (reduction₂ : Reduction m
      ((i : SharedIn) × StatementIn i × TypeTree.Path (ctx₁ i))
      (fun shared => ctx₂ shared.1 shared.2.2)
      (fun shared => roles₂ shared.1 shared.2.2)
      (fun shared => StmtMid shared.1 shared.2.2)
      (fun shared => WitMid shared.1 shared.2.2)
      (fun shared tr₂ => StmtOut shared.1 shared.2.2 tr₂)
      (fun shared tr₂ => WitOut shared.1 shared.2.2 tr₂)) :
    Reduction m SharedIn
      (fun i => (ctx₁ i).append (ctx₂ i))
      (fun i => (roles₁ i).append (fun tr₁ => roles₂ i tr₁))
      StatementIn WitnessIn
      (fun i => PFunctor.FreeM.Path.liftAppend (ctx₁ i) (ctx₂ i) (StmtOut i))
      (fun i => PFunctor.FreeM.Path.liftAppend (ctx₁ i) (ctx₂ i) (WitOut i)) where
  prover i stmt wit := do
    let strategy₁ ← reduction₁.prover i stmt wit
    let strategy ← StrategyOver.TwoParty.Focal.comp strategy₁ (fun tr₁ midOut =>
      reduction₂.prover ⟨i, stmt, tr₁⟩ midOut.stmt midOut.wit)
    pure <| StrategyOver.TwoParty.Focal.mapOutput
      (HonestProverOutput.splitLiftAppend (ctx₁ i) (ctx₂ i) (StmtOut i) (WitOut i))
      strategy
  verifier i stmt :=
    StrategyOver.TwoParty.Counterpart.append (reduction₁.verifier i stmt) (fun tr₁ stmtMid =>
      reduction₂.verifier ⟨i, stmt, tr₁⟩ stmtMid)

/-- Executing a composed reduction factors into prefix execution and its path-indexed suffix.

The final `splitLiftAppendRun` map only converts PolyFun's factored honest-prover payload into
ArkLib's separately lifted statement and witness outputs. All interaction effects occur in the two
executions inside the mapped computation. General effectful suffix construction requires
`TwoParty.LawfulCommMonad`; use PolyFun's `TwoParty.run_compFlat_appendFlat_pure` when the suffix
constructor is pure and only `LawfulMonad` is available. -/
theorem Reduction.execute_comp
    {m : Type u → Type u} [Monad m] [TwoParty.LawfulCommMonad m]
    {SharedIn : Type v}
    {StatementIn : SharedIn → Type w}
    {WitnessIn : SharedIn → Type x}
    {ctx₁ : SharedIn → TypeTree}
    {roles₁ : (i : SharedIn) → RoleDecoration (ctx₁ i)}
    {StmtMid WitMid : (i : SharedIn) → TypeTree.Path (ctx₁ i) → Type u}
    {ctx₂ : (i : SharedIn) → TypeTree.Path (ctx₁ i) → TypeTree}
    {roles₂ : (i : SharedIn) → (tr₁ : TypeTree.Path (ctx₁ i)) →
      RoleDecoration (ctx₂ i tr₁)}
    {StmtOut WitOut : (i : SharedIn) → (tr₁ : TypeTree.Path (ctx₁ i)) →
      TypeTree.Path (ctx₂ i tr₁) → Type u}
    (reduction₁ : Reduction m SharedIn ctx₁ roles₁ StatementIn WitnessIn StmtMid WitMid)
    (reduction₂ : Reduction m
      ((i : SharedIn) × StatementIn i × TypeTree.Path (ctx₁ i))
      (fun shared => ctx₂ shared.1 shared.2.2)
      (fun shared => roles₂ shared.1 shared.2.2)
      (fun shared => StmtMid shared.1 shared.2.2)
      (fun shared => WitMid shared.1 shared.2.2)
      (fun shared tr₂ => StmtOut shared.1 shared.2.2 tr₂)
      (fun shared tr₂ => WitOut shared.1 shared.2.2 tr₂))
    (i : SharedIn) (stmt : StatementIn i) (wit : WitnessIn i) :
    (Reduction.comp reduction₁ reduction₂).execute i stmt wit =
      HonestProverOutput.splitLiftAppendRun
        (ctx₁ i) (ctx₂ i) (StmtOut i) (WitOut i) <$> (do
        let ⟨tr₁, midOut, stmtMid⟩ ← reduction₁.execute i stmt wit
        let strategy₂ ← reduction₂.prover ⟨i, stmt, tr₁⟩ midOut.stmt midOut.wit
        let ⟨tr₂, out, stmtOut⟩ ←
          TwoParty.run (ctx₂ i tr₁) (roles₂ i tr₁) strategy₂
            (reduction₂.verifier ⟨i, stmt, tr₁⟩ stmtMid)
        pure ⟨PFunctor.FreeM.Path.append (ctx₁ i) (ctx₂ i) tr₁ tr₂,
          PFunctor.FreeM.Path.packAppend (ctx₁ i) (ctx₂ i)
            (fun tr₁ tr₂ => HonestProverOutput (StmtOut i tr₁ tr₂) (WitOut i tr₁ tr₂))
            tr₁ tr₂ out,
          PFunctor.FreeM.Path.packAppend (ctx₁ i) (ctx₂ i) (fun tr₁ tr₂ => StmtOut i tr₁ tr₂)
            tr₁ tr₂ stmtOut⟩) := by
  simp only [execute, comp, bind_assoc, pure_bind, map_bind, map_pure]
  refine congrArg (fun k => reduction₁.prover i stmt wit >>= k) ?_
  funext strategy₁
  let mapOut := HonestProverOutput.splitLiftAppend
    (ctx₁ i) (ctx₂ i) (StmtOut i) (WitOut i)
  let mapRun :
      ((tr : TypeTree.Path ((ctx₁ i).append (ctx₂ i))) ×
        PFunctor.FreeM.Path.liftAppend (ctx₁ i) (ctx₂ i)
          (fun tr₁ tr₂ => HonestProverOutput (StmtOut i tr₁ tr₂) (WitOut i tr₁ tr₂)) tr ×
        PFunctor.FreeM.Path.liftAppend (ctx₁ i) (ctx₂ i) (StmtOut i) tr) →
      ((tr : TypeTree.Path ((ctx₁ i).append (ctx₂ i))) ×
        HonestProverOutput
          (PFunctor.FreeM.Path.liftAppend (ctx₁ i) (ctx₂ i) (StmtOut i) tr)
          (PFunctor.FreeM.Path.liftAppend (ctx₁ i) (ctx₂ i) (WitOut i) tr) ×
        PFunctor.FreeM.Path.liftAppend (ctx₁ i) (ctx₂ i) (StmtOut i) tr) :=
    HonestProverOutput.splitLiftAppendRun
      (ctx₁ i) (ctx₂ i) (StmtOut i) (WitOut i)
  let counterpart := StrategyOver.TwoParty.Counterpart.append
    (reduction₁.verifier i stmt) (fun tr₁ stmtMid =>
      reduction₂.verifier ⟨i, stmt, tr₁⟩ stmtMid)
  have hmap :
      (do
        let strategy ← StrategyOver.TwoParty.Focal.comp strategy₁ (fun tr₁ midOut =>
          reduction₂.prover ⟨i, stmt, tr₁⟩ midOut.stmt midOut.wit)
        TwoParty.run ((ctx₁ i).append (ctx₂ i))
          ((roles₁ i).append (fun tr₁ => roles₂ i tr₁))
          (StrategyOver.TwoParty.Focal.mapOutput mapOut strategy) counterpart) =
        (do
          let strategy ← StrategyOver.TwoParty.Focal.comp strategy₁ (fun tr₁ midOut =>
            reduction₂.prover ⟨i, stmt, tr₁⟩ midOut.stmt midOut.wit)
          mapRun <$>
            TwoParty.run ((ctx₁ i).append (ctx₂ i))
            ((roles₁ i).append (fun tr₁ => roles₂ i tr₁)) strategy counterpart) := by
    refine congrArg
      (fun k => StrategyOver.TwoParty.Focal.comp strategy₁ (fun tr₁ midOut =>
        reduction₂.prover ⟨i, stmt, tr₁⟩ midOut.stmt midOut.wit) >>= k) ?_
    funext strategy
    have mapRun_eq : mapRun =
        fun z => ⟨z.1, mapOut z.1 z.2.1, z.2.2⟩ := rfl
    rw [mapRun_eq]
    simpa only [StrategyOver.TwoParty.Counterpart.mapOutput_id] using
      (TwoParty.run_mapOutput_mapOutput
        (fP := mapOut) (fC := fun _ out => out) strategy counterpart)
  rw [hmap]
  convert congrArg (fun run => mapRun <$> run) (TwoParty.run_comp_append
      (r₂ := fun tr₁ => roles₂ i tr₁)
      (FP := fun tr₁ tr₂ => HonestProverOutput (StmtOut i tr₁ tr₂) (WitOut i tr₁ tr₂))
      (FC := fun tr₁ tr₂ => StmtOut i tr₁ tr₂)
      (strat₁ := strategy₁)
      (f := fun tr₁ midOut => reduction₂.prover ⟨i, stmt, tr₁⟩ midOut.stmt midOut.wit)
      (cpt₁ := reduction₁.verifier i stmt)
      (cpt₂ := fun tr₁ stmtMid => reduction₂.verifier ⟨i, stmt, tr₁⟩ stmtMid)) using 1 <;>
    simp only [mapRun, counterpart, map_bind, map_pure] <;> rfl

end Interaction

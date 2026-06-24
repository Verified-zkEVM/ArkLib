/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import PolyFun.Interaction.Basic.Spec
import PolyFun.Interaction.TwoParty.Compose
import ArkLib.Interaction.Compat
import ArkLib.Interaction.RoleChain

open Interaction.TwoParty

/-!
# Provers, Verifiers, and Reductions

Interactive protocol participants and their composition, built on `Spec` with
a `RoleDecoration`. This module replaces the old `OracleReduction/Basic.lean`
flat-list model with one natively built on the W-type interaction tree.

## Type architecture

The canonical interaction object is indexed by:

- `SharedIn` — ambient input fixing the protocol context
- `StatementIn : SharedIn → Type` — carried local statement/state interpreted inside
  the protocol fixed by `SharedIn`
- `WitnessIn : SharedIn → Type` — carried prover-local witness/state
- `Context : SharedIn → Spec` — protocol spec depends on the ambient input
- `Roles : (i : SharedIn) → RoleDecoration (Context i)` — roles per input
- `StatementOut : (i : SharedIn) → Spec.Transcript (Context i) → Type`
- `WitnessOut : (i : SharedIn) → Spec.Transcript (Context i) → Type`

This unifies both top-level protocols and suffix/continuation protocols.
Ordinary top-level protocols are the special case `StatementIn := fun _ => PUnit`;
mid-protocol suffixes use `SharedIn` for ambient setup or prefix transcript data
and `StatementIn` for the carried local state inside that fixed protocol.

SharedIn and output are represented as:
- **SharedIn**: `Σ i, StatementIn i × WitnessIn i`
- **Honest prover output**: `HonestProverOutput (StatementOut i tr) (WitnessOut i tr)`

## Participants

- **Prover**: monadic setup producing a role-dependent `Strategy` whose output is
  `HonestProverOutput StatementOut WitnessOut`.
- **Verifier**: a `SharedIn`-indexed, `StatementIn`-parameterized counterpart
  strategy with `StatementOut` at `.done`. No `OptionT` — acceptance semantics (if
  needed) are chosen by the caller through the `StatementOut` type
  (e.g., `StatementOut = fun _ _ => Option Bool`).
- **PublicCoinVerifier**: a stronger verifier surface whose receiver nodes are
  replayable public-coin continuations, expressed as a `StrategyOver` over
  `PublicCoinCounterpart.syntax`, used by the interaction-native
  Fiat-Shamir transform.
- **Reduction**: pairs a prover with a verifier for the same protocol spec.
- **PublicCoinReduction**: pairs a prover with a public-coin verifier; forgetting
  the extra verifier structure recovers an ordinary `Reduction`.

Both `Prover` and `Verifier` are `abbrev`s (transparent type aliases) for
the underlying function types.

## Composition

Sequential composition is phrased directly at the canonical `Reduction` shape:
the second protocol is indexed by `(input, tr₁)`, where `tr₁` is the realized
prefix transcript. This subsumes the old continuation surface without requiring
a separate foundational object.

## Running a reduction

`Reduction.execute` runs the prover's strategy against the verifier (via
`TwoParty.run`), returning the transcript plus both outputs.

See `Security.lean` for completeness, soundness, and knowledge soundness
definitions built on this execution model.
-/

universe u v w

namespace Interaction

/-! ## Protocol participants -/

/-- Output produced by an honest prover: the next statement together with the
next witness to be forwarded by composition. -/
abbrev HonestProverOutput (StatementOut : Type u) (WitnessOut : Type v) :=
  StatementOut × WitnessOut

namespace HonestProverOutput

/-- Statement component of an honest prover output. -/
abbrev stmt {StatementOut : Type u} {WitnessOut : Type v}
    (out : HonestProverOutput StatementOut WitnessOut) : StatementOut :=
  out.1

/-- Witness component of an honest prover output. -/
abbrev wit {StatementOut : Type u} {WitnessOut : Type v}
    (out : HonestProverOutput StatementOut WitnessOut) : WitnessOut :=
  out.2

end HonestProverOutput

/-- A prover: given ambient input `i`, local statement `stmt`, and local witness
`wit`, performs monadic setup and produces a role-dependent strategy whose
output is `HonestProverOutput (StatementOut i tr) (WitnessOut i tr)`. -/
abbrev Prover (m : Type u → Type u)
    (SharedIn : Type v)
    (Context : SharedIn → Spec)
    (Roles : (i : SharedIn) → RoleDecoration (Context i))
    (StatementIn WitnessIn : SharedIn → Type w)
    (StatementOut WitnessOut : (i : SharedIn) → Spec.Transcript (Context i) → Type u) :=
  (i : SharedIn) → StatementIn i → WitnessIn i →
    m (Spec.StrategyOver m Interaction.TwoParty.Participant.focal
      (Context i) (Roles i)
      (fun tr => HonestProverOutput (StatementOut i tr) (WitnessOut i tr)))

/-- A verifier: given ambient input `i` and local statement `stmt`, provides the
counterpart strategy with `StatementOut i tr` at `.done`. No `OptionT` wrapping:
the caller chooses whether `StatementOut` includes `Option` for accept/reject
semantics. -/
abbrev Verifier (m : Type u → Type u)
    (SharedIn : Type v)
    (Context : SharedIn → Spec)
    (Roles : (i : SharedIn) → RoleDecoration (Context i))
    (StatementIn : SharedIn → Type w)
    (StatementOut : (i : SharedIn) → Spec.Transcript (Context i) → Type u) :=
  (i : SharedIn) → StatementIn i →
    Spec.StrategyOver m Interaction.TwoParty.Participant.counterpart
      (Context i) (Roles i) (fun tr => StatementOut i tr)

/-- A verifier whose receiver nodes are public-coin in the strong replayable
sense captured by `PublicCoinCounterpart.syntax`.

An ordinary `Verifier` is enough to execute a protocol, but not enough to
replay a prescribed receiver transcript: at a verifier node, the continuation
is hidden inside an opaque monadic sample. `PublicCoinVerifier` keeps the same
overall interface while strengthening receiver nodes so they expose both a
challenge sampler and a challenge-indexed continuation family. Forgetting this
extra structure recovers an ordinary `Verifier`.

The codomain uses `counterpartSyntax` from PolyFun; see `PublicCoinVerifier.replay` for
transcript replay. -/
abbrev PublicCoinVerifier (m : Type u → Type u)
    (SharedIn : Type v)
    (Context : SharedIn → Spec)
    (Roles : (i : SharedIn) → RoleDecoration (Context i))
    (StatementIn : SharedIn → Type w)
    (StatementOut : (i : SharedIn) → Spec.Transcript (Context i) → Type u) :=
  (i : SharedIn) → StatementIn i →
    _root_.Interaction.StrategyOver
      (_root_.Interaction.TwoParty.PublicCoinCounterpart.counterpartSyntax (m := m))
      PUnit.unit (Context i) (Roles i)
      (StatementOut i)

namespace PublicCoinVerifier

/-- Forget that a verifier is public-coin and view it as an ordinary verifier. -/
def toVerifier {m : Type u → Type u} [Monad m]
    {SharedIn : Type v}
    {Context : SharedIn → Spec}
    {Roles : (i : SharedIn) → RoleDecoration (Context i)}
    {StatementIn : SharedIn → Type w}
    {StatementOut : (i : SharedIn) → Spec.Transcript (Context i) → Type u}
    (verifier : PublicCoinVerifier m SharedIn Context Roles StatementIn StatementOut) :
    Verifier m SharedIn Context Roles StatementIn StatementOut :=
  fun i stmt => TwoParty.PublicCoinCounterpart.toCounterpart (verifier i stmt)

/-- Replay a full transcript through a public-coin verifier. -/
def replay {m : Type u → Type u} [Monad m]
    {SharedIn : Type v}
    {Context : SharedIn → Spec}
    {Roles : (i : SharedIn) → RoleDecoration (Context i)}
    {StatementIn : SharedIn → Type w}
    {StatementOut : (i : SharedIn) → Spec.Transcript (Context i) → Type u}
    (verifier : PublicCoinVerifier m SharedIn Context Roles StatementIn StatementOut)
    (i : SharedIn) (stmt : StatementIn i) (tr : Spec.Transcript (Context i)) :
    m (StatementOut i tr) :=
  TwoParty.PublicCoinCounterpart.replay (verifier i stmt) tr

end PublicCoinVerifier

/-- A reduction pairs a prover with a verifier for the same protocol. -/
structure Reduction (m : Type u → Type u)
    (SharedIn : Type v)
    (Context : SharedIn → Spec)
    (Roles : (i : SharedIn) → RoleDecoration (Context i))
    (StatementIn WitnessIn : SharedIn → Type w)
    (StatementOut WitnessOut : (i : SharedIn) → Spec.Transcript (Context i) → Type u) where
  prover : Prover m SharedIn Context Roles StatementIn WitnessIn StatementOut WitnessOut
  verifier : Verifier m SharedIn Context Roles StatementIn StatementOut

/-- A reduction whose verifier is public-coin in the replayable sense of
`PublicCoinVerifier`. The prover is unchanged; only the verifier carries the
extra structure needed by verifier-side Fiat-Shamir. -/
structure PublicCoinReduction (m : Type u → Type u)
    (SharedIn : Type v)
    (Context : SharedIn → Spec)
    (Roles : (i : SharedIn) → RoleDecoration (Context i))
    (StatementIn WitnessIn : SharedIn → Type w)
    (StatementOut WitnessOut : (i : SharedIn) → Spec.Transcript (Context i) → Type u) where
  prover : Prover m SharedIn Context Roles StatementIn WitnessIn StatementOut WitnessOut
  verifier : PublicCoinVerifier m SharedIn Context Roles StatementIn StatementOut

namespace PublicCoinReduction

/-- Forget that a reduction is public-coin and recover the underlying ordinary
interactive reduction. -/
def toReduction {m : Type u → Type u} [Monad m]
    {SharedIn : Type v}
    {Context : SharedIn → Spec}
    {Roles : (i : SharedIn) → RoleDecoration (Context i)}
    {StatementIn WitnessIn : SharedIn → Type w}
    {StatementOut : (i : SharedIn) → Spec.Transcript (Context i) → Type u}
    {WitnessOut : (i : SharedIn) → Spec.Transcript (Context i) → Type u}
    (reduction :
      PublicCoinReduction m SharedIn Context Roles StatementIn WitnessIn StatementOut WitnessOut) :
    Reduction m SharedIn Context Roles StatementIn WitnessIn StatementOut WitnessOut where
  prover := reduction.prover
  verifier := reduction.verifier.toVerifier

end PublicCoinReduction

/-- A proof system is a reduction where the prover does not forward any
witness to the next stage (`WitnessOut = PUnit`). Accept/reject semantics
are not fixed here — they are determined by the choice of `StatementOut`
(e.g., `Bool`, `Option _`) and the security definitions. Its honest prover
output is `HonestProverOutput StatementOut PUnit`. -/
abbrev Proof (m : Type u → Type u)
    (SharedIn : Type v)
    (Context : SharedIn → Spec)
    (Roles : (i : SharedIn) → RoleDecoration (Context i))
    (StatementIn WitnessIn : SharedIn → Type w)
    (StatementOut : (i : SharedIn) → Spec.Transcript (Context i) → Type u) :=
  Reduction m SharedIn Context Roles StatementIn WitnessIn StatementOut (fun _ _ => PUnit)

/-! ## Execution -/

/-- Execute a reduction: run the prover's strategy against the verifier's
counterpart (via `TwoParty.run`). Returns the transcript, the
 prover's output (`HonestProverOutput StatementOut WitnessOut`), and the verifier's output
 (`StatementOut`). -/
def Reduction.execute {m : Type u → Type u} [Monad m]
    {SharedIn : Type v}
    {Context : SharedIn → Spec}
    {Roles : (i : SharedIn) → RoleDecoration (Context i)}
    {StatementIn WitnessIn : SharedIn → Type w}
    {StatementOut WitnessOut : (i : SharedIn) → Spec.Transcript (Context i) → Type u}
    (reduction : Reduction m SharedIn Context Roles StatementIn WitnessIn StatementOut WitnessOut)
    (i : SharedIn) (stmt : StatementIn i) (wit : WitnessIn i) :
    m ((tr : Spec.Transcript (Context i)) ×
       HonestProverOutput (StatementOut i tr) (WitnessOut i tr) ×
         StatementOut i tr) := do
  let strategy ← reduction.prover i stmt wit
  TwoParty.run (Context i) (Roles i) strategy (reduction.verifier i stmt)

/-- Run a prover strategy against a verifier. Convenience wrapper around
`TwoParty.run` that applies the input-indexed verifier. -/
def Verifier.run {m : Type u → Type u} [Monad m]
    {SharedIn : Type v}
    {Context : SharedIn → Spec}
    {Roles : (i : SharedIn) → RoleDecoration (Context i)}
    {StatementIn : SharedIn → Type w}
    {StatementOut : (i : SharedIn) → Spec.Transcript (Context i) → Type u}
    (v : Verifier m SharedIn Context Roles StatementIn StatementOut)
    (i : SharedIn)
    (stmt : StatementIn i)
    {OutputP : Spec.Transcript (Context i) → Type u}
    (prover : Spec.StrategyOver m Interaction.TwoParty.Participant.focal
      (Context i) (Roles i) OutputP) :
    m ((tr : Spec.Transcript (Context i)) × OutputP tr × StatementOut i tr) :=
  TwoParty.run (Context i) (Roles i) prover (v i stmt)

/-! ## Sequential composition -/

/-- Compose a reduction with a transcript-indexed continuation reduction.
The first reduction runs over `ctx₁`, producing intermediate outputs `StmtMid` and
`WitMid`. These feed into `reduction2`, whose protocol `ctx₂` may depend on the
first transcript. The composed output types are factored two-argument families,
lifted through `Transcript.liftAppend`. -/
def Reduction.comp {m : Type u → Type u} [Monad m]
    {SharedIn : Type v}
    {StatementIn : SharedIn → Type w}
    {WitnessIn : SharedIn → Type w}
    {ctx₁ : SharedIn → Spec}
    {roles₁ : (i : SharedIn) → RoleDecoration (ctx₁ i)}
    {StmtMid WitMid : (i : SharedIn) → Spec.Transcript (ctx₁ i) → Type u}
    {ctx₂ : (i : SharedIn) → Spec.Transcript (ctx₁ i) → Spec}
    {roles₂ : (i : SharedIn) → (tr₁ : Spec.Transcript (ctx₁ i)) →
      RoleDecoration (ctx₂ i tr₁)}
    {StmtOut WitOut : (i : SharedIn) → (tr₁ : Spec.Transcript (ctx₁ i)) →
      Spec.Transcript (ctx₂ i tr₁) → Type u}
    (reduction1 : Reduction m SharedIn ctx₁ roles₁ StatementIn WitnessIn StmtMid WitMid)
    (reduction2 : Reduction m
      ((i : SharedIn) × StatementIn i × Spec.Transcript (ctx₁ i))
      (fun shared => ctx₂ shared.1 shared.2.2)
      (fun shared => roles₂ shared.1 shared.2.2)
      (fun shared => StmtMid shared.1 shared.2.2)
      (fun shared => WitMid shared.1 shared.2.2)
      (fun shared tr₂ => StmtOut shared.1 shared.2.2 tr₂)
      (fun shared tr₂ => WitOut shared.1 shared.2.2 tr₂)) :
    Reduction m SharedIn
      (fun i => (ctx₁ i).append (ctx₂ i))
      (fun i => (roles₁ i).append (roles₂ i))
      StatementIn
      WitnessIn
      (fun i => Spec.Transcript.liftAppend (ctx₁ i) (ctx₂ i) (StmtOut i))
      (fun i => Spec.Transcript.liftAppend (ctx₁ i) (ctx₂ i) (WitOut i)) where
  prover i stmt w := do
    let strat₁ ← reduction1.prover i stmt w
    let strat ← StrategyOver.TwoParty.Focal.comp strat₁ (fun tr₁ midOut =>
      reduction2.prover ⟨i, stmt, tr₁⟩ midOut.stmt midOut.wit)
    pure <| StrategyOver.TwoParty.Focal.mapOutput
      (fun tr out =>
        let ⟨stmt, wit⟩ :=
          Spec.Transcript.liftAppendProd (ctx₁ i) (ctx₂ i)
            (fun tr₁ tr₂ => StmtOut i tr₁ tr₂) (fun tr₁ tr₂ => WitOut i tr₁ tr₂) tr out
        ⟨stmt, wit⟩)
      strat
  verifier i stmt :=
    StrategyOver.TwoParty.Counterpart.append (reduction1.verifier i stmt) (fun tr₁ sMid =>
      reduction2.verifier ⟨i, stmt, tr₁⟩ sMid)

/-- Executing a sequentially composed reduction factors into first executing the
prefix reduction and then the suffix interaction induced by its outputs. -/
theorem Reduction.execute_comp
    {m : Type u → Type u} [Monad m] [TwoParty.LawfulCommMonad m]
    {SharedIn : Type v}
    {StatementIn : SharedIn → Type w}
    {WitnessIn : SharedIn → Type w}
    {ctx₁ : SharedIn → Spec}
    {roles₁ : (i : SharedIn) → RoleDecoration (ctx₁ i)}
    {StmtMid WitMid : (i : SharedIn) → Spec.Transcript (ctx₁ i) → Type u}
    {ctx₂ : (i : SharedIn) → Spec.Transcript (ctx₁ i) → Spec}
    {roles₂ : (i : SharedIn) → (tr₁ : Spec.Transcript (ctx₁ i)) →
      RoleDecoration (ctx₂ i tr₁)}
    {StmtOut WitOut : (i : SharedIn) → (tr₁ : Spec.Transcript (ctx₁ i)) →
      Spec.Transcript (ctx₂ i tr₁) → Type u}
    (reduction1 : Reduction m SharedIn ctx₁ roles₁ StatementIn WitnessIn StmtMid WitMid)
    (reduction2 : Reduction m
      ((i : SharedIn) × StatementIn i × Spec.Transcript (ctx₁ i))
      (fun shared => ctx₂ shared.1 shared.2.2)
      (fun shared => roles₂ shared.1 shared.2.2)
      (fun shared => StmtMid shared.1 shared.2.2)
      (fun shared => WitMid shared.1 shared.2.2)
      (fun shared tr₂ => StmtOut shared.1 shared.2.2 tr₂)
      (fun shared tr₂ => WitOut shared.1 shared.2.2 tr₂))
    (i : SharedIn) (stmt : StatementIn i) (w : WitnessIn i) :
    (Reduction.comp reduction1 reduction2).execute i stmt w =
      (do
        let ⟨tr₁, midOut, sMid⟩ ← reduction1.execute i stmt w
        let strat₂ ← reduction2.prover ⟨i, stmt, tr₁⟩ midOut.stmt midOut.wit
        let ⟨tr₂, out, sOut⟩ ←
          TwoParty.run (ctx₂ i tr₁) (roles₂ i tr₁) strat₂
            (reduction2.verifier ⟨i, stmt, tr₁⟩ sMid)
        pure ⟨Spec.Transcript.append (ctx₁ i) (ctx₂ i) tr₁ tr₂,
          ⟨Spec.Transcript.packAppend (ctx₁ i) (ctx₂ i) (StmtOut i) tr₁ tr₂ out.stmt,
            Spec.Transcript.packAppend (ctx₁ i) (ctx₂ i) (WitOut i) tr₁ tr₂ out.wit⟩,
          Spec.Transcript.packAppend (ctx₁ i) (ctx₂ i) (StmtOut i) tr₁ tr₂ sOut⟩) := by
  simp only [execute, comp, bind_assoc, pure_bind]
  refine congrArg (fun k => reduction1.prover i stmt w >>= k) ?_
  funext strat₁
  let mapOut :
      (tr : Spec.Transcript ((ctx₁ i).append (ctx₂ i))) →
      Spec.Transcript.liftAppend (ctx₁ i) (ctx₂ i)
        (fun tr₁ tr₂ => HonestProverOutput (StmtOut i tr₁ tr₂) (WitOut i tr₁ tr₂)) tr →
      HonestProverOutput
        (Spec.Transcript.liftAppend (ctx₁ i) (ctx₂ i) (StmtOut i) tr)
        (Spec.Transcript.liftAppend (ctx₁ i) (ctx₂ i) (WitOut i) tr) :=
    fun tr out =>
      let ⟨stmt, wit⟩ :=
        Spec.Transcript.liftAppendProd (ctx₁ i) (ctx₂ i) (StmtOut i) (WitOut i) tr out
      ⟨stmt, wit⟩
  let mapTriple :
      ((tr : Spec.Transcript ((ctx₁ i).append (ctx₂ i))) ×
        Spec.Transcript.liftAppend (ctx₁ i) (ctx₂ i)
          (fun tr₁ tr₂ => HonestProverOutput (StmtOut i tr₁ tr₂) (WitOut i tr₁ tr₂)) tr ×
        Spec.Transcript.liftAppend (ctx₁ i) (ctx₂ i) (StmtOut i) tr) →
      ((tr : Spec.Transcript ((ctx₁ i).append (ctx₂ i))) ×
        HonestProverOutput
          (Spec.Transcript.liftAppend (ctx₁ i) (ctx₂ i) (StmtOut i) tr)
          (Spec.Transcript.liftAppend (ctx₁ i) (ctx₂ i) (WitOut i) tr) ×
        Spec.Transcript.liftAppend (ctx₁ i) (ctx₂ i) (StmtOut i) tr) :=
    fun z => ⟨z.1, mapOut z.1 z.2.1, z.2.2⟩
  have hmap :
      (do
        let strat ← StrategyOver.TwoParty.Focal.comp strat₁
          (fun tr₁ midOut => reduction2.prover ⟨i, stmt, tr₁⟩ midOut.stmt midOut.wit)
        TwoParty.run ((ctx₁ i).append (ctx₂ i)) ((roles₁ i).append (roles₂ i))
          (StrategyOver.TwoParty.Focal.mapOutput mapOut strat)
          (StrategyOver.TwoParty.Counterpart.append (reduction1.verifier i stmt)
            (fun tr₁ sMid => reduction2.verifier ⟨i, stmt, tr₁⟩ sMid))) =
        mapTriple <$>
          (do
            let strat ← StrategyOver.TwoParty.Focal.comp strat₁
              (fun tr₁ midOut => reduction2.prover ⟨i, stmt, tr₁⟩ midOut.stmt midOut.wit)
            TwoParty.run ((ctx₁ i).append (ctx₂ i)) ((roles₁ i).append (roles₂ i))
              strat
                (StrategyOver.TwoParty.Counterpart.append (reduction1.verifier i stmt)
                  (fun tr₁ sMid => reduction2.verifier ⟨i, stmt, tr₁⟩ sMid))) := by
    have hraw :
        (do
          let strat ← StrategyOver.TwoParty.Focal.comp strat₁
            (fun tr₁ midOut => reduction2.prover ⟨i, stmt, tr₁⟩ midOut.stmt midOut.wit)
          TwoParty.run ((ctx₁ i).append (ctx₂ i)) ((roles₁ i).append (roles₂ i))
            (StrategyOver.TwoParty.Focal.mapOutput mapOut strat)
            (StrategyOver.TwoParty.Counterpart.append (reduction1.verifier i stmt)
              (fun tr₁ sMid => reduction2.verifier ⟨i, stmt, tr₁⟩ sMid))) =
          (do
            let strat ← StrategyOver.TwoParty.Focal.comp strat₁
              (fun tr₁ midOut => reduction2.prover ⟨i, stmt, tr₁⟩ midOut.stmt midOut.wit)
            mapTriple <$>
              TwoParty.run ((ctx₁ i).append (ctx₂ i)) ((roles₁ i).append (roles₂ i))
                strat
                (StrategyOver.TwoParty.Counterpart.append (reduction1.verifier i stmt)
                  (fun tr₁ sMid => reduction2.verifier ⟨i, stmt, tr₁⟩ sMid))) := by
      refine congrArg
        (fun k =>
          StrategyOver.TwoParty.Focal.comp strat₁
            (fun tr₁ midOut => reduction2.prover ⟨i, stmt, tr₁⟩ midOut.stmt midOut.wit) >>= k) ?_
      funext strat
      simpa [mapTriple, mapOut, StrategyOver.TwoParty.Counterpart.mapOutput_id] using
        (TwoParty.run_mapOutput_mapOutput
          (fP := mapOut) (fC := fun _ x => x) strat
          (StrategyOver.TwoParty.Counterpart.append (reduction1.verifier i stmt)
            (fun tr₁ sMid => reduction2.verifier ⟨i, stmt, tr₁⟩ sMid)))
    calc
      (do
        let strat ← StrategyOver.TwoParty.Focal.comp strat₁
          (fun tr₁ midOut => reduction2.prover ⟨i, stmt, tr₁⟩ midOut.stmt midOut.wit)
        TwoParty.run ((ctx₁ i).append (ctx₂ i)) ((roles₁ i).append (roles₂ i))
          (StrategyOver.TwoParty.Focal.mapOutput mapOut strat)
          (StrategyOver.TwoParty.Counterpart.append (reduction1.verifier i stmt)
            (fun tr₁ sMid => reduction2.verifier ⟨i, stmt, tr₁⟩ sMid))) =
          (do
            let strat ← StrategyOver.TwoParty.Focal.comp strat₁
              (fun tr₁ midOut => reduction2.prover ⟨i, stmt, tr₁⟩ midOut.stmt midOut.wit)
            mapTriple <$>
              TwoParty.run ((ctx₁ i).append (ctx₂ i)) ((roles₁ i).append (roles₂ i))
                strat
                (StrategyOver.TwoParty.Counterpart.append (reduction1.verifier i stmt)
                  (fun tr₁ sMid => reduction2.verifier ⟨i, stmt, tr₁⟩ sMid))) := hraw
      _ = mapTriple <$>
            (do
              let strat ← StrategyOver.TwoParty.Focal.comp strat₁
                (fun tr₁ midOut => reduction2.prover ⟨i, stmt, tr₁⟩ midOut.stmt midOut.wit)
              TwoParty.run ((ctx₁ i).append (ctx₂ i)) ((roles₁ i).append (roles₂ i))
                strat
                (StrategyOver.TwoParty.Counterpart.append (reduction1.verifier i stmt)
                  (fun tr₁ sMid => reduction2.verifier ⟨i, stmt, tr₁⟩ sMid))) := by
        simp
  rw [hmap]
  simpa [mapTriple, mapOut, bind_assoc] using
    congrArg (fun mx => mapTriple <$> mx)
      (TwoParty.run_comp_append
        (strat₁ := strat₁)
        (f := fun tr₁ midOut => reduction2.prover ⟨i, stmt, tr₁⟩ midOut.stmt midOut.wit)
        (cpt₁ := reduction1.verifier i stmt)
        (cpt₂ := fun tr₁ sMid => reduction2.verifier ⟨i, stmt, tr₁⟩ sMid))

/-! ## Chain-based reduction composition -/

/-- Compose concrete-chain prover and verifier handlers into a full `Reduction`
over an `n`-round `RoleChain`, threading separate prover and verifier state
families indexed by the remaining decorated chain. -/
def Reduction.ofChain {m : Type u → Type u} [Monad m]
    {SharedIn : Type v}
    {StatementIn : SharedIn → Type w}
    {WitnessIn : SharedIn → Type w}
    {n : Nat}
    {c : SharedIn → Spec.RoleChain.{u} n}
    {StatementOut WitnessOut : (i : SharedIn) →
      Spec.Transcript (Spec.RoleChain.toSpec n (c i)) → Type u}
    (ProverState : (i : SharedIn) → {k : Nat} → Spec.RoleChain.{u} k → Type u)
    (VerifierState : (i : SharedIn) → {k : Nat} → Spec.RoleChain.{u} k → Type u)
    (proverInit : (i : SharedIn) → StatementIn i → WitnessIn i → ProverState i (c i))
    (verifierInit : (i : SharedIn) → StatementIn i → VerifierState i (c i))
    (proverSteps : (i : SharedIn) →
      Spec.Strategy.RoundSteps (m := m) (ProverState i) n (c i))
    (verifierSteps : (i : SharedIn) →
      Spec.Counterpart.RoundSteps (m := m) (VerifierState i) n (c i))
    (proverStmtResult : (i : SharedIn) →
      (tr : Spec.Transcript (Spec.RoleChain.toSpec n (c i))) →
        Spec.RoleChain.outputFamily (ProverState i) n (c i) tr → StatementOut i tr)
    (verifierStmtResult : (i : SharedIn) →
      (tr : Spec.Transcript (Spec.RoleChain.toSpec n (c i))) →
        Spec.RoleChain.outputFamily (VerifierState i) n (c i) tr → StatementOut i tr)
    (witResult : (i : SharedIn) →
      (tr : Spec.Transcript (Spec.RoleChain.toSpec n (c i))) →
        Spec.RoleChain.outputFamily (ProverState i) n (c i) tr → WitnessOut i tr) :
    Reduction m SharedIn
      (fun i => Spec.RoleChain.toSpec n (c i))
      (fun i => Spec.RoleChain.toRoles n (c i))
      StatementIn
      WitnessIn
      StatementOut WitnessOut where
  prover i stmt w := do
    let strat ← Spec.Strategy.ofChain
      (ProverState i) n (c i) (proverInit i stmt w) (proverSteps i)
    pure <| StrategyOver.TwoParty.Focal.mapOutput
      (fun tr state => ⟨proverStmtResult i tr state, witResult i tr state⟩) strat
  verifier i stmt :=
    StrategyOver.TwoParty.Counterpart.mapOutput (fun tr state => verifierStmtResult i tr state)
      (Spec.Counterpart.ofChain
        (VerifierState i) n (c i) (verifierInit i stmt) (verifierSteps i))

end Interaction


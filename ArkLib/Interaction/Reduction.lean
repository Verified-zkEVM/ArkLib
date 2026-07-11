/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import PolyFun.Interaction.Basic.Spec
import PolyFun.Interaction.Basic.Chain
import PolyFun.Interaction.TwoParty.Compose

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
- **Verifier**: an `SharedIn`-indexed, `StatementIn`-parameterized `Counterpart`
  with `StatementOut` at `.done`. No `OptionT` — acceptance semantics (if
  needed) are chosen by the caller through the `StatementOut` type
  (e.g., `StatementOut = fun _ _ => Option Bool`).
- **PublicCoinVerifier**: a stronger verifier surface whose receiver nodes are
  replayable public-coin continuations (`Spec.PublicCoinCounterpart`), used by
  the interaction-native Fiat-Shamir transform.
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
`Strategy.runWithRoles`), returning the transcript plus both outputs.

See `Security.lean` for completeness, soundness, and knowledge soundness
definitions built on this execution model.
-/

universe u v w

namespace Interaction

open TwoParty

/-! ## Compatibility aliases for the PolyFun v4.30 interaction API -/

namespace Spec

namespace Transcript

abbrev append (s₁ : Spec) (s₂ : Transcript s₁ → Spec)
    (tr₁ : Transcript s₁) (tr₂ : Transcript (s₂ tr₁)) :
    Transcript (s₁.append s₂) :=
  PFunctor.FreeM.Path.append s₁ s₂ tr₁ tr₂

abbrev liftAppend (s₁ : Spec) (s₂ : Transcript s₁ → Spec)
    (F : (tr₁ : Transcript s₁) → Transcript (s₂ tr₁) → Type u)
    (tr : Transcript (s₁.append s₂)) : Type u :=
  PFunctor.FreeM.Path.liftAppend s₁ s₂ F tr

abbrev packAppend (s₁ : Spec) (s₂ : Transcript s₁ → Spec)
    (F : (tr₁ : Transcript s₁) → Transcript (s₂ tr₁) → Type u)
    (tr₁ : Transcript s₁) (tr₂ : Transcript (s₂ tr₁))
    (x : F tr₁ tr₂) :
    liftAppend s₁ s₂ F (append s₁ s₂ tr₁ tr₂) :=
  PFunctor.FreeM.Path.packAppend s₁ s₂ F tr₁ tr₂ x

abbrev liftAppendProd (s₁ : Spec) (s₂ : Transcript s₁ → Spec)
    (A B : (tr₁ : Transcript s₁) → Transcript (s₂ tr₁) → Type u)
    (tr : Transcript (s₁.append s₂))
    (x : liftAppend s₁ s₂ (fun tr₁ tr₂ => A tr₁ tr₂ × B tr₁ tr₂) tr) :
    liftAppend s₁ s₂ A tr × liftAppend s₁ s₂ B tr :=
  PFunctor.FreeM.Path.liftAppendProd s₁ s₂ A B tr x

abbrev stateChainFamily
    {Stage : Nat → Type u} {spec : (i : Nat) → Stage i → Spec}
    {advance : (i : Nat) → (s : Stage i) → Transcript (spec i s) → Stage (i + 1)}
    (Family : (i : Nat) → Stage i → Type u)
    (n : Nat) (i : Nat) (stage : Stage i) :
    Transcript (Spec.stateChain Stage spec advance n i stage) → Type u :=
  PFunctor.FreeM.Path.stateChainFamily (advance := advance) Family n i stage

end Transcript

namespace Strategy

abbrev withRoles (m : Type u → Type u)
    (spec : Spec) (roles : RoleDecoration spec)
    (Output : Transcript spec → Type u) : Type u :=
  StrategyOver (SyntaxOver.TwoParty.pairedSpec m) Participant.focal spec roles Output

def runWithRoles {m : Type u → Type u} [Monad m]
    (spec : Spec) (roles : RoleDecoration spec)
    {OutputP OutputC : Transcript spec → Type u}
    (strat : withRoles m spec roles OutputP)
    (cpt : StrategyOver (SyntaxOver.TwoParty.pairedSpec m) Participant.counterpart
      spec roles OutputC) :
    m ((tr : Transcript spec) × OutputP tr × OutputC tr) :=
  TwoParty.run spec roles strat cpt

def compWithRoles {m : Type u → Type u} [Monad m]
    {s₁ : Spec} {s₂ : Transcript s₁ → Spec}
    {r₁ : RoleDecoration s₁}
    {r₂ : (tr₁ : Transcript s₁) → RoleDecoration (s₂ tr₁)}
    {Mid : Transcript s₁ → Type u}
    {F : (tr₁ : Transcript s₁) → Transcript (s₂ tr₁) → Type u}
    (strat₁ : withRoles m s₁ r₁ Mid)
    (f : (tr₁ : Transcript s₁) → Mid tr₁ → m (withRoles m (s₂ tr₁) (r₂ tr₁) (F tr₁))) :
    m (withRoles m (s₁.append s₂) (r₁.append r₂)
      (PFunctor.FreeM.Path.liftAppend s₁ s₂ F)) :=
  StrategyOver.TwoParty.Focal.comp strat₁ f

def compWithRolesFlat {m : Type u → Type u} [Monad m]
    {s₁ : Spec} {s₂ : Transcript s₁ → Spec}
    {r₁ : RoleDecoration s₁}
    {r₂ : (tr₁ : Transcript s₁) → RoleDecoration (s₂ tr₁)}
    {Mid : Transcript s₁ → Type u}
    {Output : Transcript (s₁.append s₂) → Type u}
    (strat₁ : withRoles m s₁ r₁ Mid)
    (f : (tr₁ : Transcript s₁) → Mid tr₁ →
      m (withRoles m (s₂ tr₁) (r₂ tr₁)
        (fun tr₂ => Output (PFunctor.FreeM.Path.append s₁ s₂ tr₁ tr₂)))) :
    m (withRoles m (s₁.append s₂) (r₁.append r₂) Output) :=
  StrategyOver.TwoParty.Focal.compFlat strat₁ f

def mapOutputWithRoles {m : Type u → Type u} [Functor m]
    {spec : Spec} {roles : RoleDecoration spec}
    {A B : Transcript spec → Type u}
    (f : ∀ tr, A tr → B tr)
    (strat : withRoles m spec roles A) :
    withRoles m spec roles B :=
  StrategyOver.TwoParty.Focal.mapOutput f strat

abbrev stateChainCompWithRoles {m : Type u → Type u} [Monad m]
    {Stage : Nat → Type u} {spec : (i : Nat) → Stage i → Spec}
    {advance : (i : Nat) → (s : Stage i) → Transcript (spec i s) → Stage (i + 1)}
    {roles : (i : Nat) → (s : Stage i) → RoleDecoration (spec i s)}
    {Family : (i : Nat) → Stage i → Type u}
    (step : (i : Nat) → (s : Stage i) → Family i s →
      m (withRoles m (spec i s) (roles i s)
        (fun tr => Family (i + 1) (advance i s tr)))) :=
  StrategyOver.TwoParty.Focal.stateChainComp
    (advance := advance) (roles := roles) (Family := Family) step

theorem runWithRoles_mapOutputWithRoles_mapOutput
    {m : Type u → Type u} [Monad m] [LawfulMonad m]
    {spec : Spec} {roles : RoleDecoration spec}
    {OutputP OutputP' OutputC OutputC' : Transcript spec → Type u}
    (fP : ∀ tr, OutputP tr → OutputP' tr)
    (fC : ∀ tr, OutputC tr → OutputC' tr)
    (strat : withRoles m spec roles OutputP)
    (cpt : StrategyOver (SyntaxOver.TwoParty.pairedSpec m) Participant.counterpart
      spec roles OutputC) :
    runWithRoles spec roles (mapOutputWithRoles fP strat)
      (StrategyOver.TwoParty.Counterpart.mapOutput fC cpt) =
      (fun z => ⟨z.1, fP z.1 z.2.1, fC z.1 z.2.2⟩) <$>
        runWithRoles spec roles strat cpt :=
  TwoParty.run_mapOutput_mapOutput fP fC strat cpt

theorem runWithRoles_compWithRoles_append
    {m : Type u → Type u} [Monad m] [LawfulCommMonad m]
    {s₁ : Spec} {s₂ : Transcript s₁ → Spec}
    {r₁ : RoleDecoration s₁}
    {r₂ : (tr₁ : Transcript s₁) → RoleDecoration (s₂ tr₁)}
    {Mid OutputC : Transcript s₁ → Type u}
    {F : (tr₁ : Transcript s₁) → Transcript (s₂ tr₁) → Type u}
    {G : (tr₁ : Transcript s₁) → Transcript (s₂ tr₁) → Type u}
    (strat₁ : withRoles m s₁ r₁ Mid)
    (f : (tr₁ : Transcript s₁) → Mid tr₁ → m (withRoles m (s₂ tr₁) (r₂ tr₁) (F tr₁)))
    (cpt₁ : StrategyOver (SyntaxOver.TwoParty.pairedSpec m) Participant.counterpart
      s₁ r₁ OutputC)
    (cpt₂ : (tr₁ : Transcript s₁) → OutputC tr₁ →
      StrategyOver (SyntaxOver.TwoParty.pairedSpec m) Participant.counterpart
        (s₂ tr₁) (r₂ tr₁) (G tr₁)) :
    (do
      let strat ← compWithRoles strat₁ f
      runWithRoles (s₁.append s₂) (r₁.append r₂) strat
        (StrategyOver.TwoParty.Counterpart.append cpt₁ cpt₂)) =
      (do
        let ⟨tr₁, mid, outC⟩ ← runWithRoles s₁ r₁ strat₁ cpt₁
        let strat₂ ← f tr₁ mid
        let ⟨tr₂, outP, outC₂⟩ ← runWithRoles (s₂ tr₁) (r₂ tr₁) strat₂ (cpt₂ tr₁ outC)
        pure ⟨PFunctor.FreeM.Path.append s₁ s₂ tr₁ tr₂,
          PFunctor.FreeM.Path.packAppend s₁ s₂ F tr₁ tr₂ outP,
          PFunctor.FreeM.Path.packAppend s₁ s₂ G tr₁ tr₂ outC₂⟩) :=
  TwoParty.run_comp_append (strat₁ := strat₁) (f := f) (cpt₁ := cpt₁) (cpt₂ := cpt₂)

end Strategy

abbrev Counterpart (m : Type u → Type u)
    (spec : Spec) (roles : RoleDecoration spec)
    (Output : Transcript spec → Type u) : Type u :=
  StrategyOver (SyntaxOver.TwoParty.pairedSpec m) Participant.counterpart spec roles Output

namespace Counterpart

abbrev withMonads (spec : Spec) (roles : RoleDecoration spec)
    (md : MonadDecoration spec)
    (Output : Transcript spec → Type u) : Type u :=
  StrategyOver SyntaxOver.TwoParty.Counterpart.monadicSpec.{u + 1, u, u}
    (PUnit.unit : PUnit.{u + 1}) spec (RoleDecoration.withMonads roles md) Output

def append {m : Type u → Type u} [Monad m]
    {s₁ : Spec} {s₂ : Transcript s₁ → Spec}
    {r₁ : RoleDecoration s₁}
    {r₂ : (tr₁ : Transcript s₁) → RoleDecoration (s₂ tr₁)}
    {A : Transcript s₁ → Type u}
    {B : (tr₁ : Transcript s₁) → Transcript (s₂ tr₁) → Type u}
    (cpt₁ : Counterpart m s₁ r₁ A)
    (cpt₂ : (tr₁ : Transcript s₁) → A tr₁ → Counterpart m (s₂ tr₁) (r₂ tr₁) (B tr₁)) :
    Counterpart m (s₁.append s₂) (r₁.append r₂)
      (PFunctor.FreeM.Path.liftAppend s₁ s₂ B) :=
  StrategyOver.TwoParty.Counterpart.append cpt₁ cpt₂

def appendFlat {m : Type u → Type u} [Monad m]
    {s₁ : Spec} {s₂ : Transcript s₁ → Spec}
    {r₁ : RoleDecoration s₁}
    {r₂ : (tr₁ : Transcript s₁) → RoleDecoration (s₂ tr₁)}
    {A : Transcript s₁ → Type u}
    {Output : Transcript (s₁.append s₂) → Type u}
    (cpt₁ : Counterpart m s₁ r₁ A)
    (cpt₂ : (tr₁ : Transcript s₁) → A tr₁ → Counterpart m (s₂ tr₁) (r₂ tr₁)
      (fun tr₂ => Output (PFunctor.FreeM.Path.append s₁ s₂ tr₁ tr₂))) :
    Counterpart m (s₁.append s₂) (r₁.append r₂) Output :=
  StrategyOver.TwoParty.Counterpart.appendFlat cpt₁ cpt₂

def mapOutput {m : Type u → Type u} [Functor m]
    {spec : Spec} {roles : RoleDecoration spec}
    {A B : Transcript spec → Type u}
    (f : ∀ tr, A tr → B tr)
    (cpt : Counterpart m spec roles A) :
    Counterpart m spec roles B :=
  StrategyOver.TwoParty.Counterpart.mapOutput f cpt

abbrev stateChainComp {m : Type u → Type u} [Monad m]
    {Stage : Nat → Type u} {spec : (i : Nat) → Stage i → Spec}
    {advance : (i : Nat) → (s : Stage i) → Transcript (spec i s) → Stage (i + 1)}
    {roles : (i : Nat) → (s : Stage i) → RoleDecoration (spec i s)}
    {Family : (i : Nat) → Stage i → Type u}
    (step : (i : Nat) → (s : Stage i) → Family i s →
      Counterpart m (spec i s) (roles i s)
        (fun tr => Family (i + 1) (advance i s tr))) :=
  StrategyOver.TwoParty.Counterpart.stateChainComp
    (advance := advance) (roles := roles) (Family := Family) step

theorem mapOutput_id {m : Type u → Type u} [Functor m] [LawfulFunctor m]
    {spec : Spec} {roles : RoleDecoration spec} {A : Transcript spec → Type u}
    (cpt : Counterpart m spec roles A) :
    mapOutput (fun _ x => x) cpt = cpt :=
  StrategyOver.TwoParty.Counterpart.mapOutput_id cpt

end Counterpart

abbrev PublicCoinCounterpart (m : Type u → Type u)
    (spec : Spec) (roles : RoleDecoration spec)
    (Output : Transcript spec → Type u) : Type u :=
  StrategyOver (TwoParty.PublicCoinCounterpart.counterpartSyntax.{u, u + 1} m)
    (PUnit.unit : PUnit.{u + 2}) spec roles Output

namespace PublicCoinCounterpart

def toCounterpart {m : Type u → Type u} [Monad m]
    {spec : Spec} {roles : RoleDecoration spec} {Output : Transcript spec → Type u}
    (cpt : PublicCoinCounterpart m spec roles Output) :
    Counterpart m spec roles Output :=
  TwoParty.PublicCoinCounterpart.toCounterpart cpt

def replay {m : Type u → Type u} [Monad m]
    {spec : Spec} {roles : RoleDecoration spec} {Output : Transcript spec → Type u}
    (cpt : PublicCoinCounterpart m spec roles Output)
    (tr : Transcript spec) : m (Output tr) :=
  TwoParty.PublicCoinCounterpart.replay cpt tr

end PublicCoinCounterpart

abbrev LawfulCommMonad (m : Type u → Type u) [Monad m] :=
  TwoParty.LawfulCommMonad m

end Spec

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
    m (Spec.Strategy.withRoles m (Context i) (Roles i)
      (fun tr => HonestProverOutput (StatementOut i tr) (WitnessOut i tr)))

/-- A verifier: given ambient input `i` and local statement `stmt`, provides a
`Counterpart` with `StatementOut i tr` at `.done`. No `OptionT` wrapping — the
caller chooses whether `StatementOut` includes `Option` for accept/reject
semantics. -/
abbrev Verifier (m : Type u → Type u)
    (SharedIn : Type v)
    (Context : SharedIn → Spec)
    (Roles : (i : SharedIn) → RoleDecoration (Context i))
    (StatementIn : SharedIn → Type w)
    (StatementOut : (i : SharedIn) → Spec.Transcript (Context i) → Type u) :=
  (i : SharedIn) → StatementIn i →
    Spec.Counterpart m (Context i) (Roles i) (fun tr => StatementOut i tr)

/-- A verifier whose receiver nodes are public-coin in the strong replayable
sense captured by `Spec.PublicCoinCounterpart`.

An ordinary `Verifier` is enough to execute a protocol, but not enough to
replay a prescribed receiver transcript: at a verifier node, the continuation
is hidden inside an opaque monadic sample. `PublicCoinVerifier` keeps the same
overall interface while strengthening receiver nodes so they expose both a
challenge sampler and a challenge-indexed continuation family. Forgetting this
extra structure recovers an ordinary `Verifier`. -/
abbrev PublicCoinVerifier (m : Type u → Type u)
    (SharedIn : Type v)
    (Context : SharedIn → Spec)
    (Roles : (i : SharedIn) → RoleDecoration (Context i))
    (StatementIn : SharedIn → Type w)
    (StatementOut : (i : SharedIn) → Spec.Transcript (Context i) → Type u) :=
  (i : SharedIn) → StatementIn i →
    Spec.PublicCoinCounterpart m (Context i) (Roles i)
      (fun tr => StatementOut i tr)

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
  fun i stmt => (verifier i stmt).toCounterpart

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
  Spec.PublicCoinCounterpart.replay (verifier i stmt) tr

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
counterpart (via `Strategy.runWithRoles`). Returns the transcript, the
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
  Spec.Strategy.runWithRoles (Context i) (Roles i) strategy (reduction.verifier i stmt)

/-- Run a prover strategy against a verifier. Convenience wrapper around
`Spec.Strategy.runWithRoles` that applies the input-indexed verifier. -/
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
    (prover : Spec.Strategy.withRoles m (Context i) (Roles i) OutputP) :
    m ((tr : Spec.Transcript (Context i)) × OutputP tr × StatementOut i tr) :=
  Spec.Strategy.runWithRoles (Context i) (Roles i) prover (v i stmt)

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
    let strat ← Spec.Strategy.compWithRoles strat₁ (fun tr₁ midOut =>
      reduction2.prover ⟨i, stmt, tr₁⟩ midOut.stmt midOut.wit)
    pure <| Spec.Strategy.mapOutputWithRoles
      (fun tr out =>
        Spec.Transcript.liftAppendProd (ctx₁ i) (ctx₂ i) (StmtOut i) (WitOut i) tr out)
      strat
  verifier i stmt :=
    Spec.Counterpart.append (reduction1.verifier i stmt) (fun tr₁ sMid =>
      reduction2.verifier ⟨i, stmt, tr₁⟩ sMid)

/-- Executing a sequentially composed reduction factors into first executing the
prefix reduction and then the suffix interaction induced by its outputs. -/
theorem Reduction.execute_comp
    {m : Type u → Type u} [Monad m] [Spec.LawfulCommMonad m]
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
          Spec.Strategy.runWithRoles (ctx₂ i tr₁) (roles₂ i tr₁) strat₂
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
      Spec.Transcript.liftAppendProd (ctx₁ i) (ctx₂ i) (StmtOut i) (WitOut i) tr out
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
        let strat ← Spec.Strategy.compWithRoles strat₁
          (fun tr₁ midOut => reduction2.prover ⟨i, stmt, tr₁⟩ midOut.stmt midOut.wit)
        Spec.Strategy.runWithRoles ((ctx₁ i).append (ctx₂ i)) ((roles₁ i).append (roles₂ i))
          (Spec.Strategy.mapOutputWithRoles mapOut strat)
          (Spec.Counterpart.append (reduction1.verifier i stmt)
            (fun tr₁ sMid => reduction2.verifier ⟨i, stmt, tr₁⟩ sMid))) =
        mapTriple <$>
          (do
            let strat ← Spec.Strategy.compWithRoles strat₁
              (fun tr₁ midOut => reduction2.prover ⟨i, stmt, tr₁⟩ midOut.stmt midOut.wit)
            Spec.Strategy.runWithRoles ((ctx₁ i).append (ctx₂ i)) ((roles₁ i).append (roles₂ i))
              strat
                (Spec.Counterpart.append (reduction1.verifier i stmt)
                  (fun tr₁ sMid => reduction2.verifier ⟨i, stmt, tr₁⟩ sMid))) := by
    have hraw :
        (do
          let strat ← Spec.Strategy.compWithRoles strat₁
            (fun tr₁ midOut => reduction2.prover ⟨i, stmt, tr₁⟩ midOut.stmt midOut.wit)
          Spec.Strategy.runWithRoles ((ctx₁ i).append (ctx₂ i)) ((roles₁ i).append (roles₂ i))
            (Spec.Strategy.mapOutputWithRoles mapOut strat)
            (Spec.Counterpart.append (reduction1.verifier i stmt)
              (fun tr₁ sMid => reduction2.verifier ⟨i, stmt, tr₁⟩ sMid))) =
          (do
            let strat ← Spec.Strategy.compWithRoles strat₁
              (fun tr₁ midOut => reduction2.prover ⟨i, stmt, tr₁⟩ midOut.stmt midOut.wit)
            mapTriple <$>
              Spec.Strategy.runWithRoles ((ctx₁ i).append (ctx₂ i)) ((roles₁ i).append (roles₂ i))
                strat
                (Spec.Counterpart.append (reduction1.verifier i stmt)
                  (fun tr₁ sMid => reduction2.verifier ⟨i, stmt, tr₁⟩ sMid))) := by
      refine congrArg
        (fun k =>
          Spec.Strategy.compWithRoles strat₁
            (fun tr₁ midOut => reduction2.prover ⟨i, stmt, tr₁⟩ midOut.stmt midOut.wit) >>= k) ?_
      funext strat
      simpa [mapTriple, mapOut, Spec.Counterpart.mapOutput_id] using
        (Spec.Strategy.runWithRoles_mapOutputWithRoles_mapOutput
          (fP := mapOut) (fC := fun _ x => x) strat
          (Spec.Counterpart.append (reduction1.verifier i stmt)
            (fun tr₁ sMid => reduction2.verifier ⟨i, stmt, tr₁⟩ sMid)))
    calc
      (do
        let strat ← Spec.Strategy.compWithRoles strat₁
          (fun tr₁ midOut => reduction2.prover ⟨i, stmt, tr₁⟩ midOut.stmt midOut.wit)
        Spec.Strategy.runWithRoles ((ctx₁ i).append (ctx₂ i)) ((roles₁ i).append (roles₂ i))
          (Spec.Strategy.mapOutputWithRoles mapOut strat)
          (Spec.Counterpart.append (reduction1.verifier i stmt)
            (fun tr₁ sMid => reduction2.verifier ⟨i, stmt, tr₁⟩ sMid))) =
          (do
            let strat ← Spec.Strategy.compWithRoles strat₁
              (fun tr₁ midOut => reduction2.prover ⟨i, stmt, tr₁⟩ midOut.stmt midOut.wit)
            mapTriple <$>
              Spec.Strategy.runWithRoles ((ctx₁ i).append (ctx₂ i)) ((roles₁ i).append (roles₂ i))
                strat
                (Spec.Counterpart.append (reduction1.verifier i stmt)
                  (fun tr₁ sMid => reduction2.verifier ⟨i, stmt, tr₁⟩ sMid))) := hraw
      _ = mapTriple <$>
            (do
              let strat ← Spec.Strategy.compWithRoles strat₁
                (fun tr₁ midOut => reduction2.prover ⟨i, stmt, tr₁⟩ midOut.stmt midOut.wit)
              Spec.Strategy.runWithRoles ((ctx₁ i).append (ctx₂ i)) ((roles₁ i).append (roles₂ i))
                strat
                (Spec.Counterpart.append (reduction1.verifier i stmt)
                  (fun tr₁ sMid => reduction2.verifier ⟨i, stmt, tr₁⟩ sMid))) := by
        simp
  rw [hmap]
  simpa [mapTriple, mapOut, bind_assoc] using
    congrArg (fun mx => mapTriple <$> mx)
      (Spec.Strategy.runWithRoles_compWithRoles_append
        (strat₁ := strat₁)
        (f := fun tr₁ midOut => reduction2.prover ⟨i, stmt, tr₁⟩ midOut.stmt midOut.wit)
        (cpt₁ := reduction1.verifier i stmt)
        (cpt₂ := fun tr₁ sMid => reduction2.verifier ⟨i, stmt, tr₁⟩ sMid))

/-- Compose per-stage prover and verifier step functions into a reduction over
a chained protocol `Spec.stateChain Stage spec advance n`.

The prover and verifier each carry evolving state through the state chain:
- `ProverState i st` is the prover's state at stage `i` with state chain state `st`.
  Initialized from the witness via `proverInit`, then transformed at each stage
  by `proverStep`. The terminal prover state becomes `WitnessOut`.
- `VerifierState i st` is the verifier's state at stage `i`.
  Initialized from the statement via `verifierInit`, then transformed by
  `verifierStep`. The terminal verifier state becomes `StatementOut`.

Both output types are computed as `Transcript.stateChainFamily` of the respective
state families. -/
def Reduction.stateChainComp {m : Type u → Type u} [Monad m]
    {SharedIn : Type v}
    {StatementIn WitnessIn : SharedIn → Type w}
    {Stage : Nat → Type u}
    {spec : (i : Nat) → Stage i → Spec}
    {advance : (i : Nat) → (s : Stage i) → Spec.Transcript (spec i s) → Stage (i + 1)}
    {roles : (i : Nat) → (s : Stage i) → RoleDecoration (spec i s)}
    {ProverState VerifierState : (i : Nat) → Stage i → Type u}
    (n : Nat)
    (initStage : SharedIn → Stage 0)
    (proverInit : (i : SharedIn) → StatementIn i → WitnessIn i →
      m (ProverState 0 (initStage i)))
    (proverStep : (j : Nat) → (st : Stage j) → ProverState j st →
      m (Spec.Strategy.withRoles m (spec j st) (roles j st)
        (fun tr => ProverState (j + 1) (advance j st tr))))
    (stmtResult : (i : SharedIn) → StatementIn i →
      (tr : Spec.Transcript (Spec.stateChain Stage spec advance n 0 (initStage i))) →
      PFunctor.FreeM.Path.stateChainFamily VerifierState n 0 (initStage i) tr)
    (verifierInit : (i : SharedIn) → StatementIn i → VerifierState 0 (initStage i))
    (verifierStep : (j : Nat) → (st : Stage j) → VerifierState j st →
      Spec.Counterpart m (spec j st) (roles j st)
        (fun tr => VerifierState (j + 1) (advance j st tr))) :
    Reduction m SharedIn
      (fun i => Spec.stateChain Stage spec advance n 0 (initStage i))
      (fun i => Spec.Decoration.stateChain roles n 0 (initStage i))
      StatementIn
      WitnessIn
      (fun i => PFunctor.FreeM.Path.stateChainFamily VerifierState n 0 (initStage i))
      (fun i => PFunctor.FreeM.Path.stateChainFamily ProverState n 0 (initStage i)) where
  prover i stmt w := do
    let a ← proverInit i stmt w
    let strat ← Spec.Strategy.stateChainCompWithRoles proverStep n 0 (initStage i) a
    pure <| Spec.Strategy.mapOutputWithRoles (fun tr pOut => ⟨stmtResult i stmt tr, pOut⟩) strat
  verifier i stmt :=
    Spec.Counterpart.stateChainComp verifierStep n 0 (initStage i) (verifierInit i stmt)

/-! ## Chain-based (stateless) reduction composition

Reduction composition over an `n`-round protocol described by `Spec.Chain`,
with **no prover state, no verifier state, and no round index family**.

Each participant provides a per-round step that receives the remaining
`Chain` and produces the strategy/counterpart for the current round.
The remaining chain implicitly encodes prior transcript context
(since it was obtained by applying prior transcripts to the original
continuation). No state flows between rounds (per-round outputs are `PUnit`).
The final `StatementOut` and `WitnessOut` are computed from the full
transcript via caller-supplied result functions. -/

namespace Spec

/-- Build a `Decoration S` for `Chain.toSpec n c` from per-round decorators.
At each level, the decorator receives the remaining `Chain` and
produces the decoration for the current round's spec. -/
def Decoration.ofChain {S : Type u → Type v}
    (decoAt : {k : Nat} → (rem : Chain.{u} (k + 1)) → Decoration S rem.1) :
    (n : Nat) → (c : Chain.{u} n) → Decoration S (Chain.toSpec n c)
  | 0, _ => ⟨⟩
  | n + 1, ⟨spec, cont⟩ =>
      Decoration.append (decoAt ⟨spec, cont⟩)
        (fun tr => Decoration.ofChain decoAt n (cont tr))

namespace Chain

/-- Build a `RoleDecoration` for the full spec from per-round role
assignments. Specializes `Decoration.ofChain` to `fun _ => Role`. -/
abbrev roles
    (rolesAt : {k : Nat} → (rem : Chain.{u} (k + 1)) → RoleDecoration rem.1) :
    (n : Nat) → (c : Chain.{u} n) → RoleDecoration (Chain.toSpec n c) :=
  Decoration.ofChain rolesAt

end Chain

/-- Compose per-round prover strategies into a full strategy over the
chain. Each round's step receives the remaining `Chain` and
produces the strategy for that round's spec. Output is `PUnit` — no
state flows between rounds. -/
def Strategy.ofChain {m : Type u → Type u} [Monad m]
    {rolesAt : {k : Nat} → (rem : Chain.{u} (k + 1)) → RoleDecoration rem.1}
    (step : {k : Nat} → (rem : Chain.{u} (k + 1)) →
      m (Strategy.withRoles m rem.1 (rolesAt rem) (fun _ => PUnit.{u + 1}))) :
    (n : Nat) → (c : Chain.{u} n) →
    m (Strategy.withRoles m (Chain.toSpec n c)
      (Decoration.ofChain rolesAt n c) (fun _ => PUnit.{u + 1}))
  | 0, _ => pure ⟨⟩
  | n + 1, ⟨spec, cont⟩ => do
    let strat ← step ⟨spec, cont⟩
    @Strategy.compWithRolesFlat m _ spec (fun tr => Chain.toSpec n (cont tr))
      (rolesAt ⟨spec, cont⟩) (fun tr => Decoration.ofChain rolesAt n (cont tr))
      (fun _ => PUnit.{u + 1}) (fun _ => PUnit.{u + 1})
      strat (fun tr _ => Strategy.ofChain step n (cont tr))

/-- Compose per-round verifier counterparts into a full counterpart over
the chain. Each round's step receives the remaining `Chain` and
produces the counterpart for that round's spec. Output is `PUnit`. -/
def Counterpart.ofChain {m : Type u → Type u} [Monad m]
    {rolesAt : {k : Nat} → (rem : Chain.{u} (k + 1)) → RoleDecoration rem.1}
    (step : {k : Nat} → (rem : Chain.{u} (k + 1)) →
      Counterpart m rem.1 (rolesAt rem) (fun _ => PUnit.{u + 1})) :
    (n : Nat) → (c : Chain.{u} n) →
    Counterpart m (Chain.toSpec n c)
      (Decoration.ofChain rolesAt n c) (fun _ => PUnit.{u + 1})
  | 0, _ => ⟨⟩
  | n + 1, ⟨spec, cont⟩ =>
    @Counterpart.appendFlat m _ spec (fun tr => Chain.toSpec n (cont tr))
      (rolesAt ⟨spec, cont⟩) (fun tr => Decoration.ofChain rolesAt n (cont tr))
      (fun _ => PUnit.{u + 1}) (fun _ => PUnit.{u + 1})
      (step ⟨spec, cont⟩)
      (fun tr _ => Counterpart.ofChain step n (cont tr))

end Spec

/-- Compose per-round prover and verifier steps into a full `Reduction`
over an `n`-round `Chain`. No `ProverState`, `VerifierState`, or
round index family. Per-round steps produce `PUnit` — no state flows
between rounds. The final `StatementOut` and `WitnessOut` are computed
from the full transcript via `stmtResult` and `witResult`. -/
def Reduction.ofChain {m : Type u → Type u} [Monad m]
    {SharedIn : Type v}
    {WitnessIn : SharedIn → Type w}
    {n : Nat}
    {c : SharedIn → Spec.Chain.{u} n}
    {rolesAt : {k : Nat} → (rem : Spec.Chain.{u} (k + 1)) → RoleDecoration rem.1}
    {StatementOut WitnessOut : (i : SharedIn) →
      Spec.Transcript (Spec.Chain.toSpec n (c i)) → Type u}
    (proverRound : (i : SharedIn) → WitnessIn i →
      {k : Nat} → (rem : Spec.Chain.{u} (k + 1)) →
        m (Spec.Strategy.withRoles m rem.1 (rolesAt rem) (fun _ => PUnit.{u + 1})))
    (verifierRound : (i : SharedIn) →
      {k : Nat} → (rem : Spec.Chain.{u} (k + 1)) →
        Spec.Counterpart m rem.1 (rolesAt rem) (fun _ => PUnit.{u + 1}))
    (witResult : (i : SharedIn) →
      (tr : Spec.Transcript (Spec.Chain.toSpec n (c i))) → WitnessOut i tr)
    (stmtResult : (i : SharedIn) →
      (tr : Spec.Transcript (Spec.Chain.toSpec n (c i))) → StatementOut i tr) :
    Reduction m SharedIn
      (fun i => Spec.Chain.toSpec n (c i))
      (fun i => Spec.Decoration.ofChain rolesAt n (c i))
      (fun _ => PUnit)
      WitnessIn
      StatementOut WitnessOut where
  prover i _ w := do
    let strat ← Spec.Strategy.ofChain (rolesAt := rolesAt) (proverRound i w) n (c i)
    pure <| Spec.Strategy.mapOutputWithRoles
      (fun tr _ => ⟨stmtResult i tr, witResult i tr⟩) strat
  verifier i _ :=
    Spec.Counterpart.mapOutput (fun tr _ => stmtResult i tr)
      (Spec.Counterpart.ofChain (rolesAt := rolesAt) (verifierRound i) n (c i))

end Interaction

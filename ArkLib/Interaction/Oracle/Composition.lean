/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Interaction.Oracle.Core

/-!
# Oracle.Spec Composition Infrastructure

Composition utilities for `Oracle.Spec`-based reductions (`Oracle.Reduction`).

## Main definitions

### Utilities
- `Oracle.Reduction.id` — identity reduction (no interaction, forward
  statement/oracle/witness unchanged).
- `Oracle.Reduction.freezeSharedToPUnit` — fix the shared input, reindex over
  `PUnit`.
- `Oracle.Reduction.pullbackShared` — reindex the shared input along a map.

### Binary composition
- `Oracle.Reduction.comp` — compose two sequential oracle reductions using
  `Oracle.Spec.append`. Prover and verifier are composed by structural
  recursion on `Oracle.Spec`, so `toInteractionSpec` / `toSpecRoles` /
  `toMonadDecoration` all compute at each step without casts.
-/

open OracleComp OracleSpec
open Interaction.TwoParty

namespace Interaction.Oracle

/-! ## Identity reduction -/

/-- Identity oracle reduction: no interaction (`.done` context), forwards
statement, oracle statements, and witness unchanged. -/
def Reduction.id
    {ι : Type} {oSpec : OracleSpec.{0, 0} ι}
    {SharedIn : Type}
    {StatementIn : SharedIn → Type}
    {ιₛᵢ : SharedIn → Type}
    {OStatementIn : (shared : SharedIn) → ιₛᵢ shared → Type}
    [∀ shared i, OracleInterface (OStatementIn shared i)]
    {WitnessIn : SharedIn → Type} :
    Reduction oSpec SharedIn
      (fun _ => .done)
      (fun _ => ⟨⟩)
      (fun _ => ⟨⟩)
      StatementIn OStatementIn WitnessIn
      (fun shared _ => StatementIn shared)
      (OStatementOut := fun shared _ => OStatementIn shared)
      (fun shared _ => WitnessIn shared) where
  prover _ sWithOracles w :=
    pure ⟨⟨sWithOracles.stmt, sWithOracles.oracleStmt⟩, w⟩
  verifier := {
    toFun := fun _ stmt => stmt
    simulate := fun _ _ q => liftM <| ([OStatementIn _]ₒ).query q
  }

/-! ## SharedIn reindexing -/

/-- Freeze the shared input of an `Oracle.Reduction`, reindexing over `PUnit`. -/
def Reduction.freezeSharedToPUnit
    {ι : Type} {oSpec : OracleSpec.{0, 0} ι}
    {SharedIn : Type}
    {Context : SharedIn → Spec}
    {Roles : (shared : SharedIn) → Spec.RoleDeco (Context shared)}
    {OracleDeco : (shared : SharedIn) → Spec.OracleDeco (Context shared)}
    {StatementIn : SharedIn → Type}
    {ιₛᵢ : SharedIn → Type}
    {OStatementIn : (shared : SharedIn) → ιₛᵢ shared → Type}
    [∀ shared i, OracleInterface (OStatementIn shared i)]
    {WitnessIn : SharedIn → Type}
    {StatementOut :
      (shared : SharedIn) → Spec.PublicTranscript (Context shared) → Type}
    {ιₛₒ : (shared : SharedIn) → Spec.PublicTranscript (Context shared) → Type}
    {OStatementOut :
      (shared : SharedIn) → (pt : Spec.PublicTranscript (Context shared)) →
        ιₛₒ shared pt → Type}
    [∀ shared pt i, OracleInterface (OStatementOut shared pt i)]
    {WitnessOut :
      (shared : SharedIn) → Spec.PublicTranscript (Context shared) → Type}
    (reduction : Reduction oSpec SharedIn Context Roles OracleDeco
      StatementIn OStatementIn WitnessIn StatementOut OStatementOut WitnessOut)
    (shared : SharedIn) :
    Reduction oSpec PUnit
      (fun _ => Context shared)
      (fun _ => Roles shared)
      (fun _ => OracleDeco shared)
      (fun _ => StatementIn shared)
      (fun _ => OStatementIn shared)
      (fun _ => WitnessIn shared)
      (fun _ pt => StatementOut shared pt)
      (OStatementOut := fun _ pt => OStatementOut shared pt)
      (fun _ pt => WitnessOut shared pt) where
  prover _ s w := do
    let input' : StatementWithOracles StatementIn OStatementIn shared :=
      ⟨s.stmt, s.oracleStmt⟩
    let remapOutput :
        (tr : Interaction.Spec.Transcript (Context shared).toInteractionSpec) →
        HonestProverOutput
          (StatementWithOracles
            (fun _ => StatementOut shared ((Context shared).projectPublic tr))
            (fun _ => OStatementOut shared ((Context shared).projectPublic tr)) shared)
          (WitnessOut shared ((Context shared).projectPublic tr)) →
        HonestProverOutput
          (StatementWithOracles
            (fun _ => StatementOut shared ((Context shared).projectPublic tr))
            (fun _ => OStatementOut shared ((Context shared).projectPublic tr)) PUnit.unit)
          (WitnessOut shared ((Context shared).projectPublic tr))
      | _, ⟨stmtOut, witOut⟩ => ⟨⟨stmtOut.stmt, stmtOut.oracleStmt⟩, witOut⟩
    let strat ← reduction.prover shared input' w
    pure <| Interaction.Spec.Strategy.mapOutputWithRoles remapOutput strat
  verifier := {
    toFun := fun _ stmt =>
      reduction.verifier.toFun shared stmt
    simulate := fun _ pt =>
      reduction.verifier.simulate shared pt
  }

/-- Reindex the shared input of an `Oracle.Reduction` along a map `f`. -/
def Reduction.pullbackShared
    {ι : Type} {oSpec : OracleSpec.{0, 0} ι}
    {SharedIn SharedIn' : Type}
    (f : SharedIn' → SharedIn)
    {Context : SharedIn → Spec}
    {Roles : (shared : SharedIn) → Spec.RoleDeco (Context shared)}
    {OracleDeco : (shared : SharedIn) → Spec.OracleDeco (Context shared)}
    {StatementIn : SharedIn → Type}
    {ιₛᵢ : SharedIn → Type}
    {OStatementIn : (shared : SharedIn) → ιₛᵢ shared → Type}
    [∀ shared i, OracleInterface (OStatementIn shared i)]
    {WitnessIn : SharedIn → Type}
    {StatementOut :
      (shared : SharedIn) → Spec.PublicTranscript (Context shared) → Type}
    {ιₛₒ : (shared : SharedIn) → Spec.PublicTranscript (Context shared) → Type}
    {OStatementOut :
      (shared : SharedIn) → (pt : Spec.PublicTranscript (Context shared)) →
        ιₛₒ shared pt → Type}
    [∀ shared pt i, OracleInterface (OStatementOut shared pt i)]
    {WitnessOut :
      (shared : SharedIn) → Spec.PublicTranscript (Context shared) → Type}
    (reduction : Reduction oSpec SharedIn Context Roles OracleDeco
      StatementIn OStatementIn WitnessIn StatementOut OStatementOut WitnessOut) :
    Reduction oSpec SharedIn'
      (fun shared => Context (f shared))
      (fun shared => Roles (f shared))
      (fun shared => OracleDeco (f shared))
      (fun shared => StatementIn (f shared))
      (fun shared => OStatementIn (f shared))
      (fun shared => WitnessIn (f shared))
      (fun shared pt => StatementOut (f shared) pt)
      (OStatementOut := fun shared pt => OStatementOut (f shared) pt)
      (fun shared pt => WitnessOut (f shared) pt) where
  prover shared s w := do
    let input' : StatementWithOracles StatementIn OStatementIn (f shared) :=
      ⟨s.stmt, s.oracleStmt⟩
    let remapOutput :
        (tr : Interaction.Spec.Transcript (Context (f shared)).toInteractionSpec) →
        HonestProverOutput
          (StatementWithOracles
            (fun _ => StatementOut (f shared) ((Context (f shared)).projectPublic tr))
            (fun _ => OStatementOut (f shared) ((Context (f shared)).projectPublic tr))
            (f shared))
          (WitnessOut (f shared) ((Context (f shared)).projectPublic tr)) →
        HonestProverOutput
          (StatementWithOracles
            (fun _ => StatementOut (f shared) ((Context (f shared)).projectPublic tr))
            (fun _ => OStatementOut (f shared) ((Context (f shared)).projectPublic tr))
            shared)
          (WitnessOut (f shared) ((Context (f shared)).projectPublic tr))
      | _, ⟨stmtOut, witOut⟩ => ⟨⟨stmtOut.stmt, stmtOut.oracleStmt⟩, witOut⟩
    let strat ← reduction.prover (f shared) input' w
    pure <| Interaction.Spec.Strategy.mapOutputWithRoles remapOutput strat
  verifier := {
    toFun := fun shared stmt =>
      reduction.verifier.toFun (f shared) stmt
    simulate := fun shared pt =>
      reduction.verifier.simulate (f shared) pt
  }

/-! ## Binary composition helpers -/

namespace Prover

/-- Compose two role-aware strategies on `Oracle.Spec` by structural recursion.
At `.oracle` and `.public .sender` nodes, binds the first-phase strategy and
recurses. At `.public .receiver` nodes, produces a function and recurses.

This is the `Oracle.Spec` analog of `Interaction.Spec.Strategy.compWithRolesFlat`,
with the crucial advantage that `toInteractionSpec`, `toSpecRoles`, and
`projectPublic` all reduce definitionally at each step, so no casts are needed.

The output type is indexed by `PublicTranscript` via `split ∘ projectPublic`. -/
def compAux
    {ι : Type} {oSpec : OracleSpec.{0, 0} ι} :
    (s₁ : Oracle.Spec) → (s₂ : Spec.PublicTranscript s₁ → Oracle.Spec) →
    (r₁ : Spec.RoleDeco s₁) →
    (r₂ : (pt₁ : Spec.PublicTranscript s₁) → Spec.RoleDeco (s₂ pt₁)) →
    {Mid : Interaction.Spec.Transcript s₁.toInteractionSpec → Type} →
    {OutType : (pt₁ : Spec.PublicTranscript s₁) →
      Spec.PublicTranscript (s₂ pt₁) → Type} →
    Interaction.Spec.Strategy.withRoles (OracleComp oSpec)
      s₁.toInteractionSpec (s₁.toSpecRoles r₁) Mid →
    ((tr₁ : Interaction.Spec.Transcript s₁.toInteractionSpec) → Mid tr₁ →
      OracleComp oSpec
        (Interaction.Spec.Strategy.withRoles (OracleComp oSpec)
          ((s₂ (s₁.projectPublic tr₁)).toInteractionSpec)
          ((s₂ (s₁.projectPublic tr₁)).toSpecRoles (r₂ (s₁.projectPublic tr₁)))
          (fun tr₂ => OutType (s₁.projectPublic tr₁)
            ((s₂ (s₁.projectPublic tr₁)).projectPublic tr₂)))) →
    OracleComp oSpec
      (Interaction.Spec.Strategy.withRoles (OracleComp oSpec)
        ((s₁.append s₂).toInteractionSpec)
        ((s₁.append s₂).toSpecRoles (Spec.RoleDeco.append s₁ s₂ r₁ r₂))
        (fun tr =>
          OutType
            (Spec.PublicTranscript.split s₁ s₂
              ((s₁.append s₂).projectPublic tr)).1
            (Spec.PublicTranscript.split s₁ s₂
              ((s₁.append s₂).projectPublic tr)).2))
  | .done, _, _, _, _, _, out, cont => cont ⟨⟩ out
  | .oracle _X rest, s₂, r₁, r₂, _, _, strat₁, cont =>
      pure <| do
        let ⟨x, next⟩ ← strat₁
        let result ← compAux rest s₂ r₁ r₂ next
          (fun tr₁ mid => cont ⟨x, tr₁⟩ mid)
        pure ⟨x, result⟩
  | .«public» _X rest, s₂, ⟨.sender, rRest⟩, r₂, _, OutType, strat₁, cont =>
      pure <| do
        let ⟨x, next⟩ ← strat₁
        let result ← compAux (rest x) (fun pt => s₂ ⟨x, pt⟩)
          (rRest x) (fun pt => r₂ ⟨x, pt⟩)
          (OutType := fun pt₁ pt₂ => OutType ⟨x, pt₁⟩ pt₂) next
          (fun tr₁ mid => cont ⟨x, tr₁⟩ mid)
        pure ⟨x, result⟩
  | .«public» _X rest, s₂, ⟨.receiver, rRest⟩, r₂, _, OutType, strat₁, cont =>
      pure fun x => do
        let next ← strat₁ x
        compAux (rest x) (fun pt => s₂ ⟨x, pt⟩)
          (rRest x) (fun pt => r₂ ⟨x, pt⟩)
          (OutType := fun pt₁ pt₂ => OutType ⟨x, pt₁⟩ pt₂) next
          (fun tr₁ mid => cont ⟨x, tr₁⟩ mid)

end Prover

namespace Verifier

/-- Compose two monad-decorated counterparts on `Oracle.Spec` by structural
recursion on the first-phase spec.

At `.oracle` and `.public .sender` nodes the monad is `Id`, so the counterpart
receives a value and recurses. At `.public .receiver` nodes the monad is
`OracleComp`, so the counterpart sends a value monodically and recurses via
`Functor.map`.

The continuation is universally quantified over `accSpec'` so that the
oracle-spec accumulation through `.oracle` nodes is handled: at each such node
`accSpec` grows by `OracleInterface.spec`, and the continuation sees the final
accumulated spec when the first phase reaches `.done`. -/
def compAux
    {ι : Type} {oSpec : OracleSpec.{0, 0} ι}
    {ιₛᵢ : Type} {OStmtIn : ιₛᵢ → Type} [∀ i, OracleInterface (OStmtIn i)] :
    (s₁ : Oracle.Spec) → (s₂ : Spec.PublicTranscript s₁ → Oracle.Spec) →
    (r₁ : Spec.RoleDeco s₁) →
    (r₂ : (pt₁ : Spec.PublicTranscript s₁) → Spec.RoleDeco (s₂ pt₁)) →
    (od₁ : Spec.OracleDeco s₁) →
    (od₂ : (pt₁ : Spec.PublicTranscript s₁) → Spec.OracleDeco (s₂ pt₁)) →
    {ιₐ : Type} → (accSpec : OracleSpec.{0, 0} ιₐ) →
    {Mid : Interaction.Spec.Transcript s₁.toInteractionSpec → Type} →
    {OutType : (pt₁ : Spec.PublicTranscript s₁) →
      Spec.PublicTranscript (s₂ pt₁) → Type} →
    Interaction.Spec.Counterpart.withMonads s₁.toInteractionSpec
      (s₁.toSpecRoles r₁)
      (s₁.toMonadDecoration oSpec OStmtIn r₁ od₁ accSpec) Mid →
    (∀ {ιₐ' : Type} (accSpec' : OracleSpec.{0, 0} ιₐ'),
      (tr₁ : Interaction.Spec.Transcript s₁.toInteractionSpec) → Mid tr₁ →
      Interaction.Spec.Counterpart.withMonads
        ((s₂ (s₁.projectPublic tr₁)).toInteractionSpec)
        ((s₂ (s₁.projectPublic tr₁)).toSpecRoles (r₂ (s₁.projectPublic tr₁)))
        ((s₂ (s₁.projectPublic tr₁)).toMonadDecoration oSpec OStmtIn
          (r₂ (s₁.projectPublic tr₁)) (od₂ (s₁.projectPublic tr₁)) accSpec')
        (fun tr₂ => OutType (s₁.projectPublic tr₁)
          ((s₂ (s₁.projectPublic tr₁)).projectPublic tr₂))) →
    Interaction.Spec.Counterpart.withMonads
      ((s₁.append s₂).toInteractionSpec)
      ((s₁.append s₂).toSpecRoles (Spec.RoleDeco.append s₁ s₂ r₁ r₂))
      ((s₁.append s₂).toMonadDecoration oSpec OStmtIn
        (Spec.RoleDeco.append s₁ s₂ r₁ r₂)
        (Spec.OracleDeco.append s₁ s₂ od₁ od₂) accSpec)
      (fun tr =>
        OutType
          (Spec.PublicTranscript.split s₁ s₂
            ((s₁.append s₂).projectPublic tr)).1
          (Spec.PublicTranscript.split s₁ s₂
            ((s₁.append s₂).projectPublic tr)).2)
  | .done, _, _, _, _, _, _, accSpec, _, _, cpt, cont => cont accSpec ⟨⟩ cpt
  | .oracle _X rest, s₂, r₁, r₂, ⟨oi, odRest⟩, od₂, _, accSpec, _, OutType,
      cpt, cont =>
      fun x => compAux rest s₂ r₁ r₂ odRest od₂
        (accSpec + @OracleInterface.spec _ oi)
        (OutType := fun pt₁ pt₂ => OutType pt₁ pt₂) (cpt x)
        (fun accSpec' tr₁ mid => cont accSpec' ⟨x, tr₁⟩ mid)
  | .«public» _X rest, s₂, ⟨.sender, rRest⟩, r₂, odRest, od₂, _,
      accSpec, _, OutType, cpt, cont =>
      fun x => compAux (rest x) (fun pt => s₂ ⟨x, pt⟩)
        (rRest x) (fun pt => r₂ ⟨x, pt⟩) (odRest x) (fun pt => od₂ ⟨x, pt⟩)
        accSpec
        (OutType := fun pt₁ pt₂ => OutType ⟨x, pt₁⟩ pt₂) (cpt x)
        (fun accSpec' tr₁ mid => cont accSpec' ⟨x, tr₁⟩ mid)
  | .«public» _X rest, s₂, ⟨.receiver, rRest⟩, r₂, odRest, od₂, _,
      accSpec, _, OutType, cpt, cont =>
      (fun ⟨x, cptRest⟩ =>
        ⟨x, compAux (rest x) (fun pt => s₂ ⟨x, pt⟩)
          (rRest x) (fun pt => r₂ ⟨x, pt⟩) (odRest x) (fun pt => od₂ ⟨x, pt⟩)
          accSpec
          (OutType := fun pt₁ pt₂ => OutType ⟨x, pt₁⟩ pt₂) cptRest
          (fun accSpec' tr₁ mid => cont accSpec' ⟨x, tr₁⟩ mid)⟩) <$> cpt

end Verifier

namespace Counterpart

/-- Unifying combinator for oracle-counterpart monad rewriting.

Traverses an `Oracle.Spec` by structural recursion and rewrites the per-node
monads attached by `toMonadDecoration`, carrying a `reroute` at each receiver
node:

* `.done` — identity.
* `.oracle` — the per-node monad is `Id`; pass through as a function on the
  oracle message. Both sides grow their accumulated oracle spec by the current
  oracle's `OracleInterface.spec`; `reroute` is extended so that the new
  oracle-message queries pass through to the matching component of the target
  spec.
* `.public .sender` — the per-node monad is `Id`; pass through as a function
  on the sender message. `accSpec` does not grow.
* `.public .receiver` — the per-node monad is `OracleComp (oSpec + [OStmt?]ₒ
  + accSpec?)`; rewrite it via `simulateQ reroute`, then recurse on the
  continuation.

Both `Counterpart.liftAcc` (change `accSpec`) and `Verifier.retargetMonads`
(change `OStmt`) are thin wrappers over this combinator, obtained by building
`reroute` from their respective narrow data. -/
def mapOracles
    {ι : Type} {oSpec : OracleSpec.{0, 0} ι}
    {ιₛ₁ : Type} {OStmt₁ : ιₛ₁ → Type} [∀ i, OracleInterface (OStmt₁ i)]
    {ιₛ₂ : Type} {OStmt₂ : ιₛ₂ → Type} [∀ i, OracleInterface (OStmt₂ i)] :
    (s : Oracle.Spec) → (roles : Spec.RoleDeco s) → (od : Spec.OracleDeco s) →
    {ιₐ₁ : Type} → (accSpec₁ : OracleSpec.{0, 0} ιₐ₁) →
    {ιₐ₂ : Type} → (accSpec₂ : OracleSpec.{0, 0} ιₐ₂) →
    (reroute : QueryImpl (oSpec + [OStmt₁]ₒ + accSpec₁)
      (OracleComp (oSpec + [OStmt₂]ₒ + accSpec₂))) →
    {Output : Interaction.Spec.Transcript s.toInteractionSpec → Type} →
    Interaction.Spec.Counterpart.withMonads s.toInteractionSpec
      (s.toSpecRoles roles)
      (s.toMonadDecoration oSpec OStmt₁ roles od accSpec₁) Output →
    Interaction.Spec.Counterpart.withMonads s.toInteractionSpec
      (s.toSpecRoles roles)
      (s.toMonadDecoration oSpec OStmt₂ roles od accSpec₂) Output
  | .done, _, _, _, _, _, _, _, _, cpt => cpt
  | .oracle _ rest, _, ⟨oi, odRest⟩, _, accSpec₁, _, accSpec₂, reroute, _, cpt =>
      let oiSpec := @OracleInterface.spec _ oi
      let routeAcc : QueryImpl (accSpec₁ + oiSpec)
          (OracleComp (oSpec + [OStmt₂]ₒ + (accSpec₂ + oiSpec))) :=
        QueryImpl.add
          (fun q => (reroute (.inr q)).liftComp _)
          (fun q => liftM (oiSpec.query q))
      let newReroute : QueryImpl (oSpec + [OStmt₁]ₒ + (accSpec₁ + oiSpec))
          (OracleComp (oSpec + [OStmt₂]ₒ + (accSpec₂ + oiSpec))) :=
        QueryImpl.add
          (fun q => (reroute (.inl q)).liftComp _)
          routeAcc
      fun x => mapOracles rest _ odRest
        (accSpec₁ + oiSpec) (accSpec₂ + oiSpec) newReroute (cpt x)
  | .«public» _ rest, ⟨.sender, rRest⟩, odRest, _, accSpec₁, _, accSpec₂, reroute,
      _, cpt =>
      fun x => mapOracles (rest x) (rRest x) (odRest x)
        accSpec₁ accSpec₂ reroute (cpt x)
  | .«public» _ rest, ⟨.receiver, rRest⟩, odRest, _, accSpec₁, _, accSpec₂, reroute,
      _, cpt =>
      simulateQ reroute <| do
        let ⟨x, cptRest⟩ ← cpt
        pure ⟨x, mapOracles (rest x) (rRest x) (odRest x)
          accSpec₁ accSpec₂ reroute cptRest⟩

/-- Lift a counterpart's accumulated oracle spec from `accSpec₁` to `accSpec₂`
by routing oracle queries. At receiver nodes, `oSpec` and `OStmtIn` queries
pass through; `accSpec₁` queries are rerouted via `routeAcc`. At `.oracle`
nodes, both sides grow by the same oracle interface spec.

When `accSpec₁ = []ₒ`, the routing is trivially `PEmpty.elim`, since no
queries to the empty spec can exist.

Thin wrapper over `Counterpart.mapOracles`: the receiver-node reroute is
`QueryImpl.addLift (QueryImpl.id _) routeAcc`, i.e. identity on the fixed
`oSpec + [OStmtIn]ₒ` prefix and `routeAcc` on the accumulated suffix. -/
def liftAcc
    {ι : Type} {oSpec : OracleSpec.{0, 0} ι}
    {ιₛᵢ : Type} {OStmtIn : ιₛᵢ → Type} [∀ i, OracleInterface (OStmtIn i)]
    (s : Oracle.Spec) (roles : Spec.RoleDeco s) (od : Spec.OracleDeco s)
    {ιₐ₁ : Type} (accSpec₁ : OracleSpec.{0, 0} ιₐ₁)
    {ιₐ₂ : Type} (accSpec₂ : OracleSpec.{0, 0} ιₐ₂)
    (routeAcc : QueryImpl accSpec₁ (OracleComp ((oSpec + [OStmtIn]ₒ) + accSpec₂)))
    {Output : Interaction.Spec.Transcript s.toInteractionSpec → Type}
    (cpt : Interaction.Spec.Counterpart.withMonads s.toInteractionSpec
      (s.toSpecRoles roles)
      (s.toMonadDecoration oSpec OStmtIn roles od accSpec₁) Output) :
    Interaction.Spec.Counterpart.withMonads s.toInteractionSpec
      (s.toSpecRoles roles)
      (s.toMonadDecoration oSpec OStmtIn roles od accSpec₂) Output :=
  mapOracles s roles od accSpec₁ accSpec₂
    (QueryImpl.addLift (QueryImpl.id _) routeAcc) cpt

end Counterpart

namespace Verifier

/-- Retarget the oracle statement monad of a counterpart from `OStmtMid` to
`OStmtIn`, using a simulate function and a query answerer.

Thin wrapper over `Counterpart.mapOracles`: the receiver-node reroute maps
`[OStmtMid]ₒ` queries through `simulateMid` (with the `s₁.toOracleSpec`
queries that appear inside `simulateMid`'s output served by `answerQ` via
`liftRoute`), and passes `oSpec`/`accSpec` queries through unchanged.

Because `mapOracles` already handles the `accSpec` growth at `.oracle`
nodes generically, nothing besides the fixed receiver-node route needs to be
constructed here. -/
def retargetMonads
    {ι : Type} {oSpec : OracleSpec.{0, 0} ι}
    {ιₛᵢ : Type} {OStmtIn : ιₛᵢ → Type} [∀ i, OracleInterface.{0, 0} (OStmtIn i)]
    {ιₛₘ : Type} {OStmtMid : ιₛₘ → Type} [∀ i, OracleInterface.{0, 0} (OStmtMid i)]
    {s₁ : Oracle.Spec} {od₁ : Spec.OracleDeco s₁}
    {pt₁ : Spec.PublicTranscript s₁}
    (simulateMid : QueryImpl [OStmtMid]ₒ
      (OracleComp ([OStmtIn]ₒ + s₁.toOracleSpec od₁ pt₁)))
    (answerQ : QueryImpl (s₁.toOracleSpec od₁ pt₁) Id)
    (s₂ : Oracle.Spec) (roles₂ : Spec.RoleDeco s₂) (od₂ : Spec.OracleDeco s₂)
    {ιₐ : Type} (accSpec : OracleSpec.{0, 0} ιₐ)
    {Output : Interaction.Spec.Transcript s₂.toInteractionSpec → Type}
    (cpt : Interaction.Spec.Counterpart.withMonads s₂.toInteractionSpec
      (s₂.toSpecRoles roles₂)
      (s₂.toMonadDecoration oSpec OStmtMid roles₂ od₂ accSpec) Output) :
    Interaction.Spec.Counterpart.withMonads s₂.toInteractionSpec
      (s₂.toSpecRoles roles₂)
      (s₂.toMonadDecoration oSpec OStmtIn roles₂ od₂ accSpec) Output :=
  let liftRoute : QueryImpl ([OStmtIn]ₒ + s₁.toOracleSpec od₁ pt₁)
      (OracleComp ((oSpec + [OStmtIn]ₒ) + accSpec)) := fun
    | .inl q => liftM <| ([OStmtIn]ₒ).query q
    | .inr q => pure (answerQ q)
  let route : QueryImpl (oSpec + [OStmtMid]ₒ + accSpec)
      (OracleComp (oSpec + [OStmtIn]ₒ + accSpec)) := fun
    | .inl (.inl q) => liftM <| oSpec.query q
    | .inl (.inr q) => simulateQ liftRoute (simulateMid q)
    | .inr q => liftM <| accSpec.query q
  Counterpart.mapOracles s₂ roles₂ od₂ accSpec accSpec route cpt

end Verifier

/-! ## Binary composition -/

/-- Compose two `Oracle.Reduction`s sequentially. The composed reduction runs
the first protocol, then feeds its output statement (at the `PublicTranscript`
level) into the second reduction as shared input.

The resulting context is `(Context₁ shared).append (fun pt₁ => Context₂ ...)`,
using the `PublicTranscript`-indexed continuation. Output types are those of
the second reduction, accessed via `PublicTranscript.split`.

The `simulate` field routes output oracle queries through the second
reduction's simulate, with oracle context queries dispatched via
`QueryHandle.splitAppend`. -/
def Reduction.comp
    {ι : Type} {oSpec : OracleSpec.{0, 0} ι}
    {SharedIn : Type}
    {Context₁ : SharedIn → Spec}
    {Roles₁ : (shared : SharedIn) → Spec.RoleDeco (Context₁ shared)}
    {OracleDeco₁ : (shared : SharedIn) → Spec.OracleDeco (Context₁ shared)}
    {StatementIn : SharedIn → Type}
    {ιₛᵢ : SharedIn → Type}
    {OStatementIn : (shared : SharedIn) → ιₛᵢ shared → Type}
    [∀ shared i, OracleInterface (OStatementIn shared i)]
    {WitnessIn : SharedIn → Type}
    {StatementMid :
      (shared : SharedIn) → Spec.PublicTranscript (Context₁ shared) → Type}
    {ιₛₘ : (shared : SharedIn) → Spec.PublicTranscript (Context₁ shared) → Type}
    {OStatementMid :
      (shared : SharedIn) → (pt₁ : Spec.PublicTranscript (Context₁ shared)) →
        ιₛₘ shared pt₁ → Type}
    [∀ shared pt₁ i, OracleInterface (OStatementMid shared pt₁ i)]
    {WitnessMid :
      (shared : SharedIn) → Spec.PublicTranscript (Context₁ shared) → Type}
    {Context₂ : (shared : SharedIn) → Spec.PublicTranscript (Context₁ shared) → Spec}
    {Roles₂ : (shared : SharedIn) → (pt₁ : Spec.PublicTranscript (Context₁ shared)) →
      Spec.RoleDeco (Context₂ shared pt₁)}
    {OracleDeco₂ : (shared : SharedIn) →
      (pt₁ : Spec.PublicTranscript (Context₁ shared)) →
      Spec.OracleDeco (Context₂ shared pt₁)}
    {StatementOut :
      (shared : SharedIn) → (pt₁ : Spec.PublicTranscript (Context₁ shared)) →
      Spec.PublicTranscript (Context₂ shared pt₁) → Type}
    {ιₛₒ : (shared : SharedIn) → (pt₁ : Spec.PublicTranscript (Context₁ shared)) →
      Spec.PublicTranscript (Context₂ shared pt₁) → Type}
    {OStatementOut :
      (shared : SharedIn) → (pt₁ : Spec.PublicTranscript (Context₁ shared)) →
      (pt₂ : Spec.PublicTranscript (Context₂ shared pt₁)) → ιₛₒ shared pt₁ pt₂ → Type}
    [∀ shared pt₁ pt₂ i, OracleInterface (OStatementOut shared pt₁ pt₂ i)]
    {WitnessOut :
      (shared : SharedIn) → (pt₁ : Spec.PublicTranscript (Context₁ shared)) →
      Spec.PublicTranscript (Context₂ shared pt₁) → Type}
    (r₁ : Reduction oSpec SharedIn Context₁ Roles₁ OracleDeco₁
      StatementIn OStatementIn WitnessIn StatementMid OStatementMid WitnessMid)
    (r₂ : (shared : SharedIn) → (pt₁ : Spec.PublicTranscript (Context₁ shared)) →
      Reduction oSpec PUnit
        (fun _ => Context₂ shared pt₁)
        (fun _ => Roles₂ shared pt₁)
        (fun _ => OracleDeco₂ shared pt₁)
        (fun _ => StatementMid shared pt₁)
        (fun _ => OStatementMid shared pt₁)
        (fun _ => WitnessMid shared pt₁)
        (fun _ pt₂ => StatementOut shared pt₁ pt₂)
        (OStatementOut := fun _ pt₂ => OStatementOut shared pt₁ pt₂)
        (fun _ pt₂ => WitnessOut shared pt₁ pt₂)) :
    Reduction oSpec SharedIn
      (fun shared => (Context₁ shared).append (Context₂ shared))
      (fun shared => Spec.RoleDeco.append (Context₁ shared) (Context₂ shared)
        (Roles₁ shared) (Roles₂ shared))
      (fun shared => Spec.OracleDeco.append (Context₁ shared) (Context₂ shared)
        (OracleDeco₁ shared) (OracleDeco₂ shared))
      StatementIn OStatementIn WitnessIn
      (fun shared pt =>
        StatementOut shared
          (Spec.PublicTranscript.split (Context₁ shared) (Context₂ shared) pt).1
          (Spec.PublicTranscript.split (Context₁ shared) (Context₂ shared) pt).2)
      (ιₛₒ := fun shared pt =>
        ιₛₒ shared
          (Spec.PublicTranscript.split (Context₁ shared) (Context₂ shared) pt).1
          (Spec.PublicTranscript.split (Context₁ shared) (Context₂ shared) pt).2)
      (OStatementOut := fun shared pt i =>
        OStatementOut shared
          (Spec.PublicTranscript.split (Context₁ shared) (Context₂ shared) pt).1
          (Spec.PublicTranscript.split (Context₁ shared) (Context₂ shared) pt).2
          i)
      (fun shared pt =>
        WitnessOut shared
          (Spec.PublicTranscript.split (Context₁ shared) (Context₂ shared) pt).1
          (Spec.PublicTranscript.split (Context₁ shared) (Context₂ shared) pt).2) where
  prover shared sWithOracles w := do
    let strat₁ ← r₁.prover shared sWithOracles w
    Prover.compAux (Context₁ shared) (Context₂ shared)
      (Roles₁ shared) (Roles₂ shared)
      (OutType := fun pt₁ pt₂ =>
        HonestProverOutput
          (StatementWithOracles
            (fun _ => StatementOut shared pt₁ pt₂)
            (fun _ => OStatementOut shared pt₁ pt₂) shared)
          (WitnessOut shared pt₁ pt₂))
      strat₁
      fun tr₁ midOut => do
        let pt₁ := (Context₁ shared).projectPublic tr₁
        let midStmt : StatementWithOracles
            (fun _ => StatementMid shared pt₁)
            (fun _ => OStatementMid shared pt₁) PUnit.unit :=
          ⟨midOut.stmt.stmt, midOut.stmt.oracleStmt⟩
        let strat₂ ← (r₂ shared pt₁).prover PUnit.unit midStmt midOut.wit
        pure <| Interaction.Spec.Strategy.mapOutputWithRoles
          (fun tr₂ out =>
            (⟨⟨out.stmt.stmt, out.stmt.oracleStmt⟩, out.wit⟩ :
              HonestProverOutput
                (StatementWithOracles
                  (fun _ => StatementOut shared pt₁
                    ((Context₂ shared pt₁).projectPublic tr₂))
                  (fun _ => OStatementOut shared pt₁
                    ((Context₂ shared pt₁).projectPublic tr₂))
                  shared)
                (WitnessOut shared pt₁
                  ((Context₂ shared pt₁).projectPublic tr₂)))) strat₂
  verifier := {
    toFun := fun shared stmtIn =>
      Verifier.compAux (OStmtIn := OStatementIn shared)
        (Context₁ shared) (Context₂ shared)
        (Roles₁ shared) (Roles₂ shared) (OracleDeco₁ shared) (OracleDeco₂ shared)
        []ₒ
        (OutType := fun pt₁ pt₂ => StatementOut shared pt₁ pt₂)
        (r₁.verifier.toFun shared stmtIn)
        (fun accSpec' tr₁ midStmt =>
          let pt₁ := (Context₁ shared).projectPublic tr₁
          Counterpart.liftAcc
            (Context₂ shared pt₁) (Roles₂ shared pt₁) (OracleDeco₂ shared pt₁)
            []ₒ accSpec' (fun q => nomatch q)
            (Verifier.retargetMonads
              (r₁.verifier.simulate shared pt₁)
              (Spec.answerQuery (Context₁ shared) (OracleDeco₁ shared) tr₁)
              (Context₂ shared pt₁) (Roles₂ shared pt₁) (OracleDeco₂ shared pt₁)
              []ₒ
              ((r₂ shared pt₁).verifier.toFun PUnit.unit midStmt)))
    -- This `simulate` operates directly on `QueryImpl`s over combined
    -- oracle specs, not on `Counterpart.withMonads` values, so
    -- `Counterpart.mapOracles` (which rewrites per-node monads in a
    -- counterpart) is not applicable here. The routing below is a
    -- specialized plumbing of `simulateQ` through the two sub-verifiers'
    -- `simulate`s.
    simulate := fun shared pt =>
      let pt₁ := (Spec.PublicTranscript.split
        (Context₁ shared) (Context₂ shared) pt).1
      let pt₂ := (Spec.PublicTranscript.split
        (Context₁ shared) (Context₂ shared) pt).2
      let s₁ := Context₁ shared
      let s₂ := Context₂ shared
      let od₁ := OracleDeco₁ shared
      let od₂ := OracleDeco₂ shared
      let od_app := Spec.OracleDeco.append s₁ s₂ od₁ od₂
      let midSpec := [OStatementMid shared pt₁]ₒ +
        Spec.toOracleSpec (s₁.append s₂) od_app pt
      let inSpec := [OStatementIn shared]ₒ +
        Spec.toOracleSpec (s₁.append s₂) od_app pt
      let embedMid : QueryImpl
          (Spec.toOracleSpec (s₁.append s₂) od_app pt) (OracleComp midSpec) :=
        fun q => liftM <| midSpec.query (.inr q)
      let embedIn : QueryImpl
          (Spec.toOracleSpec (s₁.append s₂) od_app pt) (OracleComp inSpec) :=
        fun q => liftM <| inSpec.query (.inr q)
      fun ⟨i, q⟩ =>
        let base := (r₂ shared pt₁).verifier.simulate PUnit.unit pt₂ ⟨i, q⟩
        let routeRight : QueryImpl
            ([OStatementMid shared pt₁]ₒ +
              Spec.toOracleSpec (s₂ pt₁) (od₂ pt₁) pt₂)
            (OracleComp midSpec) := fun
          | .inl q => liftM <| midSpec.query (.inl q)
          | .inr q => Spec.restrictRight s₁ s₂ od₁ od₂ pt embedMid q
        let routedSuffix := simulateQ routeRight base
        let routeLeft : QueryImpl
            ([OStatementIn shared]ₒ +
              Spec.toOracleSpec s₁ od₁ pt₁)
            (OracleComp inSpec) := fun
          | .inl q => liftM <| inSpec.query (.inl q)
          | .inr q => Spec.restrictLeft s₁ s₂ od₁ od₂ pt embedIn q
        let routeMid : QueryImpl midSpec (OracleComp inSpec) := fun
          | .inl q => simulateQ routeLeft
              (r₁.verifier.simulate shared pt₁ q)
          | .inr q => liftM <| inSpec.query (.inr q)
        simulateQ routeMid routedSuffix
  }

end Interaction.Oracle

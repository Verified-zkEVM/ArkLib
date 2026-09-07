/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Interaction.Oracle.Virtual

/-!
# Open, closed, and concrete oracle claims

Closing interprets a plan with a supplied handler. It is a semantic helper, not evidence that
these two values came from the same execution. Relations observe statements and behavior only;
they receive neither query programs nor backing environments.
-/

universe u v w r s t x y z

namespace Interaction.Oracle

variable {OutIdx : Type u} {OutObj : OutIdx → Type v}

/-- A statement and its oracles, with an explicit choice of representation. -/
structure ClaimWith {OutIdx : Type u} {OutObj : OutIdx → Type v}
    (Rep : OracleFamily.{u, v, w} OutIdx OutObj → Type r) (Stmt : Type s)
    (Out : OracleFamily.{u, v, w} OutIdx OutObj) where
  /-- Public statement, including scalar results computed by the verifier. -/
  stmt : Stmt
  /-- Oracle component in the chosen representation. -/
  oracles : Rep Out

/-- An open claim carries programs over a source signature. -/
abbrev OracleClaim {I : Type x} (srcSpec : OracleSpec.{x, v} I)
    (Stmt : Type s) (Out : OracleFamily.{u, v, w} OutIdx OutObj) :=
  ClaimWith (VirtualOracle srcSpec) Stmt Out

/-- The relation boundary: only a statement and arbitrary deterministic behavior. -/
abbrev ClosedClaim (Stmt : Type s) (Out : OracleFamily.{u, v, w} OutIdx OutObj) :=
  ClaimWith OracleFamily.Behavior Stmt Out

/-- Honest concrete output, interpreted through the family's explicit interfaces. -/
abbrev DataClaim (Stmt : Type s) (Out : OracleFamily.{u, v, w} OutIdx OutObj) :=
  ClaimWith (fun O => ∀ i, O.Obj i) Stmt Out

namespace OracleClaim

variable {I : Type x} {srcSpec : OracleSpec.{x, v} I}
  {Stmt : Type s} {Out : OracleFamily.{u, v, w} OutIdx OutObj}

/-- Interpret the oracle component while retaining the run-determined statement. -/
def closeWith (c : OracleClaim srcSpec Stmt Out) (impl : QueryImpl srcSpec Id) :
    ClosedClaim Stmt Out := ⟨c.stmt, c.oracles.eval impl⟩

@[simp]
theorem closeWith_stmt (c : OracleClaim srcSpec Stmt Out) (impl : QueryImpl srcSpec Id) :
    (c.closeWith impl).stmt = c.stmt := rfl

@[simp]
theorem closeWith_oracles (c : OracleClaim srcSpec Stmt Out) (impl : QueryImpl srcSpec Id) :
    (c.closeWith impl).oracles = c.oracles.eval impl := rfl

/-- Observationally equal plans with equal statements close to the same relation input. -/
theorem closeWith_congr {c d : OracleClaim srcSpec Stmt Out}
    (hs : c.stmt = d.stmt) (ho : VirtualOracle.SemEquiv c.oracles d.oracles)
    (impl : QueryImpl srcSpec Id) : c.closeWith impl = d.closeWith impl := by
  cases c
  cases d
  simp_all [closeWith, VirtualOracle.SemEquiv]

/-- Route the source of a claim without altering its public statement. -/
def rebase {J : Type t} {E : Type r} {F : Type y}
    {S : SourceCtx.{x, v, r} I E} {T : SourceCtx.{t, v, y} J F}
    (c : OracleClaim S.spec Stmt Out) (route : SourceHom S T) :
    OracleClaim T.spec Stmt Out := ⟨c.stmt, c.oracles.rebase route⟩

/-- Closing a routed claim uses the pulled-back deterministic handler. -/
@[simp]
theorem closeWith_rebase {J : Type t} {E : Type r} {F : Type y}
    {S : SourceCtx.{x, v, r} I E} {T : SourceCtx.{t, v, y} J F}
    (c : OracleClaim S.spec Stmt Out) (route : SourceHom S T)
    (impl : QueryImpl T.spec Id) :
    (c.rebase route).closeWith impl = c.closeWith (route.pull impl) := by
  simp [rebase, closeWith]

/-- Substitute an upstream virtual view into the downstream claim's programs. -/
def subst {MidIdx : Type y} {MidObj : MidIdx → Type v}
    {Mid : OracleFamily.{y, v, z} MidIdx MidObj} (c : OracleClaim Mid.spec Stmt Out)
    (view : VirtualOracle srcSpec Mid) : OracleClaim srcSpec Stmt Out :=
  ⟨c.stmt, view.subst c.oracles⟩

/-- Closing substitution is precisely closing with the interpreted middle interface. -/
@[simp]
theorem closeWith_subst {MidIdx : Type y} {MidObj : MidIdx → Type v}
    {Mid : OracleFamily.{y, v, z} MidIdx MidObj}
    (c : OracleClaim Mid.spec Stmt Out) (view : VirtualOracle srcSpec Mid)
    (impl : QueryImpl srcSpec Id) :
    (c.subst view).closeWith impl = c.closeWith (view.eval impl) := by
  simp [subst, closeWith]

/-- Substitute the middle interface while retaining independent suffix resources. -/
def substWith {MidIdx : Type y} {MidObj : MidIdx → Type v}
    {Mid : OracleFamily.{y, v, z} MidIdx MidObj} {J : Type t}
    (extra : OracleSpec.{t, v} J) (c : OracleClaim (Mid.spec + extra) Stmt Out)
    (view : VirtualOracle srcSpec Mid) : OracleClaim (srcSpec + extra) Stmt Out :=
  ⟨c.stmt, view.substWith extra c.oracles⟩

/-- Closing keeps the suffix handler and substitutes only the middle interface. -/
@[simp]
theorem closeWith_substWith {MidIdx : Type y} {MidObj : MidIdx → Type v}
    {Mid : OracleFamily.{y, v, z} MidIdx MidObj} {J : Type t}
    (extra : OracleSpec.{t, v} J) (c : OracleClaim (Mid.spec + extra) Stmt Out)
    (view : VirtualOracle srcSpec Mid) (impl : QueryImpl srcSpec Id)
    (other : QueryImpl extra Id) :
    (substWith extra c view).closeWith (QueryImpl.add impl other) =
      c.closeWith (QueryImpl.add (view.eval impl) other) := by
  simp [substWith, closeWith]

end OracleClaim

namespace DataClaim

/-- Forget the concrete representation and keep only its answers. -/
def toClosed {Stmt : Type s} {Out : OracleFamily.{u, v, w} OutIdx OutObj}
    (c : DataClaim Stmt Out) : ClosedClaim Stmt Out :=
  ⟨c.stmt, Out.answerData c.oracles⟩

@[simp]
theorem toClosed_stmt {Stmt : Type s} {Out : OracleFamily.{u, v, w} OutIdx OutObj}
    (c : DataClaim Stmt Out) : c.toClosed.stmt = c.stmt := rfl

@[simp]
theorem toClosed_oracles {Stmt : Type s} {Out : OracleFamily.{u, v, w} OutIdx OutObj}
    (c : DataClaim Stmt Out) : c.toClosed.oracles = Out.answerData c.oracles := rfl

end DataClaim

/-- Honest data realizes a verifier output when both map to the same closed claim. -/
def ProverOutputRealizes {Stmt : Type s} {Out : OracleFamily.{u, v, w} OutIdx OutObj}
    (data : DataClaim Stmt Out) (claim : ClosedClaim Stmt Out) : Prop :=
  data.toClosed = claim

/-- Realization requires both statement agreement and equality of observable answers. -/
theorem proverOutputRealizes_iff {Stmt : Type s} {Out : OracleFamily.{u, v, w} OutIdx OutObj}
    (data : DataClaim Stmt Out) (claim : ClosedClaim Stmt Out) :
    ProverOutputRealizes data claim ↔
      data.stmt = claim.stmt ∧ Out.answerData data.oracles = claim.oracles := by
  cases data
  cases claim
  simp [ProverOutputRealizes, DataClaim.toClosed, ClaimWith.mk.injEq]

/-- Public contexts and the claim type visible in each context. -/
structure ClaimSchema (PublicCtx : Type u) where
  /-- Claims indexed by the public context. -/
  Claim : PublicCtx → Type v

/-- Oracle relations specialize the claim fiber to closed behavior. -/
def ClaimSchema.oracle (PublicCtx : Type x) (Stmt : PublicCtx → Type s)
    {Idx : PublicCtx → Type u} {Obj : ∀ ctx, Idx ctx → Type v}
    (Out : ∀ ctx, OracleFamily.{u, v, w} (Idx ctx) (Obj ctx)) : ClaimSchema PublicCtx :=
  ⟨fun ctx => ClosedClaim (Stmt ctx) (Out ctx)⟩

/-- A claim-dependent witness relation with an explicit admissibility boundary. -/
structure Problem {PublicCtx : Type u} (S : ClaimSchema.{u, v} PublicCtx) where
  /-- Witnesses can depend on both context and claim. -/
  Witness : ∀ ctx, S.Claim ctx → Type w
  /-- Claim-level promises and well-formedness. -/
  admissible : ∀ ctx, S.Claim ctx → Prop
  /-- The relation observes only the declared claim. -/
  rel : ∀ ctx claim, Witness ctx claim → Prop
  /-- Every related claim satisfies the declared promise. -/
  rel_admissible : ∀ ctx claim wit, rel ctx claim wit → admissible ctx claim

/-- Membership means existence of a related witness. -/
def Problem.language {PublicCtx : Type u} {S : ClaimSchema.{u, v} PublicCtx}
    (P : Problem.{u, v, w} S)
    (ctx : PublicCtx) (claim : S.Claim ctx) : Prop := ∃ wit, P.rel ctx claim wit

/-- Language membership entails the claim's admissibility. -/
theorem Problem.language_admissible {PublicCtx : Type u} {S : ClaimSchema.{u, v} PublicCtx}
    (P : Problem.{u, v, w} S)
    {ctx : PublicCtx} {claim : S.Claim ctx} (h : P.language ctx claim) :
    P.admissible ctx claim := by
  obtain ⟨wit, hw⟩ := h
  exact P.rel_admissible ctx claim wit hw

/-- A promise-free relation is the special case with universally true admissibility. -/
abbrev Relation {PublicCtx : Type u} (S : ClaimSchema.{u, v} PublicCtx) :=
  { P : Problem.{u, v, w} S // P.admissible = fun _ _ => True }

end Interaction.Oracle

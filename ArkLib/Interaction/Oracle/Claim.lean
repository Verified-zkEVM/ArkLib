/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import ArkLib.Interaction.Oracle.Virtual

/-!
# Open, closed, and concrete oracle claims

Closing interprets a program with a supplied handler. It is a semantic helper, not evidence that
these two values came from the same execution. Relations observe statements and behavior only;
they receive neither query programs nor concrete realizations.
-/

@[expose] public section

universe u v w r s t x y z

namespace Interaction.Oracle

variable {OutIdx : Type u} {OutRealization : OutIdx → Type v}

/-- A statement and its oracles, with an explicit choice of representation. -/
structure ClaimWith {OutIdx : Type u} {OutRealization : OutIdx → Type v}
    (Rep : OracleFamily.{u, v, w} OutIdx OutRealization → Type r) (Stmt : Type s)
    (Out : OracleFamily.{u, v, w} OutIdx OutRealization) where
  /-- Public statement, including scalar results computed by the verifier. -/
  stmt : Stmt
  /-- Oracle component in the chosen representation. -/
  oracles : Rep Out

/-- An open claim carries programs over a source signature. -/
abbrev OpenClaim {I : Type x} (srcSpec : OracleSpec.{x, v} I)
    (Stmt : Type s) (Out : OracleFamily.{u, v, w} OutIdx OutRealization) :=
  ClaimWith (VirtualOracle srcSpec) Stmt Out

/-- The relation boundary: only a statement and arbitrary deterministic behavior. -/
abbrev ClosedClaim (Stmt : Type s)
    (Out : OracleFamily.{u, v, w} OutIdx OutRealization) :=
  ClaimWith OracleFamily.Behavior Stmt Out

/-- A concrete claim carries realizations interpreted through the family's explicit interfaces. -/
abbrev ConcreteClaim (Stmt : Type s)
    (Out : OracleFamily.{u, v, w} OutIdx OutRealization) :=
  ClaimWith (fun O => ∀ i, O.Realization i) Stmt Out

namespace OpenClaim

variable {I : Type x} {srcSpec : OracleSpec.{x, v} I}
  {Stmt : Type s} {Out : OracleFamily.{u, v, w} OutIdx OutRealization}

/-- Interpret the oracle component while retaining the run-determined statement. -/
def closeWith (c : OpenClaim srcSpec Stmt Out) (impl : QueryImpl srcSpec Id) :
    ClosedClaim Stmt Out := ⟨c.stmt, c.oracles.eval impl⟩

@[simp]
theorem closeWith_stmt (c : OpenClaim srcSpec Stmt Out) (impl : QueryImpl srcSpec Id) :
    (c.closeWith impl).stmt = c.stmt := rfl

@[simp]
theorem closeWith_oracles (c : OpenClaim srcSpec Stmt Out) (impl : QueryImpl srcSpec Id) :
    (c.closeWith impl).oracles = c.oracles.eval impl := rfl

/-- Observationally equal programs with equal statements close to the same relation input. -/
theorem closeWith_congr {c d : OpenClaim srcSpec Stmt Out}
    (hs : c.stmt = d.stmt) (ho : VirtualOracle.SemEquiv c.oracles d.oracles)
    (impl : QueryImpl srcSpec Id) : c.closeWith impl = d.closeWith impl := by
  cases c
  cases d
  simp_all [closeWith, VirtualOracle.SemEquiv]

/-- Route the source of a claim without altering its public statement. -/
def mapSource {J : Type t} {E : Type r} {F : Type y}
    {S : SourceCtx.{x, v, r} I E} {T : SourceCtx.{t, v, y} J F}
    (c : OpenClaim S.spec Stmt Out) (route : SourceHom S T) :
    OpenClaim T.spec Stmt Out := ⟨c.stmt, c.oracles.mapSource route⟩

/-- Closing a routed claim uses the pulled-back deterministic handler. -/
@[simp]
theorem closeWith_mapSource {J : Type t} {E : Type r} {F : Type y}
    {S : SourceCtx.{x, v, r} I E} {T : SourceCtx.{t, v, y} J F}
    (c : OpenClaim S.spec Stmt Out) (route : SourceHom S T)
    (impl : QueryImpl T.spec Id) :
    (c.mapSource route).closeWith impl = c.closeWith (route.pull impl) := by
  simp [mapSource, closeWith]

/-- Substitute an upstream virtual view into the downstream claim's programs. -/
def subst {MidIdx : Type y} {MidRealization : MidIdx → Type v}
    {Mid : OracleFamily.{y, v, z} MidIdx MidRealization} (c : OpenClaim Mid.spec Stmt Out)
    (view : VirtualOracle srcSpec Mid) : OpenClaim srcSpec Stmt Out :=
  ⟨c.stmt, view.subst c.oracles⟩

/-- Closing substitution is precisely closing with the interpreted middle interface. -/
@[simp]
theorem closeWith_subst {MidIdx : Type y} {MidRealization : MidIdx → Type v}
    {Mid : OracleFamily.{y, v, z} MidIdx MidRealization}
    (c : OpenClaim Mid.spec Stmt Out) (view : VirtualOracle srcSpec Mid)
    (impl : QueryImpl srcSpec Id) :
    (c.subst view).closeWith impl = c.closeWith (view.eval impl) := by
  simp [subst, closeWith]

/-- Substitute the middle interface while retaining independent suffix resources. -/
def substWithSuffix {MidIdx : Type y} {MidRealization : MidIdx → Type v}
    {Mid : OracleFamily.{y, v, z} MidIdx MidRealization} {J : Type t}
    (suffix : OracleSpec.{t, v} J) (c : OpenClaim (Mid.spec + suffix) Stmt Out)
    (view : VirtualOracle srcSpec Mid) : OpenClaim (srcSpec + suffix) Stmt Out :=
  ⟨c.stmt, view.substWithSuffix suffix c.oracles⟩

/-- Closing keeps the suffix handler and substitutes only the middle interface. -/
@[simp]
theorem closeWith_substWithSuffix {MidIdx : Type y} {MidRealization : MidIdx → Type v}
    {Mid : OracleFamily.{y, v, z} MidIdx MidRealization} {J : Type t}
    (suffix : OracleSpec.{t, v} J) (c : OpenClaim (Mid.spec + suffix) Stmt Out)
    (view : VirtualOracle srcSpec Mid) (impl : QueryImpl srcSpec Id)
    (other : QueryImpl suffix Id) :
    (substWithSuffix suffix c view).closeWith (QueryImpl.add impl other) =
      c.closeWith (QueryImpl.add (view.eval impl) other) := by
  simp [substWithSuffix, closeWith]

end OpenClaim

namespace ConcreteClaim

/-- Forget the concrete representation and keep only its answers. -/
def toClosed {Stmt : Type s} {Out : OracleFamily.{u, v, w} OutIdx OutRealization}
    (c : ConcreteClaim Stmt Out) : ClosedClaim Stmt Out :=
  ⟨c.stmt, Out.behaviorOfRealizations c.oracles⟩

@[simp]
theorem toClosed_stmt {Stmt : Type s}
    {Out : OracleFamily.{u, v, w} OutIdx OutRealization}
    (c : ConcreteClaim Stmt Out) : c.toClosed.stmt = c.stmt := rfl

@[simp]
theorem toClosed_oracles {Stmt : Type s}
    {Out : OracleFamily.{u, v, w} OutIdx OutRealization}
    (c : ConcreteClaim Stmt Out) :
    c.toClosed.oracles = Out.behaviorOfRealizations c.oracles := rfl

/-- A concrete claim closes to a closed claim when interpreting its realizations gives that
claim. -/
def closesTo {Stmt : Type s} {Out : OracleFamily.{u, v, w} OutIdx OutRealization}
    (concrete : ConcreteClaim Stmt Out) (claim : ClosedClaim Stmt Out) : Prop :=
  concrete.toClosed = claim

/-- Closing agrees exactly when the statements and observable behaviors agree. -/
theorem closesTo_iff {Stmt : Type s}
    {Out : OracleFamily.{u, v, w} OutIdx OutRealization}
    (concrete : ConcreteClaim Stmt Out) (claim : ClosedClaim Stmt Out) :
    concrete.closesTo claim ↔
      concrete.stmt = claim.stmt ∧
        Out.behaviorOfRealizations concrete.oracles = claim.oracles := by
  cases concrete
  cases claim
  simp [closesTo, toClosed, ClaimWith.mk.injEq]

end ConcreteClaim

/-- Public contexts and the claim type visible in each context. -/
structure ClaimFamily (PublicCtx : Type u) where
  /-- Claims indexed by the public context. -/
  Claim : PublicCtx → Type v

/-- Oracle relations specialize the claim fiber to closed behavior. -/
def ClaimFamily.closedOracle (PublicCtx : Type x) (Stmt : PublicCtx → Type s)
    {Idx : PublicCtx → Type u} {Realization : ∀ ctx, Idx ctx → Type v}
    (Out : ∀ ctx, OracleFamily.{u, v, w} (Idx ctx) (Realization ctx)) : ClaimFamily PublicCtx :=
  ⟨fun ctx => ClosedClaim (Stmt ctx) (Out ctx)⟩

/-- A claim-dependent witness relation with an explicit admissibility boundary. -/
structure Problem {PublicCtx : Type u} (S : ClaimFamily.{u, v} PublicCtx) where
  /-- Witnesses can depend on both context and claim. -/
  Witness : ∀ ctx, S.Claim ctx → Type w
  /-- Claim-level promises and well-formedness. -/
  admissible : ∀ ctx, S.Claim ctx → Prop
  /-- The relation observes only the declared claim. -/
  rel : ∀ ctx claim, Witness ctx claim → Prop
  /-- Every related claim satisfies the declared promise. -/
  rel_admissible : ∀ ctx claim wit, rel ctx claim wit → admissible ctx claim

/-- Membership means existence of a related witness. -/
def Problem.language {PublicCtx : Type u} {S : ClaimFamily.{u, v} PublicCtx}
    (P : Problem.{u, v, w} S)
    (ctx : PublicCtx) (claim : S.Claim ctx) : Prop := ∃ wit, P.rel ctx claim wit

/-- Language membership entails the claim's admissibility. -/
theorem Problem.language_admissible {PublicCtx : Type u} {S : ClaimFamily.{u, v} PublicCtx}
    (P : Problem.{u, v, w} S)
    {ctx : PublicCtx} {claim : S.Claim ctx} (h : P.language ctx claim) :
    P.admissible ctx claim := by
  obtain ⟨wit, hw⟩ := h
  exact P.rel_admissible ctx claim wit hw

/-- A promise-free relation is the special case with universally true admissibility. -/
abbrev Relation {PublicCtx : Type u} (S : ClaimFamily.{u, v} PublicCtx) :=
  { P : Problem.{u, v, w} S // P.admissible = fun _ _ => True }

end Interaction.Oracle

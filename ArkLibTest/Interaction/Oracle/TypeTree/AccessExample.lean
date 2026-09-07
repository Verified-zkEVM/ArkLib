/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Interaction.Oracle.Access

/-!
# Accumulated-access acceptance client

This client exercises AR-3A on a public branch selecting two different oracle-message types. It
checks that public branching does not itself change oracle access, that each oracle message becomes
queryable only in its continuation, and that the concrete extension implementation routes old and
new queries to the correct source.
-/

namespace Interaction.Oracle.TypeTree.AccessExample

open OracleComp OracleSpec

/-- One ambient input resource available throughout the protocol. -/
def baseSpec : OracleSpec Unit := Unit →ₒ Nat

/-- A concrete implementation used to check passthrough routing. -/
def baseImpl : QueryImpl baseSpec Id := fun _ => 7

/-- Public future reached after the Boolean oracle branch. -/
def falseFuture : Oracle.TypeTree :=
  .public (Fin 2) fun _ => .done

/-- Public future reached after the `Fin 3` oracle branch. -/
def trueFuture : Oracle.TypeTree :=
  .public Bool fun _ => .done

/-- A public Boolean selects two different oracle messages. -/
def accessTree : Oracle.TypeTree :=
  .public Bool fun
    | false => .oracle Bool fun _ => falseFuture
    | true => .oracle (Fin 3) fun _ => trueFuture

/-- Interfaces matching the two branch-dependent oracle nodes. -/
def accessOracles : accessTree.OracleDecoration :=
  ⟨PUnit.unit, fun
    | false => ⟨OracleInterface.instDefault, fun _ => ⟨PUnit.unit, fun _ => ⟨⟩⟩⟩
    | true => ⟨OracleInterface.instDefault, fun _ => ⟨PUnit.unit, fun _ => ⟨⟩⟩⟩⟩

/-- Accumulated access starting from the ambient input resource. -/
def access : accessTree.AccessDecoration :=
  AccessDecoration.build accessTree accessOracles baseSpec

/-- Public branching preserves the current oracle capabilities on either branch. -/
example : (access.2 false).1.1 = Unit :=
  rfl

example : (access.2 true).1.1 = Unit :=
  rfl

/-- Negative canary: at either oracle-send node the only query domain is still the ambient input
resource. A query of shape `.inr _` for the current prover message is not typeable here. -/
example : access.1.1 = Unit :=
  rfl

/-- After the Boolean oracle message is sent, its query slot is appended to the prior access. -/
example : ((access.2 false).2 PUnit.unit).1.1 = Unit ⊕ Unit :=
  rfl

/-- The appended Boolean slot has Boolean responses. -/
example : ((access.2 false).2 PUnit.unit).1.2 (.inr ()) = Bool :=
  rfl

/-- The other public branch grows by the `Fin 3` oracle interface instead. -/
example : ((access.2 true).2 PUnit.unit).1.2 (.inr ()) = Fin 3 :=
  rfl

/-- Extending a concrete implementation preserves routing to the ambient input resource. -/
example :
    (AccessSpec.ofSpec baseSpec).extendImpl OracleInterface.instDefault baseImpl true (.inl ()) = 7 :=
  rfl

/-- The newly appended slot routes to the concrete prover message. -/
example :
    (AccessSpec.ofSpec baseSpec).extendImpl OracleInterface.instDefault baseImpl true (.inr ()) = true :=
  rfl

/-- Cursor selecting the public future after the Boolean oracle message. -/
def falseFutureCursor : PFunctor.FreeM.Cursor accessTree :=
  PFunctor.FreeM.Cursor.down false <|
    PFunctor.FreeM.Cursor.down PUnit.unit (PFunctor.FreeM.Cursor.root falseFuture)

/-- Restriction recovers exactly the access available at the selected future node. -/
example : (AccessDecoration.restrict falseFutureCursor access).1.1 = Unit ⊕ Unit :=
  rfl

end Interaction.Oracle.TypeTree.AccessExample

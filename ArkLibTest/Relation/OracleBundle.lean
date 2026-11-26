/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Relation.OracleBundle

/-!
# Oracle bundle constructors

The bundle constructors unfold to their fields by `rfl`, and the reducible combinators unfold at
reducible transparency. An indexed bundle built from interfaces equals the bundle of the product
interface on dependent functions, and its specification is `[A]ₒ'`. The bundle of the product
interface on pairs equals the sum of the component bundles.
-/

open Interaction Interaction.Oracle OracleComp OracleSpec

namespace Interaction.OracleBundleTests

/-! ### Definitional equalities -/

example (R S : OracleBundle) (x : R.Data × S.Data) :
    (R.sum S).answer x = R.answer x.1 + S.answer x.2 := rfl

/-- The bundle of the product interface is the sum of the component bundles. The queries and
specifications agree by `rfl`. The answers agree only query by query, because `instProd` answers
through `QueryImpl.addReaderT`. -/
example {α β : Type} (Oα : OracleInterface α) (Oβ : OracleInterface β) :
    OracleBundle.of (α × β) (@OracleInterface.instProd α β Oα Oβ) =
      (OracleBundle.of α Oα).sum (OracleBundle.of β Oβ) := by
  refine congrArg (OracleBundle.mk _ _ _) ?_
  funext x q
  cases q <;> rfl

example {I : Type} (A : I → Type) (O : ∀ i, OracleInterface (A i)) :
    OracleBundle.ofIndexed A O =
      OracleBundle.of (∀ i, A i) (@OracleInterface.instProdForall I A O) := rfl

example {I : Type} (A : I → Type) (O : ∀ i, OracleInterface (A i)) :
    (OracleBundle.ofIndexed A O).spec = @OracleInterface.toOracleSpec I A O := rfl

example {I : Type} (spec : OracleSpec.{0, 0} I) :
    (OracleBundle.ofSpec spec).answer = id := rfl

/-! ### Reducible combinators -/

example (Data : Type) [I : OracleInterface Data] :
    OracleBundle.ofInst Data = OracleBundle.of Data I := by with_reducible rfl

example (Data : Type) (I : OracleInterface Data) :
    (OracleBundle.of Data I).Query = I.Query := by with_reducible rfl

example : OracleBundle.empty.Data = Unit := by with_reducible rfl

example (R S : OracleBundle) : (R.sum S).Data = (R.Data × S.Data) := by with_reducible rfl

example (R S : OracleBundle) : (R.tensor S).Query = (R.Query × S.Query) := by with_reducible rfl

example {I : Type} (F : I → OracleBundle) :
    (OracleBundle.indexed F).Data = ∀ i, (F i).Data := by with_reducible rfl

/-! ### Oracle maps -/

/-- Adding the empty bundle keeps the data and forwards every right query. -/
example (R : OracleBundle) (x : R.Data) (q : R.Query) :
    ((OracleMap.emptyLeft R).f x).2 = x ∧
      (OracleMap.emptyLeft R).impl (.inr q) = liftM (R.spec.query q) := ⟨rfl, rfl⟩

/-- A constant renaming gives both output slots the data of one input slot. -/
example {I : Type} (F : I → OracleBundle) (i : I) (x : (OracleBundle.indexed F).Data) :
    (OracleMap.reindex F fun (_ : Bool) => i).f x false =
      (OracleMap.reindex F fun (_ : Bool) => i).f x true := rfl

end Interaction.OracleBundleTests

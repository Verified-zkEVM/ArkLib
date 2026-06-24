/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import PolyFun.Interaction.Basic.Decoration
import PolyFun.Interaction.Basic.Spec
import PolyFun.Interaction.TwoParty.Decoration
import PolyFun.Interaction.TwoParty.Strategy
import PolyFun.PFunctor.Free.Basic
import PolyFun.PFunctor.Free.Path

/-!
Backward-compatible names for the pre-PolyFun interaction API used across ArkLib.

PolyFun hosts the generic interaction core; this module re-exports the renamed
surface so protocol code can migrate incrementally.
-/

universe u v w

namespace Interaction

/-- Plain-spec paired syntax for a single monad, formerly `pairedSyntax`. -/
abbrev pairedSyntax (m : Type u → Type u) := SyntaxOver.TwoParty.pairedSpec m

/-- View a runtime path along the identity lens as a plain `Transcript`. -/
def transcriptOfPathAlong (spec : Spec)
    (path : PFunctor.FreeM.PathAlong (PFunctor.Lens.id Spec.basePFunctor) spec) :
    Spec.Transcript spec :=
  Eq.mpr (by simp [Spec.Transcript, PFunctor.FreeM.mapLens_id])
    (PFunctor.FreeM.pathAlongToMapLensPath (PFunctor.Lens.id Spec.basePFunctor) spec path)

/-- Whole-tree strategy over a plain `Spec`, with outputs indexed by `Transcript`. -/
abbrev Spec.StrategyOver (m : Type u → Type u) (agent : TwoParty.Participant)
    (spec : Spec) (roles : TwoParty.RoleDecoration spec)
    (Out : Spec.Transcript spec → Type u) :=
  _root_.Interaction.StrategyOver (pairedSyntax m) agent spec roles
    (fun (tr : PFunctor.FreeM.Path spec) => Out tr)

namespace Spec

namespace Transcript

abbrev split := @PFunctor.FreeM.Path.split Spec.basePFunctor PUnit
abbrev append := @PFunctor.FreeM.Path.append Spec.basePFunctor PUnit
abbrev liftAppend := @PFunctor.FreeM.Path.liftAppend Spec.basePFunctor PUnit
abbrev split_append := @PFunctor.FreeM.Path.split_append Spec.basePFunctor PUnit
abbrev packAppend := @PFunctor.FreeM.Path.packAppend Spec.basePFunctor PUnit
abbrev unpackAppend := @PFunctor.FreeM.Path.unpackAppend Spec.basePFunctor PUnit
abbrev liftAppendProd := @PFunctor.FreeM.Path.liftAppendProd Spec.basePFunctor PUnit
abbrev liftAppendProdMk := @PFunctor.FreeM.Path.liftAppendProdMk Spec.basePFunctor PUnit

end Transcript

end Spec

end Interaction

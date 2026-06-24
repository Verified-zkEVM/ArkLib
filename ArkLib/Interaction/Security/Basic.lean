/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Interaction.Reduction
import VCVio.OracleComp.ProbComp

open Interaction.TwoParty

/-!
# Basic Security Utilities
-/

noncomputable section

open OracleComp
open scoped NNReal ENNReal

universe u v w

namespace Interaction

/-! ## Random challenger -/

/-- Build a counterpart strategy that samples challenges uniformly at receiver
nodes. At sender nodes, the strategy simply observes. The `sample` function
provides the probability distribution for each type. Returns `PUnit` output at
`.done`. -/
def randomChallenger (sample : (T : Type) → ProbComp T) :
    (spec : Spec) → (roles : RoleDecoration spec) →
    Spec.StrategyOver (pairedSyntax ProbComp) Interaction.TwoParty.Participant.counterpart
      spec roles (fun _ => PUnit)
  | .done, _ => ⟨⟩
  | .node _X rest, ⟨.sender, rRest⟩ =>
      fun x => pure <| randomChallenger sample (rest x) (rRest x)
  | .node X rest, ⟨.receiver, rRest⟩ => do
      let x ← sample X
      return ⟨x, randomChallenger sample (rest x) (rRest x)⟩

end Interaction

end


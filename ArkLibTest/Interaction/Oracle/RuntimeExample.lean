/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Interaction.Oracle.Runtime
import ArkLibTest.Interaction.Oracle.CoreRunExample

/-! # Reduction execution in one runtime

The producer retains source answers, ambient events, private output, and final state from one
execution. Closing the virtual output does not append either kind of execution query.
-/

namespace Interaction.Oracle.RuntimeExample

open OracleComp OracleSpec CoreRunExample

private abbrev runtime : OracleRuntime (fun _ : Empty => Unit) ambient where
  State := Nat
  setup := pure 7
  handler := fun _ count => pure ((), count + 1)

example (hidden : Nat) :
    (fun result => (result.output.core.proverOut, result.state, result.trace)) <$>
      executeWithRuntime runtime (reduction true) (fun _ => 7) () (11, hidden) =
      pure (hidden, 10, [⟨0, ()⟩, ⟨1, ()⟩, ⟨2, ()⟩]) := by
  rw [executeWithRuntime_eq, OracleRuntime.run_eq]
  simp only [runtime, pure_bind]
  have observation := runtime.runFrom_observe 7
    (executeLogged (reduction true) (fun _ => 7) () (11, hidden))
  have projected := congrArg (fun program =>
    (fun result => (result.1.core.proverOut, result.2.1, result.2.2)) <$> program) observation
  calc
    _ = (fun result => (result.1.1.core.proverOut, result.2, result.1.2)) <$>
        runtime.handler.runState 7
          (executeLogged (reduction true) (fun _ => 7) () (11, hidden)).withQueryLog := by
      simpa only [Functor.map_map] using projected
    _ = _ := by rfl

end Interaction.Oracle.RuntimeExample

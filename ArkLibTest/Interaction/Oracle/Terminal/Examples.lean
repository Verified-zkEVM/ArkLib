/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Interaction.Oracle.Terminal

/-! # Outcome decoder acceptance

The two optional layers have different meanings: an absent claim rejects, while an absent
runtime result uses the caller's fault. The producer below distinguishes all four cases.
-/

namespace Interaction.Oracle.TerminalTest

private def observations : List (Option (Terminal Nat Nat)) :=
  [some (Terminal.ofOption (some 7)), some (Terminal.ofOption none), some (.fault 3), none]

example : observations.map (Terminal.decodeRuntime 9) =
    [.accept 7, .reject, .fault 3, .fault 9] := rfl

example : (observations.map (Terminal.decodeRuntime 9)).map
    (fun result => result.bind (fun n => .accept (n + 1))) =
    [.accept 8, .reject, .fault 3, .fault 9] := rfl

end Interaction.Oracle.TerminalTest

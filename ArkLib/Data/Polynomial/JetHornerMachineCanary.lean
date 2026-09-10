/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import ArkLib.Data.Polynomial.JetHornerMachine
public import Mathlib.Data.ZMod.Basic

/-!
# Jet Horner machine regression checks

The quadratic checks the old-predecessor carry, high zero entries, every cost component, and the
final return boundary. Characteristic two distinguishes Hasse jets from ordinary derivatives.
-/

@[expose] public section

namespace Polynomial.JetHornerMachine

/-- `3X²+4X+5` at `2` has Hasse jet `[25,16,3,0]`. -/
example : runFuel (2 : ℕ) 44 (.initialize [3, 4, 5] 4 []) =
    (.done [25, 16, 3, 0], ⟨12, 12, 44, 193, 9, 4⟩) := by decide

/-- All scalar emissions have occurred, but the final return still needs one transition. -/
example : runFuel (2 : ℕ) 43 (.initialize [3, 4, 5] 4 []) =
    (.emit [] [25, 16, 3, 0], ⟨12, 12, 43, 191, 9, 4⟩) := by decide

/-- Empty coefficients still initialize and emit every requested zero. -/
example : runFuel (7 : ℕ) 9 (.initialize [] 3 []) =
    (.done [0, 0, 0], ⟨0, 0, 9, 25, 7, 3⟩) := by decide

/-- Zero fuel leaves the original requested initialization intact. -/
example : runFuel (2 : ℕ) 0 (.initialize [3, 4, 5] 4 []) =
    (.initialize [3, 4, 5] 4 [], 0) := by decide

/-- `X²` retains its second Hasse coefficient in characteristic two. -/
example : runFuel (1 : ZMod 2) 44 (.initialize [1, 0, 0] 4 []) =
    (.done [1, 0, 1, 0], ⟨12, 12, 44, 193, 9, 4⟩) := by decide

end Polynomial.JetHornerMachine

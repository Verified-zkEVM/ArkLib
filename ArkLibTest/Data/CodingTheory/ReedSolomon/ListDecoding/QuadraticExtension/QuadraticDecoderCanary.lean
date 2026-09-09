/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.QuadraticExtension.QuadraticDecoderProof
/-!
# Kernel checks for outer alphabet routing and scalar-fuel decoding

Distinct ordered alphabets expose an incorrect center/guard branch or uncharged embedding.
A malformed count register exposes partial embedding failure. The core runs at its actual
scalar-parameter fuel and distinguishes an accepting guard grid from a rejecting one.
The small singleton center alphabet is an operational fixture, not a completeness premise.
-/

namespace ReedSolomon.ListDecoding.QuadraticDecoderMachine

open QuadraticAlgebra
open PreparedDecoderMachine (Element)

private def data : SetupMachine.Prepared 3 2 :=
  ⟨[2, 0, 1], [⟨0, 1⟩, ⟨1, 1⟩], [⟨1, 1⟩], 3, 2, 1⟩

private def observe (r : Option (Alphabets 3 2) × ℕ) :
    Option (List (Element (ZMod 3) 2) × List (Element (ZMod 3) 2) × ℕ) × ℕ :=
  (r.1.map (fun a ↦ (a.centers, a.guards, a.exponent)), r.2)

example : observe (chooseAlphabets data true) =
    (some ([2, 0, 1], [2, 0, 1], 1), 88) := by decide +kernel

example : observe (chooseAlphabets data false) =
    (some ([⟨0, 1⟩, ⟨1, 1⟩], [⟨1, 1⟩], 2), 32) := by decide +kernel

example : (chooseAlphabets { data with baseCount := 0 } true).1 = none := by decide +kernel

private theorem nonsquare : ¬IsSquare (2 : ZMod 3) := by
  have h : ∀ r : ZMod 3, (2 : ZMod 3) ≠ r * r := by decide +kernel
  rintro ⟨r, hr⟩
  exact h r hr

private def input : PreparedDecoderMachine.Input (ZMod 3) 2 :=
  ⟨[0], [1], [(0, 0)], 0, 0, 1, 1, 1⟩

example : (runCore input [0] nonsquare [(1, [(0, 0), (1, 1)])] 1 1).1 =
    some [[0]] := by decide +kernel

example : (runCore input [1] nonsquare [(1, [(0, 0), (1, 1)])] 1 1).1 =
    some [] := by decide +kernel

-- This executes interpolation, certified setup, recovery and collection, not just a core fixture.
example : run (q := 3) 1 0 1 1 [(0, 0)] (by decide) (by decide) =
    (some [[0]], 34225) := by decide +kernel

end ReedSolomon.ListDecoding.QuadraticDecoderMachine

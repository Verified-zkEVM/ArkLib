/-
Existence of a far direction in the row span (delegates to Lemma 4.3).
-/

import ArkLib.Data.CodingTheory.ReedSolomon
import ArkLib.Data.CodingTheory.InterleavedCode.Defs
import ArkLib.Data.CodingTheory.InterleavedCode.Lemma43
import Mathlib.Tactic

noncomputable section

open Code
open InterleavedCode

namespace ProximityToRS

variable {F : Type*} [Field F] [DecidableEq F] [Fintype F]
variable {κ ι : Type*} [Fintype κ] [Fintype ι] [DecidableEq ι]

-- Thin wrapper: obtain a far direction v* ∈ rowSpan U under the 3e and Δ(U, L^m) bounds.
lemma exists_far_dir_in_rowSpan
  {deg : ℕ} {α : ι ↪ F} {e : ℕ} {U : Matrix κ ι F}
  (hF : Nat.card F ≥ e.succ.succ)
  (he : 3 * e < Code.minDist (ReedSolomon.code α deg : Set (ι → F)))
  (hU : e < Δ(U,InterleavedCode.matrixSubmoduleOfLinearCode κ (ReedSolomon.code α deg))) :
  ∃ v ∈ Matrix.rowSpan U, e < Code.distFromCode v (ReedSolomon.code α deg) := by
  -- Instantiates Lemma 4.3 (InterleavedCode/Lemma43.lean) with the RS code.
  classical
  -- Package the RS code as a lawful interleaved code
  let IC := InterleavedCode.lawfulInterleavedCodeOfLinearCode (κ := κ)
              (LC := (ReedSolomon.code α deg : LinearCode ι F))
  -- Apply the main lemma
  have := InterleavedCode.Lemma43.distInterleavedCodeToCodeLB
    (IC := IC) (U := U) (e := e)
    (hF := hF) (he := by simpa using he) (hU := by simpa using hU)
    (hMF := rfl)
  -- Unpack and conclude
  simpa using this

end ProximityToRS

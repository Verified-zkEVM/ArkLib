/-
Lemma 4.5 (Ligero): probability of bad points on the row span.
This file hosts the statement; proof to be added.
-/

import ArkLib.Data.CodingTheory.ReedSolomon
import ArkLib.Data.CodingTheory.InterleavedCode.Defs
import ArkLib.Data.CodingTheory.InterleavedCode.ProximityToRS.ClosePoints
import Mathlib.Probability.Distributions.Uniform
import ArkLib.Data.CodingTheory.InterleavedCode.ProximityToRS.Lemma45.Assemble
import Mathlib.Tactic

noncomputable section

open Code

namespace ProximityToRS

variable {F : Type*} [Field F] [DecidableEq F] [Fintype F]
variable {κ ι : Type*} [Fintype κ] [Fintype ι] [DecidableEq ι] [Nonempty ι]

noncomputable instance fintype_rowSpan
    (U : Matrix κ ι F) :
    Fintype ↥(Matrix.rowSpan U : Submodule F (ι → F)) :=
    Fintype.ofFinite _

/--
Lemma 4.5 Ligero
-/
lemma probOfBadPts {deg : ℕ} {α : ι ↪ F} {e : ℕ} {U : Matrix κ ι F} [NeZero deg]
  (he : 3 * e < Code.minDist (ReedSolomon.code α deg : Set (ι → F)))
  (hU : e < Δ(U,InterleavedCode.matrixSubmoduleOfLinearCode κ (ReedSolomon.code α deg))) :
  (PMF.uniformOfFintype (Matrix.rowSpan U)).toOuterMeasure
    { w | distFromCode (n := ι) (R := F) w (ReedSolomon.code α deg) ≤ e }
  ≤ (Fintype.card ι - deg + 1)/(Fintype.card F) := by
  -- Delegate to the assembly lemma combining direction existence, line counting, and averaging
  simpa using
    (ProximityToRS.probOfBadPts_assemble (deg := deg) (α := α) (e := e) (U := U) he hU)

end ProximityToRS

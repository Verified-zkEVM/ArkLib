/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Katerina Hristova, František Silváši
-/

import ArkLib.Data.CodingTheory.Basic
import ArkLib.Data.CodingTheory.ReedSolomon
import Mathlib.Order.CompletePartialOrder
import Mathlib.Probability.Distributions.Uniform

noncomputable section

/-!
  Definition of an interleaved code of a linear code over a semiring.
  Definition of distances for interleaved codes and statement for the relation between the minimal
  distance of an interleaved code and its underlying linear code.
  Statements of proximity results for Reed Solomon codes
  (`Lemma 4.3`, `Lemma 4.4` and `Lemma 4.5` from Ligero) with proximity parameter less than
  the minimal code distance divided by `3`.
-/

variable {F : Type*} [Semiring F]
         {κ ι : Type*} [Fintype κ] [Fintype ι]
         {LC : LinearCode ι F}

abbrev MatrixSubmodule.{u, v, w} (κ : Type u) [Fintype κ] (ι : Type v) [Fintype ι]
                                 (F : Type w) [Semiring F] : Type (max u v w) :=
  Submodule F (Matrix κ ι F)

/--
The data needed to construct an interleaved code.
-/
structure InterleavedCode (κ ι : Type*) [Fintype κ] [Fintype ι] (F : Type*) [Semiring F] where
  MF : MatrixSubmodule κ ι F
  LC : LinearCode ι F

namespace InterleavedCode

/--
The condition making the `InterleavedCode` structure an interleaved code.
-/
def isInterleaved (IC : InterleavedCode κ ι F) :=
  ∀ V ∈ IC.MF, ∀ i, V i ∈ IC.LC

def LawfulInterleavedCode (κ : Type*) [Fintype κ] (ι : Type*) [Fintype ι]
                          (F : Type*) [Semiring F] :=
  { IC : InterleavedCode κ ι F // IC.isInterleaved }

/--
The submodule of the module of matrices whose rows belong to a linear code.
-/
def matrixSubmoduleOfLinearCode (κ : Type*) [Fintype κ]
                                (LC : LinearCode ι F) : MatrixSubmodule κ ι F :=
  Submodule.span F { V | ∀ i, V i ∈ LC }

def codeOfLinearCode (κ : Type*) [Fintype κ] (LC : LinearCode ι F) : InterleavedCode κ ι F :=
  { MF := matrixSubmoduleOfLinearCode κ LC, LC := LC }

/--
The module of matrices whose rows belong to a linear code is in fact an interleaved code.
-/
lemma isInterleaved_codeOfLinearCode : (codeOfLinearCode κ LC).isInterleaved := by sorry

def lawfulInterleavedCodeOfLinearCode (κ : Type*) [Fintype κ] (LC : LinearCode ι F) :
  LawfulInterleavedCode κ ι F := ⟨codeOfLinearCode κ LC, isInterleaved_codeOfLinearCode⟩

/--
Distance between codewords of an interleaved code.
-/
def distCodewords [DecidableEq F] (U V : Matrix κ ι F) : ℕ :=
  (Matrix.neqCols U V).card

/--
`Δ(U,V)` is the distance between codewords `U` and `V` of a `κ`-interleaved code `IC`.
-/
notation "Δ(" U "," V ")" => distCodewords U V

/--
Minimal distance of an interleaved code.
-/
def minDist [DecidableEq F] (IC : MatrixSubmodule κ ι F) : ℕ :=
  sInf { d : ℕ | ∃ U ∈ IC, ∃ V ∈ IC, distCodewords U V = d }

/--
`Δ IC` is the min distance of an interleaved code `IC`.
-/
notation "Δ" IC => minDist IC

/--
Distance from a matrix to the closest word in an interleaved code.
-/
def distToCode [DecidableEq F] (U : Matrix κ ι F) (IC : MatrixSubmodule κ ι F) : ℕ :=
 sInf { d : ℕ | ∃ V ∈ IC, distCodewords U V = d }

/--
`Δ(U,C')` denotes distance between a `κ x ι` matrix `U` and `κ`-interleaved code `IC`.
-/
notation "Δ(" U "," IC ")" => distToCode U IC

/--
Relative distance between codewords of an interleaved code.
-/
def relDistCodewords [DecidableEq F] (U V : Matrix κ ι F) : ℝ :=
  (Matrix.neqCols U V).card / Fintype.card ι

/-- List of codewords of IC r-close to U,
  with respect to relative distance of interleaved codes.
-/
def relHammingBallInterleavedCode [DecidableEq F] (U : Matrix κ ι F)
  (IC : MatrixSubmodule κ ι F) (r : ℝ) :=
    {V | V ∈ IC ∧ relDistCodewords U V < r}

/--`Λᵢ(U, IC, r)` denotes the list of codewords of IC r-close to U-/
notation "Λᵢ(" U "," IC "," r ")" => relHammingBallInterleavedCode U IC r

/--
The minimal distance of an interleaved code is the same as
the minimal distance of its underlying linear code.
-/
lemma minDist_eq_minDist [DecidableEq F] {IC : LawfulInterleavedCode κ ι F} :
  Code.minDist (IC.1.LC : Set (ι → F)) = minDist IC.1.MF := by sorry

end InterleavedCode

noncomputable section

open InterleavedCode
open Code

variable {F : Type*} [Field F] [Finite F] [DecidableEq F]
         {κ : Type*} [Fintype κ] {ι : Type*} [Fintype ι]

local instance : Fintype F := Fintype.ofFinite F

/--
Lemma 4.3 Ligero
-/
lemma distInterleavedCodeToCodeLB
  {IC : LawfulInterleavedCode κ ι F} {U : Matrix κ ι F} {e : ℕ}
  (hF : Fintype.card F ≥ e)
  (he : (e : ℚ) ≤ (minDist (IC.1.LC : Set (ι → F)) / 3)) (hU : e < Δ(U,IC.1.MF)) :
  ∃ v ∈ Matrix.rowSpan U , e < distFromCode v IC.1.LC := sorry

namespace ProximityToRS

/--
The set of points on an affine line, which are within distance `e`
from a Reed-Solomon code.
-/
def closePtsOnAffineLine {ι : Type*} [Fintype ι]
                         (u v : ι → F) (deg : ℕ) (α : ι ↪ F) (e : ℕ) : Set (ι → F) :=
  {x : ι → F | x ∈ Affine.line u v ∧ distFromCode x (ReedSolomon.code α deg) ≤ e}

/--
The number of points on an affine line between, which are within distance `e`
from a Reed-Solomon code.
-/
def numberOfClosePts (u v : ι → F) (deg : ℕ) (α : ι ↪ F)
  (e : ℕ) : ℕ :=
  Fintype.card (closePtsOnAffineLine u v deg α e)

/--
Lemma 4.4 Ligero
Remark: Below, can use (ReedSolomonCode.minDist deg α) instead of ι - deg + 1 once proved.
-/
lemma e_leq_dist_over_3 {deg : ℕ} {α : ι ↪ F} {e : ℕ} {u v : ι → F}
  (he : (e : ℚ) < (Fintype.card ι - deg + 1 / 3)) :
  ∀ x ∈ Affine.line u v, distFromCode x (ReedSolomon.code α deg) ≤ e
  ∨ (numberOfClosePts u v deg α e) ≤ Fintype.card ι - deg + 1 := by sorry

/--
Lemma 4.5 Ligero
-/
lemma probOfBadPts {deg : ℕ} {α : ι ↪ F} {e : ℕ} {U : Matrix κ ι F}
  (he : (e : ℚ) < (Fintype.card ι - deg + 1 / 3))
  (hU : e < Δ(U,matrixSubmoduleOfLinearCode κ (ReedSolomon.code α deg))) :
  (PMF.uniformOfFintype (Matrix.rowSpan U)).toOuterMeasure
    { w | distFromCode (n := ι) (R := F) w (ReedSolomon.code α deg) ≤ e }
  ≤ (Fintype.card ι - deg + 1)/(Fintype.card F) := by
  sorry

end ProximityToRS
end

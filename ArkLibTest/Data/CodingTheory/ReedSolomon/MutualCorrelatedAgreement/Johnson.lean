/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.Johnson.FullCode
import Mathlib.Data.Fin.VecNotation

open Polynomial CoreDefinitions ReedSolomon

private def fullCodeDomain : Fin 2 ↪ ℚ := ⟨![0, 1], by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all⟩

example : code fullCodeDomain 3 = ⊤ :=
  code_eq_top_of_card_le fullCodeDomain (by simp)

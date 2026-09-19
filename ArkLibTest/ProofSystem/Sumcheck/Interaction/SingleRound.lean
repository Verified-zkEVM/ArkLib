/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.ProofSystem.Sumcheck.Interaction.SingleRound
import Mathlib.Data.ZMod.Basic

/-! # Nonconstant finite-field single-round acceptance examples -/

namespace Sumcheck.Interaction.SingleRound.Test

open Polynomial OracleComp OracleSpec

/-- A nonconstant degree-one polynomial over the field with seventeen elements. -/
noncomputable def polynomial : Message (ZMod 17) 1 :=
  ⟨X, Polynomial.mem_degreeLE.mpr Polynomial.degree_X_le⟩

/-- A genuinely oracle-capable ambient signature, unused at this fixed challenge. -/
abbrev ambient : OracleSpec Unit := Unit →ₒ Unit

/-- The nonconstant polynomial sums to one on the Boolean domain. -/
example : ([0, 1].map (fun x => polynomial.val.eval x)).sum = (1 : ZMod 17) := by
  simp [polynomial]

/-- The actual paired executor accepts and obtains target five from the sent polynomial. -/
example :
    executeAt (ZMod 17) 1 ambient polynomial polynomial [0, 1] 1 5 =
      pure ⟨⟨polynomial, (5 : ZMod 17), PUnit.unit⟩, (5, 5), some (5, 5)⟩ := by
  rw [executeAt_eq]
  simp [polynomial]

/-- An incorrect sum claim is rejected by the actual verifier. -/
example :
    executeAt (ZMod 17) 1 ambient polynomial polynomial [0, 1] 2 5 =
      pure ⟨⟨polynomial, (5 : ZMod 17), PUnit.unit⟩, (5, 5), none⟩ := by
  rw [executeAt_eq]
  simp only [polynomial, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, eval_X,
    add_zero, zero_add]
  have h : (1 : ZMod 17) ≠ 2 := by decide
  rw [if_neg h]

/-- The false input polynomial in the degree-zero soundness regression. -/
noncomputable def zeroMessage : Message (ZMod 17) 0 :=
  ⟨0, Polynomial.mem_degreeLE.mpr (by simp)⟩

/-- A dishonest constant message passes the claimed sum on the singleton domain. -/
noncomputable def oneMessage : Message (ZMod 17) 0 :=
  ⟨1, Polynomial.mem_degreeLE.mpr (by simp)⟩

/-- A dishonest accepted message supplies the next target, rather than the input oracle. -/
example (r : ZMod 17) :
    executeAt (ZMod 17) 0 ambient zeroMessage oneMessage [0] 1 r =
      pure ⟨⟨oneMessage, r, PUnit.unit⟩, (1, r), some (1, r)⟩ := by
  rw [executeAt_eq]
  simp [oneMessage]

#print axioms executeAt_eq
#print axioms executeAt_honest

end Sumcheck.Interaction.SingleRound.Test

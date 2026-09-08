/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

import Mathlib.Logic.Equiv.Defs

/-!
# Deterministic checked observations

A source evaluation is an observation of the honest message, after a lossless witness change.
This unconditional identity gives honest checking and exact readback while preserving any
given commitment or witness predicate. Concrete protocols prove their original relation and
guard equivalences separately; no binding, domain, or security assumption is built into this data.
-/

namespace RingSwitching.Packing

/-- An unconditional evaluation identity, with explicit source and output witness coordinates. -/
structure CheckedObservation (Q WIn WOut Message Value : Type*) where
  /-- Exact witness coordinates; readback uses this equivalence's inverse. -/
  witnessEquiv : WIn ≃ WOut
  /-- The honest message computed from an output witness and query. -/
  honestMsg : Q → WOut → Message
  /-- The original scalar evaluation of the source witness. -/
  scalarEval : Q → WIn → Value
  /-- The scalar observation checked on an arbitrary sent message. -/
  observe : Q → Message → Value
  /-- Unconditional reconstruction for every source witness, without relation-validity premises. -/
  eval_eq_observe : ∀ q w,
    scalarEval q w = observe q (honestMsg q (witnessEquiv w))

namespace CheckedObservation

variable {Q WIn WOut Message Value : Type*}
  (D : CheckedObservation Q WIn WOut Message Value)

/-- Every correct original claim passes the observation check on its honest message. -/
theorem honest_check {q : Q} {claim : Value} {w : WIn}
    (h : claim = D.scalarEval q w) :
    claim = D.observe q (D.honestMsg q (D.witnessEquiv w)) :=
  h.trans (D.eval_eq_observe q w)

/-- A checked message with a valid output witness recovers the original evaluation claim. -/
theorem readback {q : Q} {claim : Value} {msg : Message} {w : WOut}
    (hc : claim = D.observe q msg) (hm : msg = D.honestMsg q w) :
    claim = D.scalarEval q (D.witnessEquiv.symm w) := by
  rw [D.eval_eq_observe, D.witnessEquiv.apply_symm_apply]
  exact hc.trans (congrArg (D.observe q) hm)

/-- Checked readback preserves the supplied predicate on the output witness. -/
theorem readback_keep (Keep : Q → WOut → Prop)
    {q : Q} {claim : Value} {msg : Message} {w : WOut}
    (hc : claim = D.observe q msg) (ho : Keep q w ∧ msg = D.honestMsg q w) :
    Keep q (D.witnessEquiv (D.witnessEquiv.symm w)) ∧
      claim = D.scalarEval q (D.witnessEquiv.symm w) := by
  exact ⟨by simpa only [D.witnessEquiv.apply_symm_apply] using ho.1,
    D.readback hc ho.2⟩

end CheckedObservation

end RingSwitching.Packing

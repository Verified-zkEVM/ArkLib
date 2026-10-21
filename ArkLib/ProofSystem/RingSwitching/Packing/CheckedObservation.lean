/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/
module

public import Mathlib.Logic.Equiv.Defs

/-!
# Deterministic checked observations

A source evaluation is an observation of the honest message, after a lossless witness change.
This identity is the only law of the structure. It gives two consequences: the honest message
passes the observation check, and an accepted message that is the honest message of some output
witness reads back to a correct claim about the corresponding source witness. Read-back does not
show that an arbitrary accepted message is honest; that is the job of a binding or soundness
argument at the use site. No binding, domain, or security assumption is built into this data.
-/

@[expose] public section

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

/-- If an accepted message is the honest message of some output witness, the checked claim is
the original evaluation of the corresponding source witness. -/
theorem readback {q : Q} {claim : Value} {msg : Message} {w : WOut}
    (hc : claim = D.observe q msg) (hm : msg = D.honestMsg q w) :
    claim = D.scalarEval q (D.witnessEquiv.symm w) := by
  rw [D.eval_eq_observe, D.witnessEquiv.apply_symm_apply]
  exact hc.trans (congrArg (D.observe q) hm)

end CheckedObservation

end RingSwitching.Packing

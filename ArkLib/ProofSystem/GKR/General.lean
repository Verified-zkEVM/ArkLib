/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vuk Dolijanovic, Claude(Anthropic)
-/

import ArkLib.ProofSystem.GKR.SingleRound

/-!
# The GKR protocol, composed across all layers

`SingleRound.lean` builds one layer: the inner sum-check followed by the combine step, with
`Combine.layerReduction_perfectCompleteness` proving it takes a true layer-`l` claim to a true
layer-`l+1` claim.

This file chains those `n` layers together. The key is `layerRel`, which says "`value` is what
layer `i`'s multilinear extension gives at `point`". Two facts make it the right chain
relation:

* `layerRel_castSucc_eq` — at layer `l` it *is* the inner sum-check's input relation. This is
  where `layerMLE_eval_eq_wiring_sum'` gets used: the honest oracle really does satisfy the
  wiring identity.
* `layerRel_succ_eq` — at layer `l+1` it *is* the combine step's output relation, definitionally.

So each layer reduction carries `layerRel i.castSucc` to `layerRel i.succ`, which is exactly
the shape `Reduction.seqCompose_perfectCompleteness` consumes.

The resulting `gkrReduction_perfectCompleteness` reduces a true claim about the *output* layer
to a true claim about the *input* layer. It stops there: the reduction hands back a claim, and
nothing here checks it. Neither end of the real protocol is present — no opening from a claimed
circuit output, and no terminal check of the surviving claim against the input.

Both are supplied in `OracleLayer.lean`, where the protocol is restated as an `OracleReduction`.
`Oracle.gkrFull_perfectCompleteness` runs from `evalCircuit c input = y` to the verifier
accepting, with `Oracle.terminalCheck` evaluating the input's own multilinear extension —
which the verifier can afford, since it holds the input. `Circuit.layerValues_zero` and
`Circuit.layerValues_last` are the facts that tie layer `0` to `evalCircuit` and the last layer
to `input`.

Note this inherits ArkLib's unproved composition lemmas (`Reduction.append_completeness`,
`Reduction.liftContext_completeness`, `Prover.append_run`), so `#print axioms` reports
`sorryAx`. Nothing in `ArkLib/ProofSystem/GKR/` contains a `sorry` of its own.
-/

namespace GKR
open MvPolynomial Polynomial OracleSpec OracleComp ProtocolSpec

variable (R : Type) [CommRing R] [IsDomain R] [DecidableEq R] [SampleableType R] (n : ℕ)
variable {k : ℕ} (c : Circuit k n) (input : Index k → R)

/-- The chain relation: at layer `i`, `value` is what layer `i`'s multilinear extension
gives at `point`. -/
def layerRel (i : Fin (n + 1)) : Set (GKRStatement R n k i × Unit) :=
  { ⟨⟨point, value⟩, _⟩ | MvPolynomial.eval point (layerMLE R c input i) = value }

/-- The chain relation at layer `l` *is* the inner sum-check's input relation. -/
theorem layerRel_castSucc_eq (l : Fin n) :
    layerRel R n c input l.castSucc = relationRound R n k c l (layerMLE R c input l.succ) := by
  ext ⟨⟨point, value⟩, u⟩
  simp only [layerRel, relationRound, Set.mem_setOf_eq]
  constructor
  · rintro rfl; exact layerMLE_eval_eq_wiring_sum' R c input l point
  · intro h; rw [h]; exact layerMLE_eval_eq_wiring_sum' R c input l point

/-- The chain relation at layer `l+1` *is* the combine step's output relation. -/
theorem layerRel_succ_eq (l : Fin n) :
    layerRel R n c input l.succ = Combine.relOut R n l (layerMLE R c input l.succ) := rfl

variable {σ : Type} {init : ProbComp σ}
    {impl : QueryImpl ([]ₒ : OracleSpec PEmpty) (StateT σ ProbComp)}

/-- One layer of GKR, with the honest oracle instantiated to the next layer's MLE. -/
noncomputable def gkrLayer (l : Fin n) :
    Reduction []ₒ
      (GKRStatement R n k l.castSucc) Unit (GKRStatement R n k l.succ) Unit
      (Sumcheck.Spec.pSpec R 2 (k + k) ++ₚ Combine.pSpec R k) :=
  Combine.layerReduction R n c l (layerMLE R c input l.succ) (fun j => MLE_degreeOf _ j)

/-- Each layer takes the chain relation one step down. -/
theorem gkrLayer_perfectCompleteness (l : Fin n) :
    (gkrLayer R n c input l).perfectCompleteness init impl
      (layerRel R n c input l.castSucc) (layerRel R n c input l.succ) := by
  rw [layerRel_castSucc_eq, layerRel_succ_eq]
  exact Combine.layerReduction_perfectCompleteness R n c l _ _

noncomputable def gkrReduction :
    Reduction []ₒ
      (GKRStatement R n k 0) Unit (GKRStatement R n k (Fin.last n)) Unit
      (ProtocolSpec.seqCompose
        (fun _ : Fin n => Sumcheck.Spec.pSpec R 2 (k + k) ++ₚ Combine.pSpec R k)) :=
  Reduction.seqCompose
    (Stmt := fun i => GKRStatement R n k i) (Wit := fun _ => Unit)
    (gkrLayer R n c input)

/-- **Perfect completeness of GKR.** . This is our capstone theorem. -/
theorem gkrReduction_perfectCompleteness :
    (gkrReduction R n c input).perfectCompleteness init impl
      (layerRel R n c input 0) (layerRel R n c input (Fin.last n)) :=
  Reduction.seqCompose_perfectCompleteness
    (rel := layerRel R n c input)
    (R := gkrLayer R n c input)
    (h := fun l => gkrLayer_perfectCompleteness R n c input l)

end GKR

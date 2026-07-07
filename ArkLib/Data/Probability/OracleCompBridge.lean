/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

import VCVio
import ArkLib.Data.Probability.Instances

/-!
# Bridge: VCVio `OracleComp` events ↔ `PMF` sampling notation

Round-by-round security games in ArkLib live on the VCVio side (`Pr[E | oa]` over
`OracleComp`/`ProbComp`), while per-round error analyses are naturally stated against the
`PMF`-level sampling notation `Pr_{ let c ←$ᵖ C }[ E c ]` (`ArkLib.Data.Probability.Notation`).
This file provides the bridge:

* `probEvent_uniformSample_eq_pr_uniformOfFintype`: the event probability of a uniform query
  `$ᵗ C` is exactly that of `PMF.uniformOfFintype C`.
* `probEvent_bind_uniformSample_le`: a per-prefix `PMF`-level bound transfers to the bind
  `do let a ← ma; let c ← $ᵗ C; return (a, c)` — the shape of an RBR game whose final
  round is a uniformly sampled challenge.

Layering: `Data` files may import VCVio (precedent: `ArkLib.Data.Hash.DuplexSponge`).
-/

open OracleComp ProbabilityTheory NNReal

open scoped ENNReal

section OracleCompBridge

variable {C : Type} [SampleableType C] [Fintype C] [Nonempty C]

/-- The event probability of a uniform query `$ᵗ C` agrees with the `PMF`-level probability
under `PMF.uniformOfFintype C`: both are `#{c | E c} / #C`. -/
theorem probEvent_uniformSample_eq_pr_uniformOfFintype (E : C → Prop) :
    Pr[E | $ᵗ C] = Pr_{ let c ← $ᵖ C}[E c] := by
  classical
  rw [probEvent_uniformSample, prob_uniform_eq_card_filter_div_card]
  simp

/-- A per-prefix `PMF`-level bound on a uniformly sampled challenge transfers to the
`OracleComp` bind `do let a ← ma; let c ← $ᵗ C; return (a, c)`.

This is the probability core of factoring an RBR game: `ma` is the (already simulated)
transcript prefix, `c` the fresh challenge, and `E` the bad event. -/
theorem probEvent_bind_uniformSample_le {A : Type} (ma : ProbComp A)
    (E : A → C → Prop) {ε : ℝ≥0∞}
    (h : ∀ a, Pr_{ let c ← $ᵖ C}[E a c] ≤ ε) :
    Pr[fun x => E x.1 x.2 | do let a ← ma; let c ← $ᵗ C; return (a, c)] ≤ ε := by
  refine probEvent_bind_le_of_forall_le fun a _ => ?_
  calc Pr[fun x => E x.1 x.2 | do let c ← $ᵗ C; return (a, c)]
      = Pr[fun c => E a c | $ᵗ C] := by
        rw [bind_pure_comp, probEvent_map]
        rfl
    _ = Pr_{ let c ← $ᵖ C}[E a c] := probEvent_uniformSample_eq_pr_uniformOfFintype _
    _ ≤ ε := h a

end OracleCompBridge

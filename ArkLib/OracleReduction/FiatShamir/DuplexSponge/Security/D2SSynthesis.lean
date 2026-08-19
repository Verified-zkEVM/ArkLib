/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen
-/

import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.TraceDataStructures

/-!
# D2S cache and synthesis layout

The small, trace-facing operations used by the `D2SQuery` simulator's cache and by the Item
4(e)iiiC state synthesis branch.  Keeping them outside `ProverTransform` makes their capacity
provenance reusable in the Lemma 5.8 `E_func` proof without exposing the simulator's internal
control flow.
-/

namespace DuplexSpongeFS.ProverTransform

variable {U : Type} [SpongeUnit U] [SpongeSize]

/-- CO25 §5.4 Item 4(e)iiiC — the observable sponge state assembled from one verifier-rate
block and its freshly sampled capacity block.

This deliberately exposes only the state layout needed by the Lemma 5.8 `E_func` argument:
every emitted state and every endpoint subsequently placed in `Cache_p` is one of these states.
The cache-linking implementation itself remains private. -/
def d2sSynthesisState
    (rateSeg : Vector U SpongeSize.R)
    (capSeg : Vector U SpongeSize.C) :
    CanonicalSpongeState U :=
  (Vector.append rateSeg capSeg).cast (by
    simp [SpongeSize.R_plus_C_eq_N])

/-- The capacity of a synthesized state is exactly its corresponding sampled capacity block. -/
lemma d2sSynthesisState_capacitySegment
    (rateSeg : Vector U SpongeSize.R)
    (capSeg : Vector U SpongeSize.C) :
    CanonicalSpongeState.capacitySegment
      (d2sSynthesisState (U := U) rateSeg capSeg) = capSeg := by
  change Vector.drop ((Vector.append rateSeg capSeg).cast (by
    rw [SpongeSize.R_plus_C_eq_N])) SpongeSize.R = capSeg
  ext i
  simp only [Vector.drop_eq_cast_extract, Vector.getElem_cast, Vector.getElem_extract]
  have hi : SpongeSize.R + i < SpongeSize.R + SpongeSize.C := by
    rw [SpongeSize.R_plus_C_eq_N]
    omega
  change (rateSeg ++ capSeg)[SpongeSize.R + i]'hi = capSeg[i]
  rw [Vector.getElem_append_right]
  · simp only [Nat.add_sub_cancel_left]
    exact Eq.refl _
  · omega

end DuplexSpongeFS.ProverTransform

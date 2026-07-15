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

/-- CO25 §5.4 Item 4(e)iiiC — the ordered states assembled from the ordered rate and capacity
blocks.  This is the trace-facing provenance interface for the emitted state and the latent
`Cache_p` chain. -/
def d2sSynthesisStates
    (rateBlocks : List (Vector U SpongeSize.R))
    (caps : List (Vector U SpongeSize.C)) :
    List (CanonicalSpongeState U) :=
  (rateBlocks.zip caps).map fun rc => d2sSynthesisState (U := U) rc.1 rc.2

/-- The synthesis-state list has one state for each sampled capacity block whenever the rate
parser produced the matching number of blocks. -/
lemma d2sSynthesisStates_length
    (rateBlocks : List (Vector U SpongeSize.R))
    (caps : List (Vector U SpongeSize.C))
    (hLength : rateBlocks.length = caps.length) :
    (d2sSynthesisStates (U := U) rateBlocks caps).length = caps.length := by
  rw [d2sSynthesisStates, List.length_map, List.length_zip, hLength]
  exact min_self _

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

/-- Indexed capacity provenance for Item 4(e)iiiC: state `i` in the emitted/cache chain carries
the capacity sample `caps[i]`. -/
lemma d2sSynthesisStates_get_capacitySegment
    (rateBlocks : List (Vector U SpongeSize.R))
    (caps : List (Vector U SpongeSize.C))
    (hLength : rateBlocks.length = caps.length)
    (i : Fin caps.length) :
    CanonicalSpongeState.capacitySegment
      ((d2sSynthesisStates (U := U) rateBlocks caps).get ⟨i, by
        rw [d2sSynthesisStates_length rateBlocks caps hLength]
        exact i.isLt⟩) = caps.get i := by
  unfold d2sSynthesisStates
  rw [List.get_eq_getElem, List.get_eq_getElem]
  rw [List.getElem_map]
  rw [List.getElem_zip]
  exact d2sSynthesisState_capacitySegment _ _

end DuplexSpongeFS.ProverTransform

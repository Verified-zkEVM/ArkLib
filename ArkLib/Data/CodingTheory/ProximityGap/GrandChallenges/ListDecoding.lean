/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AryaETHn
-/

import ArkLib.Data.CodingTheory.InterleavedCode
import ArkLib.Data.CodingTheory.ProximityGap.GrandChallenges

/-!
# Unique-decoding witnesses for the Grand List-Decoding Challenge

`GrandChallenges.lean` states the Grand List-Decoding Challenge on the interleaved list size
`Λ(C^⋈m, δ)` and carries the one-sided witness types `ListLowerWitness` / `ListUpperWitness`,
but ships no constructor for either. This module supplies the first `ListLowerWitness`
constructor, in the unique-decoding regime.

## Main definitions

- `ListLowerWitness.ofUniqueDecodingRange` — a one-sided Grand List-Decoding Challenge witness
  for any code at any radius up to its relative unique-decoding radius, valid whenever the
  threshold clears a single codeword.

## Main statements

- `relUDR_interleavedCode_eq` — interleaving preserves the relative unique-decoding radius.
- `lambda_interleavedCode_le_one_of_le_relUDR` — inside that radius the interleaved point lists
  are subsingletons, so `Λ ≤ 1`.

## Why the unique-decoding regime

This mirrors `McaLowerWitness.ofUniqueDecodingRange` on the MCA side, and for the same reason:
it is the honest floor. Nothing beneath it is admitted. Interleaving preserves minimum distance
(`Code.minDist_interleavedCodeSet`), hence the unique-decoding radius, and inside that radius
every point list is a subsingleton
(`Code.isUniquelyDecodable_relativeUniqueDecodingRadius`) — both proved in-tree.

The trade is radius for provenance, as it is there. The unique-decoding radius is half the
minimum distance, well short of the Johnson and capacity radii the challenge cares about, so
this is not a route to the prize thresholds. What it buys is a `Λ ≤ 1` certificate holding for
*every* code and every interleaving width with no external admit anywhere beneath it, and the
demand it puts on the threshold — that `ε* · |F|` clear a single codeword — is the weakest any
nonvacuous list bound could make.

## Implementation note

`relativeUniqueDecodingRadius` is defined in terms of `‖·‖₀`, which is notation for `Code.dist`
— *not* `Code.minDist`, which is a separate `sInf` with `≤` relaxed to `=` in its defining set.
The interleaving lemma available here, `Code.minDist_interleavedCodeSet`, is stated on
`Code.minDist`, so it does not apply to the radius directly; `Code.dist_eq_minDist` is the
bridge, and `relUDR_interleavedCode_eq` below composes the three equalities by hand.

This is worth spelling out because the failure mode is badly disguised. Feeding a `minDist`
equation to a `dist` goal makes `rw` report that it "did not find an occurrence" of a pattern
that appears verbatim in the goal — the two print almost identically — and Lean additionally
emits a note about the target not being type-correct at `instances` transparency, which invites
the wrong diagnosis entirely (a `Matrix ι (Fin m) F` versus `ι → Fin m → F` mismatch). That
note is a red herring here. The fix is to get `dist` and `minDist` straight, not to chase
transparency.

The proofs then use `Eq.trans` and `congrArg` rather than `rw`, which keeps every step checked
by `exact` at default transparency and avoids re-entering that thicket.

## References

* [Arnon, G., Boneh, D., Fenzi, G., *Open Problems in List Decoding and Correlated
  Agreement*][ABF26]
-/

namespace ProximityGap.GrandChallenges

open scoped NNReal
open Code

variable {F ι : Type} [Field F] [Fintype F] [DecidableEq F]
    [Fintype ι] [Nonempty ι]

omit [Field F] [Fintype F] [Nonempty ι] in
/-- **Interleaving preserves the relative unique-decoding radius.** The block metric on
`ι → Fin m → F` counts a position as a disagreement when the whole `m`-tuple differs, so
interleaving leaves the minimum distance alone (`Code.minDist_interleavedCodeSet`); the block
length `|ι|` normalizing it is untouched as well. -/
theorem relUDR_interleavedCode_eq (C : Set (ι → F)) {m : ℕ} (hm : 0 < m) :
    relativeUniqueDecodingRadius (C^⋈(Fin m)) = relativeUniqueDecodingRadius C := by
  haveI : Nonempty (Fin m) := Fin.pos_iff_nonempty.mp hm
  have hmd : minDist (C^⋈(Fin m)) = minDist C := minDist_interleavedCodeSet (κ := Fin m) C
  have h : dist (C^⋈(Fin m)) = dist C :=
    (dist_eq_minDist _).trans (hmd.trans (dist_eq_minDist C).symm)
  exact congrArg (fun d : ℕ => (((d : ℝ≥0) - 1) / 2) / (Fintype.card ι : ℝ≥0)) h

omit [Field F] [Fintype F] [Nonempty ι] in
/-- **Inside the unique-decoding radius the interleaved list is a subsingleton.** Combining
`relUDR_interleavedCode_eq` with unique decodability of every code at its own relative
unique-decoding radius. -/
theorem lambda_interleavedCode_le_one_of_le_relUDR (C : Set (ι → F)) {m : ℕ} (hm : 0 < m)
    {δ : ℝ≥0} (hδ : δ ≤ relativeUniqueDecodingRadius C) :
    Lambda (C^⋈(Fin m)) (δ : ℝ) ≤ 1 := by
  refine le_trans (Lambda_mono ?_)
    (isUniquelyDecodable_iff_Lambda_le.mp
      (isUniquelyDecodable_relativeUniqueDecodingRadius (C^⋈(Fin m))))
  calc (δ : ℝ)
      ≤ (relativeUniqueDecodingRadius C : ℝ) := by exact_mod_cast hδ
    _ = (relativeUniqueDecodingRadius (C^⋈(Fin m)) : ℝ) := by
        exact_mod_cast (relUDR_interleavedCode_eq C hm).symm

/-- Builds a one-sided list-decoding witness from unique decodability: at any radius `δ` up to
the relative unique-decoding radius of `C`, the interleaved list size is at most `1`, so any
threshold whose `ε_star · |F|` clears a single codeword is witnessed.

The radius hypothesis is on the base code, not the interleaved one —
`relUDR_interleavedCode_eq` identifies the two, and the base-code form is the one a caller can
discharge. -/
noncomputable def ListLowerWitness.ofUniqueDecodingRange
    (C : Set (ι → F)) (m : ℕ) (δ ε_star : ℝ≥0)
    (hm : 0 < m)
    (hδ_le_one : δ ≤ 1)
    (hδ : δ ≤ relativeUniqueDecodingRadius C)
    (hle : (1 : ENNReal) ≤ (ε_star : ENNReal) * (Fintype.card F : ENNReal)) :
    ListLowerWitness C m ε_star :=
  ListLowerWitness.ofLe hδ_le_one
    (le_trans
      (by exact_mod_cast lambda_interleavedCode_le_one_of_le_relUDR C hm hδ) hle)

end ProximityGap.GrandChallenges

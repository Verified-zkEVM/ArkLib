/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AryaETHn
-/

import ArkLib.Data.CodingTheory.InterleavedCode
import ArkLib.Data.CodingTheory.JohnsonBound.Family
import ArkLib.Data.CodingTheory.ProximityGap.GrandChallenges

/-!
# List-decoding witnesses for the Grand List-Decoding Challenge

`GrandChallenges.lean` states the Grand List-Decoding Challenge on the interleaved list size
`Λ(C^⋈m, δ)` and carries the one-sided witness types `ListLowerWitness` / `ListUpperWitness`,
together with the generic shapes that repackage a `Λ` bound as a witness
(`ListLowerWitness.ofLe`, `ListUpperWitness.ofGt`, `ListUpperWitness.ofEncardGt`). What it has
no constructor for is a witness whose `Λ` bound comes from coding theory rather than from the
caller. This module supplies the first two, one in the unique-decoding regime and one at the
Johnson radius.

## Main definitions

- `ListLowerWitness.ofUniqueDecodingRange` — a witness for any code at any radius up to its
  relative unique-decoding radius, valid whenever the threshold clears a single codeword.
- `ListLowerWitness.ofJohnsonBound` — a witness at the Johnson radius of the *interleaved*
  code, valid whenever the threshold clears `ℓ` codewords.

## Main statements

- `relUDR_interleavedCode_eq` — interleaving preserves the relative unique-decoding radius.
- `lambda_interleavedCode_le_one_of_le_relUDR` — inside that radius the interleaved point lists
  are subsingletons, so `Λ ≤ 1`.
- `lambda_interleavedCode_le_of_le_johnson` — at the Johnson radius, `Λ ≤ ℓ`.

## The two regimes

The unique-decoding constructor mirrors `McaLowerWitness.ofUniqueDecodingRange` on the MCA side,
and is the honest floor: interleaving preserves minimum distance
(`Code.minDist_interleavedCodeSet`), hence the unique-decoding radius, and inside that radius
every point list is a subsingleton (`Code.isUniquelyDecodable_relativeUniqueDecodingRadius`).
Both are proved in-tree, so nothing beneath it is admitted. But the radius is only half the
minimum distance, far short of what the challenge cares about.

The Johnson constructor reaches much further, and — unlike its MCA counterpart
`McaLowerWitness.ofJohnsonRangeBound`, which rests on the external `[BCHKS25]` admit
`rs_mcaError_le_in_johnson_range` — it is *also* admit-free:
`CodingTheory.johnson_bound_lambda_le_ell` is stated over an arbitrary finite alphabet and is
itself axiom-clean, so it applies to the interleaved code at alphabet `Fin m → F` directly.

Note the alphabet the Johnson radius is computed at. For the interleaved code that is
`q = |F|^m`, not `|F|`. The relative minimum distance is unchanged, so the whole effect of `m`
on the bound enters through `q` — and it enters against us. Writing `c = q/(q-1)`,

`J_q(δ) = (1/c) · (1 - √(1 - c·δ)) = δ · h(c·δ)`  where  `h(u) = (1 - √(1 - u))/u`,

and `h` is increasing on `(0, 1]`, so `J_q(δ)` is increasing in `c` and therefore *decreasing*
in `q`, tending to `1 - √(1 - δ)` from above. So the larger alphabet of the interleaved code
narrows this Johnson radius rather than widening it: `Jqℓ 4 2 1 ≈ 0.317` against
`Jqℓ 2 2 1 = 0.5`. (The comparison lives in the regime where the radicand `1 - c·δ` is
non-negative; outside it `Real.sqrt` is clamped to `0` and `J_q` collapses to `1 - 1/q`.)
`lambda_interleavedCode_le_of_le_johnson` states its hypothesis at `q = |F|^m` either way — the
interleaved code's own alphabet is what the Johnson bound is applied at, so the theorem is
correct as stated; what shrinks with `m` is only the room a caller has to work in.

Neither constructor resolves the challenge, but the gap is narrower than a list budget. `ℓ` is
a parameter of `ofJohnsonBound`, which accepts any proof of `ℓ ≤ ε* · |F|`, so the prize's
`Λ ≤ ε* · |F|` shape is already expressible here rather than being cut off at a fixed constant.
The binding constraint is the radius: `Jqℓ q ℓ δ_min` is capped by `J_q(δ_min)` however large
`ℓ` grows, and a resolution needs a full per-rate `GrandListResolution` — safety at every grid
point, or an exact adjacent-grid crossing — plus a concrete `ListUpperWitness`, none of which
this module supplies. What it does supply are the two admit-free footholds the challenge API
previously lacked entirely.

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
* [Ben-Sasson, E., Carmon, D., Haböck, U., Kopparty, S., Saraf, S., *On Proximity Gaps for
  Reed-Solomon Codes*][BCHKS25] — cited above only for the admit underlying the MCA-side
  Johnson-range witness, which this module's counterpart does not need.
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
  have : Nonempty (Fin m) := Fin.pos_iff_nonempty.mp hm
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

/-! ## The Johnson regime -/

omit [Field F] in
/-- **The interleaved list size at the Johnson radius.** `CodingTheory.johnson_bound_lambda_le_ell`
applied to `C^⋈(Fin m)`, with its two code-dependent inputs re-expressed on the base code: the
alphabet size becomes `|F|^m`, and the minimum distance is unchanged
(`Code.minDist_interleavedCodeSet`).

Stating the radius on the base code is what makes this usable — a caller has `C`, not
`C^⋈(Fin m)`, in hand. -/
theorem lambda_interleavedCode_le_of_le_johnson (C : Set (ι → F)) {m ℓ : ℕ}
    (hm : 0 < m) (hℓ : 1 ≤ ℓ) {δ : ℝ≥0}
    (hδ : (δ : ℝ) ≤ JohnsonBound.Jqℓ ((Fintype.card F : ℚ) ^ m) (ℓ : ℚ)
            ((Code.minDist C : ℚ) / (Fintype.card ι : ℚ))) :
    Lambda (C^⋈(Fin m)) (δ : ℝ) ≤ (ℓ : ℕ∞) := by
  have : Nonempty (Fin m) := Fin.pos_iff_nonempty.mp hm
  have hcard : (Fintype.card (Fin m → F) : ℚ) = (Fintype.card F : ℚ) ^ m := by
    simp
  have hmd : (Code.minDist (C^⋈(Fin m)) : ℚ) = (Code.minDist C : ℚ) := by
    exact_mod_cast minDist_interleavedCodeSet (κ := Fin m) C
  refine le_trans (Lambda_mono ?_)
    (CodingTheory.johnson_bound_lambda_le_ell (C^⋈(Fin m)) ℓ hℓ)
  rw [hcard, hmd]
  exact hδ

/-- Builds a one-sided list-decoding witness from the Johnson bound for the interleaved code: at
any radius up to `J_{q,ℓ}` computed at `q = |F|^m` and the base code's relative minimum distance,
the interleaved list size is at most `ℓ`, so any threshold whose `ε_star · |F|` clears `ℓ`
codewords is witnessed.

Unlike `McaLowerWitness.ofJohnsonRangeBound` on the MCA side, nothing below this constructor is
admitted. -/
noncomputable def ListLowerWitness.ofJohnsonBound
    (C : Set (ι → F)) (m ℓ : ℕ) (δ ε_star : ℝ≥0)
    (hm : 0 < m)
    (hℓ : 1 ≤ ℓ)
    (hδ_le_one : δ ≤ 1)
    (hδ : (δ : ℝ) ≤ JohnsonBound.Jqℓ ((Fintype.card F : ℚ) ^ m) (ℓ : ℚ)
            ((Code.minDist C : ℚ) / (Fintype.card ι : ℚ)))
    (hle : (ℓ : ENNReal) ≤ (ε_star : ENNReal) * (Fintype.card F : ENNReal)) :
    ListLowerWitness C m ε_star :=
  ListLowerWitness.ofLe hδ_le_one
    (le_trans
      (by exact_mod_cast lambda_interleavedCode_le_of_le_johnson C hm hℓ hδ) hle)

end ProximityGap.GrandChallenges

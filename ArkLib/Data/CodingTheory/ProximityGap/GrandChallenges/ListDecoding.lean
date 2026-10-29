/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AryaETHn
-/
module

public import ArkLib.Data.CodingTheory.JohnsonBound.Family
public import ArkLib.Data.CodingTheory.ListDecodability.Bounds.Interleaved
public import ArkLib.Data.CodingTheory.ProximityGap.GrandChallenges

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

The underlying list-size bounds live with their subjects:
`Code.relativeUniqueDecodingRadius_interleavedCodeSet`,
`InterleavedCode.lambda_interleaved_le_one_of_le_relUDR`, and
`CodingTheory.lambda_interleaved_le_of_le_johnson`.

## The two regimes

The unique-decoding constructor mirrors `McaLowerWitness.ofUniqueDecodingRange` on the MCA side,
and is the honest floor: interleaving preserves minimum distance
(`Code.minDist_interleavedCodeSet`), hence the unique-decoding radius, and inside that radius
every point list is a subsingleton (`Code.isUniquelyDecodable_relativeUniqueDecodingRadius`).
Both are proved in-tree. But the radius is only half the
minimum distance, far short of what the challenge cares about.

The Johnson constructor is the Johnson bound ([Joh62]; Theorem 3.2 of [ABF26]) applied to the
interleaved code. It reaches much further.
`CodingTheory.johnson_bound_lambda_le_ell` is stated over an arbitrary finite alphabet and is
axiom-clean, so it applies to the interleaved code at alphabet `Fin m → F` directly. Its MCA
counterpart `McaLowerWitness.ofJohnsonRangeBound` also has a proved input:
`rs_mcaError_le_in_johnson_range` follows from [DKT26], with the printed constant of
[BCHKS25] Theorem 4.6.

The Johnson radius is computed at the interleaved alphabet `q = |F|^m`, the alphabet of
`C^⋈(Fin m)`. Where the radicand is non-negative, `J_q` decreases to `J(δ) = 1 - √(1 - δ)` as
`q` grows, so this is at least the alphabet-free Johnson radius.

## References

* [Arnon, G., Boneh, D., Fenzi, G., *Open Problems in List Decoding and Correlated
  Agreement*][ABF26]
* [Ben-Sasson, E., Carmon, D., Haböck, U., Kopparty, S., Saraf, S., *On Proximity Gaps for
  Reed-Solomon Codes*][BCHKS25]
* [DKT26] (proof of the Johnson-range MCA bound).
* [Johnson, S. M., *A new upper bound for error-correcting codes*][Joh62]
-/

@[expose] public section

namespace ProximityGap.GrandChallenges

open scoped NNReal
open Code

variable {F ι : Type} [Field F] [Fintype F] [DecidableEq F]
    [Fintype ι] [Nonempty ι]

/-- Builds a one-sided list-decoding witness from unique decodability: at any radius `δ` up to
the relative unique-decoding radius of `C`, the interleaved list size is at most `1`, so any
threshold whose `ε_star · |F|` clears a single codeword is witnessed.

The radius hypothesis is on the base code, not the interleaved one —
`Code.relativeUniqueDecodingRadius_interleavedCodeSet` identifies the two, and the base-code form
is the one a caller can discharge. -/
noncomputable def ListLowerWitness.ofUniqueDecodingRange
    (C : Set (ι → F)) (m : ℕ) (δ ε_star : ℝ≥0)
    (hm : 0 < m)
    (hδ_le_one : δ ≤ 1)
    (hδ : δ ≤ relativeUniqueDecodingRadius C)
    (hle : (1 : ENNReal) ≤ (ε_star : ENNReal) * (Fintype.card F : ENNReal)) :
    ListLowerWitness C m ε_star :=
  ListLowerWitness.ofLe hδ_le_one
    (le_trans
      (by exact_mod_cast InterleavedCode.lambda_interleaved_le_one_of_le_relUDR C hm hδ) hle)

/-! ## The Johnson regime -/

/-- Builds a one-sided list-decoding witness from the Johnson bound for the interleaved code: at
any radius up to `J_{q,ℓ}` computed at `q = |F|^m` and the base code's relative minimum distance,
the interleaved list size is at most `ℓ`, so any threshold whose `ε_star · |F|` clears `ℓ`
codewords is witnessed.

The list-size bound and the corresponding Johnson-range MCA bound are both proved in-tree. -/
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
      (by exact_mod_cast CodingTheory.lambda_interleaved_le_of_le_johnson C hm hℓ hδ) hle)

end ProximityGap.GrandChallenges

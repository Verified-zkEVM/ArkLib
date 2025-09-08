/-
Lemma 4.5 (Ligero): Probability of bad points on the row span.

This file is a blueprint for the proof of Lemma 4.5. It outlines the
structure and the intermediate lemmas to be proved in the sibling files
of this directory. No statements are proved here; this is a roadmap.

High‑level statement (informal):
Let `L = RS_{F,n,k,η}` have distance `d = n - k + 1` and let `e < d/3`.
If `Δ(U, L^m) > e` for an `m×n` matrix `U`, then for a uniformly random
`w` in the row span `L* = rowSpan U`,

  Pr[ distFromCode(w, L) ≤ e ] ≤ d / |F|.

We implement this with a counting argument on cosets of the 1‑dimensional
subspace spanned by a particular direction `v* ∈ rowSpan U` that is
farther than `e` from `L` (via Lemma 4.3).

Proof plan:
- Step A (Direction existence): From `Δ(U, L^m) > e` and `3e < d`, obtain
  a vector `v* ∈ rowSpan U` with `distFromCode(v*, L) > e`.
  Source: Lemma 4.3 (file: InterleavedCode/Lemma43.lean).

- Step B (Per‑line counting): For any `x : F^n`, consider the affine line
  `ℓ_x := { x + α • v* | α ∈ F }`. By Lemma 4.4 (line dichotomy), for each
  `x` the number of `α` with `distFromCode(x + α•v*, L) ≤ e` is ≤ `d`.
  The alternative case that all points on the line are within distance `≤ e`
  is ruled out by `distFromCode(v*, L) > e` (take `x = 0, α = 1`).

- Step C (Coset averaging): Partition `rowSpan U` into cosets of the
  1‑dimensional subspace `⟪v*⟫`. Each coset has size `|F|` and, by Step B,
  contains at most `d` “good” elements (≤ e close to `L`). Therefore the
  total number of good elements in `rowSpan U` is ≤ `(#cosets) * d`.
  Since `#rowSpan U = (#cosets) * |F|`, the uniform probability is ≤ `d/|F|`.

Files and responsibilities:
- 01_CosetAveraging.lean  — finite coset partition and the probability bound
- 02_LineCounting.lean    — apply Lemma 4.4 to show ≤ d good points per line
- 03_ExistDirection.lean  — import Lemma 4.3 to get a far direction in row span
- 04_Assemble.lean        — combine A+B+C to derive Lemma 4.5

Integration notes:
- The main theorem lives in `ProximityToRS/Lemma45.lean` as `probOfBadPts`.
  Once helper lemmas are implemented, it can import the above files and
  replace the placeholder proof.

Dependencies:
- Lemma 4.3: `InterleavedCode/Lemma43.lean` (exists far direction in row span)
- Lemma 4.4: `ProximityToRS/Lemma44.lean` (line dichotomy bound ≤ d)

-/

-- This file intentionally contains no executable code.


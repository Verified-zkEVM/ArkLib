---
kind: paper
bibkey: BRW26
title: "Flock: Fast Proving for Batch Boolean Computations"
year: 2026
bib_source: blueprint/src/references.bib
canonical_url: https://eprint.iacr.org/2026/1329
status: seeded
related_concepts:
  - ring-switching
related_modules:
  - ArkLib/ProofSystem/RingSwitching/Packing/ScalarHead/Layout.lean
  - ArkLib/ProofSystem/RingSwitching/Packing/ScalarHead/Quirky.lean
  - ArkLib/ProofSystem/RingSwitching/Packing/Multiplier.lean
---

# BRW26

## At A Glance

Bünz, Rothblum and Wang's *Flock: Fast Proving for Batch Boolean Computations* is a hash-based
SNARK for batched Boolean computations. Its Appendix B reduces a scalar evaluation claim over a
small field to a packed opening by coordinate packing and weighted scalar reconstruction.

## What ArkLib Uses From This Paper

- **Faithful coordinates.** Base-field coordinates of extension-field values are transposed and
  packed. Independence of a basis does not justify treating arbitrary extension-field values as
  base-field coordinates; ArkLib's `PackingData.transpose` works on coordinates only.
- **Ordinary and quirky layouts.** Ordinary claims use equality weights. Appendix B.3's quirky
  claims use the weight `L_σ(ζ) · eq(ρ, b)` in the `(σ, b)` packing order. `ScalarHead/Quirky.lean`
  defines the interpolated extension, proves its degree and node values, and proves the weighted
  reconstruction `quirkyEval_eq_sum`.
- **Multiplier.** The public multiplier is evaluated with multiplication matrices and Boolean
  interpolation at each layer. `Multiplier.lean` proves the evaluator equals the multilinear
  extension of the Boolean table at every challenge point (`evaluateMultiplier_eq`).

## Main ArkLib Touchpoints

- [`ScalarHead/Layout.lean`](../../../ArkLib/ProofSystem/RingSwitching/Packing/ScalarHead/Layout.lean) — prefix and suffix layouts.
- [`ScalarHead/Quirky.lean`](../../../ArkLib/ProofSystem/RingSwitching/Packing/ScalarHead/Quirky.lean) — the quirky layout.
- [`Multiplier.lean`](../../../ArkLib/ProofSystem/RingSwitching/Packing/Multiplier.lean) — the multiplication-matrix evaluator.
- [Ring-switching concept](../concepts/ring-switching.md).

## Open Formalization Gaps

- Flock's scalar-claim protocol head, its completeness and knowledge contracts, and its
  candidate-list (out-of-domain) binding analysis from Appendix C are not formalized.

## Source Access

- [Cryptology ePrint Archive, 2026/1329](https://eprint.iacr.org/2026/1329).
- [Bibliography](../../../blueprint/src/references.bib), key `BRW26`.
- Locators: Appendix B pp. 36–40; multiplication matrices B.2.1 and B.4; list/out-of-domain
  analysis Appendix C.

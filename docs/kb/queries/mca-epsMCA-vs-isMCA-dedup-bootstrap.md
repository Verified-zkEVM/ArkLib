# MCA representation unification

Status: resolved.

ArkLib has one generator-parametric MCA event and one numeric error value:

- `CoreDefinitions.IsMCA` accepts an arbitrary generator and an `F`-module alphabet.
- `CoreDefinitions.mcaError G C : ℝ → ENNReal` is the worst-case event probability.
- `CoreDefinitions.IsMCAGenerator` is definitionally a pointwise bound on `mcaError`.
- `ProximityGap.epsMca` is the affine-line specialization
  `mcaError (AffineLineGenerator F)`.

This representation covers both axes that the former APIs handled separately: module alphabets
and non-affine generators. Interleaving and projected-generator results therefore target
`mcaError` directly, and the Grand Challenges API consumes the same value.

For current conventions and module routing, see
[`proximity-error-conventions.md`](../../wiki/proximity-error-conventions.md).

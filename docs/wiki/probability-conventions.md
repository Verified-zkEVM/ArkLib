# Probability Conventions

ArkLib keeps reusable finite-probability helpers in `ArkLib/Data/Probability/`.
Generic lemmas from this subtree should live in `namespace Probability`, and callers should use
qualified names such as `Probability.prob_uniform_eq_card_filter_div_card` or open the namespace
locally near the use site.

Do not add new root-level `prob_*` or `Pr_*` helper names for generic finite-probability facts.
The namespace consolidation from PR #597 is intentional because it makes exports from
`ArkLib/Data/Probability/Instances.lean` and `ArkLib/Data/Probability/Combinatorial.lean`
legible and keeps the root namespace from accumulating ad hoc helper names.

Use `namespace ProbabilityTheory` only for Mathlib probability notation and measure-theory
extensions, such as declarations in `ArkLib/Data/Probability/Notation.lean`. If a declaration is a
root-namespace extension to an existing Mathlib type or namespace, use Lean's `_root_` qualification
inside the probability file instead of moving the surrounding ArkLib helpers out of
`namespace Probability`.

If a downstream project has a concrete compatibility break on an older root-level helper name, add
an explicit, temporary compatibility export for that exact declaration and document the consumer.
Do not silently revert the namespace consolidation or reintroduce broad root-level aliases.

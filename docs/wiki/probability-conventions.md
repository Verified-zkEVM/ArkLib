# Probability Conventions

ArkLib keeps reusable finite-probability helpers in `ArkLib/Data/Probability/`.
Generic lemmas from this subtree should live in `namespace Probability`, and callers should use
qualified names such as `Probability.prob_uniform_eq_card_filter_div_card` or open the namespace
locally near the use site.

Do not add new root-level `prob_*` or `Pr_*` helper names for generic finite-probability facts.
The namespace consolidation is intentional: it makes exports from
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

## Migrating an in-flight branch

The consolidation is a **breaking change with no alias layer**, taken deliberately. Nineteen
helpers that used to sit at the root namespace now live in `Probability`:

`prob_tsum_form_singleton`, `prob_tsum_form_split_first`, `prob_tsum_form_doubleton`,
`prob_uniform_eq_card_filter_div_card`, `prob_uniform_singleton_finFun_eq`,
`prob_split_uniform_sampling_of_prod`, `prob_split_uniform_sampling_of_equiv_prod`,
`prob_split_last_uniform_sampling_of_finFun`, `prob_uniform_eq_ofReal`,
`prob_marginalization_first_of_prod`, `prob_const_and_prop_eq_ite`,
`prob_schwartz_zippel_mv_polynomial`, `Pr_le_Pr_of_implies`, `Pr_multi_let_equiv_single_let`,
`Pr_add_split_by_complement`, `Pr_congr`, `Pr_or_le`, `Pr_exists_le`, `Pr_seq_le_of_forall_le`.

**The fix is one line per file: add `open Probability` next to the existing
`open scoped ProbabilityTheory`.** The failure mode is `Unknown identifier`, so it surfaces
immediately and cannot be missed. Note that `Probability` and Mathlib's `ProbabilityTheory` are
different namespaces and both are usually wanted.

Note also that `git merge-tree` does not catch this: a branch that adds a new file using a moved
helper merges textually clean and then fails to build. When checking whether a branch is affected,
grep it for the names above, or build the merged tree.

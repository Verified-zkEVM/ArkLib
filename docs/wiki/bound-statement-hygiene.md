# Bound-Statement Hygiene

Authoring rules for theorems whose content is a numeric bound on an error or list-size carrier
(`epsCa`, `mcaError`, `Lambda`, and the protocol-level certificates built on them). The goal is
that **no statement requires prose documentation to be used safely**: whether a bound is
informative at given parameters must be checkable by the elaborator at the use site, never left
as reader discipline.

Adopted 2026-08-18 after the correlated-agreement discharge wave; the wrappers in
`JohnsonBound/Family.lean`, `CapacityBounds/*.lean`, `BCIKS20/EpsCa.lean`,
`Connections/ListDecodingAndCA/GCXK25.lean`, and `ListDecodability/Bounds/*.lean` are the
reference implementations.

## The two-layer rule

Every numeric bound has two faces with different jobs:

1. **Audit layer (source-native).** The statement exactly as printed in the source paper,
   including its deliberately loose constants. This is the *only* acceptable form for an
   **admitted** (`sorry`) statement: an admit is a trust liability, and pinning it verbatim to
   the print is what makes it auditable. Never "improve" an admitted statement — a printed
   theorem can be looser than its own proof supports (BCHKS25 Thm 4.6's multiplicity is the
   canonical example), and tightening an admit silently strengthens what the library assumes.

2. **Consumption layer (threshold form).** The public face consumers cite, added **in the same
   PR that proves the statement**:

   ```lean
   theorem foo_le_of_budget … (ε_star : ℝ≥0)
       (hbudget : ENNReal.ofReal (<the explicit formula>) ≤ (ε_star : ENNReal)) :
       <carrier> ≤ (ε_star : ENNReal) :=
     le_trans (foo_le …) hbudget
   ```

   The security target is an argument and the numeric budget check is a hypothesis, so a caller
   *cannot* instantiate the theorem in a parameter range where the formula exceeds their target:
   the use-site `norm_num`/`decide` obligation fails instead of a trivially-true bound leaking
   into prose. Naming: `<name>_of_budget`. For `Lambda` bounds the target is `(L : ℕ)` and the
   conclusion is on the bare `ℕ∞`-valued `Lambda` (the shape list-size consumers take), with
   `ENat.toENNReal_le` closing the coercion gap.

Wrappers add no logical strength — they are `le_trans` — and that is the point: they relocate
the contentful-range check from documentation into types.

## Checks before adding or accepting a bound statement

- **Upper bounds** (`carrier ≤ formula`): always true-able, but content-free where the formula
  meets the carrier's ceiling. Never clamp the statement (`min 1 formula` adds nothing); ship
  the threshold form instead.
- **Lower bounds** (`formula ≤ carrier`): if the hypotheses admit parameters where the formula
  exceeds the carrier's ceiling (`epsCa`, `mcaError` ≤ 1 — `Lambda` is a count and has none),
  the statement is **false there, hence unprovable**; for an admit this is a landmine. Verify
  the guard arithmetic before accepting the admit (e.g. T4.16 self-guards via `β > c + 2`;
  T5.4 via `ofReal (1 - 1/|F|)` plus an explicit `8 ≤ |F|`).
- **Existence statements**: check the leading `∀`-guards are satisfiable (e.g. arbitrarily
  large char-2 fields exist for `exists_rs_epsCa_large_at_johnson_radius`); an unsatisfiable
  guard makes the theorem vacuously true and its proof meaningless.
- **New predicates and structures**: surface non-degeneracy hypotheses explicitly with a
  comment saying what breaks without them, rather than leaving degenerate instantiations
  representable (`rs_epsCa_large_below_johnson_radius`'s `8 ≤ |F|` is the model).
- **Attack-side results** (lower bounds intended as witnesses): route consumers through the
  witness constructors in `ProximityGap/GrandChallenges.lean` (`McaLowerWitness.of…`,
  `McaUpperWitness.of…`) rather than raw citation; the constructors carry the threshold
  comparison in their fields.

## What not to wrap

- Transport lemmas whose right-hand side contains another carrier
  (`lambda_interleaved_le_choose_mul_pow`, `rs_Lambda_extended_le_of_epsCa`): consumers must
  bound the inner carrier first, at which point they chain directly.
- Interface lemmas whose bound side is already a variable (`Lambda_le_iff_*`,
  `isListDecodable_iff_*`, the `GrandChallenges` grid API): these are already target-shaped.
- Monotonicity/comparison lemmas between carriers.

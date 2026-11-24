/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Coratger
-/
module

public import ArkLib.ProofSystem.ConstraintSystem.Lookup
public import ArkLib.Data.Polynomial.LogDerivative

/-!
# Lookups by logarithmic derivatives

LogUp checks a lookup with one identity of rational functions [Hab22].

This file states that identity for the lookup relation over lists ([Hab22], Lemma 5).

The forward direction holds in every field.

The converse needs each of `1, 2, ...` up to the largest query count to be nonzero in `F`.

## Main statements

- `Lookup.LogUp.relation_iff_exists_logDerivSum_eq`: the bound is the largest query count.
- `Lookup.LogUp.relation_iff_exists_logDerivSum_eq_of_length`: the bound is the query count.

## References

* [Haböck, U., *Multivariate lookups based on logarithmic derivatives*][Hab22]
-/

@[expose] public section

namespace Lookup.LogUp

open RatFunc

variable {F : Type*} [Field F]

/-- **Lookups by logarithmic derivatives.**

When no count of a query vanishes in `F`, these are equivalent:
- the queries lie in the table;
- `sum_j 1 / (X - f_j) = sum_i m_i / (X - t_i)` for some multiplicities `m`. -/
theorem relation_iff_exists_logDerivSum_eq [DecidableEq F] (f t : List F)
    (hp : NatCastNeZeroUpTo F f.maxCount) :
    (f, t) ∈ Lookup.relation ↔
      ∃ m : List F, m.length = t.length ∧
        logDerivSum (f.map (·, 1)) = logDerivSum (t.zip m) :=
  subset_iff_exists_logDerivSum_eq f t hp

/-- Lookups by logarithmic derivatives, with the number of queries as the bound. -/
theorem relation_iff_exists_logDerivSum_eq_of_length (f t : List F)
    (hp : NatCastNeZeroUpTo F f.length) :
    (f, t) ∈ Lookup.relation ↔
      ∃ m : List F, m.length = t.length ∧
        logDerivSum (f.map (·, 1)) = logDerivSum (t.zip m) :=
  subset_iff_exists_logDerivSum_eq_of_length f t hp

end Lookup.LogUp

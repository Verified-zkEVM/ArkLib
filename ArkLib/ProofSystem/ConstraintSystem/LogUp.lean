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

LogUp checks a lookup with one identity of rational functions.

That is Haböck, "Multivariate lookups based on logarithmic derivatives", eprint 2022/1530.

The algebra lives with the rational functions.

This file states it for the lookup relation over lists.
-/

@[expose] public section

namespace Lookup.LogUp

open RatFunc

variable {F : Type*} [Field F]

/-- **Lookups by logarithmic derivatives (Lemma 5).**

In characteristic above the number of queries, the queries lie in the table exactly when,
for some multiplicities, sum_j 1 / (X - f_j) = sum_i m_i / (X - t_i). -/
theorem relation_iff_exists_logDerivSum_eq (f t : List F)
    (hp : ∀ n : ℕ, 0 < n → n ≤ f.length → (n : F) ≠ 0) :
    (f, t) ∈ Lookup.relation ↔
      ∃ m : List F, m.length = t.length ∧
        logDerivSum (f.map (·, 1)) = logDerivSum (t.zip m) :=
  subset_iff_exists_logDerivSum_eq f t hp

end Lookup.LogUp

/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Attila Vajda, Ilia Vlasov
-/

import Mathlib.LinearAlgebra.Lagrange

/-!
# Polynomial determination from evaluations on a large enough finite set

Mathlib's `Polynomial.eq_of_degrees_lt_of_eval_finset_eq` compares the degrees against `#s`
itself. The two lemmas here are the `n ≤ #s` restatements used throughout ArkLib, phrased with
`degree` and with `natDegree`.
-/

namespace Polynomial

variable {𝔽 : Type*} [Field 𝔽]

/-- Two polynomials of degree `< n` that agree on a finite set of at least `n` points are equal. -/
lemma eq_of_eval_eq_degree {p q : 𝔽[X]} {n : ℕ}
    (hp : p.degree < .some n) (hq : q.degree < .some n) (s : Finset 𝔽) :
    s.card ≥ n → (∀ x ∈ s, p.eval x = q.eval x) → p = q := fun hs =>
  eq_of_degrees_lt_of_eval_finset_eq s (hp.trans_le (Nat.cast_le.mpr hs))
    (hq.trans_le (Nat.cast_le.mpr hs))

/-- Two polynomials of `natDegree < n` that agree on a finite set of at least `n` points are
+equal. -/
lemma eq_of_eval_eq_natDegree {p q : 𝔽[X]} {n : ℕ}
    (hp : p.natDegree < n) (hq : q.natDegree < n) (s : Finset 𝔽) :
    s.card ≥ n → (∀ x ∈ s, p.eval x = q.eval x) → p = q :=
  eq_of_eval_eq_degree (degree_le_natDegree.trans_lt (Nat.cast_lt.mpr hp))
    (degree_le_natDegree.trans_lt (Nat.cast_lt.mpr hq)) s

end Polynomial

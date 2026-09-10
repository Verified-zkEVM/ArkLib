/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.Ordinary.QuotientLift.Series
public import ArkLib.ToCompPoly.Multivariate.PartialDerivative
/-!
# Newton lifting over a materialized quotient algebra

A state stores a series `S(T,U)` and an approximate inverse `G(T,U)` of `Q_Y(center+T,S)`.
At precision `m`, Newton's update is `S' = S - Q(center+T,S)G` modulo `T^(2m)`.
We then update the inverse to `G' = G(2 - Q_Y(center+T,S')G)` at the same precision.
Both updates reduce every coefficient modulo the parameter modulus `h(U)`.

The initial modular inverse is shared by all geometric roots of `h`; none of those roots is
computed. `newtonLoop` doubles precision until it reaches `k` and trims the last result to exactly
that precision. Its fuel is only a termination bound: the `k ≤ m` guard stops further iterations.

This is an executable precision-doubling algorithm. Correctness is proved in `NewtonProof`;
a near-linear arithmetic bound still requires costed evaluation and polynomial backends.
-/

@[expose] public section

namespace ReedSolomon.HiddenDerivative.Ordinary.QuotientLift
open CompPoly CompPoly.CPolynomial
variable {E : Type*} [Field E] [BEq E] [LawfulBEq E]

/-- Keep degrees below `m` in the series variable and reduce each coefficient modulo `h`. -/
def reduceSeries (h : CPolynomial E) (m : ℕ) (S : Series E) : Series E :=
  CPolynomial.ofArray (Array.ofFn fun i : Fin m => (S.coeff i).modByMonic h)

/-- Coefficient reduction and precision truncation are the two independent parts of
normalization. -/
theorem coeff_reduceSeries (h : CPolynomial E) (m : ℕ) (S : Series E) (i : ℕ) :
    (reduceSeries h m S).coeff i = if i < m then (S.coeff i).modByMonic h else 0 := by
  rw [reduceSeries, CPolynomial.coeff_ofArray]
  simp [Array.getD]

/-- The branch series and its approximate derivative inverse, shared over all modulus roots. -/
structure NewtonState where
  /-- Agrees with every represented branch modulo the current power of T. -/
  series : Series E
  /-- Inverts Q_Y(center+T,series) modulo the same power of T. -/
  inverse : Series E

/-- Double branch precision, then repair the inverse at the updated branch to the same precision. -/
def newtonStep (Q : CPoly.CMvPolynomial 2 E) (center : E)
    (h : CPolynomial E) (m : ℕ) (state : NewtonState (E := E)) : NewtonState (E := E) :=
  -- Q(S) vanishes to order m; multiplying by the inverse cancels the next m coefficients.
  let series := reduceSeries h (2 * m)
    (state.series - residual Q center state.series * state.inverse)
  -- The derivative changed with S. Newton inversion restores twice the inverse precision.
  let inverse := reduceSeries h (2 * m)
    (state.inverse * (2 - residual (CPoly.CMvPolynomial.partialDerivative 1 Q) center series *
      state.inverse))
  ⟨series, inverse⟩

/-- Iterate precision doubling, stopping as soon as all requested coefficients are determined. -/
def newtonLoop (Q : CPoly.CMvPolynomial 2 E) (center : E)
    (h : CPolynomial E) (k : ℕ) : ℕ → ℕ → NewtonState (E := E) → Series E
  | 0, _, state => reduceSeries h k state.series
  | fuel + 1, m, state =>
      if k ≤ m then reduceSeries h k state.series
      else newtonLoop Q center h k fuel (2 * m) (newtonStep Q center h m state)

/-- Compute the initial modular inverse and lift all regular initial values simultaneously. -/
def newtonLift? (Q : CPoly.CMvPolynomial 2 E) (center : E)
    (h : CPolynomial E) (k : ℕ) : Option (Series E) := do
  let inverse ← inverseMod? (slope Q center) h
  return newtonLoop Q center h k k 1 ⟨CPolynomial.C CPolynomial.X, CPolynomial.C inverse⟩

/-- Coprimality of the initial slope and modulus discharges the only failure guard. -/
theorem newtonLift_exists (Q : CPoly.CMvPolynomial 2 E) (center : E)
    (h : CPolynomial E) (k : ℕ) (hcoprime : IsCoprime (slope Q center).toPoly h.toPoly) :
    ∃ out, newtonLift? Q center h k = some out := by
  obtain ⟨inverse, hinverse⟩ := (inverseMod_exists_iff_coprime _ _).2 hcoprime
  refine ⟨newtonLoop Q center h k k 1
    ⟨CPolynomial.C CPolynomial.X, CPolynomial.C inverse⟩, ?_⟩
  simp [newtonLift?, hinverse]

end ReedSolomon.HiddenDerivative.Ordinary.QuotientLift

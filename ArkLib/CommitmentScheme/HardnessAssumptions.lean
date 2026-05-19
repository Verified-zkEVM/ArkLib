/-
Copyright (c) 2024 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tobias Rothmann
-/

import VCVio
import ArkLib.Data.GroupTheory.PrimeOrder
import ArkLib.Data.Classes.Serde
import CompPoly.Univariate.Basic
import CompPoly.Univariate.ToPoly
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.LinearAlgebra.Lagrange

/-!
# Hardness Assumptions

This file defines hardness assumptions used in security reductions for commitment schemes.

## Notation

* `towerOfExponents` builds vectors of group-element powers from a secret exponent.
* `generateSrs` builds the structured reference string used by KZG-style reductions.
* `tSdhExperiment` and `arsdhExperiment` are the success probabilities for the corresponding
  hardness games.

## References

* [Chiesa, A., Guan, Z., Knabenhans, C., and Yu, Z.,
  *On the Fiat-Shamir Security of Succinct Arguments from Functional Commitments*][CGKY25]
-/

open OracleSpec OracleComp SubSpec
open CompPoly.CPolynomial
open Polynomial
open scoped NNReal ENNReal

namespace Groups

section PrimeOrder

variable {G : Type} [Group G] {p : outParam ℕ} [Fact (Nat.Prime p)]
  [PrimeOrderWith G p]

variable {G₁ : Type} [Group G₁] [PrimeOrderWith G₁ p] {g₁ : G₁}
  {G₂ : Type} [Group G₂] [PrimeOrderWith G₂ p] {g₂ : G₂}

/-- The vector of length `n + 1` consisting of powers
`#v[g, g ^ a.val, g ^ (a.val ^ 2), ..., g ^ (a.val ^ n)]`. -/
def towerOfExponents (g : G) (a : ZMod p) (n : ℕ) : Vector G (n + 1) :=
  .ofFn (fun i => g ^ (a.val ^ i.val))

/-- The structured reference string for the KZG commitment scheme with secret exponent `a`:
`#v[g₁, g₁ ^ a, g₁ ^ (a ^ 2), ..., g₁ ^ (a ^ n)]` for the prover and
`#v[g₂, g₂ ^ a]` for the verifier. -/
def generateSrs (n : ℕ) (a : ZMod p) : Vector G₁ (n + 1) × Vector G₂ 2 :=
  (towerOfExponents g₁ a n, towerOfExponents g₂ a 1)

/-- A `t`-SDH adversary returns a challenge offset and a group element upon receiving the SRS. -/
def tSdhAdversary (D : ℕ) :=
  Vector G₁ (D + 1) × Vector G₂ 2 →
    StateT unifSpec.QueryCache ProbComp (Option (ZMod p × G₁))

/-- The probability of breaking `t`-SDH for a specific adversary. -/
noncomputable def tSdhExperiment [∀ i, SampleableType (unifSpec.Range i)]
    {g₁ : G₁} {g₂ : G₂} (D : ℕ)
    (adversary : tSdhAdversary D (G₁ := G₁) (G₂ := G₂) (p := p)) : ℝ≥0∞ :=
  Pr[fun (τ, c, h) =>
    τ + c ≠ 0 ∧ h = g₁ ^ (1 / (τ + c)).val
  | OptionT.mk ((do
    let τ ← simulateQ randomOracle ($ᵗ(ZMod p))
    let srs := generateSrs (g₁ := g₁) (g₂ := g₂) D τ
    let result ← adversary srs
    pure (result.map (fun ((c, h) : ZMod p × G₁) =>
      (τ, c, h)))).run' (∅))
  ]

/-- The `t`-SDH assumption bounds every adversary's success probability by `error`. -/
def tSdhAssumption [∀ i, SampleableType (unifSpec.Range i)]
    {g₁ : G₁} {g₂ : G₂} (D : ℕ) (error : ℝ≥0) : Prop :=
  ∀ (adversary : tSdhAdversary D (G₁ := G₁) (G₂ := G₂) (p := p)),
    tSdhExperiment (g₁ := g₁) (g₂ := g₂) D adversary ≤ (error : ℝ≥0∞)

/-- An ARSDH adversary returns a set and two group elements upon receiving the SRS. -/
def arsdhAdversary (D : ℕ) :=
  Vector G₁ (D + 1) × Vector G₂ 2 →
    StateT unifSpec.QueryCache ProbComp (Option (Finset (ZMod p) × G₁ × G₁))

/-- The probability of breaking ARSDH for a specific adversary. -/
noncomputable def arsdhExperiment [∀ i, SampleableType (unifSpec.Range i)]
    {g₁ : G₁} {g₂ : G₂} (D : ℕ)
    (adversary : arsdhAdversary D (G₁ := G₁) (G₂ := G₂) (p := p)) : ℝ≥0∞ :=
  Pr[fun (τ, S, h₁, h₂) =>
    let Zₛ : CompPoly.CPolynomial (ZMod p) :=
      ∏ s ∈ S, (CompPoly.CPolynomial.X - CompPoly.CPolynomial.C s)
    S.card = D + 1 ∧ h₁ ≠ 1 ∧ h₂ = h₁ ^ (1 / Zₛ.eval τ).val
  | OptionT.mk ((do
    let τ ← simulateQ randomOracle ($ᵗ(ZMod p))
    let srs := generateSrs (g₁ := g₁) (g₂ := g₂) D τ
    let result ← adversary srs
    pure (result.map (fun ((S, h₁, h₂) : Finset (ZMod p) × G₁ × G₁) =>
      (τ, S, h₁, h₂)))).run' (∅))
  ]

/-! ### Oracle Simulation Note

Why is `simulateQ` only applied to the `τ` sampling?

We can think of three alternatives (none of which we got to work so far):
1. leave out the simulateQ completely
2. apply simulateQ randomOracle to the whole game/monad
3. apply simulateQ (impl), where impl is a QueryImpl that both the τ sampling, and the adversary
call can be lifted to.

Ultimately we test this definition in our KZG function binding proof.
We ran in the following issues for each approach:
1. the function binding game simulates its whole monad with "impl" which for unifSpec is
randomOracle (stateful), so not collecting the oracle entry for τ fundamentally changes the
structure of ARSDH+reduction vs a function binding game.
Note, unifOracle, a stateless version of randomOracle exists, but does not satisfy the type
constraints of function binding (StateT σ ProbComp). One could build a wrapper around this though
which might be sensible. Throughout the repo StateT σ ProbComp is frequently used.

2. double simulation of randomOracle with idOracle didn't work.

3. conflict of lifting to self (no reflexivity for liftComp)

Thus for now it seems sensible to simulate the sampling of τ separately and pass the resulting
state of this simulation to the adversary (to use in its own simulation).
-/

/-- The adaptive rational strong Diffie–Hellman (ARSDH) assumption.
Taken from Definition 9.6 in [CGKY25]. -/
def arsdhAssumption [∀ i, SampleableType (unifSpec.Range i)]
    {g₁ : G₁} {g₂ : G₂} (D : ℕ) (error : ℝ≥0) : Prop :=
  ∀ (adversary : arsdhAdversary D (G₁ := G₁) (G₂ := G₂) (p := p)),
    arsdhExperiment (g₁ := g₁) (g₂ := g₂) D adversary ≤ (error : ℝ≥0∞)

end PrimeOrder

end Groups

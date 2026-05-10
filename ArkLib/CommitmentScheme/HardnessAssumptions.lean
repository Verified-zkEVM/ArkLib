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

/-
  # Hardness Assumptions

  This file contains hardness assumptions for commitment schemes.
  These Hardness Assumptions are used to prove the security of commitment schemes.
-/

variable {ι η : Type} (oSpec : OracleSpec ι) (advSpec : OracleSpec η)

open OracleSpec OracleComp SubSpec
open CompPoly.CPolynomial
open Polynomial
open scoped NNReal ENNReal

namespace Groups

section PrimeOrder

variable {G : Type} [Group G] {p : outParam ℕ} [hp : Fact (Nat.Prime p)] [Fact (0 < p)]
  [PrimeOrderWith G p] {g : G}

section Pairings

variable {G₁ : Type} [Group G₁] [PrimeOrderWith G₁ p] {g₁ : G₁}
  {G₂ : Type} [Group G₂] [PrimeOrderWith G₂ p] {g₂ : G₂}
  {Gₜ : Type} [Group Gₜ] [PrimeOrderWith Gₜ p] [DecidableEq Gₜ]
  [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)] [Module (ZMod p) (Additive Gₜ)]
  (pairing : (Additive G₁) →ₗ[ZMod p] (Additive G₂) →ₗ[ZMod p] (Additive Gₜ))

/-- The vector of length `n + 1` that consists of powers:
  `#v[1, g, g ^ a.val, g ^ (a.val ^ 2), ..., g ^ (a.val ^ n)` -/
def towerOfExponents (g : G) (a : ZMod p) (n : ℕ) : Vector G (n + 1) :=
  .ofFn (fun i => g ^ (a.val ^ i.val))

/-- The `srs` (structured reference string) for the KZG commitment scheme with secret exponent `a`
    is defined as `#v[g₁, g₁ ^ a, g₁ ^ (a ^ 2), ..., g₁ ^ (a ^ (n - 1))], #v[g₂, g₂ ^ a]` -/
def generateSrs (n : ℕ) (a : ZMod p) : Vector G₁ (n + 1) × Vector G₂ 2 :=
  (towerOfExponents g₁ a n, towerOfExponents g₂ a 1)

/-- The tSDH adversary returns a set of size D+1 and two group elements h₁ and h₂ upon receiving
the srs. -/
def tSDHAdversary (D : ℕ) :=
  Vector G₁ (D + 1) × Vector G₂ 2 →
    StateT unifSpec.QueryCache ProbComp (Option (ZMod p × G₁))

/-- The probabillity of breaking tSDH for a specific adversary. -/
noncomputable def tSDH_Experiment [∀ i, SampleableType (unifSpec.Range i)]
    {g₁ : G₁} {g₂ : G₂} (D : ℕ)
    (adversary : tSDHAdversary D (G₁ := G₁) (G₂ := G₂) (p := p))
    : ℝ≥0∞ :=
  Pr[fun (τ,c,h) =>
    τ + c ≠ 0 ∧ h = g₁ ^ (1 / (τ+c)).val --TODO τ≠c in here?
  | OptionT.mk ((do
    let τ ← simulateQ randomOracle ($ᵗ(ZMod p))
    let srs := generateSrs (g₁ := g₁) (g₂ := g₂) D τ
    let result ← adversary srs
    pure (result.map (fun ((c, h) : ZMod p × G₁) =>
      (τ, c, h)))).run' (∅))
  ]

def tSDHAssumption [∀ i, SampleableType (unifSpec.Range i)]
    {g₁ : G₁} {g₂ : G₂} (D : ℕ) (error : ℝ≥0)
    : Prop :=
     ∀ (adversary : tSDHAdversary D
        (G₁ := G₁) (G₂ := G₂) (p := p)),
      tSDH_Experiment (g₁ := g₁) (g₂ := g₂) D adversary ≤ (error : ℝ≥0∞)

/-- The ARSDH adversary returns a set of size D+1 and two group elements h₁ and h₂ upon receiving
the srs. -/
def ARSDHAdversary (D : ℕ) :=
  Vector G₁ (D + 1) × Vector G₂ 2 →
    StateT unifSpec.QueryCache ProbComp (Option (Finset (ZMod p) × G₁ × G₁))

/-- The probabillity of breaking ARSDH for a specific adversary. -/
noncomputable def ARSDH_Experiment [∀ i, SampleableType (unifSpec.Range i)]
    {g₁ : G₁} {g₂ : G₂} (D : ℕ)
    (adversary : ARSDHAdversary D (G₁ := G₁) (G₂ := G₂) (p := p))
    : ℝ≥0∞ :=
  Pr[fun (τ,S,h₁,h₂) =>
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

/- a note on why simulateQ is only applied to the τ sampling:
We can think of three alternatives (none of which we got to work so far):
1. leave out the simulateQ completely
2. apply simulateQ randomOracle to the whole game/monad
3. apply simulateQ (impl), where impl is a QueryImpl that both the τ sampling, and the adversary
call can be lifted to.

Ultimately we test this definition in our KZG function binding proof.
We ran in the following issues for each approach:
1. the function binding game simulates it's whole monad with "impl" which for unifSpec is
randomOracle (stateful), so not collecting the oracle entry for τ fundamentally changes the
structure of ARSDH+reduction vs a function binding game.
Note, unifOracle, a stateless version of randomOracle exists, but does not satisfy the type
constraints of function binding (StateT σ ProbComp). One could build a wrapper around this though
which might be sensible. Through out the repo StateT σ ProbComp is frequently used.

2. double simulation of randomOracle with idOracle didn't work.

3. conflcit of lifiting to slef (no reflexivity for liftComp)

Thus for now it seems sensible to simulate the sampling of τ separatly and pass the resulting state
of this simulation to the adversary (to use in it's own simulation).
-/

/-- The adaptive rational strong Diffie–Hellman (ARSDH) assumption.
Taken from Def. 9.6 in "On the Fiat–Shamir Security of Succinct Arguments from Functional
Commitments" (see https://eprint.iacr.org/2025/902.pdf)
-/
def ARSDHAssumption [∀ i, SampleableType (unifSpec.Range i)]
    {g₁ : G₁} {g₂ : G₂} (D : ℕ) (error : ℝ≥0)
    : Prop :=
     ∀ (adversary : ARSDHAdversary D
        (G₁ := G₁) (G₂ := G₂) (p := p)),
      ARSDH_Experiment (g₁ := g₁) (g₂ := g₂) D adversary ≤ (error : ℝ≥0∞)

end Pairings

end PrimeOrder

end Groups

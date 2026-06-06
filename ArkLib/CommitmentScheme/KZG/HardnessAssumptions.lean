/-
Copyright (c) 2024 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tobias Rothmann
-/

import VCVio
import ArkLib.CommitmentScheme.KZG.Algebra
import ArkLib.CommitmentScheme.KZG.Sampling
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

* `Groups.PowerSrs.tower` builds vectors of group-element powers from a secret exponent.
* `Groups.PowerSrs.generate` builds the structured reference string used by KZG-style reductions.
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

/-- A `t`-SDH adversary returns a challenge offset and a group element upon receiving the SRS. -/
abbrev tSdhAdversary (D : ℕ) :=
  Vector G₁ (D + 1) × Vector G₂ 2 →
    StateT unifSpec.QueryCache ProbComp (Option (ZMod p × G₁))

/-- t-SDH condition for an adversary to win. -/
abbrev tSdhCondition {g₁ : G₁} : (ZMod p × ZMod p × G₁) → Prop :=
  fun (τ, c, h) =>
    τ + c ≠ 0 ∧ h = g₁ ^ (1 / (τ + c)).val

/-! ### Private Setup Note

Both hardness games sample the SRS trapdoor `τ` as private setup randomness in the outer
`ProbComp`, not through the cache-backed `randomOracle` implementation. The adversary is run from
an empty query cache and receives only the public SRS generated from `τ`.
-/

/-- The t-SDH game for a specific adversary. -/
abbrev tSdhGame [∀ i, SampleableType (unifSpec.Range i)]
    {g₁ : G₁} {g₂ : G₂} (D : ℕ)
    (adversary : tSdhAdversary D (G₁ := G₁) (G₂ := G₂) (p := p)) :
    OptionT ProbComp (ZMod p × ZMod p × G₁) :=
  OptionT.mk (do
    let τ ← sampleNonzeroZMod (p := p)
    let srs := Groups.PowerSrs.generate (g₁ := g₁) (g₂ := g₂) D τ
    let result ← (adversary srs).run' ∅
    pure (result.map (fun ((c, h) : ZMod p × G₁) =>
      (τ, c, h))))

/-- The probability of breaking `t`-SDH for a specific adversary. -/
noncomputable def tSdhExperiment [∀ i, SampleableType (unifSpec.Range i)]
    {g₁ : G₁} {g₂ : G₂} (D : ℕ)
    (adversary : tSdhAdversary D (G₁ := G₁) (G₂ := G₂) (p := p)) : ℝ≥0∞ :=
  Pr[tSdhCondition (g₁ := g₁) | tSdhGame (g₁ := g₁) (g₂ := g₂) D adversary]

/-- The `t`-SDH assumption bounds every adversary's success probability by `error`. -/
def tSdhAssumption [∀ i, SampleableType (unifSpec.Range i)]
    {g₁ : G₁} {g₂ : G₂} (D : ℕ) (error : ℝ≥0) : Prop :=
  ∀ (adversary : tSdhAdversary D (G₁ := G₁) (G₂ := G₂) (p := p)),
    tSdhExperiment (g₁ := g₁) (g₂ := g₂) D adversary ≤ (error : ℝ≥0∞)

/-- An ARSDH adversary returns a set and two group elements upon receiving the SRS. -/
abbrev arsdhAdversary (D : ℕ) :=
  Vector G₁ (D + 1) × Vector G₂ 2 →
    StateT unifSpec.QueryCache ProbComp (Option (Finset (ZMod p) × G₁ × G₁))

/-- ARSDH condition for an adversary to win. -/
abbrev arsdhCondition (D : ℕ) : (ZMod p × Finset (ZMod p) × G₁ × G₁) → Prop :=
  fun (τ, S, h₁, h₂) =>
    let Zₛ : CompPoly.CPolynomial (ZMod p) :=
      ∏ s ∈ S, (CompPoly.CPolynomial.X - CompPoly.CPolynomial.C s)
    S.card = D + 1 ∧ Zₛ.eval τ ≠ 0 ∧ h₁ ≠ 1 ∧ h₂ = h₁ ^ (1 / Zₛ.eval τ).val

/-- The ARSDH game for a specific adversary. -/
abbrev arsdhGame [∀ i, SampleableType (unifSpec.Range i)]
    {g₁ : G₁} {g₂ : G₂} (D : ℕ)
    (adversary : arsdhAdversary D (G₁ := G₁) (G₂ := G₂) (p := p)) :
    OptionT ProbComp (ZMod p × Finset (ZMod p) × G₁ × G₁) :=
  OptionT.mk (do
    let τ ← sampleNonzeroZMod (p := p)
    let srs := Groups.PowerSrs.generate (g₁ := g₁) (g₂ := g₂) D τ
    let result ← (adversary srs).run' ∅
    pure (result.map (fun ((S, h₁, h₂) : Finset (ZMod p) × G₁ × G₁) =>
      (τ, S, h₁, h₂))))

/-- The probability of breaking ARSDH for a specific adversary. -/
noncomputable def arsdhExperiment [∀ i, SampleableType (unifSpec.Range i)]
    {g₁ : G₁} {g₂ : G₂} (D : ℕ)
    (adversary : arsdhAdversary D (G₁ := G₁) (G₂ := G₂) (p := p)) : ℝ≥0∞ :=
  Pr[arsdhCondition D | arsdhGame (g₁ := g₁) (g₂ := g₂) D adversary]

/-- The adaptive rational strong Diffie–Hellman (ARSDH) assumption.
Taken from Definition 9.6 in [CGKY25]. -/
def arsdhAssumption [∀ i, SampleableType (unifSpec.Range i)]
    {g₁ : G₁} {g₂ : G₂} (D : ℕ) (error : ℝ≥0) : Prop :=
  ∀ (adversary : arsdhAdversary D (G₁ := G₁) (G₂ := G₂) (p := p)),
    arsdhExperiment (g₁ := g₁) (g₂ := g₂) D adversary ≤ (error : ℝ≥0∞)

end PrimeOrder

end Groups

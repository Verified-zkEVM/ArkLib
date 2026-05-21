/-
Copyright (c) 2024 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tobias Rothmann
-/

import VCVio
import ArkLib.Data.GroupTheory.PrimeOrder
import ArkLib.Data.Classes.Serde
import ArkLib.ToVCVio.OracleComp.SimSemantics.SimulateQ
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
* `sampleNonzeroZMod` samples the SRS trapdoor from `ZMod p \ {0}`.
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

/-- Uniformly sample a nonzero element of `ZMod p`.

The implementation samples an index in `{0, ..., p - 2}` and shifts it by one, so the support is
exactly the canonical representatives `1, ..., p - 1` modulo `p`. -/
def sampleNonzeroZMod : ProbComp (ZMod p) :=
  haveI : NeZero (p - 1) :=
    ⟨Nat.pos_iff_ne_zero.mp (Nat.sub_pos_of_lt (Nat.Prime.one_lt Fact.out))⟩
  (fun i : Fin (p - 1) => ((i : ℕ) + 1 : ZMod p)) <$> ($ᵗ (Fin (p - 1)))

/-- Simulating the random oracle leaves the nonzero SRS trapdoor sampler unchanged. -/
lemma simulateQ_randomOracle_sampleNonzeroZMod :
    ((simulateQ (unifSpec.randomOracle :
      QueryImpl unifSpec (StateT unifSpec.QueryCache ProbComp))
      (sampleNonzeroZMod (p := p) : ProbComp (ZMod p)) :
        StateT unifSpec.QueryCache ProbComp (ZMod p))).run' ∅ =
      sampleNonzeroZMod (p := p) := by
  haveI : NeZero (p - 1) :=
    ⟨Nat.pos_iff_ne_zero.mp (Nat.sub_pos_of_lt (Nat.Prime.one_lt Fact.out))⟩
  unfold sampleNonzeroZMod
  cases p with
  | zero =>
      exact False.elim (Nat.not_prime_zero Fact.out)
  | succ p' =>
      cases p' with
      | zero =>
          exact False.elim (Nat.not_prime_one Fact.out)
      | succ p'' =>
          exact simulateQ_randomOracle_map_uniformFin p''
            (fun i : Fin (p'' + 1) => ((i : ℕ) + 1 : ZMod (p'' + 1 + 1)))

/-- A `t`-SDH adversary returns a challenge offset and a group element upon receiving the SRS. -/
abbrev tSdhAdversary (D : ℕ) :=
  Vector G₁ (D + 1) × Vector G₂ 2 →
    StateT unifSpec.QueryCache ProbComp (Option (ZMod p × G₁))

/-- t-SDH condition for an adversary to win. -/
abbrev tSdhCondition {g₁ : G₁} : (ZMod p × ZMod p × G₁) → Prop :=
  fun (τ, c, h) =>
    τ + c ≠ 0 ∧ h = g₁ ^ (1 / (τ + c)).val

/-- The t-SDH game for a specific adversary. -/
abbrev tSdhGame [∀ i, SampleableType (unifSpec.Range i)]
    {g₁ : G₁} {g₂ : G₂} (D : ℕ)
    (adversary : tSdhAdversary D (G₁ := G₁) (G₂ := G₂) (p := p)) :
    OptionT ProbComp (ZMod p × ZMod p × G₁) :=
  OptionT.mk (do
    let τ ← sampleNonzeroZMod (p := p)
    let srs := generateSrs (g₁ := g₁) (g₂ := g₂) D τ
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
    let srs := generateSrs (g₁ := g₁) (g₂ := g₂) D τ
    let result ← (adversary srs).run' ∅
    pure (result.map (fun ((S, h₁, h₂) : Finset (ZMod p) × G₁ × G₁) =>
      (τ, S, h₁, h₂))))

/-- The probability of breaking ARSDH for a specific adversary. -/
noncomputable def arsdhExperiment [∀ i, SampleableType (unifSpec.Range i)]
    {g₁ : G₁} {g₂ : G₂} (D : ℕ)
    (adversary : arsdhAdversary D (G₁ := G₁) (G₂ := G₂) (p := p)) : ℝ≥0∞ :=
  Pr[arsdhCondition D | arsdhGame (g₁ := g₁) (g₂ := g₂) D adversary]

/-! ### Private Setup Note

The SRS trapdoor `τ` is sampled as private setup randomness in the outer `ProbComp`, not through
the cache-backed `randomOracle` implementation.  The adversary is run from an empty query cache and
receives only the public SRS generated from `τ`.
-/

/-- The adaptive rational strong Diffie–Hellman (ARSDH) assumption.
Taken from Definition 9.6 in [CGKY25]. -/
def arsdhAssumption [∀ i, SampleableType (unifSpec.Range i)]
    {g₁ : G₁} {g₂ : G₂} (D : ℕ) (error : ℝ≥0) : Prop :=
  ∀ (adversary : arsdhAdversary D (G₁ := G₁) (G₂ := G₂) (p := p)),
    arsdhExperiment (g₁ := g₁) (g₂ := g₂) D adversary ≤ (error : ℝ≥0∞)

end PrimeOrder

end Groups

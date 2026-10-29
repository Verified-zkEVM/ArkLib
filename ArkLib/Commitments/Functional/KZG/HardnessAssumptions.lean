/-
Copyright (c) 2024 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tobias Rothmann
-/
module

public import ArkLib.Commitments.Functional.KZG.Algebra
public import ArkLib.Commitments.Functional.KZG.Sampling
public import ArkLib.Data.GroupTheory.PrimeOrder
public import CompPoly.Data.Classes.Serialize
public import CompPoly.Univariate.Basic
public import CompPoly.Univariate.ToPoly
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Order.Star.Basic
public import Mathlib.Algebra.Polynomial.FieldDivision
public import Mathlib.LinearAlgebra.Lagrange

/-!
# Hardness Assumptions

This file defines hardness games and assumptions over explicit adversary classes. The KZG
security results are reduction inequalities between concrete experiments. Their hardness-based
corollaries are as strong as the adversary classes for which the assumptions can be justified.
Group-model classes and preservation by the reductions remain separate obligations, tracked in
issue #1310. The counterexamples for the unrestricted class use classical inverses and finite-set
choice only inside proofs; they do not supply executable adversary implementations.

## Notation

* `Groups.PowerSrs.tower` builds vectors of group-element powers from a secret exponent.
* `Groups.PowerSrs.generate` builds the structured reference string used by KZG-style reductions.
* `tSdhExperiment` and `arsdhExperiment` are the success probabilities for the corresponding
  hardness games.

## References

* [Chiesa, A., Guan, Z., Knabenhans, C., and Yu, Z.,
  *On the Fiat-Shamir Security of Succinct Arguments from Functional Commitments*][CGKY25]
-/

@[expose] public section

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
  Pr{let result ← (tSdhGame (g₁ := g₁) (g₂ := g₂) D adversary)}[(tSdhCondition (g₁ := g₁)) result]

private lemma verifier_exponent_injective (hg₂ : g₂ ≠ 1) :
    Function.Injective (fun a : ZMod p => g₂ ^ a.val) := by
  intro a b hab
  have hm := pow_eq_pow_iff_modEq.mp hab
  rw [orderOf_eq_prime_of_ne_one g₂ hg₂] at hm
  apply ZMod.val_injective p
  exact hm.eq_of_lt_of_lt (ZMod.val_lt a) (ZMod.val_lt b)

/-- The `t`-SDH assumption bounds the success probability of every adversary in `Adv` by `error`.

For `Adv = Set.univ` and a nontrivial verifier generator, this is false below error `1`: the
trapdoor is a classical function of the verifier SRS. A meaningful instance must restrict `Adv`,
for example to generic or algebraic group adversaries, or resource-bounded adversaries. -/
def tSdhAssumption [∀ i, SampleableType (unifSpec.Range i)]
    {g₁ : G₁} {g₂ : G₂} (D : ℕ)
    (Adv : Set (tSdhAdversary D (G₁ := G₁) (G₂ := G₂) (p := p))) (error : ℝ≥0) : Prop :=
  ∀ adversary ∈ Adv,
    tSdhExperiment (g₁ := g₁) (g₂ := g₂) D adversary ≤ (error : ℝ≥0∞)

omit [PrimeOrderWith G₁ p] in
/-- Over all Lean functions, `t`-SDH cannot have error below one when the verifier generator is
nontrivial: a classical inverse of its exponent map recovers the trapdoor from the SRS. -/
lemma not_tSdhAssumption_univ [∀ i, SampleableType (unifSpec.Range i)]
    (D : ℕ) (hg₂ : g₂ ≠ 1) (error : ℝ≥0) (herror : error < 1) :
    ¬ tSdhAssumption (p := p) (g₁ := g₁) (g₂ := g₂) D Set.univ error := by
  classical
  let recover := Function.invFun (fun a : ZMod p => g₂ ^ a.val)
  have hrec (τ : ZMod p) : recover (g₂ ^ τ.val) = τ :=
    Function.leftInverse_invFun (verifier_exponent_injective hg₂) τ
  have hsrs (τ : ZMod p) :
      recover (PowerSrs.generate (g₁ := g₁) (g₂ := g₂) D τ).2[1] = τ := by
    simpa [PowerSrs.generate, PowerSrs.tower] using hrec τ
  let adversary : tSdhAdversary D (G₁ := G₁) (G₂ := G₂) (p := p) :=
    fun srs => pure (some (1 - recover srs.2[1], g₁))
  have hwin : tSdhExperiment (g₁ := g₁) (g₂ := g₂) D adversary = 1 := by
    unfold tSdhExperiment tSdhGame
    apply OptionT.prEvent_mk_bind_eq_one_of_support _ (OracleComp.prEvent_true_eq_one _) _ _
    intro τ _
    have hc : τ + (1 - τ) = 1 := by ring
    simp [adversary, hsrs, OptionT.prEvent_mk, tSdhCondition, hc,
      ZMod.val_one'' (ne_of_gt (Nat.Prime.one_lt Fact.out))]
  intro h
  have hb := h adversary (Set.mem_univ _)
  rw [hwin] at hb
  exact (not_le_of_gt (by exact_mod_cast herror)) hb

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
  Pr{let result ← (arsdhGame (g₁ := g₁) (g₂ := g₂) D adversary)}[(arsdhCondition D) result]

/-- The adaptive rational strong Diffie–Hellman (ARSDH) assumption bounds the success
probability of every adversary in `Adv` by `error`.

For `Adv = Set.univ`, nontrivial generators and `p ≥ D + 2`, this is false below error `1`:
the trapdoor is a classical function of the verifier SRS. A meaningful instance must restrict
`Adv`, for example to generic or algebraic group adversaries, or resource-bounded adversaries. -/
def arsdhAssumption [∀ i, SampleableType (unifSpec.Range i)]
    {g₁ : G₁} {g₂ : G₂} (D : ℕ)
    (Adv : Set (arsdhAdversary D (G₁ := G₁) (G₂ := G₂) (p := p))) (error : ℝ≥0) : Prop :=
  ∀ adversary ∈ Adv,
    arsdhExperiment (g₁ := g₁) (g₂ := g₂) D adversary ≤ (error : ℝ≥0∞)

/-- Over all Lean functions, ARSDH cannot have error below one when both generators are
nontrivial and the field contains at least `D + 2` elements. A classical adversary recovers the
trapdoor and chooses a set of size `D + 1` avoiding it. -/
lemma not_arsdhAssumption_univ [∀ i, SampleableType (unifSpec.Range i)]
    (D : ℕ) (hg₁ : g₁ ≠ 1) (hg₂ : g₂ ≠ 1) (hp : p ≥ D + 2)
    (error : ℝ≥0) (herror : error < 1) :
    ¬ arsdhAssumption (p := p) (g₁ := g₁) (g₂ := g₂) D Set.univ error := by
  classical
  let recover := Function.invFun (fun a : ZMod p => g₂ ^ a.val)
  have hrec (τ : ZMod p) : recover (g₂ ^ τ.val) = τ :=
    Function.leftInverse_invFun (verifier_exponent_injective hg₂) τ
  have hsrs (τ : ZMod p) :
      recover (PowerSrs.generate (g₁ := g₁) (g₂ := g₂) D τ).2[1] = τ := by
    simpa [PowerSrs.generate, PowerSrs.tower] using hrec τ
  have hex (τ : ZMod p) : ∃ S : Finset (ZMod p),
      S ⊆ Finset.univ.erase τ ∧ S.card = D + 1 := by
    apply Finset.exists_subset_card_eq
    simp only [Finset.card_erase_of_mem (Finset.mem_univ τ), Finset.card_univ, ZMod.card]
    omega
  let S (τ : ZMod p) := Classical.choose (hex τ)
  have hcard (τ : ZMod p) : (S τ).card = D + 1 := (Classical.choose_spec (hex τ)).2
  have havoid (τ : ZMod p) : τ ∉ S τ := by
    intro h
    exact (Finset.mem_erase.mp ((Classical.choose_spec (hex τ)).1 h)).1 rfl
  let Z (τ : ZMod p) : CompPoly.CPolynomial (ZMod p) :=
    ∏ s ∈ S τ, (CompPoly.CPolynomial.X - CompPoly.CPolynomial.C s)
  have hZ (τ : ZMod p) : (Z τ).eval τ ≠ 0 := by
    have hprod (T : Finset (ZMod p)) (hτ : τ ∉ T) :
        (∏ s ∈ T, (CompPoly.CPolynomial.X - CompPoly.CPolynomial.C s)).eval τ ≠ 0 := by
      induction T using Finset.induction_on with
      | empty => simp
      | @insert a T ha ih =>
        rw [Finset.prod_insert ha, CompPoly.CPolynomial.eval_mul]
        apply mul_ne_zero
        · simp only [CompPoly.CPolynomial.eval_sub, CompPoly.CPolynomial.eval_X,
            CompPoly.CPolynomial.eval_C]
          exact sub_ne_zero.mpr (fun h => hτ (h ▸ Finset.mem_insert_self a T))
        · exact ih (fun h => hτ (Finset.mem_insert_of_mem h))
    exact hprod (S τ) (havoid τ)
  let adversary : arsdhAdversary D (G₁ := G₁) (G₂ := G₂) (p := p) :=
    fun srs =>
      let τ := recover srs.2[1]
      pure (some (S τ, g₁, g₁ ^ (1 / (Z τ).eval τ).val))
  have hwin : arsdhExperiment (g₁ := g₁) (g₂ := g₂) D adversary = 1 := by
    unfold arsdhExperiment arsdhGame
    apply OptionT.prEvent_mk_bind_eq_one_of_support _ (OracleComp.prEvent_true_eq_one _) _ _
    intro τ _
    have hcond : arsdhCondition D (τ, S τ, g₁, g₁ ^ (1 / (Z τ).eval τ).val) :=
      ⟨hcard τ, hZ τ, hg₁, rfl⟩
    simpa [adversary, hsrs, OptionT.prEvent_mk, arsdhCondition, Z] using hcond
  intro h
  have hb := h adversary (Set.mem_univ _)
  rw [hwin] at hb
  exact (not_le_of_gt (by exact_mod_cast herror)) hb

end PrimeOrder

end Groups

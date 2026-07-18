/-
Copyright (c) 2026 Ember Arlynx. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ember Arlynx
-/
import ArkLib.Scratch.KzgVacuity.GgmAdaptive
import ArkLib.Commitments.Functional.KZG.HardnessAssumptions

/-!
# Transporting the GGM field-level t-SDH bound to the group-level game

`GgmAdaptive` proves an adaptive generic-group-model (GGM) cardinality bound about a
*field-level* predicate: the generic adversary's committed polynomial satisfies
`f.eval τ = 1 / (τ + c)` at the sampled trapdoor `τ : ZMod p`. The Boneh–Boyen t-SDH hardness
game [BB04] that underlies the KZG polynomial commitment scheme [KZG10] instead scores a
*group-level* condition over a prime-order `G₁`:
$$\mathrm{tSdhCondition}(τ, c, h) := τ + c ≠ 0 ∧ h = g_1^{(1 / (τ + c)).\mathrm{val}}$$
with `tSdhExperiment D A = Pr[tSdhCondition | tSdhGame D A]`.

The two predicates live on opposite sides of the exponent encoding `a : ZMod p ↦ g ^ a.val`.
This file proves the encoding is injective — indeed bijective — in a prime-order group, hence the
two conditions are equivalent, hence the GGM winning-trapdoor set stated in group terms is
`GgmAdaptive.realWinSet`, and the adaptive bound `fuel·Δ + (D+1)` (and its `(…)/(p−1)` fraction)
transports verbatim to the group side.

## Contents

1. `gpow_val_injective` / `gpow_val_inj_iff` — injectivity of `a ↦ g ^ a.val` for `g` of
   order `p`, derived from `Groups.gpow_div_eq` and `Groups.zmod_eq_zero_of_gpow_eq_one`; the
   iff form.
2. `gpow_val_bijective` — bijectivity: surjectivity is `Groups.exists_zmod_power_of_generator`
   (every element of a prime-order group is a `ZMod p` power of a nontrivial generator).
3. `tSdhCondition_iff_field` — for an output presented in encoded form `h = g ^ x.val`,
   `Groups.tSdhCondition (τ, c, h)` holds iff `τ + c ≠ 0 ∧ x = 1 / (τ + c)` — exactly the
   filter predicate of `GgmAdaptive.realWinSet` at `x = f.eval τ`.
4. `groupWinSet` / `groupWinSet_eq_realWinSet` / `field_bound_transports_to_group` — the set of
   trapdoors on which the adaptive generic run's realized group element wins `tSdhCondition`
   equals `realWinSet`; the cardinality bound and the rational fraction bound follow.

## Named residual

Connecting `field_bound_transports_to_group` to the literal inequality
`tSdhExperiment D A ≤ (fuel·Δ + D + 1) / (p−1)` requires threading VCVio's game monad — this is
probability-monad plumbing, with no new mathematics:

* Generic-to-game embedding: for each `Strat p`, exhibit a `tSdhAdversary D`,

      Vector G₁ (D+1) × Vector G₂ 2 →
        StateT unifSpec.QueryCache ProbComp (Option (ZMod p × G₁))

  whose realized output on the SRS `PowerSrs.generate D τ` is

      ((runOutput (realAns τ) strat fuel st₀).1,
        g₁ ^ ((runOutput (realAns τ) strat fuel st₀).2.eval τ).val)

  the generic-oracle-to-group simulation (equality queries answered by comparing real group
  elements).
* Sampler semantics: `Pr[cond | sampleNonzeroZMod >>= deterministic] =
  (nonzeroPoints.filter cond).card / (p−1)` — `probEvent` over `sampleNonzeroZMod` (a
  `Fin (p−1)` uniform mapped by `i ↦ i+1`), plus the `ℚ → ℝ≥0∞` cast.

Both are `OptionT ProbComp` bookkeeping. The condition-level identity proven here
(`groupWinSet_eq_realWinSet`) is exact, so the counting bound is about precisely the event
`tSdhExperiment` scores — nothing about the predicate remains to be aligned.

## References

* [Boneh, D., and Boyen, X., *Short Signatures Without Random Oracles*][BB04]
* [Kate, A., Zaverucha, G. M., and Goldberg, I., *Constant-Size Commitments to Polynomials and
    Their Applications*][KZG10]
-/

open Polynomial

namespace GgmArkLibTransport

open GgmCandidate GgmAdaptive

variable {p : ℕ} [Fact (Nat.Prime p)]
variable {G : Type} [Group G] [PrimeOrderWith G p]

/-! ## 1. Injectivity of the exponent encoding `a : ZMod p ↦ g ^ a.val` -/

/-- **Injectivity.** For `g` of order `p`, the encoding `a : ZMod p ↦ g ^ a.val` is injective.
Derived from ArkLib's own prime-order lemmas: `g^a/g^b = g^(a−b)` (`Groups.gpow_div_eq`) and
`g^c = 1 → c = 0` (`Groups.zmod_eq_zero_of_gpow_eq_one`). -/
theorem gpow_val_injective {g : G} (hord : orderOf g = p) :
    Function.Injective (fun a : ZMod p => g ^ a.val) := by
  intro a b hab
  simp only at hab
  have hdiv : g ^ a.val / g ^ b.val = (1 : G) := by rw [hab, div_self']
  rw [Groups.gpow_div_eq hord] at hdiv
  exact sub_eq_zero.mp (Groups.zmod_eq_zero_of_gpow_eq_one hord hdiv)

/-- **The iff.** `g ^ a.val = g ^ b.val ↔ a = b` for `g` of order `p`. -/
theorem gpow_val_inj_iff {g : G} (hord : orderOf g = p) {a b : ZMod p} :
    g ^ a.val = g ^ b.val ↔ a = b :=
  ⟨fun h => gpow_val_injective hord h, fun h => by rw [h]⟩

/-- **Bijectivity.** Injectivity above; surjectivity is exactly ArkLib's
`Groups.exists_zmod_power_of_generator` (every element of a prime-order group is a `ZMod p`
power of a nontrivial generator). The encoding is a bijection `ZMod p ≃ G` — the group carries
no more and no less information than the field of exponents. -/
theorem gpow_val_bijective {g : G} (hpG : Nat.card G = p) (hg : g ≠ 1)
    (hord : orderOf g = p) :
    Function.Bijective (fun a : ZMod p => g ^ a.val) :=
  ⟨gpow_val_injective hord, fun x => by
    obtain ⟨a, ha⟩ := Groups.exists_zmod_power_of_generator hpG hg hord x
    exact ⟨a, ha.symm⟩⟩

/-! ## 2. The condition-level transport: `tSdhCondition` ↔ the field predicate -/

/-- **Condition transport.** For an output element presented in encoded form `g ^ x.val`,
ArkLib's group-level `tSdhCondition (τ, c, g ^ x.val)` holds **iff** the field-level condition
`τ + c ≠ 0 ∧ x = 1/(τ+c)` holds. Forward: injectivity. Backward: congruence. This is the
predicate `GgmAdaptive.realWinSet` filters by, at `x = f.eval τ`. -/
theorem tSdhCondition_iff_field {g : G} (hord : orderOf g = p) (τ c x : ZMod p) :
    Groups.tSdhCondition (g₁ := g) (τ, c, g ^ x.val) ↔ (τ + c ≠ 0 ∧ x = 1 / (τ + c)) := by
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, gpow_val_injective hord h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, by rw [h2]⟩

/-! ## 3. The set-level transport and the bound in group terms -/

/-- The trapdoors on which the adaptive generic run's realized **group** output wins ArkLib's
`tSdhCondition`: the committed offset is `(runOutput …).1` and the realized group element is the
encoding `g ^ (f τ).val` of the output polynomial's evaluation — exactly the element the
generic-model environment hands the t-SDH referee. (Decidability is supplied classically —
equality in the abstract group `G` carries no decision procedure.) -/
noncomputable def groupWinSet (g : G) (strat : Strat p) (st₀ : St p) (fuel : ℕ) :
    Finset (ZMod p) :=
  letI : DecidablePred (fun τ : ZMod p =>
      Groups.tSdhCondition (g₁ := g)
        (τ, (runOutput (realAns τ) strat fuel st₀).1,
          g ^ ((runOutput (realAns τ) strat fuel st₀).2.eval τ).val)) :=
    fun _ => Classical.dec _
  nonzeroPoints.filter (fun τ =>
    Groups.tSdhCondition (g₁ := g)
      (τ, (runOutput (realAns τ) strat fuel st₀).1,
        g ^ ((runOutput (realAns τ) strat fuel st₀).2.eval τ).val))

/-- **Set transport.** The group-level winning-trapdoor set IS the field-level one:
`groupWinSet g = GgmAdaptive.realWinSet`, pointwise by `tSdhCondition_iff_field`. -/
theorem groupWinSet_eq_realWinSet {g : G} (hord : orderOf g = p)
    (strat : Strat p) (st₀ : St p) (fuel : ℕ) :
    groupWinSet g strat st₀ fuel = realWinSet strat st₀ fuel := by
  classical
  ext τ
  simp only [groupWinSet, realWinSet, Finset.mem_filter, and_congr_right_iff]
  intro _ _
  exact gpow_val_inj_iff hord

/-- **THE TRANSPORTED ADAPTIVE BOUND (cardinality).** The number of trapdoors on which the
adaptive generic adversary's realized group element satisfies ArkLib's `tSdhCondition` is
≤ `fuel·Δ + (D+1)` — `GgmAdaptive.card_realWinSet_le`, now stated on the group side of the
encoding. -/
theorem field_bound_transports_to_group {g : G} (hord : orderOf g = p)
    (strat : Strat p) (st₀ : St p) (fuel : ℕ) (D Δ : ℕ)
    (hdeg_out : (symOutput strat st₀ fuel).2.natDegree ≤ D)
    (hdeg_pairs : ∀ q ∈ badPolys strat st₀ fuel, q.natDegree ≤ Δ) :
    (groupWinSet g strat st₀ fuel).card ≤ fuel * Δ + (D + 1) := by
  rw [groupWinSet_eq_realWinSet hord strat st₀ fuel]
  exact card_realWinSet_le strat st₀ fuel D Δ hdeg_out hdeg_pairs

/-- **THE TRANSPORTED ADAPTIVE BOUND (fraction).** The fraction of the `p−1` nonzero trapdoors
on which the realized group element wins ArkLib's `tSdhCondition` is
≤ `(fuel·Δ + (D+1))/(p−1)` — `GgmAdaptive.adaptive_ggm_sound` on the group side. This rational
is the counting-level value of the probability `tSdhExperiment` assigns to the same condition
under uniform nonzero `τ` (see the NAMED RESIDUAL in the header for the `ProbComp` threading). -/
theorem fraction_bound_transports_to_group {g : G} (hord : orderOf g = p)
    (strat : Strat p) (st₀ : St p) (fuel : ℕ) (D Δ : ℕ) (hp : 2 ≤ p)
    (hdeg_out : (symOutput strat st₀ fuel).2.natDegree ≤ D)
    (hdeg_pairs : ∀ q ∈ badPolys strat st₀ fuel, q.natDegree ≤ Δ) :
    ((groupWinSet g strat st₀ fuel).card : ℚ) / (p - 1)
      ≤ ((fuel * Δ + (D + 1) : ℕ) : ℚ) / (p - 1) := by
  rw [groupWinSet_eq_realWinSet hord strat st₀ fuel]
  exact adaptive_ggm_sound strat st₀ fuel D Δ hp hdeg_out hdeg_pairs

/-! ## Axiom hygiene -/

#print axioms gpow_val_injective
#print axioms gpow_val_inj_iff
#print axioms gpow_val_bijective
#print axioms tSdhCondition_iff_field
#print axioms groupWinSet_eq_realWinSet
#print axioms field_bound_transports_to_group
#print axioms fraction_bound_transports_to_group

end GgmArkLibTransport

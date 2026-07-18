/-
Copyright (c) 2026 Ember Arlynx. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ember Arlynx
-/
import ArkLib.Commitments.Functional.KZG.Binding
import ArkLib.Commitments.Functional.KZG.FunctionBinding.Support

/-!
# Vacuity of the concrete-group `tSdhAssumption` and `arsdhAssumption`

This file mechanizes a refutation of ArkLib's `Groups.tSdhAssumption` and `Groups.arsdhAssumption`
as stated over *concrete* prime-order groups. The $t$-SDH assumption [BB04] underlies the KZG
polynomial commitment scheme [KZG10]; ArkLib's hardness game hands its adversary the structured
reference string as concrete group elements, including the verifier leg $g_2^{\tau}$.

The refutation is that a `Classical.choice`-definable adversary is a legal inhabitant of the
adversary type. From $g_2^{\tau}$ the extractor `dlogOf` (built from ArkLib's own
`Groups.exists_zmod_power_of_generator`) recovers the trapdoor $\tau : \mathbb{Z}/p$ and returns a
winning element with probability $1$:

* `not_tSdhAssumption` — `tauExtractingAdversary` wins `tSdhExperiment` below every error `< 1`.
* `binding_hypotheses_unsatisfiable` — the hypotheses bundling KZG binding to `tSdhAssumption`
  are jointly unsatisfiable in the concrete-group model.
* `not_arsdhAssumption` / `arsdh_binding_hypotheses_unsatisfiable` — the same for the algebraic
  RSDH variant, using `arsdhExtractingAdversary` on a challenge set avoiding the trapdoor.

The finding is that hardness must be quantified over a *restricted* adversary class — the generic
group model [Sho97], [Mau05], or the algebraic group model [FKL18] — where the trapdoor is never
in the adversary's view. The companion `GgmEndToEnd` file supplies that generic bound.

## References

* [Boneh, D., and Boyen, X., *Short Signatures Without Random Oracles*][BB04]
* [Kate, A., Zaverucha, G. M., and Goldberg, I., *Constant-Size Commitments to Polynomials and
    Their Applications*][KZG10]
* [Shoup, V., *Lower Bounds for Discrete Logarithms and Related Problems*][Sho97]
* [Maurer, U., *Abstract Models of Computation in Cryptography*][Mau05]
* [Fuchsbauer, G., Kiltz, E., and Loss, J., *The Algebraic Group Model and its Applications*][FKL18]
-/

open OracleSpec OracleComp
open scoped NNReal ENNReal

namespace ArkLibVacuity

section Dlog

variable {p : ℕ} [Fact (Nat.Prime p)]

/-- The choice-definable discrete logarithm base a nontrivial `g` in a prime-order group.
This is *not* an algorithm: it is `Exists.choose` applied to ArkLib's own
`Groups.exists_zmod_power_of_generator`. It is nevertheless a perfectly legal
inhabitant of `ZMod p`, and that is the whole point. -/
noncomputable def dlogOf {G : Type} [Group G] [PrimeOrderWith G p] {g : G} (hg : g ≠ 1)
    (x : G) : ZMod p :=
  (Groups.exists_zmod_power_of_generator (G := G) PrimeOrderWith.hCard hg
    (Groups.orderOf_eq_prime_of_ne_one g hg) x).choose

/-- `dlogOf` inverts exponentiation base a nontrivial element of a prime-order group. -/
lemma dlogOf_pow {G : Type} [Group G] [PrimeOrderWith G p] {g : G} (hg : g ≠ 1) (a : ZMod p) :
    dlogOf (p := p) hg (g ^ a.val) = a := by
  have hord : orderOf g = p := Groups.orderOf_eq_prime_of_ne_one g hg
  have hspec : g ^ a.val = g ^ (dlogOf (p := p) hg (g ^ a.val)).val :=
    (Groups.exists_zmod_power_of_generator (G := G) PrimeOrderWith.hCard hg hord
      (g ^ a.val)).choose_spec
  have hdiv : g ^ (dlogOf (p := p) hg (g ^ a.val) - a).val = 1 := by
    rw [← Groups.gpow_div_eq hord _ a, ← hspec, div_self']
  exact sub_eq_zero.mp (Groups.zmod_eq_zero_of_gpow_eq_one hord hdiv)

/-- Every value in the support of ArkLib's trapdoor sampler is nonzero. -/
lemma sampleNonzeroZMod_ne_zero {τ : ZMod p}
    (hτ : τ ∈ support (Groups.sampleNonzeroZMod (p := p))) : τ ≠ 0 := by
  have hp : 1 < p := Nat.Prime.one_lt Fact.out
  haveI : NeZero (p - 1) := ⟨Nat.pos_iff_ne_zero.mp (Nat.sub_pos_of_lt hp)⟩
  haveI : NeZero p := ⟨Nat.pos_iff_ne_zero.mp (Nat.zero_lt_of_lt hp)⟩
  rw [Groups.sampleNonzeroZMod, support_map] at hτ
  obtain ⟨i, -, rfl⟩ := hτ
  have hi := i.isLt
  have hlt : (i : ℕ) + 1 < p := by omega
  intro hzero
  simp only at hzero
  have hdvd : (((i : ℕ) + 1 : ℕ) : ZMod p) = 0 := by push_cast; exact hzero
  rw [ZMod.natCast_eq_zero_iff] at hdvd
  exact absurd (Nat.le_of_dvd (Nat.succ_pos _) hdvd) (not_le.mpr hlt)

/-- ArkLib's trapdoor sampler never fails. -/
lemma probFailure_sampleNonzeroZMod : Pr[⊥ | Groups.sampleNonzeroZMod (p := p)] = 0 := by
  rw [Groups.sampleNonzeroZMod]; simp

end Dlog

section Refutation

-- `PrimeOrderWith G₁ p` is deliberately absent: the t-SDH solution the adversary returns
-- lives in `G₁` as a bare group element, so nothing in this section needs `G₁` prime-order.
variable {p : ℕ} [Fact (Nat.Prime p)]
  {G₁ : Type} [Group G₁] {g₁ : G₁}
  {G₂ : Type} [Group G₂] [PrimeOrderWith G₂ p] {g₂ : G₂}
  [∀ i, SampleableType (unifSpec.Range i)]

/-- The winning t-SDH adversary. It reads `g₂ ^ τ` out of the *verifier* leg of the SRS,
recovers `τ` by `Classical.choice`, and returns the t-SDH solution at offset `c = 0`.
It makes ZERO oracle queries: all of its work happens under `pure`, which the free monad
`ProbComp` does not charge for. -/
noncomputable def tauExtractingAdversary (hg₂ : g₂ ≠ 1) (D : ℕ) :
    Groups.tSdhAdversary (G₁ := G₁) (G₂ := G₂) (p := p) D :=
  fun srs => pure (some (0, g₁ ^ (1 / dlogOf (p := p) hg₂ srs.2[1]).val))

/-- The t-SDH game with the exhibited adversary collapses to a single `map` over the
trapdoor sampler: the adversary has already recovered `τ`. -/
lemma game_run_eq (hg₂ : g₂ ≠ 1) (D : ℕ) :
    (Groups.tSdhGame (g₁ := g₁) (g₂ := g₂) D
      (tauExtractingAdversary (G₁ := G₁) (g₁ := g₁) (g₂ := g₂) (p := p) hg₂ D)).run
      = (fun τ : ZMod p => some (τ, (0 : ZMod p), g₁ ^ (1 / τ).val))
          <$> Groups.sampleNonzeroZMod := by
  simp [Groups.tSdhGame, tauExtractingAdversary, Groups.PowerSrs.generate,
    Groups.PowerSrs.tower, dlogOf_pow hg₂]

/-- The exhibited adversary wins the t-SDH game with probability exactly `1`. -/
theorem tSdhExperiment_tauExtractingAdversary (hg₂ : g₂ ≠ 1) (D : ℕ) :
    Groups.tSdhExperiment (g₁ := g₁) (g₂ := g₂) D
      (tauExtractingAdversary (G₁ := G₁) (g₁ := g₁) (g₂ := g₂) (p := p) hg₂ D) = 1 := by
  classical
  rw [Groups.tSdhExperiment, probEvent_eq_one_iff]
  refine ⟨?_, ?_⟩
  · rw [OptionT.probFailure_eq, game_run_eq (g₁ := g₁) hg₂ D, probFailure_map,
      probFailure_sampleNonzeroZMod]
    simp
  · intro x hx
    rw [OptionT.support_def, game_run_eq (g₁ := g₁) hg₂ D, support_map] at hx
    obtain ⟨τ, hτ, hxτ⟩ := hx
    simp only [Option.some.injEq] at hxτ
    subst hxτ
    have hτ0 : τ ≠ 0 := sampleNonzeroZMod_ne_zero hτ
    exact ⟨by simpa using hτ0, by simp⟩

/-- **The refutation.** ArkLib's `tSdhAssumption` is FALSE for every error bound `< 1`,
at every degree `D`, in every prime-order group pair with a nontrivial `g₂`.
No hypothesis about the size of `p` is needed: this is not an asymptotic statement. -/
theorem not_tSdhAssumption (hg₂ : g₂ ≠ 1) (D : ℕ) (error : ℝ≥0) (herr : (error : ℝ≥0∞) < 1) :
    ¬ Groups.tSdhAssumption (p := p) (G₁ := G₁) (G₂ := G₂) (g₁ := g₁) (g₂ := g₂) D error := by
  intro h
  have hle := h (tauExtractingAdversary (G₁ := G₁) (g₁ := g₁) (g₂ := g₂) (p := p) hg₂ D)
  rw [tSdhExperiment_tauExtractingAdversary (g₁ := g₁) hg₂ D] at hle
  exact absurd (lt_of_le_of_lt hle herr) (lt_irrefl 1)

omit [PrimeOrderWith G₂ p] in
/-- **The other regime.** For any error bound `≥ 1`, `tSdhAssumption` holds *trivially*: a
success probability is always `≤ 1`. Combined with `not_tSdhAssumption` (false for `error < 1`),
this shows `tSdhAssumption` has NO content at ANY parameter — it is either false or vacuously
true. `probEvent_le_one` is the whole argument. -/
theorem tSdhAssumption_trivial_of_one_le (D : ℕ) (error : ℝ≥0)
    (herr : (1 : ℝ≥0∞) ≤ (error : ℝ≥0∞)) :
    Groups.tSdhAssumption (p := p) (G₁ := G₁) (G₂ := G₂) (g₁ := g₁) (g₂ := g₂) D error := by
  intro adversary
  refine le_trans ?_ herr
  rw [Groups.tSdhExperiment]
  exact probEvent_le_one

/-! ### Canary

A gate that accepts everything is a broken gate. The two lemmas below check that
`tSdhExperiment` is not *constantly* `1` — i.e. that the probability-1 theorem above is a
statement about the exhibited adversary and not an artifact of the probability machinery. -/

/-- An adversary that simply gives up. -/
def givingUpAdversary (D : ℕ) : Groups.tSdhAdversary (G₁ := G₁) (G₂ := G₂) (p := p) D :=
  fun _ => pure none

omit [PrimeOrderWith G₂ p] in
/-- CANARY: giving up loses with probability `1`, so `tSdhExperiment` discriminates. -/
theorem tSdhExperiment_givingUpAdversary (D : ℕ) :
    Groups.tSdhExperiment (g₁ := g₁) (g₂ := g₂) D
      (givingUpAdversary (G₁ := G₁) (G₂ := G₂) (p := p) D) = 0 := by
  classical
  rw [Groups.tSdhExperiment, probEvent_eq_zero_iff]
  intro x hx
  rw [OptionT.support_def] at hx
  simp [Groups.tSdhGame, givingUpAdversary] at hx

/-- CANARY: consequently the probability-1 result is not vacuous — the two adversaries
are genuinely separated by the experiment. -/
theorem experiment_discriminates (hg₂ : g₂ ≠ 1) (D : ℕ) :
    Groups.tSdhExperiment (g₁ := g₁) (g₂ := g₂) D
      (givingUpAdversary (G₁ := G₁) (G₂ := G₂) (p := p) D)
    ≠ Groups.tSdhExperiment (g₁ := g₁) (g₂ := g₂) D
      (tauExtractingAdversary (G₁ := G₁) (g₁ := g₁) (g₂ := g₂) (p := p) hg₂ D) := by
  rw [tSdhExperiment_givingUpAdversary (g₁ := g₁) (g₂ := g₂) D,
    tSdhExperiment_tauExtractingAdversary (g₁ := g₁) hg₂ D]
  exact zero_ne_one

end Refutation

section BindingIsVacuous

variable {p : ℕ} [Fact (Nat.Prime p)]
  {G₁ : Type} [Group G₁] [PrimeOrderWith G₁ p] {g₁ : G₁}
  {G₂ : Type} [Group G₂] [PrimeOrderWith G₂ p] {g₂ : G₂}
  {Gₜ : Type} [Group Gₜ] [PrimeOrderWith Gₜ p]
  [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)]
  [Module (ZMod p) (Additive Gₜ)]
  [∀ i, SampleableType (unifSpec.Range i)]

omit [∀ i, SampleableType (unifSpec.Range i)] in
/-- `binding`'s own pairing hypothesis forces the G₂ generator to be nontrivial,
because the pairing is `ZMod p`-bilinear and therefore kills the identity. -/
lemma g₂_ne_one_of_pairing_ne_zero
    (pairing : (Additive G₁) →ₗ[ZMod p] (Additive G₂) →ₗ[ZMod p] (Additive Gₜ))
    (hpair : pairing (Additive.ofMul g₁) (Additive.ofMul g₂) ≠ 0) : g₂ ≠ 1 := by
  intro h
  apply hpair
  rw [show (Additive.ofMul g₂) = 0 from congrArg Additive.ofMul h]
  exact map_zero _

/-- **`KZG.binding`'s hypotheses are jointly unsatisfiable at every meaningful error.**
The very pairing nondegeneracy that `binding` needs to run its reduction is what makes
its `t`-SDH premise false. So `binding` is only ever applicable with `tSdhError ≥ 1`,
where its conclusion is a triviality (a probability is always `≤ 1`). -/
theorem binding_hypotheses_unsatisfiable
    (pairing : (Additive G₁) →ₗ[ZMod p] (Additive G₂) →ₗ[ZMod p] (Additive Gₜ))
    (hpair : pairing (Additive.ofMul g₁) (Additive.ofMul g₂) ≠ 0)
    (n : ℕ) (tSdhError : ℝ≥0) (herr : (tSdhError : ℝ≥0∞) < 1) :
    ¬ Groups.tSdhAssumption (p := p) (G₁ := G₁) (G₂ := G₂) (g₁ := g₁) (g₂ := g₂) n tSdhError :=
  not_tSdhAssumption (g₁ := g₁) (g₂_ne_one_of_pairing_ne_zero pairing hpair) n tSdhError herr

end BindingIsVacuous

/-! ## ARSDH is vacuous in the `function_binding` parameter regime by the same argument

ArkLib's `Groups.arsdhAssumption` (`Definition 9.6` in CGKY25, powering `KZG.function_binding`)
has the identical shape: `∀ adversary, arsdhExperiment D adversary ≤ error`, quantifying over the
adversary TYPE with no resource bound. In the parameter regime used by `function_binding`, it falls
the same two ways. The only extra work over the
`t`-SDH case is producing, for each trapdoor `τ`, a size-`D+1` set `S` with `τ ∉ S` (so the
vanishing polynomial `Z_S` does not vanish at `τ`); this requires `p ≥ D+2`, which is exactly the
`hp : p ≥ n + 2` hypothesis `function_binding` already carries. No claim is made here about the
separate degenerate regime `p < D + 2`, where a size-`D+1` set avoiding τ may not exist. -/

section ArsdhRefutation

open CompPoly CompPoly.CPolynomial

-- The combinatorial helpers below are group-free — they need only `ZMod p`. The group and
-- sampling instances enter with the second `variable` block, just before the adversary.
variable {p : ℕ} [Fact (Nat.Prime p)]

/-- When `p ≥ D + 2` there is a size-`D+1` subset of `ZMod p` avoiding any given `τ`.
Not an algorithm — `Finset.exists_subset_card_eq` on `univ.erase τ`. -/
lemma exists_finset_card_avoiding (D : ℕ) (hpD : D + 2 ≤ p) (τ : ZMod p) :
    ∃ S : Finset (ZMod p), S.card = D + 1 ∧ τ ∉ S := by
  haveI : NeZero p := ⟨Nat.pos_iff_ne_zero.mp (Nat.Prime.pos Fact.out)⟩
  have hcard : D + 1 ≤ (Finset.univ.erase τ).card := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ τ), Finset.card_univ, ZMod.card]
    omega
  obtain ⟨t, ht_sub, ht_card⟩ := Finset.exists_subset_card_eq hcard
  exact ⟨t, ht_card, fun h => (Finset.mem_erase.mp (ht_sub h)).1 rfl⟩

/-- The trapdoor-indexed choice of avoiding set. Choice-definable, like `dlogOf`. -/
noncomputable def chosenFinset (D : ℕ) (hpD : D + 2 ≤ p) (τ : ZMod p) : Finset (ZMod p) :=
  (exists_finset_card_avoiding (p := p) D hpD τ).choose

lemma chosenFinset_card (D : ℕ) (hpD : D + 2 ≤ p) (τ : ZMod p) :
    (chosenFinset (p := p) D hpD τ).card = D + 1 :=
  (exists_finset_card_avoiding (p := p) D hpD τ).choose_spec.1

lemma chosenFinset_not_mem (D : ℕ) (hpD : D + 2 ≤ p) (τ : ZMod p) :
    τ ∉ chosenFinset (p := p) D hpD τ :=
  (exists_finset_card_avoiding (p := p) D hpD τ).choose_spec.2

variable {G₁ : Type} [Group G₁] [PrimeOrderWith G₁ p] {g₁ : G₁}
  {G₂ : Type} [Group G₂] [PrimeOrderWith G₂ p] {g₂ : G₂}
  [∀ i, SampleableType (unifSpec.Range i)]

/-- The winning ARSDH adversary. As with `t`-SDH it recovers `τ` from `g₂ ^ τ` in the verifier
leg of the SRS by `Classical.choice`, then returns the ARSDH solution: a size-`D+1` set `S`
avoiding `τ`, the nontrivial element `g₁`, and `g₁ ^ (1 / Z_S(τ))`. ZERO oracle queries. -/
noncomputable def arsdhExtractingAdversary (hg₂ : g₂ ≠ 1) (D : ℕ) (hpD : D + 2 ≤ p) :
    Groups.arsdhAdversary (G₁ := G₁) (G₂ := G₂) (p := p) D :=
  fun srs =>
    pure (some
      (chosenFinset (p := p) D hpD (dlogOf (p := p) hg₂ srs.2[1]),
        g₁,
        g₁ ^ (1 / (∏ s ∈ chosenFinset (p := p) D hpD (dlogOf (p := p) hg₂ srs.2[1]),
          (X - C s : CPolynomial (ZMod p))).eval (dlogOf (p := p) hg₂ srs.2[1])).val))

omit [PrimeOrderWith G₁ p] in
/-- The ARSDH game with the exhibited adversary collapses to a single `map` over the trapdoor
sampler: the adversary has already recovered `τ`, so `S`, `h₁`, `h₂` are functions of `τ`. -/
lemma arsdh_game_run_eq (hg₂ : g₂ ≠ 1) (D : ℕ) (hpD : D + 2 ≤ p) :
    (Groups.arsdhGame (g₁ := g₁) (g₂ := g₂) D
      (arsdhExtractingAdversary (G₁ := G₁) (g₁ := g₁) (g₂ := g₂) (p := p) hg₂ D hpD)).run
      = (fun τ : ZMod p => some
          (τ, chosenFinset (p := p) D hpD τ, g₁,
            g₁ ^ (1 / (∏ s ∈ chosenFinset (p := p) D hpD τ,
              (X - C s : CPolynomial (ZMod p))).eval τ).val))
          <$> Groups.sampleNonzeroZMod := by
  simp [Groups.arsdhGame, arsdhExtractingAdversary, Groups.PowerSrs.generate,
    Groups.PowerSrs.tower, dlogOf_pow hg₂]

/-- The exhibited adversary wins the ARSDH game with probability exactly `1`. -/
theorem arsdhExperiment_arsdhExtractingAdversary (hg₁ : g₁ ≠ 1) (hg₂ : g₂ ≠ 1)
    (D : ℕ) (hpD : D + 2 ≤ p) :
    Groups.arsdhExperiment (g₁ := g₁) (g₂ := g₂) D
      (arsdhExtractingAdversary (G₁ := G₁) (g₁ := g₁) (g₂ := g₂) (p := p) hg₂ D hpD) = 1 := by
  classical
  rw [Groups.arsdhExperiment, probEvent_eq_one_iff]
  refine ⟨?_, ?_⟩
  · rw [OptionT.probFailure_eq, arsdh_game_run_eq (g₁ := g₁) hg₂ D hpD, probFailure_map,
      probFailure_sampleNonzeroZMod]
    simp
  · intro x hx
    rw [OptionT.support_def, arsdh_game_run_eq (g₁ := g₁) hg₂ D hpD, support_map] at hx
    obtain ⟨τ, hτ, hxτ⟩ := hx
    simp only [Option.some.injEq] at hxτ
    subst hxτ
    refine ⟨chosenFinset_card (p := p) D hpD τ, ?_, hg₁, rfl⟩
    exact KZG.CommitmentScheme.prod_x_sub_c_eval_ne_zero (chosenFinset_not_mem (p := p) D hpD τ)

/-- **The refutation, for ARSDH.** ArkLib's `arsdhAssumption` is FALSE for every error bound
`< 1` (at every degree `D` with `p ≥ D + 2`, in every prime-order group pair with nontrivial
`g₁, g₂`). Same `Classical.choice` adversary, same argument as `not_tSdhAssumption`. -/
theorem not_arsdhAssumption (hg₁ : g₁ ≠ 1) (hg₂ : g₂ ≠ 1) (D : ℕ) (hpD : D + 2 ≤ p)
    (error : ℝ≥0) (herr : (error : ℝ≥0∞) < 1) :
    ¬ Groups.arsdhAssumption (p := p) (G₁ := G₁) (G₂ := G₂) (g₁ := g₁) (g₂ := g₂) D error := by
  intro h
  have hle := h (arsdhExtractingAdversary (G₁ := G₁) (g₁ := g₁) (g₂ := g₂) (p := p) hg₂ D hpD)
  rw [arsdhExperiment_arsdhExtractingAdversary (g₁ := g₁) hg₁ hg₂ D hpD] at hle
  exact absurd (lt_of_le_of_lt hle herr) (lt_irrefl 1)

omit [PrimeOrderWith G₂ p] in
/-- **The other error regime, for ARSDH.** For any error bound `≥ 1`, `arsdhAssumption` holds
trivially. Combined with `not_arsdhAssumption`, this exhausts the error regimes when
`D + 2 ≤ p`, which is the regime consumed by `function_binding`. -/
theorem arsdhAssumption_trivial_of_one_le (D : ℕ) (error : ℝ≥0)
    (herr : (1 : ℝ≥0∞) ≤ (error : ℝ≥0∞)) :
    Groups.arsdhAssumption (p := p) (G₁ := G₁) (G₂ := G₂) (g₁ := g₁) (g₂ := g₂) D error := by
  intro adversary
  refine le_trans ?_ herr
  rw [Groups.arsdhExperiment]
  exact probEvent_le_one

/-- CANARY: an ARSDH adversary that gives up loses with probability `1`, so `arsdhExperiment`
discriminates — the probability-`1` result above is about the exhibited adversary, not an
artifact of the machinery. -/
def arsdhGivingUpAdversary (D : ℕ) : Groups.arsdhAdversary (G₁ := G₁) (G₂ := G₂) (p := p) D :=
  fun _ => pure none

omit [PrimeOrderWith G₂ p] in
theorem arsdhExperiment_givingUpAdversary (D : ℕ) :
    Groups.arsdhExperiment (g₁ := g₁) (g₂ := g₂) D
      (arsdhGivingUpAdversary (G₁ := G₁) (G₂ := G₂) (p := p) D) = 0 := by
  classical
  rw [Groups.arsdhExperiment, probEvent_eq_zero_iff]
  intro x hx
  rw [OptionT.support_def] at hx
  simp [Groups.arsdhGame, arsdhGivingUpAdversary] at hx

/-- **Consumer.** `KZG.function_binding` derives evaluation/function binding from
`arsdhAssumption` under `hp : p ≥ n + 2` and `hpair : pairing g₁ g₂ ≠ 0`. Since that pairing
nondegeneracy forces `g₁ ≠ 1` and `g₂ ≠ 1` (see `g₂_ne_one_of_pairing_ne_zero`), and `p ≥ n + 2`
is exactly the hypothesis `not_arsdhAssumption` needs, `function_binding` is applicable only with
`arsdhError ≥ 1`, where its conclusion is the triviality `probability ≤ 1`. Identical vacuity to
`binding` / `t`-SDH. -/
theorem arsdh_binding_hypotheses_unsatisfiable (hg₁ : g₁ ≠ 1) (hg₂ : g₂ ≠ 1)
    (n : ℕ) (hp : n + 2 ≤ p) (arsdhError : ℝ≥0) (herr : (arsdhError : ℝ≥0∞) < 1) :
    ¬ Groups.arsdhAssumption (p := p) (G₁ := G₁) (G₂ := G₂) (g₁ := g₁) (g₂ := g₂) n arsdhError :=
  not_arsdhAssumption (g₁ := g₁) hg₁ hg₂ n hp arsdhError herr

end ArsdhRefutation

end ArkLibVacuity

#print axioms ArkLibVacuity.not_tSdhAssumption
#print axioms ArkLibVacuity.tSdhAssumption_trivial_of_one_le
#print axioms ArkLibVacuity.not_arsdhAssumption
#print axioms ArkLibVacuity.arsdhAssumption_trivial_of_one_le

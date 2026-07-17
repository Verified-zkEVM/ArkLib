/-
Copyright (c) 2026 Ember Arlynx. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ember Arlynx
-/
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Finset.Card

/-!
# Static generic-group $t$-SDH soundness

The `KzgVacuity` file shows that the concrete-group $t$-SDH assumption [BB04] is vacuous: ArkLib's
adversary receives the structured reference string as concrete group elements
`Vector G₁ (D+1) × Vector G₂ 2`, and from the verifier leg $g_2^{\tau}$ a
`Classical.choice`-definable adversary recovers the trapdoor and wins with probability $1$.

This file establishes the *static* generic group model [Sho97], [Mau05] bound, the $q = 0$
fragment against which the Boneh–Boyen $t$-SDH bound is proved. A generic adversary never sees
group elements as field data. We model the committed-generic adversary: without the trapdoor, it
commits to a challenge offset $c$ and a representation polynomial $f$ of degree $\le D$ over
$\mathbb{Z}/p$. The environment defines the output group element as $g_1^{f(\tau)}$; winning
requires $f(\tau) = 1/(\tau + c)$ at the environment's random $\tau$.

Because $f$ is chosen with no $\tau$ in scope, there is nothing for `Classical.choice` to extract,
and the winning set of trapdoors is bounded by Schwartz–Zippel [Sch80], [Zip79]. `ggm_tSdh_sound`
proves the numeric bound $(D+1)/(p-1)$ for every committed adversary — including every
choice-definable one — so the concrete-group attack is dead in this model.

## References

* [Boneh, D., and Boyen, X., *Short Signatures Without Random Oracles*][BB04]
* [Shoup, V., *Lower Bounds for Discrete Logarithms and Related Problems*][Sho97]
* [Maurer, U., *Abstract Models of Computation in Cryptography*][Mau05]
* [Schwartz, J. T., *Fast Probabilistic Algorithms for Verification of Polynomial
    Identities*][Sch80]
* [Zippel, R., *Probabilistic Algorithms for Sparse Polynomials*][Zip79]
-/

open Polynomial

namespace GgmCandidate

variable {p : ℕ} [Fact (Nat.Prime p)]

/-! ## The winning polynomial and its Schwartz–Zippel degree bound -/

/-- The winning polynomial for a committed strategy `(c, f)`:
`w(X) = f(X) · (X + c) - 1`. A nonzero `τ` with `τ + c ≠ 0` wins iff `f(τ) = 1/(τ+c)`, i.e. iff
`w(τ) = 0`. -/
noncomputable def winPoly (c : ZMod p) (f : (ZMod p)[X]) : (ZMod p)[X] :=
  f * (X + C c) - 1

/-- `winPoly` is never the zero polynomial: `f·(X+c) = 1` would force `deg(f·(X+c)) = 0`, but the
degree-1 factor `X + c` is nonzero over the field `ZMod p`, so the product has degree ≥ 1. -/
lemma winPoly_ne_zero (c : ZMod p) (f : (ZMod p)[X]) : winPoly c f ≠ 0 := by
  intro h
  rw [winPoly, sub_eq_zero] at h            -- h : f * (X + C c) = 1
  have hlin_ne : (X + C c : (ZMod p)[X]) ≠ 0 := (monic_X_add_C c).ne_zero
  have hf_ne : f ≠ 0 := by
    rintro rfl; rw [zero_mul] at h; exact zero_ne_one h
  have hdeg := natDegree_mul hf_ne hlin_ne
  rw [h, natDegree_one, natDegree_X_add_C] at hdeg
  omega

/-- `winPoly` has degree ≤ D + 1 when `f` has degree ≤ D. -/
lemma winPoly_natDegree_le {D : ℕ} (c : ZMod p) {f : (ZMod p)[X]} (hf : f.natDegree ≤ D) :
    (winPoly c f).natDegree ≤ D + 1 := by
  unfold winPoly
  refine (natDegree_sub_le _ _).trans ?_
  rw [natDegree_one]
  refine max_le ?_ (by omega)
  refine natDegree_mul_le.trans ?_
  have hlin : (X + C c : (ZMod p)[X]).natDegree = 1 := natDegree_X_add_C c
  omega

/-- **Schwartz–Zippel core.** The number of field points where a committed strategy `(c, f)` (with
`deg f ≤ D`) wins is bounded by the degree: `#roots(winPoly) ≤ D + 1`. -/
lemma card_roots_winPoly_le {D : ℕ} (c : ZMod p) {f : (ZMod p)[X]} (hf : f.natDegree ≤ D) :
    Multiset.card (winPoly c f).roots ≤ D + 1 :=
  (card_roots' (winPoly c f)).trans (winPoly_natDegree_le c hf)

/-! ## The τ-free generic adversary and the counting experiment

A committed generic adversary is a bare `(c, f)` — a challenge offset and a degree-≤D
representation polynomial — with **no trapdoor input**. This is the whole point: the type the
attack exploited (`Vector G₁ (D+1) × Vector G₂ 2 → …`, carrying `g₂^τ`) is gone, so
`Classical.choice` has no `∃ a, · = g^a` to invoke. -/

/-- A committed (static) generic t-SDH adversary: a challenge offset and a representation
polynomial of degree ≤ D, chosen independently of the trapdoor. -/
structure GenericAdversary (D : ℕ) (p : ℕ) where
  offset : ZMod p
  repr : (ZMod p)[X]
  degree_le : repr.natDegree ≤ D

/-- The nonzero field elements — the support of ArkLib's trapdoor sampler `sampleNonzeroZMod`. -/
noncomputable def nonzeroPoints : Finset (ZMod p) :=
  (Finset.univ : Finset (ZMod p)).erase 0

/-- The trapdoors on which the committed adversary `A` wins: nonzero `τ` with `τ + c ≠ 0` and
`f(τ) = 1/(τ+c)`. -/
noncomputable def winningPoints {D : ℕ} (A : GenericAdversary D p) : Finset (ZMod p) :=
  nonzeroPoints.filter (fun τ => τ + A.offset ≠ 0 ∧ A.repr.eval τ = 1 / (τ + A.offset))

/-- Every winning `τ` is a root of `winPoly` (turning the rational win-condition into the
polynomial identity Schwartz–Zippel bounds). -/
lemma winningPoints_subset_roots {D : ℕ} (A : GenericAdversary D p) :
    ∀ τ ∈ winningPoints A, τ ∈ (winPoly A.offset A.repr).roots := by
  intro τ hτ
  rw [winningPoints, Finset.mem_filter] at hτ
  obtain ⟨_, hne, heval⟩ := hτ
  rw [mem_roots']
  refine ⟨winPoly_ne_zero A.offset A.repr, ?_⟩
  unfold winPoly
  simp only [IsRoot.def, eval_sub, eval_mul, eval_add, eval_X, eval_C, eval_one]
  rw [heval, one_div, inv_mul_cancel₀ hne, sub_self]

/-- **The numeric GGM bound (counting form).** For EVERY committed generic adversary — including
every `Classical.choice`-definable one — the number of trapdoors on which it wins is ≤ D + 1. -/
theorem card_winningPoints_le {D : ℕ} (A : GenericAdversary D p) :
    (winningPoints A).card ≤ D + 1 := by
  classical
  have hsub : winningPoints A ⊆ (winPoly A.offset A.repr).roots.toFinset := by
    intro τ hτ
    rw [Multiset.mem_toFinset]
    exact winningPoints_subset_roots A τ hτ
  exact (Finset.card_le_card hsub).trans
    ((Multiset.toFinset_card_le (m := (winPoly A.offset A.repr).roots)).trans
      (card_roots_winPoly_le A.offset A.degree_le))

/-- The counting experiment: the fraction of nonzero trapdoors on which the committed adversary
wins. This is the exact success probability of the static generic adversary in the t-SDH game,
`τ` sampled uniformly from `sampleNonzeroZMod` (support = the `p - 1` nonzero residues). -/
noncomputable def ggmExperiment {D : ℕ} (A : GenericAdversary D p) : ℚ :=
  (winningPoints A).card / (p - 1)

/-! ## Survives-attack: the numeric bound holds for EVERY generic adversary -/

/-- **PROVEN-SURVIVES.** Every committed generic t-SDH adversary — over the FULL adversary type,
so including any `Classical.choice`/`Exists.choose`-defined one — wins on at most a `(D+1)/(p-1)`
fraction of trapdoors. There is no winning adversary at probability 1; the exact
trapdoor-extraction attack (`tauExtractingAdversary`) cannot even be typed here, because
`GenericAdversary` receives no group element and hence no `∃ a, · = g^a` for choice to invert. -/
theorem ggm_tSdh_sound {D : ℕ} (A : GenericAdversary D p) (hp : 2 ≤ p) :
    ggmExperiment A ≤ (D + 1 : ℚ) / (p - 1) := by
  unfold ggmExperiment
  have hmono : ((winningPoints A).card : ℚ) ≤ (D + 1 : ℚ) := by
    exact_mod_cast card_winningPoints_le A
  have hden : (0 : ℚ) < (p : ℚ) - 1 := by
    have : (2 : ℚ) ≤ (p : ℚ) := by exact_mod_cast hp
    linarith
  gcongr

omit [Fact (Nat.Prime p)] in
/-- **Non-vacuity is now built in.** For `p > D + 2` the bound `(D+1)/(p-1)` is a genuine rational
strictly below `1`: the assumption `∀ A, ggmExperiment A ≤ (D+1)/(p-1)` is TRUE (proved above, over
the whole type), not refutable, and its bound is nontrivial. Contrast `not_tSdhAssumption`, which
made the original assumption FALSE below `1`. -/
theorem ggm_bound_lt_one {D : ℕ} (hp : D + 2 < p) :
    ((D : ℚ) + 1) / (p - 1) < 1 := by
  have hden : (0 : ℚ) < (p : ℚ) - 1 := by
    have : (2 : ℚ) ≤ (p : ℚ) := by
      have : (2 : ℕ) ≤ p := by omega
      exact_mod_cast this
    linarith
  rw [div_lt_one hden]
  have h1 : (D : ℚ) + 2 < (p : ℚ) := by exact_mod_cast hp
  linarith

end GgmCandidate

#print axioms GgmCandidate.winPoly_ne_zero
#print axioms GgmCandidate.card_winningPoints_le
#print axioms GgmCandidate.ggm_tSdh_sound

/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

import ArkLib.ProofSystem.RingSwitching.Generic.Carrier
import ArkLib.Data.Probability.Instances
import Mathlib.FieldTheory.Finite.GaloisField

/-!
# Generic Ring-Switching — Batching Separation (S3)

Discharges design step 5 — the *one genuine design axis* of the generic ring switch (see
`docs/kb/concepts/ring-switching.md`, "The Generic layer", for the spine/pillar vocabulary):
folding the `|W|` recombined claims into a single claim. The two
known strategies are not two protocols but two instances of one interface:

* `BatchingStrategy.gammaPowers` — γ-power random linear combination (the "Ring switching,
  generalized" note [RSG]): sample `γ ←$ P`, weight claim `u` by `γ^u`. Universal (any claim
  count `e`); error `e/|P|`.
* `BatchingStrategy.eqFold` — eq-indicator folding (Flock App. B [BRW26]; ArkLib's DP24 batching
  phase): claims indexed by `{0,1}^κ`, sample `r'' ←$ P^κ`, weight claim `u` by `eq̃(u, r'')`.
  Power-of-two claim counts only; error `κ/|P|`.

Both `separates` proofs are Schwartz–Zippel over a finite integral domain and reduce to the
generic `prob_schwartz_zippel_mv_polynomial` (`ArkLib/Data/Probability/Instances.lean`) — the
strategy supplies only the difference polynomial (`∑ᵤ (s−s')ᵤ Xᵘ` resp. `MLE (s−s')`), its
nonvanishing, and its degree bound. A downstream instance *picks* a strategy; it never re-proves
batching (design safety pillar: closed proven menu).

Statement conventions (deliberate, recorded):
* Challenges are `[Fintype]`/`[Nonempty]` types sampled uniformly via PMF (`Pr_{…}` from
  `ArkLib/Data/Probability/Notation.lean`), matching the reusable Schwartz–Zippel layer. The
  bridge to the protocol-level `SampleableType` interface is deferred to S6 (wiring).
* The structure is `[CommRing P]`-only; `[IsDomain P] [Fintype P]` gate the *proven instances*
  (and, later, the S6 domain soundness theorem) — the design's fork lives at the theorem, not
  the vocabulary, keeping the S8 non-domain (Hachi) sibling statable. No `Field` assumption.
* The base ring `B` does not appear: separation is purely a `P`-fact.

The file also provides `decoupledFieldCarrier` (`P = 𝔽₄ ≠ E = 𝔽₈`), closing the anti-overfit
gate "R5" (see the KB page): the `[IsDomain P]`-gated layer is exercised on a decoupled
non-Binius carrier (INV-2).

## References

- [BRW26] Bünz, Rothblum, Wang. "Flock: Fast Proving for Batch Boolean Computations." Cryptology
  ePrint Archive, Report 2026/1329. Appendix B (eq-fold batching, error `κ/|F|`).
- [RSG] "Ring switching, generalized." Note, leanEthereum/leanVM-b repository (γ-power batching,
  error `e/|F|`).
-/

noncomputable section

namespace RingSwitching.Generic

open Module MvPolynomial ProbabilityTheory
open scoped NNReal ENNReal

/-- **Batching strategy** (design step 5, the one real design axis): how to fold a `W`-indexed
family of claims over `P` into a single claim. `weight c u` is the coefficient the challenge `c`
assigns to claim slot `u`; `separates` is the Schwartz–Zippel guarantee that two *distinct*
claim-tuples collide after weighting with probability at most `error` — the only fact batching
soundness (S6) consumes. Instances are a closed, proven menu; a carrier picks one.

The structure itself is gated only on `[CommRing P]`: the domain/finiteness hypotheses live on
the proven instances (`gammaPowers`/`eqFold`) and on the S6 soundness theorem (`[IsDomain car.P]`,
the design's honest fork) — NOT on the vocabulary, so a non-domain carrier (Hachi `R_q`, design
§5's sibling theorem) can still *state* a strategy and supply its own proven `separates`/gap. -/
structure BatchingStrategy (P : Type) [CommRing P] (W : Type) [Fintype W] where
  /-- The verifier's batching challenge. -/
  Challenge : Type
  [ftC : Fintype Challenge]
  [neC : Nonempty Challenge]
  /-- The weight that challenge `c` assigns to claim slot `u`. -/
  weight : Challenge → W → P
  /-- The separation error (a probability, compared in `ℝ≥0∞` against a uniform challenge). -/
  error : ℝ≥0
  /-- Schwartz–Zippel separation: distinct claim-tuples stay distinct after weighting, except with
  probability `error` over the challenge. -/
  separates : ∀ s s' : W → P, s ≠ s' →
    Pr_{ let c ←$ᵖ Challenge }[ ∑ u, weight c u * s u = ∑ u, weight c u * s' u ]
      ≤ (error : ℝ≥0∞)

attribute [instance] BatchingStrategy.ftC BatchingStrategy.neC

namespace BatchingStrategy

/-- Transport a batching strategy along an equivalence of claim-index types: same challenge, same
error, weights composed with the equivalence. This is how S6 lands the proven instances at the
carrier's opening index (`gammaPowers … |>.reindex (Fintype.equivFin _)` for any finite `ιE`);
for `eqFold`, supplying `e : W' ≃ (Fin κ → Fin 2)` is exactly the instance's honest obligation to
choose a bit-indexing of its `2^κ` claims. -/
def reindex {P : Type} [CommRing P] {W : Type} [Fintype W] (bat : BatchingStrategy P W)
    {W' : Type} [Fintype W'] (e : W' ≃ W) : BatchingStrategy P W' where
  Challenge := bat.Challenge
  weight c u' := bat.weight c (e u')
  error := bat.error
  separates s s' hne := by
    have key : ∀ (c : bat.Challenge) (t : W' → P),
        ∑ u' : W', bat.weight c (e u') * t u' = ∑ u : W, bat.weight c u * (t ∘ e.symm) u :=
      fun c t => Fintype.sum_equiv e _ _ (fun u' => by simp)
    have hne' : s ∘ e.symm ≠ s' ∘ e.symm := fun hcontra =>
      hne (funext fun u' => by simpa using congrFun hcontra (e u'))
    refine (Pr_congr fun c => ?_).trans_le (bat.separates (s ∘ e.symm) (s' ∘ e.symm) hne')
    rw [key c s, key c s']

variable (P : Type) [CommRing P] [IsDomain P] [Fintype P]

/-- **γ-power random linear combination** ([RSG]): sample `γ ←$ P`, weight claim `u ∈ Fin e` by
`γ^u`. Universal — no structure on the claim count `e`. Error `e/|P|` (the difference polynomial
`∑ᵤ (s−s')ᵤ Xᵘ` has degree ≤ `e−1`; the stated error rounds up to the paper's `e/|P|`).
Exponent convention: powers run `γ^0..γ^{e−1}` (the note uses `γ^1..γ^e`) — equivalent for
separation, and slot `0` carrying the constant weight `1` is the standard RLC normalization. -/
def gammaPowers (e : ℕ) : BatchingStrategy P (Fin e) where
  Challenge := P
  weight γ u := γ ^ (u : ℕ)
  error := (e : ℝ≥0) / (Fintype.card P : ℝ≥0)
  separates s s' hne := by
    classical
    obtain ⟨u₀, hu₀⟩ := Function.ne_iff.mp hne
    -- the univariate difference polynomial `∑ᵤ (s u − s' u)·Xᵘ`
    set f : MvPolynomial (Fin 1) P := ∑ u : Fin e, C (s u - s' u) * X 0 ^ (u : ℕ) with hf
    -- the collision event is exactly the vanishing of `f` at the challenge
    have hev : ∀ γ : P,
        ((∑ u : Fin e, γ ^ (u : ℕ) * s u = ∑ u : Fin e, γ ^ (u : ℕ) * s' u) ↔
          MvPolynomial.eval (fun _ : Fin 1 => γ) f = 0) := by
      intro γ
      have hcalc : MvPolynomial.eval (fun _ : Fin 1 => γ) f
          = (∑ u : Fin e, γ ^ (u : ℕ) * s u) - ∑ u : Fin e, γ ^ (u : ℕ) * s' u := by
        rw [hf, map_sum, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun u _ => by
          simp only [map_mul, eval_C, map_pow, eval_X]; ring
      rw [hcalc, sub_eq_zero]
    -- `f ≠ 0`: its `X^{u₀}` coefficient is `s u₀ − s' u₀ ≠ 0`
    have hcoeff : MvPolynomial.coeff (Finsupp.single 0 (u₀ : ℕ)) f = s u₀ - s' u₀ := by
      rw [hf, MvPolynomial.coeff_sum]
      rw [Finset.sum_eq_single u₀]
      · rw [MvPolynomial.coeff_C_mul, MvPolynomial.coeff_X_pow]
        simp
      · intro u _ hu
        have hne' : Finsupp.single (0 : Fin 1) (u : ℕ) ≠ Finsupp.single 0 (u₀ : ℕ) :=
          fun h => hu (Fin.val_injective (Finsupp.single_injective _ h))
        rw [MvPolynomial.coeff_C_mul, MvPolynomial.coeff_X_pow, if_neg hne', mul_zero]
      · simp
    have hf_ne : f ≠ 0 := fun h0 => sub_ne_zero_of_ne hu₀ (by rw [← hcoeff, h0]; simp)
    -- degree bound `e − 1`
    have hdeg : f.totalDegree ≤ e - 1 := by
      rw [hf]
      refine totalDegree_finsetSum_le fun u _ => ?_
      refine le_trans (totalDegree_mul _ _) ?_
      have h1 : (C (s u - s' u) : MvPolynomial (Fin 1) P).totalDegree = 0 := totalDegree_C _
      have h2 : (X (0 : Fin 1) ^ (u : ℕ) : MvPolynomial (Fin 1) P).totalDegree ≤ (u : ℕ) :=
        le_trans (totalDegree_pow _ _) (by simp [totalDegree_X])
      have : (u : ℕ) ≤ e - 1 := Nat.le_sub_one_of_lt u.isLt
      omega
    refine (Pr_congr hev).trans_le
      ((prob_schwartz_zippel_single_variable f (e - 1) hf_ne hdeg).trans ?_)
    rw [ENNReal.coe_div (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)]
    gcongr
    exact_mod_cast Nat.sub_le e 1

/-- **eq-fold** ([BRW26] App. B; ArkLib's DP24 batching phase): claims indexed by the Boolean cube
`{0,1}^κ`; sample `r'' ←$ P^κ`, weight claim `u` by the multilinear eq-indicator `eq̃(u, r'')`
(the same `eqTilde ↑u r''` fold as `RingSwitching.compute_s0`, boolean point first). Power-of-two
claim counts only. Error `κ/|P|` (the difference polynomial `MLE (s−s')` is multilinear in `κ`
variables). -/
def eqFold (κ : ℕ) : BatchingStrategy P (Fin κ → Fin 2) where
  Challenge := Fin κ → P
  weight c u := eqTilde (u : Fin κ → P) c
  error := (κ : ℝ≥0) / (Fintype.card P : ℝ≥0)
  separates s s' hne := by
    classical
    obtain ⟨u₀, hu₀⟩ := Function.ne_iff.mp hne
    -- the multilinear difference polynomial `MLE (s − s')`
    set f : MvPolynomial (Fin κ) P := MLE (fun u => s u - s' u) with hf
    -- the collision event is exactly the vanishing of `f` at the challenge (MLE eq-expansion)
    have hev : ∀ c : Fin κ → P,
        ((∑ u : Fin κ → Fin 2, eqTilde (u : Fin κ → P) c * s u
            = ∑ u : Fin κ → Fin 2, eqTilde (u : Fin κ → P) c * s' u) ↔
          MvPolynomial.eval c f = 0) := by
      intro c
      have hcalc : MvPolynomial.eval c f
          = (∑ u : Fin κ → Fin 2, eqTilde (u : Fin κ → P) c * s u)
            - ∑ u : Fin κ → Fin 2, eqTilde (u : Fin κ → P) c * s' u := by
        rw [hf, MLE_eval_eq_sum_eqTilde, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun u _ => mul_sub _ _ _
      rw [hcalc, sub_eq_zero]
    -- `f ≠ 0`: it interpolates `s − s'`, which is nonzero at `u₀` (INV-3: no vacuous batching)
    have hf_ne : f ≠ 0 := fun h0 => sub_ne_zero_of_ne hu₀ (by
      have h := MLE_eval_zeroOne (R := P) u₀ (fun u => s u - s' u)
      rw [← hf, h0, map_zero] at h
      exact h.symm)
    -- degree bound: multilinear in `κ` variables
    have hdeg : f.totalDegree ≤ κ := by
      rw [hf]
      simpa using MLE_totalDegree_le (fun u => s u - s' u)
    exact (Pr_congr hev).trans_le
      ((prob_schwartz_zippel_mv_polynomial f κ hf_ne hdeg).trans_eq
        (ENNReal.coe_div (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)).symm)

end BatchingStrategy

/-! ## Decoupled field carrier (gate "R5") -/

/-- **Decoupled field carrier** (R5 gate): `P = 𝔽₄`, `E = 𝔽₈` — two *fields* with `P ≠ E` and
distinct ranks (2 ≠ 3) over `B = 𝔽₂`. Unlike `decoupledToyCarrier` (a product ring, not a
domain), this carrier can exercise every `[IsDomain P]`-gated result (batching here, soundness at
S6), keeping INV-2 live for the soundness path. `Fact (Nat.Prime 2)` is mathlib's
`Nat.fact_prime_two`; the bases come from `finrank (ZMod 2) (GaloisField 2 n) = n`. -/
def decoupledFieldCarrier : RingSwitchCarrier (ZMod 2) where
  P := GaloisField 2 2
  E := GaloisField 2 3
  ιP := Fin 2
  ιE := Fin 3
  packBasis := Module.finBasisOfFinrankEq _ _ (GaloisField.finrank (p := 2) (n := 2) (by norm_num))
  openBasis := Module.finBasisOfFinrankEq _ _ (GaloisField.finrank (p := 2) (n := 3) (by norm_num))

/-! ## Sanity / testable deliverables (S3 §5.3) -/

section Sanity

open BatchingStrategy

-- INV-5 bound pins: the stated errors are *definitionally* the papers' bounds
-- (γ-RLC `e/|P|`, [RSG]; eq-fold `κ/|P|`, [BRW26]).
example (P : Type) [CommRing P] [IsDomain P] [Fintype P] (e : ℕ) :
    (gammaPowers P e).error = (e : ℝ≥0) / (Fintype.card P : ℝ≥0) := rfl

example (P : Type) [CommRing P] [IsDomain P] [Fintype P] (κ : ℕ) :
    (eqFold P κ).error = (κ : ℝ≥0) / (Fintype.card P : ℝ≥0) := rfl

-- γ-RLC instantiates over a concrete field (𝔽₁₆) with e = 3 claims,
-- and over a computable-instance field with no `letI` plumbing.
example :
    letI : Fintype (GaloisField 2 4) := Fintype.ofFinite _
    BatchingStrategy (GaloisField 2 4) (Fin 3) :=
  letI : Fintype (GaloisField 2 4) := Fintype.ofFinite _
  gammaPowers _ 3

example : BatchingStrategy (ZMod 3) (Fin 3) := gammaPowers _ 3

-- The S8/Hachi fork stays *statable*: a non-domain ring can state a strategy (it must then
-- supply its own proven `separates`); `[IsDomain]` gates only the proven menu and, later, the
-- S6 domain soundness theorem — the fork lives at the theorem, not the vocabulary.
example : Type 1 := BatchingStrategy (ZMod 6) (Fin 2)

-- Reindexing lands a proven instance at an arbitrary (equiv) claim index — the S6 path onto
-- `car.ιE` (here: eq-fold's `2^2` cube re-indexed as `Fin 4`).
example : BatchingStrategy (ZMod 3) (Fin (2 ^ 2)) :=
  (eqFold (ZMod 3) 2).reindex finFunctionFinEquiv.symm

-- R5 closure: batching is exercised at the *decoupled carrier's own* packing algebra — the
-- `rfl` pin certifies `decoupledFieldCarrier.P` IS `𝔽₄` definitionally (the projection is
-- opaque to instance search, so the instantiations below are typed at `GaloisField 2 2`), so
-- the `[IsDomain P]` layer now has a non-Binius witness (INV-2), not merely a nearby lookalike.
example : decoupledFieldCarrier.P = GaloisField 2 2 := rfl

example :
    letI : Fintype (GaloisField 2 2) := Fintype.ofFinite _
    BatchingStrategy (GaloisField 2 2) (Fin 3) :=
  letI : Fintype (GaloisField 2 2) := Fintype.ofFinite _
  gammaPowers _ 3

-- eq-fold instantiates at the decoupled carrier's packing algebra too (κ = 2, i.e. 4 claims).
example :
    letI : Fintype (GaloisField 2 2) := Fintype.ofFinite _
    BatchingStrategy (GaloisField 2 2) (Fin 2 → Fin 2) :=
  letI : Fintype (GaloisField 2 2) := Fintype.ofFinite _
  eqFold _ 2

-- …and at the projection itself, with the instances landed by definitional transport — the
-- exact plumbing S6 will need at `car.P`.
example :
    letI : IsDomain decoupledFieldCarrier.P := inferInstanceAs (IsDomain (GaloisField 2 2))
    letI : Fintype decoupledFieldCarrier.P :=
      letI : Finite decoupledFieldCarrier.P := inferInstanceAs (Finite (GaloisField 2 2))
      Fintype.ofFinite _
    BatchingStrategy decoupledFieldCarrier.P (Fin 3) :=
  letI : IsDomain decoupledFieldCarrier.P := inferInstanceAs (IsDomain (GaloisField 2 2))
  letI : Fintype decoupledFieldCarrier.P :=
    letI : Finite decoupledFieldCarrier.P := inferInstanceAs (Finite (GaloisField 2 2))
    Fintype.ofFinite _
  gammaPowers _ 3

end Sanity

end RingSwitching.Generic

end

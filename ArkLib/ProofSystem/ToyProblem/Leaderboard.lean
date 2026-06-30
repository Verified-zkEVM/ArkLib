/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

import ArkLib.ProofSystem.ToyProblem.SoundnessBounds
import ArkLib.ProofSystem.ToyProblem.Spec.General
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.FieldTheory.Finite.GaloisField
import CompPoly.Fields.KoalaBear.Basic

/-!
# Proximity-Prize "bits of security" leaderboard (ABF26 §6)

A machine-checked **leaderboard contract** for the soundness of the §6 toy
protocol (Construction 6.2 / its simplified IOR Construction 6.9). The
Ethereum Foundation Proximity Prize (proximityprize.org) asks for the gap
between the *provable* security of small-field hash-based SNARGs and the
*best known attack*; at the KoalaBear-sextic regime (`ρ = 1/2`, `t = 128`)
this is the ≈64-vs-≈116-bit frontier (ABF26 §6.3 Tables 2–5, and the
standalone attack of Fenzi–Sanso, eprint 2025/2197).

## The common quantity: a δ-swept frontier

ABF26's §6.3 analysis is a **sweep over the proximity parameter δ**: every
round-by-round analysis of Construction 6.2 must pick an admissible
`δ ∈ (0, δ_min(C))` (the L6.8/L6.10 range), after which round 1's true error
is `winningSetSoundness enc δ` (Definition 6.11, "exactly") and round 2's is
the spot-check `(1-δ)^t`. The best soundness error provable by *any* such
analysis is therefore

  `bestProvableError p = ⨅ δ ∈ (0, δ_min), (1-δ)^t + winningSetSoundness p.enc δ · (1 - (1-δ)^t)`

(the **convex/union combination** of the two round errors — the L6.6 bound,
`≤` the paper's printed sum, see `protocol62_knowledgeSound`),
and that single scalar is what the two leaderboard sides bound (the paper's
"Knowledge soundness upperbound" / "Soundness lowerbound" parheads, `.tex`
2798–2825 and 2898–2943). Crucially, the two sides may certify their bounds
at **different δ** — the X side optimizes near `δ = 1 - √ρ - η` (Johnson
regime, `.tex` 2799–2823), the Y side attacks near `δ* = 0.468`
(`tab:elias-lowerbound-thresholds`, `.tex` ~2925) — and the `⨅` makes both
legitimate bounds on the *same* quantity:

* `SecurityLowerBound p` — "we can *prove* `≥ bits` bits":
  `bestProvableError p ≤ 2^(-bits)`. Route: `bestProvableError_le` at your
  chosen δ + an upper bound on both terms of the convex combination (the
  `winningSetSoundness` term via the L6.10 bridge
  `winningSetSoundness_le_epsMCA_add`, the spot-check `(1-δ)^t` directly).
* `SecurityUpperBound p` — "no δ-relaxation analysis can prove `> bits` bits":
  `2^(-bits) ≤ bestProvableError p`. Route: for every admissible δ, floor the
  convex combination — which dominates both `(1-δ)^t` and (since
  `winningSetSoundness ≤ 1`) `winningSetSoundness` — via an attack on
  `winningSetSoundness` for large δ (the **proven** hooks
  `epsCA_le_winningSetSoundness` (L6.13) and `listDecoding_le_winningSetSoundness`
  (L6.12)) and the spot-check term `(1-δ)^t` for small δ.
* `securityGap lo hi := hi.bits - lo.bits` — the scalar contestants minimise.
  `SecurityLowerBound.bits_le_of` proves `lo.bits ≤ hi.bits` (so the gap is
  `≥ 0`) by transitivity through the common scalar, axiom-cleanly.

**Honesty note.** `bestProvableError` is what δ-relaxation round-by-round
analyses can certify; the protocol's *true* security may exceed it (a
fundamentally different analysis is outside this contract). The leaderboard
narrows *this* quantity, per ABF26 §6.3.

## The pinned encoding

All Definition-6.11 objects are stated against the **fixed-encoding**
relations `relaxedRelationFor enc` / `winningSetFor enc` (the paper's code
*is* its injective encoding; see `Definitions.lean`). `ToyParams` therefore
carries `enc` (with injectivity) and derives the code as `Set.range enc`.
An earlier revision ran on existential-encoding relations, under which the
linear constraint is reparameterisable and the winning-set supremum collapses
— and the proven L6.12 could not even inhabit `ViolatingInstance`.

The Phase-1 grand-challenge framework (`ProximityGap.GrandChallenges`) feeds
the X side: a tighter `MCALowerWitness` shrinks the `ε_mca` term inside the
L6.10 bridge, which raises the provable lower bound `X`.

## References

* [Arnon, G., Boneh, D., Fenzi, G., *Open Problems in List Decoding and
  Correlated Agreement*][ABF26] (§6.2 Lemmas 6.6/6.8; §6.4 Lemmas 6.10, 6.12,
  6.13; Definition 6.11; §6.3 Tables 2–5).
* [KKH26] (list-size lower bounds backing the §6.3 attack tables) and
  Fenzi–Sanso, eprint 2025/2197 (Construction 4.2 ≈ C6.2; Lemma 4.4 is a
  similar observation to Lemma 6.12, per ABF26 §6.4.1 footnote).
-/

-- Several plumbing lemmas use only a subset of the `ι`/`F` typeclass instances in their
-- types; suppress the noisy `unused...InType` / `unusedSectionVars` warnings file-wide,
-- matching the idiom in `ProximityGap/GrandChallenges.lean`.
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.unusedSectionVars false

namespace ToyProblem

open Code InterleavedCode ListDecodable ProximityGap
open scoped NNReal ENNReal
open Probability

variable {ι F : Type} [Fintype ι] [Field F] [Fintype F] [DecidableEq F]
variable {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module F A]

/-! ## The per-δ soundness scalar (Definition 6.11 reading)

`winningSetSoundness enc δ` is the simplified IOR's actual soundness error at
proximity parameter `δ`: the supremum, over instances `(v, μ₁, μ₂, f₁, f₂)`
that *violate* the relaxed relation `R̃_{C,δ}^2` (fixed encoding `enc`), of
the winning-challenge fraction `|Ω| / |F|`. The violating constraint is
essential — over *all* inputs a valid instance has `Ω = F` (fraction `1`), so
the unrestricted sup is the trivial `1`. -/

/-- An instance of the simplified IOR whose stack `(v, μ₁, μ₂, f₁, f₂)`
violates the relaxed relation `R̃_{C,δ}^2` under the code's fixed encoding
`enc` ([ABF26] Definition 6.3 via `relaxedRelationFor`). This is the index of
the worst-case soundness supremum of Definition 6.11. -/
structure ViolatingInstance {k : ℕ} (enc : (Fin k → F) →ₗ[F] (ι → A)) (δ : ℝ≥0) where
  /-- The linear-constraint vector. -/
  v : Fin k → F
  /-- First constraint value. -/
  μ₁ : F
  /-- Second constraint value. -/
  μ₂ : F
  /-- First input word. -/
  f₁ : ι → A
  /-- Second input word. -/
  f₂ : ι → A
  /-- The instance violates the relaxed two-row relation `R̃_{C,δ}^2`
  (fixed-encoding form). -/
  violates : ¬ relaxedRelationFor (ℓ := 2) enc δ v ![μ₁, μ₂] ![f₁, f₂]

/-- The winning-challenge fraction `|Ω^{f₁,f₂}_{v,μ₁,μ₂}| / |F|` of a
violating instance ([ABF26] Definition 6.11, fixed-encoding `winningSetFor`).
Always in `[0, 1]` (`winningSetFor enc … ⊆ F`). -/
noncomputable def winningSetRatio {k : ℕ} {enc : (Fin k → F) →ₗ[F] (ι → A)} {δ : ℝ≥0}
    (x : ViolatingInstance enc δ) : ℝ≥0 :=
  ((winningSetFor enc δ x.v x.μ₁ x.μ₂ x.f₁ x.f₂).ncard : ℝ≥0) / (Fintype.card F : ℝ≥0)

/-- **Definition 6.11 of [ABF26]** (soundness error of the simplified IOR at
proximity parameter `δ`, with the code's encoding pinned).

The worst-case winning-challenge fraction over violating instances:
`sup_{(v,μ₁,μ₂,f₁,f₂) violating R̃²} |Ω| / |F|`. This is the protocol's
*actual* soundness error after the combination-randomness round — the paper
says the soundness error of Construction 6.9 "is exactly" this quantity. The
leaderboard's common quantity `bestProvableError` sweeps it over δ. -/
noncomputable def winningSetSoundness {k : ℕ} (enc : (Fin k → F) →ₗ[F] (ι → A))
    (δ : ℝ≥0) : ℝ≥0 :=
  ⨆ x : ViolatingInstance enc δ, winningSetRatio x

/-- The winning-challenge fraction never exceeds `1` (`winningSetFor enc … ⊆ F`;
cf. [ABF26] Definition 6.11). -/
theorem winningSetRatio_le_one {k : ℕ} {enc : (Fin k → F) →ₗ[F] (ι → A)} {δ : ℝ≥0}
    (x : ViolatingInstance enc δ) : winningSetRatio x ≤ 1 := by
  haveI : Nonempty F := ⟨0⟩
  have hpos : (0 : ℝ≥0) < (Fintype.card F : ℝ≥0) := by
    exact_mod_cast Fintype.card_pos
  rw [winningSetRatio, div_le_one hpos]
  have hle : (winningSetFor enc δ x.v x.μ₁ x.μ₂ x.f₁ x.f₂).ncard ≤ Fintype.card F := by
    have := Set.ncard_le_ncard (Set.subset_univ
      (winningSetFor enc δ x.v x.μ₁ x.μ₂ x.f₁ x.f₂)) (Set.finite_univ)
    rwa [Set.ncard_univ, Nat.card_eq_fintype_card] at this
  exact_mod_cast hle

/-- The family of winning-challenge fractions is bounded above (by `1`), so
its supremum is well-behaved in the conditionally complete order `ℝ≥0`
(cf. [ABF26] Definition 6.11). -/
theorem bddAbove_winningSetRatio {k : ℕ} (enc : (Fin k → F) →ₗ[F] (ι → A)) (δ : ℝ≥0) :
    BddAbove (Set.range (fun x : ViolatingInstance enc δ ↦ winningSetRatio x)) := by
  refine ⟨1, ?_⟩
  rintro r ⟨x, rfl⟩
  exact winningSetRatio_le_one x

/-- Each violating instance's winning fraction is a lower bound on the
soundness error of [ABF26] Definition 6.11 — the backbone of the attack (Y)
side: an explicit attack witness lower-bounds `winningSetSoundness`. -/
theorem winningSetRatio_le_winningSetSoundness {k : ℕ}
    {enc : (Fin k → F) →ₗ[F] (ι → A)} {δ : ℝ≥0} (x : ViolatingInstance enc δ) :
    winningSetRatio x ≤ winningSetSoundness enc δ :=
  le_ciSup (bddAbove_winningSetRatio enc δ) x

/-! ## The two proven attack hooks (Lemmas 6.13 and 6.12 on the leaderboard) -/

/-- **The correlated-agreement attack lower-bounds the simplified-IOR soundness**
(the §6.4.2 attack chain, end-to-end and machine-checked). For a linear code
`C = range enc` (injective `F`-linear `enc`), the soundness error
`winningSetSoundness enc δ` is at least the correlated agreement error
`ε_ca(C, δ)`. This is **Lemma 6.13 of [ABF26]**
(`simplified_iop_soundness_ca_lb`, fixed-encoding form) packaged as a
`ViolatingInstance` and pushed through `winningSetRatio_le_winningSetSoundness`:
the attack witness's winning fraction `|Ω|/|F| ≥ ε_ca` is a genuine lower bound
on the worst-case soundness.

This is a proven hook for Y-side submissions: a numeric `ε_ca(C, δ) ≥ 2^(-b)`
at an admissible δ floors `winningSetSoundness enc δ`. Axiom-clean (no
`sorryAx`). -/
theorem epsCA_le_winningSetSoundness {k : ℕ} [Nonempty ι] {C : Set (ι → A)} (δ : ℝ≥0)
    (hδpos : (0 : ℝ≥0) < δ) (hδlt : δ < 1)
    (enc : (Fin k → F) →ₗ[F] (ι → A)) (henc_inj : Function.Injective enc)
    (henc_range : Set.range enc = C) :
    epsCA (F := F) (A := A) C δ δ ≤ (winningSetSoundness enc δ : ENNReal) := by
  rcases eq_or_lt_of_le (zero_le (a := epsCA (F := F) (A := A) C δ δ)) with h | hca
  · rw [← h]; exact zero_le
  obtain ⟨v, μ₁, μ₂, f₁, f₂, hviol, hbound⟩ :=
    simplified_iop_soundness_ca_lb C δ hδpos hδlt enc henc_inj henc_range hca
  set x : ViolatingInstance enc δ := ⟨v, μ₁, μ₂, f₁, f₂, hviol⟩ with hx
  have hF0 : (Fintype.card F : ENNReal) ≠ 0 := by simp [Fintype.card_ne_zero]
  have hFt : (Fintype.card F : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top _
  have hWReq : (winningSetRatio x : ENNReal)
      = ((winningSetFor enc δ v μ₁ μ₂ f₁ f₂).ncard : ENNReal)
          / (Fintype.card F : ENNReal) := by
    rw [winningSetRatio, hx, ENNReal.coe_div (by simp [Fintype.card_ne_zero])]
    push_cast; rfl
  have hWR : (winningSetRatio x : ENNReal) ≤ (winningSetSoundness enc δ : ENNReal) := by
    exact_mod_cast winningSetRatio_le_winningSetSoundness x
  refine le_trans ?_ hWR
  rw [hWReq, ENNReal.le_div_iff_mul_le (Or.inl hF0) (Or.inl hFt)]
  exact hbound

/-- **The list-decoding attack lower-bounds the simplified-IOR soundness**
(**Lemma 6.12 of [ABF26]** hosted on the leaderboard; §6.4.1, cf. Fenzi–Sanso
eprint 2025/2197 Lemma 4.4 and the [KKH26]-backed §6.3 tables). Writing
`N := |Λ(C^{≡2}, δ)|`: for a linear code `C = range enc` with `N < |F|`,

  `N / (|F| + 2N)  ≤  winningSetSoundness enc δ`.

Derived from the proven `simplified_iop_soundness_listDecoding_lb` by packaging
its attack instance as a `ViolatingInstance` (the lemma certifies the violation
and `|winningSetFor enc …| ≥ N·|F|/(|F|+2N)`; divide by `|F|`) and pushing it
through `winningSetRatio_le_winningSetSoundness`.

This is the second proven Y-side hook: a numeric list-size lower bound (e.g.
Elias/[KKH26] at the §6.3 parameters) floors `winningSetSoundness enc δ`.
Axiom-clean (no `sorryAx`). -/
theorem listDecoding_le_winningSetSoundness {k : ℕ} [Nonempty ι] {C : Set (ι → A)}
    (δ : ℝ≥0) (hδpos : (0 : ℝ≥0) < δ) (hδlt : δ < 1)
    (enc : (Fin k → F) →ₗ[F] (ι → A)) (henc_inj : Function.Injective enc)
    (henc_range : Set.range enc = C)
    (hF : ((Lambda (interleavedCodeSet (κ := Fin 2) C) (δ : ℝ)).toNat : ℝ)
      < Fintype.card F) :
    ((Lambda (interleavedCodeSet (κ := Fin 2) C) (δ : ℝ)).toNat : ℝ≥0)
        / ((Fintype.card F : ℝ≥0)
            + 2 * ((Lambda (interleavedCodeSet (κ := Fin 2) C) (δ : ℝ)).toNat : ℝ≥0))
      ≤ winningSetSoundness enc δ := by
  obtain ⟨v, μ₁, μ₂, f₁, f₂, hviol, hbound⟩ :=
    simplified_iop_soundness_listDecoding_lb C δ hδpos hδlt enc henc_inj henc_range hF
  rw [ge_iff_le] at hbound
  set N : ℕ := (Lambda (interleavedCodeSet (κ := Fin 2) C) (δ : ℝ)).toNat with hN
  set x : ViolatingInstance enc δ := ⟨v, μ₁, μ₂, f₁, f₂, hviol⟩ with hx
  refine le_trans ?_ (winningSetRatio_le_winningSetSoundness x)
  have hcardF : (0 : ℝ) < (Fintype.card F : ℝ) := by exact_mod_cast Fintype.card_pos
  have hden : (0 : ℝ) < (Fintype.card F : ℝ) + 2 * N := by positivity
  have hkey : (N : ℝ) * Fintype.card F
      ≤ ((winningSetFor enc δ v μ₁ μ₂ f₁ f₂).ncard : ℝ)
          * ((Fintype.card F : ℝ) + 2 * N) := (div_le_iff₀ hden).mp hbound
  have hreal : (N : ℝ) / ((Fintype.card F : ℝ) + 2 * N)
      ≤ ((winningSetFor enc δ v μ₁ μ₂ f₁ f₂).ncard : ℝ) / (Fintype.card F : ℝ) := by
    rw [div_le_div_iff₀ hden hcardF]
    linarith [hkey]
  have hratio : winningSetRatio x
      = ((winningSetFor enc δ v μ₁ μ₂ f₁ f₂).ncard : ℝ≥0) / (Fintype.card F : ℝ≥0) := rfl
  rw [hratio, ← NNReal.coe_le_coe, NNReal.coe_div, NNReal.coe_div, NNReal.coe_add,
    NNReal.coe_mul]
  push_cast
  exact hreal

/-! ## The X-side vehicle (full protocol C6.2; Lemmas 6.6 / 6.8 / 6.10)

`toySoundnessError` is the *exact* error term of
`Spec.General.protocol62_knowledgeSound` (Lemma 6.6, corrected): the
**convex combination** of the spot-check error `(1-δ)^t` and the
combination-randomness error `ε_mca(C,δ) + |Λ(C^{≡2},δ)| / |F|`. The bridge from
`winningSetSoundness` to the latter is the error-bound content of Lemma 6.10. -/

/-- The round-by-round soundness upper bound of **Lemma 6.6 of [ABF26]
(corrected)** (the *full* protocol C6.2) at proximity parameter `δ`: the
**convex combination** `(1-δ)^t + ε₀·(1 - (1-δ)^t)` of the spot-check error
`(1-δ)^t` and the combination-randomness error
`ε₀ = ε_mca(C,δ) + |Λ(C^{≡2},δ)| / |F|`. This is the *exact* error term of
`protocol62_knowledgeSound`. (This convex combination is `≤` the sum
`ε₀ + (1-δ)^t` printed in [ABF26] Lemma 6.6, current `.tex` ~line 2215 — see
`protocol62_knowledgeSound`; tighter than the paper's sum by `ε₀·(1-δ)^t`,
negligible in regime.) The `(Lambda …).toNat` is faithful: `ListDecodable.Lambda_ne_top`. It
is the X-side proof vehicle: an analysis picks an admissible δ and bounds
`bestProvableError` through it (via `winningSetSoundness_le_toySoundnessError`
and `bestProvableError_le`). -/
noncomputable def toySoundnessError (C : Set (ι → A)) (δ : ℝ≥0) (t : ℕ) : ℝ≥0 :=
  (1 - δ) ^ t
    + ((epsMCA (F := F) (A := A) C δ).toNNReal +
        ((Lambda (interleavedCodeSet (κ := Fin 2) C) (δ : ℝ)).toNat : ℝ≥0)
          / (Fintype.card F : ℝ≥0)) * (1 - (1 - δ) ^ t)

/-- **Error-bound content of Lemma 6.10 of [ABF26]** (`.tex` 2627–2634:
Construction 6.9 has knowledge soundness with error `ε_mca(C,δ) + Λ/|F|`).
The Definition-6.11 soundness scalar is at most the L6.10 error term:
`winningSetSoundness enc δ ≤ ε_mca(C,δ) + |Λ(C^{≡2},δ)|/|F|`.
The `(Lambda …).toNat` is faithful: `ListDecodable.Lambda_ne_top`.

This is *only* the error bound; the full knowledge-soundness *game* of L6.10
(extractor, `O(enc + ecor)` extraction recast cost-free) is
`ToyProblem.SimplifiedIOR.simplifiedIOR_knowledgeSound` in
`Spec/SimplifiedIOR.lean` — cross-reference it (an earlier revision mislabeled
this inequality itself as "L6.10"). Paper-proof-owed (ABF26's own §6.4
result). -/
theorem winningSetSoundness_le_epsMCA_add {k : ℕ} [Nonempty ι] {C : Set (ι → A)} (δ : ℝ≥0)
    (hδ : δ ∈ Set.Ioo (0 : ℝ≥0) ((minRelHammingDistCode C : ℝ≥0)))
    (enc : (Fin k → F) →ₗ[F] (ι → A)) (henc_inj : Function.Injective enc)
    (henc_range : Set.range enc = C) :
    winningSetSoundness enc δ
      ≤ (epsMCA (F := F) (A := A) C δ).toNNReal
        + ((Lambda (interleavedCodeSet (κ := Fin 2) C) (δ : ℝ)).toNat : ℝ≥0)
          / (Fintype.card F : ℝ≥0) := by
  -- ABF26-L6.10 error bound: the 1-round (γ) form of the L6.8 γ-round analysis. Each
  -- violating instance's winning fraction `|Ω|/|F|` is exactly the uniform probability of
  -- the γ-transition event, bounded by `ε_mca + |Λ|/|F|` via `gamma_transition_prob_le`.
  classical
  obtain ⟨hδpos, hδlt⟩ := hδ
  -- `epsMCA` is a supremum of probabilities, hence `≤ 1 < ⊤`.
  have hMCAtop : epsMCA (F := F) (A := A) C δ ≠ ⊤ := Spec.epsMCA_ne_top C δ
  -- Coerced bound equals the `ℝ≥0∞` bound produced by `gamma_transition_prob_le`.
  have hε₀coe : (((epsMCA (F := F) (A := A) C δ).toNNReal +
        ((Lambda (interleavedCodeSet (κ := Fin 2) C) (δ : ℝ)).toNat : ℝ≥0)
          / (Fintype.card F : ℝ≥0) : ℝ≥0) : ℝ≥0∞)
      = epsMCA (F := F) (A := A) C δ +
        ((Lambda (interleavedCodeSet (κ := Fin 2) C) (δ : ℝ)).toNat : ℝ≥0∞)
          / (Fintype.card F : ℝ≥0∞) := by
    rw [ENNReal.coe_add, ENNReal.coe_toNNReal hMCAtop,
      ENNReal.coe_div (Nat.cast_ne_zero.mpr Fintype.card_ne_zero),
      ENNReal.coe_natCast, ENNReal.coe_natCast]
  -- Bound the supremum by bounding each violating instance's winning fraction.
  refine ciSup_le' (fun x ↦ ?_)
  obtain ⟨v, μ₁, μ₂, f₁, f₂, hviol⟩ := x
  -- The violating instance has no `R̃²` witness, in the shape `gamma_transition_prob_le` wants.
  have hNoWit : ¬ ∃ M : Fin 2 → (Fin k → F),
      (∀ i : Fin 2, ∑ j, M i j * v j = ![μ₁, μ₂] i) ∧
      ∃ S : Finset ι, (1 - (δ : ℝ)) * Fintype.card ι ≤ S.card ∧
        ∀ i : Fin 2, ∀ j ∈ S, ![f₁, f₂] i j = enc (M i) j := by
    rintro ⟨M, hlin, S, hScard, hagree⟩
    exact hviol ⟨fun i ↦ enc (M i), ⟨M, fun _ ↦ rfl, hlin⟩, S, hScard, hagree⟩
  -- `winningSetFor` membership is exactly the γ-transition event (the `ℓ=1` relaxed relation,
  -- with the codeword witness `Wstar = enc m` eliminated).
  have hWSeq : winningSetFor enc δ v μ₁ μ₂ f₁ f₂ =
      {γ : F | ∃ m : Fin k → F, (∑ j, m j * v j = μ₁ + γ * μ₂) ∧
        ∃ S : Finset ι, (1 - (δ : ℝ)) * Fintype.card ι ≤ S.card ∧
          ∀ j ∈ S, f₁ j + γ • f₂ j = enc m j} := by
    ext γ
    constructor
    · rintro ⟨Wstar, ⟨M, hWeq, hlin⟩, S, hScard, hagree⟩
      refine ⟨M 0, by simpa using hlin 0, S, hScard, fun j hj ↦ ?_⟩
      have h := hagree 0 j hj
      rw [hWeq 0] at h; simpa using h
    · rintro ⟨m, hlin, S, hScard, hagree⟩
      exact ⟨fun _ ↦ enc m, ⟨fun _ ↦ m, fun _ ↦ rfl, fun _ ↦ by simpa using hlin⟩,
        S, hScard, fun i j hj ↦ by simpa using hagree j hj⟩
  -- Push to `ℝ≥0∞`: the winning fraction is the uniform probability of the γ-transition event.
  rw [← ENNReal.coe_le_coe, hε₀coe]
  refine le_trans (le_of_eq ?_)
    (gamma_transition_prob_le C δ enc henc_inj henc_range hδpos hδlt v μ₁ μ₂ f₁ f₂ hNoWit)
  rw [winningSetRatio, prob_uniform_eq_card_filter_div_card, hWSeq,
    Set.ncard_eq_toFinset_card', Set.toFinset_setOf,
    ENNReal.coe_div (Nat.cast_ne_zero.mpr Fintype.card_ne_zero), ENNReal.coe_natCast,
    ENNReal.coe_natCast]

/-- The Definition-6.11 soundness scalar never exceeds `1` (a supremum of
fractions `|Ω|/|F| ≤ 1`). -/
theorem winningSetSoundness_le_one {k : ℕ} (enc : (Fin k → F) →ₗ[F] (ι → A)) (δ : ℝ≥0) :
    winningSetSoundness enc δ ≤ 1 :=
  ciSup_le' (fun x ↦ winningSetRatio_le_one x)

/-- **The simplified-IOR soundness is below the full-protocol RBR bound**
(corollary of the L6.10 bridge `winningSetSoundness_le_epsMCA_add` of [ABF26];
the bridge's `ε_mca + |Λ|/|F|` term is the combination-randomness slot of the
convex `toySoundnessError`). -/
theorem winningSetSoundness_le_toySoundnessError {k : ℕ} [Nonempty ι] {C : Set (ι → A)}
    (δ : ℝ≥0) (t : ℕ)
    (hδ : δ ∈ Set.Ioo (0 : ℝ≥0) ((minRelHammingDistCode C : ℝ≥0)))
    (enc : (Fin k → F) →ₗ[F] (ι → A)) (henc_inj : Function.Injective enc)
    (henc_range : Set.range enc = C) :
    winningSetSoundness enc δ ≤ toySoundnessError (F := F) C δ t := by
  -- `w ≤ ε₀` (bridge) and `w ≤ 1`, so `w = w·(1-a) + w·a ≤ ε₀·(1-a) + 1·a = a + ε₀·(1-a)`
  -- where `a = (1-δ)^t ≤ 1`.
  set w := winningSetSoundness enc δ
  set a : ℝ≥0 := (1 - δ) ^ t with ha
  have ha1 : a ≤ 1 := pow_le_one' tsub_le_self t
  have hbridge := winningSetSoundness_le_epsMCA_add δ hδ enc henc_inj henc_range
  have hw1 := winningSetSoundness_le_one enc δ
  calc w = w * (1 - a) + w * a := by
            rw [← mul_add, tsub_add_cancel_of_le ha1, mul_one]
    _ ≤ ((epsMCA (F := F) (A := A) C δ).toNNReal +
          ((Lambda (interleavedCodeSet (κ := Fin 2) C) (δ : ℝ)).toNat : ℝ≥0)
            / (Fintype.card F : ℝ≥0)) * (1 - a) + 1 * a := by gcongr
    _ = toySoundnessError (F := F) C δ t := by rw [toySoundnessError, one_mul, add_comm]

/-! ## Bits of security -/

/-- Provable security in bits of a soundness error `e`: `-log₂ e`. At `e = 0`
(perfect soundness) `Real.logb 2 0 = 0`, so `bitsOfSecurity 0 = 0`; callers
exhibiting genuine perfect soundness should special-case it. For the prize
regime `e ∈ (0, 1)` so `bitsOfSecurity e > 0`. -/
noncomputable def bitsOfSecurity (e : ℝ≥0∞) : ℝ := -Real.logb 2 e.toReal

/-! ## Parameter record (KoalaBear-sextic regime)

`ToyParams` bundles the ambient field/index, the code's **pinned injective
encoding** (the operational object — the code is `Set.range enc`), and the
plain-data numeric regime (KoalaBear field size `q`, sextic extension, rate
`ρ`, and `s, n, t`). There is deliberately **no δ field**: δ is swept inside
`bestProvableError`, per the §6.3 frontier. Full numeric population — and
swapping the placeholder encoding for the genuine KoalaBear-sextic RS/IRS
encoder — is Phase 5. -/

/-- The KoalaBear-sextic parameter regime plus its code interpretation. The
operational fields `(F, ι, k, enc, enc_injective, t)` feed `bestProvableError`;
the documentary fields `(q, ext, ρ, s, n)` record the §6.3 numeric regime for
Phase 5 and the wiki. All carrier types are pinned to `Type 0`
(`epsMCA`/`Λ` need their code at `Type 0`). -/
structure ToyParams where
  /-- Ambient field (`Type 0`; KoalaBear sextic at Phase 5). -/
  F : Type
  /-- Codeword index type (`Type 0`; `Fin n`). -/
  ι : Type
  /-- Codeword alphabet (`Type 0`; an `F`-module): `A = F` is the scalar `s = 1`
  case (interleaved RS), `A = Fin s → F` the folded case (`s`-folded RS). -/
  A : Type
  [field : Field F]
  [fintypeF : Fintype F]
  [decEqF : DecidableEq F]
  [fintypeι : Fintype ι]
  [nonemptyι : Nonempty ι]
  [addCommGroupA : AddCommGroup A]
  [moduleA : Module F A]
  [fintypeA : Fintype A]
  [decEqA : DecidableEq A]
  /-- Message dimension `k` (gives `winningSetFor`'s `v : Fin k → F`). -/
  k : ℕ
  /-- The code's fixed `F`-linear encoding into the alphabet `A` (the paper's
  "code as the injective map"; the code itself is `ToyParams.code = Set.range enc`). -/
  enc : (Fin k → F) →ₗ[F] (ι → A)
  /-- The encoding is injective (Definition 6.1's "code as injective map"). -/
  enc_injective : Function.Injective enc
  /-- Number of spot-check repetitions `t`. -/
  t : ℕ
  /-- Documentary: field characteristic-prime size `q` (KoalaBear: `2^31 - 2^24 + 1`). -/
  q : ℕ := 2 ^ 31 - 2 ^ 24 + 1
  /-- Documentary: extension degree (KoalaBear sextic: `6`). -/
  ext : ℕ := 6
  /-- Documentary: rate `ρ = k/n` (prize regime `1/2`). -/
  ρ : ℝ≥0 := 1 / 2
  /-- Documentary: interleaving / codeword symbol size `s`. -/
  s : ℕ := 1
  /-- Documentary: intended block length `n` (the intended rate is `ρ = k/n`).
  Need not equal `|ι|` for stand-in parameters. -/
  n : ℕ := 0

attribute [instance] ToyParams.field ToyParams.fintypeF ToyParams.decEqF ToyParams.fintypeι
  ToyParams.nonemptyι ToyParams.addCommGroupA ToyParams.moduleA ToyParams.fintypeA
  ToyParams.decEqA

/-- The interpreted base code at a parameter point: the image of the pinned
encoding ([ABF26] Definition 6.1's code-as-injective-map reading). -/
def ToyParams.code (p : ToyParams) : Set (p.ι → p.A) := Set.range p.enc

/-! ## The leaderboard's common quantity: the δ-swept frontier -/

/-- **The leaderboard's common quantity** ([ABF26] §6.3, the "Knowledge
soundness upperbound" and "Soundness lowerbound" parheads, `.tex` 2798–2825
and 2898–2943): the best soundness error provable by **any** δ-relaxation
round-by-round analysis of Construction 6.2,

  `⨅ δ ∈ (0, δ_min(C)), (1-δ)^t + winningSetSoundness enc δ · (1 - (1-δ)^t)`.

Reading: an analysis must pick an admissible `δ ∈ (0, δ_min(C))` (the
L6.8/L6.10 range); round 1's true error at that δ is `winningSetSoundness enc δ`
(Definition 6.11, "exactly" per the paper), round 2's is the spot-check
`(1-δ)^t`; the analysis's combined error is their **convex/union combination**
`(1-δ)^t + winningSetSoundness·(1 - (1-δ)^t)` (the L6.6 bound, `≤` the paper's
printed sum, see `protocol62_knowledgeSound`), and the best
analysis takes the infimum over δ. The protocol's *true* security may exceed
this quantity (an analysis that is not a δ-relaxation round-by-round argument is
out of scope) — the leaderboard narrows **this** quantity, per §6.3.

X-side submissions bound it from above via `bestProvableError_le` at one
chosen δ; Y-side submissions bound it from below by flooring the convex
combination (which dominates both terms) at *every* admissible δ (attack hooks
`epsCA_le_winningSetSoundness`, `listDecoding_le_winningSetSoundness` for the
`winningSetSoundness` term; the spot-check term `(1-δ)^t` floors it directly).

**Two adopted conventions** (flagged by the 2026-06-10 second adversarial
review):
1. The value lives in `ℝ≥0∞` (complete lattice), so a *degenerate* parameter
   point with an empty admissible range (`δ_min(C) = 0`, e.g. `k = 0`) gives
   `⊤` — the conservative direction: no lower bound is certifiable there,
   and any ceiling is vacuous. (In `ℝ≥0` the `⨅ δ ∈ …` binder collapses to
   `0` via the empty inner infimum — `sInf ∅ = 0` — which made *every* lower
   bound trivially inhabitable; CRITICAL finding C1, fixed.)
2. The round-2 term is floored by `(1-δ)^t` as a **convention**: the paper
   proves the analysis error `≤ (1-δ)^t` (lemma:toy-soundness), while the
   exact per-δ round-2 error is `sup_{Δ > δ} (1-Δ)^t`, marginally smaller
   (one grid step `1/n`; ≈`2^(-14)` bits at `n = 2^21`). Only the round-1
   term carries Definition 6.11's "exactly".
3. The two round errors combine by the **convex/union bound** (L6.6), which is
   `≤` the paper's printed sum; it exceeds the (unsound) `max` only by
   `winningSetSoundness·(1-δ)^t` (≤ `(1-δ)^t`), negligible in regime, so the
   anchors are unaffected. -/
noncomputable def bestProvableError (p : ToyParams) : ℝ≥0∞ :=
  ⨅ δ ∈ Set.Ioo (0 : ℝ≥0) ((minRelHammingDistCode p.code : ℝ≥0)),
    (((1 - δ) ^ p.t + winningSetSoundness p.enc δ * (1 - (1 - δ) ^ p.t) : ℝ≥0) : ℝ≥0∞)

/-- **The X-side entry point** (cf. [ABF26] §6.3): for any admissible
`δ ∈ (0, δ_min(C))`, the δ-swept `bestProvableError` is at most that δ's
analysis error `(1-δ)^t + winningSetSoundness p.enc δ · (1 - (1-δ)^t)` (the
convex/union combination). A provable-security submission picks its δ, bounds
both terms (the `winningSetSoundness` one via the L6.10 bridge
`winningSetSoundness_le_epsMCA_add` + an `ε_mca`/`Λ` analysis, the spot-check
`(1-δ)^t` directly), and concludes through this lemma. Axiom-clean. -/
theorem bestProvableError_le (p : ToyParams) {δ : ℝ≥0}
    (hδ : δ ∈ Set.Ioo (0 : ℝ≥0) ((minRelHammingDistCode p.code : ℝ≥0))) :
    bestProvableError p
      ≤ (((1 - δ) ^ p.t + winningSetSoundness p.enc δ * (1 - (1 - δ) ^ p.t) : ℝ≥0) : ℝ≥0∞) :=
  iInf₂_le δ hδ

/-- **The Y-side entry point** (the infimum-`≥` dual of `bestProvableError_le`,
cf. [ABF26] §6.3–6.4): a number `c` floors the δ-swept `bestProvableError`
whenever it floors the per-δ analysis error `(1-δ)^t + winningSetSoundness · (1 -
(1-δ)^t)` at **every** admissible `δ ∈ (0, δ_min(C))`. An attack (Y) submission
picks, at each δ, whichever attack dominates — the spot-check term `(1-δ)^t` for
small δ, the winning-set attacks (Lemmas 6.12 / 6.13, hooks
`listDecoding_le_winningSetSoundness` / `epsCA_le_winningSetSoundness`) for large
δ — and concludes through this lemma. Axiom-clean (`le_iInf₂`). -/
theorem le_bestProvableError (p : ToyParams) {c : ℝ≥0∞}
    (h : ∀ δ ∈ Set.Ioo (0 : ℝ≥0) ((minRelHammingDistCode p.code : ℝ≥0)),
      c ≤ (((1 - δ) ^ p.t + winningSetSoundness p.enc δ * (1 - (1 - δ) ^ p.t) : ℝ≥0) : ℝ≥0∞)) :
    c ≤ bestProvableError p :=
  le_iInf₂ h

/-! ## The two leaderboard interfaces

Both are stated against the **same** common quantity `bestProvableError p`. A
submission is an *inhabitant*. -/

/-- **Provable security lower bound** at parameter point `p`: a number `bits`
and a proof that the δ-swept analysis frontier is `≤ 2^(-bits)` — i.e. "we
can *prove* at least `bits` bits of security" (cf. [ABF26] §6.3). The intended
route is `bestProvableError_le` at a chosen δ, then `winningSetSoundness_le_`
`toySoundnessError` / `winningSetSoundness_le_epsMCA_add` (Lemmas 6.10 / 6.6 /
6.8) plus numerics. `bits : ℝ` because the security level *is*
`bitsOfSecurity e = -log₂ e`, a real for any soundness error `e ∈ (0,1)`
(almost never an integer); the §6.3 figures the anchors quote are themselves
fractional (the attack is `2^(-116.49)`, the C6.9 MCA branch `≈ 2^(-71.5)`,
the spot-check `(1-δ)^128 ≈ 2^(-64.00)`). -/
structure SecurityLowerBound (p : ToyParams) where
  /-- The provable security level, in bits. -/
  bits : ℝ
  /-- The δ-swept analysis frontier is at most `2^(-bits)`. -/
  proof : bestProvableError p ≤ (↑((2 : ℝ≥0) ^ (-bits)) : ℝ≥0∞)

/-- **Provable security upper bound** at parameter point `p`: a number `bits`
and a proof that the δ-swept analysis frontier is `≥ 2^(-bits)` — i.e. "no
δ-relaxation round-by-round analysis can prove *more* than `bits` bits of
security" (cf. [ABF26] §6.3–6.4). The witness floors the convex combination
(which dominates both terms) at every admissible δ: winning-set attacks
(Lemmas 6.12 / 6.13, hooks
`listDecoding_le_winningSetSoundness` / `epsCA_le_winningSetSoundness`) for
large δ, the spot-check term `(1-δ)^t` for small δ. -/
structure SecurityUpperBound (p : ToyParams) where
  /-- The provable security ceiling, in bits. -/
  bits : ℝ
  /-- The δ-swept analysis frontier is at least `2^(-bits)`. -/
  proof : (↑((2 : ℝ≥0) ^ (-bits)) : ℝ≥0∞) ≤ bestProvableError p

/-! ## The leaderboard metric -/

/-- **The leaderboard metric.** The scalar gap `Y − X` between the best known
attack (`hi`) and the best provable security (`lo`), both bounds on
`bestProvableError` (cf. [ABF26] §6.3 Tables 2–5). Contestants minimise this
— at the KoalaBear-sextic regime it is the `117 − 63.99 = 53.01`-bit honest
frontier (informally "≈116 vs ≈64"). -/
def securityGap {p : ToyParams} (lo : SecurityLowerBound p) (hi : SecurityUpperBound p) : ℝ :=
  hi.bits - lo.bits

/-- **The [ABF26] §6 prize gap is honest** (`lo.bits ≤ hi.bits`, so
`securityGap ≥ 0`). Proved by pure transitivity through the common scalar:
`2^(-hi.bits) ≤ bestProvableError ≤ 2^(-lo.bits)`, and `x ↦ 2^(-x)` is
strictly antitone, so `lo.bits ≤ hi.bits`. No degenerate `error = 0` case
arises: the two `2^(-·)` terms are positive and are chained transitively,
never divided by the error. Axiom-clean. -/
theorem SecurityLowerBound.bits_le_of {p : ToyParams}
    (lo : SecurityLowerBound p) (hi : SecurityUpperBound p) :
    lo.bits ≤ hi.bits := by
  -- `2^(-hi.bits) ≤ bestProvableError ≤ 2^(-lo.bits)` in `ℝ≥0∞`, then drop to `ℝ≥0`.
  have hchain : (2 : ℝ≥0) ^ (-hi.bits) ≤ (2 : ℝ≥0) ^ (-lo.bits) :=
    ENNReal.coe_le_coe.mp (le_trans hi.proof lo.proof)
  -- Cast to `ℝ` and use strict monotonicity of `2^(·)`.
  have hchainR : (2 : ℝ) ^ (-hi.bits) ≤ (2 : ℝ) ^ (-lo.bits) := by
    have := (NNReal.coe_le_coe.mpr hchain)
    rwa [NNReal.coe_rpow, NNReal.coe_rpow, NNReal.coe_ofNat] at this
  have hexp : -hi.bits ≤ -lo.bits :=
    (Real.rpow_le_rpow_left_iff (by norm_num : (1 : ℝ) < 2)).mp hchainR
  linarith

/-- `securityGap` is non-negative (cf. [ABF26] §6.3; the two sides bound the
same scalar). -/
theorem securityGap_nonneg {p : ToyParams}
    (lo : SecurityLowerBound p) (hi : SecurityUpperBound p) :
    0 ≤ securityGap lo hi := by
  have := lo.bits_le_of hi
  simp only [securityGap]; linarith

/-! ### The `bits` interpretation

A `SecurityLowerBound`/`SecurityUpperBound` `bits` field is exactly a bound on
the true bits-of-security `bitsOfSecurity (bestProvableError p)`. Together
these read: `lo.bits ≤ bitsOfSecurity (bestProvableError p) ≤ hi.bits` (when
the error is positive), i.e. the certified provable level sits below the true
frontier level, which sits below the attack ceiling. -/

/-- A provable lower bound's `bits` is at most the true bits-of-security of
the [ABF26] §6.3 frontier (equivalently to `lo.proof`, when the error is
positive). -/
theorem SecurityLowerBound.le_bitsOfSecurity {p : ToyParams} (lo : SecurityLowerBound p)
    (h : 0 < bestProvableError p) : lo.bits ≤ bitsOfSecurity (bestProvableError p) := by
  have htop : bestProvableError p ≠ ⊤ := ne_top_of_le_ne_top ENNReal.coe_ne_top lo.proof
  rw [bitsOfSecurity, le_neg,
    Real.logb_le_iff_le_rpow (by norm_num) (ENNReal.toReal_pos h.ne' htop)]
  have := ENNReal.toReal_mono ENNReal.coe_ne_top lo.proof
  rwa [ENNReal.coe_toReal, NNReal.coe_rpow, NNReal.coe_ofNat] at this

/-- A provable upper bound's `bits` is at least the true bits-of-security of
the [ABF26] §6.3 frontier (equivalently to `hi.proof`, when the error is
positive). -/
theorem SecurityUpperBound.bitsOfSecurity_le {p : ToyParams} (hi : SecurityUpperBound p)
    (h : 0 < bestProvableError p) (htop : bestProvableError p ≠ ⊤) :
    bitsOfSecurity (bestProvableError p) ≤ hi.bits := by
  rw [bitsOfSecurity, neg_le,
    Real.le_logb_iff_rpow_le (by norm_num) (ENNReal.toReal_pos h.ne' htop)]
  have := ENNReal.toReal_mono htop hi.proof
  rwa [ENNReal.coe_toReal, NNReal.coe_rpow, NNReal.coe_ofNat] at this

/-! ## Anchor parameter point and the two current entries

`koalaIRS` fixes the KoalaBear-sextic regime numerics (`q = 2^31 - 2^24 + 1`,
sextic extension, `ρ = 1/2`, `t = 128`). The carrier is now the genuine,
correctly-sized field: `GaloisField KoalaBear.fieldSize 6`, the KoalaBear
*sextic* extension, with `|F| = q^6 ≈ 2^186` (`koalaSextic_card`). This clears
the leaderboard-honesty precondition `|F| ≥ 2^117` — the per-δ soundness error
is a fraction `|Ω|/|F|`, so to even *represent* a value in the target window
`[2^(-117), 2^(-64)]` the field must satisfy `|F| ≥ 2^117`. (Over a tiny field,
`|Ω|/|F|` lives in `{0, 1/2, 1}` and the two anchors would be *jointly*
unsatisfiable.)

The encoder `koalaEnc` is a genuine Reed–Solomon encoder: the degree-`< 2`
evaluation map on `3` distinct points, built from `ReedSolomon.evalOnPoints`
and `Polynomial.degreeLTEquiv`. Its injectivity (`koalaEnc_injective`, proven
sorry-free) is [ABF26] Definition 6.1's "code as the injective map".

The two anchors below remain `sorry`-backed by design (like Phase 1's
`MCALowerWitness.ofJohnsonBCHKS25`): they are the §6.3.1 / §6.4.1 numeric
evaluations, owed at Phase 5. Note that with `koalaEnc` now concrete (not
`opaque`), `bestProvableError koalaIRS` is in principle evaluable — these
anchors are now genuine numeric obligations, not irreducible-by-construction
placeholders. -/

/-- The KoalaBear *sextic* extension field `𝔽_q^6` with `q = 2^31 - 2^24 + 1`
(`KoalaBear.fieldSize`), the genuine §6.3 carrier (`|F| = q^6 ≈ 2^186`). The
`Fact (Nat.Prime KoalaBear.fieldSize)` instance comes from CompPoly. -/
abbrev KoalaSextic := GaloisField KoalaBear.fieldSize 6

/-- Cardinality of the carrier: `|KoalaSextic| = q^6` (`q = KoalaBear.fieldSize`).
This is the `|F| ≈ 2^186 ≥ 2^117` honesty precondition for the anchors and the
`|Ω|/|F|` numerics of Sessions 2–3. Stated for `Nat.card` (instance-free);
convert to `Fintype.card` via `Nat.card_eq_fintype_card` under any `Fintype`
instance. -/
theorem koalaSextic_card : Nat.card KoalaSextic = KoalaBear.fieldSize ^ 6 :=
  GaloisField.card KoalaBear.fieldSize 6 (by norm_num)

/-- The `3`-point Reed–Solomon evaluation domain `{0, 1, 2} ⊆ KoalaSextic`.
Distinctness is injectivity of `Nat.cast` below the characteristic
(`4 ≤ KoalaBear.fieldSize`). The block length `n = |ι| = 4` with message
dimension `k = 2` realises the prize rate `ρ = k/n = 1/2`. -/
noncomputable def koalaDomain : Fin 4 ↪ KoalaSextic where
  toFun i := (i.val : KoalaSextic)
  inj' i j hij := by
    have hfs : (4 : ℕ) ≤ KoalaBear.fieldSize := by norm_num [KoalaBear.fieldSize]
    have hi : (i : ℕ) ∈ Set.Iio KoalaBear.fieldSize := Set.mem_Iio.mpr (i.isLt.trans_le hfs)
    have hj : (j : ℕ) ∈ Set.Iio KoalaBear.fieldSize := Set.mem_Iio.mpr (j.isLt.trans_le hfs)
    exact Fin.val_injective
      (CharP.natCast_injOn_Iio KoalaSextic KoalaBear.fieldSize hi hj hij)

/-- The genuine §6.3 encoder: the degree-`< 2` Reed–Solomon evaluation map on the
`4` points of `koalaDomain` (`k = 2`, `n = |ι| = 4`, rate `ρ = 1/2`), as an
`F`-linear map `(Fin 2 → F) →ₗ (Fin 4 → F)`. Built as
`evalOnPoints ∘ (degreeLTEquiv).symm` so that injectivity reduces to the RS
kernel-triviality lemma. ([ABF26] Definition 6.1's "code as the injective map";
the code itself is `ToyParams.code = Set.range koalaEnc`.) -/
noncomputable def koalaEnc :
    (Fin 2 → KoalaSextic) →ₗ[KoalaSextic] (Fin 4 → KoalaSextic) :=
  (ReedSolomon.evalOnPoints koalaDomain).domRestrict (Polynomial.degreeLT KoalaSextic 2)
    ∘ₗ (Polynomial.degreeLTEquiv KoalaSextic 2).symm.toLinearMap

/-- Injectivity of the genuine KoalaBear-sextic Reed–Solomon encoder
([ABF26] Definition 6.1's "code as the injective map"). The encoder is the
composite of the injective `degreeLTEquiv.symm` and the RS evaluation map
restricted to degree-`< 2` polynomials, which is injective because `2 ≤ 4 = |ι|`
distinct points pin a degree-`< 2` polynomial uniquely
(`ReedSolomon.evalOnPoints_domRestrict_injective`). -/
theorem koalaEnc_injective : Function.Injective koalaEnc := by
  simp only [koalaEnc, LinearMap.coe_comp, LinearEquiv.coe_toLinearMap]
  exact (ReedSolomon.evalOnPoints_domRestrict_injective (n := 2) (by simp)).comp
    (LinearEquiv.injective _)

/-- **The encoder's image is exactly the Reed–Solomon code** `RS[koalaDomain, 2]`.
`koalaEnc = evalOnPoints ∘ (degreeLTEquiv).symm`, and as `(degreeLTEquiv 2).symm`
ranges over all degree-`< 2` polynomials its image under `evalOnPoints` is the
RS code `(degreeLT 2).map (evalOnPoints)`. This identifies `koalaIRS.code` with a
genuine MDS code, unlocking the `minDist`/admissibility numerics below. -/
theorem koalaEnc_range :
    Set.range ⇑koalaEnc = (↑(ReedSolomon.code koalaDomain 2) : Set (Fin 4 → KoalaSextic)) := by
  ext y
  rw [SetLike.mem_coe, ReedSolomon.code, Submodule.mem_map]
  simp only [Set.mem_range]
  constructor
  · rintro ⟨m, rfl⟩
    exact ⟨↑((Polynomial.degreeLTEquiv KoalaSextic 2).symm m), Submodule.coe_mem _, rfl⟩
  · rintro ⟨p, hp, rfl⟩
    refine ⟨Polynomial.degreeLTEquiv KoalaSextic 2 ⟨p, hp⟩, ?_⟩
    simp only [koalaEnc, LinearMap.coe_comp, LinearEquiv.coe_toLinearMap, Function.comp_apply,
      LinearEquiv.symm_apply_apply, LinearMap.domRestrict_apply]

/-- **The spot-check term clears `2^(-65)` at `δ = 3/10`**: `(1 - 3/10)^128 =
(7/10)^128 ≤ 2^(-65)`, reduced to the integer fact `7^128 · 2^65 ≤ 10^128`
(`log₁₀`: `128·0.8451 + 65·0.3010 ≈ 127.74 ≤ 128`). A proven inequality, no float
`#eval`. (The true value is `≈ 2^(-65.87)`; the loose `2^(-65)` ceiling is all the
assembly needs.) -/
theorem koala_spotcheck :
    ((1 : ℝ≥0) - 3 / 10) ^ (128 : ℕ) ≤ (2 : ℝ≥0) ^ (-(65 : ℝ)) := by
  have h710 : (1 : ℝ≥0) - 3 / 10 = 7 / 10 :=
    tsub_eq_of_eq_add (by norm_num)
  rw [h710, ← NNReal.coe_le_coe]
  push_cast [NNReal.coe_rpow]
  rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2),
    show (65 : ℝ) = ((65 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, div_pow, inv_eq_one_div,
    div_le_div_iff₀ (by positivity) (by positivity), one_mul]
  exact_mod_cast (by norm_num : (7 : ℕ) ^ 128 * 2 ^ 65 ≤ 10 ^ 128)

/-- **The spot-check term still clears `2^(-117)` at the crossover `δ* = 117/250 =
0.468`** (the Y-side dual of `koala_spotcheck`): `(1 - δ*)^128 = (133/250)^128 ≥
2^(-117)`, reduced to the integer fact `250^128 ≤ 133^128 · 2^117` (`log₁₀`:
`128·2.39794 = 306.93 ≤ 271.85 + 35.22 = 307.07 = 128·log 133 + 117·log 2`). This
is *tight* — the `≈ 0.14`-decade (`≈ 0.46-bit`) margin is exactly why the attack
ceiling rounds **up** to `bits := 117`, not `116` (a 116-bit floor fails on the
band `(0.46604, 0.468)`; see `listDecodingUpperBoundAttack`). A proven integer
inequality, no float `#eval`. -/
theorem koala_spotcheck_lb :
    (2 : ℝ≥0) ^ (-(117 : ℝ)) ≤ ((133 : ℝ≥0) / 250) ^ (128 : ℕ) := by
  rw [← NNReal.coe_le_coe]
  push_cast [NNReal.coe_rpow]
  rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2),
    show (117 : ℝ) = ((117 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, div_pow, inv_eq_one_div,
    div_le_div_iff₀ (by positivity) (by positivity), one_mul]
  exact_mod_cast (by norm_num : (250 : ℕ) ^ 128 ≤ 133 ^ 128 * 2 ^ 117)

/-- The Proximity-Prize anchor parameter point: the KoalaBear-sextic regime
(`q = 2^31 - 2^24 + 1`, sextic extension, `ρ = 1/2`, `t = 128`). There is no
pinned δ — δ is swept inside `bestProvableError` per the §6.3 frontier (the
X side optimizes near `δ = 1 - √ρ - η`, the Y side attacks at `δ* = 0.468`;
a single shared δ cannot represent the frontier). The carrier is the genuine
`q^6 ≈ 2^186`-element KoalaBear sextic `KoalaSextic` (`koalaSextic_card`), and
`koalaEnc` is the genuine degree-`< 2` Reed–Solomon encoder on `4` points
(`ι = Fin 4`, `k = 2`), so the **realised** rate is `ρ = k/|ι| = 2/4 = 1/2` —
the documentary `n = 4` is now the true block length, not a stand-in fiction.

**Short-length caveat (faithfulness, owed to Sessions 2–3).** §6.3's numerics
are an *asymptotic* `(n → ∞, ρ = 1/2)` analysis, where the admissible window is
`δ ∈ (0, δ_min)` with `δ_min → 1 - ρ = 1/2`. At this concrete `n = 4` point the
code is MDS with relative distance `(n-k+1)/n = 3/4`, so `δ_min = 3/4 > 1/2`:
the realised sweep `(0, 3/4)` is *wider* than the asymptotic `(0, 1/2)`. The X
optimum (`≈ 0.293`) and the Y attack (`δ* = 0.468`) both lie inside `(0, 1/2)`,
so the anchors' optimizing/attack δ are admissible here; but the band
`δ ∈ (0.5, 0.75)` is an artefact of the short length and must be handled
explicitly when discharging the upper anchor (Session 3). The toy point thus
*approximates* but does not asymptotically reproduce §6.3 — by design for a
single concrete parameter point. -/
noncomputable def koalaIRS : ToyParams := by
  haveI : Fintype KoalaSextic := Fintype.ofFinite _
  classical
  exact
    { F := KoalaSextic
      ι := Fin 4
      A := KoalaSextic
      k := 2
      enc := koalaEnc
      enc_injective := koalaEnc_injective
      t := 128
      q := KoalaBear.fieldSize
      ext := 6
      ρ := 1 / 2
      s := 1
      n := 4 }

/-- **The realised anchor code's relative minimum distance is `3/4`** (the MDS
bound for the `[n = 4, k = 2]` Reed–Solomon code): `δ_min(koalaIRS.code) =
minDist / n = (4 - 2 + 1)/4 = 3/4`, via `koalaEnc_range` (the code *is* `RS[4,2]`),
the RS MDS distance `ReedSolomon.minDist_eq'`, and the absolute→relative bridge
`minDist_div_card_eq_minRelHammingDistCode`. This pins the admissible δ-window
`(0, 3/4)` for the §6.3 sweep — in particular `δ = 3/10` (the lower-anchor's
choice) is admissible and lies below the unique-decoding radius `δ_min/2 = 3/8`. -/
theorem koalaIRS_minRelDist : minRelHammingDistCode koalaIRS.code = (3 / 4 : ℚ≥0) := by
  classical
  have hcode : koalaIRS.code = (↑(ReedSolomon.code koalaDomain 2) : Set (Fin 4 → KoalaSextic)) :=
    koalaEnc_range
  have hcard : Fintype.card (Fin 4) = 4 := Fintype.card_fin 4
  have hmin : Code.minDist koalaIRS.code = 3 := by
    have key :
        Code.minDist (↑(ReedSolomon.code koalaDomain 2) : Set (Fin 4 → KoalaSextic)) = 3 := by
      rw [ReedSolomon.minDist_eq' (n := 2) (by rw [hcard]; norm_num)]; simp [Fintype.card_fin]
    rw [hcode]; exact key
  have hbridge := minDist_div_card_eq_minRelHammingDistCode koalaIRS.code
  have hcardι : Fintype.card koalaIRS.ι = 4 := hcard
  rw [hmin, hcardι] at hbridge
  have hQ : ((minRelHammingDistCode koalaIRS.code : ℚ≥0) : ℚ) = ((3 / 4 : ℚ≥0) : ℚ) := by
    rw [← hbridge]; push_cast; norm_num
  exact_mod_cast hQ

/-- **ArkLib provable lower bound (≈64 bits) at the IRS/KoalaBear/`t=128`
point.** Cites **Lemmas 6.10 / 6.6 / 6.8 of [ABF26]** and the §6.3.1
"Knowledge soundness upperbound" analysis (`.tex` 2798–2825,
`tab:interleaved-security-analysis`). As of Session 2 the proof is a **fully
formalized derivation, reduced to a single owed external coding-theory bound**
(it is no longer an opaque `sorry`):

1. **Pick `δ := 3/10`** — admissible: `0 < 3/10 < δ_min = 3/4` (`koalaIRS_minRelDist`,
   the MDS rel-distance of the realised `RS[4,2]` code), and below the
   unique-decoding radius `δ_min/2 = 3/8`. The lower bound is an infimum, so one
   admissible δ suffices (`bestProvableError_le`).
2. **Spot-check term** `(1-δ)^128 = (7/10)^128 ≤ 2^(-65)` — proven sorry-free in
   `koala_spotcheck` (reduced to the integer fact `7^128·2^65 ≤ 10^128`; true
   value `≈ 2^(-65.87)`).
3. **`winningSetSoundness` term** — bounded by the **proven** L6.10 bridge
   `winningSetSoundness_le_epsMCA_add` down to `ε_mca(C,3/10) + |Λ(C^{≡2},3/10)|/|F|`,
   which the single owed external admit caps at `2^(-65)`.
4. The convex combination is then `≤ (7/10)^128 + winningSetSoundness ≤ 2^(-65) +
   2^(-65) = 2^(-64) ≤ 2^(-63.99)`.

**The single owed external bound** (`#print axioms` shows `sorryAx`, from this and
nothing else in the achievable chain — `koalaIRS_minRelDist`, `koala_spotcheck`,
`koalaEnc_range` are all axiom-clean). At the concrete `n = 4` point the Johnson
RS bound is vacuous (its range `δ < 1−√(ρ+1/n)` is empty for `ρ+1/n = 3/4`), so the
governing fact is the **unique-decoding** regime: below `δ_min/2`, ABF26 L4.6
(`Errors.epsMCA_eq_epsCA_below_udr`) gives `ε_mca = ε_ca`, and with `|F| = q^6 ≈
2^186` both `ε_ca(C,3/10)` and `|Λ|/|F|` are `≪ 2^(-65)` (the §6.3 asymptotic figure
is `≈ 2^(-71.5)`). Every such `ε_mca`/`ε_ca`/`Λ` upper bound in ArkLib is a
**by-design external literature admit** (`epsMCA_eq_epsCA_below_udr`,
`CapacityBounds.rs_epsMCA_*`, the list-size bounds — `sorry`-backed from
BCHKS25/ACFY25/KKH26); this anchor inherits exactly that one external dependency,
not an opaque hand-wave. (Closing it requires formalizing the cited coding-theory
results — the prize's own research content — not session-level work.)

**Why `bits := 63.99`, not 64** (2026-06-10 second adversarial review, M1):
the paper itself notes (`.tex` 2817–2819) that `(1/√2 + η)^128 > 2^(-64)`
*strictly* — the tables' `2^(-64.00)` entries are rounding. `bits := 63.99` is the
honest certified anchor; the `δ=3/10` route above certifies `≤ 2^(-64) ≤ 2^(-63.99)`
with margin. -/
noncomputable def irsLowerBoundT128 : SecurityLowerBound koalaIRS where
  bits := 63.99
  proof := by
    -- ABF26-§6.3.1, fully formalized **down to one external coding-theory bound**.
    -- δ := 3/10 (in the §6.3 X-optimum band [0.293, 0.375) and below the MDS
    -- unique-decoding radius δ_min/2 = 3/8). The lower bound is an infimum, so one
    -- admissible δ suffices (`bestProvableError_le`); the convex combination then
    -- splits into the spot-check term `(7/10)^128 ≤ 2^(-65)` (`koala_spotcheck`,
    -- proven) and the `winningSetSoundness` term, bounded by the **proven** L6.10
    -- bridge `winningSetSoundness_le_epsMCA_add` down to `ε_mca + |Λ|/|F| ≤ 2^(-65)`
    -- (the single owed external admit — see below). Sum `≤ 2^(-64) ≤ 2^(-63.99)`.
    -- δ-window admissibility: 0 < 3/10 < δ_min = 3/4 (MDS rel-dist of RS[4,2]).
    have hmin34 : ((minRelHammingDistCode koalaIRS.code : ℚ≥0) : ℝ≥0) = (3 / 4 : ℝ≥0) := by
      rw [koalaIRS_minRelDist]; push_cast; norm_num
    have hδmem : (3 / 10 : ℝ≥0) ∈
        Set.Ioo (0 : ℝ≥0) ((minRelHammingDistCode koalaIRS.code : ℝ≥0)) := by
      rw [Set.mem_Ioo, hmin34]; norm_num
    refine le_trans (bestProvableError_le koalaIRS hδmem) ?_
    rw [ENNReal.coe_le_coe]
    -- The `winningSetSoundness` term, via the proven L6.10 bridge, then the external bound.
    have hW : winningSetSoundness koalaIRS.enc (3 / 10) ≤ (2 : ℝ≥0) ^ (-(65 : ℝ)) := by
      refine le_trans (winningSetSoundness_le_epsMCA_add (C := koalaIRS.code)
        (3 / 10 : ℝ≥0) hδmem koalaIRS.enc koalaIRS.enc_injective rfl) ?_
      -- ★ THE single owed external coding-theory bound at the concrete `n = 4` point:
      --   `ε_mca(C, 3/10) + |Λ(C^{≡2}, 3/10)|/|F| ≤ 2^(-65)`.
      -- Below the MDS unique-decoding radius (`2·δ·n = 2.4 < 3 = δ_min·n`), ABF26 L4.6
      -- gives `ε_mca = ε_ca`, and with `|F| = q^6 ≈ 2^186` both the `ε_ca` and the
      -- `|Λ|/|F|` terms are `≪ 2^(-65)` (the §6.3 figure is `≈ 2^(-71.5)`). Every such
      -- `ε_mca`/`ε_ca`/`Λ` upper bound in ArkLib is a by-design external admit
      -- (`Errors.epsMCA_eq_epsCA_below_udr`, `CapacityBounds.rs_epsMCA_*`, the list-size
      -- bounds — all `sorry`-backed from BCHKS25/ACFY25/KKH26); this anchor inherits
      -- exactly that single external dependency. Phase-5/external-owed.
      sorry
    -- The spot-check term and the `2^(-64) ≤ 2^(-63.99)` headroom.
    have ha : ((1 : ℝ≥0) - 3 / 10) ^ (128 : ℕ) ≤ (2 : ℝ≥0) ^ (-(65 : ℝ)) := koala_spotcheck
    have h1ma : (1 - ((1 : ℝ≥0) - 3 / 10) ^ (128 : ℕ)) ≤ 1 := tsub_le_self
    have hstep : (2 : ℝ≥0) ^ (-(64 : ℝ)) ≤ (2 : ℝ≥0) ^ (-(63.99 : ℝ)) :=
      NNReal.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
    calc (1 - (3 / 10 : ℝ≥0)) ^ koalaIRS.t
            + winningSetSoundness koalaIRS.enc (3 / 10) * (1 - (1 - (3 / 10 : ℝ≥0)) ^ koalaIRS.t)
        ≤ (2 : ℝ≥0) ^ (-(65 : ℝ)) + (2 : ℝ≥0) ^ (-(65 : ℝ)) :=
          add_le_add ha (le_trans (mul_le_of_le_one_right zero_le' h1ma) hW)
      _ = (2 : ℝ≥0) ^ (-(64 : ℝ)) := by
          rw [show (2 : ℝ≥0) ^ (-(65 : ℝ)) + (2 : ℝ≥0) ^ (-(65 : ℝ))
                = (2 : ℝ≥0) ^ (1 : ℝ) * (2 : ℝ≥0) ^ (-(65 : ℝ)) by rw [NNReal.rpow_one]; ring,
            ← NNReal.rpow_add (by norm_num : (2 : ℝ≥0) ≠ 0),
            show (1 : ℝ) + -(65 : ℝ) = -(64 : ℝ) by norm_num]
      _ ≤ (2 : ℝ≥0) ^ (-(63.99 : ℝ)) := hstep

/-- **List-decoding attack upper bound (≈117 bits) at the IRS/KoalaBear/`t=128`
point.** Cites **Lemma 6.12 of [ABF26]** (§6.4.1) with the [KKH26]/Elias list
bounds, cf. Fenzi–Sanso eprint 2025/2197 Lemma 4.4 (the paper's §6.4.1
footnote). The floor over the δ sweep — the convex combination
`(1-δ)^t + winningSetSoundness·(1 - (1-δ)^t)` dominates **both** of:

* for `δ ≤ δ* = 0.468` the spot-check term:
  `(1-δ)^128 ≥ (0.532)^128 ≈ 2^(-116.6) ≥ 2^(-117)`;
* for `δ ∈ [δ*, δ_min)` the L6.12 + Elias attack
  (`listDecoding_le_winningSetSoundness` at the §6.3 numerics) floors the
  `winningSetSoundness` term (and the convex combination dominates it,
  `convex ≥ winningSetSoundness` since `winningSetSoundness ≤ 1`)
  at `≈ 2^(-116.49) ≥ 2^(-117)` (`tab:elias-lowerbound-thresholds`, `.tex`
  ~2925).

**Short-length band (owed to Session 3).** At this concrete `n = 4` MDS point
`δ_min = 3/4` (see `koalaIRS`), so the attack branch must floor
`winningSetSoundness` across the *whole* `[0.468, 0.75)`, not just up to the
asymptotic `1 - ρ = 1/2`. As `δ → 3/4` the spot-check term collapses
(`(1/4)^128 ≈ 2^(-256)`), so on the wide band the `≥ 2^(-117)` bound rests
*entirely* on `winningSetSoundness ≥ 2^(-117)` (plausible — near `δ_min` the
winning sets `Ω` are large, so the ratio is near `1` — but it is a distinct
obligation from the `δ*`-attack the table reports, and is the direct cost of the
short block length). Session 3 must discharge it, not assume the asymptotic
window.

**Why `bits := 117`, not 116** (2026-06-10 second adversarial review, M2): a
*ceiling* must round **up**. The certified sweep floor is the spot/attack
crossing `≈ 2^(-116.6)`, which is `< 2^(-116)`: at `bits := 116` the
inequality `2^(-116) ≤ bestProvableError` fails on the band
`δ ∈ (0.46604, 0.468)` where the convex combination reaches neither `2^(-116)`
(the spot-check term needs `δ ≤ 1 - 2^(-116/128) ≈ 0.46604`; the Elias floor on
the `winningSetSoundness` term only ignites at `δ* = 0.468`, and the convex's
extra mass is `≤ winningSetSoundness` which is unfloored on the band) — and no
Phase-5 sharpening closes that band (the true list size there is exactly what
the Elias bound says it isn't). At `bits := 117` the sweep is covered. The
paper's `2^(-116.49)` is the per-δ*
attack value, not the sweep floor.

**Proof shape (Session 3): a full formalized reduction to owed external list-size
lower bounds** (no longer an opaque `sorry`, mirroring the lower anchor). The
infimum-`≥` goal is reduced by `le_bestProvableError` to a universal floor `∀ δ ∈
(0, 3/4), 2^(-117) ≤ (1-δ)^128 + winningSetSoundness · (1-(1-δ)^128)`, split at
the crossover `δ* = 117/250`:

1. **Small-δ half `δ ≤ δ*` — SORRY-FREE.** The convex combination dominates its
   spot-check term `(1-δ)^128`, which is `≥ (133/250)^128 ≥ 2^(-117)` by
   monotonicity (`tsub_le_tsub_left`, `gcongr`) and the proven integer inequality
   `koala_spotcheck_lb`. This is the clean, achievable half.
2. **Large-δ half `δ ∈ (δ*, 3/4)` — reduced to two owed external bounds.** The
   convex combination dominates `winningSetSoundness` (`w ≤ 1`, proven), which the
   **proven** L6.12 hook `listDecoding_le_winningSetSoundness` floors at
   `N/(|F| + 2N)`, `N := |Λ(C^{≡2}, δ)|`. Reaching `2^(-117)` then needs (i) the
   side condition `N < |F|` (true: list size below field size `|F| = q^6 ≈
   2^186`), and (ii) the numeric `2^(-117) ≤ N/(|F|+2N)`, i.e. `N ≳ 2^69`. Both
   are **owed external coding-theory lower bounds** on the interleaved list size:
   on `[δ*, δ_cross ≈ 0.4695)` the Elias/[KKH26] table
   (`tab:elias-lowerbound-thresholds`, `N ≈ 2^{186-116.49}`); on the short-length
   band `[δ_cross, 3/4)` — where the spot-check has collapsed and the table is out
   of range — the near-`δ_min` list-size blow-up (`|Λ| → ∞` as `δ → δ_min`,
   cf. 2025/2197 Lemma 4.4). No proven `Lambda` lower bound exists in ArkLib
   (`ListDecodability.lean` has only `Lambda_le_*` upper bounds), so this is
   irreducibly external — exactly the status of the lower anchor's `ε_mca`
   ceiling. **Axiom-clean is infeasible by design** (it is the prize's own
   coding-theory content); the reduction is full down to these named admits. -/
noncomputable def listDecodingUpperBoundAttack : SecurityUpperBound koalaIRS where
  bits := 117
  proof := by
    -- ABF26 §6.4.1, fully formalized **down to owed external list-size bounds**.
    -- `le_bestProvableError` reduces to a per-δ floor over the whole window
    -- `(0, δ_min = 3/4)` (MDS rel-dist of RS[4,2], `koalaIRS_minRelDist`).
    refine le_bestProvableError koalaIRS (fun δ hδ => ?_)
    have hmin34 : ((minRelHammingDistCode koalaIRS.code : ℚ≥0) : ℝ≥0) = (3 / 4 : ℝ≥0) := by
      rw [koalaIRS_minRelDist]; push_cast; norm_num
    rw [Set.mem_Ioo, hmin34] at hδ
    obtain ⟨hδpos, hδ34⟩ := hδ
    rw [ENNReal.coe_le_coe]
    have ht : koalaIRS.t = 128 := rfl
    rw [ht]
    -- Band split at the spot/attack crossover `δ* = 117/250 = 0.468`.
    rcases le_or_gt δ (117 / 250 : ℝ≥0) with hsmall | hlarge
    · -- Small-δ half: the convex combination dominates `(1-δ)^128`, which clears
      -- `2^(-117)` by `koala_spotcheck_lb` and monotonicity. SORRY-FREE.
      refine le_trans ?_ (le_add_of_nonneg_right zero_le')
      have h133 : (133 / 250 : ℝ≥0) ≤ 1 - δ := by
        apply le_tsub_of_add_le_right
        calc (133 / 250 : ℝ≥0) + δ ≤ 133 / 250 + 117 / 250 := by gcongr
          _ = 1 := by norm_num
      exact le_trans koala_spotcheck_lb (by gcongr)
    · -- Large-δ half: the convex combination dominates `winningSetSoundness`
      -- (`w ≤ 1`); floor `w` via the PROVEN L6.12 hook + owed external list size.
      have ha1 : (1 - δ : ℝ≥0) ^ (128 : ℕ) ≤ 1 := pow_le_one' tsub_le_self _
      have hw1 : winningSetSoundness koalaIRS.enc δ ≤ 1 :=
        winningSetSoundness_le_one koalaIRS.enc δ
      have hconvex : winningSetSoundness koalaIRS.enc δ
          ≤ (1 - δ) ^ (128 : ℕ)
            + winningSetSoundness koalaIRS.enc δ * (1 - (1 - δ) ^ (128 : ℕ)) := by
        have hwa : winningSetSoundness koalaIRS.enc δ * (1 - δ) ^ (128 : ℕ)
            ≤ (1 - δ) ^ (128 : ℕ) := mul_le_of_le_one_left zero_le' hw1
        calc winningSetSoundness koalaIRS.enc δ
            = winningSetSoundness koalaIRS.enc δ * (1 - (1 - δ) ^ (128 : ℕ))
                + winningSetSoundness koalaIRS.enc δ * (1 - δ) ^ (128 : ℕ) := by
              rw [← mul_add, tsub_add_cancel_of_le ha1, mul_one]
          _ ≤ winningSetSoundness koalaIRS.enc δ * (1 - (1 - δ) ^ (128 : ℕ))
                + (1 - δ) ^ (128 : ℕ) := by gcongr
          _ = (1 - δ) ^ (128 : ℕ)
                + winningSetSoundness koalaIRS.enc δ * (1 - (1 - δ) ^ (128 : ℕ)) := add_comm _ _
      refine le_trans ?_ hconvex
      have hδlt1 : δ < 1 := lt_trans hδ34 (by norm_num)
      -- ★ Owed external bound (i): the interleaved list size is below the field
      -- size `|F| = q^6 ≈ 2^186` (true in regime; no proven `Lambda` upper bound
      -- in ArkLib bridges to the `q^6` numeric — owed external coding-theory).
      have hF : ((Lambda (interleavedCodeSet (κ := Fin 2) koalaIRS.code) (δ : ℝ)).toNat : ℝ)
          < Fintype.card koalaIRS.F := by
        sorry
      -- The PROVEN L6.12 hook floors `winningSetSoundness` at `N/(|F|+2N)`.
      refine le_trans ?_ (listDecoding_le_winningSetSoundness (C := koalaIRS.code) δ hδpos hδlt1
        koalaIRS.enc koalaIRS.enc_injective rfl hF)
      -- ★ Owed external bound (ii): the interleaved list size lower bound
      -- `N/(|F|+2N) ≥ 2^(-117)` (`N ≳ 2^69`). On `[δ*, δ_cross)` this is the
      -- Elias/[KKH26] table (`≈ 2^{186-116.49}`); on the short-length band
      -- `[δ_cross, 3/4)` it is the near-`δ_min` list-size blow-up (2025/2197 L4.4).
      -- No proven `Lambda` lower bound exists in ArkLib — irreducibly external,
      -- exactly as the lower anchor's `ε_mca` ceiling. Phase-5/external-owed.
      sorry

/-- **The current leaderboard frontier.** At the KoalaBear-sextic anchor the
honest certified anchors are `63.99` provable bits and a `117`-bit attack
ceiling, so the gap the prize asks contestants to close is
`117 − 63.99 = 53.01` bits (the paper's informal "≈116 − 64 = 52" rounds both
sides toward each other; see [ABF26] §6.3 Tables 2–5 and the anchor
docstrings for the honest-rounding analysis). The value is a pure arithmetic
readoff of the two `bits` fields — it does not depend on the anchors' owed §6
*proofs* being correct (though, naming the anchor defs, this lemma inherits
their tagged `sorry`; the metric lemma `bits_le_of` is the anchor-independent,
axiom-clean guarantee). -/
theorem securityGap_koalaIRS_anchors :
    securityGap irsLowerBoundT128 listDecodingUpperBoundAttack = 53.01 := by
  simp only [securityGap, irsLowerBoundT128, listDecodingUpperBoundAttack]
  norm_num

end ToyProblem

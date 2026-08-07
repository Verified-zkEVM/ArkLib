/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

import ArkLib.Data.CodingTheory.Basic.Distance

/-!
# Erasure correction for codes over a finite alphabet

A generic erasure-correction predicate `SupportsErasureCorrection C`
asserting that a deterministic algorithm exists that recovers any codeword
`u ∈ C` from a partial observation `f : ι → Option F` with strictly fewer
than `δ_min(C) · |ι|` erasures, and returns `⊥` otherwise.

`additive_code_supports_erasure_correction_grs12` (**existence half of Lemma 6.5
of [ABF26]**, citing [GuruswamiRS12]) proves that *every* code satisfies the
predicate: with fewer than `minDist C` erasures the consistent codeword is unique
(`eq_of_consistent_with_erased`, a Hamming-distance pigeonhole), so a
classical corrector exists.

Lives in `Data/CodingTheory/` rather than at the protocol layer (where the
ABF26 toy problem originally introduced it) because the predicate is generic
across proof systems — any reduction whose extractor erasure-decodes its
oracles consumes the same shape.

## References

The predicate is paper-tagged to ABF26 D6.4 (Arnon-Boneh-Fenzi 2026, §6.2);
the "every additive code can be erasure decoded in polynomial time" lemma is
L6.5 in the same paper (citing GRS12 = Guruswami-Rudra-Sudan, *Essential
Coding Theory*).
-/

namespace CodingTheory

open Code

variable {ι F : Type*} [Fintype ι]

/-- **ABF26 Definition 6.4** (erasure-correction predicate).

A code `C ⊆ (ι → F)` supports **erasure correction** if there exists a
deterministic algorithm `E_C` that, on any input `f : ι → Option F`:

  (i)  if `f` has strictly fewer than `δ_min(C) · |ι|` erasures and
       there exists a (necessarily unique) codeword `u ∈ C` agreeing
       with `f` off the erasures, then `E_C(f) = some u`;
  (ii) otherwise `E_C(f) = none`.

Clause (ii) — easy to miss in a quick port from the paper — is what
makes the predicate non-vacuous: without it,
`E := fun _ ↦ some <arbitrary>` satisfies the recovery clause for any
`f` whose preconditions fail, hollowing the definition out.

The paper additionally tracks the corrector's running time (`ecor`); ArkLib's
extractors are uniformly cost-free (unclocked), so no cost parameter is
carried here — see `additive_code_supports_erasure_correction_grs12`. -/
def SupportsErasureCorrection [DecidableEq F]
    (C : Set (ι → F)) : Prop :=
  ∃ E : (ι → Option F) → Option (ι → F),
    ∀ (f : ι → Option F),
      -- (i) recovery clause
      (∀ u ∈ C, (∀ i, f i = some (u i) ∨ f i = none) →
        ((Finset.univ.filter (fun i ↦ f i = none)).card < Code.minDist C →
          E f = some u)) ∧
      -- (ii) failure clause: ⊥ unless both small-erasures AND a witness exist
      (¬ (∃ u ∈ C, (∀ i, f i = some (u i) ∨ f i = none) ∧
            (Finset.univ.filter (fun i ↦ f i = none)).card < Code.minDist C) →
        E f = none)

/-- **Uniqueness pigeonhole for erasure decoding (ABF26 L6.5 core).** Two
codewords consistent with the same partially-erased word `f`, with strictly
fewer than `minDist C` erasures, are equal: they can disagree only on erased
coordinates, so their Hamming distance is below the code's minimum distance. -/
theorem eq_of_consistent_with_erased [DecidableEq F] {C : Set (ι → F)}
    {f : ι → Option F} {u v : ι → F} (hu : u ∈ C) (hv : v ∈ C)
    (hfu : ∀ i, f i = some (u i) ∨ f i = none)
    (hfv : ∀ i, f i = some (v i) ∨ f i = none)
    (hcard : (Finset.univ.filter (fun i ↦ f i = none)).card < Code.minDist C) :
    u = v := by
  by_contra hne
  -- `u` and `v` agree wherever `f` is not erased.
  have hsub : disagreementCols u v ⊆ Finset.univ.filter (fun i ↦ f i = none) := by
    intro i hi
    rw [mem_disagreementCols] at hi
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    rcases hfu i with h1 | h1
    · rcases hfv i with h2 | h2
      · exact absurd (Option.some.inj (h1.symm.trans h2)) hi
      · exact h2
    · exact h1
  have hdist : Δ₀(u, v) ≤ (Finset.univ.filter (fun i ↦ f i = none)).card := by
    rw [hammingDist_eq_disagreementCols_card]
    exact Finset.card_le_card hsub
  -- but distinct codewords are at distance ≥ `minDist C`.
  have hmin : Code.minDist C ≤ Δ₀(u, v) :=
    Nat.sInf_le ⟨u, hu, v, hv, hne, rfl⟩
  omega

/-- **Existence half of ABF26 Lemma 6.5** (`lemma:efficient-erasure-correction`,
[GuruswamiRS12]): a corrector witnessing `CodingTheory.SupportsErasureCorrection C`
*exists*. We formalize only this existence claim; it holds for an arbitrary code
`C` (additivity of `C : F^k → (F^s)^n` is not needed for existence).

The corrector is defined classically: if a codeword of `C` consistent with the
non-erased positions exists (necessarily unique below `minDist C` erasures, by
`eq_of_consistent_with_erased`), return it; otherwise return `none`.

**Scope caveat — this theorem does NOT capture the cited [GRS12] content.** The
substance of the paper's citation is the *algorithmic* claim that an `F`-additive
code is erasure-corrected in `O((s · n)^3)` field operations (Gaussian elimination
on the parity-check matrix). That polynomial-time bound is out of ArkLib's
cost-free model — extractors are uniformly unclocked across the library — so it is
deliberately not formalized here, and the existence statement below requires
nothing from [GRS12]. -/
theorem additive_code_supports_erasure_correction_grs12 [DecidableEq F]
    (C : Set (ι → F)) : SupportsErasureCorrection C := by
  classical
  refine ⟨fun f ↦
    if h : ∃ u ∈ C, (∀ i, f i = some (u i) ∨ f i = none) ∧
        (Finset.univ.filter (fun i ↦ f i = none)).card < Code.minDist C
    then some h.choose else none, fun f ↦ ⟨?_, ?_⟩⟩
  · -- (i) recovery: the classical witness coincides with `u` by uniqueness.
    intro u hu hfu hcard
    have h : ∃ u ∈ C, (∀ i, f i = some (u i) ∨ f i = none) ∧
        (Finset.univ.filter (fun i ↦ f i = none)).card < Code.minDist C :=
      ⟨u, hu, hfu, hcard⟩
    dsimp only
    rw [dif_pos h]
    obtain ⟨hmem, hagree, _⟩ := h.choose_spec
    exact congrArg some (eq_of_consistent_with_erased hmem hu hagree hfu hcard)
  · -- (ii) failure clause: the guard is exactly the negated hypothesis.
    intro hno
    dsimp only
    rw [dif_neg hno]

end CodingTheory

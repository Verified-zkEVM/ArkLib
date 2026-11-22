/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.ToMathlib.Fintype.CardEmbedding
public import VCVio.OracleComp.Constructions.SampleableType.Measure

/-!
# Uniform sampling helpers

This file supplies opt-in uniform samplers for finite subtypes.  The instances are scoped because
many concrete types already have executable `SampleableType` instances, whose implementation
should remain canonical.  Opening `ProbabilityTheory` enables the noncomputable enumeration
fallback for a nonempty predicate subtype or finite-set subtype.

`prEvent_uniformSample_finsetCard_eq_embedding` compares two ways of drawing `n` distinct points of
a finite type: a uniform `n`-element set, and a uniform embedding `Fin n ↪ α` (an ordered tuple of
distinct points). An event that depends only on the drawn set has the same probability under both,
so a sample of ordered distinct points, as in [AGL24], may replace a uniform `n`-element set.
`prEvent_uniformSample_finsetCard_eq_card_embedding` states the probability under a uniform
`n`-element set as the fraction of embeddings whose image satisfies the event, which needs no
sampler for embeddings.

## References

* [Alrabiah, O., Guruswami, V., and Li, R., *Randomly punctured Reed-Solomon codes achieve
    list-decoding capacity over linear-sized fields*][AGL24]
-/

@[expose] public section

namespace ProbabilityTheory

/-- A nonempty subtype of a finite type can be sampled uniformly by enumeration.

This is a low-priority scoped fallback so an executable `FinEnum`-based sampler wins whenever one
is available. -/
noncomputable scoped instance (priority := 50) instSampleableTypeSubtype
    {α : Type} [Fintype α] (p : α → Prop) [Nonempty {x // p x}] :
    SampleableType {x // p x} := by
  classical
  exact SampleableType.subtype α p

/-- A nonempty finite set can be sampled uniformly, even when its ambient type is infinite. -/
noncomputable scoped instance (priority := 100) instSampleableTypeFinsetCoe
    {α : Type} (U : Finset α) [Nonempty ↥U] : SampleableType ↥U := by
  let x : ↥U := Classical.choice (inferInstance : Nonempty ↥U)
  exact SampleableType.finsetCoe U ⟨x, x.property⟩

open Finset in
/-- A uniform `n`-element subset of a finite type satisfies an event with probability equal to the
fraction of embeddings `f : Fin n ↪ α` whose image `univ.map f` satisfies it. Every `n`-element set
is the image of exactly `n !` embeddings (`Fintype.card_filter_embedding_map_univ_eq_factorial`).
Unlike `prEvent_uniformSample_finsetCard_eq_embedding`, this needs no sampler for embeddings. -/
theorem prEvent_uniformSample_finsetCard_eq_card_embedding {α : Type} [Fintype α] {n : ℕ}
    [SampleableType {S : Finset α // #S = n}]
    (P : Finset α → Prop) [DecidablePred P] :
    Pr{let S ← $ᵗ {S : Finset α // #S = n}}[P S] =
      (#{f : Fin n ↪ α | P (univ.map f)} : ENNReal) / Fintype.card (Fin n ↪ α) := by
  classical
  have hcard := Fintype.card_filter_embedding_map_univ (α := α) n fun _ ↦ True
  simp only [filter_true, card_univ] at hcard
  rw [SampleableType.prEvent_uniformSample, Fintype.card_filter_embedding_map_univ n P, hcard,
    Nat.cast_mul, Nat.cast_mul, ENNReal.mul_div_mul_left _ _
      (by exact_mod_cast n.factorial_ne_zero) (ENNReal.natCast_ne_top _)]

open Finset in
/-- A uniform `n`-element subset of a finite type satisfies an event with the same probability as
the image of a uniform embedding `Fin n ↪ α`. Every `n`-element set is the image of exactly `n !`
embeddings (`Fintype.card_filter_embedding_map_univ_eq_factorial`), so the image of a uniform
embedding is a uniform `n`-element set. The statement holds for any samplers of the two types. -/
theorem prEvent_uniformSample_finsetCard_eq_embedding {α : Type} [Finite α] {n : ℕ}
    [SampleableType {S : Finset α // #S = n}] [SampleableType (Fin n ↪ α)]
    (P : Finset α → Prop) :
    Pr{let S ← $ᵗ {S : Finset α // #S = n}}[P S] =
      Pr{let f ← $ᵗ (Fin n ↪ α)}[P (univ.map f)] := by
  classical
  have := Fintype.ofFinite α
  rw [prEvent_uniformSample_finsetCard_eq_card_embedding, SampleableType.prEvent_uniformSample]

end ProbabilityTheory

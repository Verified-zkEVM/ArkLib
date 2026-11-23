/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Katerina Hristova, František Silváši, Julian Sutherland,
         Ilia Vlasov, Chung Thai Nguyen
-/
module

public import ArkLib.Data.CodingTheory.InterleavedCode
public import ArkLib.Data.Probability.Uniform

/-!
# Proximity gap fundamental definitions

Define the fundamental definitions for proximity gap properties of generic codes and
module codes over (scalar) rings.

## Main Definitions

### Proximity Gap Definitions
- `proximityMeasure`: Counts vectors close to linear combinations with code `C`
- `proximityGap`: Proximity gap property at distance `d` with cardinality bound
- `δ_ε_proximityGap`: Generic `(δ, ε)`-proximity gap for any collection of sets

### Correlated Agreement Definitions
- `jointAgreement`: Words collectively agree with code `C` on the same coordinate set
- `jointAgreement_iff_jointProximity`: Equivalence between agreement and proximity formulations
- `δ_ε_correlatedAgreementAffineLines`: Correlated agreement for affine lines (2 words)
- `δ_ε_proximityGap_of_δ_ε_correlatedAgreementAffineLines`: Correlated agreement for affine lines
  gives the proximity gap for affine lines (the proximity gap of Definition 1.1 in [BCIKS20])
- `δ_ε_correlatedAgreementCurves`: Correlated agreement for parametrised curves (k words)
- `δ_ε_correlatedAgreementAffineSpaces`: Correlated agreement for affine subspaces (k+1 words)

## TODOs
- weighted correlated agreement
- generalize the CA definitions using proximity generator?

(Mutual correlated agreement lives in `ProximityGenerators.lean` (`IsMCA`/`IsMCAGenerator`/
`mcaError`, module-alphabet general) with preservation lemmas in `MCAGenerator.lean`,
`AffineGenerator.lean` and `TensorGenerator.lean`.)

## References

- [BCIKS20] Eli Ben-Sasson, Dan Carmon, Yuval Ishai, Swastik Kopparty, and Shubhangi Saraf.
  Proximity gaps for Reed–Solomon codes. In 2020 IEEE 61st Annual Symposium on Foundations of
  Computer Science (FOCS), 2020. Full paper: https://eprint.iacr.org/2020/654, version 20210703:203025.

- [DG25] Benjamin E. Diamond and Angus Gruen. “Proximity Gaps in Interleaved Codes”. In: IACR
  Communications in Cryptology 1.4 (Jan. 13, 2025). issn: 3006-5496. doi: 10.62056/a0ljbkrz.

-/

@[expose] public section

namespace ProximityGap

open NNReal Finset Function Code Affine
open scoped ProbabilityTheory BigOperators LinearCode Affine

universe u v w k l

section CoreSecurityDefinitions

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {κ : Type k} {ι : Type l} [Fintype κ] [Fintype ι] [Nonempty ι]
-- κ => row indices, ι => column indices
variable {F : Type v} [Ring F] [Fintype F]
-- variable {M : Type} [Fintype M] -- Message space type
variable {A : Type w} [Fintype A] [DecidableEq A] [AddCommMonoid A] [Module F A] -- Alphabet type
variable (C : Set (ι → A))

/-- The proximity measure of two vectors `u` and `v` from a code `C` at distance `d` is the number
  of vectors at distance at most `d` from the linear combination of `u` and `v` with coefficients
  `r` in `F`. -/
noncomputable def proximityMeasure (u v : Word A ι) (d : ℕ) : ℕ :=
  Fintype.card {r : F | Δ₀(r • u + (1 - r) • v, C) ≤ d}

/-- A code `C` exhibits proximity gap at distance `d` and cardinality bound `bound` if for every
  pair of vectors `u` and `v`, whenever the proximity measure for `C u v d` is greater than
  `bound`, then the distance of `[u | v]` from the interleaved code `C ^⊗ 2` is at most `d`. -/
def proximityGap (d : ℕ) (bound : ℕ) : Prop :=
  ∀ u v : Word (A := A) (ι := ι), (proximityMeasure (F := F) C u v d > bound)
    →
    letI : Fintype (C ^⋈ (Fin 2)) := interleavedCodeSet_fintype (C := C)
    (Δ₀(u ⋈₂ v, C ^⋈ (Fin 2)) ≤ d)

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
  {F : Type} [Ring F] [Fintype F] [SampleableType F]
  {k : ℕ}

/-- Definition 1.1 in [BCIKS20].

Let `P` be a set `P` and `C` a collection of sets. We say that `C` displays a
`(δ, ε)`-proximity gap with respect to `P` and the relative Hamming distance measure
if for every `S ∈ C` exactly one of the following holds:

1. The probability that a randomly sampled element `s` from `S` is `δ`-close to `P` is `1`.
2. The probability that a randomly sampled element `s` from `S` is `δ`-close to `P` is at most
`ε`.

We call `δ` the proximity parameter and `ε` the error parameter. -/
noncomputable def δ_ε_proximityGap {α : Type} [DecidableEq α]
  (P : Finset (ι → α)) (C : Set (Finset (ι → α))) (δ ε : ℝ≥0) : Prop :=
  ∀ S ∈ C, ∀ [Nonempty S],
  Xor
  ( Pr{let x ← $ᵗ S}[δᵣ(x.val, P) ≤ δ] = 1 )
  ( Pr{let x ← $ᵗ S}[δᵣ(x.val, P) ≤ δ] ≤ ε )

/-- Definition: `(δ, ε)`-correlated agreement for affine lines.
For every pair of words `u₀, u₁`, if the probability that a random affine line `u₀ + z • u₁` is
`δ`-close to `C` exceeds `ε`, then `u₀` and `u₁` have correlated agreement with `C`.
`δ_ε_proximityGap_of_δ_ε_correlatedAgreementAffineLines` derives the proximity gap for affine
lines from it. -/
noncomputable def δ_ε_correlatedAgreementAffineLines [Module F A]
    (C : Set (ι → A)) (δ ε : ℝ≥0) : Prop :=
  ∀ (u : WordStack (A := A) (κ := Fin 2) (ι := ι)),
    Pr{let z ← $ᵗ F}[δᵣ(u 0 + z • u 1, C) ≤ δ] > ε →
    jointAgreement (F := A) (κ := Fin 2) (ι := ι) (C := C) (W := u) (δ := δ)

omit [DecidableEq ι] [Fintype A] [Fintype F] in
/-- Under `(δ, ε)`-correlated agreement for affine lines, if a random point of the line
`u₀ + z • u₁` is `δ`-close to `C` with probability exceeding `ε`, then every point of the line is
`δ`-close to `C`. -/
private theorem line_close_of_δ_ε_correlatedAgreementAffineLines [Module F A]
    {C : Set (ι → A)} {δ ε : ℝ≥0}
    (hCA : δ_ε_correlatedAgreementAffineLines (F := F) C δ ε)
    (u : WordStack (A := A) (κ := Fin 2) (ι := ι))
    (hu : Pr{let z ← $ᵗ F}[δᵣ(u 0 + z • u 1, C) ≤ δ] > ε) (c : F) :
    δᵣ(u 0 + c • u 1, C) ≤ δ := by
  have hshift := SampleableType.prEvent_uniformSample_equiv (Equiv.addLeft c)
    (fun z : F => δᵣ(u 0 + z • u 1, C) ≤ δ)
  simp only [Equiv.coe_addLeft, add_smul, ← add_assoc] at hshift
  refine (hCA (finMapTwoWords (u 0 + c • u 1) (u 1)) ?_).relDistFromCode_le (0 : Fin 2)
  change Pr{let z ← $ᵗ F}[δᵣ(u 0 + c • u 1 + z • u 1, C) ≤ δ] > ε
  rwa [hshift]

section AffineLinesProximityGap

-- `δ_ε_proximityGap` needs `A : Type` with `[Nonempty A]`; the sampling bridge takes `[Field F]`.
variable {F : Type} [Field F] [Fintype F] [SampleableType F]
variable {A : Type} [DecidableEq A] [Nonempty A] [AddCommGroup A] [Module F A]

omit [DecidableEq ι] [Nonempty ι] [Nonempty A] in
/-- A uniform point of the affine line `{u₀ + z • u₁ | z ∈ F}` is distributed as `u₀ + z • u₁`
for a uniform parameter `z`. -/
private theorem prEvent_affineLine_image_eq (u : WordStack (A := A) (κ := Fin 2) (ι := ι))
    [Nonempty ↥(Finset.univ.image fun z : F => u 0 + z • u 1)] (p : (ι → A) → Prop) :
    Pr{let x ← $ᵗ ↥(Finset.univ.image fun z : F => u 0 + z • u 1)}[p x.val] =
      Pr{let z ← $ᵗ F}[p (u 0 + z • u 1)] := by
  let f : F → ↥(Finset.univ.image fun z : F => u 0 + z • u 1) :=
    fun z => ⟨u 0 + z • u 1, Finset.mem_image_of_mem _ (Finset.mem_univ z)⟩
  have hf : Function.Surjective f := by
    rintro ⟨x, hx⟩
    obtain ⟨z, -, rfl⟩ := Finset.mem_image.mp hx
    exact ⟨z, rfl⟩
  by_cases hu : u 1 = 0
  · have hx : ∀ x : ↥(Finset.univ.image fun z : F => u 0 + z • u 1), x.val = u 0 := by
      intro x
      obtain ⟨z, rfl⟩ := hf x
      simp [f, hu]
    simp only [hx, hu, smul_zero, add_zero]
    by_cases hp : p (u 0)
    · rw [(SampleableType.prEvent_uniformSample_eq_one_iff _).2 fun _ => hp,
        (SampleableType.prEvent_uniformSample_eq_one_iff _).2 fun _ => hp]
    · rw [(SampleableType.prEvent_uniformSample_eq_zero_iff _).2 fun _ => hp,
        (SampleableType.prEvent_uniformSample_eq_zero_iff _).2 fun _ => hp]
  · have hinj : Function.Injective f := fun a b h =>
      smul_left_injective F hu (add_left_cancel (congrArg Subtype.val h))
    exact (SampleableType.prEvent_uniformSample_comp_of_bijective ⟨hinj, hf⟩
      fun x => p x.val).symm

omit [DecidableEq ι] [Nonempty A] in
/-- `(δ, ε)`-correlated agreement for affine lines implies that the collection of affine lines
`{u₀ + z • u₁ | z ∈ F}` displays a `(δ, ε)`-proximity gap with respect to `P`. The code `P` need
not be linear. For nonempty `P` the hypothesis `ε < 1` is needed for the `Xor`: for `ε ≥ 1`
correlated agreement holds vacuously, while the line `{c}` through a codeword `c ∈ P` satisfies
both `Pr = 1` and `Pr ≤ ε`. -/
theorem δ_ε_proximityGap_of_δ_ε_correlatedAgreementAffineLines
    (P : Finset (ι → A)) {δ ε : ℝ≥0} (hε : ε < 1)
    (hCA : δ_ε_correlatedAgreementAffineLines (F := F) (P : Set (ι → A)) δ ε) :
    δ_ε_proximityGap P
      (Set.range fun u : WordStack (A := A) (κ := Fin 2) (ι := ι) =>
        Finset.univ.image fun z : F => u 0 + z • u 1)
      δ ε := by
  rintro S ⟨u, rfl⟩ _
  rw [prEvent_affineLine_image_eq u (fun y => δᵣ(y, (P : Set (ι → A))) ≤ δ)]
  by_cases h : Pr{let z ← $ᵗ F}[δᵣ(u 0 + z • u 1, (P : Set (ι → A))) ≤ δ] ≤ ε
  · refine Or.inr ⟨h, fun h1 => ?_⟩
    rw [h1] at h
    exact not_le.mpr (by exact_mod_cast hε) h
  · refine Or.inl ⟨(SampleableType.prEvent_uniformSample_eq_one_iff _).2 fun z => ?_, h⟩
    exact line_close_of_δ_ε_correlatedAgreementAffineLines hCA u (not_le.mp h) z

end AffineLinesProximityGap

section MultilinearCA

-- Shadow the section's `[Ring F]` scalars: the multilinear combination `|⨂|` needs a single
-- coherent `CommRing` structure on `F`, and mixing it with the outer `Ring F` binder creates
-- an instance diamond.
variable {F : Type} [CommRing F] [Fintype F] [SampleableType F]

/-- **[Definition 2.3, DG25]** We say that `C ⊂ F^n` features multilinear correlated agreement
with respect to the proximity parameter `δ` and the error bound `ε`, folding degree `ϑ > 0` if:
∀ word stack `u` of size `2^ϑ`, if the probability that
  (a random multilinear combination of the word stack `u` with randomness `r` is `δ`-close to `C`)
  exceeds `ϑ * ε`, then the word stack `u` has correlated agreement with `C ^⋈ (2^ϑ)`.
Here `ε` is the normalized false-witness bound `E / |F|` from [DG25]. -/
def δ_ε_multilinearCorrelatedAgreement [Module F A]
    (C : Set (ι → A)) (ϑ : ℕ) (δ ε : ℝ≥0) : Prop :=
  ∀ (u : WordStack A (Fin (2^ϑ)) ι),
    Pr{let r ← $ᵗ (Fin ϑ → F)}[ -- This syntax only works with (A : Type 0)
      δᵣ(r |⨂| u, C) ≤ δ
    ] > (ϑ : ℝ≥0) * ε →
    jointAgreement (F := A) (κ := Fin (2 ^ ϑ)) (ι := ι) (C := C) (W := u) (δ := δ)

end MultilinearCA

/-- **`(δ, ε)`-CA for low-degree parameterised (polynomial) curves**: Generalized statement of
**Theorem 1.5, [BCIKS20]**
For `k+1` words `u₀, u₁, ..., uₖ ∈ A^ι` let `curve(u) = {∑_{i ∈ {0, ..., k}}, z^i • u_i | z ∈ 𝔽}`
be a low-degree parameterised polynomial curve. If the probability that a random point in
`curve(u)` is `δ`-close to `C` exceeds `k * ε` (not `(k+1) * ε`), then the words `u₀, ..., uₖ`
have correlated agreement.
**NOTE**: this definition could be converted into the form of Pr{let r ← $ᵗ F}[...] if we want:
  + consistency with `δ_ε_correlatedAgreementAffineLines`
  + making `A` be of arbitrary type universe (Type*)
  + to be able to support the `proximity generator` notation.
-/
noncomputable def δ_ε_correlatedAgreementCurves {k : ℕ}
    {A : Type 0} [AddCommMonoid A] [Module F A] [DecidableEq A]
    (C : Set (ι → A)) (δ ε : ℝ≥0) : Prop :=
    ∀ (u : WordStack (A := A) (κ := Fin (k + 1)) (ι := ι)),
    Pr{let r ← $ᵗ F}[ δᵣ(∑ i : Fin (k + 1), (r ^ (i : ℕ)) • u i, C) ≤ δ ] > k * ε
      → jointAgreement (F := A) (κ := Fin (k + 1)) (ι := ι) (C := C) (W := u) (δ := δ)

/-- **`(δ, ε)`-CA for affine spaces**: Generalized statement of **Theorem 1.6, [BCIKS20]**
For `k+1` words `u₀, u₁, ..., uₖ ∈ A^ι` let `U = u₀ + span{u₁, ..., uₖ} ⊂ A^ι` be an affine subspace
(note that `span` here means linear span, so this formulation is not same as the default
affine span/affine hull). If the probability that a random point in `U` is `δ`-close to `C`
exceeds `ε`, then the words `u₀, u₁, ..., uₖ` have correlated agreement.

This samples uniformly from the generated affine subspace. An equivalent coefficient-sampling
formulation would sample `r : Fin k → F` and test `u₀ + ∑ i, r i • uᵢ₊₁`; proving that
equivalence requires showing the coefficient map has constant-size fibers. -/
noncomputable def δ_ε_correlatedAgreementAffineSpaces
    {A : Type 0} [AddCommGroup A] [Module F A] [Fintype A] [DecidableEq A]
    (C : Set (ι → A)) (δ ε : ℝ≥0) : Prop :=
    ∀ (u : WordStack (A := A) (κ := Fin (k + 1)) (ι := ι)),
    Pr{let y ← $ᵗ ↥(Affine.affineSubspaceAtOrigin (F := F) (u 0) (Fin.tail u))}[
      δᵣ(y.1, C) ≤ δ] > ε →
    jointAgreement (F := A) (κ := Fin (k + 1)) (ι := ι) (C := C) (W := u) (δ := δ)

end CoreSecurityDefinitions

namespace WeightedAgreement

open NNReal Finset Function
open scoped BigOperators

section

variable {ι : Type} [Fintype ι] [Nonempty ι]
variable {F : Type} [Field F] [Fintype F] [SampleableType F] [DecidableEq F]
variable (μ : ι → Set.Icc (0 : ℚ) 1)

/-- Relative `μ`-agreement between words `u` and `v`. -/
noncomputable def agree (u v : ι → F) : ℝ :=
  1 / (Fintype.card ι) * ∑ i ∈ { i | u i = v i }, (μ i).1

/-- `μ`-agreement between a word and a finite set `V`. -/
noncomputable def agree_set (u : ι → F) (V : Finset (ι → F)) [Nonempty V] : ℝ :=
  (Finset.image (agree μ u) V).max' <| by
    rcases ‹Nonempty V› with ⟨v, hv⟩
    exact ⟨agree μ u v, Finset.mem_image.mpr ⟨v, hv, rfl⟩⟩

/-- Weighted size of a subdomain. -/
noncomputable def mu_set (ι' : Finset ι) : ℝ :=
  1 / (Fintype.card ι) * ∑ i ∈ ι', (μ i).1

/-- `μ`-weighted correlated agreement. -/
noncomputable def weightedCorrelatedAgreement
    (C : Set (ι → F)) {k : ℕ} (U : Fin k → ι → F) : ℝ :=
  sSup {x |
    ∃ D' ⊆ (Finset.univ (α := ι)),
      x = mu_set μ D' ∧
      ∃ v : Fin k → ι → F, ∀ i, v i ∈ C ∧ ∀ j ∈ D', v i j = U i j
  }

end

end WeightedAgreement

end ProximityGap

/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.PowerAgreement
public import VCVio.OracleComp.Constructions.SampleableType.NativeMeasure

/-!
# Exact power agreement for interleaved Reed–Solomon codes

A received array `values : Fin (ℓ + 1) → ι → κ → F` has rows indexed by `κ`. One challenge `z`
batches it row by row into `i ↦ j ↦ ∑ t, z ^ t * values t i j`. A tuple `Q : κ → F[X]` of
polynomials of degree below `k` agreeing with the batched array on at least `L` columns has
*exact interleaved power agreement* if every `Q j` is `∑ t, z ^ t • P t j` for polynomials of
degree below `k`, and the columns where all `Q j` agree with the batched array are exactly the
columns where all `P t j` agree with `values t`.

The main theorem, `uniformExactInterleavedPowerAgreement_of_scalar`, says that a uniform scalar
guarantee (`UniformExactPowerAgreement`) with `e` exceptional challenges for every received tuple
gives the same guarantee with the same count `e` for every received array, whenever `k ≤ L`.
It is a specialization of `Code.uniformExactAgreement_moduleInterleavedCode`: the scalar and
interleaved polynomial predicates are the code-level predicates for the batching map
`CoreDefinitions.univariatePowersGenerator F ℓ`
(`uniformExactPowerAgreement_iff_uniformExactAgreement` and
`uniformExactInterleavedPowerAgreement_of_uniformExactAgreement`), and the seed space `F` has at
most `|F|` elements.

The last section composes an inner interleaved guarantee with an outer scalar guarantee for
nested power batching `v ↦ ∑ g, v ^ g * ∑ t, u ^ t * values g t` of groups of different sizes,
padding each group by zero to a common size.

## Main definitions

* `ReedSolomon.interleavedPolynomialAgreementSet`,
  `ReedSolomon.interleavedCommonPowerAgreementSet`, `ReedSolomon.interleavedPowerBatchedWord`.
* `ReedSolomon.HasExactInterleavedPowerAgreement`,
  `ReedSolomon.UniformExactInterleavedPowerAgreement`.
* `ReedSolomon.HasExactNestedPowerAgreement`, with the padding helpers `ReedSolomon.padFin` and
  `ReedSolomon.paddedPowerValues`.

## Main statements

* `ReedSolomon.uniformExactInterleavedPowerAgreement_of_uniformExactAgreement`: the code-level
  guarantee for `code domain k ^⋈ κ` gives the polynomial guarantee.
* `ReedSolomon.uniformExactInterleavedPowerAgreement_of_scalar`: the scalar-to-interleaved
  transfer, over every field and for every finite row type.
* `ReedSolomon.exactNestedPowerAgreement_of_interleaved` and
  `ReedSolomon.nestedPowerAgreement_sharedInner`: nested power agreement.
* `ReedSolomon.nestedPowerAgreement_probability_le`: for uniform challenges `(u, v)`, nested
  exact agreement fails with probability at most `(innerE + outerE) / |F|`.

## References

ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

* `ReedSolomon/Interleaved/PowerAgreement.lean`: the definitions
  `interleavedPolynomialAgreementSet`, `interleavedCommonPowerAgreementSet`,
  `interleavedPowerBatchedWord`, `HasExactInterleavedPowerAgreement`,
  `UniformExactInterleavedPowerAgreement`, `padFin`, `paddedPowerValues`, and the theorems
  `sum_padFin`, `interleavedPowerBatchedWord_padded_apply`,
  `exactNestedPowerAgreement_of_interleaved`, and `nestedPowerAgreement_sharedInner` are ported
  with `Fin n` columns generalized to a finite type `ι` and, in the definitions, `Fin width` rows
  generalized to a finite type `κ`. The theorem `uniformExactInterleavedPowerAgreement_of_scalar`
  (hypotheses `[Finite F]`, `0 < width`, `k ≤ agreement`) is generalized to the theorem of the
  same name here, which has neither `[Finite F]` nor a width hypothesis. The private counting
  lemmas `scalar_powerProjectionBad_card_le` and `interleaved_powerProjectionBad_card_le`, and the
  public `interleavedCodeword_eq_of_agree_on`, are replaced by the code-level statements of
  `ArkLib.Data.CodingTheory.InterleavedCode.ExactAgreement` and
  `ReedSolomon.determinedByAgreement_code`.
* `ReedSolomon/Interleaved/PowerAgreementArbitrary.lean`:
  `uniformExactInterleavedPowerAgreement_of_scalar_arbitrary` removed the hypothesis
  `[Finite F]` from the previous theorem by a second, infinite-field proof. Here a single proof
  covers both cases, so it is the theorem `uniformExactInterleavedPowerAgreement_of_scalar`
  itself. Its private lemmas are covered as described in
  `ArkLib.Data.CodingTheory.InterleavedCode.ExactAgreement`.
* `ReedSolomon/MutualCorrelatedAgreement/NestedPowerAgreement.lean`:
  `HasExactNestedPowerAgreement`, with `Fin n` generalized to `ι`. The arithmetic lemma
  `nestedPowerAgreement_probability_bound` (a set of at most `|F| * E` pairs has rational density
  at most `E / |F|` in `F × F`) is replaced by `nestedPowerAgreement_probability_le`, which bounds
  the probability of the failure event itself as a native event `Pr{let p ← $ᵗ (F × F)}[…]`.

Deferred: the shared-level fold and tensor-tight statements of
`ReedSolomon/Interleaved/TensorFoldAgreement.lean` and the concrete Reed–Solomon
endpoints that supply the scalar guarantee.
-/

@[expose] public section

namespace ReedSolomon

open Polynomial CoreDefinitions

noncomputable section

section Definitions

variable {F ι κ : Type*} [Field F] [Fintype ι] [Fintype κ] [DecidableEq F] {ℓ : ℕ}

/-- The columns `i` where every row polynomial `Q j` agrees with `received i j`. -/
def interleavedPolynomialAgreementSet (domain : ι ↪ F) (received : ι → κ → F)
    (Q : κ → F[X]) : Finset ι :=
  Finset.univ.filter fun i ↦ ∀ j, (Q j).eval (domain i) = received i j

/-- The columns `i` where every polynomial `P t j` agrees with `values t i j`. -/
def interleavedCommonPowerAgreementSet (domain : ι ↪ F) (values : Fin (ℓ + 1) → ι → κ → F)
    (P : Fin (ℓ + 1) → κ → F[X]) : Finset ι :=
  Finset.univ.filter fun i ↦ ∀ t j, (P t j).eval (domain i) = values t i j

@[simp] theorem mem_interleavedPolynomialAgreementSet (domain : ι ↪ F) (received : ι → κ → F)
    (Q : κ → F[X]) (i : ι) :
    i ∈ interleavedPolynomialAgreementSet domain received Q ↔
      ∀ j, (Q j).eval (domain i) = received i j := by
  simp [interleavedPolynomialAgreementSet]

@[simp] theorem mem_interleavedCommonPowerAgreementSet (domain : ι ↪ F)
    (values : Fin (ℓ + 1) → ι → κ → F) (P : Fin (ℓ + 1) → κ → F[X]) (i : ι) :
    i ∈ interleavedCommonPowerAgreementSet domain values P ↔
      ∀ t j, (P t j).eval (domain i) = values t i j := by
  simp [interleavedCommonPowerAgreementSet]

omit [Fintype ι] [Fintype κ] [DecidableEq F] in
/-- The row-wise batched array `i ↦ j ↦ ∑ t, z ^ t * values t i j`. -/
def interleavedPowerBatchedWord (values : Fin (ℓ + 1) → ι → κ → F) (z : F) : ι → κ → F :=
  fun i j ↦ ∑ t, z ^ t.val * values t i j

/-- **Exact interleaved power agreement.** Every row polynomial `Q j` is `∑ t, z ^ t • P t j` for
polynomials `P t j` of degree below `k`, and the columns where all `Q j` agree with the batched
array are exactly the columns where all `P t j` agree with `values t`. -/
def HasExactInterleavedPowerAgreement (domain : ι ↪ F) (values : Fin (ℓ + 1) → ι → κ → F)
    (k : ℕ) (z : F) (Q : κ → F[X]) : Prop :=
  ∃ P : Fin (ℓ + 1) → κ → F[X], (∀ t j, (P t j).degree < k) ∧
    (∀ j, Q j = powerBatchedPolynomial (fun t ↦ P t j) z) ∧
    interleavedPolynomialAgreementSet domain (interleavedPowerBatchedWord values z) Q =
      interleavedCommonPowerAgreementSet domain values P

/-- **Uniform exact interleaved power agreement.** One set `bad` of at most `e` challenges,
chosen after the array `values`, such that for every `z ∉ bad`, every tuple `Q` of polynomials of
degree below `k` agreeing with the batched array on at least `L` columns (all rows at once) has
exact interleaved power agreement. The count `e` does not depend on the number of rows. -/
def UniformExactInterleavedPowerAgreement (domain : ι ↪ F) (values : Fin (ℓ + 1) → ι → κ → F)
    (k L e : ℕ) : Prop :=
  ∃ bad : Finset F, bad.card ≤ e ∧ ∀ z ∉ bad, ∀ Q : κ → F[X], (∀ j, (Q j).degree < k) →
    L ≤ (interleavedPolynomialAgreementSet domain (interleavedPowerBatchedWord values z) Q).card →
    HasExactInterleavedPowerAgreement domain values k z Q

end Definitions

section Transfer

variable {F : Type} {ι κ : Type*} [Field F] [Fintype ι] [Fintype κ] [DecidableEq F] {ℓ : ℕ}

/-- **The code-level guarantee gives the polynomial guarantee.** A uniform exact-agreement
guarantee for the interleaved code `code domain k ^⋈ κ` and the batching map
`univariatePowersGenerator F ℓ` gives `UniformExactInterleavedPowerAgreement` with the same
threshold and count.

For a good challenge and a close tuple `Q`, the codeword of evaluations of `Q` has codeword
witnesses; their rows are lifted to polynomials row by row by `exists_powerBatchedPolynomial_eq`.
No relation between `k` and `L` is needed. -/
theorem uniformExactInterleavedPowerAgreement_of_uniformExactAgreement (domain : ι ↪ F)
    (values : Fin (ℓ + 1) → ι → κ → F) {k L e : ℕ}
    (h : Code.UniformExactAgreement (univariatePowersGenerator F ℓ) ((code domain k)^⋈κ) L e
      values) :
    UniformExactInterleavedPowerAgreement domain values k L e := by
  obtain ⟨bad, hcard, hbad⟩ := h
  refine ⟨bad, hcard, fun z hz Q hQ hL ↦ ?_⟩
  have hc : (fun i j ↦ (Q j).eval (domain i)) ∈ ((code domain k : ModuleCode ι F F)^⋈κ) := fun j ↦
    evalOnPoints_mem_code_of_degree_lt (hQ j)
  obtain ⟨c', hc', hcsum, hiff⟩ := hbad z hz _ hc _ hL fun i hi ↦ by
    funext j
    have := (mem_interleavedPolynomialAgreementSet _ _ _ _).mp hi j
    simpa [interleavedPowerBatchedWord] using this
  choose P hP hPc hQP using fun j ↦ exists_powerBatchedPolynomial_eq domain (hQ j)
    (c' := fun t i ↦ c' t i j) (fun t ↦ hc' t j) fun i ↦ by
      simpa using congrFun (congrFun hcsum i) j
  refine ⟨fun t j ↦ P j t, fun t j ↦ hP j t, hQP, ?_⟩
  ext i
  have hi := hiff i
  simp only [funext_iff, Finset.sum_apply, Pi.smul_apply, univariatePowersGenerator,
    smul_eq_mul] at hi
  simp only [mem_interleavedPolynomialAgreementSet, mem_interleavedCommonPowerAgreementSet,
    interleavedPowerBatchedWord, hPc]
  rw [hi]

/-- **Scalar-to-interleaved transfer of uniform exact power agreement.** If every received tuple
`w : Fin (ℓ + 1) → ι → F` has a uniform exact power-agreement guarantee with at most `e`
exceptional challenges at threshold `L`, and `k ≤ L`, then every received array
`values : Fin (ℓ + 1) → ι → κ → F`, for any finite row type `κ`, has the interleaved guarantee
with the same `e`.

This is `Code.uniformExactAgreement_moduleInterleavedCode` for `code domain k` and
`univariatePowersGenerator F ℓ`, whose seed space is `F`, so the seed-count hypothesis holds.
The scalar hypothesis must hold for every received tuple, because the proof applies it to a row
combination of `values`. The hypothesis `k ≤ L` gives `determinedByAgreement_code`, which turns
the count of projection-bad challenges back into exact agreement; the count itself does not use
it. The field may be finite or infinite, and `κ` may be empty. -/
theorem uniformExactInterleavedPowerAgreement_of_scalar (domain : ι ↪ F) {k L e : ℕ}
    (hscalar : ∀ w : Fin (ℓ + 1) → ι → F, UniformExactPowerAgreement domain w k L e)
    (hk : k ≤ L) (values : Fin (ℓ + 1) → ι → κ → F) :
    UniformExactInterleavedPowerAgreement domain values k L e :=
  uniformExactInterleavedPowerAgreement_of_uniformExactAgreement domain values
    (Code.uniformExactAgreement_moduleInterleavedCode (univariatePowersGenerator F ℓ)
      (code domain k) L (Or.inl le_rfl) (determinedByAgreement_code domain hk)
      (fun w ↦ (uniformExactPowerAgreement_iff_uniformExactAgreement domain w).mp (hscalar w))
      values)

end Transfer

section Nested

variable {F : Type} {ι : Type*} [Field F] [Fintype ι] [DecidableEq F]

/-- **Exact nested power agreement.** For groups `w g : Fin (ℓ g + 1) → ι → F` batched first by
`u` within each group and then by `v` across groups, `Q` is
`∑ g, v ^ g • ∑ t, u ^ t • P g t` for polynomials `P g t` of degree below `k`, and the agreement
set of `Q` with the nested batched word is the set of coordinates where every `P g t` agrees with
`w g t`. -/
def HasExactNestedPowerAgreement {m : ℕ} (domain : ι ↪ F) (ℓ : Fin (m + 1) → ℕ)
    (w : (g : Fin (m + 1)) → Fin (ℓ g + 1) → ι → F) (k : ℕ) (u v : F) (Q : F[X]) : Prop :=
  ∃ P : (g : Fin (m + 1)) → Fin (ℓ g + 1) → F[X], (∀ g t, (P g t).degree < k) ∧
    Q = powerBatchedPolynomial (fun g ↦ powerBatchedPolynomial (P g) u) v ∧
    polynomialAgreementSet domain (powerBatchedWord (fun g ↦ powerBatchedWord (w g) u) v) Q =
      Finset.univ.filter fun i ↦ ∀ g t, (P g t).eval (domain i) = w g t i

omit [Field F] [Fintype ι] [DecidableEq F] in
/-- Extension of a tuple `f : Fin a → A` by zero to `Fin b`, for `a ≤ b`. -/
def padFin {A : Type*} [Zero A] {a b : ℕ} (_h : a ≤ b) (f : Fin a → A) (i : Fin b) : A :=
  if hi : i.val < a then f ⟨i.val, hi⟩ else 0

omit [Field F] [Fintype ι] [DecidableEq F] in
/-- Padding by zero does not change the sum. -/
theorem sum_padFin {A : Type*} [AddCommMonoid A] {a b : ℕ} (h : a ≤ b) (f : Fin a → A) :
    ∑ i : Fin b, padFin h f i = ∑ i : Fin a, f i := by
  let g : ℕ → A := fun i ↦ if hi : i < a then f ⟨i, hi⟩ else 0
  calc ∑ i : Fin b, padFin h f i = ∑ i ∈ Finset.range b, g i := by
        rw [← Fin.sum_univ_eq_sum_range g b]
        rfl
    _ = ∑ i ∈ Finset.range a, g i := by
        rw [← Finset.sum_range_add_sum_Ico g h, Finset.sum_eq_zero (s := Finset.Ico a b),
          add_zero]
        intro i hi
        simp [g, Nat.not_lt.mpr (Finset.mem_Ico.mp hi).1]
    _ = ∑ i : Fin a, f i := by
        rw [← Fin.sum_univ_eq_sum_range g a]
        exact Finset.sum_congr rfl fun i _ ↦ by simp [g]

omit [Fintype ι] [DecidableEq F] in
/-- The groups `values g : Fin (degree g + 1) → ι → F`, padded by zero to a common size
`maxDegree + 1` and arranged as an array with one row per group. -/
def paddedPowerValues {rows maxDegree : ℕ} (degree : Fin rows → ℕ)
    (hdegree : ∀ g, degree g ≤ maxDegree) (values : (g : Fin rows) → Fin (degree g + 1) → ι → F) :
    Fin (maxDegree + 1) → ι → Fin rows → F :=
  fun t i g ↦ padFin (Nat.add_le_add_right (hdegree g) 1) (fun j ↦ values g j i) t

omit [Fintype ι] [DecidableEq F] in
/-- Padding preserves the batched word of each group. -/
theorem interleavedPowerBatchedWord_padded_apply {rows maxDegree : ℕ} (degree : Fin rows → ℕ)
    (hdegree : ∀ g, degree g ≤ maxDegree) (values : (g : Fin rows) → Fin (degree g + 1) → ι → F)
    (z : F) (i : ι) (g : Fin rows) :
    interleavedPowerBatchedWord (paddedPowerValues degree hdegree values) z i g =
      powerBatchedWord (values g) z i := by
  unfold interleavedPowerBatchedWord paddedPowerValues powerBatchedWord
  rw [← sum_padFin (Nat.add_le_add_right (hdegree g) 1)
    (fun j : Fin (degree g + 1) ↦ z ^ j.val * values g j i)]
  refine Finset.sum_congr rfl fun t _ ↦ ?_
  simp only [padFin]
  split_ifs <;> simp

/-- **Nested exact agreement from outer and inner exact agreement.** Suppose `Q` agrees with the
nested batched word on at least `L ≥ k` coordinates, has exact power agreement for the outer
batching by `v` of the group words `powerBatchedWord (values g) u`, and every tuple of degree
below `k` that is close to the padded inner array has exact interleaved power agreement at `u`.
Then `Q` has exact nested power agreement.

The outer witnesses are the row tuple fed to the inner guarantee. The inner witnesses have
padded coefficients beyond each group's size; these vanish because they agree with zero on at
least `k` coordinates, which is where `k ≤ L` is used. -/
theorem exactNestedPowerAgreement_of_interleaved {m maxDegree k L : ℕ} (domain : ι ↪ F)
    (degree : Fin (m + 1) → ℕ) (hdegree : ∀ g, degree g ≤ maxDegree)
    (values : (g : Fin (m + 1)) → Fin (degree g + 1) → ι → F) (hk : k ≤ L) (u v : F)
    (Q : F[X])
    (hclose : L ≤ (polynomialAgreementSet domain
      (powerBatchedWord (fun g ↦ powerBatchedWord (values g) u) v) Q).card)
    (houter : HasExactPowerAgreement domain (fun g ↦ powerBatchedWord (values g) u)
      (RingHom.id F) k v Q)
    (hinner : ∀ R : Fin (m + 1) → F[X], (∀ g, (R g).degree < k) →
      L ≤ (interleavedPolynomialAgreementSet domain
        (interleavedPowerBatchedWord (paddedPowerValues degree hdegree values) u) R).card →
      HasExactInterleavedPowerAgreement domain (paddedPowerValues degree hdegree values) k u R) :
    HasExactNestedPowerAgreement domain degree values k u v Q := by
  obtain ⟨R, hRdegree, hQeq, houterSet⟩ := (hasExactPowerAgreement_id_iff _ _ _ _ _).mp houter
  set padded := paddedPowerValues degree hdegree values
  have hsets : interleavedPolynomialAgreementSet domain (interleavedPowerBatchedWord padded u) R =
      polynomialAgreementSet domain
        (powerBatchedWord (fun g ↦ powerBatchedWord (values g) u) v) Q := by
    rw [houterSet]
    ext i
    simp [interleavedPolynomialAgreementSet, padded,
      interleavedPowerBatchedWord_padded_apply]
  have hinnerClose : L ≤ (interleavedPolynomialAgreementSet domain
      (interleavedPowerBatchedWord padded u) R).card := hsets ▸ hclose
  obtain ⟨Ppad, hPdegree, hReq, hinnerSet⟩ := hinner R hRdegree hinnerClose
  set S := interleavedCommonPowerAgreementSet domain padded Ppad
  have hScard : k ≤ S.card := hk.trans (hinnerSet ▸ hinnerClose)
  have hkS : ((k : ℕ) : WithBot ℕ) ≤ (S.card : WithBot ℕ) := by exact_mod_cast hScard
  -- Padded coefficients beyond a group's size vanish.
  have hzero (t : Fin (maxDegree + 1)) (g : Fin (m + 1)) (ht : ¬ t.val < degree g + 1) :
      Ppad t g = 0 := by
    apply Polynomial.eq_of_degrees_lt_of_eval_index_eq (s := S) domain.injective.injOn
      ((hPdegree t g).trans_le hkS) (by simp)
    intro i hi
    rw [(mem_interleavedCommonPowerAgreementSet _ _ _ _).mp hi t g]
    simp [padded, paddedPowerValues, padFin, ht]
  let P : (g : Fin (m + 1)) → Fin (degree g + 1) → F[X] :=
    fun g t ↦ Ppad ⟨t.val, Nat.lt_succ_iff.mpr ((Nat.le_of_lt_succ t.isLt).trans (hdegree g))⟩ g
  have hReq' (g) : R g = powerBatchedPolynomial (P g) u := by
    rw [hReq g]
    unfold powerBatchedPolynomial
    rw [← sum_padFin (Nat.add_le_add_right (hdegree g) 1)
      (fun t : Fin (degree g + 1) ↦ u ^ t.val • P g t)]
    refine Finset.sum_congr rfl fun t _ ↦ ?_
    simp only [padFin]
    split_ifs with ht
    · rfl
    · simp [hzero t g ht]
  refine ⟨P, fun g t ↦ hPdegree _ g, ?_, ?_⟩
  · rw [hQeq]
    congr 1
    funext g
    exact hReq' g
  · rw [← hsets, hinnerSet]
    ext i
    simp only [S, mem_interleavedCommonPowerAgreementSet, Finset.mem_filter, Finset.mem_univ,
      true_and]
    constructor
    · intro h g t
      have ht : t.val ≤ degree g := Nat.lt_succ_iff.mp t.isLt
      simpa [P, padded, paddedPowerValues, padFin, Nat.lt_succ_iff.mpr ht] using
        h ⟨t.val, Nat.lt_succ_iff.mpr ((Nat.le_of_lt_succ t.isLt).trans (hdegree g))⟩ g
    · intro h t g
      by_cases ht : t.val < degree g + 1
      · simpa [P, padded, paddedPowerValues, padFin, ht] using h g ⟨t.val, ht⟩
      · simp [hzero t g ht, padded, paddedPowerValues, padFin, ht]

/-- **Nested power agreement with one shared inner guarantee.** Suppose the padded inner array
has a uniform exact interleaved guarantee at threshold `L ≥ k` with `innerE` exceptional
challenges `u`, and for every `u` the group words `powerBatchedWord (values g) u` have a uniform
scalar guarantee with `outerE` exceptional challenges `v`. Then at most
`|F| · (innerE + outerE)` challenge pairs `(u, v)` are exceptional for exact nested power
agreement.

The inner exceptional count is paid once for all groups, whatever their number and sizes: the
bad pairs are `innerBad × F` together with `{u} × outerBad u` for each `u`. -/
theorem nestedPowerAgreement_sharedInner [Fintype F] {m maxDegree k L innerE outerE : ℕ}
    (domain : ι ↪ F) (degree : Fin (m + 1) → ℕ) (hdegree : ∀ g, degree g ≤ maxDegree)
    (values : (g : Fin (m + 1)) → Fin (degree g + 1) → ι → F) (hk : k ≤ L)
    (hinner : UniformExactInterleavedPowerAgreement domain
      (paddedPowerValues degree hdegree values) k L innerE)
    (houter : ∀ u, UniformExactPowerAgreement domain
      (fun g ↦ powerBatchedWord (values g) u) k L outerE) :
    ∃ bad : Finset (F × F), bad.card ≤ Fintype.card F * (innerE + outerE) ∧
      ∀ u v, (u, v) ∉ bad → ∀ Q : F[X], Q.degree < k →
        L ≤ (polynomialAgreementSet domain
          (powerBatchedWord (fun g ↦ powerBatchedWord (values g) u) v) Q).card →
        HasExactNestedPowerAgreement domain degree values k u v Q := by
  obtain ⟨innerBad, hinnerCard, hinnerGood⟩ := hinner
  choose outerBad houterCard houterGood using houter
  let outerPairs := Finset.univ.biUnion fun u ↦ ({u} : Finset F) ×ˢ outerBad u
  have ho : outerPairs.card ≤ Fintype.card F * outerE := by
    refine Finset.card_biUnion_le.trans ?_
    calc ∑ u : F, (({u} : Finset F) ×ˢ outerBad u).card ≤ ∑ _u : F, outerE :=
          Finset.sum_le_sum fun u _ ↦ by simpa using houterCard u
      _ = Fintype.card F * outerE := by simp
  refine ⟨innerBad ×ˢ Finset.univ ∪ outerPairs, ?_, fun u v huv Q hQ hclose ↦ ?_⟩
  · calc (innerBad ×ˢ Finset.univ ∪ outerPairs).card
          ≤ (innerBad ×ˢ (Finset.univ : Finset F)).card + outerPairs.card :=
          Finset.card_union_le _ _
      _ ≤ innerE * Fintype.card F + Fintype.card F * outerE := by
          simpa using Nat.add_le_add (Nat.mul_le_mul_right (Fintype.card F) hinnerCard) ho
      _ = Fintype.card F * (innerE + outerE) := by ring
  · have hu : u ∉ innerBad := fun hu ↦ huv (Finset.mem_union_left _ (by simp [hu]))
    have hv : v ∉ outerBad u := fun hv ↦ huv (Finset.mem_union_right _
      (Finset.mem_biUnion.mpr ⟨u, Finset.mem_univ _, by simp [hv]⟩))
    exact exactNestedPowerAgreement_of_interleaved domain degree hdegree values hk u v Q hclose
      (houterGood u v hv Q hQ hclose) fun R hR hRclose ↦ hinnerGood u hu R hR hRclose

open scoped ProbabilityTheory in
/-- **Nested power agreement for uniform challenges.** Under the hypotheses of
`nestedPowerAgreement_sharedInner`, draw the challenge pair `(u, v)` uniformly from `F × F`. The
probability that some `Q` of degree below `k` agrees with the nested batched word on at least `L`
coordinates without having exact nested power agreement is at most `(innerE + outerE) / |F|`.

This is the count `|F| · (innerE + outerE)` of `nestedPowerAgreement_sharedInner` divided by
`|F|²`. -/
theorem nestedPowerAgreement_probability_le [Fintype F] [SampleableType F]
    {m maxDegree k L innerE outerE : ℕ}
    (domain : ι ↪ F) (degree : Fin (m + 1) → ℕ) (hdegree : ∀ g, degree g ≤ maxDegree)
    (values : (g : Fin (m + 1)) → Fin (degree g + 1) → ι → F) (hk : k ≤ L)
    (hinner : UniformExactInterleavedPowerAgreement domain
      (paddedPowerValues degree hdegree values) k L innerE)
    (houter : ∀ u, UniformExactPowerAgreement domain
      (fun g ↦ powerBatchedWord (values g) u) k L outerE) :
    Pr{let p ← $ᵗ (F × F)}[∃ Q : F[X], Q.degree < k ∧
        L ≤ (polynomialAgreementSet domain
          (powerBatchedWord (fun g ↦ powerBatchedWord (values g) p.1) p.2) Q).card ∧
        ¬ HasExactNestedPowerAgreement domain degree values k p.1 p.2 Q] ≤
      ENNReal.ofReal ((innerE + outerE : ℕ) / (Fintype.card F : ℝ)) := by
  classical
  obtain ⟨bad, hcard, hgood⟩ :=
    nestedPowerAgreement_sharedInner domain degree hdegree values hk hinner houter
  refine (prEvent_mono _ _ (fun p ↦ p ∈ bad) fun p hp ↦ ?_).trans ?_
  · by_contra hp'
    obtain ⟨Q, hQ, hclose, hnot⟩ := hp
    exact hnot (hgood p.1 p.2 hp' Q hQ hclose)
  rw [SampleableType.prEvent_uniformSample_eq_ofReal]
  simp only [Finset.filter_mem_eq_inter, Finset.univ_inter, Fintype.card_prod]
  apply ENNReal.ofReal_le_ofReal
  have hq : (0 : ℝ) < Fintype.card F := by exact_mod_cast Fintype.card_pos
  have hb : (bad.card : ℝ) ≤ (Fintype.card F : ℝ) * (innerE + outerE : ℕ) := by
    exact_mod_cast hcard
  rw [div_le_div_iff₀ (by positivity) hq]
  push_cast at hb ⊢
  nlinarith

end Nested

end

end ReedSolomon

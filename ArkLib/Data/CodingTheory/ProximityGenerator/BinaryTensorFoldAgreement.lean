/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.InterleavedCode.ExactAgreement
public import ArkLib.Data.CodingTheory.ProximityGenerator.PolynomialGenerator

/-!
# Exact agreement through shared-level binary tensor folds

A *binary line fold* sends two words `u₀ u₁ : ι → A` and a challenge `r` to
`i ↦ (1 - r) • u₀ i + r • u₁ i`. It is the combination of the family `b ↦ (u₀, u₁) b` under the
batching map `binaryEqualityGenerator : r ↦ (1 - r, r)`, indexed by `Bool`. A *binary tensor fold*
of height `h` applies `h` line folds with challenges `r 0, …, r (h - 1)` to `2 ^ h` leaf words, one
level at a time from the root.

At one level, the words to be opened form a family indexed by some finite type `β`, and all of
them are folded with the same challenge. A *full-set level witness* (`FullSetLevelWitness C a e`)
says that for every such family there is one set of at most `e` challenges outside which every
family of codewords agreeing with the folded family on at least `a` common coordinates is the
fold of two codeword families, and the common agreement set is exactly the intersection of the
two child agreement sets. The count `e` does not depend on `β`.

This file proves three things.

* For a code determined by `a` agreements, a full-set level witness with count `e` is the same as
  a uniform exact-agreement guarantee (`Code.UniformExactAgreement`) with count `e` for every
  single binary line over `C` (`fullSetLevelWitness_iff`). The family version follows from the
  single-line version by the interleaving transfer of
  `ArkLib.Data.CodingTheory.InterleavedCode.ExactAgreement`, applied to `C ^⋈ β`.
* A full-set level witness for `C` is one for every interleaving `C ^⋈ κ`, with the same count
  (`FullSetLevelWitness.moduleInterleavedCode`); no hypothesis on `C` is needed.
* Given a full-set level witness, a height-`h` fold has at most `h * e * |F| ^ (h - 1)` bad
  challenge tuples (`tensorFoldBad_card_le`), and outside them every codeword with `a`
  agreements with the folded word is the fold of codeword leaves whose common agreement set is
  the full agreement set of the root (`hasFullTensorDecomposition_of_not_mem_bad`). Each level is
  charged once, although the number of words at a level doubles with each level.

The Reed–Solomon statements are in
`ArkLib.Data.CodingTheory.ReedSolomon.Interleaved.TensorFoldAgreement`, and the probability form
of the count is in `ArkLib.Data.CodingTheory.ProximityGenerator.BinaryTensorFoldProbability`.

## Main definitions

* `TensorMCA.binaryEqualityGenerator`, `TensorMCA.binaryLineFold`, `TensorMCA.binaryTensorFold`.
* `TensorMCA.fullAgreementSet`, `TensorMCA.familyAgreementSet`.
* `TensorMCA.FullSetLevelWitness`: one exceptional set per level for every finite family.
* `TensorMCA.HasFullTensorDecomposition`: leaf decomposition of every close root codeword.
* `TensorMCA.TensorFoldGood`, `TensorMCA.tensorFoldBad`: the levelwise good event and the set of
  challenge tuples where it fails.

## Main statements

* `TensorMCA.fullSetLevelWitness_of_uniformExactAgreement` and `TensorMCA.fullSetLevelWitness_iff`.
* `TensorMCA.FullSetLevelWitness.moduleInterleavedCode`.
* `TensorMCA.binaryTensorFold_eq_tensorGeneratorPi`: the fold is the iterated tensor generator
  `PolynomialGenIsMCA.tensorGeneratorPi` of the equality weights.
* `TensorMCA.tensorFoldBad_card_le` and `TensorMCA.hasFullTensorDecomposition_of_not_mem_bad`.
-/

@[expose] public section

namespace TensorMCA

open Code LinearCode CoreDefinitions

section AgreementSets

variable {ι A : Type*} [Fintype ι] [DecidableEq A]

/-- The coordinates where the words `c` and `u` agree. -/
def fullAgreementSet (c u : ι → A) : Finset ι :=
  Finset.univ.filter fun i ↦ c i = u i

/-- The coordinates where every member of the family `c` agrees with the corresponding member
of `u`. -/
def familyAgreementSet {β : Type*} [Fintype β] (c u : β → ι → A) : Finset ι :=
  Finset.univ.filter fun i ↦ ∀ b, c b i = u b i

/-- Membership in `fullAgreementSet c u` is agreement of `c` and `u` at that coordinate. -/
@[simp] theorem mem_fullAgreementSet (c u : ι → A) (i : ι) :
    i ∈ fullAgreementSet c u ↔ c i = u i := by
  simp [fullAgreementSet]

/-- Membership in `familyAgreementSet c u` is agreement of `c b` and `u b` at that coordinate for
every `b`. -/
@[simp] theorem mem_familyAgreementSet {β : Type*} [Fintype β] (c u : β → ι → A) (i : ι) :
    i ∈ familyAgreementSet c u ↔ ∀ b, c b i = u b i := by
  simp [familyAgreementSet]

end AgreementSets

section Definitions

variable {ι F A : Type*} [Ring F] [AddCommMonoid A] [Module F A]

/-- The equality weights `r ↦ (1 - r, r)` of a binary fold, indexed by `Bool` with `false ↦ 1 - r`
and `true ↦ r`. -/
def binaryEqualityGenerator (r : F) (b : Bool) : F := if b then r else 1 - r

/-- The binary line fold `i ↦ (1 - r) • u₀ i + r • u₁ i`. At `r = 0` it is `u₀` and at `r = 1` it
is `u₁`. -/
def binaryLineFold (r : F) (u₀ u₁ : ι → A) : ι → A :=
  fun i ↦ (1 - r) • u₀ i + r • u₁ i

/-- The binary line fold is the combined word of the family `U` under `binaryEqualityGenerator`,
in the form used by `Code.IsProjectionBad` and `Code.HasExactAgreement`. -/
theorem binaryLineFold_eq_sum (r : F) (U : Bool → ι → A) :
    binaryLineFold r (U false) (U true) = fun i ↦ ∑ b, binaryEqualityGenerator r b • U b i := by
  funext i
  simp [binaryLineFold, binaryEqualityGenerator, add_comm]

/-- The binary tensor fold of height `h`, from the root challenge `r 0`: the line fold at `r 0` of
the two height-`h - 1` folds of the leaves whose first bit is `false` and `true`. At height `0`
it is the single leaf. -/
def binaryTensorFold : ∀ {h : ℕ}, (Fin h → F) → ((Fin h → Bool) → ι → A) → ι → A
  | 0, _, u => u default
  | _ + 1, r, u => binaryLineFold (r 0)
      (binaryTensorFold (Fin.tail r) (fun leaf ↦ u (Fin.cons false leaf)))
      (binaryTensorFold (Fin.tail r) (fun leaf ↦ u (Fin.cons true leaf)))

variable [Fintype ι] [DecidableEq ι] [DecidableEq A]

/-- **Full-set level witness.** For every finite family type `β` and child families `u₀ u₁`, one
set of at most `e` challenges is chosen before the challenge and the codewords. For every
challenge `r` outside it and every family `c` of codewords agreeing with the folded family
`b ↦ binaryLineFold r (u₀ b) (u₁ b)` on at least `a` common coordinates, there are codeword
families `c₀ c₁` with `c b = binaryLineFold r (c₀ b) (c₁ b)`, and the common agreement set of `c`
equals the intersection of the common agreement sets of `c₀` with `u₀` and of `c₁` with `u₁`.

The count `e` does not depend on `β`. This is what lets a tensor fold charge each level once,
although each level opens twice as many words as the one before (`tensorFoldBad_card_le`). For a
code determined by `a` agreements the definition is equivalent to its case of a single line
(`fullSetLevelWitness_iff`). -/
def FullSetLevelWitness (C : ModuleCode ι F A) (a e : ℕ) : Prop :=
  ∀ (β : Type) [Fintype β] (u₀ u₁ : β → ι → A), ∃ bad : Finset F, bad.card ≤ e ∧
    ∀ r ∉ bad, ∀ c : β → ι → A, (∀ b, c b ∈ C) →
      a ≤ (familyAgreementSet c fun b ↦ binaryLineFold r (u₀ b) (u₁ b)).card →
      ∃ c₀ c₁ : β → ι → A, (∀ b, c₀ b ∈ C) ∧ (∀ b, c₁ b ∈ C) ∧
        (∀ b, c b = binaryLineFold r (c₀ b) (c₁ b)) ∧
        familyAgreementSet c (fun b ↦ binaryLineFold r (u₀ b) (u₁ b)) =
          familyAgreementSet c₀ u₀ ∩ familyAgreementSet c₁ u₁

/-- **Full tensor decomposition at one challenge tuple.** Every codeword `c` agreeing with the
height-`h` fold of the leaves `u` on at least `a` coordinates is the fold of codeword leaves, and
its full agreement set with the folded word is the set of coordinates where every codeword leaf
agrees with its leaf word. -/
def HasFullTensorDecomposition (C : ModuleCode ι F A) (a : ℕ) {h : ℕ} (r : Fin h → F)
    (u : (Fin h → Bool) → ι → A) : Prop :=
  ∀ c ∈ C, a ≤ (fullAgreementSet c (binaryTensorFold r u)).card →
    ∃ leafCode : (Fin h → Bool) → ι → A, (∀ leaf, leafCode leaf ∈ C) ∧
      c = binaryTensorFold r leafCode ∧
      fullAgreementSet c (binaryTensorFold r u) =
        Finset.univ.filter fun i ↦ ∀ leaf, leafCode leaf i = u leaf i

/-- **Full tensor decomposition of a family.** The family form of `HasFullTensorDecomposition`:
every codeword family agreeing with the folded family on at least `a` common coordinates is the
fold of a family of codeword leaves with the same common agreement set. -/
def HasFullTensorFamilyDecomposition (C : ModuleCode ι F A) (a : ℕ) {β : Type*} [Fintype β]
    {h : ℕ} (r : Fin h → F) (u : β → (Fin h → Bool) → ι → A) : Prop :=
  ∀ c : β → ι → A, (∀ b, c b ∈ C) →
    a ≤ (familyAgreementSet c fun b ↦ binaryTensorFold r (u b)).card →
    ∃ leafCode : β → (Fin h → Bool) → ι → A, (∀ b leaf, leafCode b leaf ∈ C) ∧
      (∀ b, c b = binaryTensorFold r (leafCode b)) ∧
      familyAgreementSet c (fun b ↦ binaryTensorFold r (u b)) =
        Finset.univ.filter fun i ↦ ∀ b leaf, leafCode b leaf i = u b leaf i

end Definitions

section TensorGenerator

variable {ι F A : Type} [Field F] [AddCommMonoid A] [Module F A]

/-- The binary tensor fold is the combination of the leaves under the iterated tensor generator
`PolynomialGenIsMCA.tensorGeneratorPi` of `h` copies of `binaryEqualityGenerator`: the weight of
a leaf is the product over levels of `r j` or `1 - r j` according to its bit at level `j`. -/
theorem binaryTensorFold_eq_tensorGeneratorPi : ∀ {h : ℕ} (r : Fin h → F)
    (u : (Fin h → Bool) → ι → A), binaryTensorFold r u = fun i ↦
      ∑ leaf, PolynomialGenIsMCA.tensorGeneratorPi (fun _ ↦ binaryEqualityGenerator) r leaf •
        u leaf i := by
  intro h
  induction h with
  | zero =>
      intro r u
      funext i
      change u default i = ∑ leaf : Fin 0 → Bool,
        (∏ j : Fin 0, binaryEqualityGenerator (r j) (leaf j)) • u leaf i
      rw [Finset.univ_unique, Finset.sum_singleton, Finset.univ_eq_empty, Finset.prod_empty,
        one_smul]
      exact congrArg (fun leaf ↦ u leaf i) (Subsingleton.elim _ _)
  | succ h ih =>
      intro r u
      funext i
      rw [binaryTensorFold]
      simp only [binaryLineFold, ih]
      rw [Finset.smul_sum, Finset.smul_sum]
      let e := Fin.consEquiv (fun _ : Fin (h + 1) ↦ Bool)
      have he (b : Bool) (tail : Fin h → Bool) : e (b, tail) = Fin.cons b tail := rfl
      rw [← e.sum_comp (fun leaf ↦
        PolynomialGenIsMCA.tensorGeneratorPi (fun _ ↦ binaryEqualityGenerator) r leaf • u leaf i)]
      rw [Fintype.sum_prod_type, Fintype.sum_bool]
      simp only [PolynomialGenIsMCA.tensorGeneratorPi, binaryEqualityGenerator, Fin.tail,
        Fin.prod_univ_succ, Fin.cons_zero, ↓reduceIte, Fin.cons_succ, he, mul_smul,
        Bool.false_eq_true]
      rw [add_comm]

end TensorGenerator

section LevelWitness

variable {ι F A : Type*} [Ring F] [AddCommMonoid A] [Module F A] [Fintype ι] [DecidableEq ι]
  [DecidableEq A] {C : ModuleCode ι F A} {a e : ℕ}

/-- **Uniform exact agreement for all interleavings gives a full-set level witness.** If for
every finite type `β` and every pair of families `U : Bool → ι → β → A` over `C ^⋈ β`, the binary
line under `binaryEqualityGenerator` has a uniform exact-agreement guarantee with count `e`, then
`C` has a full-set level witness with count `e`.

A family `c : β → ι → A` of codewords of `C` is one codeword `i ↦ (c · i)` of `C ^⋈ β`, and its
common agreement set is that codeword's agreement set; the exact-agreement witnesses of the
interleaved codeword are the two child families. No hypothesis on `C` is needed. -/
theorem fullSetLevelWitness_of_forall_uniformExactAgreement
    (h : ∀ (β : Type) [Fintype β] (U : Bool → ι → β → A),
      UniformExactAgreement binaryEqualityGenerator (C^⋈β) a e U) :
    FullSetLevelWitness C a e := by
  intro β _ u₀ u₁
  obtain ⟨bad, hcard, hgood⟩ := h β fun b i x ↦ (if b then u₁ else u₀) x i
  refine ⟨bad, hcard, fun r hr c hc hagree ↦ ?_⟩
  obtain ⟨c', hc', hcsum, hiff⟩ := hgood r hr (fun i x ↦ c x i) (fun x ↦ hc x) _ hagree
    fun i hi ↦ by
      funext x
      simpa [binaryLineFold, binaryEqualityGenerator, add_comm] using
        (mem_familyAgreementSet _ _ i).mp hi x
  refine ⟨fun x i ↦ c' false i x, fun x i ↦ c' true i x, fun x ↦ hc' false x,
    fun x ↦ hc' true x, fun x ↦ funext fun i ↦ ?_, ?_⟩
  · simpa [binaryLineFold, binaryEqualityGenerator, add_comm] using congrFun (congrFun hcsum i) x
  · ext i
    simpa [binaryLineFold, binaryEqualityGenerator, funext_iff, Bool.forall_bool, add_comm]
      using hiff i

/-- **A full-set level witness gives uniform exact agreement for every line.** The case of a
one-member family: outside the level's exceptional set, a codeword with `a` agreements with the
fold `binaryLineFold r (V false) (V true)` has exact agreement for `binaryEqualityGenerator`. No
hypothesis on `C` is needed. -/
theorem uniformExactAgreement_of_fullSetLevelWitness (h : FullSetLevelWitness C a e)
    (V : Bool → ι → A) : UniformExactAgreement binaryEqualityGenerator C a e V := by
  obtain ⟨bad, hcard, hgood⟩ := h Unit (fun _ ↦ V false) (fun _ ↦ V true)
  refine ⟨bad, hcard, fun r hr c hc T hT hcT ↦ ?_⟩
  have hsub : T ⊆ familyAgreementSet (fun _ : Unit ↦ c)
      (fun _ ↦ binaryLineFold r (V false) (V true)) := fun i hi ↦ by
    simp [hcT i hi, binaryLineFold_eq_sum]
  obtain ⟨c₀, c₁, hc₀, hc₁, hceq, hset⟩ := hgood r hr (fun _ ↦ c) (fun _ ↦ hc)
    (hT.trans (Finset.card_le_card hsub))
  refine ⟨fun b ↦ if b then c₁ () else c₀ (), fun b ↦ by cases b <;> simp [hc₀, hc₁], ?_,
    fun i ↦ ?_⟩
  · rw [hceq ()]
    funext i
    simp [binaryLineFold, binaryEqualityGenerator, add_comm]
  · have hi := congrArg (i ∈ ·) hset
    simp only [mem_familyAgreementSet, Finset.mem_inter, eq_iff_iff] at hi
    simp only [Fintype.sum_bool, binaryEqualityGenerator, ite_true, Bool.forall_bool,
      Bool.false_eq_true, ite_false]
    simpa [binaryLineFold, add_comm, Unique.forall_iff] using hi

/-- **A level witness passes to interleavings.** A full-set level witness for `C` with count `e`
is one for `C ^⋈ κ` with the same count, for every finite row type `κ`.

A family indexed by `β` over `C ^⋈ κ` is a family indexed by `β × κ` over `C`, with the same
common agreement set; the witness for `C` is applied to that family. No hypothesis on `C` and no
positive row count is needed. -/
theorem FullSetLevelWitness.moduleInterleavedCode {κ : Type} [Fintype κ]
    (h : FullSetLevelWitness C a e) : FullSetLevelWitness (C^⋈κ) a e := by
  intro β _ u₀ u₁
  let pack (u : β → ι → κ → A) : β × κ → ι → A := fun p i ↦ u p.1 i p.2
  have hpack (c v : β → ι → κ → A) :
      familyAgreementSet c v = familyAgreementSet (pack c) (pack v) := by
    ext i
    simp only [mem_familyAgreementSet, funext_iff, Prod.forall, pack]
  obtain ⟨bad, hcard, hgood⟩ := h (β × κ) (pack u₀) (pack u₁)
  refine ⟨bad, hcard, fun r hr c hc hagree ↦ ?_⟩
  have hfold : pack (fun b ↦ binaryLineFold r (u₀ b) (u₁ b)) =
      fun p ↦ binaryLineFold r (pack u₀ p) (pack u₁ p) := rfl
  rw [hpack, hfold] at hagree
  obtain ⟨d₀, d₁, hd₀, hd₁, hdeq, hset⟩ := hgood r hr (pack c) (fun p ↦ hc p.1 p.2) hagree
  refine ⟨fun b i x ↦ d₀ (b, x) i, fun b i x ↦ d₁ (b, x) i, fun b x ↦ hd₀ (b, x),
    fun b x ↦ hd₁ (b, x), fun b ↦ funext fun i ↦ funext fun x ↦ congrFun (hdeq (b, x)) i, ?_⟩
  rw [hpack, hfold, hset, hpack (fun b i x ↦ d₀ (b, x) i), hpack (fun b i x ↦ d₁ (b, x) i)]

end LevelWitness

section Transfer

variable {ι F A : Type*} [Field F] [AddCommMonoid A] [Module F A] [Fintype ι] [DecidableEq ι]
  [DecidableEq A] {C : ModuleCode ι F A} {a e : ℕ}

/-- **Exact line agreement gives a full-set level witness.** Let the codewords of `C` be
determined by `a` agreements, and let every binary line over `C` have a uniform exact-agreement
guarantee for `binaryEqualityGenerator` with at most `e` exceptional challenges. Then `C` has a
full-set level witness with count `e`: one exceptional set of the same size serves every finite
family at once.

The family case is the line case for `C ^⋈ β`, which the interleaving transfer
`Code.uniformExactAgreement_moduleInterleavedCode` provides with the same count, because the
seed space `F` has at most `|F|` elements. `hC` is used by that transfer to turn the count of
projection-bad challenges back into exact agreement. -/
theorem fullSetLevelWitness_of_uniformExactAgreement (hC : DeterminedByAgreement C a)
    (hline : ∀ V : Bool → ι → A, UniformExactAgreement binaryEqualityGenerator C a e V) :
    FullSetLevelWitness C a e :=
  fullSetLevelWitness_of_forall_uniformExactAgreement fun _ _ U ↦
    uniformExactAgreement_moduleInterleavedCode _ C a (Or.inl le_rfl) hC hline U

/-- **A full-set level witness is exact line agreement.** For a code determined by `a`
agreements, a full-set level witness with count `e` exists exactly when every binary line has a
uniform exact-agreement guarantee with count `e`. The quantification over all finite families
in `FullSetLevelWitness` therefore adds nothing beyond the single-line guarantee. -/
theorem fullSetLevelWitness_iff (hC : DeterminedByAgreement C a) :
    FullSetLevelWitness C a e ↔
      ∀ V : Bool → ι → A, UniformExactAgreement binaryEqualityGenerator C a e V :=
  ⟨uniformExactAgreement_of_fullSetLevelWitness, fullSetLevelWitness_of_uniformExactAgreement hC⟩

end Transfer

section LineChange

variable {ι : Type*} {F A : Type} [Field F] [AddCommGroup A] [Module F A]

/-- **Changing the line parametrization.** Over an additive group `A`, a challenge `r` is
projection-bad for the family `V` under `binaryEqualityGenerator` exactly when it is
projection-bad for `(V false, V true - V false)` under the affine line generator `r ↦ (1, r)`.

The two combined words are equal, `(1 - r) • u₀ + r • u₁ = u₀ + r • (u₁ - u₀)`, and on every
coordinate set, `u₀` and `u₁` both project into the code exactly when `u₀` and `u₁ - u₀` do,
since the projected code is a submodule. -/
theorem isProjectionBad_binaryEqualityGenerator_iff {C : ModuleCode ι F A} {a : ℕ} {r : F}
    (V : Bool → ι → A) :
    IsProjectionBad binaryEqualityGenerator C a r V ↔
      IsProjectionBad (AffineLineGenerator F) C a r ![V false, V true - V false] := by
  have hword : (fun i ↦ ∑ b, binaryEqualityGenerator r b • V b i) =
      fun i ↦ ∑ j, AffineLineGenerator F r j • ![V false, V true - V false] j i := by
    funext i
    simp [binaryEqualityGenerator, Fin.sum_univ_two, sub_smul, smul_sub]
    abel
  have hmem (T : Finset ι) :
      (∃ b, projectedWord (V b) T ∉ projectedCodeSubmod C T) ↔
        ∃ j, projectedWord (![V false, V true - V false] j) T ∉ projectedCodeSubmod C T := by
    have hsub : projectedWord (V true - V false) T =
        projectedWord (V true) T - projectedWord (V false) T := rfl
    simp only [← not_forall, Bool.forall_bool, Fin.forall_fin_two, Matrix.cons_val_zero,
      Matrix.cons_val_one, hsub, not_iff_not]
    constructor
    · rintro ⟨h0, h1⟩
      exact ⟨h0, Submodule.sub_mem _ h1 h0⟩
    · rintro ⟨h0, h1⟩
      exact ⟨h0, by simpa using Submodule.add_mem _ h1 h0⟩
  simp only [IsProjectionBad, hword, hmem]

end LineChange

section Count

variable {ι F A : Type*} [Ring F] [AddCommMonoid A] [Module F A] [Fintype ι] [DecidableEq ι]
  [DecidableEq A] {C : ModuleCode ι F A} {a e : ℕ}

/-- A chosen exceptional set of the level witness `hlevel` for the child families `u₀ u₁`. -/
noncomputable def levelExceptional (hlevel : FullSetLevelWitness C a e) {β : Type} [Fintype β]
    (u₀ u₁ : β → ι → A) : Finset F :=
  Classical.choose (hlevel β u₀ u₁)

/-- The chosen exceptional set has at most `e` elements. -/
theorem levelExceptional_card_le (hlevel : FullSetLevelWitness C a e) {β : Type} [Fintype β]
    (u₀ u₁ : β → ι → A) : (levelExceptional hlevel u₀ u₁).card ≤ e :=
  (Classical.choose_spec (hlevel β u₀ u₁)).1

/-- Outside the chosen exceptional set, every close codeword family opens into two child
codeword families with the same common agreement set. -/
theorem levelExceptional_good (hlevel : FullSetLevelWitness C a e) {β : Type} [Fintype β]
    (u₀ u₁ : β → ι → A) {r : F} (hr : r ∉ levelExceptional hlevel u₀ u₁) {c : β → ι → A}
    (hc : ∀ b, c b ∈ C)
    (hagree : a ≤ (familyAgreementSet c fun b ↦ binaryLineFold r (u₀ b) (u₁ b)).card) :
    ∃ c₀ c₁ : β → ι → A, (∀ b, c₀ b ∈ C) ∧ (∀ b, c₁ b ∈ C) ∧
      (∀ b, c b = binaryLineFold r (c₀ b) (c₁ b)) ∧
      familyAgreementSet c (fun b ↦ binaryLineFold r (u₀ b) (u₁ b)) =
        familyAgreementSet c₀ u₀ ∩ familyAgreementSet c₁ u₁ :=
  (Classical.choose_spec (hlevel β u₀ u₁)).2 r hr c hc hagree

/-- **The levelwise good event** for a family `u` of height-`h` leaf arrays. At the root, the
challenge `r 0` avoids the chosen exceptional set of the two child families, which are folds of
the later challenges only; recursively, the good event holds for the family indexed by `β × Bool`
of the two halves of every leaf array, at the tail challenges. -/
def TensorFoldFamilyGood (hlevel : FullSetLevelWitness C a e) :
    {β : Type} → [Fintype β] → ∀ {h : ℕ}, (Fin h → F) → (β → (Fin h → Bool) → ι → A) → Prop
  | _, _, 0, _, _ => True
  | β, _, _ + 1, r, u =>
      let u₀ := fun b leaf ↦ u b (Fin.cons false leaf)
      let u₁ := fun b leaf ↦ u b (Fin.cons true leaf)
      r 0 ∉ levelExceptional hlevel (fun b ↦ binaryTensorFold (Fin.tail r) (u₀ b))
          (fun b ↦ binaryTensorFold (Fin.tail r) (u₁ b)) ∧
        TensorFoldFamilyGood hlevel (β := β × Bool) (Fin.tail r)
          (fun p leaf ↦ if p.2 then u₁ p.1 leaf else u₀ p.1 leaf)

/-- The levelwise good event for a single leaf array. -/
def TensorFoldGood (hlevel : FullSetLevelWitness C a e) {h : ℕ} (r : Fin h → F)
    (u : (Fin h → Bool) → ι → A) : Prop :=
  TensorFoldFamilyGood hlevel (β := Unit) r (fun _ ↦ u)

/-- **The good event gives a full family decomposition.** By induction on the height: the root
level opens every member of the family, and the resulting family of children, indexed by
`β × Bool`, has the same common agreement set, so the induction hypothesis applies to it. -/
theorem hasFullTensorFamilyDecomposition_of_good (hlevel : FullSetLevelWitness C a e) {h : ℕ}
    {β : Type} [Fintype β] (r : Fin h → F) (u : β → (Fin h → Bool) → ι → A)
    (hgood : TensorFoldFamilyGood hlevel r u) : HasFullTensorFamilyDecomposition C a r u := by
  induction h generalizing β with
  | zero =>
      intro c hc _
      refine ⟨fun b _ ↦ c b, fun b _ ↦ hc b, fun _ ↦ rfl, ?_⟩
      ext i
      simp only [mem_familyAgreementSet, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨fun hi b leaf ↦ Subsingleton.elim leaf default ▸ hi b, fun hi b ↦ hi b default⟩
  | succ h ih =>
      intro c hc hagree
      obtain ⟨hroot, hrest⟩ := hgood
      let u₀ : β → (Fin h → Bool) → ι → A := fun b leaf ↦ u b (Fin.cons false leaf)
      let u₁ : β → (Fin h → Bool) → ι → A := fun b leaf ↦ u b (Fin.cons true leaf)
      let w₀ : β → ι → A := fun b ↦ binaryTensorFold (Fin.tail r) (u₀ b)
      let w₁ : β → ι → A := fun b ↦ binaryTensorFold (Fin.tail r) (u₁ b)
      obtain ⟨c₀, c₁, hc₀, hc₁, hcroot, hagreeRoot⟩ :=
        levelExceptional_good hlevel w₀ w₁ hroot hc hagree
      let c' : β × Bool → ι → A := fun p ↦ if p.2 then c₁ p.1 else c₀ p.1
      let u' : β × Bool → (Fin h → Bool) → ι → A := fun p leaf ↦
        if p.2 then u₁ p.1 leaf else u₀ p.1 leaf
      have hexpand : familyAgreementSet c' (fun p ↦ binaryTensorFold (Fin.tail r) (u' p)) =
          familyAgreementSet c₀ w₀ ∩ familyAgreementSet c₁ w₁ := by
        ext i
        simp only [mem_familyAgreementSet, Finset.mem_inter, Prod.forall, Bool.forall_bool, c',
          u', w₀, w₁, ite_true, Bool.false_eq_true, ite_false]
        exact ⟨fun hi ↦ ⟨fun b ↦ (hi b).1, fun b ↦ (hi b).2⟩,
          fun hi b ↦ ⟨hi.1 b, hi.2 b⟩⟩
      have hagree' : a ≤
          (familyAgreementSet c' fun p ↦ binaryTensorFold (Fin.tail r) (u' p)).card := by
        rw [hexpand, ← hagreeRoot]
        exact hagree
      have hc' : ∀ p, c' p ∈ C := by
        rintro ⟨b, _ | _⟩
        · exact hc₀ b
        · exact hc₁ b
      obtain ⟨leaf', hleaf', hc'eq, hagree'eq⟩ := ih (Fin.tail r) u' hrest c' hc' hagree'
      let leafCode : β → (Fin (h + 1) → Bool) → ι → A := fun b leaf ↦
        leaf' (b, leaf 0) (Fin.tail leaf)
      refine ⟨leafCode, fun b leaf ↦ hleaf' _ _, fun b ↦ ?_, ?_⟩
      · rw [hcroot b]
        exact congrArg₂ (binaryLineFold (r 0)) (hc'eq (b, false)) (hc'eq (b, true))
      · change familyAgreementSet c (fun b ↦ binaryLineFold (r 0) (w₀ b) (w₁ b)) = _
        rw [hagreeRoot, ← hexpand, hagree'eq]
        ext i
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · intro hall b leaf
          have key : u' (b, leaf 0) (Fin.tail leaf) = u b leaf := by
            conv_rhs => rw [← Fin.cons_self_tail leaf]
            cases leaf 0 <;> rfl
          exact (hall (b, leaf 0) (Fin.tail leaf)).trans (congrFun key i)
        · rintro hall ⟨b, _ | _⟩ leaf
          · simpa [leafCode, u'] using hall b (Fin.cons false leaf)
          · simpa [leafCode, u'] using hall b (Fin.cons true leaf)

/-- **Avoiding every level's exceptional set gives a full tensor decomposition.** The single-array
case of `hasFullTensorFamilyDecomposition_of_good`. -/
theorem hasFullTensorDecomposition_of_good (hlevel : FullSetLevelWitness C a e) {h : ℕ}
    (r : Fin h → F) (u : (Fin h → Bool) → ι → A) (hgood : TensorFoldGood hlevel r u) :
    HasFullTensorDecomposition C a r u := by
  intro c hc hagree
  have hset : familyAgreementSet (fun _ : Unit ↦ c) (fun _ ↦ binaryTensorFold r u) =
      fullAgreementSet c (binaryTensorFold r u) := by
    ext i
    simp
  obtain ⟨leaf, hleaf, hceq, hagreeEq⟩ := hasFullTensorFamilyDecomposition_of_good hlevel r
    (fun _ : Unit ↦ u) hgood (fun _ ↦ c) (fun _ ↦ hc) (hset ▸ hagree)
  refine ⟨leaf (), hleaf (), hceq (), ?_⟩
  rw [← hset, hagreeEq]
  ext i
  simp [Unique.forall_iff]

omit [Ring F] in
private theorem card_filter_fin_cons [Fintype F] (n : ℕ) (P : (Fin (n + 1) → F) → Prop)
    [DecidablePred P] :
    (Finset.univ.filter P).card =
      ∑ tail : Fin n → F, (Finset.univ.filter fun x : F ↦ P (Fin.cons x tail)).card := by
  rw [Finset.card_filter, ← (Fin.consEquiv fun _ : Fin (n + 1) ↦ F).sum_comp,
    Fintype.sum_prod_type, Finset.sum_comm]
  simp only [Finset.card_filter]
  rfl

private theorem levelFoldBound_succ (q e h : ℕ) :
    q ^ h * e + q * (h * e * q ^ (h - 1)) ≤ (h + 1) * e * q ^ h := by
  cases h with
  | zero => simp
  | succ h =>
      simp only [Nat.succ_sub_one, Nat.pow_succ]
      ring_nf
      exact le_rfl

/-- The challenge tuples at which the levelwise good event fails for the family `u`. -/
noncomputable def tensorFoldFamilyBad [Fintype F] (hlevel : FullSetLevelWitness C a e) {h : ℕ}
    {β : Type} [Fintype β] (u : β → (Fin h → Bool) → ι → A) : Finset (Fin h → F) := by
  classical
  exact Finset.univ.filter fun r ↦ ¬ TensorFoldFamilyGood hlevel r u

/-- The challenge tuples at which some level of the fold of `u` is exceptional. -/
noncomputable def tensorFoldBad [Fintype F] (hlevel : FullSetLevelWitness C a e) {h : ℕ}
    (u : (Fin h → Bool) → ι → A) : Finset (Fin h → F) :=
  tensorFoldFamilyBad hlevel (fun _ : Unit ↦ u)

/-- **Counting bad challenge tuples for a family.** At most `h * e * |F| ^ (h - 1)` challenge
tuples are bad for a height-`h` family fold.

Fix the tail challenges. The root challenge is bad only if it lies in one exceptional set of at
most `e` elements, which depends on the tail only, or if the tail is bad for the family of
children. Summing over tails gives `|F| ^ h * e + |F| * (h * e * |F| ^ (h - 1))`, which is the
bound at height `h + 1`. -/
theorem tensorFoldFamilyBad_card_le [Fintype F] (hlevel : FullSetLevelWitness C a e) {h : ℕ}
    {β : Type} [Fintype β] (u : β → (Fin h → Bool) → ι → A) :
    (tensorFoldFamilyBad hlevel u).card ≤ h * e * Fintype.card F ^ (h - 1) := by
  classical
  induction h generalizing β with
  | zero => simp [tensorFoldFamilyBad, TensorFoldFamilyGood]
  | succ h ih =>
      let u₀ : β → (Fin h → Bool) → ι → A := fun b leaf ↦ u b (Fin.cons false leaf)
      let u₁ : β → (Fin h → Bool) → ι → A := fun b leaf ↦ u b (Fin.cons true leaf)
      let u' : β × Bool → (Fin h → Bool) → ι → A := fun p leaf ↦
        if p.2 then u₁ p.1 leaf else u₀ p.1 leaf
      let childBad : (Fin h → F) → Prop := fun tail ↦ ¬ TensorFoldFamilyGood hlevel tail u'
      rw [tensorFoldFamilyBad, card_filter_fin_cons]
      have hpoint (tail : Fin h → F) :
          (Finset.univ.filter fun x : F ↦
              ¬ TensorFoldFamilyGood hlevel (Fin.cons x tail) u).card ≤
            e + if childBad tail then Fintype.card F else 0 := by
        let E := levelExceptional hlevel (fun b ↦ binaryTensorFold tail (u₀ b))
          (fun b ↦ binaryTensorFold tail (u₁ b))
        have hsub : (Finset.univ.filter fun x : F ↦
            ¬ TensorFoldFamilyGood hlevel (Fin.cons x tail) u) ⊆
              E ∪ Finset.univ.filter fun _ : F ↦ childBad tail := by
          intro x hx
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, TensorFoldFamilyGood,
            Fin.tail_cons, Fin.cons_zero, not_and_or, not_not] at hx
          rw [Finset.mem_union, Finset.mem_filter]
          exact hx.imp id fun hx ↦ ⟨Finset.mem_univ _, hx⟩
        refine (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans ?_)
        refine Nat.add_le_add (levelExceptional_card_le hlevel _ _) ?_
        split_ifs with htail <;> simp [htail]
      calc
        _ ≤ ∑ tail : Fin h → F, (e + if childBad tail then Fintype.card F else 0) :=
          Finset.sum_le_sum fun tail _ ↦ hpoint tail
        _ = Fintype.card F ^ h * e +
              Fintype.card F * (Finset.univ.filter childBad).card := by
          rw [Finset.sum_add_distrib, Finset.sum_ite, Finset.sum_const_zero, add_zero,
            Finset.sum_const, Finset.sum_const, Finset.card_univ, Fintype.card_fun,
            Fintype.card_fin, smul_eq_mul, smul_eq_mul]
          ring
        _ ≤ Fintype.card F ^ h * e + Fintype.card F * (h * e * Fintype.card F ^ (h - 1)) :=
          Nat.add_le_add_left (Nat.mul_le_mul_left _ (by simpa [tensorFoldFamilyBad] using ih u'))
            _
        _ ≤ (h + 1) * e * Fintype.card F ^ h := levelFoldBound_succ _ e h

/-- **Shared-level union bound.** A height-`h` fold with a full-set level witness of count `e` has
at most `h * e * |F| ^ (h - 1)` bad challenge tuples: each of the `h` levels contributes `e`
values of its own challenge, for every choice of the other `h - 1` challenges, independently of
the number of words opened at that level. At height `0` the bad set is empty. Outside the bad
set, `hasFullTensorDecomposition_of_not_mem_bad` gives the leaf decomposition. -/
theorem tensorFoldBad_card_le [Fintype F] (hlevel : FullSetLevelWitness C a e) {h : ℕ}
    (u : (Fin h → Bool) → ι → A) :
    (tensorFoldBad hlevel u).card ≤ h * e * Fintype.card F ^ (h - 1) :=
  tensorFoldFamilyBad_card_le hlevel _

/-- A height-zero fold has no bad challenge tuple. -/
theorem tensorFoldBad_eq_empty_height_zero [Fintype F] (hlevel : FullSetLevelWitness C a e)
    (u : (Fin 0 → Bool) → ι → A) : tensorFoldBad hlevel u = ∅ :=
  Finset.card_eq_zero.mp (by simpa using tensorFoldBad_card_le hlevel u)

/-- **Outside the bad set, the fold decomposes.** Every challenge tuple outside
`tensorFoldBad hlevel u` has a full tensor decomposition for `u`. -/
theorem hasFullTensorDecomposition_of_not_mem_bad [Fintype F] (hlevel : FullSetLevelWitness C a e)
    {h : ℕ} (r : Fin h → F) (u : (Fin h → Bool) → ι → A) (hr : r ∉ tensorFoldBad hlevel u) :
    HasFullTensorDecomposition C a r u :=
  hasFullTensorDecomposition_of_good hlevel r u <| by
    simpa [tensorFoldBad, tensorFoldFamilyBad, TensorFoldGood] using hr

end Count

end TensorMCA

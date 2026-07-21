/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

import ArkLib.Data.CodingTheory.ListDecodability
import ArkLib.Data.CodingTheory.InterleavedCode
import Mathlib.LinearAlgebra.Basis.Defs

/-!
# Extension fields and extension codes (ABF26 §2.6)

Definitions and one lemma (proved in-tree) from ABF26 §2.6 (Arnon-Boneh-Fenzi,
*Open Problems in List Decoding and Correlated Agreement*, 2026, page 11):
extension-field presentations, extension codes obtained by base-change, and the
relation `|Λ(C_F, δ)| = |Λ(C_B^e, δ)|` between the list size of an extension code
and the list size of the corresponding interleaved base code.

## Main definitions

- `ExtensionFieldPresentation` (D2.19): a thin wrapper around Mathlib's
  `[Algebra B F]` + a finite `B`-basis `basis : Basis (Fin e) B F` of `F`.
  All the paper's structure (`ψ : B ↪ F`, `φ : F ≃ B^e`, the coordinate maps,
  and the systematic property) is derived from these two ingredients —
  no parallel implementation.
- `CodingTheory.extensionCode` (D2.20): the extension code `C_F : F^k → F^n`
  obtained from a `B`-linear code `C_B : B^k → B^n` via an `ExtensionFieldPresentation`.

## Main statements

- `extensionCode_add_mem`, `extensionCode_smul_mem` — closure of
  `extensionCode P C_B` under addition and `F`-scalar multiplication (when
  `C_B` is `B`-linear). Together they package `extensionCode P C_B` as a
  full `F`-`Submodule` (B-linear closure was always present; the F-scalar
  closure is what the structural refactor delivers).
- `lambda_extensionCode_eq_lambda_interleaved` (L2.21, [BuenzCFW25 Lem D.3]):
  `|Λ(C_F, δ)| = |Λ(C_B^≡e, δ)|`. Proved in-tree via the coordinate Hamming isometry.

## References

- [ABF26] Arnon-Boneh-Fenzi. *Open Problems in List Decoding and Correlated Agreement*.
  2026.
- [BuenzCFW25] Bünz-Chiesa-Fenzi-Wang. Lemma D.3.

(The distance equality `δ_min(C_F) = δ_min(C_B)`, referenced in the L2.21 paragraph
context, is from Diamond-Posen [DiamondP23, Theorem 3.2].)
-/

set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

namespace CodingTheory

open scoped NNReal
open ListDecodable Module

/-- **ABF26 Definition 2.19.** An *extension field presentation* is the data of
a finite `B`-basis of `F`, in the presence of a `B`-algebra structure on `F`:

- `B` and `F` are fields,
- `[Algebra B F]` provides the embedding `ψ := algebraMap B F : B →+* F` and the
  `B`-module structure on `F`,
- `e : ℕ` is the dimension of `F` as a `B`-vector space,
- `basis : Basis (Fin e) B F` witnesses the `B`-linear isomorphism
  `F ≃ₗ[B] (Fin e → B)` (via `basis.equivFun`).

This is a thin structure on top of Mathlib's existing `Algebra` / `Basis`
machinery. The paper's named maps `ψ` and `φ` are derived (not duplicated):
`ψ := algebraMap B F` and `φ := basis.equivFun`. -/
structure ExtensionFieldPresentation (B F : Type) [Field B] [Field F] [Algebra B F] where
  /-- The dimension `e := dim_B F`. -/
  e : ℕ
  /-- The `B`-basis of `F` indexed by `Fin e`. -/
  basis : Basis (Fin e) B F

namespace ExtensionFieldPresentation

variable {B F : Type} [Field B] [Field F] [Algebra B F]

/-- The base-field embedding `ψ : B ↪ F`, derived from `[Algebra B F]`. -/
@[reducible]
def ψ (_P : ExtensionFieldPresentation B F) : B →+* F := algebraMap B F

/-- Injectivity of `ψ` — automatic since the algebra map between fields is
always injective. -/
lemma ψ_injective (P : ExtensionFieldPresentation B F) : Function.Injective P.ψ :=
  FaithfulSMul.algebraMap_injective B F

/-- The `B`-linear coordinate isomorphism `φ : F ≃ₗ[B] (Fin e → B)`, derived
from the basis. -/
noncomputable def φ (P : ExtensionFieldPresentation B F) : F ≃ₗ[B] (Fin P.e → B) :=
  P.basis.equivFun

/-- The `j`-th coordinate `φᵢ : F →ₗ[B] B` of an extension-field presentation,
as a `B`-linear map. -/
noncomputable def coord (P : ExtensionFieldPresentation B F) (j : Fin P.e) : F →ₗ[B] B :=
  LinearMap.proj (R := B) (φ := fun _ : Fin P.e ↦ B) j ∘ₗ (P.φ : F →ₗ[B] (Fin P.e → B))

/-- A presentation is *systematic* if `φ(ψ(x)) = (x, 0, …, 0)` for every `x : B`.
This makes the base-field copy of `B` inside `F` align with the first coordinate. -/
def IsSystematic (P : ExtensionFieldPresentation B F) : Prop :=
  ∀ x : B, P.φ (P.ψ x) = fun i ↦ if i.val = 0 then x else 0

/-- Each coordinate `P.coord j` is additive — direct consequence of being a
`LinearMap`. -/
lemma coord_add (P : ExtensionFieldPresentation B F) (j : Fin P.e) (x y : F) :
    P.coord j (x + y) = P.coord j x + P.coord j y :=
  (P.coord j).map_add x y

/-- Each coordinate `P.coord j` respects the `B`-action — direct consequence of
being a `B`-linear map. The `algebraMap`-based smul (`ψ b * x = b • x`) folds
into ordinary `B`-scalar multiplication via `Algebra.smul_def`. -/
lemma coord_psi_smul (P : ExtensionFieldPresentation B F)
    (j : Fin P.e) (b : B) (x : F) :
    P.coord j (P.ψ b * x) = b * P.coord j x := by
  change P.coord j ((algebraMap B F) b * x) = b * P.coord j x
  rw [← Algebra.smul_def, (P.coord j).map_smul, smul_eq_mul]

end ExtensionFieldPresentation

/-- **ABF26 Definition 2.20.** The *extension code* `C_F : F^k → F^n` associated
to a linear code `C_B : B^k → B^n` via an extension-field presentation. Defined
on a vector `v : ι → F` by

  `v ∈ C_F ↔ ∀ j : Fin e, (fun i ↦ P.coord j (v i)) ∈ C_B`

i.e. each of the `e` coordinate-projections of `v` lies in `C_B`.

**Closure properties.** With `[Algebra B F]` + `Basis (Fin e) B F` from the
refactored `ExtensionFieldPresentation`, `extensionCode P C_B` is closed under
**both** addition (when `C_B` is) and `F`-scalar multiplication (when `C_B` is
`B`-linear). See `extensionCode_add_mem` and `extensionCode_smul_mem` below. -/
def extensionCode {ι : Type} [Fintype ι]
    {B F : Type} [Field B] [Field F] [Algebra B F]
    (P : ExtensionFieldPresentation B F)
    (C_B : Set (ι → B)) : Set (ι → F) :=
  { v : ι → F | ∀ j : Fin P.e, (fun i ↦ P.coord j (v i)) ∈ C_B }

/-- **Bridge to paper's encoder-image view.** A vector `v : ι → F` is in
`extensionCode P C_B` iff each of its `e` coordinate-projections lies in `C_B`. -/
lemma extensionCode_iff_coord_in_base
    {ι : Type} [Fintype ι]
    {B F : Type} [Field B] [Field F] [Algebra B F]
    (P : ExtensionFieldPresentation B F)
    (C_B : Set (ι → B)) (v : ι → F) :
    v ∈ extensionCode P C_B ↔
      ∀ j : Fin P.e, (fun i ↦ P.coord j (v i)) ∈ C_B := by
  rfl

/-- **`extensionCode` is closed under addition** when `C_B` is. Uses
`LinearMap.map_add` of the coordinate maps. -/
lemma extensionCode_add_mem
    {ι : Type} [Fintype ι]
    {B F : Type} [Field B] [Field F] [Algebra B F]
    (P : ExtensionFieldPresentation B F)
    {C_B : Set (ι → B)}
    (hadd : ∀ {a b : ι → B}, a ∈ C_B → b ∈ C_B → a + b ∈ C_B)
    {u v : ι → F} (hu : u ∈ extensionCode P C_B) (hv : v ∈ extensionCode P C_B) :
    u + v ∈ extensionCode P C_B := by
  intro j
  have h := hadd (hu j) (hv j)
  have hpt : (fun i ↦ P.coord j ((u + v) i)) =
      (fun i ↦ P.coord j (u i)) + fun i ↦ P.coord j (v i) := by
    ext i
    exact P.coord_add j (u i) (v i)
  rw [hpt]
  exact h

/-- **`extensionCode` is closed under the `ψ`-induced `B`-scalar action** when
`C_B` is `B`-scalar closed. Uses `LinearMap.map_smul` of the coordinate maps. -/
lemma extensionCode_psi_smul_mem
    {ι : Type} [Fintype ι]
    {B F : Type} [Field B] [Field F] [Algebra B F]
    (P : ExtensionFieldPresentation B F)
    {C_B : Set (ι → B)}
    (hsmul : ∀ (b : B) {a : ι → B}, a ∈ C_B → b • a ∈ C_B)
    (b : B) {v : ι → F} (hv : v ∈ extensionCode P C_B) :
    (fun i ↦ P.ψ b * v i) ∈ extensionCode P C_B := by
  intro j
  have h := hsmul b (hv j)
  have hpt : (fun i ↦ P.coord j (P.ψ b * v i)) = b • fun i ↦ P.coord j (v i) := by
    ext i
    simpa [Pi.smul_apply, smul_eq_mul] using P.coord_psi_smul j b (v i)
  rw [hpt]
  exact h

/-- **F-scalar closure of `extensionCode`** — the paper's D2.20 F-linearity
claim, closed via the basis-expansion argument.

**Proof outline.** For `α : F` and `v ∈ extensionCode P C_B`:

  1. Write `α` in the basis: `α = ∑ k, (P.basis.repr α k) • (P.basis k)`
     via `Basis.sum_repr`. The coefficients `c_k := P.basis.repr α k` live in `B`.
  2. Distribute: `α * v i = ∑ k, c_k • (P.basis k * v i)`.
  3. Coordinate-by-coordinate, `P.coord j (α * v i) = ∑ k, c_k * P.coord j (P.basis k * v i)`.
  4. Each `(fun i ↦ P.coord j (P.basis k * v i))` is itself a `B`-linear
     combination of `(fun i ↦ P.coord m (v i))`s (since multiplication by `P.basis k`
     is `B`-linear `F →ₗ[B] F`, and then `P.coord j` is `B`-linear). These
     row-functions live in `C_B` by hypothesis (`v ∈ extensionCode P C_B`).
  5. Closure of `C_B` under (finite) `B`-linear combinations gives the result. -/
lemma extensionCode_smul_mem
    {ι : Type} [Fintype ι]
    {B F : Type} [Field B] [Field F] [Algebra B F]
    (P : ExtensionFieldPresentation B F)
    {C_B : Set (ι → B)}
    (hadd : ∀ {a b : ι → B}, a ∈ C_B → b ∈ C_B → a + b ∈ C_B)
    (hsmul : ∀ (b : B) {a : ι → B}, a ∈ C_B → b • a ∈ C_B)
    (α : F) {v : ι → F} (hv : v ∈ extensionCode P C_B) :
    (fun i ↦ α * v i) ∈ extensionCode P C_B := by
  intro j
  -- Pointwise identity:
  --   coord j (α * v i) = ∑ m, coord m (v i) * coord j (α * basis m)
  have h_pt : ∀ i,
      P.coord j (α * v i) =
        ∑ m : Fin P.e, P.coord m (v i) * P.coord j (α * P.basis m) := by
    intro i
    have h_vi : v i = ∑ m : Fin P.e, P.coord m (v i) • P.basis m :=
      (P.basis.sum_equivFun (v i)).symm
    calc P.coord j (α * v i)
        = P.coord j (α * ∑ m : Fin P.e, P.coord m (v i) • P.basis m) := by
            rw [← h_vi]
      _ = P.coord j (∑ m : Fin P.e, α * (P.coord m (v i) • P.basis m)) := by
            rw [Finset.mul_sum]
      _ = P.coord j (∑ m : Fin P.e, P.coord m (v i) • (α * P.basis m)) := by
            congr 1
            exact Finset.sum_congr rfl fun m _ ↦ mul_smul_comm _ _ _
      _ = ∑ m : Fin P.e, P.coord m (v i) * P.coord j (α * P.basis m) := by
            rw [map_sum]
            exact Finset.sum_congr rfl fun m _ ↦ by
              rw [map_smul, smul_eq_mul]
  -- Pointwise function equality:
  --   (fun i ↦ coord j (α * v i)) =
  --     ∑ m, (coord j (α * basis m)) • (fun i ↦ coord m (v i))
  have h_fun : (fun i ↦ P.coord j (α * v i)) =
      ∑ m : Fin P.e,
        (P.coord j (α * P.basis m)) • (fun i ↦ P.coord m (v i)) := by
    funext i
    rw [h_pt i, Finset.sum_apply]
    exact Finset.sum_congr rfl fun m _ ↦ by
      simp [Pi.smul_apply, smul_eq_mul, mul_comm]
  rw [h_fun]
  -- Show the B-linear combination of (fun i ↦ coord m (v i)) ∈ C_B lies in C_B.
  -- Each summand is in C_B by `hsmul`; iterate via `Finset.sum_induction`.
  -- The empty-sum (e = 0) base needs `0 ∈ C_B`; we get it from `hsmul 0 (hv m₀)`
  -- if `e ≥ 1`, and vacuously otherwise (the goal `∀ j : Fin 0, …` is empty).
  by_cases h_e_zero : P.e = 0
  · -- e = 0 case: the goal is vacuous since `j : Fin 0` doesn't exist.
    exact Fin.elim0 (h_e_zero ▸ j)
  · -- e ≥ 1 case: derive `0 ∈ C_B`, then iterate.
    have h_pos : 0 < P.e := Nat.pos_of_ne_zero h_e_zero
    let m₀ : Fin P.e := ⟨0, h_pos⟩
    have h_zero_mem : (0 : ι → B) ∈ C_B := by
      have h := hsmul 0 (hv m₀)
      simpa using h
    refine Finset.sum_induction _ (· ∈ C_B) (fun a b ha hb ↦ hadd ha hb)
      h_zero_mem ?_
    intros m _
    exact hsmul _ (hv m)

/-- **Submodule-packaging of `extensionCode`** when `C_B` is a `B`-submodule.

Bundles the three closure laws (`add_mem`, `zero_mem`, `smul_mem`) into a
single `Submodule F (ι → F)`, mirroring the `ReedSolomon.code` pattern
(which returns a `Submodule F (ι → F)` directly). Downstream code that
wants to consume an extension code as a linear code should use this
form rather than the raw `Set`-based `extensionCode`.

Built directly from the existing closure lemmas — no parallel
implementation. The `Set`-form `extensionCode` is the carrier. -/
noncomputable def extensionCodeSubmodule
    {ι : Type} [Fintype ι]
    {B F : Type} [Field B] [Field F] [Algebra B F]
    (P : ExtensionFieldPresentation B F)
    (C_B : Submodule B (ι → B)) : Submodule F (ι → F) where
  carrier := extensionCode P (C_B : Set (ι → B))
  add_mem' {u v} hu hv := extensionCode_add_mem P (fun ha hb ↦ C_B.add_mem ha hb) hu hv
  zero_mem' := by
    intro j
    change (fun i ↦ P.coord j ((0 : ι → F) i)) ∈ (C_B : Set (ι → B))
    -- (fun i ↦ P.coord j 0) = (fun i ↦ 0) = 0, which is in C_B by Submodule.zero_mem
    simp only [Pi.zero_apply, (P.coord j).map_zero]
    exact C_B.zero_mem
  smul_mem' c v hv :=
    extensionCode_smul_mem P
      (hadd := fun {a b} (ha : a ∈ C_B) (hb : b ∈ C_B) ↦ C_B.add_mem ha hb)
      (hsmul := fun (b : B) {a : ι → B} (ha : a ∈ C_B) ↦ C_B.smul_mem b ha)
      c hv

/-- The carrier of `extensionCodeSubmodule P C_B` coincides with the `Set`-form
`extensionCode P (C_B : Set _)` — by construction. -/
@[simp] lemma coe_extensionCodeSubmodule
    {ι : Type} [Fintype ι]
    {B F : Type} [Field B] [Field F] [Algebra B F]
    (P : ExtensionFieldPresentation B F)
    (C_B : Submodule B (ι → B)) :
    (extensionCodeSubmodule P C_B : Set (ι → F)) =
      extensionCode P (C_B : Set (ι → B)) := rfl

/-- **ABF26 Lemma 2.21 [BCFW25 Lemma D.3].** List size of an extension code equals the
list size of the corresponding interleaved base code. Let `C_B : B^k → B^n` be a
linear code and `P` be an extension-field presentation. For every `δ ∈ (0, 1)`:

  `|Λ(C_F, δ)| = |Λ(C_B^≡e, δ)|`

where `C_F` is the extension code (D2.20) and `C_B^≡e` is the `e`-fold interleaved
base code (D2.9). Proved in-tree: the coordinate isomorphism `Ψ := φ` (applied
componentwise) is a Hamming isometry `(ι → F) ≃ (ι → Fin e → B)` carrying `extensionCode`
onto `interleavedCodeSet`, so it matches the `δ`-close-codeword sets bijectively and the
supremum defining `Λ` is preserved. -/
theorem lambda_extensionCode_eq_lambda_interleaved
    {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    {B F : Type} [Field B] [Fintype B] [DecidableEq B]
    [Field F] [Fintype F] [DecidableEq F] [Algebra B F]
    (P : ExtensionFieldPresentation B F)
    (C_B : Set (ι → B)) (δ : ℝ) (_hδ_pos : 0 < δ) (_hδ_lt : δ < 1) :
    Lambda (extensionCode P C_B) δ =
      Lambda (Code.interleavedCodeSet (κ := Fin P.e) C_B)
        δ := by
  letI : DecidableEq F := Classical.decEq F
  letI : DecidableEq (Fin P.e → B) := Classical.decEq _
  set Ψ : (ι → F) ≃ (ι → Fin P.e → B) :=
    Equiv.piCongrRight (fun _ => P.φ.toEquiv) with hΨ
  have hΨ_apply : ∀ (v : ι → F) (i : ι), Ψ v i = P.φ (v i) := fun v i => rfl
  have hφinj : Function.Injective (P.φ : F → (Fin P.e → B)) := P.φ.injective
  have hham : ∀ x y : ι → F, hammingDist (Ψ x) (Ψ y) = hammingDist x y := by
    intro x y
    have := hammingDist_comp (fun (_ : ι) => (P.φ : F → (Fin P.e → B)))
      (x := x) (y := y) (fun _ => hφinj)
    simpa [hΨ_apply] using this
  have hrelQ : ∀ x y : ι → F,
      Code.relHammingDist (Ψ x) (Ψ y) = Code.relHammingDist x y := by
    intro x y; unfold Code.relHammingDist; rw [hham]
  have hmem : ∀ v : ι → F,
      (Ψ v ∈ Code.interleavedCodeSet (κ := Fin P.e) C_B) ↔ v ∈ extensionCode P C_B := by
    intro v
    simp only [Code.interleavedCodeSet, extensionCode, Set.mem_setOf_eq]
    constructor
    · intro h j; convert h j using 1
    · intro h j; convert h j using 1
  have hset : ∀ f : ι → F,
      closeCodewordsRel (Code.interleavedCodeSet (κ := Fin P.e) C_B) (Ψ f) δ
        = Ψ '' (closeCodewordsRel (extensionCode P C_B) f δ) := by
    intro f
    ext c
    simp only [closeCodewordsRel, relHammingBall, Set.mem_setOf_eq, Set.mem_image]
    constructor
    · rintro ⟨hc_mem, hc_ball⟩
      refine ⟨Ψ.symm c, ⟨?_, ?_⟩, by simp⟩
      · rw [← hmem]; simpa using hc_mem
      · have hq : Code.relHammingDist f (Ψ.symm c) = Code.relHammingDist (Ψ f) c := by
          have := hrelQ f (Ψ.symm c); simpa using this.symm
        calc (Code.relHammingDist f (Ψ.symm c) : ℝ)
            = (Code.relHammingDist (Ψ f) c : ℝ) := by exact_mod_cast hq
          _ ≤ δ := hc_ball
    · rintro ⟨v, ⟨hv_mem, hv_ball⟩, rfl⟩
      refine ⟨(hmem v).2 hv_mem, ?_⟩
      calc (Code.relHammingDist (Ψ f) (Ψ v) : ℝ)
          = (Code.relHammingDist f v : ℝ) := by exact_mod_cast hrelQ f v
        _ ≤ δ := hv_ball
  have hcard : ∀ f : ι → F,
      (closeCodewordsRel (Code.interleavedCodeSet (κ := Fin P.e) C_B) (Ψ f) δ).ncard
        = (closeCodewordsRel (extensionCode P C_B) f δ).ncard := by
    intro f
    rw [hset f, Set.ncard_image_of_injective _ Ψ.injective]
  unfold Lambda
  rw [← Equiv.iSup_comp (g := fun g => ((closeCodewordsRel
        (Code.interleavedCodeSet (κ := Fin P.e) C_B) g δ).ncard : ℕ∞)) Ψ]
  apply iSup_congr
  intro f
  rw [hcard f]

end CodingTheory

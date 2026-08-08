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

Definitions and lemmas (all proved in-tree) from ABF26 §2.6 (Arnon-Boneh-Fenzi,
*Open Problems in List Decoding and Correlated Agreement*, 2026, page 11):
extension-field presentations, extension codes obtained by base change, and the
relation `|Λ(C_F, δ)| = |Λ(C_B^e, δ)|` between the list size of an extension code
and the list size of the corresponding interleaved base code.

## Main definitions

- `ExtensionFieldPresentation` (D2.19): a thin wrapper around Mathlib's
  `[Algebra B F]` plus a finite `B`-basis `basis : Basis (Fin e) B F` of `F`.
  The paper's named maps are *not* redefined here: its embedding `ψ : B ↪ F` is
  Mathlib's `algebraMap B F`, its coordinate isomorphism `φ : F ≃ B^e` is
  `basis.equivFun`, and its coordinate functionals `φ_j` are `basis.coord j`
  (exposed as the abbreviation `ExtensionFieldPresentation.coord`, which is
  `rfl`-equal to `basis.coord` — see `coord_eq_basis_coord`).
- `ExtensionFieldPresentation.IsSystematic`: the paper's systematic condition
  `φ(ψ x) = (x, 0, …, 0)`.
- `CodingTheory.extensionCode` (D2.20): the extension code of a base code
  `C_B ⊆ B^ι`, **as a set of words** `Set (ι → F)`.
- `CodingTheory.extensionCodeSubmodule`: the same object packaged as an
  `F`-`Submodule` when `C_B` is a `B`-`Submodule`.

**Encoder-level content is out of scope here.** ABF26 D2.20 defines `C_F` as an
*encoder* `F^k → F^n`, whereas ArkLib (like its D2.9 sibling `interleavedCodeSet`)
models a code by its *image*. Consequently the paper's only stated consequence of
systematicity — `C_F(ψ(v)) = ψ(C_B(v))` for `v ∈ B^k`, used for soundness in
[BCFW25, §D.2] — has no counterpart here: it talks about the encoder applied to a
specific message. What *is* expressible at the image level is recorded as
`mem_extensionCode_comp_algebraMap_iff_of_isSystematic` (the base code is exactly
the `ψ`-rational part of the extension code). A future author who needs the
encoder identity has to add an `extensionEncode : (Fin k → F) → (ι → F)` built
from a base encoder first.

## Main statements

- `extensionCode_eq_span`: the basis-free characterisation
  `extensionCode P C_B = Submodule.span F (algebraMap '' C_B)` for a `B`-submodule
  `C_B`. This is the mathematically informative fact about D2.20, and it is the
  engine for the closure and independence results below.
- `extensionCode_presentation_independent`,
  `extensionCodeSubmodule_presentation_independent`: for a `B`-submodule `C_B`, the
  extension code is the **same set for every presentation** of `F` over `B`. So the
  `ExtensionFieldPresentation` argument of `extensionCode` is bookkeeping that keeps
  the definition in the paper's shape (`e` coordinate projections), not data that
  the resulting code depends on: only the pair `(B, F)` together with its
  `Algebra` structure matters. (The presentation *is* genuine data for
  `IsSystematic` and for the coordinate-level statements, and the raw `Set` form of
  `extensionCode` at a non-submodule `C_B` is *not* presentation-independent — the
  statement is scoped to submodules on purpose.)
- `extensionCode_add_mem`, `extensionCode_psi_smul_mem`, `extensionCode_smul_mem` —
  closure of `extensionCode P C_B` under addition, under the `ψ`-induced `B`-action,
  and under `F`-scalar multiplication (when `C_B` is `B`-linear). Together they
  package `extensionCode P C_B` as a full `F`-`Submodule`
  (`extensionCodeSubmodule`), which is the D2.20 linearity claim.
- `mem_extensionCode_comp_algebraMap_iff_of_isSystematic`: the strongest
  image-level consequence of systematicity, `ψ ∘ c ∈ C_F ↔ c ∈ C_B`.
- `lambda_extensionCode_eq_lambda_interleaved` (L2.21, [BCFW25, Lemma D.3]):
  `|Λ(C_F, δ)| = |Λ(C_B^≡e, δ)|`. Proved in-tree via the coordinate Hamming
  isometry. ABF26 states L2.21 for `δ ∈ (0, 1)`; the Lean statement is proved
  **unconditionally in `δ`** (the isometry argument never uses the restriction), so
  the absence of `0 < δ` and `δ < 1` hypotheses is a deliberate strengthening and
  not a transcription slip.

## References

- [ABF26] Arnon-Boneh-Fenzi. *Open Problems in List Decoding and Correlated
  Agreement*. 2026. §2.6 (D2.19, D2.20, L2.21).
- [BCFW25] Bünz-Chiesa-Fenzi-Wang. Definition D.2 and Lemma D.3.
- [DP25] Diamond-Posen, Theorem 3.2, for the distance equality
  `δ_min(C_F) = δ_min(C_B)` quoted in the L2.21 paragraph context — **not**
  formalised here.
-/

namespace CodingTheory

open ListDecodable Module

/-- **ABF26 Definition 2.19.** An *extension field presentation* is the data of
a finite `B`-basis of `F`, in the presence of a `B`-algebra structure on `F`:

- `B` and `F` are fields,
- `[Algebra B F]` provides the paper's embedding `ψ := algebraMap B F` (injective
  by `FaithfulSMul.algebraMap_injective`) and the `B`-module structure on `F`,
- `e : ℕ` is the dimension of `F` as a `B`-vector space,
- `basis : Basis (Fin e) B F` witnesses the paper's `B`-linear isomorphism
  `φ : F ≃ₗ[B] (Fin e → B)`, namely `basis.equivFun`.

Nothing is redefined: the paper's `ψ`, `φ` and `φ_j` are Mathlib's `algebraMap`,
`Basis.equivFun` and `Basis.coord` respectively. -/
structure ExtensionFieldPresentation (B F : Type*) [Field B] [Field F] [Algebra B F] where
  /-- The dimension `e := dim_B F`. -/
  e : ℕ
  /-- The `B`-basis of `F` indexed by `Fin e`. -/
  basis : Basis (Fin e) B F

namespace ExtensionFieldPresentation

variable {B F : Type*} [Field B] [Field F] [Algebra B F]

/-- The degree of an extension field presentation is positive: `F` is a field, hence
nontrivial, so its basis index type `Fin e` is nonempty. -/
lemma e_pos (P : ExtensionFieldPresentation B F) : 0 < P.e :=
  Fin.pos_iff_nonempty.2 P.basis.index_nonempty

/-- The paper's `j`-th coordinate functional `φ_j : F →ₗ[B] B`. This is *literally*
Mathlib's `Module.Basis.coord`; the abbreviation exists only to keep the D2.20
statement in the paper's shape. See `coord_eq_basis_coord`. -/
noncomputable def coord (P : ExtensionFieldPresentation B F) (j : Fin P.e) : F →ₗ[B] B :=
  P.basis.coord j

@[simp] lemma coord_eq_basis_coord (P : ExtensionFieldPresentation B F) (j : Fin P.e) :
    P.coord j = P.basis.coord j := rfl

/-- `P.coord j` and the paper's `φ` agree: the `j`-th entry of `φ x` is `φ_j x`. -/
lemma coord_eq_equivFun_apply (P : ExtensionFieldPresentation B F) (j : Fin P.e) (x : F) :
    P.coord j x = P.basis.equivFun x j := rfl

/-- A presentation is *systematic* if `φ(ψ(x)) = (x, 0, …, 0)` for every `x : B`.
This makes the base-field copy of `B` inside `F` align with the first coordinate.
(`ψ = algebraMap B F` and `φ = P.basis.equivFun`, cf. the structure docstring.) -/
def IsSystematic (P : ExtensionFieldPresentation B F) : Prop :=
  ∀ x : B, P.basis.equivFun (algebraMap B F x) = fun i ↦ if i.val = 0 then x else 0

/-- Coordinate form of `IsSystematic`: the `j`-th coordinate of `ψ x` is `x` for
`j = 0` and `0` otherwise. -/
lemma coord_algebraMap_of_isSystematic {P : ExtensionFieldPresentation B F}
    (hP : P.IsSystematic) (j : Fin P.e) (x : B) :
    P.coord j (algebraMap B F x) = if j.val = 0 then x else 0 :=
  congrFun (hP x) j

end ExtensionFieldPresentation

/-- **ABF26 Definition 2.20.** The *extension code* of a base code `C_B ⊆ B^ι`
along an extension-field presentation `P`, as a **set of words** over `F` (the
image of the paper's encoder `C_F`, in line with how ArkLib models codes; the
encoder itself is not formalised, see the module docstring). It is defined on a
vector `v : ι → F` by

  `v ∈ C_F ↔ ∀ j : Fin e, (fun i ↦ P.coord j (v i)) ∈ C_B`

i.e. each of the `e` coordinate projections of `v` lies in `C_B`.

**Closure properties.** `extensionCode P C_B` is closed under addition (when `C_B`
is) and under `F`-scalar multiplication (when `C_B` is `B`-linear); see
`extensionCode_add_mem`, `extensionCode_smul_mem` and the packaged
`extensionCodeSubmodule`. For a `B`-submodule `C_B` the code is in fact the
`F`-span of `ψ '' C_B` (`extensionCode_eq_span`) and hence does not depend on `P`
(`extensionCode_presentation_independent`). -/
def extensionCode {ι : Type*}
    {B F : Type*} [Field B] [Field F] [Algebra B F]
    (P : ExtensionFieldPresentation B F)
    (C_B : Set (ι → B)) : Set (ι → F) :=
  { v : ι → F | ∀ j : Fin P.e, (fun i ↦ P.coord j (v i)) ∈ C_B }

/-- Unfolding lemma for `extensionCode`: membership is exactly "every coordinate
projection lies in the base code". -/
lemma extensionCode_iff_coord_in_base
    {ι : Type*}
    {B F : Type*} [Field B] [Field F] [Algebra B F]
    (P : ExtensionFieldPresentation B F)
    (C_B : Set (ι → B)) (v : ι → F) :
    v ∈ extensionCode P C_B ↔
      ∀ j : Fin P.e, (fun i ↦ P.coord j (v i)) ∈ C_B := by
  rfl

/-- **`extensionCode` is closed under addition** when `C_B` is. Immediate from
additivity of the (linear) coordinate maps. -/
lemma extensionCode_add_mem
    {ι : Type*}
    {B F : Type*} [Field B] [Field F] [Algebra B F]
    (P : ExtensionFieldPresentation B F)
    {C_B : Set (ι → B)}
    (hadd : ∀ {a b : ι → B}, a ∈ C_B → b ∈ C_B → a + b ∈ C_B)
    {u v : ι → F} (hu : u ∈ extensionCode P C_B) (hv : v ∈ extensionCode P C_B) :
    u + v ∈ extensionCode P C_B := by
  intro j
  have hpt : (fun i ↦ P.coord j ((u + v) i)) =
      (fun i ↦ P.coord j (u i)) + fun i ↦ P.coord j (v i) := by
    ext i
    exact map_add (P.coord j) (u i) (v i)
  rw [hpt]
  exact hadd (hu j) (hv j)

/-- **`extensionCode` is closed under the `ψ`-induced `B`-scalar action** when `C_B`
is `B`-scalar closed, where `ψ = algebraMap B F` is the paper's embedding.
Immediate from `LinearMap.map_smul` of the coordinate maps. Note that this needs
strictly less than `extensionCode_smul_mem` (no additive closure of `C_B`). -/
lemma extensionCode_psi_smul_mem
    {ι : Type*}
    {B F : Type*} [Field B] [Field F] [Algebra B F]
    (P : ExtensionFieldPresentation B F)
    {C_B : Set (ι → B)}
    (hsmul : ∀ (b : B) {a : ι → B}, a ∈ C_B → b • a ∈ C_B)
    (b : B) {v : ι → F} (hv : v ∈ extensionCode P C_B) :
    (fun i ↦ algebraMap B F b * v i) ∈ extensionCode P C_B := by
  intro j
  have hpt : (fun i ↦ P.coord j (algebraMap B F b * v i)) = b • fun i ↦ P.coord j (v i) := by
    ext i
    rw [← Algebra.smul_def, map_smul]
    simp [Pi.smul_apply, smul_eq_mul]
  rw [hpt]
  exact hsmul b (hv j)

/-- **Basis-free characterisation of `extensionCode`.** For a `B`-submodule `C_B`,
the extension code is the `F`-span of the image of `C_B` under the paper's
embedding `ψ = algebraMap B F`:

  `extensionCode P C_B = Submodule.span F (ψ '' C_B)`.

The right-hand side mentions neither `e`, nor the basis, nor the coordinate maps.
Both inclusions are elementary: `⊆` expands each entry of `v` in the basis
(`Basis.sum_equivFun`), and `⊇` computes the coordinates of a finite `F`-linear
combination `∑ t, f t • (ψ ∘ a t)` as `∑ t, φ_j(f t) • a t`, which lies in `C_B`
because `C_B` is a `B`-submodule. -/
theorem extensionCode_eq_span {ι : Type*}
    {B F : Type*} [Field B] [Field F] [Algebra B F]
    (P : ExtensionFieldPresentation B F) (C_B : Submodule B (ι → B)) :
    extensionCode P (C_B : Set (ι → B)) =
      (Submodule.span F ((fun c : ι → B ↦ (algebraMap B F) ∘ c) '' (C_B : Set (ι → B))) :
        Set (ι → F)) := by
  apply Set.eq_of_subset_of_subset
  · -- `⊆`: expand each entry of `v` in the basis.
    intro v hv
    have hrepr : v = ∑ j : Fin P.e,
        P.basis j • ((algebraMap B F) ∘ (fun i ↦ P.coord j (v i))) := by
      funext i
      rw [Finset.sum_apply]
      simp only [Pi.smul_apply, Function.comp_apply, smul_eq_mul]
      have h := P.basis.sum_equivFun (v i)
      simp only [Basis.equivFun_apply] at h
      refine (Eq.trans (Finset.sum_congr rfl fun j _ ↦ ?_) h).symm
      simp [Algebra.smul_def, mul_comm]
    rw [SetLike.mem_coe, hrepr]
    exact Submodule.sum_mem _ fun j _ ↦
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, hv j, rfl⟩)
  · -- `⊇`: a finite `F`-combination of `ψ`-images has all coordinates in `C_B`.
    intro v hv
    obtain ⟨n, f, g, hsum⟩ := Submodule.mem_span_set'.1 hv
    have hg : ∀ t, ∃ c ∈ (C_B : Set (ι → B)), (algebraMap B F) ∘ c = (g t : ι → F) :=
      fun t ↦ (g t).2
    choose a ha hga using hg
    intro j
    have hcoord : (fun i ↦ P.coord j (v i)) = ∑ t : Fin n, (P.coord j (f t)) • a t := by
      funext i
      rw [← hsum]
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      rw [map_sum]
      refine Finset.sum_congr rfl fun t _ ↦ ?_
      have hgt : (g t : ι → F) i = algebraMap B F (a t i) := by rw [← hga t]; rfl
      rw [hgt, mul_comm, ← Algebra.smul_def, map_smul, smul_eq_mul, mul_comm]
    rw [hcoord]
    exact Submodule.sum_mem _ fun t _ ↦ C_B.smul_mem _ (ha t)

/-- **F-scalar closure of `extensionCode`** — the paper's D2.20 `F`-linearity claim.
The hypotheses `hadd`/`hsmul` make `C_B` a `B`-submodule (its `0` is `(0 : B) • c`
for any row `c` of `C_B`, and `P.e > 0` supplies such a row), after which
`extensionCode_eq_span` exhibits the code as an `F`-span, which is `F`-scalar
closed by construction. -/
lemma extensionCode_smul_mem
    {ι : Type*}
    {B F : Type*} [Field B] [Field F] [Algebra B F]
    (P : ExtensionFieldPresentation B F)
    {C_B : Set (ι → B)}
    (hadd : ∀ {a b : ι → B}, a ∈ C_B → b ∈ C_B → a + b ∈ C_B)
    (hsmul : ∀ (b : B) {a : ι → B}, a ∈ C_B → b • a ∈ C_B)
    (α : F) {v : ι → F} (hv : v ∈ extensionCode P C_B) :
    (fun i ↦ α * v i) ∈ extensionCode P C_B := by
  have h0 : (0 : ι → B) ∈ C_B := by simpa using hsmul 0 (hv ⟨0, P.e_pos⟩)
  let M : Submodule B (ι → B) :=
    { carrier := C_B
      add_mem' := fun ha hb ↦ hadd ha hb
      zero_mem' := h0
      smul_mem' := fun b _ ha ↦ hsmul b ha }
  have hv' : v ∈ extensionCode P (M : Set (ι → B)) := hv
  have key : (fun i ↦ α * v i) ∈ extensionCode P (M : Set (ι → B)) := by
    rw [extensionCode_eq_span P M] at hv' ⊢
    exact Submodule.smul_mem _ α hv'
  exact key

/-- **Submodule-packaging of `extensionCode`** when `C_B` is a `B`-submodule.

Bundles the three closure laws (`add_mem`, `zero_mem`, `smul_mem`) into a
single `Submodule F (ι → F)`, mirroring the `ReedSolomon.code` pattern
(which returns a `Submodule F (ι → F)` directly). Downstream code that
wants to consume an extension code as a linear code should use this
form rather than the raw `Set`-based `extensionCode`. The `Set`-form
`extensionCode` is the carrier, so the two agree by `rfl`
(`coe_extensionCodeSubmodule`). -/
noncomputable def extensionCodeSubmodule {ι : Type*}
    {B F : Type*} [Field B] [Field F] [Algebra B F]
    (P : ExtensionFieldPresentation B F)
    (C_B : Submodule B (ι → B)) : Submodule F (ι → F) where
  carrier := extensionCode P (C_B : Set (ι → B))
  add_mem' {u v} hu hv := extensionCode_add_mem P (fun ha hb ↦ C_B.add_mem ha hb) hu hv
  zero_mem' := by
    intro j
    change (fun i ↦ P.coord j ((0 : ι → F) i)) ∈ (C_B : Set (ι → B))
    simp only [Pi.zero_apply, map_zero]
    exact C_B.zero_mem
  smul_mem' c v hv :=
    extensionCode_smul_mem P
      (hadd := fun {a b} (ha : a ∈ C_B) (hb : b ∈ C_B) ↦ C_B.add_mem ha hb)
      (hsmul := fun (b : B) {a : ι → B} (ha : a ∈ C_B) ↦ C_B.smul_mem b ha)
      c hv

/-- The carrier of `extensionCodeSubmodule P C_B` coincides with the `Set`-form
`extensionCode P (C_B : Set _)` — by construction. -/
@[simp] lemma coe_extensionCodeSubmodule {ι : Type*}
    {B F : Type*} [Field B] [Field F] [Algebra B F]
    (P : ExtensionFieldPresentation B F)
    (C_B : Submodule B (ι → B)) :
    (extensionCodeSubmodule P C_B : Set (ι → F)) =
      extensionCode P (C_B : Set (ι → B)) := rfl

/-- `extensionCodeSubmodule` is the `F`-span of `ψ '' C_B` — the `Submodule` form of
`extensionCode_eq_span`. -/
theorem extensionCodeSubmodule_eq_span {ι : Type*}
    {B F : Type*} [Field B] [Field F] [Algebra B F]
    (P : ExtensionFieldPresentation B F) (C_B : Submodule B (ι → B)) :
    extensionCodeSubmodule P C_B =
      Submodule.span F ((fun c : ι → B ↦ (algebraMap B F) ∘ c) '' (C_B : Set (ι → B))) :=
  SetLike.coe_injective (extensionCode_eq_span P C_B)

/-- **The extension code of a `B`-submodule does not depend on the presentation.**
Any two extension-field presentations `P`, `P'` of the same pair `(B, F)` — of
possibly different shape, and in particular with different bases — give the same
set of words. Both sides equal `Submodule.span F (ψ '' C_B)`, which mentions no
presentation data at all.

So the `ExtensionFieldPresentation` argument of `extensionCode` is bookkeeping that
keeps D2.20 in the paper's coordinate shape, not data the code depends on. This is
scoped to `B`-submodules `C_B` on purpose: for a general `Set` `C_B` the
coordinate-wise definition really does see the basis. -/
theorem extensionCode_presentation_independent {ι : Type*}
    {B F : Type*} [Field B] [Field F] [Algebra B F]
    (P P' : ExtensionFieldPresentation B F) (C_B : Submodule B (ι → B)) :
    extensionCode P (C_B : Set (ι → B)) = extensionCode P' (C_B : Set (ι → B)) := by
  rw [extensionCode_eq_span P C_B, extensionCode_eq_span P' C_B]

/-- `Submodule` form of `extensionCode_presentation_independent`. -/
theorem extensionCodeSubmodule_presentation_independent {ι : Type*}
    {B F : Type*} [Field B] [Field F] [Algebra B F]
    (P P' : ExtensionFieldPresentation B F) (C_B : Submodule B (ι → B)) :
    extensionCodeSubmodule P C_B = extensionCodeSubmodule P' C_B :=
  SetLike.coe_injective (extensionCode_presentation_independent P P' C_B)

/-- **Image-level consequence of systematicity.** If `P` is systematic then the base
code is exactly the `ψ`-rational part of the extension code:

  `ψ ∘ c ∈ C_F ↔ c ∈ C_B`   for `c : ι → B`.

This is as close as the image-level modelling gets to [ABF26, D2.20] /
[BCFW25, §D.2]'s `C_F(ψ(v)) = ψ(C_B(v))`, which is a statement about *encoders* and
is therefore not expressible here (see the module docstring). Note the `←`
direction is where systematicity does real work for the coordinates `j ≠ 0`: it
pins them to `0`, so no assumption beyond `0 ∈ C_B` is needed. -/
theorem mem_extensionCode_comp_algebraMap_iff_of_isSystematic {ι : Type*}
    {B F : Type*} [Field B] [Field F] [Algebra B F]
    {P : ExtensionFieldPresentation B F} (hP : P.IsSystematic)
    (C_B : Submodule B (ι → B)) (c : ι → B) :
    (algebraMap B F) ∘ c ∈ extensionCode P (C_B : Set (ι → B)) ↔ c ∈ C_B := by
  constructor
  · intro h
    have h0 := h ⟨0, P.e_pos⟩
    have hfun : (fun i ↦ P.coord ⟨0, P.e_pos⟩ (((algebraMap B F) ∘ c) i)) = c := by
      funext i
      simpa using P.coord_algebraMap_of_isSystematic hP ⟨0, P.e_pos⟩ (c i)
    rw [hfun] at h0
    exact h0
  · intro hc j
    by_cases hj : j.val = 0
    · have hfun : (fun i ↦ P.coord j (((algebraMap B F) ∘ c) i)) = c := by
        funext i
        simpa [hj] using P.coord_algebraMap_of_isSystematic hP j (c i)
      rw [hfun]
      exact hc
    · have hfun : (fun i ↦ P.coord j (((algebraMap B F) ∘ c) i)) = 0 := by
        funext i
        simpa [hj] using P.coord_algebraMap_of_isSystematic hP j (c i)
      rw [hfun]
      exact C_B.zero_mem

/-- **ABF26 Lemma 2.21 [BCFW25, Lemma D.3].** The list size of an extension code equals
the list size of the corresponding interleaved base code. For a base code
`C_B ⊆ B^ι`, an extension-field presentation `P`, and any `δ : ℝ`:

  `|Λ(C_F, δ)| = |Λ(C_B^≡e, δ)|`

where `C_F` is the extension code (D2.20) and `C_B^≡e` is the `e`-fold interleaved
base code (D2.9).

Proved in-tree: the coordinate isomorphism `φ = P.basis.equivFun`, applied
componentwise, is a Hamming isometry `(ι → F) ≃ (ι → Fin e → B)` carrying
`extensionCode` onto `interleavedCodeSet`, so it matches the `δ`-close-codeword sets
bijectively and the supremum defining `Λ` is preserved.

ABF26 states the lemma for `δ ∈ (0, 1)`. The isometry argument never uses that
restriction, so the statement here is **unconditional in `δ`** (a strengthening, not
a transcription slip); in particular it holds at `δ = 0` and at `δ ≥ 1`. -/
theorem lambda_extensionCode_eq_lambda_interleaved
    {ι : Type*} [Fintype ι]
    {B F : Type*} [Field B] [Field F] [Algebra B F]
    (P : ExtensionFieldPresentation B F)
    (C_B : Set (ι → B)) (δ : ℝ) :
    Lambda (extensionCode P C_B) δ =
      Lambda (Code.interleavedCodeSet (κ := Fin P.e) C_B) δ := by
  letI : DecidableEq F := Classical.decEq F
  letI : DecidableEq (Fin P.e → B) := Classical.decEq _
  set Ψ : (ι → F) ≃ (ι → Fin P.e → B) :=
    Equiv.piCongrRight (fun _ => P.basis.equivFun.toEquiv) with hΨ
  have hΨ_apply : ∀ (v : ι → F) (i : ι), Ψ v i = P.basis.equivFun (v i) := fun v i => rfl
  have hφinj : Function.Injective (P.basis.equivFun : F → (Fin P.e → B)) :=
    P.basis.equivFun.injective
  have hham : ∀ x y : ι → F, hammingDist (Ψ x) (Ψ y) = hammingDist x y := by
    intro x y
    have := hammingDist_comp (fun (_ : ι) => (P.basis.equivFun : F → (Fin P.e → B)))
      (x := x) (y := y) (fun _ => hφinj)
    exact this
  have hrelQ : ∀ x y : ι → F,
      Code.relHammingDist (Ψ x) (Ψ y) = Code.relHammingDist x y := by
    intro x y; unfold Code.relHammingDist; rw [hham]
  have hmem : ∀ v : ι → F,
      (Ψ v ∈ Code.interleavedCodeSet (κ := Fin P.e) C_B) ↔ v ∈ extensionCode P C_B := by
    intro v
    simp only [Code.interleavedCodeSet, extensionCode, Set.mem_setOf_eq]
    constructor
    · intro h j; exact h j
    · intro h j; exact h j
  have hset : ∀ f : ι → F,
      closeCodewordsRel (Code.interleavedCodeSet (κ := Fin P.e) C_B) (Ψ f) δ
        = Ψ '' (closeCodewordsRel (extensionCode P C_B) f δ) := by
    intro f
    ext c
    simp only [closeCodewordsRel, relHammingBall, Set.mem_setOf_eq, Set.mem_image]
    constructor
    · rintro ⟨hc_mem, hc_ball⟩
      refine ⟨Ψ.symm c, ⟨?_, ?_⟩, by simp⟩
      · rw [← hmem, Ψ.apply_symm_apply]; exact hc_mem
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

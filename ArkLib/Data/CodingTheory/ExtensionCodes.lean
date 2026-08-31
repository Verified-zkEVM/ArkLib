/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

import ArkLib.Data.CodingTheory.ListDecodability
import ArkLib.Data.CodingTheory.InterleavedCode
import Mathlib.LinearAlgebra.Basis.Defs

/-!
# Extension codes

The *extension code* of a base code `C_B ⊆ B^ι` along a finite field extension `B ⊆ F` is
the code over `F` whose words are those all of whose coordinates, read in a `B`-basis of
`F`, lie in `C_B`. Equivalently, for a `B`-linear base code, it is the `F`-span of the image
of `C_B` in `F^ι`.

## Main definitions

* `ExtensionFieldPresentation` — a `B`-algebra structure on `F` together with a finite
  `B`-basis of `F`. Nothing is redefined here: the embedding `B ↪ F` is `algebraMap B F`,
  the coordinate isomorphism `F ≃ B^e` is `Module.Basis.equivFun`, and the coordinate
  functionals are `Module.Basis.coord`, abbreviated `ExtensionFieldPresentation.coord`.
* `ExtensionFieldPresentation.IsSystematic` — the basis is chosen so that the copy of `B`
  inside `F` is the first coordinate.
* `CodingTheory.extensionEncode`, `CodingTheory.extensionEncodeLinearMap` — scalar
  extension of a `B`-linear encoder to an `F`-linear one.
* `CodingTheory.extensionCode` — the extension code, as a `Set (ι → F)`.
* `CodingTheory.extensionCodeSubmodule` — the same object as an `F`-submodule, when the
  base code is a `B`-submodule.

## Main statements

* `CodingTheory.extensionCode_eq_span` — the basis-free characterisation
  `extensionCode P C_B = Submodule.span F (algebraMap '' C_B)` for a `B`-submodule `C_B`;
  the engine for the closure and independence results.
* `CodingTheory.extensionCode_presentation_independent` — for a `B`-submodule base code,
  the extension code is the same set for every presentation of `F` over `B`. (This fails
  for a base code that is a bare set: there the coordinate-wise definition really does see
  the basis.)
* `CodingTheory.extensionCode_add_mem`, `..._psi_smul_mem`, `..._smul_mem` — the closure
  laws bundled by `extensionCodeSubmodule`.
* `CodingTheory.extensionEncode_comp_algebraMap`,
  `CodingTheory.mem_extensionCode_comp_algebraMap_iff` — encoder- and image-level forms of
  the identification of the base code inside the extension code.
* `CodingTheory.minDist_extensionCode` — scalar extension preserves minimum distance.
* `CodingTheory.lambda_extensionCode_eq_lambda_interleaved` — the list size of an extension
  code equals that of the `e`-fold interleaved base code, at every radius.

## References

* [Arnon, G., Boneh, D., and Fenzi, G., *Open Problems in List Decoding and Correlated
    Agreement*][ABF26]
* [Bünz, B., Chiesa, A., Fenzi, G., and Wang, W., *Linear time accumulation
    schemes*][BCFW25]
* [Diamond, B. E., and Posen, J., *Succinct Arguments over Towers of Binary
    Fields*][DP25]
-/

namespace CodingTheory

open Code Module

/-- An *extension field presentation* of `F` over `B` is a finite `B`-basis of `F`,
given a `B`-algebra structure on `F`.

Together they supply the embedding `algebraMap B F` (injective by
`FaithfulSMul.algebraMap_injective`), the `B`-linear coordinate isomorphism
`basis.equivFun : F ≃ₗ[B] (Fin e → B)`, and the coordinate functionals `basis.coord j`. -/
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

/-- The `j`-th coordinate functional `F →ₗ[B] B` of a presentation, an abbreviation for
`Module.Basis.coord`. -/
noncomputable abbrev coord (P : ExtensionFieldPresentation B F) (j : Fin P.e) : F →ₗ[B] B :=
  P.basis.coord j

@[simp] lemma coord_eq_basis_coord (P : ExtensionFieldPresentation B F) (j : Fin P.e) :
    P.coord j = P.basis.coord j := rfl

/-- The `j`-th coordinate functional is the `j`-th entry of the coordinate isomorphism. -/
lemma coord_eq_equivFun_apply (P : ExtensionFieldPresentation B F) (j : Fin P.e) (x : F) :
    P.coord j x = P.basis.equivFun x j := rfl

/-- A presentation is *systematic* if the coordinates of `algebraMap B F x` are
`(x, 0, …, 0)` for every `x : B`, i.e. the copy of `B` inside `F` is the first coordinate.

No result in this file assumes systematicity; tower constructions, for instance, satisfy it
by construction. -/
def IsSystematic (P : ExtensionFieldPresentation B F) : Prop :=
  ∀ x : B, P.basis.equivFun (algebraMap B F x) = fun i ↦ if i.val = 0 then x else 0

/-- Coordinate form of `IsSystematic`: the `j`-th coordinate of `algebraMap B F x` is `x`
for `j = 0` and `0` otherwise. -/
lemma coord_algebraMap_of_isSystematic {P : ExtensionFieldPresentation B F}
    (hP : P.IsSystematic) (j : Fin P.e) (x : B) :
    P.coord j (algebraMap B F x) = if j.val = 0 then x else 0 :=
  congrFun (hP x) j

end ExtensionFieldPresentation

/-- Scalar extension of a `B`-linear encoder `B^κ →ₗ[B] B^ι` to messages and codewords over
`F`: apply the encoder independently to each coordinate row in the presentation basis, then
reassemble,

  `extensionEncode P encode v i = φ⁻¹ (fun j ↦ encode (fun t ↦ φ_j (v t)) i)` .

Its `F`-linear packaging is `extensionEncodeLinearMap`. -/
noncomputable def extensionEncode {κ ι : Type*}
    {B F : Type*} [Field B] [Field F] [Algebra B F]
    (P : ExtensionFieldPresentation B F)
    (encode : (κ → B) →ₗ[B] (ι → B)) (v : κ → F) : ι → F :=
  fun i ↦ P.basis.equivFun.symm (fun j ↦ encode (fun t ↦ P.coord j (v t)) i)

/-- The `j`-th coordinate of an extension encoding is the base encoding of the
`j`-th message-coordinate word. -/
@[simp] lemma coord_extensionEncode {κ ι : Type*}
    {B F : Type*} [Field B] [Field F] [Algebra B F]
    (P : ExtensionFieldPresentation B F)
    (encode : (κ → B) →ₗ[B] (ι → B)) (v : κ → F) (j : Fin P.e) (i : ι) :
    P.coord j (extensionEncode P encode v i) =
      encode (fun t ↦ P.coord j (v t)) i := by
  change P.basis.equivFun (P.basis.equivFun.symm
    (fun j ↦ encode (fun t ↦ P.coord j (v t)) i)) j = _
  rw [P.basis.equivFun.apply_symm_apply]

private lemma extensionEncode_zero {κ ι : Type*}
    {B F : Type*} [Field B] [Field F] [Algebra B F]
    (P : ExtensionFieldPresentation B F)
    (encode : (κ → B) →ₗ[B] (ι → B)) :
    extensionEncode P encode 0 = 0 := by
  funext i
  apply P.basis.equivFun.injective
  funext j
  change P.coord j (extensionEncode P encode 0 i) = P.coord j 0
  rw [coord_extensionEncode]
  simp only [Pi.zero_apply, map_zero]
  change encode (0 : κ → B) i = 0
  rw [map_zero]
  rfl

private lemma extensionEncode_add {κ ι : Type*}
    {B F : Type*} [Field B] [Field F] [Algebra B F]
    (P : ExtensionFieldPresentation B F)
    (encode : (κ → B) →ₗ[B] (ι → B)) (v w : κ → F) :
    extensionEncode P encode (v + w) =
      extensionEncode P encode v + extensionEncode P encode w := by
  funext i
  apply P.basis.equivFun.injective
  funext j
  change P.coord j (extensionEncode P encode (v + w) i) =
    P.coord j (extensionEncode P encode v i + extensionEncode P encode w i)
  rw [coord_extensionEncode, map_add, coord_extensionEncode, coord_extensionEncode]
  have hrow : (fun t => P.coord j ((v + w) t)) =
      (fun t => P.coord j (v t)) + fun t => P.coord j (w t) := by
    funext t
    simp
  rw [hrow, map_add]
  rfl

private lemma extensionEncode_smul_algebraMap {κ ι : Type*}
    {B F : Type*} [Field B] [Field F] [Algebra B F]
    (P : ExtensionFieldPresentation B F)
    (encode : (κ → B) →ₗ[B] (ι → B)) (a : F) (v : κ → B) :
    extensionEncode P encode (a • ((algebraMap B F) ∘ v)) =
      a • ((algebraMap B F) ∘ encode v) := by
  funext i
  apply P.basis.equivFun.injective
  funext j
  change P.coord j (extensionEncode P encode (a • ((algebraMap B F) ∘ v)) i) =
    P.coord j ((a • ((algebraMap B F) ∘ encode v)) i)
  rw [coord_extensionEncode]
  have hcoord (x : B) :
      P.coord j (a * algebraMap B F x) = x * P.coord j a := by
    rw [mul_comm, ← Algebra.smul_def, map_smul]
    rfl
  have hin : (fun t => P.coord j ((a • ((algebraMap B F) ∘ v)) t)) =
      P.coord j a • v := by
    funext t
    simp only [Pi.smul_apply, Function.comp_apply, smul_eq_mul]
    rw [hcoord]
    exact mul_comm _ _
  rw [hin, map_smul]
  simp only [Pi.smul_apply, Function.comp_apply, smul_eq_mul]
  rw [hcoord]
  exact mul_comm _ _

private lemma sum_basis_rows {κ : Type*}
    {B F : Type*} [Field B] [Field F] [Algebra B F]
    (P : ExtensionFieldPresentation B F) (v : κ → F) :
    (∑ j : Fin P.e, P.basis j •
      ((algebraMap B F) ∘ fun t => P.coord j (v t))) = v := by
  funext t
  rw [Finset.sum_apply]
  change (∑ j : Fin P.e, (P.basis j •
      ((algebraMap B F) ∘ fun t => P.coord j (v t))) t) = v t
  rw [show (∑ j : Fin P.e, (P.basis j •
      ((algebraMap B F) ∘ fun t => P.coord j (v t))) t) =
      ∑ j : Fin P.e, P.coord j (v t) • P.basis j by
    apply Finset.sum_congr rfl
    intro j _hj
    simp only [Pi.smul_apply, Function.comp_apply, smul_eq_mul, Algebra.smul_def]
    exact mul_comm _ _]
  exact P.basis.sum_repr (v t)

/-- `extensionEncode` packaged as an `F`-linear map `F^κ →ₗ[F] F^ι`.

`F`-linearity is proved by expanding a message in the presentation basis and commuting the
`B`-linear base encoder with the resulting coordinate rows. -/
noncomputable def extensionEncodeLinearMap {κ ι : Type*}
    {B F : Type*} [Field B] [Field F] [Algebra B F]
    (P : ExtensionFieldPresentation B F)
    (encode : (κ → B) →ₗ[B] (ι → B)) : (κ → F) →ₗ[F] (ι → F) where
  toFun := extensionEncode P encode
  map_add' := extensionEncode_add P encode
  map_smul' := by
    intro a v
    let E : (κ → F) →+ (ι → F) :=
      { toFun := extensionEncode P encode
        map_zero' := extensionEncode_zero P encode
        map_add' := extensionEncode_add P encode }
    let row : Fin P.e → (κ → B) := fun j t => P.coord j (v t)
    have hv : (∑ j : Fin P.e, P.basis j •
        ((algebraMap B F) ∘ row j)) = v :=
      sum_basis_rows P v
    have hEv : E v = ∑ j : Fin P.e, P.basis j •
        ((algebraMap B F) ∘ encode (row j)) := by
      rw [← hv, map_sum]
      apply Finset.sum_congr rfl
      intro j _hj
      exact extensionEncode_smul_algebraMap P encode (P.basis j) (row j)
    change E (a • v) = a • E v
    calc
      E (a • v) = E (a • (∑ j : Fin P.e, P.basis j •
          ((algebraMap B F) ∘ row j))) := by rw [hv]
      _ = E (∑ j : Fin P.e, (a * P.basis j) •
          ((algebraMap B F) ∘ row j)) := by
            congr 1
            rw [Finset.smul_sum]
            apply Finset.sum_congr rfl
            intro j _hj
            rw [smul_smul]
      _ = ∑ j : Fin P.e, E ((a * P.basis j) •
          ((algebraMap B F) ∘ row j)) := by rw [map_sum]
      _ = ∑ j : Fin P.e, (a * P.basis j) •
          ((algebraMap B F) ∘ encode (row j)) := by
            apply Finset.sum_congr rfl
            intro j _hj
            exact extensionEncode_smul_algebraMap P encode
              (a * P.basis j) (row j)
      _ = a • (∑ j : Fin P.e, P.basis j •
          ((algebraMap B F) ∘ encode (row j))) := by
            rw [Finset.smul_sum]
            apply Finset.sum_congr rfl
            intro j _hj
            rw [smul_smul]
      _ = a • E v := by rw [hEv]

@[simp] lemma extensionEncodeLinearMap_apply {κ ι : Type*}
    {B F : Type*} [Field B] [Field F] [Algebra B F]
    (P : ExtensionFieldPresentation B F)
    (encode : (κ → B) →ₗ[B] (ι → B)) (v : κ → F) :
    extensionEncodeLinearMap P encode v = extensionEncode P encode v := rfl

/-- Scalar extension preserves injectivity of the base encoder.

The proof is coordinatewise: equality of extension codewords gives equality of the base
encodings of every coordinate row, and injectivity of `encode` recovers the message. -/
theorem extensionEncode_injective {κ ι : Type*}
    {B F : Type*} [Field B] [Field F] [Algebra B F]
    (P : ExtensionFieldPresentation B F)
    (encode : (κ → B) →ₗ[B] (ι → B)) (hencode : Function.Injective encode) :
    Function.Injective (extensionEncode P encode) := by
  intro v w hvw
  funext t
  apply P.basis.equivFun.injective
  funext j
  have hout : encode (fun u ↦ P.coord j (v u)) =
      encode (fun u ↦ P.coord j (w u)) := by
    funext i
    have hij := congrArg (P.coord j) (congrFun hvw i)
    simpa only [coord_extensionEncode] using hij
  exact congrFun (hencode hout) t

/-- Encoding an embedded base-field message is the same as embedding its base encoding:
`extensionEncode P encode (ψ ∘ v) = ψ ∘ encode v`, where `ψ = algebraMap B F`.

No systematicity is needed. Since `φ_j (ψ x) = x * φ_j 1`, the `j`-th coordinate row of
`ψ ∘ v` is the rescaling `φ_j 1 • v`, and `B`-linearity pulls that scalar back out of
`encode`; systematicity would only specialise the scalars `φ_j 1` to `(1, 0, …, 0)`. -/
theorem extensionEncode_comp_algebraMap {κ ι : Type*}
    {B F : Type*} [Field B] [Field F] [Algebra B F]
    (P : ExtensionFieldPresentation B F)
    (encode : (κ → B) →ₗ[B] (ι → B)) (v : κ → B) :
    extensionEncode P encode ((algebraMap B F) ∘ v) =
      (algebraMap B F) ∘ encode v := by
  have hpsi : ∀ (j : Fin P.e) (x : B),
      P.coord j (algebraMap B F x) = x * P.coord j (1 : F) := by
    intro j x
    have hx : (algebraMap B F) x = x • (1 : F) := by rw [Algebra.smul_def]; simp
    rw [hx, map_smul, smul_eq_mul]
  funext i
  apply P.basis.equivFun.injective
  funext j
  change P.coord j (extensionEncode P encode ((algebraMap B F) ∘ v) i) =
    P.coord j (((algebraMap B F) ∘ encode v) i)
  rw [coord_extensionEncode]
  have hin : (fun t ↦ P.coord j (((algebraMap B F) ∘ v) t)) = P.coord j (1 : F) • v := by
    funext t
    simp only [Function.comp_apply, Pi.smul_apply, smul_eq_mul, hpsi]
    exact mul_comm _ _
  rw [hin, map_smul]
  simp only [Function.comp_apply, Pi.smul_apply, smul_eq_mul, hpsi]
  exact mul_comm _ _

/-- The *extension code* of a base code `C_B ⊆ B^ι` along a presentation `P`, as a set of
words over `F`: those `v : ι → F` all of whose `e` coordinate projections lie in `C_B`,

  `v ∈ extensionCode P C_B ↔ ∀ j, (fun i ↦ P.coord j (v i)) ∈ C_B` .

This is the image of `extensionEncode` (see `range_extensionEncode`). It is closed under
addition when `C_B` is, and under `F`-scalar multiplication when `C_B` is `B`-linear; see
`extensionCodeSubmodule` for the bundled form. -/
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

/-- The image of the scalar-extended encoder is the extension code of the base encoder's
image. -/
theorem range_extensionEncode {κ ι : Type*}
    {B F : Type*} [Field B] [Field F] [Algebra B F]
    (P : ExtensionFieldPresentation B F)
    (encode : (κ → B) →ₗ[B] (ι → B)) :
    Set.range (extensionEncode P encode) =
      extensionCode P (LinearMap.range encode : Set (ι → B)) := by
  apply Set.eq_of_subset_of_subset
  · rintro _ ⟨v, rfl⟩ j
    refine ⟨fun t ↦ P.coord j (v t), ?_⟩
    funext i
    exact (coord_extensionEncode P encode v j i).symm
  · intro w hw
    have hrows : ∀ j : Fin P.e, ∃ vj : κ → B,
        encode vj = fun i ↦ P.coord j (w i) := by
      intro j
      exact hw j
    choose v hv using hrows
    refine ⟨fun t ↦ P.basis.equivFun.symm (fun j ↦ v j t), ?_⟩
    funext i
    apply P.basis.equivFun.injective
    funext j
    change P.coord j (extensionEncode P encode
      (fun t ↦ P.basis.equivFun.symm (fun j ↦ v j t)) i) = P.coord j (w i)
    rw [coord_extensionEncode]
    have hin : (fun t ↦ P.coord j (P.basis.equivFun.symm (fun j ↦ v j t))) = v j := by
      funext t
      change P.basis.equivFun (P.basis.equivFun.symm (fun j ↦ v j t)) j = v j t
      rw [P.basis.equivFun.apply_symm_apply]
    rw [hin, hv]

/-- `extensionCode` is closed under addition when the base code is, by additivity of the
coordinate maps. -/
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

/-- `extensionCode` is closed under the `B`-scalar action induced by `algebraMap B F`,
when the base code is `B`-scalar closed. This needs strictly less than
`extensionCode_smul_mem`, which additionally requires additive closure. -/
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

/-- Basis-free characterisation: for a `B`-submodule `C_B`, the extension code is the
`F`-span of the image of `C_B` under `ψ = algebraMap B F`,

  `extensionCode P C_B = Submodule.span F (ψ '' C_B)` ,

a right-hand side mentioning neither `e`, nor the basis, nor the coordinate maps.

For `⊆`, expand each entry of `v` in the basis. For `⊇`, the `j`-th coordinate of a finite
`F`-linear combination `∑ t, f t • (ψ ∘ a t)` is `∑ t, φ_j (f t) • a t`, which lies in `C_B`
by `B`-linearity. -/
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

/-- `extensionCode` is closed under `F`-scalar multiplication when the base code is
`B`-linear.

The hypotheses `hadd` and `hsmul` make `C_B` a `B`-submodule — its zero is `(0 : B) • c`
for any row `c`, and `0 < P.e` supplies one — after which `extensionCode_eq_span` exhibits
the code as an `F`-span. -/
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

/-- `extensionCode` of a `B`-submodule, bundled as an `F`-submodule of `ι → F`.

Its carrier is the `Set`-form `extensionCode`, so the two agree by `rfl`
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

/-- The carrier of `extensionCodeSubmodule` is the `Set`-form `extensionCode`. -/
@[simp] lemma coe_extensionCodeSubmodule {ι : Type*}
    {B F : Type*} [Field B] [Field F] [Algebra B F]
    (P : ExtensionFieldPresentation B F)
    (C_B : Submodule B (ι → B)) :
    (extensionCodeSubmodule P C_B : Set (ι → F)) =
      extensionCode P (C_B : Set (ι → B)) := rfl

/-- `Submodule` form of `extensionCode_eq_span`: `extensionCodeSubmodule` is the `F`-span
of `algebraMap '' C_B`. -/
theorem extensionCodeSubmodule_eq_span {ι : Type*}
    {B F : Type*} [Field B] [Field F] [Algebra B F]
    (P : ExtensionFieldPresentation B F) (C_B : Submodule B (ι → B)) :
    extensionCodeSubmodule P C_B =
      Submodule.span F ((fun c : ι → B ↦ (algebraMap B F) ∘ c) '' (C_B : Set (ι → B))) :=
  SetLike.coe_injective (extensionCode_eq_span P C_B)

/-- The extension code of a `B`-submodule does not depend on the presentation: any two
presentations of the same pair `(B, F)`, with possibly different bases and even different
`e`, give the same set of words, both being `Submodule.span F (algebraMap '' C_B)`.

The restriction to submodules is essential: for a general set `C_B` the coordinate-wise
definition does see the basis. -/
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

/-- For a `B`-submodule base code, the base code is exactly the part of the extension code
defined over `B`: `ψ ∘ c ∈ extensionCode P C_B ↔ c ∈ C_B`, where `ψ = algebraMap B F`.

Every coordinate row of `ψ ∘ c` is the rescaling `φ_j 1 • c`, so `←` is `B`-scalar closure
of `C_B` and `→` rescales by `φ_j 1⁻¹` at any coordinate with `φ_j 1 ≠ 0`, which exists
because `1 ≠ 0` in `F`. Compare `extensionEncode_comp_algebraMap` for the encoder-level
form. -/
theorem mem_extensionCode_comp_algebraMap_iff {ι : Type*}
    {B F : Type*} [Field B] [Field F] [Algebra B F]
    (P : ExtensionFieldPresentation B F)
    (C_B : Submodule B (ι → B)) (c : ι → B) :
    (algebraMap B F) ∘ c ∈ extensionCode P (C_B : Set (ι → B)) ↔ c ∈ C_B := by
  have hrow : ∀ j : Fin P.e,
      (fun i ↦ P.coord j (((algebraMap B F) ∘ c) i)) = P.coord j (1 : F) • c := by
    intro j
    funext i
    have hci : (algebraMap B F) (c i) = c i • (1 : F) := by rw [Algebra.smul_def]; simp
    simp only [Function.comp_apply, hci, map_smul, Pi.smul_apply, smul_eq_mul]
    exact mul_comm _ _
  constructor
  · intro h
    obtain ⟨j, hj⟩ : ∃ j : Fin P.e, P.coord j (1 : F) ≠ 0 := by
      by_contra hc
      push Not at hc
      exact one_ne_zero (P.basis.forall_coord_eq_zero_iff.1 hc)
    have hmem : P.coord j (1 : F) • c ∈ C_B := by rw [← hrow j]; exact h j
    have hscaled := C_B.smul_mem (P.coord j (1 : F))⁻¹ hmem
    rwa [smul_smul, inv_mul_cancel₀ hj, one_smul] at hscaled
  · intro hc j
    rw [hrow j]
    exact C_B.smul_mem _ hc

/-- The presentation-coordinate equivalence is a Hamming isometry carrying an extension
code onto the corresponding interleaved base code, so their minimum distances agree. -/
theorem minDist_extensionCode_eq_interleaved
    {ι : Type*} [Fintype ι]
    {B F : Type*} [Field B] [Field F] [Algebra B F] [DecidableEq B] [DecidableEq F]
    (P : ExtensionFieldPresentation B F) (C_B : Set (ι → B)) :
    Code.minDist (extensionCode P C_B) =
      Code.minDist (Code.interleavedCodeSet (κ := Fin P.e) C_B) := by
  let Ψ : (ι → F) ≃ (ι → Fin P.e → B) :=
    Equiv.piCongrRight (fun _ => P.basis.equivFun.toEquiv)
  have hφinj : Function.Injective (P.basis.equivFun : F → (Fin P.e → B)) :=
    P.basis.equivFun.injective
  have hham : ∀ x y : ι → F, hammingDist (Ψ x) (Ψ y) = hammingDist x y := by
    intro x y
    exact hammingDist_comp (fun (_ : ι) => (P.basis.equivFun : F → (Fin P.e → B)))
      (x := x) (y := y) (fun _ => hφinj)
  have hmem : ∀ v : ι → F,
      (Ψ v ∈ Code.interleavedCodeSet (κ := Fin P.e) C_B) ↔ v ∈ extensionCode P C_B := by
    intro v
    rfl
  unfold Code.minDist
  congr 1
  ext d
  constructor
  · rintro ⟨u, hu, v, hv, huv, hdist⟩
    refine ⟨Ψ u, (hmem u).2 hu, Ψ v, (hmem v).2 hv, Ψ.injective.ne huv, ?_⟩
    rw [hham]
    exact hdist
  · rintro ⟨u, hu, v, hv, huv, hdist⟩
    refine ⟨Ψ.symm u, (hmem (Ψ.symm u)).1 (by simpa),
      Ψ.symm v, (hmem (Ψ.symm v)).1 (by simpa), Ψ.symm.injective.ne huv, ?_⟩
    have h := hham (Ψ.symm u) (Ψ.symm v)
    have h' : hammingDist u v = hammingDist (Ψ.symm u) (Ψ.symm v) := by simpa using h
    exact h'.symm.trans hdist

/-- Scalar extension preserves minimum distance: for a `B`-linear base code,
`minDist (extensionCode P C_B) = minDist C_B`.

The proof factors through the coordinate Hamming isometry and the fact that nonempty
interleaving preserves minimum distance. -/
theorem minDist_extensionCode
    {ι : Type*} [Fintype ι]
    {B F : Type*} [Field B] [Field F] [Algebra B F] [DecidableEq B] [DecidableEq F]
    (P : ExtensionFieldPresentation B F) (C_B : Submodule B (ι → B)) :
    Code.minDist (extensionCode P (C_B : Set (ι → B))) =
      Code.minDist (C_B : Set (ι → B)) := by
  let : Nonempty (Fin P.e) := Fin.pos_iff_nonempty.mp P.e_pos
  rw [minDist_extensionCode_eq_interleaved]
  exact Code.minDist_interleavedCodeSet (κ := Fin P.e) (C_B : Set (ι → B))

/-- The list size of an extension code equals that of the `e`-fold interleaved base code,
at every radius `δ : ℝ`:

  `Lambda (extensionCode P C_B) δ = Lambda (Code.interleavedCodeSet C_B) δ` .

Applied componentwise, the coordinate isomorphism `P.basis.equivFun` is a Hamming isometry
`(ι → F) ≃ (ι → Fin e → B)` carrying `extensionCode` onto `Code.interleavedCodeSet`, so it
matches the sets of `δ`-close codewords bijectively. No restriction on `δ` is needed; in
particular the statement holds at `δ = 0` and at `δ ≥ 1`. -/
theorem lambda_extensionCode_eq_lambda_interleaved
    {ι : Type*} [Fintype ι]
    {B F : Type*} [Field B] [Field F] [Algebra B F]
    (P : ExtensionFieldPresentation B F)
    (C_B : Set (ι → B)) (δ : ℝ) :
    Lambda (extensionCode P C_B) δ =
      Lambda (Code.interleavedCodeSet (κ := Fin P.e) C_B) δ := by
  let : DecidableEq F := Classical.decEq F
  let : DecidableEq (Fin P.e → B) := Classical.decEq _
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
    simp only [Code.interleavedCodeSet, extensionCode, Set.mem_ofPred_eq]
    constructor
    · intro h j; exact h j
    · intro h j; exact h j
  have hset : ∀ f : ι → F,
      closeCodewordsRel (Code.interleavedCodeSet (κ := Fin P.e) C_B) (Ψ f) δ
        = Ψ '' (closeCodewordsRel (extensionCode P C_B) f δ) := by
    intro f
    ext c
    simp only [closeCodewordsRel, Code.relHammingBall, Set.mem_ofPred_eq, Set.mem_image]
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
      (closeCodewordsRel (Code.interleavedCodeSet (κ := Fin P.e) C_B) (Ψ f) δ).encard
        = (closeCodewordsRel (extensionCode P C_B) f δ).encard := by
    intro f
    rw [hset f, Ψ.injective.encard_image]
  unfold Lambda
  rw [← Equiv.iSup_comp (g := fun g => (closeCodewordsRel
        (Code.interleavedCodeSet (κ := Fin P.e) C_B) g δ).encard) Ψ]
  apply iSup_congr
  intro f
  rw [hcard f]

end CodingTheory

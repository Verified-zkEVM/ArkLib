/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XC0R
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon
public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
public import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# The dual of a Reed–Solomon code

The generalized Reed–Solomon code `grsCode domain deg v` with evaluation points `domain : ι ↪ F`
and column multipliers `v : ι → F` is the image of `Polynomial.degreeLT F deg` under the weighted
evaluation map `p ↦ (v i * p.eval (domain i))ᵢ`. At `v = 1` it is the Reed–Solomon code
`code domain deg`.

Let `domain` be `n = Fintype.card ι` distinct points and `w i = Lagrange.nodalWeight univ domain i`,
that is `w i = ∏ j ≠ i, (domain i - domain j)⁻¹`. The dual of `code domain k`, the orthogonal
complement for the dot product `dotProductBilin`, is `grsCode domain (n - k) w`, and
`code domain k` is the dual of `grsCode domain (n - k) w`. In particular `checkMatrix domain k` is a
parity-check matrix of `code domain k`. No relation between `k` and `n` is assumed.

## Main definitions

* `ReedSolomon.grsEvalOnPoints`: evaluation with column multipliers, as a linear map.
* `ReedSolomon.grsCode`: the generalized Reed–Solomon code, as a submodule.

`grsCode` is `noncomputable`, as `code` is: `Polynomial.degreeLT` is. `grsEvalOnPoints` is
computable.

## Main statements

* `ReedSolomon.orthogonal_code`: the dual of the Reed–Solomon code is a generalized Reed–Solomon
  code.
* `ReedSolomon.orthogonal_grsCode`: the Reed–Solomon code is the dual of that generalized
  Reed–Solomon code.
* `ReedSolomon.mem_code_iff_checkMatrix_mulVec_eq_zero`: `checkMatrix` is a parity-check matrix of
  the Reed–Solomon code.
* `ReedSolomon.byCheckMatrix_checkMatrix`: the same statement as an equality of codes.
* `ReedSolomon.dotProduct_eq_zero_of_mem_code`, `ReedSolomon.mem_code_iff_forall_dotProduct_eq_zero`
  and `ReedSolomon.forall_mem_code_dotProduct_eq_zero_iff`: the two duality statements as
  membership statements, with the generalized Reed–Solomon codewords written out.
-/

@[expose] public section

namespace ReedSolomon

open Polynomial Finset Matrix

/-! ### Generalized Reed–Solomon codes -/

section GeneralizedReedSolomon

variable {ι F : Type*} [CommSemiring F] (domain : ι ↪ F)

/-- Evaluation at the points `domain` with column multipliers `v`, the linear map
`p ↦ (v i * p.eval (domain i))ᵢ`. At `v = 1` it is `evalOnPoints domain`. -/
def grsEvalOnPoints (v : ι → F) : F[X] →ₗ[F] (ι → F) where
  toFun p i := v i * p.eval (domain i)
  map_add' p q := by ext; simp [mul_add]
  map_smul' c p := by ext; simp [mul_left_comm]

@[simp]
lemma grsEvalOnPoints_apply (v : ι → F) (p : F[X]) (i : ι) :
    grsEvalOnPoints domain v p i = v i * p.eval (domain i) :=
  rfl

/-- The generalized Reed–Solomon code with evaluation points `domain` and column multipliers `v`:
the words `(v i * p.eval (domain i))ᵢ` for the polynomials `p` of degree less than `deg`. It is the
image of `Polynomial.degreeLT F deg` under `grsEvalOnPoints domain v`, as `code domain deg` is the
image under `evalOnPoints domain`. -/
noncomputable def grsCode (deg : ℕ) (v : ι → F) : Submodule F (ι → F) :=
  (degreeLT F deg).map (grsEvalOnPoints domain v)

variable {domain} in
/-- A word lies in `grsCode domain deg v` iff it is `(v i * p.eval (domain i))ᵢ` for some
polynomial `p` of degree less than `deg`. -/
lemma mem_grsCode_iff {deg : ℕ} {v f : ι → F} :
    f ∈ grsCode domain deg v ↔ ∃ p ∈ degreeLT F deg, f = fun i ↦ v i * p.eval (domain i) := by
  simp only [grsCode, Submodule.mem_map]
  exact exists_congr fun p ↦ and_congr_right fun _ ↦ by rw [eq_comm]; rfl

/-- With all column multipliers `1`, the generalized Reed–Solomon code is the Reed–Solomon
code. -/
@[simp]
lemma grsCode_one (deg : ℕ) : grsCode domain deg 1 = code domain deg := by
  have : grsEvalOnPoints domain 1 = evalOnPoints domain := by
    ext p i
    simp [evalOnPoints]
  rw [grsCode, this, code]

end GeneralizedReedSolomon

/-! ### Duality -/

variable {ι F : Type*} [Fintype ι] [DecidableEq ι] [Field F] (domain : ι ↪ F)

/-- `Lagrange.coeff_eq_sum` on all of `ι`, with the weights written as `nodalWeight`. -/
private lemma sum_nodalWeight_mul_eval {P : F[X]} (hP : P.degree < Fintype.card ι) :
    ∑ i, Lagrange.nodalWeight univ domain i * P.eval (domain i) =
      P.coeff (Fintype.card ι - 1) := by
  rw [← card_univ, Lagrange.coeff_eq_sum domain.injective.injOn (by rwa [card_univ])]
  simp [Lagrange.nodalWeight, div_eq_mul_inv, prod_inv_distrib, mul_comm]

/-- If the weighted sums of `X ^ m * Y` vanish for all `m < d`, the top `d` coefficients of
`Y` vanish. -/
private lemma degree_lt_of_forall_sum_eq_zero {Y : F[X]} (hY : Y.degree < Fintype.card ι)
    {d : ℕ} (hd : d ≤ Fintype.card ι)
    (h : ∀ m < d, ∑ i, Lagrange.nodalWeight univ domain i * (X ^ m * Y).eval (domain i) = 0) :
    Y.degree < ↑(Fintype.card ι - d) := by
  induction d with
  | zero => simpa using hY
  | succ d ih =>
    have ih := ih (by omega) fun m hm ↦ h m (by omega)
    rw [degree_lt_iff_coeff_zero] at ih ⊢
    intro m hm
    rcases (show m = Fintype.card ι - (d + 1) ∨ Fintype.card ι - d ≤ m by omega) with rfl | hm'
    · have hXY : (X ^ d * Y).degree < ↑(Fintype.card ι) := by
        rw [degree_lt_iff_coeff_zero]
        intro j hj
        rw [coeff_X_pow_mul']
        split_ifs
        · exact ih _ (by omega)
        · rfl
      have := h d (by omega)
      rw [sum_nodalWeight_mul_eval domain hXY, coeff_X_pow_mul'] at this
      simp only [show d ≤ Fintype.card ι - 1 by omega, ↓reduceIte] at this
      rwa [show Fintype.card ι - 1 - d = Fintype.card ι - (d + 1) by omega] at this
    · exact ih m hm'

/-- Row `i` of `checkMatrix domain k` is the generalized Reed–Solomon codeword of `X ^ i`. -/
private lemma checkMatrix_mulVec_apply {k : ℕ} (f : ι → F) (i : Fin (Fintype.card ι - k)) :
    (checkMatrix domain k *ᵥ f) i =
      (fun j ↦ Lagrange.nodalWeight univ domain j * (X ^ (i : ℕ)).eval (domain j)) ⬝ᵥ f := by
  have hw (j : ι) : ((∏ l, (X - C (domain l))).derivative.eval (domain j))⁻¹ =
      Lagrange.nodalWeight univ domain j :=
    (Lagrange.nodalWeight_eq_eval_derivative_nodal (mem_univ j)).symm
  simp only [checkMatrix, mulVec, dotProduct, of_apply, hw, eval_pow, eval_X]
  exact sum_congr rfl fun j _ ↦ by ring

/-- A codeword of `code domain k` is orthogonal to `(w i * g.eval (domain i))ᵢ` for every `g` of
degree below `Fintype.card ι - k`, where `w = Lagrange.nodalWeight univ domain`. -/
theorem dotProduct_eq_zero_of_mem_code {k : ℕ} {f : ι → F} (hf : f ∈ code domain k) {g : F[X]}
    (hg : g ∈ degreeLT F (Fintype.card ι - k)) :
    (fun i ↦ Lagrange.nodalWeight univ domain i * g.eval (domain i)) ⬝ᵥ f = 0 := by
  obtain ⟨p, hp, rfl⟩ := mem_code_iff_exists_polynomial.1 hf
  rcases eq_or_ne g 0 with rfl | hg0
  · simp [dotProduct]
  rcases eq_or_ne p 0 with rfl | hp0
  · simp [dotProduct, evalOnPoints]
  have hg' := (natDegree_lt_iff_degree_lt hg0).2 (mem_degreeLT.1 hg)
  have hp' := (natDegree_lt_iff_degree_lt hp0).2 hp
  have hgp : (g * p).natDegree < Fintype.card ι - 1 := by
    rw [natDegree_mul hg0 hp0]
    omega
  have := sum_nodalWeight_mul_eval domain
    ((natDegree_lt_iff_degree_lt (mul_ne_zero hg0 hp0)).1 (by omega))
  rw [coeff_eq_zero_of_natDegree_lt hgp] at this
  simpa [dotProduct, evalOnPoints, mul_assoc] using this

omit [DecidableEq ι] in
/-- `checkMatrix domain k` is a parity-check matrix of `code domain k`. -/
theorem mem_code_iff_checkMatrix_mulVec_eq_zero {k : ℕ} {f : ι → F} :
    f ∈ code domain k ↔ checkMatrix domain k *ᵥ f = 0 := by
  classical
  refine ⟨fun hf ↦ funext fun i ↦ ?_, fun h ↦ ?_⟩
  · rw [checkMatrix_mulVec_apply]
    exact dotProduct_eq_zero_of_mem_code domain hf (mem_degreeLT.2 (by simp))
  obtain ⟨Y, hY, heval⟩ : ∃ Y : F[X], Y.degree < ↑(Fintype.card ι) ∧
      ∀ i, Y.eval (domain i) = f i :=
    ⟨_, by simpa using Lagrange.degree_interpolate_lt f (s := univ) domain.injective.injOn,
      fun i ↦ Lagrange.eval_interpolate_at_node f domain.injective.injOn (mem_univ i)⟩
  have hdeg := degree_lt_of_forall_sum_eq_zero domain hY (Nat.sub_le _ k) fun m hm ↦ by
    have := congrFun h ⟨m, hm⟩
    rw [checkMatrix_mulVec_apply] at this
    simpa [dotProduct, heval, mul_assoc] using this
  exact mem_code_of_polynomial_of_degree_lt_of_eval _
    (hdeg.trans_le (by norm_cast; omega)) fun i ↦ (heval i).symm

omit [DecidableEq ι] in
/-- The code with parity-check matrix `checkMatrix domain k` is `code domain k`. -/
theorem byCheckMatrix_checkMatrix (k : ℕ) :
    LinearCode.byCheckMatrix (checkMatrix domain k) = code domain k :=
  Submodule.ext fun _ ↦ (mem_code_iff_checkMatrix_mulVec_eq_zero domain).symm

/-- The Reed–Solomon code `code domain k` is the dual of the generalized Reed–Solomon code
`{(w i * g.eval (domain i))ᵢ | g ∈ degreeLT F (Fintype.card ι - k)}`, where
`w = Lagrange.nodalWeight univ domain`. As an equality of submodules this is
`orthogonal_grsCode`. -/
theorem mem_code_iff_forall_dotProduct_eq_zero {k : ℕ} {f : ι → F} :
    f ∈ code domain k ↔ ∀ g ∈ degreeLT F (Fintype.card ι - k),
      (fun i ↦ Lagrange.nodalWeight univ domain i * g.eval (domain i)) ⬝ᵥ f = 0 := by
  refine ⟨fun hf g hg ↦ dotProduct_eq_zero_of_mem_code domain hf hg, fun h ↦ ?_⟩
  rw [mem_code_iff_checkMatrix_mulVec_eq_zero]
  funext i
  rw [checkMatrix_mulVec_apply]
  exact h _ (mem_degreeLT.2 (by simp))

/-- The dual of the Reed–Solomon code `code domain k` is the generalized Reed–Solomon code
`{(w i * g.eval (domain i))ᵢ | g ∈ degreeLT F (Fintype.card ι - k)}`, where
`w = Lagrange.nodalWeight univ domain`. As an equality of submodules this is `orthogonal_code`. -/
theorem forall_mem_code_dotProduct_eq_zero_iff {k : ℕ} {u : ι → F} :
    (∀ f ∈ code domain k, u ⬝ᵥ f = 0) ↔ ∃ g ∈ degreeLT F (Fintype.card ι - k),
      u = fun i ↦ Lagrange.nodalWeight univ domain i * g.eval (domain i) := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · have hw (i : ι) : Lagrange.nodalWeight univ domain i ≠ 0 :=
      Lagrange.nodalWeight_ne_zero domain.injective.injOn (mem_univ i)
    obtain ⟨Y, hY, heval⟩ : ∃ Y : F[X], Y.degree < ↑(Fintype.card ι) ∧
        ∀ i, Y.eval (domain i) = u i / Lagrange.nodalWeight univ domain i :=
      ⟨_, by simpa using Lagrange.degree_interpolate_lt _ (s := univ) domain.injective.injOn,
        fun i ↦ Lagrange.eval_interpolate_at_node _ domain.injective.injOn (mem_univ i)⟩
    have hdeg := degree_lt_of_forall_sum_eq_zero domain hY (min_le_right k _) fun m hm ↦ by
      have := h _ (evalOnPoints_mem_code_of_degree_lt (p := X ^ m)
        (by simpa using (lt_min_iff.1 hm).1))
      rw [← this]
      refine sum_congr rfl fun i _ ↦ ?_
      simp [evalOnPoints, heval]
      field_simp [hw i]
    refine ⟨Y, mem_degreeLT.2 ?_, funext fun i ↦ ?_⟩
    · rwa [show Fintype.card ι - min k (Fintype.card ι) = Fintype.card ι - k by omega] at hdeg
    · rw [heval, mul_div_cancel₀ _ (hw i)]
  · rintro ⟨g, hg, rfl⟩ f hf
    exact dotProduct_eq_zero_of_mem_code domain hf hg

/-- **The dual of a Reed–Solomon code.** For the dot product, the orthogonal complement of
`code domain k` is the generalized Reed–Solomon code `grsCode domain (Fintype.card ι - k) w` with
column multipliers `w = Lagrange.nodalWeight univ domain`. -/
theorem orthogonal_code (k : ℕ) :
    LinearMap.BilinForm.orthogonal (dotProductBilin F F) (code domain k) =
      grsCode domain (Fintype.card ι - k) (Lagrange.nodalWeight univ domain) := by
  ext u
  rw [LinearMap.BilinForm.mem_orthogonal_iff, mem_grsCode_iff,
    ← forall_mem_code_dotProduct_eq_zero_iff]
  simp [dotProduct_comm]

/-- **The Reed–Solomon code as a dual.** For the dot product, `code domain k` is the orthogonal
complement of the generalized Reed–Solomon code `grsCode domain (Fintype.card ι - k) w` with
column multipliers `w = Lagrange.nodalWeight univ domain`. -/
theorem orthogonal_grsCode (k : ℕ) :
    LinearMap.BilinForm.orthogonal (dotProductBilin F F)
      (grsCode domain (Fintype.card ι - k) (Lagrange.nodalWeight univ domain)) = code domain k := by
  ext f
  simp only [LinearMap.BilinForm.mem_orthogonal_iff, mem_code_iff_forall_dotProduct_eq_zero,
    grsCode, Submodule.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂,
    dotProductBilin_apply_apply, grsEvalOnPoints, LinearMap.coe_mk, AddHom.coe_mk]

end ReedSolomon

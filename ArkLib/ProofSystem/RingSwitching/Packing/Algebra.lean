/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Quang Dao
-/
module

public import ArkLib.Data.MvPolynomial.Multilinear
public import CompPoly.LinearAlgebra.TensorProduct.Basis
public import ArkLib.ProofSystem.RingSwitching.Packing.Profile
public import ArkLib.ProofSystem.RingSwitching.Transport.Coeffs
public import ArkLib.ProofSystem.Sumcheck.Structured
public import Mathlib.Data.Fintype.Basic

/-!
# Packing algebra

The framework-independent algebra of the `Packing` ring switch: everything its verifier
computes, stated without any interactive-protocol vocabulary.

## Main components

1. **The pack/unpack pair** — `packMLE` reads each `2^κ`-block of a `B`-multilinear's
   Boolean-cube evaluations (its coefficients in the multilinear Lagrange basis) as one
   `L`-element along the basis, producing a multilinear in `κ` fewer
   variables; `unpackMLE` reverses it by reading off basis coordinates.
2. **Carrier operations** — the tensor-algebra carrier `L ⊗[K] L` with its two embeddings
   `φ₀ = · ⊗ 1`, `φ₁ = 1 ⊗ ·` and its row/column coordinate maps: the concrete data behind
   the tensor-product profile `tensorProductProfile` (defined at the end of this file).
3. **Verifier subroutines** — `embedded_MLP_eval`, the honest folded carrier element
   (the packed polynomial, coefficients embedded via `φ₁`, evaluated at the `φ₀`-image of
   the point's tail); `eqWeightedCoordSum`, the coordinate-reconstruction subroutine that
   every check applies to some coordinate family; `compute_A_func`/`compute_A_MLE`, the public
   multiplier that turns the batched claim into a sumcheck about the packed polynomial; and
   the batched target `compute_s0` and final equality value `compute_final_eq_value`.

Statement/witness types, the downstream-opening interface and the protocol relations live in
`Prelude.lean`, which re-exports this file.

## References

* [Diamond, B. E., and Posen, J., *Polylogarithmic Proofs for Multilinears over
  Binary Towers*][DP24], §2.5.
-/

@[expose] public section

noncomputable section

namespace RingSwitching

open Finset MvPolynomial TensorProduct
open Sumcheck.Structured

section Preliminaries

variable (κ : ℕ) [NeZero κ]
variable (L : Type) [CommRing L] [Fintype L] [DecidableEq L]
variable (K : Type) [CommRing K] [Fintype K] [DecidableEq K]
variable [Algebra K L]
variable (ℓ ℓ' : ℕ) [NeZero ℓ] [NeZero ℓ']
variable (h_l : ℓ = ℓ' + κ)

section TensorAlgebraOps
/-!
## The tensor-algebra carrier

The tensor-product carrier: `A = L ⊗[K] L`, its two embeddings
`φ₀ = · ⊗ 1` and `φ₁ = 1 ⊗ ·`, and the row/column coordinate maps with respect to a
`K`-basis `β` of `L`.
-/

/-- The tensor-product algebra `L ⊗[K] L`. -/
abbrev TensorAlgebra (K L : Type*) [CommRing K] [CommRing L] [Algebra K L] := L ⊗[K] L

/--
Column embedding φ₀: L → A as a ring homomorphism.
φ₀(α) = α ⊗ 1, operates on columns.
-/
def φ₀ (L K : Type*) [CommRing K] [CommRing L] [Algebra K L] : L →+* TensorAlgebra K L where
  toFun α := α ⊗ₜ[K] (1 : L)
  map_one' := rfl
  map_mul' α β := by simp only [Algebra.TensorProduct.tmul_mul_tmul, mul_one]
  map_zero' := by simp only [zero_tmul]
  map_add' α β := by simp only [add_tmul]

/--
Row embedding φ₁: L → A as a ring homomorphism.
φ₁(α) = 1 ⊗ α, operates on rows.
-/
def φ₁ (L K : Type*) [CommRing K] [CommRing L] [Algebra K L] : L →+* TensorAlgebra K L where
  toFun α := (1 : L) ⊗ₜ[K] α
  map_one' := by rfl
  map_mul' α β := by
    simp only [Algebra.TensorProduct.tmul_mul_tmul, mul_one]
  map_zero' := by simp only [tmul_zero]
  map_add' α β := by simp only [tmul_add]

open Module
/-- Row coordinates in `ŝ = ∑ u, β u ⊗ ŝ_u`, using the right-factor scalar action. -/
def decompose_tensor_algebra_rows {σ : Type*} (β : Basis σ K L)
    (s_hat : TensorAlgebra K L) : σ → L := by
  letI rightAlgebra : Algebra L (L ⊗[K] L) := Algebra.TensorProduct.rightAlgebra
  letI := rightAlgebra.toModule
  exact fun u => (β.baseChangeRight (Right := L)).repr s_hat u

/-- Column coordinates in `ŝ = ∑ v, ŝ_v ⊗ β v`, using the left-factor scalar action. -/
def decompose_tensor_algebra_columns {σ : Type*} (β : Basis σ K L)
    (s_hat : TensorAlgebra K L) : σ → L :=
  fun v => (β.baseChange L).repr s_hat v

omit [Fintype L] [DecidableEq L] [Fintype K] [DecidableEq K] in
/-- Row coordinates decompose the left factor of a pure tensor in the chosen basis. -/
@[simp]
theorem decompose_tensor_algebra_rows_tmul {σ : Type*} (β : Basis σ K L)
    (x y : L) (i : σ) :
    decompose_tensor_algebra_rows (L := L) (K := K) β (x ⊗ₜ[K] y) i = β.repr x i • y := by
  let rightAlgebra := Algebra.TensorProduct.rightAlgebra (R := K) (A := L) (B := L)
  let := rightAlgebra.toModule
  exact Basis.baseChangeRight_repr_tmul β x y i

omit [Fintype L] [DecidableEq L] [Fintype K] [DecidableEq K] in
/-- Column coordinates decompose the right factor of a pure tensor in the chosen basis. -/
@[simp]
theorem decompose_tensor_algebra_columns_tmul {σ : Type*} (β : Basis σ K L)
    (x y : L) (i : σ) :
    decompose_tensor_algebra_columns (L := L) (K := K) β (x ⊗ₜ[K] y) i = β.repr y i • x := by
  exact Basis.baseChange_repr_tmul L β x y i

/--
**MLE packing**: pack a small-ring multilinear `t` into a large-ring multilinear `t'` by
reinterpreting each chunk of `2^κ` coefficients as a single `L`-element along the basis `β`.
For each `w ∈ {0,1}^ℓ'`, the evaluation `t'(w)` is defined as:
`t'(w) := ∑_{v ∈ {0,1}^κ} t(v₀, ..., v_{κ-1}, w₀, ..., w_{ℓ'-1}) ⋅ β_v`
-/
def packMLE (β : Basis (Fin κ → Fin 2) K L) (t : MultilinearPoly K ℓ) :
    MultilinearPoly L ℓ' :=
  -- 1. Define the function that gives the evaluations of t' on the boolean hypercube.
  let packing_func (w : Fin ℓ' → Fin 2) : L :=
    -- a. Define a function that computes the K-coefficients for a given `w`.
    let coeffs_for_w (v : Fin κ → Fin 2) : K :=
      -- Construct the full evaluation point `(v, w)` of length `ℓ`.
      let concatenated_point (i : Fin ℓ) : Fin 2 :=
        if h : i.val < κ then
          v ⟨i.val, h⟩
        else
          w ⟨i.val - κ, by omega⟩
      -- Evaluate the small-field polynomial `t` at this point.
      MvPolynomial.eval (fun i => ↑(concatenated_point i)) t.val
    -- b. Use `equivFun.symm` = ∑ v, (coeffs_for_w v) • (β v).
    β.equivFun.symm coeffs_for_w
  -- 2. The packed polynomial `t'` is the multilinear extension of this function.
  ⟨MvPolynomial.MLE packing_func, MLE_mem_restrictDegree packing_func⟩

/--
**Unpacking a Packed Multilinear Polynomial**.
Reverses the packing defined in `packMLE`. It reconstructs the small-field
multilinear `t` from the large-field multilinear `t'`.

The evaluation of `t` at a point `(v, w)` is recovered by taking the evaluation
of `t'` at `w`, which is an element of `L`, and finding its `v`-th coordinate
with respect to the basis `β`.
-/
def unpackMLE (β : Basis (Fin κ → Fin 2) K L) (t' : MultilinearPoly L ℓ') :
    MultilinearPoly K ℓ :=
  -- 1. Define the function that gives the evaluations of the original small-field polynomial `t`.
  let unpacked_evals (p : Fin ℓ → Fin 2) : K :=
    -- a. Deconstruct the evaluation point `p` into `v` (first κ bits) and `w` (last ℓ' bits).
    let v (i : Fin κ) : Fin 2 := p ⟨i.val, by omega⟩
    let w (i : Fin ℓ') : Fin 2 := p ⟨i.val + κ, by { rw [h_l]; omega }⟩
    -- b. Evaluate the large-field polynomial `t'` at the point `w`.
    let t'_eval_at_w : L := MvPolynomial.eval (fun i => ↑(w i)) t'.val
    -- c. Get the K-coefficients of this L-element with respect to the basis `β`.
    -- `β.repr/β.equivFun` maps an element of L to its coordinate function `(Fin κ → Fin 2) → K`.
    let coeffs : (Fin κ → Fin 2) → K := β.repr t'_eval_at_w
    -- d. The desired evaluation t(p) = t(v,w)
      -- is the coefficient corresponding to the basis vector `β_v`.
    coeffs v
  -- 2. The unpacked polynomial `t` is the multilinear extension of this evaluation function.
  ⟨MvPolynomial.MLE unpacked_evals, MLE_mem_restrictDegree unpacked_evals⟩

/--
**Component-wise `φ₁` embedding**.
Takes a polynomial `t'` with coefficients in `L` and embeds it into a polynomial
with coefficients in the tensor algebra `A` by applying `φ₁` to each coefficient.
The multilinear (`d = 1`) case of the family-shared degree-generic coefficient transport
`RingSwitching.embedCoeffs` (`ArkLib/ProofSystem/RingSwitching/Transport/Coeffs.lean`).
-/
def componentWise_embed_MLE {A' : Type} [CommRing A'] (φ : L →+* A')
    (t' : MultilinearPoly L ℓ') : MultilinearPoly A' ℓ' :=
  embedCoeffs φ t'

/-- Binius-named alias: component-wise `φ₁` embedding into the tensor algebra `L ⊗[K] L`. -/
def componentWise_φ₁_embed_MLE (t' : MultilinearPoly L ℓ') :
    MultilinearPoly (TensorAlgebra K L) ℓ' :=
  componentWise_embed_MLE L ℓ' (A' := TensorAlgebra K L) (φ₁ L K) t'

end TensorAlgebraOps

end Preliminaries

section Verifier
open Module

variable (κ : ℕ) [NeZero κ]
variable (L : Type) [CommRing L] [Nontrivial L] [Fintype L] [DecidableEq L]
variable (K : Type) [CommRing K] [Fintype K] [DecidableEq K]
variable [Algebra K L]
variable (P : RingSwitchingProfile K L κ)
variable (ℓ ℓ' : ℕ) [NeZero ℓ] [NeZero ℓ']
variable (h_l : ℓ = ℓ' + κ)

/-- **The verifier's coordinate-reconstruction subroutine**: the eq̃-weighted sum
`∑_{u ∈ {0,1}^κ} eq̃(u, r) ⋅ c u` of a `2^κ`-indexed coordinate family `c` at the round
randomness `r` — equivalently, the evaluation at `r` of the multilinear extension of `c`
(Boolean points cast into `L`). Every DP24 verifier check below is this sum at a different
coordinate family and randomness: step 2 checks the original claim against the column
coordinates of `ŝ`, step 5 batches the row coordinates of `ŝ` into the sumcheck target `s₀`,
and step 8 weighs the row coordinates of the final eq̃-tensor. -/
def eqWeightedCoordSum (c : (Fin κ → Fin 2) → L) (r : Fin κ → L) : L :=
  Finset.sum Finset.univ fun (u : Fin κ → Fin 2) =>
    let u_as_L : Fin κ → L := fun i => if (u i == 1) then 1 else 0
    (eqTilde u_as_L r) * c u

/-- The honest folded carrier element: the packed polynomial, coefficients embedded via
`φ₁`, evaluated at the `φ₀`-image of the point's tail —
`ŝ := φ₁(t')(φ₀(r_κ), ..., φ₀(r_{ℓ-1}))`. This is the prover's batching-phase message; its
row/column coordinates carry the claims the verifier checks and batches. -/
def embedded_MLP_eval (t' : MultilinearPoly L ℓ') (r : Fin ℓ → L) :
    P.A :=
  -- This implements the identity:
  -- ŝ = Σ_{w ∈ {0,1}^ℓ'} eq̃(r_suffix, w) ⊗ t'(w)
  let r_suffix : Fin ℓ' → L :=
    fun i => r ⟨i.val + κ, by { rw [h_l]; omega }⟩
  let φ₁_mapped_t': MultilinearPoly P.A ℓ' := componentWise_embed_MLE L ℓ' P.φ₁ t'
  let φ₀_mapped_r: Fin ℓ' → P.A := fun i => P.φ₀ (r_suffix i)
  φ₁_mapped_t'.val.eval φ₀_mapped_r

/-- The verifier's claim-consistency check: the claimed evaluation `s` must equal the
eq̃-weighted reconstruction from `ŝ`'s column coordinates at the point prefix,
`s ?= Σ_{v ∈ {0,1}^κ} eqTilde(v, r_{0..κ-1}) ⋅ ŝ_v` — `eqWeightedCoordSum` at
`P.decomposeColumns` ([DP24] step 2, Check 1). -/
def performCheckOriginalEvaluation (s : L) (r : Fin ℓ → L) (s_hat : P.A) : Bool :=
  let r_prefix : Fin κ → L := fun i => r ⟨i.val, by omega⟩
  decide (s = eqWeightedCoordSum κ L (P.decomposeColumns s_hat) r_prefix)

/-- The batched-multiplier function on the cube: for each `w ∈ {0,1}^{ℓ'}`, decompose
`eq̃(r_κ, ..., r_{ℓ-1}, w_0, ..., w_{ℓ'-1}) =: Σ_{u ∈ {0,1}^κ} A_{w, u} ⋅ β_u` into basis
coordinates and batch those with the eq̃-weights of the batching scalars,
`A : w ↦ Σ_{u ∈ {0,1}^κ} eq̃(u_0, ..., u_{κ-1}, r''_0, ..., r''_{κ-1}) ⋅ A_{w, u}`
([DP24] step 4a).
-/
def compute_A_func (original_r_eval_suffix : Fin ℓ' → L)
    (r''_batching : Fin κ → L) : ((Fin (ℓ') → (Fin 2)) → L) :=
  fun w =>
    -- Decompose eq̃(r_suffix, w) into K-basis coefficients A_{w,u}
    let w_as_L : Fin ℓ' → L := fun i => if w i == 1 then 1 else 0
    -- `eq̃(r_κ, ..., r_{ℓ-1}, w_0, ..., w_{ℓ'-1})`
    let eq_w: L := eqTilde original_r_eval_suffix w_as_L
    let coords_A_w_u: (Fin κ → Fin 2) →₀ K := P.basis.repr eq_w
    -- Compute A(w) = Σ_{u ∈ {0,1}^κ} eq̃(u, r'') ⋅ A_{w,u}
    Finset.sum Finset.univ fun (u : Fin κ → Fin 2) =>
      let A_w_u : K := coords_A_w_u u
      let u_as_L : Fin κ → L := fun i => if u i == 1 then 1 else 0
      -- `eq̃(u_0, ..., u_{κ-1}, r''_0, ..., r''_{κ-1}) ⋅ A_{w, u}`
      let eq_u_r_batching : L := eqTilde u_as_L r''_batching
      A_w_u • eq_u_r_batching

/-- The batched multiplier `A(X_0, ..., X_{ℓ'-1})` — the multilinear extension of
`compute_A_func`, the public factor of the relocation sumcheck's polynomial `h = A · t'`
([DP24] step 4b). -/
def compute_A_MLE
    (original_r_eval_suffix : Fin ℓ' → L) (r''_batching : Fin κ → L) :
  MultilinearPoly L ℓ' :=
  let A_func := compute_A_func κ L K P ℓ' original_r_eval_suffix r''_batching
  let A_MLE: MultilinearPoly L ℓ' := ⟨MvPolynomial.MLE A_func, MLE_mem_restrictDegree A_func⟩
  A_MLE

/-- The last `ℓ'` coordinates of an evaluation point, the part not consumed by packing. -/
def getEvaluationPointSuffix (r : Fin ℓ → L) : Fin ℓ' → L :=
  fun i => r ⟨i.val + κ, by { rw [h_l]; omega }⟩

/-- The batched sumcheck target: `s₀ := Σ_{u ∈ {0,1}^κ} eqTilde(u, r'') ⋅ ŝ_u`, where `ŝ_u`
are the row components of `ŝ` — `eqWeightedCoordSum` at `P.decomposeRows` and the batching
scalars ([DP24] step 5). -/
def compute_s0 (s_hat : P.A) (r''_batching : Fin κ → L) : L :=
  eqWeightedCoordSum κ L (P.decomposeRows s_hat) r''_batching

/-- Compute the tensor `e := eq̃(φ₀(r_κ), ..., φ₀(r_{ℓ-1}), φ₁(r'_0), ..., φ₁(r'_{ℓ'-1}))` -/
def compute_final_eq_tensor (r : Fin ℓ → L) (r' : Fin ℓ' → L) : P.A :=
  let φ₀_mapped_r_suffix : Fin ℓ' → P.A := fun i =>
    P.φ₀ (r ⟨i.val + κ, by { rw [h_l]; omega }⟩)
  let φ₁_mapped_r': Fin ℓ' → P.A := fun i => P.φ₁ (r' i)
  eqTilde φ₀_mapped_r_suffix φ₁_mapped_r'

/-- Batch the row coordinates of the final equality tensor at `r''_batching`.
In the tensor carrier, first write `e = ∑ u, P.basis u ⊗ e_u`, then return
`∑ u, eqTilde(u, r''_batching) * e_u`, casting Boolean coordinates into `L`. -/
def compute_final_eq_value (r_eval : Fin ℓ → L)
    (r'_challenges : Fin ℓ' → L) (r''_batching : Fin κ → L) : L :=
  let e_tensor := compute_final_eq_tensor κ L K P ℓ ℓ' h_l r_eval r'_challenges
  eqWeightedCoordSum κ L (P.decomposeRows e_tensor) r''_batching

end Verifier

open Module in
/-- The tensor-product ring-switching profile associated with the basis `β`.

The two ring homomorphisms send `x` to `x ⊗ 1` and `1 ⊗ x`. Row coordinates use the
right-factor scalar action, and column coordinates use the left-factor scalar action. -/
@[reducible] def tensorProductProfile (κ : ℕ) [NeZero κ] (K L : Type)
    [Field K] [Field L] [Algebra K L] (β : Module.Basis (Fin κ → Fin 2) K L) :
    RingSwitchingProfile K L κ where
  basis := β
  A := TensorAlgebra K L
  commRingA := inferInstanceAs (CommRing (L ⊗[K] L))
  algLA := Algebra.TensorProduct.leftAlgebra
  φ₀ := φ₀ L K
  φ₁ := φ₁ L K
  decomposeRows := fun s => decompose_tensor_algebra_rows (L := L) (K := K) (β := β) s
  decomposeColumns := fun s => decompose_tensor_algebra_columns (L := L) (K := K) (β := β) s
  decomposeRows_spec := fun z => by
    let rightAlgebra : Algebra L (L ⊗[K] L) := Algebra.TensorProduct.rightAlgebra
    let rightModule : Module L (L ⊗[K] L) := rightAlgebra.toModule
    conv_lhs => rw [← (Basis.baseChangeRight (b := β) (Right := L)).sum_repr z]
    refine Finset.sum_congr rfl fun u _ => ?_
    unfold decompose_tensor_algebra_rows
    rw [Basis.baseChangeRight_apply, Algebra.smul_def]
    change algebraMap L (L ⊗[K] L) _ * _ = (φ₀ L K) _ * (φ₁ L K) _
    rw [show (algebraMap L (L ⊗[K] L)) =
      (Algebra.TensorProduct.includeRight).toRingHom.comp (algebraMap L L) by rfl]
    unfold φ₀ φ₁
    simp [Algebra.TensorProduct.tmul_mul_tmul]
  decomposeColumns_spec := fun z => by
    conv_lhs => rw [← (β.baseChange L).sum_repr z]
    refine Finset.sum_congr rfl fun v _ => ?_
    unfold decompose_tensor_algebra_columns
    rw [Basis.baseChange_apply, smul_tmul']
    change _ = (φ₀ L K) _ * (φ₁ L K) _
    unfold φ₀ φ₁
    simp [Algebra.TensorProduct.tmul_mul_tmul]
  decomposeRows_recompose := fun c => by
    classical
    funext u
    simp [decompose_tensor_algebra_rows, φ₀, φ₁,
      Algebra.TensorProduct.tmul_mul_tmul, map_sum, Basis.baseChangeRight_repr_tmul]
  decomposeColumns_recompose := fun c => by
    classical
    funext v
    simp [decompose_tensor_algebra_columns, φ₀, φ₁,
      Algebra.TensorProduct.tmul_mul_tmul, map_sum, Basis.baseChange_repr_tmul]
  embeddings_agree := fun b => by
    change (algebraMap K L b) ⊗ₜ[K] (1 : L) = (1 : L) ⊗ₜ[K] (algebraMap K L b)
    simpa only [Algebra.smul_def, mul_one] using
      (TensorProduct.smul_tmul (R := K) b (1 : L) (1 : L))

end RingSwitching

/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.InterleavedCode
public import ArkLib.Data.CodingTheory.ListDecodability.SymbolMap
public import ArkLib.Data.CodingTheory.ReedSolomon
public import Mathlib.FieldTheory.RatFunc.AsPolynomial

/-!
# List sizes of interleaved Reed–Solomon codes by packing into a larger ring

Let `φ : F →+* K` be injective and let `e : κ → K` be such that the packing map
`v ↦ ∑ j, φ (v j) * e j` from `κ → F` to `K` is injective. A codeword of the `κ`-fold interleaved
Reed–Solomon code of degree bound `k` over `F` has one message polynomial `P j` per row. Packing
each column gives the word `i ↦ ∑ j, φ (P j (x i)) * e j`, which is the evaluation of
`∑ j, e j • (P j).map φ` at the mapped points `φ (x i)`. That polynomial has degree below `k`, so
the packed word is a Reed–Solomon codeword over `K`. Since packing is injective on symbols, it
preserves relative distances, and every point list of the interleaved code embeds into a point
list of the scalar code over `K` (`Code.Lambda_le_of_injective_comp`). Hence

```text
Lambda (interleaved RS over F, width κ) δ ≤ Lambda (RS over K) δ
```

at every radius, independently of the width `|κ|`.

For `κ = Fin t` a packing always exists: take `K = RatFunc F`, the field of rational functions
`F(Z)`, and `e j = Z ^ j`, which sends `(a₀, …, aₜ₋₁)` to `a₀ + a₁ Z + ⋯ + aₜ₋₁ Z ^ (t - 1)`.
Consequently any scalar list-size bound that holds uniformly over fields, applied over `F(Z)`,
gives the same bound for every interleaving of the Reed–Solomon code over `F`. These are
coding-theoretic statements about all received words; they make no protocol claim.

## Main definitions

* `ReedSolomon.tupleRatFunc`: the packing `(a₀, …, aₜ₋₁) ↦ a₀ + a₁ Z + ⋯ + aₜ₋₁ Z ^ (t - 1)`.

## Main statements

* `ReedSolomon.comp_mem_code_map`: a Reed–Solomon codeword over `F` pushed through an injective
  ring homomorphism `φ` is a codeword over `K` on the mapped domain.
* `ReedSolomon.pack_comp_mem_code_map`: packed interleaved codewords are scalar codewords.
* `ReedSolomon.Lambda_interleaved_le_of_injective_pack`: the list-size inequality for any
  injective packing.
* `ReedSolomon.tupleRatFunc_injective` and `ReedSolomon.Lambda_interleaved_le_ratFunc`: the
  packing into `F(Z)` and the resulting inequality for `κ = Fin t`.
-/

@[expose] public section

namespace ReedSolomon

open Polynomial

section Pack

variable {ι κ F K : Type*} [Fintype κ] [Semiring F] [CommSemiring K]

/-- **Reed–Solomon codewords under a ring homomorphism.** If `w` is the evaluation of a
polynomial `P` of degree below `k` on `domain`, then `φ ∘ w` is the evaluation of `P.map φ`, also
of degree below `k`, on the mapped domain `φ ∘ domain`. Injectivity of `φ` is needed only to make
the mapped domain an embedding. -/
theorem comp_mem_code_map {F K : Type*} [Semiring F] [Semiring K] (domain : ι ↪ F) {k : ℕ}
    (φ : F →+* K) (hφ : Function.Injective φ) {w : ι → F} (hw : w ∈ code domain k) :
    φ ∘ w ∈ code (domain.trans ⟨φ, hφ⟩) k := by
  obtain ⟨P, hdeg, heval⟩ := mem_code_iff_eval.mp hw
  refine mem_code_iff_eval.mpr ⟨P.map φ, degree_map_le.trans_lt hdeg, fun i ↦ ?_⟩
  simp [eval_map, eval₂_at_apply, heval]

/-- **Packed interleaved codewords are scalar codewords.** If every row of the matrix `c` is a
Reed–Solomon codeword over `F` on `domain` of degree bound `k`, then packing each column `c i`
into `∑ j, φ (c i j) * e j` gives a Reed–Solomon codeword over `K` on the mapped domain, with the
same degree bound. The packed word is the `K`-linear combination `∑ j, e j • (φ ∘ row j)` of the
mapped rows, and the code over `K` is a `K`-submodule. No hypothesis on `e` is needed here. -/
theorem pack_comp_mem_code_map (domain : ι ↪ F) {k : ℕ} (φ : F →+* K)
    (hφ : Function.Injective φ) (e : κ → K) (c : ι → κ → F)
    (hc : c ∈ Code.interleavedCodeSet (κ := κ) (code domain k : Set (ι → F))) :
    (fun v : κ → F ↦ ∑ j, φ (v j) * e j) ∘ c ∈ code (domain.trans ⟨φ, hφ⟩) k := by
  have hsum : (fun v : κ → F ↦ ∑ j, φ (v j) * e j) ∘ c =
      ∑ j, e j • (φ ∘ fun i ↦ c i j) := by
    funext i
    simp [Finset.sum_apply, mul_comm]
  rw [hsum]
  exact Submodule.sum_mem _ fun j _ ↦ Submodule.smul_mem _ _ (comp_mem_code_map domain φ hφ (hc j))

/-- **List sizes of interleaved Reed–Solomon codes.** For an injective ring homomorphism
`φ : F →+* K` and an injective packing `v ↦ ∑ j, φ (v j) * e j` of `κ → F` into `K`, the
maximised list size of the `κ`-fold interleaved Reed–Solomon code over `F` is at most that of the
scalar Reed–Solomon code over `K` on the mapped domain, with the same degree bound and radius.

Injectivity of the packing is necessary. For `K = F`, `φ = id`, a single evaluation point,
degree bound `1` and radius `1`, both codes are their whole ambient spaces, so the interleaved
list has `|F| ^ |κ|` elements while the scalar list has `|F|`; no injective packing exists there
once `|κ| ≥ 2`. -/
theorem Lambda_interleaved_le_of_injective_pack [Fintype ι] (domain : ι ↪ F) (k : ℕ)
    (φ : F →+* K) (hφ : Function.Injective φ) (e : κ → K)
    (he : Function.Injective fun v : κ → F ↦ ∑ j, φ (v j) * e j) (δ : ℝ) :
    Code.Lambda (Code.interleavedCodeSet (κ := κ) (code domain k : Set (ι → F))) δ ≤
      Code.Lambda (code (domain.trans ⟨φ, hφ⟩) k : Set (ι → K)) δ :=
  Code.Lambda_le_of_injective_comp he (pack_comp_mem_code_map domain φ hφ e) δ

end Pack

section RatFunc

variable {F : Type*} [Field F]

/-- Pack a tuple `(a₀, …, aₜ₋₁)` over `F` into the rational function
`a₀ + a₁ Z + ⋯ + aₜ₋₁ Z ^ (t - 1)` of `F(Z)`. -/
noncomputable def tupleRatFunc {t : ℕ} (v : Fin t → F) : RatFunc F :=
  ∑ j, algebraMap F (RatFunc F) (v j) * RatFunc.X ^ (j : ℕ)

/-- `tupleRatFunc` is the image in `F(Z)` of the polynomial with coefficients `v`. -/
theorem tupleRatFunc_eq_algebraMap {t : ℕ} (v : Fin t → F) :
    tupleRatFunc v = algebraMap F[X] (RatFunc F) (∑ j, C (v j) * X ^ (j : ℕ)) := by
  simp [tupleRatFunc, map_sum, ← RatFunc.algebraMap_X]

/-- **Packing into `F(Z)` is injective** for every width `t`: the packed rational function is a
polynomial whose coefficients are the entries of the tuple. -/
theorem tupleRatFunc_injective {t : ℕ} : Function.Injective (tupleRatFunc (F := F) (t := t)) := by
  intro u v huv
  rw [tupleRatFunc_eq_algebraMap, tupleRatFunc_eq_algebraMap] at huv
  have hpoly := RatFunc.algebraMap_injective F huv
  funext j
  have hcoeff := congrArg (fun p : F[X] ↦ p.coeff j) hpoly
  simpa [finsetSum_coeff, coeff_C_mul, coeff_X_pow, Fin.val_inj] using hcoeff

/-- **Interleaved Reed–Solomon list sizes over `F(Z)`.** The maximised list size of the `t`-fold
interleaved Reed–Solomon code over `F` is at most that of the scalar Reed–Solomon code over the
rational-function field `F(Z)` on the same points, with the same degree bound and radius. So a
scalar list-size bound proved for all fields, applied over `F(Z)`, bounds every interleaving by
the same number. This is `Lambda_interleaved_le_of_injective_pack` with the packing
`tupleRatFunc`. -/
theorem Lambda_interleaved_le_ratFunc {ι : Type*} [Fintype ι] (domain : ι ↪ F) (k t : ℕ)
    (δ : ℝ) :
    Code.Lambda (Code.interleavedCodeSet (κ := Fin t) (code domain k : Set (ι → F))) δ ≤
      Code.Lambda (code (domain.trans ⟨algebraMap F (RatFunc F),
        (algebraMap F (RatFunc F)).injective⟩) k : Set (ι → RatFunc F)) δ :=
  Lambda_interleaved_le_of_injective_pack domain k (algebraMap F (RatFunc F)) _
    (fun j : Fin t ↦ RatFunc.X ^ (j : ℕ)) tupleRatFunc_injective δ

end RatFunc

end ReedSolomon

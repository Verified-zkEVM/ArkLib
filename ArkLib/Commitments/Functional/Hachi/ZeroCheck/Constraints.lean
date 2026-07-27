/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tobias Rothmann, Pablo Martín Vinuelas
-/
import ArkLib.Commitments.Functional.Hachi.RingSwitch.Reduction
import ArkLib.Data.MvPolynomial.LinearMvExtension
import ArkLib.Data.MvPolynomial.Multilinear
import ArkLib.ToCompPoly.Multivariate.Multilinear

/-!
  # Constraint encoding — Hachi Eqs. (21)–(23)

  The constraint-encoding layer of the Hachi §4.3 sumcheck: the table `w̃` (Eq. (21)), the two
  batched constraint polynomials `H₀` and `H_α` (Eqs. (23) and (22)), the sumcheck summands
  `F_{0,τ₀}` and `F_{α,τ₁}`, and the Kronecker challenge curve. These definitions are consumed by
  the batching bridge (`ZeroCheck/Batch.lean`), the zero-check round (`ZeroCheck/Reduction.lean`),
  the sumcheck rounds, and the final-evaluation step. Everything is stated over the lifted witness
  `LiftedWitness Φ μ n` and the weak-binding commitment `LiftCom` of `RingSwitch/Reduction.lean`.

  ## The table `w̃` (Eq. (21))

  `wTable` re-reads the committed pair `(z, r)` as an `F`-valued function on the `m₀`-cube: the
  rows are the `Zq`-coefficient vectors of the witness entries `zⱼ ∈ Rq` followed by those of the
  quotients `rᵢ`, and the columns are the `d` coefficient positions (`d = deg Φ.φ`). The arity
  `m₀` satisfies `2 ^ m₀ ≥ (μ + n)·d`; `m₁` is the row-batching arity, with `2 ^ m₁ ≥ n`.

  ## The batched constraint polynomials (Eqs. (22)–(23))

  * `hAlpha` (Eq. (22)): the `eq̃`-batched linear-constraint polynomial
    `H_α(τ) = ∑ᵢ eq̃(τ, i)·(∑_{u,ℓ} M̃_α(i,u)·w̃(u,ℓ)·α̃(ℓ) − yᵢ(α))`, multilinear in `m₁`
    variables. `H_α ≡ 0` holds iff every lifted row vanishes at `α`.
  * `hZero` (Eq. (23)): the `eq̃`-batched range polynomial
    `H₀(τ) = ∑_{u,ℓ} eq̃(τ, (u,ℓ))·w̃(u,ℓ)·∏_{j=1}^{b−1}(w̃(u,ℓ) − j)(w̃(u,ℓ) + j)`, multilinear
    in `m₀` variables. `H₀ ≡ 0` holds iff every table entry lies in `[−(b−1), b−1]`. No
    relation between `b` and `q` is needed for the soundness direction
    (`hZero_eq_zero_imp_liftShort`): a root pins down *some* integer representative of size
    `≤ b − 1`, and the centered representative is never larger.

  Both are built as multilinear extensions, hence have degree `≤ 1` in each variable.

  ## Computable representation

  The two constraint polynomials are *defined* over CompPoly's computable `CMvPolynomial`
  (`cHZero`/`cHAlpha`, via `CMvPolynomial.MLE`), matching the rest of the Hachi stack, whose
  witness ring `Rq Φ` and committed data `CMlPolynomial` are already CompPoly types. Their
  Mathlib images `hZero`/`hAlpha` are obtained by applying the bridge `fromCMvPolynomial`, and
  `hZero_eq_MLE`/`hAlpha_eq_MLE` identify those images with the corresponding
  `MvPolynomial.MLE`s. Relations (`relBatched`, `relZeroCheck`, `roundRel`) are stated over the
  computable objects; the soundness argument — Kronecker root counting, which needs Mathlib's
  `restrictDegree` submodule and `powAlgHom` — runs on the Mathlib side and is connected back by
  `cHZero_eq_zero_iff`/`eval_cHZero` and their `α`-counterparts
  (`ArkLib/ToCompPoly/Multivariate/Multilinear.lean`).

  The range side executes: `wTable`, `cHZero`, `cWTableMle`, `wTableMleEval` and even the Mathlib
  view `hZero` and its bundled form `hZeroML` are ordinary `def`s, so the prover's range
  polynomial and committed-table opening reduce to concrete monomial data.

  The `α` side executes as well: `LiftedWitness.r`, `cRowSum`, and `cEvalAt` use
  `CPolynomial`, so `hAlphaEvals` and `cHAlpha` contain no Mathlib polynomial computation.
  `hAlpha` remains the noncomputable Mathlib image used only by the root-counting proof.

  ## The sumcheck summands

  `F_{0,τ₀}` (`sumcheckPolyZero`) sums over the cube to `H₀(τ₀)` and has per-variable degree `2b`;
  `F_{α,τ₁}` (`sumcheckPolyAlpha`) sums to `H_α(τ₁) + zcTargetAlpha` and has per-variable degree
  `≤ 2`. These are the polynomials the sumcheck rounds operate on.

  ## The Kronecker curve (Fig. 5)

  `kroneckerPoint m ρ = (ρ, ρ², ρ⁴, …, ρ^{2^{m−1}})`. A multilinear polynomial in `m` variables,
  restricted to this curve, is univariate of degree `< 2^m`, and the restriction is injective on
  multilinear polynomials, so such a polynomial is determined by its values along the curve. The
  paper's Figure 5 samples the evaluation points `τ₀, τ₁` uniformly over `F^{m₀}` and `F^{m₁}`;
  this formalization instead derives them from two scalar seeds `(ρ₀, ρ_α)` along this curve, so
  the zero-check reduces `H₀ ≡ 0` and `H_α ≡ 0` to univariate root counting.

  ## References

  * [Nguyen, N. K., O'Rourke, G., and Zhang, J., *Hachi: Efficient Lattice-Based Multilinear
      Polynomial Commitments over Extension Fields*][NOZ26]
-/

namespace ArkLib.Lattices.Ajtai.InnerOuter

open CompPoly CPoly ArkLib.Lattices.CyclotomicModulus
open OracleComp OracleSpec ProtocolSpec CoordinateWise
open MvPolynomial

variable {q : ℕ} [NeZero q] [Fact (Nat.Prime q)] [BEq (ZMod q)] [LawfulBEq (ZMod q)]
  (Φ : CyclotomicModulus (ZMod q)) [IsCyclotomic Φ]
variable {n μ : ℕ} {E : Type} {F : Type} [Field F] [BEq F] [LawfulBEq F]
variable (m₀ m₁ : ℕ)

/-! ## The Kronecker curve and the soundness parameter -/

/-- The Kronecker curve `κ_m(ρ) = (ρ, ρ², ρ⁴, …, ρ^{2^{m−1}})`, along which a multilinear
polynomial in `m` variables restricts to a univariate polynomial of degree `< 2^m`. A re-export
of `LinearMvExtension.kroneckerPoint` under the name used by the zero-check and sumcheck files.
The zero-check derives its evaluation points along this curve (see the module docstring). -/
@[reducible] def kroneckerPoint (m : ℕ) (ρ : F) : Fin m → F :=
  LinearMvExtension.kroneckerPoint (m := m) ρ

/-- The number of distinct challenge seeds the zero-check needs per coordinate,
`D := max(2, 2^{m₀}, 2^{m₁})`. `2^{m₀}` and `2^{m₁}` are the degrees of the univariate Kronecker
restrictions of `H₀` and `H_α`, so that many roots determine each polynomial; the floor of `2`
meets the `2 ≤ k` requirement of the coordinate-wise special soundness structure. The paper's
Lemma 10 uses `max(2d, 2b−1)`. -/
def zeroCheckD (m₀ m₁ : ℕ) : ℕ := max 2 (max (2 ^ m₀) (2 ^ m₁))

theorem two_le_zeroCheckD (m₀ m₁ : ℕ) : 2 ≤ zeroCheckD m₀ m₁ := le_max_left _ _

theorem two_pow_m₀_le_zeroCheckD (m₀ m₁ : ℕ) : 2 ^ m₀ ≤ zeroCheckD m₀ m₁ :=
  (le_max_left _ _).trans (le_max_right _ _)

theorem two_pow_m₁_le_zeroCheckD (m₀ m₁ : ℕ) : 2 ^ m₁ ≤ zeroCheckD m₀ m₁ :=
  (le_max_right _ _).trans (le_max_right _ _)

/-- Per-round univariate degree of the range sumcheck summand `F_{0,τ₀}`, namely `2b`. -/
def roundDegZero (b : ℕ) : ℕ := 2 * b

/-- Per-round univariate degree of the linear sumcheck summand `F_{α,τ₁}`, namely `2`. -/
def roundDegAlpha : ℕ := 2

/-! ## The range factor and the table -/

/-- Hachi Eq. (23)'s per-entry range factor `P_b(v) = v·∏_{j=1}^{b-1} (v - j)·(v + j)`, the
vanishing polynomial of the symmetric range `{-(b-1), …, b-1}`. -/
def rangeProduct (b : ℕ) (v : F) : F :=
  v * ∏ j ∈ Finset.Icc 1 (b - 1), ((v - (j : F)) * (v + (j : F)))

omit [BEq F] [LawfulBEq F] in
/-- Over a field, `P_b(v) = 0` iff `v` is the image of an integer in the symmetric range
`{-(b-1), …, b-1}`. -/
theorem rangeProduct_eq_zero_iff {b : ℕ} {v : F} :
    rangeProduct b v = 0 ↔ ∃ j : ℕ, j ≤ b - 1 ∧ (v = (j : F) ∨ v = -(j : F)) := by
  unfold rangeProduct
  rw [mul_eq_zero, Finset.prod_eq_zero_iff]
  constructor
  · rintro (h0 | ⟨j, hj, hfac⟩)
    · exact ⟨0, Nat.zero_le _, Or.inl (by simpa using h0)⟩
    · rw [mul_eq_zero, sub_eq_zero, add_eq_zero_iff_eq_neg] at hfac
      exact ⟨j, (Finset.mem_Icc.mp hj).2, hfac⟩
  · rintro ⟨j, hjb, hv⟩
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · exact Or.inl (by rcases hv with hv | hv <;> simpa using hv)
    · refine Or.inr ⟨j, Finset.mem_Icc.mpr ⟨hj0, hjb⟩, ?_⟩
      rw [mul_eq_zero, sub_eq_zero, add_eq_zero_iff_eq_neg]
      exact hv

/-- The Eq. (21) table `w̃`: the committed pair `(z, r)` read as an `F`-valued function on the
`m₀`-cube. A cube point is decoded (via `finFunctionFinEquiv`) to a flat index `idx`, split into
`row := idx / d` and `column := idx % d` (`d = deg Φ.φ`). Rows `< μ` return the `Zq`-coefficients
of the witness entries `zⱼ ∈ Rq`; rows `μ ≤ · < μ + n` return the coefficients of the quotients
`rᵢ`; both are mapped through the base-field embedding `φF`, and all remaining cube points return
zero.

The coefficients are read directly rather than gadget-decomposed, so the range polynomial `H₀`
constrains the committed data itself: `H₀ ≡ 0` says every committed coefficient lies in
`[−(b−1), b−1]`. The `b` argument is unused here and kept for signature compatibility with
`hZero`. -/
def wTable (φF : ZMod q →+* F) (_b : ℕ) (w : LiftedWitness Φ μ n) :
    (Fin m₀ → Fin 2) → F :=
  fun pt =>
    let idx : ℕ := (finFunctionFinEquiv pt : Fin (2 ^ m₀))
    let d : ℕ := Φ.φ.natDegree
    if hz : idx / d < μ then
      φF ((w.z ⟨idx / d, hz⟩).1.coeff (idx % d))
    else if hr : idx / d - μ < n then
      φF ((w.r ⟨idx / d - μ, hr⟩).coeff (idx % d))
    else 0

/-- The `m₁`-cube point that encodes row `i : Fin n` (requires `n ≤ 2 ^ m₁`): the preimage of `i`
under the binary encoding `finFunctionFinEquiv : (Fin m₁ → Fin 2) ≃ Fin (2 ^ m₁)`. Cube points
encoding an index `≥ n` are the zero-padding of the batching cube. -/
def rowPoint (hn : n ≤ 2 ^ m₁) (i : Fin n) : Fin m₁ → Fin 2 :=
  finFunctionFinEquiv.symm ⟨(i : ℕ), lt_of_lt_of_le i.isLt hn⟩

/-- The Boolean-point coefficients of `H_α` (Eq. (22)): the `M̃_α`-contracted per-row value
`i ↦ (∑_{u,ℓ} M̃_α(i,u)·w̃(u,ℓ)·α̃(ℓ)) − yᵢ(α)`.

By the "represent the constraints by polynomials" identity of [NOZ26] §4.3, this contraction
equals the `α`-evaluated per-row defect of the lift relation `relLift`, namely
`evalAt α (∑ⱼ Mᵢⱼ·zⱼ) − evalAt α yᵢ − evalAt α (X^d+1)·evalAt α rᵢ`. It is defined here as that
defect, encoded into the `m₁`-cube via `rowPoint` and zero-padded on rows `≥ n`; the row equation
of `relLift` (Fig. 4) is recovered at the Boolean points via `hAlphaEvals_rowPoint`. The `b`
argument is unused here and kept for signature compatibility with `hAlpha`. -/
def hAlphaEvals (φF : ZMod q →+* F) (_b : ℕ) (s : RlinStatement Φ n μ) (α : F)
    (w : LiftedWitness Φ μ n) : (Fin m₁ → Fin 2) → F :=
  fun pt =>
    if h : ((finFunctionFinEquiv pt : Fin (2 ^ m₁)) : ℕ) < n then
      cEvalAt φF α (cRowSum Φ s w.z ⟨_, h⟩)
        - cEvalAt φF α (s.yvec ⟨_, h⟩).1
        - cEvalAt φF α Φ.φ * cEvalAt φF α (w.r ⟨_, h⟩)
    else 0

omit [NeZero q] [IsCyclotomic Φ] [BEq F] [LawfulBEq F] in
/-- At the Boolean point `rowPoint i`, the coefficient `hAlphaEvals` equals row `i`'s
`α`-evaluated lift defect. This links `hAlpha ≡ 0` (via `MLE_eq_zero_iff`) to the per-row
constraints of `relLift`. -/
theorem hAlphaEvals_rowPoint (φF : ZMod q →+* F) (b : ℕ) (s : RlinStatement Φ n μ) (α : F)
    (w : LiftedWitness Φ μ n) (hn : n ≤ 2 ^ m₁) (i : Fin n) :
    hAlphaEvals Φ m₁ φF b s α w (rowPoint m₁ hn i) =
      cEvalAt φF α (cRowSum Φ s w.z i) - cEvalAt φF α (s.yvec i).1
        - cEvalAt φF α Φ.φ * cEvalAt φF α (w.r i) := by
  simp only [hAlphaEvals, rowPoint, Equiv.apply_symm_apply, Fin.eta, i.isLt, dif_pos]

/-! ## The batched constraint polynomials -/

/-- `H₀` (Eq. (23)) over CompPoly's `CMvPolynomial`: the range polynomial, the multilinear
extension of the per-entry range factor `P_b(w̃(·))` in `τ ∈ F^{m₀}`. `H₀ ≡ 0` iff every table
entry is a root of the range product, i.e. lies in `[−(b−1), b−1]` — with no side condition
relating `b` to `q`, see `hZero_eq_zero_imp_liftShort`.

This is the primary definition; `hZero` is its Mathlib image. It is a genuine (computable) `def`:
`wTable`'s `z`-side reads `Rq` coefficients, which are CompPoly data. -/
def cHZero (φF : ZMod q →+* F) (b : ℕ) (w : LiftedWitness Φ μ n) :
    CMvPolynomial m₀ F :=
  CMvPolynomial.MLE fun v => rangeProduct b (wTable Φ m₀ φF b w v)

/-- `H_α` (Eq. (22)) over CompPoly's `CMvPolynomial`: the linear-constraint polynomial, the
multilinear extension of the `M̃_α`-contracted per-row values `hAlphaEvals`. `H_α ≡ 0` iff every
lifted row of `relLift` vanishes at `α`. Primary definition; `hAlpha` is its Mathlib image.

The coefficient table uses only computable `CPolynomial` row operations and evaluation. -/
def cHAlpha (φF : ZMod q →+* F) (b : ℕ) (s : RlinStatement Φ n μ) (α : F)
    (w : LiftedWitness Φ μ n) : CMvPolynomial m₁ F :=
  CMvPolynomial.MLE (hAlphaEvals Φ m₁ φF b s α w)

/-- The Mathlib view of `cHZero`, the form the Kronecker root-counting argument reasons about. -/
def hZero (φF : ZMod q →+* F) (b : ℕ) (w : LiftedWitness Φ μ n) :
    MvPolynomial (Fin m₀) F :=
  fromCMvPolynomial (cHZero Φ m₀ φF b w)

/-- The Mathlib view of `cHAlpha`. -/
noncomputable def hAlpha (φF : ZMod q →+* F) (b : ℕ) (s : RlinStatement Φ n μ) (α : F)
    (w : LiftedWitness Φ μ n) : MvPolynomial (Fin m₁) F :=
  fromCMvPolynomial (cHAlpha Φ m₁ φF b s α w)

/-! ### The computable/Mathlib correspondence

Each computable constraint polynomial and its Mathlib image agree as multilinear extensions,
are simultaneously zero, and have equal evaluations. These four lemma pairs are the only interface
the downstream files need. -/

omit [NeZero q] [IsCyclotomic Φ] in
/-- `hZero` is the `MvPolynomial.MLE` of the range table — the bridge from the computable
definition to the Mathlib multilinear-extension API. -/
theorem hZero_eq_MLE (φF : ZMod q →+* F) (b : ℕ) (w : LiftedWitness Φ μ n) :
    hZero Φ m₀ φF b w = MLE fun v => rangeProduct b (wTable Φ m₀ φF b w v) :=
  CMvPolynomial.fromCMvPolynomial_MLE _

omit [NeZero q] [IsCyclotomic Φ] in
/-- `hAlpha` is the `MvPolynomial.MLE` of the per-row defect table. -/
theorem hAlpha_eq_MLE (φF : ZMod q →+* F) (b : ℕ) (s : RlinStatement Φ n μ) (α : F)
    (w : LiftedWitness Φ μ n) :
    hAlpha Φ m₁ φF b s α w = MLE (hAlphaEvals Φ m₁ φF b s α w) :=
  CMvPolynomial.fromCMvPolynomial_MLE _

omit [NeZero q] [IsCyclotomic Φ] in
/-- The computable range polynomial vanishes iff its Mathlib image does. -/
theorem cHZero_eq_zero_iff (φF : ZMod q →+* F) (b : ℕ) (w : LiftedWitness Φ μ n) :
    cHZero Φ m₀ φF b w = 0 ↔ hZero Φ m₀ φF b w = 0 := by
  rw [hZero, eq_iff_fromCMvPolynomial, CPoly.map_zero]

omit [NeZero q] [IsCyclotomic Φ] in
/-- The computable linear-constraint polynomial vanishes iff its Mathlib image does. -/
theorem cHAlpha_eq_zero_iff (φF : ZMod q →+* F) (b : ℕ) (s : RlinStatement Φ n μ) (α : F)
    (w : LiftedWitness Φ μ n) :
    cHAlpha Φ m₁ φF b s α w = 0 ↔ hAlpha Φ m₁ φF b s α w = 0 := by
  rw [hAlpha, eq_iff_fromCMvPolynomial, CPoly.map_zero]

omit [NeZero q] [IsCyclotomic Φ] in
/-- Computable and Mathlib evaluation of the range polynomial agree. -/
theorem eval_cHZero (φF : ZMod q →+* F) (b : ℕ) (w : LiftedWitness Φ μ n) (a : Fin m₀ → F) :
    (cHZero Φ m₀ φF b w).eval a = MvPolynomial.eval a (hZero Φ m₀ φF b w) :=
  CPoly.eval_equiv

omit [NeZero q] [IsCyclotomic Φ] in
/-- Computable and Mathlib evaluation of the linear-constraint polynomial agree. -/
theorem eval_cHAlpha (φF : ZMod q →+* F) (b : ℕ) (s : RlinStatement Φ n μ) (α : F)
    (w : LiftedWitness Φ μ n) (a : Fin m₁ → F) :
    (cHAlpha Φ m₁ φF b s α w).eval a = MvPolynomial.eval a (hAlpha Φ m₁ φF b s α w) :=
  CPoly.eval_equiv

omit [NeZero q] [IsCyclotomic Φ] in
/-- `H₀` has degree `≤ 1` in each variable — it is a multilinear extension. This is the bound
that makes its Kronecker restriction univariate of degree `< 2 ^ m₀`. -/
theorem hZero_degreeOf_le (φF : ZMod q →+* F) (b : ℕ) (w : LiftedWitness Φ μ n)
    (j : Fin m₀) : (hZero Φ m₀ φF b w).degreeOf j ≤ 1 := by
  rw [hZero_eq_MLE]; exact MLE_degreeOf _ j

omit [NeZero q] [IsCyclotomic Φ] in
/-- `H_α` has degree `≤ 1` in each variable — it is a multilinear extension. -/
theorem hAlpha_degreeOf_le (φF : ZMod q →+* F) (b : ℕ) (s : RlinStatement Φ n μ) (α : F)
    (w : LiftedWitness Φ μ n) (j : Fin m₁) :
    (hAlpha Φ m₁ φF b s α w).degreeOf j ≤ 1 := by
  rw [hAlpha_eq_MLE]; exact MLE_degreeOf _ j

omit [NeZero q] [IsCyclotomic Φ] in
/-- The computable range polynomial is multilinear. -/
theorem cHZero_degreeOf_le (φF : ZMod q →+* F) (b : ℕ) (w : LiftedWitness Φ μ n)
    (j : Fin m₀) : (cHZero Φ m₀ φF b w).degreeOf j ≤ 1 :=
  CMvPolynomial.MLE_degreeOf _ j

omit [NeZero q] [IsCyclotomic Φ] in
/-- The computable linear-constraint polynomial is multilinear. -/
theorem cHAlpha_degreeOf_le (φF : ZMod q →+* F) (b : ℕ) (s : RlinStatement Φ n μ) (α : F)
    (w : LiftedWitness Φ μ n) (j : Fin m₁) :
    (cHAlpha Φ m₁ φF b s α w).degreeOf j ≤ 1 :=
  CMvPolynomial.MLE_degreeOf _ j

/-- `H₀` bundled as an element of the multilinear subtype `restrictDegree _ _ 1`, the form the
zero-check's root-counting argument (`arm_eq_zero_of_family`) takes as input. -/
def hZeroML (φF : ZMod q →+* F) (b : ℕ) (w : LiftedWitness Φ μ n) :
    MvPolynomial.restrictDegree (Fin m₀) F 1 :=
  ⟨hZero Φ m₀ φF b w,
    (mem_restrictDegree_iff_degreeOf_le _ _).mpr fun j => hZero_degreeOf_le Φ m₀ φF b w j⟩

/-- `H_α` bundled as an element of the multilinear subtype `restrictDegree _ _ 1`. -/
noncomputable def hAlphaML (φF : ZMod q →+* F) (b : ℕ) (s : RlinStatement Φ n μ) (α : F)
    (w : LiftedWitness Φ μ n) : MvPolynomial.restrictDegree (Fin m₁) F 1 :=
  ⟨hAlpha Φ m₁ φF b s α w,
    (mem_restrictDegree_iff_degreeOf_le _ _).mpr fun j => hAlpha_degreeOf_le Φ m₁ φF b s α w j⟩

/-- The computable multilinear extension of the table `w̃` itself, the committed object the
final-evaluation step opens. -/
def cWTableMle (φF : ZMod q →+* F) (b : ℕ) (w : LiftedWitness Φ μ n) :
    CMvPolynomial m₀ F :=
  CMvPolynomial.MLE (wTable Φ m₀ φF b w)

/-- Evaluation of the multilinear extension of the table `w̃` at a point `a ∈ F^{m₀}`:
`mle[w̃](a) = ∑ᵢ w̃(i)·eq̃(i, a)`. This is the evaluation claim carried into the final-evaluation
step (`Sumcheck/FinalEval.lean`). Computed on the computable representation. -/
def wTableMleEval (φF : ZMod q →+* F) (b : ℕ) (w : LiftedWitness Φ μ n)
    (a : Fin m₀ → F) : F :=
  (cWTableMle Φ m₀ φF b w).eval a

omit [NeZero q] [IsCyclotomic Φ] in
/-- `wTableMleEval` agrees with evaluating Mathlib's multilinear extension of `w̃`. -/
theorem wTableMleEval_eq (φF : ZMod q →+* F) (b : ℕ) (w : LiftedWitness Φ μ n)
    (a : Fin m₀ → F) :
    wTableMleEval Φ m₀ φF b w a = MvPolynomial.eval a (MLE (wTable Φ m₀ φF b w)) := by
  rw [wTableMleEval, cWTableMle, CPoly.eval_equiv, CMvPolynomial.fromCMvPolynomial_MLE]

/-! ## Range-side soundness: `H₀ ≡ 0 ⇒ liftShort`

The range polynomial is load-bearing: an identically-zero `H₀^{w̃}` forces every committed
coefficient into the symmetric range `[−(b−1), b−1]`, hence `w̃` is short. This is what lets the
batching bridge *derive* `liftShort` rather than assume it (NOZ26 §4.3, Eqs. (20)–(23)). -/

omit [IsCyclotomic Φ] [BEq (ZMod q)] [LawfulBEq (ZMod q)] [BEq F] [LawfulBEq F] in
/-- A residue whose `φF`-image is a root of the range factor `P_b` has a small centered
representative: `P_b(φF c) = 0` gives `|c|₋ ≤ b − 1`. The field roots `{0, ±1, …, ±(b−1)}` pull
back injectively (`φF` is a ring hom out of the field `ZMod q`) to residues `c = ±j` with
`j ≤ b − 1`, and `±j` is then an integer representative of `c` of absolute value `≤ b − 1`; since
`valMinAbs` is *minimal* among all representatives (`valMinAbs_natAbs_le`), the centered one is no
larger. No anti-wraparound side condition such as `b − 1 ≤ q/2` is needed: a residue can only ever
get *closer* to zero when `q` is small. -/
theorem valMinAbs_natAbs_le_of_rangeProduct_eq_zero (φF : ZMod q →+* F) {b : ℕ}
    {c : ZMod q} (h : rangeProduct b (φF c) = 0) :
    (c.valMinAbs).natAbs ≤ b - 1 := by
  have hφ : Function.Injective φF := φF.injective
  rw [rangeProduct_eq_zero_iff] at h
  obtain ⟨j, hjb, hv⟩ := h
  have hcj : c = (j : ZMod q) ∨ c = -(j : ZMod q) := by
    rcases hv with hv | hv
    · exact Or.inl (hφ (by rw [hv, map_natCast]))
    · exact Or.inr (hφ (by rw [hv, _root_.map_neg, map_natCast]))
  rcases hcj with rfl | rfl
  · exact le_trans (valMinAbs_natAbs_le (j : ℤ) (by push_cast; ring)) (by simpa using hjb)
  · exact le_trans (valMinAbs_natAbs_le (-(j : ℤ)) (by push_cast; ring)) (by simpa using hjb)

omit [NeZero q] [IsCyclotomic Φ] [BEq F] [LawfulBEq F] in
/-- The table value at the cube point encoding the `z`-block coordinate `(i, k)` (row `i < μ`,
column `k < deg φ`) is the embedded coefficient `φF((zᵢ).coeff k)`. -/
theorem wTable_zRow (φF : ZMod q →+* F) (b : ℕ) (w : LiftedWitness Φ μ n)
    (hd : 0 < Φ.φ.natDegree) (i : Fin μ) {k : ℕ} (hk : k < Φ.φ.natDegree)
    (hlt : Φ.φ.natDegree * (i : ℕ) + k < 2 ^ m₀) :
    wTable Φ m₀ φF b w (finFunctionFinEquiv.symm ⟨Φ.φ.natDegree * (i : ℕ) + k, hlt⟩) =
      φF ((w.z i).1.coeff k) := by
  have hdiv : (Φ.φ.natDegree * (i : ℕ) + k) / Φ.φ.natDegree = (i : ℕ) := by
    rw [Nat.mul_add_div hd, Nat.div_eq_of_lt hk, Nat.add_zero]
  have hmod : (Φ.φ.natDegree * (i : ℕ) + k) % Φ.φ.natDegree = k := by
    have h := Nat.div_add_mod (Φ.φ.natDegree * (i : ℕ) + k) Φ.φ.natDegree
    rw [hdiv] at h; omega
  simp only [wTable, Equiv.apply_symm_apply, Fin.val_mk, hdiv, hmod, i.isLt, dif_pos, Fin.eta]

omit [NeZero q] [IsCyclotomic Φ] [BEq F] [LawfulBEq F] in
/-- The table value at the cube point encoding the `r`-block coordinate `(i, k)` (row `μ + i`,
column `k < deg φ`) is the embedded coefficient `φF((rᵢ).coeff k)`. -/
theorem wTable_rRow (φF : ZMod q →+* F) (b : ℕ) (w : LiftedWitness Φ μ n)
    (hd : 0 < Φ.φ.natDegree) (i : Fin n) {k : ℕ} (hk : k < Φ.φ.natDegree)
    (hlt : Φ.φ.natDegree * (μ + (i : ℕ)) + k < 2 ^ m₀) :
    wTable Φ m₀ φF b w (finFunctionFinEquiv.symm ⟨Φ.φ.natDegree * (μ + (i : ℕ)) + k, hlt⟩) =
      φF ((w.r i).coeff k) := by
  have hdiv : (Φ.φ.natDegree * (μ + (i : ℕ)) + k) / Φ.φ.natDegree = μ + (i : ℕ) := by
    rw [Nat.mul_add_div hd, Nat.div_eq_of_lt hk, Nat.add_zero]
  have hmod : (Φ.φ.natDegree * (μ + (i : ℕ)) + k) % Φ.φ.natDegree = k := by
    have h := Nat.div_add_mod (Φ.φ.natDegree * (μ + (i : ℕ)) + k) Φ.φ.natDegree
    rw [hdiv] at h; omega
  simp only [wTable, Equiv.apply_symm_apply, Fin.val_mk, hdiv, hmod]
  rw [dif_neg (by omega : ¬ μ + (i : ℕ) < μ), dif_pos (by omega : μ + (i : ℕ) - μ < n)]
  simp only [Nat.add_sub_cancel_left, Fin.eta]

omit [IsCyclotomic Φ] in
/-- **Range-side soundness (F5).** If the batched range polynomial `H₀^{w̃}` vanishes
identically then `w̃` is short. Each committed coefficient is a table entry (`wTable`), hence a
root of `P_b` (`MLE_eq_zero_iff`), hence a centered residue of absolute value `≤ b − 1`
(`valMinAbs_natAbs_le_of_rangeProduct_eq_zero`); the norm bounds follow because the declared
bounds dominate the range base (`b − 1 ≤ bound`, `b − 1 ≤ rBound`). The arity
`(μ + n)·deg φ ≤ 2^{m₀}` guarantees every coefficient position is a genuine cube point. This is
the derivation that makes the range machinery load-bearing: `liftShort` is *proved* from
`H₀ ≡ 0`, not assumed. -/
theorem hZero_eq_zero_imp_liftShort (φF : ZMod q →+* F) (b bound rBound : ℕ)
    (hd : 0 < Φ.φ.natDegree) (hμn : (μ + n) * Φ.φ.natDegree ≤ 2 ^ m₀)
    (hbound : b - 1 ≤ bound) (hrBound : b - 1 ≤ rBound)
    (w : LiftedWitness Φ μ n) (h : hZero Φ m₀ φF b w = 0) :
    liftShort Φ bound rBound w := by
  rw [hZero_eq_MLE, MvPolynomial.MLE_eq_zero_iff] at h
  refine ⟨?_, ?_⟩
  · -- z-side: `vecLInftyNorm w.z ≤ bound`
    apply Finset.sup_le
    intro i _
    apply Finset.sup_le
    intro k hk
    rw [Finset.mem_range] at hk
    have hi := i.isLt
    have hlt : Φ.φ.natDegree * (i : ℕ) + k < 2 ^ m₀ := by
      have s1 : Φ.φ.natDegree * (i : ℕ) + k < Φ.φ.natDegree * ((i : ℕ) + 1) := by
        rw [Nat.mul_succ]; omega
      have s2 : Φ.φ.natDegree * ((i : ℕ) + 1) ≤ (μ + n) * Φ.φ.natDegree := by
        rw [Nat.mul_comm]; exact Nat.mul_le_mul (by omega) (le_refl _)
      omega
    have hval := h (finFunctionFinEquiv.symm ⟨Φ.φ.natDegree * (i : ℕ) + k, hlt⟩)
    rw [wTable_zRow Φ m₀ φF b w hd i hk hlt] at hval
    exact le_trans (valMinAbs_natAbs_le_of_rangeProduct_eq_zero φF hval) hbound
  · -- r-side: `rShort rBound w.r`
    intro i k
    by_cases hkd : k < Φ.φ.natDegree
    · have hi := i.isLt
      have hlt : Φ.φ.natDegree * (μ + (i : ℕ)) + k < 2 ^ m₀ := by
        have s1 : Φ.φ.natDegree * (μ + (i : ℕ)) + k < Φ.φ.natDegree * (μ + (i : ℕ) + 1) := by
          rw [Nat.mul_succ]; omega
        have s2 : Φ.φ.natDegree * (μ + (i : ℕ) + 1) ≤ (μ + n) * Φ.φ.natDegree := by
          rw [Nat.mul_comm]; exact Nat.mul_le_mul (by omega) (le_refl _)
        omega
      have hval := h (finFunctionFinEquiv.symm ⟨Φ.φ.natDegree * (μ + (i : ℕ)) + k, hlt⟩)
      rw [wTable_rRow Φ m₀ φF b w hd i hkd hlt] at hval
      exact le_trans (valMinAbs_natAbs_le_of_rangeProduct_eq_zero φF hval) hrBound
    · -- `k ≥ deg φ`: the coefficient is zero, so trivially short
      have hz : (w.r i).coeff k = 0 := by
        rw [CPolynomial.coeff_toPoly]
        apply Polynomial.coeff_eq_zero_of_natDegree_lt
        rw [← CPolynomial.natDegree_toPoly]
        have := w.hr i; omega
      rw [hz]; simp [ZMod.valMinAbs_zero]

/-! ## The sumcheck summands -/

/-- The range sumcheck summand `F_{0,τ₀}`, characterized by `∑_{x} F_{0,τ₀}(x) = H₀(τ₀)`
(`sum_sumcheckPolyZero`) with per-variable degree `roundDegZero b = 2b`.

Unlike `H₀`/`H_α` this one is genuinely evaluated by the prover in every sumcheck round, so it is
carried in the computable representation (it is *not* multilinear, hence not an
`CMvPolynomial.MLE`). -/
def sumcheckPolyZero (φF : ZMod q →+* F) (b : ℕ) (τ₀ : Fin m₀ → F)
    (w : LiftedWitness Φ μ n) : CMvPolynomial m₀ F :=
  sorry

/-- The linear sumcheck summand `F_{α,τ₁}`, characterized by
`∑_{x} F_{α,τ₁}(x) = H_α(τ₁) + zcTargetAlpha` (`sum_sumcheckPolyAlpha`) with per-variable degree
`roundDegAlpha = 2`. Also prover-evaluated, hence computable. -/
def sumcheckPolyAlpha (φF : ZMod q →+* F) (b : ℕ) (s : RlinStatement Φ n μ) (α : F)
    (τ₁ : Fin m₁ → F) (w : LiftedWitness Φ μ n) : CMvPolynomial m₀ F :=
  sorry

/-- The public initial target of the linear sumcheck, `∑ᵢ eq̃(τ₁, i)·yᵢ(α)`, which the verifier
computes from the statement alone. -/
def zcTargetAlpha (φF : ZMod q →+* F) (s : RlinStatement Φ n μ) (α : F)
    (τ₁ : Fin m₁ → F) : F :=
  sorry

/-- Partial sum of `H` over the trailing cube coordinates: `hypercubeSum H i cs =
∑_{x ∈ {0,1}^{m₀ − i}} H(cs, x)`, where `cs` fixes the first `i` coordinates. Operates on the
computable representation — this is the fold the prover actually runs. -/
def hypercubeSum (H : CMvPolynomial m₀ F) (i : ℕ) (cs : Fin i → F) : F :=
  sorry

/-- The full-cube sum of the range summand `F_{0,τ₀}` equals `H₀(τ₀)`. -/
theorem sum_sumcheckPolyZero (φF : ZMod q →+* F) (b : ℕ) (τ₀ : Fin m₀ → F)
    (w : LiftedWitness Φ μ n) :
    hypercubeSum m₀ (sumcheckPolyZero Φ m₀ φF b τ₀ w) 0 (fun j => j.elim0) =
      (cHZero Φ m₀ φF b w).eval τ₀ := by
  sorry

omit [NeZero q] in
/-- `sum_sumcheckPolyZero` in Mathlib terms, via `eval_cHZero`. -/
theorem sum_sumcheckPolyZero' (φF : ZMod q →+* F) (b : ℕ) (τ₀ : Fin m₀ → F)
    (w : LiftedWitness Φ μ n) :
    hypercubeSum m₀ (sumcheckPolyZero Φ m₀ φF b τ₀ w) 0 (fun j => j.elim0) =
      MvPolynomial.eval τ₀ (hZero Φ m₀ φF b w) := by
  rw [sum_sumcheckPolyZero, eval_cHZero]

/-- The full-cube sum of the linear summand `F_{α,τ₁}` equals `H_α(τ₁) + zcTargetAlpha`. -/
theorem sum_sumcheckPolyAlpha (φF : ZMod q →+* F) (b : ℕ) (s : RlinStatement Φ n μ) (α : F)
    (τ₁ : Fin m₁ → F) (w : LiftedWitness Φ μ n) :
    hypercubeSum m₀ (sumcheckPolyAlpha Φ m₀ m₁ φF b s α τ₁ w) 0 (fun j => j.elim0) =
      (cHAlpha Φ m₁ φF b s α w).eval τ₁ + zcTargetAlpha Φ m₁ φF s α τ₁ := by
  sorry

omit [NeZero q] in
/-- `sum_sumcheckPolyAlpha` in Mathlib terms, via `eval_cHAlpha`. -/
theorem sum_sumcheckPolyAlpha' (φF : ZMod q →+* F) (b : ℕ) (s : RlinStatement Φ n μ) (α : F)
    (τ₁ : Fin m₁ → F) (w : LiftedWitness Φ μ n) :
    hypercubeSum m₀ (sumcheckPolyAlpha Φ m₀ m₁ φF b s α τ₁ w) 0 (fun j => j.elim0) =
      MvPolynomial.eval τ₁ (hAlpha Φ m₁ φF b s α w) + zcTargetAlpha Φ m₁ φF s α τ₁ := by
  rw [sum_sumcheckPolyAlpha, eval_cHAlpha]

/-! ## Statement types of the zero-check and sumcheck stages -/

/-- The zero-check's output statement: the lift statement extended by the two challenge seeds
`(ρ₀, ρ_α)`. The batching points are derived from them along the Kronecker curve,
`τ₀ = κ_{m₀}(ρ₀)` and `τ_α = κ_{m₁}(ρ_α)`. -/
structure ZeroCheckStatement (Φ : CyclotomicModulus (ZMod q)) (TCom F : Type) (n μ : ℕ) where
  /-- The `R^lin` statement, carrying the public `M`, `yvec`, and `bound`. -/
  rlin : RlinStatement Φ n μ
  /-- The commitment to `w̃` from the lift stage. -/
  t : TCom
  /-- The ring-switching evaluation challenge `α` from the lift stage ([HMZ25], Fig. 4). -/
  α : F
  /-- The seed `ρ₀` from which the range check's evaluation point is derived. -/
  seed₀ : F
  /-- The seed `ρ_α` from which the linear check's evaluation point is derived. -/
  seedα : F

/-- The statement after `i` sumcheck rounds: the zero-check statement, the `i` challenges drawn so
far, and the current range and linear sumcheck targets. -/
structure RoundStatement (Φ : CyclotomicModulus (ZMod q)) (TCom F : Type) (n μ : ℕ)
    (i : ℕ) where
  /-- The zero-check statement (public data, commitment, `α`, and the two seeds). -/
  zc : ZeroCheckStatement Φ TCom F n μ
  /-- The sumcheck challenges drawn so far. -/
  challenges : Fin i → F
  /-- The current target of the range sumcheck. -/
  target₀ : F
  /-- The current target of the linear sumcheck. -/
  targetα : F

variable (bound rBound : ℕ)

/-- The per-round relation of the paired sumcheck ([NOZ26] Lemma 11): `w̃` opens `t`, is short
carries the range identity `H₀^{w̃} ≡ 0`, and both partial-hypercube-sum claims at the current
challenge prefix equal the current targets. The final conjunct `bound ≤ rlin.bound` ties the global
norm parameter to the statement's declared bound.

**Shortness is not assumed here.** Where this relation previously carried a `liftShort` conjunct it
now carries `cHZero … = 0`, from which `liftShort` is *derived* on demand by
`hZero_eq_zero_imp_liftShort` — the same derivation the batching bridge uses. Lemma 11's extraction
plan routes differing openings through the norm-conditioned `K.collision_mem`, and that shortness
is now discharged from `H₀ ≡ 0` rather than assumed. See `relZeroCheck`. -/
def roundRel (K : LiftCom (LiftedWitness Φ μ n) E (liftShort Φ bound rBound))
    (φF : ZMod q →+* F) (b : ℕ) (i : ℕ) :
    Set (RoundStatement Φ K.TCom F n μ i × LiftedWitness Φ μ n) :=
  {p |
    K.com p.2 = p.1.zc.t ∧
    cHZero Φ m₀ φF b p.2 = 0 ∧
    hypercubeSum m₀ (sumcheckPolyZero Φ m₀ φF b (kroneckerPoint m₀ p.1.zc.seed₀) p.2) i
        p.1.challenges = p.1.target₀ ∧
    hypercubeSum m₀
        (sumcheckPolyAlpha Φ m₀ m₁ φF b p.1.zc.rlin p.1.zc.α (kroneckerPoint m₁ p.1.zc.seedα)
          p.2) i p.1.challenges = p.1.targetα ∧
    bound ≤ p.1.zc.rlin.bound}

/-- `roundRel` extended with the escape branch: on `.inl w` it is `roundRel`, and on `.inr e` it
requires `e ∈ K.esc`. -/
def roundRelE (K : LiftCom (LiftedWitness Φ μ n) E (liftShort Φ bound rBound))
    (φF : ZMod q →+* F) (b : ℕ) (i : ℕ) :
    Set (RoundStatement Φ K.TCom F n μ i × (LiftedWitness Φ μ n ⊕ E)) :=
  (roundRel Φ m₀ m₁ bound rBound K φF b i).withEscape K.esc

end ArkLib.Lattices.Ajtai.InnerOuter

/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tobias Rothmann, Pablo Martín Vinuelas
-/
import ArkLib.Commitments.Functional.Hachi.RingSwitch.Reduction
import ArkLib.Data.MvPolynomial.Multilinear
import ArkLib.ToCompPoly.Multilinear.NestedEvaluationTree
import CompPoly.Multivariate.Operations

/-!
  # Constraint encoding — Hachi Eqs. (21)–(23)

  The constraint-encoding layer of the Hachi §4.3 sumcheck: the table `w̃` (Eq. (21)), the two
  batched constraint polynomials `H₀` and `H_α` (Eqs. (23) and (22)), the sumcheck summands
  `F_{0,τ₀}` and `F_{α,τ₁}`. These definitions are consumed by
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
    variables. `H_α ≡ 0` holds iff every lifted row vanishes at `α`. The table is *defined* as
    the per-row defect in the ring representation; the public objects `M̃_α` (`mAlphaTilde`) and
    `α̃` (`alphaTilde`), the contraction (`alphaContract`), and its equality with that defect
    (`alphaDefect_wTable`, `hAlpha_eq_zero_iff_alphaDefect`) are constructed and proved below.
  * `hZero` (Eq. (23)): the `eq̃`-batched range polynomial
    `H₀(τ) = ∑_{u,ℓ} eq̃(τ, (u,ℓ))·w̃(u,ℓ)·∏_{j=1}^{b−1}(w̃(u,ℓ) − j)(w̃(u,ℓ) + j)`, multilinear
    in `m₀` variables. `H₀ ≡ 0` holds iff every table entry lies in `[−(b−1), b−1]`. No
    relation between `b` and `q` is needed for the soundness direction
    (`hZero_eq_zero_imp_liftShort`): a root pins down *some* integer representative of size
    `≤ b − 1`, and the centered representative is never larger.

  Both are built as multilinear extensions, hence have degree `≤ 1` in each variable.

  ## Computable representation

  The two constraint polynomials are *defined* in CompPoly's Boolean-evaluation representation
  `CMlPolynomialEval`: a length-`2 ^ m` vector containing the values of the unique multilinear
  polynomial on `{0,1}^m`. This matches Eqs. (22)–(23) directly and makes multilinearity
  structural rather than a separate degree theorem.

  `hZeroML`/`hAlphaML` are derived Mathlib `restrictDegree` views of the same tables, used only to
  prove the sumcheck identities. The protocol relations and full identities use the computable
  `hZero`/`hAlpha` representation directly; `hZero_eval_eq` and `hAlpha_eval_eq` isolate the
  conversion used by those proofs.

  ## The sumcheck summands

  `F_{0,τ₀}` (`sumcheckPolyZero`) sums over the cube to `H₀(τ₀)` and has per-variable degree `2b`;
  `F_{α,τ₁}` (`sumcheckPolyAlpha`) sums to `H_α(τ₁) + zcTargetAlpha` and has per-variable degree
  `≤ 2`. These are the polynomials the sumcheck rounds operate on.

  ## References

  * [Huang, M.-Y. M., Mao, X., and Zhang, J., *Sublinear Proofs over Polynomial Rings*][HMZ25]
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

It is *defined* in the ring representation — as the `α`-evaluated per-row defect of the lift
relation `relLift`, namely `evalAt α (∑ⱼ Mᵢⱼ·zⱼ) − evalAt α yᵢ − evalAt α (X^d+1)·evalAt α rᵢ` —
encoded into the `m₁`-cube via `rowPoint` and zero-padded on rows `≥ n`. The row equation of
`relLift` (Fig. 4) is recovered at the Boolean points via `hAlphaEvals_rowPoint`.

That this coincides with Eq. (22)'s contraction of the public `M̃_α` against the committed table
`w̃` and the public `α̃` — [NOZ26] §4.3's "represent the constraints by polynomials" step — is
**proved**, not assumed: see `alphaDefect_wTable` and `hAlphaEvals_eq_alphaDefect` below, and
`hAlpha_eq_zero_iff_alphaDefect` for the relation-level form. The `b` argument is unused here and
kept for signature compatibility with `hAlpha`. -/
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
`α`-evaluated lift defect. This links `hAlpha ≡ 0` (via `hAlpha_eq_zero_iff`) to the per-row
constraints of `relLift`. -/
theorem hAlphaEvals_rowPoint (φF : ZMod q →+* F) (b : ℕ) (s : RlinStatement Φ n μ) (α : F)
    (w : LiftedWitness Φ μ n) (hn : n ≤ 2 ^ m₁) (i : Fin n) :
    hAlphaEvals Φ m₁ φF b s α w (rowPoint m₁ hn i) =
      cEvalAt φF α (cRowSum Φ s w.z i) - cEvalAt φF α (s.yvec i).1
        - cEvalAt φF α Φ.φ * cEvalAt φF α (w.r i) := by
  simp only [hAlphaEvals, rowPoint, Equiv.apply_symm_apply, Fin.eta, i.isLt, dif_pos]

/-! ## The batched constraint polynomials -/

/-- `H₀` (Eq. (23)) in Boolean-evaluation/Lagrange form. Entry `x` is the range factor
`P_b(w̃(x))`; the vector represents the unique multilinear extension of those `2 ^ m₀` values. -/
def hZero (φF : ZMod q →+* F) (b : ℕ) (w : LiftedWitness Φ μ n) :
    CMlPolynomialEval F m₀ :=
  Vector.ofFn fun i =>
    rangeProduct b (wTable Φ m₀ φF b w (finFunctionFinEquiv.symm i))

/-- `H_α` (Eq. (22)) in Boolean-evaluation/Lagrange form. Entry `x` is the row-defect table
`hAlphaEvals x`; the vector represents its unique multilinear extension. By
`hAlpha_eq_zero_iff_alphaDefect`, `H_α ≡ 0` is equivalent to the vanishing of every row's
Eq. (22) contraction `∑_{u,ℓ} M̃_α(i,u)·w̃(u,ℓ)·α̃(ℓ) − yᵢ(α)`. -/
def hAlpha (φF : ZMod q →+* F) (b : ℕ) (s : RlinStatement Φ n μ) (α : F)
    (w : LiftedWitness Φ μ n) : CMlPolynomialEval F m₁ :=
  Vector.ofFn fun i => hAlphaEvals Φ m₁ φF b s α w (finFunctionFinEquiv.symm i)

omit [NeZero q] [IsCyclotomic Φ] [BEq F] [LawfulBEq F] in
/-- `H₀` is zero exactly when every Boolean-table range constraint is zero. -/
theorem hZero_eq_zero_iff (φF : ZMod q →+* F) (b : ℕ) (w : LiftedWitness Φ μ n) :
    hZero Φ m₀ φF b w = 0 ↔
      ∀ x, rangeProduct b (wTable Φ m₀ φF b w x) = 0 := by
  constructor
  · intro h x
    have hx := congrArg (fun p => p.get (finFunctionFinEquiv x)) h
    calc
      rangeProduct b (wTable Φ m₀ φF b w x) =
          (0 : CMlPolynomialEval F m₀).get (finFunctionFinEquiv x) := by
        simpa [hZero] using hx
      _ = 0 := by rw [Vector.get_eq_getElem]; exact Vector.getElem_zero _ _
  · intro h
    apply Vector.ext
    intro i hi
    simpa [hZero] using h (finFunctionFinEquiv.symm ⟨i, hi⟩)

omit [NeZero q] [IsCyclotomic Φ] [BEq F] [LawfulBEq F] in
/-- `H_α` is zero exactly when every Boolean-table row defect is zero. -/
theorem hAlpha_eq_zero_iff (φF : ZMod q →+* F) (b : ℕ) (s : RlinStatement Φ n μ) (α : F)
    (w : LiftedWitness Φ μ n) :
    hAlpha Φ m₁ φF b s α w = 0 ↔
      ∀ x, hAlphaEvals Φ m₁ φF b s α w x = 0 := by
  constructor
  · intro h x
    have hx := congrArg (fun p => p.get (finFunctionFinEquiv x)) h
    calc
      hAlphaEvals Φ m₁ φF b s α w x =
          (0 : CMlPolynomialEval F m₁).get (finFunctionFinEquiv x) := by
        simpa [hAlpha] using hx
      _ = 0 := by rw [Vector.get_eq_getElem]; exact Vector.getElem_zero _ _
  · intro h
    apply Vector.ext
    intro i hi
    simpa [hAlpha] using h (finFunctionFinEquiv.symm ⟨i, hi⟩)

/-- Mathlib multilinear view of `H₀`, used only in algebraic proofs. -/
noncomputable def hZeroML (φF : ZMod q →+* F) (b : ℕ) (w : LiftedWitness Φ μ n) :
    MvPolynomial.restrictDegree (Fin m₀) F 1 :=
  ⟨MLE fun x => rangeProduct b (wTable Φ m₀ φF b w x),
    MLE_mem_restrictDegree _⟩

/-- Mathlib multilinear view of `H_α`, used only in algebraic proofs. -/
noncomputable def hAlphaML (φF : ZMod q →+* F) (b : ℕ) (s : RlinStatement Φ n μ) (α : F)
    (w : LiftedWitness Φ μ n) : MvPolynomial.restrictDegree (Fin m₁) F 1 :=
  ⟨MLE (hAlphaEvals Φ m₁ φF b s α w), MLE_mem_restrictDegree _⟩

omit [NeZero q] [IsCyclotomic Φ] [BEq F] [LawfulBEq F] in
/-- Direct evaluation of the primary `CMlPolynomialEval` `H₀` agrees with its Mathlib proof
view. The protocol relation uses the left side; algebraic proofs cross this bridge. -/
theorem hZero_eval_eq (φF : ZMod q →+* F) (b : ℕ) (w : LiftedWitness Φ μ n)
    (a : Fin m₀ → F) :
    CMlPolynomialEval.eval (hZero Φ m₀ φF b w) (Vector.ofFn a) =
      MvPolynomial.eval a (hZeroML Φ m₀ φF b w).val := by
  rw [hZero, hZeroML]
  exact CMlPolynomialEval.eval_eq_MvPolynomial_MLE
    (R := F) (n := m₀) (fun x => rangeProduct b (wTable Φ m₀ φF b w x)) a

omit [NeZero q] [IsCyclotomic Φ] [BEq F] [LawfulBEq F] in
/-- Direct evaluation of the primary `CMlPolynomialEval` `H_α` agrees with its Mathlib proof
view. -/
theorem hAlpha_eval_eq (φF : ZMod q →+* F) (b : ℕ) (s : RlinStatement Φ n μ) (α : F)
    (w : LiftedWitness Φ μ n) (a : Fin m₁ → F) :
    CMlPolynomialEval.eval (hAlpha Φ m₁ φF b s α w) (Vector.ofFn a) =
      MvPolynomial.eval a (hAlphaML Φ m₁ φF b s α w).val := by
  rw [hAlpha, hAlphaML]
  exact CMlPolynomialEval.eval_eq_MvPolynomial_MLE
    (R := F) (n := m₁) (hAlphaEvals Φ m₁ φF b s α w) a

omit [NeZero q] [IsCyclotomic Φ] [BEq F] [LawfulBEq F] in
/-- **One transcript tree determines `H₀`.** `H₀` reads the *first* `m₀` levels of a
sibling-distinct complete `k`-ary evaluation tree, so vanishing at every leaf makes it identically
zero.

This is the Hachi range-polynomial specialization of
`CMlPolynomialEval.eq_zero_of_polynomialVanishes_castAdd`. It stays on the computable
`CMlPolynomialEval` representation; the generic theorem alone crosses to Mathlib internally. The
extra `s` levels below the window are the challenge rounds that `H_α` consumes
(`hAlpha_eq_zero_of_evaluationTree`), which is why the same tree serves both identities. -/
theorem hZero_eq_zero_of_evaluationTree {k s : ℕ} (hk : 2 ≤ k) (φF : ZMod q →+* F) (b : ℕ)
    (w : LiftedWitness Φ μ n) (tree : NestedEvaluationTree F k (m₀ + s))
    (hDistinct : tree.IsDistinct)
    (hVanishes : CMlPolynomialEval.PolynomialVanishes tree (hZero Φ m₀ φF b w)
      (Fin.castAdd s)) :
    hZero Φ m₀ φF b w = 0 :=
  CMlPolynomialEval.eq_zero_of_polynomialVanishes_castAdd hk tree (hZero Φ m₀ φF b w)
    hDistinct hVanishes

omit [NeZero q] [IsCyclotomic Φ] [BEq F] [LawfulBEq F] in
/-- **The same transcript tree determines `H_α`.** `H_α` reads the *last* `m₁` levels of the tree,
below the first `m` levels that `H₀` consumes (`m = m₀` at the call site), so vanishing at every
leaf makes it identically zero.

The Hachi linear-constraint specialization of the nested-tree zero test, again stated entirely
with the computable `CMlPolynomialEval` polynomial. The window is disjoint from `H₀`'s, so the two
identities are certified by disjoint variable blocks of one tree. That single tree is what the
protocol supplies — `pSpecNestedZeroCheck` is one run of `m₀ + m₁` challenge rounds, so
`ChallengeTree.IsStructured` demands all `k ^ (m + m₁)` leaves; two independent trees would need
only `k ^ m + k ^ m₁` of them, but there is no second run to draw them from. -/
theorem hAlpha_eq_zero_of_evaluationTree {k m : ℕ} (hk : 2 ≤ k) (φF : ZMod q →+* F) (b : ℕ)
    (s : RlinStatement Φ n μ) (α : F) (w : LiftedWitness Φ μ n)
    (tree : NestedEvaluationTree F k (m + m₁)) (hDistinct : tree.IsDistinct)
    (hVanishes : CMlPolynomialEval.PolynomialVanishes tree (hAlpha Φ m₁ φF b s α w)
      (Fin.natAdd m)) :
    hAlpha Φ m₁ φF b s α w = 0 :=
  CMlPolynomialEval.eq_zero_of_polynomialVanishes_natAdd hk tree (hAlpha Φ m₁ φF b s α w)
    hDistinct hVanishes

omit [NeZero q] [IsCyclotomic Φ] [BEq F] [LawfulBEq F] in
/-- The Mathlib view vanishes exactly when the primary `CMlPolynomialEval` `H₀` vanishes. -/
theorem hZeroML_eq_zero_iff (φF : ZMod q →+* F) (b : ℕ) (w : LiftedWitness Φ μ n) :
    (hZeroML Φ m₀ φF b w).val = 0 ↔ hZero Φ m₀ φF b w = 0 := by
  rw [hZeroML, MLE_eq_zero_iff, hZero_eq_zero_iff]

omit [NeZero q] [IsCyclotomic Φ] [BEq F] [LawfulBEq F] in
/-- The Mathlib view vanishes exactly when the primary `CMlPolynomialEval` `H_α` vanishes. -/
theorem hAlphaML_eq_zero_iff (φF : ZMod q →+* F) (b : ℕ) (s : RlinStatement Φ n μ) (α : F)
    (w : LiftedWitness Φ μ n) :
    (hAlphaML Φ m₁ φF b s α w).val = 0 ↔ hAlpha Φ m₁ φF b s α w = 0 := by
  rw [hAlphaML, MLE_eq_zero_iff, hAlpha_eq_zero_iff]

/-- The computable multilinear extension of the table `w̃` itself, the committed object the
final-evaluation step opens. -/
def cWTableMle (φF : ZMod q →+* F) (b : ℕ) (w : LiftedWitness Φ μ n) :
    CMlPolynomialEval F m₀ :=
  Vector.ofFn fun i => wTable Φ m₀ φF b w (finFunctionFinEquiv.symm i)

/-- Evaluation of the multilinear extension of the table `w̃` at a point `a ∈ F^{m₀}`:
`mle[w̃](a) = ∑ᵢ w̃(i)·eq̃(i, a)`. This is the evaluation claim carried into the final-evaluation
step (`Sumcheck/FinalEval.lean`). Computed on the computable representation. -/
def wTableMleEval (φF : ZMod q →+* F) (b : ℕ) (w : LiftedWitness Φ μ n)
    (a : Fin m₀ → F) : F :=
  CMlPolynomialEval.eval (cWTableMle Φ m₀ φF b w) (Vector.ofFn a)

omit [NeZero q] [IsCyclotomic Φ] [BEq F] [LawfulBEq F] in
/-- `wTableMleEval` agrees with evaluating Mathlib's multilinear extension of `w̃`. -/
theorem wTableMleEval_eq (φF : ZMod q →+* F) (b : ℕ) (w : LiftedWitness Φ μ n)
    (a : Fin m₀ → F) :
    wTableMleEval Φ m₀ φF b w a = MvPolynomial.eval a (MLE (wTable Φ m₀ φF b w)) := by
  rw [wTableMleEval, cWTableMle]
  exact CMlPolynomialEval.eval_eq_MvPolynomial_MLE (wTable Φ m₀ φF b w) a

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

omit [IsCyclotomic Φ] [BEq F] [LawfulBEq F] in
/-- **Range-side soundness (F5).** If the batched range polynomial `H₀^{w̃}` vanishes
identically then `w̃` is short. Each committed coefficient is a table entry (`wTable`), hence a
root of `P_b` (`hZero_eq_zero_iff`), hence a centered residue of absolute value `≤ b − 1`
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
  rw [hZero_eq_zero_iff] at h
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

/-! ## Eq. (22) in the paper's table form: the `M̃_α`/`w̃`/`α̃` contraction

`hAlphaEvals` specifies the `α`-evaluated row defect **directly**, in the *ring* representation:
`cRowSum` contracts the public matrix against `w.z` as `Rq` elements and `cEvalAt · α` contracts
the coefficient index. [NOZ26] Eq. (22) builds the same quantity in the *table* representation,
as a contraction of the public matrix `M̃_α` against the committed table `w̃` and the public power
vector `α̃(ℓ) = α^ℓ` — the representation the commitment opens and the sumcheck folds.

This section constructs `M̃_α`, `α̃` and the contraction, and proves the two representations equal
(`alphaDefect_wTable`, `hAlpha_eq_zero_iff_alphaDefect`). That equality is §4.3's "represent the
constraints by polynomials" step, which is otherwise *assumed* whenever `hAlphaEvals` is read as
Eq. (22). It also supplies the public `M̃_α` that the Figure 7 verifier evaluates
(`Sumcheck/FinalEval.finalCheck`). -/

/-- `α̃(ℓ) = α^ℓ` ([NOZ26] Eq. (22)): the public column-contraction vector. Contracting a table
row's `d` coefficient entries against `α̃` evaluates the corresponding `Zq[X]` polynomial at `α`. -/
def alphaTilde (α : F) (ℓ : ℕ) : F := α ^ ℓ

/-- `M̃_α(i, u)` ([NOZ26] Eq. (22)): the public constraint matrix at `α`, indexed by the row
`i ∈ [n]` of `relLift` and the table row `u ∈ [μ + n]` of `w̃`. The paper's three cases:

* `u < μ` — the `R^lin` matrix entry evaluated at `α`, namely `Mᵢᵤ(α)`;
* `u = μ + i` — `−φ(α)`, placing the lift's `−(α^d + 1)·rᵢ(α)` term on the `r` block's diagonal;
* otherwise — `0`.

Only public data enters (`s.M`, `Φ.φ`, `α`), which is what makes the Figure 7 final check
verifier-computable: the prover supplies `w̃`, the verifier supplies `M̃_α`. -/
def mAlphaTilde (φF : ZMod q →+* F) (s : RlinStatement Φ n μ) (α : F) (i : Fin n) (u : ℕ) : F :=
  if hu : u < μ then cEvalAt φF α (s.M i ⟨u, hu⟩).1
  else if u = μ + (i : ℕ) then -cEvalAt φF α Φ.φ
  else 0

/-- The `m₀`-cube point carrying table entry `(u, ℓ)` of `w̃` — row `u ∈ [μ + n]`, column
`ℓ < d = deg φ` — at the flat index `d·u + ℓ` that `wTable` decodes. The arity pin
`(μ + n)·d ≤ 2^{m₀}` is exactly what makes every such position a genuine cube point. -/
def wTablePoint (hμn : (μ + n) * Φ.φ.natDegree ≤ 2 ^ m₀)
    (u : Fin (μ + n)) (ℓ : Fin Φ.φ.natDegree) : Fin m₀ → Fin 2 :=
  finFunctionFinEquiv.symm ⟨Φ.φ.natDegree * (u : ℕ) + (ℓ : ℕ), by
    have hu := u.isLt
    have hl := ℓ.isLt
    have s1 : Φ.φ.natDegree * (u : ℕ) + (ℓ : ℕ) < Φ.φ.natDegree * ((u : ℕ) + 1) := by
      rw [Nat.mul_succ]; omega
    have s2 : Φ.φ.natDegree * ((u : ℕ) + 1) ≤ (μ + n) * Φ.φ.natDegree := by
      rw [Nat.mul_comm]; exact Nat.mul_le_mul (by omega) (le_refl _)
    omega⟩

/-- Eq. (22)'s public contraction `∑_{u,ℓ} M̃_α(i,u)·w̃(u,ℓ)·α̃(ℓ)`, stated against an arbitrary
`m₀`-cube table `T` so that the paper object is defined independently of any particular witness.
For the witness instance `T = wTable …`, the corresponding defect is related to the ring-level
row equation by `alphaDefect_wTable`. -/
def alphaContract (φF : ZMod q →+* F) (s : RlinStatement Φ n μ) (α : F)
    (hμn : (μ + n) * Φ.φ.natDegree ≤ 2 ^ m₀) (T : (Fin m₀ → Fin 2) → F) (i : Fin n) : F :=
  ∑ u : Fin (μ + n), ∑ ℓ : Fin Φ.φ.natDegree,
    mAlphaTilde Φ φF s α i (u : ℕ) * T (wTablePoint Φ m₀ hμn u ℓ) * alphaTilde α (ℓ : ℕ)

/-- Eq. (22)'s per-row defect in the paper's table form: the public contraction against `T` minus
the public right-hand side `yᵢ(α)`. `H_α`'s Boolean table is exactly this at `T = w̃`
(`alphaDefect_wTable`, `hAlphaEvals_eq_alphaDefect`). -/
def alphaDefect (φF : ZMod q →+* F) (s : RlinStatement Φ n μ) (α : F)
    (hμn : (μ + n) * Φ.φ.natDegree ≤ 2 ^ m₀) (T : (Fin m₀ → Fin 2) → F) (i : Fin n) : F :=
  alphaContract Φ m₀ φF s α hμn T i - cEvalAt φF α (s.yvec i).1

omit [NeZero q] [IsCyclotomic Φ] [BEq F] [LawfulBEq F] in
/-- A `CPolynomial` of degree `< d` evaluates as the contraction of its first `d` coefficients
against the powers of `α`. This is the column half of Eq. (22)'s contraction: it is what makes
`α̃` a faithful stand-in for evaluation at `α`. -/
theorem cEvalAt_eq_sum_range (φF : ZMod q →+* F) (α : F) {d : ℕ} {p : CPolynomial (ZMod q)}
    (hp : p.natDegree < d) :
    cEvalAt φF α p = ∑ ℓ ∈ Finset.range d, φF (p.coeff ℓ) * α ^ ℓ := by
  rw [cEvalAt, CPolynomial.eval₂_toPoly,
    Polynomial.eval₂_eq_sum_range' φF (by rwa [← CPolynomial.natDegree_toPoly]) α]
  exact Finset.sum_congr rfl fun ℓ _ => by rw [CPolynomial.coeff_toPoly]

omit [NeZero q] [IsCyclotomic Φ] [BEq F] [LawfulBEq F] in
/-- The `z`-block table entries: at a cube point whose table row is `j < μ`, `w̃` returns the
embedded `j`-th witness coefficient. Wrapper of `wTable_zRow` in `wTablePoint` coordinates. -/
theorem wTable_wTablePoint_z (φF : ZMod q →+* F) (b : ℕ) (w : LiftedWitness Φ μ n)
    (hd : 0 < Φ.φ.natDegree) (hμn : (μ + n) * Φ.φ.natDegree ≤ 2 ^ m₀)
    {u : Fin (μ + n)} {j : Fin μ} (hj : (u : ℕ) = (j : ℕ)) (ℓ : Fin Φ.φ.natDegree) :
    wTable Φ m₀ φF b w (wTablePoint Φ m₀ hμn u ℓ) = φF ((w.z j).1.coeff (ℓ : ℕ)) := by
  have hlt : Φ.φ.natDegree * (j : ℕ) + (ℓ : ℕ) < 2 ^ m₀ := by
    have hj' := j.isLt
    have hl := ℓ.isLt
    have s1 : Φ.φ.natDegree * (j : ℕ) + (ℓ : ℕ) < Φ.φ.natDegree * ((j : ℕ) + 1) := by
      rw [Nat.mul_succ]; omega
    have s2 : Φ.φ.natDegree * ((j : ℕ) + 1) ≤ (μ + n) * Φ.φ.natDegree := by
      rw [Nat.mul_comm]; exact Nat.mul_le_mul (by omega) (le_refl _)
    omega
  have hpt : wTablePoint Φ m₀ hμn u ℓ
      = finFunctionFinEquiv.symm ⟨Φ.φ.natDegree * (j : ℕ) + (ℓ : ℕ), hlt⟩ := by
    unfold wTablePoint
    congr 1
    exact Fin.ext (by simp [hj])
  rw [hpt, wTable_zRow Φ m₀ φF b w hd j ℓ.isLt hlt]

omit [NeZero q] [IsCyclotomic Φ] [BEq F] [LawfulBEq F] in
/-- The `r`-block table entries: at a cube point whose table row is `μ + k`, `w̃` returns the
embedded `k`-th quotient coefficient. Wrapper of `wTable_rRow` in `wTablePoint` coordinates. -/
theorem wTable_wTablePoint_r (φF : ZMod q →+* F) (b : ℕ) (w : LiftedWitness Φ μ n)
    (hd : 0 < Φ.φ.natDegree) (hμn : (μ + n) * Φ.φ.natDegree ≤ 2 ^ m₀)
    {u : Fin (μ + n)} {k : Fin n} (hk : (u : ℕ) = μ + (k : ℕ)) (ℓ : Fin Φ.φ.natDegree) :
    wTable Φ m₀ φF b w (wTablePoint Φ m₀ hμn u ℓ) = φF ((w.r k).coeff (ℓ : ℕ)) := by
  have hlt : Φ.φ.natDegree * (μ + (k : ℕ)) + (ℓ : ℕ) < 2 ^ m₀ := by
    have hk' := k.isLt
    have hl := ℓ.isLt
    have s1 : Φ.φ.natDegree * (μ + (k : ℕ)) + (ℓ : ℕ) < Φ.φ.natDegree * (μ + (k : ℕ) + 1) := by
      rw [Nat.mul_succ]; omega
    have s2 : Φ.φ.natDegree * (μ + (k : ℕ) + 1) ≤ (μ + n) * Φ.φ.natDegree := by
      rw [Nat.mul_comm]; exact Nat.mul_le_mul (by omega) (le_refl _)
    omega
  have hpt : wTablePoint Φ m₀ hμn u ℓ
      = finFunctionFinEquiv.symm ⟨Φ.φ.natDegree * (μ + (k : ℕ)) + (ℓ : ℕ), hlt⟩ := by
    unfold wTablePoint
    congr 1
    exact Fin.ext (by simp [hk])
  rw [hpt, wTable_rRow Φ m₀ φF b w hd k ℓ.isLt hlt]

omit [NeZero q] [BEq F] [LawfulBEq F] in
/-- **Eq. (22) is the row defect (change of representation).** The paper's public contraction of
`M̃_α`, `w̃` and `α̃`, evaluated against the committed table, equals the ring-level `α`-defect that
`hAlphaEvals` writes down directly. This is the step [NOZ26] §4.3 asserts as "representing the
constraints by polynomials", and it is the only place the table encoding of the witness (which the
commitment and the sumcheck use) and the ring encoding (which `relLift` uses) meet. -/
theorem alphaDefect_wTable (φF : ZMod q →+* F) (b : ℕ) (s : RlinStatement Φ n μ) (α : F)
    (w : LiftedWitness Φ μ n) (hd : 0 < Φ.φ.natDegree)
    (hμn : (μ + n) * Φ.φ.natDegree ≤ 2 ^ m₀) (i : Fin n) :
    alphaDefect Φ m₀ φF s α hμn (wTable Φ m₀ φF b w) i =
      cEvalAt φF α (cRowSum Φ s w.z i) - cEvalAt φF α (s.yvec i).1
        - cEvalAt φF α Φ.φ * cEvalAt φF α (w.r i) := by
  -- Column contraction (`α̃`): a reduced representative is its `d` coefficients against `α^ℓ`.
  have hzcol : ∀ j : Fin μ, cEvalAt φF α (w.z j).1
      = ∑ ℓ : Fin Φ.φ.natDegree, φF ((w.z j).1.coeff (ℓ : ℕ)) * α ^ (ℓ : ℕ) := fun j => by
    rw [cEvalAt_eq_sum_range φF α (Φ.natDegree_lt_of_reduced hd (w.z j).2)]
    exact (Fin.sum_univ_eq_sum_range _ _).symm
  have hrcol : cEvalAt φF α (w.r i)
      = ∑ ℓ : Fin Φ.φ.natDegree, φF ((w.r i).coeff (ℓ : ℕ)) * α ^ (ℓ : ℕ) := by
    have hdeg : (w.r i).natDegree < Φ.φ.natDegree := by have := w.hr i; omega
    rw [cEvalAt_eq_sum_range φF α hdeg]
    exact (Fin.sum_univ_eq_sum_range _ _).symm
  -- Row contraction (`M̃_α`'s `z` block): the public matrix against the witness entries.
  have hrow : cEvalAt φF α (cRowSum Φ s w.z i)
      = ∑ j : Fin μ, cEvalAt φF α (s.M i j).1 * cEvalAt φF α (w.z j).1 := by
    rw [cEvalAt_cRowSum_eq_evalAt, rowSum_eq_sum_toPoly, _root_.map_sum]
    exact Finset.sum_congr rfl fun j _ => by
      rw [_root_.map_mul, ← cEvalAt_eq_evalAt_toPoly, ← cEvalAt_eq_evalAt_toPoly]
  -- The `z` block of the contraction reproduces one term of `cRowSum`.
  have hz : ∀ j : Fin μ, (∑ ℓ : Fin Φ.φ.natDegree,
      mAlphaTilde Φ φF s α i ((Fin.castAdd n j : Fin (μ + n)) : ℕ) *
        wTable Φ m₀ φF b w (wTablePoint Φ m₀ hμn (Fin.castAdd n j) ℓ) * alphaTilde α (ℓ : ℕ))
      = cEvalAt φF α (s.M i j).1 * cEvalAt φF α (w.z j).1 := by
    intro j
    have hjv : ((Fin.castAdd n j : Fin (μ + n)) : ℕ) = (j : ℕ) := rfl
    have hM : mAlphaTilde Φ φF s α i ((Fin.castAdd n j : Fin (μ + n)) : ℕ)
        = cEvalAt φF α (s.M i j).1 := by
      unfold mAlphaTilde
      exact dif_pos j.isLt
    rw [hzcol j, Finset.mul_sum]
    exact Finset.sum_congr rfl fun ℓ _ => by
      simp only [hM, wTable_wTablePoint_z Φ m₀ φF b w hd hμn hjv ℓ, alphaTilde, mul_assoc]
  -- The `r` block: only the diagonal entry `u = μ + i` survives.
  have hr : ∀ k : Fin n, (∑ ℓ : Fin Φ.φ.natDegree,
      mAlphaTilde Φ φF s α i ((Fin.natAdd μ k : Fin (μ + n)) : ℕ) *
        wTable Φ m₀ φF b w (wTablePoint Φ m₀ hμn (Fin.natAdd μ k) ℓ) * alphaTilde α (ℓ : ℕ))
      = if k = i then -(cEvalAt φF α Φ.φ * cEvalAt φF α (w.r i)) else 0 := by
    intro k
    have hkv : ((Fin.natAdd μ k : Fin (μ + n)) : ℕ) = μ + (k : ℕ) := rfl
    have hlow : ¬ ((Fin.natAdd μ k : Fin (μ + n)) : ℕ) < μ := by rw [hkv]; omega
    by_cases hki : k = i
    · have hdiag : ((Fin.natAdd μ k : Fin (μ + n)) : ℕ) = μ + (i : ℕ) := by rw [hkv, hki]
      have hM : mAlphaTilde Φ φF s α i ((Fin.natAdd μ k : Fin (μ + n)) : ℕ)
          = -cEvalAt φF α Φ.φ := by
        unfold mAlphaTilde
        rw [dif_neg hlow, if_pos hdiag]
      rw [if_pos hki, hrcol, Finset.mul_sum, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun ℓ _ => ?_
      rw [hM, wTable_wTablePoint_r Φ m₀ φF b w hd hμn hdiag ℓ]
      simp only [alphaTilde]
      ring
    · have hM : mAlphaTilde Φ φF s α i ((Fin.natAdd μ k : Fin (μ + n)) : ℕ) = 0 := by
        unfold mAlphaTilde
        rw [dif_neg hlow, if_neg (by rw [hkv]; simp only [add_right_inj, Fin.val_inj]; exact hki)]
      rw [if_neg hki]
      exact Finset.sum_eq_zero fun ℓ _ => by rw [hM, zero_mul, zero_mul]
  have hzsum : (∑ j : Fin μ, ∑ ℓ : Fin Φ.φ.natDegree,
      mAlphaTilde Φ φF s α i ((Fin.castAdd n j : Fin (μ + n)) : ℕ) *
        wTable Φ m₀ φF b w (wTablePoint Φ m₀ hμn (Fin.castAdd n j) ℓ) * alphaTilde α (ℓ : ℕ))
      = cEvalAt φF α (cRowSum Φ s w.z i) := by
    rw [hrow]; exact Finset.sum_congr rfl fun j _ => hz j
  have hrsum : (∑ k : Fin n, ∑ ℓ : Fin Φ.φ.natDegree,
      mAlphaTilde Φ φF s α i ((Fin.natAdd μ k : Fin (μ + n)) : ℕ) *
        wTable Φ m₀ φF b w (wTablePoint Φ m₀ hμn (Fin.natAdd μ k) ℓ) * alphaTilde α (ℓ : ℕ))
      = -(cEvalAt φF α Φ.φ * cEvalAt φF α (w.r i)) :=
    (Finset.sum_congr rfl fun k _ => hr k).trans (by simp)
  simp only [alphaDefect, alphaContract, Fin.sum_univ_add]
  rw [hzsum, hrsum]
  ring

omit [NeZero q] [BEq F] [LawfulBEq F] in
/-- `H_α`'s Boolean table *is* Eq. (22)'s per-row defect at every Boolean point: the row-encoded
points carry the contraction, and the padding rows `≥ n` carry `0`. -/
theorem hAlphaEvals_eq_alphaDefect (φF : ZMod q →+* F) (b : ℕ) (s : RlinStatement Φ n μ) (α : F)
    (w : LiftedWitness Φ μ n) (hd : 0 < Φ.φ.natDegree)
    (hμn : (μ + n) * Φ.φ.natDegree ≤ 2 ^ m₀) (x : Fin m₁ → Fin 2) :
    hAlphaEvals Φ m₁ φF b s α w x =
      if h : ((finFunctionFinEquiv x : Fin (2 ^ m₁)) : ℕ) < n then
        alphaDefect Φ m₀ φF s α hμn (wTable Φ m₀ φF b w) ⟨_, h⟩
      else 0 := by
  by_cases h : ((finFunctionFinEquiv x : Fin (2 ^ m₁)) : ℕ) < n
  · rw [dif_pos h, alphaDefect_wTable Φ m₀ φF b s α w hd hμn ⟨_, h⟩]
    simp only [hAlphaEvals, dif_pos h]
  · rw [dif_neg h]
    simp only [hAlphaEvals, dif_neg h]

omit [NeZero q] [BEq F] [LawfulBEq F] in
/-- **`relBatched`'s `α`-conjunct is exactly Eq. (22)'s row constraints.** `H_α ≡ 0` — the identity
carried by `relBatched` (`ZeroCheck/Batch.lean`) and extracted by the zero-check — holds iff every
row's paper-form defect `∑_{u,ℓ} M̃_α(i,u)·w̃(u,ℓ)·α̃(ℓ) − yᵢ(α)` vanishes. This is what licenses
reading `relBatched` as a formalization of Eq. (22) rather than of an abstract direct-defect
variant of it. -/
theorem hAlpha_eq_zero_iff_alphaDefect (φF : ZMod q →+* F) (b : ℕ) (s : RlinStatement Φ n μ)
    (α : F) (w : LiftedWitness Φ μ n) (hd : 0 < Φ.φ.natDegree) (hn : n ≤ 2 ^ m₁)
    (hμn : (μ + n) * Φ.φ.natDegree ≤ 2 ^ m₀) :
    hAlpha Φ m₁ φF b s α w = 0 ↔
      ∀ i : Fin n, alphaDefect Φ m₀ φF s α hμn (wTable Φ m₀ φF b w) i = 0 := by
  rw [hAlpha_eq_zero_iff]
  constructor
  · intro h i
    have hlt : ((finFunctionFinEquiv (rowPoint m₁ hn i) : Fin (2 ^ m₁)) : ℕ) < n := by
      simp only [rowPoint, Equiv.apply_symm_apply]
      exact i.isLt
    have hx := h (rowPoint m₁ hn i)
    rw [hAlphaEvals_eq_alphaDefect Φ m₀ m₁ φF b s α w hd hμn, dif_pos hlt] at hx
    have hidx : (⟨((finFunctionFinEquiv (rowPoint m₁ hn i) : Fin (2 ^ m₁)) : ℕ), hlt⟩ : Fin n)
        = i := Fin.ext (by simp [rowPoint])
    rwa [hidx] at hx
  · intro h x
    rw [hAlphaEvals_eq_alphaDefect Φ m₀ m₁ φF b s α w hd hμn]
    by_cases hx : ((finFunctionFinEquiv x : Fin (2 ^ m₁)) : ℕ) < n
    · rw [dif_pos hx]; exact h _
    · rw [dif_neg hx]

/-! ## The sumcheck summands -/

/-- The computable Lagrange basis polynomial associated with a Boolean cube point. -/
def cBooleanEqPolynomial (x : Fin m₀ → Fin 2) : CMvPolynomial m₀ F :=
  ∏ i : Fin m₀,
    if x i = 1 then CMvPolynomial.X i else 1 - CMvPolynomial.X i

/-- A Boolean evaluation table reconstructed as a computable multivariate polynomial. -/
def cMultilinearExtension (evals : (Fin m₀ → Fin 2) → F) : CMvPolynomial m₀ F :=
  ∑ x : Fin m₀ → Fin 2,
    CMvPolynomial.C (evals x) * cBooleanEqPolynomial m₀ x

/-- The computable polynomial whose value at a Boolean point `x` is `eq̃(τ, x)`. -/
def cEqualityPolynomial (τ : Fin m₀ → F) : CMvPolynomial m₀ F :=
  cMultilinearExtension m₀ fun x =>
    ∏ i : Fin m₀, if x i = 1 then τ i else 1 - τ i

/-- Apply Hachi's symmetric range polynomial to a computable polynomial. -/
def cRangeProduct (b : ℕ) (p : CMvPolynomial m₀ F) : CMvPolynomial m₀ F :=
  p * ∏ j ∈ Finset.Icc 1 (b - 1),
    ((p - CMvPolynomial.C (j : F)) * (p + CMvPolynomial.C (j : F)))

/-- The public Boolean table multiplying `mle[w̃]` in the linear-constraint sumcheck.

At the flat cube index for `(u, ℓ)`, it is
`α^ℓ · ∑ᵢ eq̃(τ₁, i) M̃_α(i,u)`. Indices outside the encoded table are harmless padding. -/
def alphaPublicEvals (φF : ZMod q →+* F) (s : RlinStatement Φ n μ) (α : F)
    (τ₁ : Fin m₁ → F) (x : Fin m₀ → Fin 2) : F :=
  let idx : ℕ := (finFunctionFinEquiv x : Fin (2 ^ m₀))
  let d := Φ.φ.natDegree
  alphaTilde α (idx % d) * ∑ i : Fin n,
    (if hi : (i : ℕ) < 2 ^ m₁ then
      (∏ j : Fin m₁,
        if (finFunctionFinEquiv.symm ⟨(i : ℕ), hi⟩) j = 1 then τ₁ j else 1 - τ₁ j) *
          mAlphaTilde Φ φF s α i (idx / d)
    else 0)

/-- Assemble a point from a fixed prefix and a Boolean suffix. -/
def hypercubePoint (i : ℕ) (cs : Fin i → F) (x : Fin (m₀ - i) → Fin 2) : Fin m₀ → F :=
  fun j => if h : j.val < i then cs ⟨j, h⟩ else (x ⟨j.val - i, by omega⟩ : F)

/-- The range sumcheck summand `F_{0,τ₀}`, characterized by `∑_{x} F_{0,τ₀}(x) = H₀(τ₀)`
(`sum_sumcheckPolyZero`) with per-variable degree `roundDegZero b = 2b`.

Unlike `H₀`/`H_α` this one is genuinely evaluated by the prover in every sumcheck round. It is not
multilinear, so it remains a general `CMvPolynomial`. -/
def sumcheckPolyZero (φF : ZMod q →+* F) (b : ℕ) (τ₀ : Fin m₀ → F)
    (w : LiftedWitness Φ μ n) : CMvPolynomial m₀ F :=
  cEqualityPolynomial m₀ τ₀ *
    cRangeProduct m₀ b (cMultilinearExtension m₀ (wTable Φ m₀ φF b w))

/-- The linear sumcheck summand `F_{α,τ₁}`, characterized by
`∑_{x} F_{α,τ₁}(x) = H_α(τ₁) + zcTargetAlpha` (`sum_sumcheckPolyAlpha`) with per-variable degree
`roundDegAlpha = 2`. Also prover-evaluated, hence computable. -/
def sumcheckPolyAlpha (φF : ZMod q →+* F) (b : ℕ) (s : RlinStatement Φ n μ) (α : F)
    (τ₁ : Fin m₁ → F) (w : LiftedWitness Φ μ n) : CMvPolynomial m₀ F :=
  cMultilinearExtension m₀ (wTable Φ m₀ φF b w) *
    cMultilinearExtension m₀ (alphaPublicEvals Φ m₀ m₁ φF s α τ₁)

/-- The public initial target of the linear sumcheck, `∑ᵢ eq̃(τ₁, i)·yᵢ(α)`, which the verifier
computes from the statement alone. -/
def zcTargetAlpha (φF : ZMod q →+* F) (s : RlinStatement Φ n μ) (α : F)
    (τ₁ : Fin m₁ → F) : F :=
  ∑ i : Fin n, (if hi : (i : ℕ) < 2 ^ m₁ then
    (∏ j : Fin m₁,
      if (finFunctionFinEquiv.symm ⟨(i : ℕ), hi⟩) j = 1 then τ₁ j else 1 - τ₁ j) *
        cEvalAt φF α (s.yvec i).1
    else 0)

/-- Partial sum of `H` over the trailing cube coordinates: `hypercubeSum H i cs =
∑_{x ∈ {0,1}^{m₀ − i}} H(cs, x)`, where `cs` fixes the first `i` coordinates. Operates on the
computable representation — this is the fold the prover actually runs. -/
def hypercubeSum (H : CMvPolynomial m₀ F) (i : ℕ) (cs : Fin i → F) : F :=
  ∑ x : Fin (m₀ - i) → Fin 2, H.eval (hypercubePoint m₀ i cs x)

/-- The full-cube sum of the range summand `F_{0,τ₀}` equals `H₀(τ₀)`.

### Deliberate divergence: no `1_{≤μ}` indicator

The paper's `F_{0,τ₀}` (p. 22) carries a trailing indicator factor `1_{≤μ}(x,y)` that restricts the
range check to the `z` rows, whereas Eq. (23)'s `H₀` carries **no** such factor, sums over all
`(u, ℓ)`, and the bullet above it imposes the constraint "for each `u ∈ [μ + n]` and `ℓ ∈ [d]`" —
i.e. on the `r` rows as well, consistent with the earlier requirement `‖z‖∞, ‖r‖∞ ≤ b − 1`. The two
readings are not equivalent, so the paper's own `∑_{u,ℓ} F_{0,τ₀}(u,ℓ) = H₀(τ₀)` is **false as
printed**: the two sides differ exactly by the indicator.

This file follows the Eq. (23) reading — no indicator, and the range constraint applied to both the
`z` and the `r` rows. That is the self-consistent choice, and it is visible downstream:
`wTable` fills both row blocks (`wTable_zRow`, `wTable_rRow`), and
`hZero_eq_zero_imp_liftShort` discharges a `z`-side *and* an `r`-side bound. Anyone comparing this
statement against Figure 5 should read the absent indicator as intentional rather than as a bug. -/
theorem sum_sumcheckPolyZero (φF : ZMod q →+* F) (b : ℕ) (τ₀ : Fin m₀ → F)
    (w : LiftedWitness Φ μ n) :
    hypercubeSum m₀ (sumcheckPolyZero Φ m₀ φF b τ₀ w) 0 (fun j => j.elim0) =
      MvPolynomial.eval τ₀ (hZeroML Φ m₀ φF b w).val := by
  sorry

omit [NeZero q] in
/-- Alias of `sum_sumcheckPolyZero` retained for the sumcheck bridge. -/
theorem sum_sumcheckPolyZero' (φF : ZMod q →+* F) (b : ℕ) (τ₀ : Fin m₀ → F)
    (w : LiftedWitness Φ μ n) :
    hypercubeSum m₀ (sumcheckPolyZero Φ m₀ φF b τ₀ w) 0 (fun j => j.elim0) =
      MvPolynomial.eval τ₀ (hZeroML Φ m₀ φF b w).val :=
  sum_sumcheckPolyZero Φ m₀ φF b τ₀ w

/-- The full-cube sum of the linear summand `F_{α,τ₁}` equals `H_α(τ₁) + zcTargetAlpha`. -/
theorem sum_sumcheckPolyAlpha (φF : ZMod q →+* F) (b : ℕ) (s : RlinStatement Φ n μ) (α : F)
    (τ₁ : Fin m₁ → F) (w : LiftedWitness Φ μ n) :
    hypercubeSum m₀ (sumcheckPolyAlpha Φ m₀ m₁ φF b s α τ₁ w) 0 (fun j => j.elim0) =
      MvPolynomial.eval τ₁ (hAlphaML Φ m₁ φF b s α w).val +
        zcTargetAlpha Φ m₁ φF s α τ₁ := by
  sorry

omit [NeZero q] in
/-- Alias of `sum_sumcheckPolyAlpha` retained for the sumcheck bridge. -/
theorem sum_sumcheckPolyAlpha' (φF : ZMod q →+* F) (b : ℕ) (s : RlinStatement Φ n μ) (α : F)
    (τ₁ : Fin m₁ → F) (w : LiftedWitness Φ μ n) :
    hypercubeSum m₀ (sumcheckPolyAlpha Φ m₀ m₁ φF b s α τ₁ w) 0 (fun j => j.elim0) =
      MvPolynomial.eval τ₁ (hAlphaML Φ m₁ φF b s α w).val +
        zcTargetAlpha Φ m₁ φF s α τ₁ :=
  sum_sumcheckPolyAlpha Φ m₀ m₁ φF b s α τ₁ w

/-! ## Statement types of the zero-check and sumcheck stages -/

/-- Statement produced by the scalar-round interpretation of Hachi Figure 5.

The first `m₀` scalar rounds assemble `τ₀`; the following `m₁` scalar rounds assemble `τα`.
The direct points are retained for the paired sumcheck. -/
structure NestedZeroCheckStatement (Φ : CyclotomicModulus (ZMod q)) (TCom F : Type)
    (n μ m₀ m₁ : ℕ) where
  /-- The `R^lin` statement, carrying the public `M`, `yvec`, and `bound`. -/
  rlin : RlinStatement Φ n μ
  /-- The commitment to `w̃` from the lift stage. -/
  t : TCom
  /-- The ring-switching evaluation challenge `α` from the lift stage. -/
  α : F
  /-- The direct range-polynomial evaluation point, assembled from the first `m₀` rounds. -/
  τ₀ : Fin m₀ → F
  /-- The direct linear-polynomial evaluation point, assembled from the following `m₁` rounds. -/
  τα : Fin m₁ → F

/-- Statement after `i` paired-sumcheck rounds, retaining the direct points `τ₀` and `τα`. -/
structure NestedRoundStatement (Φ : CyclotomicModulus (ZMod q)) (TCom F : Type)
    (n μ m₀ m₁ i : ℕ) where
  /-- The zero-check statement containing the direct evaluation points. -/
  zc : NestedZeroCheckStatement Φ TCom F n μ m₀ m₁
  /-- The paired-sumcheck challenges drawn so far. -/
  challenges : Fin i → F
  /-- The current target of the range sumcheck. -/
  target₀ : F
  /-- The current target of the linear sumcheck. -/
  targetα : F

variable (bound : ℕ)

/-- Paired-sumcheck relation over direct zero-check points: an opening of `t` whose partial
hypercube sums match the current targets.

Both summands read the scalar-round challenges directly, with no derived evaluation-point encoding
(no curve, no seed expansion), and **no norm conjunct appears at all** — the
partial sums do not determine one, and the admissibility that conditions weak binding travels
inside `K.Opening` (see `LiftCom`). -/
def nestedRoundRel (K : LiftCom Φ μ n E) (φF : ZMod q →+* F) (b : ℕ) (i : ℕ) :
    Set (NestedRoundStatement Φ K.TCom F n μ m₀ m₁ i × K.Opening) :=
  {p |
    K.com p.2 = p.1.zc.t ∧
    hypercubeSum m₀ (sumcheckPolyZero Φ m₀ φF b p.1.zc.τ₀ (K.table p.2)) i
        p.1.challenges = p.1.target₀ ∧
    hypercubeSum m₀
        (sumcheckPolyAlpha Φ m₀ m₁ φF b p.1.zc.rlin p.1.zc.α p.1.zc.τα (K.table p.2)) i
        p.1.challenges = p.1.targetα ∧
    bound ≤ p.1.zc.rlin.bound}

/-- Escape-threaded paired-sumcheck relation. -/
def nestedRoundRelE (K : LiftCom Φ μ n E) (φF : ZMod q →+* F) (b : ℕ) (i : ℕ) :
    Set (NestedRoundStatement Φ K.TCom F n μ m₀ m₁ i × (K.Opening ⊕ E)) :=
  (nestedRoundRel Φ m₀ m₁ bound K φF b i).withEscape K.esc

end ArkLib.Lattices.Ajtai.InnerOuter

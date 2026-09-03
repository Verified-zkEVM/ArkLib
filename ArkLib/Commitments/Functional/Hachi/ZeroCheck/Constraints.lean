/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tobias Rothmann, Pablo Martín Vinuelas
-/
import ArkLib.Commitments.Functional.Hachi.RingSwitch.Reduction
import ArkLib.Data.MvPolynomial.Multilinear
import ArkLib.ToCompPoly.Multilinear.NestedEvaluationTree
import ArkLib.ToCompPoly.Multivariate.Eval
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

  `wTable` re-reads the committed vector as an `F`-valued function on the `m₀`-cube: the rows are
  the `Zq`-coefficient vectors of the witness entries `zⱼ ∈ Rq` followed by those of the quotients'
  base-`b` **digits** ([NOZ26] §4.3's hidden gadget decomposition — `n·δ` rows, `δ = clog_b q`,
  laid out digit-major within each quotient row), and the columns are the `d` coefficient positions
  (`d = deg Φ.φ`). The arity `m₀` satisfies `2 ^ m₀ ≥ (μ + n·δ)·d`; `m₁` is the row-batching arity,
  with `2 ^ m₁ ≥ n` — the `m₁` cube stays indexed by quotient *rows*, the digits being summed inside
  each row entry with the public weights `b^u`.

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
open RingSwitching RingSwitching.Lift
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

/-- The Eq. (21) table `w̃`: the committed vector read as an `F`-valued function on the
`m₀`-cube. A cube point is decoded (via `finFunctionFinEquiv`) to a flat index `idx`, split into
`row := idx / d` and `column := idx % d` (`d = deg Φ.φ`). Rows `< μ` return the `Zq`-coefficients
of the witness entries `zⱼ ∈ Rq`; rows `μ ≤ · < μ + n·δ` return the coefficients of the quotient
**digits**; both are mapped through the base-field embedding `φF`, and all remaining cube points
return zero.

Every entry is a coefficient of the *committed* vector, so the range polynomial `H₀` constrains
the committed data itself: `H₀ ≡ 0` says every committed coefficient lies in `[−(b−1), b−1]`.

The quotient block carries the **digits** `rhoDigits Φ b (w.ρ i) u`, not the raw quotient rows —
[NOZ26] §4.3's hidden gadget decomposition, matching `liftMessage`. Its `n·δ` rows are laid out
digit-major inside each quotient row (`row = (idx/d − μ)/δ`, `digit = (idx/d − μ)%δ`), the same
flattening `liftMessage` uses, so `w̃` is the committed vector read coefficient-wise. The `b`
argument is the digit base, and it is the **same** `b` the range factor `P_b` of `hZero` uses:
balanced base-`b` digits land in `[−⌊b/2⌋, ⌈b/2⌉−1] ⊆ [−(b−1), b−1]`, so one base serves both
roles and no cross-base orientation hypothesis is needed.

The paper's *simplified* presentation (Eq. (21)) tabulates the raw `r` rows instead; those carry
coefficients up to `q/2` (`rhoShort_half`), which would force the range base up to `q/2 + 1` for
honest completeness, collapsing `γ = q/2 = bZero − 1` and emptying both the Eq. (20) ball check and
the Module-SIS escape target. -/
def wTable (φF : ZMod q →+* F) (b : ℕ) (w : LiftedWitness Φ μ n) :
    (Fin m₀ → Fin 2) → F :=
  fun pt =>
    let idx : ℕ := (finFunctionFinEquiv pt : Fin (2 ^ m₀))
    let d : ℕ := Φ.φ.natDegree
    if hz : idx / d < μ then
      φF ((w.z ⟨idx / d, hz⟩).1.coeff (idx % d))
    else if hr : idx / d - μ < n * rhoDigitCount q b then
      φF ((rhoDigits Φ b (w.ρ ⟨(idx / d - μ) / rhoDigitCount q b,
              Nat.div_lt_of_lt_mul (by rwa [Nat.mul_comm])⟩)
            ((idx / d - μ) % rhoDigitCount q b)).coeff (idx % d))
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
`hAlpha_eq_zero_iff_alphaDefect` for the relation-level form.

The quotient term is the **digit recombination** `∑_u b^u · rᵢ,ᵤ(α)` rather than `rᵢ(α)`, since
that is what the committed table holds; `rhoDigits_evalAt` says the two agree, which is why the
`m₁` cube is still indexed by rows `Fin n` — the digits are summed *inside* the row entry with the
public weights `b^u`, exactly the paper's `M̃_α(i, u) = −(α^d + 1)·b^u` on digit columns. -/
noncomputable def hAlphaEvals (φF : ZMod q →+* F) (b : ℕ) (s : RlinStatement Φ n μ) (α : F)
    (w : LiftedWitness Φ μ n) : (Fin m₁ → Fin 2) → F :=
  fun pt =>
    if h : ((finFunctionFinEquiv pt : Fin (2 ^ m₁)) : ℕ) < n then
      cEvalAt φF α (cRowSum Φ s w.z ⟨_, h⟩)
        - cEvalAt φF α (s.yvec ⟨_, h⟩).1
        - cEvalAt φF α Φ.φ * ∑ u : Fin (rhoDigitCount q b),
            φF ((b : ZMod q) ^ (u : ℕ))
              * evalAt φF α (rhoDigits Φ b (w.ρ ⟨_, h⟩) (u : ℕ)).toPoly
    else 0

omit [NeZero q] [IsCyclotomic Φ] [BEq F] [LawfulBEq F] in
/-- At the Boolean point `rowPoint i`, the coefficient `hAlphaEvals` equals row `i`'s
`α`-evaluated lift defect. This links `hAlpha ≡ 0` (via `hAlpha_eq_zero_iff`) to the per-row
constraints of `relLift`. -/
theorem hAlphaEvals_rowPoint (φF : ZMod q →+* F) (b : ℕ) (s : RlinStatement Φ n μ) (α : F)
    (w : LiftedWitness Φ μ n) (hn : n ≤ 2 ^ m₁) (i : Fin n) :
    hAlphaEvals Φ m₁ φF b s α w (rowPoint m₁ hn i) =
      cEvalAt φF α (cRowSum Φ s w.z i) - cEvalAt φF α (s.yvec i).1
        - cEvalAt φF α Φ.φ * ∑ u : Fin (rhoDigitCount q b),
            φF ((b : ZMod q) ^ (u : ℕ))
              * evalAt φF α (rhoDigits Φ b (w.ρ i) (u : ℕ)).toPoly := by
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
noncomputable def hAlpha (φF : ZMod q →+* F) (b : ℕ) (s : RlinStatement Φ n μ) (α : F)
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
/-- The table value at the cube point encoding the quotient-block coordinate `(i, u, k)` — row
`μ + i·δ + u` (quotient row `i`, digit `u`), column `k < deg φ` — is the embedded digit
coefficient `φF((rhoDigits b rᵢ u).coeff k)`. The digit-block analogue of `wTable_zRow`. -/
theorem wTable_rRow (φF : ZMod q →+* F) (b : ℕ) (w : LiftedWitness Φ μ n)
    (hd : 0 < Φ.φ.natDegree) (i : Fin n) {u : ℕ} (hu : u < rhoDigitCount q b) {k : ℕ}
    (hk : k < Φ.φ.natDegree)
    (hlt : Φ.φ.natDegree * (μ + ((i : ℕ) * rhoDigitCount q b + u)) + k < 2 ^ m₀) :
    wTable Φ m₀ φF b w
        (finFunctionFinEquiv.symm
          ⟨Φ.φ.natDegree * (μ + ((i : ℕ) * rhoDigitCount q b + u)) + k, hlt⟩) =
      φF ((rhoDigits Φ b (w.ρ i) u).coeff k) := by
  set δ := rhoDigitCount q b with hδ
  have hrow : (Φ.φ.natDegree * (μ + ((i : ℕ) * δ + u)) + k) / Φ.φ.natDegree
      = μ + ((i : ℕ) * δ + u) := by
    rw [Nat.mul_add_div hd, Nat.div_eq_of_lt hk, Nat.add_zero]
  have hcol : (Φ.φ.natDegree * (μ + ((i : ℕ) * δ + u)) + k) % Φ.φ.natDegree = k := by
    have h := Nat.div_add_mod (Φ.φ.natDegree * (μ + ((i : ℕ) * δ + u)) + k) Φ.φ.natDegree
    rw [hrow] at h; omega
  have hδpos : 0 < δ := by omega
  have hdivδ : ((i : ℕ) * δ + u) / δ = (i : ℕ) := by
    rw [Nat.mul_comm, Nat.mul_add_div hδpos, Nat.div_eq_of_lt hu, Nat.add_zero]
  have hmodδ : ((i : ℕ) * δ + u) % δ = u := by
    rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hu]
  have hin : (i : ℕ) * δ + u < n * δ := by
    have := i.isLt
    calc (i : ℕ) * δ + u < (i : ℕ) * δ + δ := by omega
      _ = ((i : ℕ) + 1) * δ := by ring
      _ ≤ n * δ := Nat.mul_le_mul_right _ (by omega)
  simp only [wTable, Equiv.apply_symm_apply, Fin.val_mk, hrow, hcol, ← hδ]
  rw [dif_neg (by omega : ¬ μ + ((i : ℕ) * δ + u) < μ),
    dif_pos (by omega : μ + ((i : ℕ) * δ + u) - μ < n * δ)]
  simp only [Nat.add_sub_cancel_left, hdivδ, hmodδ, Fin.eta]

omit [IsCyclotomic Φ] [BEq F] [LawfulBEq F] in
/-- **Range-side soundness.** If the batched range polynomial `H₀^{w̃}` vanishes
identically then `w̃` is short. Each committed coefficient is a table entry (`wTable`), hence a
root of `P_b` (`hZero_eq_zero_iff`), hence a centered residue of absolute value `≤ b − 1`
(`valMinAbs_natAbs_le_of_rangeProduct_eq_zero`); the norm bounds follow because the declared
bound dominates the range base (`b − 1 ≤ bound`). The arity `(μ + n·δ)·deg φ ≤ 2^{m₀}` guarantees
every coefficient position is a genuine cube point. This is the derivation that makes the range
machinery load-bearing: `liftShort` is *proved* from `H₀ ≡ 0`, not assumed.

Both halves land at the **same** bound: the quotient block of `w̃` holds digits, so the range check
certifies `RhoDigitsShort` directly. A raw quotient block would need a second bound of its own, and
`rhoShort_half` forces that one up to `q/2`. -/
theorem hZero_eq_zero_imp_liftShort (φF : ZMod q →+* F) (b bound : ℕ)
    (hd : 0 < Φ.φ.natDegree) (hμn : (μ + n * rhoDigitCount q b) * Φ.φ.natDegree ≤ 2 ^ m₀)
    (hbound : b - 1 ≤ bound)
    (w : LiftedWitness Φ μ n) (h : hZero Φ m₀ φF b w = 0) :
    liftShort Φ bound b w := by
  rw [hZero_eq_zero_iff] at h
  refine ⟨?_, ?_⟩
  · -- z-side: `vecLInftyNorm w.z ≤ bound`, unchanged apart from the widened arity pin
    apply Finset.sup_le
    intro i _
    apply Finset.sup_le
    intro k hk
    rw [Finset.mem_range] at hk
    have hi := i.isLt
    have hlt : Φ.φ.natDegree * (i : ℕ) + k < 2 ^ m₀ := by
      have s1 : Φ.φ.natDegree * (i : ℕ) + k < Φ.φ.natDegree * ((i : ℕ) + 1) := by
        rw [Nat.mul_succ]; omega
      have s2 : Φ.φ.natDegree * ((i : ℕ) + 1)
          ≤ (μ + n * rhoDigitCount q b) * Φ.φ.natDegree := by
        rw [Nat.mul_comm]; exact Nat.mul_le_mul (by omega) (le_refl _)
      omega
    have hval := h (finFunctionFinEquiv.symm ⟨Φ.φ.natDegree * (i : ℕ) + k, hlt⟩)
    rw [wTable_zRow Φ m₀ φF b w hd i hk hlt] at hval
    exact le_trans (valMinAbs_natAbs_le_of_rangeProduct_eq_zero φF hval) hbound
  · -- digit side: `RhoDigitsShort bound b w.ρ`, read off the widened quotient block
    intro i u k
    by_cases hkd : k < Φ.φ.natDegree
    · have hi := i.isLt
      have hu := u.isLt
      have hrow : (i : ℕ) * rhoDigitCount q b + (u : ℕ) < n * rhoDigitCount q b := by
        calc (i : ℕ) * rhoDigitCount q b + (u : ℕ)
            < (i : ℕ) * rhoDigitCount q b + rhoDigitCount q b := by omega
          _ = ((i : ℕ) + 1) * rhoDigitCount q b := by ring
          _ ≤ n * rhoDigitCount q b := Nat.mul_le_mul (by omega) (le_refl _)
      have hlt : Φ.φ.natDegree * (μ + ((i : ℕ) * rhoDigitCount q b + (u : ℕ))) + k < 2 ^ m₀ := by
        have s1 : Φ.φ.natDegree * (μ + ((i : ℕ) * rhoDigitCount q b + (u : ℕ))) + k
            < Φ.φ.natDegree * (μ + ((i : ℕ) * rhoDigitCount q b + (u : ℕ)) + 1) := by
          rw [Nat.mul_succ]; omega
        have s2 : Φ.φ.natDegree * (μ + ((i : ℕ) * rhoDigitCount q b + (u : ℕ)) + 1)
            ≤ (μ + n * rhoDigitCount q b) * Φ.φ.natDegree := by
          rw [Nat.mul_comm]; exact Nat.mul_le_mul (by omega) (le_refl _)
        omega
      have hval := h (finFunctionFinEquiv.symm
        ⟨Φ.φ.natDegree * (μ + ((i : ℕ) * rhoDigitCount q b + (u : ℕ))) + k, hlt⟩)
      rw [wTable_rRow Φ m₀ φF b w hd i u.isLt hkd hlt] at hval
      exact le_trans (valMinAbs_natAbs_le_of_rangeProduct_eq_zero φF hval) hbound
    · -- `k ≥ deg φ`: `rhoDigits` truncates there, so the coefficient is zero
      rw [rhoDigits_coeff, if_neg hkd]
      simp

/-! ## Eq. (22) in the paper's table form: the `M̃_α`/`w̃`/`α̃` contraction

`hAlphaEvals` specifies the `α`-evaluated row defect **directly**, in the *ring* representation:
`cRowSum` contracts the public matrix against `w.z` as `Rq` elements and `evalAt · α` contracts
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
`i ∈ [n]` of `relLift` and the table row `u ∈ [μ + n·δ]` of `w̃`. The paper's three cases:

* `u < μ` — the `R^lin` matrix entry evaluated at `α`, namely `Mᵢᵤ(α)`;
* `μ ≤ u < μ + n·δ` with `(u − μ)/δ = i` — `−φ(α)·b^{(u−μ)%δ}`, placing the lift's
  `−(α^d + 1)·rᵢ(α)` term across row `i`'s `δ` **digit** columns, weighted by `b^u`. This is the
  digit-decomposed form of the paper's `−(α^d + 1)·b^u` entry;
* otherwise — `0`.

Only public data enters (`s.M`, `Φ.φ`, `α`, `b`), which is what makes the Figure 7 final check
verifier-computable: the prover supplies `w̃`, the verifier supplies `M̃_α`. -/
def mAlphaTilde (φF : ZMod q →+* F) (b : ℕ) (s : RlinStatement Φ n μ) (α : F) (i : Fin n)
    (u : ℕ) : F :=
  if hu : u < μ then cEvalAt φF α (s.M i ⟨u, hu⟩).1
  else if u < μ + n * rhoDigitCount q b ∧ (u - μ) / rhoDigitCount q b = (i : ℕ) then
    -cEvalAt φF α Φ.φ * φF ((b : ZMod q) ^ ((u - μ) % rhoDigitCount q b))
  else 0

/-- The `m₀`-cube point carrying table entry `(u, ℓ)` of `w̃` — row `u ∈ [μ + n·δ]`, column
`ℓ < d = deg φ` — at the flat index `d·u + ℓ` that `wTable` decodes. The arity pin
`(μ + n·δ)·d ≤ 2^{m₀}` is exactly what makes every such position a genuine cube point. -/
def wTablePoint (b : ℕ) (hμn : (μ + n * rhoDigitCount q b) * Φ.φ.natDegree ≤ 2 ^ m₀)
    (u : Fin (μ + n * rhoDigitCount q b)) (ℓ : Fin Φ.φ.natDegree) : Fin m₀ → Fin 2 :=
  finFunctionFinEquiv.symm ⟨Φ.φ.natDegree * (u : ℕ) + (ℓ : ℕ), by
    have hu := u.isLt
    have hl := ℓ.isLt
    have s1 : Φ.φ.natDegree * (u : ℕ) + (ℓ : ℕ) < Φ.φ.natDegree * ((u : ℕ) + 1) := by
      rw [Nat.mul_succ]; omega
    have s2 : Φ.φ.natDegree * ((u : ℕ) + 1) ≤ (μ + n * rhoDigitCount q b) * Φ.φ.natDegree := by
      rw [Nat.mul_comm]; exact Nat.mul_le_mul (by omega) (le_refl _)
    omega⟩

/-- Eq. (22)'s public contraction `∑_{u,ℓ} M̃_α(i,u)·w̃(u,ℓ)·α̃(ℓ)`, stated against an arbitrary
`m₀`-cube table `T` so that the paper object is defined independently of any particular witness.
For the witness instance `T = wTable …`, the corresponding defect is related to the ring-level
row equation by `alphaDefect_wTable`. -/
def alphaContract (φF : ZMod q →+* F) (b : ℕ) (s : RlinStatement Φ n μ) (α : F)
    (hμn : (μ + n * rhoDigitCount q b) * Φ.φ.natDegree ≤ 2 ^ m₀) (T : (Fin m₀ → Fin 2) → F)
    (i : Fin n) : F :=
  ∑ u : Fin (μ + n * rhoDigitCount q b), ∑ ℓ : Fin Φ.φ.natDegree,
    mAlphaTilde Φ φF b s α i (u : ℕ) * T (wTablePoint Φ m₀ b hμn u ℓ) * alphaTilde α (ℓ : ℕ)

/-- Eq. (22)'s per-row defect in the paper's table form: the public contraction against `T` minus
the public right-hand side `yᵢ(α)`. `H_α`'s Boolean table is exactly this at `T = w̃`
(`alphaDefect_wTable`, `hAlphaEvals_eq_alphaDefect`). -/
def alphaDefect (φF : ZMod q →+* F) (b : ℕ) (s : RlinStatement Φ n μ) (α : F)
    (hμn : (μ + n * rhoDigitCount q b) * Φ.φ.natDegree ≤ 2 ^ m₀) (T : (Fin m₀ → Fin 2) → F)
    (i : Fin n) : F :=
  alphaContract Φ m₀ φF b s α hμn T i - cEvalAt φF α (s.yvec i).1

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
    (hd : 0 < Φ.φ.natDegree) (hμn : (μ + n * rhoDigitCount q b) * Φ.φ.natDegree ≤ 2 ^ m₀)
    {u : Fin (μ + n * rhoDigitCount q b)} {j : Fin μ} (hj : (u : ℕ) = (j : ℕ))
    (ℓ : Fin Φ.φ.natDegree) :
    wTable Φ m₀ φF b w (wTablePoint Φ m₀ b hμn u ℓ) = φF ((w.z j).1.coeff (ℓ : ℕ)) := by
  have hlt : Φ.φ.natDegree * (j : ℕ) + (ℓ : ℕ) < 2 ^ m₀ := by
    have hj' := j.isLt
    have hl := ℓ.isLt
    have s1 : Φ.φ.natDegree * (j : ℕ) + (ℓ : ℕ) < Φ.φ.natDegree * ((j : ℕ) + 1) := by
      rw [Nat.mul_succ]; omega
    have s2 : Φ.φ.natDegree * ((j : ℕ) + 1) ≤ (μ + n * rhoDigitCount q b) * Φ.φ.natDegree := by
      rw [Nat.mul_comm]; exact Nat.mul_le_mul (by omega) (le_refl _)
    omega
  have hpt : wTablePoint Φ m₀ b hμn u ℓ
      = finFunctionFinEquiv.symm ⟨Φ.φ.natDegree * (j : ℕ) + (ℓ : ℕ), hlt⟩ := by
    unfold wTablePoint
    congr 1
    exact Fin.ext (by simp [hj])
  rw [hpt, wTable_zRow Φ m₀ φF b w hd j ℓ.isLt hlt]

omit [NeZero q] [IsCyclotomic Φ] [BEq F] [LawfulBEq F] in
/-- The quotient-block table entries: at a cube point whose table row is `μ + i·δ + u`, `w̃`
returns the embedded coefficient of digit `u` of quotient row `i`. Wrapper of `wTable_rRow` in
`wTablePoint` coordinates. -/
theorem wTable_wTablePoint_r (φF : ZMod q →+* F) (b : ℕ) (w : LiftedWitness Φ μ n)
    (hd : 0 < Φ.φ.natDegree) (hμn : (μ + n * rhoDigitCount q b) * Φ.φ.natDegree ≤ 2 ^ m₀)
    {U : Fin (μ + n * rhoDigitCount q b)} {i : Fin n} {u : ℕ} (hu : u < rhoDigitCount q b)
    (hU : (U : ℕ) = μ + ((i : ℕ) * rhoDigitCount q b + u)) (ℓ : Fin Φ.φ.natDegree) :
    wTable Φ m₀ φF b w (wTablePoint Φ m₀ b hμn U ℓ)
      = φF ((rhoDigits Φ b (w.ρ i) u).coeff (ℓ : ℕ)) := by
  have hU' := U.isLt
  have hl := ℓ.isLt
  have hlt : Φ.φ.natDegree * (μ + ((i : ℕ) * rhoDigitCount q b + u)) + (ℓ : ℕ) < 2 ^ m₀ := by
    have s1 : Φ.φ.natDegree * (U : ℕ) + (ℓ : ℕ) < Φ.φ.natDegree * ((U : ℕ) + 1) := by
      rw [Nat.mul_succ]; omega
    have s2 : Φ.φ.natDegree * ((U : ℕ) + 1) ≤ (μ + n * rhoDigitCount q b) * Φ.φ.natDegree := by
      rw [Nat.mul_comm]; exact Nat.mul_le_mul (by omega) (le_refl _)
    rw [← hU]; omega
  have hpt : wTablePoint Φ m₀ b hμn U ℓ
      = finFunctionFinEquiv.symm
        ⟨Φ.φ.natDegree * (μ + ((i : ℕ) * rhoDigitCount q b + u)) + (ℓ : ℕ), hlt⟩ := by
    unfold wTablePoint
    congr 1
    exact Fin.ext (by simp [hU])
  rw [hpt, wTable_rRow Φ m₀ φF b w hd i hu ℓ.isLt hlt]

omit [NeZero q] [BEq F] [LawfulBEq F] in
/-- **Eq. (22) is the row defect (change of representation).** The paper's public contraction of
`M̃_α`, `w̃` and `α̃`, evaluated against the committed table, equals the ring-level `α`-defect that
`hAlphaEvals` writes down directly. This is the step [NOZ26] §4.3 asserts as "representing the
constraints by polynomials", and it is the only place the table encoding of the witness (which the
commitment and the sumcheck use) and the ring encoding (which `relLift` uses) meet. -/
theorem alphaDefect_wTable (φF : ZMod q →+* F) (b : ℕ) (hb : 1 < b) (s : RlinStatement Φ n μ)
    (α : F) (w : LiftedWitness Φ μ n) (hd : 0 < Φ.φ.natDegree)
    (hμn : (μ + n * rhoDigitCount q b) * Φ.φ.natDegree ≤ 2 ^ m₀) (i : Fin n) :
    alphaDefect Φ m₀ φF b s α hμn (wTable Φ m₀ φF b w) i =
      cEvalAt φF α (cRowSum Φ s w.z i) - cEvalAt φF α (s.yvec i).1
        - cEvalAt φF α Φ.φ * evalAt φF α (w.ρ i).toPoly := by
  -- Column contraction (`α̃`): a reduced representative is its `d` coefficients against `α^ℓ`.
  have hzcol : ∀ j : Fin μ, cEvalAt φF α (w.z j).1
      = ∑ ℓ : Fin Φ.φ.natDegree, φF ((w.z j).1.coeff (ℓ : ℕ)) * α ^ (ℓ : ℕ) := fun j => by
    rw [cEvalAt_eq_sum_range φF α (Φ.natDegree_lt_of_reduced hd (w.z j).2)]
    exact (Fin.sum_univ_eq_sum_range _ _).symm
  -- The same column contraction for a quotient *digit*: `rhoDigits` truncates at `d`.
  have hrcol : ∀ (i' : Fin n) (u : ℕ), evalAt φF α (rhoDigits Φ b (w.ρ i') u).toPoly
      = ∑ ℓ : Fin Φ.φ.natDegree,
          φF ((rhoDigits Φ b (w.ρ i') u).coeff (ℓ : ℕ)) * α ^ (ℓ : ℕ) := by
    intro i' u
    have hdeg : (rhoDigits Φ b (w.ρ i') u).toPoly.natDegree < Φ.φ.natDegree :=
      lt_of_le_of_lt (rhoDigits_natDegree_le Φ b (w.ρ i') u) (by omega)
    rw [evalAt, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_eq_sum_range' φF hdeg α,
      ← Fin.sum_univ_eq_sum_range]
    exact Finset.sum_congr rfl fun ℓ _ => by rw [CPolynomial.coeff_toPoly]
  -- Row contraction (`M̃_α`'s `z` block): the public matrix against the witness entries.
  have hrow : cEvalAt φF α (cRowSum Φ s w.z i)
      = ∑ j : Fin μ, cEvalAt φF α (s.M i j).1 * cEvalAt φF α (w.z j).1 := by
    rw [cEvalAt_cRowSum_eq_evalAt, rowSum_eq_sum_toPoly, _root_.map_sum]
    exact Finset.sum_congr rfl fun j _ => by
      rw [_root_.map_mul, ← cEvalAt_eq_evalAt_toPoly, ← cEvalAt_eq_evalAt_toPoly]
  -- The `z` block of the contraction reproduces one term of `cRowSum`.
  have hz : ∀ j : Fin μ, (∑ ℓ : Fin Φ.φ.natDegree,
      mAlphaTilde Φ φF b s α i
          ((Fin.castAdd (n * rhoDigitCount q b) j :
            Fin (μ + n * rhoDigitCount q b)) : ℕ) *
        wTable Φ m₀ φF b w
          (wTablePoint Φ m₀ b hμn (Fin.castAdd (n * rhoDigitCount q b) j) ℓ) *
        alphaTilde α (ℓ : ℕ))
      = cEvalAt φF α (s.M i j).1 * cEvalAt φF α (w.z j).1 := by
    intro j
    have hjv : ((Fin.castAdd (n * rhoDigitCount q b) j :
        Fin (μ + n * rhoDigitCount q b)) : ℕ) = (j : ℕ) := rfl
    have hM : mAlphaTilde Φ φF b s α i
        ((Fin.castAdd (n * rhoDigitCount q b) j : Fin (μ + n * rhoDigitCount q b)) : ℕ)
        = cEvalAt φF α (s.M i j).1 := by
      unfold mAlphaTilde
      exact dif_pos j.isLt
    rw [hzcol j, Finset.mul_sum]
    exact Finset.sum_congr rfl fun ℓ _ => by
      simp only [hM, wTable_wTablePoint_z Φ m₀ φF b w hd hμn hjv ℓ, alphaTilde, mul_assoc]
  -- The flattened `(row, digit)` index, in the layout `liftMessage` and `wTable` share.
  have hprod : ∀ p : Fin n × Fin (rhoDigitCount q b),
      ((finProdFinEquiv p : Fin (n * rhoDigitCount q b)) : ℕ)
        = (p.1 : ℕ) * rhoDigitCount q b + (p.2 : ℕ) := by
    intro p
    have hv : ((finProdFinEquiv p : Fin (n * rhoDigitCount q b)) : ℕ)
        = (p.2 : ℕ) + rhoDigitCount q b * (p.1 : ℕ) := rfl
    rw [hv]; ring
  -- The digit block: only the `δ` columns of row `i` survive, weighted by `b^u`.
  have hr : ∀ p : Fin n × Fin (rhoDigitCount q b), (∑ ℓ : Fin Φ.φ.natDegree,
      mAlphaTilde Φ φF b s α i
          ((Fin.natAdd μ (finProdFinEquiv p) : Fin (μ + n * rhoDigitCount q b)) : ℕ) *
        wTable Φ m₀ φF b w
          (wTablePoint Φ m₀ b hμn (Fin.natAdd μ (finProdFinEquiv p)) ℓ) *
        alphaTilde α (ℓ : ℕ))
      = if p.1 = i then
          -(cEvalAt φF α Φ.φ * (φF ((b : ZMod q) ^ (p.2 : ℕ))
            * evalAt φF α (rhoDigits Φ b (w.ρ i) (p.2 : ℕ)).toPoly))
        else 0 := by
    intro p
    have hu := p.2.isLt
    have hδ : 0 < rhoDigitCount q b := by omega
    have hUv : ((Fin.natAdd μ (finProdFinEquiv p) : Fin (μ + n * rhoDigitCount q b)) : ℕ)
        = μ + ((p.1 : ℕ) * rhoDigitCount q b + (p.2 : ℕ)) := by
      have hv : ((Fin.natAdd μ (finProdFinEquiv p) : Fin (μ + n * rhoDigitCount q b)) : ℕ)
          = μ + ((finProdFinEquiv p : Fin (n * rhoDigitCount q b)) : ℕ) := rfl
      rw [hv, hprod p]
    have hlow : ¬ ((Fin.natAdd μ (finProdFinEquiv p) :
        Fin (μ + n * rhoDigitCount q b)) : ℕ) < μ := by rw [hUv]; omega
    have hdiv : (μ + ((p.1 : ℕ) * rhoDigitCount q b + (p.2 : ℕ)) - μ) / rhoDigitCount q b
        = (p.1 : ℕ) := by
      rw [Nat.add_sub_cancel_left, Nat.mul_comm, Nat.mul_add_div hδ,
        Nat.div_eq_of_lt hu, Nat.add_zero]
    have hmod : (μ + ((p.1 : ℕ) * rhoDigitCount q b + (p.2 : ℕ)) - μ) % rhoDigitCount q b
        = (p.2 : ℕ) := by
      rw [Nat.add_sub_cancel_left, Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hu]
    by_cases hpi : p.1 = i
    · have hM : mAlphaTilde Φ φF b s α i
          ((Fin.natAdd μ (finProdFinEquiv p) : Fin (μ + n * rhoDigitCount q b)) : ℕ)
          = -cEvalAt φF α Φ.φ * φF ((b : ZMod q) ^ (p.2 : ℕ)) := by
        unfold mAlphaTilde
        rw [dif_neg hlow, if_pos ⟨by rw [hUv]; omega, by rw [hUv, hdiv, hpi]⟩, hUv, hmod]
      rw [if_pos hpi, hrcol i (p.2 : ℕ), Finset.mul_sum, Finset.mul_sum,
        ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun ℓ _ => ?_
      rw [hM, wTable_wTablePoint_r Φ m₀ φF b w hd hμn hu (by rw [hUv, hpi]) ℓ]
      simp only [alphaTilde]
      ring
    · have hM : mAlphaTilde Φ φF b s α i
          ((Fin.natAdd μ (finProdFinEquiv p) : Fin (μ + n * rhoDigitCount q b)) : ℕ) = 0 := by
        unfold mAlphaTilde
        rw [dif_neg hlow, if_neg ?_]
        rintro ⟨-, hc⟩
        rw [hUv, hdiv] at hc
        exact hpi (Fin.ext hc)
      rw [if_neg hpi]
      exact Finset.sum_eq_zero fun ℓ _ => by rw [hM, zero_mul, zero_mul]
  have hzsum : (∑ j : Fin μ, ∑ ℓ : Fin Φ.φ.natDegree,
      mAlphaTilde Φ φF b s α i
          ((Fin.castAdd (n * rhoDigitCount q b) j :
            Fin (μ + n * rhoDigitCount q b)) : ℕ) *
        wTable Φ m₀ φF b w
          (wTablePoint Φ m₀ b hμn (Fin.castAdd (n * rhoDigitCount q b) j) ℓ) *
        alphaTilde α (ℓ : ℕ))
      = cEvalAt φF α (cRowSum Φ s w.z i) := by
    rw [hrow]; exact Finset.sum_congr rfl fun j _ => hz j
  have hrsum : (∑ k : Fin (n * rhoDigitCount q b), ∑ ℓ : Fin Φ.φ.natDegree,
      mAlphaTilde Φ φF b s α i
          ((Fin.natAdd μ k : Fin (μ + n * rhoDigitCount q b)) : ℕ) *
        wTable Φ m₀ φF b w (wTablePoint Φ m₀ b hμn (Fin.natAdd μ k) ℓ) *
        alphaTilde α (ℓ : ℕ))
      = -(cEvalAt φF α Φ.φ * evalAt φF α (w.ρ i).toPoly) := by
    rw [← Equiv.sum_comp (finProdFinEquiv (m := n) (n := rhoDigitCount q b)),
      Fintype.sum_prod_type]
    have hinner : ∀ i' : Fin n, (∑ u : Fin (rhoDigitCount q b),
        (if i' = i then
          -(cEvalAt φF α Φ.φ * (φF ((b : ZMod q) ^ (u : ℕ))
            * evalAt φF α (rhoDigits Φ b (w.ρ i) (u : ℕ)).toPoly))
        else 0))
        = if i' = i then
            -(cEvalAt φF α Φ.φ * ∑ u : Fin (rhoDigitCount q b),
              φF ((b : ZMod q) ^ (u : ℕ))
                * evalAt φF α (rhoDigits Φ b (w.ρ i) (u : ℕ)).toPoly)
          else 0 := by
      intro i'
      by_cases hc : i' = i
      · rw [if_pos hc, Finset.mul_sum, ← Finset.sum_neg_distrib]
        exact Finset.sum_congr rfl fun u _ => by rw [if_pos hc]
      · simp [hc]
    rw [show (∑ i' : Fin n, ∑ u : Fin (rhoDigitCount q b), _) = _ from
      Finset.sum_congr rfl fun i' _ => (Finset.sum_congr rfl fun u _ => hr (i', u)).trans
        (hinner i')]
    rw [Finset.sum_ite_eq' Finset.univ i (fun _ =>
      -(cEvalAt φF α Φ.φ * ∑ u : Fin (rhoDigitCount q b),
        φF ((b : ZMod q) ^ (u : ℕ))
          * evalAt φF α (rhoDigits Φ b (w.ρ i) (u : ℕ)).toPoly)), if_pos (Finset.mem_univ i),
      ← rhoDigits_evalAt Φ φF α hb hd (w.ρ i) (w.hρ i)]
  simp only [alphaDefect, alphaContract, Fin.sum_univ_add]
  rw [hzsum, hrsum]
  ring

omit [NeZero q] [BEq F] [LawfulBEq F] in
/-- `H_α`'s Boolean table *is* Eq. (22)'s per-row defect at every Boolean point: the row-encoded
points carry the contraction, and the padding rows `≥ n` carry `0`. -/
theorem hAlphaEvals_eq_alphaDefect (φF : ZMod q →+* F) (b : ℕ) (hb : 1 < b)
    (s : RlinStatement Φ n μ) (α : F) (w : LiftedWitness Φ μ n) (hd : 0 < Φ.φ.natDegree)
    (hμn : (μ + n * rhoDigitCount q b) * Φ.φ.natDegree ≤ 2 ^ m₀) (x : Fin m₁ → Fin 2) :
    hAlphaEvals Φ m₁ φF b s α w x =
      if h : ((finFunctionFinEquiv x : Fin (2 ^ m₁)) : ℕ) < n then
        alphaDefect Φ m₀ φF b s α hμn (wTable Φ m₀ φF b w) ⟨_, h⟩
      else 0 := by
  by_cases h : ((finFunctionFinEquiv x : Fin (2 ^ m₁)) : ℕ) < n
  · rw [dif_pos h, alphaDefect_wTable Φ m₀ φF b hb s α w hd hμn ⟨_, h⟩,
      rhoDigits_evalAt Φ φF α hb hd (w.ρ ⟨_, h⟩) (w.hρ _)]
    simp only [hAlphaEvals, dif_pos h]
  · rw [dif_neg h]
    simp only [hAlphaEvals, dif_neg h]

omit [NeZero q] [BEq F] [LawfulBEq F] in
/-- **`relBatched`'s `α`-conjunct is exactly Eq. (22)'s row constraints.** `H_α ≡ 0` — the identity
carried by `relBatched` (`ZeroCheck/Batch.lean`) and extracted by the zero-check — holds iff every
row's paper-form defect `∑_{u,ℓ} M̃_α(i,u)·w̃(u,ℓ)·α̃(ℓ) − yᵢ(α)` vanishes. This is what licenses
reading `relBatched` as a formalization of Eq. (22) rather than of an abstract direct-defect
variant of it. -/
theorem hAlpha_eq_zero_iff_alphaDefect (φF : ZMod q →+* F) (b : ℕ) (hb : 1 < b)
    (s : RlinStatement Φ n μ) (α : F) (w : LiftedWitness Φ μ n) (hd : 0 < Φ.φ.natDegree)
    (hn : n ≤ 2 ^ m₁)
    (hμn : (μ + n * rhoDigitCount q b) * Φ.φ.natDegree ≤ 2 ^ m₀) :
    hAlpha Φ m₁ φF b s α w = 0 ↔
      ∀ i : Fin n, alphaDefect Φ m₀ φF b s α hμn (wTable Φ m₀ φF b w) i = 0 := by
  rw [hAlpha_eq_zero_iff]
  constructor
  · intro h i
    have hlt : ((finFunctionFinEquiv (rowPoint m₁ hn i) : Fin (2 ^ m₁)) : ℕ) < n := by
      simp only [rowPoint, Equiv.apply_symm_apply]
      exact i.isLt
    have hx := h (rowPoint m₁ hn i)
    rw [hAlphaEvals_eq_alphaDefect Φ m₀ m₁ φF b hb s α w hd hμn, dif_pos hlt] at hx
    have hidx : (⟨((finFunctionFinEquiv (rowPoint m₁ hn i) : Fin (2 ^ m₁)) : ℕ), hlt⟩ : Fin n)
        = i := Fin.ext (by simp [rowPoint])
    rwa [hidx] at hx
  · intro h x
    rw [hAlphaEvals_eq_alphaDefect Φ m₀ m₁ φF b hb s α w hd hμn]
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
def alphaPublicEvals (φF : ZMod q →+* F) (b : ℕ) (s : RlinStatement Φ n μ) (α : F)
    (τ₁ : Fin m₁ → F) (x : Fin m₀ → Fin 2) : F :=
  let idx : ℕ := (finFunctionFinEquiv x : Fin (2 ^ m₀))
  let d := Φ.φ.natDegree
  alphaTilde α (idx % d) * ∑ i : Fin n,
    (if hi : (i : ℕ) < 2 ^ m₁ then
      (∏ j : Fin m₁,
        if (finFunctionFinEquiv.symm ⟨(i : ℕ), hi⟩) j = 1 then τ₁ j else 1 - τ₁ j) *
          mAlphaTilde Φ φF b s α i (idx / d)
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
    cMultilinearExtension m₀ (alphaPublicEvals Φ m₀ m₁ φF b s α τ₁)

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

omit [BEq F] [LawfulBEq F] in
/-- **Saturation of the partial sum.** Once the challenge prefix covers every cube coordinate
(`m₀ ≤ i`), the trailing cube is a single point and `hypercubeSum` collapses to a plain evaluation
at the prefix — in particular it stops depending on the coordinates beyond the `m₀`-th.

Two consumers, in opposite directions:

* at `i = m₀` this is what makes the loop's last seam a *point* claim, which is what the
  final-evaluation check reads ([NOZ26] Figure 7 tail);
* for `m₀ < i` it is exactly why a further round would be unsound: the round polynomial `g` is
  forced constant `= H.eval cs`, so the guard `g(0) + g(1) = target` yields `2·H.eval cs = target`
  while the round-`i` claim asks for `H.eval cs = target`. This is the reason
  `round_coordinateWiseSpecialSoundWithEscape` (`Sumcheck/Rounds.lean`) carries `i < m₀`. -/
theorem hypercubeSum_of_le (H : CMvPolynomial m₀ F) {i : ℕ} (hi : m₀ ≤ i) (cs : Fin i → F) :
    hypercubeSum m₀ H i cs = H.eval (fun j => cs ⟨j, lt_of_lt_of_le j.isLt hi⟩) := by
  have : IsEmpty (Fin (m₀ - i)) := ⟨fun j => absurd j.isLt (by omega)⟩
  rw [hypercubeSum, Fintype.sum_unique]
  congr 1
  funext j
  simp only [hypercubePoint]
  exact dif_pos (lt_of_lt_of_le j.isLt hi)


/-! ### Evaluating the computable summands

The summands are assembled from three computable pieces — the Lagrange basis
`cBooleanEqPolynomial`, the multilinear extension `cMultilinearExtension`, and the range factor
`cRangeProduct`. Each of the next lemmas says what one of them evaluates to, which is all the
sum identities below need: they turn a `CMvPolynomial` evaluation into an `F`-level expression,
after which the argument is ordinary algebra over the Boolean cube. The `CMvPolynomial`-side
`Finset` machinery is `ArkLib/ToCompPoly/Multivariate/Eval.lean`. -/

omit [BEq F] [LawfulBEq F] in
/-- `eq̃(x, τ)` for a *Boolean* `x`: the Mathlib equality polynomial of a cube point, evaluated at
an arbitrary point, is the product of per-coordinate selections. This is the shape the computable
Lagrange basis produces, so it is the bridge between the two representations of `eq̃`. -/
theorem eval_eqPolynomial_boolean (x : Fin m₀ → Fin 2) (τ : Fin m₀ → F) :
    MvPolynomial.eval τ (eqPolynomial ((x : Fin m₀ → F))) =
      ∏ i : Fin m₀, if x i = 1 then τ i else 1 - τ i := by
  rw [eqPolynomial_expanded, _root_.map_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  simp only [_root_.map_add, _root_.map_mul, _root_.map_sub, _root_.map_one,
    MvPolynomial.eval_C, MvPolynomial.eval_X]
  by_cases h : x i = 1
  · rw [if_pos h, h]; norm_num
  · have h0 : x i = 0 := by fin_omega
    rw [if_neg h, h0]; norm_num

omit [BEq F] [LawfulBEq F] in
/-- **A multilinear extension evaluates to the `eq̃`-weighted cube sum of its table.** The
Mathlib-side reading of "the sum over the cube of `eq̃(τ, ·)` against a table is that table's
multilinear extension at `τ`" — the identity both sum theorems below are ultimately instances
of. -/
theorem eval_MLE_eq_sum (g : (Fin m₀ → Fin 2) → F) (τ : Fin m₀ → F) :
    MvPolynomial.eval τ (MLE g) =
      ∑ x : Fin m₀ → Fin 2, g x * ∏ i : Fin m₀, if x i = 1 then τ i else 1 - τ i := by
  rw [MLE, _root_.map_sum]
  exact Finset.sum_congr rfl fun x _ => by
    rw [_root_.map_mul, MvPolynomial.eval_C, eval_eqPolynomial_boolean, mul_comm]

/-- The computable Lagrange basis polynomial of a cube point, evaluated at an arbitrary point. -/
theorem cBooleanEqPolynomial_eval (x : Fin m₀ → Fin 2) (τ : Fin m₀ → F) :
    (cBooleanEqPolynomial m₀ x).eval τ =
      ∏ i : Fin m₀, if x i = 1 then τ i else 1 - τ i := by
  rw [cBooleanEqPolynomial, CMvPolynomial.eval_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  by_cases h : x i = 1 <;> simp [h]

/-- **The computable multilinear extension is Mathlib's.** Both representations of the multilinear
extension of a Boolean table agree at every point; the computable one is what the protocol folds,
the Mathlib one is what the algebra below reasons about. -/
theorem cMultilinearExtension_eval (evals : (Fin m₀ → Fin 2) → F) (τ : Fin m₀ → F) :
    (cMultilinearExtension m₀ evals).eval τ = MvPolynomial.eval τ (MLE evals) := by
  rw [cMultilinearExtension, CMvPolynomial.eval_sum, eval_MLE_eq_sum]
  exact Finset.sum_congr rfl fun x _ => by
    rw [CPoly.eval_mul, CPoly.eval_C, cBooleanEqPolynomial_eval]

/-- At a Boolean point the computable multilinear extension returns the table entry. -/
theorem cMultilinearExtension_eval_boolean (evals : (Fin m₀ → Fin 2) → F)
    (y : Fin m₀ → Fin 2) :
    (cMultilinearExtension m₀ evals).eval ((y : Fin m₀ → F)) = evals y := by
  rw [cMultilinearExtension_eval, MLE_eval_zeroOne]

/-- At a Boolean point the computable `eq̃(τ₀, ·)` polynomial returns the per-coordinate
selection product. -/
theorem cEqualityPolynomial_eval_boolean (τ : Fin m₀ → F) (y : Fin m₀ → Fin 2) :
    (cEqualityPolynomial m₀ τ).eval ((y : Fin m₀ → F)) =
      ∏ i : Fin m₀, if y i = 1 then τ i else 1 - τ i := by
  rw [cEqualityPolynomial, cMultilinearExtension_eval_boolean]

/-- The range factor commutes with evaluation: applying `cRangeProduct` and then evaluating is
applying `rangeProduct` to the evaluation. -/
theorem cRangeProduct_eval (b : ℕ) (p : CMvPolynomial m₀ F) (τ : Fin m₀ → F) :
    (cRangeProduct m₀ b p).eval τ = rangeProduct b (p.eval τ) := by
  rw [cRangeProduct, rangeProduct, CPoly.eval_mul, CMvPolynomial.eval_prod]
  exact congrArg _ (Finset.prod_congr rfl fun j _ => by simp)

/-! ### Per-variable degrees of the summands

The round message is degree-bounded (`RoundMsg`, `Sumcheck/Rounds.lean`), and Lemma 11's
extraction needs the matching bound on the summand: a defect polynomial of degree `≤ D` vanishing
at `D + 1` points is identically zero. A degree is *not* determined by values — two distinct
polynomials agree everywhere over a finite field — so unlike the evaluation lemmas above these
must cross the representation boundary at the level of the polynomial itself, through
`fromCMvPolynomial`. -/

omit [NeZero q] [IsCyclotomic Φ] in
/-- The computable Lagrange basis transports to Mathlib's equality polynomial. -/
theorem fromCMvPolynomial_cBooleanEqPolynomial (x : Fin m₀ → Fin 2) :
    fromCMvPolynomial (cBooleanEqPolynomial m₀ x) = eqPolynomial ((x : Fin m₀ → F)) := by
  rw [cBooleanEqPolynomial, CMvPolynomial.fromCMvPolynomial_prod, eqPolynomial_zeroOne]
  refine Finset.prod_congr rfl fun i _ => ?_
  by_cases h : x i = 1
  · rw [if_pos h, if_neg (by rw [h]; decide), CMvPolynomial.fromCMvPolynomial_X]
  · have h0 : x i = 0 := by fin_omega
    rw [if_neg h, if_pos h0, CMvPolynomial.fromCMvPolynomial_sub',
      CMvPolynomial.fromCMvPolynomial_one', CMvPolynomial.fromCMvPolynomial_X]

omit [NeZero q] [IsCyclotomic Φ] in
/-- **The computable multilinear extension transports to Mathlib's `MLE`.** Strictly stronger than
`cMultilinearExtension_eval`, which only matches their values: this is an identity of
polynomials, which is what a degree bound needs. -/
theorem fromCMvPolynomial_cMultilinearExtension (evals : (Fin m₀ → Fin 2) → F) :
    fromCMvPolynomial (cMultilinearExtension m₀ evals) = MLE evals := by
  rw [cMultilinearExtension, CMvPolynomial.fromCMvPolynomial_sum, MLE]
  exact Finset.sum_congr rfl fun x _ => by
    rw [CMvPolynomial.fromCMvPolynomial_mul', CMvPolynomial.fromCMvPolynomial_C,
      fromCMvPolynomial_cBooleanEqPolynomial, mul_comm]

omit [NeZero q] [IsCyclotomic Φ] in
/-- The computable range factor transports to the corresponding Mathlib product. -/
theorem fromCMvPolynomial_cRangeProduct (b : ℕ) (p : CMvPolynomial m₀ F) :
    fromCMvPolynomial (cRangeProduct m₀ b p) =
      fromCMvPolynomial p * ∏ k ∈ Finset.Icc 1 (b - 1),
        ((fromCMvPolynomial p - MvPolynomial.C (k : F)) *
          (fromCMvPolynomial p + MvPolynomial.C (k : F))) := by
  rw [cRangeProduct, CMvPolynomial.fromCMvPolynomial_mul',
    CMvPolynomial.fromCMvPolynomial_prod]
  exact congrArg _ (Finset.prod_congr rfl fun k _ => by
    rw [CMvPolynomial.fromCMvPolynomial_mul', CMvPolynomial.fromCMvPolynomial_sub',
      CMvPolynomial.fromCMvPolynomial_add', CMvPolynomial.fromCMvPolynomial_C])

omit [NeZero q] [IsCyclotomic Φ] [BEq F] [LawfulBEq F] in
/-- Shifting by a constant does not raise the per-variable degree. -/
theorem degreeOf_add_C_le {P : MvPolynomial (Fin m₀) F} {j : Fin m₀} {c : F} {D : ℕ}
    (hP : P.degreeOf j ≤ D) : (P + MvPolynomial.C c).degreeOf j ≤ D :=
  le_trans (MvPolynomial.degreeOf_add_le _ _ _)
    (by simp [MvPolynomial.degreeOf_C, hP])

omit [NeZero q] [IsCyclotomic Φ] [BEq F] [LawfulBEq F] in
/-- **The range product raises the per-variable degree from `≤ 1` to `≤ 2b − 1`**: it is `P` times
`b − 1` quadratic factors. The `0 < b` hypothesis is real — at `b = 0` the product is empty, the
polynomial is `P` itself of degree `1`, and the claimed bound `2·0 − 1 = 0` fails. -/
theorem degreeOf_rangeProduct_le {b : ℕ} (hb : 0 < b) (P : MvPolynomial (Fin m₀) F)
    (j : Fin m₀) (hP : P.degreeOf j ≤ 1) :
    (P * ∏ k ∈ Finset.Icc 1 (b - 1),
        ((P - MvPolynomial.C (k : F)) * (P + MvPolynomial.C (k : F)))).degreeOf j
      ≤ 2 * b - 1 := by
  have hfac : ∀ k ∈ Finset.Icc 1 (b - 1),
      ((P - MvPolynomial.C (k : F)) * (P + MvPolynomial.C (k : F))).degreeOf j ≤ 2 := by
    intro k _
    have hsub : (P - MvPolynomial.C (k : F)).degreeOf j ≤ 1 := by
      have : P - MvPolynomial.C (k : F) = P + MvPolynomial.C (-(k : F)) := by
        rw [_root_.map_neg, ← sub_eq_add_neg]
      rw [this]; exact degreeOf_add_C_le (hP := hP)
    have hadd : (P + MvPolynomial.C (k : F)).degreeOf j ≤ 1 := degreeOf_add_C_le (hP := hP)
    exact le_trans (MvPolynomial.degreeOf_mul_le _ _ _) (by omega)
  have hprod : (∏ k ∈ Finset.Icc 1 (b - 1),
      ((P - MvPolynomial.C (k : F)) * (P + MvPolynomial.C (k : F)))).degreeOf j
      ≤ 2 * (b - 1) := by
    refine le_trans (MvPolynomial.degreeOf_prod_le _ _ _) ?_
    refine le_trans (Finset.sum_le_sum hfac) ?_
    rw [Finset.sum_const, Nat.card_Icc, smul_eq_mul]
    omega
  exact le_trans (MvPolynomial.degreeOf_mul_le _ _ _) (by omega)

omit [NeZero q] [IsCyclotomic Φ] in
/-- **Per-variable degree of the range summand: `deg F_{0,τ₀} ≤ 2b`** — the `roundDegZero b` pin
that `RoundMsg`'s first component and Lemma 11's `k = max (2b) 2 + 1` are set against.
`eq̃(τ₀, ·)` contributes `1` and the range product `2b − 1`. -/
theorem degreeOf_sumcheckPolyZero {b : ℕ} (hb : 0 < b) (φF : ZMod q →+* F) (τ₀ : Fin m₀ → F)
    (w : LiftedWitness Φ μ n) (j : Fin m₀) :
    (fromCMvPolynomial (sumcheckPolyZero Φ m₀ φF b τ₀ w)).degreeOf j ≤ roundDegZero b := by
  rw [sumcheckPolyZero, CMvPolynomial.fromCMvPolynomial_mul', cEqualityPolynomial,
    fromCMvPolynomial_cMultilinearExtension, fromCMvPolynomial_cRangeProduct,
    fromCMvPolynomial_cMultilinearExtension, roundDegZero]
  refine le_trans (MvPolynomial.degreeOf_mul_le _ _ _) ?_
  have h₁ := MLE_degreeOf (fun x => ∏ i : Fin m₀, if x i = 1 then τ₀ i else 1 - τ₀ i) j
  have h₂ := degreeOf_rangeProduct_le (hb := hb) (P := MLE (wTable Φ m₀ φF b w)) (j := j)
    (hP := MLE_degreeOf (wTable Φ m₀ φF b w) j)
  omega

omit [NeZero q] [IsCyclotomic Φ] in
/-- **Per-variable degree of the linear summand: `deg F_{α,τ₁} ≤ 2`** — the `roundDegAlpha` pin.
It is a product of two multilinear factors, so no hypothesis on `b` is needed. -/
theorem degreeOf_sumcheckPolyAlpha (φF : ZMod q →+* F) (b : ℕ) (s : RlinStatement Φ n μ) (α : F)
    (τ₁ : Fin m₁ → F) (w : LiftedWitness Φ μ n) (j : Fin m₀) :
    (fromCMvPolynomial (sumcheckPolyAlpha Φ m₀ m₁ φF b s α τ₁ w)).degreeOf j
      ≤ roundDegAlpha := by
  rw [sumcheckPolyAlpha, CMvPolynomial.fromCMvPolynomial_mul',
    fromCMvPolynomial_cMultilinearExtension,
    fromCMvPolynomial_cMultilinearExtension, roundDegAlpha]
  refine le_trans (MvPolynomial.degreeOf_mul_le _ _ _) ?_
  have h₁ := MLE_degreeOf (wTable Φ m₀ φF b w) j
  have h₂ := MLE_degreeOf (alphaPublicEvals Φ m₀ m₁ φF b s α τ₁) j
  omega

omit [NeZero q] [BEq F] [LawfulBEq F] in
/-- The full-cube sum, with the empty challenge prefix unfolded: `hypercubeSum … 0` ranges over
every Boolean point of the `m₀`-cube. -/
theorem hypercubeSum_zero (H : CMvPolynomial m₀ F) :
    hypercubeSum m₀ H 0 (fun j => j.elim0) =
      ∑ x : Fin m₀ → Fin 2, H.eval ((x : Fin m₀ → F)) := rfl

omit [NeZero q] [IsCyclotomic Φ] in
omit [NeZero q] [IsCyclotomic Φ] in
/-- The full-cube sum of the range summand `F_{0,τ₀}` equals `H₀(τ₀)`.

### Deliberate divergence: no `1_{≤μ}` indicator

The paper's `F_{0,τ₀}` (p. 22) carries a trailing indicator factor `1_{≤μ}(x,y)` that restricts the
range check to the `z` rows, whereas Eq. (23)'s `H₀` carries **no** such factor, sums over all
`(u, ℓ)`, and the bullet above it imposes the constraint "for each `u ∈ [μ + n]` and `ℓ ∈ [d]`" —
i.e. on the `r` rows as well, consistent with the earlier requirement `‖z‖∞, ‖r‖∞ ≤ b − 1`. The two
readings are not equivalent, so the paper's own `∑_{u,ℓ} F_{0,τ₀}(u,ℓ) = H₀(τ₀)` is **false as
printed**: the two sides differ exactly by the indicator.

This file follows the Eq. (23) reading — no indicator, and the range constraint applied to **every**
row of `w̃`, the `n·δ` quotient-digit rows included. That is not just the self-consistent choice but
the paper's *intended* protocol: §4.3 (p. 19) gadget-decomposes the quotient into base-`b` digits
before committing ("there is a hidden gadget decomposition of r"), and committing `w̃` without
re-decomposition (§4.5) requires every committed row short — so the indicator-free `H₀` is the
correct object and the `1_{≤μ}` in `F_{0,τ₀}` is the leftover of the paper's simplified
presentation.

Where the two blocks *differ* is in what the constraint buys, and it is worth being exact.
`wTable` fills both (`wTable_zRow`, `wTable_rRow`), and `hZero_eq_zero_imp_liftShort` reads both.
But the digit rows are in range **by construction** — `wTable` computes them with `rhoDigits`, and
`rhoDigits_valMinAbs_natAbs_le` bounds every digit by `⌊b/2⌋` for an arbitrary quotient — so `H₀`'s
substantive soundness content is the `z` block. The digit half is a consistency condition on the
encoding, not a constraint that can fail. That is the point of committing digits: the bound on the
quotient block is supplied at radius `⌊b/2⌋` by the encoding rather than extracted from `H₀` at
radius `q/2` (`rhoShort_half`), which is what keeps `LiftCom.Collision` a real Module-SIS instance.

Anyone comparing this statement against Figure 5 should read the absent indicator as intentional
rather than as a bug. -/
theorem sum_sumcheckPolyZero (φF : ZMod q →+* F) (b : ℕ) (τ₀ : Fin m₀ → F)
    (w : LiftedWitness Φ μ n) :
    hypercubeSum m₀ (sumcheckPolyZero Φ m₀ φF b τ₀ w) 0 (fun j => j.elim0) =
      MvPolynomial.eval τ₀ (hZeroML Φ m₀ φF b w).val := by
  rw [hypercubeSum_zero]
  simp only [hZeroML, eval_MLE_eq_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [sumcheckPolyZero, CPoly.eval_mul, cEqualityPolynomial_eval_boolean, cRangeProduct_eval,
    cMultilinearExtension_eval_boolean, mul_comm]

/-! ### The `α`-summand's table contraction

`alphaPublicEvals` multiplies the committed table by the public data at the *flat cube index*,
reading the row as `idx / d` and the column as `idx % d`; Eq. (22)'s `alphaContract` instead sums
over the table's `(row, column)` block. The next lemmas reconcile the two sums: the flat index of
block entry `(u, ℓ)` is `d·u + ℓ`, that assignment is injective, and off its image the public
matrix vanishes — so the cube sum and the block sum have the same terms. -/

omit [NeZero q] [IsCyclotomic Φ] [BEq F] [LawfulBEq F] in
/-- Outside the encoded block the public matrix vanishes: row `u ≥ μ + n·δ` is neither an `R^lin`
column (`u < μ`) nor one of row `i`'s `δ` digit columns (those have `u < μ + n·δ`). This is what
makes the cube sum collapse onto the block. -/
theorem mAlphaTilde_eq_zero_of_ge (φF : ZMod q →+* F) (b : ℕ) (s : RlinStatement Φ n μ) (α : F)
    (i : Fin n) {u : ℕ} (hu : μ + n * rhoDigitCount q b ≤ u) :
    mAlphaTilde Φ φF b s α i u = 0 := by
  have hi := i.isLt
  rw [mAlphaTilde, dif_neg (by omega), if_neg (by omega)]

/-- The flat `m₀`-cube index of table entry `(u, ℓ)`, namely `d·u + ℓ` — the index `wTablePoint`
decodes and the index `alphaPublicEvals` reads back through `/ d` and `% d`. -/
def wTableIndex (b : ℕ) (hμn : (μ + n * rhoDigitCount q b) * Φ.φ.natDegree ≤ 2 ^ m₀)
    (p : Fin (μ + n * rhoDigitCount q b) × Fin Φ.φ.natDegree) : Fin (2 ^ m₀) :=
  ⟨Φ.φ.natDegree * (p.1 : ℕ) + (p.2 : ℕ), by
    have hu := p.1.isLt
    have hl := p.2.isLt
    have s1 : Φ.φ.natDegree * (p.1 : ℕ) + (p.2 : ℕ) < Φ.φ.natDegree * ((p.1 : ℕ) + 1) := by
      rw [Nat.mul_succ]; omega
    have s2 : Φ.φ.natDegree * ((p.1 : ℕ) + 1)
        ≤ (μ + n * rhoDigitCount q b) * Φ.φ.natDegree := by
      rw [Nat.mul_comm]; exact Nat.mul_le_mul (by omega) (le_refl _)
    omega⟩

omit [NeZero q] [IsCyclotomic Φ] in
/-- `wTablePoint` is `wTableIndex` decoded — the two spellings of the same cube point. -/
theorem wTablePoint_eq_symm_wTableIndex (b : ℕ)
    (hμn : (μ + n * rhoDigitCount q b) * Φ.φ.natDegree ≤ 2 ^ m₀)
    (u : Fin (μ + n * rhoDigitCount q b)) (ℓ : Fin Φ.φ.natDegree) :
    wTablePoint Φ m₀ b hμn u ℓ = finFunctionFinEquiv.symm (wTableIndex Φ m₀ b hμn (u, ℓ)) := rfl

omit [NeZero q] [IsCyclotomic Φ] in
/-- Recovering the block coordinates from the flat index: `(d·u + ℓ) / d = u` and
`(d·u + ℓ) % d = ℓ`. -/
theorem wTableIndex_div_mod (b : ℕ) (hd : 0 < Φ.φ.natDegree)
    (hμn : (μ + n * rhoDigitCount q b) * Φ.φ.natDegree ≤ 2 ^ m₀)
    (p : Fin (μ + n * rhoDigitCount q b) × Fin Φ.φ.natDegree) :
    ((wTableIndex Φ m₀ b hμn p : Fin (2 ^ m₀)) : ℕ) / Φ.φ.natDegree = (p.1 : ℕ) ∧
      ((wTableIndex Φ m₀ b hμn p : Fin (2 ^ m₀)) : ℕ) % Φ.φ.natDegree = (p.2 : ℕ) := by
  have hdiv : (Φ.φ.natDegree * (p.1 : ℕ) + (p.2 : ℕ)) / Φ.φ.natDegree = (p.1 : ℕ) := by
    rw [Nat.mul_add_div hd, Nat.div_eq_of_lt p.2.isLt, Nat.add_zero]
  refine ⟨hdiv, ?_⟩
  have h := Nat.div_add_mod (Φ.φ.natDegree * (p.1 : ℕ) + (p.2 : ℕ)) Φ.φ.natDegree
  rw [show ((wTableIndex Φ m₀ b hμn p : Fin (2 ^ m₀)) : ℕ)
    = Φ.φ.natDegree * (p.1 : ℕ) + (p.2 : ℕ) from rfl, hdiv] at *
  omega

omit [NeZero q] [IsCyclotomic Φ] in
/-- Distinct block entries have distinct flat indices. -/
theorem wTableIndex_injective (b : ℕ) (hd : 0 < Φ.φ.natDegree)
    (hμn : (μ + n * rhoDigitCount q b) * Φ.φ.natDegree ≤ 2 ^ m₀) :
    Function.Injective (wTableIndex Φ m₀ b hμn) := by
  rintro ⟨u, l⟩ ⟨u', l'⟩ h
  obtain ⟨hu, hl⟩ := wTableIndex_div_mod Φ m₀ b hd hμn (u, l)
  obtain ⟨hu', hl'⟩ := wTableIndex_div_mod Φ m₀ b hd hμn (u', l')
  rw [h] at hu hl
  exact Prod.ext (Fin.ext (hu.symm.trans hu')) (Fin.ext (hl.symm.trans hl'))

omit [NeZero q] [IsCyclotomic Φ] [BEq F] [LawfulBEq F] in
/-- **The cube sum of the `α`-summand's public factor is Eq. (22)'s block contraction.** Summing
the committed table against `α̃` and `M̃_α` over the whole `m₀`-cube — which is what the sumcheck
does — equals `alphaContract`, which sums over the table block only. The terms outside the block
vanish because `M̃_α` does (`mAlphaTilde_eq_zero_of_ge`), and inside it the flat index is exactly
the block coordinate. -/
theorem sum_cube_alphaPublic (φF : ZMod q →+* F) (b : ℕ) (s : RlinStatement Φ n μ) (α : F)
    (w : LiftedWitness Φ μ n) (hd : 0 < Φ.φ.natDegree)
    (hμn : (μ + n * rhoDigitCount q b) * Φ.φ.natDegree ≤ 2 ^ m₀) (i : Fin n) :
    ∑ y : Fin m₀ → Fin 2,
        wTable Φ m₀ φF b w y *
          (alphaTilde α (((finFunctionFinEquiv y : Fin (2 ^ m₀)) : ℕ) % Φ.φ.natDegree) *
            mAlphaTilde Φ φF b s α i
              (((finFunctionFinEquiv y : Fin (2 ^ m₀)) : ℕ) / Φ.φ.natDegree))
      = alphaContract Φ m₀ φF b s α hμn (wTable Φ m₀ φF b w) i := by
  classical
  set g : Fin (2 ^ m₀) → F := fun k =>
    wTable Φ m₀ φF b w (finFunctionFinEquiv.symm k) *
      (alphaTilde α ((k : ℕ) % Φ.φ.natDegree) *
        mAlphaTilde Φ φF b s α i ((k : ℕ) / Φ.φ.natDegree)) with hgdef
  -- Reindex the cube by the flat index.
  have hre : ∑ y : Fin m₀ → Fin 2,
      wTable Φ m₀ φF b w y *
        (alphaTilde α (((finFunctionFinEquiv y : Fin (2 ^ m₀)) : ℕ) % Φ.φ.natDegree) *
          mAlphaTilde Φ φF b s α i
            (((finFunctionFinEquiv y : Fin (2 ^ m₀)) : ℕ) / Φ.φ.natDegree))
      = ∑ k : Fin (2 ^ m₀), g k := by
    refine (Equiv.sum_comp finFunctionFinEquiv.symm _).symm.trans ?_
    exact Finset.sum_congr rfl fun k _ => by simp [hgdef]
  rw [hre]
  -- Off the widened block the public matrix vanishes, so the cube sum is the block sum.
  have hzero : ∀ k ∈ (Finset.univ : Finset (Fin (2 ^ m₀))),
      k ∉ Finset.univ.image (wTableIndex Φ m₀ b hμn) → g k = 0 := by
    intro k _ hk
    have hrow : μ + n * rhoDigitCount q b ≤ (k : ℕ) / Φ.φ.natDegree := by
      by_contra hlt
      rw [Nat.not_le] at hlt
      refine hk (Finset.mem_image.mpr ⟨(⟨(k : ℕ) / Φ.φ.natDegree, hlt⟩,
        ⟨(k : ℕ) % Φ.φ.natDegree, Nat.mod_lt _ hd⟩), Finset.mem_univ _, ?_⟩)
      exact Fin.ext (Nat.div_add_mod _ _)
    rw [hgdef]
    simp only [mAlphaTilde_eq_zero_of_ge Φ φF b s α i hrow, mul_zero]
  rw [(Finset.sum_subset (Finset.subset_univ _) hzero).symm,
    Finset.sum_image fun p _ p' _ h => wTableIndex_injective Φ m₀ b hd hμn h,
    alphaContract, ← Finset.univ_product_univ, Finset.sum_product]
  refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun ℓ _ => ?_
  obtain ⟨hu, hl⟩ := wTableIndex_div_mod Φ m₀ b hd hμn (u, ℓ)
  rw [hgdef]
  simp only [hu, hl, ← wTablePoint_eq_symm_wTableIndex]
  ring

omit [NeZero q] [IsCyclotomic Φ] [BEq F] [LawfulBEq F] in
/-- **Row-indexed cube sums.** An `eq̃(τ₁, ·)`-weighted sum over the `m₁`-batching cube of a table
supported on the rows `< n` equals the row-indexed sum that `zcTargetAlpha` and `alphaPublicEvals`
are written with.

Both sides silently drop the same rows — on the left the cube's padding rows `≥ n`, on the right
the rows `≥ 2 ^ m₁` that the cube cannot encode — so the two supports agree and **no `n ≤ 2 ^ m₁`
hypothesis is needed**, even though the row encoding `rowPoint` requires one. -/
theorem sum_cube_rowIndexed (τ₁ : Fin m₁ → F) (f : Fin n → F) :
    ∑ z : Fin m₁ → Fin 2,
        (if h : ((finFunctionFinEquiv z : Fin (2 ^ m₁)) : ℕ) < n then f ⟨_, h⟩ else 0) *
          ∏ j : Fin m₁, (if z j = 1 then τ₁ j else 1 - τ₁ j)
      = ∑ i : Fin n, (if hi : (i : ℕ) < 2 ^ m₁ then
          (∏ j : Fin m₁,
            if (finFunctionFinEquiv.symm ⟨(i : ℕ), hi⟩) j = 1 then τ₁ j else 1 - τ₁ j) * f i
        else 0) := by
  classical
  rw [← Equiv.sum_comp finFunctionFinEquiv.symm
    (fun z : Fin m₁ → Fin 2 =>
      (if h : ((finFunctionFinEquiv z : Fin (2 ^ m₁)) : ℕ) < n then f ⟨_, h⟩ else 0) *
        ∏ j : Fin m₁, (if z j = 1 then τ₁ j else 1 - τ₁ j))]
  simp only [Equiv.apply_symm_apply]
  -- Restrict both sides to their supports, then match them row by row.
  rw [← Finset.sum_subset (Finset.subset_univ
        (Finset.univ.filter (fun k : Fin (2 ^ m₁) => (k : ℕ) < n)))
      (fun k _ hk => by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
        rw [dif_neg hk, zero_mul]),
    ← Finset.sum_subset (Finset.subset_univ
        (Finset.univ.filter (fun i : Fin n => (i : ℕ) < 2 ^ m₁)))
      (fun i _ hi => by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
        rw [dif_neg hi])]
  refine Finset.sum_bij'
    (fun k hk => (⟨(k : ℕ), by simpa using hk⟩ : Fin n))
    (fun i hi => (⟨(i : ℕ), by simpa using hi⟩ : Fin (2 ^ m₁)))
    (fun k hk => by simp) (fun i hi => by simp)
    (fun _ _ => rfl) (fun _ _ => rfl) ?_
  intro k hk
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
  rw [dif_pos hk, dif_pos k.isLt, mul_comm]

omit [NeZero q] in
omit [NeZero q] in
/-- **The full-cube sum of the linear summand `F_{α,τ₁}` equals `H_α(τ₁) + zcTargetAlpha`.**

The two hypotheses are the ones that make the table encoding faithful, and both are already
carried by the composition (`Composition.iteration`'s `hd` and `hcov`): `hd` is what lets the
flat cube index be split as `(row, column)`, and `hμn` is what makes every coefficient position a
genuine cube point. Without them the cube contraction of `M̃_α`, `w̃` and `α̃` does **not**
reproduce the ring-level row defect that `H_α` stores — the block would overflow the cube — so
the identity is false as stated without them, not merely unprovable. -/
theorem sum_sumcheckPolyAlpha (φF : ZMod q →+* F) (b : ℕ) (hb : 1 < b) (s : RlinStatement Φ n μ)
    (α : F) (τ₁ : Fin m₁ → F) (w : LiftedWitness Φ μ n) (hd : 0 < Φ.φ.natDegree)
    (hμn : (μ + n * rhoDigitCount q b) * Φ.φ.natDegree ≤ 2 ^ m₀) :
    hypercubeSum m₀ (sumcheckPolyAlpha Φ m₀ m₁ φF b s α τ₁ w) 0 (fun j => j.elim0) =
      MvPolynomial.eval τ₁ (hAlphaML Φ m₁ φF b s α w).val +
        zcTargetAlpha Φ m₁ φF s α τ₁ := by
  classical
  -- The left side: evaluate both multilinear extensions at every Boolean point, then exchange
  -- the cube sum with the row sum hidden inside `alphaPublicEvals`.
  have hL : hypercubeSum m₀ (sumcheckPolyAlpha Φ m₀ m₁ φF b s α τ₁ w) 0 (fun j => j.elim0)
      = ∑ i : Fin n, (if hi : (i : ℕ) < 2 ^ m₁ then
          (∏ j : Fin m₁,
            if (finFunctionFinEquiv.symm ⟨(i : ℕ), hi⟩) j = 1 then τ₁ j else 1 - τ₁ j) *
              alphaContract Φ m₀ φF b s α hμn (wTable Φ m₀ φF b w) i
        else 0) := by
    rw [hypercubeSum_zero]
    have hpt : ∀ y : Fin m₀ → Fin 2,
        (sumcheckPolyAlpha Φ m₀ m₁ φF b s α τ₁ w).eval ((y : Fin m₀ → F))
          = ∑ i : Fin n, wTable Φ m₀ φF b w y *
              (alphaTilde α (((finFunctionFinEquiv y : Fin (2 ^ m₀)) : ℕ) % Φ.φ.natDegree) *
                (if hi : (i : ℕ) < 2 ^ m₁ then
                  (∏ j : Fin m₁,
                    if (finFunctionFinEquiv.symm ⟨(i : ℕ), hi⟩) j = 1 then τ₁ j else 1 - τ₁ j) *
                      mAlphaTilde Φ φF b s α i
                        (((finFunctionFinEquiv y : Fin (2 ^ m₀)) : ℕ) / Φ.φ.natDegree)
                else 0)) := by
      intro y
      rw [sumcheckPolyAlpha, CPoly.eval_mul, cMultilinearExtension_eval_boolean,
        cMultilinearExtension_eval_boolean, alphaPublicEvals, Finset.mul_sum, Finset.mul_sum]
    rw [Finset.sum_congr rfl fun y _ => hpt y, Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases hi : (i : ℕ) < 2 ^ m₁
    · rw [dif_pos hi, ← sum_cube_alphaPublic Φ m₀ φF b s α w hd hμn i, Finset.mul_sum]
      exact Finset.sum_congr rfl fun y _ => by rw [dif_pos hi]; ring
    · rw [dif_neg hi]
      exact Finset.sum_eq_zero fun y _ => by rw [dif_neg hi]; ring
  -- The right side: the `H_α` cube sum and `zcTargetAlpha` are two row-indexed sums, and the
  -- row-level defect plus `yᵢ(α)` is exactly Eq. (22)'s contraction — now with the quotient term
  -- in its digit-recombined form.
  rw [hL]
  simp only [hAlphaML, eval_MLE_eq_sum, hAlphaEvals, zcTargetAlpha]
  rw [sum_cube_rowIndexed m₁ τ₁ (fun i => cEvalAt φF α (cRowSum Φ s w.z i)
      - cEvalAt φF α (s.yvec i).1 - cEvalAt φF α Φ.φ *
        ∑ u : Fin (rhoDigitCount q b), φF ((b : ZMod q) ^ (u : ℕ))
          * evalAt φF α (rhoDigits Φ b (w.ρ i) (u : ℕ)).toPoly),
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hi : (i : ℕ) < 2 ^ m₁
  · rw [dif_pos hi, dif_pos hi, dif_pos hi, ← mul_add]
    congr 1
    have hdef := alphaDefect_wTable Φ m₀ φF b hb s α w hd hμn i
    rw [alphaDefect, rhoDigits_evalAt Φ φF α hb hd (w.ρ i) (w.hρ i)] at hdef
    linear_combination hdef
  · rw [dif_neg hi, dif_neg hi, dif_neg hi, add_zero]

/-! ### Evaluation at a point: the final-evaluation factorizations

The sum identities above are what the *bridge* needs (row 7): the full-cube sums of the summands
are the zero-check's point claims. The final-evaluation step (row 9, [NOZ26] Figure 7 tail) needs
the opposite reading of the same two polynomials: once the sumcheck has consumed every cube
coordinate, each summand is a plain evaluation at the challenge point, and it **factors into a
public factor times a function of `mle[w̃]` alone**. That is what lets the verifier check the last
two targets against the single claimed value `y′` — the formal content of "the verifier does not
need to perform any multiplication over `R_q`" (§4.4): neither factor below mentions the
witness except through `wTableMleEval`. -/

omit [NeZero q] [IsCyclotomic Φ] in
/-- **Evaluation factorization of the range summand**:
`F_{0,τ₀}(a) = eq̃(τ₀, a) · P_b(mle[w̃](a))`. The left factor is public; the right depends on the
witness only through the claimed evaluation. -/
theorem eval_sumcheckPolyZero (φF : ZMod q →+* F) (b : ℕ) (τ₀ : Fin m₀ → F)
    (w : LiftedWitness Φ μ n) (a : Fin m₀ → F) :
    (sumcheckPolyZero Φ m₀ φF b τ₀ w).eval a =
      (cEqualityPolynomial m₀ τ₀).eval a * rangeProduct b (wTableMleEval Φ m₀ φF b w a) := by
  rw [sumcheckPolyZero, CPoly.eval_mul, cRangeProduct_eval, cMultilinearExtension_eval,
    wTableMleEval_eq]

omit [NeZero q] [IsCyclotomic Φ] in
/-- **Evaluation factorization of the linear summand**:
`F_{α,τ₁}(a) = mle[w̃](a) · Ã(a)`, where `Ã` is the multilinear extension of the public table
`alphaPublicEvals` — the paper's `∑ᵢ eq̃(τ₁,i)·M̃_α(i,·)·α̃`, whose evaluation at the sumcheck
point is the verifier's one expensive step (`Õ(√(2^ℓ)·λ)` by dynamic programming, §4.4). -/
theorem eval_sumcheckPolyAlpha (φF : ZMod q →+* F) (b : ℕ) (s : RlinStatement Φ n μ) (α : F)
    (τ₁ : Fin m₁ → F) (w : LiftedWitness Φ μ n) (a : Fin m₀ → F) :
    (sumcheckPolyAlpha Φ m₀ m₁ φF b s α τ₁ w).eval a =
      wTableMleEval Φ m₀ φF b w a *
        (cMultilinearExtension m₀ (alphaPublicEvals Φ m₀ m₁ φF b s α τ₁)).eval a := by
  rw [sumcheckPolyAlpha, CPoly.eval_mul, wTableMleEval_eq, cMultilinearExtension_eval]

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

variable (bound bDig : ℕ)

/-- Paired-sumcheck relation over direct zero-check points: an opening of `t` whose partial
hypercube sums match the current targets.

Both summands read the scalar-round challenges directly, with no derived evaluation-point encoding
(no curve, no seed expansion). The `liftShort` conjunct is the commitment's shortness index: it is
what makes a pair of colliding branch openings a member of `LiftCom.Collision`, hence a
Module-SIS break, at the escape event of the sumcheck rounds. Its `RhoShort` half — the range
claim Lemma 10 exists to prove — is still *derived* from `H₀ ≡ 0`
(`hZero_eq_zero_imp_liftShort`), never assumed. -/
def nestedRoundRel (K : LiftCom (LiftedWitness Φ μ n) (liftShort Φ bound bDig))
    (φF : ZMod q →+* F) (b : ℕ) (i : ℕ) :
    Set (NestedRoundStatement Φ K.TCom F n μ m₀ m₁ i × LiftedWitness Φ μ n) :=
  {p |
    K.com p.2 = p.1.zc.t ∧
    liftShort Φ bound bDig p.2 ∧
    hypercubeSum m₀ (sumcheckPolyZero Φ m₀ φF b p.1.zc.τ₀ p.2) i
        p.1.challenges = p.1.target₀ ∧
    hypercubeSum m₀
        (sumcheckPolyAlpha Φ m₀ m₁ φF b p.1.zc.rlin p.1.zc.α p.1.zc.τα p.2) i
        p.1.challenges = p.1.targetα ∧
    bound ≤ p.1.zc.rlin.bound}

end ArkLib.Lattices.Ajtai.InnerOuter

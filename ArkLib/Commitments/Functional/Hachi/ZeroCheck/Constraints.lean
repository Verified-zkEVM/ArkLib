/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tobias Rothmann
-/
import ArkLib.Commitments.Functional.Hachi.RingSwitch.Reduction
import CompPoly.Multilinear.Basic
import Mathlib.Algebra.MvPolynomial.Basic

/-!
  # Constraint encoding — Hachi Eqs. (21)–(23) — skeleton

  Definitions only (no protocol): the shared constraint-encoding layer consumed by the batching
  bridge, the zero-check, the sumcheck rounds, and the final-evaluation step.

  ## The table `w̃` (Eq. (21))

  The committed lifted witness `(z, ρ)` is re-read as a `Zq`-valued table `w̃` indexed by the
  `m₀`-cube: rows are the `Zq`-coefficient vectors of the `zⱼ ∈ Rq` followed by the base-`b`
  gadget digits of the quotients `ρᵢ`, columns are the `d` coefficient positions. **Arity pin**:
  `2 ^ m₀` = (number of `z`-rows + number of `ρ`-digit rows) · `d`, padded to a power of
  two; the paper's `τ₀ ← F^{log μ + log d}` undercounts its own index space `[μ+n] × [d]` — the
  formalization fixes `m₀` as *the table's* log-size and `m₁` as the row-batching arity
  (`2 ^ m₁ ≥ n` rows of the lifted system). Little-endian cube indexing throughout
  (`CMlPolynomial`/`EvalSplit` convention).

  ## The batched constraint polynomials (Eqs. (22)–(23))

  * `hAlpha` (Eq. (22)): the `eq̃`-batched *linear* constraint polynomial
    `H_α(τ) := ∑ᵢ eq̃(τ, i)·(∑_{u,ℓ} M̃_α(i,u)·w̃(u,ℓ)·α̃(ℓ) − ŷᵢ(α))`, multilinear in `m₁`
    variables; `H_α ≡ 0` iff every lifted row vanishes at `α`.
  * `hZero` (Eq. (23)): the `eq̃`-batched *range* polynomial
    `H₀(τ) := ∑_{u,ℓ} eq̃(τ, (u,ℓ))·w̃(u,ℓ)·∏_{j=1}^{b−1}(w̃(u,ℓ) − j)(w̃(u,ℓ) + j)`,
    multilinear in `m₀` variables; `H₀ ≡ 0` iff every table entry lies in `[−(b−1), b−1]`
    (needs `2b − 1 < q` to read field-roots as centered representatives).

  ## The sumcheck polynomials and degree pins

  `F_{0,τ₀} := eq̃(τ₀,·)·(range product)(w̃(·))` has per-variable degree `2b` (range product
  `2b − 1` on the multilinear `w̃`, times the multilinear `eq̃`) — hence `k = 2b + 1` transcripts
  per round; `F_{α,τ₁} := w̃(·)·α̃(·)·(∑ᵢ eq̃(τ₁,i)·M̃_α(i,·))` has per-variable degree `≤ 2`.
  The repo docstring's `2b+1` round degree and the paper's `b+1` coefficient count are both
  off against the printed product — everything downstream is degree-parametric
  (`roundDegZero`/`roundDegAlpha`), so the pin is a one-line change if a convention shifts.

  ## The Kronecker point (Lemma 10 repair)

  `kroneckerPoint m ρ = (ρ, ρ², ρ⁴, …, ρ^{2^{m−1}})`: the pullback of an `m`-variate multilinear
  polynomial along this curve is univariate of degree `< 2^m` and the pullback is **injective**
  (binary expansion of exponents), so univariate root counting is information-complete — the
  engine of the corrected zero-check (`ZeroCheck/Reduction.lean`).

  Everything protocol-shaped built on these defs lives in the subsequent files; the defs here are
  **sorried** (their content is index bookkeeping over the conventions plus `eqPolynomial`/
  `LinearMvExtension` algebra), with their characterizing lemmas stated sorried alongside.

  ## References

  * [Nguyen, N. K., O'Rourke, G., and Zhang, J., *Hachi: Efficient Lattice-Based Multilinear
      Polynomial Commitments over Extension Fields*][NOZ26]
-/

namespace ArkLib.Lattices.Ajtai.InnerOuter

open CompPoly ArkLib.Lattices.CyclotomicModulus
open OracleComp OracleSpec ProtocolSpec CoordinateWise

variable {q : ℕ} [NeZero q] [Fact (Nat.Prime q)] [BEq (ZMod q)] [LawfulBEq (ZMod q)]
  (Φ : CyclotomicModulus (ZMod q)) [IsCyclotomic Φ]
variable {n μ : ℕ} {E : Type} {F : Type} [Field F]
variable (m₀ m₁ : ℕ)

/-! ## The Kronecker curve (real definitions) -/

/-- **The Kronecker point** `κ_m(ρ) := (ρ, ρ², ρ⁴, …, ρ^{2^{m−1}})` — the corrected Lemma 10's
challenge-derivation curve. Computable by repeated squaring. -/
def kroneckerPoint (m : ℕ) (ρ : F) : Fin m → F :=
  fun j => ρ ^ (2 ^ (j : ℕ))

/-- Per-round univariate degree of the range sumcheck (`F_{0,τ₀}`): the `2b − 1`-factor range
product over the multilinear `w̃`, times the multilinear `eq̃` — degree `2b`. -/
def roundDegZero (b : ℕ) : ℕ := 2 * b

/-- Per-round univariate degree of the linear sumcheck (`F_{α,τ₁}`): `w̃ · α̃ · (∑ eq̃·M̃_α)` —
at most two multilinear factors per variable, degree `≤ 2`. -/
def roundDegAlpha : ℕ := 2

/-! ## The range factor -/

/-- Hachi Eq. (23)'s per-entry **range factor** `P_b(v) = v·∏_{j=1}^{b−1} (v − j)·(v + j)`, the
vanishing polynomial of the symmetric range `{−(b−1), …, b−1}`. Its multilinear extension over
the table entries is `H₀`. -/
def rangeProduct (b : ℕ) (v : F) : F :=
  v * ∏ j ∈ Finset.Icc 1 (b - 1), ((v - (j : F)) * (v + (j : F)))

/-- Over a field, `P_b(v) = 0` iff `v` is the image of an integer in the symmetric range
`{−(b−1), …, b−1}`. The engine of the `H₀ ⇒ liftShort` bridge (the corrected [NOZ26, Lemma 10]
reads the field roots back as centered representatives under `2b − 1 < q`). **Sorried**
(skeleton). -/
theorem rangeProduct_eq_zero_iff {b : ℕ} {v : F} :
    rangeProduct b v = 0 ↔ ∃ j : ℕ, j ≤ b - 1 ∧ (v = (j : F) ∨ v = -(j : F)) := by
  sorry

/-! ## The table (Eq. (21)) -/

/-- **The Eq. (21) table** `w̃`: the committed pair `(z, ρ)` re-read as an `F`-valued function on
the `m₀`-cube, indexed by the little-endian flat index `idx : Fin (2 ^ m₀)`. Splitting
`row := idx / d` and `column := idx % d` (`d = deg Φ.φ`): rows `< μ` return the `Zq`-coefficients
of the witness entries `zⱼ ∈ Rq`, rows `μ ≤ · < μ + n` return the coefficients of the quotients
`ρᵢ`, both mapped through `φF`, and all remaining indices return zero.

The coefficients are read **directly** (the ρ-direct model), so `H₀` constrains the committed
data itself: `H₀ ≡ 0` says every committed coefficient lies in `[−(b−1), b−1]`. These are exactly
the Boolean-hypercube values (Lagrange coefficients) of the `CMlPolynomialEval` `H₀`. **Sorried**
(skeleton); the concrete encoding is supplied when the corrected [NOZ26, Lemma 10] is
discharged. -/
noncomputable def wTable (φF : ZMod q →+* F) (_b : ℕ) (w : LiftedWitness Φ μ n) :
    Fin (2 ^ m₀) → F :=
  sorry

/-- Evaluation of the multilinear extension of the table `w̃` at a point `a ∈ F^{m₀}` (through
the embedding `φF`): `mle[w̃](a) = ∑ᵢ w̃(i)·eq̃(i, a)`. The evaluation claim carried into the
final-evaluation step (`Sumcheck/FinalEval.lean`). **Sorried.** -/
noncomputable def wTableMleEval (φF : ZMod q →+* F) (b : ℕ) (w : LiftedWitness Φ μ n)
    (a : Fin m₀ → F) : F :=
  sorry

/-! ## Row encoding and the linear-constraint coefficients -/

/-- The little-endian flat index `Fin (2 ^ m₁)` that encodes row `i : Fin n` (needs `n ≤ 2 ^ m₁`)
as a Boolean-hypercube vertex of the batching cube: literally `i` cast into `Fin (2 ^ m₁)`.
Indices `≥ n` are the zero-padding of the batching cube. -/
def rowPoint (hn : n ≤ 2 ^ m₁) (i : Fin n) : Fin (2 ^ m₁) :=
  ⟨(i : ℕ), lt_of_lt_of_le i.isLt hn⟩

/-- The Boolean-hypercube values of `H_α` (Eq. (22)): the `M̃_α`-contracted per-row value
`i ↦ (∑_{u,ℓ} M̃_α(i,u)·w̃(u,ℓ)·α̃(ℓ)) − ŷᵢ(α)`, indexed by the flat index `Fin (2 ^ m₁)` via
`rowPoint` and zero-padded on rows `≥ n`. These are the Lagrange coefficients of the
`CMlPolynomialEval` `H_α`. The per-row equation of `relLift` (Fig. 4) is recovered via
`hAlphaEvals_rowPoint`. **Sorried.** -/
noncomputable def hAlphaEvals (φF : ZMod q →+* F) (_b : ℕ) (s : RlinStatement Φ n μ) (α : F)
    (w : LiftedWitness Φ μ n) : Fin (2 ^ m₁) → F :=
  sorry

/-- At the row index `rowPoint i`, the value `hAlphaEvals` equals row `i`'s `α`-evaluated lift
defect, stated against `relLift`'s per-row equation as packaged by `liftCheckAt`
(`Lift.checkAt` at `cyclotomicPresentation Φ`): the left-hand side `rowSum(α)` minus the
right-hand side `rep(yᵢ)(α) + Φ.φ(α)·ρᵢ(α)`. This is what links `H_α ≡ 0` (its `CMlPolynomialEval`
value vector being zero) to the per-row constraints of `relLift` in the batching bridge.
**Sorried.** -/
theorem hAlphaEvals_rowPoint (φF : ZMod q →+* F) (b : ℕ) (s : RlinStatement Φ n μ) (α : F)
    (w : LiftedWitness Φ μ n) (hn : n ≤ 2 ^ m₁) (i : Fin n) :
    hAlphaEvals Φ m₁ φF b s α w (rowPoint m₁ hn i) =
      RingSwitching.evalAt φF α ((cyclotomicPresentation Φ).rowSum s.M w.z i)
        - RingSwitching.evalAt φF α ((cyclotomicPresentation Φ).rep (s.yvec i))
        - RingSwitching.evalAt φF α (cyclotomicPresentation Φ).modulus
            * RingSwitching.evalAt φF α (w.ρ i) := by
  sorry

/-! ## The batched constraint polynomials (Eqs. (22)–(23)) -/

/-- **Eq. (23)**: the `eq̃`-batched range polynomial
`H₀(τ) := ∑ᵢ eq̃(τ, i)·w̃(i)·∏_{j=1}^{b−1}(w̃(i) − j)(w̃(i) + j)`, the multilinear extension of
the per-entry range factor `rangeProduct b (w̃(·))` — a `CMlPolynomial` in eval (Lagrange) form,
whose value vector is `rangeProduct b ∘ wTable`. `H₀ = 0` iff every table entry is a root of the
range product, i.e. lies in `[−(b−1), b−1]` (under `2b − 1 < q`). Multilinearity is structural
(the representation is a length-`2 ^ m₀` coefficient vector). **Sorried.** -/
noncomputable def hZero (φF : ZMod q →+* F) (b : ℕ) (w : LiftedWitness Φ μ n) :
    CMlPolynomialEval F m₀ :=
  sorry

/-- **Eq. (22)**: the `eq̃`-batched linear constraint polynomial
`H_α(τ) := ∑ᵢ eq̃(τ, i)·(∑_u M̃_α(i,u)·(∑_ℓ w̃(u,ℓ)·α̃(ℓ)) − ŷᵢ(α))`, the multilinear extension of
the `M̃_α`-contracted per-row values `hAlphaEvals` — a `CMlPolynomial` in eval (Lagrange) form,
whose value vector is `hAlphaEvals`. `H_α = 0` iff every lifted row of `relLift` vanishes at `α`.
Multilinearity is structural. **Sorried.** -/
noncomputable def hAlpha (φF : ZMod q →+* F) (b : ℕ) (s : RlinStatement Φ n μ) (α : F)
    (w : LiftedWitness Φ μ n) : CMlPolynomialEval F m₁ :=
  sorry

/-! ## The sumcheck polynomials (sorried content)

**TODO (reuse `Sumcheck/Structured`):** `sumcheckPolyZero`/`sumcheckPolyAlpha` should be defined as
`Sumcheck.Structured.computeRoundPoly` instances rather than from scratch — `F_α` via the identity
combinator (degree 2), `F_{0,τ₀}` via the range combinator `∏ⱼ (X − j)` of degree `2b` (the
`SumcheckMultiplierParam` docstring anticipates this Hachi case) — and the round consistency
(`hypercubeSum` / `roundRel`) via `Sumcheck.Structured.sumcheckConsistencyProp` over
`SumcheckDomain.boolDomain`. See the `Sumcheck.lean` umbrella. -/

/-- **`F_{0,τ₀}`** (the range sumcheck summand, [NOZ26] §4.3 "finish the proof using sumcheck"):
`F_{0,τ₀}(x) := eq̃(τ₀, x)·w̃(x)·∏_{j=1}^{b−1}(w̃(x) − j)(w̃(x) + j)·1_{table}(x)`, where `w̃` is
read through its multilinear extension. Satisfies `∑_{x ∈ {0,1}^{m₀}} F_{0,τ₀}(x) = H₀(τ₀)`
(`sum_sumcheckPolyZero`). Per-variable degree `roundDegZero b = 2b`. **Sorried.** -/
def sumcheckPolyZero (φF : ZMod q →+* F) (b : ℕ) (τ₀ : Fin m₀ → F)
    (w : LiftedWitness Φ μ n) : MvPolynomial (Fin m₀) F :=
  sorry

/-- **`F_{α,τ₁}`** (the linear sumcheck summand):
`F_{α,τ₁}(x) := w̃(x)·α̃(x)·(∑ᵢ eq̃(τ₁, i)·M̃_α(i, x))`. Satisfies
`∑_{x ∈ {0,1}^{m₀}} F_{α,τ₁}(x) = H_α(τ₁) + zcTargetAlpha` (`sum_sumcheckPolyAlpha`).
Per-variable degree `roundDegAlpha = 2`. **Sorried.** -/
def sumcheckPolyAlpha (φF : ZMod q →+* F) (b : ℕ) (s : RlinStatement Φ n μ) (a : F)
    (τ₁ : Fin m₁ → F) (w : LiftedWitness Φ μ n) : MvPolynomial (Fin m₀) F :=
  sorry

/-- The public initial target of the linear sumcheck: `a := ∑ᵢ eq̃(τ₁, i)·ŷᵢ(α)` — computable
by the verifier from the statement alone ([NOZ26] §4.3). **Sorried.** -/
def zcTargetAlpha (φF : ZMod q →+* F) (s : RlinStatement Φ n μ) (a : F)
    (τ₁ : Fin m₁ → F) : F :=
  sorry

/-- Partial hypercube sum: `hypercubeSum H i cs = ∑_{x ∈ {0,1}^{m₀ − i}} H(cs, x)` — the claim
currency of the `i`-th sumcheck round (round `0` is the full sum; round `m₀` is the point
evaluation `H(cs)`). **Sorried.** -/
def hypercubeSum (H : MvPolynomial (Fin m₀) F) (i : ℕ) (cs : Fin i → F) : F :=
  sorry

/-- The sum of `F_{0,τ₀}` over the cube is `H₀(τ₀)` — the algebraic identity behind the
sumcheck bridge (`Sumcheck/Bridge.lean`). **Sorried.** -/
theorem sum_sumcheckPolyZero (φF : ZMod q →+* F) (b : ℕ) (τ₀ : Fin m₀ → F)
    (w : LiftedWitness Φ μ n) :
    hypercubeSum m₀ (sumcheckPolyZero Φ m₀ φF b τ₀ w) 0 (fun j => j.elim0) =
      CMlPolynomialEval.eval (hZero Φ m₀ φF b w) (Vector.ofFn τ₀) := by
  sorry

/-- The sum of `F_{α,τ₁}` over the cube is `H_α(τ₁) + zcTargetAlpha` — the algebraic identity
behind the sumcheck bridge. **Sorried.** -/
theorem sum_sumcheckPolyAlpha (φF : ZMod q →+* F) (b : ℕ) (s : RlinStatement Φ n μ) (a : F)
    (τ₁ : Fin m₁ → F) (w : LiftedWitness Φ μ n) :
    hypercubeSum m₀ (sumcheckPolyAlpha Φ m₀ m₁ φF b s a τ₁ w) 0 (fun j => j.elim0) =
      CMlPolynomialEval.eval (hAlpha Φ m₁ φF b s a w) (Vector.ofFn τ₁)
        + zcTargetAlpha Φ m₁ φF s a τ₁ := by
  sorry

/-! ## Statement types of the zero-check and sumcheck stages -/

/-- The zero-check's output statement: the lift statement extended by the two **Kronecker
seeds** `(ρ₀, ρ_α)` of the corrected Lemma 10 (the challenge is
the seed pair; the batching points `τ₀ := κ_{m₀}(ρ₀)`, `τ_α := κ_{m₁}(ρ_α)` are derived
deterministically). -/
structure ZeroCheckStatement (Φ : CyclotomicModulus (ZMod q)) (TCom F : Type) (n μ : ℕ) where
  /-- The `R^lin` statement (carrying the public `M`, `yvec`, `bound`). -/
  rlin : RlinStatement Φ n μ
  /-- The `w̃`-commitment from the lift stage. -/
  t : TCom
  /-- The HMZ25 evaluation challenge `α` from the lift stage. -/
  α : F
  /-- The Kronecker seed `ρ₀` of the range zero-check. -/
  seed₀ : F
  /-- The Kronecker seed `ρ_α` of the linear zero-check. -/
  seedα : F

/-- The statement after `i` (paired) sumcheck rounds: the zero-check statement, the challenges
`a₁, …, aᵢ` so far, and the current pair of sumcheck targets `(z_i^{(0)}, z_i^{(α)})`
([NOZ26] Figure 6's `z_{i−1} ↦ z_i := g_i(a_i)`, for both parallel sumchecks). -/
structure RoundStatement (Φ : CyclotomicModulus (ZMod q)) (TCom F : Type) (n μ : ℕ)
    (i : ℕ) where
  /-- The zero-check statement (public data, commitment, `α`, Kronecker seeds). -/
  zc : ZeroCheckStatement Φ TCom F n μ
  /-- The sumcheck challenges so far. -/
  challenges : Fin i → F
  /-- The current target of the range sumcheck. -/
  target₀ : F
  /-- The current target of the linear sumcheck. -/
  targetα : F

variable (bound ρBound : ℕ)

/-- **The per-round seam relation** of the paired sumcheck (the CWSS currency of [NOZ26]
Lemma 11): `w̃` opens `t`, is short (`liftShort`, the shortness precondition of the commitment's
weak binding `LiftCom.collision_mem` used by each round's collision extractor), and both
partial-hypercube-sum claims at the current challenge prefix equal the current targets. Round `0`
(full sums) is produced by the sumcheck bridge; round `m₀` (point evaluations) is consumed by the
final-evaluation step. The public sanity conjunct `bound ≤ rlin.bound` threads the global norm
parameter back to the `R^lin` statement bound (it originates in `relLift`, is preserved by every
intermediate extraction since the statement components are shared, and is re-supplied at the
final-evaluation step by its runtime guard). -/
def roundRel (K : LiftCom (LiftedWitness Φ μ n) E (liftShort Φ bound ρBound))
    (φF : ZMod q →+* F) (b : ℕ) (i : ℕ) :
    Set (RoundStatement Φ K.TCom F n μ i × LiftedWitness Φ μ n) :=
  {p |
    K.com p.2 = p.1.zc.t ∧
    liftShort Φ bound ρBound p.2 ∧
    hypercubeSum m₀ (sumcheckPolyZero Φ m₀ φF b (kroneckerPoint m₀ p.1.zc.seed₀) p.2) i
        p.1.challenges = p.1.target₀ ∧
    hypercubeSum m₀
        (sumcheckPolyAlpha Φ m₀ m₁ φF b p.1.zc.rlin p.1.zc.α (kroneckerPoint m₁ p.1.zc.seedα)
          p.2) i p.1.challenges = p.1.targetα ∧
    bound ≤ p.1.zc.rlin.bound}

/-- Escape-threaded per-round seam relation. -/
def roundRelE (K : LiftCom (LiftedWitness Φ μ n) E (liftShort Φ bound ρBound))
    (φF : ZMod q →+* F) (b : ℕ) (i : ℕ) :
    Set (RoundStatement Φ K.TCom F n μ i × (LiftedWitness Φ μ n ⊕ E)) :=
  (roundRel Φ m₀ m₁ bound ρBound K φF b i).withEscape K.esc

end ArkLib.Lattices.Ajtai.InnerOuter

/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tobias Rothmann
-/
import ArkLib.Commitments.Functional.Hachi.RingSwitch.Reduction
import Mathlib.Algebra.MvPolynomial.Basic

/-!
  # Constraint encoding — Hachi Eqs. (21)–(23) — skeleton (sumcheck-track milestone F5)

  Definitions only (no protocol): the shared constraint-encoding layer consumed by the batching
  bridge, the zero-check, the sumcheck rounds, and the final-evaluation step.

  ## The table `w̃` (Eq. (21))

  The committed lifted witness `(z, ρ)` is re-read as a `Zq`-valued table `w̃` indexed by the
  `m₀`-cube: rows are the `Zq`-coefficient vectors of the `zⱼ ∈ Rq` followed by the base-`b`
  gadget digits of the quotients `ρᵢ`, columns are the `d` coefficient positions. **Arity pin
  (F5)**: `2 ^ m₀` = (number of `z`-rows + number of `ρ`-digit rows) · `d`, padded to a power of
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

  ## The sumcheck polynomials and degree pins (design R8)

  `F_{0,τ₀} := eq̃(τ₀,·)·(range product)(w̃(·))` has per-variable degree `2b` (range product
  `2b − 1` on the multilinear `w̃`, times the multilinear `eq̃`) — hence `k = 2b + 1` transcripts
  per round; `F_{α,τ₁} := w̃(·)·α̃(·)·(∑ᵢ eq̃(τ₁,i)·M̃_α(i,·))` has per-variable degree `≤ 2`.
  The repo docstring's `2b+1` round degree and the paper's `b+1` coefficient count are both
  off against the printed product — everything downstream is degree-parametric
  (`roundDegZero`/`roundDegAlpha`), so the pin is a one-line change if a convention shifts.

  ## The Kronecker point (Lemma 10 repair, `HACHI_LEMMA10_GAP.md`)

  `kroneckerPoint m ρ = (ρ, ρ², ρ⁴, …, ρ^{2^{m−1}})`: the pullback of an `m`-variate multilinear
  polynomial along this curve is univariate of degree `< 2^m` and the pullback is **injective**
  (binary expansion of exponents), so univariate root counting is information-complete — the
  engine of the corrected zero-check (`ZeroCheck/Reduction.lean`).

  Everything protocol-shaped built on these defs lives in the subsequent files; the defs here are
  **sorried** (their content is index bookkeeping over the F2.1 conventions plus `eqPolynomial`/
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
challenge-derivation curve (`HACHI_LEMMA10_GAP.md` §3.K). Computable by repeated squaring. -/
def kroneckerPoint (m : ℕ) (ρ : F) : Fin m → F :=
  fun j => ρ ^ (2 ^ (j : ℕ))

/-- Per-round univariate degree of the range sumcheck (`F_{0,τ₀}`): the `2b − 1`-factor range
product over the multilinear `w̃`, times the multilinear `eq̃` — degree `2b` (pin R8). -/
def roundDegZero (b : ℕ) : ℕ := 2 * b

/-- Per-round univariate degree of the linear sumcheck (`F_{α,τ₁}`): `w̃ · α̃ · (∑ eq̃·M̃_α)` —
at most two multilinear factors per variable, degree `≤ 2` (pin R8). -/
def roundDegAlpha : ℕ := 2

/-! ## The table and the batched constraint polynomials (sorried F5 content) -/

/-- **The Eq. (21) table**: the committed `(z, ρ)` re-read as a `Zq`-valued function on the
`m₀`-cube — `Zq`-coefficient rows of the `zⱼ`, then base-`b` gadget-digit rows of the `ρᵢ`,
zero-padded to `2 ^ m₀`. **Sorried (F5)**: index bookkeeping over the F2.1 conventions plus the
`ρ`-digit decomposition (F3.4). -/
def wTable (b : ℕ) (w : LiftedWitness Φ μ n) : Fin (2 ^ m₀) → ZMod q :=
  sorry

/-- Evaluation of the multilinear extension of the table `w̃` at a point `a ∈ F^{m₀}` (through
the embedding `φF`): `mle[w̃](a) = ∑ᵢ w̃(i)·eq̃(i, a)`. **Sorried (F5).** -/
def wTableMleEval (φF : ZMod q →+* F) (b : ℕ) (w : LiftedWitness Φ μ n)
    (a : Fin m₀ → F) : F :=
  sorry

/-- **Eq. (23)**: the `eq̃`-batched range polynomial
`H₀(τ) := ∑ᵢ eq̃(τ, i)·w̃(i)·∏_{j=1}^{b−1}(w̃(i) − j)(w̃(i) + j)` — multilinear in `τ ∈ F^{m₀}`;
`H₀ ≡ 0` iff every table entry is a root of the range product, i.e. lies in `[−(b−1), b−1]`
(under `2b − 1 < q`). **Sorried (F5).** -/
def hZero (φF : ZMod q →+* F) (b : ℕ) (w : LiftedWitness Φ μ n) :
    MvPolynomial (Fin m₀) F :=
  sorry

/-- **Eq. (22)**: the `eq̃`-batched linear constraint polynomial
`H_α(τ) := ∑ᵢ eq̃(τ, i)·(∑_u M̃_α(i,u)·(∑_ℓ w̃(u,ℓ)·α̃(ℓ)) − ŷᵢ(α))` — multilinear in
`τ ∈ F^{m₁}`, built from the public `M̃_α` (the multilinear extension of the `α`-evaluated
lifted matrix, including the `−(α^d + 1)` quotient columns) and the table `w̃`; `H_α ≡ 0` iff
every lifted row of `relLift` vanishes at `α`. **Sorried (F5).** -/
def hAlpha (φF : ZMod q →+* F) (b : ℕ) (s : RlinStatement Φ n μ) (a : F)
    (w : LiftedWitness Φ μ n) : MvPolynomial (Fin m₁) F :=
  sorry

/-- `H₀` is multilinear (degree `≤ 1` in each batching variable — only `eq̃` depends on `τ`).
Load-bearing for the Kronecker pullback degree bound `< 2 ^ m₀`. **Sorried (F5).** -/
theorem hZero_degreeOf_le (φF : ZMod q →+* F) (b : ℕ) (w : LiftedWitness Φ μ n)
    (j : Fin m₀) : (hZero Φ m₀ φF b w).degreeOf j ≤ 1 := by
  sorry

/-- `H_α` is multilinear (degree `≤ 1` in each batching variable). Load-bearing for the
Kronecker pullback degree bound `< 2 ^ m₁`. **Sorried (F5).** -/
theorem hAlpha_degreeOf_le (φF : ZMod q →+* F) (b : ℕ) (s : RlinStatement Φ n μ) (a : F)
    (w : LiftedWitness Φ μ n) (j : Fin m₁) :
    (hAlpha Φ m₁ φF b s a w).degreeOf j ≤ 1 := by
  sorry

/-! ## The sumcheck polynomials (sorried F5 content)

**TODO (reuse `Sumcheck/Structured`):** `sumcheckPolyZero`/`sumcheckPolyAlpha` should be defined as
`Sumcheck.Structured.computeRoundPoly` instances rather than from scratch — `F_α` via the identity
combinator (degree 2), `F_{0,τ₀}` via the range combinator `∏ⱼ (X − j)` of degree `2b` (the
`SumcheckMultiplierParam` docstring anticipates this Hachi case) — and the round consistency
(`hypercubeSum` / `roundRel`) via `Sumcheck.Structured.sumcheckConsistencyProp` over
`SumcheckDomain.boolDomain`. See the `Sumcheck.lean` umbrella. -/

/-- **`F_{0,τ₀}`** (the range sumcheck summand, [NOZ26] §4.3 "finish the proof using sumcheck"):
`F_{0,τ₀}(x) := eq̃(τ₀, x)·w̃(x)·∏_{j=1}^{b−1}(w̃(x) − j)(w̃(x) + j)·1_{table}(x)`, where `w̃` is
read through its multilinear extension. Satisfies `∑_{x ∈ {0,1}^{m₀}} F_{0,τ₀}(x) = H₀(τ₀)`
(`sum_sumcheckPolyZero`). Per-variable degree `roundDegZero b = 2b`. **Sorried (F5).** -/
def sumcheckPolyZero (φF : ZMod q →+* F) (b : ℕ) (τ₀ : Fin m₀ → F)
    (w : LiftedWitness Φ μ n) : MvPolynomial (Fin m₀) F :=
  sorry

/-- **`F_{α,τ₁}`** (the linear sumcheck summand):
`F_{α,τ₁}(x) := w̃(x)·α̃(x)·(∑ᵢ eq̃(τ₁, i)·M̃_α(i, x))`. Satisfies
`∑_{x ∈ {0,1}^{m₀}} F_{α,τ₁}(x) = H_α(τ₁) + zcTargetAlpha` (`sum_sumcheckPolyAlpha`).
Per-variable degree `roundDegAlpha = 2`. **Sorried (F5).** -/
def sumcheckPolyAlpha (φF : ZMod q →+* F) (b : ℕ) (s : RlinStatement Φ n μ) (a : F)
    (τ₁ : Fin m₁ → F) (w : LiftedWitness Φ μ n) : MvPolynomial (Fin m₀) F :=
  sorry

/-- The public initial target of the linear sumcheck: `a := ∑ᵢ eq̃(τ₁, i)·ŷᵢ(α)` — computable
by the verifier from the statement alone ([NOZ26] §4.3). **Sorried (F5).** -/
def zcTargetAlpha (φF : ZMod q →+* F) (s : RlinStatement Φ n μ) (a : F)
    (τ₁ : Fin m₁ → F) : F :=
  sorry

/-- Partial hypercube sum: `hypercubeSum H i cs = ∑_{x ∈ {0,1}^{m₀ − i}} H(cs, x)` — the claim
currency of the `i`-th sumcheck round (round `0` is the full sum; round `m₀` is the point
evaluation `H(cs)`). **Sorried (F5).** -/
def hypercubeSum (H : MvPolynomial (Fin m₀) F) (i : ℕ) (cs : Fin i → F) : F :=
  sorry

/-- The sum of `F_{0,τ₀}` over the cube is `H₀(τ₀)` — the algebraic identity behind the
sumcheck bridge (`Sumcheck/Bridge.lean`). **Sorried (F5).** -/
theorem sum_sumcheckPolyZero (φF : ZMod q →+* F) (b : ℕ) (τ₀ : Fin m₀ → F)
    (w : LiftedWitness Φ μ n) :
    hypercubeSum m₀ (sumcheckPolyZero Φ m₀ φF b τ₀ w) 0 (fun j => j.elim0) =
      MvPolynomial.eval τ₀ (hZero Φ m₀ φF b w) := by
  sorry

/-- The sum of `F_{α,τ₁}` over the cube is `H_α(τ₁) + zcTargetAlpha` — the algebraic identity
behind the sumcheck bridge. **Sorried (F5).** -/
theorem sum_sumcheckPolyAlpha (φF : ZMod q →+* F) (b : ℕ) (s : RlinStatement Φ n μ) (a : F)
    (τ₁ : Fin m₁ → F) (w : LiftedWitness Φ μ n) :
    hypercubeSum m₀ (sumcheckPolyAlpha Φ m₀ m₁ φF b s a τ₁ w) 0 (fun j => j.elim0) =
      MvPolynomial.eval τ₁ (hAlpha Φ m₁ φF b s a w) + zcTargetAlpha Φ m₁ φF s a τ₁ := by
  sorry

/-! ## Statement types of the zero-check and sumcheck stages -/

/-- The zero-check's output statement: the lift statement extended by the two **Kronecker
seeds** `(ρ₀, ρ_α)` of the corrected Lemma 10 (`HACHI_LEMMA10_GAP.md` §3.K.2: the challenge is
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
Lemma 11): `w̃` opens `t`, and both partial-hypercube-sum claims at the current challenge prefix
equal the current targets. Round `0` (full sums) is produced by the sumcheck bridge; round `m₀`
(point evaluations) is consumed by the final-evaluation step. The public sanity conjunct
`bound ≤ rlin.bound` threads the global norm parameter back to the `R^lin` statement bound (it
originates in `relLift`, is preserved by every intermediate extraction since the statement
components are shared, and is re-supplied at the final-evaluation step by its runtime guard). -/
def roundRel (K : LiftCom (LiftedWitness Φ μ n) E (liftShort Φ bound ρBound))
    (φF : ZMod q →+* F) (b : ℕ) (i : ℕ) :
    Set (RoundStatement Φ K.TCom F n μ i × LiftedWitness Φ μ n) :=
  {p |
    K.com p.2 = p.1.zc.t ∧
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

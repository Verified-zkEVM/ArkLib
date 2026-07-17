/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tobias Rothmann, Pablo Martín Vinuelas
-/
import ArkLib.Commitments.Functional.Hachi.RingSwitch.Reduction
import ArkLib.Data.MvPolynomial.LinearMvExtension
import ArkLib.Data.MvPolynomial.Multilinear

/-!
  # Constraint encoding — Hachi Eqs. (21)–(23) — escape-threaded (sumcheck-track milestone F5/F6)

  Definitions only (no protocol): the shared constraint-encoding layer consumed by the batching
  bridge (`ZeroCheck/Batch.lean`), the zero-check round (`ZeroCheck/Reduction.lean`), the sumcheck
  rounds, and the final-evaluation step. All declarations live in the §4.3 chain's namespace
  `ArkLib.Lattices.Ajtai.InnerOuter`, over the **concrete** lifted witness `LiftedWitness Φ μ n`
  and the abstract weak-binding commitment `LiftCom` of `RingSwitch/Reduction.lean`, so this layer
  composes directly into the escape-threaded opening chain (`Composition.lean`).

  ## The table `w̃` (Eq. (21))

  The committed lifted witness `(z, ρ)` is re-read as an `F`-valued table `w̃` indexed by the
  `m₀`-cube: rows are the `Zq`-coefficient vectors of the `zⱼ ∈ Rq` followed by the base-`b`
  gadget digits of the quotients `ρᵢ`, columns are the `d` coefficient positions. **Arity pin
  (F5)**: `2 ^ m₀` = (number of `z`-rows + number of `ρ`-digit rows) · `d`, padded to a power of
  two; `m₁` is the row-batching arity (`2 ^ m₁ ≥ n` rows of the lifted system, the arity pin
  `hAlphaEvals`/`rowPoint` require). The `M̃_α` contraction `hAlphaEvals` is now **concrete** — the
  `α`-evaluated per-row lift defect, row-encoded into the `m₁`-cube (`hAlphaEvals_rowPoint`,
  axiom-clean) — so `H_α ≡ 0` genuinely characterizes "every lifted row vanishes at `α`" (consumed
  by the batching bridge). The table entry function `wTable` is now **concrete** too — it reads the
  committed `z`/`ρ` coefficients directly (decoding the `m₀`-cube to `row := idx / d`,
  `col := idx % d`), so `H₀ ≡ 0` is a genuine (non-vacuous) shortness statement on the committed
  data. Both `hZero`/`hAlpha` are built via the real multilinear extension `MvPolynomial.MLE`, so
  their multilinearity (`hZero_degreeOf_le`/`hAlpha_degreeOf_le` — the hypothesis of the corrected
  Lemma 10's Kronecker interpolation) is **`sorry`-free**, and the whole zero-check is now
  **axiom-clean**. Matching `H₀ ≡ 0` to `liftShort`'s two bounds `(bound, ρBound)` (the range-side
  soundness step) and the sumcheck-polynomial stubs remain F5.

  ## The batched constraint polynomials (Eqs. (22)–(23))

  * `hAlpha` (Eq. (22)): the `eq̃`-batched *linear* constraint polynomial
    `H_α(τ) := ∑ᵢ eq̃(τ, i)·(∑_{u,ℓ} M̃_α(i,u)·w̃(u,ℓ)·α̃(ℓ) − ŷᵢ(α))`, multilinear in `m₁`
    variables; `H_α ≡ 0` iff every lifted row vanishes at `α`.
  * `hZero` (Eq. (23)): the `eq̃`-batched *range* polynomial
    `H₀(τ) := ∑_{u,ℓ} eq̃(τ, (u,ℓ))·w̃(u,ℓ)·∏_{j=1}^{b−1}(w̃(u,ℓ) − j)(w̃(u,ℓ) + j)`,
    multilinear in `m₀` variables; `H₀ ≡ 0` iff every table entry lies in `[−(b−1), b−1]`
    (needs `2b − 1 < q` to read field-roots as centered representatives).

  ## The sumcheck polynomials and degree pins (design R8)

  `F_{0,τ₀}` has per-variable degree `2b` (range product `2b − 1` on the multilinear `w̃`, times
  the multilinear `eq̃`) — hence `k = 2b + 1` transcripts per round; `F_{α,τ₁}` has per-variable
  degree `≤ 2`. Everything downstream is degree-parametric (`roundDegZero`/`roundDegAlpha`).

  ## The Kronecker point (Lemma 10 repair)

  `kroneckerPoint m ρ = (ρ, ρ², ρ⁴, …, ρ^{2^{m−1}})`: the pullback of an `m`-variate multilinear
  polynomial along this curve is univariate of degree `< 2^m` and the pullback is **injective**
  (`LinearMvExtension.powAlgHom_eq_zero_iff`), so univariate root counting is information-complete
  — the engine of the corrected zero-check (`ZeroCheck/Reduction.lean`). Re-exported here as the
  same map used by the downstream sumcheck files.

  ## References

  * [Nguyen, N. K., O'Rourke, G., and Zhang, J., *Hachi: Efficient Lattice-Based Multilinear
      Polynomial Commitments over Extension Fields*][NOZ26]
-/

namespace ArkLib.Lattices.Ajtai.InnerOuter

open CompPoly ArkLib.Lattices.CyclotomicModulus
open OracleComp OracleSpec ProtocolSpec CoordinateWise
open MvPolynomial

variable {q : ℕ} [NeZero q] [Fact (Nat.Prime q)] [BEq (ZMod q)] [LawfulBEq (ZMod q)]
  (Φ : CyclotomicModulus (ZMod q)) [IsCyclotomic Φ]
variable {n μ : ℕ} {E : Type} {F : Type} [Field F]
variable (m₀ m₁ : ℕ)

/-! ## The Kronecker curve and the corrected soundness parameter -/

/-- **The Kronecker point** `κ_m(ρ) := (ρ, ρ², ρ⁴, …, ρ^{2^{m−1}})` — the corrected Lemma 10's
challenge-derivation curve. Definitionally the kernel map `LinearMvExtension.kroneckerPoint`, so
the zero-check's root-counting kernel applies verbatim; re-exported here as the name the
downstream sumcheck files use. -/
@[reducible] def kroneckerPoint (m : ℕ) (ρ : F) : Fin m → F :=
  LinearMvExtension.kroneckerPoint (m := m) ρ

/-- **The corrected Lemma 10 parameter** `D := max(2, 2^{m₀}, 2^{m₁})`: the maximum padded
constraint-table size, i.e. the univariate degree bound of the Kronecker pullbacks (plus the `2`
padding for degenerate zero-arity identities, meeting the CWSS convention `2 ≤ k`). The paper's
`max(2d, 2b-1)` conflates parameters of Lemmas 9 and 11; no value of it repairs the original
challenge encoding. -/
def zeroCheckD (m₀ m₁ : ℕ) : ℕ := max 2 (max (2 ^ m₀) (2 ^ m₁))

theorem two_le_zeroCheckD (m₀ m₁ : ℕ) : 2 ≤ zeroCheckD m₀ m₁ := le_max_left _ _

theorem two_pow_m₀_le_zeroCheckD (m₀ m₁ : ℕ) : 2 ^ m₀ ≤ zeroCheckD m₀ m₁ :=
  (le_max_left _ _).trans (le_max_right _ _)

theorem two_pow_m₁_le_zeroCheckD (m₀ m₁ : ℕ) : 2 ^ m₁ ≤ zeroCheckD m₀ m₁ :=
  (le_max_right _ _).trans (le_max_right _ _)

/-- Per-round univariate degree of the range sumcheck (`F_{0,τ₀}`): degree `2b` (pin R8). -/
def roundDegZero (b : ℕ) : ℕ := 2 * b

/-- Per-round univariate degree of the linear sumcheck (`F_{α,τ₁}`): degree `≤ 2` (pin R8). -/
def roundDegAlpha : ℕ := 2

/-! ## The range factor and the table (now concrete; range-side soundness is F5) -/

/-- Hachi Eq. (23)'s per-entry range factor `P_b(v) := v·∏_{j=1}^{b-1} (v - j)·(v + j)`: the
vanishing polynomial of the symmetric range `{-(b-1), …, b-1}`. -/
def rangeProduct (b : ℕ) (v : F) : F :=
  v * ∏ j ∈ Finset.Icc 1 (b - 1), ((v - (j : F)) * (v + (j : F)))

/-- **Root characterization of the range factor** (over a field): `P_b(v) = 0` iff `v` is (the
image of) an integer in the symmetric range `{-(b-1), …, b-1}`. -/
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

/-- **The Eq. (21) table**: the committed `(z, ρ)` re-read as an `F`-valued function on the
`m₀`-cube. The cube point is decoded (via `finFunctionFinEquiv`) to a flat index `idx`, split into
a `row := idx / d` and `column := idx % d` (`d = deg Φ.φ`); rows `< μ` read the `Zq`-coefficients
of the committed `zⱼ ∈ Rq`, rows `μ ≤ · < μ + n` read the coefficients of the committed quotients
`ρᵢ`, both mapped through the base-field embedding `φF`; all other cube points are zero-padded.

**The coefficients are read directly** — the range test `H₀` is on the *committed* data, so that
`H₀ ≡ 0 ⇒` every committed coefficient lies in `[−(b−1), b−1]` is a genuine (non-vacuous) shortness
statement. (The paper's base-`b` gadget decomposition is the *honest prover's* pre-commit step to
obtain short pieces; re-decomposing here would make every entry a base-`b` digit, hence trivially
in range, and `H₀` would test nothing.) The `b` argument is retained for signature compatibility
with `hZero`; matching `H₀ ≡ 0` to `liftShort`'s two bounds `(bound, ρBound)` is the range-side
soundness step (F5, out of scope here). -/
noncomputable def wTable (φF : ZMod q →+* F) (_b : ℕ) (w : LiftedWitness Φ μ n) :
    (Fin m₀ → Fin 2) → F :=
  fun pt =>
    let idx : ℕ := (finFunctionFinEquiv pt : Fin (2 ^ m₀))
    let d : ℕ := Φ.φ.natDegree
    if hz : idx / d < μ then
      φF ((w.z ⟨idx / d, hz⟩).1.coeff (idx % d))
    else if hr : idx / d - μ < n then
      φF ((w.ρ ⟨idx / d - μ, hr⟩).coeff (idx % d))
    else 0

/-- **The `m₁`-cube point encoding row `i : Fin n`** (arity pin `n ≤ 2 ^ m₁`): the inverse image
of `i` under the binary encoding `finFunctionFinEquiv : (Fin m₁ → Fin 2) ≃ Fin (2 ^ m₁)`. Rows
with index `≥ n` are the zero-padding of the batching cube. -/
def rowPoint (hn : n ≤ 2 ^ m₁) (i : Fin n) : Fin m₁ → Fin 2 :=
  finFunctionFinEquiv.symm ⟨(i : ℕ), lt_of_lt_of_le i.isLt hn⟩

/-- The `M̃_α`-contracted per-row value of Eq. (22): the Boolean-point coefficients of `H_α`,
`i ↦ (∑_{u,ℓ} M̃_α(i,u)·w̃(u,ℓ)·α̃(ℓ)) − ŷᵢ(α)`.

**Given concretely (Lemma-10 design, Option A).** By the "represent the constraints by
polynomials" identity of [NOZ26] §4.3, this `M̃_α`-contraction equals the `α`-evaluated per-row
**defect** of the lift relation `relLift`,
`evalAt α (∑ⱼ Mᵢⱼ·zⱼ) − evalAt α ŷᵢ − evalAt α (X^d+1)·evalAt α ρᵢ`, so we take that defect as
the definition, row-encoded into the `m₁`-cube via `rowPoint` and zero-padded on rows `≥ n`. Its
vanishing at every Boolean point is then exactly the `relLift` row constraint
(`hAlphaEvals_rowPoint`) — the content the batching bridge's un-batching pull-back consumes. The
literal table-contraction form (needed only for the sumcheck *summand* `sumcheckPolyAlpha`)
remains F5 (`wTable`). The `b` argument is retained for signature compatibility with `hAlpha`. -/
noncomputable def hAlphaEvals (φF : ZMod q →+* F) (_b : ℕ) (s : RlinStatement Φ n μ) (a : F)
    (w : LiftedWitness Φ μ n) : (Fin m₁ → Fin 2) → F :=
  fun pt =>
    if h : ((finFunctionFinEquiv pt : Fin (2 ^ m₁)) : ℕ) < n then
      evalAt φF a (rowSum Φ s w.z ⟨_, h⟩)
        - evalAt φF a ((s.yvec ⟨_, h⟩).1.toPoly)
        - evalAt φF a Φ.φ.toPoly * evalAt φF a (w.ρ ⟨_, h⟩)
    else 0

omit [NeZero q] [IsCyclotomic Φ] in
/-- **Faithfulness of the row encoding**: at the Boolean point `rowPoint i`, the `H_α`
coefficient `hAlphaEvals` is exactly row `i`'s `α`-evaluated lift defect. This is the bridge
between `hAlpha ≡ 0` (via `MLE_eq_zero_iff`) and the per-row `relLift` constraints. -/
theorem hAlphaEvals_rowPoint (φF : ZMod q →+* F) (b : ℕ) (s : RlinStatement Φ n μ) (a : F)
    (w : LiftedWitness Φ μ n) (hn : n ≤ 2 ^ m₁) (i : Fin n) :
    hAlphaEvals Φ m₁ φF b s a w (rowPoint m₁ hn i) =
      evalAt φF a (rowSum Φ s w.z i) - evalAt φF a ((s.yvec i).1.toPoly)
        - evalAt φF a Φ.φ.toPoly * evalAt φF a (w.ρ i) := by
  simp only [hAlphaEvals, rowPoint, Equiv.apply_symm_apply, Fin.eta, i.isLt, dif_pos]

/-! ## The batched constraint polynomials (genuine multilinear extensions) -/

/-- **Eq. (23)**: the `eq̃`-batched range polynomial as the real multilinear extension of the
per-entry range factor `P_b(w̃(·))` — multilinear in `τ ∈ F^{m₀}`; `H₀ ≡ 0` iff every table entry
is a root of the range product, i.e. lies in `[−(b−1), b−1]` (under `2b − 1 < q`). -/
noncomputable def hZero (φF : ZMod q →+* F) (b : ℕ) (w : LiftedWitness Φ μ n) :
    MvPolynomial (Fin m₀) F :=
  MLE fun v => rangeProduct b (wTable Φ m₀ φF b w v)

/-- **Eq. (22)**: the `eq̃`-batched linear constraint polynomial as the real multilinear
extension of the `M̃_α`-contracted per-row values; `H_α ≡ 0` iff every lifted row of `relLift`
vanishes at `α`. -/
noncomputable def hAlpha (φF : ZMod q →+* F) (b : ℕ) (s : RlinStatement Φ n μ) (a : F)
    (w : LiftedWitness Φ μ n) : MvPolynomial (Fin m₁) F :=
  MLE (hAlphaEvals Φ m₁ φF b s a w)

omit [NeZero q] [IsCyclotomic Φ] in
/-- `H₀` is multilinear (degree `≤ 1` in each batching variable) — the hypothesis of the
Kronecker pullback degree bound `< 2 ^ m₀`. `sorry`-free (a genuine `MLE`). -/
theorem hZero_degreeOf_le (φF : ZMod q →+* F) (b : ℕ) (w : LiftedWitness Φ μ n)
    (j : Fin m₀) : (hZero Φ m₀ φF b w).degreeOf j ≤ 1 :=
  MLE_degreeOf _ j

omit [NeZero q] [IsCyclotomic Φ] in
/-- `H_α` is multilinear (degree `≤ 1` in each batching variable). `sorry`-free. -/
theorem hAlpha_degreeOf_le (φF : ZMod q →+* F) (b : ℕ) (s : RlinStatement Φ n μ) (a : F)
    (w : LiftedWitness Φ μ n) (j : Fin m₁) :
    (hAlpha Φ m₁ φF b s a w).degreeOf j ≤ 1 :=
  MLE_degreeOf _ j

/-- `H₀` as an element of the multilinear subtype (the input the Kronecker root-counting kernel
consumes). -/
noncomputable def hZeroML (φF : ZMod q →+* F) (b : ℕ) (w : LiftedWitness Φ μ n) :
    MvPolynomial.restrictDegree (Fin m₀) F 1 :=
  ⟨hZero Φ m₀ φF b w,
    (mem_restrictDegree_iff_degreeOf_le _ _).mpr fun j => hZero_degreeOf_le Φ m₀ φF b w j⟩

/-- `H_α` as an element of the multilinear subtype. -/
noncomputable def hAlphaML (φF : ZMod q →+* F) (b : ℕ) (s : RlinStatement Φ n μ) (a : F)
    (w : LiftedWitness Φ μ n) : MvPolynomial.restrictDegree (Fin m₁) F 1 :=
  ⟨hAlpha Φ m₁ φF b s a w,
    (mem_restrictDegree_iff_degreeOf_le _ _).mpr fun j => hAlpha_degreeOf_le Φ m₁ φF b s a w j⟩

/-- Evaluation of the multilinear extension of the table `w̃` at a point `a ∈ F^{m₀}`:
`mle[w̃](a) = ∑ᵢ w̃(i)·eq̃(i, a)`. The final-evaluation step's claim currency
(`Sumcheck/FinalEval.lean`). `sorry`-free modulo the `wTable` encoding. -/
noncomputable def wTableMleEval (φF : ZMod q →+* F) (b : ℕ) (w : LiftedWitness Φ μ n)
    (a : Fin m₀ → F) : F :=
  MvPolynomial.eval a (MLE (wTable Φ m₀ φF b w))

/-! ## The sumcheck polynomials (sorried F5 content) -/

/-- **`F_{0,τ₀}`** (the range sumcheck summand): satisfies `∑_{x} F_{0,τ₀}(x) = H₀(τ₀)`
(`sum_sumcheckPolyZero`). Per-variable degree `roundDegZero b = 2b`. **Sorried (F5).** -/
def sumcheckPolyZero (φF : ZMod q →+* F) (b : ℕ) (τ₀ : Fin m₀ → F)
    (w : LiftedWitness Φ μ n) : MvPolynomial (Fin m₀) F :=
  sorry

/-- **`F_{α,τ₁}`** (the linear sumcheck summand): satisfies
`∑_{x} F_{α,τ₁}(x) = H_α(τ₁) + zcTargetAlpha` (`sum_sumcheckPolyAlpha`).
Per-variable degree `roundDegAlpha = 2`. **Sorried (F5).** -/
def sumcheckPolyAlpha (φF : ZMod q →+* F) (b : ℕ) (s : RlinStatement Φ n μ) (a : F)
    (τ₁ : Fin m₁ → F) (w : LiftedWitness Φ μ n) : MvPolynomial (Fin m₀) F :=
  sorry

/-- The public initial target of the linear sumcheck: `a := ∑ᵢ eq̃(τ₁, i)·ŷᵢ(α)` — computable
by the verifier from the statement alone. **Sorried (F5).** -/
def zcTargetAlpha (φF : ZMod q →+* F) (s : RlinStatement Φ n μ) (a : F)
    (τ₁ : Fin m₁ → F) : F :=
  sorry

/-- Partial hypercube sum: `hypercubeSum H i cs = ∑_{x ∈ {0,1}^{m₀ − i}} H(cs, x)`. **Sorried
(F5).** -/
def hypercubeSum (H : MvPolynomial (Fin m₀) F) (i : ℕ) (cs : Fin i → F) : F :=
  sorry

/-- The sum of `F_{0,τ₀}` over the cube is `H₀(τ₀)`. **Sorried (F5).** -/
theorem sum_sumcheckPolyZero (φF : ZMod q →+* F) (b : ℕ) (τ₀ : Fin m₀ → F)
    (w : LiftedWitness Φ μ n) :
    hypercubeSum m₀ (sumcheckPolyZero Φ m₀ φF b τ₀ w) 0 (fun j => j.elim0) =
      MvPolynomial.eval τ₀ (hZero Φ m₀ φF b w) := by
  sorry

/-- The sum of `F_{α,τ₁}` over the cube is `H_α(τ₁) + zcTargetAlpha`. **Sorried (F5).** -/
theorem sum_sumcheckPolyAlpha (φF : ZMod q →+* F) (b : ℕ) (s : RlinStatement Φ n μ) (a : F)
    (τ₁ : Fin m₁ → F) (w : LiftedWitness Φ μ n) :
    hypercubeSum m₀ (sumcheckPolyAlpha Φ m₀ m₁ φF b s a τ₁ w) 0 (fun j => j.elim0) =
      MvPolynomial.eval τ₁ (hAlpha Φ m₁ φF b s a w) + zcTargetAlpha Φ m₁ φF s a τ₁ := by
  sorry

/-! ## Statement types of the zero-check and sumcheck stages -/

/-- The zero-check's output statement: the lift statement extended by the two **Kronecker
seeds** `(ρ₀, ρ_α)` of the corrected Lemma 10 (the challenge is the seed pair; the batching
points `τ₀ := κ_{m₀}(ρ₀)`, `τ_α := κ_{m₁}(ρ_α)` are derived deterministically). -/
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
`a₁, …, aᵢ` so far, and the current pair of sumcheck targets `(z_i^{(0)}, z_i^{(α)})`. -/
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

/-- **The per-round seam relation** of the paired sumcheck ([NOZ26] Lemma 11): `w̃` opens `t`, is
short (`liftShort` — the weak-binding escape's precondition, threaded through every seam;
resolution option 2 of the audit doc), and both partial-hypercube-sum claims at the current
challenge prefix equal the current targets. The public sanity conjunct `bound ≤ rlin.bound`
threads the global norm parameter back to the `R^lin` statement bound. -/
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

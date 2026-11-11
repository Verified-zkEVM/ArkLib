/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pablo Martín Vinuelas
-/
module

public import ArkLib.Commitments.Functional.Hachi.ZeroCheck.Constraints
public import ArkLib.ToCompPoly.Univariate.Basic

/-!
  # The round-polynomial layer of the Hachi sumcheck

  The partial hypercube sums of `ZeroCheck/Constraints.lean` are `F`-valued: `hypercubeSum`
  *evaluates*. The round soundness argument needs more than the value — the partial sum, as a
  function of the free coordinate, must be a univariate polynomial of bounded degree, because
  that is what upgrades "the sum agrees with the prover's message `gᵢ` at the `k` sibling
  challenges" to "it agrees with `gᵢ` everywhere", and in particular at `0` and `1`. This
  file builds that polynomial and the cube-split identity that consumes it.

  ## Contents

  * `roundPoly_sum` — the round-`i` partial sum is the sum of the two
    round-`(i+1)` partial sums at the Boolean extensions of the challenge prefix. With the
    round check `gᵢ(0) + gᵢ(1) = targetᵢ₋₁` this is what carries a round's claim back one
    round.
  * `roundPoly` — the partial sum as a `Polynomial F`, with `roundPoly_eval` (its values are
    the partial sums) and `roundPoly_degree_le` (it inherits the summand's per-variable
    degree).
  * `roundPoly_degree_le_sumcheckPolyZero` / `…Alpha` — the two instances at Hachi's
    summands, with degree bounds `roundDegZero b = 2b` and `roundDegAlpha = 2`.
  * `computableRoundPoly` — the same partial sum as a **computable** `CPolynomial F`, with
    `computableRoundPoly_toPoly` identifying it with `roundPoly`, `computableRoundPoly_eval`
    its values, and `computableRoundPoly_mem_degreeLE…` its two degree memberships. This is
    what the honest prover actually sends (`Sumcheck/Completeness.lean`'s `honestComputeG`).

  ## Computability

  `roundPoly` is a proof-side object: it is `noncomputable` and lives in Mathlib's
  `Polynomial`, because its only role is to witness that the partial sum *is* polynomial.
  Nothing the protocol computes depends on it — the wire object is the computable
  `RoundMsg = CPolynomial.degreeLE (2b) × CPolynomial.degreeLE 2` of `Sumcheck/Rounds.lean`,
  so the honest prover's round message must be a `CPolynomial`. Keeping the two apart lets the
  soundness argument use Mathlib's degree API without making any executable definition
  noncomputable.

  The bridge between them is `computableRoundPoly`, built by evaluating the summand `H` in the
  ring `CPolynomial F` itself: the challenge prefix and the Boolean tail go to constants
  (`CPolynomial.CHom`), the free coordinate goes to `CPolynomial.X`. Only `CMvPolynomial.eval₂`
  and `CPolynomial`'s own ring structure are used, so the definition stays computable — in
  particular it does **not** go through `CPolynomial.ringEquiv`, `CMvPolynomial.finSuccEquiv`
  or any interpolation, all of which are `noncomputable`. Its two properties are then obtained
  from `roundPoly`'s by transport along `computableRoundPoly_toPoly`, which is where the
  representation boundary is crossed once and for all.

  ## References

  * [Nguyen, N. K., O'Rourke, G., and Zhang, J., *Hachi: Efficient Lattice-Based Multilinear
      Polynomial Commitments over Extension Fields*][NOZ26]
-/

@[expose] public section

namespace ArkLib.Lattices.Ajtai.InnerOuter

open CompPoly CPoly ArkLib.Lattices.CyclotomicModulus
open MvPolynomial

variable {q : ℕ} [NeZero q] [Fact (Nat.Prime q)] [BEq (ZMod q)] [LawfulBEq (ZMod q)]
  (Φ : CyclotomicModulus (ZMod q)) [IsCyclotomic Φ]
variable {n μ : ℕ} {F : Type} [Field F] [BEq F] [LawfulBEq F]
variable (m₀ m₁ : ℕ)

/-! ### The round-polynomial layer

Everything in this section is stated at arity `M + 1`. That is no loss: a round only exists
when there is a coordinate left to fold, so `0 < m₀` holds at every call site, and
destructing it (`obtain ⟨M, rfl⟩`) is what lets `MvPolynomial (Fin m₀)` meet the
`Fin (n + 1)` shape that `finSuccEquivNth` is stated at, without a dependent cast. -/

section RoundPoly

variable {M : ℕ}

/-- The univariate polynomial whose value at `T` is the partial hypercube sum at `cs`
extended by `T`. -/
noncomputable def roundPoly (H : CMvPolynomial (M + 1) F) (i : Fin (M + 1)) (cs : Fin i → F) :
    Polynomial F :=
  ∑ x : Fin (M + 1 - (i + 1)) → Fin 2,
    (fromCMvPolynomial H).evalExcept i (hypercubeSuffix i cs x)

omit [NeZero q] [IsCyclotomic Φ] [BEq (ZMod q)] [LawfulBEq (ZMod q)] [BEq F] [LawfulBEq F] in
/-- The round polynomial computes the partial sum: its value at any `T` is the round-`(i+1)`
partial hypercube sum at the prefix extended by `T`. -/
theorem roundPoly_eval (H : CMvPolynomial (M + 1) F) (i : Fin (M + 1)) (cs : Fin i → F) (T : F) :
    Polynomial.eval T (roundPoly H i cs)
      = hypercubeSum (M + 1) H ((i : ℕ) + 1) (Fin.snoc cs T) := by
  simpa only [roundPoly, hypercubeSum_eq_mathlib] using
    MvPolynomial.eval_sum_evalExcept_hypercube (fromCMvPolynomial H) i cs T

omit [NeZero q] [IsCyclotomic Φ] [BEq (ZMod q)] [LawfulBEq (ZMod q)] [BEq F] [LawfulBEq F] in
/-- The two Boolean values recover the previous CompPoly residual sum. -/
theorem roundPoly_sum (H : CMvPolynomial (M + 1) F) (i : Fin (M + 1)) (cs : Fin i → F) :
    (roundPoly H i cs).eval 0 + (roundPoly H i cs).eval 1 = hypercubeSum (M + 1) H i cs := by
  simpa only [roundPoly, hypercubeSum_eq_mathlib] using
    MvPolynomial.sum_eval_sum_evalExcept_hypercube (fromCMvPolynomial H) i cs

omit [NeZero q] [IsCyclotomic Φ] [BEq (ZMod q)] [LawfulBEq (ZMod q)] [BEq F] [LawfulBEq F] in
/-- A uniform bound on the variable degrees of `H` bounds its round polynomial's degree. -/
theorem roundPoly_degree_le (H : CMvPolynomial (M + 1) F) (i : Fin (M + 1)) (cs : Fin i → F)
    {D : ℕ} (hH : ∀ j, (fromCMvPolynomial H).degreeOf j ≤ D) :
    (roundPoly H i cs).degree ≤ (D : WithBot ℕ) := by
  exact Polynomial.natDegree_le_iff_degree_le.mp
    (Polynomial.natDegree_sum_le_of_forall_le _ _ fun _ _ =>
      (MvPolynomial.natDegree_evalExcept_le i _ (fromCMvPolynomial H)).trans (hH i))

/-! ### The computable round polynomial

What the prover sends. `roundPoly` is built by *mapping* a Mathlib `MvPolynomial` through
`finSuccEquivNth`, both noncomputable; `computableRoundPoly` instead evaluates `H` in the ring
`CPolynomial F`, sending the free coordinate to `X` and every other coordinate to a constant.
That is an ordinary `CMvPolynomial.eval₂`, so it computes, and `computableRoundPoly_toPoly`
identifies the result with `roundPoly` — after which the value and degree facts are transports
of `roundPoly_eval` and `roundPoly_degree_le`, proved once above. -/

/-- The assignment `computableRoundPoly` evaluates through: the free coordinate `i` gets the
indeterminate `X`, every other coordinate gets the constant from `MvPolynomial.hypercubeSuffix`.
This is the computable counterpart of `finSuccEquivNth`'s pivot convention. -/
def freeVariableAssignment (i : Fin (M + 1)) (cs : Fin i → F)
    (y : Fin (M + 1 - ((i : ℕ) + 1)) → Fin 2) : Fin (M + 1) → CPolynomial F :=
  Fin.insertNth i CPolynomial.X (fun j => CPolynomial.C (hypercubeSuffix i cs y j))

/-- **The round polynomial the honest prover computes**: the partial hypercube sum in the free
coordinate, as a computable `CPolynomial F`. Each Boolean tail `y` contributes `H` evaluated
with `X` in the free coordinate and constants elsewhere, and the `2^{M-i}` contributions are
summed in `CPolynomial F`.

Computable by construction — no `ringEquiv`, no `finSuccEquiv`, no interpolation. Its
specification is `computableRoundPoly_eval` (values) plus `computableRoundPoly_toPoly` (it *is*
`roundPoly`), and the degree memberships its `RoundMsg` component needs follow from the
latter. -/
def computableRoundPoly (H : CMvPolynomial (M + 1) F) (i : Fin (M + 1)) (cs : Fin i → F) :
    CPolynomial F :=
  ∑ y : Fin (M + 1 - ((i : ℕ) + 1)) → Fin 2,
    H.eval₂ CPolynomial.CHom (freeVariableAssignment i cs y)

omit [NeZero q] [IsCyclotomic Φ] [BEq (ZMod q)] [LawfulBEq (ZMod q)] in
/-- **The representation boundary, crossed once**: evaluating a computable multivariate
polynomial in `CPolynomial F` — `X` at the pivot `i`, constants elsewhere — is the same as
Mathlib's partial evaluation of `finSuccEquivNth` at the same point.

Both sides are ring homomorphisms in `P`, and both reduce to the *same* `MvPolynomial.eval₂`
(coefficients to `Polynomial.C`, variables to `insertNth i X (C ∘ s)`) by
`MvPolynomial.eval₂_comp_left`: on the left along `toPoly`, on the right along
`Polynomial.map`, using `finSuccEquivNth_eq`'s `eval₂Hom` presentation. No cardinality
hypothesis on `F` is needed — this is an identity of polynomials, not of their value tables. -/
theorem toPoly_eval₂_CHom_insertNth (P : CMvPolynomial (M + 1) F) (i : Fin (M + 1))
    (s : Fin M → F) :
    (P.eval₂ CPolynomial.CHom
        (Fin.insertNth i CPolynomial.X (fun j => CPolynomial.C (s j)))).toPoly
      = Polynomial.map (MvPolynomial.eval s) (finSuccEquivNth F i (fromCMvPolynomial P)) := by
  have hleft : (P.eval₂ CPolynomial.CHom
        (Fin.insertNth i CPolynomial.X (fun j => CPolynomial.C (s j)))).toPoly
      = MvPolynomial.eval₂ Polynomial.C
          (Fin.insertNth i Polynomial.X (fun j => Polynomial.C (s j)))
          (fromCMvPolynomial P) := by
    rw [CPoly.eval₂_equiv, ← CPolynomial.toPolyRingHom_apply, MvPolynomial.eval₂_comp_left]
    congr 1
    · ext a; simp [CPolynomial.C_toPoly]
    · funext j
      refine Fin.succAboveCases i ?_ ?_ j
      · simp [Fin.insertNth_apply_same]
      · intro k
        simp [Fin.insertNth_apply_succAbove, CPolynomial.C_toPoly]
  rw [hleft, MvPolynomial.map_finSuccEquivNth_eq_eval₂_insertNth]

omit [NeZero q] [IsCyclotomic Φ] [BEq (ZMod q)] [LawfulBEq (ZMod q)] in
/-- **The computable round polynomial is the round polynomial.** Termwise
`toPoly_eval₂_CHom_insertNth`, after pushing `toPoly` through the finite sum
(`CPolynomial.toPoly_sum`); the two summations are over the same Boolean tail and at the same
scalar assignment `MvPolynomial.hypercubeSuffix`. -/
theorem computableRoundPoly_toPoly (H : CMvPolynomial (M + 1) F) (i : Fin (M + 1))
    (cs : Fin i → F) :
    (computableRoundPoly H i cs).toPoly = roundPoly H i cs := by
  rw [computableRoundPoly, roundPoly, CPolynomial.toPoly_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  exact toPoly_eval₂_CHom_insertNth H i (hypercubeSuffix i cs y)

omit [NeZero q] [IsCyclotomic Φ] [BEq (ZMod q)] [LawfulBEq (ZMod q)] in
/-- **What the prover's round message evaluates to**: the round-`(i+1)` partial hypercube sum at
the challenge prefix extended by `T`. The computational counterpart of `roundPoly_eval`, and the
only property of `honestComputeG` the round check and the round output map need. -/
theorem computableRoundPoly_eval (H : CMvPolynomial (M + 1) F) (i : Fin (M + 1))
    (cs : Fin i → F) (T : F) :
    (computableRoundPoly H i cs).eval T
      = hypercubeSum (M + 1) H ((i : ℕ) + 1) (Fin.snoc cs T) := by
  rw [CPolynomial.eval_toPoly, computableRoundPoly_toPoly, roundPoly_eval]

omit [NeZero q] [IsCyclotomic Φ] [BEq (ZMod q)] [LawfulBEq (ZMod q)] in
/-- **Degree membership through the bridge.** `CPolynomial.degreeLE` is `Polynomial.degreeLE`
transported along `toPoly` (`CPolynomial.degreeLE_toPoly`), so the computable round polynomial
inherits `roundPoly`'s degree bound with no `CPolynomial.Raw.degreeBound` reasoning. -/
theorem computableRoundPoly_mem_degreeLE (H : CMvPolynomial (M + 1) F) (i : Fin (M + 1))
    (cs : Fin i → F) {D : ℕ} (hH : ∀ j, (fromCMvPolynomial H).degreeOf j ≤ D) :
    computableRoundPoly H i cs ∈ CPolynomial.degreeLE (R := F) (D : WithBot ℕ) := by
  rw [CPolynomial.degreeLE_toPoly, Polynomial.mem_degreeLE, computableRoundPoly_toPoly]
  exact roundPoly_degree_le H i cs hH

end RoundPoly

/-! ### The round polynomials of the two Hachi summands

The two corollaries the round soundness consumes: each summand's partial sum is a univariate
of the degree its `RoundMsg` component is bounded by, so a defect vanishing at
`k = max (2b) 2 + 1` distinct challenges is identically zero. -/

section RoundPolyHachi

variable {M : ℕ}

omit [NeZero q] [IsCyclotomic Φ] in
/-- The range summand's round polynomial has degree `≤ roundDegZero b = 2b`. -/
theorem roundPoly_degree_le_sumcheckPolyZero {b : ℕ} (hb : 0 < b) (φF : ZMod q →+* F)
    (τ₀ : Fin (M + 1) → F) (w : LiftedWitness Φ μ n) (i : Fin (M + 1)) (cs : Fin i → F) :
    (roundPoly (sumcheckPolyZero Φ (M + 1) φF b τ₀ w) i cs).degree
      ≤ (roundDegZero b : WithBot ℕ) :=
  roundPoly_degree_le _ _ _ fun j => degreeOf_sumcheckPolyZero Φ (M + 1) hb φF τ₀ w j

omit [NeZero q] [IsCyclotomic Φ] in
/-- The linear summand's round polynomial has degree `≤ roundDegAlpha = 2`. -/
theorem roundPoly_degree_le_sumcheckPolyAlpha (φF : ZMod q →+* F) (b : ℕ)
    (s : RlinStatement Φ n μ) (α : F) (m₁ : ℕ) (τ₁ : Fin m₁ → F) (w : LiftedWitness Φ μ n)
    (i : Fin (M + 1)) (cs : Fin i → F) :
    (roundPoly (sumcheckPolyAlpha Φ (M + 1) m₁ φF b s α τ₁ w) i cs).degree
      ≤ (roundDegAlpha : WithBot ℕ) :=
  roundPoly_degree_le _ _ _ fun j =>
    degreeOf_sumcheckPolyAlpha Φ (M + 1) m₁ φF b s α τ₁ w j

omit [NeZero q] [IsCyclotomic Φ] in
/-- The range summand's *computable* round polynomial lies in `degreeLE (roundDegZero b)` —
the first component of `RoundMsg F b`. Carries `0 < b` for the same reason
`degreeOf_sumcheckPolyZero` does: at `b = 0` the range factor `P_0(v) = v` overflows `2b`. -/
theorem computableRoundPoly_sumcheckPolyZero_mem_degreeLE {b : ℕ} (hb : 0 < b)
    (φF : ZMod q →+* F) (τ₀ : Fin (M + 1) → F) (w : LiftedWitness Φ μ n) (i : Fin (M + 1))
    (cs : Fin i → F) :
    computableRoundPoly (sumcheckPolyZero Φ (M + 1) φF b τ₀ w) i cs
      ∈ CPolynomial.degreeLE (R := F) (roundDegZero b : ℕ) :=
  computableRoundPoly_mem_degreeLE _ _ _ fun j =>
    degreeOf_sumcheckPolyZero Φ (M + 1) hb φF τ₀ w j

omit [NeZero q] [IsCyclotomic Φ] in
/-- The linear summand's *computable* round polynomial lies in `degreeLE roundDegAlpha` — the
second component of `RoundMsg F b`. -/
theorem computableRoundPoly_sumcheckPolyAlpha_mem_degreeLE (φF : ZMod q →+* F) (b : ℕ)
    (s : RlinStatement Φ n μ) (α : F) (m₁ : ℕ) (τ₁ : Fin m₁ → F) (w : LiftedWitness Φ μ n)
    (i : Fin (M + 1)) (cs : Fin i → F) :
    computableRoundPoly (sumcheckPolyAlpha Φ (M + 1) m₁ φF b s α τ₁ w) i cs
      ∈ CPolynomial.degreeLE (R := F) (roundDegAlpha : ℕ) :=
  computableRoundPoly_mem_degreeLE _ _ _ fun j =>
    degreeOf_sumcheckPolyAlpha Φ (M + 1) m₁ φF b s α τ₁ w j

end RoundPolyHachi

end ArkLib.Lattices.Ajtai.InnerOuter

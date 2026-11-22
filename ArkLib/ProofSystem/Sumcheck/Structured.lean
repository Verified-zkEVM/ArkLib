/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Quang Dao
-/
module

public import ArkLib.Data.MvPolynomial.RestrictDegree
public import ArkLib.ProofSystem.Sumcheck.Domain

/-!
# Structured (Witness-Mode) Sumcheck — Types and Helpers

This file owns the product polynomial `P · Q(t)`, its per-variable degree parameters,
and the degree-bounded next-coordinate projection. It also collects the state types for
**structured sumcheck**, including the degree-2 multilinear-times-multilinear specialization
that underlies Binius BinaryBasefold and Binius RingSwitching. (Hachi's §4.3 sumcheck is *shaped*
like this — see `SumcheckMultiplierParam` — but carries its own guarded round layer under
`Commitments/Functional/Hachi/Sumcheck/`, for the reasons set out in that folder's umbrella.)

Unlike the canonical, oracle-mode sumcheck in `ArkLib/ProofSystem/Sumcheck/Spec/*`, where
the polynomial being sumchecked is an oracle statement accessible to the verifier, here
the polynomial `H = m · t` is the prover's *witness*: `t` is a committed multilinear, `m`
is a context-dependent multilinear multiplier, and `H` is their degree-2 product. The
verifier sees only the prover's round polynomials `pᵢ`, not `H` directly.

The two modes coexist as parallel primitives under `Sumcheck`.

## TODO (option C, tracked separately)

A refinement theorem connecting the two modes — given `H = m · t`, derive structured-mode
soundness from canonical-mode soundness — is left for follow-up work. Until then, the two
modes carry independent proofs.

## Contents (lifted from `Binius.BinaryBasefold.Basic` § `SumcheckOperations` and
`Sumcheck.Structured.SumcheckWitness`)

- `MultilinearPoly`, `MultiquadraticPoly` — degree-1 / degree-2 `MvPolynomial` abbreviations.
- `SumcheckMultiplierParam` — the multiplier and combinator, with per-variable degree bounds.
- `computeInitialSumcheckPoly` — `H := m · t` with the degree-2 proof.
- `MvPolynomial.fixPrefix`, `projectToNextSumcheckPoly` — partial evaluation of `H` at
  the verifier's previous challenges.
- `SumcheckBaseContext` — `(t_eval_point, original_claim)` shared input.
- `Statement Context i` — per-round state: `(sumcheck_target, challenges, ctx)`.
- `sumcheckConsistencyProp` — claim equals hypercube sum.
- `SumcheckWitness` — per-round witness `(t', H)` (the committed multilinear + projected
  round polynomial).
-/

@[expose] public section

noncomputable section

namespace Sumcheck.Structured

open Finset MvPolynomial

section SumcheckOperations

abbrev MultilinearPoly (L : Type) [CommSemiring L] (ℓ : ℕ) := L⦃≤ 1⦄[X Fin ℓ]
abbrev MultiquadraticPoly (L : Type) [CommSemiring L] (ℓ : ℕ) := L⦃≤ 2⦄[X Fin ℓ]

/-- A polynomial in `ℓ` variables over `L` whose degree in each variable `i` is bounded by `b i`
(the "**prismalinear**" shape: SWIRL hyperprism = degree `|D|-1` in the skip coord, `≤ 1` in the
Boolean coords). `MultilinearPoly L ℓ = PrismalinearPoly L (fun _ : Fin ℓ => 1)` by `rfl` (via
`restrictDegreeVar_const`), so the multilinear case is the natural specialization. -/
abbrev PrismalinearPoly (L : Type) [CommSemiring L] {ℓ : ℕ} (b : Fin ℓ → ℕ) :=
  ↥(MvPolynomial.restrictDegreeVar (Fin ℓ) L b)

/-- Public parameters for `P · Q(t)`. The multiplier has a separate degree bound for each
variable; constant bounds cover multilinear multipliers.

Binary Basefold takes `P = eqTilde(r₀, …, r_{ℓ-1}, X₀, …, X_{ℓ-1})` and `Q = X`,
with `degCombinator = 1`, giving a degree-two product. Hachi's range check takes the
vanishing polynomial of `{−(b−1), …, b−1}`,
`Q = X · ∏_{j=1}^{b−1} (X − j)(X + j)`. For `0 < b`, its degree is `2b − 1`, giving a
product of degree at most `2b` in each variable with a multilinear multiplier. At `b = 0`,
`Q = X`, so Hachi's degree bound requires `0 < b` (see `roundDegZero` in
`Commitments/Functional/Hachi/ZeroCheck/Constraints.lean`). -/
structure SumcheckMultiplierParam (L : Type) [CommSemiring L] (ℓ : ℕ) (Context : Type)
    (multpolyBound : Fin ℓ → ℕ := fun _ => 1) where
  /-- Public multiplier `P`. -/
  multpoly : Context → PrismalinearPoly L multpolyBound
  /-- Public univariate combinator `Q`. -/
  combinator : Context → Polynomial L
  /-- Uniform degree bound on `Q`. -/
  degCombinator : ℕ
  /-- The combinator respects its bound. -/
  combinator_natDegree_le : ∀ ctx, (combinator ctx).natDegree ≤ degCombinator

variable {L : Type} [CommSemiring L] (ℓ : ℕ)

/-- The product polynomial `P · Q(t)`, with per-variable degree bounds. -/
def computeRoundPoly {Context : Type} {multpolyBound : Fin ℓ → ℕ}
    (param : SumcheckMultiplierParam L ℓ Context multpolyBound)
    (ctx : Context) (t : MultilinearPoly L ℓ) :
    PrismalinearPoly L (fun i => param.degCombinator + multpolyBound i) :=
  ⟨(param.multpoly ctx).val * Polynomial.aeval t.val (param.combinator ctx), by
    rw [MvPolynomial.mem_restrictDegreeVar_iff_degreeOf_le]
    intro i
    have hP : degreeOf i (param.multpoly ctx).val ≤ multpolyBound i :=
      (MvPolynomial.mem_restrictDegreeVar_iff_degreeOf_le _).mp
        (param.multpoly ctx).property i
    have ht : degreeOf i t.val ≤ 1 :=
      degreeOf_le_iff.mpr fun term a ↦ t.property a i
    calc degreeOf i ((param.multpoly ctx).val * Polynomial.aeval t.val (param.combinator ctx))
        ≤ degreeOf i (param.multpoly ctx).val
            + degreeOf i (Polynomial.aeval t.val (param.combinator ctx)) := degreeOf_mul_le i _ _
      _ ≤ multpolyBound i + (param.combinator ctx).natDegree := by
          gcongr
          exact MvPolynomial.degreeOf_aeval_le i (param.combinator ctx) t.val ht
      _ ≤ multpolyBound i + param.degCombinator := by
          gcongr
          exact param.combinator_natDegree_le ctx
      _ = param.degCombinator + multpolyBound i := by ring⟩

/-- The identity-combinator specialization `m · t`, packaged with its degree-two bound. -/
def computeInitialSumcheckPoly (t m : MultilinearPoly L ℓ) : MultiquadraticPoly L ℓ :=
  computeRoundPoly ℓ
    { multpoly := fun _ : Unit => m
      combinator := fun _ => Polynomial.X
      degCombinator := 1
      combinator_natDegree_le := fun _ => Polynomial.natDegree_X_le } () t

/-- The identity combinator reduces the general construction to ordinary multiplication. -/
@[simp]
theorem coe_computeInitialSumcheckPoly (t m : MultilinearPoly L ℓ) :
    (computeInitialSumcheckPoly ℓ t m).val = m.val * t.val := by
  simp [computeInitialSumcheckPoly, computeRoundPoly]

/-- Fix the next coordinate of a uniformly degree-bounded residual polynomial. The renaming
handles the round-index equation once; prefix fixing itself is `MvPolynomial.fixPrefix`. -/
def projectToNextSumcheckPoly {d : ℕ} (i : Fin ℓ)
    (Hᵢ : L⦃≤ d⦄[X Fin (ℓ - i)]) (rᵢ : L) : L⦃≤ d⦄[X Fin (ℓ - i.succ)] :=
  let p := fixPrefix (ℓ - i) ⟨1, by omega⟩ Hᵢ (fun _ => rᵢ)
  let hdim : ℓ - i - 1 = ℓ - i.succ := by simp only [Fin.val_succ]; omega
  ⟨rename (finCongr hdim) p.val,
    rename_equiv_mem_restrictDegreeVar (finCongr hdim) p.val (b := fun _ => d) p.property⟩

end SumcheckOperations

section ContextAndStatement

/-- Input context for the sumcheck protocol, used mainly in BinaryBasefold.
For other protocols, there might be other context data.
NOTE: might add a flag `rejected` to indicate if prover has been rejected before. But that seems
like a fundamental feature of OracleReduction instead, so no action taken for now. -/
structure SumcheckBaseContext (L : Type) (ℓ : ℕ) where
  t_eval_point : Fin ℓ → L         -- r = (r_0, ..., r_{ℓ-1}) => shared input
  original_claim : L               -- s = t(r) => the original claim to verify

-- `[NeZero ℓ]` matches the original auto-bind on `Statement` (the variable block in
-- `Binius.BinaryBasefold.Basic` line 384 had `[NeZero ℓ]` in scope, so `Statement` carried it).
variable {L : Type} {ℓ : ℕ} [NeZero ℓ]

/-- Statement per iterated sumcheck round -/
structure Statement (Context : Type) (i : Fin (ℓ + 1)) where
  -- Current round state
  sumcheck_target : L              -- s_i (current sumcheck target for round i)
  challenges : Fin i → L           -- R'_i = (r'_0, ..., r'_{i-1}) from previous rounds
  ctx : Context -- external context for composition from the outer protocol

end ContextAndStatement

section ConsistencyProp

variable {L : Type} [CommRing L]

/-- Sumcheck consistency: the claimed sum equals the actual polynomial evaluation sum over the
evaluation domain `D`'s cube. For the boolean hypercube (`D = boolDomain` / `uniform 𝓑`) this is the
sum over `{0,1}^k`. -/
def sumcheckConsistencyProp {k d : ℕ} (D : SumcheckDomain L k) (sumcheckTarget : L)
    (H : L⦃≤ d⦄[X Fin (k)]) : Prop :=
  sumcheckTarget = ∑ x ∈ D.cube, H.val.eval x

end ConsistencyProp

section Witness

/-- Witness for the structured sumcheck at round `i`:
- `t'` — the original multilinear polynomial (the "data" being committed); same across rounds.
- `H`  — the projected round polynomial `H_i(X_i, …, X_{ℓ-1})` of degree `≤ d`, equal to the
  round polynomial `P · Q(t')` with the first `i` variables fixed to the verifier's previous
  challenges.

The degree bound `d` is explicit (no privileged instantiation): the `H = P · t'` case passes
`d := 2`, Hachi's smallness check passes `d := 2b` (a degree-`(2b−1)` range combinator times the
multilinear multiplier).

Generic in shape; the per-round prover/verifier consume this witness uniformly across all
structured-sumcheck instantiations. -/
structure SumcheckWitness (L : Type) [CommSemiring L] (ℓ : ℕ) (i : Fin (ℓ + 1)) (d : ℕ) where
  t' : MultilinearPoly L ℓ
  H : L⦃≤ d⦄[X Fin (ℓ - i)]

end Witness

end Sumcheck.Structured

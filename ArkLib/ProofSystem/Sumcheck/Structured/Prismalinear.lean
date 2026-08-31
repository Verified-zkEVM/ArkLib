/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.ProofSystem.Sumcheck.Structured

/-!
# Structured (Witness-Mode) Sumcheck — Prismalinear specialization

The SWIRL hyperprism (Gruen 2024) replaces the multilinear multiplier `P` in the structured
sumcheck `H = P · Q(t)` with a *prismalinear* multiplier: per-variable degree `≤ multpolyBound i` in
coord `i`, where the canonical SWIRL bound `MvPolynomial.prismalinearBound ℓ' k` gives degree
`2^ℓ' − 1` in the univariate-skip coordinate and `≤ 1` in the remaining `k` Boolean coordinates.

This file is the prismalinear polynomial-shape specialization, mirroring the multilinear surface in
`ArkLib.ProofSystem.Sumcheck.Structured` *under a sub-namespace*. It is groundwork for SWIRL-style
hyperprisms; it does not yet model SWIRL's special univariate-skip round or its separate `d₀`
soundness term:

| Multilinear (`Sumcheck.Structured`)    | Prismalinear (`Sumcheck.Structured.Prismalinear`)    |
|----------------------------------------|------------------------------------------------------|
| `SumcheckMultiplierParam`              | `SumcheckMultiplierParam`                            |
| `computeRoundPoly`                     | `computeRoundPoly`                                   |
| `projectToMidSumcheckPolyWithParam`    | `projectToMidSumcheckPolyWithParam`                  |

For `multpolyBound = fun _ => 1`, the prismalinear case is *definitionally* the multilinear
case (via `restrictDegreeVar_const`, mechanically locked in by `example := rfl` next to
`PrismalinearPoly` in `Sumcheck.Structured`).

The polynomial-shape primitives `MultilinearPoly` and `PrismalinearPoly` live at the parent
namespace `Sumcheck.Structured` — they're shape primitives, not sumcheck-specific concepts, so
they're shared across the multilinear and prismalinear specializations.
-/

noncomputable section

namespace Sumcheck.Structured.Prismalinear

open Finset MvPolynomial

variable {L : Type} [CommSemiring L] (ℓ : ℕ) [NeZero ℓ]

/-- Parameters describing how a *prismalinear* round polynomial `H = P · Q(t)` is built from the
witness `t`: `P` respects a per-variable degree bound `multpolyBound : Fin ℓ → ℕ` (e.g.
`MvPolynomial.prismalinearBound ℓ' k` = degree `2^ℓ' − 1` in the univariate-skip coordinate, `≤ 1`
in the remaining Boolean coords). The round polynomial then has degree
`≤ multpolyBound i + degCombinator` in coord `i`.

The multilinear analog is `Sumcheck.Structured.SumcheckMultiplierParam`; with
`multpolyBound = fun _ => 1`, the two specialize to the same shape via `restrictDegreeVar_const`. -/
structure SumcheckMultiplierParam (L : Type) [CommSemiring L] {ℓ : ℕ} (Context : Type)
    (multpolyBound : Fin ℓ → ℕ) where
  /-- Public *prismalinear* multiplier `P`; per-variable degree in coord `i` is
  `≤ multpolyBound i`. -/
  multpoly : (ctx : Context) → PrismalinearPoly L multpolyBound
  /-- Public univariate combinator `Q`, applied to the witness: `H = P · Q(t)`. -/
  combinator : (ctx : Context) → Polynomial L
  /-- Uniform degree bound on `combinator`; the round polynomial in coord `i` has degree
  `≤ multpolyBound i + degCombinator`. -/
  degCombinator : ℕ
  /-- `combinator` respects its degree bound. -/
  combinator_natDegree_le : ∀ ctx, (combinator ctx).natDegree ≤ degCombinator

/-- The *prismalinear* round polynomial `H = P · Q(t)`, where `P = param.multpoly ctx` has
per-variable degree `≤ multpolyBound i` in coord `i` and `Q = param.combinator ctx` is the public
univariate combinator applied to the multilinear witness `t`. Output has degree
`≤ param.degCombinator + multpolyBound i` in coord `i`.

For `multpolyBound = fun _ => 1`, recovers `Sumcheck.Structured.computeRoundPoly`'s uniform output
via `restrictDegreeVar_const` (defeq). -/
def computeRoundPoly {Context : Type} {multpolyBound : Fin ℓ → ℕ}
    (param : SumcheckMultiplierParam L Context multpolyBound)
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

/-- Generic prismalinear projection
`Hᵢ(Xᵢ, ..., X_{ℓ-1}) = H₀(r₀, …, rᵢ₋₁, Xᵢ, …, X_{ℓ-1})`
for `H₀ = P · Q(t)`. The surviving per-variable bounds are the original suffix bounds after
fixing the first `i` variables. -/
def projectToMidSumcheckPolyWithParam {Context : Type} {multpolyBound : Fin ℓ → ℕ}
    (param : SumcheckMultiplierParam L Context multpolyBound)
    (ctx : Context) (t : MultilinearPoly L ℓ) (i : Fin (ℓ + 1)) (challenges : Fin i → L) :
    PrismalinearPoly L
      (fun j => param.degCombinator +
        multpolyBound (fixFirstVariablesOfMQP_survivingIndex ℓ ⟨i, by omega⟩ j)) :=
  let H₀ := computeRoundPoly (L := L) (ℓ := ℓ) param ctx t
  let Hᵢ := fixFirstVariablesOfMQP (ℓ := ℓ) (v := ⟨i, by omega⟩)
    (H := H₀) (challenges := challenges)
  ⟨Hᵢ, by
    have hp := H₀.property
    simpa [Function.comp_def] using
      (fixFirstVariablesOfMQP_degreeVarLE (L := L) (ℓ := ℓ)
        (b := fun k => param.degCombinator + multpolyBound k) (v := ⟨i, by omega⟩)
        (poly := H₀.val) (challenges := challenges) hp)
  ⟩

end Sumcheck.Structured.Prismalinear

end

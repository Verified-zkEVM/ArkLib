/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Commitments.Functional.KZG.EvaluationBinding
public import ArkLib.ToMathlib.LinearAlgebra.LagrangePartialFraction
public import CompPoly.Univariate.Lagrange
public import Batteries.Data.List.Pairwise

/-!
# KZG function binding: an efficient ARSDH reduction

A function-binding adversary outputs a commitment `cm` and a list of accepted openings
`(qᵢ, rᵢ, πᵢ)` such that no polynomial of degree at most `n` takes all values `rᵢ` at the `qᵢ`.
This file computes, from that output and the honest keys, an answer `(S, h₁, h₂)` that wins the
ARSDH experiment of Chiesa, Guan, Knabenhans and Yu with `D = n`: `|S| = n + 1`,
`Z_S(τ) ≠ 0`, `h₁ ≠ 0` and `h₂ = Z_S(τ)⁻¹ • h₁`, where `Z_S = ∏ s ∈ S, (X - s)`.

The reduction also receives `n + 2` distinct field elements `pts`. It treats three cases.

* **Conflict.** Two openings share a point `q` but give different values. As in evaluation
  binding, they yield `h = (τ - q)⁻¹ • g₁`. With `P` a set of `n` points of `pts` other than `q`
  and `τ`, the answer is `S = {q} ∪ P`, `h₁ = Z_P(τ) • g₁` (a commitment to the coefficients of
  `Z_P`) and `h₂ = h`.
* **Trapdoor among the queries.** Some query `q` satisfies `q • vk 0 = vk 1`, so `q = τ`. With
  `τ` known, the answer is a set `S` of `n + 1` points of `pts` other than `τ`, `h₁ = g₁` and
  `h₂ = Z_S(τ)⁻¹ • g₁`.
* **Interpolation.** Otherwise each query point has one value and `τ` is not a query. Let `T` be
  the first `n + 1` distinct query points and `I_T` their interpolant of degree at most `n`; some
  query `x` has `I_T(x) ≠ r_x`, otherwise `I_T` would fit every opening. For a node set `S`, the
  partial-fraction identity `(c - I_S(τ)) / Z_S(τ) = ∑ s, w_s (c - r_s) / (τ - s)` and the
  opening equations `π_s = ((c - r_s) / (τ - s)) • g₁` give the answer
  `h₁ = cm - commit(I_S)`, `h₂ = ∑ s, w_s • π_s`. It is used with `S = T`, or with
  `T` whose first node is replaced by `x` when `h₁ = 0` for `T`. At most one of the two choices
  has `h₁ = 0`: the two interpolants agree on `n` common nodes, so if they also agreed at `τ`
  they would be equal, but they differ at `x`.

The reduction never fails: on a branch that cannot occur for a winning adversary it returns
`(∅, 0, 0)`. It uses `O(n + L)` group operations for `L` openings: one scalar multiplication per
query to detect `τ`, and `O(n)` for the commitment and the combination of proofs. Field work is
polynomial in `n` and `L`; there is no enumeration of the field and no search over subsets.

## Main statements

* `KZG.FunctionBinding.functionBindingReduction`: the computable reduction.
* `KZG.FunctionBinding.arsdhWins`: the win predicate of `ARSDH.experiment`.

The proof that the answer wins is in `KZG.FunctionBinding.Wins`.

## References

* [Chiesa, A., Guan, Z., Knabenhans, C., and Yu, Z.,
  *On the Fiat–Shamir Security of Succinct Arguments from Functional Commitments*][CGKY25]
-/

@[expose] public section

open CompPoly Finset

namespace KZG

namespace FunctionBinding

variable {F : Type} [Field F] [DecidableEq F]
variable {G₁ G₂ Gₜ : Type} [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
  [AddCommGroup Gₜ] [Module F Gₜ]
variable {n : ℕ}

/-- An opening `(q, r, π)`: a point, a claimed value and an opening proof. -/
abbrev Opening (F G₁ : Type) := F × F × G₁

section Reduction

/-- Whether `s` is the trapdoor, detected through the verifier key: `s • vk 0 = vk 1`. -/
def isTrapdoor [DecidableEq G₂] (vk : Fin 2 → G₂) (s : F) : Bool :=
  decide (s • vk 0 = vk 1)

/-- Find two openings at the same point with different values. -/
def findConflict (os : List (Opening F G₁)) : Option (Opening F G₁ × Opening F G₁) :=
  os.findSome? fun o => (os.find? fun o' => decide (o'.1 = o.1 ∧ o'.2.1 ≠ o.2.1)).map (o, ·)

/-- The vanishing polynomial `∏ s ∈ P, (X - s)` of a list of points. -/
def vanishing (P : List F) : CPolynomial F :=
  (P.map fun s => CPolynomial.X - CPolynomial.C s).prod

/-- `n` points of `pts` other than `q` and the trapdoor. -/
def conflictPoints [DecidableEq G₂] (pts : Fin (n + 2) ↪ F) (vk : Fin 2 → G₂) (q : F) : List F :=
  ((List.ofFn pts).filter fun s => decide (s ≠ q) && !isTrapdoor vk s).take n

/-- The answer in the conflict case, given `h = (τ - q)⁻¹ • g₁`: the set `{q} ∪ P` for the
`n` points `P = conflictPoints pts vk q`, the commitment to `Z_P`, and `h`. -/
def conflictAnswer [DecidableEq G₂] (pts : Fin (n + 2) ↪ F) (ck : Fin (n + 1) → G₁)
    (vk : Fin 2 → G₂) (q : F) (h : G₁) : Finset F × G₁ × G₁ :=
  (insert q (conflictPoints pts vk q).toFinset,
    commit ck (fun i => (vanishing (conflictPoints pts vk q)).coeff i), h)

/-- `n + 1` points of `pts` other than `τ`. -/
def trapdoorPoints (pts : Fin (n + 2) ↪ F) (τ : F) : List F :=
  ((List.ofFn pts).filter fun s => s != τ).take (n + 1)

/-- The answer when the trapdoor `τ` is known: the `n + 1` points `S = trapdoorPoints pts τ`,
`h₁ = ck 0` and `h₂ = Z_S(τ)⁻¹ • ck 0`. -/
def trapdoorAnswer (pts : Fin (n + 2) ↪ F) (ck : Fin (n + 1) → G₁) (τ : F) :
    Finset F × G₁ × G₁ :=
  ((trapdoorPoints pts τ).toFinset, ck 0,
    (∏ s ∈ (trapdoorPoints pts τ).toFinset, (τ - s))⁻¹ • ck 0)

/-- The nodal weight `∏ j ≠ i, (v i - v j)⁻¹`; it is Mathlib's `Lagrange.nodalWeight univ v i`,
which is noncomputable only because of its section. -/
def weight (v : Fin (n + 1) → F) (i : Fin (n + 1)) : F :=
  ∏ j ∈ univ.erase i, (v i - v j)⁻¹

/-- The interpolant of degree at most `n` through the points and values of `n + 1` openings. -/
def interpolant (node : Fin (n + 1) → Opening F G₁) : CPolynomial F :=
  CPolynomial.CLagrange.interpolate univ (fun i => (node i).1) (fun i => (node i).2.1)

/-- The answer for the node set of `n + 1` openings: the set of their points,
`h₁ = cm - commit(I)` for their interpolant `I`, and `h₂ = ∑ i, wᵢ • πᵢ`. -/
def interpolationAnswer (ck : Fin (n + 1) → G₁) (cm : G₁) (node : Fin (n + 1) → Opening F G₁) :
    Finset F × G₁ × G₁ :=
  (univ.image fun i => (node i).1, cm - commit ck (fun i => (interpolant node).coeff i),
    ∑ i, weight (fun j => (node j).1) i • (node i).2.2)

/-- The fixed answer on branches that cannot occur for a winning adversary. -/
def losingAnswer : Finset F × G₁ × G₁ :=
  (∅, 0, 0)

/-- The openings with the first occurrence of each point. -/
def distinctOpenings (os : List (Opening F G₁)) : List (Opening F G₁) :=
  os.pwFilter fun a b => a.1 ≠ b.1

/-- The interpolation case: interpolate the first `n + 1` distinct openings, and if the resulting
`h₁` vanishes, replace the first node by an opening off the interpolant. -/
def genericAnswer [DecidableEq G₁] (ck : Fin (n + 1) → G₁) (cm : G₁) (os : List (Opening F G₁)) :
    Finset F × G₁ × G₁ :=
  let D := distinctOpenings os
  if hD : n + 1 ≤ D.length then
    let node : Fin (n + 1) → Opening F G₁ := fun i => D[i.1]'(lt_of_lt_of_le i.isLt hD)
    match os.find? (fun o => (interpolant node).eval o.1 != o.2.1) with
    | none => losingAnswer
    | some x =>
      let out := interpolationAnswer ck cm node
      if out.2.1 = 0 then interpolationAnswer ck cm (Function.update node 0 x) else out
  else losingAnswer

/-- **The function-binding reduction to ARSDH.** From the keys, `n + 2` distinct points, a
commitment and a list of openings, compute an ARSDH answer. -/
def functionBindingReduction [DecidableEq G₁] [DecidableEq G₂]
    (pts : Fin (n + 2) ↪ F) (ck : Fin (n + 1) → G₁) (vk : Fin 2 → G₂)
    (cm : G₁) (os : List (Opening F G₁)) : Finset F × G₁ × G₁ :=
  match findConflict os with
  | some (o, o') =>
    conflictAnswer pts ck vk o.1 (evalBindingReduction o.1 o.2.1 o.2.2 o'.2.1 o'.2.2).2
  | none =>
    match os.find? (fun o => isTrapdoor vk o.1) with
    | some o => trapdoorAnswer pts ck o.1
    | none => genericAnswer ck cm os

end Reduction

/-- The win predicate of `ARSDH.experiment` with `D = n` at trapdoor `τ`, verbatim. -/
def arsdhWins (τ : F) (n : ℕ) (out : Finset F × G₁ × G₁) : Prop :=
  out.1.card = n + 1 ∧ (∏ s ∈ out.1, (Polynomial.X - Polynomial.C s)).eval τ ≠ 0 ∧
    out.2.1 ≠ 0 ∧ out.2.2 = ((∏ s ∈ out.1, (Polynomial.X - Polynomial.C s)).eval τ)⁻¹ • out.2.1


end FunctionBinding

end KZG

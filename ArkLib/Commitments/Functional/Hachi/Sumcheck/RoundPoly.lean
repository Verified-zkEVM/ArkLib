/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pablo Martín Vinuelas
-/
import ArkLib.Commitments.Functional.Hachi.ZeroCheck.Constraints

/-!
  # The round-polynomial layer of the Hachi sumcheck

  The partial hypercube sums of `ZeroCheck/Constraints.lean` are `F`-valued: `hypercubeSum`
  *evaluates*. The round soundness argument needs more than the value — the partial sum, as a
  function of the free coordinate, must be a univariate polynomial of bounded degree, because
  that is what upgrades "the sum agrees with the prover's message `gᵢ` at the `k` sibling
  challenges" to "it agrees with `gᵢ` everywhere", and in particular at `0` and `1`. This
  file builds that polynomial and the cube-split identity that consumes it.

  ## Contents

  * `hypercubeSum_succ` — the cube split: the round-`i` partial sum is the sum of the two
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

/-! ## Two `CPolynomial` bundlings

`C` and `toPoly` as ring homomorphisms. Both are needed by `computableRoundPoly` and its
transfer lemma and neither exists in CompPoly; they are generic and belong upstream (CompPoly's
`Univariate/ToPoly`), not to Hachi. `CHom` must stay computable — it is what the prover
evaluates through — while `toPolyRingHom` is a proof-side bundling of the (noncomputable)
`CPolynomial.ringEquiv`, used only to bring `MvPolynomial.eval₂_comp_left` to bear. -/

namespace CompPoly.CPolynomial

variable {R : Type*} [CommSemiring R] [BEq R] [LawfulBEq R] [Nontrivial R]

/-- `toPoly` is injective: it is the forward map of the ring equivalence
`CPolynomial.ringEquiv`. This is what reduces an equation between computable polynomials to
one between Mathlib polynomials. -/
theorem toPoly_injective : Function.Injective (CPolynomial.toPoly (R := R)) :=
  fun _ _ h => CPolynomial.ringEquiv.injective h

/-- `CPolynomial.C` bundled as a ring homomorphism — the coefficient map that
`CMvPolynomial.eval₂` takes as its first argument. Computable: only the four structure fields
are proved through `toPoly`, and proofs carry no computational content. -/
def CHom : R →+* CPolynomial R where
  toFun := CPolynomial.C
  map_one' := toPoly_injective (by rw [C_toPoly, toPoly_one, Polynomial.C_1])
  map_mul' _ _ := toPoly_injective (by
    rw [C_toPoly, toPoly_mul, C_toPoly, C_toPoly, Polynomial.C_mul])
  map_zero' := toPoly_injective (by rw [C_toPoly, toPoly_zero, Polynomial.C_0])
  map_add' _ _ := toPoly_injective (by
    rw [C_toPoly, toPoly_add, C_toPoly, C_toPoly, Polynomial.C_add])

@[simp] theorem CHom_apply (r : R) : CHom r = CPolynomial.C r := rfl

/-- `toPoly` bundled as a ring homomorphism, so that `MvPolynomial.eval₂_comp_left` applies to
it. Noncomputable (it is `CPolynomial.ringEquiv`), and used in proofs only. -/
noncomputable def toPolyRingHom : CPolynomial R →+* Polynomial R :=
  (CPolynomial.ringEquiv (R := R)).toRingHom

@[simp] theorem toPolyRingHom_apply (p : CPolynomial R) : toPolyRingHom p = p.toPoly := rfl

end CompPoly.CPolynomial

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

omit [NeZero q] [IsCyclotomic Φ] [BEq F] [LawfulBEq F] in
/-- Peeling the leading free coordinate: prepending `b` to the summation index of the
round-`(i+1)` cube is the same as appending `b` to the round-`i` challenge prefix — both name
the same point of `F^{M+1}`. -/
theorem hypercubePoint_cons (i : Fin (M + 1)) (cs : Fin i → F) (b : Fin 2)
    (y : Fin (M + 1 - ((i : ℕ) + 1)) → Fin 2) :
    hypercubePoint (M + 1) i cs (Fin.cons b y ∘ finCongr (by omega)) =
      hypercubePoint (M + 1) ((i : ℕ) + 1) (Fin.snoc cs ((b : ℕ) : F)) y := by
  funext j
  simp only [hypercubePoint, Function.comp_apply]
  by_cases h1 : (j : ℕ) < (i : ℕ)
  · rw [dif_pos h1, dif_pos (show (j : ℕ) < (i : ℕ) + 1 by omega),
      show (⟨(j : ℕ), by omega⟩ : Fin ((i : ℕ) + 1)) = Fin.castSucc ⟨(j : ℕ), h1⟩ from rfl,
      Fin.snoc_castSucc]
  · rw [dif_neg h1]
    by_cases h2 : (j : ℕ) = (i : ℕ)
    · rw [dif_pos (show (j : ℕ) < (i : ℕ) + 1 by omega),
        show (finCongr (by omega) ⟨(j : ℕ) - (i : ℕ), by omega⟩ :
            Fin ((M + 1 - ((i : ℕ) + 1)) + 1)) = 0 from Fin.ext (by simp; omega),
        Fin.cons_zero,
        show (⟨(j : ℕ), by omega⟩ : Fin ((i : ℕ) + 1)) = Fin.last (i : ℕ) from
          Fin.ext (by simp; omega),
        Fin.snoc_last]
    · rw [dif_neg (show ¬ (j : ℕ) < (i : ℕ) + 1 by omega),
        show (finCongr (by omega) ⟨(j : ℕ) - (i : ℕ), by omega⟩ :
            Fin ((M + 1 - ((i : ℕ) + 1)) + 1))
          = Fin.succ ⟨(j : ℕ) - ((i : ℕ) + 1), by omega⟩ from Fin.ext (by simp; omega),
        Fin.cons_succ]

omit [NeZero q] [IsCyclotomic Φ] [BEq F] [LawfulBEq F] in
/-- The cube split — the identity every sumcheck round turns on: the round-`i` partial sum is
the sum of the two round-`(i+1)` partial sums at the two Boolean extensions of the challenge
prefix. Together with the round check `g(0) + g(1) = targetᵢ₋₁` this is what carries a
round's claim back to the previous round. -/
theorem hypercubeSum_succ (H : CMvPolynomial (M + 1) F) (i : Fin (M + 1)) (cs : Fin i → F) :
    hypercubeSum (M + 1) H i cs =
      hypercubeSum (M + 1) H ((i : ℕ) + 1) (Fin.snoc cs 0) +
        hypercubeSum (M + 1) H ((i : ℕ) + 1) (Fin.snoc cs 1) := by
  have hsplit : (M + 1) - (i : ℕ) = (M + 1 - ((i : ℕ) + 1)) + 1 := by omega
  let e : Fin 2 × (Fin (M + 1 - ((i : ℕ) + 1)) → Fin 2) ≃ (Fin ((M + 1) - (i : ℕ)) → Fin 2) :=
    (Fin.consEquiv (fun _ => Fin 2)).trans
      (Equiv.arrowCongr (finCongr hsplit.symm) (Equiv.refl (Fin 2)))
  have hstep : hypercubeSum (M + 1) H i cs
      = ∑ p : Fin 2 × (Fin (M + 1 - ((i : ℕ) + 1)) → Fin 2),
          H.eval (hypercubePoint (M + 1) i cs (Fin.cons p.1 p.2 ∘ finCongr hsplit)) := by
    rw [hypercubeSum]
    exact (Fintype.sum_equiv e _ _ fun _ => rfl).symm
  rw [hstep, Fintype.sum_prod_type, Fin.sum_univ_two]
  congr 1 <;>
    · rw [hypercubeSum]
      refine Finset.sum_congr rfl fun y _ => ?_
      rw [hypercubePoint_cons]
      norm_num

/-- The round polynomial of a partial hypercube sum: the univariate whose value at `T` is the
round-`(i+1)` partial sum at the challenge prefix extended by `T` (`roundPoly_eval`), with
the per-variable degree of `H` as its degree bound (`roundPoly_degree_le`).

This is what the honest prover sends. For soundness it plays the central role: it is the
object that upgrades "the sum agrees with the prover's `g` at `k` challenges" to "it agrees
with `g` everywhere". -/
noncomputable def roundPoly (H : CMvPolynomial (M + 1) F) (i : Fin (M + 1)) (cs : Fin i → F) :
    Polynomial F :=
  ∑ y : Fin (M + 1 - ((i : ℕ) + 1)) → Fin 2,
    Polynomial.map
      (MvPolynomial.eval (Fin.append cs (fun j => ((y j : ℕ) : F)) ∘ Fin.cast (by omega)))
      (MvPolynomial.finSuccEquivNth F i (fromCMvPolynomial H))

omit [NeZero q] [IsCyclotomic Φ] [BEq F] [LawfulBEq F] in
/-- The point `roundPoly`'s summand evaluates at: the challenge prefix, then the free coordinate,
then the Boolean tail — which is exactly the round-`(i+1)` cube point. -/
theorem insertNth_eq_hypercubePoint (i : Fin (M + 1)) (cs : Fin i → F) (T : F)
    (y : Fin (M + 1 - ((i : ℕ) + 1)) → Fin 2) :
    Fin.insertNth i T (Fin.append cs (fun j => ((y j : ℕ) : F)) ∘ Fin.cast (by omega))
      = hypercubePoint (M + 1) ((i : ℕ) + 1) (Fin.snoc cs T) y := by
  funext j
  refine Fin.succAboveCases i ?_ ?_ j
  · rw [Fin.insertNth_apply_same]
    simp only [hypercubePoint]
    rw [dif_pos (by omega : (i : ℕ) < (i : ℕ) + 1),
      show (⟨(i : ℕ), by omega⟩ : Fin ((i : ℕ) + 1)) = Fin.last (i : ℕ) from Fin.ext rfl,
      Fin.snoc_last]
  · intro k
    rw [Fin.insertNth_apply_succAbove]
    simp only [hypercubePoint, Function.comp_apply]
    by_cases hk : (k : ℕ) < (i : ℕ)
    · have hsa : ((i.succAbove k : Fin (M + 1)) : ℕ) = (k : ℕ) := by
        rw [Fin.succAbove_of_castSucc_lt _ _ (by exact Fin.lt_def.mpr (by simpa using hk))]
        rfl
      have hlt : ((i.succAbove k : Fin (M + 1)) : ℕ) < (i : ℕ) + 1 := by omega
      rw [dif_pos hlt,
        show (⟨((i.succAbove k : Fin (M + 1)) : ℕ), hlt⟩ : Fin ((i : ℕ) + 1))
          = Fin.castSucc ⟨(k : ℕ), hk⟩ from Fin.ext hsa,
        Fin.snoc_castSucc]
      exact (congrArg (Fin.append cs (fun j => ((y j : ℕ) : F)))
        (Fin.ext rfl : (Fin.cast (by omega) k : Fin ((i : ℕ) + (M + 1 - ((i : ℕ) + 1))))
          = Fin.castAdd _ ⟨(k : ℕ), hk⟩)).trans (Fin.append_left _ _ _)
    · have hsa : ((i.succAbove k : Fin (M + 1)) : ℕ) = (k : ℕ) + 1 := by
        rw [Fin.succAbove_of_le_castSucc _ _ (by exact Fin.le_def.mpr (by simpa using hk))]
        rfl
      rw [dif_neg (by omega : ¬ ((i.succAbove k : Fin (M + 1)) : ℕ) < (i : ℕ) + 1)]
      refine (congrArg (Fin.append cs (fun j => ((y j : ℕ) : F)))
        (Fin.ext (by simp; omega) :
          (Fin.cast (by omega) k : Fin ((i : ℕ) + (M + 1 - ((i : ℕ) + 1))))
            = Fin.natAdd _ ⟨(k : ℕ) - (i : ℕ), by omega⟩)).trans ?_
      rw [Fin.append_right]
      have hidx : (k : ℕ) - (i : ℕ)
          = ((i.succAbove k : Fin (M + 1)) : ℕ) - ((i : ℕ) + 1) := by omega
      exact congrArg (fun z : Fin 2 => ((z : ℕ) : F)) (congrArg y (Fin.ext hidx))

omit [NeZero q] [IsCyclotomic Φ] [BEq (ZMod q)] [LawfulBEq (ZMod q)] [BEq F] [LawfulBEq F] in
/-- The round polynomial computes the partial sum: its value at any `T` is the round-`(i+1)`
partial hypercube sum at the prefix extended by `T`. -/
theorem roundPoly_eval (H : CMvPolynomial (M + 1) F) (i : Fin (M + 1)) (cs : Fin i → F) (T : F) :
    Polynomial.eval T (roundPoly H i cs)
      = hypercubeSum (M + 1) H ((i : ℕ) + 1) (Fin.snoc cs T) := by
  rw [roundPoly, Polynomial.eval_finsetSum, hypercubeSum]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [← MvPolynomial.eval_eq_eval_mv_eval_finSuccEquivNth, insertNth_eq_hypercubePoint,
    ← CPoly.eval_equiv]

omit [NeZero q] [IsCyclotomic Φ] [BEq (ZMod q)] [LawfulBEq (ZMod q)] [BEq F] [LawfulBEq F] in
/-- The round polynomial inherits `H`'s per-variable degree bound: each summand is a
one-variable specialization of `H`, whose degree is `H`'s degree in the free coordinate, and
a finite sum does not raise it. -/
theorem roundPoly_degree_le (H : CMvPolynomial (M + 1) F) (i : Fin (M + 1)) (cs : Fin i → F)
    {D : ℕ} (hH : ∀ j, (fromCMvPolynomial H).degreeOf j ≤ D) :
    (roundPoly H i cs).degree ≤ (D : WithBot ℕ) := by
  refine (Polynomial.degree_sum_le _ _).trans (Finset.sup_le fun y _ => ?_)
  refine Polynomial.degree_map_le.trans (Polynomial.natDegree_le_iff_degree_le.mp ?_)
  rw [MvPolynomial.natDegree_finSuccEquivNth]
  exact hH i

/-! ### The computable round polynomial

What the prover sends. `roundPoly` is built by *mapping* a Mathlib `MvPolynomial` through
`finSuccEquivNth`, both noncomputable; `computableRoundPoly` instead evaluates `H` in the ring
`CPolynomial F`, sending the free coordinate to `X` and every other coordinate to a constant.
That is an ordinary `CMvPolynomial.eval₂`, so it computes, and `computableRoundPoly_toPoly`
identifies the result with `roundPoly` — after which the value and degree facts are transports
of `roundPoly_eval` and `roundPoly_degree_le`, proved once above. -/

/-- The scalar half of the round assignment: the challenge prefix `cs` followed by the Boolean
tail `y`, as a point of `F^M`. Shared with `roundPoly`, whose summand evaluates at exactly this
point (`insertNth_eq_hypercubePoint` identifies it with the round-`(i+1)` cube point). -/
def roundAssignment (i : Fin (M + 1)) (cs : Fin i → F)
    (y : Fin (M + 1 - ((i : ℕ) + 1)) → Fin 2) : Fin M → F :=
  Fin.append cs (fun k => ((y k : ℕ) : F)) ∘ Fin.cast (by omega)

/-- The assignment `computableRoundPoly` evaluates through: the free coordinate `i` gets the
indeterminate `X`, every other coordinate gets the constant `roundAssignment` puts there. This
is the computable counterpart of `finSuccEquivNth`'s pivot convention. -/
def freeVariableAssignment (i : Fin (M + 1)) (cs : Fin i → F)
    (y : Fin (M + 1 - ((i : ℕ) + 1)) → Fin 2) : Fin (M + 1) → CPolynomial F :=
  Fin.insertNth i CPolynomial.X (fun j => CPolynomial.C (roundAssignment i cs y j))

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
  have hright : Polynomial.map (MvPolynomial.eval s) (finSuccEquivNth F i (fromCMvPolynomial P))
      = MvPolynomial.eval₂ Polynomial.C
          (Fin.insertNth i Polynomial.X (fun j => Polynomial.C (s j)))
          (fromCMvPolynomial P) := by
    rw [MvPolynomial.finSuccEquivNth_apply, MvPolynomial.coe_eval₂Hom]
    rw [show Polynomial.map (MvPolynomial.eval s)
          (MvPolynomial.eval₂ (Polynomial.C.comp MvPolynomial.C)
            (Fin.insertNth i Polynomial.X (Polynomial.C ∘ MvPolynomial.X)) (fromCMvPolynomial P))
        = (Polynomial.mapRingHom (MvPolynomial.eval s))
            (MvPolynomial.eval₂ (Polynomial.C.comp MvPolynomial.C)
              (Fin.insertNth i Polynomial.X (Polynomial.C ∘ MvPolynomial.X))
              (fromCMvPolynomial P)) from rfl,
      MvPolynomial.eval₂_comp_left]
    congr 1
    · ext a; simp
    · funext j
      refine Fin.succAboveCases i ?_ ?_ j
      · simp [Fin.insertNth_apply_same]
      · intro k; simp [Fin.insertNth_apply_succAbove]
  rw [hleft, hright]

omit [NeZero q] [IsCyclotomic Φ] [BEq (ZMod q)] [LawfulBEq (ZMod q)] in
/-- **The computable round polynomial is the round polynomial.** Termwise
`toPoly_eval₂_CHom_insertNth`, after pushing `toPoly` through the finite sum
(`CPolynomial.toPoly_sum`); the two summations are over the same Boolean tail and at the same
scalar assignment `roundAssignment`. -/
theorem computableRoundPoly_toPoly (H : CMvPolynomial (M + 1) F) (i : Fin (M + 1))
    (cs : Fin i → F) :
    (computableRoundPoly H i cs).toPoly = roundPoly H i cs := by
  rw [computableRoundPoly, roundPoly, CPolynomial.toPoly_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  exact toPoly_eval₂_CHom_insertNth H i (roundAssignment i cs y)

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

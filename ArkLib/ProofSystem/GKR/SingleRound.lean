/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vuk Dolijanovic, Claude(Anthropic)
-/

import ArkLib.OracleReduction.Security.Basic
import ArkLib.OracleReduction.LiftContext.Reduction
import ArkLib.ProofSystem.GKR.Circuit
import ArkLib.Data.MvPolynomial.Multilinear
import ArkLib.Data.MvPolynomial.LineRestriction
import Mathlib.Algebra.MvPolynomial.Monad
import Mathlib.Logic.Equiv.Prod
import ArkLib.ProofSystem.Sumcheck.Spec.General
import ArkLib.ProofSystem.GKR.SumcheckAux

/-!
# One layer of the GKR protocol

Turns a claim about layer `l` of a layered arithmetic circuit into a claim about layer `l + 1`,
and proves the reduction perfectly complete. Composed across all layers in
`ArkLib/ProofSystem/GKR/General.lean`.

The layer identity being exploited is

```
V l z = ∑ x, ∑ y, add(z,x,y) * (V (l+1) x + V (l+1) y)
              + mul(z,x,y) * (V (l+1) x * V (l+1) y)
```

which `relationRound` states over the multilinear extensions, and
`relationRound_sum_at_gate` ties back to the circuit itself.

## Structure

* `addPredMLE` / `mulPredMLE` — multilinear extensions of the wiring predicates.
* `relationRound` — the layer-`l` relation, taking the next layer's polynomial `V` as an
  explicit parameter rather than as an oracle, so that layers compose.
* `roundPoly` / `roundPolyFin` — the summand as a polynomial in the `2k` summed variables,
  with its degree bound.
* `relationRound_to_relationRound` — input bridge: a true GKR claim is a true sum-check claim.
* `innerReduction` — sum-check, reused verbatim.
* `relationRound_output_to_wiring_identity` — output bridge: sum-check's output claim is the
  wiring identity at the challenge point.
* `namespace Combine` — the line trick collapsing the two surviving claims `V x*` and `V y*`
  into one, plus its completeness proof, plus the context lens gluing it to the sum-check.
* `layerMLE` / `wiringPoly` / `layerMLE_eq_wiringPoly` — the honest polynomial for each layer,
  and the fact that consecutive layers' extensions satisfy the wiring identity.

## References

This file follows Thaler's presentation (Section 4.6), not the original protocol. The two
differ in how the two claims left over by the sum-check — about `V (l+1) x*` and
`V (l+1) y*` — are collapsed back into one: we restrict `V (l+1)` to the line through `x*`
and `y*` and have the verifier sample a point on it, which is the variant described there.

* [Thaler, J., *Proofs, Arguments, and Zero-Knowledge*][Thaler2022], Section 4.6

Portions of the framework-side proofs in this file were AI-generated.
-/

namespace GKR

open MvPolynomial Polynomial OracleSpec OracleComp ProtocolSpec

variable (R : Type) [CommRing R] (n : ℕ)

-- a GKR statement, consisting of a point at and the claimed value of the circuit at that point
structure GKRStatement (k : ℕ) (l : Fin (n + 1)) where
  point : Fin k → R
  value : R



/-- Send a Boolean gate index to the corresponding point of `R`, mapping `false` to `0` and
`true` to `1`.

`Index k = Fin k → Bool` is the natural way to name gates, while polynomial evaluation wants
`Fin k → R`. This is the coercion between the two, and it is what lets a statement about the
hypercube be read as a statement about `R`-points. -/
def bridge {k : ℕ} (R : Type) [CommSemiring R] (x : Index k) : Fin k → R :=
  fun i => ((finTwoEquiv.symm (x i) : Fin 2) : R)

/-- Multilinear extension of addPred c l, jointly over its three Index k arguments
  (z, x, y), glued into one domain via Sum. -/
noncomputable def addPredMLE {k d : ℕ} (R : Type) [CommRing R] (c : Circuit k d) (l : Fin d) :
    MvPolynomial (Fin k ⊕ Fin k ⊕ Fin k) R :=
  MLE (fun w =>
    addPred R c l
      (finTwoEquiv ∘ (w ∘ Sum.inl))
      (finTwoEquiv ∘ (w ∘ Sum.inr ∘ Sum.inl))
      (finTwoEquiv ∘ (w ∘ Sum.inr ∘ Sum.inr)))

noncomputable def mulPredMLE {k d : ℕ} (R : Type) [CommRing R] (c : Circuit k d) (l : Fin d) :
    MvPolynomial (Fin k ⊕ Fin k ⊕ Fin k) R :=
  MLE (fun w =>
    mulPred R c l
      (finTwoEquiv ∘ (w ∘ Sum.inl))
      (finTwoEquiv ∘ (w ∘ Sum.inr ∘ Sum.inl))
      (finTwoEquiv ∘ (w ∘ Sum.inr ∘ Sum.inr)))

/-- **The fundamental GKR identity.** For a real gate `z` at layer `l`, the wiring sum
computes exactly what the circuit computes at `z`: the predicates `addPred`/`mulPred` vanish
except at `z`'s actual children, so the double sum collapses to the single term
`W a + W b` (add gate) or `W a * W b` (mul gate) — which is `evalLayer` by definition.

This is what ties `relationRound` below to the circuit. Without it, `relationRound` would be
an arbitrary algebraic equation with no connection to `c`. -/
theorem wiring_sum_eq_evalLayer {k d : ℕ} (c : Circuit k d) (l : Fin d)
    (W : Index k → R) (z : Index k) :
    ∑ x : Index k, ∑ y : Index k,
      (addPred R c l z x y * (W x + W y) + mulPred R c l z x y * (W x * W y))
    = evalLayer (c.gate l) W z := by
  unfold addPred mulPred evalLayer
  cases hgate : c.gate l z with
  | add a b => simp [ite_and]
  | mul a b => simp [ite_and]

/-- The Boolean point `(z, x, y)` packaged as a single `Fin 2`-valued assignment, so that
`MLE_eval_zeroOne` can fire on it. -/
def boolPoint {k : ℕ} (z x y : Index k) : (Fin k ⊕ Fin k ⊕ Fin k) → Fin 2 :=
  Sum.elim (fun i => finTwoEquiv.symm (z i))
    (Sum.elim (fun i => finTwoEquiv.symm (x i)) (fun i => finTwoEquiv.symm (y i)))

theorem bridge_elim_eq {k : ℕ} (z x y : Index k) :
    Sum.elim (bridge R z) (Sum.elim (bridge R x) (bridge R y))
      = fun j => ((boolPoint z x y j : Fin 2) : R) := by
  funext j
  rcases j with i | i | i <;> rfl

/-- At a Boolean point the multilinear extension `addPredMLE` agrees with `addPred` itself.
(The MLE is only pinned down by `addPred` on the hypercube — off it, it is an extension.) -/
theorem eval_addPredMLE_bool {k d : ℕ} (c : Circuit k d) (l : Fin d) (z x y : Index k) :
    MvPolynomial.eval (Sum.elim (bridge R z) (Sum.elim (bridge R x) (bridge R y)))
      (addPredMLE R c l) = addPred R c l z x y := by
  rw [bridge_elim_eq, addPredMLE, MLE_eval_zeroOne]
  congr 1 <;> funext i <;> simp [boolPoint]

/-- At a Boolean point the multilinear extension `mulPredMLE` agrees with `mulPred` itself. -/
theorem eval_mulPredMLE_bool {k d : ℕ} (c : Circuit k d) (l : Fin d) (z x y : Index k) :
    MvPolynomial.eval (Sum.elim (bridge R z) (Sum.elim (bridge R x) (bridge R y)))
      (mulPredMLE R c l) = mulPred R c l z x y := by
  rw [bridge_elim_eq, mulPredMLE, MLE_eval_zeroOne]
  congr 1 <;> funext i <;> simp [boolPoint]

/-- **The semantics link.** At a Boolean point (a real gate `z`), the wiring sum appearing in
`relationRound` is exactly what the circuit computes at `z` from the lower layer's values.
This is what makes `relationRound` a statement about the circuit `c` rather than an
arbitrary algebraic identity. -/
theorem relationRound_sum_at_gate {k d : ℕ} (c : Circuit k d) (l : Fin d) (z : Index k)
    (V : MvPolynomial (Fin k) R) :
    ∑ x : Index k, ∑ y : Index k,
      (MvPolynomial.eval (Sum.elim (bridge R z) (Sum.elim (bridge R x) (bridge R y)))
          (addPredMLE R c l)
        * (MvPolynomial.eval (bridge R x) V + MvPolynomial.eval (bridge R y) V)
      + MvPolynomial.eval (Sum.elim (bridge R z) (Sum.elim (bridge R x) (bridge R y)))
          (mulPredMLE R c l)
        * (MvPolynomial.eval (bridge R x) V * MvPolynomial.eval (bridge R y) V))
    = evalLayer (c.gate l) (fun w => MvPolynomial.eval (bridge R w) V) z := by
  rw [← wiring_sum_eq_evalLayer R c l (fun w => MvPolynomial.eval (bridge R w) V) z]
  refine Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun y _ => ?_))
  rw [eval_addPredMLE_bool, eval_mulPredMLE_bool]

/-! ### Chaining layers

`relationRound_sum_at_gate` above says the wiring sum computes the circuit *at a Boolean
point*. To chain layer `l` into layer `l + 1` we need the same statement *everywhere*, with
`V` instantiated to the honest oracle — the multilinear extension of the next layer's values.
That is `layerMLE_eval_eq_wiring_sum` below, currently unproved.

Proof sketch: both sides are multilinear in `point`, and they agree on the Boolean cube (by
`relationRound_sum_at_gate` together with `MLE_eval_zeroOne` and the definition of
`layerValues`). Two multilinear polynomials agreeing on the cube are equal —
`MvPolynomial.is_multilinear_eq_iff_eq_evals_zeroOne` in
`ArkLib/Data/MvPolynomial/Multilinear.lean`.

The snag: the right-hand side is written as a *function* of `point`, not as a polynomial, so
applying that lemma needs it expressed as one (via `bind₁`, as `roundPoly` does). An
alternative is to stay pointwise and expand `layerMLE` with `MLE_expanded`, pushing the wiring
identity through the resulting sum of `eqPolynomial` terms. -/

/-- The multilinear extension of layer `l`'s values, for the circuit `c` run on `input`.
This is what the honest prover's oracle actually is at each layer. -/
noncomputable def layerMLE {k d : ℕ} (c : Circuit k d) (input : Index k → R)
    (l : Fin (d + 1)) : MvPolynomial (Fin k) R :=
  MLE (fun w => layerValues c input l (finTwoEquiv ∘ w))

/-- At a Boolean point, `layerMLE` agrees with the layer values it extends. -/
theorem eval_layerMLE_bool {k d : ℕ} (c : Circuit k d) (input : Index k → R)
    (i : Fin (d + 1)) (w : Index k) :
    MvPolynomial.eval (bridge R w) (layerMLE R c input i) = layerValues c input i w := by
  have hb : bridge R w = fun j => ((finTwoEquiv.symm (w j) : Fin 2) : R) := rfl
  rw [hb, layerMLE, MLE_eval_zeroOne]
  congr 1
  funext j
  simp

/-- Mirror of `substZ`: fix `x` and `y` to constants, keep `z` symbolic. -/
noncomputable def substXY {k : ℕ} (x y : Fin k → R) :
    (Fin k ⊕ Fin k ⊕ Fin k) → MvPolynomial (Fin k) R
  | Sum.inl i => MvPolynomial.X i
  | Sum.inr (Sum.inl i) => MvPolynomial.C (x i)
  | Sum.inr (Sum.inr i) => MvPolynomial.C (y i)

/-- The wiring sum, as a polynomial in the `z` variables. -/
noncomputable def wiringPoly {k d : ℕ} (c : Circuit k d) (l : Fin d)
    (V : MvPolynomial (Fin k) R) : MvPolynomial (Fin k) R :=
  ∑ x : Index k, ∑ y : Index k,
    (MvPolynomial.bind₁ (substXY R (bridge R x) (bridge R y)) (addPredMLE R c l)
        * MvPolynomial.C (MvPolynomial.eval (bridge R x) V + MvPolynomial.eval (bridge R y) V)
      + MvPolynomial.bind₁ (substXY R (bridge R x) (bridge R y)) (mulPredMLE R c l)
        * MvPolynomial.C (MvPolynomial.eval (bridge R x) V * MvPolynomial.eval (bridge R y) V))

/-- `wiringPoly` evaluates to the wiring sum. -/
theorem eval_wiringPoly {k d : ℕ} (c : Circuit k d) (l : Fin d)
    (V : MvPolynomial (Fin k) R) (point : Fin k → R) :
    MvPolynomial.eval point (wiringPoly R c l V) =
      ∑ x : Index k, ∑ y : Index k,
        (MvPolynomial.eval (Sum.elim point (Sum.elim (bridge R x) (bridge R y)))
            (addPredMLE R c l)
          * (MvPolynomial.eval (bridge R x) V + MvPolynomial.eval (bridge R y) V)
        + MvPolynomial.eval (Sum.elim point (Sum.elim (bridge R x) (bridge R y)))
            (mulPredMLE R c l)
          * (MvPolynomial.eval (bridge R x) V * MvPolynomial.eval (bridge R y) V)) := by
  rw [wiringPoly, map_sum]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [map_sum]
  refine Finset.sum_congr rfl (fun y _ => ?_)
  simp only [map_add, map_mul, MvPolynomial.eval_C, ← MvPolynomial.aeval_eq_eval, aeval_bind₁]
  have key : (fun i => (MvPolynomial.aeval point) (substXY R (bridge R x) (bridge R y) i))
      = Sum.elim point (Sum.elim (bridge R x) (bridge R y)) := by
    funext j
    cases j with
    | inl j => simp [substXY]
    | inr j => cases j with
      | inl j => simp [substXY]
      | inr j => simp [substXY]
  rw [key]

/-- `substXY` sends each variable to something of degree at most 1. -/
theorem degreeOf_substXY_le {k : ℕ} (x y : Fin k → R) (i : Fin k ⊕ Fin k ⊕ Fin k) (j : Fin k) :
    degreeOf j (substXY R x y i) ≤ 1 := by
  rcases i with i | i | i
  · rcases eq_or_ne j i with h | h <;> simp [substXY, h, MvPolynomial.degreeOf_X_le]
  · simp [substXY, degreeOf_C]
  · simp [substXY, degreeOf_C]

/-- Substituting into a multilinear polynomial keeps it multilinear in a given output variable
`j`, provided every substituted polynomial has degree at most `1` in `j` and only one of them
mentions `j` at all. (This is the `key` step inside `degreeOf_roundPoly_le`, generalised.) -/
theorem degreeOf_bind₁_le {σ τ : Type} (f : σ → MvPolynomial τ R)
    (p : MvPolynomial σ R) (hp : ∀ i, degreeOf i p ≤ 1) (j : τ) (i₀ : σ)
    (hf : ∀ i, degreeOf j (f i) ≤ 1)
    (hzero : ∀ i, i ≠ i₀ → degreeOf j (f i) = 0) :
    degreeOf j (MvPolynomial.bind₁ f p) ≤ 1 := by
  have := Classical.decEq σ
  conv_lhs => rw [p.as_sum]
  rw [map_sum]
  refine le_trans (degreeOf_sum_le j p.support _) ?_
  rw [Finset.sup_le_iff]
  intro d hd
  rw [bind₁_monomial]
  refine le_trans (degreeOf_mul_le j _ _) ?_
  rw [degreeOf_C, zero_add]
  refine le_trans (degreeOf_prod_le j _ _) ?_
  have step1 : ∀ i ∈ d.support, degreeOf j (f i ^ d i) ≤ if i = i₀ then d i else 0 := by
    intro i _
    split
    · next h =>
      rw [h]
      calc degreeOf j (f i₀ ^ d i₀) ≤ d i₀ * degreeOf j (f i₀) := degreeOf_pow_le _ _ _
        _ ≤ d i₀ * 1 := by gcongr; exact hf i₀
        _ = d i₀ := mul_one _
    · next h =>
      calc degreeOf j (f i ^ d i) ≤ d i * degreeOf j (f i) := degreeOf_pow_le _ _ _
        _ = d i * 0 := by rw [hzero i h]
        _ = 0 := mul_zero _
  refine le_trans (Finset.sum_le_sum step1) ?_
  rw [Finset.sum_ite_eq']
  split
  · next h =>
    have hle : d i₀ ≤ degreeOf i₀ p := by
      rw [degreeOf_eq_sup]; exact Finset.le_sup (f := fun e => e i₀) hd
    exact le_trans hle (hp i₀)
  · exact zero_le_one

/-- `wiringPoly` is multilinear. -/
theorem degreeOf_wiringPoly_le {k d : ℕ} [Nontrivial R] (c : Circuit k d) (l : Fin d)
    (V : MvPolynomial (Fin k) R) (j : Fin k) :
    degreeOf j (wiringPoly R c l V) ≤ 1 := by
  -- each `bind₁` factor is multilinear: only `substXY … (Sum.inl j)` mentions `X j`
  have hbind : ∀ (x y : Fin k → R) (p : MvPolynomial (Fin k ⊕ Fin k ⊕ Fin k) R),
      (∀ i, degreeOf i p ≤ 1) →
      degreeOf j (MvPolynomial.bind₁ (substXY R x y) p) ≤ 1 := by
    intro x y p hp
    refine degreeOf_bind₁_le R (substXY R x y) p hp j (Sum.inl j)
      (fun i => degreeOf_substXY_le R x y i j) ?_
    intro i hi
    rcases i with i | i | i
    · simp only [substXY, degreeOf_X]
      simp only [ite_eq_right_iff]
      intro h; exact absurd (congrArg Sum.inl h.symm) hi
    · simp [substXY, degreeOf_C]
    · simp [substXY, degreeOf_C]
  rw [wiringPoly]
  refine le_trans (degreeOf_sum_le j _ _) (Finset.sup_le (fun x _ => ?_))
  refine le_trans (degreeOf_sum_le j _ _) (Finset.sup_le (fun y _ => ?_))
  refine le_trans (degreeOf_add_le _ _ _) (max_le ?_ ?_)
  · refine le_trans (degreeOf_mul_le _ _ _) ?_
    rw [degreeOf_C, add_zero]
    exact hbind _ _ _ (fun i => MLE_degreeOf _ i)
  · refine le_trans (degreeOf_mul_le _ _ _) ?_
    rw [degreeOf_C, add_zero]
    exact hbind _ _ _ (fun i => MLE_degreeOf _ i)

/-- **The chaining fact, as a polynomial identity.** -/
theorem layerMLE_eq_wiringPoly {k d : ℕ} [IsDomain R] (c : Circuit k d) (input : Index k → R)
    (l : Fin d) :
    layerMLE R c input l.castSucc = wiringPoly R c l (layerMLE R c input l.succ) := by
  rw [is_multilinear_eq_iff_eq_evals_zeroOne]
  · funext w
    change MvPolynomial.eval _ _ = MvPolynomial.eval _ _
    have hcoe : ((w : Fin k → Fin 2) : Fin k → R) = bridge R (finTwoEquiv ∘ w) := by
      funext i; simp [bridge]
    rw [hcoe, eval_wiringPoly, eval_layerMLE_bool,
      relationRound_sum_at_gate R c l (finTwoEquiv ∘ w) (layerMLE R c input l.succ),
      layerValues_castSucc]
    congr 1
    funext v
    exact (eval_layerMLE_bool R c input l.succ v).symm
  · exact MLE_mem_restrictDegree _
  · rw [mem_restrictDegree_iff_degreeOf_le]
    exact fun j => degreeOf_wiringPoly_le R c l _ j

/-- **The chaining fact**, pointwise. -/
theorem layerMLE_eval_eq_wiring_sum' {k d : ℕ} [IsDomain R] (c : Circuit k d)
    (input : Index k → R) (l : Fin d) (point : Fin k → R) :
    MvPolynomial.eval point (layerMLE R c input l.castSucc) =
      ∑ x : Index k, ∑ y : Index k,
        (MvPolynomial.eval (Sum.elim point (Sum.elim (bridge R x) (bridge R y)))
            (addPredMLE R c l)
          * (MvPolynomial.eval (bridge R x) (layerMLE R c input l.succ)
            + MvPolynomial.eval (bridge R y) (layerMLE R c input l.succ))
        + MvPolynomial.eval (Sum.elim point (Sum.elim (bridge R x) (bridge R y)))
            (mulPredMLE R c l)
          * (MvPolynomial.eval (bridge R x) (layerMLE R c input l.succ)
            * MvPolynomial.eval (bridge R y) (layerMLE R c input l.succ))) := by
  rw [layerMLE_eq_wiringPoly, eval_wiringPoly]

/-- The claim proved by layer `l`'s inner sum-check: `value` is the wiring sum at `point`,
computed against the next layer's polynomial `V`.

`V` is an explicit *parameter* rather than an oracle bundled into the statement. That is what
makes this relation composable: under sequential composition the verifier must be able to
build the output statement from the input statement and the transcript alone, and it has no
way to produce a fresh oracle for layer `l + 2`. Keeping `V` outside the statement also keeps
the relation meaningful — see `relationRound_sum_at_gate`, which ties it to the circuit. -/
def relationRound (k : ℕ) (c : Circuit k n) (l : Fin n) (V : MvPolynomial (Fin k) R) :
    Set ((GKR.GKRStatement R n k l.castSucc) × Unit) :=
  { ⟨⟨point, value⟩, _⟩ |
    value =  ∑ x : Index k , ∑ y : Index k,
      (MvPolynomial.eval (Sum.elim point (Sum.elim (bridge R x) (bridge R y))) (addPredMLE R c l)
        * (MvPolynomial.eval (bridge R x) V + MvPolynomial.eval (bridge R y) V)
      + MvPolynomial.eval (Sum.elim point (Sum.elim (bridge R x) (bridge R y))) (mulPredMLE R c l)
        * (MvPolynomial.eval (bridge R x) V * MvPolynomial.eval (bridge R y) V)) }

/-- The consequence you actually want: the honest layer-`l` statement — point anywhere, value
read off the layer-`l` MLE — satisfies `relationRound` with `V` the next layer's MLE.

Follows from `layerMLE_eval_eq_wiring_sum` by definitional unfolding alone. -/
theorem honest_mem_relationRound {k : ℕ} [IsDomain R] (c : Circuit k n) (input : Index k → R)
    (l : Fin n) (point : Fin k → R) :
    ⟨⟨point, MvPolynomial.eval point (layerMLE R c input l.castSucc)⟩, ()⟩
      ∈ relationRound R n k c l (layerMLE R c input l.succ) :=
  layerMLE_eval_eq_wiring_sum' R c input l point

/-- Substitute `z := point`, leaving `x`/`y` symbolic — fixes the round polynomial's
  z-slot to a concrete field value while keeping x/y as free variables. -/
noncomputable def substZ {k : ℕ} (point : Fin k → R) :
    (Fin k ⊕ Fin k ⊕ Fin k) → MvPolynomial (Fin k ⊕ Fin k) R
  | Sum.inl i => MvPolynomial.C (point i)
  | Sum.inr (Sum.inl i) => MvPolynomial.X (Sum.inl i)
  | Sum.inr (Sum.inr i) => MvPolynomial.X (Sum.inr i)

/-- The round polynomial for layer `l`, `z` fixed to `point`: the thing that gets
  sumchecked over `x, y`, matching relationRound's wiring-sum identity term for term. -/
noncomputable def roundPoly {k d : ℕ} (c : Circuit k d) (l : Fin d) (point : Fin k → R)
    (V : MvPolynomial (Fin k) R) : MvPolynomial (Fin k ⊕ Fin k) R:=
  let Vx := MvPolynomial.rename Sum.inl V
  let Vy := MvPolynomial.rename Sum.inr V
  MvPolynomial.bind₁ (substZ R point) (addPredMLE R c l) * (Vx + Vy)
    + MvPolynomial.bind₁ (substZ R point) (mulPredMLE R c l) * (Vx * Vy)

/--
Degreee of a polynomial that we are doing sumcheck over is <= 2
roundPolynomial defined above has a degree less than 2 in each of the variables
-/
theorem degreeOf_roundPoly_le
    {k : ℕ} [Nontrivial R] (point : Fin k → R) (V : MvPolynomial (Fin k) R)
    (hV : ∀ i, degreeOf i V ≤ 1)
    (A M : MvPolynomial (Fin k ⊕ Fin k ⊕ Fin k) R)
    (hA : ∀ i, degreeOf i A ≤ 1) (hM : ∀ i, degreeOf i M ≤ 1)
    (j : Fin k ⊕ Fin k) :
    degreeOf j (bind₁ (substZ R point) A * (rename Sum.inl V + rename Sum.inr V)
      + bind₁ (substZ R point) M * (rename Sum.inl V * rename Sum.inr V)) ≤ 2 := by
  -- ultimately we want
  -- A * (V(x) + V(y)) + M * (V(x) * V(y)) has degree of most 2 in each variable
  -- provided that we have thar A, M and V are multilinear
  -- V(x) is multilinear
    have hVleft (j : Fin k ⊕ Fin k): degreeOf j (rename Sum.inl V) ≤ 1 :=
      by cases j with
      | inl m =>
        rw [degreeOf_rename_of_injective]
        · exact hV m
        · intro x y h
          apply Sum.inl_injective
          exact h
      | inr m =>
        rw [degreeOf_def]
        rw [degrees_rename_of_injective]
        · have hz : Multiset.count (Sum.inr m) (Multiset.map Sum.inl V.degrees) = 0 := by
            rw [Multiset.count_eq_zero, Multiset.mem_map]
            rintro ⟨a, -, heq⟩
            exact Sum.inl_ne_inr heq
          omega
        · exact Sum.inl_injective
  -- V(y) is multilinear
    have hVright (j : Fin k ⊕ Fin k): degreeOf j (rename Sum.inr V) ≤ 1 :=
      by cases j with
      | inl m =>
      rw [degreeOf_def]
      rw [degrees_rename_of_injective]
      · have hz : Multiset.count (Sum.inl m) (Multiset.map Sum.inr V.degrees) = 0 := by
          rw [Multiset.count_eq_zero, Multiset.mem_map]
          rintro ⟨a, -, heq⟩
          exact Sum.inr_ne_inl heq
        omega
      · exact Sum.inr_injective
      | inr m =>
      rw [degreeOf_rename_of_injective]
      · exact hV m
      · intro x y h
        apply Sum.inr_injective
        exact h
    -- V(x) + V(y) is multilinear
    have hSumVxy (j : Fin k ⊕ Fin k) : degreeOf j (rename Sum.inl V + rename Sum.inr V) ≤ 1 := by
       calc
       _ ≤ max (degreeOf j ((rename Sum.inl) V)) (degreeOf j ((rename Sum.inr) V)) := by
         exact degreeOf_add_le j (rename Sum.inl V) (rename Sum.inr V)
       _ ≤ 1 := by rw [max_le_iff]; exact ⟨hVleft j, hVright j⟩
    -- V(X) * V(y)  is multilinear
    have hProdVxy (j : Fin k ⊕ Fin k) : degreeOf j (rename Sum.inl V * rename Sum.inr V) ≤ 1 := by
      cases j with
      | inl m =>
        have hzero : degreeOf (Sum.inl m) (rename Sum.inr V) = 0 := by
          rw [degreeOf_def, degrees_rename_of_injective, Multiset.count_eq_zero, Multiset.mem_map]
          · rintro ⟨a, -, heq⟩
            exact Sum.inr_ne_inl heq
          · exact Sum.inr_injective
        calc degreeOf (Sum.inl m) (rename Sum.inl V * rename Sum.inr V)
            ≤ degreeOf (Sum.inl m) (rename Sum.inl V) + degreeOf (Sum.inl m) (rename Sum.inr V) :=
              degreeOf_mul_le _ _ _
            _ ≤ 1 := by
              rw [hzero, add_zero, degreeOf_rename_of_injective]
              · exact hV m
              · exact Sum.inl_injective
      | inr m =>
        have hzero : degreeOf (Sum.inr m) (rename Sum.inl V) = 0 := by
          rw [degreeOf_def, degrees_rename_of_injective, Multiset.count_eq_zero, Multiset.mem_map]
          · rintro ⟨a, -, heq⟩
            exact Sum.inl_ne_inr heq
          · exact Sum.inl_injective
        calc degreeOf (Sum.inr m) (rename Sum.inl V * rename Sum.inr V)
            ≤ degreeOf (Sum.inr m) (rename Sum.inl V) + degreeOf (Sum.inr m) (rename Sum.inr V) :=
              degreeOf_mul_le _ _ _
          _ ≤ 1 := by
              rw [hzero, zero_add, degreeOf_rename_of_injective]
              · exact hV m
              · exact Sum.inr_injective
    -- substitution at a point has degree at msot 1, helpthe below lemmaer for
    have hSubstZ_pt : ∀ (i : Fin k ⊕ Fin k ⊕ Fin k) (j' : Fin k ⊕ Fin k),
        degreeOf j' (substZ R point i) ≤ 1 := by
      intro i j'
      rcases i with i | i | i
      · simp [substZ, degreeOf_C]
      · rcases eq_or_ne j' (Sum.inl i) with h | h <;> simp [substZ, degreeOf_X, h]
      · rcases eq_or_ne j' (Sum.inr i) with h | h <;> simp [substZ, degreeOf_X, h]
    -- we need this to show that A and M stay mutlilinear when we fix k out of their 3k variables
    -- (they turn into a multili polynomial in 2k variables)
    have hSubstZ : ∀ (p : MvPolynomial (Fin k ⊕ Fin k ⊕ Fin k) R), (∀ i, degreeOf i p ≤ 1) →
        ∀ j' : Fin k ⊕ Fin k, degreeOf j' (bind₁ (substZ R point) p) ≤ 1 := by
      have key : ∀ (p : MvPolynomial (Fin k ⊕ Fin k ⊕ Fin k) R), (∀ i, degreeOf i p ≤ 1) →
          ∀ i₀ : Fin k ⊕ Fin k ⊕ Fin k, ∀ j' : Fin k ⊕ Fin k,
          (∀ i, i ≠ i₀ → degreeOf j' (substZ R point i) = 0) →
          degreeOf j' (bind₁ (substZ R point) p) ≤ 1 := by
        intro p hp i₀ j' hzero
        conv_lhs => rw [p.as_sum]
        rw [map_sum]
        refine le_trans (degreeOf_sum_le j' p.support _) ?_
        rw [Finset.sup_le_iff]
        intro d hd
        rw [bind₁_monomial]
        refine le_trans (degreeOf_mul_le j' _ _) ?_
        rw [degreeOf_C, zero_add]
        refine le_trans (degreeOf_prod_le j' _ _) ?_
        have step1 : ∀ i ∈ d.support,
            degreeOf j' (substZ R point i ^ d i) ≤ if i = i₀ then d i else 0 := by
          intro i _
          split
          · next h =>
            rw [h]
            calc degreeOf j' (substZ R point i₀ ^ d i₀)
                ≤ d i₀ * degreeOf j' (substZ R point i₀) := degreeOf_pow_le _ _ _
              _ ≤ d i₀ * 1 := by gcongr; exact hSubstZ_pt i₀ j'
              _ = d i₀ := mul_one _
          · next h =>
            calc degreeOf j' (substZ R point i ^ d i)
                ≤ d i * degreeOf j' (substZ R point i) := degreeOf_pow_le _ _ _
              _ = d i * 0 := by rw [hzero i h]
              _ = 0 := mul_zero _
        refine le_trans (Finset.sum_le_sum step1) ?_
        rw [Finset.sum_ite_eq']
        split
        · next h =>
          have hle : d i₀ ≤ degreeOf i₀ p := by
            rw [degreeOf_eq_sup]; exact Finset.le_sup (f := fun e => e i₀) hd
          exact le_trans hle (hp i₀)
        · exact zero_le_one
      intro p hp j'
      rcases j' with m | m
      · apply key p hp (Sum.inr (Sum.inl m)) (Sum.inl m)
        intro i hi
        rcases i with i | i | i
        · simp [substZ, degreeOf_C]
        · simp only [ne_eq, Sum.inr.injEq, Sum.inl.injEq] at hi
          simp only [substZ]
          rw [degreeOf_X]
          simp only [ite_eq_right_iff]
          intro h; exact absurd (Sum.inl.inj h).symm hi
        · simp [substZ, degreeOf_X]
      · apply key p hp (Sum.inr (Sum.inr m)) (Sum.inr m)
        intro i hi
        rcases i with i | i | i
        · simp [substZ, degreeOf_C]
        · simp [substZ, degreeOf_X]
        · simp only [ne_eq, Sum.inr.injEq] at hi
          simp only [substZ]
          rw [degreeOf_X]
          simp only [ite_eq_right_iff]
          intro h; exact absurd (Sum.inr.inj h).symm hi
    -- here we finish of the inequality
    calc degreeOf j (bind₁ (substZ R point) A * (rename Sum.inl V + rename Sum.inr V)
        + bind₁ (substZ R point) M * (rename Sum.inl V * rename Sum.inr V))
        ≤ max (degreeOf j (bind₁ (substZ R point) A * (rename Sum.inl V + rename Sum.inr V)))
              (degreeOf j (bind₁ (substZ R point) M * (rename Sum.inl V * rename Sum.inr V))) :=
          degreeOf_add_le _ _ _
      _ ≤ 2 := by
          apply max_le
          · calc degreeOf j (bind₁ (substZ R point) A * (rename Sum.inl V + rename Sum.inr V))
                ≤ degreeOf j (bind₁ (substZ R point) A)
                    + degreeOf j (rename Sum.inl V + rename Sum.inr V) :=
                  degreeOf_mul_le _ _ _
              _ ≤ 1 + 1 := Nat.add_le_add (hSubstZ A hA j) (hSumVxy j)
              _ = 2 := rfl
          · calc degreeOf j (bind₁ (substZ R point) M * (rename Sum.inl V * rename Sum.inr V))
                ≤ degreeOf j (bind₁ (substZ R point) M)
                    + degreeOf j (rename Sum.inl V * rename Sum.inr V) :=
                  degreeOf_mul_le _ _ _
              _ ≤ 1 + 1 := Nat.add_le_add (hSubstZ M hM j) (hProdVxy j)
              _ = 2 := rfl


/-- `roundPoly`, transported to live over `Fin (k + k)` instead of `Fin k ⊕ Fin k`,
  so it fits the shape `Sumcheck.Spec` expects. -/
noncomputable def roundPolyFin {k d : ℕ} (c : Circuit k d) (l : Fin d) (point : Fin k → R)
    (V : MvPolynomial (Fin k) R) : MvPolynomial (Fin (k + k)) R :=
  MvPolynomial.rename finSumFinEquiv (roundPoly R c l point V)

theorem degreeOf_roundPolyFin_le {k d : ℕ} [Nontrivial R] (c : Circuit k d) (l : Fin d)
    (point : Fin k → R) (V : MvPolynomial (Fin k) R) (hV : ∀ i, degreeOf i V ≤ 1)
    (j : Fin (k + k)) :
    degreeOf j (roundPolyFin R c l point V) ≤ 2 := by
  unfold roundPolyFin
  rw [← finSumFinEquiv.apply_symm_apply j, degreeOf_rename_of_injective finSumFinEquiv.injective]
  exact degreeOf_roundPoly_le R point V hV (addPredMLE R c l) (mulPredMLE R c l)
    (fun i => MLE_degreeOf _ i) (fun i => MLE_degreeOf _ i) (finSumFinEquiv.symm j)

/--
Embed Fin 2 into R
-/
def D [Nontrivial R] : Fin 2  ↪ R where
  toFun := fun i => (i : R)
  inj' := by
    unfold Function.Injective
    intro a b ha
    fin_cases a
    {
      fin_cases b
      {
        rfl
      }
      {
          dsimp at ha
          simp at ha
      }
    }
    {
        fin_cases b
        {
            dsimp at ha
            simp at ha
        }
        {
          rfl
        }
    }

-- The six theorems below are AI-generated.

/-- Summing over the "Boolean cube via `D`" (as `Fintype.piFinset`/`^ᶠ` presents it in
`Sumcheck.Spec.relationRound`) is the same as summing over all of `Fin k' → Fin 2`,
precomposed with `D`. -/
theorem sum_piFinset_D [Nontrivial R] {k' : ℕ} {M : Type} [AddCommMonoid M]
    (F : (Fin k' → R) → M) :
    ∑ x ∈ Fintype.piFinset (fun _ : Fin k' ↦ (Finset.univ.map (D R))), F x
      = ∑ g : Fin k' → Fin 2, F (D R ∘ g) := by
  have := Classical.decEq R
  have h1 : (fun _ : Fin k' ↦ (Finset.univ.map (D R) : Finset R))
      = fun _ ↦ ((Finset.univ : Finset (Fin 2)).image (D R)) := by
    funext _
    rw [Finset.map_eq_image]
  rw [h1, Fintype.piFinset_image (fun _ => D R) (fun _ => Finset.univ),
    Fintype.piFinset_univ]
  rw [Finset.sum_image]
  · rfl
  · intro x _ y _ hxy
    funext i
    exact (D R).injective (congrFun hxy i)

/-- The per-point content of the bridge: evaluating `roundPoly` at a concatenated `(x, y)`
  point matches `relationRound`'s wiring-sum term for `x, y` directly (not yet summed, and
  not yet over the Boolean cube — see `sum_roundPolyFin_eq` for the full statement). -/
theorem roundPoly_eval_eq {k d : ℕ} (c : Circuit k d) (l : Fin d) (point x y : Fin k → R)
    (V : MvPolynomial (Fin k) R) :
    MvPolynomial.eval (Sum.elim x y) (roundPoly R c l point V) =
      MvPolynomial.eval (Sum.elim point (Sum.elim x y)) (addPredMLE R c l) *
        (MvPolynomial.eval x V + MvPolynomial.eval y V)
      + MvPolynomial.eval (Sum.elim point (Sum.elim x y)) (mulPredMLE R c l) *
        (MvPolynomial.eval x V * MvPolynomial.eval y V) := by
  simp only [← MvPolynomial.aeval_eq_eval]
  unfold roundPoly
  simp only [map_add, map_mul, aeval_bind₁, aeval_rename]
  congr 3
  · congr 1
    funext i
    cases i with
    | inl i => simp [substZ]
    | inr i => cases i with
      | inl i => simp [substZ]
      | inr i => simp [substZ]
  · congr 1
    funext i
    cases i with
    | inl i => simp [substZ]
    | inr i => cases i with
      | inl i => simp [substZ]
      | inr i => simp [substZ]

/-- Split a sum over `Fin (k'+k') → Fin 2` into a double sum over `Fin k' → Fin 2`, matching
  how `roundPolyFin` transports `roundPoly` across `finSumFinEquiv`. -/
theorem sum_finSumFinEquiv {k' : ℕ} {M : Type} [AddCommMonoid M]
    (F : (Fin (k' + k') → Fin 2) → M) :
    ∑ g : Fin (k' + k') → Fin 2, F g
      = ∑ x : Fin k' → Fin 2, ∑ y : Fin k' → Fin 2, F (Sum.elim x y ∘ finSumFinEquiv.symm) := by
  have h := Fintype.sum_equiv
    ((Equiv.sumArrowEquivProdArrow (Fin k') (Fin k') (Fin 2)).symm.trans
      (finSumFinEquiv.arrowCongr (Equiv.refl (Fin 2))))
    (fun p => F (Sum.elim p.1 p.2 ∘ finSumFinEquiv.symm)) F (fun p => rfl)
  rw [← h, Fintype.sum_prod_type]

/-- Convert a sum over `Fin k' → Fin 2` to a sum over `Index k'`, via `finTwoEquiv`. -/
theorem sum_finTwoEquiv {k' : ℕ} {M : Type} [AddCommMonoid M] (F : (Fin k' → Fin 2) → M) :
    ∑ x : Fin k' → Fin 2, F x = ∑ x : Index k', F (fun i => finTwoEquiv.symm (x i)) := by
  exact Fintype.sum_equiv (Equiv.arrowCongr (Equiv.refl (Fin k')) finTwoEquiv) F
    (fun x => F (fun i => finTwoEquiv.symm (x i))) (fun a => by simp [Equiv.arrowCongr_apply])

/-- The full bridge: summing `roundPolyFin` over the Boolean cube (as `Sumcheck.Spec`'s
  `relationRound` presents it, via `D`/`Fintype.piFinset`) equals `relationRound`'s
  wiring-sum formula. This is the fact needed to transport GKR's completeness down to
  `innerReduction`'s (i.e. plain sum-check's) completeness. -/
theorem sum_roundPolyFin_eq {k d : ℕ} [Nontrivial R] (c : Circuit k d) (l : Fin d)
    (point : Fin k → R) (V : MvPolynomial (Fin k) R) :
    ∑ z ∈ Fintype.piFinset (fun _ : Fin (k + k) ↦ (Finset.univ.map (D R))),
        MvPolynomial.eval z (roundPolyFin R c l point V) =
      ∑ x : Index k, ∑ y : Index k,
        (MvPolynomial.eval (Sum.elim point (Sum.elim (bridge R x) (bridge R y)))
            (addPredMLE R c l)
              * (MvPolynomial.eval (bridge R x) V + MvPolynomial.eval (bridge R y) V)
          + MvPolynomial.eval (Sum.elim point (Sum.elim (bridge R x) (bridge R y)))
            (mulPredMLE R c l)
              * (MvPolynomial.eval (bridge R x) V * MvPolynomial.eval (bridge R y) V)) := by
  have := Classical.decEq R
  rw [sum_piFinset_D R (fun z => MvPolynomial.eval z (roundPolyFin R c l point V))]
  rw [sum_finSumFinEquiv (fun g => MvPolynomial.eval (D R ∘ g) (roundPolyFin R c l point V))]
  simp_rw [sum_finTwoEquiv]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  have hcomp : D R ∘ (Sum.elim (fun i => finTwoEquiv.symm (x i)) (fun i => finTwoEquiv.symm (y i))
      ∘ finSumFinEquiv.symm) = Sum.elim (bridge R x) (bridge R y) ∘ finSumFinEquiv.symm := by
    funext i
    rcases heq : finSumFinEquiv.symm i with j | j <;> simp [heq, D, bridge]
  rw [hcomp]
  unfold roundPolyFin
  rw [eval_rename]
  have hcancel : Sum.elim (bridge R x) (bridge R y) ∘ finSumFinEquiv.symm ∘ finSumFinEquiv
      = Sum.elim (bridge R x) (bridge R y) := by
    funext i
    simp
  rw [Function.comp_assoc, hcancel]
  exact roundPoly_eval_eq R c l point (bridge R x) (bridge R y) V

/-- Package `roundPolyFin`, built from the next layer's polynomial `V`, as a sum-check oracle
  statement — i.e. bundled with a proof its degree is ≤ 2, since `Sumcheck.Spec.OracleStatement`
  is a subtype of (polynomial, degree-bound proof) pairs, not bare polynomials. -/
noncomputable def roundPolyFinOracle {k d : ℕ} [Nontrivial R] (c : Circuit k d) (l : Fin d)
    (point : Fin k → R) (V : MvPolynomial (Fin k) R) (hV : ∀ j, degreeOf j V ≤ 1) :
    Sumcheck.Spec.OracleStatement R (k + k) 2 () := by
  refine ⟨roundPolyFin R c l point V, ?_⟩
  rw [mem_restrictDegree_iff_sup (Fin (k+k)) (roundPolyFin R c l point V) 2]
  intro i
  rw [← degreeOf_def]
  exact degreeOf_roundPolyFin_le R c l point V hV i

/-- The full wiring lemma: if a GKR statement/oracle pair satisfies GKR's `relationRound`,
  then the corresponding sum-check statement/oracle pair (target := `value`, no prior
  challenges, oracle := `roundPolyFinOracle`) satisfies `Sumcheck.Spec.relationRound` at
  round `0`. This is what lets `innerReduction`'s (plain sum-check's) completeness transport
  to GKR. -/
theorem relationRound_to_relationRound {k d : ℕ} [Nontrivial R]
    (c : Circuit k d) (l : Fin d) (point : Fin k → R) (value : R)
    (V : MvPolynomial (Fin k) R) (hV : ∀ j, degreeOf j V ≤ 1)
    (h : ⟨⟨point, value⟩, ()⟩ ∈ relationRound R d k c l V) :
    ⟨⟨(⟨value, Fin.elim0⟩ : Sumcheck.Spec.StatementRound R (k + k) 0),
       fun (_ : Unit) => roundPolyFinOracle R c l point V hV⟩, ()⟩
      ∈ Sumcheck.Spec.relationRound R (k + k) 2 (D R) 0 := by
  have := Classical.decEq R
  have key := sum_roundPolyFin_eq R c l point V
  simp only [relationRound, Set.mem_ofPred_eq] at h
  change ∑ z ∈ Fintype.piFinset (fun _ : Fin (k + k) ↦ (Finset.univ.map (D R))),
      MvPolynomial.eval (Fin.append (Fin.elim0 : Fin 0 → R) z ∘ Fin.cast (by omega))
        (roundPolyFin R c l point V) = value
  have hcast : ∀ z : Fin (k+k) → R,
      MvPolynomial.eval (Fin.append (Fin.elim0 : Fin 0 → R) z ∘ Fin.cast (by omega))
        (roundPolyFin R c l point V) =
      MvPolynomial.eval z (roundPolyFin R c l point V) := by
    intro z
    have hfun : Fin.append (Fin.elim0 : Fin 0 → R) z ∘ Fin.cast (by omega) = z := by
      rw [Fin.elim0_append]
      funext i
      simp [Fin.cast_cast]
    rw [hfun]
  simp_rw [hcast]
  rw [key, ← h]



noncomputable def innerReduction {k : ℕ} [Nontrivial R] [DecidableEq R] [SampleableType R] :
    Reduction []ₒ
      (Sumcheck.Spec.StatementRound R (k + k) 0 × ∀ i, Sumcheck.Spec.OracleStatement R (k + k) 2 i)
      Unit
      (Sumcheck.Spec.StatementRound R (k + k) (Fin.last (k + k)) ×
        ∀ i, Sumcheck.Spec.OracleStatement R (k + k) 2 i)
      Unit
      (Sumcheck.Spec.pSpec R 2 (k + k)) :=
  Sumcheck.Spec.reduction R 2 (D R) (k + k) []ₒ

variable {σ : Type} {init : ProbComp σ}
    {impl : QueryImpl ([]ₒ : OracleSpec PEmpty) (StateT σ ProbComp)}

/-- `innerReduction` inherits plain sum-check's perfect completeness verbatim, because it *is*
plain sum-check. -/
theorem innerReduction_perfectCompleteness {k : ℕ} [Nontrivial R] [DecidableEq R]
    [SampleableType R] :
    (innerReduction R (k := k)).perfectCompleteness init impl
      (Sumcheck.Spec.relationRound R (k + k) 2 (D R) 0)
      (Sumcheck.Spec.relationRound R (k + k) 2 (D R) (Fin.last (k + k))) :=
  Sumcheck.Spec.reduction_perfectCompleteness R 2 (D R) (k + k) []ₒ

/-- Helper 1 (pure algebra): once sum-check's final claim is stripped down to a bare
  equation, evaluating `roundPolyFin` at a point is the wiring formula evaluated at the
  two halves of that point. No `Set`/membership packaging is involved here. -/
theorem output_relation_to_wiring_identity {k d : ℕ}
    (c : Circuit k d) (l : Fin d) (point : Fin k → R) (target : R)
    (challenges : Fin (k + k) → R) (V : MvPolynomial (Fin k) R)
    (h : MvPolynomial.eval challenges (roundPolyFin R c l point V) = target) :
    target =
      MvPolynomial.eval (Sum.elim point (Sum.elim (challenges ∘ (finSumFinEquiv ∘ Sum.inl))
          (challenges ∘ (finSumFinEquiv ∘ Sum.inr)))) (addPredMLE R c l) *
        (MvPolynomial.eval (challenges ∘ (finSumFinEquiv ∘ Sum.inl)) V
          + MvPolynomial.eval (challenges ∘ (finSumFinEquiv ∘ Sum.inr)) V)
      + MvPolynomial.eval (Sum.elim point (Sum.elim (challenges ∘ (finSumFinEquiv ∘ Sum.inl))
          (challenges ∘ (finSumFinEquiv ∘ Sum.inr)))) (mulPredMLE R c l) *
        (MvPolynomial.eval (challenges ∘ (finSumFinEquiv ∘ Sum.inl)) V
          * MvPolynomial.eval (challenges ∘ (finSumFinEquiv ∘ Sum.inr)) V) := by
  rw [← h]
  unfold roundPolyFin
  rw [eval_rename]
  have : (challenges ∘ ⇑finSumFinEquiv) =
      Sum.elim (challenges ∘ (finSumFinEquiv ∘ Sum.inl))
        (challenges ∘ (finSumFinEquiv ∘ Sum.inr)) := by
    funext i
    cases i with
    | inl i => rfl
    | inr i => rfl
  rw [this]
  exact roundPoly_eval_eq R c l point _ _ V

/-- Helper 2 (pure bookkeeping): at the final round the leftover cube has dimension `0`,
  so sum-check's "sum over the cube" degenerates to a single evaluation at the challenge
  point. This is what peels the membership statement down to a bare equation. -/
theorem sumcheck_output_mem_to_eval {k : ℕ} [Nontrivial R]
    (target : R) (challenges : Fin (k + k) → R)
    (polyOracle : ∀ _ : Unit, Sumcheck.Spec.OracleStatement R (k + k) 2 ())
    (h : ⟨⟨⟨target, challenges⟩, polyOracle⟩, ()⟩ ∈
      Sumcheck.Spec.relationRound R (k + k) 2 (D R) (Fin.last (k + k))) :
    MvPolynomial.eval challenges (polyOracle ()).val = target := by
  simp only [Sumcheck.Spec.relationRound, Set.mem_ofPred_eq] at h
  have hempty : IsEmpty (Fin (k + k - (Fin.last (k + k) : Fin (k + k + 1)))) := by
    constructor
    intro i
    have := i.2
    simp only [Fin.val_last] at this
    omega
  rw [Fintype.piFinset_of_isEmpty] at h
  have hsingle :
      (Finset.univ : Finset (Fin (k + k - (Fin.last (k + k) : Fin (k + k + 1))) → R)) = {default} :=
    Finset.eq_singleton_iff_unique_mem.mpr
      ⟨Finset.mem_univ _, fun x _ => Subsingleton.elim x default⟩
  rw [hsingle, Finset.sum_singleton] at h
  rw [← h]
  have hfun : challenges =
      Fin.append challenges (default : Fin (k + k - (Fin.last (k + k) : Fin (k + k + 1))) → R)
        ∘ Fin.cast (by simp) := by
    funext i
    rw [Function.comp_apply,
      show Fin.cast (by simp : k + k = k + k + (k + k - (Fin.last (k + k) : Fin (k + k + 1)))) i
        = Fin.castAdd (k + k - (Fin.last (k + k) : Fin (k + k + 1))) i from Fin.ext rfl,
      Fin.append_left]
  conv_lhs => rw [hfun]

/--
When we run sumcheck, and it accepts, we are left with a gkr instance to prove
i.e. when we run sumcheck we are left with this equation which reduces to two singular points
-/
theorem relationRound_output_to_wiring_identity {k d : ℕ} [Nontrivial R]
    (c : Circuit k d) (l : Fin d) (point : Fin k → R) (V : MvPolynomial (Fin k) R)
    (target : R) (challenges : Fin (k + k) → R)
    (hV : roundPolyFin R c l point V ∈ MvPolynomial.restrictDegree (Fin (k + k)) R 2)
    -- roundPolyFin evaluated at challenges = target
    (h : ⟨⟨⟨target, challenges⟩, fun (_ : Unit) => (⟨roundPolyFin R c l point V, hV⟩ :
        Sumcheck.Spec.OracleStatement R (k + k) 2 ())⟩, ()⟩ ∈
      Sumcheck.Spec.relationRound R (k + k) 2 (D R) (Fin.last (k + k))) :
    target =
      MvPolynomial.eval (Sum.elim point (Sum.elim (challenges ∘ (finSumFinEquiv ∘ Sum.inl))
          (challenges ∘ (finSumFinEquiv ∘ Sum.inr)))) (addPredMLE R c l) *
        (MvPolynomial.eval (challenges ∘ (finSumFinEquiv ∘ Sum.inl)) V
          + MvPolynomial.eval (challenges ∘ (finSumFinEquiv ∘ Sum.inr)) V)
      + MvPolynomial.eval (Sum.elim point (Sum.elim (challenges ∘ (finSumFinEquiv ∘ Sum.inl))
          (challenges ∘ (finSumFinEquiv ∘ Sum.inr)))) (mulPredMLE R c l) *
        (MvPolynomial.eval (challenges ∘ (finSumFinEquiv ∘ Sum.inl)) V
          * MvPolynomial.eval (challenges ∘ (finSumFinEquiv ∘ Sum.inr)) V) :=
  output_relation_to_wiring_identity R c l point target challenges V
    (sumcheck_output_mem_to_eval R target challenges
      (fun (_ : Unit) => (⟨roundPolyFin R c l point V, hV⟩ :
        Sumcheck.Spec.OracleStatement R (k + k) 2 ())) h)

-- The line through two points (`MvPolynomial.line`), the restriction of a multilinear
-- polynomial to it (`MvPolynomial.restrictToLine`), and the accompanying degree bound now
-- live in `ArkLib.Data.MvPolynomial.LineRestriction` — they are generic, with no GKR content.


/-!
The following few lemmas are concerned with the correctnes of the collapse
of the 2 claims to 1 collapse
so the prover collapses two claims about the previous layer into one
if the claims are about x and y, the prover computes
l(t) = x + t * (y - x), so we have l(0) = x and l(1) = y
so the verifier can pick those two things and then send a random challenge
-/

/--
The verifier's check, re-expressed in terms of the polynomial the prover sent,
since q(0) = V(x) and q(1) = V(y) — where q is that polynomial.
-/
theorem combine_check_passes {k d : ℕ} (c : Circuit k d) (l : Fin d)
    (point : Fin k → R) (V : MvPolynomial (Fin k) R) (target : R) (x y : Fin k → R)
    (h : target =
      MvPolynomial.eval (Sum.elim point (Sum.elim x y)) (addPredMLE R c l)
          * (MvPolynomial.eval x V + MvPolynomial.eval y V)
        + MvPolynomial.eval (Sum.elim point (Sum.elim x y)) (mulPredMLE R c l)
          * (MvPolynomial.eval x V * MvPolynomial.eval y V)) :
    target =
      MvPolynomial.eval (Sum.elim point (Sum.elim x y)) (addPredMLE R c l)
          * ((restrictToLine x y V).eval 0 + (restrictToLine x y V).eval 1)
        + MvPolynomial.eval (Sum.elim point (Sum.elim x y)) (mulPredMLE R c l)
          * ((restrictToLine x y V).eval 0 * (restrictToLine x y V).eval 1) := by
  simpa using h

/-- **Combine step, the surviving claim.** After the verifier sends a random challenge `r`,
the two claims `V x` and `V y` have been replaced by the single claim that `V`, evaluated at
the point `line x y r`, equals `q r` — where `q` is the polynomial the prover already sent.

The verifier can compute `q r` itself, and `line x y r` from `x`, `y`, `r`. So this is a
well-formed claim about `V` at *one* point, ready to become the next layer's input. -/
theorem combine_output_claim {k : ℕ} (x y : Fin k → R) (V : MvPolynomial (Fin k) R) (r : R) :
    MvPolynomial.eval (line x y r) V = (restrictToLine x y V).eval r :=
  (eval_restrictToLine x y V r).symm



namespace Combine

/-!
## The combine step

Sum-check leaves two claims on the table, about `V x*` and `V y*`. Carrying both would double
the number of claims at every layer, so they are folded back into one: the prover sends `V`
restricted to the line through `x*` and `y*`, and the verifier samples a single point on it.
-/

/-- The `x` half of a sum-check challenge point. -/
def leftHalf {k : ℕ} (ch : Fin (k + k) → R) : Fin k → R := ch ∘ (finSumFinEquiv ∘ Sum.inl)

/-- The `y` half of a sum-check challenge point. -/
def rightHalf {k : ℕ} (ch : Fin (k + k) → R) : Fin k → R := ch ∘ (finSumFinEquiv ∘ Sum.inr)

/-- Input statement for the combine step: the layer-`l` claim the inner sum-check was run on,
together with the challenge point that sum-check ended at. -/
structure StmtIn (k : ℕ) (l : Fin (n + 1)) where
  /-- The layer-`l` claim: the point `z` and the target value. -/
  claim : GKRStatement R n k l
  /-- The sum-check challenge point; `x*` and `y*` are its two halves. -/
  challenges : Fin (k + k) → R

/-- Prover sends a univariate polynomial of degree ≤ `k`; verifier replies with a challenge. -/
@[reducible] def pSpec (k : ℕ) : ProtocolSpec 2 :=
  ⟨!v[.P_to_V, .V_to_P], !v[R⦃≤ (k : WithBot ℕ)⦄[X], R]⟩

variable {k : ℕ} (c : Circuit k n) (l : Fin n) (V : MvPolynomial (Fin k) R)

/-- The wiring identity at the sum-check challenge point — the conclusion of
`relationRound_output_to_wiring_identity`. -/
def relIn : Set (StmtIn R n k l.castSucc × Unit) :=
  { ⟨⟨⟨point, target⟩, ch⟩, _⟩ |
    target =
      MvPolynomial.eval (Sum.elim point (Sum.elim (leftHalf R ch) (rightHalf R ch)))
          (addPredMLE R c l)
        * (MvPolynomial.eval (leftHalf R ch) V + MvPolynomial.eval (rightHalf R ch) V)
      + MvPolynomial.eval (Sum.elim point (Sum.elim (leftHalf R ch) (rightHalf R ch)))
          (mulPredMLE R c l)
        * (MvPolynomial.eval (leftHalf R ch) V * MvPolynomial.eval (rightHalf R ch) V) }

/-- The single surviving claim, phrased as a layer-`l+1` GKR statement — exactly the shape
the next layer consumes. -/
def relOut : Set (GKRStatement R n k l.succ × Unit) :=
  { ⟨⟨point', value'⟩, _⟩ | MvPolynomial.eval point' V = value' }

variable {ι : Type} (oSpec : OracleSpec ι)
variable {σ' : Type} {init' : ProbComp σ'} {impl' : QueryImpl oSpec (StateT σ' ProbComp)}

/-- The polynomial the honest prover sends: `V` restricted to the line through `x*` and `y*`,
bundled with its degree bound (`natDegree_restrictToLine_le`). -/
noncomputable def sentPoly (hV : ∀ i, degreeOf i V ≤ 1) (ch : Fin (k + k) → R) :
    R⦃≤ (k : WithBot ℕ)⦄[X] :=
  ⟨restrictToLine (leftHalf R ch) (rightHalf R ch) V, by
    rw [Polynomial.mem_degreeLE, ← Polynomial.natDegree_le_iff_degree_le]
    exact natDegree_restrictToLine_le _ _ V hV⟩

/-- The honest prover: sends `V` restricted to the line, receives the challenge `r`, and
outputs the layer-`l+1` claim `V (line x* y* r) = q r`. It uses `V`, which the verifier never
sees — note it does not even take the circuit `c` as an argument. -/
noncomputable def prover (hV : ∀ i, degreeOf i V ≤ 1) :
    Prover oSpec (StmtIn R n k l.castSucc) Unit (GKRStatement R n k l.succ) Unit (pSpec R k) where
  PrvState
  | 0 => StmtIn R n k l.castSucc
  | 1 => StmtIn R n k l.castSucc
  | 2 => StmtIn R n k l.castSucc × R
  input := Prod.fst
  sendMessage
  | ⟨0, _⟩ => fun s => pure (sentPoly R V hV s.challenges, s)
  | ⟨1, h⟩ => nomatch h
  receiveChallenge
  | ⟨0, h⟩ => nomatch h
  | ⟨1, _⟩ => fun s => pure fun r => (s, r)
  output := fun ⟨s, r⟩ =>
    pure (⟨line (leftHalf R s.challenges) (rightHalf R s.challenges) r,
      (sentPoly R V hV s.challenges).val.eval r⟩, ())

/-- The verifier: reads the prover's polynomial `q` off the transcript, checks the wiring
identity using only `q 0` and `q 1`, reads the challenge `r`, and outputs the layer-`l+1`
claim. It never touches `V` — only the public wiring `c`, `l`. -/
noncomputable def verifier [DecidableEq R] :
    Verifier oSpec (StmtIn R n k l.castSucc) (GKRStatement R n k l.succ) (pSpec R k) where
  verify := fun s transcript => do
    let q : R⦃≤ (k : WithBot ℕ)⦄[X] := transcript 0
    guard (s.claim.value =
      MvPolynomial.eval (Sum.elim s.claim.point
          (Sum.elim (leftHalf R s.challenges) (rightHalf R s.challenges)))
          (addPredMLE R c l) * (q.val.eval 0 + q.val.eval 1)
      + MvPolynomial.eval (Sum.elim s.claim.point
          (Sum.elim (leftHalf R s.challenges) (rightHalf R s.challenges)))
          (mulPredMLE R c l) * (q.val.eval 0 * q.val.eval 1))
    let r : R := transcript 1
    pure ⟨line (leftHalf R s.challenges) (rightHalf R s.challenges) r, q.val.eval r⟩

/-- The combine-step reduction: two claims about `V` in, one layer-`l+1` claim out. -/
noncomputable def reduction [DecidableEq R] (hV : ∀ i, degreeOf i V ≤ 1) :
    Reduction oSpec (StmtIn R n k l.castSucc) Unit (GKRStatement R n k l.succ) Unit
      (pSpec R k) where
  prover := prover R n l V oSpec hV
  verifier := verifier R n c l oSpec

/-- `R` is sampleable, so the challenge round of `pSpec` is too. Sum-check gets this instance
from its `append` lemmas; we build `pSpec` directly, so we supply it by hand. -/
instance instSampleableChallenge [SampleableType R] :
    ∀ i, SampleableType ((pSpec R k).Challenge i)
  | ⟨0, h⟩ => absurd h (by rw [show (pSpec R k).dir 0 = Direction.P_to_V from rfl]; simp)
  | ⟨1, _⟩ => (inferInstance : SampleableType R)

--  Thsi is written by AI and modeled on Sumcheck.Spec.Simple.reduction_perfectCompleteness
theorem reduction_perfectCompleteness [DecidableEq R] [SampleableType R]
    (hV : ∀ i, degreeOf i V ≤ 1) :
    (reduction R n c l V oSpec hV).perfectCompleteness init' impl'
      (relIn R n c l V) (relOut R n l V) := by
  simp only [Reduction.perfectCompleteness, Reduction.completeness, ENNReal.coe_zero, tsub_zero]
  intro s () hValid
  have optionT_lift_eq_map {M : Type → Type} [Monad M] [LawfulMonad M]
      {α : Type} (mx : M α) :
      (OptionT.lift mx : OptionT M α) = OptionT.mk (some <$> mx) := by
    apply OptionT.ext
    change (monadLift mx : OptionT M α).run = some <$> mx
    rw [OptionT.run_monadLift, monadLift_self]
  simp only [relIn, Set.mem_ofPred_eq] at hValid
  -- restate the hypothesis in the `q 0`/`q 1` form the verifier actually checks
  have hCheck := combine_check_passes R c l s.claim.point V s.claim.value
    (leftHalf R s.challenges) (rightHalf R s.challenges) hValid
  have hCheck' : s.claim.value =
      MvPolynomial.eval (Sum.elim s.claim.point
          (Sum.elim (leftHalf R s.challenges) (rightHalf R s.challenges))) (addPredMLE R c l)
        * ((sentPoly R V hV s.challenges).val.eval 0 + (sentPoly R V hV s.challenges).val.eval 1)
      + MvPolynomial.eval (Sum.elim s.claim.point
          (Sum.elim (leftHalf R s.challenges) (rightHalf R s.challenges))) (mulPredMLE R c l)
        * ((sentPoly R V hV s.challenges).val.eval 0 * (sentPoly R V hV s.challenges).val.eval 1) :=
    hCheck
  -- unfold the honest execution
  simp only [reduction, Reduction.run, Prover.run, Verifier.run, prover, verifier,
    Prover.runToRound, Prover.processRound, Fin.induction_two, pSpec,
    bind_pure_comp]
  -- round 0 is `P_to_V`, round 1 is `V_to_P`; the other cases are impossible
  split <;> rename_i hDir0
  · exact absurd hDir0 (by decide)
  try simp only [pure_bind]
  split <;> rename_i hDir1
  swap
  · exact absurd hDir1 (by decide)
  -- the verifier's `guard` succeeds, by `hCheck`
  simp only [MonadLift.monadLift, liftM, monadLift, MonadLiftT.monadLift,
    OracleComp.liftComp_pure, pure_bind, map_pure,
    bind_pure_comp, Transcript.concat,
    guard, optionT_lift_eq_map, OptionT.mk]
  -- probability 1 splits into: never fails, and every output is good
  rw [ge_iff_le, one_le_probEvent_iff, probEvent_eq_one_iff]
  refine ⟨?_, ?_⟩
  -- ## the execution never fails
  · rw [OptionT.probFailure_eq]
    simp only [probFailure_eq_zero, zero_add]
    apply probOutput_eq_zero_of_not_mem_support
    simp only [OptionT.run, support_bind, Set.mem_iUnion, not_exists]
    intro st _ hmem
    simp only [StateT.run'_eq, support_map, Set.mem_image] at hmem
    obtain ⟨⟨_, s'⟩, hmem, rfl⟩ := hmem
    erw [simulateQ_bind] at hmem
    erw [StateT.run_bind] at hmem
    rw [mem_support_bind_iff] at hmem
    obtain ⟨⟨x, s''⟩, hx, hs⟩ := hmem
    erw [simulateQ_map] at hx
    rw [StateT.run_map] at hx
    simp only [support_map, Set.mem_image] at hx
    obtain ⟨⟨val, s₀⟩, hval, heq⟩ := hx
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
    erw [simulateQ_bind] at hs
    erw [StateT.run_bind] at hs
    rw [mem_support_bind_iff] at hs
    obtain ⟨⟨y, s'''⟩, hy, hs⟩ := hs
    erw [simulateQ_map] at hy
    erw [simulateQ_map] at hy
    rw [StateT.run_map] at hy
    simp only [support_map, Set.mem_image] at hy
    obtain ⟨⟨val2, s₁⟩, hval2, heq2⟩ := hy
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq2
    dsimp only [] at hs
    rcases val2 with _ | out
    · simp only [Option.getM] at hs
      erw [simulateQ_pure] at hs
      simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hs
      erw [simulateQ_bind] at hval
      erw [StateT.run_bind] at hval
      rw [mem_support_bind_iff] at hval
      obtain ⟨⟨chal_res, s₂⟩, hchal, hval⟩ := hval
      erw [simulateQ_map] at hval
      rw [StateT.run_map] at hval
      simp only [support_map, Set.mem_image] at hval
      obtain ⟨⟨valp, sp⟩, hvalp, heqp⟩ := hval
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj heqp
      -- v4.33: the `pure`-tail no longer needs peeling separately; one map-peel suffices
      erw [simulateQ_map] at hchal
      erw [StateT.run_map] at hchal
      simp only [support_map, Set.mem_image] at hchal
      obtain ⟨⟨inner_val, s_inner⟩, hinner, heq_c⟩ := hchal
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq_c
      simp only [QueryImpl.addLift_def,
        OracleQuery.input_query,
        Fin.snoc] at hval2
      norm_num at hval2
      simp only [sentPoly] at hval2
      erw [if_pos hCheck] at hval2
      simp only [map_pure] at hval2
      erw [simulateQ_pure] at hval2
      simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hval2
      exact absurd (congr_arg Prod.fst hval2) (by simp)
    · simp only [Option.getM] at hs
      erw [simulateQ_pure] at hs
      simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hs
      exact absurd (congr_arg Prod.fst hs) (by simp)
  -- ## every possible output is correct
  · intro x hx
    rw [OptionT.mem_support_iff] at hx
    simp only [OptionT.run, support_bind, Set.mem_iUnion] at hx
    obtain ⟨st, _, hx⟩ := hx
    simp only [StateT.run'_eq, support_map, Set.mem_image] at hx
    obtain ⟨⟨_, s'⟩, hx, rfl⟩ := hx
    erw [simulateQ_bind] at hx
    erw [StateT.run_bind] at hx
    rw [mem_support_bind_iff] at hx
    obtain ⟨⟨x_opt, s''⟩, hx_first, hx_rest⟩ := hx
    erw [simulateQ_map] at hx_first
    rw [StateT.run_map] at hx_first
    simp only [support_map, Set.mem_image] at hx_first
    obtain ⟨⟨val, s₀⟩, hval, heq⟩ := hx_first
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
    erw [simulateQ_bind] at hx_rest
    erw [StateT.run_bind] at hx_rest
    rw [mem_support_bind_iff] at hx_rest
    obtain ⟨⟨y, s'''⟩, hy, hx_rest⟩ := hx_rest
    erw [simulateQ_map] at hy
    erw [simulateQ_map] at hy
    rw [StateT.run_map] at hy
    simp only [support_map, Set.mem_image] at hy
    obtain ⟨⟨val2, s₁⟩, hval2, heq2⟩ := hy
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq2
    dsimp only [] at hx_rest
    rcases val2 with _ | out
    · simp only [Option.getM] at hx_rest
      erw [simulateQ_pure] at hx_rest
      simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hx_rest
      exact absurd (congr_arg Prod.fst hx_rest) (by simp)
    · simp only [Option.getM] at hx_rest
      erw [simulateQ_pure] at hx_rest
      simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hx_rest
      obtain ⟨rfl, rfl⟩ := hx_rest
      erw [simulateQ_bind] at hval
      erw [StateT.run_bind] at hval
      rw [mem_support_bind_iff] at hval
      obtain ⟨⟨chal_res, s₂⟩, hchal, hval⟩ := hval
      erw [simulateQ_map] at hval
      rw [StateT.run_map] at hval
      simp only [support_map, Set.mem_image] at hval
      obtain ⟨⟨valp, sp⟩, hvalp, heqp⟩ := hval
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj heqp
      -- v4.33: the `pure`-tail no longer needs peeling separately; one map-peel suffices
      erw [simulateQ_map] at hchal
      erw [StateT.run_map] at hchal
      simp only [support_map, Set.mem_image] at hchal
      obtain ⟨⟨inner_val, s_inner⟩, hinner, heq_c⟩ := hchal
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq_c
      simp only [QueryImpl.addLift_def,
        QueryImpl.simulateQ_add_liftComp_left, simulateQ_pure,
        StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hvalp
      obtain ⟨rfl, rfl⟩ := hvalp
      simp only [QueryImpl.addLift_def,
        OracleQuery.input_query,
        Fin.snoc] at hval2
      norm_num at hval2
      simp only [sentPoly] at hval2
      erw [if_pos hCheck] at hval2
      simp only [map_pure] at hval2
      erw [simulateQ_pure] at hval2
      simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff,
        Prod.mk.injEq, Option.some.injEq] at hval2
      obtain ⟨hout, -⟩ := hval2
      subst hout
      refine ⟨?_, ?_⟩
      -- the surviving claim is true
      · exact (eval_restrictToLine _ _ V _).symm
      -- prover and verifier agree: the prover recomputes the polynomial it sent
      · rfl

-- It carries `point` around the inner sum-check: sum-check never sees `point` (it was
-- substituted into `roundPolyFin` beforehand), but the combine step needs it, so the lens
-- holds it on the side and re-attaches it to sum-check's output.

/-- The statement lens carrying `point` around the inner sum-check.

`toFunA` (project): from the layer-`l` claim `(point, value)`, build sum-check's starting
statement — target `value`, no challenges yet, and `roundPolyFin` as the oracle. `point` is
*dropped*: it has already been substituted into `roundPolyFin`, and sum-check has no use for it.

`toFunB` (lift): sum-check hands back `(target', challenges)` with no `point` in sight, so we
take `point` from the **outer input** — which `toFunB` also receives — and reassemble the
combine step's input statement. This is the whole trick: `point` travels *around* the
sum-check rather than through it. -/
noncomputable def stmtLens [Nontrivial R] (hV : ∀ i, degreeOf i V ≤ 1) :
    Statement.Lens
      (GKRStatement R n k l.castSucc)
      (StmtIn R n k l.castSucc)
      (Sumcheck.Spec.StatementRound R (k + k) 0 ×
        ∀ i, Sumcheck.Spec.OracleStatement R (k + k) 2 i)
      (Sumcheck.Spec.StatementRound R (k + k) (Fin.last (k + k)) ×
        ∀ i, Sumcheck.Spec.OracleStatement R (k + k) 2 i) where
  toFunA := fun gkrStmt =>
    ⟨⟨gkrStmt.value, Fin.elim0⟩, fun _ => roundPolyFinOracle R c l gkrStmt.point V hV⟩
  toFunB := fun gkrStmt innerOut =>
    ⟨⟨gkrStmt.point, innerOut.1.target⟩, innerOut.1.challenges⟩

/-- The context lens: the statement lens above, plus the trivial witness lens (both witnesses
are `Unit`, so there is nothing to transport). -/
noncomputable def ctxLens [Nontrivial R] (hV : ∀ i, degreeOf i V ≤ 1) :
    Context.Lens
      (GKRStatement R n k l.castSucc)
      (StmtIn R n k l.castSucc)
      (Sumcheck.Spec.StatementRound R (k + k) 0 ×
        ∀ i, Sumcheck.Spec.OracleStatement R (k + k) 2 i)
      (Sumcheck.Spec.StatementRound R (k + k) (Fin.last (k + k)) ×
        ∀ i, Sumcheck.Spec.OracleStatement R (k + k) 2 i)
      Unit Unit Unit Unit where
  stmt := stmtLens R n c l V hV
  wit := Witness.Lens.trivial

/-- The inner sum-check, lifted so that it speaks GKR's language: it takes a layer-`l` claim
and produces the combine step's input statement, with `point` carried around it by the lens. -/
noncomputable def liftedInner [Nontrivial R] [DecidableEq R] [SampleableType R]
    (hV : ∀ i, degreeOf i V ≤ 1) :
    Reduction []ₒ
      (GKRStatement R n k l.castSucc) Unit
      (StmtIn R n k l.castSucc) Unit
      (Sumcheck.Spec.pSpec R 2 (k + k)) :=
  (innerReduction R (k := k)).liftContext (ctxLens R n c l V hV)

-- Everything below is AI generated.
-- It glues the two halves of a layer together: the lifted inner sum-check, then the combine
-- step. The oracle-preservation step is discharged by
-- `Sumcheck.Spec.reduction_run_preserves_oracle`
-- (proved in `GKR/SumcheckAux.lean`).

instance lensIsComplete [Nontrivial R] [DecidableEq R] [SampleableType R]
    (hV : ∀ i, degreeOf i V ≤ 1) :
    (ctxLens R n c l V hV).IsComplete
      (relationRound R n k c l V)
      (Sumcheck.Spec.relationRound R (k + k) 2 (D R) 0)
      (relIn R n c l V)
      (Sumcheck.Spec.relationRound R (k + k) 2 (D R) (Fin.last (k + k)))
      ((innerReduction R (k := k)).compatContext (ctxLens R n c l V hV)) where
  proj_complete := by
    rintro ⟨point, value⟩ ⟨⟩ h
    exact relationRound_to_relationRound R c l point value V hV h
  lift_complete := by
    rintro ⟨point, value⟩ ⟨⟩ ⟨⟨target, challenges⟩, oStmt⟩ ⟨⟩ hCompat _ hInner
    -- `hCompat` says this output came from actually running the inner sum-check, whose input
    -- oracle was `roundPolyFinOracle`. Sum-check passes its oracle statement through unchanged
    -- (`Sumcheck.Spec.reduction_run_preserves_oracle`), so the oracle we are handed is ours.
    have hOracle : oStmt = fun _ => roundPolyFinOracle R c l point V hV := by
      obtain ⟨x, hx, hxeq⟩ := hCompat
      have := Sumcheck.Spec.reduction_run_preserves_oracle R 2 (D R) (k + k) []ₒ
        ⟨⟨value, Fin.elim0⟩, fun _ => roundPolyFinOracle R c l point V hV⟩ () x hx
      simp only [Function.comp_apply] at hxeq
      rw [hxeq] at this
      dsimp only at this
      exact this
    subst hOracle
    exact relationRound_output_to_wiring_identity R c l point V target challenges _ hInner


/-- The lifted inner sum-check is complete, stated in GKR's own vocabulary. -/
theorem liftedInner_perfectCompleteness [Nontrivial R] [DecidableEq R] [SampleableType R]
    (hV : ∀ i, degreeOf i V ≤ 1) :
    (liftedInner R n c l V hV).perfectCompleteness init impl
      (relationRound R n k c l V) (relIn R n c l V) :=
  Reduction.liftContext_perfectCompleteness (innerReduction_perfectCompleteness R)

instance instSampleableAppend [SampleableType R] :
    ∀ i, SampleableType ((Sumcheck.Spec.pSpec R 2 (k + k) ++ₚ pSpec R k).Challenge i) :=
  ProtocolSpec.instSampleableTypeChallengeAppend

/-- **One full layer of GKR**: the inner sum-check followed by the combine step. -/
noncomputable def layerReduction [Nontrivial R] [DecidableEq R] [SampleableType R]
    (hV : ∀ i, degreeOf i V ≤ 1) :
    Reduction []ₒ
      (GKRStatement R n k l.castSucc) Unit
      (GKRStatement R n k l.succ) Unit
      (Sumcheck.Spec.pSpec R 2 (k + k) ++ₚ pSpec R k) :=
  (liftedInner R n c l V hV).append (reduction R n c l V []ₒ hV)

/-- **Completeness of one full layer.** A true layer-`l` claim goes in; a true layer-`l+1`
claim comes out. -/
theorem layerReduction_perfectCompleteness [Nontrivial R] [DecidableEq R] [SampleableType R]
    (hV : ∀ i, degreeOf i V ≤ 1) :
    (layerReduction R n c l V hV).perfectCompleteness init impl
      (relationRound R n k c l V) (relOut R n l V) :=
  Reduction.append_perfectCompleteness _ _
    (liftedInner_perfectCompleteness R n c l V hV)
    (reduction_perfectCompleteness R n c l V []ₒ hV)


end Combine

end GKR

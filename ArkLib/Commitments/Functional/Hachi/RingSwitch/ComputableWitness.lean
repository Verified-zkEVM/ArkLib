/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pablo Martín Vinuelas
-/
import ArkLib.Commitments.Functional.Hachi.RingSwitch.Reduction
import CompPoly.Univariate.DivisionCorrectness

/-!
# A computable honest lifted witness

`honestLiftWitness` (`RingSwitch/Completeness.lean`) is the one *essentially* noncomputable step
on Hachi's honest-prover path: the quotient rows are produced by Mathlib's `/ₘ`
(`Presentation.quotient`), then repackaged into the `CPolynomial (ZMod q)` rows `LiftedWitness`
stores through the noncomputable `Polynomial.toImpl`. Since the lifted witness is carried by
every later link and revealed by the terminal message, nothing downstream can be run until this
is fixed.

The fix changes no definition and no statement: the division is synthetic division by a monic
divisor, which CompPoly implements as `CPolynomial.divByMonic` with
`divByMonic_toPoly_eq_divByMonic` as its correctness statement, operating on the canonical
coefficient arrays directly — no Mathlib polynomial is ever built.

So `honestLiftWitnessC` is a computable `def` at the *same signature and same type* as generic
`Lift.honestWitness` at `cyclotomicPresentation` — which is exactly what Hachi's
`honestLiftWitness` (`RingSwitch/Completeness.lean`) is defined to be — and
`honestLiftWitnessC_eq_honestWitness` says they are equal. The noncomputable original stays as
the spec-side definition, every theorem about it applies verbatim, and `liftReduction` is
re-pointed at the computable twin one file up, transferring completeness through the agreement
lemma. This file sits *below* `Completeness.lean` in the import graph so that it can.

## Main definitions

* `cQuotient` / `cQuotient_toPoly` — the computable honest quotient and its agreement with
  `Presentation.quotient` at `cyclotomicPresentation`.
* `honestLiftWitnessC` / `honestLiftWitnessC_eq_honestWitness` — the computable honest lifted
  witness and its agreement with generic `Lift.honestWitness`.

## References

* [Nguyen, N. K., O'Rourke, G., and Zhang, J., *Hachi: Efficient Lattice-Based Multilinear
    Polynomial Commitments over Extension Fields*][NOZ26]
-/

namespace ArkLib.Lattices.Ajtai.InnerOuter

open CompPoly ArkLib.Lattices ArkLib.Lattices.CyclotomicModulus
open RingSwitching RingSwitching.Lift

variable {q : ℕ} [NeZero q] [Fact (Nat.Prime q)] [BEq (ZMod q)] [LawfulBEq (ZMod q)]
  (Φ : CyclotomicModulus (ZMod q)) [IsCyclotomic Φ]
variable {n μ : ℕ}

omit [NeZero q] in
/-- The cyclotomic modulus is monic in CompPoly's `Bool`-valued sense — the hypothesis
`CPolynomial.divByMonic`'s correctness statement asks for, transported from
`IsCyclotomic.monic` across `monic_toPoly_iff`. -/
theorem cModulus_monic : Φ.φ.monic :=
  (CPolynomial.monic_toPoly_iff Φ.φ).mpr IsCyclotomic.monic

/-- **The computable honest quotient** of row `i`: synthetic division of the lifted row defect
`∑ⱼ Mᵢⱼ·zⱼ − yᵢ` by the modulus, on canonical coefficient arrays. The numerator is the
already-computable `cRowSum` (`RingSwitch/Reduction.lean`) minus the canonical representative of
`yᵢ`; the division is CompPoly's `divByMonic`, which the monic modulus licenses. -/
def cQuotient (s : RlinStatement Φ n μ) (z : ArkLib.Lattices.PolyVec (Rq Φ) μ) (i : Fin n) :
    CPolynomial (ZMod q) :=
  (cRowSum Φ s z i - (s.yvec i).1).divByMonic Φ.φ

omit [NeZero q] in
/-- **Agreement of the computable quotient with the presentation's.** Chains CompPoly's division
correctness (`divByMonic_toPoly_eq_divByMonic`, at `cModulus_monic`) with `toPoly`'s additivity;
the two sides' numerators are the same polynomial because `cyclotomicPresentation`'s `rep` is
`toPoly` of the canonical representative and its `rowSum` is `rowSum_eq_sum_toPoly`. -/
theorem cQuotient_toPoly (s : RlinStatement Φ n μ)
    (z : ArkLib.Lattices.PolyVec (Rq Φ) μ) (i : Fin n) :
    (cQuotient Φ s z i).toPoly
      = (cyclotomicPresentation Φ).quotient s.M z s.yvec i := by
  rw [cQuotient, CPolynomial.divByMonic_toPoly_eq_divByMonic _ _ (cModulus_monic Φ),
    CPolynomial.toPoly_sub, Presentation.quotient]
  congr 1
  · rw [show (cRowSum Φ s z i).toPoly = rowSum Φ s z i from rfl,
      rowSum_eq_sum_toPoly, Presentation.rowSum]
    rfl

/-- **The computable honest lifted witness.** Same signature, same type, and — by
`honestLiftWitnessC_eq_honestWitness` — the same value as the spec witness; only the route to
the quotient rows differs. The degree field is transported from the spec side, which costs
nothing at runtime: `hρ` is a `Prop` and is erased by compilation. -/
def honestLiftWitnessC (hd : 0 < Φ.φ.natDegree)
    (s : RlinStatement Φ n μ) (z : ArkLib.Lattices.PolyVec (Rq Φ) μ) : LiftedWitness Φ μ n where
  z := z
  ρ := fun i => cQuotient Φ s z i
  hρ := fun i => by
    have := isPresentation_cyclotomic Φ hd
    rw [cQuotient_toPoly]
    have h := (cyclotomicPresentation Φ).natDegree_quotient_le s.M z s.yvec i
    rw [cyclotomicPresentation_modulus_natDegree] at h
    omega

omit [NeZero q] [IsCyclotomic Φ] in
/-- A lifted witness is determined by its two data fields: the degree bound is a `Prop` and
comes along by proof irrelevance. Local to this file — the only thing it is for is stating the
agreement lemma below without destructuring both sides by hand. -/
private theorem liftedWitness_eq_of {w w' : LiftedWitness Φ μ n}
    (hz : w.z = w'.z) (hρ : w.ρ = w'.ρ) : w = w' := by
  cases w; cases w'; cases hz; cases hρ; rfl

omit [NeZero q] in
/-- **The agreement lemma**: the computable honest lifted witness *is* the generic honest
witness at the cyclotomic presentation — hence, by `honestLiftWitness`'s definition, Hachi's own
honest lifted witness. Field by field: `z` by `rfl`, `ρ` by injectivity of `toPoly` through
`cQuotient_toPoly` against `toPoly_mk_toImpl`, and the propositional `hρ` by proof irrelevance.
Every completeness theorem stated at the spec witness therefore transfers by rewriting; nothing
is restated or weakened. -/
theorem honestLiftWitnessC_eq_honestWitness (hd : 0 < Φ.φ.natDegree)
    (s : RlinStatement Φ n μ) (z : ArkLib.Lattices.PolyVec (Rq Φ) μ) :
    have := isPresentation_cyclotomic Φ hd
    honestLiftWitnessC Φ hd s z
      = Lift.honestWitness (cyclotomicPresentation Φ) (fun s => s.M) (fun s => s.yvec)
          (cyclotomicPresentation_modulus_natDegree Φ) s z := by
  have := isPresentation_cyclotomic Φ hd
  refine liftedWitness_eq_of Φ rfl (funext fun i => ?_)
  have h : (cQuotient Φ s z i).toPoly
      = ((Lift.honestWitness (cyclotomicPresentation Φ) (fun s => s.M) (fun s => s.yvec)
          (cyclotomicPresentation_modulus_natDegree Φ) s z).ρ i).toPoly := by
    rw [cQuotient_toPoly,
      show ((Lift.honestWitness (cyclotomicPresentation Φ) (fun s => s.M) (fun s => s.yvec)
          (cyclotomicPresentation_modulus_natDegree Φ) s z).ρ i).toPoly
        = (cyclotomicPresentation Φ).quotient s.M z s.yvec i
        from CPolynomial.toPoly_mk_toImpl _]
  exact CPolynomial.toPolyLinearEquiv.injective h

end ArkLib.Lattices.Ajtai.InnerOuter

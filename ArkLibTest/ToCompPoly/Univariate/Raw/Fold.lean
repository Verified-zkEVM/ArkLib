/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ToCompPoly.Univariate.Raw.Fold
import Lean.Compiler.IR

/-! # Padded sum and fraction-fold acceptance checks -/

namespace CompPoly.CPolynomial.Raw.FoldTest

/-- A generic external caller retains coefficient padding through a left fold. -/
def sumCaller {R : Type*} [Zero R] [Add R] (ps : List (Raw R)) : Raw R := sumRaw ps

/-- A generic external caller preserves fresh-factor order through the raw fraction fold. -/
def fractionCaller {R : Type*} [CommSemiring R] (ps : List (FractionPair (Raw R))) :
    FractionPair (Raw R) := fractionSum ps

/-- Three asymmetric affine fractions distinguish cross terms and coefficient positions. -/
def asymmetricPairs : List (FractionPair (Raw ℤ)) :=
  [⟨#[2, 3], #[5, 7]⟩, ⟨#[11, 13], #[17, 19]⟩, ⟨#[23, 29], #[31, 37]⟩]

example : fractionCaller ([] : List (FractionPair (Raw ℤ))) = ⟨#[], #[1]⟩ := rfl

example {R : Type*} [CommSemiring R] (ps : List (FractionPair (Raw R))) :
    FractionPair.map toPoly (fractionCaller ps) =
      FractionPair.sum (ps.map (FractionPair.map toPoly)) :=
  map_toPoly_fractionSum ps

example {R : Type*} [Semiring R] (ps : List (Raw R)) :
    (sumCaller ps).toPoly = (ps.map toPoly).sum := toPoly_sumRaw ps

-- These consumers require the widened owner bounds at a genuinely higher universe.
example {R : Type 1} [Zero R] [Add R] (ps : List (Raw R)) (d : ℕ)
    (hps : ∀ p ∈ ps, p.size ≤ d) : (sumCaller ps).size ≤ d :=
  size_sumRaw_le ps d hps

example {R : Type 1} [CommSemiring R] (ps : List (FractionPair (Raw R)))
    (hps : ∀ p ∈ ps, p.numerator.size ≤ 2 ∧ p.denominator.size ≤ 2) :
    (fractionCaller ps).denominator.size ≤ ps.length + 1 :=
  (size_fractionSum_le ps hps).2

#eval (show IO _ from do
  let s := sumCaller ([#[2, 1], #[-2], #[0, 0, 7]] : List (Raw ℤ))
  let p := fractionCaller asymmetricPairs
  unless s == #[0, 1, 7] && p.numerator == #[4714, 17841, 22400, 9333] &&
      p.denominator == #[2635, 9779, 12041, 4921] do
    throw (IO.userError "incorrect asymmetric coefficient fold")
  pure (s, p))

#eval (show IO _ from do
  let single := fractionCaller ([⟨#[3, 0], #[0, 0]⟩] : List (FractionPair (Raw ℤ)))
  let repeated := fractionCaller
    ([⟨#[1, 0], #[0, 0]⟩, ⟨#[3, 0], #[0, 0]⟩] : List (FractionPair (Raw ℤ)))
  unless single == ⟨#[3, 0], #[0, 0]⟩ && repeated == ⟨#[0, 0, 0], #[0, 0, 0]⟩ do
    throw (IO.userError "zero denominators lost their unnormalized coefficient behavior")
  pure (single, repeated))

-- Large inputs exercise compiled traversals, without a kernel computation proof.
#eval (show IO _ from do
  let s := sumCaller (List.replicate 100000 (#[0, 0] : Raw ℤ))
  let p := fractionCaller (List.replicate 100000 (⟨#[], #[1]⟩ : FractionPair (Raw ℤ)))
  unless s == #[0, 0] && p == ⟨#[], #[1]⟩ do
    throw (IO.userError "large raw coefficient traversal returned incorrect data")
  pure (s, p))

open Lean Elab Command

run_cmd do
  for name in #[``sumRaw, ``fractionCombine, ``fractionSum, ``sumCaller, ``fractionCaller] do
    unless (Lean.IR.findEnvDecl (← getEnv) name).isSome do
      throwError "expected compiler IR for `{name}`"
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``size_C, ``size_smul, ``size_mulPowX, ``size_addRaw, ``size_mulRaw,
      ``size_mulRaw_le, ``toPoly_sumRaw, ``map_toPoly_fractionCombine,
      ``map_toPoly_fractionSum, ``size_sumRaw_le, ``size_fractionSum_le] do
    let axioms ← collectAxioms name
    unless axioms.all allowed.contains do
      throwError "`{name}` depends on unexpected axioms: {axioms}"

end CompPoly.CPolynomial.Raw.FoldTest

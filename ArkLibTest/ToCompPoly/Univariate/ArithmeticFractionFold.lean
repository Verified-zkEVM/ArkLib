/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/
import ArkLib.ToCompPoly.Univariate.ArithmeticFractionFoldCost
import Lean.Compiler.IR

/-! # Executed profiles of padded coefficient folds -/

namespace CompPoly.Arithmetic.FractionFoldTest

open OracleComp OracleSpec

/-- An external caller executes the exact program whose instruction profile is bounded. -/
def fractionCaller {F : Type} [CommSemiring F] [Sub F] [Inv F] [DecidableEq F]
    (ps : List (FractionPair (CPolynomial.Raw F))) : FractionPair (CPolynomial.Raw F) :=
  simulateQ arithmeticAnswer (fractionSum ps)

/-- The sum caller uses the same selected additions as the measured traversal. -/
def sumCaller {F : Type} [Zero F] [Add F] [Sub F] [Mul F] [Inv F] [DecidableEq F]
    (ps : List (CPolynomial.Raw F)) : CPolynomial.Raw F :=
  simulateQ arithmeticAnswer (sumRaw ps)

example {F : Type} [CommSemiring F] [Sub F] [Inv F] [DecidableEq F]
    (ps : List (FractionPair (CPolynomial.Raw F))) :
    fractionCaller ps = CPolynomial.Raw.fractionSum ps := by
  rw [fractionCaller, ← profileArithmetic_fst, profileArithmetic_fractionSum_fst]

example {F : Type} [Zero F] [Add F] [Sub F] [Mul F] [Inv F] [DecidableEq F]
    (ps : List (CPolynomial.Raw F)) : sumCaller ps = CPolynomial.Raw.sumRaw ps := by
  rw [sumCaller, ← profileArithmetic_fst, profileArithmetic_sumRaw_fst]

#eval (show IO _ from do
  let ps : List (FractionPair (CPolynomial.Raw ℚ)) :=
    [⟨#[2, 3], #[5, 7]⟩, ⟨#[11, 13], #[17, 19]⟩, ⟨#[23, 29], #[31, 37]⟩]
  let (p, c) := profileArithmetic (fractionSum ps)
  unless p.numerator == #[4714, 17841, 22400, 9333] &&
      p.denominator == #[2635, 9779, 12041, 4921] &&
      c .add == 52 && c .mul == 34 && c .coefficientRead == 156 && c .metadata == 156 &&
      c .sub == 0 && c .inv == 0 && c .eq == 0 && c .valueRead == 0 && c .nodeRead == 0 do
    throw (IO.userError "incorrect affine fraction circuit or instruction profile")
  pure (p, c .add, c .mul, c .coefficientRead, c .metadata))

-- The same zero polynomial can incur different work as its retained widths are reordered.
#eval (show IO _ from do
  let wide : CPolynomial.Raw ℚ := Array.replicate 8 0
  let small : CPolynomial.Raw ℚ := #[0, 0]
  let (a, ca) := profileArithmetic (sumRaw [wide, small, small, small])
  let (b, cb) := profileArithmetic (sumRaw [small, small, small, wide])
  unless a == wide && b == wide && ca .add == 32 && ca .coefficientRead == 64 &&
      ca .metadata == 41 && cb .add == 14 && cb .coefficientRead == 28 && cb .metadata == 23 do
    throw (IO.userError "padded sum profile ignored its actual prefix widths")
  pure (ca .add, cb .add, ca .metadata, cb .metadata))

#eval (show IO _ from do
  let (p, c) := profileArithmetic (fractionSum ([] : List (FractionPair (CPolynomial.Raw ℚ))))
  unless p == ⟨#[], #[1]⟩ && c .metadata == 1 && c .mul == 0 do
    throw (IO.userError "incorrect empty fraction traversal")
  pure (p, c .metadata))

#eval (show IO _ from do
  let neutral : FractionPair (CPolynomial.Raw ℚ) := ⟨#[], #[1]⟩
  let p := fractionCaller (List.replicate 10000 neutral)
  let s := sumCaller (List.replicate 10000 (#[0, 0] : CPolynomial.Raw ℚ))
  unless p == neutral && s == #[0, 0] do
    throw (IO.userError "large interpreted coefficient traversal returned incorrect data")
  pure (p, s))

open Lean Elab Command

run_cmd do
  for name in #[``sumRawFrom, ``sumRaw, ``fractionCombine, ``fractionSum,
      ``fractionCaller, ``sumCaller] do
    unless (Lean.IR.findEnvDecl (← getEnv) name).isSome do
      throwError "expected compiler IR for `{name}`"
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``profileArithmetic_sumRawFrom_fst, ``profileArithmetic_sumRaw_fst,
      ``fractionSum_nil, ``fractionSum_cons, ``profileArithmetic_fractionSum_fst,
      ``profileArithmetic_sumRawFrom_nil, ``profileArithmetic_sumRawFrom_cons,
      ``profileArithmetic_sumRaw, ``profileArithmetic_sumRawFrom_le, ``profileArithmetic_sumRaw_le,
      ``profileArithmetic_fractionCombine, ``profileArithmetic_fractionSum_nil,
      ``profileArithmetic_fractionSum_cons, ``profileArithmetic_fractionCombine_le,
      ``profileArithmetic_fractionSum_le] do
    let axioms ← collectAxioms name
    unless axioms.all allowed.contains do
      throwError "`{name}` depends on unexpected axioms: {axioms}"

end CompPoly.Arithmetic.FractionFoldTest

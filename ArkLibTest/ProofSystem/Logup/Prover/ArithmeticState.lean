/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/
import ArkLib.ProofSystem.Logup.Prover.ArithmeticState
import ArkLibTest.ProofSystem.Logup.Prover.State
import ArkLib.Data.Probability.KoalaBear
import Lean.Compiler.IR

/-! # Actual measured private initialization, termwise poles, kernel and table folds -/

open CompPoly OracleComp OracleSpec Logup.Prover MvPolynomial
namespace ArithmeticStateTests
open LogupStateTest

def prepared (alpha : F) : Prepared F 2 2 1 :=
  simulateQ arithmeticAnswer (State.prepareProgram (RingHom.id F) alpha cfg.groups data)

theorem prepared_eq (alpha : F) : prepared alpha = LogupStateTest.prepared alpha :=
  State.simulateQ_prepareProgram _ _ cfg _

def initial (alpha : F) : Logup.Prover.State F 2 2 1 :=
  simulateQ arithmeticAnswer (State.startProgram (prepared alpha) (fun _ => 3) (![4, 6]))

theorem initial_eq (alpha : F) : initial alpha = LogupStateTest.initial alpha := by
  rw [initial, State.simulateQ_startProgram, prepared_eq]
  rfl

def finalState : Logup.Prover.State F 2 2 0 :=
  simulateQ arithmeticAnswer (State.foldProgram (initial 2) 5)

theorem measured_cubic : State.polynomial cfg.groups (initial 2) =
    C (2 : F) * X 0 - C (7 : F) * X 0 ^ 2 + C (5 : F) * X 0 ^ 3 := by
  rw [initial_eq]
  exact honest_cubic

theorem measured_fold_coherence : State.polynomial cfg.groups finalState =
    Polynomial.eval (C (5 : F)) (MvPolynomial.finSuccEquiv F 0
      (State.polynomial cfg.groups (initial 2))) := by
  rw [finalState, State.simulateQ_foldProgram]
  exact State.polynomial_fold _ _ _

#eval (show IO _ from do
  let (p, cost) := profileArithmetic
    (State.prepareProgram (RingHom.id F) 2 cfg.groups data)
  unless p.denominator == #v[#v[2, 1], #v[2, 1]] &&
      p.weight == #v[#v[1, 1], #v[-1, -1]] && p.helper == #v[#v[9, 1], #v[8, 16]] &&
      cost .sub == 4 && cost .add == 4 && cost .mul == 4 && cost .inv == 4 &&
      cost .valueRead == 8 && cost .metadata == 8 && cost .eq == 0 &&
      cost .coefficientRead == 0 && cost .nodeRead == 0 do
    throw (IO.userError "measured preparation changed data, helper inversions or E-only profile")
  let (s, startCost) := profileArithmetic (State.startProgram p (fun _ => 3) (![4, 6]))
  unless s.kernel == #v[15, 3] && s.lambda == #v[4, 6] &&
      startCost .mul == 2 && startCost .sub == 1 && startCost .inv == 0 &&
      startCost .valueRead == 0 && startCost .metadata == 0 do
    throw (IO.userError "kernel initializer did not select the measured fast table program")
  let (t, foldCost) := profileArithmetic (State.foldProgram s 5)
  unless t.denominator == #v[#v[14], #v[14]] && t.weight == #v[#v[1], #v[-1]] &&
      t.helper == #v[#v[3], #v[14]] && t.kernel == #v[6] && t.lambda == #v[4, 6] &&
      foldCost .sub == 7 && foldCost .mul == 7 && foldCost .add == 7 &&
      foldCost .valueRead == 14 && foldCost .inv == 0 && foldCost .metadata == 0 do
    throw (IO.userError "state folding changed a retained family or its exact profile")
  unless (prepared 0).helper == #v[#v[0, -1], #v[0, 1]] do
    throw (IO.userError "measured preparation silently repaired or retried a pole")
  pure "measured preparation, kernel and all four folded families passed")


-- Multiple outputs charge a difference per adjacent pair rather than a global complement.
#eval (show IO _ from do
  let s : Logup.Prover.State F 1 1 2 :=
    ⟨⟨#v[#v[2, 2, 2, 2]], #v[#v[1, 1, 1, 1]], #v[#v[9, 9, 9, 9]]⟩,
      #v[3, 3, 3, 3], #v[4]⟩
  let (t, cost) := profileArithmetic (State.foldProgram s 5)
  unless t.denominator == #v[#v[2, 2]] && t.helper == #v[#v[9, 9]] &&
      cost .sub == 8 && cost .mul == 8 && cost .add == 8 && cost .valueRead == 16 do
    throw (IO.userError "state profile miscounted per-pair differences or products")
  pure "two-output fold counts each table and pair")

-- Termwise inversion must preserve the off-pole term even when another denominator is zero.
#eval (show IO _ from do
  let d : Vector (CMlPolynomialEval F 0) 2 := #v[#v[0], #v[1]]
  let w : Vector (CMlPolynomialEval F 0) 2 := #v[#v[5], #v[7]]
  let groups : Vector (List (Fin 2)) 2 := #v[[0, 1, 0], []]
  let (h, cost) := profileArithmetic (State.helperTablesProgram groups d w)
  unless h == #v[#v[7], #v[0]] && cost .inv == 3 && cost .mul == 3 && cost .add == 3 &&
      cost .valueRead == 6 && cost .metadata == 5 && (5 : F) / 0 == 0 do
    throw (IO.userError "helpers folded the fraction before dividing or skipped empty-group work")
  pure h)

-- The generic arithmetic programs use the supplied inverse operation without imposing field laws.
section ArbitraryInverse
local instance : Inv ℤ := ⟨fun _ => 1⟩
#eval (show IO _ from do
  let d : Vector (CMlPolynomialEval ℤ 0) 2 := #v[#v[0], #v[2]]
  let w : Vector (CMlPolynomialEval ℤ 0) 2 := #v[#v[3], #v[5]]
  let h : Vector (CMlPolynomialEval ℤ 0) 1 := simulateQ arithmeticAnswer
    (State.helperTablesProgram (#v[[0, 1]] : Vector (List (Fin 2)) 1) d w)
  unless h == #v[#v[8]] do
    throw (IO.userError "generic helper requests smuggled in inverse laws")
  pure h)
end ArbitraryInverse

namespace Extension
abbrev B := KoalaBear.Field
abbrev E := KoalaBear.Ext6
def f : B →+* E := algebraMap B E
def data (i : Fin 2 × Fin 1) : CMlPolynomialEval B 0 := if i.1 = 0 then #v[0] else #v[1]
def prepared : Prepared E 1 1 0 := simulateQ arithmeticAnswer
  (State.prepareProgram f KoalaBear.ext6Gen #v[[0]] data)
#eval (show IO _ from do
  let p := prepared
  let s := simulateQ arithmeticAnswer (State.startProgram p Fin.elim0 (fun _ => KoalaBear.ext6Gen))
  unless KoalaBear.Ext6.coeffsEquiv.symm (p.denominator[0].get 0) == #v[0, 1, 0, 0, 0, 0] &&
      p.weight == #v[#v[1]] && p.helper[0].get 0 * KoalaBear.ext6Gen == 1 &&
      s.kernel == #v[1] && s.lambda == #v[KoalaBear.ext6Gen] do
    throw (IO.userError "measured state lost genuine base-to-extension alpha or n0 initialization")
  pure "genuine extension alpha and zero-native-round kernel passed")
end Extension

open Lean Elab Command in
run_cmd do
  for name in #[``State.helperRowFromProgram, ``State.helperOccurrenceCost,
      ``State.helperRowProgram,
      ``State.helperRowCost, ``State.helperTablesProgram, ``State.helperTablesCost,
      ``State.denominatorTablesProgram, ``State.startProgram, ``State.foldTablesProgram,
      ``State.foldProgram, ``State.prepareProgram, ``prepared, ``initial, ``finalState,
      ``Extension.prepared] do
    unless (Lean.IR.findEnvDecl (← getEnv) name).isSome do
      throwError "expected executable compiler IR for `{name}`"
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``State.profileArithmetic_helperRowFromProgram,
      ``State.profileArithmetic_helperRowProgram, ``State.profileArithmetic_helperTablesProgram,
      ``State.profileArithmetic_denominatorTablesProgram, ``State.profileArithmetic_startProgram,
      ``State.profileArithmetic_foldTablesProgram, ``State.profileArithmetic_foldProgram,
      ``State.profileArithmetic_foldProgram_apply,
      ``State.profileArithmetic_prepareProgram_cost, ``State.simulateQ_denominatorTablesProgram,
      ``State.simulateQ_helperTablesProgram, ``State.simulateQ_prepareProgram,
      ``State.simulateQ_startProgram, ``State.simulateQ_foldProgram,
      ``State.helperTablesCost_apply, ``prepared_eq, ``initial_eq,
      ``measured_cubic, ``measured_fold_coherence] do
    unless (← collectAxioms name).all allowed.contains do
      throwError "unexpected axioms in `{name}`"

end ArithmeticStateTests

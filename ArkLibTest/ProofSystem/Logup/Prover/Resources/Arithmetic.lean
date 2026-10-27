/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/
import ArkLib.ProofSystem.Logup.Prover.Resources.Arithmetic
import ArkLibTest.ProofSystem.Logup.Prover.Arithmetic.Ledger
import Lean.Compiler.IR

/-! # Actual optional-history call charges and geometric request bounds -/

open Interaction.Oracle OracleComp OracleSpec CompPoly Logup.Interaction
open Logup.Prover.Honest.Accounting Logup.Prover.Honest.Accounting.Resources
open Lean Elab Command
namespace ArithmeticResourcesTests
abbrev F := ZMod 17
abbrev ambient : OracleSpec Unit := Unit →ₒ F
def handler : QueryImpl ambient Id := fun _ => 0

def cfg (n : Nat) : Config n 3 2 :=
  (Config.create? n 3 2).get ((Config.isSome_create? n 3 2).mpr (by decide))
def data (n : Nat) : Fin 2 × Fin 3 → CMlPolynomialEval F n :=
  fun i => Vector.ofFn fun u => ((i.2.val+1)*(u.val+2)+3*i.1.val : Nat)
def joint (n : Nat) : (Fin n → F) × (Fin (3 ⌈/⌉ 2) → F) :=
  (fun i => (i.val+3 : Nat), ![4,6])
def choices (n code : Nat) : Vector (Option F) n := Vector.ofFn fun i =>
  match code / 3 ^ i.val % 3 with | 0 => none | 1 => some 0 | _ => some 5

def traced (n code : Nat) (alpha : F) :=
  observeProver ambient handler
    (proverWith callInterpreter call_erases (· ++ ·) [] (RingHom.id F) (cfg n) (data n) ambient)
    alpha (joint n) (choices n code)
def costed (n code : Nat) (alpha : F) (initial : ArithmeticCost) :=
  observeProver ambient handler
    (proverWith costInterpreter cost_erases (· + ·) initial
      (RingHom.id F) (cfg n) (data n) ambient)
    alpha (joint n) (choices n code)

example {B E : Type} [CommRing B] [Field E] [DecidableEq E] {n T ell : Nat}
    (f : B →+* E) (cfg : Config n T ell)
    (data : Fin 2 × Fin T → CMlPolynomialEval B n) {ι : Type} (ambient : OracleSpec ι)
    (handler : QueryImpl ambient Id) (alpha : E)
    (joint : (Fin n → E) × (Fin (T ⌈/⌉ ell) → E)) (history : Vector (Option E) n)
    (initial : ArithmeticCost) (kind : ArithmeticCostKind) :
    (observeProver ambient handler
      (proverWith costInterpreter cost_erases (· + ·) initial f cfg data ambient)
      alpha joint history).2.2 kind ≤ initial kind + 1012 * 2 ^ n * T * ell :=
  observed_prover_cost_initial_le f cfg data ambient handler alpha joint history initial kind

example {B E : Type} [CommRing B] [CommRing E] [Inv E] [DecidableEq E]
    {T K ell : Nat} {ι : Type} (ambient : OracleSpec ι) (handler : QueryImpl ambient Id)
    (groups : Vector (List (Fin T)) K) (hgroups : ∀ k, (groups.get k).length ≤ ell)
    (hT : 0 < T) (hell : 0 < ell) (hK : K ≤ T)
    (htotal : ((List.finRange K).map fun k => (groups.get k).length).sum = T)
    (count : Nat) (state : Logup.Prover.State E T K count)
    (history : Vector (Option E) count) (kind : ArithmeticCostKind) :
    charges (observeNative ambient handler count
      (nativeWith (callInterpreter (B := B)) call_erases (· ++ ·) ambient groups hgroups
        count state []) history).2 kind ≤ nativeBudget T K ell count :=
  observed_native_charges_le ambient handler groups hgroups hT hell hK htotal
    count state history kind

run_cmd do
  let kinds := #[ArithmeticCostKind.add,.sub,.mul,.inv,.eq,.coefficientRead,.nodeRead,.valueRead,
    .metadata]
  let initial : ArithmeticCost := fun kind => (kinds.toList.idxOf kind)+1
  let mut histories := 0
  for n in [0,1,2,3] do
    unless messageRows n == 2^n-1 && foldedRows n == 2^n-2 do
      throwError "message/fold geometric omission changed"
    for code in List.range (3^n) do
      for alpha in [(0:F),1,5] do
        let calls := traced n code alpha
        let cost := costed n code alpha initial
        let charged := charges calls.2.2
        unless cost.1 == calls.1 && cost.2.1 == calls.2.1 do
          throwError "request instrumentation changed actual helper/coefficient messages"
        for kind in kinds do
          unless cost.2.2 kind == initial kind + charged kind &&
              charged kind ≤ 1012*2^n*3*2 do
            throwError "actual selected-program charges exceed geometric/initial-offset envelope"
        let tags := calls.2.2.map ArithmeticLedgerTests.tag
        let expectedPrefix := if n == 0 then [(0,0)] else [(0,n),(1,n)]
        unless tags.take expectedPrefix.length == expectedPrefix do
          throwError "zero-round initialization omission or actual preparation order changed"
        let messageRows := (calls.2.2.filterMap fun call => match call with
          | .message r _ _ => some (2^r) | _ => none).sum
        let foldRows := (calls.2.2.filterMap fun call => match call with
          | .fold r _ _ => some (2^r) | _ => none).sum
        unless messageRows ≤ 2^n-1 && foldRows ≤ 2^n-2 do
          throwError "actual message/fold row sums violate the geometric budget"
        histories := histories+1
  unless histories == 120 do throwError "optional-history grid lost a case"
  for name in #[``traced,``costed,``choices,``messageRows,``foldedRows,``nativeBudget] do
    unless (Lean.IR.findEnvDecl (← getEnv) name).isSome do
      throwError "missing executable resource/call observer IR"
  let allowed := #[``propext,``Classical.choice,``Quot.sound]
  for name in #[``messageRows_eq,``foldedRows_eq,``observed_native_cost_le,``nativeBudget_le,
      ``config_group_bounds,``config_total_length,``prepare_cost_le,``start_cost_le,
      ``observed_native_charges_le,``observed_prover_cost_le,
      ``observed_prover_cost_le_geometric,``observed_prover_charges_le,
      ``observed_prover_cost_initial_le,``observed_prover_total_cost_le] do
    unless (← collectAxioms name).all allowed.contains do
      throwError "unexpected actual-prover geometric envelope axioms: {name}"
  logInfo "120 optional/pole histories: exact calls, geometric and initial-offset bounds passed"

end ArithmeticResourcesTests

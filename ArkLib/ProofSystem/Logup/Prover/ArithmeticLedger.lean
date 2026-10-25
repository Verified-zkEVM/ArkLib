/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
module

public import ArkLib.ProofSystem.Logup.Prover.ArithmeticControl

/-!
# Exact observed arithmetic calls of the honest strategy

The observer follows an actual ordinary strategy at prescribed typed public choices. It records
its actual helper and coefficient messages and terminal annotation, including early public abort.
It performs no verifier check and does not introduce another verifier or sampler.

The Cost interpretation equals the sum of the primitive-request profiles of the complete call
arguments recorded by the List interpretation of the same executable control. Thus preparation,
cache initialization, messages and nonterminal private folds are charged exactly where selected.
Zero native rounds omit initialization; terminal rounds omit unused folds. These equalities are
a call-ledger refinement, not a whole-prover resource envelope. Supplied data construction and
embeddings, base and natural-number work,
source backends, retained storage, allocations and machine work require separate accounting.
-/

@[expose] public section

open Interaction.Oracle OracleComp OracleSpec CompPoly Logup.Interaction
namespace Logup.Prover.Honest.Accounting
variable {B E C : Type} [CommRing B] [CommRing E] [Inv E] [DecidableEq E] {T K : Nat}

/-- Replay the prescribed optional challenges against an actual ordinary native strategy. -/
def observeNative {ell : Nat} {ι : Type} (ambient : OracleSpec ι)
    (handler : QueryImpl ambient Id) :
    (count : Nat) → NativeStrategy (E := E) ambient ell count C →
      Vector (Option E) count → List (Sumcheck.Impl.Representation.Message E (ell + 2)) × C
  | 0, strategy, _ => ([], strategy)
  | count + 1, strategy, choices =>
    let sent := simulateQ handler strategy
    match choices[0] with
    | none => ([sent.1], simulateQ handler (sent.2 none))
    | some r =>
      let next := simulateQ handler (sent.2 (some r))
      let result := observeNative ambient handler count next choices.tail
      (sent.1 :: result.1, result.2)

/-- Sum profiles of the exact programs selected by complete call descriptions. -/
def charges (calls : List (Call B E T K)) : ArithmeticCost :=
  (calls.map fun call => (profileArithmetic call.program).2).sum

/-- Profiles of concatenated call histories add coordinatewise. -/
theorem charges_append (xs ys : List (Call B E T K)) :
    charges (xs ++ ys) = charges xs + charges ys := by
  simp [charges]

/-- An empty call history requests no arithmetic. -/
theorem charges_nil : charges ([] : List (Call B E T K)) = 0 := by
  simp [charges]

/-- One recorded call charges precisely its selected arithmetic program. -/
theorem charges_singleton (call : Call B E T K) :
    charges [call] = (profileArithmetic call.program).2 := by
  simp [charges]

omit [Inv E] [DecidableEq E] in
/-- A zero-round observation returns the ordinary terminal annotation. -/
theorem observeNative_zero {ell : Nat} {ι : Type} (ambient : OracleSpec ι)
    (handler : QueryImpl ambient Id) (strategy : NativeStrategy (E := E) ambient ell 0 C)
    (choices : Vector (Option E) 0) : observeNative ambient handler 0 strategy choices =
      ([], strategy) := rfl

/-- A terminal message returns its annotation without a private fold. -/
theorem observeNative_one (run : Interpreter B E C T K) (law : Erases run)
    (combine : C → C → C) {ell : Nat} {ι : Type} (ambient : OracleSpec ι)
    (handler : QueryImpl ambient Id) (groups : Vector (List (Fin T)) K)
    (hgroups : ∀ k, (groups.get k).length ≤ ell)
    (state : Logup.Prover.State E T K 1) (acc : C) (choices : Vector (Option E) 1) :
    observeNative ambient handler 1 (nativeWith run law combine ambient groups hgroups 1 state acc)
      choices = ([(messageWith run law groups hgroups state).1],
        combine acc (messageWith run law groups hgroups state).2) := by
  simp only [observeNative, nativeWith, simulateQ_pure]
  split <;> rfl

/-- Observation follows the actual message and optional nonterminal private fold. -/
theorem observeNative_succ_succ (run : Interpreter B E C T K) (law : Erases run)
    (combine : C → C → C) {ell count : Nat} {ι : Type} (ambient : OracleSpec ι)
    (handler : QueryImpl ambient Id) (groups : Vector (List (Fin T)) K)
    (hgroups : ∀ k, (groups.get k).length ≤ ell)
    (state : Logup.Prover.State E T K (count + 2)) (acc : C)
    (choices : Vector (Option E) (count + 2)) :
    observeNative ambient handler (count + 2)
      (nativeWith run law combine ambient groups hgroups (count + 2) state acc) choices =
      let message := messageWith run law groups hgroups state
      match choices[0] with
      | none => ([message.1], combine acc message.2)
      | some r =>
        let call := Call.fold (B := B) (count + 1) state r
        let next := run call call.program
        let result := observeNative ambient handler (count + 1)
          (nativeWith run law combine ambient groups hgroups (count + 1) next.1
            (combine (combine acc message.2) next.2)) choices.tail
        (message.1 :: result.1, result.2) := by
  rw [observeNative]
  cases choices[0] <;> simp only [nativeWith, simulateQ_pure] <;> rfl

/-- The message annotation is produced by its exact selected arithmetic program. -/
theorem messageWith_snd (run : Interpreter B E C T K) (law : Erases run)
    {ell r : Nat} (groups : Vector (List (Fin T)) K)
    (hgroups : ∀ k, (groups.get k).length ≤ ell)
    (state : Logup.Prover.State E T K (r + 1)) :
    (messageWith run law groups hgroups state).2 =
      (run (Call.message (B := B) r groups state)
        (Call.message (B := B) r groups state).program).2 := rfl

/-- Observed native profiles add exact selected-program charges to their initial annotation. -/
theorem native_cost_eq_initial_add_charges {ell : Nat} {ι : Type} (ambient : OracleSpec ι)
    (handler : QueryImpl ambient Id) (groups : Vector (List (Fin T)) K)
    (hgroups : ∀ k, (groups.get k).length ≤ ell) (count : Nat)
    (state : Logup.Prover.State E T K count) (choices : Vector (Option E) count)
    (initial : ArithmeticCost) (callsBefore : List (Call B E T K)) :
    observeNative ambient handler count
      (nativeWith (costInterpreter (B := B)) (cost_erases (B := B)) (· + ·) ambient
        groups hgroups count state
        (initial + charges callsBefore)) choices =
      let observed := observeNative ambient handler count
        (nativeWith (callInterpreter (B := B)) (call_erases (B := B)) (· ++ ·) ambient
          groups hgroups count state callsBefore)
        choices
      (observed.1, initial + charges observed.2) := by
  induction count generalizing callsBefore with
  | zero => rfl
  | succ count ih =>
    cases count with
    | zero =>
      rw [observeNative_one, observeNative_one]
      simp only [messageWith_fst, messageWith_snd, costInterpreter, callInterpreter]
      congr 1
      simp [charges_append, charges_singleton, add_assoc]
    | succ count =>
      rw [observeNative_succ_succ, observeNative_succ_succ]
      cases choices[0] with
      | none =>
        simp only [messageWith_fst, messageWith_snd, costInterpreter, callInterpreter]
        congr 1
        simp [charges_append, charges_singleton, add_assoc]
      | some r =>
        simp only [messageWith_fst, messageWith_snd, costInterpreter, callInterpreter,
          profileArithmetic_fst]
        have hnext := ih (simulateQ arithmeticAnswer
            (Call.fold (B := B) (count + 1) state r).program) choices.tail
          (callsBefore ++ [Call.message (B := B) (count + 1) groups state] ++
            [Call.fold (B := B) (count + 1) state r])
        simp only [charges_append, charges_singleton, ← add_assoc] at hnext
        exact congrArg (fun result =>
          (pureBuilder groups hgroups (count + 1) state :: result.1, result.2)) hnext

/-- Zero-initial native profiles charge exactly the recorded calls. -/
theorem native_cost_eq_charges {ell : Nat} {ι : Type} (ambient : OracleSpec ι)
    (handler : QueryImpl ambient Id) (groups : Vector (List (Fin T)) K)
    (hgroups : ∀ k, (groups.get k).length ≤ ell) (count : Nat)
    (state : Logup.Prover.State E T K count) (choices : Vector (Option E) count)
    (callsBefore : List (Call B E T K)) :
    observeNative ambient handler count
      (nativeWith (costInterpreter (B := B)) (cost_erases (B := B)) (· + ·) ambient
        groups hgroups count state
        (charges callsBefore)) choices =
      let observed := observeNative ambient handler count
        (nativeWith (callInterpreter (B := B)) (call_erases (B := B)) (· ++ ·) ambient
          groups hgroups count state callsBefore)
        choices
      (observed.1, charges observed.2) := by
  simpa only [zero_add] using native_cost_eq_initial_add_charges ambient handler groups hgroups
    count state choices 0 callsBefore

/-- An ordinary weighted strategy with a constant terminal output type. -/
abbrev WeightedStrategy {n ell : Nat} {ι : Type} (ambient : OracleSpec ι) (C : Type) :=
  Prover.Strategy ambient (protocol E n K ell).tree (protocol E n K ell).roles (fun _ => C)

/-- Observe actual helper and native messages at prescribed public challenges. -/
def observeProver {n ell : Nat} {ι : Type} (ambient : OracleSpec ι)
    (handler : QueryImpl ambient Id) (strategy : WeightedStrategy (E := E) (K := K)
      (n := n) (ell := ell) ambient C)
    (alpha : E) (joint : (Fin n → E) × (Fin K → E)) (choices : Vector (Option E) n) :
    Vector (CMlPolynomialEval E n) K ×
      List (Sumcheck.Impl.Representation.Message E (ell + 2)) × C :=
  let afterAlpha := simulateQ handler (strategy alpha)
  let sent := simulateQ handler afterAlpha
  let native := simulateQ handler (sent.2 joint)
  let observed := observeNative ambient handler n native choices
  (sent.1, observed.1, observed.2)

/-- The complete observer follows actual preparation, helper sending and initialization. -/
theorem observeProver_with {B E C : Type} [CommRing B] [Field E] [DecidableEq E]
    {n T ell : Nat} (run : Interpreter B E C T (T ⌈/⌉ ell)) (law : Erases run)
    (combine : C → C → C) (initial : C) (f : B →+* E) (cfg : Config n T ell)
    (data : Fin 2 × Fin T → CMlPolynomialEval B n) {ι : Type} (ambient : OracleSpec ι)
    (handler : QueryImpl ambient Id) (alpha : E)
    (joint : (Fin n → E) × (Fin (T ⌈/⌉ ell) → E)) (choices : Vector (Option E) n) :
    observeProver ambient handler (proverWith run law combine initial f cfg data ambient)
      alpha joint choices =
      let call := Call.prepare n f alpha cfg.groups data
      let prepared := run call call.program
      let observed := observeNative ambient handler n
        (startWith run law combine ambient cfg.groups cfg.length_group_le n prepared.1
          joint.1 joint.2 (combine initial prepared.2)) choices
      (prepared.1.helper, observed.1, observed.2) := rfl

/-- The complete observed profile adds exact call charges to its initial annotation. -/
theorem prover_cost_eq_initial_add_charges {B E : Type} [CommRing B] [Field E] [DecidableEq E]
    {n T ell : Nat} (f : B →+* E) (cfg : Config n T ell)
    (data : Fin 2 × Fin T → CMlPolynomialEval B n) {ι : Type} (ambient : OracleSpec ι)
    (handler : QueryImpl ambient Id) (alpha : E)
    (joint : (Fin n → E) × (Fin (T ⌈/⌉ ell) → E)) (choices : Vector (Option E) n)
    (initial : ArithmeticCost) :
    observeProver ambient handler
      (proverWith costInterpreter cost_erases (· + ·) initial f cfg data ambient)
      alpha joint choices =
      let observed := observeProver ambient handler
        (proverWith callInterpreter call_erases (· ++ ·) [] f cfg data ambient)
        alpha joint choices
      (observed.1, observed.2.1, initial + charges observed.2.2) := by
  rw [observeProver_with, observeProver_with]
  simp only [costInterpreter, callInterpreter, profileArithmetic_fst]
  cases n with
  | zero =>
    simp only [startWith, observeNative]
    simp [charges, Call.program]
  | succ n =>
    simp only [startWith, costInterpreter, callInterpreter, profileArithmetic_fst]
    let prepareCall : Call B E T (T ⌈/⌉ ell) := Call.prepare (n + 1) f alpha cfg.groups data
    let prepared := simulateQ arithmeticAnswer prepareCall.program
    let startCall : Call B E T (T ⌈/⌉ ell) := Call.start (n + 1) prepared joint.1 joint.2
    let started := simulateQ arithmeticAnswer startCall.program
    have h := native_cost_eq_initial_add_charges ambient handler cfg.groups cfg.length_group_le
      (n + 1)
      started choices initial ([] ++ [prepareCall] ++ [startCall])
    simp only [charges_append, charges_singleton, charges_nil, zero_add, ← add_assoc] at h
    exact congrArg (fun observed => (prepared.helper, observed.1, observed.2)) h

/-- Zero-initial complete profiles charge exactly the recorded selected programs. -/
theorem prover_cost_eq_charges {B E : Type} [CommRing B] [Field E] [DecidableEq E]
    {n T ell : Nat} (f : B →+* E) (cfg : Config n T ell)
    (data : Fin 2 × Fin T → CMlPolynomialEval B n) {ι : Type} (ambient : OracleSpec ι)
    (handler : QueryImpl ambient Id) (alpha : E)
    (joint : (Fin n → E) × (Fin (T ⌈/⌉ ell) → E)) (choices : Vector (Option E) n) :
    observeProver ambient handler
      (proverWith costInterpreter cost_erases (· + ·) 0 f cfg data ambient)
      alpha joint choices =
      let observed := observeProver ambient handler
        (proverWith callInterpreter call_erases (· ++ ·) [] f cfg data ambient)
        alpha joint choices
      (observed.1, observed.2.1, charges observed.2.2) := by
  simpa only [zero_add] using
    prover_cost_eq_initial_add_charges f cfg data ambient handler alpha joint choices 0

end Logup.Prover.Honest.Accounting

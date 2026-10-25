/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
module

public import ArkLib.ProofSystem.Logup.Prover.ArithmeticState
public import ArkLib.ProofSystem.Logup.Prover.ArithmeticRound
public import ArkLib.ProofSystem.Logup.Prover.Strategy

/-!
# Default honest strategy executing the measured arithmetic programs

The ordinary prover computes actual helper tables, initializes its equality cache after the joint
challenge, and streams native coefficient messages using the measured builders. Nonterminal
challenges fold all retained private table families through the measured one-product fold. The
last continuation returns Unit without an unused private fold; zero native rounds also skip the
unused private kernel and batching-vector copy. The required joint challenge and original retained
source authentication remain in the verifier.

The equality theorems identify ordinary strategy values with the existing correctness constructor.
They transfer correctness only. Resource claims must count the named programs actually selected
here, including the terminal call structure, separate base preprocessing and retained messages.
-/

@[expose] public section

open Interaction.Oracle OracleComp OracleSpec CompPoly Logup.Interaction
namespace Logup.Prover.Honest

/-- Build each message by executing the measured streamed coefficient program. -/
def arithmeticBuilder {E : Type} [CommRing E] [Inv E] [DecidableEq E] {T K ell : Nat}
    (groups : Vector (List (Fin T)) K) (hgroups : ∀ k, (groups.get k).length ≤ ell)
    (r : Nat) (state : Logup.Prover.State E T K (r + 1)) :
    Sumcheck.Impl.Representation.Message E (ell + 2) :=
  RoundCoefficients.messageByProgram groups hgroups state.lambda state.denominator state.weight
    state.helper state.kernel

/-- The measured builder has the existing formal coefficient constructor as its value. -/
theorem arithmeticBuilder_eq_pureBuilder {E : Type} [CommRing E] [Inv E] [DecidableEq E]
    {T K ell : Nat} (groups : Vector (List (Fin T)) K)
    (hgroups : ∀ k, (groups.get k).length ≤ ell) :
    arithmeticBuilder (E := E) groups hgroups = pureBuilder groups hgroups := by
  funext r state
  exact RoundCoefficients.messageByProgram_eq_message _ _ _ _ _ _ _

/-- Send measured messages and fold only private states consumed by a subsequent round. -/
def nativeArithmetic {E : Type} [CommRing E] [Inv E] [DecidableEq E]
    {T K ell : Nat} {ι : Type} (ambient : OracleSpec ι)
    (groups : Vector (List (Fin T)) K) (hgroups : ∀ k, (groups.get k).length ≤ ell) :
    (count : Nat) → Logup.Prover.State E T K count →
      Prover.Strategy ambient (Sumcheck.Interaction.Computable.protocol E (ell + 2) count).tree
        (Sumcheck.Interaction.Computable.protocol E (ell + 2) count).roles (fun _ => Unit)
  | 0, _ => ()
  | 1, state => pure ⟨arithmeticBuilder groups hgroups 0 state, fun choice => match choice with
      | none => pure ()
      | some _ => pure ()⟩
  | count + 2, state => pure ⟨arithmeticBuilder groups hgroups (count + 1) state,
      fun choice => match choice with
      | none => pure ()
      | some r =>
        let next := simulateQ arithmeticAnswer (State.foldProgram state r)
        pure (nativeArithmetic ambient groups hgroups (count + 1) next)⟩

/-- The measured continuation has the existing ordinary-strategy value, including terminal
branches. -/
theorem nativeArithmetic_eq_nativeWith {E : Type} [CommRing E] [Inv E] [DecidableEq E]
    {T K ell : Nat} {ι : Type} (ambient : OracleSpec ι)
    (groups : Vector (List (Fin T)) K) (hgroups : ∀ k, (groups.get k).length ≤ ell)
    (count : Nat) (state : Logup.Prover.State E T K count) :
    nativeArithmetic ambient groups hgroups count state =
      nativeWith ambient (arithmeticBuilder groups hgroups) count state := by
  induction count with
  | zero => rfl
  | succ count ih =>
    cases count with
    | zero =>
      simp only [nativeArithmetic, nativeWith]
      rfl
    | succ count =>
      simp only [nativeArithmetic, nativeWith, State.simulateQ_foldProgram, ih]
      rfl

/-- Initialize the measured private cache only when at least one native message follows. -/
def startNativeArithmetic {E : Type} [CommRing E] [Inv E] [DecidableEq E]
    {T K ell : Nat} {ι : Type} (ambient : OracleSpec ι)
    (groups : Vector (List (Fin T)) K) (hgroups : ∀ k, (groups.get k).length ≤ ell) :
    (count : Nat) → Logup.Prover.Prepared E T K count → (Fin count → E) → (Fin K → E) →
      Prover.Strategy ambient (Sumcheck.Interaction.Computable.protocol E (ell + 2) count).tree
        (Sumcheck.Interaction.Computable.protocol E (ell + 2) count).roles (fun _ => Unit)
  | 0, _, _, _ => ()
  | count + 1, prepared, z, lambda =>
    let started := simulateQ arithmeticAnswer (State.startProgram prepared z lambda)
    nativeArithmetic ambient groups hgroups (count + 1) started

/-- Skipping an unused zero-round cache preserves the existing ordinary continuation. -/
theorem startNativeArithmetic_eq_nativeWith {E : Type} [CommRing E] [Inv E] [DecidableEq E]
    {T K ell : Nat} {ι : Type} (ambient : OracleSpec ι)
    (groups : Vector (List (Fin T)) K) (hgroups : ∀ k, (groups.get k).length ≤ ell)
    (count : Nat) (prepared : Logup.Prover.Prepared E T K count)
    (z : Fin count → E) (lambda : Fin K → E) :
    startNativeArithmetic ambient groups hgroups count prepared z lambda =
      nativeWith ambient (arithmeticBuilder groups hgroups) count
        (State.start prepared z lambda) := by
  cases count with
  | zero => rfl
  | succ count =>
    simp only [startNativeArithmetic, State.simulateQ_startProgram, nativeArithmetic_eq_nativeWith]

/-- Send actual measured helpers, then execute the measured native strategy without unused
terminal work. -/
def prover {B E : Type} [CommRing B] [Field E] [DecidableEq E] {n T ell : Nat}
    (f : B →+* E) (cfg : Config n T ell)
    (data : Fin 2 × Fin T → CMlPolynomialEval B n) {ι : Type} (ambient : OracleSpec ι) :
    Prover.Strategy ambient (protocol E n (T ⌈/⌉ ell) ell).tree
      (protocol E n (T ⌈/⌉ ell) ell).roles (fun _ => Unit) :=
  fun (alpha : E) => pure (do
    let prepared := simulateQ arithmeticAnswer (State.prepareProgram f alpha cfg.groups data)
    return ⟨prepared.helper, fun joint =>
      pure (startNativeArithmetic ambient cfg.groups cfg.length_group_le n prepared
        joint.1 joint.2)⟩)

/-- The default ordinary strategy equals the existing honest correctness constructor. -/
theorem prover_eq_honestWith {B E : Type} [CommRing B] [Field E] [DecidableEq E]
    {n T ell : Nat} (f : B →+* E) (cfg : Config n T ell)
    (data : Fin 2 × Fin T → CMlPolynomialEval B n) {ι : Type} (ambient : OracleSpec ι) :
    prover f cfg data ambient =
      honestWith f cfg data ambient (pureBuilder cfg.groups cfg.length_group_le) := by
  unfold prover honestWith
  funext alpha
  rw [State.simulateQ_prepareProgram f alpha cfg data]
  simp only [startNativeArithmetic_eq_nativeWith, arithmeticBuilder_eq_pureBuilder]

end Logup.Prover.Honest

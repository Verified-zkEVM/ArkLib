/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/
module

public import ArkLib.ProofSystem.Logup.Prover.Arithmetic.Control

/-!
# Default honest strategy executing the measured arithmetic programs

This is the selected weighted `Logup.Prover.Honest.prover`. The explicit-builder construction
is in `Prover/Reference.lean`; endpoint correctness is in `Security/Completeness.lean`.
See the code-local `Logup/README.md` for the scalar and tuple entry points.

The ordinary prover computes actual helper tables, initializes its equality cache after the joint
challenge, and streams native coefficient messages using the measured builders. Nonterminal
challenges fold all retained private table families through the measured one-product fold. The
last continuation returns Unit without an unused private fold; zero native rounds also skip the
unused private kernel and batching-vector copy. The required joint challenge and original retained
source authentication remain in the verifier.

The equality theorems identify ordinary strategy values with the explicit-builder reference and
transfer correctness only. `Prover/Resources/Arithmetic.lean` bounds the named programs selected
by this driver. Frontend resource owners account for BASE preprocessing separately, and
`Prover/Resources/StorageLedger.lean` counts retained messages.
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
        (Sumcheck.Interaction.Computable.protocol E (ell + 2) count).roles (fun _ => Unit) :=
  fun count state => Accounting.nativeWith (Accounting.unitInterpreter (B := E))
    Accounting.unit_erases (fun _ _ => ()) ambient groups hgroups count state ()

/-- The measured continuation has the existing ordinary-strategy value, including terminal
branches. -/
theorem nativeArithmetic_eq_nativeWith {E : Type} [CommRing E] [Inv E] [DecidableEq E]
    {T K ell : Nat} {ι : Type} (ambient : OracleSpec ι)
    (groups : Vector (List (Fin T)) K) (hgroups : ∀ k, (groups.get k).length ≤ ell)
    (count : Nat) (state : Logup.Prover.State E T K count) :
    nativeArithmetic ambient groups hgroups count state =
      nativeWith ambient (arithmeticBuilder groups hgroups) count state := by
  rw [arithmeticBuilder_eq_pureBuilder]
  exact Accounting.native_unit_eq (B := E) ambient groups hgroups count state

/-- Initialize the measured private cache only when at least one native message follows. -/
def startNativeArithmetic {E : Type} [CommRing E] [Inv E] [DecidableEq E]
    {T K ell : Nat} {ι : Type} (ambient : OracleSpec ι)
    (groups : Vector (List (Fin T)) K) (hgroups : ∀ k, (groups.get k).length ≤ ell) :
    (count : Nat) → Logup.Prover.Prepared E T K count → (Fin count → E) → (Fin K → E) →
      Prover.Strategy ambient (Sumcheck.Interaction.Computable.protocol E (ell + 2) count).tree
        (Sumcheck.Interaction.Computable.protocol E (ell + 2) count).roles (fun _ => Unit) :=
  fun count prepared z lambda => Accounting.startWith (Accounting.unitInterpreter (B := E))
    Accounting.unit_erases (fun _ _ => ()) ambient groups hgroups count prepared z lambda ()

/-- Skipping an unused zero-round cache preserves the existing ordinary continuation. -/
theorem startNativeArithmetic_eq_nativeWith {E : Type} [CommRing E] [Inv E] [DecidableEq E]
    {T K ell : Nat} {ι : Type} (ambient : OracleSpec ι)
    (groups : Vector (List (Fin T)) K) (hgroups : ∀ k, (groups.get k).length ≤ ell)
    (count : Nat) (prepared : Logup.Prover.Prepared E T K count)
    (z : Fin count → E) (lambda : Fin K → E) :
    startNativeArithmetic ambient groups hgroups count prepared z lambda =
      nativeWith ambient (arithmeticBuilder groups hgroups) count
        (State.start prepared z lambda) := by
  rw [arithmeticBuilder_eq_pureBuilder]
  exact Accounting.start_unit_eq_nativeWith (B := E) ambient groups hgroups count prepared z lambda

/-- Send actual measured helpers, then execute the measured native strategy without unused
terminal work. -/
def prover {B E : Type} [CommRing B] [Field E] [DecidableEq E] {n T ell : Nat}
    (f : B →+* E) (cfg : Config n T ell)
    (data : Fin 2 × Fin T → CMlPolynomialEval B n) {ι : Type} (ambient : OracleSpec ι) :
    Prover.Strategy ambient (protocol E n (T ⌈/⌉ ell) ell).tree
      (protocol E n (T ⌈/⌉ ell) ell).roles (fun _ => Unit) :=
  Accounting.proverWith Accounting.unitInterpreter Accounting.unit_erases (fun _ _ => ()) ()
    f cfg data ambient

/-- The default ordinary strategy equals the existing honest correctness constructor. -/
theorem prover_eq_honestWith {B E : Type} [CommRing B] [Field E] [DecidableEq E]
    {n T ell : Nat} (f : B →+* E) (cfg : Config n T ell)
    (data : Fin 2 × Fin T → CMlPolynomialEval B n) {ι : Type} (ambient : OracleSpec ι) :
    prover f cfg data ambient =
      honestWith f cfg data ambient (pureBuilder cfg.groups cfg.length_group_le) := by
  exact Accounting.prover_unit_eq_honestWith f cfg data ambient

end Logup.Prover.Honest

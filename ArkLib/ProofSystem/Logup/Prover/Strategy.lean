/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/
module

public import ArkLib.ProofSystem.Logup.Interaction.Protocol
public import ArkLib.ProofSystem.Logup.Prover.State
public import ArkLib.ProofSystem.Logup.Prover.RoundCoefficients

/-!
# Ordinary honest LogUp strategies with explicit message implementations

The prover prepares denominator, weight and termwise helper tables after alpha, sends the helpers,
then starts the cached kernel only after the joint challenge. Native continuations fold private
state at each received challenge. Public abort terminates the continuation.

The round builder is explicit. `pureBuilder` is a correctness constructor; the eventual default
must select the measured implementation explicitly. This owner makes no arithmetic or storage
claim, and an equal-output implementation alone does not transfer its work.
-/

@[expose] public section

open Interaction.Oracle OracleComp OracleSpec CompPoly Logup.Interaction
namespace Logup.Prover.Honest

/-- Send each built message and retain folded private tables in ordinary native continuations. -/
def nativeWith {E : Type} [CommRing E] {T K ell : Nat} {ι : Type}
    (ambient : OracleSpec ι)
    (build : (r : Nat) → Logup.Prover.State E T K (r + 1) →
      Sumcheck.Impl.Representation.Message E (ell + 2)) :
    (count : Nat) → Logup.Prover.State E T K count →
      Prover.Strategy ambient (Sumcheck.Interaction.Computable.protocol E (ell + 2) count).tree
        (Sumcheck.Interaction.Computable.protocol E (ell + 2) count).roles (fun _ => Unit)
  | 0, _ => ()
  | count + 1, state => pure ⟨build count state, fun choice => match choice with
      | none => pure ()
      | some r => pure (nativeWith ambient build count (State.fold state r))⟩

/-- Pure coefficient constructor for correctness, without a default-runtime cost claim. -/
def pureBuilder {E : Type} [CommRing E] [DecidableEq E] {T K ell : Nat}
    (groups : Vector (List (Fin T)) K) (hgroups : ∀ k, (groups.get k).length ≤ ell)
    (r : Nat) (state : Logup.Prover.State E T K (r + 1)) :
    Sumcheck.Impl.Representation.Message E (ell + 2) :=
  RoundCoefficients.message groups hgroups state.lambda state.denominator state.weight
    state.helper state.kernel


/-- Send the actual termwise helper tables before the joint challenge, then run native Sumcheck. -/
def honestWith {B E : Type} [CommRing B] [Field E] {n T ell : Nat}
    (f : B →+* E) (cfg : Config n T ell)
    (data : Fin 2 × Fin T → CMlPolynomialEval B n) {ι : Type} (ambient : OracleSpec ι)
    (build : (r : Nat) → Logup.Prover.State E T (T ⌈/⌉ ell) (r + 1) →
      Sumcheck.Impl.Representation.Message E (ell + 2)) :
    Prover.Strategy ambient (protocol E n (T ⌈/⌉ ell) ell).tree
      (protocol E n (T ⌈/⌉ ell) ell).roles (fun _ => Unit) :=
  fun (alpha : E) => pure (do
    let prepared := State.prepare f alpha cfg data
    return ⟨prepared.helper, fun joint =>
      pure (nativeWith ambient build n (State.start prepared joint.1 joint.2))⟩)


end Logup.Prover.Honest

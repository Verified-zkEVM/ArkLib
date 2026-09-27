/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.ProofSystem.Sumcheck.Interaction.Protocol
public import ArkLib.ProofSystem.Sumcheck.Impl.Representation

/-!
# Native Sumcheck on computable messages

This is the shared native verifier and executor specialized to bounded coefficient arrays.
Every runtime message query uses Horner evaluation. Arbitrary ordinary prover strategies are
interpreted into mathematical strategies only for the execution and security bridge.
-/

@[expose] public section

namespace Sumcheck.Interaction.Computable

open _root_.Interaction.Oracle
open Impl.Representation

variable (R : Type) [CommSemiring R] (n deg : ℕ)

/-- The terminal statement is the unchanged full-prefix evaluation claim. -/
abbrev FinalStatement := Native.FinalStatement R n
/-- Truth compares the exported original behavior with the final claimed evaluation. -/
abbrev outputRelation := Native.outputRelation R n deg

/-- Native protocol carrying actual computable degree-bounded messages. -/
abbrev protocol := Native.Core.protocol R (Message R deg) (evaluate R deg)

variable {ι : Type} (ambient : OracleSpec ι)

/-- The shared native verifier, with Horner evaluation as its oracle interface. -/
abbrev verifier [DecidableEq R] := Native.Core.verifier R n deg (Message R deg)
  (evaluate R deg) ambient
/-- Actual execution of any ordinary prover sending computable messages. -/
abbrev execute [DecidableEq R] := Native.Core.execute R n deg (Message R deg)
  (evaluate R deg) ambient

variable [BEq R] [LawfulBEq R]

/-- Proof-only interpretation of the whole prover; private state stays in its continuations. -/
noncomputable abbrev interpretProver := Native.Core.transportProver R (Message R deg)
  (evaluate R deg) ambient (SingleRound.Message R deg) (fun q x => q.val.eval x)
  (toMessage R deg)

/-- Exact closed execution equality transfers mathematical native claims to computable
messages. No query to the retained original oracle is added by this interpretation. -/
theorem execute_eq_native [DecidableEq R]
    (challenge : OracleComp ambient R) (domain : List R)
    (count start : ℕ) (finish : start + count = n) (A : PFunctor)
    (originalOracle : VirtualOracle (OracleSpec.ofPFunctor A)
      (MultivariateRound.polynomialFamily R n deg))
    (stmt : Spec.StatementRound R n ⟨start, by omega⟩)
    (impl : QueryImpl (OracleSpec.ofPFunctor A) Id)
    (prover : Prover.Strategy ambient (protocol R deg count).tree
      (protocol R deg count).roles (fun _ => Unit)) :
    execute R n deg ambient challenge domain count start finish A originalOracle stmt impl prover =
      Native.execute R n deg ambient challenge domain count start finish A originalOracle stmt impl
        (interpretProver R deg ambient count prover) := by
  apply Native.Core.execute_transport
  · intro q x
    exact (evaluate_eq R deg q x).symm
  · rfl

end Sumcheck.Interaction.Computable

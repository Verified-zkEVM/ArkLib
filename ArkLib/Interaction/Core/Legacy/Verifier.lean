/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Interaction.Core.Legacy.Prover

/-!
# Legacy verifiers and reductions on protocol trees

A legacy verifier is public-coin: it samples each challenge uniformly and decides once from the
full transcript. Its embedding into the interaction layer keeps both parts. The sampler is the
counterpart `legacySampler` built in `Legacy.Prover`, and the decision reads the legacy transcript
off the completed run and calls `verify` unchanged.

An embedded reduction pairs the embedded honest prover with the embedded verifier. The prover's
output keeps the legacy output statement and witness.
-/

@[expose] public section

namespace Interaction.Core.Legacy
open PFunctor FreeM TwoParty.Lens OracleComp OracleSpec ProtocolSpec

variable {n : ℕ} {pSpec : ProtocolSpec n} {ι : Type} {oSpec : OracleSpec ι}
  {StmtIn WitIn StmtOut WitOut : Type}

/-- The embedded verifier decides by calling legacy `verify` on the decoded transcript. -/
def embedVerifier (V : _root_.Verifier oSpec StmtIn StmtOut pSpec) :
    Core.Verifier oSpec (protocol pSpec) StmtIn StmtOut where
  decide stmt _ view := V.verify stmt (decode pSpec view.val)

@[simp] theorem embedVerifier_decide (V : _root_.Verifier oSpec StmtIn StmtOut pSpec)
    (stmt : StmtIn) (p : Path (protocol pSpec)) (view : PlainView (protocol pSpec) p) :
    (embedVerifier V).decide stmt p view = V.verify stmt (decode pSpec view.val) := rfl

/-- The embedded reduction. -/
def embedReduction (R : _root_.Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec) :
    Core.Reduction oSpec (protocol pSpec) StmtIn WitIn StmtOut (fun _ => StmtOut × WitOut) where
  prover := embedProver R.prover
  verifier := embedVerifier R.verifier

end Interaction.Core.Legacy

/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ArkLib.ToVCVio.ToMathlib.Data.Vector.Basic
import VCVio.OracleComp.EvalDist

/-!
# Additions to VCV-io's `OracleComp.EvalDist`
-/

namespace OracleComp

/-- Index-extraction for `(Vector.ofFn id).mapM` over an `OracleComp`: any element in the
    support of the monadic `mapM` has each component lying in the support of the corresponding
    inner computation. -/
lemma support_ofFn_mapM_index
    {ι α : Type} {spec : OracleSpec ι} {L : ℕ}
    (f : Fin L → OracleComp spec α)
    {v : Vector α L}
    (hv : v ∈ support ((Vector.ofFn (fun i : Fin L => i)).mapM f))
    (i : Fin L) : v[i] ∈ support (f i) := by
  simpa using
    Vector.support_mapM_index (Vector.ofFn (fun i : Fin L => i)) f hv i

end OracleComp

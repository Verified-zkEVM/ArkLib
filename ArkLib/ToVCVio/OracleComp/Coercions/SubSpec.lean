/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import VCVio.OracleComp.Coercions.SubSpec

/-!
# Additions to VCV-io's `OracleComp.Coercions.SubSpec`
-/

namespace OracleComp

lemma bind_liftComp_map
    {ι τ α β γ : Type} {spec : OracleSpec ι} {superSpec : OracleSpec τ}
    [MonadLiftT (OracleQuery spec) (OracleQuery superSpec)]
    (oa : OracleComp spec α) (f : α → β) (body : β → OracleComp superSpec γ) :
    (do
      let b ← f <$> OracleComp.liftComp oa superSpec
      body b) =
    (do
      let a ← OracleComp.liftComp oa superSpec
      body (f a)) := by
  simp only [map_eq_bind_pure_comp, bind_assoc, Function.comp_apply, pure_bind]

end OracleComp

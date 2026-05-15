/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import VCVio.OracleComp.Coercions.SubSpec

/-!
# Additions to VCV-io's `OracleComp.Coercions.SubSpec`
-/

namespace OracleComp

lemma mem_support_of_mem_support_liftComp
    {ι τ α : Type} {spec : OracleSpec ι} {superSpec : OracleSpec τ}
    [MonadLiftT (OracleQuery spec) (OracleQuery superSpec)]
    (oa : OracleComp spec α) (x : α) :
    x ∈ support (oa.liftComp superSpec) → x ∈ support oa := by
  intro hx
  induction oa using OracleComp.inductionOn generalizing x with
  | pure y =>
      simpa using hx
  | query_bind q oa ih =>
      rw [OracleComp.liftComp_bind, mem_support_bind_iff] at hx
      rw [mem_support_bind_iff]
      obtain ⟨u, _hu, hx⟩ := hx
      exact ⟨u, OracleComp.mem_support_query q u, ih u x hx⟩

end OracleComp

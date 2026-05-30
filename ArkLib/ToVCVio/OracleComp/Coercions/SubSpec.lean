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

lemma liftComp_bind_pure
    {ι τ α β : Type} {spec : OracleSpec ι} {superSpec : OracleSpec τ}
    [MonadLiftT (OracleQuery spec) (OracleQuery superSpec)]
    (oa : OracleComp spec α) (f : α → β) :
    OracleComp.liftComp (do let a ← oa; pure (f a)) superSpec =
      f <$> OracleComp.liftComp oa superSpec := by
  change (f <$> oa).liftComp superSpec = f <$> oa.liftComp superSpec
  exact OracleComp.liftComp_map superSpec oa f

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

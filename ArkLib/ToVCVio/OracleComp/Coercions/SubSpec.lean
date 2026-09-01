/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michele Orrù
-/

import VCVio.OracleComp.Coercions.SubSpec

/-! Compatibility import for additions that now live in VCVio.

`mem_support_of_mem_support_liftComp` and `liftComp_bind_pure` were upstreamed and removed at the
v4.31.0 bump (#644). `bind_liftComp_map` is removed here: it had no call site anywhere in the tree
and duplicates Mathlib's `bind_map_left`. -/

namespace OracleComp

/-! ### Instance-route irrelevance for `liftComp`

Lifting across nested sum specs (e.g. `(spec₁ + spec₂) + spec₃`) can go through several
`MonadLiftT (OracleQuery _) (OracleQuery _)` instance routes, which elaboration picks
unpredictably and which are not definitionally equal.  The lemmas below let proofs align any
two routes that agree on single queries — the agreement hypothesis is typically closed by
`rfl` for the canonical sum embeddings.  All instances are *free* implicit arguments (not
instance-bound), so `rw` applies to whatever route appears in the goal. -/

/-- Lifting an oracle computation in two steps (`spec₁ ↪ spec₂ ↪ spec₃`) equals lifting it
directly, provided the two routes agree on single queries. -/
lemma liftComp_liftComp {ι₁ ι₂ ι₃ : Type} {spec₁ : OracleSpec ι₁}
    {spec₂ : OracleSpec ι₂} {spec₃ : OracleSpec ι₃} {α : Type}
    {i₁₂ : MonadLiftT (OracleQuery spec₁) (OracleQuery spec₂)}
    {i₂₃ : MonadLiftT (OracleQuery spec₂) (OracleQuery spec₃)}
    {i₁₃ : MonadLiftT (OracleQuery spec₁) (OracleQuery spec₃)}
    (hq : ∀ (t : spec₁.Domain),
      ((liftM (spec₁.query t) : OracleComp spec₂ (spec₁.Range t)).liftComp spec₃)
        = (liftM (spec₁.query t) : OracleComp spec₃ (spec₁.Range t)))
    (x : OracleComp spec₁ α) :
    liftComp (liftComp x spec₂) spec₃ = liftComp x spec₃ := by
  induction x using OracleComp.inductionOn with
  | pure x => simp only [liftComp_pure]
  | query_bind t k ih =>
    simp only [liftComp_bind, liftComp_query, bind_map_left, ih]
    rw [hq]

/-- `liftComp` only depends on the `MonadLiftT` instance through its action on single queries:
two (possibly structurally different) instance routes that agree on queries give equal lifts. -/
lemma liftComp_inst_irrel {ι₁ ι₂ : Type} {spec₁ : OracleSpec ι₁}
    {spec₂ : OracleSpec ι₂} {α : Type}
    {i₁ i₂ : MonadLiftT (OracleQuery spec₁) (OracleQuery spec₂)}
    (hq : ∀ (t : spec₁.Domain),
      (liftComp ((spec₁.query t : OracleQuery spec₁ _) : OracleComp spec₁ _) spec₂
          (h := i₁))
        = (liftComp ((spec₁.query t : OracleQuery spec₁ _) : OracleComp spec₁ _) spec₂
            (h := i₂)))
    (x : OracleComp spec₁ α) :
    liftComp x spec₂ (h := i₁) = liftComp x spec₂ (h := i₂) := by
  induction x using OracleComp.inductionOn with
  | pure x => simp only [liftComp_pure]
  | query_bind t k ih =>
    simp only [liftComp_bind, ih]
    exact congrArg (· >>= _) (hq t)

/-- Instance-agnostic double-lift bind congruence: a two-step lift bound to `f` equals the
direct lift bound to `g`, given per-query compatibility of the routes and pointwise equality of
the continuations.  Proven by induction, so no alignment of `MonadLiftT` instance routes is
needed at the use site. -/
lemma liftComp_liftComp_bind_congr {ι₁ ι₂ ι₃ : Type} {spec₁ : OracleSpec ι₁}
    {spec₂ : OracleSpec ι₂} {spec₃ : OracleSpec ι₃} {α β : Type}
    {i₁₂ : MonadLiftT (OracleQuery spec₁) (OracleQuery spec₂)}
    {i₂₃ : MonadLiftT (OracleQuery spec₂) (OracleQuery spec₃)}
    {i₁₃ : MonadLiftT (OracleQuery spec₁) (OracleQuery spec₃)}
    (hq : ∀ t : spec₁.Domain,
      (liftComp (liftComp ((liftM (spec₁.query t) : OracleComp spec₁ _)) spec₂ (h := i₁₂))
          spec₃
          (h := i₂₃))
        = liftComp ((liftM (spec₁.query t) : OracleComp spec₁ _)) spec₃ (h := i₁₃))
    (X : OracleComp spec₁ α) (f g : α → OracleComp spec₃ β) (hfg : ∀ a, f a = g a) :
    (liftComp (liftComp X spec₂ (h := i₁₂)) spec₃ (h := i₂₃)) >>= f
      = (liftComp X spec₃ (h := i₁₃)) >>= g := by
  induction X using OracleComp.inductionOn generalizing f g with
  | pure x => simp only [liftComp_pure, pure_bind, hfg]
  | query_bind t k ih =>
    simp only [liftComp_bind, bind_assoc]
    rw [show (liftComp (liftComp ((liftM (spec₁.query t) : OracleComp spec₁ _)) spec₂
        (h := i₁₂)) spec₃ (h := i₂₃))
      = liftComp ((liftM (spec₁.query t) : OracleComp spec₁ _)) spec₃ (h := i₁₃) from hq t]
    refine bind_congr fun u => ?_
    exact ih u f g hfg

end OracleComp

import VCVio

/-!

# Some special cases of `QueryImpl` where the monad is another (stateful) oracle computation

TODO: figure out a better organization / naming scheme for this

-/


universe u v

open OracleComp OracleSpec

variable {ι ι' ιₜ : Type*} {spec : OracleSpec ι}
    {spec' : OracleSpec ι'} {specₜ : OracleSpec ιₜ}
    {m : Type u → Type v} {α β γ σ : Type u}

#check SubSpec

instance : IsEmpty (OracleQuery []ₒ α) where
  false := by simp only [IsEmpty.forall_iff]

-- TODO: revamp the `SubSpec` stuff to work for `MonadLiftT` instead of `MonadLift`
instance (priority := high) : MonadLiftT (OracleComp []ₒ) (OracleComp spec) where
  monadLift := OracleComp.construct pure (fun a => by contradiction) failure

section SimulateNeverFails

variable [Monad m] (so : QueryImpl spec m)

/-- Canonical lifting of a function `OracleQuery spec α → m α`, for an arbitrary monad `m`,
to a new function on computations `OracleComp spec α` that _never_ fails. -/
def simulateQ' (oa : OracleComp spec α) (h : oa.neverFails) : m α := by
  induction oa using OracleComp.construct with
  | pure x => exact pure x
  | query_bind q r ih => exact (do let b ← so.impl q; ih b (by simp at h; exact h b))
  | failure => simp [neverFails] at h

@[simp]
theorem simulateQ'_pure (x : α) : simulateQ' so (pure x) (by simp) = pure x := by
  simp [simulateQ']

@[simp]
theorem simulateQ'_query_bind (q : OracleQuery spec α)
    (ob : α → OracleComp spec β) (h : ∀ x, (ob x).neverFails) :
    simulateQ' so (liftM q >>= ob) (by simp [h]) =
      so.impl q >>= (fun x => simulateQ' so (ob x) (h x)) := by
  simp only [simulateQ', query_bind_eq_roll, OptionT.mk]
  congr

variable [LawfulMonad m]

@[simp]
theorem simulateQ'_query (q : OracleQuery spec α) :
    simulateQ' so q (by simp) = so.impl q := by
  simp [simulateQ']

@[simp]
theorem simulateQ'_bind (oa : OracleComp spec α) (ob : α → OracleComp spec β)
    -- Could potentially be weakened to `∀ x ∈ oa.support, (ob x).neverFails`
    -- Would require `bindOnSupport` instead of just `bind`
    (ha : oa.neverFails) (hb : ∀ x, (ob x).neverFails) :
      simulateQ' so (oa >>= ob) (by simp; exact ⟨ha, fun x _ => hb x⟩) =
      simulateQ' so oa ha >>= fun x ↦ simulateQ' so (ob x) (hb x) := by
  induction oa using OracleComp.inductionOn with
  | pure x => simp [simulateQ']; congr
  | query_bind i q r ih =>
    simp at ih ha ⊢; rw [simulateQ'_query_bind]
    · sorry
    · simp; intro x; refine ⟨ha x, ?_⟩; sorry
  | failure => simp [neverFails] at ha

-- An alternate approach is just to show that `simulateQ` is not failure if `oa.neverFails`?
-- Not very well-defined since `OptionT m` pushes option _inside_ the monad

-- theorem simulateQ_ne_none_of_neverFails [Monad m] (so : QueryImpl spec (OptionT m))
--     (oa : OracleComp spec α)
--     (h : oa.neverFails) : simulateQ so oa ≠ Option.none := by
--   induction oa using OracleComp.construct with
--   | pure x => simp
--   | query_bind q r ih => simp [simulateQ]
--   | failure => simp [neverFails] at h

end SimulateNeverFails

-- We can then use the rest of the `simulateQ` lemmas
theorem simulateQ'_eq_simulateQ [AlternativeMonad m] [LawfulMonad m]
    {so : QueryImpl spec m} (oa : OracleComp spec α) (h : oa.neverFails) :
      simulateQ' so oa h = simulateQ so oa := by
  induction oa using OracleComp.inductionOn with
  | pure x => simp [simulateQ_pure]
  | query_bind i q r ih =>
    simp at h ⊢; rw [simulateQ'_query_bind (h := h)]
    conv =>
      enter [1, 2, x]
      apply ih x (h x)
    congr
  | failure => simp [neverFails] at h

@[reducible]
def SimOracle.Stateful (spec : OracleSpec ι) (specₜ : OracleSpec ιₜ) (σ : Type) :=
  QueryImpl spec (StateT σ (OracleComp specₜ))

@[reducible]
def SimOracle.Stateless (spec : OracleSpec ι) (specₜ : OracleSpec ιₜ) :=
  QueryImpl spec (OracleComp specₜ)

set_option pp.universes true

@[reducible]
def SimOracle.Impl (spec : OracleSpec ι) := SimOracle.Stateless spec []ₒ

#print SimOracle.Stateless

namespace SimOracle

variable {ι₁ ι₂ ιₜ₁ ιₜ₂ : Type} {spec : OracleSpec ι} {spec₁ : OracleSpec ι₁}
  {spec₂ : OracleSpec ι₂} {specₜ : OracleSpec ιₜ} {specₜ₁ : OracleSpec ιₜ₁}
  {specₜ₂ : OracleSpec ιₜ₂} {σ τ α β : Type}

variable [DecidableEq ι]

open OracleSpec

def fnOracle (spec : OracleSpec ι) (f : (i : ι) → spec.domain i → spec.range i) :
    SimOracle.Impl spec where
  impl | query i t => pure (f i t)

def statelessOracle (baseSpec : OracleSpec ιₜ) (spec : OracleSpec ι)
    (f : (i : ι) → spec.domain i → spec.range i) :
    SimOracle.Stateless (baseSpec ++ₒ spec) baseSpec where
  impl
  | query (.inl i) t => query i t
  | query (.inr i) t => pure (f i t)

-- instance : (loggingOracle (spec := spec)).IsTracking where
--   state_indep | query _ _, _ => rfl

def append' (so₁ : SimOracle.Stateful spec₁ specₜ₁ σ) (so₂ : SimOracle.Stateful spec₂ specₜ₂ τ) :
    SimOracle.Stateful (spec₁ ++ₒ spec₂) (specₜ₁ ++ₒ specₜ₂) (σ × τ) where
  impl
  | query (.inl i) t => fun (s₁, s₂) ↦ do
      let (u, s₁') ← so₁.impl (query i t) s₁; return (u, s₁', s₂)
  | query (.inr i) t => fun (s₁, s₂) ↦ do
      let (u, s₂') ← so₂.impl (query i t) s₂; return (u, s₁, s₂')

def dedup {ι : Type} (spec : OracleSpec ι) : SimOracle.Stateless (spec ++ₒ spec) spec where
  impl
  | query (.inl i) t => query i t
  | query (.inr i) t => query i t

-- theorem append'_dedup (so₁ : SimOracle spec₁ specₜ σ) (so₂ : SimOracle spec₂ specₜ τ) :
--     append so₁ so₂ = (dedup specₜ ∘ₛ append' so₁ so₂).equivState (.prodPUnit _) := by
--   sorry

-- /-- Answer all oracle queries to `oSpec` with a deterministic function `f` having the same domain
--   and range as `oSpec`. -/
-- def fnOracle {ι : Type} (spec : OracleSpec ι)
--     (f : (i : ι) → spec.domain i → spec.range i) : SimOracle spec []ₒ PUnit :=
--   statelessOracle fun (query i q) ↦ pure (f i q)

def lift {ι₁ ι₂ ι : Type} {σ : Type} (oSpec₁ : OracleSpec ι₁) (oSpec₂ : OracleSpec ι₂)
    (oSpec : OracleSpec ι) (so : SimOracle.Stateful oSpec₁ oSpec₂ σ) :
      SimOracle.Stateful (oSpec ++ₒ oSpec₁) (oSpec ++ₒ oSpec₂) σ where
  impl := fun q s => match q with
    | query (.inl i) q => do return ⟨← query i q, s⟩
    | query (.inr i) q => so.impl (query (spec := oSpec₁) i q) s

-- def liftLeft' {ι₁ ι₂ ι : Type} {σ : Type} {oSpec₁ : OracleSpec ι₁} {oSpec₂ : OracleSpec ι₂}
--     (oSpec : OracleSpec ι) (so : SimOracle oSpec₁ oSpec₂ σ) :
--       SimOracle (oSpec ++ₒ oSpec₁) (oSpec ++ₒ oSpec₂) σ :=
--   (append' idOracle so).equivState (.punitProd σ)

def liftLeftNil {ι : Type} {σ : Type} (oSpec : OracleSpec ι) :
    SimOracle.Stateful ([]ₒ ++ₒ oSpec) oSpec σ where impl
  | query (.inr i) q => fun s ↦ do return ⟨← query i q, s⟩

def liftRightNil {ι : Type} {σ : Type} (oSpec : OracleSpec ι) :
    SimOracle.Stateful (oSpec ++ₒ []ₒ) oSpec σ where impl
  | query (.inl i) q => fun s ↦ do return ⟨← query i q, s⟩

end SimOracle

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

-- @[reducible]
-- def SimOracle.Stateful (spec : OracleSpec ι) (specₜ : OracleSpec ιₜ) (σ : Type) :=
--   QueryImpl spec (StateT σ (OracleComp specₜ))

-- @[reducible]
-- def SimOracle.Stateless (spec : OracleSpec ι) (specₜ : OracleSpec ιₜ) :=
--   QueryImpl spec (OracleComp specₜ)

-- set_option pp.universes true

-- @[reducible]
-- def SimOracle.Impl (spec : OracleSpec ι) := SimOracle.Stateless spec []ₒ

-- #print SimOracle.Stateless

-- namespace SimOracle

-- variable {ι₁ ι₂ ιₜ₁ ιₜ₂ : Type} {spec : OracleSpec ι} {spec₁ : OracleSpec ι₁}
--   {spec₂ : OracleSpec ι₂} {specₜ : OracleSpec ιₜ} {specₜ₁ : OracleSpec ιₜ₁}
--   {specₜ₂ : OracleSpec ιₜ₂} {σ τ α β : Type}

-- variable [DecidableEq ι]

-- open OracleSpec

-- def fnOracle (spec : OracleSpec ι) (f : (t : spec.Domain) → spec.Range t) :
--     SimOracle.Impl spec where
--   impl | query i t => pure (f i t)

-- def statelessOracle (baseSpec : OracleSpec ιₜ) (spec : OracleSpec ι)
--     (f : (i : ι) → spec.domain i → spec.range i) :
--     SimOracle.Stateless (baseSpec + spec) baseSpec where
--   impl
--   | query (.inl i) t => query i t
--   | query (.inr i) t => pure (f i t)

-- -- instance : (loggingOracle (spec := spec)).IsTracking where
-- --   state_indep | query _ _, _ => rfl

-- def append' (so₁ : SimOracle.Stateful spec₁ specₜ₁ σ) (so₂ : SimOracle.Stateful spec₂ specₜ₂ τ) :
--     SimOracle.Stateful (spec₁ + spec₂) (specₜ₁ + specₜ₂) (σ × τ) where
--   impl
--   | query (.inl i) t => fun (s₁, s₂) ↦ do
--       let (u, s₁') ← so₁.impl (query i t) s₁; return (u, s₁', s₂)
--   | query (.inr i) t => fun (s₁, s₂) ↦ do
--       let (u, s₂') ← so₂.impl (query i t) s₂; return (u, s₁, s₂')

-- def dedup {ι : Type} (spec : OracleSpec ι) : SimOracle.Stateless (spec + spec) spec
--   | query (.inl i) t => query i t
--   | query (.inr i) t => query i t

-- -- theorem append'_dedup (so₁ : SimOracle spec₁ specₜ σ) (so₂ : SimOracle spec₂ specₜ τ) :
-- --     append so₁ so₂ = (dedup specₜ ∘ₛ append' so₁ so₂).equivState (.prodPUnit _) := by
-- --   sorry

-- -- /-- Answer all oracle queries to `oSpec` with a deterministic function `f` having the same domain
-- --   and range as `oSpec`. -/
-- -- def fnOracle {ι : Type} (spec : OracleSpec ι)
-- --     (f : (i : ι) → spec.domain i → spec.range i) : SimOracle spec []ₒ PUnit :=
-- --   statelessOracle fun (query i q) ↦ pure (f i q)

-- def lift {ι₁ ι₂ ι : Type} {σ : Type} (oSpec₁ : OracleSpec ι₁) (oSpec₂ : OracleSpec ι₂)
--     (oSpec : OracleSpec ι) (so : SimOracle.Stateful oSpec₁ oSpec₂ σ) :
--       SimOracle.Stateful (oSpec + oSpec₁) (oSpec + oSpec₂) σ where
--   impl := fun q s => match q with
--     | query (.inl i) q => do return ⟨← query i q, s⟩
--     | query (.inr i) q => so.impl (query (spec := oSpec₁) i q) s

-- -- def liftLeft' {ι₁ ι₂ ι : Type} {σ : Type} {oSpec₁ : OracleSpec ι₁} {oSpec₂ : OracleSpec ι₂}
-- --     (oSpec : OracleSpec ι) (so : SimOracle oSpec₁ oSpec₂ σ) :
-- --       SimOracle (oSpec + oSpec₁) (oSpec + oSpec₂) σ :=
-- --   (append' idOracle so).equivState (.punitProd σ)

-- def liftLeftNil {ι : Type} {σ : Type} (oSpec : OracleSpec ι) :
--     SimOracle.Stateful ([]ₒ + oSpec) oSpec σ where impl
--   | query (.inr i) q => fun s ↦ do return ⟨← query i q, s⟩

-- def liftRightNil {ι : Type} {σ : Type} (oSpec : OracleSpec ι) :
--     SimOracle.Stateful (oSpec + []ₒ) oSpec σ where impl
--   | query (.inl i) q => fun s ↦ do return ⟨← query i q, s⟩

-- end SimOracle

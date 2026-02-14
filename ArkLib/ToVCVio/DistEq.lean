/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.ToVCVio.SimOracle

/-!
  # Distributional Equality of Oracle Computations

  We define distributional equality of oracle computations (or more generally, any monad `m` with
  an `HasEvalDist` instance).
-/

universe u v w

open OracleComp

namespace HasEvalDist

variable {m : Type u → Type v} [Monad m] [HasEvalSPMF m]

def eq {α : Type u} (mx my : m α) : Prop :=
  evalDist mx = evalDist my

@[simp]
theorem eq_refl {α : Type u} (mx : m α) : eq mx mx := by
  simp [eq]

theorem eq_symm {α : Type u} (mx my : m α) : eq mx my → eq my mx := by
  intro i; simp_all [eq]

theorem eq_trans {α : Type u} (mx my mz : m α) (hxy : eq mx my) (hyz : eq my mz) : eq mx mz := by
  simp [eq]
  rw [hxy, hyz]

end HasEvalDist

namespace OracleComp

-- Shouldn't have to define this separately once we have an instance `HasEvalDist (OracleComp spec)`

variable {ι : Type u} {spec : OracleSpec ι} [spec.Fintype] [spec.Inhabited] {α : Type u}

def distEq (mx my : OracleComp spec α) : Prop :=
  evalDist mx = evalDist my

@[simp]
theorem distEq_refl (mx : OracleComp spec α) : distEq mx mx := by
  simp [distEq]

theorem distEq_symm (mx my : OracleComp spec α) : distEq mx my → distEq my mx := by
  intro i; simp_all [distEq]

theorem distEq_trans (mx my mz : OracleComp spec α)
    (hxy : distEq mx my) (hyz : distEq my mz) : distEq mx mz := by
  simp [distEq]
  rw [hxy, hyz]

-- universe level issue
-- /-- Functional equality of oracle computations. This is *different* from distributional equality,
-- since the distribution of each new query when applying `evalDist` is independently random, unlike
-- a function which always returns the same value. -/
-- def fnEquiv (oa ob : OracleComp spec α) : Prop :=
--   ∀ f : (i : ι) → spec.domain i → spec.range i,
--     simulateQ (fnOracle spec f) oa = simulateQ (fnOracle spec f) ob

end OracleComp

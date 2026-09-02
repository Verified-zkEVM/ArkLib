/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks, Cody Gunton, Quang Dao, Tobias Rothmann
-/

import VCVio.OracleComp.QueryTracking.RandomOracle.Simulation
import VCVio.OracleComp.SimSemantics.OptionT.Basic
import VCVio.OracleComp.SimSemantics.StateT.Basic

/-! Compatibility import for additions that now live in VCVio.

`simulateQ_randomOracle_map_uniformFin` now lives in
`VCVio/OracleComp/QueryTracking/RandomOracle/Simulation.lean`, which this file imports so the name
keeps resolving for downstream consumers.

Worth knowing when deduplicating against VCVio: the local copy was identical in statement and proof,
yet no "already declared" error ever fired, because the two sat at root scope in *different* modules
— nothing imported both at once. A green build therefore does not certify the absence of duplicates;
names must also be checked against the dependency's sources directly. -/

open OracleComp

/-- `simulateQ` fixes `OptionT` `pure` values: the simulated pure computation is pure.
Complements VCVio's `simulateQ_optionT_bind`/`simulateQ_optionT_bind_run` family
(`VCVio/OracleComp/SimSemantics/OptionT/Basic.lean`); upstream candidate. -/
lemma simulateQ_optionT_pure {ι : Type}
    {oSpec : OracleSpec ι} {M : Type → Type}
    [Monad M] [LawfulMonad M] (impl : QueryImpl oSpec M) {X : Type} (x : X) :
    simulateQ impl (pure x : OptionT (OracleComp oSpec) X) =
      (pure x : OptionT M X) := by
  apply OptionT.ext
  change simulateQ impl (pure (some x)) = pure (some x)
  exact simulateQ_pure impl (some x)

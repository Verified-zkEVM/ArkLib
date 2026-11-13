/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import AxiomSweepTestFixtures.Solicited

/-! # Forbidden consumers, excluded when only the Solicited root is swept -/

public section

namespace AxiomSweepTestFixtures.SolicitedConsumer

private theorem hidden : True := AxiomSweepTestFixtures.Solicited.second

theorem direct : True := AxiomSweepTestFixtures.Solicited.first

theorem transitive : True := hidden

end AxiomSweepTestFixtures.SolicitedConsumer

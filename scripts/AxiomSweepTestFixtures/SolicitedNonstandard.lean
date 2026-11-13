/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import AxiomSweepTestFixtures.Tainted.AxiomInType

/-! # Solicited entries cannot hide non-standard axioms in their statements -/

public section

namespace AxiomSweepTestFixtures.SolicitedNonstandard

/-- Solicited proof: see <https://github.com/Verified-zkEVM/ArkLib/issues/1352>. -/
theorem bad : AxiomSweepTestFixtures.Tainted.typeIndex = 0 := sorryAx _ true

end AxiomSweepTestFixtures.SolicitedNonstandard

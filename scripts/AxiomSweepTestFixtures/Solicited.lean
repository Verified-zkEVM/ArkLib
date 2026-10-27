/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

/-! # Solicited-proof fixtures for axiomsweep -/

public section

namespace AxiomSweepTestFixtures.Solicited

/-- Solicited proof: see <https://github.com/Verified-zkEVM/ArkLib/issues/1352>. -/
theorem first : True := sorryAx True true

/-- Solicited proof: see <https://github.com/Verified-zkEVM/ArkLib/issues/1352>. -/
theorem second : True := first

/-- A proved declaration must not be listed, even with the right link:
https://github.com/Verified-zkEVM/ArkLib/issues/1352 -/
theorem proved : True := True.intro

end AxiomSweepTestFixtures.Solicited

/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

/-! # Axiom-in-type fixture for axiomsweep -/

public section

namespace AxiomSweepTestFixtures.Tainted

axiom typeIndex : Nat

axiom axiomInType : Fin (typeIndex + 1)

end AxiomSweepTestFixtures.Tainted

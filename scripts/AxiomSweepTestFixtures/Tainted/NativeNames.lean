/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

/-! # Native-axiom name-normalization fixtures for axiomsweep -/

public section

namespace AxiomSweepTestFixtures.Tainted.Generated._native.native_decide

axiom ax_12_34 : True

end AxiomSweepTestFixtures.Tainted.Generated._native.native_decide

namespace AxiomSweepTestFixtures.Tainted.Collision._native.native_decide

axiom ax_12_extra : True
axiom ax_x_34 : True

namespace ax_12_34

axiom extra : True

end ax_12_34

end AxiomSweepTestFixtures.Tainted.Collision._native.native_decide

namespace AxiomSweepTestFixtures.Tainted

theorem generatedNativeUser : True := Generated._native.native_decide.ax_12_34

theorem collisionUser : True := Collision._native.native_decide.ax_12_extra

theorem collisionNondecimalUser : True := Collision._native.native_decide.ax_x_34

theorem collisionExtraSegmentUser : True :=
  Collision._native.native_decide.ax_12_34.extra

end AxiomSweepTestFixtures.Tainted

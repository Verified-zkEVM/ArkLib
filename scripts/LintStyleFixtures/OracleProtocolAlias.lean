/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Interaction.Core.Signature

/-! The exact alias exception, accepted only under its authorized module identity. -/

open PFunctor

namespace Interaction.Core

universe u q

set_option linter.checkUnivs false in
/-- An oracle protocol is authored directly over the oracle polynomial. -/
abbrev OracleProtocol := FreeM OraclePoly.{u, q} PUnit.{u + 1}

end Interaction.Core

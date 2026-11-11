/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

/-! The maintainer-authorized universe-linter exception for the oracle protocol type alias. -/

namespace ArkLib.LintStyle

/-- Only this source module may contain the authorized alias exception. -/
def oracleProtocolModule : String := "ArkLib.Interaction.Core.Protocol"

/-- The source pass requires the exact repository path as well as the exact alias command. -/
def oracleProtocolPath : String := "ArkLib/Interaction/Core/Protocol.lean"

/-- The complete authorized command. Other declarations, bodies and option scopes are rejected. -/
def oracleProtocolAliasLines : Array String := #[
  "set_option linter.checkUnivs false in",
  "/-- An oracle protocol is authored directly over the oracle polynomial. -/",
  "abbrev OracleProtocol := FreeM OraclePoly.{u, q} PUnit.{u + 1}"]

end ArkLib.LintStyle

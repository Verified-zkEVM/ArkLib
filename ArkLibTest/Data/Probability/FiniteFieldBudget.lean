/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.Probability.FiniteFieldBudget
import ArkLib.Data.Probability.StridedQueryBoundary
import ArkLibExamples.ReedSolomon.ProveKit.ExpectedPayload

/-!
# Acceptance checks for finite-field and authentication budgets

The small cases distinguish the inclusive grinding threshold, height-three level factor three,
target OOD count in a transition, and repeated-query treatment at a strided opening.
-/

namespace ArkLibTest.FiniteFieldBudget

open ArkLib.FiniteFieldBudget ArkLib.UniformQueryBoundary
open ArkLibExamples.ReedSolomon

example : QueryMeetsTarget 4 0 1 2 1 1 := by norm_num [QueryMeetsTarget]

-- Accepting hashes through T includes T itself. Omitting the +1 would reverse this check.
example : QueryFailsTarget 4 2 1 2 1 2 := by norm_num [QueryFailsTarget]

example : RepeatedOodMeetsTarget 2 2 4 2 1 := by norm_num [RepeatedOodMeetsTarget]

example : TensorFoldIdentityMeetsTarget 1 1 0 4 1 := by
  norm_num [TensorFoldIdentityMeetsTarget]

-- Three shared challenge levels cost three width-independent level events.
example : ¬TensorFoldIdentityMeetsTarget 3 1 0 5 1 := by
  norm_num [TensorFoldIdentityMeetsTarget]

example : TransitionMeetsTarget 1 1 1 10 1 := by norm_num [TransitionMeetsTarget]

example : ¬TransitionMeetsTarget 1 2 1 10 1 := by norm_num [TransitionMeetsTarget]

example : binaryAuthenticationCount 3 (strideLeaves 1 {0, 1, 3}) = 4 := by decide

-- A repeated requested row changes no authentication boundary.
example : binaryAuthenticationCount 3 (strideLeaves 1 {0, 1, 1, 3}) = 4 := by decide

example : (795647584 : ℚ) / 10000 < ProveKit.passportExpectedSaving ∧
    ProveKit.passportExpectedSaving < (795647587 : ℚ) / 10000 :=
  ProveKit.passportExpectedSaving_interval

end ArkLibTest.FiniteFieldBudget

/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Commitments.Functional.Hachi.TraceHead.Commitment

/-!
# Hachi §3.1 scalar trace head

`Coordinates` instantiates finite-free packing with the actual fixed subring and `psi` basis.
`Coefficients` packs the last variables' monomial coefficients. `Protocol` sends one ring
value, checks the scaled trace equality, and hands the unchanged weak opening to `relPolyEval`.
`Completeness` and `Commitment` supply honest execution and coverage by the real balanced-gadget
committer, including the additional message bound used by the nonrecursive honest chain.

The new proofs use only the fixed subring's ring structure. Identifying it with the field
`GF(q^k)` still belongs to `Subfield/Field.lean`, whose existing unfinished theorem is not used
here. The existing finite-sum `traceH` and fixed-subring definitions are noncomputable, so these
are exact semantic protocol definitions, not an executable scalar-opening implementation.
The recursive §4.5 trace handoff is a separate protocol and is not repaired here.
-/

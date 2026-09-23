/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Intervals

/-!
# Finite sums over shifted natural-number ranges

Mathlib's `Finset.sum_Ico_eq_sum_range` expresses a shifted range sum as an interval sum, and
`Finset.sum_range_add` splits it into adjacent chunks. Four- and two-chunk forms follow by
repeated applications of the split theorem.

## Main statements

* `Finset.sum_Ico_eq_sum_range`: the shifted range sum as an interval sum.
* `Finset.sum_range_add`: the sum over adjacent ranges as the sum of the two chunks.

## References
-/

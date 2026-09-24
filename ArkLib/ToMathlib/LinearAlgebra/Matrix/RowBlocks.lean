/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.ToMathlib.LinearAlgebra.Matrix.Rank

/-!
# Matrix row-block rank bounds

The rank bound for matrices with product row indices is available from the matrix rank API.

## Main statements

* `Matrix.rank_prod_rows_le_sum`: a product-row matrix has rank at most the sum of its block ranks.

## References

* [DKT26]
-/

@[expose] public section

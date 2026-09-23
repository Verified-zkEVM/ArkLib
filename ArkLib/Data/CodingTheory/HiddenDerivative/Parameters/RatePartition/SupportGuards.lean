/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.PartitionSupport.RateBound

/-!
# Rate-dependent partition-support interface

The rate-dependent total jet-degree bound is available with the partition-support API.

## Main statements

* `partitionSupport_totalJetDegree_le_rateJetCap`: eligible exponents satisfy the rate-dependent
  total jet-degree cap.

## References

* [DKT26]
-/

@[expose] public section

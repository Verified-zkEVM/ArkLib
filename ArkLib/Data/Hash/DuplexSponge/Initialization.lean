/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Yuxi Zheng, Michele Orrù
-/
module

public import ArkLib.Data.Hash.DuplexSponge
public import CompPoly.Data.Classes.HasSize

/-!
# Fixed-state duplex initialization

Initial objects are encoded transcript inputs. Initialization starts from the fixed public zero
state and absorbs that encoding through the rate. The absorber owns the resulting cursors.
-/

@[expose] public section

open OracleComp OracleSpec

namespace DuplexSponge

variable {U : Type} [SpongeUnit U] [SpongeSize]

/-- The fixed public starting sponge, before absorption of an initial object. -/
def zeroStart : CanonicalDuplexSponge U where
  state := Vector.replicate SpongeSize.N (0 : U)
  absorbPos := 0
  squeezePos := Fin.last SpongeSize.R

/-- Encode and absorb an initial object using the same embedding requirements as ordinary
messages. The returned cursors are the absorber's actual cursors. -/
def absorbInitialObject {Object : Type} [HasSize Object U] (obj : Object) :
    OracleComp (forwardPermutationOracle (CanonicalSpongeState U)) (CanonicalDuplexSponge U) :=
  zeroStart.absorb ((HasSize.toFun (α := Object) (β := U)) obj).toList

end DuplexSponge

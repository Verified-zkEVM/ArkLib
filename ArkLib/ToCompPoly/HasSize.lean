/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
module

public import CompPoly.Data.Classes.HasSize
public import Init.Data.Vector.Lemmas

/-!
# Product encodings of fixed size

An explicit product embedding concatenates two fixed-length injective encodings. This is useful
for transcript contexts such as `(session identifier, statement)` without imposing a global
encoding instance on every product type.
-/

@[expose] public section

namespace HasSize

/-- Encode a pair in component order. Fixed component lengths make the concatenation injective. -/
@[instance_reducible]
def prod {α β U : Type} [HasSize α U] [HasSize β U] : HasSize (α × β) U where
  size := size α U + size β U
  toFun :=
    { toFun := fun pair => (HasSize.toFun (α := α) (β := U)) pair.1 ++
        (HasSize.toFun (α := β) (β := U)) pair.2
      inj' := by
        intro a b h
        have hparts := Vector.append_inj h
        exact Prod.ext (HasSize.toFun.injective hparts.1)
          (HasSize.toFun.injective hparts.2) }

end HasSize

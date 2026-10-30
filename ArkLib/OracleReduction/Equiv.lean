/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.OracleReduction.Security.Basic
public import ArkLib.OracleReduction.LiftContext.OracleReduction

/-!
  # Equivalence / Isomorphism of Oracle Reductions

  This file defines equivalences between protocol specifications.
  Observational equivalence between provers and verifiers is not yet formalized.
-/

@[expose] public section

namespace ProtocolSpec

-- #check Equiv.instEquivLike

/-- Two protocol specifications are equivalent if they have the same number of rounds, same
  direction for each round, and an equivalence of types for each round. -/
@[ext]
structure Equiv {m n : ℕ} (pSpec : ProtocolSpec m) (pSpec' : ProtocolSpec n) where
  round_eq : m = n
  dir_eq : ∀ i, pSpec.dir i = pSpec'.dir (Fin.cast round_eq i)
  typeEquiv : ∀ i, pSpec.«Type» i ≃ pSpec'.«Type» (Fin.cast round_eq i)

namespace Equiv

-- Note: this is not quite an `EquivLike` since `pSpec`s are terms, not types

variable {m n k : ℕ} {pSpec : ProtocolSpec m} {pSpec' : ProtocolSpec n} {pSpec'' : ProtocolSpec k}

@[simps]
def refl (pSpec : ProtocolSpec n) : Equiv pSpec pSpec where
  round_eq := rfl
  dir_eq := fun _ => rfl
  typeEquiv := fun _ => _root_.Equiv.refl _

def symm (eqv : Equiv pSpec pSpec') : Equiv pSpec' pSpec where
  round_eq := eqv.round_eq.symm
  dir_eq := fun i => by simp [eqv.dir_eq]
  typeEquiv := fun i => (eqv.typeEquiv (Fin.cast (eqv.round_eq.symm) i)).symm

/-- Compose protocol specification equivalences (spelled `equivTrans` because `trans` is
reserved). -/
def equivTrans (eqv : Equiv pSpec pSpec') (eqv' : Equiv pSpec' pSpec'') : Equiv pSpec pSpec'' where
  round_eq := eqv.round_eq.trans eqv'.round_eq
  dir_eq := fun i => by simp [eqv.dir_eq, eqv'.dir_eq]
  typeEquiv := fun i =>
    _root_.Equiv.trans (eqv.typeEquiv i) (eqv'.typeEquiv (Fin.cast eqv.round_eq i))

end Equiv


end ProtocolSpec



variable {n : ℕ} {pSpec pSpec' : ProtocolSpec n}

namespace Reduction

end Reduction

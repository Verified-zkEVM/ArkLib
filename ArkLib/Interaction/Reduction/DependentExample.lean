/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Interaction.Reduction

/-!
# A genuinely dependent composed reduction

This executable acceptance client prevents `Reduction.comp` from collapsing to a fixed suffix.
The prefix sends a `Bool`. A `false` prefix selects a `Bool` suffix message, while a `true` prefix
selects a `Fin 3` suffix message. Both branches execute through the same composed reduction.
-/

namespace Interaction.Reduction.DependentExample

open TwoParty

/-- The first interaction sends one Boolean. -/
def prefixTree : TypeTree := TypeTree.node Bool (fun _ => TypeTree.done)

/-- The focal participant sends the prefix Boolean. -/
def prefixRoles : RoleDecoration prefixTree := ⟨Role.sender, fun _ => ⟨⟩⟩

/-- The continuation tree changes its message type according to the complete prefix path. -/
def suffixTree : TypeTree.Path prefixTree → TypeTree
  | ⟨false, ⟨⟩⟩ => TypeTree.node Bool (fun _ => TypeTree.done)
  | ⟨true, ⟨⟩⟩ => TypeTree.node (Fin 3) (fun _ => TypeTree.done)

/-- The focal participant also sends the suffix message. -/
def suffixRoles : (tr : TypeTree.Path prefixTree) → RoleDecoration (suffixTree tr)
  | ⟨false, ⟨⟩⟩ => ⟨Role.sender, fun _ => ⟨⟩⟩
  | ⟨true, ⟨⟩⟩ => ⟨Role.sender, fun _ => ⟨⟩⟩

abbrev PrefixStatement (_ : Unit) := Unit
abbrev PrefixWitness (_ : Unit) := Bool
abbrev MidStatement (_ : Unit) (_ : TypeTree.Path prefixTree) := Bool
abbrev MidWitness (_ : Unit) (_ : TypeTree.Path prefixTree) := Unit

/-- The prefix reduction forwards the sent Boolean as its next statement. -/
def prefixReduction : Reduction Id Unit (fun _ => prefixTree) (fun _ => prefixRoles)
    PrefixStatement PrefixWitness MidStatement MidWitness where
  prover _ _ bit := ⟨bit, ⟨bit, ()⟩⟩
  verifier _ _ bit := bit

abbrev SuffixShared := (i : Unit) × PrefixStatement i × TypeTree.Path prefixTree
abbrev SuffixStatement (shared : SuffixShared) := MidStatement shared.1 shared.2.2
abbrev SuffixWitness (shared : SuffixShared) := MidWitness shared.1 shared.2.2

/-- The suffix emits a branch-specific message and turns it into a natural-number statement.

The explicit dependent match is the acceptance canary: the two branches cannot be replaced by one
constant continuation tree because their move types differ. -/
def suffixReduction : Reduction Id SuffixShared
    (fun shared => suffixTree shared.2.2)
    (fun shared => suffixRoles shared.2.2)
    SuffixStatement SuffixWitness
    (fun _ _ => Nat) (fun _ _ => Unit) where
  prover shared _ _ :=
    match shared with
    | ⟨(), (), ⟨false, ⟨⟩⟩⟩ => ⟨false, ⟨0, ()⟩⟩
    | ⟨(), (), ⟨true, ⟨⟩⟩⟩ => ⟨(2 : Fin 3), ⟨2, ()⟩⟩
  verifier shared _ :=
    match shared with
    | ⟨(), (), ⟨false, ⟨⟩⟩⟩ => fun (bit : Bool) => (if bit then 1 else 0 : Nat)
    | ⟨(), (), ⟨true, ⟨⟩⟩⟩ => fun (value : Fin 3) => value.val

/-- The dependent two-stage reduction produced by `Reduction.comp`. -/
def composed := Reduction.comp
  (ctx₂ := fun _ => suffixTree)
  (roles₂ := fun _ => suffixRoles)
  (StmtOut := fun _ _ _ => Nat)
  (WitOut := fun _ _ _ => Unit)
  prefixReduction suffixReduction

/-- The false prefix selects the Boolean continuation branch. -/
example : (composed.execute () () false).1 =
    ⟨false, false, ⟨⟩⟩ := rfl

/-- The true prefix selects the `Fin 3` continuation branch. -/
example : (composed.execute () () true).1 =
    ⟨true, (2 : Fin 3), ⟨⟩⟩ := rfl

/-- Both honest participants agree on the final statement in the Boolean branch. -/
example : composed.execute () () false =
    let tr₁ : TypeTree.Path prefixTree := ⟨false, ⟨⟩⟩
    let tr₂ : TypeTree.Path (suffixTree tr₁) := ⟨false, ⟨⟩⟩
    ⟨PFunctor.FreeM.Path.append prefixTree suffixTree tr₁ tr₂,
      ⟨PFunctor.FreeM.Path.packAppend prefixTree suffixTree (fun _ _ => Nat) tr₁ tr₂ 0,
        PFunctor.FreeM.Path.packAppend prefixTree suffixTree (fun _ _ => Unit) tr₁ tr₂ ()⟩,
      PFunctor.FreeM.Path.packAppend prefixTree suffixTree (fun _ _ => Nat) tr₁ tr₂ 0⟩ := rfl

/-- Both honest participants agree on the final statement in the `Fin 3` branch. -/
example : composed.execute () () true =
    let tr₁ : TypeTree.Path prefixTree := ⟨true, ⟨⟩⟩
    let tr₂ : TypeTree.Path (suffixTree tr₁) := ⟨(2 : Fin 3), ⟨⟩⟩
    ⟨PFunctor.FreeM.Path.append prefixTree suffixTree tr₁ tr₂,
      ⟨PFunctor.FreeM.Path.packAppend prefixTree suffixTree (fun _ _ => Nat) tr₁ tr₂ 2,
        PFunctor.FreeM.Path.packAppend prefixTree suffixTree (fun _ _ => Unit) tr₁ tr₂ ()⟩,
      PFunctor.FreeM.Path.packAppend prefixTree suffixTree (fun _ _ => Nat) tr₁ tr₂ 2⟩ := rfl

end Interaction.Reduction.DependentExample

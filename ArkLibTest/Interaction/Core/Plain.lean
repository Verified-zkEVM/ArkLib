import ArkLib.Interaction.Core.Execution

/-! Acceptance examples for shape independence, recorded challenges and terminal effects. -/

open PFunctor PFunctor.FreeM Interaction.Core Interaction.TwoParty.Lens

namespace Interaction.Core.Tests

def done : Protocol := .pure ⟨⟩
def coin : Protocol := .liftBind (.challenge Bool) (fun _ => done)

example : projectPathAlong plainSig coin ⟨true, ⟨⟩⟩ =
    projectPathAlong plainSig coin ⟨false, ⟨⟩⟩ := rfl

def branching : Protocol :=
  .liftBind (.message Bool) (fun (b : Bool) => if b = true then coin else done)

example : branching =
    .liftBind (.message Bool) (fun (b : Bool) => if b = true then coin else done) := rfl

example : projectPathAlong plainSig branching ⟨false, ⟨⟩⟩ ≠
    projectPathAlong plainSig branching ⟨true, ⟨true, ⟨⟩⟩⟩ := by
  intro h
  have := congrArg Sigma.fst h
  exact Bool.false_ne_true this

def echo : Focal plainSig Id coin (fun _ => Bool) := fun b => b

def trueCoin : Counterpart plainSig Id coin (fun _ => PUnit) := ⟨true, ⟨⟩⟩
def falseCoin : Counterpart plainSig Id coin (fun _ => PUnit) := ⟨false, ⟨⟩⟩

example : (Interaction.TwoParty.Lens.run (OutC := fun _ => PUnit) coin echo trueCoin).2.1 =
    true := by
  rfl

example : (Interaction.TwoParty.Lens.run (OutC := fun _ => PUnit) coin echo falseCoin).2.1 =
    false := by
  rfl

def leaf : Focal plainSig (StateM Nat) done (fun _ => Nat) := do
  modify (· + 1)
  get

def leafSampler : Counterpart plainSig (StateM Nat) done (fun _ => PUnit) := pure ⟨⟩

example : (Interaction.TwoParty.Lens.run (OutC := fun _ => PUnit) done leaf leafSampler).run 0 =
    (⟨⟨⟩, 1, ⟨⟩⟩, 1) := by
  rfl

run_cmd do
  unless ((Interaction.TwoParty.Lens.run (OutC := fun _ => PUnit)
    done leaf leafSampler).run 0).2 == 1 do
    throwError "the zero-round leaf must execute exactly once"

end Interaction.Core.Tests

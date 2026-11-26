/-!
Declarations that satisfy the universe rule of record D2, or that the fixture allowlist covers.
`scripts/test-universe-rule.sh` expects `lake exe universe-rule` to accept this module with
`allowlist.txt` and to report only `AdversaryModel` without it.
-/

namespace UniverseRuleTestFixtures.Pass

/-- An argument type determines `u`. -/
def pick.{u} {α : Type u} (b : Bool) (x y : α) : α :=
  match b with
  | true => x
  | false => y

/-- The monad argument determines the result universe `v`. -/
def twice.{v} (m : Type → Type v) [Monad m] (x : m Unit) : m Unit := x *> x

/-- A parameter determines the structure's universe. Lean generates a constructor, projections,
a recursor, `noConfusion`, injectivity lemmas and a derived instance from it. -/
structure Box.{u} (α : Type u) where
  val : α
  deriving Inhabited

/-- An inductive type with a parameter, and a structurally recursive function on it. -/
inductive Tree.{u} (α : Type u) where
  | leaf
  | node (a : α) (l r : Tree α)

def Tree.size.{u} {α : Type u} : Tree α → Nat
  | .leaf => 0
  | .node _ l r => l.size + r.size + 1

/-- A hypothesis is an argument too, and its type determines `u`. -/
theorem box_val.{u} {α : Type u} (b : Box α) (h : b.val = b.val) : b.val = b.val := h

/-- The adversary universe: no argument determines `w`, and the fixture allowlist records it
with reason `adversary`. -/
structure AdversaryModel.{w} (S : Type) where
  Adv : S → Type w

/-- A declaration that takes an adversary model: the model argument determines `w`. -/
def Secure.{w} {S : Type} (M : AdversaryModel.{w} S) (good : (s : S) → M.Adv s → Prop) : Prop :=
  ∀ s (a : M.Adv s), good s a

/-- No universe parameters at all. -/
def three : Nat := 3

end UniverseRuleTestFixtures.Pass

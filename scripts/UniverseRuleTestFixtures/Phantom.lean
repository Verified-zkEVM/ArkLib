/-!
A limitation of the universe rule of record D2. The rule is syntactic: each universe parameter
occurs in the type of an argument. It does not guarantee that unification determines the
universe at a use. `scripts/test-universe-rule.sh` expects `lake exe universe-rule` to accept
this module, which documents the gap.
-/

namespace UniverseRuleTestFixtures.Phantom

/-- A type that ignores its argument: `Carrier α` reduces to `Nat` for every `α`. -/
def Carrier.{u} (_ : Type u) : Type := Nat

/-- The argument type `Carrier PUnit.{u + 1}` mentions `u`, so `hidden` satisfies the rule. That
occurrence disappears when the type reduces to `Nat`. A client such as
`theorem reuseHidden (x : Nat) (h : hidden x) : hidden x := h` therefore fails: `h` has type
`hidden.{u_1} x`, and the goal is `hidden.{u_2} x`. -/
def hidden.{u} (x : Carrier PUnit.{u + 1}) : Prop :=
  ∃ β : Type u, Nonempty β ∧ x = x

end UniverseRuleTestFixtures.Phantom

/-!
Declarations that break the universe rule of record D2. `scripts/test-universe-rule.sh` expects
`lake exe universe-rule` to reject this module and to report exactly the violations it lists.
-/

namespace UniverseRuleTestFixtures.Fail

/-- A constant without arguments: each use gets a fresh `u`. -/
def noArgs.{u} : List (ULift.{u} Nat) := []

/-- Only a structure field mentions `u`. The checker reports the structure once, not its
constructor, projection or derived instance. -/
structure Bundle.{u} where
  carrier : Type u
  deriving Nonempty

/-- Only the result type mentions `u`. The constructor `Marker.mk.{u} : Marker.{u}` and the
derived `Repr` instance have the structure's own universe. The checker reports only the
structure. -/
structure Marker.{u} : Type u
  deriving Repr

/-- A hand-written instance is a user declaration: the checker reports it. -/
instance instInhabitedMarker.{u} : Inhabited Marker.{u} := ⟨⟨⟩⟩

/-- Only the `Prop` body mentions `k`. -/
def HasWitness.{k} (S : Type) (R : S → Prop) : Prop :=
  ∃ (K : S → Type k) (_ : ∀ s, K s → R s), ∀ s, R s → Nonempty (K s)

/-- Two universes: an argument determines `u`, and only the result mentions `v`. -/
def lift.{u, v} (α : Type u) : Type (max u v) := ULift.{v} α

end UniverseRuleTestFixtures.Fail

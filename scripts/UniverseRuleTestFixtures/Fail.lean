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

/-! Hand-written declarations whose names look like the ones Lean generates. The checker must
report each of them: Lean's data, not the name, decides whether a constant is generated. -/

/-- Named like an equation lemma, but the namespace above it is not a constant. -/
def eq_def.{u} : Type u := PUnit

/-- Named like an equation lemma, but the namespace above it is not a constant. -/
def eq_unfold.{u} : Type u := PUnit

/-- Named like a matcher, but Lean did not register it as one. -/
def match_1.{u} : Type u := PUnit

/-- Named like an auxiliary lemma, but it is a definition below a namespace. -/
def proof_1.{u} : Type u := PUnit

/-- A structure that satisfies the rule. Lean generates `Box.mk.inj`, not `Box.inj`. -/
structure Box.{u} (α : Type u) where
  val : α

/-- Named like an injectivity lemma, but it sits below the type, not below a constructor, and
it has a universe `v` that `Box` does not have. -/
def Box.inj.{u, v} (_α : Type u) : Type v := PUnit

/-- Named like an auxiliary lemma below `Box`, with `Box`'s level parameters. It has a
declaration range, which no generated constant has. -/
theorem Box._proof_1.{u} : Nonempty (Type u) := ⟨PUnit⟩

/-- Named like a structural-recursion helper below `Box`, with `Box`'s level parameters. It has
a declaration range, which no generated constant has. -/
def Box._f.{u} : Type u := PUnit

/-- `Tiny` satisfies the rule through `α`. The instance starts on the line of `Tiny`'s
declaration, after it ends, and applies `Tiny` to a constant, not to a variable. It is
hand-written, and nothing determines its `u`. -/
structure Tiny.{u} (α : Type u) where instance sameLine.{u} : Inhabited (Tiny PUnit.{u + 1}) := ⟨⟨⟩⟩

end UniverseRuleTestFixtures.Fail

/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/
module

/-! # Proof-dependency fixtures for `axiomsweep --must-depend-on`

Each theorem below is a candidate "conformance proof" with a known answer to the question
"does its proof use `sharedLaw` (or `sharedConst`)?". `scripts/test-axiomsweep.sh` checks
the mode's verdict on every one of them.

The statement-only fixtures are written so that the elaborated proof term provably does not
mention the shared name: the statement is closed by an unrelated lemma whose type is only
definitionally equal to it. Writing `fun h => ...` instead would put the shared name into the
proof term through the binder's type, which the mode (correctly) counts as an occurrence.
-/

public section

namespace AxiomSweepTestFixtures.MustDependOn

/-- The shared law the conformance fixtures are required to use. -/
theorem sharedLaw (n : Nat) : n + 0 = n := Nat.add_zero n

/-- A shared definition, mentioned by statements that never unfold it in their proofs. -/
def sharedConst : Nat := 3

/-- An unrelated closed fact, used to prove statements without naming the shared ones. -/
theorem localFact : (3 : Nat) = 3 := rfl

/-- Uses `sharedLaw` directly in its proof: the requirement holds. -/
theorem usesDirectly : (5 : Nat) + 0 = 5 := sharedLaw 5

/-- An intermediate lemma that uses `sharedLaw`. -/
theorem intermediate (n : Nat) : n + 0 = n := sharedLaw n

/-- Uses `sharedLaw` only through `intermediate`: the requirement holds transitively. -/
theorem usesTransitively : (7 : Nat) + 0 = 7 := intermediate 7

/-- Proves the same shape of statement without `sharedLaw`: the requirement fails. -/
theorem independent : (5 : Nat) + 0 = 5 := rfl

/-- Mentions `sharedConst` only in its statement; the proof term is `localFact`, which the
kernel accepts by unfolding `sharedConst` during type checking. The requirement fails. -/
theorem constOnlyInType : sharedConst = 3 := localFact

/-- Mentions the theorem `sharedLaw` only in its statement: the requirement fails. -/
theorem lawOnlyInType : ∀ h : (2 : Nat) + 0 = 2, h = sharedLaw 2 :=
  fun _ => rfl

/-- A wrapper lemma whose *statement* mentions `sharedConst` but whose proof does not. -/
theorem constWrapper : sharedConst = 3 := localFact

/-- Reaches `sharedConst` only through the statement of `constWrapper`. Restating the claim
as a lemma is not use, so the requirement fails: intermediate theorems are entered through
their proofs, never their statements. -/
theorem constOnlyInWrapperType : sharedConst = 3 := constWrapper

/-- A private step that uses `sharedLaw`. -/
private theorem privateStep (n : Nat) : n + 0 = n := sharedLaw n

/-- Uses `sharedLaw` only through a private lemma: the requirement holds. -/
theorem usesThroughPrivate : (9 : Nat) + 0 = 9 := privateStep 9

/-- A definition whose embedded proof is abstracted into a generated `_proof_` auxiliary
theorem, so `sharedLaw` is reached only through that auxiliary: the requirement holds. -/
def usesThroughAuxProof : { n : Nat // n + 0 = n } := ⟨4, sharedLaw 4⟩

/-! Shared constants whose *bodies* use `sharedLaw`; the consumers in
`AxiomSweepTestFixtures.MustDependOn.Statement` name them in statements and in proofs. -/

/-- A relation whose body uses `sharedLaw`. -/
def relUsingLaw (n : Nat) : Prop := (⟨n, sharedLaw n⟩ : { m : Nat // m + 0 = m }).val = n

/-- A law class, with an instance whose field proof is `sharedLaw`. -/
class Law (f : Nat → Nat) : Prop where
  law : ∀ n, f n + 0 = f n

/-- The production instance: its field proof is the shared law. -/
instance idLaw : Law id := ⟨fun n => sharedLaw n⟩

/-- A profile structure carrying a law. -/
structure Profile where
  size : Nat
  law : ∀ n : Nat, n + 0 = n

/-- A profile whose law field is `sharedLaw`. -/
def lawProfile : Profile := ⟨3, sharedLaw⟩

/-- A structure whose field type mentions `relUsingLaw`. -/
structure Wrap where
  ok : relUsingLaw 0

/-- An exposed identity, rewritten by `myId_eq`. -/
@[expose] def myId (n : Nat) : Nat := n

/-- An `rfl` lemma about `myId`. -/
theorem myId_eq (n : Nat) : myId n = n := rfl

/-- Uses `sharedLaw`, but carries a gap. -/
theorem sorriedHelper (n : Nat) : n + 0 = n ∧ True := ⟨sharedLaw n, sorryAx True false⟩

/-- A production object carrying admitted debt in a field unrelated to `sharedLaw`. -/
def admittedObject : { n : Nat // n = 3 } := ⟨3, sorryAx (3 = 3) false⟩

/-- A production object whose *law* is admitted. -/
def admittedLaw : { f : Nat → Nat // ∀ n, f n + 0 = f n } := ⟨id, fun _ => sorryAx _ false⟩

/-- Refutes the negation of an instance of `sharedLaw`. -/
theorem notShared (h : ¬ ((3 : Nat) + 0 = 3)) : False := h (sharedLaw 3)

/-- An axiom: it has no proof term, so it cannot be the subject of a requirement. -/
axiom noProof : (1 : Nat) + 0 = 1

end AxiomSweepTestFixtures.MustDependOn

/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/
module

public import AxiomSweepTestFixtures.MustDependOn

/-! # Statement-blocking fixtures for `axiomsweep --must-depend-on`

Candidate conformance proofs in a module of their own, as conformance theorems sit apart
from the shared declarations they reuse. The `stmt*` and `dead*` theorems never use
`sharedLaw` in their proofs: their proof terms only repeat constants the statement names, or
mention `sharedLaw` in dead code. Before statement-blocking and dead-code removal, all of
them passed. The `use*` theorems use `sharedLaw` in their proofs and must keep passing.
-/

public section

namespace AxiomSweepTestFixtures.MustDependOn.Statement

open AxiomSweepTestFixtures.MustDependOn

/-! ## Not use: statement constants repeated by the proof, dead code, gaps -/

/-- The proof `h` repeats the statement's `relUsingLaw`, whose body uses `sharedLaw`. -/
theorem stmtRelIdentity (h : relUsingLaw 3) : relUsingLaw 3 := h

/-- The instance `idLaw` is named by the statement; `rfl` repeats it. -/
theorem stmtInstance : Law.law (self := idLaw) 0 = Nat.add_zero 0 := rfl

/-- `lawProfile` occurs only in an unused hypothesis. -/
theorem stmtDefInBinder (p : Profile) (_h : p = lawProfile) : True := trivial

/-- `Wrap` (whose field mentions `relUsingLaw`) occurs only in an unused binder. -/
theorem stmtStructureInBinder (_w : Wrap) : True := trivial

/-- `sharedLaw` occurs only in a `have` the proof never consults. -/
theorem deadHave : (5 : Nat) + 0 = 5 := by
  have _h := sharedLaw 5
  rfl

/-- `sharedLaw` occurs only in the type of a `have` the proof never consults. -/
theorem deadHaveType : (5 : Nat) + 0 = 5 := by
  have _h : sharedLaw 5 = sharedLaw 5 := rfl
  rfl

/-- `sharedLaw` occurs only at the head of a chain of unused `have`s. -/
theorem deadHaveChain : (5 : Nat) + 0 = 5 := by
  have h := sharedLaw 5
  have _h2 := h.symm
  rfl

/-- `sharedLaw` occurs only in a `have` consumed by a redex that discards it. -/
theorem deadHaveThenRedex : (5 : Nat) + 0 = 5 := by
  have h := sharedLaw 5
  exact (fun (_ : (5 : Nat) + 0 = 5) => (rfl : (5 : Nat) + 0 = 5)) h

/-- `sharedLaw` occurs only as arguments to nested redexes that discard them. -/
theorem deadNestedRedex : (5 : Nat) + 0 = 5 :=
  (fun (_ _ : (5 : Nat) + 0 = 5) => (rfl : (5 : Nat) + 0 = 5)) (sharedLaw 5) (sharedLaw 5)

/-- `sharedLaw` occurs only in a proof destructured by `obtain` and never used. -/
theorem deadObtain : (5 : Nat) + 0 = 5 := by
  obtain ⟨_n, _hn⟩ : ∃ n : Nat, n + 0 = n := ⟨0, sharedLaw 0⟩
  rfl

/-- Uses `sharedLaw`, but the proof has a gap. -/
theorem useWithSorry : (5 : Nat) + 0 = 5 ∧ True := ⟨sharedLaw 5, sorryAx True false⟩

/-- Uses `sharedLaw` through a helper that has a gap. -/
theorem useThroughSorriedHelper : (5 : Nat) + 0 = 5 := (sorriedHelper 5).1

/-- Documented false negative: `simp only` applies the `rfl` lemma `myId_eq` by
definitional unfolding, which leaves no constant in the proof term. -/
theorem simpRflUse (n : Nat) : myId (myId n) = n := by simp only [myId_eq]

/-! ## Use -/

/-- Uses `sharedLaw` through the instance `idLaw`, which the statement does not name. -/
theorem useInstance : id 3 + 0 = id 3 := Law.law 3

/-- Uses `sharedLaw` through a projection of `lawProfile`. -/
theorem useProjection : (3 : Nat) + 0 = 3 := lawProfile.law 3

/-- Uses `myId_eq` by rewriting (the statement names `myId`, not the lemma). -/
theorem useRewrite (n : Nat) : myId (myId n) = n := by rw [myId_eq, myId_eq]

/-- Uses `sharedLaw` in a match arm. -/
theorem useMatch : ∀ n : Nat, n + 0 = n
  | 0 => rfl
  | k + 1 => sharedLaw (k + 1)

/-- Uses `sharedLaw` in an induction step. -/
theorem useInduction (n : Nat) : n + 0 = n := by
  induction n with
  | zero => rfl
  | succ k _ => exact sharedLaw (k + 1)

/-- Uses the fields of a proof destructured by `obtain`, so its `sharedLaw` is used. -/
theorem useObtain : ∃ n : Nat, n + 0 = n := by
  obtain ⟨n, hn⟩ : ∃ n : Nat, n + 0 = n := ⟨0, sharedLaw 0⟩
  exact ⟨n, hn⟩

/-- Uses `sharedLaw` in a sorry-free proof whose statement names an object with admitted
debt: a gap the proof does not rely on does not count. -/
theorem useWithAdmittedStatement : admittedObject.val + 0 = admittedObject.val :=
  sharedLaw admittedObject.val

/-- Uses `sharedLaw` through the only proof it has, eliminated as `False`: an empty
eliminator has no minor premise to stand in for it, so its major premise is live. -/
theorem useObtainFalse (h : ¬ ((3 : Nat) + 0 = 3)) : (0 : Nat) = 1 := by
  obtain ⟨⟩ := notShared h

/-- The same, by `cases`. -/
theorem useCasesFalse (h : ¬ ((3 : Nat) + 0 = 3)) : (0 : Nat) = 1 := by
  cases notShared h

/-- Uses `sharedLaw`, and projects the admitted law of an object the statement names: the gap
is reported as a note but does not fail the requirement. -/
theorem useAdmittedField (n : Nat) : admittedLaw.val n + 0 + 0 = admittedLaw.val n :=
  (sharedLaw (admittedLaw.val n + 0)).trans (admittedLaw.property n)

/-- Names `sharedLaw` in the statement and repeats it in the proof term: a direct occurrence
counts, and the report says the statement names it too. -/
theorem useNamedByStatement :
    (⟨3, sharedLaw 3⟩ : { m : Nat // m + 0 = m }).val = 3 := rfl

end AxiomSweepTestFixtures.MustDependOn.Statement

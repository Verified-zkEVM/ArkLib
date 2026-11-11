/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.OracleReduction.LiftContext.Reduction

/-!
# Guarded soundness of an OR-statement lens

An unchanged auxiliary disjunct can accept an outer output even when its inner output is false.
The statement lens preserves soundness at outer inputs outside the outer input language.
-/

namespace GuardedLensRegression

variable {CIn COut Flag : Type}

/-- Preserve the auxiliary statement while replacing the main statement. -/
def orLens : Statement.Lens (CIn × Flag) (COut × Flag) CIn COut where
  toFunA := Prod.fst
  toFunB := fun stmt stmtOut => (stmtOut, stmt.2)

/-- Either the main statement or the auxiliary statement belongs to its language. -/
def orLanguage {C : Type} (L : Set C) (E : Set Flag) : Set (C × Flag) :=
  {stmt | stmt.1 ∈ L ∨ stmt.2 ∈ E}

/-- The OR lens is sound whenever the outer input satisfies neither disjunct. -/
theorem orLens_sound (langIn : Set CIn) (langOut : Set COut) (extra : Set Flag) :
    Statement.Lens.IsSound (orLanguage langIn extra) (orLanguage langOut extra)
      langIn langOut (fun _ _ => True) orLens where
  proj_sound := by
    intro stmt hOuter hInner
    exact hOuter (Or.inl hInner)
  lift_sound := by
    intro stmt stmtOut hOuter _ hInner hLift
    rcases hLift with hMain | hExtra
    · exact hInner hMain
    · exact hOuter (Or.inr hExtra)

/-- An accepting auxiliary statement contradicts the unguarded output law. -/
theorem orLens_unguarded_fails (langOut : Set COut) (extra : Set Flag)
    (stmt : CIn) (stmtOut : COut) (flag : Flag)
    (hOut : stmtOut ∉ langOut) (hExtra : flag ∈ extra) :
    ¬ (∀ outerStmtIn innerStmtOut, True → innerStmtOut ∉ langOut →
      (orLens : Statement.Lens (CIn × Flag) (COut × Flag) CIn COut).lift
        outerStmtIn innerStmtOut ∉ orLanguage langOut extra) := by
  intro h
  exact h (stmt, flag) stmtOut trivial hOut (Or.inr hExtra)

/-- The auxiliary Boolean disjunct gives a concrete guarded soundness certificate. -/
example : Statement.Lens.IsSound
    (orLanguage (∅ : Set Bool) {true}) (orLanguage (∅ : Set Bool) {true})
    ∅ ∅ (fun _ _ => True) orLens :=
  orLens_sound ∅ ∅ {true}

/-- The same lens violates the unguarded output law at an accepting auxiliary statement. -/
example : ¬ (∀ outerStmtIn innerStmtOut, True → innerStmtOut ∉ (∅ : Set Bool) →
    (orLens : Statement.Lens (Bool × Bool) (Bool × Bool) Bool Bool).lift
      outerStmtIn innerStmtOut ∉ orLanguage (∅ : Set Bool) {true}) :=
  orLens_unguarded_fails ∅ {true} false false true (by simp) (by simp)

/-- Unit witnesses specialize knowledge soundness to the guarded statement certificate. -/
theorem orLens_knowledgeSound (langIn : Set CIn) (langOut : Set COut) (extra : Set Flag) :
    (Extractor.Lens.idWit (stmtLens := orLens)
      (OuterWitIn := Unit) (OuterWitOut := Unit)).IsKnowledgeSound
      (orLanguage langIn extra ×ˢ Set.univ) (langIn ×ˢ Set.univ)
      (orLanguage langOut extra ×ˢ Set.univ) (langOut ×ˢ Set.univ)
      (fun _ _ => True) (fun _ _ => True) :=
  Extractor.Lens.unit_knowledgeSound orLens (orLanguage langIn extra)
    (orLanguage langOut extra) langIn langOut (fun _ _ => True)
    (orLens_sound langIn langOut extra)

/-- Recover statement soundness from the Unit-witness certificate. -/
example (langIn : Set CIn) (langOut : Set COut) (extra : Set Flag) :
    Statement.Lens.IsSound (orLanguage langIn extra) (orLanguage langOut extra)
      langIn langOut (fun _ _ => True) orLens :=
  Extractor.Lens.sound_of_unit_knowledgeSound orLens (orLanguage langIn extra)
    (orLanguage langOut extra) langIn langOut (fun _ _ => True)
    (orLens_knowledgeSound langIn langOut extra)

open OracleComp OracleSpec ProtocolSpec

abbrev emptyOracle : OracleSpec Empty := Empty →ₒ Unit
abbrev zeroRounds : ProtocolSpec 0 := !p[]

/-- An accepting auxiliary bit lets the outer output witness supply the input witness. -/
def shortcutLens : Extractor.Lens (Bool × Bool) (Bool × Bool) Bool Bool Nat Nat Nat Nat where
  stmt := orLens
  wit := ⟨Prod.snd, fun p innerWit => if p.1.2 then p.2 else innerWit⟩

/-- The inner extractor may fail independently of an accepting auxiliary bit. -/
def optionalExtractor (result : Option Nat) :
    Extractor.Straightline emptyOracle Bool Nat Nat zeroRounds :=
  fun _ _ _ _ _ => OptionT.mk (pure result)

/-- Failed inner extraction still produces the outer witness through the shortcut. -/
example : ((optionalExtractor none).liftContext shortcutLens
    (false, true) 7 default default default).run = pure (some 7) := rfl

/-- Successful inner extraction is retained when the auxiliary bit is false. -/
example : ((optionalExtractor (some 11)).liftContext shortcutLens
    (false, false) 7 default default default).run = pure (some 11) := rfl

/-- Without the auxiliary bit, failed inner extraction uses the default input witness. -/
example : ((optionalExtractor none).liftContext shortcutLens
    (false, false) 7 default default default).run = pure (some 0) := rfl

/-- Execute the lifted extractor over the empty oracle interface. -/
def runOptionalExtractor (result : Option Nat) (flag : Bool) : Option Nat :=
  Id.run (simulateQ (fun q => nomatch q)
    (((optionalExtractor result).liftContext shortcutLens
      (false, flag) 7 default default default).run))

run_cmd do
  unless runOptionalExtractor none true == some 7 do
    throwError "Failed inner extraction lost the shortcut witness"
  unless runOptionalExtractor (some 11) false == some 11 do
    throwError "Successful inner extraction lost the extracted witness"
  unless runOptionalExtractor none false == some 0 do
    throwError "Failed inner extraction did not use the default witness"

end GuardedLensRegression

/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/
module

public import ArkLib.ToCompPoly.Univariate.ArithmeticCost
public import ArkLib.ProofSystem.Fri.Spec.Transcript

/-!
# Immutable access instructions for FRI extraction

Word addresses carry their actual field points. Their handlers read the retained word directly;
domain evaluation occurs only at separately charged domain instructions. Arithmetic instructions
remain explicit. Profiles count these accesses and designated metadata operations, without
asserting machine runtime bounds for arbitrary committed-word or domain functions.
-/

@[expose] public section

namespace Fri.Spec.Extractor

open Domain OracleComp OracleSpec CompPoly

/-- An immutable input access or a final-polynomial metadata access. -/
inductive AccessOp {F : Type} [Field F] [DecidableEq F] {n k : ℕ}
    (s : Fin (k + 1) → ℕ+) (ω : SmoothCosetFftDomain n F)
  | wordRead (i : Fin (k + 1))
      (x : (ω.subdomain (foldingPrefix s i.castSucc)).toFinset)
  | domainRead (z : Fin (2 ^ n))
  | challengeRead (i : Fin (k + 1))
  | finalPolynomialRead
  | polynomialDegreeRead (p : CPolynomial F)

/-- Coordinates counted by accesses to immutable FRI inputs. -/
inductive AccessCostKind
  | wordRead | domainRead | challengeRead | finalPolynomialRead
  deriving DecidableEq, Repr

/-- Arithmetic and immutable-input access coordinates. -/
abbrev CostKind := ArithmeticCostKind ⊕ AccessCostKind

/-- The product of all extractor access and arithmetic counts. -/
abbrev Cost := CostKind → ℕ

variable {F : Type} [NonBinaryField F] [Fintype F] [DecidableEq F]
variable {n k : ℕ} {ω : SmoothCosetFftDomain n F}
variable (s : Fin (k + 1) → ℕ+)

/-- Certified responses from a fixed retained history and challenge vector. -/
def AccessSpec (o : ∀ j, FinalOracleStatement s ω j) (α : FinalStatement F k) :
    OracleSpec (AccessOp s ω)
  | .wordRead i x => {y : F // y = committedWord s o i x}
  | .domainRead z => {x : F // x = ω z}
  | .challengeRead i => {a : F // a = α i}
  | .finalPolynomialRead => {p : CPolynomial F // p = finalPolynomial s o}
  | .polynomialDegreeRead p => {m : ℕ // m = p.natDegree}

/-- The complete instruction family of the extractor backend. -/
abbrev InstructionSpec (o : ∀ j, FinalOracleStatement s ω j) (α : FinalStatement F k) :=
  ArithmeticSpec F + AccessSpec s o α

/-- The coordinate charged by each input instruction. -/
def AccessOp.costKind : AccessOp s ω → CostKind
  | .wordRead _ _ => .inr .wordRead
  | .domainRead _ => .inr .domainRead
  | .challengeRead _ => .inr .challengeRead
  | .finalPolynomialRead => .inr .finalPolynomialRead
  | .polynomialDegreeRead _ => .inl .metadata

/-- One unit in the coordinate charged by an extractor instruction. -/
def instructionCost (op : ArithmeticOp F ⊕ AccessOp s ω) : Cost :=
  fun kind ↦ if kind = (match op with
    | .inl a => .inl a.costKind
    | .inr a => a.costKind s) then 1 else 0

/-- Read one immutable input or its degree metadata and certify the result. -/
def accessAnswer (o : ∀ j, FinalOracleStatement s ω j) (α : FinalStatement F k) :
    QueryImpl (AccessSpec s o α) Id
  | .wordRead i x => ⟨committedWord s o i x, rfl⟩
  | .domainRead z => ⟨ω z, rfl⟩
  | .challengeRead i => ⟨α i, rfl⟩
  | .finalPolynomialRead => ⟨finalPolynomial s o, rfl⟩
  | .polynomialDegreeRead p => ⟨p.natDegree, rfl⟩

/-- Execute a certified arithmetic or immutable-input instruction. -/
def instructionAnswer (o : ∀ j, FinalOracleStatement s ω j) (α : FinalStatement F k) :
    QueryImpl (InstructionSpec s o α) Id
  | .inl op => arithmeticAnswer op
  | .inr op => accessAnswer s o α op

/-- Every certified instruction response is the handler's answer. -/
theorem eq_instructionAnswer (o : ∀ j, FinalOracleStatement s ω j) (α : FinalStatement F k)
    (op : ArithmeticOp F ⊕ AccessOp s ω) (u : (InstructionSpec s o α).Range op) :
    u = instructionAnswer s o α op := by
  rcases op with op | op
  · exact eq_arithmeticAnswer op u
  · cases op <;> exact Subtype.ext u.property

/-- Execute the instruction backend while recording every requested operation. -/
def measuredAnswer (o : ∀ j, FinalOracleStatement s ω j) (α : FinalStatement F k) :
    QueryImpl (InstructionSpec s o α) (AddWriterT Cost Id) :=
  (instructionAnswer s o α).withCost
    (fun op ↦ Multiplicative.ofAdd (instructionCost s op))

/-- The exact result and cost vector of an extractor instruction program. -/
def profile {A : Type} (o : ∀ j, FinalOracleStatement s ω j) (α : FinalStatement F k)
    (program : OracleComp (InstructionSpec s o α) A) : A × Cost :=
  (simulateQ (measuredAnswer s o α) program).runAdd

/-- Erasing the measured execution preserves the same instruction program's result. -/
theorem profile_fst {A : Type} (o : ∀ j, FinalOracleStatement s ω j)
    (α : FinalStatement F k) (program : OracleComp (InstructionSpec s o α) A) :
    (profile s o α program).1 = simulateQ (instructionAnswer s o α) program := by
  exact QueryImpl.fst_map_run_withCost (instructionAnswer s o α)
    (fun op ↦ Multiplicative.ofAdd (instructionCost s op)) program

end Fri.Spec.Extractor

namespace Fri.Spec.Extractor

open Domain OracleComp OracleSpec CompPoly

variable {F : Type} [NonBinaryField F] [Fintype F] [DecidableEq F]
variable {n k : ℕ} {ω : SmoothCosetFftDomain n F}
variable (s : Fin (k + 1) → ℕ+) (o : ∀ j, FinalOracleStatement s ω j)
variable (α : FinalStatement F k)

/-- Pure programs request no backend operations. -/
@[simp]
theorem profile_pure {A : Type} (a : A) : profile s o α (pure a) = (a, 0) := by
  simp only [profile, simulateQ_pure, AddWriterT.runAdd_pure]
  rfl

/-- Sequential execution adds the complete cost vectors. -/
theorem profile_bind {A B : Type} (p : OracleComp (InstructionSpec s o α) A)
    (f : A → OracleComp (InstructionSpec s o α) B) :
    profile s o α (p >>= f) =
      let a := profile s o α p
      let b := profile s o α (f a.1)
      (b.1, a.2 + b.2) := by
  simp only [profile, simulateQ_bind, AddWriterT.runAdd_bind]
  rfl

/-- A backend instruction executes once and contributes its designated unit cost. -/
@[simp]
theorem profile_query (op : ArithmeticOp F ⊕ AccessOp s ω) :
    profile s o α (liftM (OracleSpec.query (spec := InstructionSpec s o α) op)) =
      (instructionAnswer s o α op, instructionCost s op) := by
  simp [profile, simulateQ_query, OracleSpec.query_def, measuredAnswer,
    QueryImpl.withCost_apply, AddWriterT.runAdd]
  rfl

/-- Mapping a result leaves every operation count unchanged. -/
@[simp]
theorem profile_map {A B : Type} (f : A → B)
    (p : OracleComp (InstructionSpec s o α) A) :
    profile s o α (f <$> p) = let a := profile s o α p; (f a.1, a.2) := by
  rw [map_eq_bind_pure_comp, profile_bind]
  simp only [Function.comp_apply, profile_pure, add_zero]

/-- A certified program returns the unique value described by its response type. -/
@[simp]
theorem profile_certified_fst {A : Type} {a : A}
    (p : OracleComp (InstructionSpec s o α) {b : A // b = a}) :
    (profile s o α p).1 = ⟨a, rfl⟩ :=
  Subtype.ext (profile s o α p).1.property

/-- Include arithmetic coordinates and assign zero to immutable-input coordinates. -/
def embedArithmeticCost (cost : ArithmeticCost) : Cost :=
  Sum.elim cost (fun _ ↦ 0)

/-- Including the zero arithmetic profile gives the zero backend profile. -/
@[simp]
theorem embedArithmeticCost_zero : embedArithmeticCost 0 = 0 := by
  funext kind
  cases kind <;> rfl

/-- Including arithmetic profiles preserves addition. -/
@[simp]
theorem embedArithmeticCost_add (a b : ArithmeticCost) :
    embedArithmeticCost (a + b) = embedArithmeticCost a + embedArithmeticCost b := by
  funext kind
  cases kind <;> rfl

private theorem profile_lift_query (op : ArithmeticOp F) :
    profile s o α (liftComp (liftM (OracleSpec.query (spec := ArithmeticSpec F) op) :
      OracleComp (ArithmeticSpec F) (ArithmeticSpec F op)) (InstructionSpec s o α)) =
      (arithmeticAnswer op, embedArithmeticCost (arithmeticCost op)) := by
  change profile s o α
    (liftM (OracleSpec.query (spec := InstructionSpec s o α) (.inl op))) = _
  rw [profile_query]
  apply Prod.ext
  · rfl
  · funext kind
    cases kind <;> simp [instructionCost, embedArithmeticCost, arithmeticCost]

/-- Lifting an arithmetic program retains its result and embeds every cost coordinate. -/
theorem profile_liftComp_arithmetic {A : Type} (p : OracleComp (ArithmeticSpec F) A) :
    profile s o α (liftComp p (InstructionSpec s o α)) =
      ((profileArithmetic p).1, embedArithmeticCost (profileArithmetic p).2) := by
  induction p using OracleComp.inductionOn with
  | pure a => simp
  | query_bind op cont ih =>
    rw [OracleComp.liftComp_bind, profile_bind, profile_lift_query,
      profileArithmetic_bind, profileArithmetic_query]
    simp only
    rw [ih, embedArithmeticCost_add]

/-- Lifting arithmetic into the backend embeds its cost vector unchanged. -/
@[simp]
theorem profile_liftM_arithmetic {A : Type} (p : OracleComp (ArithmeticSpec F) A) :
    profile s o α (liftM p : OracleComp (InstructionSpec s o α) A) =
      ((profileArithmetic p).1, embedArithmeticCost (profileArithmetic p).2) := by
  exact profile_liftComp_arithmetic s o α p

end Fri.Spec.Extractor

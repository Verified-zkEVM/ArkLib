/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Data.Fin.Tuple.Basic

/-!
# The formula language of protocol specifications

This module provides the typed formula language that a protocol specification uses for the
verifier's checks, its local values and the claims of its stages, together with the display
names of transcript values.

* `Name` is a display name: a base and a subscript over a round index. `Name.tex` renders it
  folded (round `j` prints as `i`, `j + 1` as `i+1`) or expanded (round `j` prints as `j`).
* `Fml v o β` is a formula with result type `β` in parametric higher-order abstract syntax
  (PHOAS). The carrier `v` holds the bound values and `o` the oracle handles.
* `Fml.evalM` runs a formula in a monad, `Fml.syntax` converts it to the first-order tree `Syn`,
  and `Fml.tex` prints it. `Syn.tex` prints the tree, and `Fml.tex_eq` proves that both
  printings agree.
* `Hole`, `Args`, `Curry` and `Closed` describe a formula with named holes: a Lean function
  `∀ {v o}, o Q A → v α → … → Fml v o β`. A specification fills the holes with transcript
  values at run time and with their names in the skeleton.
* `FO` is a typed first-order tree with named variables and `FO.eval` evaluates it, so the tests
  at the end compare the evaluation of the exported tree with the formula's own evaluation.

## Design choices

* The formula has two carriers, `v` for values and `o` for oracles. *Why:* the verifier reads an
  oracle only through queries, so an oracle hole must not be usable as a value. With one carrier a
  formula could print an oracle as a value.
* `evalM` takes the oracle answers as a function `ask` on the carrier `o`. *Why:* the honest
  prover, the verifier's decision and its pure verdict instantiate the formula at the same carriers
  and differ only in `ask`. A theorem about all three then follows by induction on the one formula
  term, and needs no parametricity, which Lean cannot prove.
* A sum takes a `Dom`, a printed name and the list of its elements. *Why:* the verifier evaluates
  the sum by enumeration, and the figure prints `\sum_{a \in D}` without enumerating.
* A literal carries its printed form. *Why:* a literal's value can be a polynomial or another
  object with no canonical printing.
* The display of a subscript is computed at export time from `Ix.rnd k`, the absolute round. *Why:*
  the same skeleton then renders folded (`g_i`) and expanded (`g_2`), and the round index stays a
  natural number that `simp` and `rfl` reduce.
* `Syn` is untyped and holds only strings and names. *Why:* the skeleton stores it as a type index,
  and an untyped tree keeps that index computable even when a formula's values are noncomputable.
  `FO` is the typed counterpart used to evaluate the exported structure.
* The conversion theorem `eval (syntax φ) = eval φ` holds only by tests here. *Why:* a general
  proof relates the instance of a PHOAS term at the name carrier to its instance at the value
  carrier, which needs parametricity. The tests check it by `simp` on the sum-check formulas.
-/

set_option linter.hashCommand false

namespace Specs

/-! ## Names -/

/-- A subscript index: `rnd k` is the absolute round `k` of a `rounds` block, which the folded
figure prints relative to the displayed round. `num k` is a fixed number. -/
inductive Ix
  | rnd (k : ℕ)
  | num (k : ℕ)
  deriving DecidableEq, Repr, Inhabited

/-- The subscript of a name: none, an index (`g_i`), the indices below an index (`r_{<i}`), or a
fixed symbol (`z_x`). -/
inductive Subscript
  | none
  | at (e : Ix)
  | below (e : Ix)
  | sym (s : String)
  deriving DecidableEq, Repr, Inhabited

/-- The display name of a transcript value, an oracle or a bound variable. The base is TeX. -/
structure Name where
  base : String
  sub : Subscript := .none
  deriving DecidableEq, Repr, Inhabited

instance : Coe String Name := ⟨fun s => ⟨s, .none⟩⟩

/-- The name `b_i` of a value of round `i`. -/
def ix (b : String) (i : ℕ) : Name := ⟨b, .at (.rnd i)⟩

/-- The name `b_{<i}` of the values of the rounds before `i`. -/
def below (b : String) (i : ℕ) : Name := ⟨b, .below (.rnd i)⟩

/-- How names render. In the folded figure (`round = some j`) the round `j` prints as `var` and
round `k` as `var+(k-j)`. Outside a round, a round number listed in `counts` prints as its symbol
(`n`), so `c_n` names the claim after an `n`-round block. The expanded figure prints numbers. -/
structure Mode where
  folded : Bool := false
  round : Option ℕ := none
  var : String := "i"
  counts : List (ℕ × String) := []
  deriving Inhabited

/-- The expanded mode: every round index prints as its number. -/
def Mode.expanded : Mode := {}

/-- Render an index in a mode. -/
def Ix.tex (m : Mode) : Ix → String
  | .num k => toString k
  | .rnd k =>
    if m.folded then
      match m.round with
      | some j =>
        if k = j then m.var
        else if j < k then m.var ++ "+" ++ toString (k - j)
        else m.var ++ "-" ++ toString (j - k)
      | none => ((m.counts.find? (·.1 = k)).map (·.2)).getD (toString k)
    else toString k

/-- Render a name in a mode. -/
def Name.tex (m : Mode) (nm : Name) : String :=
  nm.base ++
    match nm.sub with
    | .none => ""
    | .at e => "_{" ++ e.tex m ++ "}"
    | .below e => "_{<" ++ e.tex m ++ "}"
    | .sym s => "_{" ++ s ++ "}"

/-- The folded mode inside round `j` of a block. -/
def Mode.inRound (m : Mode) (j : ℕ) : Mode := { m with round := some j }

#guard (ix "g" 2).tex Mode.expanded == "g_{2}"
#guard (ix "g" 2).tex { folded := true, round := some 2 } == "g_{i}"
#guard (ix "c" 3).tex { folded := true, round := some 2 } == "c_{i+1}"
#guard (below "r" 2).tex { folded := true, round := some 2 } == "r_{<i}"
#guard (ix "c" 3).tex { folded := true, counts := [(3, "n")] } == "c_{n}"
#guard (ix "c" 0).tex { folded := true, counts := [(3, "n")] } == "c_{0}"

/-! ## Domains and formulas -/

/-- A finite domain for a sum: its printed name and its elements. -/
structure Dom (α : Type) where
  tex : String
  elems : List α

/-- The domain `{D 0, …, D (k-1)}` of a function `D : Fin k → α`, printed as `tex`. -/
def Dom.ofFn {α : Type} {k : ℕ} (tex : String) (D : Fin k → α) : Dom α :=
  ⟨tex, List.ofFn D⟩

/-- All tuples of `n` elements of `D`. -/
def Dom.tuples {α : Type} (D : List α) : (n : ℕ) → List (Fin n → α)
  | 0 => [Fin.elim0]
  | n + 1 => D.flatMap fun a => (tuples D n).map (Fin.cons a)

/-- The domain `D^n` of `n`-tuples, printed with the exponent `ntex`. -/
def Dom.pow {α : Type} (D : Dom α) (n : ℕ) (ntex : String := toString n) : Dom (Fin n → α) :=
  ⟨D.tex ++ "^{" ++ ntex ++ "}", Dom.tuples D.elems n⟩

/-- A typed formula in PHOAS. Values bound by a sum or supplied for a hole live in `v`, oracle
handles in `o`. -/
inductive Fml (v : Type → Type) (o : Type → Type → Type) : Type → Type 1
  /-- A bound value or a hole. -/
  | var {α : Type} (x : v α) : Fml v o α
  /-- A literal with its printed form. -/
  | lit {α : Type} (tex : String) (a : α) : Fml v o α
  | add {α : Type} [Add α] (a b : Fml v o α) : Fml v o α
  | sub {α : Type} [Sub α] (a b : Fml v o α) : Fml v o α
  | mul {α : Type} [Mul α] (a b : Fml v o α) : Fml v o α
  | neg {α : Type} [Neg α] (a : Fml v o α) : Fml v o α
  | pow {α : Type} [Monoid α] (a : Fml v o α) (k : ℕ) : Fml v o α
  /-- Equality, decided. -/
  | eq {α : Type} [DecidableEq α] (a b : Fml v o α) : Fml v o Bool
  | and (a b : Fml v o Bool) : Fml v o Bool
  /-- The sum of `body x` over the elements `x` of `dom`. The binder prints as `x`. -/
  | sum {α β : Type} [AddCommMonoid β] (x : Name) (dom : Dom α) (body : v α → Fml v o β) :
      Fml v o β
  /-- The answer of the oracle `h` at the query `q`. -/
  | query {Q A : Type} (h : o Q A) (q : Fml v o Q) : Fml v o A
  /-- A named opaque function, printed `name(x)`. -/
  | app {α β : Type} (name : String) (f : α → β) (x : Fml v o α) : Fml v o β

namespace Fml
variable {v : Type → Type} {o : Type → Type → Type}

instance {α : Type} [Add α] : Add (Fml v o α) := ⟨Fml.add⟩
instance {α : Type} [Sub α] : Sub (Fml v o α) := ⟨Fml.sub⟩
instance {α : Type} [Mul α] : Mul (Fml v o α) := ⟨Fml.mul⟩
instance {α : Type} [Neg α] : Neg (Fml v o α) := ⟨Fml.neg⟩
instance {α : Type} [Monoid α] : HPow (Fml v o α) ℕ (Fml v o α) := ⟨Fml.pow⟩
instance {α : Type} {n : ℕ} [OfNat α n] : OfNat (Fml v o α) n :=
  ⟨Fml.lit (toString n) (OfNat.ofNat n)⟩

/-- Formula equality, decided by the verifier. -/
infix:50 " =' " => Fml.eq
/-- Formula conjunction. -/
infixr:35 " ∧' " => Fml.and

end Fml

/-- The answer of the oracle `h` at the value `x`. -/
abbrev ask {v : Type → Type} {o : Type → Type → Type} {Q A : Type} (h : o Q A) (x : v Q) :
    Fml v o A :=
  .query h (.var x)

/-- `∑∈ x ∈ D, body` is the formula sum of `body` over the domain `D`. The binder name prints as
the Lean identifier. -/
macro "∑∈ " x:ident " ∈ " D:term ", " b:term:51 : term =>
  `(Fml.sum (Name.mk $(Lean.quote x.getId.toString) .none) $D fun $x => $b)

/-! ## Evaluation -/

/-- The sum of `f a` over the list, in a monad. -/
def sumM {m : Type → Type} [Monad m] {α β : Type} [AddCommMonoid β] (f : α → m β) :
    List α → m β
  | [] => pure 0
  | a :: l => do
    let b ← f a
    let s ← sumM f l
    pure (b + s)

/-- Evaluate a formula in the monad `m`. `ask h q` answers the query `q` to the oracle `h`. -/
def Fml.evalM {m : Type → Type} [Monad m] {o : Type → Type → Type}
    (ask : ∀ ⦃Q A : Type⦄, o Q A → Q → m A) : {β : Type} → Fml (fun α => α) o β → m β
  | _, .var x => pure x
  | _, .lit _ a => pure a
  | _, @Fml.add _ _ _ _ a b => do pure ((← a.evalM ask) + (← b.evalM ask))
  | _, @Fml.sub _ _ _ _ a b => do pure ((← a.evalM ask) - (← b.evalM ask))
  | _, @Fml.mul _ _ _ _ a b => do pure ((← a.evalM ask) * (← b.evalM ask))
  | _, @Fml.neg _ _ _ _ a => do pure (-(← a.evalM ask))
  | _, @Fml.pow _ _ _ _ a k => do pure ((← a.evalM ask) ^ k)
  | _, @Fml.eq _ _ _ _ a b => do pure (decide ((← a.evalM ask) = (← b.evalM ask)))
  | _, .and a b => do pure ((← a.evalM ask) && (← b.evalM ask))
  | _, @Fml.sum _ _ _ _ _ _ dom body => sumM (fun x => (body x).evalM ask) dom.elems
  | _, .query h q => do ask h (← q.evalM ask)
  | _, .app _ f x => do pure (f (← x.evalM ask))

/-- Evaluate a formula without effects. -/
def Fml.eval {o : Type → Type → Type} (ask : ∀ ⦃Q A : Type⦄, o Q A → Q → A) {β : Type}
    (φ : Fml (fun α => α) o β) : β :=
  Id.run (φ.evalM (m := Id) fun ⦃_ _⦄ h q => pure (ask h q))

/-- In the identity monad `sumM` is the sum of the mapped list. -/
theorem sumM_id {α β : Type} [AddCommMonoid β] (f : α → Id β) (l : List α) :
    sumM f l = pure (l.map fun a => (f a).run).sum := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [sumM, ih]; rfl

section EvalLemmas
variable {o : Type → Type → Type} (ask : ∀ ⦃Q A : Type⦄, o Q A → Q → A)

@[simp] theorem Fml.eval_var {α : Type} (x : α) : (Fml.var (o := o) x).eval ask = x := rfl
@[simp] theorem Fml.eval_lit {α : Type} (tex : String) (a : α) :
    (Fml.lit (v := fun α => α) (o := o) tex a).eval ask = a := rfl
@[simp] theorem Fml.eval_add {α : Type} [Add α] (a b : Fml (fun α => α) o α) :
    (a + b).eval ask = a.eval ask + b.eval ask := rfl
@[simp] theorem Fml.eval_sub {α : Type} [Sub α] (a b : Fml (fun α => α) o α) :
    (a - b).eval ask = a.eval ask - b.eval ask := rfl
@[simp] theorem Fml.eval_mul {α : Type} [Mul α] (a b : Fml (fun α => α) o α) :
    (a * b).eval ask = a.eval ask * b.eval ask := rfl
@[simp] theorem Fml.eval_neg {α : Type} [Neg α] (a : Fml (fun α => α) o α) :
    (-a).eval ask = -a.eval ask := rfl
@[simp] theorem Fml.eval_pow {α : Type} [Monoid α] (a : Fml (fun α => α) o α) (k : ℕ) :
    (a ^ k).eval ask = a.eval ask ^ k := rfl
@[simp] theorem Fml.eval_eq {α : Type} [DecidableEq α] (a b : Fml (fun α => α) o α) :
    (a =' b).eval ask = decide (a.eval ask = b.eval ask) := rfl
@[simp] theorem Fml.eval_and (a b : Fml (fun α => α) o Bool) :
    (a ∧' b).eval ask = (a.eval ask && b.eval ask) := rfl
@[simp] theorem Fml.eval_sum {α β : Type} [AddCommMonoid β] (x : Name) (dom : Dom α)
    (body : α → Fml (fun α => α) o β) :
    (Fml.sum x dom body).eval ask = (dom.elems.map fun a => (body a).eval ask).sum := by
  change Id.run (sumM _ dom.elems) = _
  rw [sumM_id]
  rfl
@[simp] theorem Fml.eval_query {Q A : Type} (h : o Q A) (q : Fml (fun α => α) o Q) :
    (Fml.query h q).eval ask = ask h (q.eval ask) := rfl
@[simp] theorem Fml.eval_app {α β : Type} (name : String) (f : α → β)
    (x : Fml (fun α => α) o α) : (Fml.app name f x).eval ask = f (x.eval ask) := rfl

end EvalLemmas

/-! ## The first-order syntax tree -/

/-- A binary operation of the syntax tree. -/
inductive BinOp
  | add | sub | mul | eq | and
  deriving DecidableEq, Repr, Inhabited

/-- The first-order, untyped syntax of a formula: what the skeleton stores and the JSON export
prints. -/
inductive Syn
  | var (nm : Name)
  | lit (tex : String)
  | bin (op : BinOp) (a b : Syn)
  | neg (a : Syn)
  | pow (a : Syn) (k : ℕ)
  | sum (x : Name) (dom : String) (body : Syn)
  | query (h : Name) (q : Syn)
  | app (name : String) (x : Syn)
  deriving DecidableEq, Repr, Inhabited

/-- The carrier of the naming instance: every value and oracle is its name. -/
abbrev NameV : Type → Type := fun _ => Name
/-- The oracle carrier of the naming instance. -/
abbrev NameO : Type → Type → Type := fun _ _ => Name

/-- Convert a formula at the naming carriers into its syntax tree. A sum binds its own name. -/
def Fml.syntax : {β : Type} → Fml NameV NameO β → Syn
  | _, .var x => .var x
  | _, .lit tex _ => .lit tex
  | _, @Fml.add _ _ _ _ a b => .bin .add a.syntax b.syntax
  | _, @Fml.sub _ _ _ _ a b => .bin .sub a.syntax b.syntax
  | _, @Fml.mul _ _ _ _ a b => .bin .mul a.syntax b.syntax
  | _, @Fml.neg _ _ _ _ a => .neg a.syntax
  | _, @Fml.pow _ _ _ _ a k => .pow a.syntax k
  | _, @Fml.eq _ _ _ _ a b => .bin .eq a.syntax b.syntax
  | _, .and a b => .bin .and a.syntax b.syntax
  | _, @Fml.sum _ _ _ _ _ x dom body => .sum x dom.tex (body x).syntax
  | _, .query h q => .query h q.syntax
  | _, .app name _ x => .app name x.syntax

/-- The binding strength of an operation: a child binds weaker than its context gets
parentheses. -/
def BinOp.prec : BinOp → ℕ
  | .and => 10
  | .eq => 20
  | .add | .sub => 30
  | .mul => 40

/-- The TeX symbol of an operation. -/
def BinOp.tex : BinOp → String
  | .add => " + "
  | .sub => " - "
  | .mul => " \\cdot "
  | .eq => " = "
  | .and => " \\land "

/-- The binding strength of a tree's top operation. Atoms bind tightest. -/
def Syn.prec : Syn → ℕ
  | .bin op _ _ => op.prec
  | .sum .. => 25
  | .neg _ => 35
  | _ => 100

/-- Wrap `s` in parentheses when the subtree binds weaker than `p`. -/
def parenIf (b : Bool) (s : String) : String :=
  if b then "(" ++ s ++ ")" else s

/-- Print a syntax tree in TeX. -/
def Syn.tex (m : Mode) : Syn → String
  | .var nm => nm.tex m
  | .lit t => t
  | .bin op a b =>
    parenIf (a.prec < op.prec) (a.tex m) ++ op.tex ++ parenIf (b.prec ≤ op.prec) (b.tex m)
  | .neg a => "-" ++ parenIf (a.prec < 100) (a.tex m)
  | .pow a k => parenIf (a.prec < 100) (a.tex m) ++ "^{" ++ toString k ++ "}"
  | .sum x dom body => "\\sum_{" ++ x.tex m ++ " \\in " ++ dom ++ "} " ++
      parenIf (body.prec ≤ 30) (body.tex m)
  | .query h q => h.tex m ++ "(" ++ q.tex m ++ ")"
  | .app name x => "\\mathrm{" ++ name ++ "}(" ++ x.tex m ++ ")"

/-- The TeX reading of a formula: instantiate both carriers at names and print. -/
def Fml.tex (m : Mode) : {β : Type} → Fml NameV NameO β → String
  | _, .var x => x.tex m
  | _, .lit t _ => t
  | _, @Fml.add _ _ _ _ a b => (Syn.bin .add a.syntax b.syntax).tex m
  | _, @Fml.sub _ _ _ _ a b => (Syn.bin .sub a.syntax b.syntax).tex m
  | _, @Fml.mul _ _ _ _ a b => (Syn.bin .mul a.syntax b.syntax).tex m
  | _, @Fml.neg _ _ _ _ a => (Syn.neg a.syntax).tex m
  | _, @Fml.pow _ _ _ _ a k => (Syn.pow a.syntax k).tex m
  | _, @Fml.eq _ _ _ _ a b => (Syn.bin .eq a.syntax b.syntax).tex m
  | _, .and a b => (Syn.bin .and a.syntax b.syntax).tex m
  | _, @Fml.sum _ _ _ _ _ x dom body => (Syn.sum x dom.tex (body x).syntax).tex m
  | _, .query h q => h.tex m ++ "(" ++ q.tex m ++ ")"
  | _, .app name _ x => "\\mathrm{" ++ name ++ "}(" ++ x.tex m ++ ")"

/-- Printing a formula and printing its syntax tree agree. -/
theorem Fml.tex_eq (m : Mode) : ∀ {β : Type} (φ : Fml NameV NameO β), φ.tex m = φ.syntax.tex m
  | _, .var _ => rfl
  | _, .lit _ _ => rfl
  | _, @Fml.add _ _ _ _ _ _ => rfl
  | _, @Fml.sub _ _ _ _ _ _ => rfl
  | _, @Fml.mul _ _ _ _ _ _ => rfl
  | _, @Fml.neg _ _ _ _ _ => rfl
  | _, @Fml.pow _ _ _ _ _ _ => rfl
  | _, @Fml.eq _ _ _ _ _ _ => rfl
  | _, .and _ _ => rfl
  | _, @Fml.sum _ _ _ _ _ _ _ _ => rfl
  | _, .query _ q => by simp only [Fml.tex, Fml.syntax, Syn.tex, Fml.tex_eq m q]
  | _, .app _ _ x => by simp only [Fml.tex, Fml.syntax, Syn.tex, Fml.tex_eq m x]

/-! ## Formulas with named holes -/

/-- A hole of a formula: a named value of type `α`, or a named oracle with queries `Q` and
answers `A`. -/
inductive Hole : Type 1
  | val (nm : Name) (α : Type)
  | orc (nm : Name) (Q A : Type)

/-- The name of a hole. -/
def Hole.name : Hole → Name
  | .val nm _ => nm
  | .orc nm _ _ => nm

/-- Values for a list of holes at the carriers `v` and `o`. -/
inductive Args (v : Type → Type) (o : Type → Type → Type) : List Hole → Type 1
  | nil : Args v o []
  | val {nm : Name} {α : Type} {Γ : List Hole} (x : v α) (xs : Args v o Γ) :
      Args v o (.val nm α :: Γ)
  | orc {nm : Name} {Q A : Type} {Γ : List Hole} (h : o Q A) (xs : Args v o Γ) :
      Args v o (.orc nm Q A :: Γ)

/-- Concatenate two argument lists. -/
def Args.append {v : Type → Type} {o : Type → Type → Type} :
    {Γ Δ : List Hole} → Args v o Γ → Args v o Δ → Args v o (Γ ++ Δ)
  | _, _, .nil, ys => ys
  | _, _, .val x xs, ys => .val x (xs.append ys)
  | _, _, .orc h xs, ys => .orc h (xs.append ys)

/-- The names of the holes, as arguments at the naming carriers. -/
def Hole.names : (Γ : List Hole) → Args NameV NameO Γ
  | [] => .nil
  | .val nm _ :: Γ => .val nm (Hole.names Γ)
  | .orc nm _ _ :: Γ => .orc nm (Hole.names Γ)

/-- The curried type of a formula with holes `Γ` and result `β`. -/
def Curry (v : Type → Type) (o : Type → Type → Type) : List Hole → Type → Type 1
  | [], β => Fml v o β
  | .val _ α :: Γ, β => v α → Curry v o Γ β
  | .orc _ Q A :: Γ, β => o Q A → Curry v o Γ β

/-- Apply a curried formula to its arguments. -/
def Curry.app {v : Type → Type} {o : Type → Type → Type} {β : Type} :
    {Γ : List Hole} → Curry v o Γ β → Args v o Γ → Fml v o β
  | [], φ, .nil => φ
  | .val _ _ :: _, φ, .val x xs => Curry.app (φ x) xs
  | .orc _ _ _ :: _, φ, .orc h xs => Curry.app (φ h) xs

/-- A closed formula with holes `Γ`: one term for every pair of carriers. The structure keeps
Lean from instantiating the carriers when a closed formula is passed around. -/
structure Closed (Γ : List Hole) (β : Type) : Type 1 where
  /-- The formula at every pair of carriers. -/
  fml : ∀ {v : Type → Type} {o : Type → Type → Type}, Curry v o Γ β

/-- Fill the holes of a closed formula. -/
def Closed.inst {Γ : List Hole} {β : Type} (φ : Closed Γ β) {v : Type → Type}
    {o : Type → Type → Type} (args : Args v o Γ) : Fml v o β :=
  Curry.app (φ.fml (v := v) (o := o)) args

/-- The syntax tree of a closed formula, with every hole replaced by its name. -/
def Closed.syntax {Γ : List Hole} {β : Type} (φ : Closed Γ β) : Syn :=
  (φ.inst (Hole.names Γ)).syntax

/-- The TeX of a closed formula, with every hole replaced by its name. -/
def Closed.tex {Γ : List Hole} {β : Type} (m : Mode) (φ : Closed Γ β) : String :=
  (φ.inst (Hole.names Γ)).tex m

/-! ## Typed first-order trees with named variables

`FO β` keeps the structure of `Syn` together with the values and instances that evaluation
needs. A variable and an oracle are looked up by name in an environment. -/

/-- A typed first-order formula with named variables. -/
inductive FO : Type → Type 1
  | var {α : Type} (nm : Name) : FO α
  | lit {α : Type} (tex : String) (a : α) : FO α
  | add {α : Type} [Add α] (a b : FO α) : FO α
  | sub {α : Type} [Sub α] (a b : FO α) : FO α
  | mul {α : Type} [Mul α] (a b : FO α) : FO α
  | neg {α : Type} [Neg α] (a : FO α) : FO α
  | pow {α : Type} [Monoid α] (a : FO α) (k : ℕ) : FO α
  | eq {α : Type} [DecidableEq α] (a b : FO α) : FO Bool
  | and (a b : FO Bool) : FO Bool
  | sum {α β : Type} [AddCommMonoid β] (x : Name) (dom : Dom α) (body : FO β) : FO β
  | query {Q A : Type} (h : Name) (q : FO Q) : FO A
  | app {α β : Type} (name : String) (f : α → β) (x : FO α) : FO β

/-- An environment: a typed value for each name, and a typed answer function for each oracle
name. -/
structure Env where
  val : Name → (α : Type) → Option α
  orc : Name → (Q A : Type) → Option (Q → A)

open Classical in
/-- Bind the name `x` to the value `a`. -/
noncomputable def Env.bind (E : Env) {α : Type} (x : Name) (a : α) : Env :=
  { E with val := fun y β => if h : y = x ∧ α = β then some (h.2 ▸ a) else E.val y β }

/-- Evaluate a typed first-order formula. An unbound name evaluates to `none`. -/
noncomputable def FO.eval (E : Env) : {β : Type} → FO β → Option β
  | _, .var nm => E.val nm _
  | _, .lit _ a => some a
  | _, @FO.add _ _ a b => do pure ((← a.eval E) + (← b.eval E))
  | _, @FO.sub _ _ a b => do pure ((← a.eval E) - (← b.eval E))
  | _, @FO.mul _ _ a b => do pure ((← a.eval E) * (← b.eval E))
  | _, @FO.neg _ _ a => do pure (-(← a.eval E))
  | _, @FO.pow _ _ a k => do pure ((← a.eval E) ^ k)
  | _, @FO.eq _ _ a b => do pure (decide ((← a.eval E) = (← b.eval E)))
  | _, .and a b => do pure ((← a.eval E) && (← b.eval E))
  | _, @FO.sum _ _ _ x dom body =>
    (dom.elems.mapM fun a => body.eval (E.bind x a)).map List.sum
  | _, @FO.query Q A h q => do pure ((← E.orc h Q A) (← q.eval E))
  | _, .app _ f x => do pure (f (← x.eval E))

/-- Convert a formula at the naming carriers into a typed first-order formula. -/
def Fml.toFO : {β : Type} → Fml NameV NameO β → FO β
  | _, .var x => .var x
  | _, .lit tex a => .lit tex a
  | _, @Fml.add _ _ _ _ a b => .add a.toFO b.toFO
  | _, @Fml.sub _ _ _ _ a b => .sub a.toFO b.toFO
  | _, @Fml.mul _ _ _ _ a b => .mul a.toFO b.toFO
  | _, @Fml.neg _ _ _ _ a => .neg a.toFO
  | _, @Fml.pow _ _ _ _ a k => .pow a.toFO k
  | _, @Fml.eq _ _ _ _ a b => .eq a.toFO b.toFO
  | _, .and a b => .and a.toFO b.toFO
  | _, @Fml.sum _ _ _ _ _ x dom body => .sum x dom (body x).toFO
  | _, .query h q => .query h q.toFO
  | _, .app name f x => .app name f x.toFO

/-- Forget the types of a first-order formula. -/
def FO.erase : {β : Type} → FO β → Syn
  | _, .var x => .var x
  | _, .lit tex _ => .lit tex
  | _, @FO.add _ _ a b => .bin .add a.erase b.erase
  | _, @FO.sub _ _ a b => .bin .sub a.erase b.erase
  | _, @FO.mul _ _ a b => .bin .mul a.erase b.erase
  | _, @FO.neg _ _ a => .neg a.erase
  | _, @FO.pow _ _ a k => .pow a.erase k
  | _, @FO.eq _ _ a b => .bin .eq a.erase b.erase
  | _, .and a b => .bin .and a.erase b.erase
  | _, @FO.sum _ _ _ x dom body => .sum x dom.tex body.erase
  | _, .query h q => .query h q.erase
  | _, .app name _ x => .app name x.erase

/-- The exported syntax tree is the typed first-order tree with its types forgotten. -/
theorem Fml.erase_toFO : ∀ {β : Type} (φ : Fml NameV NameO β), φ.toFO.erase = φ.syntax
  | _, .var _ | _, .lit _ _ => rfl
  | _, @Fml.add _ _ _ _ a b | _, @Fml.sub _ _ _ _ a b | _, @Fml.mul _ _ _ _ a b
  | _, @Fml.eq _ _ _ _ a b | _, .and a b => by
    simp only [Fml.toFO, FO.erase, Fml.syntax, Fml.erase_toFO a, Fml.erase_toFO b]
  | _, @Fml.neg _ _ _ _ a | _, @Fml.pow _ _ _ _ a _ | _, .query _ a | _, .app _ _ a => by
    simp only [Fml.toFO, FO.erase, Fml.syntax, Fml.erase_toFO a]
  | _, @Fml.sum _ _ _ _ _ x _ body => by
    simp only [Fml.toFO, FO.erase, Fml.syntax, Fml.erase_toFO (body x)]

/-! ## Tests -/

/-- A test formula: `Σ_{a ∈ D} g_i(a) = c_i`, with an oracle hole `g_i` and a value hole `c_i`. -/
private def testSum (D : Dom ℤ) :
    Closed [.orc (ix "g" 2) ℤ ℤ, .val (ix "c" 2) ℤ] Bool :=
  ⟨fun g c => (∑∈ a ∈ D, ask g a) =' .var c⟩

#guard (testSum ⟨"D", [0, 1]⟩).tex { folded := true, round := some 2 } ==
  "\\sum_{a \\in D} g_{i}(a) = c_{i}"
#guard (testSum ⟨"D", [0, 1]⟩).tex Mode.expanded == "\\sum_{a \\in D} g_{2}(a) = c_{2}"

/-- A test of precedence: `(x + 1) · y - z^{2}`. -/
private def testPrec : Closed [.val "x" ℤ, .val "y" ℤ, .val "z" ℤ] ℤ :=
  ⟨fun x y z => (Fml.var x + 1) * Fml.var y - Fml.var z ^ 2⟩

#guard testPrec.tex Mode.expanded == "(x + 1) \\cdot y - z^{2}"

/-- The test formula evaluates by enumeration: with `g a = a + 1` and `D = {0, 1}`, the sum is
`3`. -/
example : ((testSum ⟨"D", [0, 1]⟩).inst (v := fun α => α) (o := fun Q A => Q → A)
    (.orc (fun a : ℤ => a + 1) (.val (3 : ℤ) .nil))).eval (fun ⦃_ _⦄ f q => f q) = true := by
  decide

#print axioms Fml.tex_eq
#print axioms Fml.erase_toFO
#print axioms Fml.eval_sum

end Specs

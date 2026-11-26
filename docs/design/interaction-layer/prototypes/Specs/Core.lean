/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import Specs.Formula
import ArkLib.Interaction.OracleVerifier

/-!
# Protocol descriptions

This module provides the description type `Desc` of an interactive oracle protocol, its
skeleton `Skel`, the combinators that authors write, and the specification structure `Spec`.

* Handles: `Val nm α` is a transcript value named `nm`, and `OHdl nm Q A` is an oracle named
  `nm` with queries `Q` and answers `A`. A handle's name is part of its type.
* `Skel` is the skeleton: a list of items (moves, input reads, checks, local values and stage
  markers) that ends in `done`, in a `branch` node with one sub-skeleton per case, in an `opaque`
  node, or in a `loop` node: one generic round of a loop, over the round variable `i` and the count
  `n`, followed by the rest.
* `Desc In W T t ks` describes a protocol with input oracle bundle `In`, witness `W`, output `T`,
  tree `t` and skeleton `ks`.
* Combinators: `message`, `oracle`, `challenge`, `input`, `check`, `compute`, `rounds`, `stage`,
  `branch`, `branchOpaque` and `done`.
* `Spec In S W T t ks` is a description for every input statement. Its anonymous constructor
  infers the tree and the skeleton from the description.
* `Skel.checks` lists the checks of a skeleton with their labels, in protocol order. Tests and
  exporters read the formulas from it.

## Design choices

* `Desc` has no monad parameter, and a check or a local value is a closed formula (`Closed`) with
  its arguments. *Why:* the honest prover, the decision and the pure verdict all interpret the
  same term, so `Specs.Run` proves their agreement by induction on the description. v0 ran one
  description in two monads and needed parametricity, which Lean cannot prove.
* An oracle handle holds a first-order reference (`Ref`): its level, the number of oracles
  (input reads and oracle messages) before it. *Why:* every interpreter passes the same handle
  value to the continuation and resolves the level in its own handler table. The decision
  resolves an oracle message to a query of the path's oracle messages, the verdict to the
  transcript's message, the prover to its honest message, and all three resolve an input read
  through the input bundle.
* Handles and formula arguments do not mention the input bundle. *Why:* inside a description the
  bundle is often still a metavariable when Lean elaborates a `check`, and the type class
  `ToArgs` that computes a formula's holes must not depend on it.
* An oracle node fixes the answer type `A` with a proof `∀ q, I.spec q = A`. *Why:* a formula
  query has one result type. Every oracle in the examples has a constant answer type.
* A handle carries a default answer. *Why:* a level that a description invents itself cannot be
  resolved, and the default keeps all three interpreters total. A description built from the
  combinators never does this.
* The tree and the skeleton are type indices. *Why:* no challenge, oracle handle or local value
  can change the shape, and `Spec.skeleton` is computable even when the description uses
  noncomputable polynomials.
* The skeleton stores the syntax of each formula with its holes replaced by their names. *Why:*
  a hole's name is in its type, so the skeleton never depends on transcript values.
* **A loop is one node with a generic body.** `rounds` produces `Skel.loop l n body rest`, where
  `body` is the skeleton of one round, written over the round variable `i` and the count's symbol
  `n`, and `n` is the count itself, a Lean term that may be a variable. The display data `l` holds
  the block name, the round variable, the count's symbol and the per-round error. *Why:* a paper
  writes a loop once, for a generic round, and so must the figure and the JSON. An unrolled
  skeleton exists only for a numeral `n`, so a specification with a variable round count had no
  skeleton that the export could compute, and the folded figure had to guess one round from the
  first.
* **Lean checks that the body is generic.** The body's skeleton is inferred as `G ks`, with `G` a
  function of the continuation's skeleton only, not of the round number, and `rounds` requires
  `G ks = (G .done).seq ks`, by `rfl` by default. *Why:* if any name, type or formula in a round
  mentioned the round number, `G` would have to depend on it and elaboration fails. So the one
  displayed round is, by typing, the skeleton of every round. Names in a body therefore use
  symbols (`iv "g"` for `g_i`, `iv "c" 1` for `c_{i+1}`), and a type whose printed name depends on
  the round passes its symbolic name (`ty := "\\mathbb{F}^{2^{k-i}}"`).
* **The count stays in the skeleton.** *Why:* the expanded figure and the accessors into later
  rounds need its value, and `Skel.erase` sets every count to `0`: each example proves by `rfl`
  that its erased skeleton is the same for every count, so the JSON and the folded figure, which
  read only the erased data, describe the protocol for every `n`.
* **The description keeps the unrolled rounds.** `Desc.loop l n body inner` holds the rounds as a
  description of skeleton `Skel.unroll l body rest 0 n`, with begin and end markers per round.
  *Why:* the interpreters and the proofs about them run on the unrolled description unchanged,
  and the index ties the generic body to the rounds that run.
* `rounds` passes the absolute round to the body and lets the round's tree vary with it
  (`F : ℕ → OracleProtocol → OracleProtocol`). *Why:* FRI's oracle in round `i` lives on a domain
  of size `2^(k-i)`. A `rounds` block may name the tree family of its rounds (`tree`) when each
  step agrees with it by `rfl`. *Why:* the elaborator cannot unfold a structural recursion on a
  variable `n` (smart unfolding), so `Sumcheck.protocol R d n` and a generic tree are not
  definitionally equal to it. Naming ArkLib's tree makes the statements of `Specs.Examples.Sumcheck`
  typecheck as they are.
* `rounds` counts the round up from `0` and the remaining rounds down to `0`, and passes the final
  state to the continuation with a cast along `j + 0 = n`. *Why:* the state of round `i` has type
  `State i`, and ArkLib's trees peel the first round. The cast is internal: no statement in these
  modules mentions it, and `subst` removes it in a proof about the last round.
* Hierarchical labels: a move is addressed by its stage path, its loop and round, and the base of
  its name.
  `Specs.Run` computes the position at elaboration time. *Why:* the position is then a numeral, so
  the accessor elaborates to a chain of projections that `rfl` and `simp` handle without unfolding
  string comparisons.
* Free-form text remains only as an optional `note` on a step, which the export marks unchecked.
-/

namespace Specs
open Interaction PFunctor FreeM

/-! ## Printed type names -/

/-- The printed name of a type, in TeX. -/
class TypeName (X : Type) where
  name : String

instance : TypeName ℕ := ⟨"\\mathbb{N}"⟩
instance : TypeName Bool := ⟨"\\{0,1\\}"⟩
instance {n : ℕ} : TypeName (Fin n) := ⟨"[" ++ toString n ++ "]"⟩

/-! ## Handles -/

/-- A first-order reference to an oracle: its level in the interpreter's handler table, and a
default answer. -/
structure Ref (Q A : Type) where
  lvl : ℕ
  dflt : A

/-- A transcript value or a local value named `nm`. -/
structure Val (nm : Name) (α : Type) where
  val : α

instance {nm : Name} {α : Type} : CoeOut (Val nm α) α := ⟨Val.val⟩

/-- An oracle named `nm`: the verifier reads it only through queries. -/
structure OHdl (nm : Name) (Q A : Type) where
  ref : Ref Q A

/-- Values for the holes `Γ` at run time: values for value holes, references for oracle holes. -/
abbrev Hs : List Hole → Type 1 := Args (fun α => α) Ref

/-- A tuple of handles that fills the holes `Γ`, in order. -/
class ToArgs (τ : Type) (Γ : outParam (List Hole)) where
  toArgs : τ → Hs Γ

instance {nm : Name} {α : Type} : ToArgs (Val nm α) [.val nm α] :=
  ⟨fun x => .val x.val .nil⟩

instance {nm : Name} {Q A : Type} : ToArgs (OHdl nm Q A) [.orc nm Q A] :=
  ⟨fun h => .orc h.ref .nil⟩

instance {τ σ : Type} {Γ Δ : List Hole} [ToArgs τ Γ] [ToArgs σ Δ] : ToArgs (τ × σ) (Γ ++ Δ) :=
  ⟨fun p => (ToArgs.toArgs p.1).append (ToArgs.toArgs p.2)⟩

instance : ToArgs Unit [] := ⟨fun _ => .nil⟩

section ArgsNotation
open Lean Elab Term Meta

/-- `⟪a, b, …⟫` is the formula arguments of the handles `a, b, …`, in order. The elaborator
resolves the holes right away, so a formula written after it sees its hole list. -/
syntax (name := argsNotation) "⟪" term,* "⟫" : term

@[term_elab argsNotation] def elabArgsNotation : TermElab := fun stx _ => do
  let xs : Array Term := match stx with
    | `(⟪$xs,*⟫) => xs.getElems
    | _ => #[]
  let tupStx ← match xs.back? with
    | none => `(())
    | some last => xs.pop.foldrM (fun x acc => `(($x, $acc))) last
  let tup ← elabTerm tupStx none
  synthesizeSyntheticMVars (postpone := .yes)
  let τ ← instantiateMVars (← inferType tup)
  let Γ ← mkFreshExprMVar (mkApp (mkConst ``List [Level.one]) (mkConst ``Hole))
  let inst ← synthInstance (mkApp2 (mkConst ``ToArgs) τ Γ)
  let Γ ← instantiateMVars Γ
  return mkApp4 (mkConst ``ToArgs.toArgs) τ Γ inst tup

end ArgsNotation

@[simp] theorem ToArgs.toArgs_val {nm : Name} {α : Type} (x : Val nm α) :
    ToArgs.toArgs x = .val x.val .nil := rfl
@[simp] theorem ToArgs.toArgs_ohdl {nm : Name} {Q A : Type} (h : OHdl nm Q A) :
    ToArgs.toArgs h = .orc h.ref .nil := rfl
@[simp] theorem ToArgs.toArgs_prod {τ σ : Type} {Γ Δ : List Hole} [ToArgs τ Γ] [ToArgs σ Δ]
    (p : τ × σ) : ToArgs.toArgs p = (ToArgs.toArgs p.1).append (ToArgs.toArgs p.2) := rfl

/-! ## The skeleton -/

/-- The kind of a move. -/
inductive MoveKind
  | message | oracle | challenge
  deriving DecidableEq, Repr, Inhabited

/-- The display data of a loop: the name of its block, its round variable, the symbol of its count
and the soundness error of one round, as annotation text over the round variable. -/
structure Loop where
  block : String
  var : String := "i"
  count : String := "n"
  error : String := ""
  deriving Inhabited, DecidableEq, Repr

/-- One item of a skeleton. `note` is free-form annotation text, never checked. -/
inductive Item
  /-- A move: its name, printed type and, for a prover move, the name of the honest function. -/
  | move (kind : MoveKind) (nm : Name) (ty : String) (honest : String) (note : String)
  /-- The description reads the input oracle `nm`. -/
  | input (nm : Name) (ty : String)
  /-- A check, as the syntax of its formula. -/
  | check (label : String) (φ : Syn) (note : String)
  /-- A local value and the syntax of its formula. -/
  | let_ (nm : Name) (ty : String) (φ : Syn) (note : String)
  /-- Round `j` of the loop `l`. Only the unrolled rounds of a loop (`Skel.unroll`) have round
  markers. -/
  | beginRound (l : Loop) (j : ℕ)
  | endRound
  /-- A stage and the syntax of its input and output claims. -/
  | beginStage (name : String) (input output : Syn)
  | endStage
  deriving Inhabited

/-- The skeleton of a description: items in protocol order, ending in a leaf, a branch on a
message with one sub-skeleton per case, an opaque branch, or a loop. -/
inductive Skel
  | done
  | cons (it : Item) (rest : Skel)
  | branch (nm : Name) (ty honest : String) (cases : List (String × Skel))
  | opaque (nm : Name) (ty honest : String)
  /-- A loop of `n` rounds with display data `l`: the skeleton `body` of one round, the same for
  every round, then `rest`. The body ends in `done` where the next round starts. -/
  | loop (l : Loop) (n : ℕ) (body rest : Skel)
  deriving Inhabited

/-- The skeleton node of a branching message: one case per listed value, or opaque. -/
def Skel.ofBranch {X : Type} (nm : Name) (ty honest : String)
    (cases : Option (List (String × X))) (ks : X → Skel) : Skel :=
  match cases with
  | some l => .branch nm ty honest (l.map fun c => (c.1, ks c.2))
  | none => .opaque nm ty honest

mutual
/-- The checks of a skeleton in protocol order, with their labels, through every branch. A loop
contributes the checks of its generic round once. -/
def Skel.checks : Skel → List (String × Syn)
  | .done => []
  | .opaque .. => []
  | .cons (.check label φ _) rest => (label, φ) :: rest.checks
  | .cons _ rest => rest.checks
  | .branch _ _ _ cases => Skel.casesChecks cases
  | .loop _ _ body rest => body.checks ++ rest.checks

/-- The checks of the cases of a branch, case by case. -/
def Skel.casesChecks : List (String × Skel) → List (String × Syn)
  | [] => []
  | (_, k) :: cs => k.checks ++ Skel.casesChecks cs
end

mutual
/-- The skeleton `s` followed by `k`: every `done` leaf of `s` becomes `k`. An opaque branch
keeps no continuation. -/
def Skel.seq : Skel → Skel → Skel
  | .done, k => k
  | .cons it rest, k => .cons it (rest.seq k)
  | .branch nm ty hn cases, k => .branch nm ty hn (Skel.seqCases cases k)
  | .opaque nm ty hn, _ => .opaque nm ty hn
  | .loop l n body rest, k => .loop l n body (rest.seq k)

/-- The cases of a branch, each followed by `k`. -/
def Skel.seqCases : List (String × Skel) → Skel → List (String × Skel)
  | [], _ => []
  | (v, s) :: cs, k => (v, s.seq k) :: Skel.seqCases cs k
end

/-- The rounds `j, …, j + k - 1` of the loop `l` with generic round `body`, each between round
markers, followed by `ks`. -/
@[reducible] def Skel.unroll (l : Loop) (body ks : Skel) : ℕ → ℕ → Skel
  | _, 0 => ks
  | j, k + 1 =>
    .cons (.beginRound l j) (body.seq (.cons .endRound (Skel.unroll l body ks (j + 1) k)))

mutual
/-- The skeleton with the count of every loop set to `0`: the data that the JSON and the folded
figure read. -/
def Skel.erase : Skel → Skel
  | .done => .done
  | .cons it rest => .cons it rest.erase
  | .branch nm ty hn cases => .branch nm ty hn (Skel.eraseCases cases)
  | .opaque nm ty hn => .opaque nm ty hn
  | .loop l _ body rest => .loop l 0 body.erase rest.erase

/-- The cases of a branch, erased. -/
def Skel.eraseCases : List (String × Skel) → List (String × Skel)
  | [] => []
  | (v, s) :: cs => (v, s.erase) :: Skel.eraseCases cs
end

/-! ## Descriptions -/

/-- A description of an interactive oracle protocol in continuation-passing style, with input
oracle bundle `In`, witness `W`, output `T`, tree `t` and skeleton `ks`. -/
inductive Desc (In : OracleBundle) (W T : Type) : OracleProtocol → Skel → Type 1
  | done (out : T) : Desc In W T (.pure ⟨⟩) .done
  | message (nm : Name) (X : Type) (ty hn note : String) (honest : W → X)
      {t : X → OracleProtocol} {ks : Skel} (rest : (x : X) → Desc In W T (t x) ks) :
      Desc In W T (.liftBind (.message X) t) (.cons (.move .message nm ty hn note) ks)
  | oracle (nm : Name) (X : Type) (I : OracleInterface X) (A : Type) (hA : ∀ q, I.spec q = A)
      (dflt : A) (ty hn note : String) (honest : W → X) {t : OracleProtocol} {ks : Skel}
      (rest : OHdl nm I.Query A → Desc In W T t ks) :
      Desc In W T (.liftBind (.oracle X I) fun _ => t) (.cons (.move .oracle nm ty hn note) ks)
  | challenge (nm : Name) (C : Type) (ty note : String) {t : OracleProtocol} {ks : Skel}
      (rest : C → Desc In W T t ks) :
      Desc In W T (.liftBind (.challenge C) fun _ => t) (.cons (.move .challenge nm ty "" note) ks)
  | check (label : String) (Γ : List Hole) (φ : Closed Γ Bool) (args : Hs Γ) (note : String)
      {t : OracleProtocol} {ks : Skel} (rest : Desc In W T t ks) :
      Desc In W T t (.cons (.check label φ.syntax note) ks)
  | compute (nm : Name) (α : Type) (ty : String) (Γ : List Hole) (φ : Closed Γ α)
      (args : Hs Γ) (note : String) {t : OracleProtocol} {ks : Skel}
      (rest : α → Desc In W T t ks) :
      Desc In W T t (.cons (.let_ nm ty φ.syntax note) ks)
  | input (nm : Name) (Q A : Type) (ty : String) (embed : Q → In.Query)
      (resp : ∀ q, In.spec (embed q) = A) (dflt : A) {t : OracleProtocol} {ks : Skel}
      (rest : OHdl nm Q A → Desc In W T t ks) :
      Desc In W T t (.cons (.input nm ty) ks)
  | branch (nm : Name) (X : Type) (ty hn : String) (honest : W → X)
      (cases : Option (List (String × X))) {t : X → OracleProtocol} {ks : X → Skel}
      (rest : (x : X) → Desc In W T (t x) (ks x)) :
      Desc In W T (.liftBind (.message X) t) (Skel.ofBranch nm ty hn cases ks)
  | stageIn (name : String) (Γ : List Hole) (φ : Closed Γ Bool) (args : Hs Γ)
      (Δ : List Hole) (ψ : Closed Δ Bool) {t : OracleProtocol} {ks : Skel}
      (rest : Desc In W T t ks) :
      Desc In W T t (.cons (.beginStage name φ.syntax ψ.syntax) ks)
  | stageOut (Δ : List Hole) (ψ : Closed Δ Bool) (args : Hs Δ) {t : OracleProtocol}
      {ks : Skel} (rest : Desc In W T t ks) :
      Desc In W T t (.cons .endStage ks)
  | mark (it : Item) {t : OracleProtocol} {ks : Skel} (rest : Desc In W T t ks) :
      Desc In W T t (.cons it ks)
  /-- A loop of `n` rounds: the unrolled rounds `inner`, which the skeleton shows as the generic
  round `body` with the display data `l`. -/
  | loop (l : Loop) (n : ℕ) (body : Skel) {t : OracleProtocol} {ks : Skel}
      (inner : Desc In W T t (Skel.unroll l body ks 0 n)) :
      Desc In W T t (.loop l n body ks)

variable {In : OracleBundle} {W T : Type}

/-- Move a description to a tree that is equal to its own. With an `rfl` proof, as `rounds`
uses, it reduces to the description. -/
def Desc.retree {t t' : OracleProtocol} {ks : Skel} (h : t = t') (d : Desc In W T t ks) :
    Desc In W T t' ks :=
  h ▸ d

@[simp] theorem Desc.retree_rfl {t : OracleProtocol} {ks : Skel} (h : t = t)
    (d : Desc In W T t ks) : d.retree h = d := rfl

/-- Move a description to a skeleton that is equal to its own. With an `rfl` proof, as `rounds`
uses, it reduces to the description. -/
def Desc.reskel {t : OracleProtocol} {ks ks' : Skel} (h : ks = ks') (d : Desc In W T t ks) :
    Desc In W T t ks' :=
  h ▸ d

@[simp] theorem Desc.reskel_rfl {t : OracleProtocol} {ks : Skel} (h : ks = ks)
    (d : Desc In W T t ks) : d.reskel h = d := rfl

/-! ## Combinators -/

/-- The protocol ends with output `out`. -/
abbrev done (out : T) : Desc In W T (.pure ⟨⟩) .done := .done out

/-- The prover sends the plain message `nm : X`, honestly `honest w`, printed as the function
`hn`. The continuation's tree may depend on the message. -/
abbrev message (nm : Name) (X : Type) [TypeName X] (hn : String) (honest : W → X)
    {t : Val nm X → OracleProtocol} {ks : Skel} (rest : (x : Val nm X) → Desc In W T (t x) ks)
    (note : String := "") (ty : String := TypeName.name X) :=
  Desc.message (t := fun x => t ⟨x⟩) nm X ty hn note honest fun x => rest ⟨x⟩

/-- The prover sends the oracle message `nm : X`, honestly `honest w`. The verifier gets a handle
that answers queries in `A`. `ty` prints the type, by default its `TypeName`. -/
abbrev oracle (nm : Name) (X : Type) [I : OracleInterface X] [TypeName X] (A : Type)
    [Inhabited A] (hn : String) (honest : W → X) {t : OracleProtocol} {ks : Skel}
    (rest : OHdl nm I.Query A → Desc In W T t ks) (note : String := "")
    (ty : String := TypeName.name X) (hA : ∀ q, I.spec q = A := by intros; rfl) :=
  Desc.oracle nm X I A hA default ty hn note honest rest

/-- The verifier samples the public challenge `nm : C`. -/
abbrev challenge (nm : Name) (C : Type) [TypeName C] {t : OracleProtocol} {ks : Skel}
    (rest : Val nm C → Desc In W T t ks) (note : String := "")
    (ty : String := TypeName.name C) :=
  Desc.challenge nm C ty note fun c => rest ⟨c⟩

/-- The description reads the input oracle `nm`: the query `q : Q` goes to `embed q` of the input
bundle, and `resp` shows that its answer has type `A` (usually `fun _ => rfl`). `resp` has no
default value, and the tree and skeleton come first. *Why:* Lean passes the expected type into an
application only when it has no optional arguments and its result type depends on no later
argument, and `embed` needs the input bundle from the expected type. -/
abbrev input {t : OracleProtocol} {ks : Skel} (nm : Name) (Q A : Type) [Inhabited A]
    (ty : String) (embed : Q → In.Query) (resp : ∀ q, In.spec (embed q) = A)
    (rest : OHdl nm Q A → Desc In W T t ks) :=
  Desc.input nm Q A ty embed resp default rest

/-- The verifier checks the formula `φ` on the handles `args`. The decision rejects when it
evaluates to `false`. -/
abbrev check (label : String) {Γ : List Hole} (args : Hs Γ)
    (φ : ∀ {v : Type → Type} {o : Type → Type → Type}, Curry v o Γ Bool) {t : OracleProtocol}
    {ks : Skel} (rest : Desc In W T t ks) (note : String := "") :=
  Desc.check label Γ ⟨φ⟩ args note rest

/-- The verifier computes the local value `nm : α` as the formula `φ` on the handles `args`. -/
abbrev compute (nm : Name) (α : Type) [TypeName α] {Γ : List Hole} (args : Hs Γ)
    (φ : ∀ {v : Type → Type} {o : Type → Type → Type}, Curry v o Γ α)
    {t : OracleProtocol} {ks : Skel} (rest : Val nm α → Desc In W T t ks)
    (note : String := "") :=
  Desc.compute nm α (TypeName.name α) Γ ⟨φ⟩ args note fun a => rest ⟨a⟩

/-- The prover sends the message `nm : X`, and the rest of the protocol depends on it. The
skeleton has one case for each element of `cases`, printed with its string. -/
abbrev branch (nm : Name) (X : Type) [TypeName X] (hn : String) (honest : W → X)
    (cases : List (String × X)) {t : Val nm X → OracleProtocol} {ks : Val nm X → Skel}
    (rest : (x : Val nm X) → Desc In W T (t x) (ks x)) :=
  Desc.branch (t := fun x => t ⟨x⟩) (ks := fun x => ks ⟨x⟩) nm X (TypeName.name X) hn honest
    (some cases) fun x => rest ⟨x⟩

/-- A branch on a message with no listed cases. The skeleton marks it opaque. -/
abbrev branchOpaque (nm : Name) (X : Type) [TypeName X] (hn : String) (honest : W → X)
    {t : Val nm X → OracleProtocol} {ks : Val nm X → Skel}
    (rest : (x : Val nm X) → Desc In W T (t x) (ks x)) :=
  Desc.branch (t := fun x => t ⟨x⟩) (ks := fun x => ks ⟨x⟩) nm X (TypeName.name X) hn honest
    none fun x => rest ⟨x⟩

/-- The default tree of the rounds `j, …, j + k - 1` of shape `F`, followed by `t`. -/
@[reducible] def roundsTree (F : ℕ → OracleProtocol → OracleProtocol) (t : OracleProtocol) :
    ℕ → ℕ → OracleProtocol
  | _, 0 => t
  | j, k + 1 => F j (roundsTree F t (j + 1) k)

/-- The rounds `j, …, j + k - 1` of a loop with display data `l` and generic round skeleton
`body`, on the tree family `τ`. -/
def roundsGo {State : ℕ → Type} {F : ℕ → OracleProtocol → OracleProtocol}
    (l : Loop) (n : ℕ) (B : Skel)
    (body : ∀ {t : OracleProtocol} {ks : Skel}, (i : ℕ) → i < n → State i →
      (State (i + 1) → Desc In W T t ks) → Desc In W T (F i t) (B.seq ks))
    {t : OracleProtocol} {ks : Skel} (next : State n → Desc In W T t ks)
    (τ : ℕ → ℕ → OracleProtocol) (h0 : ∀ j, τ j 0 = t)
    (hS : ∀ j k, τ j (k + 1) = F j (τ (j + 1) k)) :
    (k j : ℕ) → j + k = n → State j → Desc In W T (τ j k) (Skel.unroll l B ks j k)
  | 0, j, h, st => (next (h ▸ st)).retree (h0 j).symm
  | k + 1, j, h, st =>
    (Desc.mark (.beginRound l j) <|
      body j (by omega) st fun st' =>
        .mark .endRound (roundsGo l n B body next τ h0 hS k (j + 1) (by omega) st')).retree
      (hS j k).symm

/-- The rounds `j, …, j + k - 1` of a `rounds` block whose round `body` has skeleton `G ks`:
`roundsGo` with each round moved to the skeleton `(G .done).seq ks` along `hG`. Proofs about a
loop state their round induction on this term. -/
abbrev roundsFrom {State : ℕ → Type} {F : ℕ → OracleProtocol → OracleProtocol} {G : Skel → Skel}
    (l : Loop) (n : ℕ)
    (body : ∀ {t : OracleProtocol} {ks : Skel}, (i : ℕ) → i < n → State i →
      (State (i + 1) → Desc In W T t ks) → Desc In W T (F i t) (G ks))
    {t : OracleProtocol} {ks : Skel} (next : State n → Desc In W T t ks)
    (τ : ℕ → ℕ → OracleProtocol) (h0 : ∀ j, τ j 0 = t)
    (hS : ∀ j k, τ j (k + 1) = F j (τ (j + 1) k)) (hG : ∀ ks, G ks = (G .done).seq ks) :
    (k j : ℕ) → j + k = n → State j → Desc In W T (τ j k) (Skel.unroll l (G .done) ks j k) :=
  roundsGo l n (G .done) (fun i hi st k => (body i hi st k).reskel (hG _)) next τ h0 hS

/-- A loop of `n` rounds with round-indexed state: round `i`, counting up from `0`, maps `State i`
to `State (i + 1)` and has tree `F i`. The skeleton is one loop node whose body is the skeleton
of a generic round, `G .done`. The body's skeleton `G ks` may not depend on the round number:
`hG` checks that it is the generic round followed by `ks`. `block` names the loop, `var` is its
round variable and `countName` the symbol of `n`. `error` is the soundness error of one round, as
annotation text. `tree` names the tree family of the rounds, by default `roundsTree F t`. -/
abbrev rounds (block : String) (n : ℕ) {State : ℕ → Type} (init : State 0)
    {F : ℕ → OracleProtocol → OracleProtocol} {G : Skel → Skel}
    (body : ∀ {t : OracleProtocol} {ks : Skel}, (i : ℕ) → i < n → State i →
      (State (i + 1) → Desc In W T t ks) → Desc In W T (F i t) (G ks))
    {t : OracleProtocol} {ks : Skel} (next : State n → Desc In W T t ks)
    (error : String := "") (countName : String := "n") (var : String := "i")
    (tree : ℕ → ℕ → OracleProtocol := roundsTree F t)
    (h0 : ∀ j, tree j 0 = t := by intros; rfl)
    (hS : ∀ j k, tree j (k + 1) = F j (tree (j + 1) k) := by intros; rfl)
    (hG : ∀ ks, G ks = (G .done).seq ks := by intros; rfl) :=
  Desc.loop ⟨block, var, countName, error⟩ n (G .done)
    (roundsFrom ⟨block, var, countName, error⟩ n body next tree h0 hS hG n 0 (Nat.zero_add n)
      init)

/-- A named stage. It consumes the claim `φ` on `inArgs` and produces the claim `ψ` on
`outArgs s`, where `s` is the value it passes to the continuation. -/
abbrev stage (name : String) {Γ Δ : List Hole} (inArgs : Hs Γ)
    (φ : ∀ {v : Type → Type} {o : Type → Type → Type}, Curry v o Γ Bool) {S : Type}
    (outArgs : S → Hs Δ) (ψ : ∀ {v : Type → Type} {o : Type → Type → Type}, Curry v o Δ Bool)
    {t t' : OracleProtocol} {ks ks' : Skel}
    (body : (S → Desc In W T t (.cons .endStage ks)) → Desc In W T t' ks')
    (next : S → Desc In W T t ks) :=
  Desc.stageIn name Γ ⟨φ⟩ inArgs Δ ⟨ψ⟩ (body fun s => .stageOut Δ ⟨ψ⟩ (outArgs s) (next s))

/-! ## Specifications -/

/-- A protocol specification: a description for every input statement. The tree `t` and the
skeleton `ks` are parameters, so `Spec.mk` infers them from the description. -/
structure Spec (In : OracleBundle) (S W T : Type) (t : OracleProtocol) (ks : Skel) : Type 1 where
  /-- The description for each input statement. -/
  desc : S → Desc In W T t ks

namespace Spec
variable {S : Type} {t : OracleProtocol} {ks : Skel}

/-- The protocol tree of a specification. -/
abbrev tree (_ : Spec In S W T t ks) : OracleProtocol := t

/-- The skeleton of a specification, read from its type. Inlining drops the description, which is
usually noncomputable. -/
@[macro_inline] def skeleton (_ : Spec In S W T t ks) : Skel := ks

/-- The transcripts of a specification. -/
abbrev Tr (_ : Spec In S W T t ks) : Type := Transcript oracleSig t

/-- The verifier's views of a specification along the path `p`. -/
abbrev Vw (_ : Spec In S W T t ks) (p : Path t) : Type := View t p

end Spec

#print axioms Desc.retree_rfl
#print axioms Desc.reskel_rfl
#print axioms ToArgs.toArgs_prod

end Specs

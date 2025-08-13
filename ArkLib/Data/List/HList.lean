/-
Copyright (c) 2024 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import Mathlib.Data.Matrix.DMatrix
import Mathlib.Data.Fin.Tuple.Curry
import Mathlib.Tactic

/-!
  # Heterogeneous Lists

  We define `HList` as a synonym for `List (Σ α : Type u, α)`, namely a list of types together with
  a value.

  We note some other implementations of `HList`:
  - [Soup](https://github.com/crabbo-rave/Soup/tree/master)
  - Part of Certified Programming with Dependent Types (it's in Coq, but can be translated to Lean)

  Our choice of definition is so that we can directly rely on the existing API for `List`.
-/

universe u v

/-- Heterogeneous list -/
abbrev HList := List (Σ α : Type u, α)

namespace HList

def nil : HList := []

def cons (x : Σ α : Type u, α) (xs : HList) : HList := x :: xs

syntax (name := hlist) "[" term,* "]ₕ" : term
macro_rules (kind := hlist)
  | `([]ₕ) => `(HList.nil)
  | `([$x]ₕ) => `(HList.cons $x HList.nil)
  | `([$x, $xs,*]ₕ) => `(HList.cons $x [$xs,*]ₕ)

/- HList.cons notation -/
infixr:67 " ::ₕ " => HList.cons

variable {x : (α : Type u) × α} {xs : HList}

@[simp]
lemma cons_eq_List.cons : x ::ₕ xs = x :: xs := rfl

@[simp]
lemma length_nil : nil.length = 0 := rfl

@[simp]
lemma length_cons (x : Σ α : Type u, α) (xs : HList) : (x ::ₕ xs).length = xs.length + 1 := rfl

/-- Returns the types of the elements in the `HList` -/
def getTypes : HList → List (Type u) := List.map (fun x => x.1)

@[simp]
lemma getTypes_nil : getTypes [] = [] := rfl

@[simp]
lemma getTypes_cons (x : Σ α : Type u, α) (xs : HList) :
    getTypes (x :: xs) = x.1 :: xs.getTypes := rfl

@[simp]
lemma getTypes_hcons (x : Σ α : Type u, α) (xs : HList) :
    (x ::ₕ xs).getTypes = x.1 :: xs.getTypes := rfl

@[simp]
lemma length_getTypes (l : HList) : l.getTypes.length = l.length := by
  induction l with
  | nil => simp
  | cons _ xs ih => simp [ih]

@[simp]
lemma getTypes_eq_get_fst (l : HList) (i : Fin l.length) : l.getTypes[i] = l[i].1 := by
  induction l with
  | nil => simp at i; exact isEmptyElim i
  | cons x xs ih =>
    refine Fin.cases ?_ (fun i => ?_) i
    · simp
    · aesop


/-- Get the value of the element at index `i`, of type `l[i].1` -/
def getValue (l : HList) (i : Fin l.length) := l[i].2

end HList

variable {α : Type u} {n : ℕ}

@[simp]
lemma List.get_nil (i : Fin 0) (a : α) : [].get i = a := by exact isEmptyElim i

/-- Dependent vectors
-/
def DVec {m : Type v} (α : m → Type u) : Type (max u v) := ∀ i, α i


/-- Convert a `HList` to a `DVec` -/
def HList.toDVec (l : HList) : DVec (m := Fin l.length) (fun i => l[i].1) := fun i => l[i].2

/-- Create an `HList` from a `DVec` -/
def HList.ofDVec {α : Fin n → Type u} (l : DVec (m := Fin n) α) :
    HList := (List.finRange n).map fun i => ⟨α i, l i⟩

-- /-- Convert a `DVec` to an `HList` -/
-- def DVec.toHList (l : DVec (m := Fin n) α) : HList := (List.finRange n).map fun i => ⟨α i, l i⟩

-- theorem DVec.toHList_getTypes (l : DVec (m := Fin n) α) :
--     l.toHList.getTypes = List.ofFn α := by aesop


/-- Equivalent between `HList.getValue` and `HList.toDVec` -/
lemma HList.toDVec_eq_getValue (l : HList) (i : Fin l.length) : l.toDVec i = l.getValue i := rfl


/-

Other candidate implementations of `HList`:

-- This is a port from [Soup](https://github.com/crabbo-rave/Soup/tree/master)

inductive HList : List (Type u) → Type (u + 1) where
  | nil : HList []
  | cons {α : Type u} (x : α) {αs : List (Type u)} (xs : HList αs) : HList (α :: αs)

syntax (name := hlist) "[" term,* "]ₕ" : term
macro_rules (kind := hlist)
  | `([]ₕ) => `(HList.nil)
  | `([$x]ₕ) => `(HList.cons $x HList.nil)
  | `([$x, $xs,*]ₕ) => `(HList.cons $x [$xs,*]ₕ)

/- HList.cons notation -/
infixr:67 " ::ₕ " => HList.cons


namespace HList

/-- Returns the first element of a HList -/
def head {α : Type u} {αs : List (Type u)} : HList (α :: αs) → α
  | x ::ₕ _ => x

/-- Returns a HList of all the elements besides the first -/
def tail {α : Type u} {αs : List (Type u)} : HList (α :: αs) → HList αs
  | _ ::ₕ xs => xs

/-- Returns the length of a HList -/
def length {αs : List (Type u)} (_ : HList αs) := αs.length

/-- Returns the nth element of a HList -/
@[reducible]
def get {αs : List (Type u)} : HList αs → (n : Fin αs.length) → αs.get n
  | x ::ₕ _, ⟨0, _⟩ => x
  | _ ::ₕ xs, ⟨n+1, h⟩ => xs.get ⟨n, Nat.lt_of_succ_lt_succ h⟩

def getTypes {αs : List Type} (_ : HList αs) : List Type := αs

/--
`O(|join L|)`. `join L` concatenates all the lists in `L` into one list.
* `join [[a], [], [b, c], [d, e, f]] = [a, b, c, d, e, f]`
-/
-- def join {αs : List (Type u)} {βs : αs → List (Type v)} : HList (List (HList βs)) → HList αs
--   | []      => []
--   | a :: as => a ++ join as

@[simp] theorem join_nil : List.join ([] : List (List α)) = [] := rfl
@[simp] theorem join_cons : (l :: ls).join = l ++ ls.join := rfl


section Repr

class HListRepr (α : Type _) where
  repr: α → Std.Format

instance : HListRepr (HList []) where
  repr := fun _ => ""

instance [Repr α] (αs : List Type) [HListRepr (HList αs)] : HListRepr (HList (α :: αs)) where
  repr
  | HList.cons x xs =>
    match xs with
    | HList.nil => reprPrec x 0
    | HList.cons _ _ => reprPrec x 0 ++ ", " ++ HListRepr.repr xs

/-- Repr instance for HLists -/
instance (αs : List Type) [HListRepr (HList αs)] : Repr (HList αs) where
  reprPrec
  | v, _ => "[" ++ HListRepr.repr v ++ "]"

class HListString (α : Type _) where
  toString : α → String

instance : HListString (HList []) where
  toString
  | HList.nil => ""

instance [ToString α] (αs : List Type) [HListString (HList αs)] :
    HListString (HList (α :: αs)) where
  toString
  | HList.cons x xs =>
    match xs with
    | HList.nil => toString x
    | HList.cons _ _ => toString x ++ ", " ++ HListString.toString xs

/-- ToString instance for HLists -/
instance (αs : List Type) [HListString (HList αs)] : ToString (HList αs) where
  toString : HList αs → String
  | t => "[" ++ HListString.toString t ++ "]"

end Repr

def test : HList [Nat, String, Nat] :=
  HList.cons 1 (HList.cons "bad" (HList.cons 3 HList.nil))

#eval test


-- def mapNthNoMetaEval : (n : Fin αs.length) → ((αs.get n) → β) → HList αs → HList (αs.repla n β)
--   | ⟨0, _⟩, f, a::as => (f a)::as
--   | ⟨n+1, h⟩, f, a::as => a::(as.mapNthNoMetaEval ⟨n, Nat.lt_of_succ_lt_succ h⟩ f)

-- def mapNth (n : Fin' αs.length) (f : (αs.get' n) → β) (h : HList αs) :
--     HList (αs.replaceAt n β) :=
--   let typeSig : List Type := αs.replaceAt n β
--   the (HList typeSig) (h.mapNthNoMetaEval n f)

end HList


inductive HList' {α : Type v} (β : α → Type u) : List α → Type (max u v)
  | nil  : HList' β []
  | cons : β i → HList' β is → HList' β (i :: is)

namespace HList'

variable {α : Type v} (β : α → Type u)

inductive member (a : α) : List α → Type v where
  | first : member a (a :: is)
  | next : member a is → member a (b :: is)

def length : HList' β ls → Nat
  | nil => 0
  | cons _ xs => xs.length + 1


def get (mls : HList' β ls) : member a ls → β a := match mls with
  | nil => fun h => nomatch h
  | cons x xs => fun h => match h with
    | member.first => x
    | member.next h => get xs h

#check HList'.get

def someTypes : List Type := [Nat, String, Nat]

def someValues : HList' (fun x => x) someTypes :=
  HList'.cons 1 (HList'.cons "bad" (HList'.cons 3 HList'.nil))

#eval HList'.get (fun x => x) someValues HList'.member.first

def somePairs : HList' (fun x => x × x) someTypes :=
  HList'.cons (1, 1) (HList'.cons ("good", "bad") (HList'.cons (5, 3) HList'.nil))

#eval HList'.get (fun x => x × x) somePairs (HList'.member.next HList'.member.first)

end HList'

-/

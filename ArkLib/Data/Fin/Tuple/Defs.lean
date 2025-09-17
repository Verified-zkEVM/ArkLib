/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import Mathlib.Data.Fin.Tuple.Take

/-!
# Custom Fin tuple operations with better definitional equality

This file provides custom tuple operations that use pattern matching for better definitional
equality, replacing standard library functions that rely on complex constructions like `cases`,
`addCases`, and conditional statements with casts.

## Utility operations:

- `Fin.rtake`: Taking from the right (i.e. the end) of a tuple
- `Fin.drop`: Dropping from the left (i.e. the beginning) of a tuple
- `Fin.rdrop`: Dropping from the right (i.e. the end) of a tuple
- `Fin.extract`: Extract a sub-tuple from a given range
- `Fin.rightpad`: Padding (or truncation) on the right of a tuple
- `Fin.leftpad`: Padding (or truncation) on the left of a tuple

## Three-Tier Construction System:

**Dependent operations (`d*`)**: Work with a unified motive `Fin n → Sort*` that determines the type
at each position. These are the foundational operations.
- `Fin.dcons`, `Fin.dconcat`, `Fin.dappend`

**Homogeneous operations (`v*`)**: Specialize the dependent operations to constant-type motives `fun
_ => α`, creating vectors where all elements have the same type.
- `Fin.vcons`, `Fin.vconcat`, `Fin.vappend`

**Functorial operations (`f*`)**: Apply a type constructor `F` uniformly across all positions of a
heterogeneous tuple, with the return type constructed using `v*` operations at the type level. We
define versions for both the unary and binary versions of `F` (arbitrary arity version?)
- `Fin.fcons`, `Fin.fconcat`, `Fin.fappend`
- `Fin.fcons₂`, `Fin.fconcat₂`, `Fin.fappend₂`

**Heterogeneous operations (`h*`)**: Specialize the unary functorial operations to the identity
functor, allowing different types at each position without requiring an explicit motive.
- `Fin.hcons`, `Fin.hconcat`, `Fin.happend`

## Empty tuples:

- `Fin.dempty`/`Fin.vempty`: Empty tuples for dependent and homogeneous cases
-/

universe u v w

namespace Fin

/-- Take the last `m` elements of a finite vector -/
def rtake {n : ℕ} {α : Fin n → Sort*} (m : ℕ) (h : m ≤ n) (v : (i : Fin n) → α i) :
    (i : Fin m) → α (Fin.cast (Nat.sub_add_cancel h) (natAdd (n - m) i)) :=
  fun i => v (Fin.cast (Nat.sub_add_cancel h) (natAdd (n - m) i))

/-- Drop the first `m` elements of an `n`-tuple where `m ≤ n`, returning an `(n - m)`-tuple. -/
def drop {n : ℕ} {α : Fin n → Sort*} (m : ℕ) (h : m ≤ n) (v : (i : Fin n) → α i) :
    (i : Fin (n - m)) → α (Fin.cast (Nat.sub_add_cancel h) (addNat i m)) :=
  fun i ↦ v (Fin.cast (Nat.sub_add_cancel h) (addNat i m))

/-- Drop the last `m` elements of an `n`-tuple where `m ≤ n`, returning an `(n - m)`-tuple.

This is defined to be taking the first `n - m` elements of the tuple. Thus, one should not use this
and use `Fin.take` instead. -/
abbrev rdrop {n : ℕ} {α : Fin n → Sort*} (m : ℕ) (h : m ≤ n) (v : (i : Fin n) → α i) :
    (i : Fin (n - m)) → α (Fin.cast (Nat.sub_add_cancel h) (i.castAdd m)) :=
  take (n - m) (by omega) v

/-- Extract a sub-tuple from a `Fin`-tuple, from index `start` to `stop - 1`. -/
def extract {n : ℕ} {α : Fin n → Sort*} (start stop : ℕ) (h1 : start ≤ stop) (h2 : stop ≤ n)
    (v : (i : Fin n) → α i) : (i : Fin (stop - start)) → α ⟨i + start, by omega⟩ :=
  fun i ↦ v ⟨i + start, by omega⟩

/-- Extracting with `start = 0` is the same as taking the first `stop` elements. -/
lemma extract_start_zero_eq_take {n : ℕ} {α : Fin n → Sort*} (stop : ℕ) (h : stop ≤ n)
    (v : (i : Fin n) → α i) : extract 0 stop (Nat.zero_le _) h v = take stop h v :=
  rfl

/-- Extracting with `stop = n` is the same as dropping the first `start` elements. -/
lemma extract_stop_last_eq_drop {n : ℕ} {α : Fin n → Sort*} (start : ℕ) (h : start ≤ n)
    (v : (i : Fin n) → α i) : extract start n h (Nat.le_refl _) v = drop start h v :=
  rfl

/-- Pad a `Fin`-indexed vector on the right with an element `a`.

This becomes truncation if `n < m`. -/
def rightpad {m : ℕ} {α : Sort*} (n : ℕ) (a : α) (v : Fin m → α) : Fin n → α :=
  fun i => if h : i < m then v ⟨i, h⟩ else a

/-- Pad a `Fin`-indexed vector on the left with an element `a`.

This becomes truncation if `n < m`. -/
def leftpad {m : ℕ} {α : Sort*} (n : ℕ) (a : α) (v : Fin m → α) : Fin n → α :=
  fun i => if h : n - m ≤ i then v ⟨i - (n - m), by omega⟩ else a

section Vec

/-- Dependent cons with unified motive: prepends `a : motive 0` to a dependent tuple
`(i : Fin n) → motive i.succ` using pattern matching for better definitional equality.

This is meant to replace `Fin.cons` for dependent tuples with a unified motive.

Notation: `a ::ᵈ b` or `a ::ᵈ⟨motive⟩ b` for explicit motive specification. -/
@[elab_as_elim]
def dcons {n : ℕ} {motive : Fin (n + 1) → Sort u} (a : motive 0)
    (b : (i : Fin n) → motive i.succ) (i : Fin (n + 1)) : motive i :=
  match n with
  | 0 => match i with | 0 => a
  | _ + 1 => match i with
    | 0 => a
    | ⟨k + 1, hk⟩ => b ⟨k, Nat.succ_lt_succ_iff.mp hk⟩

/-- Dependent snoc with unified motive: appends `a : motive (last n)` to the end of a
dependent tuple `(i : Fin n) → motive i.castSucc` using pattern matching for better
definitional equality.

This is meant to replace `Fin.snoc` for dependent tuples with a unified motive.

Notation: `u :+ᵈ a` or `u :+ᵈ⟨motive⟩ a` for explicit motive specification. -/
@[elab_as_elim]
def dconcat {n : ℕ} {motive : Fin (n + 1) → Sort u}
    (u : (i : Fin n) → motive i.castSucc) (a : motive (last n)) (i : Fin (n + 1)) : motive i :=
  match n with
  | 0 => match i with | 0 => a
  | _ + 1 => dcons (u 0) (dconcat (fun i => u (Fin.succ i)) a) i

/-- Dependent append with unified motive: concatenates two dependent tuples under a shared motive
using pattern matching for better definitional equality.

This is meant to replace `Fin.addCases` for dependent tuples with a unified motive.

Notation: `u ++ᵈ v` or `u ++ᵈ⟨motive⟩ v` for explicit motive specification. -/
@[elab_as_elim]
def dappend {m n : ℕ} {motive : Fin (m + n) → Sort u}
    (u : (i : Fin m) → motive (Fin.castAdd n i))
    (v : (i : Fin n) → motive (Fin.natAdd m i))
    (i : Fin (m + n)) : motive i :=
  match n with
  | 0 => u i
  | k + 1 => dconcat (dappend u (fun i => v (Fin.castSucc i))) (v (Fin.last k)) i

variable {α : Sort*}

/-- `vempty` is the empty vector, and a wrapper around `Fin.elim0`.

Notation: `!v[]` or `!v⟨α⟩[]` with explicit type ascription. -/
abbrev vempty {α : Sort*} : Fin 0 → α := Fin.elim0

/-- Homogeneous cons: prepends `a : α` to a vector by specializing `dcons` to the
constant-type motive `fun _ => α`.

Notation: `a ::ᵛ v` (using standard `::` for vectors). -/
def vcons {n : ℕ} (a : α) (v : Fin n → α) : Fin (n + 1) → α :=
  dcons a v
  -- match n with
  -- | 0 => match i with | 0 => a
  -- | _ + 1 => match i with
  --   | 0 => a
  --   | ⟨k + 1, hk⟩ => v ⟨k, Nat.lt_of_succ_lt_succ hk⟩

/-- Homogeneous snoc: appends `a : α` to the end of a vector by specializing `dconcat` to the
constant-type motive `fun _ => α`.

Notation: `v :+ᵛ a`. -/
def vconcat {n : ℕ} (v : Fin n → α) (a : α) : Fin (n + 1) → α :=
  dconcat v a
  -- match n with
  -- | 0 => fun i => match i with | 0 => a
  -- | _ + 1 => vcons (v 0) (vconcat (v ∘ Fin.succ) a)

/-- Homogeneous append: concatenates two vectors by specializing `dappend` to the
constant-type motive `fun _ => α`.

Notation: `u ++ᵛ v` or standard `u ++ v`. -/
def vappend {m n : ℕ} {α : Sort*} (u : Fin m → α) (v : Fin n → α) : Fin (m + n) → α :=
  dappend u v
  -- match n with
  -- | 0 => u
  -- | _ + 1 => vconcat (vappend u (v ∘ Fin.castSucc)) (v (Fin.last _))

end Vec

/-- `dempty` is the dependent empty tuple.

Notation: `!d[]`, `!d⟨motive⟩[]`, or `!h[]` for heterogeneous usage. -/
def dempty {α : Fin 0 → Sort u} : (i : Fin 0) → α i := fun i => Fin.elim0 i

/-- Functorial cons: prepends `a : F α` to a functorial tuple `(i : Fin n) → F (β i)`,
with the return type constructed as `(i : Fin (n + 1)) → F (vcons α β i)` where `F` is applied
to the motive built by `vcons` at the type level.

Unlike `dcons` which requires an explicit unified motive, `fcons` uses `vcons` to automatically
construct the motive from the input types and applies functor `F` uniformly. When `F` is the
identity functor, this reduces to `hcons`.

Notation: `a ::ʰ⦃F⦄⟨α ; β⟩ b` with explicit functor and type ascriptions. -/
def fcons {A : Sort u} {F : A → Sort v} {n : ℕ} {α : A} {β : Fin n → A}
    (a : F α) (b : (i : Fin n) → F (β i)) : (i : Fin (n + 1)) → F (Fin.vcons α β i) :=
  match n with
  | 0 => fun i => match i with | 0 => a
  | _ + 1 => fun i => match i with
    | 0 => a
    | ⟨k + 1, hk⟩ => b ⟨k, Nat.succ_lt_succ_iff.mp hk⟩

/-- Functorial cons with two arguments: prepends `a : F α₁ α₂` to a functorial tuple
`(i : Fin n) → F (β₁ i) (β₂ i)`, with the return type constructed as
`(i : Fin (n + 1)) → F (vcons α₁ β₁ i) (vcons α₂ β₂ i)` where `F` is applied to the two motives
built by `vcons` at the type level.

Notation: `a ::ʰ⦃F⦄⟨α₁ ; β₁⟩⟨α₂ ; β₂⟩ b` with explicit binary functor and type ascriptions. -/
def fcons₂ {A : Sort u} {B : Sort v} {F : A → B → Sort w} {n : ℕ}
    {α₁ : A} {β₁ : Fin n → A} {α₂ : B} {β₂ : Fin n → B}
    (a₁ : F α₁ α₂) (b : (i : Fin n) → F (β₁ i) (β₂ i)) :
    (i : Fin (n + 1)) → F (Fin.vcons α₁ β₁ i) (Fin.vcons α₂ β₂ i) :=
  match n with
  | 0 => fun i => match i with | 0 => a₁
  | _ + 1 => fun i => match i with
    | 0 => a₁
    | ⟨k + 1, hk⟩ => b ⟨k, Nat.succ_lt_succ_iff.mp hk⟩

/-- Heterogeneous cons: prepends `a : α` to a tuple `(i : Fin n) → β i`, with the return type
constructed as `(i : Fin (n + 1)) → vcons α β i` where `vcons` builds the motive at the type level.

This is a specialization of `fcons` to the identity functor, allowing different types at each
position without requiring an explicit motive.

Notation: `a ::ʰ b`. -/
def hcons {n : ℕ} {α : Sort u} {β : Fin n → Sort u} (a : α) (b : (i : Fin n) → β i) :
    (i : Fin (n + 1)) → Fin.vcons α β i :=
  fcons (F := id) a b

/-- Functorial snoc: appends `a : F β` to the end of a functorial tuple `(i : Fin n) → F (α i)`,
  with the return type constructed as `(i : Fin (n + 1)) → F (vconcat α β i)` where `F` is applied
  to the motive built by `vconcat` at the type level.

Unlike `dconcat` which requires an explicit unified motive, `fconcat` uses `vconcat` to
automatically construct the motive from the input types and applies functor `F` uniformly. When `F`
is the identity functor, this reduces to `hconcat`.

Notation: `u :+ʰ⦃F⦄⟨α ; β⟩ a` with explicit functor and type ascriptions. -/
def fconcat {A : Sort u} {F : A → Sort v} {n : ℕ} {α : Fin n → A} {β : A}
    (u : (i : Fin n) → F (α i)) (a : F β) : (i : Fin (n + 1)) → F (Fin.vconcat α β i) :=
  match n with
  | 0 => fun i => match i with | 0 => a
  | _ + 1 => fcons (u 0) (fconcat (fun i => u (Fin.succ i)) a)

/-- Functorial snoc with two arguments: appends `a : F β₁ β₂` to the end of a functorial tuple
`(i : Fin n) → F (α₁ i) (α₂ i)`, with the return type constructed as
`(i : Fin (n + 1)) → F (vconcat α₁ β₁ i) (vconcat α₂ β₂ i)` where `F` is applied
to the two motives built by `vconcat` at the type level.

Notation: `u :+ʰ⦃F⦄⟨α₁ ; β₁⟩⟨α₂ ; β₂⟩ a` with explicit binary functor and type ascriptions. -/
def fconcat₂ {A : Sort u} {B : Sort v} {F : A → B → Sort w} {n : ℕ}
    {α₁ : Fin n → A} {β₁ : A} {α₂ : Fin n → B} {β₂ : B}
    (u : (i : Fin n) → F (α₁ i) (α₂ i)) (a : F β₁ β₂) :
    (i : Fin (n + 1)) → F (Fin.vconcat α₁ β₁ i) (Fin.vconcat α₂ β₂ i) :=
  match n with
  | 0 => fun i => match i with | 0 => a
  | _ + 1 => fcons₂ (u 0) (fconcat₂ (fun i => u (Fin.succ i)) a)

/-- Heterogeneous snoc: appends `a : β` to the end of a tuple `(i : Fin n) → α i`, with the
return type constructed as `(i : Fin (n + 1)) → vconcat α β i` where `vconcat` builds the motive
at the type level.

This is a specialization of `fconcat` to the identity functor.

Notation: `u :+ʰ a`. -/
def hconcat {n : ℕ} {α : Fin n → Sort u} {β : Sort u} (u : (i : Fin n) → α i) (a : β) :
    (i : Fin (n + 1)) → Fin.vconcat α β i :=
  fconcat (F := id) u a

/-- Functorial append: concatenates functorial tuples `(i : Fin m) → F (α i)` and `(i : Fin n) → F
  (β i)`, with the return type constructed as `(i : Fin (m + n)) → F (vappend α β i)` where `F` is
  applied to the motive built by `vappend` at the type level.

Unlike `dappend` which requires an explicit unified motive, `fappend` uses `vappend` to
automatically construct the motive from the input types and applies functor `F` uniformly. When `F`
is the identity functor, this reduces to `happend`.

Notation: `u ++ʰ⦃F⦄⟨α ; β⟩ v` with explicit functor and type ascriptions. -/
def fappend {A : Sort u} {F : A → Sort v} {m n : ℕ} {α : Fin m → A} {β : Fin n → A}
    (u : (i : Fin m) → F (α i)) (v : (i : Fin n) → F (β i)) :
    (i : Fin (m + n)) → F (Fin.vappend α β i) :=
  match n with
  | 0 => u
  | k + 1 => fconcat (fappend u (fun i => v (Fin.castSucc i))) (v (Fin.last k))

/-- Functorial append with two arguments: concatenates functorial tuples `(i : Fin m) → F (α i)` and
`(i : Fin n) → F (β i)`, with the return type constructed as
`(i : Fin (m + n)) → F (vappend α₁ β₁ i) (vappend α₂ β₂ i)` where `F` is applied to the two motives
built by `vappend` at the type level.

Notation: `u ++ʰ⦃F⦄⟨α₁ ; β₁⟩⟨α₂ ; β₂⟩ v` with explicit binary functor and type ascriptions. -/
def fappend₂ {A : Sort u} {B : Sort v} {F : A → B → Sort w} {m n : ℕ}
    {α₁ : Fin m → A} {β₁ : Fin n → A} {α₂ : Fin m → B} {β₂ : Fin n → B}
    (u : (i : Fin m) → F (α₁ i) (α₂ i)) (v : (i : Fin n) → F (β₁ i) (β₂ i)) :
    (i : Fin (m + n)) → F (Fin.vappend α₁ β₁ i) (Fin.vappend α₂ β₂ i) :=
  match n with
  | 0 => u
  | k + 1 => fconcat₂ (fappend₂ u (fun i => v (Fin.castSucc i))) (v (Fin.last k))

/-- Heterogeneous append: concatenates tuples `(i : Fin m) → α i` and `(i : Fin n) → β i`,
with the return type constructed as `(i : Fin (m + n)) → vappend α β i` where `vappend` builds
the motive at the type level.

This is a specialization of `fappend` to the identity functor.

Notation: `u ++ʰ v`. -/
def happend {m n : ℕ} {α : Fin m → Sort u} {β : Fin n → Sort u}
    (u : (i : Fin m) → α i) (v : (i : Fin n) → β i) : (i : Fin (m + n)) → Fin.vappend α β i :=
  fappend (F := id) u v

/-- Cast a dependent or heterogeneous vector across an equality `n' = n` and a family of equalities
  `∀ i, α (Fin.cast h i) = α' i`.

This is meant to replace `Fin.cast` for our use cases, as this definition offers better
definitional equality. -/
protected def dcast {n n' : ℕ} {α : Fin n → Sort u} {α' : Fin n' → Sort u}
    (h : n' = n) (hα : ∀ i, α (Fin.cast h i) = α' i) (v : (i : Fin n) → α i) :
      (i : Fin n') → α' i :=
  fun i => _root_.cast (hα i) (v (Fin.cast h i))

end Fin

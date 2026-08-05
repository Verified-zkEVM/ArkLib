/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

/-!
# Pushing a projection through a monad lift

`monadLift_bind_map` moves a post-composed function from the continuation of a lifted computation
into the lifted computation itself. It is the `monadLift`-generic form of `bind_map_left`, and is a
two-step composite of the Lean core lemmas `monadLift_map` and `bind_map_left`.

Upstreaming candidate: the statement mentions nothing outside Lean core, so it belongs beside
`Init.Control.Lawful.MonadLift.Lemmas`.

Note on normal forms: core's simp set already rewrites this lemma's right-hand side *into* its
left-hand side (via `liftM_map` and `bind_map_left`, both `@[simp]`), so this is deliberately not
tagged `@[simp]` — use it explicitly, typically right-to-left to expose a lemma about `h <$> x`.
-/

universe u v w

/-- Lifting a computation and post-composing `h` in the continuation is the same as lifting the
`h`-mapped computation. Use it to move a projection inside a `monadLift` so that lemmas about the
projected computation apply. -/
theorem monadLift_bind_map {m : Type u → Type v} {n : Type u → Type w}
    [Monad m] [LawfulMonad m] [Monad n] [LawfulMonad n]
    [MonadLiftT m n] [LawfulMonadLiftT m n] {α α' γ : Type u}
    (h : α → α') (x : m α) (f : α' → n γ) :
    ((monadLift x : n α) >>= fun a => f (h a)) = (monadLift (h <$> x) : n α') >>= f := by
  rw [monadLift_map, bind_map_left]

/-- The `Prod.fst` case of `monadLift_bind_map`: discard the second component of a lifted
pair-valued computation. -/
theorem monadLift_bind_fst {m : Type u → Type v} {n : Type u → Type w}
    [Monad m] [LawfulMonad m] [Monad n] [LawfulMonad n]
    [MonadLiftT m n] [LawfulMonadLiftT m n] {α β γ : Type u}
    (x : m (α × β)) (f : α → n γ) :
    ((monadLift x : n (α × β)) >>= fun p => f p.1) = (monadLift (Prod.fst <$> x) : n α) >>= f :=
  monadLift_bind_map Prod.fst x f

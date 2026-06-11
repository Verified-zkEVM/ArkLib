/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib.Data.Vector.Basic
import VCVio.EvalDist.Monad.Basic

/-!
# Additions to VCV-io's `ToMathlib.Data.Vector.Basic`
-/

/-- `Vector.mapM` commutes with post-composition by a pure map:
    mapping `g` after each monadic action is the same as mapping `g` over the collected vector. -/
lemma Vector.mapM_map_postcomp {m : Type → Type} {α β γ : Type} {n : ℕ}
    [Monad m] [LawfulMonad m]
    (v : Vector α n) (f : α → m β) (g : β → γ) :
    (v.mapM (fun a => g <$> f a)) = (Vector.map g) <$> (v.mapM f) := by
  have hlist : ∀ l : List α, l.mapM (fun a => g <$> f a) = List.map g <$> l.mapM f := by
    intro l
    induction l with
    | nil => simp
    | cons a t ih => simp [ih]
  apply Vector.map_toArray_inj.mp
  rw [Vector.toArray_mapM]
  simp only [Functor.map_map, Vector.toArray_map]
  rw [← Functor.map_map]
  rw [Vector.toArray_mapM]
  rw [Array.mapM_eq_mapM_toList, Array.mapM_eq_mapM_toList]
  simp only [Functor.map_map]
  rw [hlist]
  simp [Functor.map_map]

/-- `Option.map` distributes through `Vector.mapM id` (sequencing of options):
    mapping before sequencing equals sequencing then mapping. -/
lemma Vector.mapM_id_option_map_comm {α β : Type} {n : ℕ}
    (v : Vector (Option α) n) (g : α → β) :
    (v.map (Option.map g)).mapM (id : Option β → Option β) =
    (v.mapM (id : Option α → Option α)).map (Vector.map g) := by
  rw [Vector.mapM_map]
  exact Vector.mapM_map_postcomp v (id : Option α → Option α) g

/-- Two `Vector.mapM` calls with pointwise-related monadic bodies produce equal
    results after compatible post-processing when the bodies differ by a pure map. -/
lemma Vector.mapM_bind_map_eq {m : Type → Type} {α β γ δ : Type} {n : ℕ}
    [Monad m] [LawfulMonad m]
    (v : Vector α n)
    (f₁ : α → m γ) (f₂ : α → m β) (g : β → γ)
    (hf : ∀ a, f₁ a = g <$> f₂ a)
    (post₁ : Vector γ n → m δ) (post₂ : Vector β n → m δ)
    (hpost : ∀ opts, post₁ (opts.map g) = post₂ opts) :
    (v.mapM f₁ >>= post₁) = (v.mapM f₂ >>= post₂) := by
  have hf' : f₁ = fun a => g <$> f₂ a := by
    funext a
    exact hf a
  rw [hf']
  rw [Vector.mapM_map_postcomp]
  simp only [map_eq_bind_pure_comp, bind_assoc, Function.comp, pure_bind]
  apply bind_congr
  intro opts
  exact hpost opts

/-- Index-extraction for `Vector.mapM`: any component of a vector in the support of
    the sequenced computation lies in the support of the corresponding component computation. -/
lemma Vector.support_mapM_index
    {m : Type → Type} [Monad m] [LawfulMonad m]
    [MonadLiftT m SetM] [LawfulMonadLiftT m SetM]
    {α β : Type} {L : ℕ} (xs : Vector β L) (f : β → m α)
    {v : Vector α L} (hv : v ∈ support (xs.mapM f)) (i : Fin L) :
    v[i] ∈ support (f xs[i]) := by
  induction L with
  | zero => exact Fin.elim0 i
  | succ L ih =>
      obtain ⟨xs0, x, hxs⟩ := Vector.exists_push (xs := xs)
      obtain ⟨v0, y, hv0⟩ := Vector.exists_push (xs := v)
      subst hxs
      subst hv0
      have hpush : (xs0.push x).mapM f =
          (xs0.mapM f >>= (fun ys => f x >>= fun last => pure (ys.push last))) := by
        have hsingle : (#v[x]).mapM f = (fun last => #v[last]) <$> f x := by
          apply Vector.map_toArray_inj.mp
          simp
        rw [← Vector.append_singleton, Vector.mapM_append, hsingle]
        simp only [map_eq_bind_pure_comp, bind_assoc, Function.comp, pure_bind]
        rfl
      rw [hpush] at hv
      rw [mem_support_bind_iff] at hv
      obtain ⟨ys, hys, hv⟩ := hv
      rw [mem_support_bind_iff] at hv
      obtain ⟨last, hlast, hpush_eq⟩ := hv
      rw [mem_support_pure_iff] at hpush_eq
      have hparts := Vector.push_eq_push.mp hpush_eq.symm
      by_cases hi : (i : ℕ) < L
      · change (v0.push y)[(i : ℕ)] ∈ support (f ((xs0.push x)[(i : ℕ)]))
        rw [Vector.getElem_push_lt hi, Vector.getElem_push_lt hi]
        rw [← hparts.2]
        exact ih xs0 hys ⟨i, hi⟩
      · have hilast : (i : ℕ) = L := by omega
        have hi_eq : i = ⟨L, Nat.lt_succ_self L⟩ := Fin.ext hilast
        subst i
        simpa [← hparts.1] using hlast

/-- For a `Vector` of `Option` values, if `mapM id` yields `some w`, then each entry is
    `some` of the corresponding entry in `w`. -/
lemma Vector.mapM_id_some_index
    {α : Type} {L : ℕ} {v : Vector (Option α) L} {w : Vector α L}
    (h : v.mapM id = some w) (i : Fin L) : v[i] = some w[i] := by
  induction L with
  | zero => exact Fin.elim0 i
  | succ L ih =>
      obtain ⟨v0, a, hv⟩ := Vector.exists_push (xs := v)
      obtain ⟨w0, b, hw⟩ := Vector.exists_push (xs := w)
      subst hv
      subst hw
      have hdecomp : v0.mapM id = some w0 ∧ a = some b := by
        have hpush : (v0.push a).mapM id =
            (v0.mapM id >>= (fun x => a.map (fun last => x.push last))) := by
          have hsingle : (#v[a]).mapM id = a.map (fun last => #v[last]) := by
            apply Vector.map_toArray_inj.mp
            cases a <;> simp
          rw [← Vector.append_singleton, Vector.mapM_append, hsingle]
          cases a <;> simp [Vector.append_singleton]
        rw [hpush] at h
        cases hv0 : v0.mapM id with
        | none => simp [hv0] at h
        | some w0' =>
            cases ha : a with
            | none => simp [hv0, ha] at h
            | some aval =>
                simp only [hv0, ha, Option.map_some, Option.bind_eq_bind, Option.bind_some,
                  Option.some.injEq] at h
                have hp := Vector.push_eq_push.mp h
                exact ⟨congrArg some hp.2, congrArg some hp.1⟩
      by_cases hi : (i : ℕ) < L
      · change (v0.push a)[(i : ℕ)] = some ((w0.push b)[(i : ℕ)])
        rw [Vector.getElem_push_lt hi, Vector.getElem_push_lt hi]
        exact ih hdecomp.1 ⟨i, hi⟩
      · have hilast : (i : ℕ) = L := by omega
        have hi_eq : i = ⟨L, Nat.lt_succ_self L⟩ := Fin.ext hilast
        subst i
        simp [hdecomp.2]

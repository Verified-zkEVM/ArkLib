/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.InterleavedCode
public import ArkLib.ToMathlib.LinearAlgebra.Submodule.Union
public import Mathlib.Algebra.Module.Submodule.Union

/-!
# Row projection for interleaved module codes

A linear combination of rows preserves projected membership in a module code. For a family of
interleaved words, the row functionals preserving every projected membership form a submodule.
If at most `|F|` projected failures are given over a field `F`, one row functional detects all of
them. The first two facts hold over a semiring; the avoidance step uses a field.

## References

* [Jo, S., *Interleaving Stability for Mutual Correlated Agreement and Curve
  Decodability*][Jo26], Corollary 4.5.
-/

@[expose] public section

namespace Code

open LinearCode

section RowFunctionals

variable {ι F A κ ℓ : Type*} [Semiring F] [AddCommMonoid A] [Module F A] [Fintype κ]

/-- Projecting the `l`-combination of the rows of an interleaved word gives the `l`-combination
of the projected rows. -/
private lemma projectedWord_rowCombination_eq (w : ι → κ → A) (T : Finset ι) (l : κ → F) :
    projectedWord (fun i ↦ ∑ r, l r • w i r) T =
      ∑ r, l r • projectedWord (fun i ↦ w i r) T := by
  funext i
  simp [projectedWord]

/-- **Row combinations preserve projected membership.** If an interleaved word `w` projects into
`C ^⋈ κ` on `T`, then for every row functional `l : κ → F` the row combination
`i ↦ ∑ r, l r • w i r` projects into `C` on `T`.

Each row of `w` projects into `C` on `T` (`projectedCodeSubmod_moduleInterleavedCode_iff`), and
the projected code is a submodule. No hypothesis on `l` is needed; `l = 0` gives the zero word,
and an empty `κ` gives the empty sum. -/
theorem projectedWord_rowCombination_mem (C : ModuleCode ι F A) (w : ι → κ → A) (T : Finset ι)
    (l : κ → F) (h : projectedWord w T ∈ projectedCodeSubmod (C^⋈κ) T) :
    projectedWord (fun i ↦ ∑ r, l r • w i r) T ∈ projectedCodeSubmod C T := by
  have hrows := (projectedCodeSubmod_moduleInterleavedCode_iff F A κ ι C w T).mp h
  rw [projectedWord_rowCombination_eq]
  exact Submodule.sum_mem _ fun r _ ↦ Submodule.smul_mem _ _ (hrows r)

/-- The row functionals that keep a family of interleaved words inside `C` on `T`.

For a family `U : ℓ → ι → κ → A` and a coordinate set `T`, this is the set of `l : κ → F` such
that, for every `j`, the row combination `i ↦ ∑ r, l r • U j i r` projects into `C` on `T`
(`mem_goodRowFunctionals_iff`). It is a submodule because the row combination is linear in `l`.
It is all of `κ → F` exactly when every `U j` projects into `C ^⋈ κ` on `T`
(`goodRowFunctionals_eq_top_iff`). -/
def goodRowFunctionals (C : ModuleCode ι F A) (U : ℓ → ι → κ → A) (T : Finset ι) :
    Submodule F (κ → F) :=
  ⨅ j, (projectedCodeSubmod C T).comap
    (Fintype.linearCombination F fun r ↦ projectedWord (fun i ↦ U j i r) T)

/-- Membership in `goodRowFunctionals`: every row combination of every member of the family
projects into `C` on `T`. -/
theorem mem_goodRowFunctionals_iff (C : ModuleCode ι F A) (U : ℓ → ι → κ → A) (T : Finset ι)
    (l : κ → F) :
    l ∈ goodRowFunctionals C U T ↔
      ∀ j, projectedWord (fun i ↦ ∑ r, l r • U j i r) T ∈ projectedCodeSubmod C T := by
  simp only [goodRowFunctionals, Submodule.mem_iInf, Submodule.mem_comap,
    Fintype.linearCombination_apply, projectedWord_rowCombination_eq]

/-- Every row functional is good exactly when every member of the family projects into the
interleaved code `C ^⋈ κ` on `T`.

The reverse direction is `projectedWord_rowCombination_mem`. The forward direction evaluates at
the coordinate functional `Pi.single r 1`, whose row combination is the row `r`. Consequently, a
single member `U j` that fails to project into `C ^⋈ κ` makes the submodule proper, which is the
input to the avoidance step of `exists_rowFunctional_forall_notMem`. -/
theorem goodRowFunctionals_eq_top_iff (C : ModuleCode ι F A) (U : ℓ → ι → κ → A)
    (T : Finset ι) :
    goodRowFunctionals C U T = ⊤ ↔
      ∀ j, projectedWord (U j) T ∈ projectedCodeSubmod (C^⋈κ) T := by
  classical
  constructor
  · intro htop j
    refine (projectedCodeSubmod_moduleInterleavedCode_iff F A κ ι C (U j) T).mpr fun r ↦ ?_
    have hr : Pi.single r (1 : F) ∈ goodRowFunctionals C U T := htop ▸ Submodule.mem_top
    simp only [goodRowFunctionals, Submodule.mem_iInf, Submodule.mem_comap,
      Fintype.linearCombination_apply_single, one_smul] at hr
    exact hr j
  · intro h
    refine eq_top_iff.mpr fun l _ ↦ (mem_goodRowFunctionals_iff C U T l).mpr fun j ↦ ?_
    exact projectedWord_rowCombination_mem C (U j) T l (h j)

end RowFunctionals

section Avoidance

variable {ι F A κ ℓ : Type*} [Field F] [AddCommMonoid A] [Module F A]
  [Fintype κ]

/-- **One row functional detects every listed interleaved failure.** Let `s` be a finite set of
indices with at most `|F|` elements, and for each `x ∈ s` let some member `U j` of the family fail
to project into `C ^⋈ κ` on the coordinate set `T x`. Then a single row functional `l : κ → F`
has the following property: for every `x ∈ s`, some row combination `i ↦ ∑ r, l r • U j i r`
fails to project into `C` on `T x`.

The statement involves no generator or seed type;
`exists_forall_isMCA_of_forall_isMCA_interleaved` instantiates it with the bad seeds of a
generator.

For each `x ∈ s`, the failing functionals form the complement of `goodRowFunctionals C U (T x)`,
which is a proper submodule by `goodRowFunctionals_eq_top_iff`. The bound `hs` is what lets a
single `l` avoid all of them:
* for finite `F`, at most `|F|` proper submodules do not cover `κ → F`
  (`Submodule.exists_forall_notMem_of_card_le`). The bound is sharp, since the `|F| + 1` lines
  through the origin cover `F²`;
* for infinite `F`, `ENat.card F = ⊤` and `hs` always holds; finitely many proper submodules do
  not cover `κ → F` (`Submodule.exists_forall_notMem_of_forall_ne_top`). This Mathlib theorem
  requires a field in the pinned version, so the unified finite/infinite statement does too.

Edge cases: for empty `s` every `l` works. For empty `κ`, every word projects into `C ^⋈ κ`,
so `hbad` forces `s` to be empty. -/
theorem exists_rowFunctional_forall_notMem (C : ModuleCode ι F A) (U : ℓ → ι → κ → A)
    {σ : Type*} (s : Finset σ) (T : σ → Finset ι) (hs : (s.card : ℕ∞) ≤ ENat.card F)
    (hbad : ∀ x ∈ s, ∃ j, projectedWord (U j) (T x) ∉ projectedCodeSubmod (C^⋈κ) (T x)) :
    ∃ l : κ → F, ∀ x ∈ s, ∃ j,
      projectedWord (fun i ↦ ∑ r, l r • U j i r) (T x) ∉ projectedCodeSubmod C (T x) := by
  have hp : ∀ x ∈ s, goodRowFunctionals C U (T x) ≠ ⊤ := fun x hx htop ↦ by
    obtain ⟨j, hj⟩ := hbad x hx
    exact hj ((goodRowFunctionals_eq_top_iff C U (T x)).mp htop j)
  obtain ⟨l, hl⟩ : ∃ l : κ → F, ∀ x ∈ s, l ∉ goodRowFunctionals C U (T x) := by
    rcases finite_or_infinite F with hF | hF
    · refine Submodule.exists_forall_notMem_of_card_le s _ hp ?_
      rwa [ENat.card_eq_coe_natCard F, Nat.cast_le] at hs
    · obtain ⟨l, hl⟩ := Submodule.exists_forall_notMem_of_forall_ne_top
        (fun x : s ↦ goodRowFunctionals C U (T x)) fun x ↦ hp x x.2
      exact ⟨l, fun x hx ↦ hl ⟨x, hx⟩⟩
  exact ⟨l, fun x hx ↦ not_forall.mp fun h ↦ hl x hx ((mem_goodRowFunctionals_iff C U _ l).mpr h)⟩

end Avoidance

end Code

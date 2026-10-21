/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Julian Sutherland, Ilia Vlasov, Aristotle (Harmonic)
-/
module

public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import Mathlib.Algebra.Group.Fin.Basic
public import Mathlib.Algebra.Group.TypeTags.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Tactic.Cases
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Field

public import ArkLib.Data.Domain.CosetFftDomain.Mem
public import ArkLib.Data.Domain.FftDomain.Mem

/-!
# ArkLib.Data.Domain.CosetFftDomain.ToList

Definitions and results for this component of ArkLib.
-/

@[expose] public section

namespace Domain

variable {ι : Type} [Fintype ι] [AddCommGroup ι]
variable {F : Type} [Field F] [DecidableEq F]

namespace CosetFftDomainClass

variable {D : Type} [FunLike D ι F] [CosetFftDomainClass D ι F]

noncomputable def toList (ω : D) : List (toFinset ω) :=
  Finset.toListWithProof <| toFinset ω

lemma toList_eq_finset_toList {ω : D} :
    (toList ω).map (fun x ↦ x.1) = (toFinset ω).toList := by
  exact Finset.toListWithProof_eq_toList

end CosetFftDomainClass

namespace CosetFftDomain

/-- Convert a coset FFT domain into a list of all its members
  with proofs the members belong to the FFT domain.

  Computable for FFT domains indexed by `Fin m`, by enumerating via `List.finRange m`. -/
def toList {m : ℕ} [NeZero m] (ω : CosetFftDomain (Fin m) F) : List (ω.toFinset) :=
  (List.finRange m).map fun i ↦ ⟨ω i, by simp⟩

end CosetFftDomain

namespace FftDomain

/-- Convert a FFT domain into a list of all its members
  with proofs the members belong to the FFT domain.

  Computable for FFT domains indexed by `Fin m`, by enumerating via `List.finRange m`. -/
def toList {m : ℕ} [NeZero m] (ω : FftDomain (Fin m) F) : List (ω.toFinset) :=
  (List.finRange m).map fun i ↦ ⟨ω i, by simp⟩
end FftDomain

end Domain

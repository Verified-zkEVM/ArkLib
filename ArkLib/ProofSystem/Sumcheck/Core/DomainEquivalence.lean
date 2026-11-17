/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.ProofSystem.Sumcheck.Core.Domain
public import ArkLib.ProofSystem.Sumcheck.Spec.SingleRound

/-! # Indexed-domain compatibility with the injective Sumcheck specification -/

@[expose] public section

namespace Sumcheck.Core
open Polynomial MvPolynomial Finset
variable {R : Type} [CommSemiring R] {d n deg : ℕ}

/-- For an injective domain the indexed honest polynomial is Spec's projected polynomial. -/
theorem projectedRoundPolynomial_embedding (D : Fin d ↪ R) (i : Fin n)
    (c : Fin i.castSucc → R) (p : R⦃≤ deg⦄[X Fin n]) :
    projectedRoundPolynomial (⇑D) i c p =
      Spec.SingleRound.projectedRoundPolynomial R n deg D i c p := by
  apply Subtype.ext
  exact sum_domain_embedding D _ (fun x =>
    p.val.evalExcept i (Spec.SingleRound.roundSuffix R n i c x))

/-- The indexed relation agrees with the finite-set relation for an injective domain. -/
theorem indexedRelation_embedding (D : Fin d ↪ R) (i : Fin (n + 1))
    (stmt : Spec.StatementRound R n i) (p : R⦃≤ deg⦄[X Fin n]) :
    indexedRelation (⇑D) i ⟨stmt.target, stmt.challenges⟩ p ↔
      ((stmt, fun _ => p), ()) ∈ Spec.relationRound R n deg D i := by
  unfold indexedRelation roundSum
  rw [sum_domain_embedding D _ (fun x =>
    p.val.eval (Fin.append stmt.challenges x ∘ Fin.cast (by have := i.isLt; omega)))]
  rfl


end Sumcheck.Core

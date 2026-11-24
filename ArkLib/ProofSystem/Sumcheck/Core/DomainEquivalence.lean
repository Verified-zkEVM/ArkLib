/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.ProofSystem.Sumcheck.Core.Domain
public import ArkLib.ProofSystem.Sumcheck.Spec.SingleRound

/-! # Indexed-domain compatibility with the injective Sumcheck specification

For an injective domain `D : Fin d ↪ R`, this file relates the indexed definitions of `Domain` to
the finite-set definitions of `Spec.SingleRound`. The scope is the honest projected polynomials
(`projectedRoundPolynomial_embedding`) and the remaining-sum relations
(`indexedRelation_embedding`). It does not compare verifiers. A closed-verdict bridge between
`indexedVerifier` and the compatibility `verifier` would compare their decisions after
interpreting the messages, and a security transfer would also need the matching relations,
output maps and challenge draws. The interaction-layer soundness proof in `Soundness` does not
import this file.
-/

@[expose] public section

namespace Sumcheck.Core
open Polynomial MvPolynomial Finset
/-- The interaction layer's suffix assignment `roundSuffix` is the frozen legacy
`Spec.SingleRound.roundSuffix`, by definition. -/
theorem roundSuffix_eq_spec {R : Type} [CommSemiring R] {n : ℕ} (i : Fin n)
    (c : Fin i.castSucc → R) (x : Fin (n - 1 - i) → R) :
    roundSuffix i c x = Spec.SingleRound.roundSuffix R n i c x :=
  rfl

variable {R : Type} [CommSemiring R] {d n deg : ℕ}

/-- For an injective domain the indexed honest polynomial is Spec's projected polynomial. -/
theorem projectedRoundPolynomial_embedding (D : Fin d ↪ R) (i : Fin n)
    (c : Fin i.castSucc → R) (p : R⦃≤ deg⦄[X Fin n]) :
    projectedRoundPolynomial (⇑D) i c p =
      Spec.SingleRound.projectedRoundPolynomial R n deg D i c p := by
  apply Subtype.ext
  exact sum_domain_embedding D _ (fun x =>
    p.val.evalExcept i (roundSuffix i c x))

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

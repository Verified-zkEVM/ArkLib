/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tobias Rothmann
-/
import ArkLib.OracleReduction.Composition.Sequential.General

/-!
  # Purity of composed verifiers

  A verifier is `Verifier.IsPure` when its `verify` is a deterministic (`pure`) function of the
  statement and transcript. This is exactly the deterministic-left hypothesis `hV₁` of the
  CWSS / tree-soundness binary append (`Verifier.append_treeSpecialSound`,
  `Verifier.append_coordinateWiseSpecialSound`), so propagating `IsPure` through composition lets
  an `n`-ary CWSS composition discharge that hypothesis from per-factor purity.

  We show that the identity verifier is pure (`instIsPureId`), and that purity is preserved by
  binary `append` (`IsPure.append`) and `n`-ary `seqCompose` (`IsPure.seqCompose`).
-/

open OracleComp OracleSpec ProtocolSpec

namespace Verifier

variable {ι : Type} {oSpec : OracleSpec ι}

/-- The identity verifier is pure: `verify = fun stmt _ => pure stmt`. -/
instance instIsPureId {Statement : Type} :
    (Verifier.id (oSpec := oSpec) (Statement := Statement)).IsPure :=
  ⟨fun stmt _ => stmt, fun _ _ => rfl⟩

variable {Stmt₁ Stmt₂ Stmt₃ : Type} {m k : ℕ}
  {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec k}

/-- Purity is preserved by binary sequential composition of verifiers: the composed `verify` is the
  composition of the two deterministic outputs. -/
theorem IsPure.append (V₁ : Verifier oSpec Stmt₁ Stmt₂ pSpec₁)
    (V₂ : Verifier oSpec Stmt₂ Stmt₃ pSpec₂) (h₁ : V₁.IsPure) (h₂ : V₂.IsPure) :
    (V₁.append V₂).IsPure := by
  obtain ⟨f₁, hf₁⟩ := h₁.is_pure
  obtain ⟨f₂, hf₂⟩ := h₂.is_pure
  refine ⟨fun stmt tr => f₂ (f₁ stmt tr.fst) tr.snd, fun stmt tr => ?_⟩
  simp only [Verifier.append, hf₁, hf₂, pure_bind, bind_pure]

/-- Purity is preserved by `n`-ary sequential composition of verifiers. The base case is the
  identity verifier (`Verifier.seqCompose` reduces to `Verifier.id` at `m = 0`); the step case is
  `IsPure.append` of the head with the recursively-composed tail. -/
theorem IsPure.seqCompose :
    {m : ℕ} → (Stmt : Fin (m + 1) → Type) → {n : Fin m → ℕ} →
      {pSpec : ∀ i, ProtocolSpec (n i)} →
      (V : (i : Fin m) → Verifier oSpec (Stmt i.castSucc) (Stmt i.succ) (pSpec i)) →
      (hV : ∀ i, (V i).IsPure) → (Verifier.seqCompose Stmt V).IsPure
  | 0, _, _, _, _, _ => ⟨fun stmt _ => stmt, fun _ _ => rfl⟩
  | _ + 1, Stmt, _, _, V, hV =>
      IsPure.append (V 0) _ (hV 0)
        (IsPure.seqCompose (Stmt ∘ Fin.succ) (fun i => V (Fin.succ i)) (fun i => hV (Fin.succ i)))

end Verifier

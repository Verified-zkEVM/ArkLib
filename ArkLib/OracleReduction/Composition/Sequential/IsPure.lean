/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tobias Rothmann
-/
module

public import ArkLib.OracleReduction.Composition.Sequential.General

/-!
# Purity under sequential composition

Identity, binary, and finite sequential composition preserve deterministic verifier outputs and
pure prover outputs. `Verifier.PureForm.append` also composes explicit deterministic verdict data.
The binary prover-output result is defined beside the append operation in `Append/Basic.lean`.
-/

@[expose] public section

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
  simp only [Verifier.append, hf₁, hf₂, pure_bind]

/-- Compose deterministic verifier data by passing the first verdict to the second verifier. -/
def PureForm.append {V₁ : Verifier oSpec Stmt₁ Stmt₂ pSpec₁}
    {V₂ : Verifier oSpec Stmt₂ Stmt₃ pSpec₂} (P₁ : V₁.PureForm) (P₂ : V₂.PureForm) :
    (V₁.append V₂).PureForm where
  verify := fun stmt tr => P₂.verify (P₁.verify stmt tr.fst) tr.snd
  verify_eq := fun stmt tr => by
    simp only [Verifier.append, P₁.verify_eq, P₂.verify_eq, pure_bind]

/-- Finite sequential composition preserves deterministic verifier outputs. -/
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

namespace Prover

variable {ι : Type} {oSpec : OracleSpec ι}

/-- The identity prover has pure output: its `output` field is literally `pure`. -/
instance instOutputIsPureId {Statement Witness : Type} :
    (Prover.id (oSpec := oSpec) (Statement := Statement) (Witness := Witness)).OutputIsPure :=
  ⟨_root_.id, fun _ => rfl⟩

/-- Finite sequential composition preserves pure prover outputs. -/
theorem OutputIsPure.seqCompose :
    {m : ℕ} → (Stmt : Fin (m + 1) → Type) → (Wit : Fin (m + 1) → Type) → {n : Fin m → ℕ} →
      {pSpec : ∀ i, ProtocolSpec (n i)} →
      (P : (i : Fin m) →
        Prover oSpec (Stmt i.castSucc) (Wit i.castSucc) (Stmt i.succ) (Wit i.succ) (pSpec i)) →
      (hP : ∀ i, (P i).OutputIsPure) → (Prover.seqCompose Stmt Wit P).OutputIsPure
  | 0, _, _, _, _, _, _ => ⟨_root_.id, fun _ => rfl⟩
  | _ + 1, Stmt, Wit, _, _, P, hP =>
      OutputIsPure.append (P 0) _ (hP 0)
        (OutputIsPure.seqCompose (Stmt ∘ Fin.succ) (Wit ∘ Fin.succ)
          (fun i => P (Fin.succ i)) (fun i => hP (Fin.succ i)))

end Prover

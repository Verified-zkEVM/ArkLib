/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Commitments.Functional.KZG.AGM.Adversary
public import VCVio.CryptoFoundations.GroupModel.PairingExplained

/-!
# Generic KZG adversaries

This interface runs a Type 3 handle adversary in the existing KZG binding games. Private coins
are its only game interaction; encodings reveal only unit.

References: [KZG10TR]; Shoup, EUROCRYPT 1997; Maurer, IMA 2005;
Fuchsbauer–Kiltz–Loss, *The Algebraic Group Model and its Applications*, CRYPTO 2018.
-/

@[expose] public section

open OracleComp OracleSpec GroupModel GroupModel.Interaction

namespace KZG.Generic

instance sourceAddCommMonoid {G₁ G₂ : Type} [AddCommGroup G₁] [AddCommGroup G₂]
    (b : Bool) : AddCommMonoid (AGM.Group G₁ G₂ b) where
  toAddMonoid := inferInstance
  add_comm := by cases b <;> exact add_comm

instance sourceModule {F G₁ G₂ : Type} [Semiring F] [AddCommGroup G₁] [Module F G₁]
    [AddCommGroup G₂] [Module F G₂] (b : Bool) : Module F (AGM.Group G₁ G₂ b) where
  smul := (· • ·)
  one_smul := by cases b <;> exact one_smul F
  mul_smul := by cases b <;> exact mul_smul
  smul_zero := by cases b <;> exact smul_zero
  smul_add := by cases b <;> exact smul_add
  add_smul := by cases b <;> exact add_smul
  zero_smul := by cases b <;> exact zero_smul F

instance sourceDecidableEq {G₁ G₂ : Type} [DecidableEq G₁] [DecidableEq G₂] :
    ∀ b, DecidableEq (AGM.Group G₁ G₂ b)
  | false => inferInstanceAs (DecidableEq G₁)
  | true => inferInstanceAs (DecidableEq G₂)

/-- A KZG handle program has no game requests. -/
abbrev Adversary (F D : Type) :=
  HandleAdversary F pairingSig (fun _ => Unit) Unit Empty (fun _ => Unit) D

/-- The handle interface, including private uniform coins and trivial encodings. -/
abbrev adversarySpec (F : Type) := Pairing.HandleSpec F Empty (fun _ => Unit)

/-- Initial handles index the committer and verifier keys, with no target inputs. -/
def input (n : ℕ) : Message Unit (fun _ : PSort => Handle) :=
  ⟨(), fun | .g₁ => List.range (n + 1) | .g₂ => List.range 2 | .gₜ => []⟩

/-- An empty game interface has no replies to implement. -/
def emptyOracle {G : PSort → Type} :
    QueryImpl (plainSpec G Empty (fun _ => Unit)) ProbComp := fun q => q.data.elim

variable {F G₁ G₂ Gₜ D : Type} [Field F]
  [AddCommGroup G₁] [Module F G₁] [DecidableEq G₁]
  [AddCommGroup G₂] [Module F G₂] [DecidableEq G₂]
  [AddCommGroup Gₜ] [Module F Gₜ] [DecidableEq Gₜ] {n : ℕ}

/-- Run the handle adversary on the real KZG keys and decode its source outputs. -/
def Adversary.run (A : Adversary F D) (e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ)
    (ck : Fin (n + 1) → G₁) (vk : Fin 2 → G₂) :
    ProbComp (Message D (AGM.Group G₁ G₂)) :=
  (fun z => Pairing.sourceValue (lookupMessage z.2 z.1)) <$>
    HandleAdversary.run A (pairingReal e) (fun _ _ => ())
      (QueryImpl.ofLift unifSpec ProbComp) emptyOracle
      (Pairing.pairingMessage (AGM.initialInput ck vk))

/-- Forget generic handles to obtain the existing evaluation-binding adversary. -/
def Adversary.toEvalBindingAdversary (A : Adversary F (F × F × F))
    (e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ) : EvalBindingAdversary F G₁ G₂ n :=
  fun ck vk => (fun out => ((out.groups false)[0]?.getD 0, out.data.1, out.data.2.1,
    (out.groups false)[1]?.getD 0, out.data.2.2, (out.groups false)[2]?.getD 0)) <$>
      A.run e ck vk

/-- Forget generic handles to obtain the existing function-binding adversary. -/
def Adversary.toFunctionBindingAdversary (A : Adversary F (List (F × F)))
    (e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ) : FunctionBindingAdversary F G₁ G₂ n :=
  fun ck vk => (fun out => ((out.groups false)[0]?.getD 0,
    List.ofFn fun i : Fin out.data.length =>
      (out.data[i].1, out.data[i].2, (out.groups false)[i.val + 1]?.getD 0))) <$>
        A.run e ck vk

end KZG.Generic

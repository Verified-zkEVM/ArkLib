/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tobias Rothmann
-/
import ArkLib.Commitments.Ordinary.Ajtai.Simple.Correctness
import ArkLib.Data.Lattices.CyclotomicRing.NormBounds

/-!
# Binding Security of the Simple Ajtai Commitment

Binding of the simple non-hiding Ajtai [Ajt96] commitment reduces to Module-SIS over `Rq Φ`:
a binding adversary that opens one commitment to two distinct short messages `s₁ ≠ s₂`
yields the Module-SIS witness `s₁ - s₂` (nonzero, short, in the kernel of `A`).

The headline result `bindingAdvantage_le_moduleSIS` is stated over `ZMod q` with a *single*
norm — the centered squared-`ℓ₂` norm `vecL2NormSq` — using shortness bound `boundSq` for
the commitment and `subL2NormSqBound boundSq = 4·boundSq` for Module-SIS; the norm-growth
fact `sub_l2NormSq_le` discharges the subtraction closure internally. A general version over
an abstract shortness predicate with an explicit closure hypothesis is kept as
`bindingAdvantage_le_moduleSIS_of_shortClosure`.

## References

* [Ajtai, M., *Generating Hard Instances of Lattice Problems*][Ajt96]
-/

open OracleComp CommitmentScheme CompPoly ArkLib.Lattices ArkLib.Lattices.CyclotomicModulus

namespace ArkLib.Lattices.Ajtai.Simple

variable {R : Type} [Field R] [BEq R] [LawfulBEq R] (Φ : CyclotomicModulus R) [IsCyclotomic Φ]

/-- Boolean monotonicity of `pure` outcome probability. -/
private theorem probOutput_pure_bool_le (b₁ b₂ : Bool) (h : b₁ = true → b₂ = true) :
    Pr[= true | (pure b₁ : ProbComp Bool)] ≤ Pr[= true | (pure b₂ : ProbComp Bool)] := by
  cases b₁ <;> cases b₂ <;> simp_all

/-- A binding adversary against the simple Ajtai commitment yields a Module-SIS
adversary: the extracted witness is the difference of the two opened messages. -/
def bindingAdvToModuleSIS {rows cols : Nat}
    [SampleableType (PublicParams Φ rows cols)]
    [DecidableEq (PolyVec (Rq Φ) cols)] [DecidableEq (PolyVec (Rq Φ) rows)]
    (isShortSIS : ModuleSIS.Solution Φ cols → Bool)
    (adv : BindingAdv (PublicParams Φ rows cols) (Message Φ cols) (Commitment Φ rows) Opening) :
    ModuleSIS.Adversary Φ rows cols isShortSIS :=
  fun A => do
    let (_c, s₁, _o₁, s₂, _o₂) ← adv A
    pure (s₁ - s₂)

/-- Binding reduces to Module-SIS for any commitment/Module-SIS shortness predicates closed
under differences. -/
theorem bindingAdvantage_le_moduleSIS_of_shortClosure {rows cols : Nat}
    [SampleableType (PublicParams Φ rows cols)]
    [DecidableEq (Message Φ cols)] [DecidableEq (Commitment Φ rows)]
    (isShort : Message Φ cols → Bool) (isShortSIS : ModuleSIS.Solution Φ cols → Bool)
    (hsub : ∀ s₁ s₂ : Message Φ cols, isShort s₁ = true → isShort s₂ = true →
      isShortSIS (s₁ - s₂) = true)
    (adv : BindingAdv (PublicParams Φ rows cols) (Message Φ cols) (Commitment Φ rows) Opening) :
    bindingAdvantage (commitmentScheme Φ rows cols isShort) adv ≤
      ModuleSIS.advantage Φ rows cols isShortSIS (bindingAdvToModuleSIS Φ isShortSIS adv) := by
  unfold bindingAdvantage CommitmentScheme.bindingExp ModuleSIS.advantage
    SIS.advantage SIS.experiment ModuleSIS.problem bindingAdvToModuleSIS
    commitmentScheme ModuleSIS.relation
  simp only [bind_pure_comp, Functor.map_map]
  refine probOutput_bind_mono fun A _ => ?_
  refine probOutput_bind_mono fun ⟨c, s₁, o₁, s₂, o₂⟩ _ => ?_
  refine probOutput_pure_bool_le _ _ (fun hwin => ?_)
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hwin ⊢
  obtain ⟨⟨hne, hshort₁, hverify₁⟩, hshort₂, hverify₂⟩ := hwin
  have hc₁ : commit Φ A s₁ = c := (verify_eq_true_iff Φ A s₁ c o₁).1 hverify₁
  have hc₂ : commit Φ A s₂ = c := (verify_eq_true_iff Φ A s₂ c o₂).1 hverify₂
  have hmat : A *ᵥ s₁ = A *ᵥ s₂ := by simpa [commit] using hc₁.trans hc₂.symm
  refine ⟨⟨sub_ne_zero.mpr hne, hsub s₁ s₂ hshort₁ hshort₂⟩, ?_⟩
  rw [matVecMul_sub, hmat, sub_self]

end ArkLib.Lattices.Ajtai.Simple

/-! ## Headline binding bound with a single centered `ℓ₂²` norm (over `ZMod q`) -/

namespace ArkLib.Lattices.Ajtai.Simple

open ArkLib.Lattices.CyclotomicModulus

variable {q : ℕ} [Fact (Nat.Prime q)] [BEq (ZMod q)] [LawfulBEq (ZMod q)]
  (Φ : CyclotomicModulus (ZMod q)) [IsCyclotomic Φ]

/-- **Binding of the simple Ajtai commitment reduces to Module-SIS**, using a single norm:
a commitment accepting messages with centered squared-`ℓ₂` norm `≤ boundSq` has binding
advantage bounded by the Module-SIS advantage with norm bound `subL2NormSqBound boundSq`. The
subtraction closure is discharged by `sub_l2NormSq_le`. -/
theorem bindingAdvantage_le_moduleSIS {rows cols : Nat}
    [SampleableType (PublicParams Φ rows cols)]
    [DecidableEq (Message Φ cols)] [DecidableEq (Commitment Φ rows)] (boundSq : ℕ)
    (adv : BindingAdv (PublicParams Φ rows cols) (Message Φ cols) (Commitment Φ rows) Opening) :
    bindingAdvantage
        (commitmentScheme Φ rows cols (fun s => decide (‖s‖₂² ≤ boundSq))) adv ≤
      ModuleSIS.advantage Φ rows cols
        (fun z => decide (‖z‖₂² ≤ subL2NormSqBound boundSq))
        (bindingAdvToModuleSIS Φ
          (fun z => decide (‖z‖₂² ≤ subL2NormSqBound boundSq)) adv) :=
  bindingAdvantage_le_moduleSIS_of_shortClosure Φ _ _
    (fun s₁ s₂ h₁ h₂ => by
      simp only [decide_eq_true_eq] at h₁ h₂ ⊢
      exact sub_l2NormSq_le Φ s₁ s₂ h₁ h₂)
    adv

end ArkLib.Lattices.Ajtai.Simple

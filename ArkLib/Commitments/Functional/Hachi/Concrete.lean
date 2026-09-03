/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pablo Martín Vinuelas
-/
import ArkLib.Commitments.Functional.Hachi.Correctness

/-!
# Nonrecursive Hachi at a concrete commitment

`hachiNonrecursive` (`Correctness.lean`) is parameterized by an *abstract* `LiftCom`: the lift's
commitment space `K.TCom` and map `K.com` are opaque, which is right for the correctness proof —
correctness holds for any commitment — but leaves the scheme with nothing an implementation could
compute. This file instantiates at `hachiLiftCom` (`RingSwitch/Reduction.lean`), the Ajtai product
`D · (z ‖ ρ)`. Both declarations here are applications of the general theorems.

## Main definitions

* `hachiNonrecursiveConcrete` — `hachiNonrecursive` at `K := hachiLiftCom …`. A plain `def`: the
  whole honest run is computable (see `scripts/HachiRuntime.lean` for an evaluated accepting
  run).
* `hachiNonrecursiveConcrete_perfectCorrectness` — perfect correctness, as a corollary of
  `hachiNonrecursive_perfectCorrectness`.

## References

* [Nguyen, N. K., O'Rourke, G., and Zhang, J., *Hachi: Efficient Lattice-Based Multilinear
    Polynomial Commitments over Extension Fields*][NOZ26]
-/

namespace ArkLib.Lattices.Ajtai.InnerOuter

open CompPoly ArkLib.Lattices ArkLib.Lattices.CyclotomicModulus
open RingSwitching RingSwitching.Lift
open OracleComp OracleSpec ProtocolSpec CoordinateWise CoordinateWise.ScalarRound

section Concrete

variable {q : ℕ} [NeZero q] [Fact (Nat.Prime q)] [BEq (ZMod q)] [LawfulBEq (ZMod q)] {α : ℕ}
variable {innerRows outerRows dRows m r M m₁ : Nat} {ω : ℕ}
variable {F : Type} [Field F] [DecidableEq F] [BEq F] [LawfulBEq F] [SampleableType F]
variable {σ : Type}

/-! `τ` (the folded witness's digit count) and `zBound` (the honest `ℓ∞` bound on `z` it is sized
for) are independent parameters here, exactly as in `Correctness.lean`: the message and inner
decompositions stay full-width at `δ = ⌈log_b q⌉`, while `τ` comes from the honest shortness bound.
`μ₀` and hence the lift key's width `μ₀ + n₀·δ_{bZero}` depend on `τ`. -/

variable {τ zBound : Nat}

local notation "δ" P => Nat.clog (HonestRangeParams.b P) q
local notation "μ₀" P =>
  rlinCols innerRows (Nat.clog (HonestRangeParams.b P) q) (Nat.clog (HonestRangeParams.b P) q)
    τ m r
local notation "n₀" => rlinRows innerRows outerRows dRows

/-- The concrete lift commitment of the nonrecursive chain: `hachiLiftCom` at the chain's own
shortness parameters (`bound = P.γ`, digit base `bDig = P.bZero`). The Ajtai key is now
`μ₀ + n₀·δ` columns wide, `δ = clog_{bZero} q`, because the quotient block committed is its base-
`bZero` **digits** ([NOZ26] §4.3) rather than the raw rows — which is what makes a member of
`LiftCom.Collision` a short kernel vector of `D`. Named so the scheme and its correctness
corollary below cannot drift apart. -/
def nonrecursiveLiftCom (P : HonestRangeParams q)
    (D : Simple.PublicParams 𝓜(q, α) dRows ((μ₀ P) + n₀ * rhoDigitCount q P.bZero)) :
    LiftCom (LiftedWitness 𝓜(q, α) (μ₀ P) n₀) (liftShort 𝓜(q, α) P.γ P.bZero) :=
  hachiLiftCom 𝓜(q, α) P.γ P.bZero D

/-- `DecidableEq` on the concrete commitment space, derived from `DecidableEq (Rq Φ)` — no
`Classical.dec`. Stated as an instance so the `[DecidableEq K.TCom]` arguments of the chain are
discharged by synthesis at this instantiation. -/
instance instDecidableEqNonrecursiveLiftComTCom (P : HonestRangeParams q)
    (D : Simple.PublicParams 𝓜(q, α) dRows ((μ₀ P) + n₀ * rhoDigitCount q P.bZero)) :
    DecidableEq (nonrecursiveLiftCom (α := α) P D).TCom :=
  inferInstanceAs (DecidableEq (CarrierCom 𝓜(q, α) dRows))

/-- **Nonrecursive Hachi at the concrete commitment.** `hachiNonrecursive` applied to
`nonrecursiveLiftCom`; the type is left to inference precisely because it is the general
scheme's type with `K.TCom` replaced by `CarrierCom 𝓜(q, α) dRows`, and restating that whole
composed `pSpec` here would only invite it to drift.

A plain `def`, so every field — `keygen`, the committer, and the full composed opening —
is executable. -/
def hachiNonrecursiveConcrete (P : HonestRangeParams q)
    [SampleableType (Simple.PublicParams 𝓜(q, α) innerRows ((2 ^ m) * Nat.clog P.b q))]
    [SampleableType
      (Simple.PublicParams 𝓜(q, α) outerRows ((2 ^ r) * (innerRows * Nat.clog P.b q)))]
    [SampleableType (Simple.PublicParams 𝓜(q, α) dRows ((2 ^ r) * Nat.clog P.b q))]
    (D : Simple.PublicParams 𝓜(q, α) dRows ((μ₀ P) + n₀ * rhoDigitCount q P.bZero))
    (hcap : zBound ≤ balancedDigitCapacity P.b τ)
    (hd : 0 < 𝓜(q, α).φ.natDegree) (hbZero : 0 < P.bZero) (φF : ZMod q →+* F) :=
  hachiNonrecursive (F := F) (ω := ω) (M := M) (m₁ := m₁) P hcap
    (nonrecursiveLiftCom (α := α) P D) hd hbZero φF

set_option linter.unusedSectionVars false in
omit [DecidableEq F] in
/-- **Perfect correctness of nonrecursive Hachi at the concrete commitment** — the corollary of
`hachiNonrecursive_perfectCorrectness` at `K := nonrecursiveLiftCom P D`. Same hypotheses, same
proof: correctness never inspects the commitment beyond its being a function, so instantiating the
general theorem is all that is needed. -/
theorem hachiNonrecursiveConcrete_perfectCorrectness
    [∀ i, SampleableType
      ((CoordinateWise.SingleRound.pSpec
        (CarrierCom 𝓜(q, α) dRows) (ShortChallenge 𝓜(q, α) ω) r).Challenge i)]
    (P : HonestRangeParams q)
    [SampleableType (Simple.PublicParams 𝓜(q, α) innerRows ((2 ^ m) * Nat.clog P.b q))]
    [SampleableType
      (Simple.PublicParams 𝓜(q, α) outerRows ((2 ^ r) * (innerRows * Nat.clog P.b q)))]
    [SampleableType (Simple.PublicParams 𝓜(q, α) dRows ((2 ^ r) * Nat.clog P.b q))]
    (init : ProbComp σ) (impl : QueryImpl unifSpec (StateT σ ProbComp))
    (hInit : NeverFail init)
    (hKeygen : ∀ s : σ, NeverFail ((simulateQ impl
      (keygen (q := q) (α := α) (innerRows := innerRows) (outerRows := outerRows)
        (dRows := dRows) (m := m) (r := r) P.b)).run s))
    (hclog : 0 < Nat.clog P.b q) (hd : 0 < 𝓜(q, α).φ.natDegree) (hbZero : 0 < P.bZero)
    (D : Simple.PublicParams 𝓜(q, α) dRows ((μ₀ P) + n₀ * rhoDigitCount q P.bZero))
    (hcap : zBound ≤ balancedDigitCapacity P.b τ)
    (hzb : 2 ^ r * ω * (P.b / 2) ≤ zBound) (hτ : 0 < τ)
    (φF : ZMod q →+* F)
    (hμn : ((μ₀ P) + n₀ * rhoDigitCount q P.bZero) * 𝓜(q, α).φ.natDegree ≤ 2 ^ (M + 1))
    (hZeroγ : P.bZero - 1 ≤ P.γ) :
    Commitment.perfectCorrectness init impl
      (hachiNonrecursiveConcrete (F := F) (ω := ω) (M := M) (m₁ := m₁)
        P D hcap hd hbZero φF) :=
  hachiNonrecursive_perfectCorrectness (F := F) (ω := ω) (M := M) (m₁ := m₁)
    P init impl hInit hKeygen hcap hzb hτ hclog hd hbZero
    (nonrecursiveLiftCom (α := α) P D) φF hμn hZeroγ

end Concrete

end ArkLib.Lattices.Ajtai.InnerOuter

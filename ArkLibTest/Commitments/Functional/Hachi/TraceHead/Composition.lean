/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/
import ArkLib.Commitments.Functional.Hachi.TraceHead.Basic
import ArkLib.Commitments.Functional.Hachi.Composition

/-!
# The trace head composes in front of Hachi's evaluation step

The trace head's output relation is `relPolyEval`, the input relation of the Figure 3 bridge, so
its guarded package composes with `bridgePackage ▷ quadEvalPackage` with no adapter. The composite
starts at the trace head's scalar relation and ends at the evaluation step's output relation.
-/

open CompPoly ArkLib.Lattices.CyclotomicModulus
open OracleComp OracleSpec ProtocolSpec CoordinateWise
open ArkLib.Lattices.Ajtai.InnerOuter WeakBinding

namespace HachiTraceHeadCompositionTest

variable {q : ℕ} [NeZero q] [Fact (Nat.Prime q)] [BEq (ZMod q)] [LawfulBEq (ZMod q)] {α κ : ℕ}
variable {innerRows messageDigits outerRows innerDigits dRows zDigits m r : Nat}
variable {ι : Type} {oSpec : OracleSpec ι} {σ : Type}

/-- The trace head, then the polynomial-to-quadratic bridge, then the Figure 3 evaluation step. -/
noncomputable def composed (init : ProbComp σ)
    (impl : QueryImpl oSpec (StateT σ ProbComp)) (hq5 : q % 8 = 5) {b ω γ : ℕ}
    (hκ : (2 * ω) ^ 2 < q) (hτ : 0 < zDigits)
    (hk : 2 * 2 ^ κ ∣ 2 ^ α) (h2 : (2 : ZMod q) ≠ 0)
    (pp : ArkLib.Lattices.Hachi.PublicParamsD 𝓜(q, α) innerRows (2 ^ m) messageDigits
      outerRows (2 ^ r) innerDigits dRows) :=
  ArkLib.Lattices.Hachi.TraceHead.traceHeadPackage (oSpec := oSpec) α κ hk h2 init impl pp
      (b : ZMod q)
      (quadEvalBetaSq γ b zDigits ((𝓜(q, α)).φ.natDegree) m messageDigits) γ (2 * ω) ▷
    (bridgePackage (oSpec := oSpec) 𝓜(q, α) init impl pp (b : ZMod q)
        (quadEvalBetaSq γ b zDigits ((𝓜(q, α)).φ.natDegree) m messageDigits) γ (2 * ω) ▷
      quadEvalPackage init impl hq5 hκ hτ pp)

/-- The composite starts at the trace head's scalar relation and ends at the evaluation step's
output relation. -/
theorem composed_endpoints (init : ProbComp σ)
    (impl : QueryImpl oSpec (StateT σ ProbComp)) (hq5 : q % 8 = 5) {b ω γ : ℕ}
    (hκ : (2 * ω) ^ 2 < q) (hτ : 0 < zDigits)
    (hk : 2 * 2 ^ κ ∣ 2 ^ α) (h2 : (2 : ZMod q) ≠ 0)
    (pp : ArkLib.Lattices.Hachi.PublicParamsD 𝓜(q, α) innerRows (2 ^ m) messageDigits
      outerRows (2 ^ r) innerDigits dRows) :
    (composed (oSpec := oSpec) init impl hq5 (b := b) (ω := ω) (γ := γ) hκ hτ hk h2 pp).relIn =
        ArkLib.Lattices.Hachi.TraceHead.relScalarEval α κ hk h2 pp (b : ZMod q)
          (quadEvalBetaSq γ b zDigits ((𝓜(q, α)).φ.natDegree) m messageDigits) γ (2 * ω) ∧
      (composed (oSpec := oSpec) init impl hq5 (b := b) (ω := ω) (γ := γ) hκ hτ hk h2
          pp).relOut = (quadEvalPackage init impl hq5 (b := b) (γ := γ) hκ hτ pp).relOut :=
  ⟨rfl, rfl⟩

end HachiTraceHeadCompositionTest

/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tobias Rothmann
-/
import ArkLib.Commitments.Functional.Hachi.QuadEval.Bridge
import ArkLib.Commitments.Functional.Hachi.QuadEval.Soundness
import ArkLib.OracleReduction.Security.CoordinateWiseSpecialSoundness.Escape

/-!
  # Escape-threaded Hachi front (`evalChainE`) — skeleton (sumcheck-track milestone F2.0)

  The §4.3 opening chain (`LinSumcheck/`) introduces a **new commitment** — Figure 4's
  `t = Com(w̃)` — whose binding break is a fresh extraction escape (Hachi [NOZ26] Remark 2:
  weak binding, a Module-SIS solution via Lemma 7). Composed CWSS extraction feeds every
  downstream extractor's output into the *previous* seam relation, so this escape must flow
  backwards through **all** upstream seams — including the finished bridge/`QuadEval` chain,
  whose relations (`relPolyEval`, `relIn`, `relOut`) have no home for it.

  This file threads a single abstract escape budget `E` (with escape set `esc : Set E`,
  statement-independent — design decision G1) through the finished front via `Set.withEscape`:

  * `relPolyEvalE`, `relInE`, `relOutE` — the widened relations (witnesses `· ⊕ E`);
  * `bridgePackageE` — the widened polynomial-level bridge, **sorry-free** (the escape branch of
    the pull-back is the identity; the real branch is the finished `mem_relPolyEval_of_relIn`);
  * `quadEval_coordinateWiseSpecialSound_withEscape` — the widened Lemma 8 (**sorried**: re-run
    the finished extraction with an escape-pass-through witness assembler `buildWitnessE`; if any
    branch response is `.inr e`, output `.inr e`; otherwise strip the `Sum.inl`s and apply the
    finished `buildWitness_mem_relIn` verbatim — no edits to done proofs);
  * `quadEvalPackageE` and the composed widened front `evalChainE = bridgePackageE ▷
    quadEvalPackageE`, the drop-in replacement of `evalChain` that the §4.3 chain composes onto.

  At `E := Empty`, `esc := ∅` the widened relations degenerate to the originals
  (`Set.withEscape_empty_iff`), so nothing is lost.

  ## References

  * [Nguyen, N. K., O'Rourke, G., and Zhang, J., *Hachi: Efficient Lattice-Based Multilinear
      Polynomial Commitments over Extension Fields*][NOZ26]
-/

namespace ArkLib.Lattices.Ajtai.InnerOuter

open CompPoly ArkLib.Lattices.CyclotomicModulus
open WeakBinding
open OracleComp OracleSpec ProtocolSpec CoordinateWise CoordinateWise.SingleRound

/-- A left-inhabited sum is inhabited — `Nonempty (Wit ⊕ E)` for the escape-threaded witness
types, from the existing witness `Nonempty` instances. -/
instance {A E : Type} [Nonempty A] : Nonempty (A ⊕ E) := ⟨.inl (Classical.arbitrary A)⟩

section ThreadedRelations

variable {q : ℕ} [NeZero q] [Fact (Nat.Prime q)] [BEq (ZMod q)] [LawfulBEq (ZMod q)]
  (Φ : CyclotomicModulus (ZMod q)) [IsCyclotomic Φ]
variable {innerRows messageDigits outerRows innerDigits dRows zDigits m r : Nat}
variable {E : Type}

/-- Escape-threaded `relPolyEval` (the chain-head relation): a real polynomial-level witness, or
an escape from further down the chain. -/
def relPolyEvalE (base : ZMod q) (βSq γ κ : ℕ) (esc : Set E) :
    Set (PolyEvalStatement Φ innerRows messageDigits outerRows innerDigits dRows m r ×
         (QuadEvalWitness Φ innerRows (2 ^ m) messageDigits (2 ^ r) innerDigits ⊕ E)) :=
  (relPolyEval Φ base βSq γ κ).withEscape esc

/-- Escape-threaded `QuadEval.relIn` (Lemma 8's extraction disjunction, widened). -/
def relInE (base : ZMod q) (βSq γ κ : ℕ) (esc : Set E) :
    Set (QuadEvalStatement Φ innerRows (2 ^ m) messageDigits outerRows (2 ^ r) innerDigits
          dRows ×
         (QuadEvalWitness Φ innerRows (2 ^ m) messageDigits (2 ^ r) innerDigits ⊕ E)) :=
  (relIn Φ base βSq γ κ).withEscape esc

/-- Escape-threaded `QuadEval.relOut` (Hachi Eq. (20) + range checks, widened): the §4.3 chain's
input seam. -/
def relOutE (base : ZMod q) (ω γ : ℕ) (esc : Set E) :
    Set ((QuadEvalStatement Φ innerRows (2 ^ m) messageDigits outerRows (2 ^ r) innerDigits
            dRows ×
          CarrierCom Φ dRows × (Fin (2 ^ r) → ShortChallenge Φ ω)) ×
         (QuadEvalResponse Φ innerRows (2 ^ m) messageDigits (2 ^ r) innerDigits zDigits ⊕ E)) :=
  (relOut (zDigits := zDigits) Φ base ω γ).withEscape esc

omit [NeZero q] in
/-- **Escape-threaded pull-back** for the polynomial-level bridge (the `hRel` of
`bridgePackageE`): the real branch is the finished `mem_relPolyEval_of_relIn`; the escape branch
passes through (escapes are statement-independent). Sorry-free. -/
theorem mem_relPolyEvalE_of_relInE (base : ZMod q) (βSq γ κ : ℕ) (esc : Set E)
    (s : PolyEvalStatement Φ innerRows messageDigits outerRows innerDigits dRows m r)
    (w : QuadEvalWitness Φ innerRows (2 ^ m) messageDigits (2 ^ r) innerDigits ⊕ E)
    (h : (toQuadEvalStatement Φ s, w) ∈ relInE Φ base βSq γ κ esc) :
    (s, w) ∈ relPolyEvalE Φ base βSq γ κ esc := by
  cases w with
  | inl w' => exact mem_relPolyEval_of_relIn Φ base βSq γ κ s w' h
  | inr e => exact h

end ThreadedRelations

section ThreadedPackages

variable {q : ℕ} [NeZero q] [Fact (Nat.Prime q)] [BEq (ZMod q)] [LawfulBEq (ZMod q)] {α : ℕ}
variable {innerRows messageDigits outerRows innerDigits dRows zDigits m r : Nat}
variable {ι : Type} {oSpec : OracleSpec ι} {σ : Type} {E : Type}

/-- **The escape-threaded polynomial-level bridge as a `CWSSPackage`** (widened
`bridgePackage`), sorry-free: the same zero-round `ReduceClaim` verifier, with the widened
relations and the escape-pass-through pull-back `mem_relPolyEvalE_of_relInE`. -/
def bridgePackageE (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (base : ZMod q) (βSq γ κ : ℕ) (esc : Set E) :
    CWSSPackage init impl
      (PolyEvalStatement 𝓜(q, α) innerRows messageDigits outerRows innerDigits dRows m r)
      (QuadEvalWitness 𝓜(q, α) innerRows (2 ^ m) messageDigits (2 ^ r) innerDigits ⊕ E)
      (QuadEvalStatement 𝓜(q, α) innerRows (2 ^ m) messageDigits outerRows (2 ^ r) innerDigits
        dRows)
      (QuadEvalWitness 𝓜(q, α) innerRows (2 ^ m) messageDigits (2 ^ r) innerDigits ⊕ E)
      (!p[] : ProtocolSpec 0) where
  verifier := bridgeVerifier (oSpec := oSpec) 𝓜(q, α)
  struct := CWSSStructure.ofIsEmpty
  relIn := relPolyEvalE 𝓜(q, α) base βSq γ κ esc
  relOut := relInE 𝓜(q, α) base βSq γ κ esc
  isPure := ⟨fun stmt _ => toQuadEvalStatement 𝓜(q, α) stmt, fun _ _ => rfl⟩
  isCWSS := ReduceClaim.verifier_coordinateWiseSpecialSound
    (relIn := relPolyEvalE 𝓜(q, α) base βSq γ κ esc)
    (relOut := relInE 𝓜(q, α) base βSq γ κ esc)
    (mapWitInv := fun _ w => w) (D := CWSSStructure.ofIsEmpty)
    (mem_relPolyEvalE_of_relInE 𝓜(q, α) base βSq γ κ esc)

/-- **Escape-threaded Hachi Lemma 8 (skeleton).** The `QuadEval` fold verifier is CWSS for the
*widened* relations `relInE`/`relOutE`.

**Sorried (F2.0).** Proof plan: `coordinateWiseSpecialSound_of_mkWitness` with the widened
assembler `buildWitnessE` — if some branch response is `.inr e` (pick the least such branch),
output `.inr e` (its `relOutE`-membership is exactly `e ∈ esc`, which is `relInE`'s `.inr`
case); otherwise all responses are `.inl`, strip them and apply the finished
`buildWitness_mem_relIn` verbatim. No edits to the finished sorry-free proofs. -/
theorem quadEval_coordinateWiseSpecialSound_withEscape
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (hq5 : q % 8 = 5) {b ω γ : ℕ} (hκ : (2 * ω) ^ 2 < q) (hτ : 0 < zDigits) (esc : Set E) :
    (verifier (oSpec := oSpec) (ω := ω) 𝓜(q, α) (innerRows := innerRows)
        (messageDigits := messageDigits) (outerRows := outerRows)
        (innerDigits := innerDigits) (dRows := dRows) (m := m)
        (r := r)).coordinateWiseSpecialSound init impl
      (foldStructure (CarrierCom := CarrierCom 𝓜(q, α) dRows)
        (C := ShortChallenge 𝓜(q, α) ω) (r := r))
      (relInE 𝓜(q, α) (b : ZMod q)
        (quadEvalBetaSq γ b zDigits ((𝓜(q, α)).φ.natDegree) m messageDigits) γ (2 * ω) esc)
      (relOutE (zDigits := zDigits) 𝓜(q, α) (b : ZMod q) ω γ esc) := by
  sorry

/-- **Escape-threaded `QuadEval` package** (widened `quadEvalPackage`): the same two-round fold
verifier and `foldStructure`, with the widened relations; the certificate is the sorried
`quadEval_coordinateWiseSpecialSound_withEscape`. -/
def quadEvalPackageE (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (hq5 : q % 8 = 5) {b ω γ : ℕ} (hκ : (2 * ω) ^ 2 < q) (hτ : 0 < zDigits) (esc : Set E) :
    CWSSPackage init impl
      (QuadEvalStatement 𝓜(q, α) innerRows (2 ^ m) messageDigits outerRows (2 ^ r) innerDigits
        dRows)
      (QuadEvalWitness 𝓜(q, α) innerRows (2 ^ m) messageDigits (2 ^ r) innerDigits ⊕ E)
      (QuadEvalStatement 𝓜(q, α) innerRows (2 ^ m) messageDigits outerRows (2 ^ r) innerDigits
          dRows ×
        CarrierCom 𝓜(q, α) dRows × (Fin (2 ^ r) → ShortChallenge 𝓜(q, α) ω))
      (QuadEvalResponse 𝓜(q, α) innerRows (2 ^ m) messageDigits (2 ^ r) innerDigits zDigits ⊕ E)
      (pSpec (CarrierCom 𝓜(q, α) dRows) (ShortChallenge 𝓜(q, α) ω) r) where
  verifier := verifier (oSpec := oSpec) (ω := ω) 𝓜(q, α)
  struct :=
    foldStructure (CarrierCom := CarrierCom 𝓜(q, α) dRows) (C := ShortChallenge 𝓜(q, α) ω)
      (r := r)
  relIn := relInE 𝓜(q, α) (b : ZMod q)
    (quadEvalBetaSq γ b zDigits ((𝓜(q, α)).φ.natDegree) m messageDigits) γ (2 * ω) esc
  relOut := relOutE (zDigits := zDigits) 𝓜(q, α) (b : ZMod q) ω γ esc
  isPure := ⟨fun stmt tr => (stmt, tr.messages ⟨0, rfl⟩, tr.challenges ⟨1, rfl⟩), fun _ _ => rfl⟩
  isCWSS := quadEval_coordinateWiseSpecialSound_withEscape init impl hq5 hκ hτ esc

/-- **The escape-threaded evaluation front** `bridgePackageE ▷ quadEvalPackageE`: the widened
drop-in for `evalChain`, from `relPolyEvalE` to `relOutE` (Eq. (20) + ranges, widened). The
§4.3 opening chain (`LinSumcheck/`) composes onto this front's `relOutE` seam. -/
def evalChainE (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (hq5 : q % 8 = 5) {b ω γ : ℕ} (hκ : (2 * ω) ^ 2 < q) (hτ : 0 < zDigits) (esc : Set E) :
    CWSSPackage init impl
      (PolyEvalStatement 𝓜(q, α) innerRows messageDigits outerRows innerDigits dRows m r)
      (QuadEvalWitness 𝓜(q, α) innerRows (2 ^ m) messageDigits (2 ^ r) innerDigits ⊕ E)
      (QuadEvalStatement 𝓜(q, α) innerRows (2 ^ m) messageDigits outerRows (2 ^ r) innerDigits
          dRows ×
        CarrierCom 𝓜(q, α) dRows × (Fin (2 ^ r) → ShortChallenge 𝓜(q, α) ω))
      (QuadEvalResponse 𝓜(q, α) innerRows (2 ^ m) messageDigits (2 ^ r) innerDigits zDigits ⊕ E)
      ((!p[] : ProtocolSpec 0) ++ₚ
        pSpec (CarrierCom 𝓜(q, α) dRows) (ShortChallenge 𝓜(q, α) ω) r) :=
  bridgePackageE init impl (b : ZMod q)
      (quadEvalBetaSq γ b zDigits ((𝓜(q, α)).φ.natDegree) m messageDigits) γ (2 * ω) esc ▷
    quadEvalPackageE init impl hq5 hκ hτ esc

end ThreadedPackages

end ArkLib.Lattices.Ajtai.InnerOuter

/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tobias Rothmann
-/
import ArkLib.Commitments.Functional.Hachi.Recursion.PartialEval

/-!
  # `Z`-packing bridge — Hachi §4.5, Eqs. (25)–(26) — skeleton, ⚠ **open soundness question**

  Zero-round bridge collapsing the per-`i` partial-evaluation claims into the **single
  `Z`-packed claim** of Hachi Eq. (26):

  * `relIn = relPartialEvalE` — `∀ i ∈ {0,1}^κ: partialEvalAt w̃ a₀ i = yᵢ`
    (`Recursion/PartialEval.lean`);
  * `relOut = relHatEvalE` — `hatEval w̃ a₀ = ∑ᵢ yᵢ·Z^{⟨i⟩}`, where
    `hatEval w̃ a₀ := ∑ⱼ ŵⱼ·eq(j, a₀)` with `ŵⱼ := ∑ᵢ w̃_{j‖i}·Z^{⟨i⟩}` (Eq. (25)); the
    statement map computes the public right-hand side `∑ᵢ yᵢ·zpow i`.

  The completeness direction is trivial (substitute the per-`i` claims). **The extraction
  direction — the paper's implicit "equivalence" claim below Eq. (26) — appears to be FALSE**,
  and this bridge's sorried pull-back `mem_relPartialEvalE_of_relHatEvalE` is recorded as an
  **open soundness question**, deliberately isolated in this one zero-round seam (mirroring how
  the Lemma 10 gap is isolated in the zero-check).

  ## ⚠ The gap (see `HACHI_RECURSION_GAP.md` for the full analysis)

  The packed claim pins only the single `F`-linear combination `∑ᵢ Z^{⟨i⟩}·(pᵢ − yᵢ) = 0` of
  the per-`i` defects `pᵢ − yᵢ := partialEvalAt w̃ a₀ i − yᵢ ∈ F`. Since the defects are
  full field elements (the point `a₀` lies in `F`, not in the base field), this one equation
  has a `(k−1)·k`-dimensional `F_q`-kernel for `k = 2^κ ≥ 2` — the per-`i` claims do **not**
  follow. Concretely (`κ = 1`, `F = F_q[Z]`): choosing `y₁ := p₁ − δ`, `y₀ := p₀ + Zδ` keeps
  the packed right-hand side invariant while shifting the reconstructed evaluation
  `y₀ + a·y₁ = mle[w̃](a₀, a) + δ(Z − a)` — for `a ≠ Z` every target value is reachable, so the
  §4.5 recursion step (and §3.2's generic form) is not knowledge-sound as stated. Candidate
  repairs (recorded in the gap note; all deviate from the paper): a batching challenge round
  over the peeled index (Kronecker-seeded, DP24-relocation style), or replacing the peeling with
  the generic §3.1 packing (`F_{q^k}`-coefficient reading, paper Fig. 2 row 1, at the cost of
  `κ` extra variables and a sparser commitment reinterpretation).

  Until a repair is adopted, this bridge is the faithful rendering of the paper's step, and its
  sorry is expected to be **unprovable as stated** — kept so the composed chain records exactly
  where the paper's argument stands.

  ## References

  * [Nguyen, N. K., O'Rourke, G., and Zhang, J., *Hachi: Efficient Lattice-Based Multilinear
      Polynomial Commitments over Extension Fields*][NOZ26]
-/

namespace ArkLib.Lattices.Ajtai.InnerOuter

open CompPoly ArkLib.Lattices.CyclotomicModulus
open OracleComp OracleSpec ProtocolSpec CoordinateWise

/-- The `Z`-packed evaluation-claim statement (Hachi Eq. (26)): the commitment, the low point
half, and the public packed value `∑ᵢ yᵢ·Z^{⟨i⟩}`. -/
structure HatEvalStatement (TCom F : Type) (mLow : ℕ) where
  /-- The `w̃`-commitment. -/
  t : TCom
  /-- The low point half `a₀ ∈ F^{mLow}`. -/
  pointLow : Fin mLow → F
  /-- The packed claim value `∑ᵢ yᵢ·Z^{⟨i⟩} ∈ F ≅ F_{q^k}`. -/
  value : F

section Bridge

variable {q : ℕ} [NeZero q] [Fact (Nat.Prime q)] [BEq (ZMod q)] [LawfulBEq (ZMod q)]
  (Φ : CyclotomicModulus (ZMod q)) [IsCyclotomic Φ]
variable {n μ : ℕ} {E : Type} {F : Type} [Field F]
variable (mLow κ : ℕ) (bound ρBound : ℕ)
variable {ι : Type} {oSpec : OracleSpec ι} {σ : Type}

/-- The `Z`-packed table evaluation (Hachi Eqs. (25)–(26) left-hand side):
`hatEval w̃ a₀ = ∑_{j ∈ {0,1}^{mLow}} ŵⱼ·eq(j, a₀)` with `ŵⱼ := ∑ᵢ w̃_{j‖i}·zpow i` — the
reading of the committed table as an `F`-entried table along the `Z`-power basis `zpow`
(honestly `zpow i = Z^{⟨i⟩}`, the power basis of `F/F_q`). **Sorried (G3-adjacent)**. -/
def hatEval (φF : ZMod q →+* F) (zpow : Fin (2 ^ κ) → F) (w : LiftedWitness Φ μ n)
    (a₀ : Fin mLow → F) : F :=
  sorry

/-- **The `Z`-packed claim relation** (Hachi Eq. (26)): `w̃` opens `t` and its `Z`-packed table
evaluates to the packed public value at the low point half. This is the claim the trace handoff
(`Recursion/TraceHandoff.lean`) converts into the next iteration's `Rq`-statement. -/
def relHatEval (zpow : Fin (2 ^ κ) → F)
    (K : LiftCom (LiftedWitness Φ μ n) E (liftShort Φ bound ρBound))
    (φF : ZMod q →+* F) :
    Set (HatEvalStatement K.TCom F mLow × LiftedWitness Φ μ n) :=
  {p |
    K.com p.2 = p.1.t ∧
    hatEval Φ mLow κ φF zpow p.2 p.1.pointLow = p.1.value}

/-- Escape-threaded `Z`-packed claim relation. -/
def relHatEvalE (zpow : Fin (2 ^ κ) → F)
    (K : LiftCom (LiftedWitness Φ μ n) E (liftShort Φ bound ρBound))
    (φF : ZMod q →+* F) :
    Set (HatEvalStatement K.TCom F mLow × (LiftedWitness Φ μ n ⊕ E)) :=
  (relHatEval Φ mLow κ bound ρBound zpow K φF).withEscape K.esc

/-- The bridge's statement map: forget the peeled point half and pack the partial evaluations
into the public right-hand side `∑ᵢ yᵢ·zpow i` of Eq. (26). -/
def toHatEvalStatement {TCom : Type} (zpow : Fin (2 ^ κ) → F)
    (s : PartialEvalStatement TCom F mLow κ) : HatEvalStatement TCom F mLow :=
  ⟨s.t, s.pointLow, ∑ i, s.partials i * zpow i⟩

/-- ⚠ **The un-packing pull-back — open soundness question (`HACHI_RECURSION_GAP.md`).** As the
paper's step below Eq. (26) implicitly requires, the packed claim should imply the per-`i`
claims. **This statement is expected to be unprovable**: the packed claim constrains only one
`F`-linear combination of the per-`i` defects, which have a nontrivial kernel for `κ ≥ 1` (see
the module docstring for the explicit `κ = 1` cheat). The sorry is kept — deliberately isolated
in this zero-round seam — until a repair (batching challenge / generic §3.1 packing) is adopted;
any repair changes this bridge's *protocol content*, not the surrounding seams. -/
theorem mem_relPartialEvalE_of_relHatEvalE (zpow : Fin (2 ^ κ) → F)
    (K : LiftCom (LiftedWitness Φ μ n) E (liftShort Φ bound ρBound))
    (φF : ZMod q →+* F)
    (s : PartialEvalStatement K.TCom F mLow κ) (w : LiftedWitness Φ μ n ⊕ E)
    (h : (toHatEvalStatement mLow κ zpow s, w) ∈ relHatEvalE Φ mLow κ bound ρBound zpow K φF) :
    (s, w) ∈ relPartialEvalE Φ mLow κ bound ρBound K φF := by
  sorry

/-- **The `Z`-packing bridge as a `CWSSPackage`** (Hachi §4.5, Eqs. (25)–(26)): zero-round
`ReduceClaim` at `mapStmt := toHatEvalStatement`, reducing `relPartialEvalE` to `relHatEvalE`.
⚠ Its certificate rests on the sorried — and expectedly unprovable as stated — un-packing
pull-back; see the module docstring. -/
def zBatchPackage (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (zpow : Fin (2 ^ κ) → F)
    (K : LiftCom (LiftedWitness Φ μ n) E (liftShort Φ bound ρBound))
    (φF : ZMod q →+* F) :
    CWSSPackage init impl
      (PartialEvalStatement K.TCom F mLow κ) (LiftedWitness Φ μ n ⊕ E)
      (HatEvalStatement K.TCom F mLow) (LiftedWitness Φ μ n ⊕ E)
      (!p[] : ProtocolSpec 0) where
  verifier := ReduceClaim.verifier oSpec (toHatEvalStatement mLow κ zpow)
  struct := CWSSStructure.ofIsEmpty
  relIn := relPartialEvalE Φ mLow κ bound ρBound K φF
  relOut := relHatEvalE Φ mLow κ bound ρBound zpow K φF
  isPure := ⟨fun stmt _ => toHatEvalStatement mLow κ zpow stmt, fun _ _ => rfl⟩
  isCWSS := ReduceClaim.verifier_coordinateWiseSpecialSound
    (relIn := relPartialEvalE Φ mLow κ bound ρBound K φF)
    (relOut := relHatEvalE Φ mLow κ bound ρBound zpow K φF)
    (mapWitInv := fun _ w => w) (D := CWSSStructure.ofIsEmpty)
    (mem_relPartialEvalE_of_relHatEvalE Φ mLow κ bound ρBound zpow K φF)

end Bridge

end ArkLib.Lattices.Ajtai.InnerOuter

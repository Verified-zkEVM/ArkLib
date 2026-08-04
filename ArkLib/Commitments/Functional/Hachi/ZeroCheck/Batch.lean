/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tobias Rothmann
-/
import ArkLib.Commitments.Functional.Hachi.ZeroCheck.Constraints

/-!
  # Batching bridge — Hachi Eqs. (22)–(23) — skeleton (zero-round)

  Zero-round bridge between the lift's per-row/per-entry residual claims and the **batched
  polynomial-identity** form the zero-check tests:

  * `relIn = relLiftE` — opening `w̃` of `t`, per-row `α`-evaluated constraints, entrywise
    ranges (`RingSwitch/Reduction.lean`);
  * `relOut = relBatchedE` — opening `w̃` of `t`, `H₀^{w̃} ≡ 0` and `H_α^{w̃} ≡ 0` as
    `CMlPolynomialEval` identities (Eqs. (22)–(23), `ZeroCheck/Constraints.lean`).

  The statement is **unchanged** (`ReduceClaim` at `mapStmt := id`, witness maps `id`): only the
  *reading* of the claims changes. This isolates the batching algebra away from the zero-check's
  Kronecker interpolation:

  * **completeness direction** (not needed for CWSS): per-row + ranges ⇒ every `eq̃`-basis
    coefficient of `H_α`/`H₀` vanishes ⇒ both identities;
  * **extraction direction** (the sorried pull-back `mem_relLiftE_of_relBatchedE`):
    `H_α ≡ 0` ⇒ per-row constraints, by non-degeneracy of the `eq̃` basis (evaluation at the
    Boolean points is the identity matrix); `H₀ ≡ 0` ⇒ per-entry range membership, since each
    entry is a root of the `2b − 1`-factor range product over the *field* `F` (needs
    `IsDomain F` — a field here — and `2b − 1 < q` to read the field roots back as centered
    `Zq`-representatives), which yields `liftShort` under the norm-parameter hypotheses.

  ## References

  * [Nguyen, N. K., O'Rourke, G., and Zhang, J., *Hachi: Efficient Lattice-Based Multilinear
      Polynomial Commitments over Extension Fields*][NOZ26]
-/

namespace ArkLib.Lattices.Ajtai.InnerOuter

open CompPoly ArkLib.Lattices.CyclotomicModulus
open OracleComp OracleSpec ProtocolSpec CoordinateWise

variable {q : ℕ} [NeZero q] [Fact (Nat.Prime q)] [BEq (ZMod q)] [LawfulBEq (ZMod q)]
  (Φ : CyclotomicModulus (ZMod q)) [IsCyclotomic Φ]
variable {n μ : ℕ} {E : Type} {F : Type} [Field F]
variable (m₀ m₁ : ℕ) (bound ρBound : ℕ)
variable {ι : Type} {oSpec : OracleSpec ι} {σ : Type}

/-- **The batched relation** (Hachi Eqs. (22)–(23) as polynomial identities): `w̃` opens `t`,
the range polynomial `H₀^{w̃}` and the linear-constraint polynomial `H_α^{w̃}` are identically
zero, and the public bound-sanity conjunct is retained. This is the zero-check's `relIn`. -/
def relBatched (K : LiftCom (LiftedWitness Φ μ n) E (liftShort Φ bound ρBound))
    (φF : ZMod q →+* F) (b : ℕ) :
    Set (LiftStatement Φ K.TCom F n μ × LiftedWitness Φ μ n) :=
  {p |
    K.com p.2 = p.1.2.1 ∧
    hZero Φ m₀ φF b p.2 = 0 ∧
    hAlpha Φ m₁ φF b p.1.1 p.1.2.2 p.2 = 0 ∧
    bound ≤ p.1.1.bound}

/-- Escape-threaded batched relation — the zero-check's seam. -/
def relBatchedE (K : LiftCom (LiftedWitness Φ μ n) E (liftShort Φ bound ρBound))
    (φF : ZMod q →+* F) (b : ℕ) :
    Set (LiftStatement Φ K.TCom F n μ × (LiftedWitness Φ μ n ⊕ E)) :=
  (relBatched Φ m₀ m₁ bound ρBound K φF b).withEscape K.esc

/-- **Un-batching pull-back** (the bridge's `hRel`): the batched identities imply the lift's
per-row claims *and* shortness. Escapes pass through.

Because `relBatched` deliberately omits the `liftShort` conjunct (unlike `relLift`), `H₀` is
load-bearing here rather than decorative: shortness must be *derived* from the range identity.

**Sorried** (the substantive content is the corrected [NOZ26, Lemma 10]):
* the **per-row half** — `H_α ≡ 0` (its `CMlPolynomialEval` value vector being zero) ⇒ (reading
  the vector at each `rowPoint i`, then `hAlphaEvals_rowPoint`) the per-row `evalAt`-equations of
  `relLift` as packaged by `liftCheckAt`; this uses `hn : n ≤ 2 ^ m₁` (the batching-cube
  row-encoding bound);
* the **shortness half** — `H₀ ≡ 0` ⇒ each table entry is a root of `rangeProduct b` over the
  field `F` ⇒ (`rangeProduct_eq_zero_iff`, with `hq : 2 * b ≤ q + 1` reading field roots as
  centered representatives, `hcov : (μ + n) * Φ.φ.natDegree ≤ 2 ^ m₀` covering every witness /
  quotient coefficient by a cube point, `hb : b - 1 ≤ bound` on the `z`-side and
  `hρ : b - 1 ≤ ρBound` on the `ρ`-side) `liftShort Φ bound ρBound w̃`.

The bound-sanity conjunct is shared verbatim. The `hρ` hypothesis is load-bearing (at
`ρBound = 0`, `b ≥ 2`, an honest `ρ ≠ 0` witness satisfies `relBatched` yet violates
`RhoShort`), which is exactly why `relBatched` omits `liftShort` and this bridge re-derives it. -/
theorem mem_relLiftE_of_relBatchedE
    (K : LiftCom (LiftedWitness Φ μ n) E (liftShort Φ bound ρBound))
    (φF : ZMod q →+* F) (b : ℕ) (hq : 2 * b ≤ q + 1) (hb : b - 1 ≤ bound)
    (hρ : b - 1 ≤ ρBound) (hcov : (μ + n) * Φ.φ.natDegree ≤ 2 ^ m₀) (hn : n ≤ 2 ^ m₁)
    (X : LiftStatement Φ K.TCom F n μ) (w : LiftedWitness Φ μ n ⊕ E)
    (h : (X, w) ∈ relBatchedE Φ m₀ m₁ bound ρBound K φF b) :
    (X, w) ∈ relLiftE Φ bound ρBound K φF := by
  sorry

/-- **The batching bridge as a `CWSSPackage`**: zero-round `ReduceClaim` at `mapStmt := id`,
reducing `relLiftE` to `relBatchedE` with no soundness error (the whole content is the sorried
un-batching pull-back). -/
def batchPackage (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (K : LiftCom (LiftedWitness Φ μ n) E (liftShort Φ bound ρBound))
    (φF : ZMod q →+* F) (b : ℕ) (hq : 2 * b ≤ q + 1) (hb : b - 1 ≤ bound)
    (hρ : b - 1 ≤ ρBound) (hcov : (μ + n) * Φ.φ.natDegree ≤ 2 ^ m₀) (hn : n ≤ 2 ^ m₁) :
    CWSSPackage init impl
      (LiftStatement Φ K.TCom F n μ) (LiftedWitness Φ μ n ⊕ E)
      (LiftStatement Φ K.TCom F n μ) (LiftedWitness Φ μ n ⊕ E)
      (!p[] : ProtocolSpec 0) where
  verifier := ReduceClaim.verifier oSpec id
  struct := CWSSStructure.ofIsEmpty
  relIn := relLiftE Φ bound ρBound K φF
  relOut := relBatchedE Φ m₀ m₁ bound ρBound K φF b
  isPure := ⟨fun stmt _ => stmt, fun _ _ => rfl⟩
  isCWSS := ReduceClaim.verifier_coordinateWiseSpecialSound
    (relIn := relLiftE Φ bound ρBound K φF)
    (relOut := relBatchedE Φ m₀ m₁ bound ρBound K φF b)
    (mapWitInv := fun _ w => w) (D := CWSSStructure.ofIsEmpty)
    (fun stmtIn witOut h =>
      mem_relLiftE_of_relBatchedE Φ m₀ m₁ bound ρBound K φF b hq hb hρ hcov hn stmtIn witOut h)

end ArkLib.Lattices.Ajtai.InnerOuter

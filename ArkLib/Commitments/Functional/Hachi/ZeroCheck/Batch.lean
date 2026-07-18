/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tobias Rothmann
-/
import ArkLib.Commitments.Functional.Hachi.ZeroCheck.Constraints

/-!
  # Batching bridge — Hachi Eqs. (22)–(23) — skeleton (zero-round, part of milestone F6)

  Zero-round bridge between the lift's per-row/per-entry residual claims and the **batched
  polynomial-identity** form the zero-check tests:

  * `relIn = relLift` — opening `w̃` of `t`, per-row `α`-evaluated constraints, entrywise
    ranges (`RingSwitch/Reduction.lean`);
  * `relOut = relBatched` — opening `w̃` of `t`, `H₀^{w̃} ≡ 0` and `H_α^{w̃} ≡ 0` as
    `MvPolynomial` identities (Eqs. (22)–(23), `ZeroCheck/Constraints.lean`).

  The statement is **unchanged** (`ReduceClaim` at `mapStmt := id`, witness maps `id`): only the
  *reading* of the claims changes. This isolates the batching algebra away from the zero-check's
  Kronecker interpolation:

  * **completeness direction** (not needed for CWSS): per-row + ranges ⇒ every `eq̃`-basis
    coefficient of `H_α`/`H₀` vanishes ⇒ both identities;
  * **extraction direction** (the sorried pull-back `mem_relLift_of_relBatched`):
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
    (φF : ZMod q →+* F) (b : ℕ) (esc : Set E) :
    Set (LiftStatement Φ K.TCom F n μ × (LiftedWitness Φ μ n ⊕ E)) :=
  (relBatched Φ m₀ m₁ bound ρBound K φF b).withEscape esc

/-- **Un-batching pull-back** (the bridge's `hRel`): the batched identities imply the lift's
per-row and range claims. Escapes pass through.

**Sorried.** Proof plan: `H_α ≡ 0` ⇒ all `eq̃`-basis coefficients vanish (basis non-degeneracy:
`eq̃(i', i) = δ_{i,i'}` on Boolean points) ⇒ the per-row `evalAt`-equations of `relLift`
(faithfulness of the sorried `M̃_α`/table encodings, F5); `H₀ ≡ 0` ⇒ each table entry is a root
of `X·∏_{j=1}^{b−1}(X − j)(X + j)` over the field `F` ⇒ (with `hq : 2 * b ≤ q + 1` reading roots
as centered representatives and `hb : b - 1 ≤ bound`, `hρ`-side analogously through the digit
recomposition) `liftShort bound ρBound w̃`; the bound-sanity conjunct is shared verbatim. -/
theorem mem_relLift_of_relBatched
    (K : LiftCom (LiftedWitness Φ μ n) E (liftShort Φ bound ρBound))
    (φF : ZMod q →+* F) (b : ℕ) (hq : 2 * b ≤ q + 1) (hb : b - 1 ≤ bound)
    (X : LiftStatement Φ K.TCom F n μ) (w : LiftedWitness Φ μ n)
    (h : (X, w) ∈ relBatched Φ m₀ m₁ bound ρBound K φF b) :
    (X, w) ∈ relLift Φ bound ρBound K φF := by
  sorry

/-- **The batching bridge as an `EscapeCWSSPackage`**: zero-round `ReduceClaim` at `mapStmt := id`,
reducing plain `relLift` to `relBatched` and carrying `esc` unchanged (the content is the sorried
un-batching pull-back). -/
def batchPackage (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (K : LiftCom (LiftedWitness Φ μ n) E (liftShort Φ bound ρBound))
    (φF : ZMod q →+* F) (b : ℕ) (hq : 2 * b ≤ q + 1) (hb : b - 1 ≤ bound)
    (esc : Set E) :
    EscapeCWSSPackage init impl E
      (LiftStatement Φ K.TCom F n μ) (LiftedWitness Φ μ n)
      (LiftStatement Φ K.TCom F n μ) (LiftedWitness Φ μ n)
      (!p[] : ProtocolSpec 0) where
  verifier := ReduceClaim.verifier oSpec id
  struct := CWSSStructure.ofIsEmpty
  relIn := relLift Φ bound ρBound K φF
  relOut := relBatched Φ m₀ m₁ bound ρBound K φF b
  escIn := esc
  escOut := esc
  escape_mono := fun _ h => h
  isPure := ⟨fun stmt _ => stmt, fun _ _ => rfl⟩
  isCWSS := ReduceClaim.verifier_coordinateWiseSpecialSound
    (relIn := (relLift Φ bound ρBound K φF).withEscape esc)
    (relOut := relBatchedE Φ m₀ m₁ bound ρBound K φF b esc)
    (mapWitInv := fun _ w => w) (D := CWSSStructure.ofIsEmpty)
    (fun stmtIn witOut h => by
      cases witOut with
      | inl w => exact mem_relLift_of_relBatched Φ m₀ m₁ bound ρBound K φF b hq hb stmtIn w h
      | inr e => exact h)

end ArkLib.Lattices.Ajtai.InnerOuter

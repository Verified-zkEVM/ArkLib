/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tobias Rothmann, Pablo Martín Vinuelas
-/
import ArkLib.Commitments.Functional.Hachi.ZeroCheck.Constraints

/-!
  # Batching bridge — Hachi Eqs. (22)–(23) — escape-threaded (zero-round, part of milestone F6)

  Zero-round bridge between the lift's per-row/per-entry residual claims and the **batched
  polynomial-identity** form the zero-check tests:

  * `relIn = relLiftE` — opening `w̃` of `t`, per-row `α`-evaluated constraints, entrywise
    ranges (`RingSwitch/Reduction.lean`);
  * `relOut = relBatchedE` — opening `w̃` of `t`, `H₀^{w̃} ≡ 0` and `H_α^{w̃} ≡ 0` as
    `MvPolynomial` identities (Eqs. (22)–(23), `ZeroCheck/Constraints.lean`), and `w̃` short.

  The statement is **unchanged** (`ReduceClaim` at `mapStmt := id`, witness maps `id`): only the
  *reading* of the claims changes. This isolates the batching algebra away from the zero-check's
  Kronecker interpolation. The `liftShort` conjunct (resolution option 2) is preserved verbatim
  from `relLift`; it is the precondition of the weak-binding escape (`LiftCom.collision_mem`)
  invoked by the zero-check's extraction.

  * **extraction direction** (the pull-back `mem_relLiftE_of_relBatchedE`, **axiom-clean**):
    the only nontrivial conjunct is the per-row equation, recovered from `H_α ≡ 0` by non-degeneracy
    of the `eq̃` basis (`MvPolynomial.MLE_eq_zero_iff`) followed by the row-encoding faithfulness
    lemma `hAlphaEvals_rowPoint`. The `K.com`, `liftShort` and bound-sanity conjuncts are carried
    **verbatim** by `relBatched`; in particular the *range* identity `H₀ ≡ 0` and the norm-parameter
    hypotheses `2b ≤ q+1`, `b−1 ≤ bound` play **no role** in this pull-back (shortness is asserted
    directly), so they are not assumed. The only genuine hypothesis is the row-encoding arity pin
    `hn : n ≤ 2 ^ m₁`. (With `hAlphaEvals`/`wTable` now concrete, no `sorryAx` remains.)

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

/-- **The batched relation** (Hachi Eqs. (22)–(23) as polynomial identities): `w̃` opens `t`, is
short (`liftShort`), the range polynomial `H₀^{w̃}` and the linear-constraint polynomial
`H_α^{w̃}` are identically zero, and the public bound-sanity conjunct is retained. This is the
zero-check's `relIn`. -/
def relBatched (K : LiftCom (LiftedWitness Φ μ n) E (liftShort Φ bound ρBound))
    (φF : ZMod q →+* F) (b : ℕ) :
    Set (LiftStatement Φ K.TCom F n μ × LiftedWitness Φ μ n) :=
  {p |
    K.com p.2 = p.1.2.1 ∧
    liftShort Φ bound ρBound p.2 ∧
    hZero Φ m₀ φF b p.2 = 0 ∧
    hAlpha Φ m₁ φF b p.1.1 p.1.2.2 p.2 = 0 ∧
    bound ≤ p.1.1.bound}

/-- Escape-threaded batched relation — the zero-check's seam. -/
def relBatchedE (K : LiftCom (LiftedWitness Φ μ n) E (liftShort Φ bound ρBound))
    (φF : ZMod q →+* F) (b : ℕ) :
    Set (LiftStatement Φ K.TCom F n μ × (LiftedWitness Φ μ n ⊕ E)) :=
  (relBatched Φ m₀ m₁ bound ρBound K φF b).withEscape K.esc

omit [NeZero q] [IsCyclotomic Φ] in
/-- **Un-batching pull-back** (the bridge's `hRel`): the batched identities imply the lift's
per-row claims. Escapes pass through.

The only nontrivial conjunct is the per-row equation, recovered from `H_α ≡ 0`: by
`MvPolynomial.MLE_eq_zero_iff` every Boolean-point coefficient `hAlphaEvals` vanishes, and by
`hAlphaEvals_rowPoint` the coefficient at `rowPoint i` is exactly row `i`'s `α`-evaluated lift
defect, so the row equation of `relLift` follows. The `K.com`, `liftShort` and bound-sanity
conjuncts are carried verbatim by `relBatched` — in particular the *range* identity `H₀ ≡ 0` and
the norm-parameter hypotheses `2b ≤ q+1`, `b-1 ≤ bound` play **no role** in this pull-back
(shortness is already asserted directly), so they are not assumed. The arity pin `hn : n ≤ 2 ^ m₁`
is the batching cube's row-encoding requirement. -/
theorem mem_relLiftE_of_relBatchedE
    (K : LiftCom (LiftedWitness Φ μ n) E (liftShort Φ bound ρBound))
    (φF : ZMod q →+* F) (b : ℕ) (hn : n ≤ 2 ^ m₁)
    (X : LiftStatement Φ K.TCom F n μ) (w : LiftedWitness Φ μ n ⊕ E)
    (h : (X, w) ∈ relBatchedE Φ m₀ m₁ bound ρBound K φF b) :
    (X, w) ∈ relLiftE Φ bound ρBound K φF := by
  rcases w with w | e
  · -- real witness: only the per-row equation needs work
    simp only [relBatchedE, Set.mem_withEscape_inl, relBatched, Set.mem_setOf_eq] at h
    obtain ⟨hcom, hshort, _hZero, hAlphaZ, hbound⟩ := h
    simp only [relLiftE, Set.mem_withEscape_inl, relLift, Set.mem_setOf_eq]
    refine ⟨hcom, fun i => ?_, hshort, hbound⟩
    unfold hAlpha at hAlphaZ
    rw [MvPolynomial.MLE_eq_zero_iff] at hAlphaZ
    have hi := hAlphaZ (rowPoint m₁ hn i)
    rw [hAlphaEvals_rowPoint] at hi
    linear_combination hi
  · -- escape: statement-independent pass-through
    simpa only [relBatchedE, relLiftE, Set.mem_withEscape_inr] using h

/-- **The batching bridge as a `CWSSPackage`**: zero-round `ReduceClaim` at `mapStmt := id`,
reducing `relLiftE` to `relBatchedE` with no soundness error (the whole content is the sorried
un-batching pull-back). -/
def batchPackage (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (K : LiftCom (LiftedWitness Φ μ n) E (liftShort Φ bound ρBound))
    (φF : ZMod q →+* F) (b : ℕ) (hn : n ≤ 2 ^ m₁) :
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
      mem_relLiftE_of_relBatchedE Φ m₀ m₁ bound ρBound K φF b hn stmtIn witOut h)

end ArkLib.Lattices.Ajtai.InnerOuter

/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tobias Rothmann, Pablo Martín Vinuelas
-/
import ArkLib.Commitments.Functional.Hachi.ZeroCheck.Constraints

/-!
  # Batching bridge — Hachi Eqs. (22)–(23)

  A zero-round reduction between two readings of the lift's claims:

  * `relLiftE` — `w̃` opens `t`, the per-row `α`-evaluated constraints hold, `w̃` is short
    (`RingSwitch/Reduction.lean`);
  * `relBatchedE` — `w̃` opens `t`, the batched polynomials `H₀^{w̃}` and `H_α^{w̃}` are identically
    zero (Eqs. (22)–(23), `ZeroCheck/Constraints.lean`), and `w̃` is short.

  The statement and witness are unchanged (`ReduceClaim` at `mapStmt := id`); only the reading of
  the claims changes, which separates the batching algebra from the Kronecker root counting of the
  zero-check. The `liftShort` conjunct is carried through unchanged, since it is the shortness
  precondition of the commitment's weak binding (`LiftCom.collision_mem`) used later by the
  zero-check's extractor.

  The reduction's content is the pull-back `mem_relLiftE_of_relBatchedE` from `relBatchedE` to
  `relLiftE`: the per-row equation is recovered from `H_α ≡ 0` via `MvPolynomial.MLE_eq_zero_iff`
  and `hAlphaEvals_rowPoint`, and the remaining conjuncts are carried over directly. Its only
  hypothesis is the row-encoding arity bound `n ≤ 2 ^ m₁`.

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
variable (m₀ m₁ : ℕ) (bound rBound : ℕ)
variable {ι : Type} {oSpec : OracleSpec ι} {σ : Type}

/-- The batched relation (Hachi Eqs. (22)–(23) as polynomial identities): `w̃` opens `t`, is short
(`liftShort`), the range polynomial `H₀^{w̃}` and the linear-constraint polynomial `H_α^{w̃}` are
both identically zero, and `bound ≤ rlin.bound`. This is the zero-check's input relation. -/
def relBatched (K : LiftCom (LiftedWitness Φ μ n) E (liftShort Φ bound rBound))
    (φF : ZMod q →+* F) (b : ℕ) :
    Set (LiftStatement Φ K.TCom F n μ × LiftedWitness Φ μ n) :=
  {p |
    K.com p.2 = p.1.2.1 ∧
    liftShort Φ bound rBound p.2 ∧
    hZero Φ m₀ φF b p.2 = 0 ∧
    hAlpha Φ m₁ φF b p.1.1 p.1.2.2 p.2 = 0 ∧
    bound ≤ p.1.1.bound}

/-- `relBatched` extended with the escape branch (`.inr e` requires `e ∈ K.esc`); the zero-check's
input relation. -/
def relBatchedE (K : LiftCom (LiftedWitness Φ μ n) E (liftShort Φ bound rBound))
    (φF : ZMod q →+* F) (b : ℕ) :
    Set (LiftStatement Φ K.TCom F n μ × (LiftedWitness Φ μ n ⊕ E)) :=
  (relBatched Φ m₀ m₁ bound rBound K φF b).withEscape K.esc

omit [NeZero q] [IsCyclotomic Φ] in
/-- The batched identities imply the lift's per-row claims; escapes pass through.

The per-row equation is recovered from `H_α ≡ 0`: by `MvPolynomial.MLE_eq_zero_iff` every
Boolean-point coefficient `hAlphaEvals` vanishes, and by `hAlphaEvals_rowPoint` the coefficient at
`rowPoint i` is row `i`'s `α`-evaluated lift defect, giving the row equation of `relLift`. The
`K.com`, `liftShort`, and bound conjuncts are shared between the two relations. The range identity
`H₀ ≡ 0` is not needed here, since shortness is asserted directly. The hypothesis `hn : n ≤ 2 ^ m₁`
is the row-encoding bound of the batching cube. -/
theorem mem_relLiftE_of_relBatchedE
    (K : LiftCom (LiftedWitness Φ μ n) E (liftShort Φ bound rBound))
    (φF : ZMod q →+* F) (b : ℕ) (hn : n ≤ 2 ^ m₁)
    (X : LiftStatement Φ K.TCom F n μ) (w : LiftedWitness Φ μ n ⊕ E)
    (h : (X, w) ∈ relBatchedE Φ m₀ m₁ bound rBound K φF b) :
    (X, w) ∈ relLiftE Φ bound rBound K φF := by
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

/-- The batching bridge packaged as a `CWSSPackage`: a zero-round `ReduceClaim` at `mapStmt := id`
reducing `relLiftE` to `relBatchedE` with no soundness error, its correctness supplied by
`mem_relLiftE_of_relBatchedE`. -/
def batchPackage (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (K : LiftCom (LiftedWitness Φ μ n) E (liftShort Φ bound rBound))
    (φF : ZMod q →+* F) (b : ℕ) (hn : n ≤ 2 ^ m₁) :
    CWSSPackage init impl
      (LiftStatement Φ K.TCom F n μ) (LiftedWitness Φ μ n ⊕ E)
      (LiftStatement Φ K.TCom F n μ) (LiftedWitness Φ μ n ⊕ E)
      (!p[] : ProtocolSpec 0) where
  verifier := ReduceClaim.verifier oSpec id
  struct := CWSSStructure.ofIsEmpty
  relIn := relLiftE Φ bound rBound K φF
  relOut := relBatchedE Φ m₀ m₁ bound rBound K φF b
  isPure := ⟨fun stmt _ => stmt, fun _ _ => rfl⟩
  isCWSS := ReduceClaim.verifier_coordinateWiseSpecialSound
    (relIn := relLiftE Φ bound rBound K φF)
    (relOut := relBatchedE Φ m₀ m₁ bound rBound K φF b)
    (mapWitInv := fun _ w => w) (D := CWSSStructure.ofIsEmpty)
    (fun stmtIn witOut h =>
      mem_relLiftE_of_relBatchedE Φ m₀ m₁ bound rBound K φF b hn stmtIn witOut h)

end ArkLib.Lattices.Ajtai.InnerOuter

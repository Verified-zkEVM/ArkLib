/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/
module

public import ArkLib.ProofSystem.Fri.Spec.Extraction.Cost
public import ArkLib.ToCompPoly.Univariate.ArithmeticEvaluationBound
public import ArkLib.ToCompPoly.Univariate.ArithmeticInterpolationBound

/-!
# Folding-check profile envelopes

The bounds include generated block points, cached-array accesses, coefficient interpolation,
power-sum evaluation, and the final equality test of each executed round check.
-/

@[expose] public section

namespace Fri.Spec.Extractor
open Domain OracleComp OracleSpec CompPoly
variable {F : Type} [NonBinaryField F] [Fintype F] [DecidableEq F]
variable {n k : ℕ} {ω : SmoothCosetFftDomain n F}
variable (s : Fin (k + 1) → ℕ+) (o : ∀ j, FinalOracleStatement s ω j)
variable (α : FinalStatement F k)

/-- A projected query uses one multiplication and tick per preceding fold bit. -/
theorem profile_projectedPoint_apply (hs : (∑ j, (s j).val) ≤ n) (i : Fin (k + 1))
    (x : (ω.subdomain 0).toFinset) (kind : CostKind) :
    (profile s o α (projectedPoint s o α hs i x)).2 kind =
      if kind = .inl .mul ∨ kind = .inl .metadata then foldingPrefix s i.castSucc else 0 := by
  cases kind with
  | inl kind => cases kind <;>
      simp [projectedPoint, Arithmetic.profileArithmetic_squareIter, embedArithmeticCost]
  | inr kind => cases kind <;> simp [projectedPoint, embedArithmeticCost]

/-- A generated block node uses a binary power and one multiplication. -/
theorem profile_generateBlockNode_apply_le (hs : (∑ j, (s j).val) ≤ n)
    (gen : Generator ω) (i : Fin (k + 1)) (roundGen : RoundGenerator s gen i)
    (x : (ω.subdomain 0).toFinset)
    (projected : {a : F // a = (QueryRound.queryPoint s hs i x).val})
    (j : Fin (2 ^ (s i).val)) (kind : CostKind) :
    (profile s o α (generateBlockNode s hs o α gen i roundGen x projected j)).2 kind ≤
      if kind = .inl .mul then 2 * (s i).val + 1
      else if kind = .inl .metadata then (s i).val else 0 := by
  have hp := Arithmetic.profileArithmetic_powerBits_apply_le roundGen.root (s i).val
    j.val j.isLt
  cases kind with
  | inl kind =>
    have h := hp kind
    cases kind <;>
      simp [generateBlockNode, profile_bind, embedArithmeticCost,
        arithmeticCost, ArithmeticOp.costKind] at h ⊢ <;> omega
  | inr kind => simp [generateBlockNode, profile_bind, embedArithmeticCost]

/-- A generated block pays for each node and its array traversal. -/
theorem profile_blockNodes_apply_le (hs : (∑ j, (s j).val) ≤ n) (gen : Generator ω)
    (i : Fin (k + 1)) (roundGen : RoundGenerator s gen i)
    (x : (ω.subdomain 0).toFinset)
    (projected : {a : F // a = (QueryRound.queryPoint s hs i x).val}) (kind : CostKind) :
    (profile s o α (blockNodes s o α hs gen i roundGen x projected)).2 kind ≤
      2 ^ (s i).val * (if kind = .inl .mul then 2 * (s i).val + 1
        else if kind = .inl .metadata then (s i).val else 0) +
        if kind = .inl .metadata then 2 ^ (s i).val + 1 else 0 := by
  apply profile_arrayProgram_apply_le
  intro j
  simpa [profile_bind] using
    profile_generateBlockNode_apply_le s o α hs gen i roundGen x projected j kind

/-- A block-value array reads one cached node and one retained word at every index. -/
theorem profile_blockValues_apply (hs : (∑ j, (s j).val) ≤ n) (i : Fin (k + 1))
    (x : (ω.subdomain 0).toFinset)
    (nodes : {a : Array F // a = Array.ofFn (fun j : Fin (2 ^ (s i).val) ↦
      (blockNode s hs i x j).val)}) (kind : CostKind) :
    (profile s o α (blockValues s o α hs i x nodes)).2 kind =
      if kind = .inr .wordRead ∨ kind = .inl .nodeRead then 2 ^ (s i).val
      else if kind = .inl .metadata then 2 ^ (s i).val + 1 else 0 := by
  cases kind with
  | inl kind => cases kind <;>
      simp [blockValues, profile_arrayProgram_apply, profile_bind, embedArithmeticCost,
        arithmeticCost, ArithmeticOp.costKind, instructionCost, AccessOp.costKind]
  | inr kind => cases kind <;>
      simp [blockValues, profile_arrayProgram_apply, profile_bind, embedArithmeticCost,
        instructionCost, AccessOp.costKind]

/-- The folded-value profile pays for squaring and either a successor read or final evaluation. -/
def nextValueProfileBound (s : Fin (k + 1) → ℕ+) (d : ℕ) (i : Fin (k + 1))
    (kind : CostKind) : ℕ :=
  (if kind = .inl .mul ∨ kind = .inl .metadata then (s i).val else 0) +
    if i.val < k then (if kind = .inr .wordRead then 1 else 0)
    else embedArithmeticCost (Arithmetic.evaluationProfileBound d) kind

/-- Folded-value evaluation uses at most the guarded final coefficient count. -/
theorem profile_nextValue_apply_le (hs : (∑ j, (s j).val) ≤ n) {d : ℕ+}
    (input : PreparedInput s o α d) (i : Fin (k + 1))
    (x : (ω.subdomain 0).toFinset)
    (projected : {a : F // a = (QueryRound.queryPoint s hs i x).val}) (kind : CostKind) :
    (profile s o α (nextValue s o α hs input i x projected)).2 kind ≤
      nextValueProfileBound s d.val i kind := by
  have hsize : input.coefficients.size ≤ d.val := by
    rw [input.coefficients_eq]
    exact CPolynomial.size_le_of_natDegree_lt input.polynomial input.degree_lt
  by_cases hi : i.val < k
  · cases kind with
    | inl kind => cases kind <;>
        simp [nextValue, hi, nextValueProfileBound, profile_bind,
          Arithmetic.profileArithmetic_squareIter, embedArithmeticCost,
          instructionCost, AccessOp.costKind]
    | inr kind => cases kind <;>
        simp [nextValue, hi, nextValueProfileBound, profile_bind,
          embedArithmeticCost, instructionCost, AccessOp.costKind]
  · let t := (profile s o α
      (liftComp (Arithmetic.squareIter projected.val (s i).val) _)).1
    have heval := Arithmetic.profileArithmetic_evalRaw_apply_le input.coefficients t.val d.val hsize
    cases kind with
    | inl kind =>
      have h := Nat.add_le_add_left (heval kind)
        (if kind = .mul ∨ kind = .metadata then (s i).val else 0)
      cases kind <;>
        simpa [nextValue, hi, nextValueProfileBound, profile_bind,
          Arithmetic.profileArithmetic_squareIter, embedArithmeticCost, t] using h
    | inr kind => cases kind <;>
        simp [nextValue, hi, nextValueProfileBound, profile_bind, embedArithmeticCost]

/-- Reading a cached root contributes one node-array access. -/
theorem profile_readRoundGenerator_apply {d : ℕ+} (input : PreparedInput s o α d)
    (i : Fin (k + 1)) (kind : CostKind) :
    (profile s o α (readRoundGenerator s o α input i)).2 kind =
      if kind = .inl .nodeRead then 1 else 0 := by
  cases kind with
  | inl kind => cases kind <;>
      simp [readRoundGenerator, embedArithmeticCost,
        arithmeticCost, ArithmeticOp.costKind]
  | inr kind => simp [readRoundGenerator, embedArithmeticCost]

/-- Reading a cached challenge contributes one field-value array access. -/
theorem profile_readCachedChallenge_apply {d : ℕ+} (input : PreparedInput s o α d)
    (i : Fin (k + 1)) (kind : CostKind) :
    (profile s o α (readCachedChallenge s o α input i)).2 kind =
      if kind = .inl .valueRead then 1 else 0 := by
  cases kind with
  | inl kind => cases kind <;>
      simp [readCachedChallenge, embedArithmeticCost,
        arithmeticCost, ArithmeticOp.costKind]
  | inr kind => simp [readCachedChallenge, embedArithmeticCost]

/-- The block-node envelope counts binary powers and array traversal ticks. -/
def blockNodesProfileBound (e : ℕ) (kind : CostKind) : ℕ :=
  2 ^ e * (if kind = .inl .mul then 2 * e + 1
    else if kind = .inl .metadata then e else 0) +
    if kind = .inl .metadata then 2 ^ e + 1 else 0

/-- The block-value envelope counts cached-node reads, retained-word reads, and traversal ticks. -/
def blockValuesProfileBound (e : ℕ) (kind : CostKind) : ℕ :=
  if kind = .inr .wordRead ∨ kind = .inl .nodeRead then 2 ^ e
  else if kind = .inl .metadata then 2 ^ e + 1 else 0

/-- The local-check envelope counts caches, point generation, interpolation and evaluations. -/
def roundProfileBound {k : ℕ} (s : Fin (k + 1) → ℕ+) (d : ℕ)
    (i : Fin (k + 1)) (kind : CostKind) : ℕ :=
  (if kind = .inl .nodeRead then 1 else 0) +
  ((if kind = .inl .valueRead then 1 else 0) +
  ((if kind = .inl .mul ∨ kind = .inl .metadata then foldingPrefix s i.castSucc else 0) +
  (blockNodesProfileBound (s i).val kind +
  (blockValuesProfileBound (s i).val kind +
  (embedArithmeticCost (Arithmetic.interpolationProfileBound (2 ^ (s i).val)) kind +
  (embedArithmeticCost (Arithmetic.evaluationProfileBound (2 ^ (s i).val)) kind +
  (nextValueProfileBound s d i kind +
  (if kind = .inl .eq then 1 else 0))))))))

/-- Every primitive coordinate of a local check satisfies the explicit round envelope. -/
theorem profile_checkRoundProgram_apply_le (hs : (∑ j, (s j).val) ≤ n) {d : ℕ+}
    (input : PreparedInput s o α d) (i : Fin (k + 1))
    (x : (ω.subdomain 0).toFinset) (kind : CostKind) :
    (profile s o α (checkRoundProgram s o α hs input i x)).2 kind ≤
      roundProfileBound s d.val i kind := by
  unfold checkRoundProgram roundProfileBound
  refine profile_bind_apply_le s o α _ _ kind _ _ ?_ ?_
  · exact (profile_readRoundGenerator_apply s o α input i kind).le
  intro root
  refine profile_bind_apply_le s o α _ _ kind _ _ ?_ ?_
  · exact (profile_readCachedChallenge_apply s o α input i kind).le
  intro challenge
  refine profile_bind_apply_le s o α _ _ kind _ _ ?_ ?_
  · exact (profile_projectedPoint_apply s o α hs i x kind).le
  intro projected
  refine profile_bind_apply_le s o α _ _ kind _ _ ?_ ?_
  · exact profile_blockNodes_apply_le s o α hs input.generator i root x projected kind
  intro nodes
  refine profile_bind_apply_le s o α _ _ kind _ _ ?_ ?_
  · exact (profile_blockValues_apply s o α hs i x nodes kind).le
  intro values
  refine profile_bind_apply_le s o α _ _ kind _ _ ?_ ?_
  · exact profile_liftComp_apply_le s o α _ _
      (Arithmetic.profileArithmetic_interpolate_le nodes.val values.val (2 ^ (s i).val)) kind
  intro p
  have hsize : p.val.val.size ≤ 2 ^ (s i).val := by
    rw [p.property]
    exact CPolynomial.CLagrange.size_interpolate_univ_le _ _
  refine profile_bind_apply_le s o α _ _ kind _ _ ?_ ?_
  · exact profile_liftComp_apply_le s o α _ _
      (Arithmetic.profileArithmetic_evalRaw_apply_le p.val.val challenge.val
        (2 ^ (s i).val) hsize) kind
  intro y
  refine profile_bind_apply_le s o α _ _ kind _ _ ?_ ?_
  · exact profile_nextValue_apply_le s o α hs input i x projected kind
  intro beta
  refine profile_bind_apply_le s o α _ _ kind
    (if kind = .inl .eq then 1 else 0) 0 ?_ ?_
  · cases kind with
    | inl kind => cases kind <;>
        simp [embedArithmeticCost, arithmeticCost, ArithmeticOp.costKind]
    | inr kind => simp [embedArithmeticCost]
  intro result
  simp

end Fri.Spec.Extractor

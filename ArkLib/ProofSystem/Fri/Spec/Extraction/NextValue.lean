/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
module

public import ArkLib.ProofSystem.Fri.Spec.Extraction.BlockArrays
public import ArkLib.ProofSystem.Fri.Spec.Extraction.Prepare
public import ArkLib.ToCompPoly.Univariate.ArithmeticEvaluation

/-!
# Measured values after folding

Non-final rounds read the next retained word at its generated projected point. The final round
evaluates cached final-polynomial coefficients through the measured power-sum program.
-/

@[expose] public section

namespace Fri.Spec.Extractor
open Domain OracleComp OracleSpec CompPoly
variable {F : Type} [NonBinaryField F] [Fintype F] [DecidableEq F]
variable {n k : ℕ} {ω : SmoothCosetFftDomain n F}
variable (s : Fin (k + 1) → ℕ+) (o : ∀ j, FinalOracleStatement s ω j)
variable (α : FinalStatement F k)

/-- Read the next word value, or evaluate the cached final coefficients after the last fold. -/
def nextValue (hs : (∑ j, (s j).val) ≤ n) {d : ℕ+}
    (input : PreparedInput s o α d) (i : Fin (k + 1))
    (x : (ω.subdomain 0).toFinset)
    (projected : {a : F // a = (QueryRound.queryPoint s hs i x).val}) :
    OracleComp (InstructionSpec s o α)
      {a : F // a = committedFunction s o i.succ (x.val ^ (2 ^ foldingPrefix s i.succ))} := do
  let t ← liftComp (Arithmetic.squareIter projected.val (s i).val) _
  have ht : t.val = x.val ^ (2 ^ foldingPrefix s i.succ) := by
    rw [t.property, projected.property]
    change (x.val ^ (2 ^ foldingPrefix s i.castSucc)) ^ (2 ^ (s i).val) = _
    rw [foldingPrefix_succ, pow_add, pow_mul]
  if hi : i.val < k then
    let j : Fin (k + 1) := ⟨i.val + 1, by omega⟩
    have hj : j.castSucc = i.succ := Fin.ext rfl
    let q : (ω.subdomain (foldingPrefix s j.castSucc)).toFinset := ⟨t.val, by
      rw [hj, ht]
      exact CosetFftDomainClass.pow_mem_subdomain_of_mem_subdomain_0_toFinset
        ((foldingPrefix_le s i.succ).trans hs) x.property⟩
    let a ← readWord s o α j q
    pure ⟨a.val, by
      rw [a.property]
      calc
        committedWord s o j q = committedFunction s o j.castSucc t.val :=
          (committedFunction_castSucc s o j q).symm
        _ = committedFunction s o i.succ (x.val ^ (2 ^ foldingPrefix s i.succ)) := by
          rw [hj, ht]⟩
  else
    let a ← liftComp (Arithmetic.evalRaw input.coefficients t.val) _
    pure ⟨a.val, by
      rw [a.property, input.coefficients_eq, CPolynomial.Raw.eval_val]
      rw [input.polynomial_eq, ht]
      have hiLast : i = Fin.last k := Fin.ext (by simp; omega)
      subst i
      rw [Fin.succ_last, committedFunction_last]⟩

end Fri.Spec.Extractor

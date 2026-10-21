/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
module

public import ArkLib.ProofSystem.Fri.Spec.Extraction.NextValue
public import ArkLib.ToCompPoly.Univariate.ArithmeticInterpolation

/-!
# Measured checks of a retained folding history

Local interpolation and evaluation implement the verifier's round check on generated nodes.
The position check stops at the first failing round and certifies the complete acceptance predicate.
-/

@[expose] public section

namespace RoundConsistency
variable {F : Type} [Field F] [DecidableEq F]

private theorem roundConsistencyCheck_cast_get {A : Type} (γ β : F) (xs : List A)
    (f : A → F × F) {m : ℕ} (hlen : xs.length = m) :
    roundConsistencyCheck γ (fun j : Fin m ↦ f (xs.get (j.cast hlen.symm))) β =
      roundConsistencyCheck γ (xs.map f).get β := by
  subst m
  rw [roundConsistencyCheck_map_get]
  rfl

end RoundConsistency

namespace Fri.Spec.Extractor
open Domain OracleComp OracleSpec CompPoly
variable {F : Type} [NonBinaryField F] [Fintype F] [DecidableEq F]
variable {n k : ℕ} {ω : SmoothCosetFftDomain n F}
variable (s : Fin (k + 1) → ℕ+)

private theorem interpolate_blockArrays_eq_roundConsistencyCheck
    (hs : (∑ j, (s j).val) ≤ n)
    (o : ∀ j, FinalOracleStatement s ω j) (α β : F) (i : Fin (k + 1))
    (x : (ω.subdomain 0).toFinset) :
    let nodes := Array.ofFn (fun j : Fin (2 ^ (s i).val) ↦ (blockNode s hs i x j).val)
    let values := Array.ofFn (fun j : Fin (2 ^ (s i).val) ↦
      committedWord s o i (blockNode s hs i x j))
    (CPolynomial.CLagrange.interpolate Finset.univ
      (fun j : Fin (2 ^ (s i).val) ↦ nodes[j.val]?.getD 0)
      (fun j : Fin (2 ^ (s i).val) ↦ values[j.val]?.getD 0)).eval α == β =
      RoundConsistency.roundConsistencyCheck α
        ((QueryRound.queryBlock s hs i x).map (fun q ↦ (q.val, committedWord s o i q))).get β := by
  simp only [Array.getElem?_ofFn, Fin.is_lt, dite_eq_left, Option.getD_some]
  exact RoundConsistency.roundConsistencyCheck_cast_get α β
    (QueryRound.queryBlock s hs i x) (fun q ↦ (q.val, committedWord s o i q))
    (QueryRound.queryBlock_length s hs i x)


/-- Check one actual retained folding transition using generated nodes and charged arithmetic. -/
def checkRoundProgram (o : ∀ j, FinalOracleStatement s ω j) (α : FinalStatement F k)
    (hs : (∑ j, (s j).val) ≤ n) {d : ℕ+}
    (input : PreparedInput s o α d) (i : Fin (k + 1))
    (x : (ω.subdomain 0).toFinset) :
    OracleComp (InstructionSpec s o α) {b : Bool // b =
      simulateQ (OracleInterface.simOracle0 (FinalOracleStatement s ω) o)
        (QueryRound.checkRound s hs (finalPolynomial s o) (α i) i x)} := do
  let root ← readRoundGenerator s o α input i
  let challenge ← readCachedChallenge s o α input i
  let projected ← projectedPoint s o α hs i x
  let nodes ← blockNodes s o α hs input.generator i root x projected
  let values ← blockValues s o α hs i x nodes
  let p ← liftComp (Arithmetic.interpolate nodes.val values.val (2 ^ (s i).val)) _
  let y ← liftComp (Arithmetic.evalRaw p.val.val challenge.val) _
  let β ← nextValue s o α hs input i x projected
  let e ← liftComp (Arithmetic.eq y.val β.val) _
  pure ⟨e.val, by
    rw [e.property, y.property, CPolynomial.Raw.eval_val]
    rw [p.property, nodes.property, values.property, challenge.property, β.property,
      QueryRound.eval_checkRound]
    rw [← QueryRound.eval_queryNext s hs o i x]
    rw [← interpolate_blockArrays_eq_roundConsistencyCheck s hs o (α i) _ i x]
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq, beq_iff_eq]⟩


/-- Check an explicit list of folding rounds, stopping at its first failing transition. -/
def checkRounds (o : ∀ j, FinalOracleStatement s ω j) (α : FinalStatement F k)
    (hs : (∑ j, (s j).val) ≤ n) {d : ℕ+} (input : PreparedInput s o α d)
    (x : (ω.subdomain 0).toFinset) :
    (indices : List (Fin (k + 1))) → OracleComp (InstructionSpec s o α)
      {b : Bool // b = true ↔ ∀ i ∈ indices,
        simulateQ (OracleInterface.simOracle0 (FinalOracleStatement s ω) o)
          (QueryRound.checkRound s hs (finalPolynomial s o) (α i) i x) = true}
  | [] => pure ⟨true, by simp⟩
  | i :: indices => do
    liftComp (Arithmetic.tick (F := F)) _
    let b ← checkRoundProgram s o α hs input i x
    if hb : b.val = true then
      let rest ← checkRounds o α hs input x indices
      have hi := b.property.symm.trans hb
      pure ⟨rest.val, by simpa [hi] using rest.property⟩
    else
      pure ⟨false, by
        simp only [Bool.false_eq_true, false_iff]
        intro hall
        apply hb
        rw [b.property]
        exact hall i List.mem_cons_self⟩

/-- Check all folding rounds at one generated initial-domain position, stopping at failure. -/
def checkPosition (o : ∀ j, FinalOracleStatement s ω j) (α : FinalStatement F k)
    (hs : (∑ j, (s j).val) ≤ n) {d : ℕ+} (input : PreparedInput s o α d)
    (z : Fin (2 ^ n)) (x : {q : (ω.subdomain 0).toFinset // q = initialQuery z}) :
    OracleComp (InstructionSpec s o α)
      {b : Bool // b = true ↔ z ∈ acceptingQueries s hs o α} := do
  let b ← checkRounds s o α hs input x.val (List.finRange (k + 1))
  pure ⟨b.val, by
    classical
    simpa [acceptingQueries, x.property] using b.property⟩

end Fri.Spec.Extractor

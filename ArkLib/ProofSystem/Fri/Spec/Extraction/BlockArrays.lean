/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/
module

public import ArkLib.ProofSystem.Fri.Spec.Extraction.Generator
public import ArkLib.ProofSystem.Fri.Spec.Extraction.Readers
public import ArkLib.ProofSystem.Fri.Spec.Extraction.Traversal

/-!
# Generated folding blocks

The node arrays follow the verifier's finite block order. Word reads use these generated field
points directly, and both arrays carry erased certificates for the retained history.
-/

@[expose] public section

namespace Fri.Spec.Extractor
open Domain OracleComp OracleSpec CompPoly
variable {F : Type} [NonBinaryField F] [Fintype F] [DecidableEq F]
variable {n k : ℕ} {ω : SmoothCosetFftDomain n F}
variable (s : Fin (k + 1) → ℕ+) (o : ∀ j, FinalOracleStatement s ω j)
variable (α : FinalStatement F k)

/-- Compute the projected query point using charged squarings. -/
def projectedPoint (hs : (∑ j, (s j).val) ≤ n) (i : Fin (k + 1))
    (x : (ω.subdomain 0).toFinset) :
    OracleComp (InstructionSpec s o α)
      {a : F // a = (QueryRound.queryPoint s hs i x).val} := do
  let a ← liftComp (Arithmetic.squareIter x.val (foldingPrefix s i.castSucc)) _
  pure ⟨a.val, a.property⟩

/-- Generate all block nodes, preserving the verifier's FFT enumeration. -/
def blockNodes (hs : (∑ j, (s j).val) ≤ n) (gen : Generator ω)
    (i : Fin (k + 1)) (roundGen : RoundGenerator s gen i)
    (x : (ω.subdomain 0).toFinset)
    (projected : {a : F // a = (QueryRound.queryPoint s hs i x).val}) :
    OracleComp (InstructionSpec s o α)
      {a : Array F // a = Array.ofFn (fun j : Fin (2 ^ (s i).val) ↦
        (blockNode s hs i x j).val)} :=
  arrayProgram s o α _ fun j ↦ do
    let q ← generateBlockNode s hs o α gen i roundGen x projected j
    pure ⟨q.val.val, congrArg Subtype.val q.property⟩

/-- Read the retained word at each cached block node. -/
def blockValues (hs : (∑ j, (s j).val) ≤ n) (i : Fin (k + 1))
    (x : (ω.subdomain 0).toFinset)
    (nodes : {a : Array F // a = Array.ofFn (fun j : Fin (2 ^ (s i).val) ↦
      (blockNode s hs i x j).val)}) :
    OracleComp (InstructionSpec s o α)
      {a : Array F // a = Array.ofFn (fun j : Fin (2 ^ (s i).val) ↦
        committedWord s o i (blockNode s hs i x j))} :=
  arrayProgram s o α _ fun j ↦ do
    let a ← liftComp (Arithmetic.nodeRead nodes.val j.val) _
    have ha : a.val = (blockNode s hs i x j).val := by
      rw [a.property, nodes.property]
      simp
    let q : (ω.subdomain (foldingPrefix s i.castSucc)).toFinset :=
      ⟨a.val, by rw [ha]; exact (blockNode s hs i x j).property⟩
    let y ← readWord s o α i q
    pure ⟨y.val, by rw [y.property]; congr 1; exact Subtype.ext ha⟩

end Fri.Spec.Extractor

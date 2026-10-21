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
# Guarded extractor preparation

The final polynomial degree is checked before any coefficient, domain, or challenge traversal.
Successful preparation caches its coefficients, domain generators, and folding challenges.
-/

@[expose] public section

namespace Fri.Spec.Extractor
open Domain OracleComp OracleSpec CompPoly
variable {F : Type} [NonBinaryField F] [Fintype F] [DecidableEq F]
variable {n k : ℕ} {ω : SmoothCosetFftDomain n F}
variable (s : Fin (k + 1) → ℕ+) (o : ∀ j, FinalOracleStatement s ω j)
variable (α : FinalStatement F k)

/-- The guarded polynomial and the immutable field arrays used throughout extraction. -/
structure PreparedInput (d : ℕ+) where
  polynomial : CPolynomial F
  polynomial_eq : polynomial = finalPolynomial s o
  degree_lt : polynomial.natDegree < d.val
  coefficients : Array F
  coefficients_eq : coefficients = polynomial.val
  generator : Generator ω
  roots : Array F
  roots_eq : roots = Array.ofFn (fun i : Fin (k + 1) ↦
    generator.ratio ^ (2 ^ (n - (s i).val)))
  challenges : Array F
  challenges_eq : challenges = Array.ofFn α

/-- Reject oversized final polynomials before traversing coefficients or accessing other inputs. -/
def prepareInputs (d : ℕ+) :
    OracleComp (InstructionSpec s o α) (Option (PreparedInput s o α d)) := do
  let p ← readFinalPolynomial s o α
  let degree ← readDegree s o α p.val
  if hd : degree.val < d.val then
    let coefficients ← copyCoefficients s o α p.val.val
    let gen ← initGenerator s o α
    let roots ← arrayProgram s o α
      (fun i : Fin (k + 1) ↦ gen.ratio ^ (2 ^ (n - (s i).val))) fun i ↦ do
        let g ← initRoundGenerator s o α gen i
        pure ⟨g.root, g.root_eq⟩
    let challenges ← arrayProgram s o α α (readChallenge s o α)
    pure (some {
      polynomial := p.val
      polynomial_eq := p.property
      degree_lt := by simpa [degree.property] using hd
      coefficients := coefficients.val
      coefficients_eq := coefficients.property
      generator := gen
      roots := roots.val
      roots_eq := roots.property
      challenges := challenges.val
      challenges_eq := challenges.property })
  else
    pure none

/-- Read one cached block generator through its charged array instruction. -/
def readRoundGenerator {d : ℕ+} (input : PreparedInput s o α d) (i : Fin (k + 1)) :
    OracleComp (InstructionSpec s o α) (RoundGenerator s input.generator i) := do
  let a ← liftComp (Arithmetic.nodeRead input.roots i.val) _
  pure ⟨a.val, by
    simpa only [input.roots_eq, Array.getElem?_ofFn, Fin.is_lt, dite_eq_left,
      Option.getD_some] using a.property⟩

/-- Read one cached folding challenge through its charged array instruction. -/
def readCachedChallenge {d : ℕ+} (input : PreparedInput s o α d) (i : Fin (k + 1)) :
    OracleComp (InstructionSpec s o α) {a : F // a = α i} := do
  let a ← liftComp (Arithmetic.valueRead input.challenges i.val) _
  pure ⟨a.val, by
    simpa only [input.challenges_eq, Array.getElem?_ofFn, Fin.is_lt, dite_eq_left,
      Option.getD_some] using a.property⟩

end Fri.Spec.Extractor

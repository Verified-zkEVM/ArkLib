/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Commitments.Functional.KZG.Generic.Translation
public import ArkLib.Commitments.Functional.KZG.AGM.FirstReduction
public import VCVio.CryptoFoundations.GroupModel.PairingMetadata
public import VCVio.CryptoFoundations.GroupModel.GenericPairing

/-!
# Generic KZG recovery program

The program forwards all handle operations unchanged and tracks source coefficients using
zero-valued metadata. After the adversary finishes, each candidate costs one source scaling;
equality tests and scalar computations are free. No setup group operations are needed.

References: [KZG10TR]; Shoup, EUROCRYPT 1997; Maurer, IMA 2005;
Fuchsbauer–Kiltz–Loss, *The Algebraic Group Model and its Applications*, CRYPTO 2018.
-/

@[expose] public section

open CompPoly OracleComp OracleSpec GroupModel GroupModel.Interaction

namespace KZG.Generic

attribute [local implicit_reducible] spec handleSpec

variable {F D : Type} [Field F] [DecidableEq F]

/-- Test candidates using the generator and trapdoor handles at indices zero and one in `G₂`. -/
def testRoots : List F → OracleComp (genSpec F pairingSig) F
  | [] => pure 0
  | r :: rs => do
      let h ← (genSpec F pairingSig).query (.inl (.smul .g₂ r 0))
      let ok : Bool ← (genSpec F pairingSig).query (.inl (.eq .g₂ h 1))
      if ok = true then pure r else testRoots rs

/-- Run the handle program while retaining only scalar coefficient metadata. -/
def reductionProgram (n : ℕ) (roots : CPolynomial F → List F) (claims : D → List (F × F))
    (p : OracleComp (adversarySpec F) (Message D (fun _ : PSort => Handle))) :
    Pairing.Tracked F (fun _ : Bool => F) F → OracleComp (genSpec F pairingSig) F :=
  OracleComp.recOn p
    (fun msg st =>
      let out := explain st.1 (Pairing.sourceMessage msg)
      testRoots (AGM.candidatesFirstData (n := n) roots
        (fun i j => (((out.coefficients false)[i]?).getD [])[j.val]?.getD 0)
        (claims out.value.data)))
    (fun q _ next st => match q with
      | .inl q => do
          let a ← (genSpec F pairingSig).query (.inl q)
          next a (Pairing.step (0 : F →ₗ[F] F →ₗ[F] F) q st).2
      | .inr (.inl _) => next () st
      | .inr (.inr (.inl k)) => do
          let a ← (genSpec F pairingSig).query (.inr k)
          next a st
      | .inr (.inr (.inr q)) => q.data.elim)

/-- Initial metadata consists of the key lengths and their unit coefficient vectors. -/
def initialMetadata (n : ℕ) : Pairing.Tracked F (fun _ : Bool => F) F :=
  ((fun b => List.range (if b then 2 else n + 1),
    trackInputs (fun b => List.replicate (if b then 2 else n + 1) (0 : F))), [])

/-- The explicit generic `(n, 1)`-PairingDLog program implementing first-claim recovery. -/
def program (n : ℕ) (roots : CPolynomial F → List F) (claims : D → List (F × F))
    (A : Adversary F D) : OracleComp (genSpec F pairingSig) F :=
  reductionProgram n roots claims (A (input n)) (initialMetadata n)

end KZG.Generic

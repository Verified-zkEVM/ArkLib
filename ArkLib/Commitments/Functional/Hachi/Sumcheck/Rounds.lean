/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tobias Rothmann
-/
import ArkLib.Commitments.Functional.Hachi.Sumcheck.Bridge
import ArkLib.OracleReduction.Security.CoordinateWiseSpecialSoundness.Guarded

/-!
  # Paired sumcheck rounds — Hachi Figure 6 / Lemma 11 — skeleton (milestone F7)

  The sumcheck loop of Hachi §4.3: `m₀` rounds, each reducing the pair of
  partial-hypercube-sum claims (`roundRel i`, `ZeroCheck/Constraints.lean`) by one variable.

  ## Paired rounds (design D9)

  Figure 7 runs the `H₀`- and `H_α`-sumchecks with **shared challenges**: each round's message
  is the *pair* of univariate round polynomials `(g_i^{(0)}, g_i^{(α)})` (degrees
  `roundDegZero b = 2b` resp. `roundDegAlpha = 2`), followed by one scalar challenge
  `a_i ← F` — the `pSpecScalar (RoundMsg F b) F` wire format.

  ## Guarded round verifiers (designs D6/R10)

  The round check `g_i(0) + g_i(1) = target_{i−1}` (for both components) reads the *previous*
  target, which the next round's statement **drops** — so it cannot live in the output relation,
  and a pure-with-dummy convention destroys extractability (all siblings of a tree node share
  the message `g_i`, so a failed check would collapse every branch onto the same dummy — plan
  risk R10). The round verifier is therefore **guarded**: `failure` on a failed check, which is
  exactly the paper's "valid transcripts" premise for Lemma 11.

  ## Per-round soundness (Lemma 11) and the loop

  Per-round CWSS at `k = max (2b) 2 + 1` (plain special soundness, `scalarStructure`): the
  branches of a tree node share the message pair; either two branch witnesses differ (binding
  escape via `K.collision_mem`) or the shared `w̃` makes
  `T ↦ ∑_{x} H(prefix, T, x) − g_i(T)` a degree-`≤ deg` polynomial with `deg + 1` distinct
  roots, hence zero; evaluating at `0, 1` and summing, the **guard's** `g_i(0) + g_i(1) =
  target_{i−1}` recovers the previous round's claim. (The guard fact is available to the round's
  own extraction: acceptance probability `1` on a guarded verifier forces `check = true`.)

  The loop is composed by **recursion over the binary guarded append `▷ᵍ`**
  (`roundsChain count = roundsChain (count−1) ▷ᵍ roundPackage (count−1)`, base = the identity
  package), so the only composition machinery it consumes is `Guarded.lean`'s B4 skeleton.

  **Sorried**: the per-round CWSS theorem `round_coordinateWiseSpecialSound` (Lemma 11).

  ## References

  * [Nguyen, N. K., O'Rourke, G., and Zhang, J., *Hachi: Efficient Lattice-Based Multilinear
      Polynomial Commitments over Extension Fields*][NOZ26]
-/

namespace ArkLib.Lattices.Ajtai.InnerOuter

open CompPoly ArkLib.Lattices.CyclotomicModulus
open OracleComp OracleSpec ProtocolSpec CoordinateWise CoordinateWise.ScalarRound

section Wire

variable (F : Type) [Field F] (b : ℕ)

/-- A round message: the pair of univariate round polynomials `(g_i^{(0)}, g_i^{(α)})`, degree-
bounded by the R8 pins (`roundDegZero b = 2b`, `roundDegAlpha = 2`). -/
@[reducible] def RoundMsg : Type :=
  ↥(Polynomial.degreeLE F (roundDegZero b : ℕ)) × ↥(Polynomial.degreeLE F (roundDegAlpha : ℕ))

/-- The concatenated wire format of `count` paired sumcheck rounds (each round is
`pSpecScalar (RoundMsg F b) F`: one message pair, one scalar challenge). -/
def roundsSpec : (count : ℕ) → ProtocolSpec (2 * count)
  | 0 => !p[]
  | count + 1 => roundsSpec count ++ₚ pSpecScalar (RoundMsg F b) F

/-- Challenges of the concatenated rounds are sampleable (by recursion over the append
instance, applied by name — the append instance does not fire automatically on the
equation-compiled `roundsSpec`). -/
instance roundsSpecSampleable [SampleableType F] :
    ∀ (count : ℕ) (i : (roundsSpec F b count).ChallengeIdx),
      SampleableType ((roundsSpec F b count).Challenge i)
  | 0, i => Fin.elim0 i.1
  | count + 1, i =>
    letI := roundsSpecSampleable count
    ProtocolSpec.instSampleableTypeChallengeAppend
      (pSpec₁ := roundsSpec F b count) (pSpec₂ := pSpecScalar (RoundMsg F b) F) i

end Wire

section Protocol

variable {q : ℕ} [NeZero q] [Fact (Nat.Prime q)] [BEq (ZMod q)] [LawfulBEq (ZMod q)]
  (Φ : CyclotomicModulus (ZMod q)) [IsCyclotomic Φ]
variable {n μ : ℕ} {E : Type} {F : Type} [Field F] [DecidableEq F]
variable (m₀ m₁ : ℕ) (bound ρBound : ℕ) (b : ℕ)
variable {ι : Type} {oSpec : OracleSpec ι} {σ : Type}

/-- The round check ([NOZ26] Figure 6): both round polynomials sum to the current targets over
`{0, 1}`. `Bool`-valued (design G3) so the guarded-verifier witness is definitional. -/
def roundCheck {TCom : Type} {i : ℕ} (stmt : RoundStatement Φ TCom F n μ i)
    (g : RoundMsg F b) : Bool :=
  decide (g.1.1.eval 0 + g.1.1.eval 1 = stmt.target₀) &&
    decide (g.2.1.eval 0 + g.2.1.eval 1 = stmt.targetα)

/-- The `i`-th round's **guarded** verifier ([NOZ26] Figure 6): on a passing check, extend the
challenge prefix by `a_i` and replace the targets by `(g_i^{(0)}(a_i), g_i^{(α)}(a_i))`;
otherwise `failure` (see the module docstring for why the check cannot live in the output
relation). -/
def roundVerifier {TCom : Type} (i : ℕ) :
    Verifier oSpec (RoundStatement Φ TCom F n μ i) (RoundStatement Φ TCom F n μ (i + 1))
      (pSpecScalar (RoundMsg F b) F) where
  verify := fun stmt tr =>
    if roundCheck Φ b stmt (tr.messages ⟨0, rfl⟩) then
      pure ⟨stmt.zc, Fin.snoc stmt.challenges (tr.challenges ⟨1, rfl⟩),
        (tr.messages ⟨0, rfl⟩).1.1.eval (tr.challenges ⟨1, rfl⟩),
        (tr.messages ⟨0, rfl⟩).2.1.eval (tr.challenges ⟨1, rfl⟩)⟩
    else failure

omit [NeZero q] [IsCyclotomic Φ] in
/-- The round verifier is guarded — definitionally, by `roundCheck`. -/
theorem roundVerifier_isGuarded {TCom : Type} (i : ℕ) :
    (roundVerifier (oSpec := oSpec) Φ b (n := n) (μ := μ) (TCom := TCom)
      (F := F) i).IsGuarded :=
  ⟨fun stmt tr => roundCheck Φ b stmt (tr.messages ⟨0, rfl⟩),
   fun stmt tr =>
     ⟨stmt.zc, Fin.snoc stmt.challenges (tr.challenges ⟨1, rfl⟩),
      (tr.messages ⟨0, rfl⟩).1.1.eval (tr.challenges ⟨1, rfl⟩),
      (tr.messages ⟨0, rfl⟩).2.1.eval (tr.challenges ⟨1, rfl⟩)⟩,
   fun _ _ => rfl⟩

/-- The `i`-th round's honest prover skeleton ([NOZ26] Figure 6; completeness out of scope): the
round-polynomial pair is the parameter `computeG` (honestly: the partial hypercube sums of the
two sumcheck polynomials in the free variable), and the output witness carries `w̃` forward. -/
def roundProver {TCom : Type} (i : ℕ)
    (computeG : RoundStatement Φ TCom F n μ i → LiftedWitness Φ μ n → RoundMsg F b) :
    Prover oSpec (RoundStatement Φ TCom F n μ i) (LiftedWitness Φ μ n)
      (RoundStatement Φ TCom F n μ (i + 1)) (LiftedWitness Φ μ n)
      (pSpecScalar (RoundMsg F b) F) where
  PrvState
    | 0 => RoundStatement Φ TCom F n μ i × LiftedWitness Φ μ n
    | 1 => RoundStatement Φ TCom F n μ i × LiftedWitness Φ μ n
    | 2 => (RoundStatement Φ TCom F n μ i × LiftedWitness Φ μ n) × F
  input := id
  sendMessage
    | ⟨0, _⟩ => fun st => pure (computeG st.1 st.2, st)
    | ⟨1, h⟩ => nomatch h
  receiveChallenge
    | ⟨0, h⟩ => nomatch h
    | ⟨1, _⟩ => fun st => pure fun c => (st, c)
  output := fun ⟨⟨stmt, wit⟩, c⟩ =>
    pure (⟨stmt.zc, Fin.snoc stmt.challenges c,
      (computeG stmt wit).1.1.eval c, (computeG stmt wit).2.1.eval c⟩, wit)

variable [SampleableType F]

/-- **Hachi Lemma 11 (skeleton): per-round CWSS of the paired sumcheck round at
`k = max (2b) 2 + 1`.**

**Sorried (F7).** Extraction plan (Lemma 11, case-faithful): the `k` accepting branches of a
tree node share the message pair `(g^{(0)}, g^{(α)})` and carry pairwise-distinct challenges
(`scalarStructure`'s injective family); escapes and differing openings pass through resp. hit
`K.collision_mem`; otherwise the shared `w̃` makes both defect polynomials
`T ↦ hypercubeSum H (i+1) (snoc prefix T) − g(T)` (degrees `≤ 2b` resp. `≤ 2`) vanish at `k`
distinct points, hence identically; evaluating at `0, 1`, summing, and using the **guard fact**
`roundCheck = true` (available from acceptance on a guarded verifier) recovers the round-`i`
claims. Assembled via a guarded variant of the scalar-round machinery (F4.1 + B4.1's
`check_eq_true_of_guarded_accepting`).

**TODO (reuse `Sumcheck/Structured`):** this round should be the existing structured sum-check
round (`ArkLib/ProofSystem/Sumcheck/Structured`) rather than the bespoke `roundVerifier` above —
its CWSS discharged by the (to-be-built, wire-format-generic / guarded) analog of the scalar-round
engine applied to `Structured.roundOracleVerifier`, with the round relations read off
`Structured.sumcheckConsistencyProp` / `computeRoundPoly`. The verifier wiring is left `sorry` for
now pending that reconciliation (see the `Sumcheck.lean` umbrella). -/
theorem round_coordinateWiseSpecialSound
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (K : LiftCom (LiftedWitness Φ μ n) E (liftShort Φ bound ρBound))
    (φF : ZMod q →+* F) (i : ℕ) :
    (roundVerifier (oSpec := oSpec) Φ b (TCom := K.TCom)
        i).coordinateWiseSpecialSound init impl
      (scalarStructure (max (roundDegZero b) roundDegAlpha + 1)
        (by have := Nat.le_max_right (roundDegZero b) roundDegAlpha
            unfold roundDegAlpha at *; omega))
      (roundRelE Φ m₀ m₁ bound ρBound K φF b i)
      (roundRelE Φ m₀ m₁ bound ρBound K φF b (i + 1)) := by
  sorry

/-- The `i`-th paired sumcheck round as a **guarded** package (`GCWSSPackage`): the guarded
round verifier with the `k = max (2b) 2 + 1` plain-special-soundness structure, reducing the
round-`i` seam to the round-`(i+1)` seam. Certificate: the sorried
`round_coordinateWiseSpecialSound` (Lemma 11). -/
def roundPackage (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (K : LiftCom (LiftedWitness Φ μ n) E (liftShort Φ bound ρBound))
    (φF : ZMod q →+* F) (i : ℕ) :
    GCWSSPackage init impl
      (RoundStatement Φ K.TCom F n μ i) (LiftedWitness Φ μ n ⊕ E)
      (RoundStatement Φ K.TCom F n μ (i + 1)) (LiftedWitness Φ μ n ⊕ E)
      (pSpecScalar (RoundMsg F b) F) where
  verifier := roundVerifier (oSpec := oSpec) Φ b (TCom := K.TCom) i
  struct := scalarStructure (max (roundDegZero b) roundDegAlpha + 1)
    (by have := Nat.le_max_right (roundDegZero b) roundDegAlpha
        unfold roundDegAlpha at *; omega)
  relIn := roundRelE Φ m₀ m₁ bound ρBound K φF b i
  relOut := roundRelE Φ m₀ m₁ bound ρBound K φF b (i + 1)
  isGuarded := roundVerifier_isGuarded Φ b i
  isCWSS := round_coordinateWiseSpecialSound Φ m₀ m₁ bound ρBound b init impl K φF i

/-- The empty round loop has no challenges. -/
instance : IsEmpty (roundsSpec F b 0).ChallengeIdx := ⟨fun i => Fin.elim0 i.1⟩

/-- **The composed sumcheck loop, with its seam invariant** (Hachi Figure 7's round phase):
`count` paired rounds chained by recursion over the binary guarded append `▷ᵍ` (base case: the
zero-round identity package), together with the proofs that the composite's `relIn`/`relOut`
are the round-`0`/round-`count` seam relations — the recursion's seams are definitional only
*per instance*, not for an open `count`, so the invariant must ride along. -/
noncomputable def roundsChainAux (init : ProbComp σ)
    (impl : QueryImpl oSpec (StateT σ ProbComp))
    (K : LiftCom (LiftedWitness Φ μ n) E (liftShort Φ bound ρBound))
    (φF : ZMod q →+* F) :
    (count : ℕ) →
      { P : GCWSSPackage init impl
          (RoundStatement Φ K.TCom F n μ 0) (LiftedWitness Φ μ n ⊕ E)
          (RoundStatement Φ K.TCom F n μ count) (LiftedWitness Φ μ n ⊕ E)
          (roundsSpec F b count) //
        P.relIn = roundRelE Φ m₀ m₁ bound ρBound K φF b 0 ∧
        P.relOut = roundRelE Φ m₀ m₁ bound ρBound K φF b count }
  | 0 =>
    ⟨CWSSPackage.toGuarded
      { verifier := ReduceClaim.verifier oSpec id
        struct := CWSSStructure.ofIsEmpty
        relIn := roundRelE Φ m₀ m₁ bound ρBound K φF b 0
        relOut := roundRelE Φ m₀ m₁ bound ρBound K φF b 0
        isPure := ⟨fun stmt _ => stmt, fun _ _ => rfl⟩
        isCWSS := ReduceClaim.verifier_coordinateWiseSpecialSound
          (relIn := roundRelE Φ m₀ m₁ bound ρBound K φF b 0)
          (relOut := roundRelE Φ m₀ m₁ bound ρBound K φF b 0)
          (mapWitInv := fun _ w => w) (D := CWSSStructure.ofIsEmpty)
          (fun _ _ h => h) },
     rfl, rfl⟩
  | count + 1 =>
    let prev := roundsChainAux init impl K φF count
    ⟨prev.1.append (roundPackage Φ m₀ m₁ bound ρBound b init impl K φF count) prev.2.2,
     prev.2.1, rfl⟩

/-- **The composed sumcheck loop** (Hachi Figure 7's round phase), from the round-`0` seam
(installed by the sumcheck bridge) to the round-`count` seam (consumed by the final-evaluation
step). Instantiated at `count := m₀` in the composition. -/
noncomputable def roundsChain (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (K : LiftCom (LiftedWitness Φ μ n) E (liftShort Φ bound ρBound))
    (φF : ZMod q →+* F) (count : ℕ) :
    GCWSSPackage init impl
      (RoundStatement Φ K.TCom F n μ 0) (LiftedWitness Φ μ n ⊕ E)
      (RoundStatement Φ K.TCom F n μ count) (LiftedWitness Φ μ n ⊕ E)
      (roundsSpec F b count) :=
  (roundsChainAux Φ m₀ m₁ bound ρBound b init impl K φF count).1

/-- The loop's input seam is the round-`0` relation (the seam pin for composing after the
sumcheck bridge). -/
theorem roundsChain_relIn (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (K : LiftCom (LiftedWitness Φ μ n) E (liftShort Φ bound ρBound))
    (φF : ZMod q →+* F) (count : ℕ) :
    (roundsChain Φ m₀ m₁ bound ρBound b init impl K φF count).relIn =
      roundRelE Φ m₀ m₁ bound ρBound K φF b 0 :=
  (roundsChainAux Φ m₀ m₁ bound ρBound b init impl K φF count).2.1

/-- The loop's output seam is the round-`count` relation (the seam pin for composing with the
final-evaluation step). -/
theorem roundsChain_relOut (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (K : LiftCom (LiftedWitness Φ μ n) E (liftShort Φ bound ρBound))
    (φF : ZMod q →+* F) (count : ℕ) :
    (roundsChain Φ m₀ m₁ bound ρBound b init impl K φF count).relOut =
      roundRelE Φ m₀ m₁ bound ρBound K φF b count :=
  (roundsChainAux Φ m₀ m₁ bound ρBound b init impl K φF count).2.2

end Protocol

end ArkLib.Lattices.Ajtai.InnerOuter

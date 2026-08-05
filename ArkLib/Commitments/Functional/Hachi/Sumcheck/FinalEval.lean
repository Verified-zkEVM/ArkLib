/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tobias Rothmann
-/
import ArkLib.Commitments.Functional.Hachi.Sumcheck.Rounds

/-!
  # Final evaluation — Hachi Figure 7 tail — skeleton

  The step closing the sumcheck loop ([NOZ26] Figure 7, "Open `t` to evaluate
  `w̃(a₁, …, a_ℓ)`; evaluate `M̃_α(a₁, …, a_ℓ)`; check the correctness of the sumcheck"):

  * **message (P→V)** — the claimed evaluation `y′ := w̃(a₁, …, a_{m₀}) ∈ F`, sent in the
    clear;
  * **check (guarded)** — the verifier evaluates the *public* factors at the challenge point —
    `eq̃(τ₀, a)`, the range product at `y′`, `α̃`, and `∑ᵢ eq̃(τ_α, i)·M̃_α(i, a)` (the paper's
    expensive `Õ(√(2^ℓ)·λ)` step) — and checks both final sumcheck targets:
    `eq̃(τ₀,a)·P_b(y′)·… = target₀` and `y′·α̃(a)·(∑ᵢ eq̃(τ_α,i)M̃_α(i,a)) = target_α`, plus the
    bound-sanity conjunct. The verifier must be **guarded**: the check reads the
    final targets, which the output statement drops — it can live neither downstream nor in a
    pull-back.
  * **output** — the *evaluation claim* `WEvalStatement`: the commitment `t`, the sumcheck point
    `a`, and the claimed value `y′` — the recursion currency (`mle[w̃](a) = y′` for the
    committed `w̃`), consumed by the `Recursion/` adapters.

  Extraction (sorried): from a `relWEvalClaim`-witness (an opening `w̃` of `t` with
  `mle[w̃](a) = y′`) and the **guard facts** (available from acceptance on a
  guarded verifier), the two final-round point-evaluation claims of `roundRel m₀` follow by
  computing `F_{0,τ₀}(a)` and `F_{α,τ_α}(a)` through `mle[w̃](a) = y′` — the evaluation
  factorizations of the (sorried) sumcheck polynomials.

  ## References

  * [Nguyen, N. K., O'Rourke, G., and Zhang, J., *Hachi: Efficient Lattice-Based Multilinear
      Polynomial Commitments over Extension Fields*][NOZ26]
-/

namespace ArkLib.Lattices.Ajtai.InnerOuter

open CompPoly ArkLib.Lattices.CyclotomicModulus
open OracleComp OracleSpec ProtocolSpec CoordinateWise

/-- The final-evaluation wire format: one prover message carrying the claimed evaluation
`y′ ∈ F`. -/
@[reducible] def pSpecFinalEval (F : Type) : ProtocolSpec 1 :=
  ⟨!v[.P_to_V], !v[F]⟩

/-- The final-evaluation step has no challenge round: its `ChallengeIdx` is empty. -/
instance {F : Type} : IsEmpty (pSpecFinalEval F).ChallengeIdx :=
  ⟨fun ⟨0, h⟩ => nomatch h⟩

/-- Each challenge of `pSpecFinalEval` is (vacuously) sampleable — there are none. -/
instance {F : Type} [SampleableType F] :
    ∀ i, SampleableType ((pSpecFinalEval F).Challenge i) :=
  fun i => isEmptyElim i

/-- **The evaluation-claim statement** — the recursion currency after one full §4.3 pass: the
`w̃`-commitment `t`, the sumcheck point `a ∈ F^{m₀}`, and the claimed multilinear evaluation
`y′`. Everything else (the `R^lin` data, `α`, the seeds, the targets) is dropped — which is
exactly why the final check must be a runtime guard. -/
structure WEvalStatement (TCom F : Type) (m₀ : ℕ) where
  /-- The `w̃`-commitment from the lift stage. -/
  t : TCom
  /-- The sumcheck challenge point `a = (a₁, …, a_{m₀})`. -/
  point : Fin m₀ → F
  /-- The claimed evaluation `y′ = mle[w̃](a)`. -/
  value : F

section Protocol

variable {q : ℕ} [NeZero q] [Fact (Nat.Prime q)] [BEq (ZMod q)] [LawfulBEq (ZMod q)]
  (Φ : CyclotomicModulus (ZMod q)) [IsCyclotomic Φ]
variable {n μ : ℕ} {F : Type} [Field F]
variable (m₀ m₁ : ℕ) (bound ρBound : ℕ) (b : ℕ)
variable {ι : Type} {oSpec : OracleSpec ι} {σ : Type}

/-- The final check ([NOZ26] Figure 7 tail): both final sumcheck targets against the public
factors evaluated at the point, with the claimed `y′` in place of `w̃(a)`, plus the bound-sanity
conjunct `bound ≤ rlin.bound`. All parameters the future implementation reads are pinned
explicitly. **Sorried** — the verifier's expensive public-evaluation step (`M̃_α` via
dynamic programming). -/
def finalCheck {TCom : Type} (m₁ bound b : ℕ) (φF : ZMod q →+* F)
    (stmt : RoundStatement Φ TCom F n μ m₀) (y' : F) : Bool :=
  sorry

/-- The final-evaluation verifier: **guarded** on `finalCheck`, outputting the evaluation claim
`⟨t, a, y′⟩`. -/
def finalEvalVerifier {TCom : Type} (φF : ZMod q →+* F) :
    Verifier oSpec (RoundStatement Φ TCom F n μ m₀) (WEvalStatement TCom F m₀)
      (pSpecFinalEval F) where
  verify := fun stmt tr =>
    if finalCheck Φ m₀ m₁ bound b φF stmt (tr 0) then
      pure ⟨stmt.zc.t, stmt.challenges, tr 0⟩
    else failure

omit [NeZero q] [IsCyclotomic Φ] in
/-- The final-evaluation verifier is guarded — definitionally, by `finalCheck`. -/
theorem finalEvalVerifier_isGuarded {TCom : Type} (φF : ZMod q →+* F) :
    (finalEvalVerifier (oSpec := oSpec) Φ m₀ m₁ bound b (n := n) (μ := μ) (TCom := TCom)
      φF).IsGuarded :=
  ⟨fun stmt tr => finalCheck Φ m₀ m₁ bound b φF stmt (tr 0),
   fun stmt tr => ⟨stmt.zc.t, stmt.challenges, tr 0⟩,
   fun _ _ => rfl⟩

/-- The honest final-evaluation prover skeleton: sends `y′ := mle[w̃](a)` (the parameter
`computeY`, honestly `wTableMleEval`) and carries `w̃` forward as the output witness. -/
def finalEvalProver {TCom : Type}
    (computeY : RoundStatement Φ TCom F n μ m₀ → LiftedWitness Φ μ n → F) :
    Prover oSpec (RoundStatement Φ TCom F n μ m₀) (LiftedWitness Φ μ n)
      (WEvalStatement TCom F m₀) (LiftedWitness Φ μ n) (pSpecFinalEval F) where
  PrvState
    | 0 => RoundStatement Φ TCom F n μ m₀ × LiftedWitness Φ μ n
    | 1 => RoundStatement Φ TCom F n μ m₀ × LiftedWitness Φ μ n
  input := id
  sendMessage
    | ⟨0, _⟩ => fun st => pure (computeY st.1 st.2, st)
  receiveChallenge
    | ⟨0, h⟩ => nomatch h
  output := fun ⟨stmt, wit⟩ =>
    pure (⟨stmt.zc.t, stmt.challenges, computeY stmt wit⟩, wit)

/-- **The evaluation-claim relation** — the §4.3 chain's final seam and the recursion's input:
`w̃` opens `t` and its table's multilinear extension evaluates to the claimed value at the
point. -/
def relWEvalClaim (K : LiftCom (LiftedWitness Φ μ n) (liftShort Φ bound ρBound))
    (φF : ZMod q →+* F) :
    Set (WEvalStatement K.TCom F m₀ × LiftedWitness Φ μ n) :=
  {p |
    K.com p.2 = p.1.t ∧
    wTableMleEval Φ m₀ φF b p.2 p.1.point = p.1.value}

variable [SampleableType F]

/-- **The final-evaluation extraction algorithm.**

**Sorried** — this def is the extraction *algorithm* itself (the transcript-level pull-back of the
proof plan on `finalEval_coordinateWiseSpecialSoundWith`). -/
noncomputable def finalEvalExtractor
    (K : LiftCom (LiftedWitness Φ μ n) (liftShort Φ bound ρBound))
    (φF : ZMod q →+* F) :
    Extractor.TreeBased (RoundStatement Φ K.TCom F n μ m₀) (LiftedWitness Φ μ n)
      (pSpecFinalEval F)
      (CWSSStructure.toShape (CWSSStructure.ofIsEmpty
        (pSpec := pSpecFinalEval F))).arity :=
  sorry

/-- **CWSS of the final-evaluation step, at the named `finalEvalExtractor`**
(the named form is deliberate — see `Verifier.treeSpecialSoundWith`; closing this gap means
filling the extractor and this specification about it).

**Sorried.** Proof plan: the protocol has no challenge round, so CWSS collapses (via the
probability-phrased no-challenge bridge, which already tolerates rejecting verifiers) to a
transcript-level extraction: acceptance forces `finalCheck = true` (the guarded rejection
lemma) and yields a `relWEvalClaim`-witness; evaluate the two sumcheck polynomials at the
point through `mle[w̃](a) = y′` and the guard's target equations to recover `roundRel m₀`'s point
claims (the round-`m₀` `hypercubeSum` is the plain evaluation); the bound-sanity conjunct is
re-supplied by the guard. -/
theorem finalEval_coordinateWiseSpecialSoundWith
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (K : LiftCom (LiftedWitness Φ μ n) (liftShort Φ bound ρBound))
    (φF : ZMod q →+* F) :
    Verifier.coordinateWiseSpecialSoundWith init impl
      CWSSStructure.ofIsEmpty
      (roundRel Φ m₀ m₁ bound ρBound K φF b m₀)
      (relWEvalClaim Φ m₀ bound ρBound b K φF)
      (finalEvalVerifier (oSpec := oSpec) Φ m₀ m₁ bound b (TCom := K.TCom) φF)
      (finalEvalExtractor Φ m₀ bound ρBound K φF) := by
  sorry

/-- **The final-evaluation step as a guarded `GCWSSPackage`**: the guarded one-message verifier with
the empty challenge structure, reducing the round-`m₀` seam to the evaluation claim `relWEvalClaim`.
A guarded *re-reading* of the final targets, hence escape-free. Certificate: the sorried
`finalEval_coordinateWiseSpecialSoundWith`. -/
noncomputable def finalEvalPackage (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (K : LiftCom (LiftedWitness Φ μ n) (liftShort Φ bound ρBound))
    (φF : ZMod q →+* F) :
    GCWSSPackage init impl
      (RoundStatement Φ K.TCom F n μ m₀) (LiftedWitness Φ μ n)
      (WEvalStatement K.TCom F m₀) (LiftedWitness Φ μ n)
      (pSpecFinalEval F) where
  verifier := finalEvalVerifier (oSpec := oSpec) Φ m₀ m₁ bound b (TCom := K.TCom) φF
  struct := CWSSStructure.ofIsEmpty
  relIn := roundRel Φ m₀ m₁ bound ρBound K φF b m₀
  relOut := relWEvalClaim Φ m₀ bound ρBound b K φF
  isGuarded := finalEvalVerifier_isGuarded Φ m₀ m₁ bound b φF
  extractor := finalEvalExtractor Φ m₀ bound ρBound K φF
  isCWSS := finalEval_coordinateWiseSpecialSoundWith Φ m₀ m₁ bound ρBound b init impl K φF

end Protocol

end ArkLib.Lattices.Ajtai.InnerOuter

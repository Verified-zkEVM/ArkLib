/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tobias Rothmann
-/
import ArkLib.Commitments.Functional.Hachi.ZeroCheck.Batch

/-!
  # Zero-check — Hachi Figure 5 / **corrected** Lemma 10 — skeleton

  One challenge round reducing the batched polynomial identities `H₀ ≡ 0 ∧ H_α ≡ 0` to their
  evaluations at random points: the verifier samples the points, and the (never-sent) committed
  `w̃` must make both evaluations zero.

  ## ⚠ The paper's Lemma 10 is not provable as stated — this file implements the repair

  Hachi's Lemma 10 claims CWSS of this round from an `SS(F, 2, max(2d, 2b−1))` star of
  transcripts with **uniform vector challenges** `(τ₀, τ₁) ∈ F^{m₀} × F^{m₁}`. That claim is
  **false**: a coordinate-wise star certifies only that the multilinear `H` vanishes on the
  *axis cross* through the star's center, and for `m ≥ 2` cross-vanishing does not imply
  `H ≡ 0` — `H(t₁,t₂) = (t₁−a)(t₂−b)` vanishes on every axis line through `(a,b)` yet is
  nonzero, and an adversary can realize exactly this shape against the paper's own range check
  with a single out-of-range entry. No choice of the paper's parameter `D` helps: uniform vector
  challenges cannot certify more than axis-cross vanishing, so [NOZ26, Lemma 10] is unprovable
  without changing the challenge *distribution* — which is what the repair below does.

  **Adopted repair (one round, Kronecker curve):** sample two independent scalar **seeds**
  `(ρ₀, ρ_α) ← F²` and derive the evaluation points on the Kronecker curves

  `τ₀ := κ_{m₀}(ρ₀) = (ρ₀, ρ₀², ρ₀⁴, …)`, `τ_α := κ_{m₁}(ρ_α)`.

  The pullback of an `m`-variate multilinear polynomial along `κ_m` is univariate of degree
  `< 2^m` and the pullback is **injective** (binary expansion of exponents:
  `LinearMvExtension.powAlgHom`), so ordinary univariate root counting becomes
  information-complete. The challenge is modeled as the **seed pair** `F × F` with an
  `(ℓ, k) = (2, D)` CWSS structure, `D := max 2 (max 2^{m₀} 2^{m₁})`: an `SS(F, 2, D)` star has
  `2D − 1` members — `D` distinct seeds on each arm — and each arm interpolates one pullback.
  The checked equations, `H₀`/`H_α`, and all downstream sumcheck formulas are unchanged; what
  changes is the challenge *distribution* (curve-supported rather than uniform) and the error
  scale (`D/|F|` rather than `m/|F|` — requires `D ≤ |F|`, i.e. a large enough extension field).
  **This is the one place the formalization deliberately changes the paper's protocol to repair
  its proof.**

  ## Protocol shape

  A single `V_to_P` round carrying `(ρ₀, ρ_α) : F × F`; no prover message. The verifier is a
  pure pass-through extending the lift statement by the seeds (`ZeroCheckStatement`); the
  evaluation claims constrain the never-sent `w̃` and live in `relZeroCheck`. This block runs at
  the *fixed* `α` produced by the lift — the lift's `α`-fork remains a separate, earlier CWSS
  node (one flat three-coordinate star over `(α, ρ₀, ρ_α)` would recreate the missing-corners
  problem for the mixed `(α, ρ_α)`-dependence of `H_α`).

  **Sorried**: the extraction algorithm `zeroCheckExtractor` and the CWSS theorem
  `zeroCheck_coordinateWiseSpecialSoundWithEscape` (the corrected Lemma 10; Kronecker injectivity
  + univariate root counting + the weak-binding escape event `zeroCheckEsc`).

  ## References

  * [Nguyen, N. K., O'Rourke, G., and Zhang, J., *Hachi: Efficient Lattice-Based Multilinear
      Polynomial Commitments over Extension Fields*][NOZ26]
-/

namespace ArkLib.Lattices.Ajtai.InnerOuter

open CompPoly ArkLib.Lattices.CyclotomicModulus
open OracleComp OracleSpec ProtocolSpec CoordinateWise

/-- The zero-check's wire format: one verifier challenge carrying the **Kronecker seed pair**
`(ρ₀, ρ_α) ∈ F × F` (corrected Lemma 10; the batching points are derived on the curves). -/
@[reducible] def pSpecZeroCheck (F : Type) : ProtocolSpec 1 :=
  ⟨!v[.V_to_P], !v[F × F]⟩

section Instances

variable {F : Type} [SampleableType F]

/-- The zero-check's lone challenge (the Kronecker seed pair `F × F`) is sampleable
whenever `F` is. -/
instance : ∀ i, SampleableType ((pSpecZeroCheck F).Challenge i)
  | ⟨0, _⟩ => (inferInstance : SampleableType (F × F))

end Instances

/-- **The corrected Lemma 10 CWSS structure**: the seed-pair challenge decomposes into `ℓ = 2`
scalar coordinates over the alphabet `F`, with soundness parameter
`k = D := max 2 (max 2^{m₀} 2^{m₁})` — the maximum padded constraint-table size (NOT the
paper's `max(2d, 2b−1)`, whose provenance is the Lemma 9 interpolation resp. the Lemma 11 round
degree). Star arity `2·(D−1)+1 = 2D−1`. -/
def zeroCheckStructure (F : Type) (m₀ m₁ : ℕ) : CWSSStructure (pSpecZeroCheck F) where
  coordIndex := fun _ => ⟨2, by omega⟩
  alphabet := fun _ => F
  decompose := fun i => match i with
    | ⟨0, _⟩ => (piFinTwoEquiv fun _ => F).symm
  soundnessParam := fun _ => ⟨max 2 (max (2 ^ m₀) (2 ^ m₁)), le_max_left _ _⟩
  arity := fun _ => 2 * (max 2 (max (2 ^ m₀) (2 ^ m₁)) - 1) + 1
  arity_eq := rfl

/-! ### Reading the seed family off a tree

The zero-check has a *single* challenge round and no prover message, so every full challenge tree is
one `chalNode` over leaves. The reader below is index-generic in the same way as
`CoordinateWise.SingleRound`'s (a naive `match` on a `ChallengeTree … 0` fails with "dependent
elimination failed"), but needs no `Fin.cast` bridge: `zeroCheckStructure`'s arity is already
`2D − 1` by `rfl`. The reader is what makes the escape event below
`(statement, tree)`-determined. -/

section SeedReader

variable {F : Type} {arity : (pSpecZeroCheck F).ChallengeIdx → ℕ}

/-- Index-generic reader: peel the round-0 `chalNode`'s sibling-seed family off a tree at any
index `a`, together with a proof `a = 0`. -/
def seedsAux : {a : Fin 2} → ChallengeTree (pSpecZeroCheck F) arity a → a = (0 : Fin 2) →
    (Fin (arity ⟨0, rfl⟩) → (pSpecZeroCheck F).Challenge ⟨0, rfl⟩)
  | _, .leaf, ha => by simp at ha
  | _, .msgNode m h _ _, ha => by
      obtain rfl : m = 0 := Fin.ext (by have := congrArg Fin.val ha; simp at this ⊢)
      exact absurd h Direction.noConfusion
  | _, .chalNode m _ chals _, ha => by
      obtain rfl : m = 0 := Fin.ext (by have := congrArg Fin.val ha; simp at this ⊢)
      exact chals

/-- Read the sibling family of Kronecker seed pairs off a full tree. -/
def readSeeds (tree : ChallengeTree (pSpecZeroCheck F) arity 0) :
    Fin (arity ⟨0, rfl⟩) → (pSpecZeroCheck F).Challenge ⟨0, rfl⟩ :=
  seedsAux tree rfl

/-- The star tree of the zero-check: one challenge node carrying the seed family, leaves below. -/
def tree1 (seeds : Fin (arity ⟨0, rfl⟩) → (pSpecZeroCheck F).Challenge ⟨0, rfl⟩) :
    ChallengeTree (pSpecZeroCheck F) arity 0 :=
  .chalNode 0 rfl seeds (fun _ => .leaf)

/-- The reader computes on the star tree. -/
@[simp] theorem readSeeds_tree1
    (seeds : Fin (arity ⟨0, rfl⟩) → (pSpecZeroCheck F).Challenge ⟨0, rfl⟩) :
    readSeeds (tree1 seeds) = seeds := rfl

end SeedReader

section Protocol

variable {q : ℕ} [NeZero q] [Fact (Nat.Prime q)] [BEq (ZMod q)] [LawfulBEq (ZMod q)]
  (Φ : CyclotomicModulus (ZMod q)) [IsCyclotomic Φ]
variable {n μ : ℕ} {F : Type} [Field F]
variable (m₀ m₁ : ℕ) (bound ρBound : ℕ)
variable {ι : Type} {oSpec : OracleSpec ι} {σ : Type}

/-- The zero-check verifier (corrected Figure 5): a pure pass-through extending the lift
statement by the two Kronecker seeds. The evaluation claims constrain the never-sent `w̃` and
live in `relZeroCheck`. -/
def zeroCheckVerifier {TCom : Type} :
    Verifier oSpec (LiftStatement Φ TCom F n μ) (ZeroCheckStatement Φ TCom F n μ)
      (pSpecZeroCheck F) where
  verify := fun stmt tr =>
    pure ⟨stmt.1, stmt.2.1, stmt.2.2,
      (tr.challenges ⟨0, rfl⟩).1, (tr.challenges ⟨0, rfl⟩).2⟩

/-- The zero-check prover (trivial: the round is challenge-only; the honest prover just absorbs
the seeds and carries its lifted witness forward as the output witness). -/
def zeroCheckProver {TCom : Type} :
    Prover oSpec (LiftStatement Φ TCom F n μ) (LiftedWitness Φ μ n)
      (ZeroCheckStatement Φ TCom F n μ) (LiftedWitness Φ μ n) (pSpecZeroCheck F) where
  PrvState
    | 0 => LiftStatement Φ TCom F n μ × LiftedWitness Φ μ n
    | 1 => (LiftStatement Φ TCom F n μ × LiftedWitness Φ μ n) × (F × F)
  input := id
  sendMessage
    | ⟨0, h⟩ => nomatch h
  receiveChallenge
    | ⟨0, _⟩ => fun st => pure fun c => (st, c)
  output := fun ⟨⟨stmt, wit⟩, c⟩ =>
    pure (⟨stmt.1, stmt.2.1, stmt.2.2, c.1, c.2⟩, wit)

/-- **The zero-check's output relation** (corrected Figure 5 residual claims): `w̃` opens `t`,
is short (`liftShort`, the shortness regime of the commitment's short-collision set
`LiftCom.Collision`, the hardness target of the escape event `zeroCheckEsc` below),
and both batched constraint polynomials vanish **at the derived Kronecker points**
`τ₀ = κ_{m₀}(ρ₀)`, `τ_α = κ_{m₁}(ρ_α)`. -/
def relZeroCheck (K : LiftCom (LiftedWitness Φ μ n) (liftShort Φ bound ρBound))
    (φF : ZMod q →+* F) (b : ℕ) :
    Set (ZeroCheckStatement Φ K.TCom F n μ × LiftedWitness Φ μ n) :=
  {p |
    K.com p.2 = p.1.t ∧
    liftShort Φ bound ρBound p.2 ∧
    CMlPolynomialEval.eval (hZero Φ m₀ φF b p.2)
        (Vector.ofFn (kroneckerPoint m₀ p.1.seed₀)) = 0 ∧
    CMlPolynomialEval.eval (hAlpha Φ m₁ φF b p.1.rlin p.1.α p.2)
        (Vector.ofFn (kroneckerPoint m₁ p.1.seedα)) = 0 ∧
    bound ≤ p.1.rlin.bound}

/-- **The zero-check's escape event** (corrected Lemma 10's weak-binding case): the tree's own seed
family admits per-branch `relZeroCheck`-responses among which two are **distinct short openings of
the statement's commitment `t`** — a member of `LiftCom.Collision`, hence a Module-SIS break of the
fixed key by [NOZ26] Lemma 7. (Both openings automatically open `t`: `relZeroCheck`'s first conjunct
pins `K.com w = t` and every branch's output statement carries the same `t`.)

Against the escape-event contract (`ChallengeTree.EscapeEvent`): the collision conjunct is an
unconditional break at *every* `(statement, tree)`, and the event is determined by the statement and
the tree's seeds (read by `readSeeds`) together with responses pinned to the **output** relation.
That pinning is what keeps it tight — it cannot fire on trees where all branches share one opening,
which is exactly where extraction succeeds. -/
def zeroCheckEsc (K : LiftCom (LiftedWitness Φ μ n) (liftShort Φ bound ρBound))
    (φF : ZMod q →+* F) (b : ℕ) :
    ChallengeTree.EscapeEvent (LiftStatement Φ K.TCom F n μ) (pSpecZeroCheck F)
      (CWSSStructure.toShape (zeroCheckStructure F m₀ m₁)).arity :=
  fun stmt tree =>
    ∃ resp : Fin ((zeroCheckStructure F m₀ m₁).arity ⟨0, rfl⟩) → LiftedWitness Φ μ n,
      (∀ j, (⟨stmt.1, stmt.2.1, stmt.2.2,
            (readSeeds tree j).1, (readSeeds tree j).2⟩, resp j) ∈
          relZeroCheck Φ m₀ m₁ bound ρBound K φF b) ∧
      ∃ j j', (resp j, resp j') ∈ K.Collision

variable [SampleableType F]

/-- **The corrected Lemma 10 extraction algorithm (skeleton).**

**Sorried** — this def is the extraction *algorithm* itself (the case split of the proof plan on
`zeroCheck_coordinateWiseSpecialSoundWithEscape`). -/
noncomputable def zeroCheckExtractor
    (K : LiftCom (LiftedWitness Φ μ n) (liftShort Φ bound ρBound))
    (φF : ZMod q →+* F) (b : ℕ) :
    Extractor.TreeBased (LiftStatement Φ K.TCom F n μ) (LiftedWitness Φ μ n)
      (pSpecZeroCheck F)
      (CWSSStructure.toShape (zeroCheckStructure F m₀ m₁)).arity :=
  sorry

/-- **Corrected Hachi Lemma 10 (skeleton): one-round Kronecker-seed escape-threaded CWSS of the
zero-check, at the named `zeroCheckExtractor`.** The relations are `relBatched` / `relZeroCheck`;
the weak-binding failure mode is the escape disjunct `zeroCheckEsc`.

**Sorried.** Extraction plan: an `SS(F, 2, D)` star of `2D − 1` accepting branches has `D`
pairwise-distinct `ρ₀`-values on its first arm (the second coordinate held at the center) and `D`
pairwise-distinct `ρ_α`-values on its second arm. If two branch witnesses are distinct openings of
`t`, they are short (by `relZeroCheck`'s downstream range content, the same weak-binding route as
Lemma 9's) and `zeroCheckEsc` fires — take the left disjunct. Otherwise all branches share one `w̃`:
the univariate pullback `K₀(T) := H₀^{w̃}(κ_{m₀}(T))` has degree `< 2^{m₀} ≤ D` (multilinearity of
`hZero` is structural — its `CMlPolynomialEval` representation is a length-`2 ^ m₀` coefficient
vector — plus the `LinearMvExtension.powAlgHom` degree bound) and `D` distinct roots on the
first arm, hence `K₀ = 0`; **Kronecker injectivity** of the pullback on multilinear polynomials (the
still-missing `powAlgHom_injective_on_multilinear`) gives `H₀^{w̃} ≡ 0`. The second arm gives
`H_α^{w̃} ≡ 0` identically. The axis-cross counterexample of the module docstring cannot survive:
its pullback is a nonzero univariate of degree `< 2^{m₀}`. -/
theorem zeroCheck_coordinateWiseSpecialSoundWithEscape
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (K : LiftCom (LiftedWitness Φ μ n) (liftShort Φ bound ρBound))
    (φF : ZMod q →+* F) (b : ℕ) :
    Verifier.coordinateWiseSpecialSoundWithEscape init impl
      (zeroCheckStructure F m₀ m₁)
      (zeroCheckEsc Φ m₀ m₁ bound ρBound K φF b)
      (relBatched Φ m₀ m₁ bound ρBound K φF b)
      (relZeroCheck Φ m₀ m₁ bound ρBound K φF b)
      (zeroCheckVerifier (oSpec := oSpec) Φ (n := n) (μ := μ) (F := F) (TCom := K.TCom))
      (zeroCheckExtractor Φ m₀ m₁ bound ρBound K φF b) := by
  sorry

/-- **The zero-check as an `EscapeCWSSPackage`** (corrected Hachi Figure 5 / Lemma 10): the
one-round seed-pair verifier with the `(ℓ, k) = (2, D)` Kronecker structure, reducing `relBatched`
to `relZeroCheck`, with the weak-binding event `zeroCheckEsc` as its one escape-specific field. -/
noncomputable def zeroCheckPackage (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (K : LiftCom (LiftedWitness Φ μ n) (liftShort Φ bound ρBound))
    (φF : ZMod q →+* F) (b : ℕ) :
    EscapeCWSSPackage init impl
      (LiftStatement Φ K.TCom F n μ) (LiftedWitness Φ μ n)
      (ZeroCheckStatement Φ K.TCom F n μ) (LiftedWitness Φ μ n)
      (pSpecZeroCheck F) where
  verifier := zeroCheckVerifier (oSpec := oSpec) Φ
  struct := zeroCheckStructure F m₀ m₁
  relIn := relBatched Φ m₀ m₁ bound ρBound K φF b
  relOut := relZeroCheck Φ m₀ m₁ bound ρBound K φF b
  esc := zeroCheckEsc Φ m₀ m₁ bound ρBound K φF b
  isPure := ⟨fun stmt tr =>
    ⟨stmt.1, stmt.2.1, stmt.2.2, (tr.challenges ⟨0, rfl⟩).1, (tr.challenges ⟨0, rfl⟩).2⟩,
    fun _ _ => rfl⟩
  extractor := zeroCheckExtractor Φ m₀ m₁ bound ρBound K φF b
  isCWSS := zeroCheck_coordinateWiseSpecialSoundWithEscape Φ m₀ m₁ bound ρBound init impl K φF b

end Protocol

end ArkLib.Lattices.Ajtai.InnerOuter

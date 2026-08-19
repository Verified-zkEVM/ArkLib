/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tobias Rothmann
-/
import ArkLib.Commitments.Functional.Hachi.Sumcheck.FinalEval

/-!
  # Partial evaluations — Hachi §4.5, Eq. (24) — skeleton

  First recursion adapter: peel the top `κ` variables of the evaluation claim
  `mle[w̃](a) = y′` produced by the §4.3 chain, in preparation for the `Z`-packing that closes
  the recursion (Hachi §4.5 "avoiding re-decomposition"; the §3.2 pattern).

  Writing `a = (a₀, a₁)` with `a₀ ∈ F^{mLow}` and `a₁ ∈ F^κ` (the extension degree is
  `k = 2^κ`), Eq. (24) factors the claim as

  `y′ = ∑_{i ∈ {0,1}^κ} eq(i, a₁) · yᵢ`, where `yᵢ := ∑_{j ∈ {0,1}^{mLow}} w̃_{j‖i}·eq(j, a₀)`.

  * **message (P→V)** — the partial evaluations `(yᵢ)_{i ≠ 0}` (all but one);
  * **derive-`y₀`** (paper footnote 10) — the verifier *derives*
    `y₀ := (y′ − ∑_{i ≠ 0} eq(i, a₁)·yᵢ) / eq(0, a₁)`-style instead of checking the display
    equation, keeping this head **pure** (total, no guard) and the Eq. (24) consistency true by
    construction;
  * **output** — the statement extended by the full derived family `(yᵢ)ᵢ`; residual claims:
    the per-`i` well-formedness `yᵢ = partialEvalAt w̃ a₀ i` for **every** `i ∈ {0,1}^κ`.

  This seam is **sound**: from the per-`i` claims and the derivation identity, the input claim
  `mle[w̃](a₀ ++ a₁) = y′` follows by the mle splitting identity (`wTableMleEval_split`), with
  zero soundness error. (The *next* seam — collapsing the per-`i` claims into the single
  `Z`-packed claim of Eq. (26) — is where the paper's §4.5/§3.2 argument has an apparent gap;
  see `Recursion/ZBatchBridge.lean`.)

  **Sorried**: the encoding defs (`partialEvalAt`, `deriveFamily`, `wTableMleEval_split`) and
  the CWSS theorem.

  ## References

  * [Nguyen, N. K., O'Rourke, G., and Zhang, J., *Hachi: Efficient Lattice-Based Multilinear
      Polynomial Commitments over Extension Fields*][NOZ26]
-/

namespace ArkLib.Lattices.Ajtai.InnerOuter

open CompPoly ArkLib.Lattices.CyclotomicModulus
open OracleComp OracleSpec ProtocolSpec CoordinateWise

/-- The partial-evaluation wire format: one prover message carrying the `2^κ − 1` partial
evaluations `(yᵢ)_{i ≠ 0}` (the remaining `y₀` is derived). -/
@[reducible] def pSpecPartialEval (F : Type) (κ : ℕ) : ProtocolSpec 1 :=
  ⟨!v[.P_to_V], !v[{i : Fin (2 ^ κ) // i ≠ 0} → F]⟩

/-- The partial-evaluation protocol has no challenge round: its single message is a `P→V`, so
the challenge index type is empty. -/
instance {F : Type} {κ : ℕ} : IsEmpty (pSpecPartialEval F κ).ChallengeIdx :=
  ⟨fun ⟨0, h⟩ => nomatch h⟩

/-- Sampleability of the challenges of `pSpecPartialEval`: vacuous, as there is no challenge
round (the challenge index type is empty). -/
instance {F : Type} {κ : ℕ} [SampleableType F] :
    ∀ i, SampleableType ((pSpecPartialEval F κ).Challenge i) :=
  fun i => isEmptyElim i

/-- The statement after the partial-evaluation step: the commitment, the *split* evaluation
point, and the full derived family of partial evaluations. -/
structure PartialEvalStatement (TCom F : Type) (mLow κ : ℕ) where
  /-- The `w̃`-commitment. -/
  t : TCom
  /-- The low point half `a₀ ∈ F^{mLow}` (the first `mLow` variables). -/
  pointLow : Fin mLow → F
  /-- The high point half `a₁ ∈ F^κ` (the last `κ` variables, to be peeled). -/
  pointHigh : Fin κ → F
  /-- The full family of partial evaluations `(yᵢ)ᵢ` — the sent `(yᵢ)_{i≠0}` together with the
  derived `y₀`. -/
  partials : Fin (2 ^ κ) → F

section Protocol

variable {q : ℕ} [NeZero q] [Fact (Nat.Prime q)] [BEq (ZMod q)] [LawfulBEq (ZMod q)]
  (Φ : CyclotomicModulus (ZMod q)) [IsCyclotomic Φ]
variable {n μ : ℕ} {F : Type} [Field F] [BEq F] [LawfulBEq F]
variable (mLow κ : ℕ) (bound ρBound : ℕ) (b : ℕ)
variable {ι : Type} {oSpec : OracleSpec ι} {σ : Type}

/-- The `i`-th true partial evaluation of the table (Eq. (24)):
`partialEvalAt w a₀ i = ∑_{j ∈ {0,1}^{mLow}} w̃_{j‖i}·eq(j, a₀)`. **Sorried** — index
bookkeeping over the `wTable` encoding. -/
def partialEvalAt (φF : ZMod q →+* F) (w : LiftedWitness Φ μ n)
    (a₀ : Fin mLow → F) (i : Fin (2 ^ κ)) : F :=
  sorry

/-- The Lagrange/equality weight `eq(i, a₁)` of the Boolean index `i ∈ {0,1}^κ` at the point
`a₁ ∈ F^κ` (little-endian bits of `i`, matching the `wTable` convention). **Sorried** —
`MvPolynomial.eqTilde` at the bit vector of `i`. -/
def eqWeight (a₁ : Fin κ → F) (i : Fin (2 ^ κ)) : F :=
  sorry

/-- The mle splitting identity behind Eq. (24):
`mle[w̃](a₀ ++ a₁) = ∑ᵢ eq(i, a₁)·partialEvalAt w̃ a₀ i`. **Sorried** — the `eq`
factorization `eq(j‖i, a₀‖a₁) = eq(j, a₀)·eq(i, a₁)`. -/
theorem wTableMleEval_split (φF : ZMod q →+* F) (w : LiftedWitness Φ μ n)
    (a : Fin (mLow + κ) → F) :
    wTableMleEval Φ (mLow + κ) φF b w a =
      ∑ i : Fin (2 ^ κ),
        eqWeight κ (fun j => a (Fin.natAdd mLow j)) i *
          partialEvalAt Φ mLow κ φF w (fun j => a (Fin.castAdd κ j)) i := by
  sorry

/-- Derive the full partial-evaluation family from the message (paper footnote 10):
install the sent `(yᵢ)_{i≠0}` and *derive* `y₀` so that Eq. (24)'s display equation holds by
construction. **Sorried** — needs `eq(0, a₁)`'s invertibility handling (the honest
derivation divides by `∏ⱼ (1 − a₁ⱼ)`; the degenerate case is absorbed into the derivation's
convention and the CWSS proof). -/
def deriveFamily (value : F) (pointHigh : Fin κ → F)
    (msg : {i : Fin (2 ^ κ) // i ≠ 0} → F) : Fin (2 ^ κ) → F :=
  sorry

/-- The partial-evaluation verifier (Hachi §4.5, Eq. (24)): a **pure** head — it splits the
point, installs the sent partials, and derives `y₀`. No runtime check. -/
def partialEvalVerifier {TCom : Type} :
    Verifier oSpec (WEvalStatement TCom F (mLow + κ)) (PartialEvalStatement TCom F mLow κ)
      (pSpecPartialEval F κ) where
  verify := fun stmt tr =>
    pure ⟨stmt.t, fun j => stmt.point (Fin.castAdd κ j), fun j => stmt.point (Fin.natAdd mLow j),
      deriveFamily κ stmt.value (fun j => stmt.point (Fin.natAdd mLow j)) (tr 0)⟩

/-- The honest partial-evaluation prover skeleton: sends the true partials at the nonzero
indices (the parameter `computeY`, honestly `partialEvalAt`). -/
def partialEvalProver {TCom Wit : Type}
    (computeY : WEvalStatement TCom F (mLow + κ) → Wit →
      {i : Fin (2 ^ κ) // i ≠ 0} → F) :
    Prover oSpec (WEvalStatement TCom F (mLow + κ)) Wit
      (PartialEvalStatement TCom F mLow κ) Wit
      (pSpecPartialEval F κ) where
  PrvState
    | 0 => WEvalStatement TCom F (mLow + κ) × Wit
    | 1 => WEvalStatement TCom F (mLow + κ) × Wit
  input := id
  sendMessage
    | ⟨0, _⟩ => fun st => pure (computeY st.1 st.2, st)
  receiveChallenge
    | ⟨0, h⟩ => nomatch h
  output := fun ⟨stmt, wit⟩ =>
    pure (⟨stmt.t, fun j => stmt.point (Fin.castAdd κ j), fun j => stmt.point (Fin.natAdd mLow j),
      deriveFamily κ stmt.value (fun j => stmt.point (Fin.natAdd mLow j))
        (computeY stmt wit)⟩, wit)

/-- **The per-`i` partial-evaluation relation** (the residual claims of Eq. (24)): `w̃` is a
*short* opening of `t` and *every* partial evaluation in the derived family is well-formed. This
seam is the sound stopping point of the §4.5 peeling; collapsing it into the single `Z`-packed
claim is the `Recursion/ZBatchBridge.lean` step (⚠ see there).

The `liftShort` conjunct is the commitment's shortness index, carried unchanged from
`relWEvalClaim` (see there for why a norm-free seam is not an option) and consumed at the §4.5
handoff, whose output must exhibit the *next* iteration's `Short`. -/
def relPartialEval (K : LiftCom (LiftedWitness Φ μ n) (liftShort Φ bound ρBound))
    (φF : ZMod q →+* F) :
    Set (PartialEvalStatement K.TCom F mLow κ × (LiftedWitness Φ μ n)) :=
  {p |
    K.com p.2 = p.1.t ∧
    liftShort Φ bound ρBound p.2 ∧
    ∀ i, partialEvalAt Φ mLow κ φF p.2 p.1.pointLow i = p.1.partials i}

variable [SampleableType F]

/-- **The partial-evaluation extraction algorithm.**

**Sorried** — this def is the extraction *algorithm* itself (the transcript-level pull-back of the
proof plan on `partialEval_coordinateWiseSpecialSoundWith`). -/
noncomputable def partialEvalExtractor
    (K : LiftCom (LiftedWitness Φ μ n) (liftShort Φ bound ρBound))
    (φF : ZMod q →+* F) :
    Extractor.TreeBased (WEvalStatement K.TCom F (mLow + κ)) (LiftedWitness Φ μ n)
      (pSpecPartialEval F κ)
      (CWSSStructure.toShape (CWSSStructure.ofIsEmpty
        (pSpec := pSpecPartialEval F κ))).arity :=
  sorry

/-- **CWSS of the partial-evaluation head — a sound, zero-error seam, at the
named `partialEvalExtractor`** (the named form is deliberate — see
`Verifier.treeSpecialSoundWith`; closing this gap means filling the extractor and this
specification about it).

**Sorried.** Proof plan: no challenge round, so CWSS collapses to a transcript-level pull-back
(the no-challenge bridge; the verifier is pure): from a `relPartialEval` witness at the derived
statement, the mle splitting identity `wTableMleEval_split` plus the derivation construction
(`deriveFamily` makes Eq. (24)'s display equation true by fiat, and the per-`i` claims pin every
`partials i` to the true partial) yield `mle[w̃](a₀ ++ a₁) = y′`, i.e. `relWEvalClaim`
membership. -/
theorem partialEval_coordinateWiseSpecialSoundWith
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (K : LiftCom (LiftedWitness Φ μ n) (liftShort Φ bound ρBound))
    (φF : ZMod q →+* F) :
    Verifier.coordinateWiseSpecialSoundWith init impl
      CWSSStructure.ofIsEmpty
      (relWEvalClaim Φ (mLow + κ) bound ρBound b K φF)
      (relPartialEval Φ mLow κ bound ρBound K φF)
      (partialEvalVerifier (oSpec := oSpec) mLow κ (TCom := K.TCom) (F := F))
      (partialEvalExtractor Φ mLow κ bound ρBound K φF) := by
  sorry

/-- **The partial-evaluation head as a (plain) `CWSSPackage`** (Hachi §4.5, Eq. (24)): the pure
one-message derive-`y₀` head with the empty challenge structure, reducing the evaluation claim
`relWEvalClaim` to the per-`i` claims `relPartialEval`. A sound, zero-error reshaping, hence
escape-free. -/
noncomputable def partialEvalPackage (init : ProbComp σ)
    (impl : QueryImpl oSpec (StateT σ ProbComp))
    (K : LiftCom (LiftedWitness Φ μ n) (liftShort Φ bound ρBound))
    (φF : ZMod q →+* F) :
    CWSSPackage init impl
      (WEvalStatement K.TCom F (mLow + κ)) (LiftedWitness Φ μ n)
      (PartialEvalStatement K.TCom F mLow κ) (LiftedWitness Φ μ n)
      (pSpecPartialEval F κ) where
  verifier := partialEvalVerifier (oSpec := oSpec) mLow κ (TCom := K.TCom) (F := F)
  struct := CWSSStructure.ofIsEmpty
  relIn := relWEvalClaim Φ (mLow + κ) bound ρBound b K φF
  relOut := relPartialEval Φ mLow κ bound ρBound K φF
  isPure := ⟨fun stmt tr =>
    ⟨stmt.t, fun j => stmt.point (Fin.castAdd κ j), fun j => stmt.point (Fin.natAdd mLow j),
      deriveFamily κ stmt.value (fun j => stmt.point (Fin.natAdd mLow j)) (tr 0)⟩,
    fun _ _ => rfl⟩
  extractor := partialEvalExtractor Φ mLow κ bound ρBound K φF
  isCWSS := partialEval_coordinateWiseSpecialSoundWith Φ mLow κ bound ρBound b init impl K φF

end Protocol

end ArkLib.Lattices.Ajtai.InnerOuter

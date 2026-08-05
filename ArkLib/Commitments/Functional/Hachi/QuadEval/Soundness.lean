/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tobias Rothmann
-/
import ArkLib.Commitments.Functional.Hachi.QuadEval.Reduction
import ArkLib.Commitments.Functional.Hachi.Gadget.Norms
import ArkLib.OracleReduction.Security.CoordinateWiseSpecialSoundness.Escape
import ArkLib.OracleReduction.Security.CoordinateWiseSpecialSoundness.SingleRound

/-!
  # Hachi polynomial-evaluation reduction (`QuadEval`) — coordinate-wise special soundness
    (Hachi Lemma 8)

  **Hachi Lemma 8** (Hachi [NOZ26] §4.2, Figure 3, p. 17–18): the `QuadEval` reduction of
  `QuadEval/Reduction.lean` is coordinate-wise special sound. Concretely: from `2ʳ+1` accepting
  transcripts whose challenge vectors form a star in `SS(C, 2ʳ, 2)` — a central branch plus, for
  each coordinate `j`, a sibling branch differing from it exactly at `j` — the tree extractor
  either reconstructs a valid weak `InnerOuter.Opening` by subtract-and-divide (subtract the
  central branch's response from the sibling's, then divide by the invertible challenge
  difference), or outputs a Module-SIS solution for `B` or `D`. The file is `sorry`-free.

  ## Main definitions

  * `quadEvalZL2SqBound` — the reduction's derived `B_z`: the `ℓ₂²` bound on the recomposed
    `z = J ẑ` that follows from Eq. (20)'s range check on `ẑ` alone (no extra verifier check).
  * `quadEvalBetaSq` — Lemma 8's `βSq := 4·B_z`, the bound on the extracted `c̄ⱼ •ᵥ sⱼ` fed to
    `VerifiedBlock.scaled_short`.
  * `extractedOpening` — the subtract-and-divide weak opening assembled from a star of accepting
    branches (total, no `IsUnit`/star hypotheses; correctness lives in the lemmas below).
  * `buildWitness` — Lemma 8's three-case extraction result: divergent inner/carrier
    decompositions give `B`/`D`-kernel Module-SIS breaks; otherwise the star yields
    `extractedOpening`. Its sum is protocol-local data, split into:
  * `quadEvalMkWitness` — the plain (`WitIn`-valued) witness assembler fed to the generic
    single-round assembly, and
  * `quadEvalEscLocal` — the reduction's **escape event** in local per-star form: "the tree's own
    responses make extraction land in a Module-SIS break valid for the fixed key `pp`".
  * `quadEvalPackage` — the reduction as an `EscapeCWSSPackage`.

  ## Main results

  * `msis_of_commit_eq` — two-transcript step of cases (A)/(B): two `γ`-short openings of the
    same commitment differ by an `ℓ∞`-short (bound `2·γ`) Module-SIS solution.
  * `inner_eq_of_chain` — the unit-cancellation core of subtract-and-divide.
  * `slack_isUnit` — the challenge slack `c̄ⱼ` is a unit, by Lyubashevsky–Seiler [LS18]
    invertibility of short elements.
  * `verifiedOpening_of_star`, `evalConsistency_of_relOut_star` — case (C): the extracted
    opening is a `VerifiedOpening` at `βSq`/`γ`/`2ω` and satisfies Eq. (15) eval-consistency.
  * `buildWitness_break_or_mem_relIn` — every local result is either a concrete break in the
    key-tied `quadEvalSISSet` of the fixed `pp`, or an opening in the plain `relIn`.
  * `quadEval_coordinateWiseSpecialSoundWithEscape` — **the advertised Lemma 8 statement**, and the
    one the composed chain consumes: a *named-extractor*, escape-threaded CWSS certificate at
    `relIn`/`relOut`, whose escape disjunct is the tight, key-tied event
    `SingleRound.escEvent relOut quadEvalEscLocal`. Feeds `quadEvalPackage`'s certificate.

  Mirroring `InnerOuter/Security.lean`, the extraction lemmas carry the Lyubashevsky–Seiler
  [LS18] hypotheses `q ≡ 5 (mod 8)`, `(2ω)² < q` (only there does challenge invertibility
  enter), so they are stated over the power-of-two modulus `𝓜(q, α)`. An `OracleVerifier`
  wrapper is deliberately omitted (see the comment after the top-level theorem); the
  plain-`Verifier` statement is the intended Lemma 8 interface.

  Same namespace/opens discipline as `QuadEval/Reduction.lean`
  (`namespace ArkLib.Lattices.Ajtai.InnerOuter`, `open WeakBinding`; never `open ArkLib.Lattices`).

  ## References

  * [Nguyen, N. K., and Seiler, G., *Greyhound: Fast Polynomial Commitments from Lattices*][NS24]
  * [Nguyen, N. K., O'Rourke, G., and Zhang, J., *Hachi: Efficient Lattice-Based Multilinear
      Polynomial Commitments over Extension Fields*][NOZ26]
  * [Lyubashevsky, V., and Seiler, G., *Short, Invertible Elements in Partially Splitting
      Cyclotomic Rings and Applications to Lattice-Based Zero-Knowledge Proofs*][LS18]
-/

namespace ArkLib.Lattices.Ajtai.InnerOuter

open CompPoly ArkLib.Lattices.CyclotomicModulus
open WeakBinding
open OracleComp OracleSpec ProtocolSpec CoordinateWise CoordinateWise.SingleRound

/-! ## The constants of Hachi's polynomial-evaluation reduction (`B_z`, `βSq`) -/

/-- **The reduction's derived `B_z`** (Hachi Lemma 8) — the `ℓ₂²` bound on `z = J_{2^m}·ẑ` that
follows from
Eq. (20)'s range check on `ẑ` alone (no extra verifier check): `z` has `2^m·δ` entries
(`cols = 2^m·δ`, `d = deg φ`, `τ = ⌈log_b β⌉` digits of the `J` gadget), so
`B_z = 2^m·δ · (d · ((∑_{u<τ} bᵘ)·γ)²)`.

**Honest values (paper footnote):** `γ` plays the paper's `b` — Eq. (20) checks
`ẑ ∈ S_b` (centered coefficients in `[⌈-b/2⌉, ⌈b/2⌉-1]`, magnitude `≤ b`), which the
symmetric model relaxes to `‖ẑ‖∞ ≤ γ` with `γ := b`. Then the entrywise `ℓ∞` bound
`(∑_{u<τ} bᵘ)·b = b·(b^τ-1)/(b-1) ≤ 2·b^τ` recovers (up to the constant 2) the paper's
derived `‖z⁽ʲ⁾‖∞ ≤ b^τ` (Lemma 8's `β̄ = 2b^τ` slack), and
`B_z ≈ 2^m·δ·d·b^{2τ}` up to small constants. -/
def quadEvalZL2SqBound (γ b τ d m δ : ℕ) : ℕ := zRecomposeL2SqBound γ b τ d (2 ^ m * δ)

/-- **The reduction's `βSq`** (Hachi Lemma 8) := `subL2NormSqBound B_z = 4·B_z` — the `ℓ₂²` bound
on the extracted `c̄ⱼ •ᵥ sⱼ = z_sib − z_central` fed to `VerifiedBlock.scaled_short`. -/
def quadEvalBetaSq (γ b τ d m δ : ℕ) : ℕ := subL2NormSqBound (quadEvalZL2SqBound γ b τ d m δ)

section Extraction

variable {q : ℕ} [NeZero q] [Fact (Nat.Prime q)] [BEq (ZMod q)] [LawfulBEq (ZMod q)]
  (Φ : CyclotomicModulus (ZMod q)) [IsCyclotomic Φ]
variable {innerRows messageRows messageDigits outerRows blocks innerDigits dRows zDigits
  m r : Nat}

omit [NeZero q] in
/-- Eq. (15) for the extracted opening (an internal step of Hachi Lemma 8, case (C)): from c3
(`dot b w = y`) and the c4-subtractions (`wⱼ = dot a (derivedMessage o j)`), the extracted
opening is eval-consistent. -/
theorem evalConsistency_of_star (base : ZMod q) (a : PolyVec (Rq Φ) (2 ^ m))
    (b : PolyVec (Rq Φ) (2 ^ r)) (y : Rq Φ)
    (o : Opening Φ innerRows (2 ^ m) messageDigits (2 ^ r) innerDigits)
    (w : PolyVec (Rq Φ) (2 ^ r)) (c3 : dot b w = y)
    (c4 : ∀ j, w j = dot a (derivedMessage Φ base o.toDecomp j)) :
    evalConsistency Φ base a b y o := by
  unfold evalConsistency
  rw [splitForm, ← c3, dot_eq_sum, dot_eq_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [c4 j, matVecMul_apply, dot_comm]
  rfl

/-! ## The two-transcript MSIS extraction step (Hachi Lemma 8, cases (A)/(B)) -/

/-- **Hachi Lemma 8, cases (A)/(B), two-transcript step**: two `γ`-short openings of the same
commitment under `M` differ by an `ℓ∞`-short kernel vector — a Module-SIS solution for `M` at
the bound `subLInftyNormBound γ = 2·γ`. Instantiated at `M = B` with `outerShort` (case (A))
and at `M = D` with `dShort` (case (B)) in `buildWitness_break_or_mem_relIn`. -/
theorem msis_of_commit_eq {rows cols γ : ℕ}
    (M : Simple.PublicParams Φ rows cols) {u : Simple.Commitment Φ rows}
    {x₁ x₂ : PolyVec (Rq Φ) cols}
    (h₁ : Simple.commit Φ M x₁ = u) (h₂ : Simple.commit Φ M x₂ = u)
    (hγ₁ : vecLInftyNorm Φ x₁ ≤ γ) (hγ₂ : vecLInftyNorm Φ x₂ ≤ γ) (hne : x₁ ≠ x₂) :
    ModuleSIS.relation Φ (fun z => decide (vecLInftyNorm Φ z ≤ subLInftyNormBound γ)) M (x₁ - x₂)
      = true := by
  have hker : M *ᵥ (x₁ - x₂) = 0 := by
    rw [matVecMul_sub]
    exact sub_eq_zero.mpr (by simpa [Simple.commit] using h₁.trans h₂.symm)
  simp [ModuleSIS.relation, sub_ne_zero.mpr hne, sub_lInftyNorm_le Φ _ _ hγ₁ hγ₂, hker]

/-! ## The subtract-and-divide core step (`inner_eq` via `Ring.inverse`) -/

omit [NeZero q] in
/-- The c5-side unit-cancellation of the subtract-and-divide extraction (Hachi Lemma 8, case (C)):
from the c5-subtract chain `c̄ᵢ •ᵥ (G_{n_A} t̂ᵢ) = A *ᵥ Δz` and `IsUnit c̄ᵢ`, the extracted
message block `sᵢ := Ring.inverse c̄ᵢ •ᵥ Δz` satisfies the weak-opening inner gadget relation
(`VerifiedBlock.inner_eq`). -/
theorem inner_eq_of_chain {base : ZMod q} {cols : Nat}
    (A : Simple.PublicParams Φ innerRows cols)
    (that : Simple.Message Φ (innerRows * innerDigits)) (zdiff : PolyVec (Rq Φ) cols)
    (c : Rq Φ) (hc : IsUnit c)
    (hchain : c •ᵥ Simple.commit Φ (gadgetMatrix Φ base innerRows innerDigits) that =
      A *ᵥ zdiff) :
    Simple.commit Φ (gadgetMatrix Φ base innerRows innerDigits) that
      = Simple.commit Φ A (Ring.inverse c •ᵥ zdiff) := by
  have hAs : Simple.commit Φ A (Ring.inverse c •ᵥ zdiff) = Ring.inverse c •ᵥ (A *ᵥ zdiff) := by
    simp only [Simple.commit]; rw [matVecMul_scalarVecMul]
  rw [hAs, ← hchain]; funext i
  simp only [scalarVecMul_apply, ← mul_assoc, Ring.inverse_mul_cancel c hc, one_mul]

end Extraction

/-! ## The extracted opening and the witness assembler (generic `Φ`) -/

section BuildWitness

variable {q : ℕ} [NeZero q] [Fact (Nat.Prime q)] [BEq (ZMod q)] [LawfulBEq (ZMod q)]
  (Φ : CyclotomicModulus (ZMod q)) [IsCyclotomic Φ]
variable {innerRows messageDigits outerRows innerDigits dRows zDigits m r ω : Nat}

/-- The subtract-and-divide weak opening extracted from a star of accepting branches
(Hachi Lemma 8, case (C)): per coordinate `j`, the message is
`sⱼ := c̄ⱼ⁻¹ •ᵥ (z^{(sib j)} − z^{(central)})` with `z^{(i)} := J ẑ^{(i)}`, the inner
decomposition is the shared central `t̂`, and the challenge is the slack
`c̄ⱼ := c_{sib j, j} − c_{central, j}`. Total — no `IsUnit`/star hypotheses at the definition
(`Ring.inverse` is total); correctness lives in `verifiedOpening_of_star`. -/
noncomputable def extractedOpening (base : ZMod q)
    (fam : Fin (2 ^ r + 1) → (Fin (2 ^ r) → ShortChallenge Φ ω))
    (resp : Fin (2 ^ r + 1) →
      QuadEvalResponse Φ innerRows (2 ^ m) messageDigits (2 ^ r) innerDigits zDigits) :
    Opening Φ innerRows (2 ^ m) messageDigits (2 ^ r) innerDigits :=
  let z : Fin (2 ^ r + 1) → PolyVec (Rq Φ) ((2 ^ m) * messageDigits) := fun j =>
    Hachi.jMatrix Φ base ((2 ^ m) * messageDigits) zDigits *ᵥ (resp j).zDec
  { message := fun j =>
      Ring.inverse ((fam (sib fam j) j).val - (fam (central fam) j).val) •ᵥ
        (z (sib fam j) - z (central fam))
    innerDecomp := (resp (central fam)).innerDec
    challenge := fun j => (fam (sib fam j) j).val - (fam (central fam) j).val }

open Classical in
/-- The reduction's witness assembler (Hachi Lemma 8's three-case extraction) — the `mkWitness`
argument of the generic extractor `E`:

* some branch's (flattened) inner decomposition `t̂` differs from the central one → a
  `B`-kernel Module-SIS solution;
* else some branch's carrier decomposition `ŵ` differs from the central one → a `D`-kernel
  Module-SIS solution;
* else all branches share `t̂` and `ŵ`, and the star's subtract-and-divide yields the weak
  opening `extractedOpening`.

("Two branches differ" is equivalent to "some branch differs from the central one": if two
branches disagree, at least one of them disagrees with the central branch.) The sum is
**protocol-local data**: the left summand is the ordinary opening witness and the right summand a
concrete Module-SIS break of the fixed key `pp` (`quadEvalSISSet Φ pp γ`). The two summands are
separated below into the plain extractor `quadEvalMkWitness` and the escape event
`quadEvalEscLocal`; correctness is `buildWitness_break_or_mem_relIn`. -/
noncomputable def buildWitness (base : ZMod q)
    (fam : Fin (2 ^ r + 1) → (Fin (2 ^ r) → ShortChallenge Φ ω))
    (resp : Fin (2 ^ r + 1) →
      QuadEvalResponse Φ innerRows (2 ^ m) messageDigits (2 ^ r) innerDigits zDigits) :
    QuadEvalWitness Φ innerRows (2 ^ m) messageDigits (2 ^ r) innerDigits ⊕
      QuadEvalSISBreak Φ innerRows messageDigits outerRows (2 ^ r) innerDigits dRows :=
  if hB : ∃ j, PolyVec.flattenBlocks (resp j).innerDec
      ≠ PolyVec.flattenBlocks (resp (central fam)).innerDec then
    .inr (.msisB
      (PolyVec.flattenBlocks (resp hB.choose).innerDec -
        PolyVec.flattenBlocks (resp (central fam)).innerDec))
  else if hD : ∃ j, (resp j).carrierDec ≠ (resp (central fam)).carrierDec then
    .inr (.msisD
      ((resp hD.choose).carrierDec - (resp (central fam)).carrierDec))
  else
    .inl (extractedOpening Φ base fam resp)

/-- **The reduction's escape event, in local (per-star) form** — the `escLocal` argument of
`SingleRound.escEvent`: at a shared message `v` and a star-shaped challenge family with per-branch
responses, the three-case extraction lands in its Module-SIS branch with a break that is **valid for
the fixed key `pp`**.

Against the escape-event contract (`ChallengeTree.EscapeEvent`): the conjunct
`br ∈ quadEvalSISSet Φ pp γ` alone says `br` is a short nonzero kernel vector of `pp`'s `B` or `D`
matrix — a Module-SIS solution for the *actual, statement-independent* key ([NOZ26] Remark 2 /
Lemma 7) — and it says so at every `(stmt, v, fam, resp)`, including ones no honest execution
produces. The event reads only the message, the challenge family and the responses, which the
ambient `SingleRound.escEvent` pins to the tree's own data. The `buildWitness … = Sum.inr br` is
what makes it *tight*: it fires only where extraction genuinely cannot return an opening. -/
def quadEvalEscLocal (base : ZMod q)
    (pp : Hachi.PublicParamsD Φ innerRows (2 ^ m) messageDigits outerRows (2 ^ r) innerDigits
      dRows) (γ : ℕ) :
    QuadEvalStatement Φ innerRows (2 ^ m) messageDigits outerRows (2 ^ r) innerDigits dRows →
    CarrierCom Φ dRows →
    (Fin (2 ^ r + 1) → (Fin (2 ^ r) → ShortChallenge Φ ω)) →
    (Fin (2 ^ r + 1) →
      QuadEvalResponse Φ innerRows (2 ^ m) messageDigits (2 ^ r) innerDigits zDigits) → Prop :=
  fun _ _ fam resp =>
    ∃ br ∈ quadEvalSISSet Φ pp γ, buildWitness Φ base fam resp = Sum.inr br

/-- **The reduction's plain witness assembler** — the `mkWitness` argument of
`SingleRound.coordinateWiseSpecialSoundWithEscape_of_mkWitness`: `buildWitness`'s opening branch,
with the (total) `extractedOpening` as the fallback on its Module-SIS branch. The fallback is
irrelevant to soundness: on exactly those inputs `quadEvalEscLocal` fires, so the certificate's left
disjunct carries the conclusion. -/
noncomputable def quadEvalMkWitness (base : ZMod q)
    (_stmt : QuadEvalStatement Φ innerRows (2 ^ m) messageDigits outerRows (2 ^ r) innerDigits
      dRows)
    (_v : CarrierCom Φ dRows)
    (fam : Fin (2 ^ r + 1) → (Fin (2 ^ r) → ShortChallenge Φ ω))
    (resp : Fin (2 ^ r + 1) →
      QuadEvalResponse Φ innerRows (2 ^ m) messageDigits (2 ^ r) innerDigits zDigits) :
    QuadEvalWitness Φ innerRows (2 ^ m) messageDigits (2 ^ r) innerDigits :=
  (buildWitness (outerRows := outerRows) (dRows := dRows) Φ base fam resp).elim id
    (fun _ => extractedOpening Φ base fam resp)

omit [NeZero q] in
/-- On `buildWitness`'s opening branch, `quadEvalMkWitness` *is* that opening. -/
theorem quadEvalMkWitness_of_inl (base : ZMod q)
    (stmt : QuadEvalStatement Φ innerRows (2 ^ m) messageDigits outerRows (2 ^ r) innerDigits
      dRows)
    (v : CarrierCom Φ dRows)
    (fam : Fin (2 ^ r + 1) → (Fin (2 ^ r) → ShortChallenge Φ ω))
    (resp : Fin (2 ^ r + 1) →
      QuadEvalResponse Φ innerRows (2 ^ m) messageDigits (2 ^ r) innerDigits zDigits)
    {w : QuadEvalWitness Φ innerRows (2 ^ m) messageDigits (2 ^ r) innerDigits}
    (hw : buildWitness (outerRows := outerRows) (dRows := dRows) Φ base fam resp = Sum.inl w) :
    quadEvalMkWitness Φ base stmt v fam resp = w := by
  unfold quadEvalMkWitness
  rw [hw]
  rfl

omit [NeZero q] [IsCyclotomic Φ] in
/-- Coordinate difference transfers from the `ShortChallenge` subtype to the underlying ring
vectors — the bridge from `sib_coordEq` (subtype-level `CoordEq`) to the ring-level
coordinate-isolation lemmas `tensorG_coord_diff`/`tensorG1_coord_diff` (`QuadEval/Gadgets.lean`). -/
theorem ShortChallenge.coordEq_val {ℓ : ℕ} {i : Fin ℓ} {x y : Fin ℓ → ShortChallenge Φ ω}
    (h : CoordEq i x y) :
    CoordEq i (fun j => (x j).val) (fun j => (y j).val) :=
  ⟨ShortChallenge.val_ne_of_ne h.1, fun j hj => congrArg ShortChallenge.val (h.2 j hj)⟩

end BuildWitness

/-! ## The extraction lemmas and the top-level theorem (pinned to `𝓜(q, α)`)

Only here does the Lyubashevsky–Seiler invertibility enter (`isUnit_of_l1Norm_le` is pinned
to the power-of-two modulus), so — mirroring `InnerOuter/Security.lean` — the statements are
pinned to `𝓜(q, α)` and carry the [LS18] hypotheses `q ≡ 5 (mod 8)`, `(2ω)² < q`. -/

section Pinned

variable {q : ℕ} [NeZero q] [Fact (Nat.Prime q)] [BEq (ZMod q)] [LawfulBEq (ZMod q)] {α : ℕ}
variable {innerRows messageDigits outerRows innerDigits dRows zDigits m r : Nat}

/-- The slack `c̄ᵢ := c_{sib i, i} − c_{central, i}` of a star-shaped short-challenge family is a
unit: it is nonzero (the sibling differs at `i`), `ℓ₁`-bounded by `2ω` (two subtype challenges),
and `(2ω)² < q` — Lyubashevsky–Seiler [LS18] invertibility. -/
theorem slack_isUnit (hq5 : q % 8 = 5) {ω : ℕ} (hκ : (2 * ω) ^ 2 < q)
    (fam : Fin (2 ^ r + 1) → (Fin (2 ^ r) → ShortChallenge 𝓜(q, α) ω))
    (hstar : ∃ e, StarAt fam e) (i : Fin (2 ^ r)) :
    IsUnit ((fam (sib fam i) i).val - (fam (central fam) i).val) :=
  isUnit_of_l1Norm_le α hq5
    (Rq.l1Norm_pos_of_ne_zero 𝓜(q, α)
      (sub_ne_zero_of_ne (ShortChallenge.val_ne_of_ne (sib_coordEq_ne fam hstar i))))
    (ShortChallenge.l1Norm_val_sub_le _ _) hκ

/-- **Weak-opening validity of the extracted opening** (Hachi Lemma 8, case (C), part 1).
At a star-shaped family of `2^r + 1` `relOut`-accepting branches sharing the carrier commitment
`v` and (cases (A)/(B) excluded) sharing `t̂` and `ŵ`, the subtract-and-divide
`extractedOpening` is a `VerifiedOpening` at

* `βSq := quadEvalBetaSq γ b zDigits (deg φ) m messageDigits = 4·B_z`, the `Gadget/Norms`-derived
  `J`-recomposition bound (`deg φ = 2^α`; no primitive `‖z‖₂²` verifier check anywhere);
* `γ' := γ` — **not** `2γ`: `outer_short` constrains the extracted opening's `innerDecomp`,
  which is the CENTRAL branch's `t̂` verbatim, and relOut c6 bounds it by `γ` directly (the
  `2γ` slack of `subLInftyNormBound` is only for the *difference* witnesses of cases (A)/(B));
* `κ := 2ω`, the slack bound for `c̄ⱼ = c_{sib j, j} − c_{central, j}` from two `‖·‖₁ ≤ ω`
  subtype challenges (`ShortChallenge.l1Norm_val_sub_le`). -/
theorem verifiedOpening_of_star (hq5 : q % 8 = 5) {b ω γ : ℕ} (hκ : (2 * ω) ^ 2 < q)
    (hτ : 0 < zDigits)
    (pp : Hachi.PublicParamsD 𝓜(q, α) innerRows (2 ^ m) messageDigits outerRows (2 ^ r)
      innerDigits dRows)
    (stmt : QuadEvalStatement 𝓜(q, α) innerRows (2 ^ m) messageDigits outerRows (2 ^ r) innerDigits
      dRows)
    (v : CarrierCom 𝓜(q, α) dRows)
    (fam : Fin (2 ^ r + 1) → (Fin (2 ^ r) → ShortChallenge 𝓜(q, α) ω))
    (resp : Fin (2 ^ r + 1) →
      QuadEvalResponse 𝓜(q, α) innerRows (2 ^ m) messageDigits (2 ^ r) innerDigits zDigits)
    (hrel : ∀ j, ((stmt, v, fam j), resp j) ∈ relOut 𝓜(q, α) pp (b : ZMod q) ω γ)
    (hstar : ∃ e, StarAt fam e)
    (ht : ∀ j, (resp j).innerDec = (resp (central fam)).innerDec)
    (_hw : ∀ j, (resp j).carrierDec = (resp (central fam)).carrierDec) :
    VerifiedOpening 𝓜(q, α) (b : ZMod q)
      (quadEvalBetaSq γ b zDigits ((𝓜(q, α)).φ.natDegree) m messageDigits) γ (2 * ω)
      pp.toPublicParams stmt.u
      (extractedOpening 𝓜(q, α) (b : ZMod q) fam resp) := by
  -- `outer_eq` / `outer_short` are c2 / c6t of the central branch (the extracted `innerDecomp`
  -- IS the central `t̂`, so the `γ` bound applies verbatim — no `2γ` slack).
  obtain ⟨-, hc2e, -, -, -, -, hc6te, -⟩ := hrel (central fam)
  refine ⟨hc2e, hc6te, fun i => ?_⟩
  -- Block `i`: the slack `c̄ᵢ` is a unit (Lyubashevsky–Seiler).
  have hunit := slack_isUnit hq5 hκ fam hstar i
  refine ⟨hunit, ShortChallenge.l1Norm_val_sub_le _ _, ?_, ?_⟩
  · -- scaled_short: `c̄ᵢ •ᵥ (c̄ᵢ⁻¹ •ᵥ Δzᵢ) = Δzᵢ = J ẑ^{(sib i)} − J ẑ^{(e)}`, then the
    -- `J`-recomposition ℓ₂² bound from the two branches' c6z (`Gadget/Norms.lean`).
    have h1 : 1 ≤ (𝓜(q, α)).φ.natDegree := by
      rw [hachiModulus_natDegree]; exact Nat.one_le_two_pow
    obtain ⟨-, -, -, -, -, -, -, hc6zs⟩ := hrel (sib fam i)
    obtain ⟨-, -, -, -, -, -, -, hc6ze⟩ := hrel (central fam)
    have hcancel : (extractedOpening 𝓜(q, α) (b : ZMod q) fam resp).challenge i •ᵥ
        (extractedOpening 𝓜(q, α) (b : ZMod q) fam resp).message i
        = Hachi.jMatrix 𝓜(q, α) (b : ZMod q) ((2 ^ m) * messageDigits) zDigits *ᵥ
            (resp (sib fam i)).zDec
          - Hachi.jMatrix 𝓜(q, α) (b : ZMod q) ((2 ^ m) * messageDigits) zDigits *ᵥ
            (resp (central fam)).zDec := by
      simp only [extractedOpening]
      funext k
      simp only [scalarVecMul_apply, ← mul_assoc, Ring.mul_inverse_cancel _ hunit, one_mul]
    rw [hcancel]
    exact gadgetMul_zmod_sub_l2NormSq_le 𝓜(q, α) hτ h1
      (resp (sib fam i)).zDec (resp (central fam)).zDec hc6zs hc6ze
  · -- inner_eq: the c5-subtract chain, shared `t̂ := (resp e).innerDec`, coordinate-isolated
    -- and unit-divided.
    have hcoord : CoordEq i (fun k => (fam (sib fam i) k).val)
        (fun k => (fam (central fam) k).val) :=
      ShortChallenge.coordEq_val 𝓜(q, α) (coordEq_symm (sib_coordEq fam hstar i))
    obtain ⟨-, -, -, -, hc5s, -, -, -⟩ := hrel (sib fam i)
    obtain ⟨-, -, -, -, hc5e, -, -, -⟩ := hrel (central fam)
    rw [ht (sib fam i)] at hc5s
    have hchain : ((fam (sib fam i) i).val - (fam (central fam) i).val) •ᵥ
        (gadgetMatrix 𝓜(q, α) (b : ZMod q) innerRows innerDigits *ᵥ
          (resp (central fam)).innerDec i)
        = pp.innerMatrix *ᵥ
          (Hachi.jMatrix 𝓜(q, α) (b : ZMod q) ((2 ^ m) * messageDigits) zDigits *ᵥ
              (resp (sib fam i)).zDec
           - Hachi.jMatrix 𝓜(q, α) (b : ZMod q) ((2 ^ m) * messageDigits) zDigits *ᵥ
              (resp (central fam)).zDec) := by
      rw [matVecMul_sub, ← hc5s, ← hc5e, ← Hachi.tensorG_sub_challenge,
        Hachi.tensorG_coord_diff 𝓜(q, α) (b : ZMod q) innerRows innerDigits hcoord]
    simp only [extractedOpening]
    exact inner_eq_of_chain 𝓜(q, α) pp.innerMatrix
      ((resp (central fam)).innerDec i) _
      ((fam (sib fam i) i).val - (fam (central fam) i).val) hunit hchain

/-- **Eval-consistency of the extracted opening** (Hachi Lemma 8, case (C), part 2 — Eq. (15)):
the shared-`ŵ` c3 row plus the coordinate-isolated, unit-divided c4 rows discharge the
`w`/`c3`/`c4` hypotheses of `evalConsistency_of_star` at the shared recomposed carrier
`w := G_{2^r} *ᵥ ŵ`. -/
theorem evalConsistency_of_relOut_star (hq5 : q % 8 = 5) {b ω γ : ℕ} (hκ : (2 * ω) ^ 2 < q)
    (pp : Hachi.PublicParamsD 𝓜(q, α) innerRows (2 ^ m) messageDigits outerRows (2 ^ r)
      innerDigits dRows)
    (stmt : QuadEvalStatement 𝓜(q, α) innerRows (2 ^ m) messageDigits outerRows (2 ^ r) innerDigits
      dRows)
    (v : CarrierCom 𝓜(q, α) dRows)
    (fam : Fin (2 ^ r + 1) → (Fin (2 ^ r) → ShortChallenge 𝓜(q, α) ω))
    (resp : Fin (2 ^ r + 1) →
      QuadEvalResponse 𝓜(q, α) innerRows (2 ^ m) messageDigits (2 ^ r) innerDigits zDigits)
    (hrel : ∀ j, ((stmt, v, fam j), resp j) ∈ relOut 𝓜(q, α) pp (b : ZMod q) ω γ)
    (hstar : ∃ e, StarAt fam e)
    (hw : ∀ j, (resp j).carrierDec = (resp (central fam)).carrierDec) :
    evalConsistency 𝓜(q, α) (b : ZMod q) stmt.avec stmt.bvec stmt.y
      (extractedOpening 𝓜(q, α) (b : ZMod q) fam resp) := by
  refine evalConsistency_of_star 𝓜(q, α) (b : ZMod q) stmt.avec stmt.bvec stmt.y
    (extractedOpening 𝓜(q, α) (b : ZMod q) fam resp)
    (gadgetMatrix 𝓜(q, α) (b : ZMod q) (2 ^ r) messageDigits *ᵥ (resp (central fam)).carrierDec)
    ?_ ?_
  · -- c3: verbatim c3 row of the central branch.
    obtain ⟨-, -, hc3, -, -, -, -, -⟩ := hrel (central fam)
    exact hc3
  · -- c4 j: the coordinate-isolated, unit-divided c4-subtract chain.
    intro j
    obtain ⟨-, -, -, hc4s, -, -, -, -⟩ := hrel (sib fam j)
    obtain ⟨-, -, -, hc4e, -, -, -, -⟩ := hrel (central fam)
    rw [hw (sib fam j)] at hc4s
    have hunit := slack_isUnit hq5 hκ fam hstar j
    have hcoord : CoordEq j (fun i => (fam (sib fam j) i).val)
        (fun i => (fam (central fam) i).val) :=
      ShortChallenge.coordEq_val 𝓜(q, α) (coordEq_symm (sib_coordEq fam hstar j))
    -- Subtract-and-isolate: the two branches' c4 rows, sharing `ŵ`, give `c̄ⱼ · wⱼ = aᵀ G Δzⱼ`.
    have hchain : dot stmt.avec (gadgetMatrix 𝓜(q, α) (b : ZMod q) (2 ^ m) messageDigits *ᵥ
          ((Hachi.jMatrix 𝓜(q, α) (b : ZMod q) ((2 ^ m) * messageDigits) zDigits *ᵥ
              (resp (sib fam j)).zDec)
           - (Hachi.jMatrix 𝓜(q, α) (b : ZMod q) ((2 ^ m) * messageDigits) zDigits *ᵥ
              (resp (central fam)).zDec)))
        = ((fam (sib fam j) j).val - (fam (central fam) j).val) *
            (gadgetMatrix 𝓜(q, α) (b : ZMod q) (2 ^ r) messageDigits *ᵥ
              (resp (central fam)).carrierDec) j := by
      rw [matVecMul_sub, dot_sub, ← hc4s, ← hc4e, ← Hachi.tensorG1_sub_challenge,
        Hachi.tensorG1_coord_diff 𝓜(q, α) (b : ZMod q) messageDigits hcoord]
    -- Divide by `c̄ⱼ`: the extracted message `sⱼ := c̄ⱼ⁻¹ •ᵥ Δzⱼ` recovers `wⱼ` under `aᵀ G`.
    change (gadgetMatrix 𝓜(q, α) (b : ZMod q) (2 ^ r) messageDigits *ᵥ
          (resp (central fam)).carrierDec) j
        = dot stmt.avec (gadgetMatrix 𝓜(q, α) (b : ZMod q) (2 ^ m) messageDigits *ᵥ
            (Ring.inverse ((fam (sib fam j) j).val - (fam (central fam) j).val) •ᵥ
              ((Hachi.jMatrix 𝓜(q, α) (b : ZMod q) ((2 ^ m) * messageDigits) zDigits *ᵥ
                  (resp (sib fam j)).zDec)
               - (Hachi.jMatrix 𝓜(q, α) (b : ZMod q) ((2 ^ m) * messageDigits) zDigits *ᵥ
                  (resp (central fam)).zDec))))
    rw [matVecMul_scalarVecMul, dot_scalarVecMul, hchain, ← mul_assoc,
      Ring.inverse_mul_cancel _ hunit, one_mul]

/-- **The local extractor is correct** — the mathematical content of Hachi Lemma 8's three-case
split. At every star-shaped family of `relOut`-accepting branches, `buildWitness` either returns a
concrete break of the fixed key `pp` (an element of `quadEvalSISSet`) or an opening lying in
`relIn`.

The first disjunct is exactly the escape event `quadEvalEscLocal`; the second gives the plain
assembler `quadEvalMkWitness` its `relIn`-membership (via `quadEvalMkWitness_of_inl`). Together they
feed `SingleRound.coordinateWiseSpecialSoundWithEscape_of_mkWitness`. -/
theorem buildWitness_break_or_mem_relIn (hq5 : q % 8 = 5) {b ω γ : ℕ}
    (hκ : (2 * ω) ^ 2 < q)
    (hτ : 0 < zDigits)
    (pp : Hachi.PublicParamsD 𝓜(q, α) innerRows (2 ^ m) messageDigits outerRows (2 ^ r)
      innerDigits dRows)
    (stmt : QuadEvalStatement 𝓜(q, α) innerRows (2 ^ m) messageDigits outerRows (2 ^ r) innerDigits
      dRows)
    (v : CarrierCom 𝓜(q, α) dRows)
    (fam : Fin (2 ^ r + 1) → (Fin (2 ^ r) → ShortChallenge 𝓜(q, α) ω))
    (resp : Fin (2 ^ r + 1) →
      QuadEvalResponse 𝓜(q, α) innerRows (2 ^ m) messageDigits (2 ^ r) innerDigits zDigits)
    (hrel : ∀ j, ((stmt, v, fam j), resp j) ∈ relOut 𝓜(q, α) pp (b : ZMod q) ω γ)
    (hstar : ∃ e, StarAt fam e) :
    (∃ br ∈ quadEvalSISSet 𝓜(q, α) pp γ,
        buildWitness (outerRows := outerRows) (dRows := dRows) 𝓜(q, α) (b : ZMod q) fam resp
          = Sum.inr br) ∨
      ∃ w, buildWitness (outerRows := outerRows) (dRows := dRows) 𝓜(q, α) (b : ZMod q) fam resp
          = Sum.inl w ∧
        (stmt, w) ∈ relIn 𝓜(q, α) pp (b : ZMod q)
          (quadEvalBetaSq γ b zDigits ((𝓜(q, α)).φ.natDegree) m messageDigits) γ (2 * ω) := by
  by_cases hB : ∃ j, PolyVec.flattenBlocks (resp j).innerDec
      ≠ PolyVec.flattenBlocks (resp (central fam)).innerDec
  · -- Case (A): some branch's inner decomposition differs → `B`-kernel MSIS solution
    -- (both branches' c2 commit to the shared `stmt.u`).
    refine Or.inl ⟨.msisB (PolyVec.flattenBlocks (resp hB.choose).innerDec -
      PolyVec.flattenBlocks (resp (central fam)).innerDec), ?_, ?_⟩
    · obtain ⟨-, hu₁, -, -, -, -, hγ₁, -⟩ := hrel hB.choose
      obtain ⟨-, hu₂, -, -, -, -, hγ₂, -⟩ := hrel (central fam)
      exact msis_of_commit_eq 𝓜(q, α) pp.outerMatrix hu₁ hu₂ hγ₁ hγ₂ hB.choose_spec
    · unfold buildWitness
      rw [dif_pos hB]
  · by_cases hD : ∃ j, (resp j).carrierDec ≠ (resp (central fam)).carrierDec
    · -- Case (B): shared `t̂` but some carrier decomposition differs → `D`-kernel MSIS solution
      -- (the shared round-0 message `v` is what makes both branches commit to the same `v`).
      refine Or.inl ⟨.msisD ((resp hD.choose).carrierDec -
        (resp (central fam)).carrierDec), ?_, ?_⟩
      · obtain ⟨hv₁, -, -, -, -, hγ₁, -, -⟩ := hrel hD.choose
        obtain ⟨hv₂, -, -, -, -, hγ₂, -, -⟩ := hrel (central fam)
        exact msis_of_commit_eq 𝓜(q, α) pp.dMatrix hv₁ hv₂ hγ₁ hγ₂ hD.choose_spec
      · unfold buildWitness
        rw [dif_neg hB, dif_pos hD]
    · -- Case (C): shared `t̂` and `ŵ` → the subtract-and-divide weak opening.
      refine Or.inr ⟨extractedOpening 𝓜(q, α) (b : ZMod q) fam resp, ?_, ?_⟩
      · unfold buildWitness
        rw [dif_neg hB, dif_neg hD]
      · push Not at hB hD
        have ht : ∀ j, (resp j).innerDec = (resp (central fam)).innerDec :=
          fun j => funext fun i => PolyVec.block_eq_of_flattenBlocks_eq (hB j) i
        exact ⟨verifiedOpening_of_star hq5 hκ hτ pp stmt v fam resp hrel hstar ht hD,
          evalConsistency_of_relOut_star hq5 hκ pp stmt v fam resp hrel hstar hD⟩

/-- **Hachi Lemma 8 (CWSS of Hachi's polynomial-evaluation reduction, Figure 3; originally
Greyhound's [NS24, §3.1] folding protocol), escape-threaded.** `relIn` contains only an
eval-consistent weak opening, `relOut` Eq. (20) plus its range checks, and the extractor is a plain
tree-based extractor. The Module-SIS(B/D) outcomes of the three-case extraction appear as the
certificate's *escape disjunct*: the event `SingleRound.escEvent relOut quadEvalEscLocal`, which
fires on a `(statement, tree)` pair exactly when that tree's own `relOut`-responses make the
extraction land in a genuine Module-SIS break of the fixed key `pp` (honesty argument:
`quadEvalEscLocal`).

**Paper parameter mapping (an intentional generalization).** The theorem is stated over ArkLib's
generalized relation and exposes `(βSq, γ, κ)` as free parameters: `βSq = quadEvalBetaSq γ b …` is
a squared-`ℓ₂` bound on the scaled blocks (the shape `VerifiedOpening` records), `γ` is the
symmetric-ball range bound of c6, and `κ = 2ω`. Hachi Lemma 8 fixes the specific triple
`(β̄, ω̄, γ̄) = (2·bᵗ, 2ω, b)`. Instantiating `γ := b` matches `γ̄ = b` and `ω̄ = 2ω` exactly, but
**not** `β̄`: ArkLib's `VerifiedOpening` records a squared-`ℓ₂` bound `βSq` on the scaled blocks
(not the paper's `ℓ₂`/`ℓ∞` value `2·bᵗ`), a deliberate modeling choice (see `quadEvalZL2SqBound`).
That `γ := b` instantiation is the named corollary
`quadEval_coordinateWiseSpecialSoundWithEscape_paperParams` below. The paper's exact `S_b`-box
output relation is `QuadEval/Reduction.paperRelOut`, with the `paperRelOut ⊆ relOut` containment
proved as `QuadEval/Reduction.paperRelOut_subset_relOut`.

Assembled by `SingleRound.coordinateWiseSpecialSoundWithEscape_of_mkWitness`, which discharges
every tree/extractor/guard obligation generically; the protocol-specific content is
`buildWitness_break_or_mem_relIn`. -/
theorem quadEval_coordinateWiseSpecialSoundWithEscape
    {ι : Type} {oSpec : OracleSpec ι} {σ : Type}
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (hq5 : q % 8 = 5) {b ω γ : ℕ} (hκ : (2 * ω) ^ 2 < q) (hτ : 0 < zDigits)
    (pp : Hachi.PublicParamsD 𝓜(q, α) innerRows (2 ^ m) messageDigits outerRows (2 ^ r)
      innerDigits dRows) :
    Verifier.coordinateWiseSpecialSoundWithEscape init impl
      (foldStructure (CarrierCom := CarrierCom 𝓜(q, α) dRows)
        (C := ShortChallenge 𝓜(q, α) ω) (r := r))
      (escEvent (relOut (zDigits := zDigits) 𝓜(q, α) pp (b : ZMod q) ω γ)
        (quadEvalEscLocal (zDigits := zDigits) 𝓜(q, α) (b : ZMod q) pp γ))
      (relIn 𝓜(q, α) pp (b : ZMod q)
        (quadEvalBetaSq γ b zDigits ((𝓜(q, α)).φ.natDegree) m messageDigits) γ (2 * ω))
      (relOut (zDigits := zDigits) 𝓜(q, α) pp (b : ZMod q) ω γ)
      (verifier (oSpec := oSpec) (ω := ω) 𝓜(q, α) (innerRows := innerRows)
        (messageDigits := messageDigits) (outerRows := outerRows)
        (innerDigits := innerDigits) (dRows := dRows) (m := m) (r := r))
      (treeExtractor (relOut (zDigits := zDigits) 𝓜(q, α) pp (b : ZMod q) ω γ)
        (quadEvalMkWitness (outerRows := outerRows) 𝓜(q, α) (b : ZMod q))) := by
  refine coordinateWiseSpecialSoundWithEscape_of_mkWitness init impl _ (fun _ _ => rfl) _ _ _ _
    (fun stmtIn v fam resp hbranch hstar => ?_)
  rcases buildWitness_break_or_mem_relIn hq5 hκ hτ pp stmtIn v fam resp hbranch hstar with
    hbad | ⟨w, hw, hmem⟩
  · exact Or.inl hbad
  · refine Or.inr ?_
    rw [quadEvalMkWitness_of_inl 𝓜(q, α) (b : ZMod q) stmtIn v fam resp hw]
    exact hmem

/-- **Paper-parameter instantiation of Hachi Lemma 8** — the named bridge to the paper's
weak-opening contract. This is `quadEval_coordinateWiseSpecialSoundWithEscape` specialized to the
paper's range `γ := b`. Two of the paper's three Lemma 8 bounds match **exactly**: `γ̄ = b` and
`ω̄ = 2ω`. The third does **not**: the paper's `β̄ = 2·bᵗ` (an `ℓ₂`/`ℓ∞` bound on `‖c̄ᵢsᵢ‖`) is
replaced by ArkLib's `βSq = quadEvalBetaSq b b zDigits (deg φ) m messageDigits`, a
*squared-`ℓ₂`* bound on the scaled blocks carrying extra `2ᵐ·δ·(deg φ)` dimensional factors — a
deliberate `VerifiedOpening` modeling choice, not a paper-faithful value (see
`quadEvalZL2SqBound`). Later binding code should cite this entry point; the general-`γ` theorem
above is the intentional ArkLib generalization, and
`QuadEval/Reduction.paperRelOut_subset_relOut` proves the `paper ⊆ code` containment on the
output relation (for `b / 2 ≤ γ`, in particular `γ := b`). -/
theorem quadEval_coordinateWiseSpecialSoundWithEscape_paperParams
    {ι : Type} {oSpec : OracleSpec ι} {σ : Type}
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (hq5 : q % 8 = 5) {b ω : ℕ} (hκ : (2 * ω) ^ 2 < q) (hτ : 0 < zDigits)
    (pp : Hachi.PublicParamsD 𝓜(q, α) innerRows (2 ^ m) messageDigits outerRows (2 ^ r)
      innerDigits dRows) :
    Verifier.coordinateWiseSpecialSoundWithEscape init impl
      (foldStructure (CarrierCom := CarrierCom 𝓜(q, α) dRows)
        (C := ShortChallenge 𝓜(q, α) ω) (r := r))
      (escEvent (relOut (zDigits := zDigits) 𝓜(q, α) pp (b : ZMod q) ω b)
        (quadEvalEscLocal (zDigits := zDigits) 𝓜(q, α) (b : ZMod q) pp b))
      (relIn 𝓜(q, α) pp (b : ZMod q)
        (quadEvalBetaSq b b zDigits ((𝓜(q, α)).φ.natDegree) m messageDigits) b (2 * ω))
      (relOut (zDigits := zDigits) 𝓜(q, α) pp (b : ZMod q) ω b)
      (verifier (oSpec := oSpec) (ω := ω) 𝓜(q, α) (innerRows := innerRows)
        (messageDigits := messageDigits) (outerRows := outerRows)
        (innerDigits := innerDigits) (dRows := dRows) (m := m) (r := r))
      (treeExtractor (relOut (zDigits := zDigits) 𝓜(q, α) pp (b : ZMod q) ω b)
        (quadEvalMkWitness (outerRows := outerRows) 𝓜(q, α) (b : ZMod q))) :=
  quadEval_coordinateWiseSpecialSoundWithEscape (γ := b) init impl hq5 hκ hτ pp

/-- **The escape-aware `QuadEval` package.** `relIn` is the ordinary opening relation, `relOut` the
Eq.-(20) response relation, and `extractor` the actual Lemma 8 extraction algorithm
(`quadEvalMkWitness`), exposed by composed chains via `.extractor`. Its one escape-specific field is
the `esc` event, firing exactly on trees whose responses yield a genuine break of the fixed key
`pp`. -/
noncomputable def quadEvalPackage {ι : Type} {oSpec : OracleSpec ι} {σ : Type}
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (hq5 : q % 8 = 5) {b ω γ : ℕ} (hκ : (2 * ω) ^ 2 < q) (hτ : 0 < zDigits)
    (pp : Hachi.PublicParamsD 𝓜(q, α) innerRows (2 ^ m) messageDigits outerRows (2 ^ r)
      innerDigits dRows) :
    EscapeCWSSPackage init impl
      (QuadEvalStatement 𝓜(q, α) innerRows (2 ^ m) messageDigits outerRows (2 ^ r) innerDigits
        dRows)
      (QuadEvalWitness 𝓜(q, α) innerRows (2 ^ m) messageDigits (2 ^ r) innerDigits)
      (QuadEvalStatement 𝓜(q, α) innerRows (2 ^ m) messageDigits outerRows (2 ^ r) innerDigits
          dRows ×
        CarrierCom 𝓜(q, α) dRows × (Fin (2 ^ r) → ShortChallenge 𝓜(q, α) ω))
      (QuadEvalResponse 𝓜(q, α) innerRows (2 ^ m) messageDigits (2 ^ r) innerDigits zDigits)
      (pSpec (CarrierCom 𝓜(q, α) dRows) (ShortChallenge 𝓜(q, α) ω) r) where
  verifier := verifier (oSpec := oSpec) (ω := ω) 𝓜(q, α)
  struct :=
    foldStructure (CarrierCom := CarrierCom 𝓜(q, α) dRows)
      (C := ShortChallenge 𝓜(q, α) ω) (r := r)
  relIn := relIn 𝓜(q, α) pp (b : ZMod q)
    (quadEvalBetaSq γ b zDigits ((𝓜(q, α)).φ.natDegree) m messageDigits) γ (2 * ω)
  relOut := relOut (zDigits := zDigits) 𝓜(q, α) pp (b : ZMod q) ω γ
  esc := escEvent (relOut (zDigits := zDigits) 𝓜(q, α) pp (b : ZMod q) ω γ)
    (quadEvalEscLocal (zDigits := zDigits) 𝓜(q, α) (b : ZMod q) pp γ)
  isPure := ⟨fun stmt tr => (stmt, tr.messages ⟨0, rfl⟩, tr.challenges ⟨1, rfl⟩), fun _ _ => rfl⟩
  extractor := treeExtractor (relOut (zDigits := zDigits) 𝓜(q, α) pp (b : ZMod q) ω γ)
    (quadEvalMkWitness (outerRows := outerRows) 𝓜(q, α) (b : ZMod q))
  isCWSS := quadEval_coordinateWiseSpecialSoundWithEscape init impl hq5 hκ hτ pp

-- An `OracleVerifier` wrapper is deliberately not included: it needs an `OracleInterface`
-- instance for `Simple.Commitment` (a query-model design decision that does not exist in the
-- repo yet) and the still-sorried oracle-level append theorem. The plain-`Verifier` statement
-- above is the right interface for Lemma 8; the oracle wrapper belongs to the composition step.

end Pinned

end ArkLib.Lattices.Ajtai.InnerOuter

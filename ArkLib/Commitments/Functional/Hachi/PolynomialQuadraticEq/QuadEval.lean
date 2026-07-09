/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tobias Rothmann
-/
import ArkLib.Commitments.Functional.Hachi.PolynomialQuadraticEq.QuadEvalGadgets
import ArkLib.Commitments.Functional.Hachi.InnerOuter.Security
import ArkLib.OracleReduction.Security.CoordinateWiseSpecialSoundness.SingleRound
import ArkLib.OracleReduction.Security.CoordinateWiseSpecialSoundness.Package

/-!
  # Hachi polynomial-evaluation reduction (QuadEval) — coordinate-wise special soundness
    (Hachi Lemma 8)

  Hachi's polynomial-evaluation reduction proves `f(x) = y` by rewriting the evaluation as the
  quadratic form `bᵀ M a` and folding the `2ʳ` carrier blocks under the verifier's challenge
  vector — hence the name `QuadEval`. It is Hachi's multilinear / inner-outer lift of Greyhound's
  [NS24, §3.1] polynomial-evaluation protocol.

  **Lemma 8** (Hachi [NOZ26] §4.2, Figure 3, p. 17–18): this reduction is coordinate-wise special
  sound. From `2ʳ+1` accepting transcripts with challenge vectors in `SS(C, 2ʳ, 2)`, the tree
  extractor either reconstructs a valid weak `InnerOuter.Opening` by subtract-and-divide, or
  outputs a Module-SIS solution for `B` or `D`.

  The reduction is modeled as the two-round
  `pSpec ⟨!v[.P_to_V, .V_to_P], !v[CarrierCom, Fin 2ʳ → C]⟩`: round 0 (P→V) sends the short
  commitment `v = D ŵ`; round 1 (V→P) is the challenge vector. The triple `(ŵ, t̂, ẑ)` is the
  **output witness** (`QuadEvalResponse`, never sent — §4.3 proves knowledge of it instead), so
  the verifier is a pure pass-through and the extractor sources per-branch triples from
  `relOut.language`.

  Contents: the reduction's types and relations (`QuadEvalStatement`, `QuadEvalResponse`,
  `QuadEvalWitness`, `ShortChallenge`, `relOut` = Eq. (20) + range checks, `relIn` = weak opening
  ∨ MSIS(B) ∨ MSIS(D)); the pure `verifier` and the honest `prover` skeleton; the extractor
  (`extractedOpening`, `buildWitness`) with its correctness lemmas; and the top-level theorem
  `quadEval_coordinateWiseSpecialSound`.

  The file sits inside `namespace ArkLib.Lattices.Ajtai.InnerOuter` (required: that namespace
  activates the scoped `PolyVec`/`*ᵥ`/`•ᵥ`/`dot`/`splitForm`), with `open WeakBinding` (so
  `VerifiedOpening`/`outerShort` resolve). Never `open ArkLib.Lattices` here (the `⬝ᵥ` token is
  ambiguous between `Matrix.dotProduct` and `ArkLib.Lattices.dot`); spell `dot _ _`.

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

/-! ## Generic definitions (any coefficient field `R`) -/

section Defs

variable {R : Type} [Field R] [BEq R] [LawfulBEq R] (Φ : CyclotomicModulus R) [IsCyclotomic Φ]
variable {innerRows messageRows messageDigits outerRows blocks innerDigits dRows zDigits : Nat}

/-- The carrier commitment space: `v = D ŵ` lives in the `D`-row space. -/
abbrev CarrierCom (Φ : CyclotomicModulus R) (dRows : Nat) := Simple.Commitment Φ dRows

/-- Input statement of Hachi's polynomial-evaluation reduction (Hachi §4.2, Figure 3): the public
parameters `(A, B, D)`, the outer commitment `u`, the two evaluation basis vectors
`a ∈ Rq^{2^m}` (`avec`) and `b ∈ Rq^{2^r}` (`bvec`) of Eq. (12), and the claimed evaluation
`y = u_eval`. -/
structure QuadEvalStatement (Φ : CyclotomicModulus R)
    (innerRows messageRows messageDigits outerRows blocks innerDigits dRows : Nat) where
  /-- Public matrices `(A, B, D)`. -/
  pp : Hachi.PublicParamsD Φ innerRows messageRows messageDigits outerRows blocks innerDigits dRows
  /-- The outer commitment `u`. -/
  u : Commitment Φ outerRows
  /-- The inner evaluation basis `aᵀ = (x_{r+1}^{j₁} ⋯ x_l^{j_m})_j ∈ Rq^{2^m}` (Eq. 12). -/
  avec : PolyVec (Rq Φ) messageRows
  /-- The outer evaluation basis `bᵀ = (x_1^{i₁} ⋯ x_r^{i_r})_i ∈ Rq^{2^r}` (Eq. 12). -/
  bvec : PolyVec (Rq Φ) blocks
  /-- The claimed evaluation `y = u_eval = f(x)`. -/
  y : Rq Φ

/-- The reduction's output witness `(ŵ, t̂, ẑ)` of Hachi Eq. (20) — Figure 3's final "message",
never sent in the composed protocol (§4.3 proves knowledge of it instead). Block-major layouts
(`finProdFinEquiv`, block = outer index). -/
structure QuadEvalResponse (Φ : CyclotomicModulus R)
    (innerRows messageRows messageDigits blocks innerDigits zDigits : Nat) where
  /-- `ŵ := G⁻¹_{2^r}(w)`, the decomposed carrier (block-major, `blocks · messageDigits`). -/
  carrierDec : PolyVec (Rq Φ) (blocks * messageDigits)
  /-- `t̂ = (t̂ᵢ)ᵢ`, the per-block inner decompositions. -/
  innerDec : PolyVec (PolyVec (Rq Φ) (innerRows * innerDigits)) blocks
  /-- `ẑ := J⁻¹(z)`, the decomposed masked opening (`τ = zDigits` digits). -/
  zDec : PolyVec (Rq Φ) ((messageRows * messageDigits) * zDigits)

/-- `QuadEvalResponse` is inhabited (the all-zero triple). -/
instance : Nonempty
    (QuadEvalResponse Φ innerRows messageRows messageDigits blocks innerDigits zDigits) :=
  ⟨⟨fun _ => 0, fun _ _ => 0, fun _ => 0⟩⟩

/-- The extracted (input-side) witness of Hachi Lemma 8: either a weak `Opening` for `u`, or a
Module-SIS solution for the outer matrix `B`, or one for the short-commitment matrix `D`. -/
inductive QuadEvalWitness (Φ : CyclotomicModulus R)
    (innerRows messageRows messageDigits blocks innerDigits : Nat) where
  /-- A weak opening `(sᵢ, t̂ᵢ, c̄ᵢ)ᵢ` for the outer commitment `u`. -/
  | opening (o : Opening Φ innerRows messageRows messageDigits blocks innerDigits)
  /-- A Module-SIS solution for the outer matrix `B`. -/
  | msisB (z : ModuleSIS.Solution Φ (blocks * (innerRows * innerDigits)))
  /-- A Module-SIS solution for the short-commitment matrix `D`. -/
  | msisD (z : ModuleSIS.Solution Φ (blocks * messageDigits))

/-- `QuadEvalWitness` is inhabited (a trivial `msisB` witness). -/
instance : Nonempty (QuadEvalWitness Φ innerRows messageRows messageDigits blocks innerDigits) :=
  ⟨.msisB (fun _ => 0)⟩

end Defs

/-! ## The challenge space (over `ZMod q`, where the norms live) -/

section ShortChallenge

variable {q : ℕ} [NeZero q] [Fact (Nat.Prime q)] [BEq (ZMod q)] [LawfulBEq (ZMod q)]

/-- **The reduction's challenge space, carried by the type** (Hachi §4.2): the paper's
`C ⊆ {c ∈ Rq : ‖c‖₁ ≤ ω}` is rendered as the subtype of `ℓ₁`-short ring elements. The
verifier's relation `relOut` therefore needs NO challenge-norm checks (faithful to Eq. (20),
which never checks the challenge); extraction recovers `‖cᵢ‖₁ ≤ ω` from the subtype property. -/
def ShortChallenge (Φ : CyclotomicModulus (ZMod q)) (ω : ℕ) : Type :=
  {c : Rq Φ // Rq.l1Norm Φ c ≤ ω}

variable {Φ : CyclotomicModulus (ZMod q)} [IsCyclotomic Φ] {ω : ℕ}

namespace ShortChallenge

/-- The underlying ring element `c ∈ Rq` of a short challenge (Hachi §4.2's challenge `cᵢ`). -/
def val (c : ShortChallenge Φ ω) : Rq Φ := Subtype.val c

omit [NeZero q] [IsCyclotomic Φ] in
/-- The subtype bound: every challenge is `ℓ₁`-short. -/
theorem l1Norm_le (c : ShortChallenge Φ ω) : ‖c.val‖₁ ≤ ω := Subtype.prop c

/-- Coordinate difference of two short challenges is `ℓ₁`-bounded by `2ω` — the extractor's
`hshort` for the slack `c̄ⱼ = c_{j,j} - c_{0,j}` (Hachi Lemma 8), for free from the subtype. -/
theorem l1Norm_val_sub_le (c c' : ShortChallenge Φ ω) : ‖c.val - c'.val‖₁ ≤ 2 * ω :=
  calc ‖c.val - c'.val‖₁ ≤ ‖c.val‖₁ + ‖c'.val‖₁ := Rq.l1Norm_sub_le Φ c.val c'.val
    _ ≤ ω + ω := Nat.add_le_add c.l1Norm_le c'.l1Norm_le
    _ = 2 * ω := (Nat.two_mul ω).symm

omit [NeZero q] [IsCyclotomic Φ] in
/-- `≠` on the subtype transfers to `≠` on the underlying ring elements — the extractor's
nonzero-slack input (`CoordEq` gives subtype-`≠` at the differing coordinate). -/
theorem val_ne_of_ne {c c' : ShortChallenge Φ ω} (h : c ≠ c') : c.val ≠ c'.val :=
  fun hval => h (Subtype.ext hval)

end ShortChallenge

end ShortChallenge

/-! ## Eval consistency (Eq. 15) and the relations -/

section ZModDefs

variable {q : ℕ} [NeZero q] [Fact (Nat.Prime q)] [BEq (ZMod q)] [LawfulBEq (ZMod q)]
  (Φ : CyclotomicModulus (ZMod q)) [IsCyclotomic Φ]
variable {innerRows messageRows messageDigits outerRows blocks innerDigits dRows zDigits
  m r : Nat}

/-- The matrix `M` of Hachi Eq. (15): row `i` = derived message block `G_{2^m} · sᵢ`; rows are
indexed by the outer basis `b`, columns by the inner basis `a`. -/
def derivedMsgMatrix (base : ZMod q)
    (o : Opening Φ innerRows (2 ^ m) messageDigits (2 ^ r) innerDigits) :
    PolyMatrix (Rq Φ) (2 ^ r) (2 ^ m) := fun i k => derivedMessage Φ base o.toDecomp i k

/-- Eq. (15): the derived messages of the weak opening evaluate to `y` under the split
bilinear form (`splitForm`, argument order `b a` load-bearing). -/
def evalConsistency (base : ZMod q) (a : PolyVec (Rq Φ) (2 ^ m)) (b : PolyVec (Rq Φ) (2 ^ r))
    (y : Rq Φ) (o : Opening Φ innerRows (2 ^ m) messageDigits (2 ^ r) innerDigits) : Prop :=
  splitForm (derivedMsgMatrix Φ base o) b a = y

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

/-- Shortness predicate for the extracted `D`-kernel witness (Hachi Lemma 8, case (B)): the
`D`-matrix analogue of `outerShort`, at `subLInftyNormBound γ = 2·γ`. -/
def dShort (γ : ℕ) : ModuleSIS.Solution Φ (blocks * messageDigits) → Bool :=
  fun z => decide (vecLInftyNorm Φ z ≤ subLInftyNormBound γ)

/-- **`relOut` — exactly Hachi Eq. (20) plus the `S_b` range checks** on
`((stmt, v, c), (ŵ, t̂, ẑ))`, with `z := J ẑ`:

* c1: `D ŵ = v`
* c2: `B (flatten t̂) = u`
* c3: `bᵀ (G_{2^r} ŵ) = y` (row 3 of Eq. (20), `u_eval`)
* c4: `(cᵀ ⊗ G₁) ŵ = aᵀ G_{2^m} J ẑ` (row 4; challenges coerced from the subtype)
* c5: `(cᵀ ⊗ G_{n_A}) t̂ = A J ẑ` (row 5)
* c6: the `S_b` range checks, as symmetric `ℓ∞` balls `≤ γ`.

**`S_b` modeling**: Eq. (20) checks `(ŵ, t̂, ẑ) ∈ S_b^…`, whose elements have centered
coefficients in `[⌈-b/2⌉, ⌈b/2⌉-1]`; c6 uses the symmetric ball `‖·‖∞ ≤ γ`, which with `γ ≥
⌈b/2⌉` **contains** the paper's box — so every Eq.-(20)-valid transcript is `relOut`-valid and
the CWSS theorem covers the paper's verifier. No challenge-norm checks appear (the challenge
TYPE carries `‖cᵢ‖₁ ≤ ω`), and no `‖z‖₂²` check appears (`‖z‖∞ ≤ …` is derived downstream from
c6's `‖ẑ‖∞ ≤ γ` via the `J`-recomposition norm lemma, `GadgetNorms.lean`) — both exactly as in the
paper. -/
def relOut (base : ZMod q) (ω γ : ℕ) :
    Set ((QuadEvalStatement Φ innerRows (2 ^ m) messageDigits outerRows (2 ^ r) innerDigits dRows ×
          CarrierCom Φ dRows × (Fin (2 ^ r) → ShortChallenge Φ ω)) ×
         QuadEvalResponse Φ innerRows (2 ^ m) messageDigits (2 ^ r) innerDigits zDigits) :=
  { p | match p with
    | ((stmt, v, chals), resp) =>
      let c : PolyVec (Rq Φ) (2 ^ r) := fun i => (chals i).val
      let z : PolyVec (Rq Φ) ((2 ^ m) * messageDigits) :=
        Hachi.jMatrix Φ base ((2 ^ m) * messageDigits) zDigits *ᵥ resp.zDec
      -- c1: `D ŵ = v`
      Simple.commit Φ stmt.pp.dMatrix resp.carrierDec = v ∧
      -- c2: `B (flatten t̂) = u`
      Simple.commit Φ stmt.pp.outerMatrix (PolyVec.flattenBlocks resp.innerDec) = stmt.u ∧
      -- c3: `bᵀ (G_{2^r} ŵ) = y`
      dot stmt.bvec (gadgetMatrix Φ base (2 ^ r) messageDigits *ᵥ resp.carrierDec) = stmt.y ∧
      -- c4: `(cᵀ ⊗ G₁) ŵ = aᵀ (G_{2^m} z)`
      Hachi.tensorG1 Φ base messageDigits c resp.carrierDec =
        dot stmt.avec (gadgetMatrix Φ base (2 ^ m) messageDigits *ᵥ z) ∧
      -- c5: `(cᵀ ⊗ G_{n_A}) t̂ = A z`
      Hachi.tensorG Φ base innerRows innerDigits c resp.innerDec =
        stmt.pp.innerMatrix *ᵥ z ∧
      -- c6: the `S_b` range checks (as `ℓ∞` balls)
      vecLInftyNorm Φ resp.carrierDec ≤ γ ∧
      vecLInftyNorm Φ (PolyVec.flattenBlocks resp.innerDec) ≤ γ ∧
      vecLInftyNorm Φ resp.zDec ≤ γ }

/-- **`relIn` — Hachi Lemma 8's extraction disjunction**: a weak `VerifiedOpening` for `u` that is
also eval-consistent (Eq. 15), or a Module-SIS solution for `B`, or one for `D`. The `.opening`
disjunct is the interface into `outputToModuleSIS_valid_of_verified` for the downstream
cross-run knowledge-soundness step. -/
def relIn (base : ZMod q) (βSq γ κ : ℕ) :
    Set (QuadEvalStatement Φ innerRows (2 ^ m) messageDigits outerRows (2 ^ r) innerDigits dRows ×
         QuadEvalWitness Φ innerRows (2 ^ m) messageDigits (2 ^ r) innerDigits) :=
  { p | match p with
    | (stmt, .opening o) =>
        VerifiedOpening Φ base βSq γ κ stmt.pp.toPublicParams stmt.u o ∧
        evalConsistency Φ base stmt.avec stmt.bvec stmt.y o
    | (stmt, .msisB z) =>
        ModuleSIS.relation Φ (outerShort Φ γ) stmt.pp.outerMatrix z = true
    | (stmt, .msisD z) =>
        ModuleSIS.relation Φ (dShort Φ γ) stmt.pp.dMatrix z = true }

/-! ## The two-transcript MSIS extraction step (Hachi Lemma 8, cases (A)/(B)) -/

/-- **Hachi Lemma 8, cases (A)/(B), two-transcript step**: two `γ`-short openings of the same
commitment under `M` differ by an `ℓ∞`-short kernel vector — a Module-SIS solution for `M` at
the bound `subLInftyNormBound γ = 2·γ`. Instantiated at `M = B` with `outerShort` (case (A))
and at `M = D` with `dShort` (case (B)) in `buildWitness_mem_relIn`. -/
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

/-! ## The protocol: pure pass-through verifier and honest prover -/

section Protocol

variable {ι : Type} {oSpec : OracleSpec ι} {ω : ℕ}

/-- The reduction's verifier (Hachi §4.2, Figure 3) is a **pure pass-through**: it re-emits the
statement, the round-0 carrier commitment `v`, and the round-1 challenge vector. The Eq.-(20)
checks live in `relOut` (the `(ŵ, t̂, ẑ)` triple is never sent — §4.3 proves knowledge of it),
so there is no runtime `guard`. -/
def verifier :
    Verifier oSpec
      (QuadEvalStatement Φ innerRows (2 ^ m) messageDigits outerRows (2 ^ r) innerDigits dRows)
      (QuadEvalStatement Φ innerRows (2 ^ m) messageDigits outerRows (2 ^ r) innerDigits dRows ×
        CarrierCom Φ dRows × (Fin (2 ^ r) → ShortChallenge Φ ω))
      (pSpec (CarrierCom Φ dRows) (ShortChallenge Φ ω) r) where
  verify := fun stmt tr => pure (stmt, tr.messages ⟨0, rfl⟩, tr.challenges ⟨1, rfl⟩)

/-- The honest prover (Hachi §4.2, Figure 3; completeness is out of scope for Lemma 8): round 0
sends the carrier commitment `v`, round 1 receives the challenge vector, and the output witness
is the `QuadEvalResponse` `(ŵ, t̂, ẑ)` of Eq. (20). The honest computations (`v = D ŵ` with
`ŵ = G⁻¹(w)`, `ẑ = J⁻¹(Σᵢ cᵢ sᵢ)`, …) are the parameters `computeV` / `computeResp`, to be
instantiated by the completeness layer from the `QuadEvalGadgets` carrier/decomposition
definitions. -/
def prover (WitIn : Type)
    (computeV :
      QuadEvalStatement Φ innerRows (2 ^ m) messageDigits outerRows (2 ^ r) innerDigits dRows →
      WitIn → CarrierCom Φ dRows)
    (computeResp :
      QuadEvalStatement Φ innerRows (2 ^ m) messageDigits outerRows (2 ^ r) innerDigits dRows →
      WitIn → (Fin (2 ^ r) → ShortChallenge Φ ω) →
      QuadEvalResponse Φ innerRows (2 ^ m) messageDigits (2 ^ r) innerDigits zDigits) :
    Prover oSpec
      (QuadEvalStatement Φ innerRows (2 ^ m) messageDigits outerRows (2 ^ r) innerDigits dRows)
      WitIn
      (QuadEvalStatement Φ innerRows (2 ^ m) messageDigits outerRows (2 ^ r) innerDigits dRows ×
        CarrierCom Φ dRows × (Fin (2 ^ r) → ShortChallenge Φ ω))
      (QuadEvalResponse Φ innerRows (2 ^ m) messageDigits (2 ^ r) innerDigits zDigits)
      (pSpec (CarrierCom Φ dRows) (ShortChallenge Φ ω) r) where
  PrvState
    | 0 =>
      QuadEvalStatement Φ innerRows (2 ^ m) messageDigits outerRows (2 ^ r) innerDigits dRows
        × WitIn
    | 1 =>
      QuadEvalStatement Φ innerRows (2 ^ m) messageDigits outerRows (2 ^ r) innerDigits dRows
        × WitIn
    | 2 =>
      (QuadEvalStatement Φ innerRows (2 ^ m) messageDigits outerRows (2 ^ r) innerDigits dRows
          × WitIn) × (Fin (2 ^ r) → ShortChallenge Φ ω)
  input := id
  sendMessage
    | ⟨0, _⟩ => fun st => pure (computeV st.1 st.2, st)
    | ⟨1, h⟩ => nomatch h
  receiveChallenge
    | ⟨0, h⟩ => nomatch h
    | ⟨1, _⟩ => fun st => pure fun c => (st, c)
  output := fun ⟨⟨stmt, wit⟩, c⟩ =>
    pure ((stmt, computeV stmt wit, c), computeResp stmt wit c)

end Protocol

end ZModDefs

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
branches disagree, at least one of them disagrees with the central branch.) Fully defined;
that each case lands in `relIn` is `buildWitness_mem_relIn`. -/
noncomputable def buildWitness (base : ZMod q)
    (_stmt :
      QuadEvalStatement Φ innerRows (2 ^ m) messageDigits outerRows (2 ^ r) innerDigits dRows)
    (_v : CarrierCom Φ dRows)
    (fam : Fin (2 ^ r + 1) → (Fin (2 ^ r) → ShortChallenge Φ ω))
    (resp : Fin (2 ^ r + 1) →
      QuadEvalResponse Φ innerRows (2 ^ m) messageDigits (2 ^ r) innerDigits zDigits) :
    QuadEvalWitness Φ innerRows (2 ^ m) messageDigits (2 ^ r) innerDigits :=
  if hB : ∃ j, PolyVec.flattenBlocks (resp j).innerDec
      ≠ PolyVec.flattenBlocks (resp (central fam)).innerDec then
    .msisB (PolyVec.flattenBlocks (resp hB.choose).innerDec -
      PolyVec.flattenBlocks (resp (central fam)).innerDec)
  else if hD : ∃ j, (resp j).carrierDec ≠ (resp (central fam)).carrierDec then
    .msisD ((resp hD.choose).carrierDec - (resp (central fam)).carrierDec)
  else
    .opening (extractedOpening Φ base fam resp)

omit [NeZero q] [IsCyclotomic Φ] in
/-- Coordinate difference transfers from the `ShortChallenge` subtype to the underlying ring
vectors — the bridge from `sib_coordEq` (subtype-level `CoordEq`) to the ring-level
coordinate-isolation lemmas `tensorG_coord_diff`/`tensorG1_coord_diff` (`QuadEvalGadgets.lean`). -/
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

* `βSq := quadEvalBetaSq γ b zDigits (deg φ) m messageDigits = 4·B_z`, the `GadgetNorms`-derived
  `J`-recomposition bound (`deg φ = 2^α`; no primitive `‖z‖₂²` verifier check anywhere);
* `γ' := γ` — **not** `2γ`: `outer_short` constrains the extracted opening's `innerDecomp`,
  which is the CENTRAL branch's `t̂` verbatim, and relOut c6 bounds it by `γ` directly (the
  `2γ` slack of `subLInftyNormBound` is only for the *difference* witnesses of cases (A)/(B));
* `κ := 2ω`, the slack bound for `c̄ⱼ = c_{sib j, j} − c_{central, j}` from two `‖·‖₁ ≤ ω`
  subtype challenges (`ShortChallenge.l1Norm_val_sub_le`). -/
theorem verifiedOpening_of_star (hq5 : q % 8 = 5) {b ω γ : ℕ} (hκ : (2 * ω) ^ 2 < q)
    (hτ : 0 < zDigits)
    (stmt : QuadEvalStatement 𝓜(q, α) innerRows (2 ^ m) messageDigits outerRows (2 ^ r) innerDigits
      dRows)
    (v : CarrierCom 𝓜(q, α) dRows)
    (fam : Fin (2 ^ r + 1) → (Fin (2 ^ r) → ShortChallenge 𝓜(q, α) ω))
    (resp : Fin (2 ^ r + 1) →
      QuadEvalResponse 𝓜(q, α) innerRows (2 ^ m) messageDigits (2 ^ r) innerDigits zDigits)
    (hrel : ∀ j, ((stmt, v, fam j), resp j) ∈ relOut 𝓜(q, α) (b : ZMod q) ω γ)
    (hstar : ∃ e, StarAt fam e)
    (ht : ∀ j, (resp j).innerDec = (resp (central fam)).innerDec)
    (_hw : ∀ j, (resp j).carrierDec = (resp (central fam)).carrierDec) :
    VerifiedOpening 𝓜(q, α) (b : ZMod q)
      (quadEvalBetaSq γ b zDigits ((𝓜(q, α)).φ.natDegree) m messageDigits) γ (2 * ω)
      stmt.pp.toPublicParams stmt.u
      (extractedOpening 𝓜(q, α) (b : ZMod q) fam resp) := by
  -- `outer_eq` / `outer_short` are c2 / c6t of the central branch (the extracted `innerDecomp`
  -- IS the central `t̂`, so the `γ` bound applies verbatim — no `2γ` slack).
  obtain ⟨-, hc2e, -, -, -, -, hc6te, -⟩ := hrel (central fam)
  refine ⟨hc2e, hc6te, fun i => ?_⟩
  -- Block `i`: the slack `c̄ᵢ` is a unit (Lyubashevsky–Seiler).
  have hunit := slack_isUnit hq5 hκ fam hstar i
  refine ⟨hunit, ShortChallenge.l1Norm_val_sub_le _ _, ?_, ?_⟩
  · -- scaled_short: `c̄ᵢ •ᵥ (c̄ᵢ⁻¹ •ᵥ Δzᵢ) = Δzᵢ = J ẑ^{(sib i)} − J ẑ^{(e)}`, then the
    -- `J`-recomposition ℓ₂² bound from the two branches' c6z (`GadgetNorms.lean`).
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
        = stmt.pp.innerMatrix *ᵥ
          (Hachi.jMatrix 𝓜(q, α) (b : ZMod q) ((2 ^ m) * messageDigits) zDigits *ᵥ
              (resp (sib fam i)).zDec
           - Hachi.jMatrix 𝓜(q, α) (b : ZMod q) ((2 ^ m) * messageDigits) zDigits *ᵥ
              (resp (central fam)).zDec) := by
      rw [matVecMul_sub, ← hc5s, ← hc5e, ← Hachi.tensorG_sub_challenge,
        Hachi.tensorG_coord_diff 𝓜(q, α) (b : ZMod q) innerRows innerDigits hcoord]
    simp only [extractedOpening]
    exact inner_eq_of_chain 𝓜(q, α) stmt.pp.innerMatrix
      ((resp (central fam)).innerDec i) _
      ((fam (sib fam i) i).val - (fam (central fam) i).val) hunit hchain

/-- **Eval-consistency of the extracted opening** (Hachi Lemma 8, case (C), part 2 — Eq. (15)):
the shared-`ŵ` c3 row plus the coordinate-isolated, unit-divided c4 rows discharge the
`w`/`c3`/`c4` hypotheses of `evalConsistency_of_star` at the shared recomposed carrier
`w := G_{2^r} *ᵥ ŵ`. -/
theorem evalConsistency_of_relOut_star (hq5 : q % 8 = 5) {b ω γ : ℕ} (hκ : (2 * ω) ^ 2 < q)
    (stmt : QuadEvalStatement 𝓜(q, α) innerRows (2 ^ m) messageDigits outerRows (2 ^ r) innerDigits
      dRows)
    (v : CarrierCom 𝓜(q, α) dRows)
    (fam : Fin (2 ^ r + 1) → (Fin (2 ^ r) → ShortChallenge 𝓜(q, α) ω))
    (resp : Fin (2 ^ r + 1) →
      QuadEvalResponse 𝓜(q, α) innerRows (2 ^ m) messageDigits (2 ^ r) innerDigits zDigits)
    (hrel : ∀ j, ((stmt, v, fam j), resp j) ∈ relOut 𝓜(q, α) (b : ZMod q) ω γ)
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

/-- **The witness assembler is correct** — the `hmk` input to the generic assembly
`coordinateWiseSpecialSound_of_mkWitness` (`SingleRound.lean`), and the mathematical content of
Hachi Lemma 8's three-case split: at every star-shaped family of `relOut`-accepting branches,
`buildWitness` lands in `relIn`. -/
theorem buildWitness_mem_relIn (hq5 : q % 8 = 5) {b ω γ : ℕ} (hκ : (2 * ω) ^ 2 < q)
    (hτ : 0 < zDigits)
    (stmt : QuadEvalStatement 𝓜(q, α) innerRows (2 ^ m) messageDigits outerRows (2 ^ r) innerDigits
      dRows)
    (v : CarrierCom 𝓜(q, α) dRows)
    (fam : Fin (2 ^ r + 1) → (Fin (2 ^ r) → ShortChallenge 𝓜(q, α) ω))
    (resp : Fin (2 ^ r + 1) →
      QuadEvalResponse 𝓜(q, α) innerRows (2 ^ m) messageDigits (2 ^ r) innerDigits zDigits)
    (hrel : ∀ j, ((stmt, v, fam j), resp j) ∈ relOut 𝓜(q, α) (b : ZMod q) ω γ)
    (hstar : ∃ e, StarAt fam e) :
    (stmt, buildWitness 𝓜(q, α) (b : ZMod q) stmt v fam resp) ∈
      relIn 𝓜(q, α) (b : ZMod q)
        (quadEvalBetaSq γ b zDigits ((𝓜(q, α)).φ.natDegree) m messageDigits) γ (2 * ω) := by
  unfold buildWitness
  by_cases hB : ∃ j, PolyVec.flattenBlocks (resp j).innerDec
      ≠ PolyVec.flattenBlocks (resp (central fam)).innerDec
  · -- Case (A): some branch's inner decomposition differs → `B`-kernel MSIS solution
    -- (both branches' c2 commit to the shared `stmt.u`).
    rw [dif_pos hB]
    obtain ⟨-, hu₁, -, -, -, -, hγ₁, -⟩ := hrel hB.choose
    obtain ⟨-, hu₂, -, -, -, -, hγ₂, -⟩ := hrel (central fam)
    exact msis_of_commit_eq 𝓜(q, α) stmt.pp.outerMatrix hu₁ hu₂ hγ₁ hγ₂ hB.choose_spec
  · by_cases hD : ∃ j, (resp j).carrierDec ≠ (resp (central fam)).carrierDec
    · -- Case (B): shared `t̂` but some carrier decomposition differs → `D`-kernel MSIS solution
      -- (the shared round-0 message `v` is what makes both branches commit to the same `v`).
      rw [dif_neg hB, dif_pos hD]
      obtain ⟨hv₁, -, -, -, -, hγ₁, -, -⟩ := hrel hD.choose
      obtain ⟨hv₂, -, -, -, -, hγ₂, -, -⟩ := hrel (central fam)
      exact msis_of_commit_eq 𝓜(q, α) stmt.pp.dMatrix hv₁ hv₂ hγ₁ hγ₂ hD.choose_spec
    · -- Case (C): shared `t̂` and `ŵ` → the subtract-and-divide weak opening.
      rw [dif_neg hB, dif_neg hD]
      push Not at hB hD
      have ht : ∀ j, (resp j).innerDec = (resp (central fam)).innerDec :=
        fun j => funext fun i => PolyVec.block_eq_of_flattenBlocks_eq (hB j) i
      exact ⟨verifiedOpening_of_star hq5 hκ hτ stmt v fam resp hrel hstar ht hD,
        evalConsistency_of_relOut_star hq5 hκ stmt v fam resp hrel hstar hD⟩

/-- **Hachi Lemma 8 (CWSS of Hachi's polynomial-evaluation reduction, Figure 3; originally
Greyhound's [NS24, §3.1] folding protocol).** The reduction's verifier is coordinate-wise
special sound for the `(ℓ, k) = (2^r, 2)` structure, with `relOut` = Eq. (20) + the `S_b` range
checks and `relIn` = weak opening (eval-consistent) ∨ MSIS(B) ∨ MSIS(D), at the derived
constants `βSq = quadEvalBetaSq γ b zDigits (deg φ) m messageDigits` and `κ = 2ω`.

Assembled by `coordinateWiseSpecialSound_of_mkWitness` (`SingleRound.lean`), which discharges
every tree/extractor/guard obligation generically; the whole of Hachi Lemma 8 thereby reduces
to the single math lemma `buildWitness_mem_relIn`. -/
theorem quadEval_coordinateWiseSpecialSound {ι : Type} {oSpec : OracleSpec ι} {σ : Type}
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (hq5 : q % 8 = 5) {b ω γ : ℕ} (hκ : (2 * ω) ^ 2 < q) (hτ : 0 < zDigits) :
    (verifier (oSpec := oSpec) (ω := ω) 𝓜(q, α) (innerRows := innerRows)
        (messageDigits := messageDigits) (outerRows := outerRows)
        (innerDigits := innerDigits) (dRows := dRows) (m := m)
        (r := r)).coordinateWiseSpecialSound init impl
      (foldStructure (CarrierCom := CarrierCom 𝓜(q, α) dRows)
        (C := ShortChallenge 𝓜(q, α) ω) (r := r))
      (relIn 𝓜(q, α) (b : ZMod q)
        (quadEvalBetaSq γ b zDigits ((𝓜(q, α)).φ.natDegree) m messageDigits) γ (2 * ω))
      (relOut (zDigits := zDigits) 𝓜(q, α) (b : ZMod q) ω γ) :=
  coordinateWiseSpecialSound_of_mkWitness init impl _ (fun _ _ => rfl) _ _
    (buildWitness 𝓜(q, α) (b : ZMod q))
    (fun stmtIn v fam resp hbranch hstar =>
      buildWitness_mem_relIn hq5 hκ hτ stmtIn v fam resp hbranch hstar)

-- An `OracleVerifier` wrapper is deliberately not included: it needs an `OracleInterface`
-- instance for `Simple.Commitment` (a query-model design decision that does not exist in the
-- repo yet) and the still-sorried oracle-level append theorem. The plain-`Verifier` statement
-- above is the right interface for Lemma 8; the oracle wrapper belongs to the composition step.

/-- **`QuadEval` as a `CWSSPackage`** (Hachi [NOZ26, §4.2, Figure 3]; Lemma 8): the two-round fold
`verifier` bundled with its `foldStructure` CWSS certificate `quadEval_coordinateWiseSpecialSound`,
ready to be `▷`-composed after the polynomial-level bridge. -/
def quadEvalPackage {ι : Type} {oSpec : OracleSpec ι} {σ : Type}
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (hq5 : q % 8 = 5) {b ω γ : ℕ} (hκ : (2 * ω) ^ 2 < q) (hτ : 0 < zDigits) :
    CWSSPackage init impl
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
    foldStructure (CarrierCom := CarrierCom 𝓜(q, α) dRows) (C := ShortChallenge 𝓜(q, α) ω) (r := r)
  relIn := relIn 𝓜(q, α) (b : ZMod q)
    (quadEvalBetaSq γ b zDigits ((𝓜(q, α)).φ.natDegree) m messageDigits) γ (2 * ω)
  relOut := relOut (zDigits := zDigits) 𝓜(q, α) (b : ZMod q) ω γ
  isPure := ⟨fun stmt tr => (stmt, tr.messages ⟨0, rfl⟩, tr.challenges ⟨1, rfl⟩), fun _ _ => rfl⟩
  isCWSS := quadEval_coordinateWiseSpecialSound init impl hq5 hκ hτ

end Pinned

end ArkLib.Lattices.Ajtai.InnerOuter

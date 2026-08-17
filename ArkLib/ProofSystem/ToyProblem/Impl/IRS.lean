/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

import ArkLib.Data.CodingTheory.ReedSolomon.Interleaved
import ArkLib.ProofSystem.ToyProblem.Spec.ErasureDecoder
import ArkLib.ProofSystem.ToyProblem.Spec.KnowledgeSoundness
import ArkLib.ProofSystem.ToyProblem.Spec.SimplifiedIOR
import ArkLib.ProofSystem.ToyProblem.SoundnessBounds

/-!
# Executable interleaved Reed--Solomon implementation for the toy problem

This file realizes the toy problem over the genuine interleaved alphabet `Fin s → F`.
A length-`k` scalar message is split into `s` rows of length `k / s`, each row is encoded
by the scalar Reed--Solomon encoder, and the resulting rows are exposed column-wise.

The divisibility hypothesis `s ∣ k` is part of every flattening API.  Consequently the
executable encoder has exactly `k` scalar input coordinates and its range is the current
`ReedSolomon.Interleaved.irsCode domain k s`, without silently dropping a remainder.

The definitions in the extraction path are computable.  Proofs may use classical logic,
but no proof-side choice is called by the encoder, decoder, agreement-set computation, or
transition extractor.

## Distance from here to a numeric knowledge error

Everything proven below is parametric: the shipped error keeps `ε_mca(C,δ)` and
`Λ(C^{≡2},δ)` symbolic, so no numeral is asserted at any parameter shape (see the
"Verified vs. admitted" section of `Spec/General.lean`).  For this interleaved-RS profile
the route to a numeral is short, and it is worth recording exactly what is missing:

* **MCA term.**  `ProximityGap.mcaError_interleaved_eq` (`ProximityGap/Errors.lean`,
  `sorry`-free) collapses the interleaved MCA error to the scalar one, so at radius
  `δ ∈ (0,1)` the `s`-interleaved code inherits the RS bound at message length `k / s`.
  The scalar bound itself, `rs_mcaError_le_in_johnson_range`
  (`ProximityGap/CapacityBounds.lean`), is the **one external admit** on this path
  ([BCHKS25, Thm 4.6]).
* **List term.**  Fully proven route, no admits:
  `ListDecodability.lambda_interleaved_le_choose_mul_pow` composed with
  `irs_lambda_le_johnson_mds` (both in `sorry`-free files), with
  `ReedSolomon.Interleaved.minDist_irsCode` supplying the relative-distance input.  What
  is missing is only real-arithmetic glue, not a mathematical input.
* **Coercions.**  The `ENNReal → ℝ≥0` bridges needed to land the two terms in the
  error type are proven.

So a numeric §6.4-shaped corollary would rest on exactly one external admit.  It is
deliberately not stated here.  Beyond the import-cone quarantine, the live downstream
consumer of these theorems cannot use an admit-backed numeral at all: it enforces a
transitive axiom closure of exactly `propext`, `Classical.choice`, `Quot.sound`, and it
reaches a numeric bound by a different, fully axiom-clean route — ArkLib's *unique-decoding*
correlated-agreement bound transported through interleaving, rather than the Johnson-range
MCA admit.  An admit-backed corollary here would therefore be a weaker-provenance parallel
route to the same quantity.  Any future numeric claim in-tree should adopt
`CapacityBounds.lean`'s "external admit unless stated" convention rather than pull that file
into the launch cone.
-/

namespace ToyProblem.Impl.IRS

open Code InterleavedCode CoreDefinitions
open Probability
open scoped NNReal ProbabilityTheory

variable {ι F : Type} [DecidableEq ι] [Field F] [DecidableEq F] [BEq F] [LawfulBEq F]

/-- Row-major equivalence between `s` rows of length `k / s` and a length-`k`
message.  The proof argument records that no coordinates are lost to division. -/
def irsIndexEquiv (k s : ℕ) (hdvd : s ∣ k) : Fin s × Fin (k / s) ≃ Fin k :=
  finProdFinEquiv.trans (finCongr (Nat.mul_div_cancel' hdvd))

/-- Split a length-`k` scalar message into `s` rows of length `k / s`. -/
def irsUnflatten (k s : ℕ) (hdvd : s ∣ k) (m : Fin k → F) :
    Fin s → Fin (k / s) → F :=
  fun row col ↦ m (irsIndexEquiv k s hdvd (row, col))

/-- Join `s` rows of length `k / s` into a length-`k` scalar message. -/
def irsFlatten (k s : ℕ) (hdvd : s ∣ k) (rows : Fin s → Fin (k / s) → F) :
    Fin k → F :=
  fun j ↦ rows ((irsIndexEquiv k s hdvd).symm j).1
    ((irsIndexEquiv k s hdvd).symm j).2

omit [Field F] [DecidableEq F] [BEq F] [LawfulBEq F] in
@[simp]
theorem irsUnflatten_flatten (k s : ℕ) (hdvd : s ∣ k)
    (rows : Fin s → Fin (k / s) → F) :
    irsUnflatten k s hdvd (irsFlatten k s hdvd rows) = rows := by
  funext row col
  simp [irsUnflatten, irsFlatten]

omit [Field F] [DecidableEq F] [BEq F] [LawfulBEq F] in
@[simp]
theorem irsFlatten_unflatten (k s : ℕ) (hdvd : s ∣ k) (m : Fin k → F) :
    irsFlatten k s hdvd (irsUnflatten k s hdvd m) = m := by
  funext j
  simp [irsUnflatten, irsFlatten]

omit [Field F] [DecidableEq F] [BEq F] [LawfulBEq F] in
theorem irsUnflatten_injective (k s : ℕ) (hdvd : s ∣ k) :
    Function.Injective (irsUnflatten (F := F) k s hdvd) := by
  intro m₁ m₂ h
  rw [← irsFlatten_unflatten k s hdvd m₁, ← irsFlatten_unflatten k s hdvd m₂, h]

/-- Executable `s`-interleaved Reed--Solomon encoder.  Its public alphabet is
`Fin s → F`; interleaving is not modeled by enlarging the word-position type. -/
def irsEncoder (k s : ℕ) (hdvd : s ∣ k) (domain : ι ↪ F) :
    (Fin k → F) →ₗ[F] (ι → Fin s → F) :=
  { toFun := fun m j row ↦
      Spec.rsEncoder (k / s) domain (irsUnflatten k s hdvd m row) j
    map_add' := by
      intro m₁ m₂
      ext j row
      rw [show irsUnflatten k s hdvd (m₁ + m₂) row =
        irsUnflatten k s hdvd m₁ row + irsUnflatten k s hdvd m₂ row by rfl]
      exact congrFun (map_add (Spec.rsEncoder (k / s) domain)
        (irsUnflatten k s hdvd m₁ row) (irsUnflatten k s hdvd m₂ row)) j
    map_smul' := by
      intro c m
      ext j row
      rw [show irsUnflatten k s hdvd (c • m) row =
        c • irsUnflatten k s hdvd m row by rfl]
      exact congrFun (map_smul (Spec.rsEncoder (k / s) domain) c
        (irsUnflatten k s hdvd m row)) j }

omit [DecidableEq ι] [DecidableEq F] [BEq F] [LawfulBEq F] in
@[simp]
theorem irsEncoder_apply (k s : ℕ) (hdvd : s ∣ k) (domain : ι ↪ F)
    (m : Fin k → F) (j : ι) (row : Fin s) :
    irsEncoder k s hdvd domain m j row =
      Spec.rsEncoder (k / s) domain (irsUnflatten k s hdvd m row) j := rfl

omit [DecidableEq ι] [DecidableEq F] [BEq F] [LawfulBEq F] in
/-- The executable encoder has exactly the canonical interleaved Reed--Solomon code
as its range. -/
theorem irsEncoder_range (k s : ℕ) (hdvd : s ∣ k) (domain : ι ↪ F) :
    Set.range (irsEncoder k s hdvd domain) =
      (ReedSolomon.Interleaved.irsCode domain k s : Set (ι → Fin s → F)) := by
  ext w
  constructor
  · rintro ⟨m, rfl⟩
    change ∀ row, (fun j ↦ irsEncoder k s hdvd domain m j row) ∈
      ReedSolomon.code domain (k / s)
    intro row
    change Spec.rsEncoder (k / s) domain (irsUnflatten k s hdvd m row) ∈
      ReedSolomon.code domain (k / s)
    have hmem : Spec.rsEncoder (k / s) domain (irsUnflatten k s hdvd m row) ∈
        (ReedSolomon.code domain (k / s) : Set (ι → F)) := by
      rw [← Spec.rsEncoder_range]
      exact ⟨irsUnflatten k s hdvd m row, rfl⟩
    exact hmem
  · intro hw
    change (∀ row, (fun j ↦ w j row) ∈ ReedSolomon.code domain (k / s)) at hw
    classical
    have hrange : ∀ row, (fun j ↦ w j row) ∈
        Set.range (Spec.rsEncoder (k / s) domain) := by
      intro row
      rw [Spec.rsEncoder_range]
      exact hw row
    choose rows hrows using hrange
    refine ⟨irsFlatten k s hdvd rows, ?_⟩
    funext j row
    change Spec.rsEncoder (k / s) domain
      (irsUnflatten k s hdvd (irsFlatten k s hdvd rows) row) j = w j row
    rw [irsUnflatten_flatten]
    exact congrFun (hrows row) j

omit [DecidableEq ι] [DecidableEq F] [BEq F] [LawfulBEq F] in
/-- Below scalar-row saturation, the executable interleaved encoder is injective. -/
theorem irsEncoder_injective [Fintype ι] (k s : ℕ) (hdvd : s ∣ k)
    (domain : ι ↪ F) (hcard : k / s ≤ Fintype.card ι) :
    Function.Injective (irsEncoder k s hdvd domain) := by
  intro m₁ m₂ henc
  exact irsUnflatten_injective k s hdvd <| funext fun row ↦
    Spec.rsEncoder_injective hcard <| funext fun j ↦
      congrFun (congrFun henc j) row

/-- Decode every interleaved row on the same known-good node set and flatten the
recovered scalar rows back into one length-`k` message. -/
def irsErasureDecodeOrZero [Fintype ι] (k s : ℕ) (hdvd : s ∣ k)
    (domain : ι ↪ F) (nodes : Finset ι) (w : ι → Fin s → F) : Fin k → F :=
  irsFlatten k s hdvd fun row ↦
    Spec.rsErasureDecodeOrZero (k / s) domain nodes (fun j ↦ w j row)

/-- Row-wise erasure recovery: if every retained interleaved symbol agrees with an
encoded message, decoding on those nodes recovers the entire length-`k` message. -/
theorem irsErasureDecodeOrZero_eq [Fintype ι] (k s : ℕ) (hdvd : s ∣ k)
    (domain : ι ↪ F) {nodes : Finset ι} {w : ι → Fin s → F} {m : Fin k → F}
    (hcard : k / s ≤ nodes.card)
    (hval : ∀ j ∈ nodes, irsEncoder k s hdvd domain m j = w j) :
    irsErasureDecodeOrZero k s hdvd domain nodes w = m := by
  rw [irsErasureDecodeOrZero, ← irsFlatten_unflatten k s hdvd m]
  congr 1
  funext row
  apply Spec.rsErasureDecodeOrZero_eq hcard
  intro j hj
  exact congrFun (hval j hj) row

/-- Maximal column agreement set computed from the fresh challenge and the prover's
post-challenge message.  Equality is at the full `Fin s → F` alphabet symbol. -/
def irsGammaAgreementSet [Fintype ι] (k s : ℕ) (hdvd : s ∣ k)
    (domain : ι ↪ F) (f₁ f₂ : ι → Fin s → F) (γ : F) (g : Fin k → F) : Finset ι :=
  Finset.univ.filter fun j ↦
    irsEncoder k s hdvd domain g j = f₁ j + γ • f₂ j

omit [DecidableEq ι] [BEq F] [LawfulBEq F] in
@[simp]
theorem mem_irsGammaAgreementSet [Fintype ι] (k s : ℕ) (hdvd : s ∣ k)
    (domain : ι ↪ F) {f₁ f₂ : ι → Fin s → F} {γ : F} {g : Fin k → F} {j : ι} :
    j ∈ irsGammaAgreementSet k s hdvd domain f₁ f₂ γ g ↔
      irsEncoder k s hdvd domain g j = f₁ j + γ • f₂ j := by
  simp [irsGammaAgreementSet]

omit [DecidableEq ι] [BEq F] [LawfulBEq F] in
/-- A post-`γ` knowledge state makes the computed maximal interleaved agreement
set large. -/
theorem irsGammaAgreementSet_card_of_gammaState [Fintype ι]
    (k s : ℕ) (hdvd : s ∣ k) (domain : ι ↪ F) {δ : ℝ≥0}
    {v : Fin k → F} {μ₁ μ₂ γ : F} {f₁ f₂ : ι → Fin s → F} {g : Fin k → F}
    (hstate : Spec.gammaState k (irsEncoder k s hdvd domain) δ
      v μ₁ μ₂ f₁ f₂ γ g) :
    (1 - (δ : ℝ)) * Fintype.card ι ≤
      (irsGammaAgreementSet k s hdvd domain f₁ f₂ γ g).card := by
  obtain ⟨-, S, hScard, hagree⟩ := hstate
  have hsub : S ⊆ irsGammaAgreementSet k s hdvd domain f₁ f₂ γ g := by
    intro j hj
    exact mem_irsGammaAgreementSet k s hdvd domain |>.mpr (hagree j hj).symm
  have hcard := Finset.card_le_card hsub
  have hcardR : (S.card : ℝ) ≤
      ((irsGammaAgreementSet k s hdvd domain f₁ f₂ γ g).card : ℝ) := by
    exact_mod_cast hcard
  exact hScard.trans hcardR

/-- Concrete interleaved-RS transition extractor.  Both input oracle words are decoded
on the same maximal post-`γ` agreement set. -/
def irsTransitionExtractor [Fintype ι] (k s : ℕ) (hdvd : s ∣ k)
    (domain : ι ↪ F)
    (stmtIn : Spec.Statement (F := F) k ×
      (∀ i, Spec.OracleStatement ι (Fin s → F) i))
    (γ : F) (g : Fin k → F) : Spec.Witness (F := F) k :=
  let nodes := irsGammaAgreementSet k s hdvd domain
    (stmtIn.2 0) (stmtIn.2 1) γ g
  fun i ↦ irsErasureDecodeOrZero k s hdvd domain nodes (stmtIn.2 i)

section Protocol

open OracleSpec ProtocolSpec

variable [Fintype ι] [Fintype F]

/-- The honest toy-problem reduction instantiated with the executable interleaved-RS
encoder. -/
def reductionIRS (k s t : ℕ) (hdvd : s ∣ k) (domain : ι ↪ F) :
    Reduction []ₒ
      (Spec.Statement (F := F) k ×
        (∀ i, Spec.OracleStatement ι (Fin s → F) i))
      (Spec.Witness (F := F) k)
      Spec.OutputStatement Spec.OutputWitness
      (Spec.pSpec (ι := ι) (F := F) k t) :=
  Spec.reduction (k := k) (t := t) (irsEncoder k s hdvd domain)

/-- Oracle-flavoured honest toy-problem reduction instantiated with the executable
interleaved-RS encoder. -/
def oracleReductionIRS (k s t : ℕ) (hdvd : s ∣ k) (domain : ι ↪ F) :
    OracleReduction []ₒ
      (Spec.Statement (F := F) k)
      (Spec.OracleStatement ι (Fin s → F))
      (Spec.Witness (F := F) k)
      Spec.OutputStatement Spec.OutputOracleStatement Spec.OutputWitness
      (Spec.pSpec (ι := ι) (F := F) k t) :=
  Spec.oracleReduction (k := k) (t := t) (irsEncoder k s hdvd domain)

/-- Construction 6.9 instantiated over the executable interleaved-RS
alphabet.  Its output is a virtual oracle answered by querying both input
codewords and taking their challenge-linear combination. -/
def simplifiedOracleReductionIRS (k s : ℕ) :
    OracleReduction (emptySpec.{0, 0})
      (Spec.Statement (F := F) k)
      (Spec.OracleStatement ι (Fin s → F))
      (Spec.Witness (F := F) k)
      (SimplifiedIOR.OutputStatement (F := F) k)
      (SimplifiedIOR.OutputOracleStatement ι (Fin s → F))
      (SimplifiedIOR.OutputWitness (F := F) k)
      (SimplifiedIOR.pSpec (F := F)) :=
  SimplifiedIOR.oracleReduction
    (ι := ι) (F := F) (A := Fin s → F) (k := k)

/-- Compatibility name for the bundled execution view of the executable
interleaved-RS C6.9 reduction.  The composable protocol object is
`simplifiedOracleReductionIRS`. -/
def simplifiedReductionIRS (k s : ℕ) :
    Reduction []ₒ
      (Spec.Statement (F := F) k ×
        (∀ i, Spec.OracleStatement ι (Fin s → F) i))
      (Spec.Witness (F := F) k)
      (SimplifiedIOR.OutputStatement (F := F) k ×
        (∀ i, SimplifiedIOR.OutputOracleStatement ι (Fin s → F) i))
      (SimplifiedIOR.OutputWitness (F := F) k)
      (SimplifiedIOR.pSpec (F := F)) :=
  SimplifiedIOR.reduction
    (ι := ι) (F := F) (A := Fin s → F) (k := k)

/-- Intermediate witness types for the executable C6.9 round-by-round
extractor: a two-row input witness before `γ`, and the combined message after
`γ`. -/
def simplifiedIorRbrWitMid (k : ℕ) : Fin 2 → Type
  | ⟨0, _⟩ => Spec.Witness (F := F) k
  | ⟨1, _⟩ => SimplifiedIOR.OutputWitness (F := F) k

/-- Named executable round-by-round extractor for C6.9 over interleaved RS.
It erasure-decodes both input rows on the maximal agreement set selected by
the exact combined output witness. -/
def simplifiedIorRbrExtractor (k s : ℕ) (hdvd : s ∣ k)
    (domain : ι ↪ F) :
    Extractor.RoundByRound []ₒ
      (Spec.Statement (F := F) k ×
        (∀ i, Spec.OracleStatement ι (Fin s → F) i))
      (Spec.Witness (F := F) k)
      (SimplifiedIOR.OutputWitness (F := F) k)
      (SimplifiedIOR.pSpec (F := F))
      (simplifiedIorRbrWitMid (F := F) k) where
  eqIn := rfl
  extractMid
  | ⟨0, _⟩ => fun stmtIn tr g ↦
      irsTransitionExtractor k s hdvd domain stmtIn
        (SimplifiedIOR.transcriptGamma (F := F) tr) g
  extractOut := fun _ _ g ↦ g

/-- Named executable straightline extractor for C6.9 over interleaved RS. -/
def simplifiedIorStraightlineExtractor (k s : ℕ) (hdvd : s ∣ k)
    (domain : ι ↪ F) :
    Extractor.Straightline []ₒ
      (Spec.Statement (F := F) k ×
        (∀ i, Spec.OracleStatement ι (Fin s → F) i))
      (Spec.Witness (F := F) k)
      (SimplifiedIOR.OutputWitness (F := F) k)
      (SimplifiedIOR.pSpec (F := F)) :=
  SimplifiedIOR.transitionStraightlineExtractor k
    (irsTransitionExtractor k s hdvd domain)

/-- Intermediate witness types for the executable round-by-round extractor. -/
def irsRbrWitMid (k : ℕ) : Fin 4 → Type
  | ⟨0, _⟩ => Spec.Witness (F := F) k
  | ⟨1, _⟩ => Fin k → F
  | ⟨2, _⟩ => Fin k → F
  | ⟨3, _⟩ => PUnit

/-- Named executable round-by-round extractor for interleaved RS. -/
def irsRbrExtractor (k s t : ℕ) (hdvd : s ∣ k) (domain : ι ↪ F) :
    Extractor.RoundByRound []ₒ
      (Spec.Statement (F := F) k ×
        (∀ i, Spec.OracleStatement ι (Fin s → F) i))
      (Spec.Witness (F := F) k) Spec.OutputWitness
      (Spec.pSpec (ι := ι) (F := F) k t) (irsRbrWitMid (F := F) k) where
  eqIn := rfl
  extractMid
  | ⟨0, _⟩ => fun stmtIn tr g ↦
      irsTransitionExtractor k s hdvd domain stmtIn
        (tr ⟨0, Nat.zero_lt_succ _⟩) g
  | ⟨1, _⟩ => fun _ _ g ↦ g
  | ⟨2, _⟩ => fun _ tr _ ↦
      tr ⟨1, Nat.succ_lt_succ (Nat.zero_lt_succ _)⟩
  extractOut := fun _ _ _ ↦ PUnit.unit

/-- Named executable straightline extractor used by the public exact-extractor game
theorem.  Query logs are ignored because the toy reduction has an empty ambient oracle
specification; all extraction data is in the public transcript and input words. -/
def irsStraightlineExtractor (k s t : ℕ) (hdvd : s ∣ k) (domain : ι ↪ F) :
    Extractor.Straightline []ₒ
      (Spec.Statement (F := F) k ×
        (∀ i, Spec.OracleStatement ι (Fin s → F) i))
      (Spec.Witness (F := F) k) Spec.OutputWitness
      (Spec.pSpec (ι := ι) (F := F) k t) :=
  fun stmtIn _ tr _ _ ↦ pure <|
    irsTransitionExtractor k s hdvd domain stmtIn
      (tr ⟨0, Nat.zero_lt_succ _⟩)
      (tr ⟨1, Nat.succ_lt_succ (Nat.zero_lt_succ _)⟩)

/-- On a non-MCA transition, the executable extractor returns a two-row point-list
element whose affine constraint holds at the sampled challenge.  This is the
deterministic kernel of the extractor-certified probability bound. -/
theorem irsTransitionExtractor_pointList_and_affine [Nonempty ι]
    (k s : ℕ) (hdvd : s ∣ k) [NeZero (k / s)] (domain : ι ↪ F)
    (hfull : k / s ≤ Fintype.card ι) {δ : ℝ≥0}
    (hδ : δ < (minRelHammingDistCode
      (ReedSolomon.code domain (k / s) : Set (ι → F)) : ℝ≥0))
    (stmtIn : Spec.Statement (F := F) k ×
      (∀ i, Spec.OracleStatement ι (Fin s → F) i))
    (γ : F) (g : Fin k → F)
    (hstate : Spec.gammaState k (irsEncoder k s hdvd domain) δ
      stmtIn.1.1 stmtIn.1.2.1 stmtIn.1.2.2
      (stmtIn.2 0) (stmtIn.2 1) γ g)
    (hmca : ¬ IsMCA (AffineLineGenerator F)
      (ReedSolomon.Interleaved.irsCode domain k s) γ
      ![stmtIn.2 0, stmtIn.2 1] (δ : ℝ)) :
    let M := irsTransitionExtractor k s hdvd domain stmtIn γ g
    encStack (irsEncoder k s hdvd domain) (M 0, M 1) ∈
        Code.closeCodewordsRel
          (((ReedSolomon.Interleaved.irsCode domain k s) ^⋈ (Fin 2) :
            ModuleCode ι F (Fin 2 → Fin s → F)) :
              Set (ι → Fin 2 → Fin s → F))
          (fun j ↦ ![stmtIn.2 0 j, stmtIn.2 1 j]) (δ : ℝ) ∧
      (∑ j, M 0 j * stmtIn.1.1 j) + γ *
          (∑ j, M 1 j * stmtIn.1.1 j) =
        stmtIn.1.2.1 + γ * stmtIn.1.2.2 := by
  classical
  let nodes := irsGammaAgreementSet k s hdvd domain
    (stmtIn.2 0) (stmtIn.2 1) γ g
  have hnodes : (1 - (δ : ℝ)) * Fintype.card ι ≤ nodes.card :=
    irsGammaAgreementSet_card_of_gammaState k s hdvd domain hstate
  have hcard : k / s ≤ nodes.card :=
    Spec.rs_large_agreement_card domain hfull hδ hnodes
  have hcomb : LinearCode.projectedWord
      (fun x ↦ ∑ i : Fin 2, AffineLineGenerator F γ i •
        ![stmtIn.2 0, stmtIn.2 1] i x) nodes ∈
      LinearCode.projectedCodeSubmod
        (ReedSolomon.Interleaved.irsCode domain k s) nodes := by
    rw [LinearCode.mem_projectedCodeSubmod_iff]
    refine ⟨irsEncoder k s hdvd domain g, ?_, ?_⟩
    · have hg : irsEncoder k s hdvd domain g ∈
          (ReedSolomon.Interleaved.irsCode domain k s : Set (ι → Fin s → F)) :=
        (irsEncoder_range k s hdvd domain) ▸ Set.mem_range_self g
      exact hg
    · funext x
      simp only [LinearCode.projectedWord, Set.restrict_apply]
      have hx := mem_irsGammaAgreementSet k s hdvd domain
        (f₁ := stmtIn.2 0) (f₂ := stmtIn.2 1) (γ := γ) (g := g)
        (j := x) |>.mp x.property
      simpa [AffineLineGenerator, Fin.sum_univ_two] using hx.symm
  have hall : ∀ i : Fin 2, LinearCode.projectedWord
      (![stmtIn.2 0, stmtIn.2 1] i) nodes ∈
      LinearCode.projectedCodeSubmod
        (ReedSolomon.Interleaved.irsCode domain k s) nodes := by
    by_contra hnot
    push Not at hnot
    have hcardR : (nodes.card : ℝ) ≥
        (Fintype.card ι : ℝ) * (1 - (δ : ℝ)) := by linarith
    exact hmca ⟨nodes, hcardR, hcomb, hnot⟩
  choose words hwords hproj using fun i ↦
    (LinearCode.mem_projectedCodeSubmod_iff
      (ReedSolomon.Interleaved.irsCode domain k s) nodes
      (LinearCode.projectedWord (![stmtIn.2 0, stmtIn.2 1] i) nodes)).mp (hall i)
  have hmsg : ∀ i : Fin 2, ∃ msg,
      irsEncoder k s hdvd domain msg = words i := by
    intro i
    have hw : words i ∈
        (ReedSolomon.Interleaved.irsCode domain k s : Set (ι → Fin s → F)) := hwords i
    rw [← irsEncoder_range] at hw
    exact hw
  choose msgs hmsgs using hmsg
  have hdecode : ∀ i : Fin 2,
      irsErasureDecodeOrZero k s hdvd domain nodes (stmtIn.2 i) = msgs i := by
    intro i
    apply irsErasureDecodeOrZero_eq k s hdvd domain hcard
    intro x hx
    have hp := congrFun (hproj i) ⟨x, hx⟩
    rw [hmsgs i]
    fin_cases i <;> simpa [LinearCode.projectedWord] using hp.symm
  have hM : irsTransitionExtractor k s hdvd domain stmtIn γ g = msgs := by
    funext i
    change irsErasureDecodeOrZero k s hdvd domain nodes (stmtIn.2 i) = msgs i
    exact hdecode i
  have hcombMsg : g = msgs 0 + γ • msgs 1 := by
    have hgdecode : irsErasureDecodeOrZero k s hdvd domain nodes
        (irsEncoder k s hdvd domain g) = g :=
      irsErasureDecodeOrZero_eq k s hdvd domain hcard (fun _ _ ↦ rfl)
    have hother : irsErasureDecodeOrZero k s hdvd domain nodes
        (irsEncoder k s hdvd domain g) = msgs 0 + γ • msgs 1 := by
      apply irsErasureDecodeOrZero_eq k s hdvd domain hcard
      intro x hx
      rw [map_add, map_smul]
      simp only [Pi.add_apply, Pi.smul_apply]
      have h0 := congrFun (hproj 0) ⟨x, hx⟩
      have h1 := congrFun (hproj 1) ⟨x, hx⟩
      rw [hmsgs 0, hmsgs 1]
      have h0' : stmtIn.2 0 x = words 0 x := by
        simpa [LinearCode.projectedWord] using h0
      have h1' : stmtIn.2 1 x = words 1 x := by
        simpa [LinearCode.projectedWord] using h1
      have hxagree := mem_irsGammaAgreementSet k s hdvd domain
        (f₁ := stmtIn.2 0) (f₂ := stmtIn.2 1) (γ := γ) (g := g)
        (j := x) |>.mp hx
      exact (hxagree.trans (by rw [h0', h1'])).symm
    exact hgdecode.symm.trans hother
  rw [hM]
  constructor
  · rw [encStack_mem_closeCodewordsRel_iff
      (irsEncoder k s hdvd domain)
      (ReedSolomon.Interleaved.irsCode domain k s)
      (irsEncoder_range k s hdvd domain)]
    · refine ⟨nodes, hnodes, fun x hx ↦ ⟨?_, ?_⟩⟩
      · rw [hmsgs 0]
        have hp := congrFun (hproj 0) ⟨x, hx⟩
        simpa [LinearCode.projectedWord] using hp
      · rw [hmsgs 1]
        have hp := congrFun (hproj 1) ⟨x, hx⟩
        simpa [LinearCode.projectedWord] using hp
    · exact lt_of_lt_of_le hδ (by
        exact_mod_cast (Code.minRelHammingDistCode_le_one
          (C := (ReedSolomon.code domain (k / s) : Set (ι → F)))))
  · have hlinear := hstate.1
    rw [hcombMsg] at hlinear
    simpa only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul,
      Finset.sum_add_distrib, mul_assoc, Finset.mul_sum] using hlinear

/-- The bad combination-round event for the exact executable extractor: some
post-challenge message reaches the knowledge state, but the witness returned by
`irsTransitionExtractor` does not satisfy the relaxed two-row relation. -/
def IRSExactGammaFailure (k s : ℕ) (hdvd : s ∣ k) (domain : ι ↪ F)
    (δ : ℝ≥0)
    (stmtIn : Spec.Statement (F := F) k ×
      (∀ i, Spec.OracleStatement ι (Fin s → F) i))
    (γ : F) : Prop :=
  ∃ g : Fin k → F,
    (stmtIn, irsTransitionExtractor k s hdvd domain stmtIn γ g) ∉
        Spec.outputRelationFor k (irsEncoder k s hdvd domain) δ ∧
      Spec.gammaState k (irsEncoder k s hdvd domain) δ
        stmtIn.1.1 stmtIn.1.2.1 stmtIn.1.2.2
        (stmtIn.2 0) (stmtIn.2 1) γ g

/-- The exact executable transition extractor has the canonical MCA-plus-list
combination-round error.  Unlike `gamma_transition_prob_le`, this statement does
not assume that the input has no valid witness: it bounds failure of the specific
witness computed from each transcript. -/
theorem irs_exact_gamma_failure_prob_le [Nonempty ι]
    (k s : ℕ) (hdvd : s ∣ k) [NeZero (k / s)] (domain : ι ↪ F)
    (hfull : k / s ≤ Fintype.card ι) (δ : ℝ≥0)
    (hδ : δ < (minRelHammingDistCode
      (ReedSolomon.code domain (k / s) : Set (ι → F)) : ℝ≥0))
    (stmtIn : Spec.Statement (F := F) k ×
      (∀ i, Spec.OracleStatement ι (Fin s → F) i)) :
    Pr_{let γ ← $ᵖ F}[IRSExactGammaFailure k s hdvd domain δ stmtIn γ] ≤
      mcaError (AffineLineGenerator F)
          (ReedSolomon.Interleaved.irsCode domain k s) (δ : ℝ) +
        ((Code.Lambda
          (((ReedSolomon.Interleaved.irsCode domain k s) ^⋈ (Fin 2) :
            ModuleCode ι F (Fin 2 → Fin s → F)) :
              Set (ι → Fin 2 → Fin s → F))
          (δ : ℝ)).toNat : ENNReal) / (Fintype.card F : ENNReal) := by
  classical
  let C : ModuleCode ι F (Fin s → F) :=
    ReedSolomon.Interleaved.irsCode domain k s
  let Cint : Set (ι → Fin 2 → Fin s → F) :=
    ((C ^⋈ (Fin 2) : ModuleCode ι F (Fin 2 → Fin s → F)) :
      Set (ι → Fin 2 → Fin s → F))
  let center : ι → Fin 2 → Fin s → F :=
    fun i ↦ ![stmtIn.2 0 i, stmtIn.2 1 i]
  let Smsg : Finset ((Fin k → F) × (Fin k → F)) := Finset.univ.filter
    (fun p ↦ encStack (irsEncoder k s hdvd domain) p ∈
        Code.closeCodewordsRel Cint center (δ : ℝ) ∧
      ¬ ((∑ j, p.1 j * stmtIn.1.1 j) = stmtIn.1.2.1 ∧
        (∑ j, p.2 j * stmtIn.1.1 j) = stmtIn.1.2.2))
  have hSmsg_le : Smsg.card ≤ (Code.Lambda Cint (δ : ℝ)).toNat := by
    have hsub : encStack (irsEncoder k s hdvd domain) ''
        (Smsg : Set ((Fin k → F) × (Fin k → F))) ⊆
        Code.closeCodewordsRel Cint center (δ : ℝ) := by
      rintro V ⟨p, hp, rfl⟩
      exact (Finset.mem_filter.mp hp).2.1
    have himage :
        (encStack (irsEncoder k s hdvd domain) ''
          (Smsg : Set ((Fin k → F) × (Fin k → F)))).ncard = Smsg.card := by
      rw [Set.ncard_image_of_injective _
        (encStack_injective (irsEncoder_injective k s hdvd domain hfull)),
        Set.ncard_coe_finset]
    have hencard :
        ((Code.closeCodewordsRel Cint center (δ : ℝ)).ncard : ENat) ≤
          Code.Lambda Cint (δ : ℝ) := by
      rw [(Set.toFinite (Code.closeCodewordsRel Cint center (δ : ℝ))).cast_ncard_eq]
      exact Code.encard_closeCodewordsRel_le_Lambda Cint (δ : ℝ) center
    have hfinite : Code.Lambda Cint (δ : ℝ) ≠ ⊤ := Code.Lambda_ne_top _
    have hncard : Smsg.card ≤ (Code.closeCodewordsRel Cint center (δ : ℝ)).ncard := by
      rw [← himage]
      exact Set.ncard_le_ncard hsub (Set.toFinite _)
    have hcast : (Smsg.card : ENat) ≤ Code.Lambda Cint (δ : ℝ) :=
      le_trans (by exact_mod_cast hncard) hencard
    rwa [← ENat.coe_toNat hfinite, Nat.cast_le] at hcast
  have hδ1 : δ < 1 := lt_of_lt_of_le hδ (by
    exact_mod_cast (Code.minRelHammingDistCode_le_one
      (C := (ReedSolomon.code domain (k / s) : Set (ι → F)))))
  have hcards : (Finset.univ.filter (fun γ : F ↦
      IRSExactGammaFailure k s hdvd domain δ stmtIn γ ∧
        ¬ IsMCA (AffineLineGenerator F) C γ
          ![stmtIn.2 0, stmtIn.2 1] (δ : ℝ))).card ≤
      (Code.Lambda Cint (δ : ℝ)).toNat := by
    have hsub : Finset.univ.filter (fun γ : F ↦
        IRSExactGammaFailure k s hdvd domain δ stmtIn γ ∧
          ¬ IsMCA (AffineLineGenerator F) C γ
            ![stmtIn.2 0, stmtIn.2 1] (δ : ℝ)) ⊆
        Smsg.biUnion (fun p ↦ Finset.univ.filter (fun γ : F ↦
          (∑ j, p.1 j * stmtIn.1.1 j) + γ *
            (∑ j, p.2 j * stmtIn.1.1 j) =
              stmtIn.1.2.1 + γ * stmtIn.1.2.2)) := by
      intro γ hγ
      rw [Finset.mem_filter] at hγ
      obtain ⟨g, hbad, hstate⟩ := hγ.2.1
      have hkernel := irsTransitionExtractor_pointList_and_affine
        k s hdvd domain hfull hδ stmtIn γ g hstate hγ.2.2
      let M := irsTransitionExtractor k s hdvd domain stmtIn γ g
      have hlist : encStack (irsEncoder k s hdvd domain) (M 0, M 1) ∈
          Code.closeCodewordsRel Cint center (δ : ℝ) := hkernel.1
      have haffine := hkernel.2
      have hviol : ¬ ((∑ j, M 0 j * stmtIn.1.1 j) = stmtIn.1.2.1 ∧
          (∑ j, M 1 j * stmtIn.1.1 j) = stmtIn.1.2.2) := by
        intro hlin
        apply hbad
        obtain ⟨S, hScard, hagree⟩ :=
          (encStack_mem_closeCodewordsRel_iff
            (irsEncoder k s hdvd domain) C
            (irsEncoder_range k s hdvd domain) hδ1 (M 0, M 1)).mp hlist
        refine ⟨fun i ↦ ?_, S, hScard, fun i x hx ↦ ?_⟩
        · fin_cases i
          · exact hlin.1
          · exact hlin.2
        · fin_cases i
          · exact (hagree x hx).1
          · exact (hagree x hx).2
      rw [Finset.mem_biUnion]
      refine ⟨(M 0, M 1), ?_, ?_⟩
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlist, hviol⟩
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, haffine⟩
    refine le_trans (Finset.card_le_card hsub) (le_trans Finset.card_biUnion_le ?_)
    calc
      ∑ p ∈ Smsg, (Finset.univ.filter (fun γ : F ↦
          (∑ j, p.1 j * stmtIn.1.1 j) + γ *
            (∑ j, p.2 j * stmtIn.1.1 j) =
              stmtIn.1.2.1 + γ * stmtIn.1.2.2)).card
          ≤ ∑ _p ∈ Smsg, 1 := Finset.sum_le_sum fun p hp ↦
            affine_solution_card_le_one (Finset.mem_filter.mp hp).2.2
      _ = Smsg.card := by rw [Finset.sum_const, smul_eq_mul, mul_one]
      _ ≤ (Code.Lambda Cint (δ : ℝ)).toNat := hSmsg_le
  refine le_trans (Pr_le_Pr_of_implies ($ᵖ F) _
      (fun γ ↦ IsMCA (AffineLineGenerator F) C γ
          ![stmtIn.2 0, stmtIn.2 1] (δ : ℝ) ∨
        (IRSExactGammaFailure k s hdvd domain δ stmtIn γ ∧
          ¬ IsMCA (AffineLineGenerator F) C γ
            ![stmtIn.2 0, stmtIn.2 1] (δ : ℝ)))
      (fun γ h ↦ by
        by_cases hm : IsMCA (AffineLineGenerator F) C γ
            ![stmtIn.2 0, stmtIn.2 1] (δ : ℝ)
        · exact Or.inl hm
        · exact Or.inr ⟨h, hm⟩))
    (le_trans (Probability.Pr_or_le ($ᵖ F) _ _) (add_le_add ?_ ?_))
  · exact le_iSup
      (fun U : Fin 2 → (ι → Fin s → F) ↦
        Pr_{let γ ← $ᵖ F}[IsMCA (AffineLineGenerator F) C γ U (δ : ℝ)])
      ![stmtIn.2 0, stmtIn.2 1]
  · rw [prob_uniform_eq_card_filter_div_card]
    exact ENNReal.div_le_div_right (by exact_mod_cast hcards) _

/-- The certified combination-round error for the executable interleaved-RS
extractor.  This is the finite `ℝ≥0` reflection of the canonical MCA-plus-list
`ENNReal` expression. -/
noncomputable def irsCertifiedGammaError (k s : ℕ) (domain : ι ↪ F)
    (δ : ℝ≥0) : ℝ≥0 :=
  certifiedGammaError (ReedSolomon.Interleaved.irsCode domain k s) δ

omit [DecidableEq ι] [DecidableEq F] [BEq F] [LawfulBEq F] in
/-- The certified combination-round error coerces back to its defining
MCA-plus-list expression. -/
theorem coe_irsCertifiedGammaError (k s : ℕ) (domain : ι ↪ F)
    (δ : ℝ≥0) :
    (irsCertifiedGammaError k s domain δ : ENNReal) =
      mcaError (AffineLineGenerator F)
          (ReedSolomon.Interleaved.irsCode domain k s) (δ : ℝ) +
        ((Code.Lambda
          (((ReedSolomon.Interleaved.irsCode domain k s) ^⋈ (Fin 2) :
            ModuleCode ι F (Fin 2 → Fin s → F)) :
              Set (ι → Fin 2 → Fin s → F))
          (δ : ℝ)).toNat : ENNReal) / (Fintype.card F : ENNReal) := by
  exact coe_certifiedGammaError
    (ReedSolomon.Interleaved.irsCode domain k s) δ

/-- Full extractor-certified error: the spot-check failure probability combined
sharply with the executable transition extractor's combination-round error. -/
noncomputable def irsExtractorCertifiedError (k s t : ℕ)
    (domain : ι ↪ F) (δ : ℝ≥0) : ℝ≥0 :=
  extractorCertifiedError (ReedSolomon.Interleaved.irsCode domain k s) δ t

/-- The uniform challenge bound in the exact shape consumed by the generic
knowledge-soundness assembly theorem. -/
theorem irs_exact_gamma_failure_sample_le [SampleableType F] [Nonempty ι]
    (k s : ℕ) (hdvd : s ∣ k) [NeZero (k / s)] (domain : ι ↪ F)
    (hfull : k / s ≤ Fintype.card ι) (δ : ℝ≥0)
    (hδ : δ < (minRelHammingDistCode
      (ReedSolomon.code domain (k / s) : Set (ι → F)) : ℝ≥0))
    (stmtIn : Spec.Statement (F := F) k ×
      (∀ i, Spec.OracleStatement ι (Fin s → F) i)) :
    Pr[ IRSExactGammaFailure k s hdvd domain δ stmtIn | $ᵗ F] ≤
      (irsCertifiedGammaError k s domain δ : ENNReal) := by
  rw [probEvent_uniformSample_eq_prob_uniformOfFintype,
    coe_irsCertifiedGammaError]
  exact irs_exact_gamma_failure_prob_le k s hdvd domain hfull δ hδ stmtIn

/-- Public exact-extractor game theorem for C6.9 over executable interleaved
RS.  The proposition names `simplifiedIorStraightlineExtractor`, whose
algorithm erasure-decodes both input rows from the challenge and the claimed
combined message. -/
theorem simplifiedOracleVerifier_knowledgeSoundnessWith_irsStraightlineExtractor
    [SampleableType F] [Nonempty ι]
    (k s : ℕ) (hdvd : s ∣ k) [NeZero (k / s)] (domain : ι ↪ F)
    (hfull : k / s ≤ Fintype.card ι) (δ : ℝ≥0)
    (hδ : δ < (minRelHammingDistCode
      (ReedSolomon.code domain (k / s) : Set (ι → F)) : ℝ≥0))
    {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    (SimplifiedIOR.oracleVerifier
      (ι := ι) (F := F) (A := Fin s → F) (k := k)).knowledgeSoundnessWith
        (WitOut := SimplifiedIOR.OutputWitness (F := F) k)
        init impl (Spec.outputRelationFor k (irsEncoder k s hdvd domain) δ)
        (SimplifiedIOR.outputRelationFor k (irsEncoder k s hdvd domain) δ)
        (simplifiedIorStraightlineExtractor k s hdvd domain)
        (irsCertifiedGammaError k s domain δ) := by
  apply SimplifiedIOR.knowledgeSoundWith_of_gamma_bound
    (k := k) init impl δ (irsCertifiedGammaError k s domain δ)
      (irsEncoder k s hdvd domain)
      (irsTransitionExtractor k s hdvd domain)
  intro stmtIn
  exact irs_exact_gamma_failure_sample_le
    k s hdvd domain hfull δ hδ stmtIn

set_option linter.unusedDecidableInType false in
/-- Existential C6.9 knowledge soundness, retained as a corollary of the
public exact straightline-extractor theorem. -/
theorem simplifiedOracleVerifier_knowledgeSoundness_irs
    [SampleableType F] [Nonempty ι]
    (k s : ℕ) (hdvd : s ∣ k) [NeZero (k / s)] (domain : ι ↪ F)
    (hfull : k / s ≤ Fintype.card ι) (δ : ℝ≥0)
    (hδ : δ < (minRelHammingDistCode
      (ReedSolomon.code domain (k / s) : Set (ι → F)) : ℝ≥0))
    {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    (SimplifiedIOR.oracleVerifier
      (ι := ι) (F := F) (A := Fin s → F) (k := k)).knowledgeSoundness
        (WitOut := SimplifiedIOR.OutputWitness (F := F) k)
        init impl (Spec.outputRelationFor k (irsEncoder k s hdvd domain) δ)
        (SimplifiedIOR.outputRelationFor k (irsEncoder k s hdvd domain) δ)
        (irsCertifiedGammaError k s domain δ) := by
  exact OracleVerifier.knowledgeSoundness_of_with init impl
    (simplifiedOracleVerifier_knowledgeSoundnessWith_irsStraightlineExtractor
      k s hdvd domain hfull δ hδ init impl)

/-- Knowledge-state function paired with the exact executable C6.9 extractor.
The final state is the combined-message relation, expressed as the same
`gammaState` used by the exact IRS failure event. -/
noncomputable def simplifiedIorRbrKSF (k s : ℕ) (hdvd : s ∣ k)
    (domain : ι ↪ F) (δ : ℝ≥0)
    {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    ((SimplifiedIOR.oracleVerifier
      (ι := ι) (F := F) (A := Fin s → F) (k := k)).toVerifier).KnowledgeStateFunction
      init impl (Spec.outputRelationFor k (irsEncoder k s hdvd domain) δ)
      (SimplifiedIOR.outputRelationFor k (irsEncoder k s hdvd domain) δ)
      (simplifiedIorRbrExtractor k s hdvd domain) where
  toFun
  | ⟨0, _⟩ => fun stmtIn _ w ↦
      (stmtIn, w) ∈ Spec.outputRelationFor k (irsEncoder k s hdvd domain) δ
  | ⟨1, _⟩ => fun stmtIn tr g ↦
      Spec.gammaState k (irsEncoder k s hdvd domain) δ
        stmtIn.1.1 stmtIn.1.2.1 stmtIn.1.2.2
        (stmtIn.2 0) (stmtIn.2 1)
        (SimplifiedIOR.transcriptGamma (F := F) tr) g
  toFun_empty := fun _ _ ↦ Iff.rfl
  toFun_next := fun m ↦ match m with
    | ⟨0, _⟩ => fun hDir ↦ absurd hDir (fun h ↦ Direction.noConfusion h)
  toFun_full := fun stmtIn tr witOut h ↦
    SimplifiedIOR.outputRelation_of_probEvent_pos_oracleVerifier_run
      (k := k) init impl (irsEncoder k s hdvd domain) δ stmtIn tr witOut h

/-- Worst-case round-by-round knowledge soundness for C6.9, naming the exact
executable IRS extractor and its knowledge-state function in the public
theorem type.  This is the deterministic Definition A.5 contract used by
Lemma 6.10. -/
theorem simplifiedOracleVerifier_rbrKnowledgeSoundnessWorstCaseWith_irsRbrExtractor
    [SampleableType F] [Nonempty ι]
    (k s : ℕ) (hdvd : s ∣ k) [NeZero (k / s)] (domain : ι ↪ F)
    (hfull : k / s ≤ Fintype.card ι) (δ : ℝ≥0)
    (hδ : δ < (minRelHammingDistCode
      (ReedSolomon.code domain (k / s) : Set (ι → F)) : ℝ≥0))
    {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    ((SimplifiedIOR.oracleVerifier
      (ι := ι) (F := F) (A := Fin s → F)
      (k := k)).toVerifier).rbrKnowledgeSoundnessWorstCaseWith
        (WitIn := Spec.Witness (F := F) k)
        (WitOut := SimplifiedIOR.OutputWitness (F := F) k)
        init impl (Spec.outputRelationFor k (irsEncoder k s hdvd domain) δ)
        (SimplifiedIOR.outputRelationFor k (irsEncoder k s hdvd domain) δ)
        (simplifiedIorRbrWitMid (F := F) k)
        (simplifiedIorRbrExtractor k s hdvd domain)
        (simplifiedIorRbrKSF k s hdvd domain δ init impl)
        (fun _ ↦ irsCertifiedGammaError k s domain δ) := by
  classical
  unfold Verifier.rbrKnowledgeSoundnessWorstCaseWith
  intro stmtIn i transcript
  obtain ⟨⟨iv, hi⟩, _hdir⟩ := i
  rcases iv with _ | iv
  · change Pr[ IRSExactGammaFailure k s hdvd domain δ stmtIn | $ᵗ F] ≤
      (irsCertifiedGammaError k s domain δ : ENNReal)
    exact irs_exact_gamma_failure_sample_le
      k s hdvd domain hfull δ hδ stmtIn
  · exact absurd hi (by omega)

/-- Averaged C6.9 round-by-round knowledge soundness for the same exact
executable extractor, derived from the worst-case-prefix theorem. -/
theorem simplifiedOracleVerifier_rbrKnowledgeSoundnessWith_irsRbrExtractor
    [SampleableType F] [Nonempty ι]
    (k s : ℕ) (hdvd : s ∣ k) [NeZero (k / s)] (domain : ι ↪ F)
    (hfull : k / s ≤ Fintype.card ι) (δ : ℝ≥0)
    (hδ : δ < (minRelHammingDistCode
      (ReedSolomon.code domain (k / s) : Set (ι → F)) : ℝ≥0))
    {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    (SimplifiedIOR.oracleVerifier
      (ι := ι) (F := F) (A := Fin s → F) (k := k)).rbrKnowledgeSoundnessWith
        (WitOut := SimplifiedIOR.OutputWitness (F := F) k)
        init impl (Spec.outputRelationFor k (irsEncoder k s hdvd domain) δ)
        (SimplifiedIOR.outputRelationFor k (irsEncoder k s hdvd domain) δ)
        (simplifiedIorRbrWitMid (F := F) k)
        (simplifiedIorRbrExtractor k s hdvd domain)
        (simplifiedIorRbrKSF k s hdvd domain δ init impl)
        (fun _ ↦ irsCertifiedGammaError k s domain δ) := by
  unfold OracleVerifier.rbrKnowledgeSoundnessWith
  exact Verifier.rbrKnowledgeSoundnessWorstCaseWith_implies_rbrKnowledgeSoundnessWith
    init impl
    (simplifiedOracleVerifier_rbrKnowledgeSoundnessWorstCaseWith_irsRbrExtractor
      k s hdvd domain hfull δ hδ init impl)

set_option linter.unusedDecidableInType false in
/-- Existential worst-case C6.9 RBR knowledge soundness, retained only as a
corollary of the exact-object theorem. -/
theorem simplifiedOracleVerifier_rbrKnowledgeSoundnessWorstCase_irs
    [SampleableType F] [Nonempty ι]
    (k s : ℕ) (hdvd : s ∣ k) [NeZero (k / s)] (domain : ι ↪ F)
    (hfull : k / s ≤ Fintype.card ι) (δ : ℝ≥0)
    (hδ : δ < (minRelHammingDistCode
      (ReedSolomon.code domain (k / s) : Set (ι → F)) : ℝ≥0))
    {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    ((SimplifiedIOR.oracleVerifier
      (ι := ι) (F := F) (A := Fin s → F) (k := k)).toVerifier).rbrKnowledgeSoundnessWorstCase
        (WitIn := Spec.Witness (F := F) k)
        (WitOut := SimplifiedIOR.OutputWitness (F := F) k)
        init impl (Spec.outputRelationFor k (irsEncoder k s hdvd domain) δ)
        (SimplifiedIOR.outputRelationFor k (irsEncoder k s hdvd domain) δ)
        (fun _ ↦ irsCertifiedGammaError k s domain δ) := by
  classical
  rw [Verifier.rbrKnowledgeSoundnessWorstCase_iff_exists_with]
  exact ⟨simplifiedIorRbrWitMid (F := F) k,
    simplifiedIorRbrExtractor k s hdvd domain,
    simplifiedIorRbrKSF k s hdvd domain δ init impl,
    simplifiedOracleVerifier_rbrKnowledgeSoundnessWorstCaseWith_irsRbrExtractor
      k s hdvd domain hfull δ hδ init impl⟩

set_option linter.unusedDecidableInType false in
/-- Existential averaged C6.9 RBR knowledge soundness, retained only as a
corollary of the exact-object theorem. -/
theorem simplifiedOracleVerifier_rbrKnowledgeSoundness_irs
    [SampleableType F] [Nonempty ι]
    (k s : ℕ) (hdvd : s ∣ k) [NeZero (k / s)] (domain : ι ↪ F)
    (hfull : k / s ≤ Fintype.card ι) (δ : ℝ≥0)
    (hδ : δ < (minRelHammingDistCode
      (ReedSolomon.code domain (k / s) : Set (ι → F)) : ℝ≥0))
    {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    (SimplifiedIOR.oracleVerifier
      (ι := ι) (F := F) (A := Fin s → F) (k := k)).rbrKnowledgeSoundness
        (WitOut := SimplifiedIOR.OutputWitness (F := F) k)
        init impl (Spec.outputRelationFor k (irsEncoder k s hdvd domain) δ)
        (SimplifiedIOR.outputRelationFor k (irsEncoder k s hdvd domain) δ)
        (fun _ ↦ irsCertifiedGammaError k s domain δ) := by
  classical
  unfold OracleVerifier.rbrKnowledgeSoundness
  rw [Verifier.rbrKnowledgeSoundness_iff_exists_with]
  exact ⟨simplifiedIorRbrWitMid (F := F) k,
    simplifiedIorRbrExtractor k s hdvd domain,
    simplifiedIorRbrKSF k s hdvd domain δ init impl,
    simplifiedOracleVerifier_rbrKnowledgeSoundnessWith_irsRbrExtractor
      k s hdvd domain hfull δ hδ init impl⟩

/-- Knowledge-state function paired with the executable interleaved-RS
round-by-round extractor.  This is proof-side data; the extractor itself remains
a separate computable declaration. -/
noncomputable def irsRbrKSF (k s t : ℕ) (hdvd : s ∣ k)
    (domain : ι ↪ F) (δ : ℝ≥0)
    {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    ((Spec.oracleVerifier (k := k) (t := t)
      (irsEncoder k s hdvd domain)).toVerifier).KnowledgeStateFunction
      init impl (Spec.outputRelationFor k (irsEncoder k s hdvd domain) δ)
      (Set.univ : Set ((Spec.OutputStatement ×
        ∀ i, Spec.OutputOracleStatement i) × Spec.OutputWitness))
      (irsRbrExtractor k s t hdvd domain) where
  toFun
  | ⟨0, _⟩ => fun stmtIn _ w ↦
      (stmtIn, w) ∈ Spec.outputRelationFor k (irsEncoder k s hdvd domain) δ
  | ⟨1, _⟩ => fun stmtIn tr g ↦
      Spec.gammaState k (irsEncoder k s hdvd domain) δ
        stmtIn.1.1 stmtIn.1.2.1 stmtIn.1.2.2
        (stmtIn.2 0) (stmtIn.2 1) (tr ⟨0, Nat.zero_lt_succ _⟩) g
  | ⟨2, _⟩ => fun stmtIn tr g ↦
      Spec.gammaState k (irsEncoder k s hdvd domain) δ
        stmtIn.1.1 stmtIn.1.2.1 stmtIn.1.2.2
        (stmtIn.2 0) (stmtIn.2 1) (tr ⟨0, Nat.zero_lt_succ _⟩) g
  | ⟨3, _⟩ => fun stmtIn tr _ ↦
      Spec.accepts (k := k) (t := t) (irsEncoder k s hdvd domain)
        stmtIn.1 stmtIn.2
        (tr ⟨0, Nat.zero_lt_succ _⟩)
        (tr ⟨1, Nat.succ_lt_succ (Nat.zero_lt_succ _)⟩)
        (tr ⟨2, Nat.succ_lt_succ
          (Nat.succ_lt_succ (Nat.zero_lt_succ _))⟩)
  toFun_empty := fun _ _ ↦ Iff.rfl
  toFun_next := fun m ↦ match m with
    | ⟨0, _⟩ => fun hDir ↦ absurd hDir (fun h ↦ Direction.noConfusion h)
    | ⟨1, _⟩ => fun _ _ _ _ _ h ↦ h
    | ⟨2, _⟩ => fun hDir ↦ absurd hDir (fun h ↦ Direction.noConfusion h)
  toFun_full := fun stmtIn tr witOut h ↦
    Spec.accepts_of_probEvent_pos_verifier_run (k := k) (t := t)
      init impl (irsEncoder k s hdvd domain) stmtIn tr witOut _ h

/-- Worst-case-per-fixed-prefix round-by-round knowledge soundness for the
exact named executable interleaved-RS extractor and its knowledge-state
function.  Both objects occur in the proposition type, rather than being
hidden behind existential quantifiers. -/
theorem oracleVerifier_rbrKnowledgeSoundnessWorstCaseWith_irsRbrExtractor
    [SampleableType F] [SampleableType ι] [Nonempty ι]
    (k s t : ℕ) (hdvd : s ∣ k) [NeZero (k / s)] (domain : ι ↪ F)
    (hfull : k / s ≤ Fintype.card ι) (δ : ℝ≥0)
    (hδ : δ < (minRelHammingDistCode
      (ReedSolomon.code domain (k / s) : Set (ι → F)) : ℝ≥0))
    {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    ((Spec.oracleVerifier (k := k) (t := t)
      (irsEncoder k s hdvd domain)).toVerifier).rbrKnowledgeSoundnessWorstCaseWith
      (WitIn := Spec.Witness (F := F) k) (WitOut := Spec.OutputWitness)
      init impl (Spec.outputRelationFor k (irsEncoder k s hdvd domain) δ)
      (Set.univ : Set ((Spec.OutputStatement ×
        ∀ i, Spec.OutputOracleStatement i) × Spec.OutputWitness))
      (irsRbrWitMid (F := F) k)
      (irsRbrExtractor k s t hdvd domain)
      (irsRbrKSF k s t hdvd domain δ init impl)
      (fun i ↦ if i.1 = 0 then irsCertifiedGammaError k s domain δ
        else (1 - δ) ^ t) := by
  classical
  unfold Verifier.rbrKnowledgeSoundnessWorstCaseWith
  intro stmtIn i transcript
  obtain ⟨⟨iv, hi⟩, hdir⟩ := i
  rcases iv with _ | _ | _ | iv
  · change Pr[ IRSExactGammaFailure k s hdvd domain δ stmtIn | $ᵗ F] ≤
      (irsCertifiedGammaError k s domain δ : ENNReal)
    exact irs_exact_gamma_failure_sample_le
      k s hdvd domain hfull δ hδ stmtIn
  · exact absurd hdir (fun h ↦ Direction.noConfusion h)
  · change Pr[ fun xs : Fin t → ι ↦ ∃ _w : PUnit,
        ¬ Spec.gammaState k (irsEncoder k s hdvd domain) δ
          stmtIn.1.1 stmtIn.1.2.1 stmtIn.1.2.2
          (stmtIn.2 0) (stmtIn.2 1)
          (transcript ⟨0, Nat.zero_lt_succ _⟩)
          (transcript ⟨1, Nat.succ_lt_succ (Nat.zero_lt_succ _)⟩) ∧
        Spec.accepts (k := k) (t := t) (irsEncoder k s hdvd domain)
          stmtIn.1 stmtIn.2
          (transcript ⟨0, Nat.zero_lt_succ _⟩)
          (transcript ⟨1, Nat.succ_lt_succ (Nat.zero_lt_succ _)⟩) xs
      | $ᵗ (Fin t → ι)] ≤ (((1 - δ) ^ t : ℝ≥0) : ENNReal)
    exact Spec.spotcheck_round_game_bound k t
      (encode := irsEncoder k s hdvd domain) δ stmtIn
      (transcript ⟨0, Nat.zero_lt_succ _⟩)
      (transcript ⟨1, Nat.succ_lt_succ (Nat.zero_lt_succ _)⟩)
  · exact absurd hi (by omega)

omit [DecidableEq ι] in
/-- Existential worst-case RBR knowledge soundness, retained as a compatibility
corollary of the exact-object theorem. -/
theorem oracleVerifier_rbrKnowledgeSoundnessWorstCase_irs
    [SampleableType F] [SampleableType ι] [Nonempty ι]
    (k s t : ℕ) (hdvd : s ∣ k) [NeZero (k / s)] (domain : ι ↪ F)
    (hfull : k / s ≤ Fintype.card ι) (δ : ℝ≥0)
    (hδ : δ < (minRelHammingDistCode
      (ReedSolomon.code domain (k / s) : Set (ι → F)) : ℝ≥0))
    {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    ((Spec.oracleVerifier (k := k) (t := t)
      (irsEncoder k s hdvd domain)).toVerifier).rbrKnowledgeSoundnessWorstCase
      (WitIn := Spec.Witness (F := F) k) (WitOut := Spec.OutputWitness)
      init impl (Spec.outputRelationFor k (irsEncoder k s hdvd domain) δ)
      (Set.univ : Set ((Spec.OutputStatement ×
        ∀ i, Spec.OutputOracleStatement i) × Spec.OutputWitness))
      (fun i ↦ if i.1 = 0 then irsCertifiedGammaError k s domain δ
        else (1 - δ) ^ t) := by
  classical
  rw [Verifier.rbrKnowledgeSoundnessWorstCase_iff_exists_with]
  exact ⟨irsRbrWitMid (F := F) k, irsRbrExtractor k s t hdvd domain,
    irsRbrKSF k s t hdvd domain δ init impl,
    oracleVerifier_rbrKnowledgeSoundnessWorstCaseWith_irsRbrExtractor
      k s t hdvd domain hfull δ hδ init impl⟩

/-- Averaged round-by-round knowledge soundness for the exact named executable
extractor and knowledge-state function, derived from the stronger
worst-case-per-prefix theorem without hiding either object. -/
theorem oracleVerifier_rbrKnowledgeSoundnessWith_irsRbrExtractor
    [SampleableType F] [SampleableType ι] [Nonempty ι]
    (k s t : ℕ) (hdvd : s ∣ k) [NeZero (k / s)] (domain : ι ↪ F)
    (hfull : k / s ≤ Fintype.card ι) (δ : ℝ≥0)
    (hδ : δ < (minRelHammingDistCode
      (ReedSolomon.code domain (k / s) : Set (ι → F)) : ℝ≥0))
    {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    (Spec.oracleVerifier (k := k) (t := t)
      (irsEncoder k s hdvd domain)).rbrKnowledgeSoundnessWith
      (WitOut := Spec.OutputWitness) init impl
      (Spec.outputRelationFor k (irsEncoder k s hdvd domain) δ)
      (Set.univ : Set ((Spec.OutputStatement ×
        ∀ i, Spec.OutputOracleStatement i) × Spec.OutputWitness))
      (irsRbrWitMid (F := F) k)
      (irsRbrExtractor k s t hdvd domain)
      (irsRbrKSF k s t hdvd domain δ init impl)
      (fun i ↦ if i.1 = 0 then irsCertifiedGammaError k s domain δ
        else (1 - δ) ^ t) := by
  unfold OracleVerifier.rbrKnowledgeSoundnessWith
  exact Verifier.rbrKnowledgeSoundnessWorstCaseWith_implies_rbrKnowledgeSoundnessWith
    init impl
    (oracleVerifier_rbrKnowledgeSoundnessWorstCaseWith_irsRbrExtractor
      k s t hdvd domain hfull δ hδ init impl)

omit [DecidableEq ι] in
/-- Existential averaged RBR knowledge soundness, retained as a compatibility
corollary of the exact-object theorem. -/
theorem oracleVerifier_rbrKnowledgeSoundness_irs
    [SampleableType F] [SampleableType ι] [Nonempty ι]
    (k s t : ℕ) (hdvd : s ∣ k) [NeZero (k / s)] (domain : ι ↪ F)
    (hfull : k / s ≤ Fintype.card ι) (δ : ℝ≥0)
    (hδ : δ < (minRelHammingDistCode
      (ReedSolomon.code domain (k / s) : Set (ι → F)) : ℝ≥0))
    {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    (Spec.oracleVerifier (k := k) (t := t)
      (irsEncoder k s hdvd domain)).rbrKnowledgeSoundness
      (WitOut := Spec.OutputWitness) init impl
      (Spec.outputRelationFor k (irsEncoder k s hdvd domain) δ)
      (Set.univ : Set ((Spec.OutputStatement ×
        ∀ i, Spec.OutputOracleStatement i) × Spec.OutputWitness))
      (fun i ↦ if i.1 = 0 then irsCertifiedGammaError k s domain δ
        else (1 - δ) ^ t) := by
  classical
  unfold OracleVerifier.rbrKnowledgeSoundness
  rw [Verifier.rbrKnowledgeSoundness_iff_exists_with]
  exact ⟨irsRbrWitMid (F := F) k, irsRbrExtractor k s t hdvd domain,
    irsRbrKSF k s t hdvd domain δ init impl,
    oracleVerifier_rbrKnowledgeSoundnessWith_irsRbrExtractor
      k s t hdvd domain hfull δ hδ init impl⟩

/-- Public exact-extractor theorem for the executable interleaved-RS toy
protocol.  The theorem type names `irsStraightlineExtractor`, so downstream
code can inspect and run exactly the algorithm whose game bound is proved. -/
theorem oracleVerifier_knowledgeSoundnessWith_irsStraightlineExtractor
    [SampleableType F] [SampleableType ι] [Nonempty ι]
    (k s t : ℕ) (hdvd : s ∣ k) [NeZero (k / s)] (domain : ι ↪ F)
    (hfull : k / s ≤ Fintype.card ι) (δ : ℝ≥0)
    (hδ : δ < (minRelHammingDistCode
      (ReedSolomon.code domain (k / s) : Set (ι → F)) : ℝ≥0))
    {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    (Spec.oracleVerifier (k := k) (t := t)
      (irsEncoder k s hdvd domain)).knowledgeSoundnessWith
      (WitOut := Spec.OutputWitness) init impl
      (Spec.outputRelationFor k (irsEncoder k s hdvd domain) δ)
      (Set.univ : Set ((Spec.OutputStatement ×
        ∀ i, Spec.OutputOracleStatement i) × Spec.OutputWitness))
      (irsStraightlineExtractor k s t hdvd domain)
      (irsExtractorCertifiedError k s t domain δ) := by
  apply Spec.protocol62_knowledgeSoundWith_of_gamma_bound
    init impl δ (irsCertifiedGammaError k s domain δ)
      (irsEncoder k s hdvd domain)
      (irsTransitionExtractor k s hdvd domain)
      (irsStraightlineExtractor k s t hdvd domain) rfl
  intro stmtIn
  exact irs_exact_gamma_failure_sample_le
    k s hdvd domain hfull δ hδ stmtIn

omit [DecidableEq ι] in
/-- Existential knowledge soundness is retained as a corollary of the public
exact-extractor theorem. -/
theorem oracleVerifier_knowledgeSoundness_irs [SampleableType F]
    [SampleableType ι] [Nonempty ι]
    (k s t : ℕ) (hdvd : s ∣ k) [NeZero (k / s)] (domain : ι ↪ F)
    (hfull : k / s ≤ Fintype.card ι) (δ : ℝ≥0)
    (hδ : δ < (minRelHammingDistCode
      (ReedSolomon.code domain (k / s) : Set (ι → F)) : ℝ≥0))
    {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    (Spec.oracleVerifier (k := k) (t := t)
      (irsEncoder k s hdvd domain)).knowledgeSoundness
      (WitOut := Spec.OutputWitness) init impl
      (Spec.outputRelationFor k (irsEncoder k s hdvd domain) δ)
      (Set.univ : Set ((Spec.OutputStatement ×
        ∀ i, Spec.OutputOracleStatement i) × Spec.OutputWitness))
      (irsExtractorCertifiedError k s t domain δ) := by
  classical
  exact OracleVerifier.knowledgeSoundness_of_with init impl
    (oracleVerifier_knowledgeSoundnessWith_irsStraightlineExtractor
      k s t hdvd domain hfull δ hδ init impl)

omit [Fintype F] in
@[simp]
theorem irsStraightlineExtractor_apply (k s t : ℕ) (hdvd : s ∣ k)
    (domain : ι ↪ F)
    (stmtIn : Spec.Statement (F := F) k ×
      (∀ i, Spec.OracleStatement ι (Fin s → F) i))
    (witOut : Spec.OutputWitness)
    (tr : (Spec.pSpec (ι := ι) (F := F) k t).FullTranscript)
    (proverLog verifierLog : QueryLog ([]ₒ : OracleSpec PEmpty)) :
    irsStraightlineExtractor k s t hdvd domain stmtIn witOut tr proverLog verifierLog =
      pure (irsTransitionExtractor k s hdvd domain stmtIn
        (tr ⟨0, Nat.zero_lt_succ _⟩)
        (tr ⟨1, Nat.succ_lt_succ (Nat.zero_lt_succ _)⟩)) := rfl

end Protocol

end ToyProblem.Impl.IRS

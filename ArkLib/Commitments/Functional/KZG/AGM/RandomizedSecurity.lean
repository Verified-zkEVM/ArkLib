/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Commitments.Functional.KZG.AGM.Security
public import ArkLib.ToVCVio.PairingDLog
public import CompPoly.Univariate.Roots.LasVegas.Correctness.Loop
public import VCVio.OracleComp.Constructions.Replicate
public import VCVio.OracleComp.EvalDist.Sum

/-!
# KZG AGM reductions with randomized root finding

A seed selects a complete root finder. Averaging the deterministic AGM bounds preserves the
additive `1 / |F|` error. The executable instance samples coefficient tables for CompPoly's
Las Vegas splitter, whose enumeration fallback ensures completeness for every table.
-/

@[expose] public section

open CompPoly OracleComp OracleSpec
open CompPoly.CPolynomial.Roots.FiniteField
open scoped ENNReal

namespace KZG.AGM

variable {F G₁ G₂ Gₜ Data T : Type} [Field F] [DecidableEq F]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
  [DecidableEq G₂] {n : ℕ}

/-- Sample a root-finder seed, then run the deterministic AGM reduction on the received keys. -/
def randomizedReduction (g₂ : G₂) (sample : ProbComp T)
    (roots : T → CPolynomial F → List F) (claims : Data → List (F × F))
    (A : Adversary F G₁ G₂ Data) : PairingDLog.Adversary F G₁ G₂ n 1 :=
  fun ck vk => do
    let t ← sample
    reduction g₂ (roots t) claims A ck vk

private theorem le_average_add (sample : ProbComp T) (game : T → ProbComp Bool)
    (p c : ℝ≥0∞) (h : ∀ t, p ≤ Pr{let b ← game t}[b = true] + c) :
    p ≤ Pr{let b ← sample >>= game}[b = true] + c := by
  rw [prEvent_bind_eq_tsum]
  have havg := tsum_prEvent_mul_le_add_of_le sample
    (f := fun _ => p) (g := fun t => Pr{let b ← game t}[b = true])
    (C := c) (fun t => by simpa only [add_comm] using h t)
  rw [tsum_prEvent_mul_of_const_on_support sample (fun _ _ => rfl)] at havg
  simpa only [add_comm] using havg

variable [Fintype F] [SampleableType F]
  [AddCommGroup Gₜ] [Module F Gₜ] [DecidableEq Gₜ]
  {e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ} {g₁ : G₁} {g₂ : G₂}

/-- Per-seed completeness gives the extractability bound after averaging over the seed. -/
theorem extract_le_pairingDLog_randomized (he : e g₁ g₂ ≠ 0)
    (sample : ProbComp T) (roots : T → CPolynomial F → List F)
    (hroots : ∀ t p, p ≠ 0 → ∀ a, p.eval a = 0 → a ∈ roots t p)
    (claims : Data → List (F × F)) (A : Adversary F G₁ G₂ Data) :
    Pr{let b ← extractExperiment (n := n) e g₁ g₂ claims A}[b = true] ≤
      Pr{let b ← (PairingDLog.experiment g₁ g₂
        (randomizedReduction (n := n) g₂ sample roots claims A))}[b = true] +
        1 / (Fintype.card F : ℝ≥0∞) := by
  unfold randomizedReduction
  rw [PairingDLog.experiment_sample]
  exact le_average_add sample _ _ _ fun t =>
    extract_le_pairingDLog he (roots t) (hroots t) claims A

/-- Per-seed completeness gives evaluation binding with the same additive distribution error. -/
theorem evalBinding_le_pairingDLog_randomized (he : e g₁ g₂ ≠ 0)
    (sample : ProbComp T) (roots : T → CPolynomial F → List F)
    (hroots : ∀ t p, p ≠ 0 → ∀ a, p.eval a = 0 → a ∈ roots t p)
    (A : Adversary F G₁ G₂ (F × F × F)) :
    Pr{let b ← (evalBindingExperiment e g₁ g₂
      (toEvalBindingAdversary (n := n) A))}[b = true] ≤
      Pr{let b ← (PairingDLog.experiment g₁ g₂
        (randomizedReduction (n := n) g₂ sample roots evalClaims A))}[b = true] +
        1 / (Fintype.card F : ℝ≥0∞) := by
  unfold randomizedReduction
  rw [PairingDLog.experiment_sample]
  exact le_average_add sample _ _ _ fun t =>
    evalBinding_le_pairingDLog he (roots t) (hroots t) A

/-- Per-seed completeness gives function binding with the same additive distribution error. -/
theorem functionBinding_le_pairingDLog_randomized (he : e g₁ g₂ ≠ 0)
    (sample : ProbComp T) (roots : T → CPolynomial F → List F)
    (hroots : ∀ t p, p ≠ 0 → ∀ a, p.eval a = 0 → a ∈ roots t p)
    (A : Adversary F G₁ G₂ (List (F × F))) :
    Pr{let b ← (functionBindingExperiment e g₁ g₂
      (toFunctionBindingAdversary (n := n) A))}[b = true] ≤
      Pr{let b ← (PairingDLog.experiment g₁ g₂
        (randomizedReduction (n := n) g₂ sample roots id A))}[b = true] +
        1 / (Fintype.card F : ℝ≥0∞) := by
  unfold randomizedReduction
  rw [PairingDLog.experiment_sample]
  exact le_average_add sample _ _ _ fun t =>
    functionBinding_le_pairingDLog he (roots t) (hroots t) A

/-- Independent probes built from independent uniform coefficient arrays, using the same
`CPolynomial.ofArray` construction as CompPoly's `uniformProbePMF`. -/
def sampleProbeTable (coefficientCount attempts : ℕ) : ProbComp (List (CPolynomial F)) :=
  replicate attempts (do
    let coeffs ← replicate coefficientCount ($ᵗ F : ProbComp F)
    return CPolynomial.ofArray coeffs.toArray)

/-- Executable Las Vegas root finding with a fixed probe table and enumeration fallback. -/
def lasVegasRoots (M : CPolynomial.Raw.MulContext F) (D : CPolynomial.Raw.ModContext F)
    (ctx : FiniteFieldContext F) (enumeration : FieldEnumeration F)
    (cfg : LasVegasConfig) (table : List (CPolynomial F)) (p : CPolynomial F) : List F :=
  (CPolynomial.Roots.FiniteField.rootsInFiniteField ctx
    (lasVegasLinearFactorProductSplitterWith M D ctx enumeration cfg
      (tableProbeFamily table)) p).toList

omit [Fintype F] [SampleableType F] in
/-- Every probe table yields a complete root finder, because failed splitting falls back to
field enumeration. -/
theorem lasVegasRoots_complete
    (M : CPolynomial.Raw.MulContext F) (D : CPolynomial.Raw.ModContext F)
    (ctx : FiniteFieldContext F) (enumeration : FieldEnumeration F)
    (cfg : LasVegasConfig) (table : List (CPolynomial F)) :
    ∀ p : CPolynomial F, p ≠ 0 → ∀ a : F, p.eval a = 0 →
      a ∈ lasVegasRoots M D ctx enumeration cfg table p := by
  apply KZG.AGM.rootsInFiniteField_complete ctx
    (lasVegasLinearFactorProductSplitterWith M D ctx enumeration cfg (tableProbeFamily table))
  intro p hp
  exact rootProduct_satisfies_lasVegasSplitterInput
    CPolynomial.Raw.MulContext.naive CPolynomial.Raw.ModContext.naive
    ctx enumeration cfg (tableProbeFamily table) hp

/-- Sample `cfg.cutoff` probes with `n + 2` coefficients and use the Las Vegas root finder.
Completeness is unconditional because the splitter falls back to enumeration; no running-time
statement is made. CompPoly's `lasVegasSplitWithTables_fallback_probability_le_binomialTail`
bounds a per-factor-table mirror, while executable `tableProbeFamily` gives every factor the
same table, so that bound does not yet apply to this finder. -/
def lasVegasReduction (g₂ : G₂)
    (M : CPolynomial.Raw.MulContext F) (D : CPolynomial.Raw.ModContext F)
    (ctx : FiniteFieldContext F) (enumeration : FieldEnumeration F) (cfg : LasVegasConfig)
    (claims : Data → List (F × F)) (A : Adversary F G₁ G₂ Data) :
    PairingDLog.Adversary F G₁ G₂ n 1 :=
  randomizedReduction g₂ (sampleProbeTable (n + 2) cfg.cutoff)
    (lasVegasRoots M D ctx enumeration cfg) claims A

/-- Las Vegas extractability requires only a nonzero pairing, with additive error `1 / |F|`. -/
theorem extract_le_pairingDLog_lasVegas (he : e g₁ g₂ ≠ 0)
    (M : CPolynomial.Raw.MulContext F) (D : CPolynomial.Raw.ModContext F)
    (ctx : FiniteFieldContext F) (enumeration : FieldEnumeration F) (cfg : LasVegasConfig)
    (claims : Data → List (F × F)) (A : Adversary F G₁ G₂ Data) :
    Pr{let b ← extractExperiment (n := n) e g₁ g₂ claims A}[b = true] ≤
      Pr{let b ← (PairingDLog.experiment g₁ g₂
        (lasVegasReduction (n := n) g₂ M D ctx enumeration cfg claims A))}[b = true] +
        1 / (Fintype.card F : ℝ≥0∞) := by
  exact extract_le_pairingDLog_randomized he _ _
    (lasVegasRoots_complete M D ctx enumeration cfg) claims A

/-- Las Vegas evaluation binding requires only a nonzero pairing, with error `1 / |F|`. -/
theorem evalBinding_le_pairingDLog_lasVegas (he : e g₁ g₂ ≠ 0)
    (M : CPolynomial.Raw.MulContext F) (D : CPolynomial.Raw.ModContext F)
    (ctx : FiniteFieldContext F) (enumeration : FieldEnumeration F) (cfg : LasVegasConfig)
    (A : Adversary F G₁ G₂ (F × F × F)) :
    Pr{let b ← (evalBindingExperiment e g₁ g₂
      (toEvalBindingAdversary (n := n) A))}[b = true] ≤
      Pr{let b ← (PairingDLog.experiment g₁ g₂
        (lasVegasReduction (n := n) g₂ M D ctx enumeration cfg evalClaims A))}[b = true] +
        1 / (Fintype.card F : ℝ≥0∞) := by
  exact evalBinding_le_pairingDLog_randomized he _ _
    (lasVegasRoots_complete M D ctx enumeration cfg) A

/-- Las Vegas function binding requires only a nonzero pairing, with error `1 / |F|`. -/
theorem functionBinding_le_pairingDLog_lasVegas (he : e g₁ g₂ ≠ 0)
    (M : CPolynomial.Raw.MulContext F) (D : CPolynomial.Raw.ModContext F)
    (ctx : FiniteFieldContext F) (enumeration : FieldEnumeration F) (cfg : LasVegasConfig)
    (A : Adversary F G₁ G₂ (List (F × F))) :
    Pr{let b ← (functionBindingExperiment e g₁ g₂
      (toFunctionBindingAdversary (n := n) A))}[b = true] ≤
      Pr{let b ← (PairingDLog.experiment g₁ g₂
        (lasVegasReduction (n := n) g₂ M D ctx enumeration cfg id A))}[b = true] +
        1 / (Fintype.card F : ℝ≥0∞) := by
  exact functionBinding_le_pairingDLog_randomized he _ _
    (lasVegasRoots_complete M D ctx enumeration cfg) A

end KZG.AGM

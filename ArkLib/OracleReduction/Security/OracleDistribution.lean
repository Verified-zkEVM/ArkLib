/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen
-/

import ArkLib.OracleReduction.Execution

/-!
  # Oracle Distributions: First-Class Sampled Oracles

  This file introduces a paper-faithful abstraction for "sample an oracle from a distribution,
  then run an adversary against it":

  ```
  let O ← D.sample
  simulateQ (D.toImpl O) A
  ```

  The mathematical primitive is `OracleDistribution`: a triple of a `Carrier` (one realization),
  a `sample : ProbComp Carrier`, and a derivation `Carrier → QueryImpl spec ProbComp` that turns a
  sampled realization into something `simulateQ` can run against.

  The function-table case (`OracleFamily`) is one realization, suitable for random-function
  oracles such as `D_Σ`, `D_IP`, `D_ROM`. Permutation components use a different carrier
  (`Equiv.Perm State`) that satisfies the bijection invariant by construction; paper `D_𝔖`
  combines this permutation carrier with a random-function carrier for `h`.

  Layered probability laws are the API surface (Level 3, post-`simulateQ`); this file states
  the foundational pieces (Levels 1-2) and leaves the lifts (Level 3) as `sorry` for downstream
  development.
-/

namespace ArkLib.OracleReduction

open OracleComp OracleSpec
open scoped ENNReal

variable {ι : Type}

/-! ## §1. Function-table carriers -/

/-- A deterministic answer table for an `OracleSpec`: each query gets a fixed response. -/
abbrev OracleFamily (spec : OracleSpec ι) : Type _ := (q : spec.Domain) → spec.Range q

/-- Promote a deterministic answer table to a `QueryImpl spec ProbComp`. -/
@[reducible]
def tableQueryImpl {spec : OracleSpec ι} (g : OracleFamily spec) :
    QueryImpl spec ProbComp := fun q => pure (g q)

/-- `VCVCompatible` on both domain and range implies `SampleableType (α → β)`.

`OracleFamily (α →ₒ β)` is definitionally `α → β`, so this instance also fires for
`[SampleableType (OracleFamily (StartType →ₒ Vector U n))]` via reducibility of `OracleFamily`. -/
noncomputable instance instSampleableTypePiVCV
    {α β : Type} [VCVCompatible α] [VCVCompatible β] :
    SampleableType (α → β) := by
  letI : FinEnum α := VCVCompatible.instFinEnum
  letI : FinEnum β := VCVCompatible.instFinEnum
  letI : Nonempty (α → β) := ⟨fun _ => default⟩
  infer_instance

/-! ## §2. The `OracleDistribution` primitive

`Carrier` lets us cover not just random-function oracles (`Carrier := OracleFamily spec`) but
also permutations (`Carrier := Equiv.Perm State`), ideal ciphers, and parameter-keyed schemes
(`Carrier := K`) — all via the same abstraction.
-/

/-! A distribution over deterministic interpretations of `spec`.
TODO: should we use `PMF`? -/
structure OracleDistribution (spec : OracleSpec ι) where
  /-- Internal carrier: what is sampled and then fixed. -/
  Carrier : Type
  /-- Sampling procedure for one realization. -/
  sample  : ProbComp Carrier
  /-- Turn a fixed realization into a deterministic interpreter. -/
  toImpl  : Carrier → QueryImpl spec ProbComp

namespace OracleDistribution

variable {spec : OracleSpec ι}

/-- Run an oracle adversary against a sampled realization. Paper-faithful syntax:
`let O ← D.sample; simulateQ (D.toImpl O) A`. -/
def runWith (D : OracleDistribution spec) {α : Type} (A : OracleComp spec α) : ProbComp α := do
  let c ← D.sample
  simulateQ (D.toImpl c) A

/-- The function-table realization (random-function oracles).
Used for `D_Σ`, `D_IP`, `D_ROM`, etc. -/
def functionTable (D : ProbComp (OracleFamily spec)) : OracleDistribution spec where
  Carrier := OracleFamily spec
  sample  := D
  toImpl  := tableQueryImpl

/-- Uniform full-table sampling. Requires `SampleableType` over the dependent product
`OracleFamily spec`, which holds when `ι` and each `spec i` are finite + decidable. -/
def uniform (spec : OracleSpec ι) [SampleableType (OracleFamily spec)] :
    OracleDistribution spec :=
  functionTable (D := $ᵗ OracleFamily spec)

/-- Bridge to the existing VCVio pattern `let k ← keygen; simulateQ (mkImpl k) A`.
Wraps a parameter sampler + table builder into a paper-faithful `OracleDistribution`. -/
def ofKeygen {K : Type} (keygen : ProbComp K) (table : K → OracleFamily spec) :
    OracleDistribution spec where
  Carrier := K
  sample  := keygen
  toImpl  := fun k => tableQueryImpl (table k)

/-- Independent product of two oracle distributions over disjoint oracle specs.

This models paper syntax such as `(O₁, O₂) ← D₁ × D₂`: sample one realization from `D₁`,
sample one realization from `D₂`, and answer sum-oracle queries by dispatching to the
corresponding sampled component. -/
def prod {ι₁ ι₂ : Type} {spec₁ : OracleSpec ι₁} {spec₂ : OracleSpec ι₂}
    (D₁ : OracleDistribution spec₁) (D₂ : OracleDistribution spec₂) :
    OracleDistribution (spec₁ + spec₂) where
  Carrier := D₁.Carrier × D₂.Carrier
  sample := do
    let c₁ ← D₁.sample
    let c₂ ← D₂.sample
    pure (c₁, c₂)
  toImpl := fun c q =>
    match q with
    | Sum.inl q₁ => D₁.toImpl c.1 q₁
    | Sum.inr q₂ => D₂.toImpl c.2 q₂

end OracleDistribution

/-! ## §3. Probability laws on `OracleDistribution.uniform`

Pointwise marginal at a single query for the uniform full-table distribution.
Lifts through `runWith` are left to downstream game proofs.
-/

section MarginalLaws

variable {spec : OracleSpec ι}

private noncomputable def mapRangeAt {spec : OracleSpec ι} (q : spec.Domain)
    (e : spec.Range q ≃ spec.Range q) : OracleFamily spec ≃ OracleFamily spec := by
  classical
  refine
    { toFun := fun g => Function.update g q (e (g q))
      invFun := fun g => Function.update g q (e.symm (g q))
      left_inv := ?_
      right_inv := ?_ }
  · intro g
    funext q'
    by_cases h : q' = q
    · subst q'
      simp [Function.update]
    · simp [Function.update, h]
  · intro g
    funext q'
    by_cases h : q' = q
    · subst q'
      simp [Function.update]
    · simp [Function.update, h]

private lemma mapRangeAt_apply_self {spec : OracleSpec ι} (q : spec.Domain)
    (e : spec.Range q ≃ spec.Range q) (g : OracleFamily spec) :
    (mapRangeAt q e g) q = e (g q) := by
  classical
  simp [mapRangeAt, Function.update]

private theorem probOutput_uniform_marginal_eq
    [SampleableType (OracleFamily spec)] (q : spec.Domain)
    (y z : spec.Range q) :
    Pr[= y | do let g ← (OracleDistribution.uniform spec).sample; pure (g q)] =
      Pr[= z | do let g ← (OracleDistribution.uniform spec).sample; pure (g q)] := by
  classical
  let e : spec.Range q ≃ spec.Range q := Equiv.swap y z
  let T : OracleFamily spec ≃ OracleFamily spec := mapRangeAt q e
  rw [probOutput_bind_eq_tsum, probOutput_bind_eq_tsum]
  change (∑' (x : OracleFamily spec),
      Pr[= x | (OracleDistribution.uniform spec).sample] *
        Pr[= y | (pure (x q) : ProbComp (spec.Range q))]) =
    ∑' (x : OracleFamily spec),
      Pr[= x | (OracleDistribution.uniform spec).sample] *
        Pr[= z | (pure (x q) : ProbComp (spec.Range q))]
  rw [← Equiv.tsum_eq T (fun g =>
    Pr[= g | (OracleDistribution.uniform spec).sample] *
      Pr[= y | (pure (g q) : ProbComp (spec.Range q))])]
  apply tsum_congr
  intro g
  have hsample : Pr[= T g | (OracleDistribution.uniform spec).sample] =
      Pr[= g | (OracleDistribution.uniform spec).sample] := by
    exact SampleableType.probOutput_selectElem_eq (T g) g
  have hpure : Pr[= y | (pure ((T g) q) : ProbComp (spec.Range q))] =
      Pr[= z | (pure (g q) : ProbComp (spec.Range q))] := by
    rw [probOutput_pure, probOutput_pure]
    change (if y = (mapRangeAt q (Equiv.swap y z) g) q then 1 else 0) =
      if z = g q then 1 else 0
    rw [mapRangeAt_apply_self]
    by_cases hz : z = g q
    · have hy : y = (Equiv.swap y z) (g q) := by
        calc
          y = (Equiv.swap y z) z := (Equiv.swap_apply_right y z).symm
          _ = (Equiv.swap y z) (g q) := congrArg (Equiv.swap y z) hz
      rw [if_pos hy, if_pos hz]
    · have hy : y ≠ (Equiv.swap y z) (g q) := by
        intro hy
        have hswap : (Equiv.swap y z) (g q) = y := hy.symm
        rw [Equiv.swap_apply_eq_iff] at hswap
        rw [Equiv.swap_apply_left] at hswap
        exact hz hswap.symm
      rw [if_neg hy, if_neg hz]
  rw [hsample, hpure]

/-- **Level 2.** Marginal at a single query is uniform over the range. -/
theorem probOutput_uniform_marginal
    [SampleableType (OracleFamily spec)] (q : spec.Domain)
    [Fintype (spec.Range q)] (y : spec.Range q) :
    Pr[= y | do let g ← (OracleDistribution.uniform spec).sample; pure (g q)] =
      (Fintype.card (spec.Range q) : ℝ≥0∞)⁻¹ := by
  classical
  let M : ProbComp (spec.Range q) := do
    let g ← (OracleDistribution.uniform spec).sample
    pure (g q)
  change Pr[= y | M] = (Fintype.card (spec.Range q) : ℝ≥0∞)⁻¹
  have hsum : ∑ z, Pr[= z | M] = 1 := by
    exact sum_probOutput_eq_one (HasEvalPMF.probFailure_eq_zero M)
  have hconst : ∑ _z : spec.Range q, Pr[= y | M] = 1 := by
    rw [← hsum]
    apply Finset.sum_congr rfl
    intro z _hz
    change Pr[= y | do let g ← (OracleDistribution.uniform spec).sample; pure (g q)] =
      Pr[= z | do let g ← (OracleDistribution.uniform spec).sample; pure (g q)]
    exact probOutput_uniform_marginal_eq q y z
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hconst
  rw [mul_comm] at hconst
  exact ENNReal.eq_inv_of_mul_eq_one_left hconst

/-- **Modular pointwise uniform query.** *"Given `g` sampled from `uniform spec`, the
probability that `g q = y` is `1 / |Range q|`."* `g` is the predicate's bound variable,
**not** a do-binding — the surrounding security experiment can keep
`(uniform spec).sample` as an opaque step and apply this lemma at any point that reads
its result via a query. -/
lemma probEvent_uniform_query_eq
    [SampleableType (OracleFamily spec)] (q : spec.Domain)
    [Fintype (spec.Range q)] (y : spec.Range q) :
    Pr[ fun g => g q = y | (OracleDistribution.uniform spec).sample ] =
      (Fintype.card (spec.Range q) : ℝ≥0∞)⁻¹ := by
  rw [← probOutput_uniform_marginal (spec := spec) q y, ← probEvent_eq_eq_probOutput]
  change Pr[ (fun x => x = y) ∘ (fun g => g q) | (OracleDistribution.uniform spec).sample ] =
    Pr[ (· = y) | (OracleDistribution.uniform spec).sample >>=
      pure ∘ (fun g : OracleFamily spec => g q) ]
  rw [probEvent_bind_pure_comp]
  rfl

end MarginalLaws

/-! ## §6. Examples — random-function oracle distributions

This section demonstrates the *random-function* `OracleDistribution` shape — sample a uniform
function-table over a finite spec, then expose it as a deterministic interpreter. All examples
below are instances of `OracleDistribution.uniform`. They cover three reusable shapes:

- `DROM` — generic random oracle `Input →ₒ Output` (not DSFS-specific).
- `DIP`  — uniform random function over `fsChallengeOracle Statement pSpec`. Generic; DSFS uses
  this with a salted statement type at the call sites (see "DSFS mapping" below).
- (concrete `D_Σ` / Hyb2 — illustrated as code sketches; concrete instances live downstream.)

Permutation-carrier distributions (paper `D_𝔖`) do *not* fit this random-function template — they
require `Carrier := Equiv.Perm State` to enforce the bijection invariant. The concrete DSFS
`D_𝔖` lives in `FiatShamir/DuplexSponge/Defs.lean`.

### DSFS Section 5 mapping

- `D_𝔖`  — base IPM. Spec `duplexSpongeChallengeOracle StmtIn U`. Shape:
  `OracleFamily × Equiv.Perm`. Defined in `DuplexSponge/Defs.lean`.
- `D_Σ`  — Hyb1 (encoded). Spec `section58EncodedChallengeOracle StmtIn pSpec δ`.
  Shape: random function. Defined in
  `DuplexSponge/Security/TraceTransform.lean`.
- Eq. 52 — Hyb2 (decoded). Spec `section58DecodedChallengeOracle StmtIn pSpec δ`.
  Shape: random function (this is *not* `D_Σ`). Same file as Hyb1.
- `D_IP` — Hyb3 / Hyb4 (salted). Spec
  `fsChallengeOracle (Vector U δ × StmtIn) pSpec`. Shape: random function.
  Realized at call sites.

The §5.8-specific encoded/decoded challenge oracles currently live in
`Security/TraceTransform.lean`; if they grow theorem-facing uses they may deserve their own
`Defs`-level module. To keep `OracleDistribution.lean` import-light, this file demonstrates only
the *generic* random-function shapes; concrete DSFS instances are produced at the call sites by
partial application of `OracleDistribution.uniform`.
-/

namespace OracleDistribution.Examples

/-! ### `D_ROM` — random-function constructor. -/

/-- Generic `D_ROM` constructor for any random-function oracle spec:
uniformly sample one deterministic table realization. -/
@[reducible]
def DROM {ι : Type} (spec : OracleSpec ι) [SampleableType (OracleFamily spec)] :
    OracleDistribution spec :=
  OracleDistribution.uniform spec

/-! ### `D_IP` — ideal-protocol Fiat-Shamir challenger.

The Fiat-Shamir challenge oracle (`fsChallengeOracle` / `srChallengeOracle`) is keyed by
`(challenge index, statement, prover-prefix)` and returns the round-`i` challenge type.
`D_IP` samples a single deterministic such function.

DSFS Hyb3 / Hyb4 (salted) instantiate `D_IP` with the *salted* statement type
`Statement := Vector U δ × StmtIn`, i.e. `DIP (Vector U δ × StmtIn) pSpec`. -/

/-- Bridge instance: granular `VCVCompatible` hypotheses on statement, message, and challenge
types suffice to derive `SampleableType (OracleFamily (fsChallengeOracle Statement pSpec))`.

The oracle family is a finite function table `(q : Domain) → pSpec.Challenge q.1` where the
domain is a dependent sigma type over the challenge index and the message-prefix history.
Finiteness follows from `VCVCompatible` on each component via `FinEnum.sigma` + `Pi.finEnum`.

Note: The connection `pSpec.MessageUpTo k pSpec i = pSpec.Message i_orig` requires unfolding
`ProtocolSpec.take` which is not `@[reducible]`. The proof is deferred (see `sorry`). -/
noncomputable instance instSampleableTypeFSChallengeOracle
    {n : ℕ} {pSpec : ProtocolSpec n} {Statement : Type}
    [VCVCompatible Statement]
    [∀ i, VCVCompatible (pSpec.Message i)]
    [∀ i, VCVCompatible (pSpec.Challenge i)] :
    SampleableType (OracleFamily (ProtocolSpec.fsChallengeOracle Statement pSpec)) := by
  -- `OracleFamily spec = (q : Domain) → spec.Range q` (dependent Pi over the domain sigma type).
  -- Domain = Σ i : ChallengeIdx, (Statement × MessagesUpTo i.1.castSucc).
  -- Range q = pSpec.Challenge q.1.
  -- Each component is VCVCompatible; the full table is finite via FinEnum.sigma + Pi.finEnum.
  -- The MessagesUpTo component needs pSpec.MessageUpTo k i = pSpec.Message i_orig; deferred.
  sorry

/-- `D_IP` over `fsChallengeOracle Statement pSpec`: uniform random function from prover-prefix
queries to challenges. DSFS Hyb3 / Hyb4 use this with `Statement := Vector U δ × StmtIn`. -/
@[reducible]
noncomputable def DIP {n : ℕ} (Statement : Type) (pSpec : ProtocolSpec n)
    [VCVCompatible Statement]
    [∀ i, VCVCompatible (pSpec.Message i)]
    [∀ i, VCVCompatible (pSpec.Challenge i)] :
    OracleDistribution (ProtocolSpec.fsChallengeOracle Statement pSpec) :=
  DROM (spec := ProtocolSpec.fsChallengeOracle Statement pSpec)

/-! ### `D_Σ` — §5.8 encoded-challenge oracle.

Paper `D_Σ` (Hyb1) has domain
`(i : pSpec.ChallengeIdx) × (StmtIn × Vector U δ × List <prover-prefix entries>)`
and range `Vector U (challengeSize i)`.

The realization lives at the call site (e.g. `FiatShamir/DuplexSponge/Security/...`):
```
def DΣ_encoded {n : ℕ} (StmtIn : Type) (pSpec : ProtocolSpec n) (δ : ℕ) … :
    OracleDistribution (section58EncodedChallengeOracle StmtIn pSpec δ) :=
  OracleDistribution.uniform _
```
The pattern is identical to `DROM` / `DIP`; only the underlying spec differs. -/

/-! ### Hyb2 decoded challenge distribution.

Hyb2 samples `e_i` with the same input domain as `D_Σ`, but range `pSpec.Challenge i`
(`𝓜_{V,i}` in the paper). This is not `D_Σ`; it is the decoded verifier-message oracle family
from Eq. (52). At the concrete DSFS call site:
```
def DHyb2_decoded {n : ℕ} (StmtIn : Type) (pSpec : ProtocolSpec n) (δ : ℕ) … :
    OracleDistribution (section58DecodedChallengeOracle StmtIn pSpec δ) :=
  OracleDistribution.uniform _
```
-/

end OracleDistribution.Examples

/-! ## §7. Probes — FinEnum-route inference for `SampleableType (OracleFamily spec)`

These probes verify that `[FinEnum ι] + [∀ q, FinEnum (spec.Range q)] + Nonempty` is enough
for typeclass synthesis to find `SampleableType (OracleFamily spec)` via
`Pi.finEnum` ∘ `FinEnum.SampleableType`. If they typecheck, the FinEnum route is free.
-/

section BridgeProbes

noncomputable def VCVCompatible.toFinEnum_aux {α : Type} [VCVCompatible α] : FinEnum α where
  card := Fintype.card α
  equiv := Fintype.equivFin α
  decEq := inferInstance

-- rootVectorEquivFin : Vector α n ≃ (Fin n → α), direction: from Vector to Pi
noncomputable def Vector.toFinEnum_aux {α : Type} {n : ℕ} [FinEnum α] : FinEnum (Vector α n) :=
  FinEnum.ofEquiv _ Equiv.rootVectorEquivFin

-- Composite probe 1: hash oracle family
noncomputable example {StartType U : Type} (n : ℕ) [VCVCompatible StartType] [VCVCompatible U] :
    SampleableType (OracleFamily (StartType →ₒ Vector U n)) := by
  letI : FinEnum StartType := VCVCompatible.toFinEnum_aux
  letI : FinEnum U := VCVCompatible.toFinEnum_aux
  letI : FinEnum (Vector U n) := Vector.toFinEnum_aux
  infer_instance

-- Composite probe 2: Equiv.Perm of Vector (manual FinEnum construction for Perm)
noncomputable example {U : Type} (n : ℕ) [VCVCompatible U] :
    SampleableType (Equiv.Perm (Vector U n)) := by
  letI : FinEnum U := VCVCompatible.toFinEnum_aux
  letI : FinEnum (Vector U n) := Vector.toFinEnum_aux
  -- FinEnum → Fintype + DecidableEq on Vector U n
  letI : Fintype (Vector U n) := inferInstance
  letI : DecidableEq (Vector U n) := inferInstance
  -- Fintype + DecidableEq on Perm
  letI : Fintype (Equiv.Perm (Vector U n)) := inferInstance
  letI : DecidableEq (Equiv.Perm (Vector U n)) := inferInstance
  -- Build FinEnum (Perm ...) noncomputably
  letI : FinEnum (Equiv.Perm (Vector U n)) :=
    { card := Fintype.card (Equiv.Perm (Vector U n))
      equiv := Fintype.equivFin _
      decEq := inferInstance }
  letI : Nonempty (Equiv.Perm (Vector U n)) := ⟨Equiv.refl _⟩
  infer_instance

end BridgeProbes

end ArkLib.OracleReduction

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

  See `.planning/dsfs-section5-migration/oracle-distribution-requirements.md` for the design
  rationale.
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

/-! ## §2. The `OracleDistribution` primitive

`Carrier` lets us cover not just random-function oracles (`Carrier := OracleFamily spec`) but
also permutations (`Carrier := Equiv.Perm State`), ideal ciphers, and parameter-keyed schemes
(`Carrier := K`) — all via the same abstraction.
-/

/-- A distribution over deterministic interpretations of `spec`. -/
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
  functionTable ($ᵗ OracleFamily spec)

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

@[simp]
lemma functionTable_sample (D : ProbComp (OracleFamily spec)) :
    (functionTable D).sample = D := rfl

@[simp]
lemma functionTable_toImpl (D : ProbComp (OracleFamily spec)) (g : OracleFamily spec) :
    (functionTable D).toImpl g = tableQueryImpl g := rfl

@[simp]
lemma uniform_sample (spec : OracleSpec ι) [SampleableType (OracleFamily spec)] :
    (uniform spec).sample = ($ᵗ OracleFamily spec) := rfl

@[simp]
lemma ofKeygen_sample {K : Type} (keygen : ProbComp K) (table : K → OracleFamily spec) :
    (ofKeygen keygen table).sample = keygen := rfl

@[simp]
lemma ofKeygen_toImpl {K : Type} (keygen : ProbComp K) (table : K → OracleFamily spec) (k : K) :
    (ofKeygen keygen table).toImpl k = tableQueryImpl (table k) := rfl

@[simp]
lemma prod_sample {ι₁ ι₂ : Type} {spec₁ : OracleSpec ι₁} {spec₂ : OracleSpec ι₂}
    (D₁ : OracleDistribution spec₁) (D₂ : OracleDistribution spec₂) :
    (prod D₁ D₂).sample = (do
      let c₁ ← D₁.sample
      let c₂ ← D₂.sample
      pure (c₁, c₂)) := rfl

@[simp]
lemma prod_toImpl_inl {ι₁ ι₂ : Type} {spec₁ : OracleSpec ι₁} {spec₂ : OracleSpec ι₂}
    (D₁ : OracleDistribution spec₁) (D₂ : OracleDistribution spec₂)
    (c : D₁.Carrier × D₂.Carrier) (q : spec₁.Domain) :
    (prod D₁ D₂).toImpl c (Sum.inl q) = D₁.toImpl c.1 q := rfl

@[simp]
lemma prod_toImpl_inr {ι₁ ι₂ : Type} {spec₁ : OracleSpec ι₁} {spec₂ : OracleSpec ι₂}
    (D₁ : OracleDistribution spec₁) (D₂ : OracleDistribution spec₂)
    (c : D₁.Carrier × D₂.Carrier) (q : spec₂.Domain) :
    (prod D₁ D₂).toImpl c (Sum.inr q) = D₂.toImpl c.2 q := rfl

end OracleDistribution

/-! ## §3. Stateful realizations and refinement

For executable / lazy implementations (lazy random oracle, lazy ideal cipher), the operational
form lives in `StateT σ ProbComp`. The contract relating it to the abstract `OracleDistribution`
is `refines : Prop` — a Lean predicate, not English.
-/

/-- Stateful (executable) realization. The `init` produces an initial state and `impl` answers
queries while threading state. -/
structure StatefulOracleDistribution (spec : OracleSpec ι) where
  /-- Internal mutable state (e.g. a query cache). -/
  State : Type
  /-- Sample an initial state. -/
  init  : ProbComp State
  /-- Stateful query interpreter. -/
  impl  : QueryImpl spec (StateT State ProbComp)

namespace StatefulOracleDistribution

variable {spec : OracleSpec ι}

/-- Run an adversary against the stateful realization, discarding the final state. -/
def runWith (SD : StatefulOracleDistribution spec) {α : Type} (A : OracleComp spec α) :
    ProbComp α := do
  let s ← SD.init
  (simulateQ SD.impl A).run' s

/-- `SD` refines the abstract distribution `D` when every adversary observes the same induced
distribution against either. This is the load-bearing contract for lazy/full-table equivalence
(e.g. cached lazy random oracle ≡ uniform `D_ROM` on finite domains). -/
def refines (SD : StatefulOracleDistribution spec) (D : OracleDistribution spec) : Prop :=
  ∀ {α : Type} (A : OracleComp spec α), SD.runWith A = D.runWith A

end StatefulOracleDistribution

/-! ## §4. Probability laws — Level 1

Level 1: full-table uniform follows directly from VCVio's `probOutput_uniformSample`.
Levels 2-3 (marginals, independence, repeat-consistency, lifts through `runWith`) are stated
below as proof obligations for downstream development.
-/

section UniformLaws

variable {spec : OracleSpec ι}

/-- **Level 1.** Full-table uniform: each oracle realization is sampled with probability
`1 / |OracleFamily spec|` under the uniform distribution. -/
theorem probOutput_uniformOracleFamily
    [SampleableType (OracleFamily spec)] [Fintype (OracleFamily spec)]
    (g : OracleFamily spec) :
    Pr[= g | (OracleDistribution.uniform spec).sample] =
      (Fintype.card (OracleFamily spec) : ℝ≥0∞)⁻¹ := by
  rw [OracleDistribution.uniform_sample]
  exact probOutput_uniformSample _ g

end UniformLaws

/-! ## §5. Probability laws — Level 2 and Level 3 (proof obligations)

These are the laws security proofs actually consume. Level 2 is "post-sample, pre-`simulateQ`":
joint distribution on `OracleFamily` directly. Level 3 is "post-`simulateQ`": after running an
adversary. Statements are provided so callers can refer to them by name; proofs are deferred.
-/

section MarginalLaws

variable {spec : OracleSpec ι}

/-- **Level 2.** Marginal at a single query is uniform over the range. -/
theorem probOutput_uniform_marginal
    [SampleableType (OracleFamily spec)] (q : spec.Domain)
    [Fintype (spec.Range q)] (y : spec.Range q) :
    Pr[= y | do let g ← (OracleDistribution.uniform spec).sample; pure (g q)] =
      (Fintype.card (spec.Range q) : ℝ≥0∞)⁻¹ := by
  sorry

/-- **Level 2.** Distinct queries produce independent answers under uniform full-table. -/
theorem probOutput_uniform_indep
    [SampleableType (OracleFamily spec)]
    {q₁ q₂ : spec.Domain} (hne : q₁ ≠ q₂)
    (y₁ : spec.Range q₁) (y₂ : spec.Range q₂) :
    Pr[= (y₁, y₂) | do let g ← (OracleDistribution.uniform spec).sample; pure (g q₁, g q₂)] =
      Pr[= y₁ | do let g ← (OracleDistribution.uniform spec).sample; pure (g q₁)] *
      Pr[= y₂ | do let g ← (OracleDistribution.uniform spec).sample; pure (g q₂)] := by
  sorry

/-- **Level 2.** Repeated query returns the same answer with probability one
(joint at distinct outputs has probability zero). -/
theorem probOutput_uniform_repeat_consistent
    [SampleableType (OracleFamily spec)] (q : spec.Domain)
    {y₁ y₂ : spec.Range q} (hne : y₁ ≠ y₂) :
    Pr[= (y₁, y₂) | do let g ← (OracleDistribution.uniform spec).sample; pure (g q, g q)] = 0 := by
  sorry

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

/-! ### `D_ROM` — random oracle hash. -/

/-- `D_ROM` over `Input →ₒ Output`: uniform random function, paper notation `H ← D_ROM`. -/
@[reducible]
def DROM (Input Output : Type) [SampleableType (OracleFamily (Input →ₒ Output))] :
    OracleDistribution (Input →ₒ Output) :=
  OracleDistribution.uniform _

/-! ### `D_IP` — ideal-protocol Fiat-Shamir challenger.

The Fiat-Shamir challenge oracle (`fsChallengeOracle` / `srChallengeOracle`) is keyed by
`(challenge index, statement, prover-prefix)` and returns the round-`i` challenge type.
`D_IP` samples a single deterministic such function.

DSFS Hyb3 / Hyb4 (salted) instantiate `D_IP` with the *salted* statement type
`Statement := Vector U δ × StmtIn`, i.e. `DIP (Vector U δ × StmtIn) pSpec`. -/

/-- `D_IP` over `fsChallengeOracle Statement pSpec`: uniform random function from prover-prefix
queries to challenges. DSFS Hyb3 / Hyb4 use this with `Statement := Vector U δ × StmtIn`. -/
@[reducible]
def DIP {n : ℕ} (Statement : Type) (pSpec : ProtocolSpec n)
    [SampleableType (OracleFamily (ProtocolSpec.fsChallengeOracle Statement pSpec))] :
    OracleDistribution (ProtocolSpec.fsChallengeOracle Statement pSpec) :=
  OracleDistribution.uniform _

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

end ArkLib.OracleReduction

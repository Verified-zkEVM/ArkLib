# KZG evaluation binding: a vacuity finding, an honest de-vacuation, and two GGM soundness bounds

This directory (`ArkLib/Scratch/KzgVacuity/`) contains a mechanized formalization-soundness
finding about `ArkLib/Commitments/Functional/KZG/Binding.lean`, a minimal fix applied to that
file, and the generic-group soundness bound the fix points at — proved in **two** standard
generic-group models, **both wired to ArkLib's real `tSdhExperiment`**. Everything is checked
against ArkLib at `d72f8392ff03047dc5386f4f4bb513743e7ada65` (Lean `v4.31.0`, VCVio/CompPoly
`v4.31.0`), imports the genuine upstream modules, redefines nothing, builds `sorry`-free, and has
axiom closure exactly `[propext, Classical.choice, Quot.sound]`.

**This is not a security advisory.** There is no vulnerability, nothing exploitable, and no
embargo. KZG, the `t`-SDH assumption as normally stated, and the reduction in `Binding.lean`
are all sound. The issue is the *quantifier* in one Lean assumption. We found the identical
pattern in our own Lean floors first; we bring it here as a shared field lesson, not a dunk.

---

## 1. The finding: `tSdhAssumption` is vacuous, and so is `binding`

`Groups.tSdhAssumption` quantifies over an *unrestricted* adversary type:

```lean
def tSdhAssumption … (D : ℕ) (error : ℝ≥0) : Prop :=
  ∀ (adversary : tSdhAdversary D …),
    tSdhExperiment (g₁ := g₁) (g₂ := g₂) D adversary ≤ (error : ℝ≥0∞)
```

`tSdhAdversary` lands in `StateT unifSpec.QueryCache ProbComp`. Because `ProbComp` is a free
monad over oracle queries, **pure computation is free** and no resource bound is imposed. An
adversary may therefore `pure` an arbitrary noncomputable function of the SRS at zero cost.

The SRS includes the verifier leg `(g₂, g₂^τ)`, which determines `τ` whenever `g₂ ≠ 1`, and
ArkLib's own `Algebra.lean:105 exists_zmod_power_of_generator` makes that discrete log
`Classical.choice`-definable. So a one-line adversary recovers `τ`, returns the `t`-SDH
solution `(c = 0, g₁^{1/τ})`, and wins with probability *exactly* `1` (it makes zero oracle
queries). Consequently:

- `tSdhAssumption D error` is **false for every `error < 1`** (`not_tSdhAssumption`), and
- trivially true for `error ≥ 1`, since a probability is `≤ 1` (`tSdhAssumption_trivial_of_one_le`).

`KZG.CommitmentScheme.binding` takes `tSdhAssumption` as a hypothesis and concludes a bound
at the *same* `error`, so it carries no information at any parameter: below `1` its premise is
unsatisfiable, at or above `1` its conclusion is free. `binding`'s own `hpair : pairing g₁ g₂ ≠ 0`
even *forces* `g₂ ≠ 1` (via bilinearity and `map_zero`), so the killing adversary's one
hypothesis is discharged from `binding`'s own premises (`binding_hypotheses_unsatisfiable`).

The sibling `Groups.arsdhAssumption` — the hypothesis of `KZG.function_binding` — has the
identical unrestricted quantifier and falls the identical way (`not_arsdhAssumption` /
`arsdhAssumption_trivial_of_one_le`); the ARSDH branch's `D + 2 ≤ p` is exactly the
`p ≥ n + 2` that `function_binding` already carries.

The mechanized witness is `KzgVacuity.lean` (namespace `ArkLibVacuity`). It ships with
canaries — `tSdhExperiment_givingUpAdversary = 0`, `arsdhExperiment_givingUpAdversary = 0` —
proving the `= 1` is a fact about *this* adversary, not an artifact of the probability
machinery: the experiment genuinely discriminates.

The idiom is not special to `t`-SDH. Stated in ArkLib's adversary type, a `q`-strong-DLOG base
assumption ("recover the SRS trapdoor `τ` from the KZG power-SRS") is vacuous the same way, by
the identical `Classical.choice` extraction — so "reduce KZG binding to `q`-DLOG instead" does
not, by itself, escape the hole: any base assumption must first be stated over a sound
adversary class.

**Why `#print axioms` does not catch this.** `binding` is axiom-clean *and* vacuous at the
same time. A clean axiom closure certifies "no `sorry`, no `native_decide`"; it says nothing
about whether a hypothesis is satisfiable. That blindness is the whole reason the pattern is
easy to miss, and it is why we treat it as a discipline problem rather than a typo.

---

## 2. The fix: an extraction-shaped restatement (`+42 / −14`, one file)

The right tool here is **not** query-bounding. `t`-SDH is an *algebraic* assumption whose
killing adversary makes zero queries, so an `IsQueryBoundP`-style restriction (the correct
fix for random-oracle/hash floors) constrains something this adversary never does. The honest
menu is the generic/algebraic group model, or an extraction-shaped restatement that turns the
assumption into *data the adversary must produce*. We ship the latter as the minimal step —
it is the pattern VCVio already uses for its Merkle `Binding`.

The key observation is structural: **ArkLib's reduction is already fully constructive.**
`binding`'s proof is a five-step `calc`; the first four steps are unconditional transition
lemmas, and `tSdhAssumption` is consumed in exactly one place — the last `≤`. So the fix is to
*split the calc at that last step*:

```lean
/-- Extraction-shaped evaluation binding: every binding adversary yields — as the explicit
    reduction `bindingReduction … adversary` — a t-SDH adversary whose success probability
    upper-bounds its binding advantage. No assumption `Prop`, hence nothing for a
    `Classical.choice` adversary to inhabit. -/
theorem binding_reduces_to_tSdh {g₁ : G₁} {g₂ : G₂} (hg₁ : g₁ ≠ 1)
    (hpair : pairing g₁ g₂ ≠ 0) [SampleableType G₁] (AuxState : Type)
    (adversary : KzgBindingAdversary p G₁ G₂ n unifSpec AuxState) :
    Commitment.bindingExperiment … (kzg …) AuxState adversary
      ≤ Groups.tSdhExperiment (g₁ := g₁) (g₂ := g₂) n
          (bindingReduction … AuxState adversary) := by
  … -- the existing calc prefix, verbatim; the four transition lemmas are untouched

/-- The original assumption-form binding, now a one-line corollary. -/
theorem binding … (htSdh : Groups.tSdhAssumption … n tSdhError) :
    Commitment.binding … (kzg …) tSdhError := by
  simp only [Commitment.binding]; intro AuxState adversary
  exact (binding_reduces_to_tSdh (pairing := pairing) hg₁ hpair AuxState adversary).trans
    (t_sdh_error_bound … tSdhError htSdh adversary)
```

`binding_reduces_to_tSdh` carries the full constructive content *without* the
universally-quantified assumption, so it is immune to the vacuity: the bound relates two
concrete probabilities — *this* adversary's advantage and *its* reduction's success — and
carries content at every parameter. `binding` keeps its exact signature (backward
compatible) as an immediate corollary; its docstring notes that the corollary only becomes
informative once `tSdhAssumption` is stated over a restricted adversary class.

The full diff is `+42 / −14` in `Binding.lean`. The whole tree still builds; both theorems are
`[propext, Classical.choice, Quot.sound]`.

### The fix survives the exact attack (mechanized)

A de-vacuation is only honest if it survives the attack rather than merely avoiding it.
`RepairSurvives.lean` (namespace `ArkLibRepairCheck`) proves both facts as one conjunction,
`repair_survives_attack`:

1. the identical trapdoor-extracting adversary *still* refutes `tSdhAssumption` below `1`
   (we did not weaken the assumption), **and**
2. `binding_reduces_to_tSdh` holds *unconditionally* — it takes no `tSdhAssumption`
   hypothesis, so leg (1) has nothing to empty.

Both hold at once, in the same groups, `sorry`-free. That is the precise sense in which the
vacuity is closed: the disease was an unsatisfiable premise; the cure removes the premise
while keeping every step of the reduction.

---

## 3. The sound numeric bound: KZG binding in the generic group model, two ways — both wired

The extraction-shaped fix removes the vacuity but hands *no number*: its right-hand side is
still `tSdhExperiment` of the constructed reduction adversary. The number a KZG binding bound
ultimately rests on is the generic-group hardness of `t`-SDH. This directory mechanizes it in
the **two** standard generic-group models — Maurer's explicit-equality model [Mau05] and
Shoup's random-encoding model [Sho97] — and **wires both to ArkLib's real `tSdhExperiment`**.
Both yield the same Boneh–Boyen [BB04] numerator `C(fuel+D+4, 2)·D + (D+1)` over `p − 1`.

Group elements are modelled as opaque handles carrying *ordinary* polynomials in the trapdoor
indeterminate `X` (**not Laurent** — group inversion negates the exponent, it does not
introduce `X⁻¹`; that is exactly why a winning `1/(X+c)` output is unrepresentable and forces
a bounded-degree root event). The oracle is pairing-free (`lin` moves only), matching ArkLib's
`G₁`-only `tSdhAdversary`, so the honest collision degree is `δ = D`.

### 3a. Maurer explicit-equality track — wired via `embed`

The Maurer model spends a `Move.query` step per equality test; only queried pairs enter the
bad event. The capstone is `GgmEndToEnd.tSdh_ggm_sound`, stated about ArkLib's **real**
`tSdhExperiment` via the embedding `embed`:

```lean
theorem tSdh_ggm_sound … (strat : Strat p) (fuel : ℕ) :
    tSdhExperiment D (embed strat) ≤ (C(fuel+D+4,2)·D + (D+1)) / (p − 1)
```

with a companion `tSdh_ggm_sound_lt_one` giving a genuine `< 1` in the standard regime
`C(fuel+D+4,2)·D + (D+1) < p − 1` (at cryptographic parameters, `≈ 2⁻²³⁴`). It quantifies over
the **image of the generic embedding** `embed` — the generic-restricted class that escapes the
vacuity: `embed strat` receives only equality booleans, never a group element, so it can only
realize `g₁^{f(τ)}` with `deg f ≤ D`, which is exactly what the counting bound bounds. The full
`tSdhAdversary` type does *not* escape (§1 proves the statement over it false); the embedding is
what makes the number meaningful.

### 3b. Shoup random-encoding track — also wired via `embedShoup`

The Shoup model gives the adversary **free** comparison: at every step it observes the full
pairwise-equality matrix of all its held encodings and branches on the entire pattern-history,
at no fuel or handle cost. This is the genuinely different model — the all-pairs collision
event is now *tight* rather than a conservative over-count. It is proved in two layers:

* `GgmShoup.shoup_ggm_sound` states the bound about the free-comparison experiment
  `shoupExperiment` on that model's own SRS seeding — the model-internal statement, where the
  crux (an identical-until-bad hybrid over a whole equality matrix, `runShoup_congr_off_bad`,
  discharged from a single global non-collision fact) is proved rather than assumed.
* `GgmShoupEmbed.shoup_tSdh_ggm_sound` **wires that model into ArkLib's real `tSdhExperiment`**,
  exactly as the Maurer track is wired via `embed`:

```lean
theorem shoup_tSdh_ggm_sound (hord₁ : orderOf g₁ = p) (hD : 1 ≤ D)
    (strat : ShoupStrat p) (fuel : ℕ) :
    tSdhExperiment (g₁ := g₁) (g₂ := g₂) D (embedShoup g₁ D fuel strat)
      ≤ (C(fuel+D+4,2)·D + (D+1)) / (p − 1)
```

with a companion `shoup_tSdh_ggm_sound_lt_one`. Free comparison is **realized, not assumed**:
a real `tSdhAdversary` holds actual `G₁` elements and can test equality of any two it holds for
free (`DecidableEq G₁`, classically). In a prime-order group the exponent encoding
`a ↦ g₁^{a.val}` is injective (`GgmArkLibTransport.gpow_val_inj_iff`), so the full pairwise
group-equality matrix of the adversary's realized handles equals the symbolic
`eqPattern (realAns τ)` the strategy branches on — discharged off the bad event by
`groupEqPattern_eq`. The lazily-sampled encoding `σ : ZMod p ↪ E` never enters the
mechanization: injectivity folds it away, exactly as `gpow_val_inj_iff` folds the concrete
encoding away in the Maurer embed.

The numerator is byte-identical to the Maurer track's; the difference is the *model in which it
is proved*. With both `embed` and `embedShoup` in place, the two standard GGM formulations bound
the **same** real experiment through one socket each.

### The dependency spine

All `sorry`-free, axioms exactly `[propext, Classical.choice, Quot.sound]`:

| Module | Role |
|---|---|
| `GgmCandidate` | static (zero-query) Schwartz–Zippel core, `(D+1)/(p−1)`; reused by both tracks |
| `GgmDegreeInvariant` | structural handle-table degree invariants (`natDegree_getD_le`, …); reused by both tracks |
| `GgmAdaptive` | the adaptive `q`-query bound; identical-until-bad hybrid by induction on fuel |
| `GgmRandomEncoding` | the all-pairs (quadratic) collision count at `δ = D`; table size is a theorem |
| `GgmArkLibTransport` | field→group transport against ArkLib's real `Groups.tSdhCondition` |
| `GgmProbThreading` | collapses ArkLib's `OptionT ProbComp` / `StateT QueryCache` game to `card/(p−1)` |
| `GgmDegreeDischarge` | discharges the SRS degree invariant on the *actual* (linear, pairing-free) oracle |
| `GgmEmbed` | constructs the generic-restricted Maurer adversary and certifies what it realizes |
| `GgmEndToEnd` | the Maurer capstone `tSdh_ggm_sound` (+ `tSdh_ggm_sound_lt_one`), wired to `tSdhExperiment` |
| `GgmShoup` | the Shoup free-comparison capstone `shoup_ggm_sound` (+ `_lt_one`), model-internal |
| `GgmShoupEmbed` | wires Shoup into `tSdhExperiment`: `shoup_tSdh_ggm_sound` (+ `_lt_one`) |

To our knowledge — a census of ArkLib, VCVio, and Mathlib — no generic-group-model security
*theorem* previously existed in Lean, so this is a candidate first of its kind. ArkLib's own
`AGM/Basic.lean` is a WIP stub (`Adversary.run` is `sorry`, zero theorems, orphaned) and is
moreover unsound as written: its adversary is a `ReaderT` over the concrete group table, so its
outputs can still depend on discrete logs. If you would prefer to complete that module to
opacity instead, the extraction-shaped fix in §2 is the right first step regardless: it isolates
the *single* obligation (bound the success of the one reduction adversary) that any restricted
assumption — generic, algebraic, or otherwise — must discharge.

### Honest side-conditions on both bounds

These travel with every citation:

- `1 ≤ D` — the meaningful KZG regime; at `D = 0` a pairing-free `G₁` adversary genuinely
  cannot form `g₁^τ`.
- `2 ≤ p` (so `p − 1 ≥ 1`) and, for both tracks' transport into `tSdhExperiment`,
  `orderOf g₁ = p` (the base is a generator, used for encoding injectivity).
- Maurer only: `[∀ i, SampleableType (unifSpec.Range i)]` — ArkLib's own instance on
  `tSdhExperiment`, carried verbatim.
- The bound is the classical Boneh–Boyen shape `O((q_G + D)²·D / p)` — degree-dependent, **not**
  a clean `q²/p`.
- Both capstones quantify over the **image of their embedding** (`embed` / `embedShoup`) into
  ArkLib's `tSdhAdversary`, not the full type — over the full type the statement is false (§1).
  `GgmShoup.shoup_ggm_sound` is the model-internal statement about `shoupExperiment`;
  `GgmShoupEmbed.shoup_tSdh_ggm_sound` is the one wired to ArkLib's `tSdhExperiment`.

`GgmRandomEncoding` additionally carries, clearly labelled as **off-path**, a conservative
pairing-capable `δ = 2D` variant (`rand_encoding_bound` / `_srs` / `card_pairRootUnion_le_two_mul`).
It is not consumed by either capstone — both take the `δ = D` chain — and is kept only as the
conservative ceiling for a stronger, off-interface (pairing-capable) adversary. It builds
`sorry`-free on the same axioms.

---

## 4. Build and check

Against ArkLib at `d72f8392` with Lean `v4.31.0` (VCVio/CompPoly `v4.31.0`), the modules under
`ArkLib/Scratch/KzgVacuity/` (these are `Scratch` modules — build them by explicit target; the
default `lake build` builds the main `ArkLib` library, which includes the §2 fix to
`Binding.lean`):

```bash
# The finding
lake build ArkLib.Scratch.KzgVacuity.KzgVacuity
#   #print axioms ArkLibVacuity.not_tSdhAssumption               → [propext, Classical.choice, Quot.sound]
#   #print axioms ArkLibVacuity.not_arsdhAssumption              → [propext, Classical.choice, Quot.sound]
#   #print axioms ArkLibVacuity.tSdhAssumption_trivial_of_one_le → [propext, Classical.choice, Quot.sound]

# The fix (applied to ArkLib/Commitments/Functional/KZG/Binding.lean) and its survival proof
lake build ArkLib.Scratch.KzgVacuity.RepairSurvives
#   #print axioms KZG.CommitmentScheme.binding_reduces_to_tSdh   → [propext, Classical.choice, Quot.sound]
#   #print axioms ArkLibRepairCheck.repair_survives_attack       → [propext, Classical.choice, Quot.sound]

# The GGM bound, Maurer track (wired to ArkLib's real tSdhExperiment)
lake build ArkLib.Scratch.KzgVacuity.GgmEndToEnd
#   #print axioms GgmEndToEnd.tSdh_ggm_sound                      → [propext, Classical.choice, Quot.sound]
#   #print axioms GgmEndToEnd.tSdh_ggm_sound_lt_one              → [propext, Classical.choice, Quot.sound]

# The GGM bound, Shoup track (wired to ArkLib's real tSdhExperiment)
lake build ArkLib.Scratch.KzgVacuity.GgmShoupEmbed
#   #print axioms GgmShoup.shoup_ggm_sound                        → [propext, Classical.choice, Quot.sound]
#   #print axioms GgmShoupEmbed.shoup_tSdh_ggm_sound              → [propext, Classical.choice, Quot.sound]
#   #print axioms GgmShoupEmbed.shoup_tSdh_ggm_sound_lt_one       → [propext, Classical.choice, Quot.sound]
```

Every headline theorem is `sorry`-free with axiom closure exactly
`[propext, Classical.choice, Quot.sound]` — no `sorryAx`, no `native_decide`, no
`ofReduceBool`. The `Classical.choice` in the vacuity theorems is the *content*, not a smell:
it is the unbounded extractor being exhibited as a legal inhabitant of the unrestricted
adversary type.

---

## 5. A note on framing

We ran this same "try to prove each hardness floor false at its deployed parameters" tooth on
our own Lean tree before pointing it here, and found the identical unrestricted-quantifier hole
in several of our own floors first. `#print axioms` was blind to all of them. The reduction in
`Binding.lean` is careful, correct work — which is exactly why the honest thing is to state it
soundly rather than route around it. We bring the finding, the fix, and both GGM bounds together
so the whole story is one branch a reviewer can `git checkout` at any commit and `lake build`.

## References

- **[BB04]** Boneh, D., and Boyen, X. *Short Signatures Without Random Oracles.* EUROCRYPT 2004.
- **[KZG10]** Kate, A., Zaverucha, G. M., and Goldberg, I. *Constant-Size Commitments to
  Polynomials and Their Applications.* ASIACRYPT 2010.
- **[Sho97]** Shoup, V. *Lower Bounds for Discrete Logarithms and Related Problems.* EUROCRYPT 1997.
- **[Mau05]** Maurer, U. *Abstract Models of Computation in Cryptography.* IMA 2005.
- **[FKL18]** Fuchsbauer, G., Kiltz, E., and Loss, J. *The Algebraic Group Model and its
  Applications.* CRYPTO 2018.
- **[Sch80]** Schwartz, J. T. *Fast Probabilistic Algorithms for Verification of Polynomial
  Identities.* J. ACM 1980.
- **[Zip79]** Zippel, R. *Probabilistic Algorithms for Sparse Polynomials.* EUROSAM 1979.

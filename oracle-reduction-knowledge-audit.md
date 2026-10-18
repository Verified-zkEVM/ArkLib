# OracleReduction knowledge soundness audit

## Historical interface restoration

The concrete public RBR theorem names again denote the historical averaged guarantee,
now written explicitly as `rbrKnowledgeSoundnessAveraged`. Their stronger internal proofs
have the suffix `_fixedPrefix`. The framework's canonical `rbrKnowledgeSoundness` still
means fixed-prefix security; no averaged-to-fixed-prefix implication is assumed.

The historical inventory at `88e079f0a5b871088e5cc53a0b6047f459fc0323` contains 51 public
completeness, RBR knowledge-soundness, and plain knowledge-soundness theorems in scope.
All 51 full elaborated types match after translating the historical averaged predicate's
name. The comparison checks binder explicitness as well as Lean definitional equality.
The saved fixtures under `ArkLibTest/OracleReduction/HistoricalInterfaces/` replay the
historical signatures and declaration contexts, not signatures copied from current code.
`HistoricalTypeCheck.lean` performs the comparisons. Proofs in the fixtures reuse the
current public results without admissions. These checks do not, by themselves, establish
that every definition referenced by a signature retains its historical meaning; the
definition and execution audit is a separate obligation.

The generic `RingSwitching.FullRingSwitching.fullOracleVerifier_rbrKnowledgeSoundness`
also has its historical type again, without an extra fixed-prefix tail certificate.
`MLIOPCS` retains its historical averaged-only security field. The proved
`Verifier.append_rbrKnowledgeSoundnessAveraged_empty` composes a fixed-prefix guarded front
with an averaged-only tail when the ambient oracle is empty. It conditions on the actual
front transcript and private prover state, applies averaged security to the resulting
suffix prover, and averages without changing the component errors. The required inhabited
tail witness is supplied internally by the zero multilinear polynomial; no public
hypothesis is added. Stronger fixed-prefix results remain separately named auxiliaries.
This specialization does not restore the false unrestricted shared-state contracts.

The targeted build through `FRIBinius.General` and all 51 signature checks pass.
The latest dependency sweep contains 17,647 declarations across 867 modules, with 200
pre-existing sorry-tainted declarations and no nonstandard axioms. All 999 Binius and
521 RingSwitching declarations have only standard foundational axiom dependencies.
Full `./scripts/validate.sh --axioms --docs` passed with exit code zero using Python
3.12.14, including the full build, tests, source policy, retirement scan, axiom baseline,
and API documentation generation.

The averaged-only investigation now has proved execution support in
`Composition/Sequential/Append/ProverSuffix.lean`: an arbitrary prover can be continued
from its actual boundary state; projecting that continuation yields the suffix prover's
execution; and the original run factors through the boundary without resetting state.
The corresponding axiom regression test permits only standard foundational axioms.
These identities feed the now-proved averaged-composition theorem and its generic
RingSwitching application.

The continuation support now also proves that every supported suffix execution preserves
the completed front transcript. `Security/EmptyAmbient.lean` proves state independence for
challenge-only execution and rewrites the logged averaged RBR game as a stateless prefix
run followed by a fresh challenge. Both modules build, and the continuation regression
test checks the transitive axioms of the boundary-preservation and RBR-game identities:
only `propext`, `Classical.choice`, and `Quot.sound` occur. These targeted checks do not
replace repository-wide validation, which also passed.

`Append/AveragedEmpty.lean` now proves the averaged tail bound for each fixed boundary
state and for any distribution of boundary states. The intermediate statement may depend
on the sampled boundary transcript and private state. The bound remains the original
tail error; no averaged-to-fixed-prefix implication is used. Composed-bad-event containment
along the actual continuation, the generic RingSwitching application, and its historical
full-type check now pass. The definition-preservation audit below and repository-wide
validation are complete.

## Public theorem compatibility table

### Definition and execution preservation

A parser-level comparison against the historical commit checked non-theorem declarations
in the changed Binius and packing modules, ignoring source locations and documentation.
It found 192 identical definition/instance declarations and one changed declaration,
`bbfMLIOPCS`; 37 other source files were byte-for-byte unchanged. Inspection of the complete
`bbfMLIOPCS` diff confirms that only its `rbrKnowledgeSoundness` proof field changed:
the protocol specification, oracle reduction, completeness field, and error function are
unchanged. The packing `Prelude` was inspected separately: its only change is the `MLIOPCS`
averaged-security field's explicit predicate spelling and definitionally equivalent verifier
wrapper, plus documentation. No executable field or relation is changed there.

The historical averaged predicate's game body itself is unchanged by its rename, as is its
certificate-specific variant. Thus the type comparisons are not concealing a switch from
averaged to fixed-prefix security. Protocol message schedules, prover/verifier definitions,
strict and relaxed relations, and numerical error definitions remain historical. New
fixed-prefix theorems and empty-ambient composition lemmas change the proof route only.
The separate, necessary legacy simple-Sumcheck correction below is retained; it is not a
change to the Binius structured-Sumcheck protocol.

Historical and current public theorem names in this table are identical. “Exact translated
type” means syntactically identical elaborated expressions after translating the historical
averaged predicate to its explicit current name; it does not claim that the predicate's
source spelling is unchanged. “Definitionally equivalent” means the kernel expressions
differ but Lean verifies definitional equality, with the same binder explicitness. There
are 38 exact translated types and 13 definitionally equivalent types, including generic
RingSwitching. No theorem in this inventory has a remaining signature exception.

| Historical and current public theorem | Classification |
| --- | --- |
| `Binius.BinaryBasefold.CoreInteraction.coreInteractionOracleReduction_perfectCompleteness` | Exact translated type |
| `Binius.BinaryBasefold.CoreInteraction.coreInteractionOracleVerifier_rbrKnowledgeSoundness` | Exact translated type |
| `Binius.BinaryBasefold.CoreInteraction.foldRelayOracleReduction_perfectCompleteness` | Exact translated type |
| `Binius.BinaryBasefold.CoreInteraction.foldRelayOracleVerifier_rbrKnowledgeSoundness` | Exact translated type |
| `Binius.BinaryBasefold.CoreInteraction.foldCommitOracleReduction_perfectCompleteness` | Exact translated type |
| `Binius.BinaryBasefold.CoreInteraction.foldCommitOracleVerifier_rbrKnowledgeSoundness` | Exact translated type |
| `Binius.BinaryBasefold.CoreInteraction.nonLastSingleBlockOracleReduction_perfectCompleteness` | Definitionally equivalent |
| `Binius.BinaryBasefold.CoreInteraction.lastBlockOracleReduction_perfectCompleteness` | Definitionally equivalent |
| `Binius.BinaryBasefold.CoreInteraction.sumcheckFoldOracleReduction_perfectCompleteness` | Exact translated type |
| `Binius.BinaryBasefold.CoreInteraction.lastBlockOracleVerifier_rbrKnowledgeSoundness` | Definitionally equivalent |
| `Binius.BinaryBasefold.CoreInteraction.nonLastSingleBlockOracleVerifier_rbrKnowledgeSoundness` | Definitionally equivalent |
| `Binius.BinaryBasefold.CoreInteraction.nonLastBlocksOracleVerifier_rbrKnowledgeSoundness` | Definitionally equivalent |
| `Binius.BinaryBasefold.CoreInteraction.sumcheckFoldOracleVerifier_rbrKnowledgeSoundness` | Exact translated type |
| `Binius.BinaryBasefold.FullBinaryBasefold.fullOracleReduction_perfectCompleteness` | Exact translated type |
| `Binius.BinaryBasefold.FullBinaryBasefold.fullOracleVerifier_rbrKnowledgeSoundness` | Exact translated type |
| `Binius.BinaryBasefold.FullBinaryBasefold.fullOracleVerifier_knowledgeSoundness` | Definitionally equivalent |
| `Binius.BinaryBasefold.QueryPhase.queryOracleProof_perfectCompleteness` | Exact translated type |
| `Binius.BinaryBasefold.QueryPhase.queryOracleVerifier_rbrKnowledgeSoundness` | Definitionally equivalent |
| `Binius.BinaryBasefold.CoreInteraction.commitOracleReduction_perfectCompleteness` | Exact translated type |
| `Binius.BinaryBasefold.CoreInteraction.commitOracleVerifier_rbrKnowledgeSoundness` | Exact translated type |
| `Binius.BinaryBasefold.CoreInteraction.finalSumcheckOracleReduction_perfectCompleteness` | Exact translated type |
| `Binius.BinaryBasefold.CoreInteraction.finalSumcheckOracleVerifier_rbrKnowledgeSoundness` | Exact translated type |
| `Binius.BinaryBasefold.CoreInteraction.foldOracleVerifier_rbrKnowledgeSoundness` | Exact translated type |
| `Binius.BinaryBasefold.CoreInteraction.foldOracleReduction_perfectCompleteness` | Exact translated type |
| `Binius.BinaryBasefold.CoreInteraction.relayOracleReduction_perfectCompleteness` | Exact translated type |
| `Binius.BinaryBasefold.CoreInteraction.relayOracleVerifier_rbrKnowledgeSoundness` | Exact translated type |
| `Binius.FRIBinius.CoreInteractionPhase.finalSumcheckOracleReduction_perfectCompleteness` | Exact translated type |
| `Binius.FRIBinius.CoreInteractionPhase.finalSumcheckOracleVerifier_rbrKnowledgeSoundness` | Exact translated type |
| `Binius.FRIBinius.CoreInteractionPhase.coreInteractionOracleReduction_perfectCompleteness` | Exact translated type |
| `Binius.FRIBinius.CoreInteractionPhase.coreInteractionOracleVerifier_rbrKnowledgeSoundness` | Exact translated type |
| `Binius.FRIBinius.CoreInteractionPhase.sumcheckFoldOracleReduction_perfectCompleteness` | Exact translated type |
| `Binius.FRIBinius.CoreInteractionPhase.sumcheckFoldOracleVerifier_rbrKnowledgeSoundness` | Exact translated type |
| `Binius.FRIBinius.FullFRIBinius.fullOracleReduction_perfectCompleteness` | Exact translated type |
| `Binius.FRIBinius.FullFRIBinius.batchingCoreVerifier_rbrKnowledgeSoundness` | Exact translated type |
| `Binius.FRIBinius.FullFRIBinius.fullOracleVerifier_rbrKnowledgeSoundness` | Definitionally equivalent |
| `Binius.FRIBinius.FullFRIBinius.fullOracleVerifier_knowledgeSoundness` | Definitionally equivalent |
| `Binius.RingSwitching.BBFSmallFieldIOPCS.largeFieldInvocationOracleReduction_perfectCompleteness` | Definitionally equivalent |
| `Binius.RingSwitching.BBFSmallFieldIOPCS.bbf_fullOracleReduction_perfectCompleteness` | Definitionally equivalent |
| `Binius.RingSwitching.BBFSmallFieldIOPCS.bbf_fullOracleVerifier_rbrKnowledgeSoundness` | Definitionally equivalent |
| `Binius.RingSwitching.BBFSmallFieldIOPCS.bbf_fullOracleVerifier_knowledgeSoundness` | Definitionally equivalent |
| `RingSwitching.BatchingPhase.batchingReduction_perfectCompleteness` | Exact translated type |
| `RingSwitching.BatchingPhase.batchingOracleVerifier_rbrKnowledgeSoundness` | Exact translated type |
| `RingSwitching.FullRingSwitching.batchingCore_perfectCompleteness` | Exact translated type |
| `RingSwitching.FullRingSwitching.fullOracleReduction_perfectCompleteness` | Exact translated type |
| `RingSwitching.SumcheckPhase.iteratedSumcheckOracleReduction_perfectCompleteness` | Exact translated type |
| `RingSwitching.SumcheckPhase.iteratedSumcheckOracleVerifier_rbrKnowledgeSoundness` | Exact translated type |
| `RingSwitching.SumcheckPhase.finalSumcheckOracleReduction_perfectCompleteness` | Exact translated type |
| `RingSwitching.SumcheckPhase.finalSumcheckOracleVerifier_rbrKnowledgeSoundness` | Exact translated type |
| `RingSwitching.SumcheckPhase.coreInteraction_perfectCompleteness` | Exact translated type |
| `RingSwitching.SumcheckPhase.coreInteraction_rbrKnowledgeSoundness` | Exact translated type |
| `RingSwitching.FullRingSwitching.fullOracleVerifier_rbrKnowledgeSoundness` | Exact translated type |

## Framework repair

### Restoration acceptance evidence

| Requirement | Evidence |
| --- | --- |
| Historical theorem inventory and full types | 51 static signature fixtures; 38 exact translated types, 13 definitionally equal types; binder explicitness checked |
| Historical averaged meaning | Unchanged averaged game body, explicitly named `rbrKnowledgeSoundnessAveraged`; no reverse implication used |
| Internal stronger proofs | `_fixedPrefix` auxiliaries use proved guarded composition and context lifting |
| Protocol execution, relations, errors | Parser comparison and complete review of the two differing data/interface declarations, described above |
| Generic MLIOPCS | Averaged-only field suffices via proved empty-ambient append; original generic theorem type verified without extra assumptions |
| Necessary Sumcheck correction | Corrected message-polynomial evaluation retained; compiled old-execution counterexample and security dependency tests |
| Other clients | Caller inventory below; repository build/tests cover component, cast, vector, and ToyProblem migrations |
| Axiom cleanliness | 999 Binius and 521 RingSwitching declarations checked transitively; no nonfoundational dependencies |
| Full validation | `--axioms --docs` exited zero with Python 3.12.14; full build and all validation gates passed |
| Local-only changes | Branch remains `fix/oracle-reduction-knowledge-contracts`, HEAD remains the historical commit; no commit, push, or PR mutation |

The unrestricted append, sequential composition, and RBR-to-plain knowledge-soundness
contracts are false for arbitrary shared-state oracle implementations. The context-lifting
claims survive, but the round-by-round extractor needs a different intermediate witness
family. This branch supplies compiled counterexamples and proved replacements; it does not
claim that the entire OracleReduction framework is admission-free.

This audit is on `fix/oracle-reduction-knowledge-contracts`, based at
`88e079f0a5b871088e5cc53a0b6047f459fc0323`. The read-only remote-main check returned
`35ddcaa83f683011f944f58904be779495a5709a`. No merge, rebase, commit, push, or PR update is
part of this repair. The paper directory and Obsidian notes are outside its write scope.

Alex's [port plan](https://github.com/Verified-zkEVM/ArkLib/pull/383#issuecomment-6035284809)
separates statement review, RingSwitching, framework additions, Binary Basefold, and finally
FRI-Binius composition. This work addresses the separately identified framework caveat;
it does not import the RingSwitching profile redesign or modify those port PRs. Current
main was fetched for inspection only. Its append, sequential, implication, and context-lifting
files have no changes relative to this branch's base; the five contracts are therefore not
already repaired there. The differing framework files principally reflect additions present
on the FRI-Binius branch, not a reason to overwrite current main's probability infrastructure.

## Truth status of the original contracts

| Original contract | Status | Replacement |
| --- | --- | --- |
| `Verifier.append_rbrKnowledgeSoundness` | False without state restrictions | Fixed-prefix bounds and a guarded first verifier; alternatively, state-valid accepting refinements of guarded references |
| `Verifier.seqCompose_rbrKnowledgeSoundness` | False without state restrictions | Induction from repaired append, with guarded components or their state-valid accepting refinements |
| `Verifier.rbrKnowledgeSoundness_implies_knowledgeSoundness` | False with only fresh-initialization terminal knowledge | Actual-reachable-state terminal certificate plus backward extraction and a bad-transition union bound |
| `Verifier.liftContext_rbr_knowledgeSoundness` | Valid with the lens compatibility hypotheses and repaired extractor | Proved fixed-prefix and averaged variants with unchanged error |
| `Reduction.liftContext_completeness` | Valid under its existing completeness lens hypotheses | Direct execution transport proof; no stronger completeness assumption |

The original unsuffixed RBR definition averaged over prover-generated prefixes. In this
branch, `rbrKnowledgeSoundness` denotes the stronger fixed-prefix property;
`rbrKnowledgeSoundnessAveraged` preserves the old averaged meaning. Their `With` variants
retain the exact extractor and knowledge-state certificate. The fixed-prefix-to-averaged
implication is proved; the reverse implication is not assumed.

## Compiled counterexamples

`ArkLibTest/OracleReduction/Composition/Sequential/KnowledgeStateCounterexample.lean`
uses a Boolean shared state initialized to `false` and zero-message protocols. The oracle
can write `true` or read the current bit.

For append, the first verifier writes `true` and returns the unique statement. Its input
and output relations are empty, so its individual knowledge claim is valid. The second
verifier accepts precisely when the bit is `true`; its input relation is empty and output
relation universal. From fresh initialization it always rejects, so its individual
zero-error claim is also valid. In the actual composition it instead receives `true`,
accepts, and produces a related output from an unrelated input with probability one.

The file proves `first_secure`, `second_secure`, `composed_accepts`, and
`composed_not_secure`. It also constructs the actual two-component n-ary composition and
proves `sequence_accepts` and `sequence_not_secure`, rather than merely appealing to an
informal equivalence with append.

For RBR-to-plain, the malicious zero-message prover writes `true` in its output action.
The second verifier is secure under the fresh-initialization RBR certificate but accepts
in the real reduction execution. `second_not_plain` rules out the claimed zero-error
plain knowledge soundness, including arbitrary candidate extractors.

The same file proves `same_family_lift_impossible`: retaining an inner witness family
whose round-zero type is `Unit` cannot supply the required equality with an outer
round-zero witness type `Bool`. The fix is a new family, not another assumption asserting
that these types coincide. The counterexample dependency checks exclude `sorryAx`.

## Repaired composition and extraction

### Guarded verifiers

`Append/KnowledgeState.lean` constructs the composed extractor and knowledge state.
`append_rbrKnowledgeSoundness_of_guarded_first` requires a deterministic, possibly rejecting
first verifier and fixed-prefix component bounds. The second verifier may use ambient
state. Guardedness prevents the first verifier from changing the state at the seam and
provides a deterministic intermediate statement for transporting the certificates.

The resulting per-round error is exactly
`Sum.elim ε₁ ε₂ ∘ ChallengeIdx.sumEquiv.symm`. It is not replaced by a larger uniform bound.
`Sequential/GuardedKnowledge.lean` derives finite sequential composition and oracle-verifier
wrappers, retaining each component's error through `seqComposeChallengeIdxToSigma`.

### Stateful implementations

`Sequential/StatefulKnowledge.lean` defines `GuardedForm.AcceptingRefinement`. At every shared
state, each accepting execution of the actual verifier must pass the reference check and
return the reference output. State mutation and probabilistic rejection are allowed.
This is a sufficient operational condition, not unrestricted stateful composition and not
an assumption of the desired knowledge-soundness conclusion.

The append proof factors acceptance through the actual intermediate state using
`append_accepting_support_iff`. The sequential theorem follows by induction. Reference
knowledge predicates and extractors are retained, and the reference errors are unchanged.
Requiring refinement at every state is stronger than requiring it only at reachable states.

The regression example in
`ArkLibTest/OracleReduction/Composition/Sequential/StatefulKnowledge.lean` flips the shared
bit while returning the input statement. It proves plain zero-error knowledge soundness
for the nontrivial relation that the statement equals its witness. Thus the theorem does
not require state preservation or a universal input relation.

### Actual execution terminal knowledge

`Security/ActualExtraction.lean` proves the reachable-state version first. For every
malicious prover, the terminal knowledge condition must hold for accepting verifier runs
starting in the state produced by that prover's actual run, including its output action.
Backward extraction then shows that a related accepted output with failed input extraction
requires a bad challenge transition. The union bound gives total error $\sum_i\varepsilon_i$.

Sufficient special cases are provided for terminal knowledge at every state, guarded
verifiers, full-support initialization, and actual reachable verifier-start states remaining
inside initialization support. These conditions justify the terminal step; they do not
silently reset the actual execution. The accepting-refinement theorem supplies the
every-state certificate and therefore also plain knowledge soundness.

## Context lifting

`LiftContext/Reduction.lean` uses the outer input witness at round zero. At later rounds the
lifted family carries the inner intermediate witness together with the outer output witness.
This supplies the information needed for the inverse witness lens during backward extraction.
The empty-round identity, next-round implication, terminal condition, and bad-event transport
are proved for this family.

The fixed-prefix lifting theorem needs no simulated inner prover or inhabited inner input
witness. The averaged variant simulates the projected prover and retains its required
inhabitedness hypotheses. `LiftContext/OracleReduction.lean` transports both results through
the executable oracle-statement lens. Completeness is proved separately by execution and
relation transport.

## Caller migration inventory

| Caller family | Repair and preserved guarantee |
| --- | --- |
| Binary Basefold steps, core interaction, query phase, full protocol | Fixed-prefix component bounds feed guarded append and sequential composition; existing relations and error expressions are retained; headline plain KS uses guarded terminal knowledge |
| RingSwitching packing batching and Sumcheck phases, core and full reduction | Guarded composition replaces unrestricted composition; component and composed error expressions are retained |
| BBFSmallFieldIOPCS | Uses repaired context lifting and guarded composition; plain KS obtains the actual-state terminal condition from guardedness |
| FRIBinius SumcheckFold, core interaction, full protocol | Uses fixed-prefix lifting and composition; headline plain KS follows through the proved extraction theorem |
| `Prelude.MLIOPCS` | Historical averaged field and generic composed theorem restored through proved empty-ambient composition; no added public tail certificate |
| Legacy Sumcheck specification | Corrected verifier output and strengthened algebraic hypotheses; details below |
| ToyProblem specification and IRS implementation | Existing fixed-prefix and averaged proofs are renamed distinctly; extractor-specific guarantees and error expressions are retained |
| Basic components, casts, and VectorIOR | Averaged uses are named explicitly; fixed-prefix transport is separate, avoiding an unproved averaged-to-fixed upgrade |

The historical direct-call inventory below comes from the five original identifiers in
`git grep` at the branch base. Counts exclude declarations, comments, and framework wrappers.
Paths are relative to `ArkLib/ProofSystem/`.

| Historical caller file | Direct uses | Current route |
| --- | --- | --- |
| `Binius/BinaryBasefold/CoreInteractionPhase.lean` | 1 append | Guarded append |
| `Binius/BinaryBasefold/CoreInteractionPhase/Protocol.lean` | 2 append | Guarded append |
| `Binius/BinaryBasefold/CoreInteractionPhase/Security.lean` | 2 append, 3 sequential | Guarded append and sequential composition |
| `Binius/BinaryBasefold/General.lean` | 1 append, 1 RBR-to-plain | Guarded append and actual-state extraction |
| `Binius/FRIBinius/CoreInteractionPhase.lean` | 1 append | Guarded append |
| `Binius/FRIBinius/CoreInteractionPhase/SumcheckFold.lean` | 1 lifting | Fixed-prefix context lifting |
| `Binius/FRIBinius/General.lean` | 2 append, 1 RBR-to-plain | Guarded append and actual-state extraction |
| `RingSwitching/Packing/BBFSmallFieldIOPCS.lean` | 1 lifting, 1 RBR-to-plain | Fixed-prefix lifting and actual-state extraction |
| `RingSwitching/Packing/General.lean` | 2 append | Guarded append |
| `RingSwitching/Packing/SumcheckPhase.lean` | 1 append, 1 sequential | Guarded append and sequential composition |
| `Sumcheck/Spec/General.lean` | 1 sequential | Guarded sequential composition with integral-domain hypotheses |
| `Sumcheck/Spec/SingleRound.lean` | 1 lifting | Proved replacement in `Sumcheck/Spec/Knowledge.lean` |

The context-completeness contract is also called by its perfect-completeness corollary and
oracle wrapper; both remain proved. The old sequential contract's recursive append call and
both oracle composition wrappers were replaced with the guarded routes. Searches of the
current `ArkLib/` and `ArkLibTest/` trees find no exact occurrences of the three retired
unrestricted append, sequential, and RBR-to-plain identifiers.

The perfect-completeness corollary adds four protocol call sites: FRIBinius `SumcheckFold`,
BBFSmallFieldIOPCS's large-field invocation, and both plain and oracle single-round legacy
Sumcheck completeness. All four continue to call the proved lifting corollary. The first two
and their composed Binius consequences are now axiom-clean. The latter two retain their
pre-existing, independently admitted Sumcheck lens-completeness obligations; repairing the
generic lifting theorem does not prove those caller-specific lens laws.

The protocol-specific axiom regression files cover Binary Basefold, RingSwitching,
BBFSmallFieldIOPCS, FRIBinius, and the repaired Sumcheck security results. Their dependency
checks inspect the transitive axioms of the named headline theorems, not just their source
bodies. The full per-declaration axiom sweep additionally checked all 999 declarations in
`ArkLib.ProofSystem.Binius` and all 521 in `ArkLib.ProofSystem.RingSwitching`: none depends on
`sorryAx` or a nonstandard axiom. This includes transitive users of the repaired contracts,
not only the historical direct-call sites.

## Necessary Sumcheck correction

The legacy simple verifier checked the prover's polynomial $q$ but set the next claimed
value to the input polynomial's evaluation $p(r)$. The corrected next claim is $q(r)$.
The oracle verifier correspondingly queries the message oracle for that value.

`SumcheckExecutionCounterexample.lean` records the old behavior over $\mathbb F_2$ with
$p=0$, claimed sum $1$, and constant message $q=1$ over the singleton summation domain.
The sum check passes for every challenge. The old output satisfies the next relation,
although the input does not, contradicting the claimed degree-zero error. The corrected
output remains false. Honest execution is preserved because the honest prover sends $q=p$.

The collision argument also needs a root bound. Security theorems now require a finite
commutative integral domain rather than an arbitrary semiring; execution remains defined
over semirings. `Spec/CollisionBound.lean` and `Spec/Knowledge.lean` prove the corrected
degree-over-cardinality bound, the extractor lens, and the security corollaries. This is
an explicit mathematical and execution correction, not merely a theorem rename.

## Validation and residual admissions

The repaired guarded composition, context lifting, backward extraction, stateful refinement,
counterexamples, and protocol regression tests have compiled. Their explicit dependency
checks permit only `propext`, `Classical.choice`, and `Quot.sound`, not `sorryAx`.

The final restoration run passed `./scripts/validate.sh --axioms --docs` with exit code zero:
5,153 build jobs, 5,032 test jobs, and 10,628 documentation jobs. During validation,
the retirement gate exposed a broad simplifier's
dependency on deprecated probability lemmas; the proof now uses explicit native measure
lemmas, and the retirement scan is clean. Two isolated `by` formatting violations in
historical fixtures were also corrected without changing their signatures.

Run from the repository root:

```sh
env PATH="/opt/homebrew/opt/python@3.12/libexec/bin:/Users/chung-thai-nguyen/.elan/bin:$PATH" \
  ./scripts/validate.sh --axioms --docs
```

The per-declaration dependency report can be reproduced after building with
`lake exe axiomsweep --out /tmp/oracle-reduction-dependencies.json`.

The full current per-declaration sweep reports 17,647 declarations across 867 modules.
All 20 declarations in the new append knowledge module, 8 in guarded sequential knowledge,
13 in stateful knowledge, 10 in actual extraction, and 17 in the Sumcheck knowledge module
have only standard foundational axiom dependencies. The repaired lifting declarations and
their oracle wrappers were also individually checked in that report.

The API now includes fixed-prefix `OracleVerifier.rbrKnowledgeSoundness`, its certificate-specific
`With` variant, and the `Proof` and `OracleProof` wrappers. They are definitionally the underlying
fixed-prefix games. Existing averaged wrappers remain explicitly named. The legacy
`Verifier.IsRBRKnowledgeSound` typeclass still packages the averaged notion; no caller uses
that class to infer a fixed-prefix guarantee.

Accepting-refinement composition is proved for guarded reference outputs; it is not a theorem
covering arbitrary state-dependent reference outputs. The more general actual-state terminal
extraction theorem does allow state-dependent outputs. These are explicit sufficient conditions,
not a reinstatement of the refuted unrestricted composition contracts.

The audited baseline changes from 243 to 200 sorry-tainted declarations: 44 old entries
are removed and one entry is added. The addition is only the renamed pre-existing admitted
`Sumcheck.Spec.SingleRound.Simpler.oracleVerifier_rbrKnowledgeSoundnessAveraged`. The removed
entries include deleted false contracts, proved lifting results, corrected Sumcheck security
results, and protocol declarations freed from those transitive dependencies. This is not a
claim that 44 independent theorems were newly proved. The completed sweep reported zero
nonstandard-axiom dependencies.

Unrelated admissions remain, including other framework soundness/completeness results and
the experimental `Sumcheck.Spec.SingleRound.Simpler` construction. They must not be confused
with the proved repaired results. The axiom-baseline changes are audited separately from
proof completion: removing a false declaration or renaming one is not a new proof.

Specifically, the eight remaining tainted declarations under `OracleReduction.LiftContext`
are ordinary soundness and plain knowledge-soundness lifting and their oracle wrappers,
`Verifier.StateFunction.liftContext`, and `Reduction.liftContext_runWithLog`. The repaired
completeness and RBR knowledge-soundness proofs do not depend on them.
